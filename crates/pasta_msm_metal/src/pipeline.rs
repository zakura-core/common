//! The MSM pipeline shared by every backend: planning, host-side
//! preparation, the two device kernels as portable functions, and the
//! host-side finish.
//!
//! # Algorithm
//!
//! A bucket (Pippenger) multiscalar multiplication, shaped for a GPU:
//!
//! 1. **GLV split (host).** Each scalar $k$ becomes two signed halves,
//!    $k = k_1 + k_2 \lambda$, and each base $P$ becomes the pair
//!    $P, \phi(P) = (\zeta x, y)$, so the MSM has $2n$ terms with 127-bit
//!    scalars instead of $n$ terms with 255-bit ones. Half the windows,
//!    the same number of bucket additions, and half the final doublings.
//! 2. **Signed digits (host).** Every half is recoded into `windows`
//!    digits of `window_bits` bits in $[-2^{c-1}, 2^{c-1}]$. A negative
//!    digit adds the negated base ($y \mapsto -y$, free), so a window only
//!    keeps $2^{c-1}$ buckets rather than $2^c - 1$.
//! 3. **Bucket sort (host).** A counting sort groups the term references
//!    by bucket: `terms` lists, for every bucket in turn, the bases that
//!    fall into it (with the sign folded into the top bit), and `offsets`
//!    delimits the groups. This is the only host work linear in
//!    `terms × windows`, and it is a byte-cheap integer pass.
//! 4. **Bucket accumulation (device, [`accumulate_bucket`]).** One thread
//!    per bucket sums its bases with mixed additions. Buckets are
//!    independent, so this is embarrassingly parallel with no atomics.
//! 5. **Bucket reduction (device, [`reduce_chunk`]).** Each window needs
//!    $\sum_b b\,B_b$. The classical serial running-sum trick is replaced
//!    by a chunked recursion (see [`reduce_chunk`]) that runs one thread per
//!    chunk of $s$ buckets per level and finishes in $\lceil\log_s m\rceil$
//!    levels, each of them a few dozen sequential group operations.
//! 6. **Window combination (host).** The `windows` window results are
//!    combined by Horner's rule — `window_bits` doublings per window —
//!    with the curve's own arithmetic, after each result was validated to
//!    lie on the curve. Anything the backend got wrong surfaces here as
//!    `None`, and the caller falls back to the CPU planner.
//!
//! The kernels are written once, as portable Rust in this module, and
//! transliterated into `shaders/pasta_msm.metal`. The reference backend
//! executes the Rust versions over the very buffers the GPU would receive,
//! so the shader's contract — buffer layouts, index arithmetic, digit
//! conventions — is exercised on every platform.

use core::fmt;

use group::Group;

use crate::curve::{Affine, Jacobian};
use crate::field::{Field, Limbs};

/// The narrowest window the planner accepts.
pub const MIN_WINDOW_BITS: u32 = 4;
/// The widest window the planner accepts.
pub const MAX_WINDOW_BITS: u32 = 16;
/// The bit width every signed-recoded GLV half fits in: magnitudes are
/// below $2^{127}$, and the recoding's carry needs one more bit.
pub const HALF_BITS: u32 = 128;
/// The largest number of windows a half can need (`HALF_BITS / MIN_WINDOW_BITS`).
pub const MAX_WINDOWS: usize = (HALF_BITS / MIN_WINDOW_BITS) as usize;
/// The narrowest reduction chunk (two buckets per thread).
pub const MIN_CHUNK_LOG2: u32 = 1;
/// The widest reduction chunk (64 buckets per thread).
pub const MAX_CHUNK_LOG2: u32 = 6;

/// Backend tunables.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Config {
    /// The smallest MSM (in input terms, before the GLV split) the backend
    /// accepts; smaller MSMs stay on the CPU planner.
    ///
    /// The default is a placeholder pending measurement on real hardware:
    /// fixed dispatch latency dominates small MSMs, and the crossover
    /// against the multicore CPU backends has not been measured yet.
    pub min_terms: usize,
    /// Window width in bits, or `None` to derive it from the term count.
    pub window_bits: Option<u32>,
    /// $\log_2$ of the bucket-reduction chunk size $s$ (buckets per thread
    /// per level).
    pub chunk_log2: u32,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            min_terms: 4096,
            window_bits: None,
            chunk_log2: 3,
        }
    }
}

impl Config {
    /// Reads overrides from the environment, for experiments:
    /// `PASTA_MSM_METAL_MIN_TERMS`, `PASTA_MSM_METAL_WINDOW_BITS`, and
    /// `PASTA_MSM_METAL_CHUNK_LOG2`. Unset or unparsable variables keep the
    /// defaults.
    pub fn from_env() -> Self {
        let mut config = Config::default();
        let read = |name: &str| std::env::var(name).ok().and_then(|v| v.parse::<u32>().ok());
        if let Some(min_terms) = read("PASTA_MSM_METAL_MIN_TERMS") {
            config.min_terms = min_terms as usize;
        }
        if let Some(bits) = read("PASTA_MSM_METAL_WINDOW_BITS") {
            config.window_bits = Some(bits);
        }
        if let Some(chunk) = read("PASTA_MSM_METAL_CHUNK_LOG2") {
            config.chunk_log2 = chunk;
        }
        config
    }
}

/// One level of the chunked bucket reduction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Level {
    /// Entries per window in this level's input arrays.
    pub input_len: u32,
    /// Chunks (threads, and output entries) per window.
    pub chunks: u32,
}

/// The shape of one MSM: window geometry and reduction schedule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan {
    /// Input terms, before the GLV split.
    pub terms: usize,
    /// Window width $c$ in bits.
    pub window_bits: u32,
    /// Windows per half: $\lceil 128 / c \rceil$.
    pub windows: u32,
    /// Bucket slots per window: $2^{c-1} + 1$ (slot 0 is unused, so a
    /// digit's magnitude is its slot).
    pub slots: u32,
    /// $\log_2$ of the reduction chunk size.
    pub chunk_log2: u32,
    /// The reduction levels, first to last.
    pub levels: Vec<Level>,
}

impl Plan {
    /// Plans an MSM of `terms` input terms under `config`.
    ///
    /// Out-of-range configuration values are clamped to the supported
    /// ranges rather than rejected.
    pub fn new(terms: usize, config: &Config) -> Plan {
        let window_bits = config
            .window_bits
            .unwrap_or_else(|| Self::auto_window_bits(terms))
            .clamp(MIN_WINDOW_BITS, MAX_WINDOW_BITS);
        let windows = HALF_BITS.div_ceil(window_bits);
        let slots = (1u32 << (window_bits - 1)) + 1;
        let chunk_log2 = config.chunk_log2.clamp(MIN_CHUNK_LOG2, MAX_CHUNK_LOG2);
        let chunk = 1u32 << chunk_log2;
        let mut levels = Vec::new();
        let mut len = slots;
        while len > 1 {
            let chunks = len.div_ceil(chunk);
            levels.push(Level {
                input_len: len,
                chunks,
            });
            len = chunks;
        }
        Plan {
            terms,
            window_bits,
            windows,
            slots,
            chunk_log2,
            levels,
        }
    }

    /// The window width the planner picks on its own: about
    /// $\log_2(2n) - 1$, so a window holds roughly two terms per bucket.
    /// Unmeasured on hardware; a starting point for tuning.
    fn auto_window_bits(terms: usize) -> u32 {
        let split_terms = (terms.max(1) as u64).saturating_mul(2);
        // u64::ilog2 is at most 63, so the subtraction cannot underflow
        // past the clamp's lower bound in `new`.
        (split_terms.ilog2())
            .saturating_sub(1)
            .clamp(MIN_WINDOW_BITS, MAX_WINDOW_BITS)
    }

    /// Bucket slots over all windows.
    pub fn total_slots(&self) -> usize {
        self.windows as usize * self.slots as usize
    }

    /// Terms after the GLV split.
    pub fn split_terms(&self) -> usize {
        self.terms * 2
    }
}

/// A curve the pipeline can run over: the glue between `pasta_curves`
/// types and the backend's limb representation.
pub trait PastaCurve {
    /// The scalar field element type.
    type Scalar: Copy + Send + Sync;
    /// The affine point type.
    type Affine: Copy + Send + Sync;
    /// The projective point type.
    type Point: group::Group;

    /// The base field.
    const FIELD: Field;

    /// A short name for diagnostics.
    const NAME: &'static str;

    /// `Base::ZETA` in Montgomery form: the x-coordinate multiplier of the
    /// endomorphism $\phi$ with $\phi(P) = [\lambda] P$.
    fn zeta() -> Limbs;

    /// The affine limbs of `point` (identity to `(0, 0)`).
    fn affine(point: &Self::Affine) -> Affine;

    /// The GLV split of `scalar` as two `(is_negative, magnitude)` halves.
    fn split(scalar: &Self::Scalar) -> ((bool, u128), (bool, u128));

    /// Validates and converts a Jacobian result; `None` if it is not on
    /// the curve (the backend misbehaved).
    fn point(jacobian: &Jacobian) -> Option<Self::Point>;

    /// Combines window results by Horner's rule:
    /// $\sum_w 2^{c w} W_w$.
    fn combine_windows(windows: &[Self::Point], window_bits: u32) -> Self::Point {
        let mut acc = Self::Point::identity();
        for window in windows.iter().rev() {
            for _ in 0..window_bits {
                acc = acc.double();
            }
            acc += window;
        }
        acc
    }
}

/// A prepared MSM: exactly the buffers a backend consumes.
#[derive(Clone, Debug)]
pub struct Job {
    /// The plan this job was prepared under.
    pub plan: Plan,
    /// The split bases: `bases[2i]` is $P_i$, `bases[2i + 1]` is $\phi(P_i)$.
    pub bases: Vec<Affine>,
    /// Term references grouped by bucket: `base index | (negate << 31)`.
    pub terms: Vec<u32>,
    /// `total_slots + 1` offsets into `terms`; bucket `b` owns
    /// `terms[offsets[b]..offsets[b + 1]]`.
    pub offsets: Vec<u32>,
}

/// The sign flag in a term reference.
pub const TERM_NEGATE: u32 = 1 << 31;

/// The largest MSM (in input terms) the buffer formats can address: term
/// references keep 31 bits for the split-term index, and the bucket
/// offsets must count every `split term × window` entry in a `u32`.
pub const MAX_TERMS: usize = (1 << 26) - 1;

/// Recodes `magnitude` ($< 2^{127}$) into `windows` signed digits of
/// `window_bits` bits, each in $[-2^{c-1}, 2^{c-1}]$, such that
/// $\sum_w d_w 2^{c w}$ equals `magnitude`.
pub fn signed_digits(magnitude: u128, window_bits: u32, windows: u32, out: &mut [i32]) {
    debug_assert!(magnitude < 1 << 127);
    debug_assert!(window_bits * windows >= HALF_BITS);
    let mask = (1u128 << window_bits) - 1;
    let half = 1i64 << (window_bits - 1);
    let full = 1i64 << window_bits;
    let mut carry = 0i64;
    for (w, digit) in out.iter_mut().enumerate().take(windows as usize) {
        let shift = window_bits * w as u32;
        let raw = if shift >= HALF_BITS {
            0
        } else {
            // Masked to `window_bits` bits, so the cast cannot truncate.
            ((magnitude >> shift) & mask) as i64
        };
        let value = raw + carry;
        if value > half {
            *digit = (value - full) as i32;
            carry = 1;
        } else {
            *digit = value as i32;
            carry = 0;
        }
    }
    debug_assert_eq!(
        carry, 0,
        "a 127-bit magnitude never carries out of its windows"
    );
}

/// Prepares the device buffers for `scalars` and `bases` under `plan`.
///
/// # Panics
///
/// Panics if `scalars` and `bases` have different lengths, or if the
/// lengths disagree with `plan.terms`.
pub fn prepare<C: PastaCurve>(scalars: &[C::Scalar], bases: &[C::Affine], plan: &Plan) -> Job {
    assert_eq!(scalars.len(), bases.len());
    assert_eq!(scalars.len(), plan.terms);
    assert!(
        plan.terms <= MAX_TERMS,
        "MSM exceeds the backend's addressable size"
    );
    let field = &C::FIELD;
    let zeta = C::zeta();

    let mut split_bases = Vec::with_capacity(plan.split_terms());
    for base in bases {
        let affine = C::affine(base);
        split_bases.push(affine);
        // phi(P) = (zeta x, y); the identity's zero x stays zero.
        split_bases.push(Affine {
            x: field.mul(&affine.x, &zeta),
            y: affine.y,
        });
    }

    // The split halves, as (negate, magnitude) per split term.
    let halves: Vec<(bool, u128)> = scalars
        .iter()
        .flat_map(|scalar| {
            let (first, second) = C::split(scalar);
            [first, second]
        })
        .collect();

    // Counting sort by bucket over every nonzero digit. The digits are
    // recomputed in the placement pass rather than stored: the recoding is
    // a few shifts per digit, cheaper than the memory traffic of
    // materializing `split_terms × windows` entries.
    let total_slots = plan.total_slots();
    let mut counts = vec![0u32; total_slots + 1];
    let mut digits = [0i32; MAX_WINDOWS];
    for &(_, magnitude) in &halves {
        signed_digits(magnitude, plan.window_bits, plan.windows, &mut digits);
        for (w, &digit) in digits.iter().enumerate().take(plan.windows as usize) {
            if digit != 0 {
                let slot = w * plan.slots as usize + digit.unsigned_abs() as usize;
                counts[slot + 1] += 1;
            }
        }
    }
    for slot in 1..=total_slots {
        counts[slot] += counts[slot - 1];
    }
    let offsets = counts;
    let mut cursor = offsets.clone();
    let mut terms = vec![0u32; offsets[total_slots] as usize];
    for (index, &(negate, magnitude)) in halves.iter().enumerate() {
        signed_digits(magnitude, plan.window_bits, plan.windows, &mut digits);
        // Term indices are far below 2^31 for any MSM this crate can hold.
        let reference = index as u32;
        for (w, &digit) in digits.iter().enumerate().take(plan.windows as usize) {
            if digit != 0 {
                let slot = w * plan.slots as usize + digit.unsigned_abs() as usize;
                let flip = (digit < 0) != negate;
                terms[cursor[slot] as usize] = reference | if flip { TERM_NEGATE } else { 0 };
                cursor[slot] += 1;
            }
        }
    }

    Job {
        plan: plan.clone(),
        bases: split_bases,
        terms,
        offsets,
    }
}

/// Kernel 1: the sum of the bases referenced by bucket `bucket`.
///
/// Mirrors `accumulate_buckets` in the shader.
pub fn accumulate_bucket(
    field: &Field,
    bases: &[Affine],
    terms: &[u32],
    offsets: &[u32],
    bucket: usize,
) -> Jacobian {
    let start = offsets[bucket] as usize;
    let end = offsets[bucket + 1] as usize;
    let mut acc = Jacobian::IDENTITY;
    for &reference in &terms[start..end] {
        let base = bases[(reference & !TERM_NEGATE) as usize];
        let addend = if reference & TERM_NEGATE != 0 {
            base.neg(field)
        } else {
            base
        };
        acc = acc.add_mixed(&addend, field);
    }
    acc
}

/// Kernel 2: one chunk of one level of the bucket reduction.
///
/// A level holds, per window, `input_len` entries of two arrays: plain
/// values $P_j$ and weighted values $V_j$, and represents the sum
/// $R = \sum_j P_j + \sum_j j\,V_j$ (at level 0, $P$ is absent and $V$ is
/// the bucket array, so $R$ is the window's $\sum_b b\,B_b$). Splitting
/// the index as $j = q s + i$ with chunk size $s = 2^{\text{chunk\_log2}}$
/// gives
///
/// $$R = \sum_q A_q + s \sum_q q\,T_q,\quad
///   A_q = \sum_i (P_{qs+i} + i\,V_{qs+i}),\quad T_q = \sum_i V_{qs+i},$$
///
/// so the chunk outputs $(A_q, s\,T_q)$ are the next level's plain and
/// weighted arrays, and a level with a single chunk per window returns
/// the window's $R$ as its $A_0$. Within a chunk, $\sum_i i\,V_i$ is the
/// classical descending running sum.
///
/// Mirrors `reduce_level` in the shader.
#[allow(clippy::too_many_arguments)]
pub fn reduce_chunk(
    field: &Field,
    weighted: &[Jacobian],
    plain: Option<&[Jacobian]>,
    window: usize,
    input_len: usize,
    chunk_log2: u32,
    chunk: usize,
) -> (Jacobian, Jacobian) {
    let size = 1usize << chunk_log2;
    let base = window * input_len;
    let start = chunk * size;
    let end = (start + size).min(input_len);
    let count = end - start;

    let mut running = Jacobian::IDENTITY;
    let mut acc = Jacobian::IDENTITY;
    for i in (1..count).rev() {
        running = running.add(&weighted[base + start + i], field);
        acc = acc.add(&running, field);
    }
    let total = running.add(&weighted[base + start], field);
    if let Some(plain) = plain {
        for entry in &plain[base + start..base + end] {
            acc = acc.add(entry, field);
        }
    }
    (acc, total.double_n(chunk_log2, field))
}

/// An execution engine for prepared jobs.
pub trait Backend: Send + Sync + fmt::Debug {
    /// Runs `job` over `field`, returning one Jacobian result per window
    /// (`job.plan.windows` entries).
    fn run(&self, job: &Job, field: &Field) -> Result<Vec<Jacobian>, Error>;
}

/// A backend failure. The accelerator turns these into a CPU fallback.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error(pub String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

/// The CPU reference backend: the kernels above, run over the same
/// buffers a GPU would receive.
#[derive(Debug, Default, Clone, Copy)]
pub struct Reference;

impl Backend for Reference {
    fn run(&self, job: &Job, field: &Field) -> Result<Vec<Jacobian>, Error> {
        let plan = &job.plan;
        let total = plan.total_slots();
        let accumulate =
            |bucket: usize| accumulate_bucket(field, &job.bases, &job.terms, &job.offsets, bucket);

        #[cfg(feature = "multicore")]
        let mut weighted: Vec<Jacobian> = {
            use maybe_rayon::prelude::*;
            (0..total).into_par_iter().map(accumulate).collect()
        };
        #[cfg(not(feature = "multicore"))]
        let mut weighted: Vec<Jacobian> = (0..total).map(accumulate).collect();

        let mut plain: Option<Vec<Jacobian>> = None;
        for level in &plan.levels {
            let windows = plan.windows as usize;
            let chunks = level.chunks as usize;
            let reduce = |index: usize| {
                reduce_chunk(
                    field,
                    &weighted,
                    plain.as_deref(),
                    index / chunks,
                    level.input_len as usize,
                    plan.chunk_log2,
                    index % chunks,
                )
            };
            #[cfg(feature = "multicore")]
            let (next_plain, next_weighted): (Vec<_>, Vec<_>) = {
                use maybe_rayon::prelude::*;
                (0..windows * chunks).into_par_iter().map(reduce).unzip()
            };
            #[cfg(not(feature = "multicore"))]
            let (next_plain, next_weighted): (Vec<_>, Vec<_>) =
                (0..windows * chunks).map(reduce).unzip();
            plain = Some(next_plain);
            weighted = next_weighted;
        }

        match plain {
            Some(results) => Ok(results),
            // No level ran: a one-slot window (impossible under the
            // planner's minimum width) would be its own weighted sum.
            None => Ok(weighted),
        }
    }
}

/// Runs the whole pipeline: plan, prepare, execute, validate, combine.
///
/// Returns `None` when the backend fails or returns a point that is not
/// on the curve; callers fall back to the CPU planner.
pub fn multiexp<C: PastaCurve>(
    backend: &dyn Backend,
    config: &Config,
    scalars: &[C::Scalar],
    bases: &[C::Affine],
) -> Option<C::Point> {
    assert_eq!(scalars.len(), bases.len());
    if scalars.is_empty() {
        return Some(C::Point::identity());
    }
    if scalars.len() > MAX_TERMS {
        return None;
    }
    let plan = Plan::new(scalars.len(), config);
    let job = prepare::<C>(scalars, bases, &plan);
    let windows = backend.run(&job, &C::FIELD).ok()?;
    if windows.len() != plan.windows as usize {
        return None;
    }
    let points = windows.iter().map(C::point).collect::<Option<Vec<_>>>()?;
    Some(C::combine_windows(&points, plan.window_bits))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plans_cover_the_half_width() {
        for terms in [1, 2, 100, 4096, 1 << 20] {
            for chunk_log2 in MIN_CHUNK_LOG2..=MAX_CHUNK_LOG2 {
                let config = Config {
                    chunk_log2,
                    ..Config::default()
                };
                let plan = Plan::new(terms, &config);
                assert!(plan.window_bits >= MIN_WINDOW_BITS);
                assert!(plan.window_bits <= MAX_WINDOW_BITS);
                assert!(plan.windows * plan.window_bits >= HALF_BITS);
                assert!((plan.windows - 1) * plan.window_bits < HALF_BITS);
                assert_eq!(plan.slots, (1 << (plan.window_bits - 1)) + 1);
                assert_eq!(plan.levels.first().map(|l| l.input_len), Some(plan.slots));
                assert_eq!(plan.levels.last().map(|l| l.chunks), Some(1));
                for pair in plan.levels.windows(2) {
                    assert_eq!(pair[0].chunks, pair[1].input_len);
                }
            }
        }
        assert_eq!(Plan::new(4096, &Config::default()).window_bits, 12);
        assert_eq!(
            Plan::new(8, &Config::default()).window_bits,
            MIN_WINDOW_BITS
        );
        let wide = Config {
            window_bits: Some(99),
            ..Config::default()
        };
        assert_eq!(Plan::new(8, &wide).window_bits, MAX_WINDOW_BITS);
    }

    #[test]
    fn signed_digits_reconstruct() {
        let mut digits = [0i32; MAX_WINDOWS];
        for window_bits in MIN_WINDOW_BITS..=MAX_WINDOW_BITS {
            let windows = HALF_BITS.div_ceil(window_bits);
            let half = 1i64 << (window_bits - 1);
            for magnitude in [
                0u128,
                1,
                (1 << 127) - 1,
                (1 << 127) - 2,
                0x5555_5555_5555_5555_5555_5555_5555_5555,
                0x7fff_ffff_ffff_ffff_0000_0000_0000_0001,
                0xf0f0_f0f0_f0f0_f0f0_f0f0 & ((1 << 127) - 1),
            ] {
                signed_digits(magnitude, window_bits, windows, &mut digits);
                // Summed modulo 2^128: a top digit can carry the sum past
                // i128 mid-way even though the total fits.
                let mut value = 0u128;
                for (w, &digit) in digits.iter().enumerate().take(windows as usize) {
                    assert!((digit as i64).abs() <= half);
                    value = value
                        .wrapping_add((digit as i128 as u128).wrapping_shl(window_bits * w as u32));
                }
                assert_eq!(value, magnitude, "c = {window_bits}");
            }
        }
    }
}
