use super::super::{CommitDomains, HashDomains, SinsemillaInstructions};
use super::{NonIdentityEccPoint, SinsemillaChip};
use crate::{
    ecc::{FixedPoints, chip::DoubleAndAdd},
    sinsemilla::primitives::{self as sinsemilla, INV_TWO_POW_K, SINSEMILLA_S},
    utilities::lookup_range_check::PallasLookupRangeCheck,
};

use ff::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Chip, Region, Value},
    plonk::{Assigned, Error},
};

use group::ff::PrimeField;
use pasta_curves::{arithmetic::CurveAffine, pallas};

use std::ops::Deref;

mod first_word_witnesses;
use first_word_witnesses::{MERKLE_FIRST_WORD_WITNESSES, MERKLE_INITIAL_Q};

const FIELD_REPR_LIMBS: usize =
    core::mem::size_of::<<pallas::Base as PrimeField>::Repr>() / core::mem::size_of::<u64>();

#[inline(always)]
fn square_with_runtime_backend(value: &pallas::Base) -> pallas::Base {
    // Method syntax selects `pallas::Base`'s portable inherent square.
    // Trait dispatch selects the configured runtime backend instead.
    Field::square(value)
}

fn decompose_words(value: pallas::Base, num_words: usize) -> Vec<u32> {
    let repr = value.to_repr();
    let mut limbs = [0_u64; FIELD_REPR_LIMBS];
    for (limb, bytes) in limbs
        .iter_mut()
        .zip(repr.as_ref().chunks_exact(core::mem::size_of::<u64>()))
    {
        *limb = u64::from_le_bytes(bytes.try_into().unwrap());
    }

    let word_mask = (1_u64 << sinsemilla::K) - 1;
    (0..num_words)
        .map(|word| {
            let bit_offset = word * sinsemilla::K;
            let limb = bit_offset / u64::BITS as usize;
            let shift = bit_offset % u64::BITS as usize;
            let mut value = limbs[limb] >> shift;
            if shift + sinsemilla::K > u64::BITS as usize {
                value |= limbs[limb + 1] << (u64::BITS as usize - shift);
            }
            (value & word_mask) as u32
        })
        .collect()
}

#[derive(Clone, Copy)]
struct ProjectivePoint {
    x: pallas::Base,
    y: pallas::Base,
    z: pallas::Base,
    z_sq: pallas::Base,
}

#[derive(Clone, Copy)]
struct DoubleAndAddWitness {
    lambda_1_numerator: pallas::Base,
    lambda_2_numerator: pallas::Base,
}

#[derive(Clone, Copy)]
struct CachedFirstWordWitness {
    point: ProjectivePoint,
    witness: DoubleAndAddWitness,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct PreparedHashRound {
    lambda_1: Assigned<pallas::Base>,
    lambda_2: Assigned<pallas::Base>,
    x_a: Assigned<pallas::Base>,
}

#[derive(Clone, Debug)]
pub(crate) struct PreparedHashWitness {
    rounds: Vec<PreparedHashRound>,
    final_y: Assigned<pallas::Base>,
    output_x: pallas::Base,
}

impl PreparedHashWitness {
    pub(crate) fn output_x(&self) -> pallas::Base {
        self.output_x
    }
}

fn assign_hash_rounds(
    region: &mut Region<'_, pallas::Base>,
    double_and_add: &DoubleAndAdd,
    offset: usize,
    len: usize,
    round: impl Fn(usize) -> Value<PreparedHashRound>,
) -> Result<X<pallas::Base>, Error> {
    region.assign_advice_batch(
        |_| "lambda_1",
        double_and_add.lambda_1,
        offset,
        len,
        |row| round(row).map(|round| round.lambda_1),
    )?;
    region.assign_advice_batch(
        |_| "lambda_2",
        double_and_add.lambda_2,
        offset,
        len,
        |row| round(row).map(|round| round.lambda_2),
    )?;

    // Only the final accumulator cell is referenced after assignment.
    region.assign_advice_batch(
        |_| "x_a",
        double_and_add.x_a,
        offset + 1,
        len - 1,
        |row| round(row).map(|round| round.x_a),
    )?;
    region
        .assign_advice(
            || "x_a",
            double_and_add.x_a,
            offset + len,
            || round(len - 1).map(|round| round.x_a),
        )
        .map(X)
}

impl DoubleAndAddWitness {
    fn lambda_1(&self, point: &ProjectivePoint) -> Assigned<pallas::Base> {
        Assigned::Rational(self.lambda_1_numerator, point.z)
    }

    fn lambda_2(&self, point: &ProjectivePoint) -> Assigned<pallas::Base> {
        Assigned::Rational(self.lambda_2_numerator, point.z)
    }
}

impl ProjectivePoint {
    fn from_affine(point: pallas::Affine) -> Self {
        let coordinates = point.coordinates().unwrap();
        Self {
            x: *coordinates.x(),
            y: *coordinates.y(),
            z: pallas::Base::ONE,
            z_sq: pallas::Base::ONE,
        }
    }

    /// Computes witnesses for the incomplete addition `2A + P` while keeping
    /// the accumulator in Jacobian coordinates. The returned rational values
    /// are the same affine values assigned by the circuit's existing witness
    /// flow.
    fn double_and_add(&mut self, (x_p, y_p): (pallas::Base, pallas::Base)) -> DoubleAndAddWitness {
        let z_cubed = self.z_sq * self.z;
        let h = x_p * self.z_sq - self.x;
        let r = y_p * z_cubed - self.y;

        let h_sq = square_with_runtime_backend(&h);
        let h_cubed = h_sq * h;
        let x_h_sq = self.x * h_sq;
        let x_r = square_with_runtime_backend(&r) - h_cubed - x_h_sq.double();
        let d = x_h_sq - x_r;

        let d_sq = square_with_runtime_backend(&d);
        let d_cubed = d_sq * d;
        let y_h_cubed = self.y * h_cubed;
        // Scale lambda_1 by d so it shares z_new as its denominator with
        // lambda_2. The product is also needed for lambda_2's numerator.
        let r_d = r * d;
        let lambda_2_numerator = y_h_cubed.double() - r_d;

        let x_h_sq_d_sq = x_h_sq * d_sq;
        // Since d = x_h_sq - x_r, this saves a field multiplication over
        // computing (x_h_sq + x_r) * d_sq directly.
        let x_new =
            square_with_runtime_backend(&lambda_2_numerator) - x_h_sq_d_sq.double() + d_cubed;
        let y_new = lambda_2_numerator * (x_h_sq_d_sq - x_new) - y_h_cubed * d_cubed;
        let z_new = self.z * h * d;
        let z_new_sq = square_with_runtime_backend(&z_new);

        *self = Self {
            x: x_new,
            y: y_new,
            z: z_new,
            z_sq: z_new_sq,
        };

        DoubleAndAddWitness {
            lambda_1_numerator: r_d,
            lambda_2_numerator,
        }
    }
}

/// Returns whether `initial_q` is the Orchard MerkleCRH domain point whose
/// first-word witnesses are precomputed in [`first_word_witnesses`].
fn has_merkle_initial_q(initial_q: pallas::Affine) -> bool {
    initial_q.raw_coordinates() == MERKLE_INITIAL_Q
}

pub(crate) fn prepare_hash_witness(
    initial_q: pallas::Affine,
    words: &[u32],
) -> Option<PreparedHashWitness> {
    let mut point = ProjectivePoint::from_affine(initial_q);
    let cache_first_word = has_merkle_initial_q(initial_q);
    let mut rounds = Vec::with_capacity(words.len());

    for (row, &word) in words.iter().enumerate() {
        let generator = *SINSEMILLA_S.get(word as usize)?;
        let witness = if row == 0 && cache_first_word {
            let cached = *MERKLE_FIRST_WORD_WITNESSES.get(word as usize)?;
            point = cached.point;
            cached.witness
        } else {
            point.double_and_add(generator)
        };
        rounds.push(PreparedHashRound {
            lambda_1: witness.lambda_1(&point),
            lambda_2: witness.lambda_2(&point),
            x_a: Assigned::Rational(point.x, point.z_sq),
        });
    }

    if point.z.is_zero_vartime() {
        return None;
    }

    let output_x = Assigned::Rational(point.x, point.z_sq).evaluate();
    rounds.last_mut()?.x_a = Assigned::Trivial(output_x);
    Some(PreparedHashWitness {
        rounds,
        final_y: Assigned::Rational(point.y, point.z_sq * point.z),
        output_x,
    })
}

/// `EccPointQ` can hold either a public or a private ECC Point
#[cfg(test)]
enum EccPointQ {
    PublicPoint(pallas::Affine),
    PrivatePoint(NonIdentityEccPoint),
}

impl<Hash, Commit, Fixed, Lookup> SinsemillaChip<Hash, Commit, Fixed, Lookup>
where
    Hash: HashDomains<pallas::Affine>,
    Fixed: FixedPoints<pallas::Affine>,
    Commit: CommitDomains<pallas::Affine, Fixed, Hash>,
    Lookup: PallasLookupRangeCheck,
{
    /// [Specification](https://p.z.cash/halo2-0.1:sinsemilla-constraints?partial).
    #[allow(non_snake_case)]
    #[allow(clippy::type_complexity)]
    pub(super) fn hash_message(
        &self,
        region: &mut Region<'_, pallas::Base>,
        Q: pallas::Affine,
        message: &<Self as SinsemillaInstructions<
            pallas::Affine,
            { sinsemilla::K },
            { sinsemilla::C },
        >>::Message,
    ) -> Result<
        (
            NonIdentityEccPoint,
            Vec<Vec<AssignedCell<pallas::Base, pallas::Base>>>,
        ),
        Error,
    > {
        let projective = Value::known(ProjectivePoint::from_affine(Q));
        // An Orchard MerkleCRH message starts with the 10-bit encoding of its
        // layer index, so its first Sinsemilla word is cached.
        let cache_first_word = has_merkle_initial_q(Q);
        let (offset, x_a, y_a) = self.public_q_initialization(region, Q)?;

        let (x_a, y_a, zs_sum) = self.hash_all_pieces(
            region,
            offset,
            message,
            x_a,
            y_a,
            Some(projective),
            cache_first_word,
            None,
        )?;

        #[cfg(test)]
        self.check_hash_result(EccPointQ::PublicPoint(Q), message, &x_a, &y_a);

        x_a.value()
            .zip(y_a.value())
            .error_if_known_and(|(x_a, y_a)| x_a.is_zero_vartime() || y_a.is_zero_vartime())?;
        Ok((
            NonIdentityEccPoint::from_coordinates_unchecked(x_a.0, y_a),
            zs_sum,
        ))
    }

    pub(super) fn hash_message_prepared(
        &self,
        region: &mut Region<'_, pallas::Base>,
        q: pallas::Affine,
        message: &<Self as SinsemillaInstructions<
            pallas::Affine,
            { sinsemilla::K },
            { sinsemilla::C },
        >>::Message,
        prepared: Value<&PreparedHashWitness>,
    ) -> Result<
        (
            NonIdentityEccPoint,
            Vec<Vec<AssignedCell<pallas::Base, pallas::Base>>>,
        ),
        Error,
    > {
        let (offset, x_a, y_a) = self.public_q_initialization(region, q)?;
        let (x_a, y_a, zs_sum) = self.hash_all_pieces(
            region,
            offset,
            message,
            x_a,
            y_a,
            None,
            false,
            Some(prepared),
        )?;

        x_a.value()
            .zip(y_a.value())
            .error_if_known_and(|(x_a, y_a)| x_a.is_zero_vartime() || y_a.is_zero_vartime())?;
        Ok((
            NonIdentityEccPoint::from_coordinates_unchecked(x_a.0, y_a),
            zs_sum,
        ))
    }

    /// [Specification](https://p.z.cash/halo2-0.1:sinsemilla-constraints?partial).
    #[allow(non_snake_case)]
    #[allow(clippy::type_complexity)]
    pub(super) fn hash_message_with_private_init(
        &self,
        region: &mut Region<'_, pallas::Base>,
        Q: &NonIdentityEccPoint,
        message: &<Self as SinsemillaInstructions<
            pallas::Affine,
            { sinsemilla::K },
            { sinsemilla::C },
        >>::Message,
    ) -> Result<
        (
            NonIdentityEccPoint,
            Vec<Vec<AssignedCell<pallas::Base, pallas::Base>>>,
        ),
        Error,
    > {
        if !self.config().allow_init_from_private_point {
            return Err(Error::IllegalHashFromPrivatePoint);
        }

        let (offset, x_a, y_a) = self.private_q_initialization(region, Q)?;

        let (x_a, y_a, zs_sum) =
            self.hash_all_pieces(region, offset, message, x_a, y_a, None, false, None)?;

        #[cfg(test)]
        self.check_hash_result(EccPointQ::PrivatePoint(Q.clone()), message, &x_a, &y_a);

        x_a.value()
            .error_if_known_and(|x_a| x_a.is_zero_vartime())?;
        y_a.value()
            .error_if_known_and(|y_a| y_a.is_zero_vartime())?;
        Ok((
            NonIdentityEccPoint::from_coordinates_unchecked(x_a.0, y_a),
            zs_sum,
        ))
    }

    #[allow(non_snake_case)]
    /// Assign the coordinates of the initial public point `Q`.
    ///
    /// If allow_init_from_private_point is not set,
    /// | offset | x_A | q_sinsemilla4 | fixed_y_q |
    /// --------------------------------------
    /// |   0    | x_Q |   1           |   y_Q     |
    ///
    /// If allow_init_from_private_point is set,
    /// | offset | x_A | x_P | q_sinsemilla4 |
    /// --------------------------------------
    /// |   0    |     | y_Q |               |
    /// |   1    | x_Q |     |         1     |
    fn public_q_initialization(
        &self,
        region: &mut Region<'_, pallas::Base>,
        Q: pallas::Affine,
    ) -> Result<(usize, X<pallas::Base>, Y<pallas::Base>), Error> {
        let config = self.config().clone();
        let mut offset = 0;

        // Get the `x`- and `y`-coordinates of the starting `Q` base.
        let x_q = *Q.coordinates().unwrap().x();
        let y_q = *Q.coordinates().unwrap().y();

        // Constrain the initial x_a, lambda_1, lambda_2, x_p using the q_sinsemilla4
        // selector.
        let y_a: Y<pallas::Base> = if config.allow_init_from_private_point {
            // Enable `q_sinsemilla4` on the second row.
            config.q_sinsemilla4.enable(region, offset + 1)?;
            let y_a: AssignedCell<Assigned<pallas::Base>, pallas::Base> = region
                .assign_advice_from_constant(
                    || "variable y_q",
                    config.double_and_add.x_p,
                    offset,
                    y_q.into(),
                )?;
            offset += 1;
            y_a.value_field().into()
        } else {
            // Enable `q_sinsemilla4` on the first row.
            config.q_sinsemilla4.enable(region, offset)?;
            region.assign_fixed(
                || "fixed y_q",
                config.fixed_y_q,
                offset,
                || Value::known(y_q),
            )?;

            Value::known(y_q.into()).into()
        };

        // Constrain the initial x_q to equal the x-coordinate of the domain's `Q`.
        let x_a: X<pallas::Base> = {
            let x_a = region.assign_advice_from_constant(
                || "variable x_q",
                config.double_and_add.x_a,
                offset,
                x_q.into(),
            )?;

            x_a.into()
        };

        Ok((offset, x_a, y_a))
    }

    #[allow(non_snake_case)]
    /// Assign the coordinates of the initial private point `Q`
    ///
    /// | offset | x_A | x_P | q_sinsemilla4 |
    /// --------------------------------------
    /// |   0    |     | y_Q |               |
    /// |   1    | x_Q |     |         1     |
    fn private_q_initialization(
        &self,
        region: &mut Region<'_, pallas::Base>,
        Q: &NonIdentityEccPoint,
    ) -> Result<(usize, X<pallas::Base>, Y<pallas::Base>), Error> {
        let config = self.config().clone();

        if !config.allow_init_from_private_point {
            return Err(Error::IllegalHashFromPrivatePoint);
        }

        // Assign `x_Q` and `y_Q` in the region and constrain the initial x_a, lambda_1, lambda_2,
        // x_p, y_Q using the q_sinsemilla4 selector.
        let y_a: Y<pallas::Base> = {
            // Enable `q_sinsemilla4` on the second row.
            config.q_sinsemilla4.enable(region, 1)?;
            let q_y: AssignedCell<Assigned<pallas::Base>, pallas::Base> = Q.y().into();
            let y_a: AssignedCell<Assigned<pallas::Base>, pallas::Base> =
                q_y.copy_advice(|| "fixed y_q", region, config.double_and_add.x_p, 0)?;

            y_a.value_field().into()
        };

        let x_a: X<pallas::Base> = {
            let q_x: AssignedCell<Assigned<pallas::Base>, pallas::Base> = Q.x().into();
            let x_a = q_x.copy_advice(|| "fixed x_q", region, config.double_and_add.x_a, 1)?;

            x_a.into()
        };

        Ok((1, x_a, y_a))
    }

    #[allow(clippy::type_complexity)]
    /// Hash `message` from the initial point `Q`.
    fn hash_all_pieces(
        &self,
        region: &mut Region<'_, pallas::Base>,
        mut offset: usize,
        message: &<Self as SinsemillaInstructions<
            pallas::Affine,
            { sinsemilla::K },
            { sinsemilla::C },
        >>::Message,
        mut x_a: X<pallas::Base>,
        mut y_a: Y<pallas::Base>,
        mut projective: Option<Value<ProjectivePoint>>,
        mut cache_first_word: bool,
        prepared: Option<Value<&PreparedHashWitness>>,
    ) -> Result<
        (
            X<pallas::Base>,
            AssignedCell<Assigned<pallas::Base>, pallas::Base>,
            Vec<Vec<AssignedCell<pallas::Base, pallas::Base>>>,
        ),
        Error,
    > {
        let config = self.config().clone();

        let mut zs_sum: Vec<Vec<AssignedCell<pallas::Base, pallas::Base>>> = Vec::new();

        // Hash each piece in the message.
        let mut prepared_offset = 0;
        for (idx, piece) in message.iter().enumerate() {
            let final_piece = idx == message.len() - 1;

            // The value of the accumulator after this piece is processed.
            let (x, y, zs, next_projective) = self.hash_piece(
                region,
                offset,
                piece,
                x_a,
                y_a,
                final_piece,
                projective,
                cache_first_word,
                prepared.map(|prepared| {
                    prepared.map(|prepared| {
                        &prepared.rounds[prepared_offset..prepared_offset + piece.num_words()]
                    })
                }),
            )?;
            cache_first_word = false;

            // Since each message word takes one row to process, we increase
            // the offset by `piece.num_words` on each iteration.
            offset += piece.num_words();

            // Update the accumulator to the latest value.
            x_a = x;
            y_a = y;
            projective = next_projective;
            zs_sum.push(zs);
            prepared_offset += piece.num_words();
        }

        // The projective path does not need an affine y-coordinate between
        // rounds. Derive it once, when the circuit finally assigns it.
        if let Some(prepared) = prepared {
            y_a = prepared.map(|prepared| prepared.final_y).into();
        } else if let Some(point) = projective {
            point.error_if_known_and(|point| point.z.is_zero_vartime())?;
            y_a = point
                .map(|point| Assigned::Rational(point.y, point.z_sq * point.z))
                .into();
        }

        // Assign the final y_a.
        let y_a = {
            // Assign the final y_a.
            let y_a_cell =
                region.assign_advice(|| "y_a", config.double_and_add.lambda_1, offset, || y_a.0)?;

            // Assign lambda_2 and x_p zero values since they are queried
            // in the gate. (The actual values do not matter since they are
            // multiplied by zero.)
            {
                region.assign_advice(
                    || "dummy lambda2",
                    config.double_and_add.lambda_2,
                    offset,
                    || Value::known(pallas::Base::zero()),
                )?;
                region.assign_advice(
                    || "dummy x_p",
                    config.double_and_add.x_p,
                    offset,
                    || Value::known(pallas::Base::zero()),
                )?;
            }

            y_a_cell
        };

        Ok((x_a, y_a, zs_sum))
    }

    #[allow(clippy::too_many_arguments, clippy::type_complexity)]
    /// Hashes a message piece containing `piece.length` number of `K`-bit words.
    ///
    /// To avoid a duplicate assignment, the accumulator x-coordinate provided
    /// by the caller is not copied. This only works because `hash_piece()` is
    /// an internal API. Before this call to `hash_piece()`, x_a MUST have been
    /// already assigned within this region at the correct offset.
    fn hash_piece(
        &self,
        region: &mut Region<'_, pallas::Base>,
        offset: usize,
        piece: &<Self as SinsemillaInstructions<
            pallas::Affine,
            { sinsemilla::K },
            { sinsemilla::C },
        >>::MessagePiece,
        mut x_a: X<pallas::Base>,
        mut y_a: Y<pallas::Base>,
        final_piece: bool,
        mut projective: Option<Value<ProjectivePoint>>,
        cache_first_word: bool,
        prepared: Option<Value<&[PreparedHashRound]>>,
    ) -> Result<
        (
            X<pallas::Base>,
            Y<pallas::Base>,
            Vec<AssignedCell<pallas::Base, pallas::Base>>,
            Option<Value<ProjectivePoint>>,
        ),
        Error,
    > {
        let config = self.config().clone();

        // Selector assignments
        {
            // Enable `q_sinsemilla1` selector on every row.
            for row in 0..piece.num_words() {
                config.q_sinsemilla1.enable(region, offset + row)?;
            }

            // Set `q_sinsemilla2` fixed column to 1 on every row but the last.
            for row in 0..(piece.num_words() - 1) {
                region.assign_fixed(
                    || "q_s2 = 1",
                    config.q_sinsemilla2,
                    offset + row,
                    || Value::known(pallas::Base::one()),
                )?;
            }

            // Set `q_sinsemilla2` fixed column to 0 on the last row if this is
            // not the final piece, or to 2 on the last row of the final piece.
            region.assign_fixed(
                || {
                    if final_piece {
                        "q_s2 for final piece"
                    } else {
                        "q_s2 between pieces"
                    }
                },
                config.q_sinsemilla2,
                offset + piece.num_words() - 1,
                || {
                    Value::known(if final_piece {
                        pallas::Base::from(2)
                    } else {
                        pallas::Base::zero()
                    })
                },
            )?;
        }

        let words = piece
            .field_elem()
            .map(|value| decompose_words(value, piece.num_words()));

        // Convert `words` from `Value<Vec<u32>>` to `Vec<Value<u32>>`
        let words = words.transpose_vec(piece.num_words());

        // Decompose message piece into `K`-bit pieces with a running sum `z`.
        let zs = {
            let mut zs = Vec::with_capacity(piece.num_words() + 1);

            // Copy message and initialize running sum `z` to decompose message in-circuit
            let initial_z = piece.cell_value().copy_advice(
                || "z_0 (copy of message piece)",
                region,
                config.bits,
                offset,
            )?;
            zs.push(initial_z);

            // Assign cumulative sum such that for 0 <= i < n,
            //          z_i = 2^K * z_{i + 1} + m_{i + 1}
            // => z_{i + 1} = (z_i - m_{i + 1}) / 2^K
            //
            // For a message piece m = m_1 + 2^K m_2 + ... + 2^{K(n-1)} m_n}, initialize z_0 = m.
            // We end up with z_n = 0. (z_n is not directly encoded as a cell value;
            // it is implicitly taken as 0 by adjusting the definition of m_{i+1}.)
            let mut z = piece.field_elem();
            let inv_2_k = Value::known(pallas::Base::from_repr(INV_TWO_POW_K).unwrap());

            // We do not assign the final z_n as it is constrained to be zero.
            for (idx, word) in words[0..(words.len() - 1)].iter().enumerate() {
                let word = word.map(|word| pallas::Base::from(word as u64));
                // z_{i + 1} = (z_i - m_{i + 1}) / 2^K
                z = (z - word) * inv_2_k;
                let cell = region.assign_advice(
                    || format!("z_{:?}", idx + 1),
                    config.bits,
                    offset + idx + 1,
                    || z,
                )?;
                zs.push(cell)
            }

            zs
        };

        // The accumulator x-coordinate provided by the caller MUST have been assigned
        // within this region.

        region.assign_advice_batch(
            |_| "x_p",
            config.double_and_add.x_p,
            offset,
            words.len(),
            |row| words[row].map(|word| SINSEMILLA_S[word as usize].0),
        )?;

        if let Some(prepared) = prepared {
            let x_a =
                assign_hash_rounds(region, &config.double_and_add, offset, words.len(), |row| {
                    prepared.map(|prepared| prepared[row])
                })?;

            return Ok((x_a, y_a, zs, projective));
        }

        if let Some(point) = projective.as_mut() {
            let mut rounds = Vec::with_capacity(words.len());
            for (row, word) in words.iter().enumerate() {
                let r#gen = word.map(|word| SINSEMILLA_S[word as usize]);
                let witness = if row == 0 && cache_first_word {
                    let (next_point, witness) = point
                        .as_ref()
                        .zip(*word)
                        .zip(r#gen)
                        .map(|((point, word), r#gen)| {
                            MERKLE_FIRST_WORD_WITNESSES
                                .get(word as usize)
                                .copied()
                                .unwrap_or_else(|| {
                                    // Preserve generic behavior if the Merkle
                                    // domain is used with another message.
                                    let mut point = *point;
                                    let witness = point.double_and_add(r#gen);
                                    CachedFirstWordWitness { point, witness }
                                })
                        })
                        .map(|cached| (cached.point, cached.witness))
                        .unzip();
                    *point = next_point;
                    witness
                } else {
                    point
                        .as_mut()
                        .zip(r#gen)
                        .map(|(point, r#gen)| point.double_and_add(r#gen))
                };

                rounds.push(
                    witness
                        .as_ref()
                        .zip(point.as_ref())
                        .map(|(witness, point)| PreparedHashRound {
                            lambda_1: witness.lambda_1(point),
                            lambda_2: witness.lambda_2(point),
                            x_a: Assigned::Rational(point.x, point.z_sq),
                        }),
                );
            }

            let x_a = assign_hash_rounds(
                region,
                &config.double_and_add,
                offset,
                rounds.len(),
                |row| rounds[row],
            )?;

            return Ok((x_a, y_a, zs, projective));
        }

        for (row, word) in words.iter().enumerate() {
            let r#gen = word.map(|word| SINSEMILLA_S[word as usize]);
            let x_p = r#gen.map(|r#gen| r#gen.0);
            let y_p = r#gen.map(|r#gen| r#gen.1);

            // Compute and assign `lambda_1`
            let lambda_1 = {
                let lambda_1 = (y_a.0 - y_p) * (x_a.value() - x_p).invert();

                // Assign lambda_1
                region.assign_advice(
                    || "lambda_1",
                    config.double_and_add.lambda_1,
                    offset + row,
                    || lambda_1,
                )?;

                lambda_1
            };

            // Compute `x_r`
            let x_r = lambda_1.square() - x_a.value() - x_p;

            // Compute and assign `lambda_2`
            let lambda_2 = {
                let lambda_2 = y_a.0.double() * (x_a.value() - x_r).invert() - lambda_1;

                region.assign_advice(
                    || "lambda_2",
                    config.double_and_add.lambda_2,
                    offset + row,
                    || lambda_2,
                )?;

                lambda_2
            };

            // Compute and assign `x_a` for the next row.
            let x_a_new: X<pallas::Base> = {
                let x_a_new = lambda_2.square() - x_a.value() - x_r;

                let x_a_cell = region.assign_advice(
                    || "x_a",
                    config.double_and_add.x_a,
                    offset + row + 1,
                    || x_a_new,
                )?;

                x_a_cell.into()
            };

            // Compute y_a for the next row.
            let y_a_new: Y<pallas::Base> =
                (lambda_2 * (x_a.value() - x_a_new.value()) - y_a.0).into();

            // Update the mutable `x_a`, `y_a` variables.
            x_a = x_a_new;
            y_a = y_a_new;
        }

        Ok((x_a, y_a, zs, projective))
    }

    #[cfg(test)]
    #[allow(non_snake_case)]
    fn check_hash_result(
        &self,
        Q: EccPointQ,
        message: &<Self as SinsemillaInstructions<
            pallas::Affine,
            { sinsemilla::K },
            { sinsemilla::C },
        >>::Message,
        x_a: &X<pallas::Base>,
        y_a: &AssignedCell<Assigned<pallas::Base>, pallas::Base>,
    ) {
        // Check equivalence to result from primitives::sinsemilla::hash_to_point
        {
            use crate::sinsemilla::primitives::{K, S_PERSONALIZATION, lebs2ip_k};

            use group::ff::PrimeFieldBits;
            use group::{Curve, CurveAffine as _};
            use pasta_curves::arithmetic::CurveExt;

            let field_elems: Value<Vec<_>> = message
                .iter()
                .map(|piece| piece.field_elem().map(|elem| (elem, piece.num_words())))
                .collect();

            let value_Q = match Q {
                EccPointQ::PublicPoint(p) => Value::known(p),
                EccPointQ::PrivatePoint(p) => p.point(),
            };

            field_elems
                .zip(x_a.value().zip(y_a.value()))
                .zip(value_Q)
                .assert_if_known(|((field_elems, (x_a, y_a)), value_Q)| {
                    // Get message as a bitstring.
                    let bitstring: Vec<bool> = field_elems
                        .iter()
                        .flat_map(|(elem, num_words)| {
                            elem.to_le_bits().into_iter().take(K * num_words)
                        })
                        .collect();

                    let hasher_S = pallas::Point::hash_to_curve(S_PERSONALIZATION);
                    let S = |chunk: &[bool]| {
                        hasher_S(
                            &lebs2ip_k(chunk.try_into().expect("correct length")).to_le_bytes(),
                        )
                    };

                    // We can use complete addition here because it differs from
                    // incomplete addition with negligible probability.
                    let expected_point = bitstring
                        .chunks(K)
                        .fold(value_Q.to_curve(), |acc, chunk| (acc + S(chunk)) + acc);
                    let actual_point =
                        pallas::Affine::from_xy(x_a.evaluate(), y_a.evaluate()).unwrap();
                    expected_point.to_affine() == actual_point
                });
        }
    }
}

/// The x-coordinate of the accumulator in a Sinsemilla hash instance.
struct X<F: Field>(AssignedCell<Assigned<F>, F>);

impl<F: Field> From<AssignedCell<Assigned<F>, F>> for X<F> {
    fn from(cell_value: AssignedCell<Assigned<F>, F>) -> Self {
        X(cell_value)
    }
}

impl<F: Field> Deref for X<F> {
    type Target = AssignedCell<Assigned<F>, F>;

    fn deref(&self) -> &AssignedCell<Assigned<F>, F> {
        &self.0
    }
}

/// The y-coordinate of the accumulator in a Sinsemilla hash instance.
///
/// This is never actually witnessed until the last round, since it
/// can be derived from other variables. Thus it only exists as a field
/// element, not a `CellValue`.
struct Y<F: Field>(Value<Assigned<F>>);

impl<F: Field> From<Value<Assigned<F>>> for Y<F> {
    fn from(value: Value<Assigned<F>>) -> Self {
        Y(value)
    }
}

impl<F: Field> Deref for Y<F> {
    type Target = Value<Assigned<F>>;

    fn deref(&self) -> &Value<Assigned<F>> {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ProjectivePoint, decompose_words,
        first_word_witnesses::{MERKLE_FIRST_WORD_COUNT, MERKLE_FIRST_WORD_WITNESSES},
        has_merkle_initial_q,
    };
    use crate::sinsemilla::primitives::{K, SINSEMILLA_S, lebs2ip_k};

    use group::{
        Curve, Group,
        ff::{Field, PrimeField, PrimeFieldBits},
    };
    use halo2_proofs::plonk::Assigned;
    use pasta_curves::{arithmetic::CurveAffine, pallas};

    #[test]
    fn cached_merkle_first_word_witnesses_match_arithmetic() {
        use crate::sinsemilla::{merkle::MERKLE_CRH_PERSONALIZATION, primitives::HashDomain};

        let initial_q = HashDomain::new(MERKLE_CRH_PERSONALIZATION).Q().to_affine();
        assert!(has_merkle_initial_q(initial_q));
        assert!(!has_merkle_initial_q(
            pallas::Point::generator().to_affine()
        ));
        assert!(!has_merkle_initial_q(pallas::Point::identity().to_affine()));

        for (word, cached) in MERKLE_FIRST_WORD_WITNESSES.iter().enumerate() {
            let mut point = ProjectivePoint::from_affine(initial_q);
            let witness = point.double_and_add(SINSEMILLA_S[word]);
            assert_eq!(cached.point.x, point.x);
            assert_eq!(cached.point.y, point.y);
            assert_eq!(cached.point.z, point.z);
            assert_eq!(cached.point.z_sq, point.z_sq);
            assert_eq!(
                cached.witness.lambda_1_numerator,
                witness.lambda_1_numerator
            );
            assert_eq!(
                cached.witness.lambda_2_numerator,
                witness.lambda_2_numerator
            );
        }
        assert_eq!(MERKLE_FIRST_WORD_WITNESSES.len(), MERKLE_FIRST_WORD_COUNT);
    }

    #[test]
    fn word_decomposition_matches_bit_decomposition() {
        let values = [
            pallas::Base::ZERO,
            pallas::Base::ONE,
            pallas::Base::from_raw([u64::MAX, u64::MAX, u64::MAX, 0x1234]),
        ];
        let max_words = pallas::Base::CAPACITY as usize / K;

        for value in values {
            let bits = value.to_le_bits();
            for num_words in [1, 2, max_words] {
                let expected = bits[..K * num_words]
                    .chunks_exact(K)
                    .map(|chunk| lebs2ip_k(std::array::from_fn(|i| chunk[i])))
                    .collect::<Vec<_>>();
                assert_eq!(decompose_words(value, num_words), expected);
            }
        }
    }

    #[test]
    fn projective_witness_matches_curve_arithmetic() {
        let mut expected = pallas::Point::generator();
        let mut point = ProjectivePoint::from_affine(expected.to_affine());

        for generator in SINSEMILLA_S.iter().copied() {
            let accumulator = expected.to_affine();
            let accumulator = accumulator.coordinates().unwrap();
            let generator = pallas::Affine::from_xy(generator.0, generator.1).unwrap();
            let generator_coordinates = generator.coordinates().unwrap();
            let lambda_1 = (*generator_coordinates.y() - *accumulator.y())
                * (*generator_coordinates.x() - *accumulator.x())
                    .invert()
                    .unwrap();
            let intermediate = (expected + pallas::Point::from(generator)).to_affine();
            let intermediate = intermediate.coordinates().unwrap();
            let lambda_2 = (*accumulator.y() - *intermediate.y())
                * (*accumulator.x() - *intermediate.x()).invert().unwrap();

            let witness =
                point.double_and_add((*generator_coordinates.x(), *generator_coordinates.y()));
            assert!(!point.z.is_zero_vartime());
            assert_eq!(witness.lambda_1(&point).evaluate(), lambda_1);
            assert_eq!(witness.lambda_2(&point).evaluate(), lambda_2);

            expected = expected.double() + pallas::Point::from(generator);
            let expected = expected.to_affine();
            let coordinates = expected.coordinates().unwrap();
            assert_eq!(
                Assigned::Rational(point.x, point.z_sq).evaluate(),
                *coordinates.x()
            );

            let z_sq = point.z.square();
            assert_eq!(point.z_sq, z_sq);
            assert_eq!(point.x, *coordinates.x() * z_sq);
            assert_eq!(point.y, *coordinates.y() * z_sq * point.z);
        }
    }
}
