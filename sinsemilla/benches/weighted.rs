use std::hint::black_box;
use std::mem;

use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput};
use sinsemilla::{weighted::UncheckedFixedLengthHashDomain, HashDomain, K};

const MERKLE_WORDS: usize = 52;
const MERKLE_BITS: usize = MERKLE_WORDS * K;
const MERKLE_DOMAIN: &str = "z.cash:Orchard-MerkleCRH";
const FIXTURE_SEED: u64 = 0x5369_6e73_656d_696c;
const VARIED_MESSAGES: usize = 512;
/// Streaming this many bytes between iterations displaces the weighted table
/// (and the baseline generator table) from typical CPU cache hierarchies.
const CACHE_DISPLACEMENT_BYTES: usize = 64 << 20;
/// Cold-cache samples pay an unmeasured displacement pass per iteration, so
/// keep the sample count modest.
const COLD_SAMPLE_SIZE: usize = 20;

fn displace_cache(buffer: &mut [u64]) {
    for (index, slot) in buffer.iter_mut().enumerate() {
        *slot = slot.wrapping_add(index as u64);
    }
    black_box(buffer.last());
}

fn message_words(state: &mut u64) -> [u16; MERKLE_WORDS] {
    core::array::from_fn(|_| {
        *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut value = *state;
        value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        ((value ^ (value >> 31)) & 0x3ff) as u16
    })
}

fn words_to_bits(words: &[u16]) -> Vec<bool> {
    words
        .iter()
        .flat_map(|word| (0..K).map(move |bit| ((word >> bit) & 1) == 1))
        .collect()
}

fn benchmark_weighted(c: &mut Criterion) {
    let mut state = FIXTURE_SEED;
    let words = message_words(&mut state);
    let bits = words_to_bits(&words);
    let varied_bits: Vec<_> = (0..VARIED_MESSAGES)
        .map(|_| words_to_bits(&message_words(&mut state)))
        .collect();
    let domain = HashDomain::new(MERKLE_DOMAIN);
    let weighted = UncheckedFixedLengthHashDomain::<MERKLE_WORDS>::new(&domain);

    let expected = domain.hash_to_point(bits.iter().copied());
    let actual = weighted.hash_to_point(bits.iter().copied());
    assert!(bool::from(expected.is_some()));
    assert_eq!(expected.unwrap(), actual);
    for bits in &varied_bits {
        let expected = domain.hash_to_point(bits.iter().copied());
        let actual = weighted.hash_to_point(bits.iter().copied());
        assert!(bool::from(expected.is_some()));
        assert_eq!(expected.unwrap(), actual);
    }

    let mut group = c.benchmark_group("sinsemilla-merkle-52-words-single");
    group.throughput(Throughput::Elements(MERKLE_WORDS as u64));

    group.bench_with_input(
        BenchmarkId::new("pr67-double-and-add", MERKLE_BITS),
        &bits,
        |bencher, bits| {
            bencher.iter(|| black_box(domain.hash_to_point(bits.iter().copied())));
        },
    );
    group.bench_with_input(
        BenchmarkId::new("position-weighted-unchecked", MERKLE_BITS),
        &bits,
        |bencher, bits| {
            bencher.iter(|| black_box(weighted.hash_to_point(bits.iter().copied())));
        },
    );
    group.finish();

    let mut group = c.benchmark_group("sinsemilla-merkle-52-words-varied");
    group.throughput(Throughput::Elements(VARIED_MESSAGES as u64));

    group.bench_function("pr67-double-and-add", |bencher| {
        bencher.iter(|| {
            for bits in &varied_bits {
                black_box(domain.hash_to_point(bits.iter().copied()));
            }
        });
    });
    group.bench_function("position-weighted-unchecked", |bencher| {
        bencher.iter(|| {
            for bits in &varied_bits {
                black_box(weighted.hash_to_point(bits.iter().copied()));
            }
        });
    });
    group.finish();

    // Displace the cache before every sample so the single-hash comparison
    // also covers table traffic that the warm lanes above amortize away.
    let mut displacement = vec![0_u64; CACHE_DISPLACEMENT_BYTES / mem::size_of::<u64>()];
    let mut group = c.benchmark_group("sinsemilla-merkle-52-words-cold");
    group.throughput(Throughput::Elements(MERKLE_WORDS as u64));
    group.sample_size(COLD_SAMPLE_SIZE);

    group.bench_with_input(
        BenchmarkId::new("pr67-double-and-add", MERKLE_BITS),
        &bits,
        |bencher, bits| {
            bencher.iter_batched(
                || displace_cache(&mut displacement),
                |()| black_box(domain.hash_to_point(bits.iter().copied())),
                BatchSize::PerIteration,
            );
        },
    );
    group.bench_with_input(
        BenchmarkId::new("position-weighted-unchecked", MERKLE_BITS),
        &bits,
        |bencher, bits| {
            bencher.iter_batched(
                || displace_cache(&mut displacement),
                |()| black_box(weighted.hash_to_point(bits.iter().copied())),
                BatchSize::PerIteration,
            );
        },
    );
    group.finish();

    c.bench_function(
        "sinsemilla-merkle-unchecked-weighted-table-construction",
        |bencher| {
            bencher
                .iter(|| black_box(UncheckedFixedLengthHashDomain::<MERKLE_WORDS>::new(&domain)));
        },
    );
}

criterion_group!(benches, benchmark_weighted);
criterion_main!(benches);
