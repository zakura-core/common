use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use orchard::bundle::testing::arb_bundle;
use proptest::{
    strategy::{Strategy, ValueTree},
    test_runner::TestRunner,
};
use std::hint::black_box;

/// One and many actions separate point conversion from commitment summation.
const ACTION_COUNTS: [usize; 3] = [1, 8, 32];
/// Zero and a public fee exercise both short value-balance paths.
const BALANCES: [i64; 2] = [0, 50_000];

fn binding_key(c: &mut Criterion) {
    let mut runner = TestRunner::deterministic();
    let mut group = c.benchmark_group("orchard_bundle_binding_key");
    for n in ACTION_COUNTS {
        let fixture = arb_bundle(n).new_tree(&mut runner).unwrap().current();
        for balance in BALANCES {
            let bundle = fixture
                .clone()
                .try_map_value_balance(|_| Ok::<_, ()>(balance))
                .unwrap();
            group.bench_with_input(
                BenchmarkId::new(format!("balance_{balance}"), n),
                &bundle,
                |b, bundle| b.iter(|| black_box(bundle).binding_validating_key()),
            );
        }
    }
    group.finish();
}
criterion_group!(benches, binding_key);
criterion_main!(benches);
