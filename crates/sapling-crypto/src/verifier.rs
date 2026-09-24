use bellman::groth16::Proof;
use bls12_381::Bls12;
use group::{Curve, ff::PrimeField};
use redjubjub::{Binding, SpendAuth};

use crate::{
    note::ExtractedNoteCommitment,
    value::{CommitmentSum, ValueCommitment},
};

mod single;
pub use single::SaplingVerificationContext;

mod batch;
pub use batch::BatchValidator;

// A nullifier fills one scalar-capacity public input and two bits of the next.
const NULLIFIER_LOW_BITS: u32 = bls12_381::Scalar::CAPACITY;
const _: () = assert!(NULLIFIER_LOW_BITS == 254);

fn pack_nullifier(nullifier: &[u8; 32]) -> [bls12_381::Scalar; 2] {
    const SPLIT_BYTE: usize = (NULLIFIER_LOW_BITS / 8) as usize;
    const SPLIT_BITS: u8 = (NULLIFIER_LOW_BITS % 8) as u8;

    let mut low = *nullifier;
    let high = low[SPLIT_BYTE] >> SPLIT_BITS;
    low[SPLIT_BYTE] &= (1 << SPLIT_BITS) - 1;

    [
        bls12_381::Scalar::from_repr(low).unwrap(),
        bls12_381::Scalar::from(u64::from(high)),
    ]
}

/// A context object for verifying the Sapling components of a Zcash transaction.
struct SaplingVerificationContextInner {
    // (sum of the Spend value commitments) - (sum of the Output value commitments)
    cv_sum: CommitmentSum,
}

impl SaplingVerificationContextInner {
    /// Construct a new context to be used with a single transaction.
    fn new() -> Self {
        SaplingVerificationContextInner {
            cv_sum: CommitmentSum::zero(),
        }
    }

    /// Perform consensus checks on a Sapling SpendDescription, while
    /// accumulating its value commitment inside the context for later use.
    #[allow(clippy::too_many_arguments)]
    fn check_spend<C>(
        &mut self,
        cv: &ValueCommitment,
        anchor: bls12_381::Scalar,
        nullifier: &[u8; 32],
        rk: &redjubjub::VerificationKey<SpendAuth>,
        zkproof: Proof<Bls12>,
        verifier_ctx: &mut C,
        spend_auth_sig_verifier: impl FnOnce(&mut C, &redjubjub::VerificationKey<SpendAuth>) -> bool,
        proof_verifier: impl FnOnce(&mut C, Proof<Bls12>, [bls12_381::Scalar; 7]) -> bool,
    ) -> bool {
        // The "cv is not small order" happens when a SpendDescription is deserialized.
        // This happens when transactions or blocks are received over the network, or when
        // mined blocks are introduced via the `submitblock` RPC method on full nodes.
        let rk_affine = jubjub::AffinePoint::from_bytes((*rk).into()).unwrap();
        if rk_affine.is_small_order().into() {
            return false;
        }

        // Accumulate the value commitment in the context
        self.cv_sum += cv;

        // Verify the spend_auth_sig
        if !spend_auth_sig_verifier(verifier_ctx, rk) {
            return false;
        }

        // Construct public input for circuit
        let mut public_input = [bls12_381::Scalar::zero(); 7];
        {
            let affine = rk_affine;
            let (u, v) = (affine.get_u(), affine.get_v());
            public_input[0] = u;
            public_input[1] = v;
        }
        {
            let affine = cv.as_inner().to_affine();
            let (u, v) = (affine.get_u(), affine.get_v());
            public_input[2] = u;
            public_input[3] = v;
        }
        public_input[4] = anchor;

        // Pack the nullifier into the circuit's two public inputs.
        let packed_nullifier = pack_nullifier(nullifier);
        public_input[5] = packed_nullifier[0];
        public_input[6] = packed_nullifier[1];

        // Verify the proof
        proof_verifier(verifier_ctx, zkproof, public_input)
    }

    /// Perform consensus checks on a Sapling OutputDescription, while
    /// accumulating its value commitment inside the context for later use.
    fn check_output(
        &mut self,
        cv: &ValueCommitment,
        cmu: ExtractedNoteCommitment,
        epk: jubjub::ExtendedPoint,
        zkproof: Proof<Bls12>,
        proof_verifier: impl FnOnce(Proof<Bls12>, [bls12_381::Scalar; 5]) -> bool,
    ) -> bool {
        // The "cv is not small order" happens when an OutputDescription is deserialized.
        // This happens when transactions or blocks are received over the network, or when
        // mined blocks are introduced via the `submitblock` RPC method on full nodes.
        if epk.is_small_order().into() {
            return false;
        }

        // Accumulate the value commitment in the context
        self.cv_sum -= cv;

        // Construct public input for circuit
        let mut public_input = [bls12_381::Scalar::zero(); 5];
        {
            let affine = cv.as_inner().to_affine();
            let (u, v) = (affine.get_u(), affine.get_v());
            public_input[0] = u;
            public_input[1] = v;
        }
        {
            let affine = epk.to_affine();
            let (u, v) = (affine.get_u(), affine.get_v());
            public_input[2] = u;
            public_input[3] = v;
        }
        public_input[4] = bls12_381::Scalar::from_repr(cmu.to_bytes()).unwrap();

        // Verify the proof
        proof_verifier(zkproof, public_input)
    }

    /// Perform consensus checks on the valueBalance and bindingSig parts of a
    /// Sapling transaction. All SpendDescriptions and OutputDescriptions must
    /// have been checked before calling this function.
    fn final_check<V: Into<i64>>(
        &self,
        value_balance: V,
        binding_sig_verifier: impl FnOnce(redjubjub::VerificationKey<Binding>) -> bool,
    ) -> bool {
        // Compute the final bvk.
        let bvk = self.cv_sum.into_bvk(value_balance);

        // Verify the binding_sig
        binding_sig_verifier(bvk)
    }
}

#[cfg(test)]
mod tests {
    use bellman::gadgets::multipack;

    use super::pack_nullifier;

    #[test]
    fn nullifier_packing_matches_circuit() {
        let check = |nullifier: [u8; 32]| {
            let bits = multipack::bytes_to_bits_le(&nullifier);
            let expected = multipack::compute_multipacking(&bits);
            assert_eq!(pack_nullifier(&nullifier).as_slice(), expected);
        };

        check([0; 32]);
        check([u8::MAX; 32]);

        for bit in 0..256 {
            let mut nullifier = [0; 32];
            nullifier[bit / 8] = 1 << (bit % 8);
            check(nullifier);
        }

        for seed in 0..256u16 {
            let mut nullifier = [0; 32];
            for (i, byte) in nullifier.iter_mut().enumerate() {
                *byte = seed.wrapping_mul(73).wrapping_add(i as u16 * 109) as u8;
            }
            check(nullifier);
        }
    }

    #[test]
    #[ignore = "release-mode performance measurement"]
    fn bench_nullifier_packing() {
        use std::{eprintln, hint::black_box, time::Instant, vec::Vec};

        const SAMPLES: usize = 100;
        const ITERATIONS: usize = 1_000;

        let nullifier = [0xa5; 32];
        let mut old = Vec::with_capacity(SAMPLES);
        let mut new = Vec::with_capacity(SAMPLES);

        for _ in 0..SAMPLES {
            let start = Instant::now();
            for _ in 0..ITERATIONS {
                let input = black_box(&nullifier);
                let bits = multipack::bytes_to_bits_le(input);
                black_box(multipack::compute_multipacking::<bls12_381::Scalar>(&bits));
            }
            old.push(start.elapsed().as_nanos() / ITERATIONS as u128);

            let start = Instant::now();
            for _ in 0..ITERATIONS {
                black_box(pack_nullifier(black_box(&nullifier)));
            }
            new.push(start.elapsed().as_nanos() / ITERATIONS as u128);
        }

        old.sort_unstable();
        new.sort_unstable();
        eprintln!(
            "nullifier packing: {} -> {} ns",
            old[SAMPLES / 2],
            new[SAMPLES / 2]
        );
    }
}
