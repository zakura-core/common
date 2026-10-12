import LooseMultiply

open Aeneas Std Result
open udon_kernel_slice.field.pasta
open udon_kernel_slice.field.pasta.montgomery

namespace UdonVerify
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post UScalar.ofNat UScalar.cMax

theorem ordering_lt_of_relation (out : Ordering) (a b : Nat)
    (hrel : orderingRel out a b) (hlt : a<b) : out=Ordering.lt := by
  cases out <;> simp_all [orderingRel] <;> omega

theorem ordering_is_lt_result : udon_kernel_slice.core.cmp.Ordering.is_lt Ordering.lt = ok true := by
  rfl

@[step]
theorem montgomery_multiply_loose_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (lhs rhs : A4)
    (ha : val4 lhs < 2*val4 params.modulus) (hb : val4 rhs < 2*val4 params.modulus) :
    montgomery_multiply_loose inst lhs rhs ⦃ out =>
      val4 out < 2*val4 params.modulus ∧
      ∃ m : Nat,m<R ∧ R*val4 out=val4 lhs*val4 rhs+m*val4 params.modulus ⦄ := by
  unfold montgomery_multiply_loose
  rw [params.modulus_ok]
  simp only [bind_ok]
  step +scalarTac -grind as ⟨p2,hp2⟩
  have hp2zero : p2=0#u64 := by
    have hz := params.zero_limb
    have hp2val : p2.val=0 := by simpa [hp2] using hz
    clear * - hp2val
    scalar_tac
  step
  step +scalarTac -grind as ⟨p3,hp3⟩
  step -grind as ⟨shift,hshift,hshiftBV⟩
  have hp3shift : p3=shift := by
    have hh := params.high_limb
    have hp3val : p3.val=2^62 := by simpa [hp3] using hh
    have hsh : shift.val=2^62 := by
      simpa [Nat.shiftLeft_eq,U64.size,U64.numBits] using hshift
    clear * - hp3val hsh
    scalar_tac
  step
  rw [params.twice_ok]
  simp only [bind_ok]
  step -grind with slice_compare_limbs_spec as ⟨orderL,horderL⟩
  have hltL : val4 lhs<val4 params.twice := by rw [params.twice_val]; exact ha
  have horderLEq := ordering_lt_of_relation orderL _ _ horderL hltL
  subst orderL
  rw [ordering_is_lt_result]
  simp only [bind_ok]
  step
  step -grind with slice_compare_limbs_spec as ⟨orderR,horderR⟩
  have hltR : val4 rhs<val4 params.twice := by rw [params.twice_val]; exact hb
  have horderREq := ordering_lt_of_relation orderR _ _ horderR hltR
  subst orderR
  rw [ordering_is_lt_result]
  simp only [bind_ok]
  step
  exact montgomery_multiply_loose_rust_spec inst params lhs rhs ha hb

#print axioms ordering_lt_of_relation
#print axioms ordering_is_lt_result
#print axioms montgomery_multiply_loose_spec
end UdonVerify
