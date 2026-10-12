import RedcProofs
import ReduceProofs
import SquareProofs
import MontgomerySemantics

open Aeneas Std Result
open udon_kernel_slice.field.pasta
open udon_kernel_slice.field.pasta.montgomery

namespace UdonVerify
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post UScalar.ofNat

@[step]
theorem montgomery_square_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (value : A4)
    (hvalue : val4 value < 2*val4 params.modulus) :
    montgomery_square inst value ⦃ out => val4 out < 2*val4 params.modulus ∧
      ∃ m : Nat, m < R ∧ R*val4 out = val4 value^2 + m*val4 params.modulus ⦄ := by
  unfold montgomery_square
  step -grind with slice_square_wide_spec as ⟨wide, hwide⟩
  have hbound : val8 wide < val4 params.modulus*R + val4 params.modulus^2 := by
    rw [hwide]
    have hp0 := params.positive
    have hp3 := params.thrice_lt
    have hs := Nat.mul_lt_mul_of_pos_right hp3 hp0
    nlinarith only [hvalue, hp0, hs]
  step -grind with (montgomery_reduce_unreduced_spec inst params wide hbound) as ⟨out, h3, m, hm, hcert⟩
  have hcert' : R*val4 out = val4 value*val4 value + m*val4 params.modulus := by
    simpa [hwide, pow_two] using hcert
  have hb := pasta_loose_bound params (val4 value) (val4 value) m (val4 out) hvalue hvalue hm hcert'
  try simp only [WP.spec_ok]
  exact ⟨hb,m,hm,by simpa [hwide] using hcert⟩

@[step]
theorem montgomery_reduce_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (limbs : A8)
    (hlimbs : val8 limbs < val4 params.modulus*R) :
    montgomery_reduce inst limbs ⦃ out =>
      val4 out < val4 params.modulus ∧ Nat.ModEq (val4 params.modulus) (R*val4 out) (val8 limbs) ⦄ := by
  unfold montgomery_reduce
  have hbound : val8 limbs < val4 params.modulus*R+val4 params.modulus^2 :=
    _root_.lt_of_lt_of_le hlimbs (Nat.le_add_right _ _)
  step -grind with (montgomery_reduce_unreduced_spec inst params limbs hbound) as ⟨raw, h3, m, hm, hcert⟩
  have hmp : m*val4 params.modulus < R*val4 params.modulus :=
    Nat.mul_lt_mul_of_pos_right hm params.positive
  have hraw : val4 raw < 2*val4 params.modulus := by
    have hmul : R*val4 raw < R*(2*val4 params.modulus) := by
      nlinarith only [hcert,hlimbs,hmp]
    exact Nat.lt_of_mul_lt_mul_left hmul
  step -grind with (reduce_once_spec inst params raw hraw) as ⟨out, houtval, houtbound⟩
  try simp only [WP.spec_ok]
  refine ⟨houtbound,?_⟩
  unfold Nat.ModEq
  rw [houtval]
  have hc := certificate_congruence (val4 params.modulus) (val8 limbs) m (val4 raw) hcert
  simpa [Nat.ModEq, Nat.mul_mod] using hc

#print axioms montgomery_square_spec
#print axioms montgomery_reduce_spec

end UdonVerify
