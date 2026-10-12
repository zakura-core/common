import CommonDivsteps.Funs
import CommonSigned62Math
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def trailingZeros64 (value : U64) : Nat := value.bv.ctz.toNat

theorem trailing_zeros_bound (value : U64) : trailingZeros64 value≤64 := by
  have h := BitVec.clz_le (x:=value.bv.reverse)
  simpa [trailingZeros64,BitVec.ctz,BitVec.le_def] using h

@[step]
theorem trailing_zeros_spec (value : U64) :
    CommonDivsteps.core.num.U64.trailing_zeros value ⦃ out => out.val=trailingZeros64 value ⦄ := by
  simp only [CommonDivsteps.core.num.U64.trailing_zeros,WP.spec_ok,UScalar.val]
  apply Nat.mod_eq_of_lt
  have h := trailing_zeros_bound value
  unfold trailingZeros64 at h
  omega

theorem trailing_zeros_low_bits (value : U64) (n : Nat) (hn : n≤trailingZeros64 value) :
    value.val%2^n=0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow,Nat.zero_testBit]
  by_cases hi : i<n
  · simp only [hi,decide_true,Bool.true_and]
    have h := BitVec.getLsbD_false_of_lt_ctz (x:=value.bv) (i:=i) (by unfold trailingZeros64 at hn;omega)
    exact h
  · simp [hi]

theorem trailing_zeros_odd_quotient (value : U64) (hnonzero : value.val≠0) :
    (value.val/2^(trailingZeros64 value))%2=1 := by
  apply Nat.mod_two_eq_one_iff_testBit_zero.mpr
  rw [←Nat.shiftRight_eq_div_pow,Nat.testBit_shiftRight]
  have h := BitVec.getLsbD_true_ctz_of_ne_zero (x:=value.bv) (by
    intro hz;apply hnonzero;exact congrArg BitVec.toNat hz)
  exact h

#print axioms trailing_zeros_bound
#print axioms trailing_zeros_spec
#print axioms trailing_zeros_low_bits
#print axioms trailing_zeros_odd_quotient
end UdonVerify.CommonSigned62
