import CommonTrailingZeros
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def sentinelWord (value : U64) (remaining : Nat) : U64 :=
  ⟨value.bv ||| (BitVec.allOnes 64 <<< remaining)⟩

theorem sentinel_bit_true (value : U64) (remaining : Nat) (hr : remaining<64) :
    (sentinelWord value remaining).bv.getLsbD remaining=true := by
  change (value.bv ||| (BitVec.allOnes 64 <<< remaining)).getLsbD remaining=true
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_allOnes,hr,
    decide_true,lt_self_iff_false,decide_false,Bool.not_false,Nat.sub_self,
    show (0:Nat)<64 from by decide,Bool.true_and,Bool.or_true]

theorem sentinel_count_bound (value : U64) (remaining : Nat) (hr : remaining<64) :
    trailingZeros64 (sentinelWord value remaining)≤remaining := by
  by_contra h
  have hzero := BitVec.getLsbD_false_of_lt_ctz (x:=(sentinelWord value remaining).bv)
    (i:=remaining) (by unfold trailingZeros64 at h;omega)
  rw [sentinel_bit_true value remaining hr] at hzero
  contradiction

theorem sentinel_low_bits (value : U64) (remaining : Nat) :
    value.val%2^(trailingZeros64 (sentinelWord value remaining))=0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow,Nat.zero_testBit]
  by_cases hi : i<trailingZeros64 (sentinelWord value remaining)
  · simp only [hi,decide_true,Bool.true_and]
    have hz := BitVec.getLsbD_false_of_lt_ctz (x:=(sentinelWord value remaining).bv) (i:=i) hi
    change (value.bv ||| (BitVec.allOnes 64 <<< remaining)).getLsbD i=false at hz
    simp only [BitVec.getLsbD_or,Bool.or_eq_false_iff] at hz
    exact hz.1
  · simp [hi]

theorem sentinel_odd_quotient (value : U64) (remaining : Nat) (hr : remaining<64)
    (hlt : trailingZeros64 (sentinelWord value remaining)<remaining) :
    (value.val/2^(trailingZeros64 (sentinelWord value remaining)))%2=1 := by
  have hnz : (sentinelWord value remaining).bv≠0#64 := by
    intro h
    have ht := sentinel_bit_true value remaining hr
    rw [h] at ht
    simpa using ht
  have htrue := BitVec.getLsbD_true_ctz_of_ne_zero hnz
  change (value.bv ||| (BitVec.allOnes 64 <<< remaining)).getLsbD
    (trailingZeros64 (sentinelWord value remaining))=true at htrue
  have hs : (BitVec.allOnes 64 <<< remaining).getLsbD
      (trailingZeros64 (sentinelWord value remaining))=false := by
    simp only [BitVec.getLsbD_shiftLeft,hlt,decide_true,Bool.not_true,Bool.and_false,Bool.false_and]
  rw [BitVec.getLsbD_or,hs,Bool.or_false] at htrue
  apply Nat.mod_two_eq_one_iff_testBit_zero.mpr
  rw [←Nat.shiftRight_eq_div_pow,Nat.testBit_shiftRight]
  exact htrue

#print axioms sentinel_bit_true
#print axioms sentinel_count_bound
#print axioms sentinel_low_bits
#print axioms sentinel_odd_quotient
end UdonVerify.CommonSigned62
