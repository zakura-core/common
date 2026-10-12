import CommonDivstepStrip
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem ones_div_pow (width count : Nat) (hc : count ≤ width) :
    (2^width-1)/2^(width-count)=2^count-1 := by
  have hx : (0:Nat)<2^count := by positivity
  have hy : (0:Nat)<2^(width-count) := by positivity
  have hprod : (2^count:Nat)*2^(width-count)=2^width := by
    rw [←Nat.pow_add]
    congr 1
    omega
  have hxsub : (2^count-1:Nat)+1=2^count := by omega
  have hw : (0:Nat)<2^width := by positivity
  have hws : (2^width-1:Nat)+1=2^width := by omega
  have hmul : ((2^count-1:Nat)+1)*2^(width-count)=2^width := by rw [hxsub,hprod]
  apply Nat.div_eq_of_lt_le
  · nlinarith
  · rw [hxsub,hprod]
    omega

theorem ones_mod_pow (width count : Nat) :
    (2^width-1)%2^count=2^(min width count)-1 := by
  by_cases hle : width ≤ count
  · rw [Nat.min_eq_left hle]
    apply Nat.mod_eq_of_lt
    have hp : (2^width:Nat)≤2^count := Nat.pow_le_pow_right (by decide) hle
    have hz : (0:Nat)<2^width := by positivity
    omega
  · have hcw : count ≤ width := by omega
    rw [Nat.min_eq_right hcw]
    have hx : (0:Nat)<2^count := by positivity
    have hy : (0:Nat)<2^(width-count) := by positivity
    have hprod : (2^count:Nat)*2^(width-count)=2^width := by
      rw [←Nat.pow_add]
      congr 1
      omega
    have heq : (2^width-1:Nat)=(2^(width-count)-1)*2^count+(2^count-1) := by
      have hxs : (2^count-1:Nat)+1=2^count := by omega
      have hys : (2^(width-count)-1:Nat)+1=2^(width-count) := by omega
      have hws : (2^width-1:Nat)+1=2^width := by
        have h : (0:Nat)<2^width := by positivity
        omega
      have hmul : ((2^(width-count)-1:Nat)+1)*2^count=2^width := by rw [hys,Nat.mul_comm,hprod]
      nlinarith
    rw [heq]
    simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,
      Nat.zero_add,Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)

theorem ones_mask_and (width count : Nat) :
    (2^width-1) &&& (2^count-1)=2^(min width count)-1 := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact ones_mod_pow width count

@[step]
theorem cancellation_mask_spec (limit : U32) (cap : Nat) (mask : U64)
    (hl : 0 < limit.val ∧ limit.val ≤ 62) (hm : mask.val=2^cap-1) :
    (do let shift ← 64#u32-limit
        let full ← core.num.U64.MAX >>> shift
        ok (full &&& mask)) ⦃ out => out.val=2^(min limit.val cap)-1 ⦄ := by
  step +scalarTac -grind with U32.sub_spec as ⟨shift,hshift⟩
  step -grind with U64.ShiftRight_spec as ⟨full,hfull,hbv⟩
  simp only [UScalar.val_and,hfull,hm,show U64.rMax=2^64-1 from by decide,
    Nat.shiftRight_eq_div_pow,hshift]
  rw [ones_div_pow 64 limit.val (by omega)]
  exact ones_mask_and limit.val cap

#print axioms ones_div_pow
#print axioms ones_mod_pow
#print axioms ones_mask_and
#print axioms cancellation_mask_spec
end UdonVerify.CommonSigned62
