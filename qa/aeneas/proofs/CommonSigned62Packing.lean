import CommonSigned62Math
open Aeneas Std Result
open Signed62Native.field.pasta.safegcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem mask62_eq : MASK62=ok 4611686018427387903#u64 := by
  have h : MASK62 ⦃ out => out=4611686018427387903#u64 ⦄ := by
    unfold MASK62
    step +scalarTac -grind with U64.ShiftLeft_IScalar_spec as ⟨shifted,hshift,_⟩
    step +scalarTac -grind as ⟨out,hout⟩
    apply UScalar.eq_of_val_eq
    norm_num only [Nat.shiftLeft_eq,U64.size] at hshift
    scalar_tac
  obtain ⟨out,hresult,hout⟩ := WP.spec_imp_exists h
  simpa only [hout] using hresult

theorem mask62_value : (4611686018427387903#u64).val=2^62-1 := by decide

theorem signed62_cast_value (value : U64) (hbound : value.val<2^62) :
    (UScalar.hcast .I64 value).val=(value.val : Int) := by
  rw [UScalar.hcast_val_eq]
  change Int.bmod (value.val : Int) (2^64)=(value.val : Int)
  apply Arith.Int.bmod_pow2_eq_of_inBounds 63 <;> omega

@[step]
theorem to_signed62_digits (limbs : A4) :
    to_signed62 limbs ⦃ out => ∀ k : Fin 5, out[k.val]!.val=(packed62Digit limbs k.val : Int) ⦄ := by
  unfold to_signed62
  step +scalarTac -grind as ⟨x0,hx0⟩
  rw [mask62_eq]
  simp only [lift,bind_ok]
  let m0 := x0 &&& 4611686018427387903#u64
  have hm0 : m0.val=packed62Digit limbs 0 := by
    simp only [m0,UScalar.val_and,mask62_value,packed62Digit]
    rw [Nat.and_two_pow_sub_one_eq_mod _ 62]
    change x0.val % (2^62) = limbs[0]!.val % (2^62)
    rw [hx0]
    simp [Array.getElem!_Nat_eq,limbs.property]
  have hc0 : (UScalar.hcast .I64 m0).val=(packed62Digit limbs 0 : Int) := by
    rw [signed62_cast_value m0 (by rw [hm0];exact packed62_digit_bound limbs ⟨0,by decide⟩),hm0]
  step -grind with U64.ShiftRight_IScalar_spec as ⟨lo1,hlo1,_⟩
  step +scalarTac -grind as ⟨x1,hx1⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨hi1,hhi1,_⟩
  try simp only [lift,bind_ok]
  let m1 := (lo1 ||| hi1) &&& 4611686018427387903#u64
  have hm1 : m1.val=packed62Digit limbs 1 := by
    have hjoin := signed62_join x0.val x1.val ⟨0,by decide⟩ (by scalar_tac)
    simp only [Nat.shiftRight_eq_div_pow,IScalar.toNat] at hlo1
    simp only [Nat.shiftLeft_eq,IScalar.toNat] at hhi1
    norm_num only [U64.size,U64.numBits,UScalarTy.numBits,IScalar.val] at hlo1 hhi1 hjoin
    simp only [m1,UScalar.val_and,UScalar.val_or,mask62_value]
    rw [Nat.and_two_pow_sub_one_eq_mod _ 62]
    simpa [hlo1,hhi1,hx0,hx1,packed62Digit,Array.getElem!_Nat_eq,limbs.property] using hjoin
  have hc1 : (UScalar.hcast .I64 m1).val=(packed62Digit limbs 1 : Int) := by
    rw [signed62_cast_value m1 (by rw [hm1];exact packed62_digit_bound limbs ⟨1,by decide⟩),hm1]
  step -grind with U64.ShiftRight_IScalar_spec as ⟨lo2,hlo2,_⟩
  step +scalarTac -grind as ⟨x2,hx2⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨hi2,hhi2,_⟩
  try simp only [lift,bind_ok]
  let m2 := (lo2 ||| hi2) &&& 4611686018427387903#u64
  have hm2 : m2.val=packed62Digit limbs 2 := by
    have hjoin := signed62_join x1.val x2.val ⟨1,by decide⟩ (by scalar_tac)
    simp only [Nat.shiftRight_eq_div_pow,IScalar.toNat] at hlo2
    simp only [Nat.shiftLeft_eq,IScalar.toNat] at hhi2
    norm_num only [U64.size,U64.numBits,UScalarTy.numBits,IScalar.val] at hlo2 hhi2 hjoin
    simp only [m2,UScalar.val_and,UScalar.val_or,mask62_value]
    rw [Nat.and_two_pow_sub_one_eq_mod _ 62]
    simpa [hlo2,hhi2,hx1,hx2,packed62Digit,Array.getElem!_Nat_eq,limbs.property] using hjoin
  have hc2 : (UScalar.hcast .I64 m2).val=(packed62Digit limbs 2 : Int) := by
    rw [signed62_cast_value m2 (by rw [hm2];exact packed62_digit_bound limbs ⟨2,by decide⟩),hm2]
  step -grind with U64.ShiftRight_IScalar_spec as ⟨lo3,hlo3,_⟩
  step +scalarTac -grind as ⟨x3,hx3⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨hi3,hhi3,_⟩
  try simp only [lift,bind_ok]
  let m3 := (lo3 ||| hi3) &&& 4611686018427387903#u64
  have hm3 : m3.val=packed62Digit limbs 3 := by
    have hjoin := signed62_join x2.val x3.val ⟨2,by decide⟩ (by scalar_tac)
    simp only [Nat.shiftRight_eq_div_pow,IScalar.toNat] at hlo3
    simp only [Nat.shiftLeft_eq,IScalar.toNat] at hhi3
    norm_num only [U64.size,U64.numBits,UScalarTy.numBits,IScalar.val] at hlo3 hhi3 hjoin
    simp only [m3,UScalar.val_and,UScalar.val_or,mask62_value]
    rw [Nat.and_two_pow_sub_one_eq_mod _ 62]
    simpa [hlo3,hhi3,hx2,hx3,packed62Digit,Array.getElem!_Nat_eq,limbs.property] using hjoin
  have hc3 : (UScalar.hcast .I64 m3).val=(packed62Digit limbs 3 : Int) := by
    rw [signed62_cast_value m3 (by rw [hm3];exact packed62_digit_bound limbs ⟨3,by decide⟩),hm3]
  step -grind with U64.ShiftRight_IScalar_spec as ⟨top,htop,_⟩
  try simp only [lift,bind_ok,WP.spec_ok]
  have htopValue : top.val=packed62Digit limbs 4 := by
    simpa [Nat.shiftRight_eq_div_pow,IScalar.toNat,packed62Digit,hx3,Array.getElem!_Nat_eq,limbs.property] using htop
  have hc4 : (UScalar.hcast .I64 top).val=(packed62Digit limbs 4 : Int) := by
    rw [signed62_cast_value top (by rw [htopValue];exact packed62_digit_bound limbs ⟨4,by decide⟩),htopValue]
  intro k
  fin_cases k
  · simpa [Array.make,Array.getElem!_Nat_eq,m0,m1,m2,m3] using hc0
  · simpa [Array.make,Array.getElem!_Nat_eq,m0,m1,m2,m3] using hc1
  · simpa [Array.make,Array.getElem!_Nat_eq,m0,m1,m2,m3] using hc2
  · simpa [Array.make,Array.getElem!_Nat_eq,m0,m1,m2,m3] using hc3
  · simpa [Array.make,Array.getElem!_Nat_eq,m0,m1,m2,m3] using hc4

@[step]
theorem to_signed62_spec (limbs : A4) (hbound : val4 limbs<2^255) :
    to_signed62 limbs ⦃ out => signed62Normalized out ∧ signed62Value out=(val4 limbs:Int) ∧
      0≤out[4]!.val ∧ out[4]!.val<128 ⦄ := by
  step -grind with (to_signed62_digits limbs) as ⟨out,hout⟩
  exact packed62_representation limbs out hbound hout

#print axioms mask62_eq
#print axioms mask62_value
#print axioms signed62_cast_value
#print axioms to_signed62_digits
#print axioms to_signed62_spec
end UdonVerify.CommonSigned62
