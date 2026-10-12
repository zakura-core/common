import CommonSigned62Packing
import CommonSigned62UnpackMath
open Aeneas Std Result
open Signed62Native.field.pasta.safegcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem signed62_uncast_value (value : I64) (h0 : 0≤value.val) (h1 : value.val<2^64) :
    (IScalar.hcast .U64 value).val=value.val.toNat := by
  rw [IScalar.hcast_val_eq]
  change (value.val % (2^64)).toNat=value.val.toNat
  rw [Int.emod_eq_of_lt h0 h1]

@[step]
theorem unpack62_digits (digits : Signed62) (hn : signed62Normalized digits)
    (ht : 0≤digits[4]!.val ∧ digits[4]!.val<128) :
    unpack62 digits ⦃ out => ∀ k : Fin 4, out[k.val]!.val=unpacked62Digit digits k.val ⦄ := by
  unfold unpack62
  step +scalarTac -grind as ⟨x0,hx0⟩
  try simp only [lift,bind_ok]
  have hx0Value : x0.val=digits[0]!.val := by
    rw [hx0]
    simp [Array.getElem!_Nat_eq,digits.property]
  let v0 := IScalar.hcast .U64 x0
  have hn0 := hn ⟨0,by decide⟩
  change 0≤digits[0]!.val ∧ digits[0]!.val<signedRadix at hn0
  have hv0 : v0.val=digits[0]!.val.toNat := by
    rw [signed62_uncast_value x0 (by rw [hx0Value];exact hn0.1)
      (by rw [hx0Value];unfold signedRadix at hn0;omega),hx0Value]
  have hb0 : v0.val<2^62 := by
    rw [hv0]
    unfold signedRadix at hn0
    omega
  step +scalarTac -grind as ⟨x1,hx1⟩
  try simp only [lift,bind_ok]
  have hx1Value : x1.val=digits[1]!.val := by
    rw [hx1]
    simp [Array.getElem!_Nat_eq,digits.property]
  let v1 := IScalar.hcast .U64 x1
  have hn1 := hn ⟨1,by decide⟩
  change 0≤digits[1]!.val ∧ digits[1]!.val<signedRadix at hn1
  have hv1 : v1.val=digits[1]!.val.toNat := by
    rw [signed62_uncast_value x1 (by rw [hx1Value];exact hn1.1)
      (by rw [hx1Value];unfold signedRadix at hn1;omega),hx1Value]
  have hb1 : v1.val<2^62 := by
    rw [hv1]
    unfold signedRadix at hn1
    omega
  step +scalarTac -grind as ⟨x2,hx2⟩
  try simp only [lift,bind_ok]
  have hx2Value : x2.val=digits[2]!.val := by
    rw [hx2]
    simp [Array.getElem!_Nat_eq,digits.property]
  let v2 := IScalar.hcast .U64 x2
  have hn2 := hn ⟨2,by decide⟩
  change 0≤digits[2]!.val ∧ digits[2]!.val<signedRadix at hn2
  have hv2 : v2.val=digits[2]!.val.toNat := by
    rw [signed62_uncast_value x2 (by rw [hx2Value];exact hn2.1)
      (by rw [hx2Value];unfold signedRadix at hn2;omega),hx2Value]
  have hb2 : v2.val<2^62 := by
    rw [hv2]
    unfold signedRadix at hn2
    omega
  step +scalarTac -grind as ⟨x3,hx3⟩
  try simp only [lift,bind_ok]
  have hx3Value : x3.val=digits[3]!.val := by
    rw [hx3]
    simp [Array.getElem!_Nat_eq,digits.property]
  let v3 := IScalar.hcast .U64 x3
  have hn3 := hn ⟨3,by decide⟩
  change 0≤digits[3]!.val ∧ digits[3]!.val<signedRadix at hn3
  have hv3 : v3.val=digits[3]!.val.toNat := by
    rw [signed62_uncast_value x3 (by rw [hx3Value];exact hn3.1)
      (by rw [hx3Value];unfold signedRadix at hn3;omega),hx3Value]
  have hb3 : v3.val<2^62 := by
    rw [hv3]
    unfold signedRadix at hn3
    omega
  step +scalarTac -grind as ⟨x4,hx4⟩
  try simp only [lift,bind_ok]
  have hx4Value : x4.val=digits[4]!.val := by
    rw [hx4]
    simp [Array.getElem!_Nat_eq,digits.property]
  let v4 := IScalar.hcast .U64 x4
  have hv4 : v4.val=digits[4]!.val.toNat := by
    rw [signed62_uncast_value x4 (by rw [hx4Value];exact ht.1)
      (by rw [hx4Value];omega),hx4Value]
  have hb4 : v4.val<128 := by rw [hv4];omega
  norm_num only at hb0 hb1 hb2 hb3 hb4
  rw [mask62_eq]
  try simp only [lift,bind_ok]
  step +scalarTac -grind
  step +scalarTac -grind
  step +scalarTac -grind
  step +scalarTac -grind
  step +scalarTac -grind
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨hi0,hhi0,_⟩
  try simp only [lift,bind_ok]
  let u0 := v0 ||| hi0
  have hu0 : u0.val=unpacked62Digit digits 0 := by
    simp only [Nat.shiftLeft_eq] at hhi0
    norm_num only [U64.size,U64.numBits,UScalarTy.numBits] at hhi0
    have hjoin := unpack62_join v0.val v1.val ⟨0,by decide⟩ hb0
    simp only [u0,UScalar.val_or]
    norm_num only [Fin.val_zero,Fin.val_one,Fin.val_ofNat] at hjoin
    rw [hhi0]
    rw [hv0,hv1] at hjoin ⊢
    norm_num only [unpacked62Digit] at hjoin ⊢
    exact hjoin
  step -grind with U64.ShiftRight_IScalar_spec as ⟨lo1,hlo1,_⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨hi1,hhi1,_⟩
  try simp only [lift,bind_ok]
  let u1 := lo1 ||| hi1
  have hu1 : u1.val=unpacked62Digit digits 1 := by
    simp only [Nat.shiftRight_eq_div_pow] at hlo1
    simp only [Nat.shiftLeft_eq] at hhi1
    norm_num only [U64.size,U64.numBits,UScalarTy.numBits] at hlo1 hhi1
    have hlow : lo1.val<2^(60) := by rw [hlo1,hv1];norm_num only [signedRadix] at hn1;omega
    have hjoin := unpack62_join lo1.val v2.val ⟨1,by decide⟩ hlow
    simp only [u1,UScalar.val_or]
    norm_num only [Fin.val_zero,Fin.val_one,Fin.val_ofNat] at hjoin
    rw [hhi1]
    rw [hlo1] at hjoin ⊢
    rw [hv1,hv2] at hjoin ⊢
    norm_num only [unpacked62Digit] at hjoin ⊢
    exact hjoin
  step -grind with U64.ShiftRight_IScalar_spec as ⟨lo2,hlo2,_⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨hi2,hhi2,_⟩
  try simp only [lift,bind_ok]
  let u2 := lo2 ||| hi2
  have hu2 : u2.val=unpacked62Digit digits 2 := by
    simp only [Nat.shiftRight_eq_div_pow] at hlo2
    simp only [Nat.shiftLeft_eq] at hhi2
    norm_num only [U64.size,U64.numBits,UScalarTy.numBits] at hlo2 hhi2
    have hlow : lo2.val<2^(58) := by rw [hlo2,hv2];norm_num only [signedRadix] at hn2;omega
    have hjoin := unpack62_join lo2.val v3.val ⟨2,by decide⟩ hlow
    simp only [u2,UScalar.val_or]
    norm_num only [Fin.val_zero,Fin.val_one,Fin.val_ofNat] at hjoin
    rw [hhi2]
    rw [hlo2] at hjoin ⊢
    rw [hv2,hv3] at hjoin ⊢
    norm_num only [unpacked62Digit] at hjoin ⊢
    exact hjoin
  step -grind with U64.ShiftRight_IScalar_spec as ⟨lo3,hlo3,_⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨hi3,hhi3,_⟩
  try simp only [lift,bind_ok]
  let u3 := lo3 ||| hi3
  have hu3 : u3.val=unpacked62Digit digits 3 := by
    simp only [Nat.shiftRight_eq_div_pow] at hlo3
    simp only [Nat.shiftLeft_eq] at hhi3
    norm_num only [U64.size,U64.numBits,UScalarTy.numBits] at hlo3 hhi3
    have hlow : lo3.val<2^(56) := by rw [hlo3,hv3];norm_num only [signedRadix] at hn3;omega
    have hjoin := unpack62_join lo3.val v4.val ⟨3,by decide⟩ hlow
    have hmod : v4.val%256=v4.val := Nat.mod_eq_of_lt (by omega)
    simp only [u3,UScalar.val_or]
    norm_num only [Fin.val_zero,Fin.val_one,Fin.val_ofNat] at hjoin
    rw [hhi3]
    rw [hlo3] at hjoin ⊢
    rw [hmod] at hjoin
    rw [hv3,hv4] at hjoin ⊢
    norm_num only [unpacked62Digit] at hjoin ⊢
    exact hjoin
  try simp only [lift,bind_ok,WP.spec_ok]
  intro k
  fin_cases k
  · simpa [Array.make,Array.getElem!_Nat_eq,u0,u1,u2,u3,v0,v1,v2,v3,v4] using hu0
  · simpa [Array.make,Array.getElem!_Nat_eq,u0,u1,u2,u3,v0,v1,v2,v3,v4] using hu1
  · simpa [Array.make,Array.getElem!_Nat_eq,u0,u1,u2,u3,v0,v1,v2,v3,v4] using hu2
  · simpa [Array.make,Array.getElem!_Nat_eq,u0,u1,u2,u3,v0,v1,v2,v3,v4] using hu3

@[step]
theorem unpack62_spec (digits : Signed62) (hn : signed62Normalized digits)
    (ht : 0≤digits[4]!.val ∧ digits[4]!.val<128) :
    unpack62 digits ⦃ out => (val4 out : Int)=signed62Value digits ⦄ := by
  step -grind with (unpack62_digits digits hn ht) as ⟨out,hout⟩
  have hvalue := unpacked62_value digits hn ht
  simpa only [val4,B,hout ⟨0,by decide⟩,hout ⟨1,by decide⟩,
    hout ⟨2,by decide⟩,hout ⟨3,by decide⟩] using hvalue

#print axioms signed62_uncast_value
#print axioms unpack62_digits
#print axioms unpack62_spec
end UdonVerify.CommonSigned62
