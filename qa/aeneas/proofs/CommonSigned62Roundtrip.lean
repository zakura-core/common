import CommonSigned62Pack
import CommonSigned62Unpack
open Aeneas Std Result
open Signed62Native.field.pasta.safegcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem limbs_eq_of_digits (lhs rhs : A4)
    (hdigits : ∀ k : Fin 4, lhs[k.val]!.val=rhs[k.val]!.val) : lhs=rhs := by
  apply Aeneas.Std.Array.ext
  apply List.ext_getElem
  · simp only [lhs.property,rhs.property]
  · intro k hk hk'
    have hbound : k<4 := by simpa [lhs.property] using hk
    have h := UScalar.eq_of_val_eq (hdigits ⟨k,hbound⟩)
    simpa only [Array.getElem!_Nat_eq,getElem!_pos lhs.val k hk,
      getElem!_pos rhs.val k hk'] using h

theorem limbs_eq_of_value (lhs rhs : A4) (hvalue : val4 lhs=val4 rhs) : lhs=rhs := by
  have ha0 := lhs[0]!.hmax
  have ha1 := lhs[1]!.hmax
  have ha2 := lhs[2]!.hmax
  have ha3 := lhs[3]!.hmax
  have hb0 := rhs[0]!.hmax
  have hb1 := rhs[1]!.hmax
  have hb2 := rhs[2]!.hmax
  have hb3 := rhs[3]!.hmax
  norm_num only [UScalar.cMax,UScalarTy.numBits,val4,B] at hvalue ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  apply limbs_eq_of_digits
  intro k
  fin_cases k
  · change lhs[0]!.val=rhs[0]!.val
    omega
  · change lhs[1]!.val=rhs[1]!.val
    omega
  · change lhs[2]!.val=rhs[2]!.val
    omega
  · change lhs[3]!.val=rhs[3]!.val
    omega

@[step]
theorem pack_unpack_roundtrip (limbs : A4) (hbound : val4 limbs<2^255) :
    (do let packed ← pack62 limbs; unpack62 packed) ⦃ out => out=limbs ⦄ := by
  step -grind with (pack62_spec limbs hbound) as ⟨packed,hn,hvalue,ht0,ht1⟩
  step -grind with (unpack62_spec packed hn ⟨ht0,ht1⟩) as ⟨out,hout⟩
  apply limbs_eq_of_value
  omega

#print axioms limbs_eq_of_digits
#print axioms limbs_eq_of_value
#print axioms pack_unpack_roundtrip
end UdonVerify.CommonSigned62
