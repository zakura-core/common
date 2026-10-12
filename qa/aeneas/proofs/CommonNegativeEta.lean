import CommonCancellationWords
open Aeneas Std Result
open Signed62Native.field.pasta.safegcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def negativeEtaWord (f g mask : U64) : U64 :=
  UScalar.wrapping_mul (UScalar.wrapping_mul f g)
    (UScalar.wrapping_sub (UScalar.wrapping_mul f f) 2#u64) &&& mask

theorem negative_eta_eq (f g mask : U64) :
    negative_eta_multiplier f g mask=ok (negativeEtaWord f g mask) := by
  simp only [negative_eta_multiplier,negativeEtaWord,lift,bind_ok,core.num.U64.wrapping_mul,core.num.U64.wrapping_sub]

theorem negative_eta_word_mod (f g mask : U64) (n : Nat) (hn : n≤64)
    (hm : mask.val=2^n-1) :
    Int.ModEq (2^n) ((negativeEtaWord f g mask).val : Int)
      ((f.val:Int)*g.val*((f.val:Int)*f.val-2)) := by
  have hfg := wrapping_mul_mod_pow f g n hn
  have hff := wrapping_mul_mod_pow f f n hn
  have hs := wrapping_sub_mod_pow (UScalar.wrapping_mul f f) 2#u64 n hn
  have hprod := wrapping_mul_mod_pow (UScalar.wrapping_mul f g)
    (UScalar.wrapping_sub (UScalar.wrapping_mul f f) 2#u64) n hn
  norm_num only at hs
  have hsub := hs.trans (hff.sub (Int.ModEq.refl (n:=(2^n)) 2))
  have hproduct := hprod.trans (hfg.mul hsub)
  have hmask : Int.ModEq (2^n) ((negativeEtaWord f g mask).val : Int)
      ((UScalar.wrapping_mul (UScalar.wrapping_mul f g)
        (UScalar.wrapping_sub (UScalar.wrapping_mul f f) 2#u64)).val : Int) := by
    unfold negativeEtaWord
    rw [and_mask_mod _ mask n hm]
    simp only [Int.ModEq,Int.natCast_emod,Nat.cast_pow,Nat.cast_ofNat,Int.emod_emod]
  exact hmask.trans hproduct

@[step]
theorem negative_eta_multiplier_spec (f g mask : U64) (n : Nat) (hn : n≤6)
    (hm : mask.val=2^n-1) (hodd : f.val%2=1) :
    negative_eta_multiplier f g mask ⦃ out => out.val<2^n ∧
      (g.val+f.val*out.val)%2^n=0 ⦄ := by
  rw [negative_eta_eq]
  simp only [WP.spec_ok]
  constructor
  · unfold negativeEtaWord
    rw [and_mask_mod _ mask n hm]
    exact Nat.mod_lt _ (by positivity)
  · have hword := negative_eta_word_mod f g mask n (by omega) hm
    have hoddInt : (f.val:Int)%2=1 := by exact_mod_cast hodd
    have hcancel := (negative_cancel64 (f.val:Int) g.val hoddInt).of_dvd
      (show (2^n:Int) ∣ 64 from by change (2^n:Int) ∣ 2^6;exact pow_dvd_pow 2 hn)
    have h := (hword.mul_left (f.val:Int)).add_left (g.val:Int)
    have hzero := h.trans hcancel
    have hnat : Nat.ModEq (2^n) (g.val+f.val*(negativeEtaWord f g mask).val) 0 := by
      apply Int.natCast_modEq_iff.mp
      simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_mul,Nat.cast_zero] using hzero
    exact hnat

#print axioms negative_eta_eq
#print axioms negative_eta_word_mod
#print axioms negative_eta_multiplier_spec
end UdonVerify.CommonSigned62
