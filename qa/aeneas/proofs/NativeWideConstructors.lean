import NativeWideDecode

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem loose_constructor_value_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (limbs : A4)
    (hlimbs : val4 limbs < 2 * val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.from_loose inst looseInst limbs
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (val4 out.limbs) (val4 limbs) ⦄ := by
  step -grind with (from_loose_loose_spec inst params limbs hlimbs) as ⟨out, hout⟩
  refine ⟨by simpa only [hout] using hlimbs, ?_⟩
  rw [hout]

@[step]
theorem reduced_constructor_value_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (limbs : A4)
    (hlimbs : val4 limbs < 2 * val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.from_loose inst reducedInst limbs
      ⦃ out => val4 out.limbs < val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (val4 out.limbs) (val4 limbs) ⦄ := by
  step -grind with (from_loose_reduced_spec inst params limbs hlimbs) as ⟨out, hbound, hout⟩
  exact ⟨hbound, by simp only [Nat.ModEq, hout, Nat.mod_mod]⟩

end UdonVerify.Native
