import CommonInversionFGBridge

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def inversionZero : A4 := Array.repeat 4#usize 0#u64

theorem inversion_zero_value : val4 inversionZero = 0 := by
  norm_num [inversionZero, val4, Array.repeat]

@[step]
theorem inversion_zero_array_spec (x : A4) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU64 x inversionZero ⦃ out =>
      out = true ↔ val4 x = 0 ⦄ := by
  have hbridge : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU64 x inversionZero =
      core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU64 x.to_slice inversionZero.to_slice := by
    unfold core.array.equality.PartialEqArray.eq core.slice.cmp.PartialEqSlice.eq
    simp [Array.length, Array.length_to_slice, Array.val_to_slice]
  have heq : x.to_slice = inversionZero.to_slice ↔ val4 x = 0 := by
    rw [Slice.eq_iff, Array.val_to_slice, Array.val_to_slice, ← Array.eq_iff]
    constructor
    · intro h
      rw [h, inversion_zero_value]
    · intro h
      exact limbs_eq_of_value x inversionZero (h.trans inversion_zero_value.symm)
  rw [hbridge]
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU64
    x.to_slice inversionZero.to_slice (by
      intro a b
      simp [core.cmp.impls.PartialEqU64.ne, liftFun2, WP.spec_ok]))
  intro out hout
  exact hout.trans heq

#print axioms inversion_zero_value
#print axioms inversion_zero_array_spec
end UdonVerify.CommonSigned62
