import NativeSqrtRoots

open Aeneas Std Result

namespace UdonVerify.SqrtNativeBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def reducedValid {M S : Type} (p : Nat) (value : Element M S) : Prop :=
  val4 value.limbs < p

theorem reduce_loose_bridge {M : Type} (inst : Modulus M) (value : Element M Loose) :
    SqrtNative.zakura_udon.field.pasta.PastaField.reduce inst looseInst value = (do
      let out ← NativeField.zakura_udon.field.pasta.PastaField.reduce
        (nativeModulus inst) Native.looseInst (convertNative (T := Native.Loose) value)
      ok (convertSqrt (T := Reduced) out)) := by
  unfold SqrtNative.zakura_udon.field.pasta.PastaField.reduce
    NativeField.zakura_udon.field.pasta.PastaField.reduce
  simp only [
    SqrtNative.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED,
    NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED,
    bind_ok, Bool.false_eq_true, ↓reduceIte, Std.bind_assoc]
  with_unfolding_all rfl

@[step]
theorem sqrt_reduce_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    (value : Element M Loose) (hvalue : looseValid (val4 params.modulus) value) :
    SqrtNative.zakura_udon.field.pasta.PastaField.reduce inst looseInst value ⦃ out =>
      reducedValid (val4 params.modulus) out ∧
      fieldValue (val4 params.modulus) inverse out = fieldValue (val4 params.modulus) inverse value ⦄ := by
  rw [reduce_loose_bridge]
  step -grind with (Native.reduce_loose_spec (nativeModulus inst) params
    (convertNative (T := Native.Loose) value) hvalue) as ⟨out, houtBound, houtValue⟩
  refine ⟨houtBound, ?_⟩
  unfold fieldValue Native.decode
  simp only [convertSqrt, convertNative] at *
  rw [houtValue, Native.decoded_reduce]

@[step]
theorem sqrt_widen_spec {M S : Type} (p inverse : Nat) (value : Element M S)
    (hvalue : reducedValid p value) :
    SqrtNative.zakura_udon.field.pasta.PastaField.into_loose value ⦃ out =>
      looseValid p out ∧ fieldValue p inverse out = fieldValue p inverse value ⦄ := by
  unfold SqrtNative.zakura_udon.field.pasta.PastaField.into_loose
  simp only [WP.spec_ok]
  exact ⟨by change val4 value.limbs < 2 * p; change val4 value.limbs < p at hvalue; omega, rfl⟩

theorem sqrt_zero_reduced {M : Type} (p inverse : Nat) (hp : 0 < p) :
    reducedValid p (SqrtNative.zakura_udon.field.pasta.PastaField.ZERO M Reduced) ∧
    fieldValue p inverse (SqrtNative.zakura_udon.field.pasta.PastaField.ZERO M Reduced) = 0 := by
  have hzero : val4 (SqrtNative.zakura_udon.field.pasta.PastaField.ZERO M Reduced).limbs = 0 := by
    norm_num [SqrtNative.zakura_udon.field.pasta.PastaField.ZERO, val4, Array.repeat]
  constructor
  · simpa only [reducedValid, hzero] using hp
  · simp only [fieldValue, Native.decode, hzero, zero_mul, Nat.zero_mod, Nat.cast_zero]

@[step]
theorem sqrt_is_zero_reduced {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (value : Element M Reduced) (hvalue : reducedValid (val4 params.modulus) value) :
    SqrtNative.zakura_udon.field.pasta.PastaField.is_zero inst reducedInst value ⦃ out =>
      out = true ↔ fieldValue (val4 params.modulus) inverse value = 0 ⦄ := by
  have hwords : SqrtNative.zakura_udon.field.pasta.PastaField.is_zero inst reducedInst value
      ⦃ out => out = true ↔ val4 value.limbs = 0 ⦄ := by
    have hz := Native.val4_zero_iff value.limbs
    unfold SqrtNative.zakura_udon.field.pasta.PastaField.is_zero
    simp only [
      SqrtNative.zakura_udon.field.pasta.representation.Reduced.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED,
      Native.index0_eq, Native.index1_eq, Native.index2_eq, Native.index3_eq, bind_ok, ↓reduceIte]
    split_ifs <;> simp_all [WP.spec_ok, Native.u64_eq_iff]
  step -grind with hwords as ⟨out, hout⟩
  rw [field_value_eq_zero_iff, Native.decode, Native.decoded_zero_iff _ inverse _ hinverse,
    Nat.mod_eq_of_lt hvalue]
  exact hout

#print axioms sqrt_reduce_spec
#print axioms sqrt_is_zero_reduced

end UdonVerify.SqrtNativeBridge
