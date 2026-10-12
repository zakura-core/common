import NativeLargePublicContracts
import NativeLargeCallbacks

open Aeneas Std Result

namespace UdonVerify.LargePublicBridge
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem fp_large_callback_spec (value : Element Base Reduced) (w : Element Base Loose)
    (hv : reducedValid Native.fpPrime value)
    (ha : fieldValue Native.fpPrime Native.fpRadixInverse value ≠ 0)
    (hw : looseValid Native.fpPrime w)
    (hpower : (fieldValue Native.fpPrime Native.fpRadixInverse value *
      fieldValue Native.fpPrime Native.fpRadixInverse w ^ 2) ^ (2 ^ 32) = 1) :
    fpSqrtInst.sealedParametersInst.sqrt_large value w ⦃ out =>
      sqrtResult Native.fpPrime Native.fpRadixInverse
        (fieldValue Native.fpPrime Native.fpRadixInverse value) out ⦄ := by
  change LargePublic.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.sqrt_large value w ⦃ out => _ ⦄
  unfold LargePublic.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.sqrt_large
  step -grind with (LargeNativeBridge.fp_large_sqrt_callback_spec
    { limbs := value.limbs, marker := () } { limbs := w.limbs, marker := () } hv ha hw
    (by simpa only [fieldValue, LargeNativeBridge.fieldValue, show (2 : Nat) ^ 32 = 256 ^ 4 from by decide] using hpower)) as ⟨root, hroot⟩
  cases root with
  | none =>
      simpa only [WP.spec_ok, sqrtResult, fieldValue, LargeNativeBridge.fieldValue, LargeNativeBridge.largeSqrtResult] using hroot
  | some root =>
      simpa only [WP.spec_ok, sqrtResult, fieldValue, reducedValid,
        LargeNativeBridge.largeSqrtResult, LargeNativeBridge.fieldValue, LargeNativeBridge.reducedValid] using hroot

@[step]
theorem fp_large_finish_spec (a : ZMod Native.fpPrime) (ha : a ≠ 0)
    (x t : Element Base Loose) (hx : looseValid Native.fpPrime x) (ht : looseValid Native.fpPrime t)
    (hsquare : fieldValue Native.fpPrime Native.fpRadixInverse x ^ 2 =
      a * fieldValue Native.fpPrime Native.fpRadixInverse t)
    (hpower : fieldValue Native.fpPrime Native.fpRadixInverse t ^ (2 ^ 32) = 1) :
    fpSqrtInst.sealedParametersInst.sqrt_finish_large x t ⦃ out =>
      sqrtAltResult Native.fpPrime Native.fpRadixInverse a (LargeNativeBridge.fpLargeRoot : ZMod Native.fpPrime) out ⦄ := by
  change LargePublic.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.sqrt_finish_large x t ⦃ out => _ ⦄
  unfold LargePublic.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.sqrt_finish_large
  step -grind with (LargeNativeBridge.fp_large_finish_callback_spec a ha
    { limbs := x.limbs, marker := () } { limbs := t.limbs, marker := () } hx ht hsquare
    (by simpa only [fieldValue, LargeNativeBridge.fieldValue, show (2 : Nat) ^ 32 = 256 ^ 4 from by decide] using hpower)) as ⟨flag, root, hroot⟩
  simpa only [sqrtAltResult, fieldValue, reducedValid,
    LargeNativeBridge.largeAltResult, LargeNativeBridge.fieldValue, LargeNativeBridge.reducedValid] using hroot

@[step]
theorem fq_large_callback_spec (value : Element Scalar Reduced) (w : Element Scalar Loose)
    (hv : reducedValid Native.fqPrime value)
    (ha : fieldValue Native.fqPrime Native.fqRadixInverse value ≠ 0)
    (hw : looseValid Native.fqPrime w)
    (hpower : (fieldValue Native.fqPrime Native.fqRadixInverse value *
      fieldValue Native.fqPrime Native.fqRadixInverse w ^ 2) ^ (2 ^ 32) = 1) :
    fqSqrtInst.sealedParametersInst.sqrt_large value w ⦃ out =>
      sqrtResult Native.fqPrime Native.fqRadixInverse
        (fieldValue Native.fqPrime Native.fqRadixInverse value) out ⦄ := by
  change LargePublic.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.sqrt_large value w ⦃ out => _ ⦄
  unfold LargePublic.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.sqrt_large
  step -grind with (LargeNativeBridge.fq_large_sqrt_callback_spec
    { limbs := value.limbs, marker := () } { limbs := w.limbs, marker := () } hv ha hw
    (by simpa only [fieldValue, LargeNativeBridge.fieldValue, show (2 : Nat) ^ 32 = 256 ^ 4 from by decide] using hpower)) as ⟨root, hroot⟩
  cases root with
  | none =>
      simpa only [WP.spec_ok, sqrtResult, fieldValue, LargeNativeBridge.fieldValue, LargeNativeBridge.largeSqrtResult] using hroot
  | some root =>
      simpa only [WP.spec_ok, sqrtResult, fieldValue, reducedValid,
        LargeNativeBridge.largeSqrtResult, LargeNativeBridge.fieldValue, LargeNativeBridge.reducedValid] using hroot

@[step]
theorem fq_large_finish_spec (a : ZMod Native.fqPrime) (ha : a ≠ 0)
    (x t : Element Scalar Loose) (hx : looseValid Native.fqPrime x) (ht : looseValid Native.fqPrime t)
    (hsquare : fieldValue Native.fqPrime Native.fqRadixInverse x ^ 2 =
      a * fieldValue Native.fqPrime Native.fqRadixInverse t)
    (hpower : fieldValue Native.fqPrime Native.fqRadixInverse t ^ (2 ^ 32) = 1) :
    fqSqrtInst.sealedParametersInst.sqrt_finish_large x t ⦃ out =>
      sqrtAltResult Native.fqPrime Native.fqRadixInverse a (LargeNativeBridge.fqLargeRoot : ZMod Native.fqPrime) out ⦄ := by
  change LargePublic.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.sqrt_finish_large x t ⦃ out => _ ⦄
  unfold LargePublic.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.sqrt_finish_large
  step -grind with (LargeNativeBridge.fq_large_finish_callback_spec a ha
    { limbs := x.limbs, marker := () } { limbs := t.limbs, marker := () } hx ht hsquare
    (by simpa only [fieldValue, LargeNativeBridge.fieldValue, show (2 : Nat) ^ 32 = 256 ^ 4 from by decide] using hpower)) as ⟨flag, root, hroot⟩
  simpa only [sqrtAltResult, fieldValue, reducedValid,
    LargeNativeBridge.largeAltResult, LargeNativeBridge.fieldValue, LargeNativeBridge.reducedValid] using hroot

#print axioms fp_large_callback_spec
#print axioms fp_large_finish_spec
#print axioms fq_large_callback_spec
#print axioms fq_large_finish_spec

end UdonVerify.LargePublicBridge
