import NativeLargeConfig

open Aeneas Std Result

namespace UdonVerify.LargeNativeBridge
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def largeAltResult {M : Type} (p inverse : Nat) (a root : ZMod p)
    (out : Bool × Element M Reduced) : Prop :=
  reducedValid p out.2 ∧ fieldValue p inverse out.2 ^ 2 = a * (if out.1 then 1 else root) ∧
    (out.1 = true ↔ IsSquare a)

@[step]
theorem fp_large_sqrt_callback_spec
    (value : Element LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase Reduced) (w : Element LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase Loose)
    (hv : reducedValid Native.fpPrime value)
    (ha : fieldValue Native.fpPrime Native.fpRadixInverse value ≠ 0)
    (hw : looseValid Native.fpPrime w)
    (hpower : (fieldValue Native.fpPrime Native.fpRadixInverse value *
      fieldValue Native.fpPrime Native.fpRadixInverse w ^ 2) ^ (256 ^ 4) = 1) :
    LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.sqrt_large value w ⦃ out =>
      largeSqrtResult Native.fpPrime Native.fpRadixInverse
        (fieldValue Native.fpPrime Native.fpRadixInverse value) out ⦄ := by
  letI : Fact (Nat.Prime (val4 fpLargeParameters.modulus)) := ⟨Native.fp_prime⟩
  unfold LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.sqrt_large
  with_unfolding_all exact (large_sqrt_spec fpLargeInst fpLargeParameters Native.fpRadixInverse fpLargeRoot
      Native.fp_radix_inverse Native.fpLargeTable 0x54c11db5#u32 Native.fp_large_progression_checks
      Native.fp_large_inverse_checks fp_large_root_primitive fp_large_root_nonsquare
      value hv ha w hw hpower)

@[step]
theorem fp_large_finish_callback_spec
    (a : ZMod Native.fpPrime) (ha : a ≠ 0)
    (x t : Element LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase Loose)
    (hx : looseValid Native.fpPrime x) (ht : looseValid Native.fpPrime t)
    (hsquare : fieldValue Native.fpPrime Native.fpRadixInverse x ^ 2 =
      a * fieldValue Native.fpPrime Native.fpRadixInverse t)
    (hpower : fieldValue Native.fpPrime Native.fpRadixInverse t ^ (256 ^ 4) = 1) :
    LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.sqrt_finish_large x t ⦃ out =>
      largeAltResult Native.fpPrime Native.fpRadixInverse a (fpLargeRoot : ZMod Native.fpPrime) out ⦄ := by
  letI : Fact (Nat.Prime (val4 fpLargeParameters.modulus)) := ⟨Native.fp_prime⟩
  unfold LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.sqrt_finish_large
  have hfinish :
      LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish
        fpLargeInst Native.fpLargeTable x t 0x54c11db5#u32 ⦃ out =>
          looseValid Native.fpPrime out.2 ∧
          fieldValue Native.fpPrime Native.fpRadixInverse out.2 ^ 2 = a * (if out.1 then 1 else (fpLargeRoot : ZMod Native.fpPrime)) ∧
          (out.1 = true ↔ IsSquare a) ⦄ := by
    with_unfolding_all exact (large_finish_square_spec fpLargeInst fpLargeParameters Native.fpRadixInverse fpLargeRoot
        Native.fp_radix_inverse Native.fpLargeTable 0x54c11db5#u32 Native.fp_large_progression_checks
        Native.fp_large_inverse_checks fp_large_root_primitive fp_large_root_nonsquare
        a ha x t hx ht hsquare hpower)
  step -grind with hfinish as ⟨flag, candidate, hcBound, hcSquare, hflag⟩
  have hreduce : LargeAlgorithms.zakura_udon.field.pasta.PastaField.reduce fpLargeInst looseInst candidate ⦃ out =>
      reducedValid Native.fpPrime out ∧ fieldValue Native.fpPrime Native.fpRadixInverse out =
        fieldValue Native.fpPrime Native.fpRadixInverse candidate ⦄ := by
    with_unfolding_all exact large_reduce_spec fpLargeInst fpLargeParameters Native.fpRadixInverse candidate hcBound
  step -grind with hreduce as ⟨canonical, hcanonicalBound, hcanonicalValue⟩
  try simp only [largeAltResult]
  refine ⟨hcanonicalBound, ?_, hflag⟩
  rw [hcanonicalValue]
  exact hcSquare

@[step]
theorem fq_large_sqrt_callback_spec
    (value : Element LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar Reduced) (w : Element LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar Loose)
    (hv : reducedValid Native.fqPrime value)
    (ha : fieldValue Native.fqPrime Native.fqRadixInverse value ≠ 0)
    (hw : looseValid Native.fqPrime w)
    (hpower : (fieldValue Native.fqPrime Native.fqRadixInverse value *
      fieldValue Native.fqPrime Native.fqRadixInverse w ^ 2) ^ (256 ^ 4) = 1) :
    LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.sqrt_large value w ⦃ out =>
      largeSqrtResult Native.fqPrime Native.fqRadixInverse
        (fieldValue Native.fqPrime Native.fqRadixInverse value) out ⦄ := by
  letI : Fact (Nat.Prime (val4 fqLargeParameters.modulus)) := ⟨Native.fq_prime⟩
  unfold LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.sqrt_large
  with_unfolding_all exact (large_sqrt_spec fqLargeInst fqLargeParameters Native.fqRadixInverse fqLargeRoot
      Native.fq_radix_inverse Native.fqLargeTable 0x4b7fdd31#u32 Native.fq_large_progression_checks
      Native.fq_large_inverse_checks fq_large_root_primitive fq_large_root_nonsquare
      value hv ha w hw hpower)

@[step]
theorem fq_large_finish_callback_spec
    (a : ZMod Native.fqPrime) (ha : a ≠ 0)
    (x t : Element LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar Loose)
    (hx : looseValid Native.fqPrime x) (ht : looseValid Native.fqPrime t)
    (hsquare : fieldValue Native.fqPrime Native.fqRadixInverse x ^ 2 =
      a * fieldValue Native.fqPrime Native.fqRadixInverse t)
    (hpower : fieldValue Native.fqPrime Native.fqRadixInverse t ^ (256 ^ 4) = 1) :
    LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.sqrt_finish_large x t ⦃ out =>
      largeAltResult Native.fqPrime Native.fqRadixInverse a (fqLargeRoot : ZMod Native.fqPrime) out ⦄ := by
  letI : Fact (Nat.Prime (val4 fqLargeParameters.modulus)) := ⟨Native.fq_prime⟩
  unfold LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.sqrt_finish_large
  have hfinish :
      LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish
        fqLargeInst Native.fqLargeTable x t 0x4b7fdd31#u32 ⦃ out =>
          looseValid Native.fqPrime out.2 ∧
          fieldValue Native.fqPrime Native.fqRadixInverse out.2 ^ 2 = a * (if out.1 then 1 else (fqLargeRoot : ZMod Native.fqPrime)) ∧
          (out.1 = true ↔ IsSquare a) ⦄ := by
    with_unfolding_all exact (large_finish_square_spec fqLargeInst fqLargeParameters Native.fqRadixInverse fqLargeRoot
        Native.fq_radix_inverse Native.fqLargeTable 0x4b7fdd31#u32 Native.fq_large_progression_checks
        Native.fq_large_inverse_checks fq_large_root_primitive fq_large_root_nonsquare
        a ha x t hx ht hsquare hpower)
  step -grind with hfinish as ⟨flag, candidate, hcBound, hcSquare, hflag⟩
  have hreduce : LargeAlgorithms.zakura_udon.field.pasta.PastaField.reduce fqLargeInst looseInst candidate ⦃ out =>
      reducedValid Native.fqPrime out ∧ fieldValue Native.fqPrime Native.fqRadixInverse out =
        fieldValue Native.fqPrime Native.fqRadixInverse candidate ⦄ := by
    with_unfolding_all exact large_reduce_spec fqLargeInst fqLargeParameters Native.fqRadixInverse candidate hcBound
  step -grind with hreduce as ⟨canonical, hcanonicalBound, hcanonicalValue⟩
  try simp only [largeAltResult]
  refine ⟨hcanonicalBound, ?_, hflag⟩
  rw [hcanonicalValue]
  exact hcSquare

#print axioms fp_large_sqrt_callback_spec
#print axioms fp_large_finish_callback_spec
#print axioms fq_large_sqrt_callback_spec
#print axioms fq_large_finish_callback_spec

end UdonVerify.LargeNativeBridge
