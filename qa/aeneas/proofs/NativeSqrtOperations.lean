import NativeSqrtBridge

open Aeneas Std Result

namespace UdonVerify.SqrtNativeBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def fieldValue {M S : Type} (p inverse : Nat) (value : Element M S) : ZMod p :=
  (Native.decode p inverse value.limbs : ZMod p)

def looseValid {M S : Type} (p : Nat) (value : Element M S) : Prop :=
  val4 value.limbs < 2 * p

abbrev sqrtInst {M : Type} (inst : Modulus M) := algorithmsSqrtField
  (SqrtNative.zakura_udon.field.pasta.PastaFieldMLoose.Insts.Zakura_udonFieldPastaAlgorithmsSqrtField inst)

theorem field_value_eq_zero_iff {M S : Type} (p inverse : Nat) (value : Element M S) :
    fieldValue p inverse value = 0 ↔ Native.decode p inverse value.limbs = 0 := by
  unfold fieldValue
  have h := ZMod.natCast_eq_natCast_iff' (Native.decode p inverse value.limbs) 0 p
  simpa only [Nat.cast_zero, Native.decode, Nat.mod_mod, Nat.zero_mod] using h

theorem field_value_eq_one_iff {M S : Type} (p inverse : Nat) (value : Element M S)
    (hp : 1 < p) :
    fieldValue p inverse value = 1 ↔ Native.decode p inverse value.limbs = 1 := by
  unfold fieldValue
  have h := ZMod.natCast_eq_natCast_iff' (Native.decode p inverse value.limbs) 1 p
  simpa only [Nat.cast_one, Native.decode, Nat.mod_mod, Nat.mod_eq_of_lt hp] using h

@[step]
theorem sqrt_multiply_spec {M S T : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (lhs : Element M S) (rhs : Element M T)
    (ha : looseValid (val4 params.modulus) lhs) (hb : looseValid (val4 params.modulus) rhs) :
    SqrtNative.zakura_udon.field.pasta.PastaField.mul inst lhs rhs ⦃ out =>
      looseValid (val4 params.modulus) out ∧ fieldValue (val4 params.modulus) inverse out =
        fieldValue (val4 params.modulus) inverse lhs * fieldValue (val4 params.modulus) inverse rhs ⦄ := by
  rw [multiply_bridge]
  step -grind with (Native.multiply_spec (nativeModulus inst) params (toNative lhs) (toNative rhs) ha hb)
    as ⟨out, hout, multiplier, hmultiplier, hcertificate⟩
  refine ⟨hout, ?_⟩
  have hdecode := Native.decoded_product _ inverse _ _ _ multiplier hinverse hcertificate
  change Native.decode (val4 params.modulus) inverse out.limbs =
    (Native.decode (val4 params.modulus) inverse lhs.limbs *
      Native.decode (val4 params.modulus) inverse rhs.limbs) % val4 params.modulus at hdecode
  have hcast := congrArg (fun x : Nat => (x : ZMod (val4 params.modulus))) hdecode
  simpa only [fieldValue, convertSqrt, ZMod.natCast_mod, Nat.cast_mul] using hcast

@[step]
theorem sqrt_square_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (value : Element M S) (ha : looseValid (val4 params.modulus) value) :
    SqrtNative.zakura_udon.field.pasta.PastaField.square inst value ⦃ out =>
      looseValid (val4 params.modulus) out ∧ fieldValue (val4 params.modulus) inverse out =
        fieldValue (val4 params.modulus) inverse value ^ 2 ⦄ := by
  rw [square_bridge]
  step -grind with (Native.square_spec (nativeModulus inst) params (toNative value) ha)
    as ⟨out, hout, multiplier, hmultiplier, hcertificate⟩
  refine ⟨hout, ?_⟩
  have hdecode := Native.decoded_product _ inverse _ _ _ multiplier hinverse
    (by simpa only [pow_two] using hcertificate)
  change Native.decode (val4 params.modulus) inverse out.limbs =
    (Native.decode (val4 params.modulus) inverse value.limbs *
      Native.decode (val4 params.modulus) inverse value.limbs) % val4 params.modulus at hdecode
  have hcast := congrArg (fun x : Nat => (x : ZMod (val4 params.modulus))) hdecode
  simpa only [fieldValue, convertSqrt, ZMod.natCast_mod, Nat.cast_mul, pow_two] using hcast

def nativeOperations {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst)))
    (constants : Native.ConversionParameters (nativeModulus inst) params)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    [Fact (Nat.Prime (val4 params.modulus))] :
    Sqrt.Operations (K := ZMod (val4 params.modulus)) (sqrtInst inst) where
  value := fieldValue (val4 params.modulus) inverse
  valid := looseValid (val4 params.modulus)
  zero := by
    simp only [sqrtInst, algorithmsSqrtField,
      SqrtNative.zakura_udon.field.pasta.PastaFieldMLoose.Insts.Zakura_udonFieldPastaAlgorithmsSqrtField.ZERO,
      WP.spec_ok]
    have hzero : val4 (SqrtNative.zakura_udon.field.pasta.PastaField.ZERO M Loose).limbs = 0 := by
      norm_num [SqrtNative.zakura_udon.field.pasta.PastaField.ZERO, val4, Array.repeat]
    refine ⟨?_, ?_⟩
    · unfold looseValid
      rw [hzero]
      have hp := params.positive
      omega
    · simp only [fieldValue, Native.decode, hzero, zero_mul, Nat.zero_mod, Nat.cast_zero]
  zero_test := by
    intro value hvalid
    change SqrtNative.zakura_udon.field.pasta.PastaField.is_zero inst looseInst value ⦃ out => _ ⦄
    rw [is_zero_bridge]
    step -grind with (Native.is_zero_loose_spec (nativeModulus inst) params
      (convertNative (T := Native.Loose) value)) as ⟨out, hout⟩
    rw [field_value_eq_zero_iff, Native.decode,
      Native.decoded_zero_iff _ inverse _ hinverse]
    exact hout.trans (Native.loose_mod_zero_iff _ _ params.positive hvalid).symm
  one_test := by
    intro value hvalid
    change SqrtNative.zakura_udon.field.pasta.PastaField.is_one inst looseInst value ⦃ out => _ ⦄
    rw [is_one_bridge]
    step -grind with (Native.is_one_loose_spec (nativeModulus inst) params constants (convertNative (T := Native.Loose) value)) as ⟨out, hout⟩
    have hp : 1 < val4 params.modulus := by
      have h := params.offset_positive
      norm_num only [R, B] at h
      omega
    rw [field_value_eq_one_iff _ _ _ hp, Native.decode,
      Native.decoded_one_iff _ inverse _ hp hinverse]
    rw [← constants.radix_val]
    exact hout.trans (Native.loose_mod_representative_iff _ _ _ params.positive
      (by rw [constants.radix_val]; exact Nat.mod_lt _ params.positive) hvalid).symm
  square := by
    intro value hvalid
    change SqrtNative.zakura_udon.field.pasta.PastaField.square inst value ⦃ out => _ ⦄
    exact sqrt_square_spec inst params inverse hinverse value hvalid
  mul := by
    intro lhs rhs hleft hright
    change SqrtNative.zakura_udon.field.pasta.PastaField.mul inst lhs rhs ⦃ out => _ ⦄
    exact sqrt_multiply_spec inst params inverse hinverse lhs rhs hleft hright

#print axioms sqrt_multiply_spec
#print axioms sqrt_square_spec
#print axioms nativeOperations

end UdonVerify.SqrtNativeBridge
