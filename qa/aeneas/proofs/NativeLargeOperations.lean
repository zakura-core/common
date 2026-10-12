import NativeLargeBridge

open Aeneas Std Result

namespace UdonVerify.LargeNativeBridge
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def fieldValue {M S : Type} (p inverse : Nat) (value : Element M S) : ZMod p :=
  (Native.decode p inverse value.limbs : ZMod p)

def looseValid {M S : Type} (p : Nat) (value : Element M S) : Prop :=
  val4 value.limbs < 2 * p

def reducedValid {M S : Type} (p : Nat) (value : Element M S) : Prop :=
  val4 value.limbs < p

theorem field_value_words {M S : Type} (p inverse : Nat) (value : Element M S) :
    fieldValue p inverse value = (val4 value.limbs : ZMod p) * (inverse : ZMod p) := by
  simp only [fieldValue, Native.decode, ZMod.natCast_mod, Nat.cast_mul]

@[step]
theorem large_from_montgomery_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst)))
    (limbs : A4) (hbound : val4 limbs < 2 * val4 params.modulus) :
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.from_montgomery inst looseInst limbs
      ⦃ out => out.limbs = limbs ⦄ := by
  rw [from_montgomery_bridge]
  step -grind with (Native.from_montgomery_loose_spec (nativeModulus inst) params limbs hbound)
    as ⟨out, hout⟩
  simpa only [convertLarge, WP.spec_ok] using hout

@[step]
theorem large_multiply_spec {M S T : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (lhs : Element M S) (rhs : Element M T)
    (ha : looseValid (val4 params.modulus) lhs) (hb : looseValid (val4 params.modulus) rhs) :
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.mul inst lhs rhs
      ⦃ out => looseValid (val4 params.modulus) out ∧ fieldValue (val4 params.modulus) inverse out =
        fieldValue (val4 params.modulus) inverse lhs * fieldValue (val4 params.modulus) inverse rhs ⦄ := by
  rw [multiply_bridge]
  step -grind with (Native.multiply_spec (nativeModulus inst) params (toNative lhs) (toNative rhs) ha hb)
    as ⟨out, hout, multiplier, hmultiplier, hcertificate⟩
  refine ⟨hout, ?_⟩
  have hdecode := Native.decoded_product _ inverse _ _ _ multiplier hinverse hcertificate
  change Native.decode (val4 params.modulus) inverse out.limbs =
    (Native.decode (val4 params.modulus) inverse lhs.limbs *
      Native.decode (val4 params.modulus) inverse rhs.limbs) % val4 params.modulus at hdecode
  have hcast := congrArg (fun value : Nat => (value : ZMod (val4 params.modulus))) hdecode
  simpa only [fieldValue, convertLarge, ZMod.natCast_mod, Nat.cast_mul] using hcast

@[step]
theorem large_reduce_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    (value : Element M Loose) (hvalue : looseValid (val4 params.modulus) value) :
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.reduce inst looseInst value
      ⦃ out => reducedValid (val4 params.modulus) out ∧
        fieldValue (val4 params.modulus) inverse out = fieldValue (val4 params.modulus) inverse value ⦄ := by
  rw [reduce_loose_bridge]
  step -grind with (Native.reduce_loose_spec (nativeModulus inst) params
    (convertNative (T := Native.Loose) value) hvalue) as ⟨out, houtBound, houtValue⟩
  refine ⟨houtBound, ?_⟩
  unfold fieldValue Native.decode
  simp only [convertLarge, convertNative] at *
  rw [houtValue, Native.decoded_reduce]

@[step]
theorem large_square_eight_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (value : Element M Loose) (hvalue : looseValid (val4 params.modulus) value) :
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish.closure_1.Insts.CoreOpsFunctionFnTuplePastaFieldMLoosePastaFieldMLoose.call
      inst () value
      ⦃ out => looseValid (val4 params.modulus) out ∧
        fieldValue (val4 params.modulus) inverse out = fieldValue (val4 params.modulus) inverse value ^ 256 ⦄ := by
  unfold LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish.closure_1.Insts.CoreOpsFunctionFnTuplePastaFieldMLoosePastaFieldMLoose.call
  simp only [LargeAlgorithms.zakura_udon.field.pasta.encoding.PastaField.montgomery_limbs, bind_ok]
  rw [square_run_bridge]
  step -grind with (Native.native_square_run_spec (nativeModulus inst) params inverse hinverse
    value.limbs 8#usize none hvalue (by trivial)) as ⟨limbs, hbound, hdecode⟩
  step -grind with (large_from_montgomery_spec inst params limbs hbound) as ⟨out, hout⟩
  refine ⟨by simpa only [looseValid, hout] using hbound, ?_⟩
  have hcast := congrArg (fun result : Nat => (result : ZMod (val4 params.modulus))) hdecode
  simpa only [fieldValue, hout, ZMod.natCast_mod, Nat.cast_pow,
    show (2 : Nat) ^ 8 = 256 from by decide] using hcast

#print axioms field_value_words
#print axioms large_from_montgomery_spec
#print axioms large_multiply_spec
#print axioms large_reduce_spec
#print axioms large_square_eight_spec

end UdonVerify.LargeNativeBridge
