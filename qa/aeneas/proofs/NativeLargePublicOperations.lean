import NativeLargePublicBridge

open Aeneas Std Result

namespace UdonVerify.LargePublicBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def fieldValue {M S : Type} (p inverse : Nat) (value : Element M S) : ZMod p :=
  (Native.decode p inverse value.limbs : ZMod p)

def looseValid {M S : Type} (p : Nat) (value : Element M S) : Prop :=
  val4 value.limbs < 2 * p

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
    LargePublic.zakura_udon.field.pasta.PastaField.mul inst lhs rhs ⦃ out =>
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
  simpa only [fieldValue, convertPublic, ZMod.natCast_mod, Nat.cast_mul] using hcast

@[step]
theorem sqrt_square_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (value : Element M S) (ha : looseValid (val4 params.modulus) value) :
    LargePublic.zakura_udon.field.pasta.PastaField.square inst value ⦃ out =>
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
  simpa only [fieldValue, convertPublic, ZMod.natCast_mod, Nat.cast_mul, pow_two] using hcast

#print axioms sqrt_multiply_spec
#print axioms sqrt_square_spec

end UdonVerify.LargePublicBridge
