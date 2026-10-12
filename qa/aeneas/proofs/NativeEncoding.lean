import NativeEncodingCaps
import NativeByteEncode

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem from_bytes_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst))
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S)
    (bound inverse : Nat) (bytes : Bytes32)
    (hconstructor : ∀ limbs : A4, val4 limbs < val4 params.modulus →
      NativeField.zakura_udon.field.pasta.encoding.PastaField.from_canonical_limbs inst state limbs
        ⦃ out => val4 out.limbs < bound ∧
          decode (val4 params.modulus) inverse out.limbs = val4 limbs ⦄) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes inst state bytes
      ⦃ out => match out with
        | none => val4 params.modulus ≤ byteValue bytes.val
        | some result => byteValue bytes.val < val4 params.modulus ∧
            val4 result.limbs < bound ∧
            decode (val4 params.modulus) inverse result.limbs = byteValue bytes.val ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes
  step -grind with (uint_from_bytes_spec bytes) as ⟨integer, hinteger⟩
  apply WP.spec_mono (from_canonical_uint_spec inst params state bound inverse integer hconstructor)
  intro out hout
  cases out <;> simpa only [hinteger] using hout

@[step]
theorem to_bytes_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (value : Element M S)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (ha : val4 value.limbs < 2 * val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes inst value
      ⦃ out => byteValue out.val < val4 params.modulus ∧
        byteValue out.val = decode (val4 params.modulus) inverse value.limbs ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes
  step -grind with (to_canonical_uint_spec inst params value inverse hinverse ha)
    as ⟨integer, hbound, hvalue⟩
  step -grind with (uint_to_bytes_spec integer) as ⟨out, hout⟩
  exact ⟨by simpa only [hout] using hbound, hout.trans hvalue⟩

theorem canonical_bytes_roundtrip {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst))
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (bound : Nat) (hbound : bound ≤ 2 * val4 params.modulus) (bytes : Bytes32)
    (hbytes : byteValue bytes.val < val4 params.modulus)
    (hconstructor : ∀ limbs : A4, val4 limbs < val4 params.modulus →
      NativeField.zakura_udon.field.pasta.encoding.PastaField.from_canonical_limbs inst state limbs
        ⦃ out => val4 out.limbs < bound ∧
          decode (val4 params.modulus) inverse out.limbs = val4 limbs ⦄) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes inst state bytes
      ⦃ out => ∃ value : Element M S, out = some value ∧
        NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes inst value
          ⦃ encoded => encoded = bytes ⦄ ⦄ := by
  apply WP.spec_mono (from_bytes_spec inst params state bound inverse bytes hconstructor)
  intro out hout
  cases out with
  | none => simp only at hout; omega
  | some value =>
    simp only at hout
    refine ⟨value, rfl, ?_⟩
    have hv : val4 value.limbs < 2 * val4 params.modulus := by omega
    step -grind with (to_bytes_spec inst params value inverse hinverse hv)
      as ⟨encoded, hcanonical, hvalue⟩
    apply (Array.eq_iff encoded bytes).mpr
    apply byteValue_injective
    · simp
    · exact hvalue.trans hout.2.2

theorem field_bytes_roundtrip {M S T : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst))
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (bound : Nat) (value : Element M T) (ha : val4 value.limbs < 2 * val4 params.modulus)
    (hconstructor : ∀ limbs : A4, val4 limbs < val4 params.modulus →
      NativeField.zakura_udon.field.pasta.encoding.PastaField.from_canonical_limbs inst state limbs
        ⦃ out => val4 out.limbs < bound ∧
          decode (val4 params.modulus) inverse out.limbs = val4 limbs ⦄) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes inst value
      ⦃ bytes => NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes inst state bytes
        ⦃ out => ∃ decoded : Element M S, out = some decoded ∧ val4 decoded.limbs < bound ∧
          decode (val4 params.modulus) inverse decoded.limbs =
            decode (val4 params.modulus) inverse value.limbs ⦄ ⦄ := by
  step -grind with (to_bytes_spec inst params value inverse hinverse ha)
    as ⟨bytes, hbound, hvalue⟩
  apply WP.spec_mono (from_bytes_spec inst params state bound inverse bytes hconstructor)
  intro out hout
  cases out with
  | none => simp only at hout; omega
  | some decoded =>
    simp only at hout
    exact ⟨decoded, rfl, hout.2.1, hout.2.2.trans hvalue⟩

theorem uint_bytes_roundtrip (bytes : Bytes32) :
    NativeField.zakura_udon.field.pasta.uint.CanonicalUint.from_le_bytes bytes
      ⦃ integer => NativeField.zakura_udon.field.pasta.uint.CanonicalUint.to_le_bytes integer
        ⦃ encoded => encoded = bytes ⦄ ⦄ := by
  step -grind with (uint_from_bytes_spec bytes) as ⟨integer, hinteger⟩
  step -grind with (uint_to_bytes_spec integer) as ⟨encoded, hencoded⟩
  apply (Array.eq_iff encoded bytes).mpr
  exact byteValue_injective _ _ (by simp) (hencoded.trans hinteger)

#print axioms canonical_bytes_roundtrip

end UdonVerify.Native
