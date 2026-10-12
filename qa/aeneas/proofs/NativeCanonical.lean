import NativeRepresentation

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev CanonicalUint := NativeField.zakura_udon.field.pasta.uint.CanonicalUint

theorem fp_native_prime_eq : val4 fpNativeParameters.modulus = fpPrime := by rfl
theorem fq_native_prime_eq : val4 fqNativeParameters.modulus = fqPrime := by rfl

theorem ordering_is_lt_eq :
    NativeField.core.cmp.Ordering.is_lt Ordering.eq = ok false := by rfl

theorem ordering_is_lt_gt :
    NativeField.core.cmp.Ordering.is_lt Ordering.gt = ok false := by rfl

theorem canonical_multiply_eq {M : Type} (inst : Modulus M) (lhs rhs : A4) :
    NativeField.zakura_udon.field.pasta.montgomery.montgomery_multiply inst lhs rhs =
      udon_kernel_slice.field.pasta.montgomery.montgomery_multiply (kernelInst inst) lhs rhs := by rfl

theorem canonical_reduce_eq {M : Type} (inst : Modulus M) (limbs : A8) :
    NativeField.zakura_udon.field.pasta.montgomery.montgomery_reduce inst limbs =
      udon_kernel_slice.field.pasta.montgomery.montgomery_reduce (kernelInst inst) limbs := by
  rfl

theorem decoded_redc (p inverse a u : Nat)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (hcongruence : Nat.ModEq p (R * u) a) (hu : u < p) :
    u = (a * inverse) % p := by
  have hc : Nat.ModEq p ((R * inverse) * u) (a * inverse) := by
    convert hcongruence.mul_right inverse using 1 <;> ring
  have hi : Nat.ModEq p ((R * inverse) * u) u := by
    simpa using hinverse.mul_right u
  have h := hi.symm.trans hc
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hu] using h

@[step]
theorem canonical_limbs_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (value : Element M S)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (ha : val4 value.limbs < 2 * val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.canonical_limbs inst value
      ⦃ out => val4 out < val4 params.modulus ∧
        val4 out = decode (val4 params.modulus) inverse value.limbs ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.encoding.PastaField.canonical_limbs
  step -grind as ⟨slice, back, hslice, hsize, hback⟩
  step -grind as ⟨source, hsource⟩
  step -grind as ⟨copied, hcopied⟩
  have hwide : val8 (back copied) = val4 value.limbs := by
    simp [val8, val4, Array.getElem!_Nat_eq, hback, hcopied, hsource]
    simp_lists [List.getElem!_setSlice!_middle, List.getElem!_setSlice!_suffix]
    norm_num
  have hinput : val8 (back copied) < val4 params.modulus * R := by
    rw [hwide]
    have hp := params.positive
    have hr : 2 < R := by norm_num [R, B]
    nlinarith only [ha, hp, hr]
  rw [canonical_reduce_eq]
  step -grind with (montgomery_reduce_spec (kernelInst inst) params (back copied) hinput)
    as ⟨out, hout, hcongruence⟩
  refine ⟨hout, ?_⟩
  unfold decode
  rw [hwide] at hcongruence
  exact decoded_redc _ inverse _ _ hinverse hcongruence hout

@[step]
theorem to_canonical_uint_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (value : Element M S)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (ha : val4 value.limbs < 2 * val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.to_canonical_uint inst value
      ⦃ out => val4 out.limbs < val4 params.modulus ∧
        val4 out.limbs = decode (val4 params.modulus) inverse value.limbs ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.encoding.PastaField.to_canonical_uint
  step -grind with (canonical_limbs_spec inst params value inverse hinverse ha)
    as ⟨limbs, hbound, hdecode⟩
  simp only [NativeField.zakura_udon.field.pasta.uint.CanonicalUint.from_limbs, bind_ok]
  exact ⟨hbound, hdecode⟩

@[step]
theorem from_canonical_uint_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst))
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S)
    (bound inverse : Nat) (value : CanonicalUint)
    (hconstructor : ∀ limbs : A4, val4 limbs < val4 params.modulus →
      NativeField.zakura_udon.field.pasta.encoding.PastaField.from_canonical_limbs inst state limbs
        ⦃ out => val4 out.limbs < bound ∧
          decode (val4 params.modulus) inverse out.limbs = val4 limbs ⦄) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_canonical_uint inst state value
      ⦃ out => match out with
        | none => val4 params.modulus ≤ val4 value.limbs
        | some result => val4 value.limbs < val4 params.modulus ∧
            val4 result.limbs < bound ∧
            decode (val4 params.modulus) inverse result.limbs = val4 value.limbs ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.encoding.PastaField.from_canonical_uint
  simp only [NativeField.zakura_udon.field.pasta.uint.CanonicalUint.impl.limbs, bind_ok]
  have hmodulus : inst.MODULUS = ok params.modulus := params.modulus_ok
  rw [hmodulus]
  simp only [bind_ok]
  rw [compare_eq]
  step -grind with (slice_compare_limbs_spec value.limbs params.modulus) as ⟨order, horder⟩
  cases order with
  | lt =>
      have hlt : val4 value.limbs < val4 params.modulus := horder
      simp only [ordering_is_lt, bind_ok]
      unfold core.bool.Bool.then
      simp only [↓reduceIte]
      simp only [NativeField.zakura_udon.field.pasta.encoding.PastaField.from_canonical_uint.closure.Insts.CoreOpsFunctionFnOnceTuplePastaField.call_once,
        NativeField.zakura_udon.field.pasta.uint.CanonicalUint.impl.limbs,bind_ok]
      step -grind with (hconstructor value.limbs hlt) as ⟨out, hbound, hdecode⟩
      exact ⟨hlt, hbound, hdecode⟩
  | eq =>
      rw [ordering_is_lt_eq]
      simp only [bind_ok, core.bool.Bool.then, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      simpa only [orderingRel] using horder.ge
  | gt =>
      rw [ordering_is_lt_gt]
      simp only [bind_ok, core.bool.Bool.then, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact Nat.le_of_lt horder

@[step]
theorem from_uint_reduced_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : ConversionParameters inst params)
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S)
    (bound inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (value : CanonicalUint)
    (hconstructor : ∀ limbs : A4, val4 limbs < 2 * val4 params.modulus →
      NativeField.zakura_udon.field.pasta.PastaField.from_loose inst state limbs
        ⦃ out => val4 out.limbs < bound ∧
          Nat.ModEq (val4 params.modulus) (val4 out.limbs) (val4 limbs) ⦄) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_uint_reduced inst state value
      ⦃ out => val4 out.limbs < bound ∧
        decode (val4 params.modulus) inverse out.limbs = val4 value.limbs % val4 params.modulus ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.encoding.PastaField.from_uint_reduced
  simp only [NativeField.zakura_udon.field.pasta.uint.CanonicalUint.impl.limbs, bind_ok]
  rw [constants.radix2_ok]
  simp only [bind_ok]
  rw [canonical_multiply_eq]
  have hr2 : val4 constants.radix2 < val4 params.modulus := by
    rw [constants.radix2_val]
    exact Nat.mod_lt _ params.positive
  have hvalue := val4_lt value.limbs
  have hproduct : val4 value.limbs * val4 constants.radix2 < val4 params.modulus * R := by
    nlinarith only [hvalue, hr2, params.positive]
  step -grind with (montgomery_multiply_bounded_spec (kernelInst inst) params
      value.limbs constants.radix2 (Or.inr hproduct)) as ⟨limbs, hbound, m, hm, hcert⟩
  step -grind with (hconstructor limbs hbound) as ⟨out, hout, hcongruence⟩
  refine ⟨hout, ?_⟩
  have hr2mod : Nat.ModEq (val4 params.modulus) (val4 constants.radix2) (R ^ 2) := by
    unfold Nat.ModEq
    rw [constants.radix2_val, Nat.mod_mod]
  have hc := hcongruence.mul_right inverse
  exact hc.trans (decoded_conversion _ inverse _ _ _ m hinverse hr2mod hcert)

#print axioms canonical_limbs_spec

end UdonVerify.Native
