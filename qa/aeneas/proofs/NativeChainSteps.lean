import NativeSquareRun

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev chainDoubleN :=
  @NativeField.zakura_udon.field.pasta.parameters.Power.Insts.Zakura_bento_coreAddchainAdditionChain.double_n
abbrev chainDoubleNAdd :=
  @NativeField.zakura_udon.field.pasta.parameters.Power.Insts.Zakura_bento_coreAddchainAdditionChain.double_n_add
abbrev chainAdd :=
  @NativeField.zakura_udon.field.pasta.parameters.Power.Insts.Zakura_bento_coreAddchainAdditionChain.add

theorem modular_power_power (p base exponent count : Nat) :
    (base ^ exponent % p) ^ count % p = base ^ (exponent * count) % p := by
  rw [← Nat.pow_mod, ← pow_mul]

theorem modular_power_product (p base lhs rhs : Nat) :
    ((base ^ lhs % p) * (base ^ rhs % p)) % p = base ^ (lhs + rhs) % p := by
  rw [pow_add]
  exact (Nat.mul_mod _ _ _).symm

theorem modular_power_power_product (p base exponent count factor : Nat) :
    ((base ^ exponent % p) ^ count * (base ^ factor % p)) % p =
      base ^ (exponent * count + factor) % p := by
  calc
    _ = ((base ^ exponent) ^ count * base ^ factor) % p := by
      simp only [Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
    _ = base ^ (exponent * count + factor) % p := by rw [← pow_mul, pow_add]

@[step]
theorem chain_double_n_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (base : Nat) (value : Element M Loose) (exponent : Nat) (count : Usize)
    (hvalue : val4 value.limbs < 2 * val4 params.modulus)
    (hpower : decode (val4 params.modulus) inverse value.limbs = base ^ exponent % val4 params.modulus) :
    chainDoubleN inst value count ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
      decode (val4 params.modulus) inverse out.limbs = base ^ (exponent * 2 ^ count.val) % val4 params.modulus ⦄ := by
  unfold chainDoubleN
    NativeField.zakura_udon.field.pasta.parameters.Power.Insts.Zakura_bento_coreAddchainAdditionChain.double_n
    NativeField.zakura_udon.field.pasta.parameters.Power.double_n_add_impl
  step -grind with (native_square_run_spec inst params inverse hinverse value.limbs count none hvalue trivial)
    as ⟨limbs, hbound, hdecode⟩
  step -grind with (from_montgomery_loose_spec inst params limbs hbound) as ⟨out, hout⟩
  refine ⟨by simpa only [hout] using hbound, ?_⟩
  rw [hout, hdecode, hpower]
  exact modular_power_power _ base exponent _

@[step]
theorem chain_double_n_add_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (base : Nat) (value factor : Element M Loose) (exponent factorExponent : Nat) (count : Usize)
    (hvalue : val4 value.limbs < 2 * val4 params.modulus)
    (hfactor : val4 factor.limbs < 2 * val4 params.modulus)
    (hpower : decode (val4 params.modulus) inverse value.limbs = base ^ exponent % val4 params.modulus)
    (hfactorPower : decode (val4 params.modulus) inverse factor.limbs = base ^ factorExponent % val4 params.modulus) :
    chainDoubleNAdd inst value count factor ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
      decode (val4 params.modulus) inverse out.limbs =
        base ^ (exponent * 2 ^ count.val + factorExponent) % val4 params.modulus ⦄ := by
  unfold chainDoubleNAdd
    NativeField.zakura_udon.field.pasta.parameters.Power.Insts.Zakura_bento_coreAddchainAdditionChain.double_n_add
    NativeField.zakura_udon.field.pasta.parameters.Power.double_n_add_impl
  step -grind with (native_square_run_spec inst params inverse hinverse value.limbs count
    (some factor.limbs) hvalue hfactor) as ⟨limbs, hbound, hdecode⟩
  step -grind with (from_montgomery_loose_spec inst params limbs hbound) as ⟨out, hout⟩
  refine ⟨by simpa only [hout] using hbound, ?_⟩
  rw [hout, hdecode, hpower, hfactorPower]
  exact modular_power_power_product _ base exponent _ factorExponent

@[step]
theorem chain_add_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (base : Nat) (lhs rhs : Element M Loose) (leftExponent rightExponent : Nat)
    (hleft : val4 lhs.limbs < 2 * val4 params.modulus)
    (hright : val4 rhs.limbs < 2 * val4 params.modulus)
    (hleftPower : decode (val4 params.modulus) inverse lhs.limbs = base ^ leftExponent % val4 params.modulus)
    (hrightPower : decode (val4 params.modulus) inverse rhs.limbs = base ^ rightExponent % val4 params.modulus) :
    chainAdd inst lhs rhs ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
      decode (val4 params.modulus) inverse out.limbs = base ^ (leftExponent + rightExponent) % val4 params.modulus ⦄ := by
  unfold chainAdd
    NativeField.zakura_udon.field.pasta.parameters.Power.Insts.Zakura_bento_coreAddchainAdditionChain.add
  step -grind with (multiply_spec inst params lhs rhs hleft hright) as ⟨out, hbound, m, hm, hcert⟩
  refine ⟨hbound, ?_⟩
  have hdecode := decoded_product _ inverse _ _ _ m hinverse hcert
  change decode (val4 params.modulus) inverse out.limbs =
    (decode (val4 params.modulus) inverse lhs.limbs * decode (val4 params.modulus) inverse rhs.limbs) % val4 params.modulus at hdecode
  rw [hdecode, hleftPower, hrightPower]
  exact modular_power_product _ base leftExponent rightExponent

#print axioms chain_double_n_spec
#print axioms chain_double_n_add_spec
#print axioms chain_add_spec

end UdonVerify.Native
