import NativeEncoding
import NativeHalf

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem uint_bit_zero_spec (value : CanonicalUint) :
    NativeField.zakura_udon.field.pasta.uint.CanonicalUint.bit value 0#usize
      ⦃ out => out = some (decide (val4 value.limbs % 2 = 1)) ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.uint.CanonicalUint.bit
  simp only [NativeField.zakura_udon.field.pasta.ENCODED_SIZE]
  step -grind as ⟨size, hsize⟩
  have hsizeeq : size = 256#usize := by scalar_tac
  subst size
  simp only [show 0#usize < 256#usize from by decide, if_pos]
  step -grind as ⟨index, hindex⟩
  have hindexeq : index = 0#usize := by scalar_tac
  subst index
  step -grind as ⟨word, hword⟩
  step -grind as ⟨shift, hshift⟩
  have hshifteq : shift = 0#usize := by scalar_tac
  subst shift
  step -grind as ⟨mask, hmask⟩
  have hmaskeq : mask = 1#u64 := by scalar_tac
  subst mask
  step -grind with UScalar.and_spec as ⟨parity, hparity, hparitybound⟩
  have hp : parity.val = val4 value.limbs % 2 := by
    simp only [UScalar.val_and] at hparity
    change parity.val = word.val &&& 1 at hparity
    rw [show word.val &&& 1 = word.val % 2 by
      simpa using Nat.and_two_pow_sub_one_eq_mod word.val 1] at hparity
    simpa [hword, val4_parity] using hparity
  have hval : parity.val < 2 := by rw [hp]; omega
  have hne : (parity != 0#u64) = decide (val4 value.limbs % 2 = 1) := by
    by_cases hz : parity.val = 0
    · have hzero : parity = 0#u64 := UScalar.eq_of_val_eq hz
      have hmod : val4 value.limbs % 2 = 0 := by omega
      subst parity
      simp [hmod]
    · have hv : parity.val = 1 := by omega
      have hone : parity = 1#u64 := UScalar.eq_of_val_eq hv
      have hmod : val4 value.limbs % 2 = 1 := by omega
      subst parity
      simp [hmod]
  exact congrArg some hne

@[step]
theorem is_odd_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (value : Element M S)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (ha : val4 value.limbs < 2 * val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.is_odd inst value
      ⦃ out => out = decide (decode (val4 params.modulus) inverse value.limbs % 2 = 1) ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.encoding.PastaField.is_odd
  step -grind with (to_canonical_uint_spec inst params value inverse hinverse ha)
    as ⟨integer, hbound, hvalue⟩
  step -grind with (uint_bit_zero_spec integer) as ⟨result, hresult⟩
  rw [hresult]
  rw [← hvalue]
  cases h : decide (val4 integer.limbs % 2 = 1) <;>
    simp [core.option.Option.Insts.CoreCmpPartialEqOption.eq,core.cmp.PartialEqBool,core.cmp.impls.PartialEqBool.eq,h,WP.spec_ok]

@[step]
theorem fp_is_odd_spec (value : Element Base Loose) (ha : val4 value.limbs < 2 * fpPrime) :
    NativeField.fp_is_odd value ⦃ out => out = decide (decode fpPrime fpRadixInverse value.limbs % 2 = 1) ⦄ := by
  unfold NativeField.fp_is_odd
  simpa only [fp_native_prime_eq] using
    is_odd_spec fpNativeInst fpNativeParameters value fpRadixInverse fp_radix_inverse ha

@[step]
theorem fq_is_odd_spec (value : Element Scalar Loose) (ha : val4 value.limbs < 2 * fqPrime) :
    NativeField.fq_is_odd value ⦃ out => out = decide (decode fqPrime fqRadixInverse value.limbs % 2 = 1) ⦄ := by
  unfold NativeField.fq_is_odd
  simpa only [fq_native_prime_eq] using
    is_odd_spec fqNativeInst fqNativeParameters value fqRadixInverse fq_radix_inverse ha

@[step]
theorem fp_is_odd_reduced_spec (value : Element Base Reduced) (ha : val4 value.limbs < fpPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.is_odd fpNativeInst value
      ⦃ out => out = decide (decode fpPrime fpRadixInverse value.limbs % 2 = 1) ⦄ := by
  simpa only [fp_native_prime_eq] using
    is_odd_spec fpNativeInst fpNativeParameters value fpRadixInverse fp_radix_inverse
      (by rw [fp_native_prime_eq]; omega)

@[step]
theorem fq_is_odd_reduced_spec (value : Element Scalar Reduced) (ha : val4 value.limbs < fqPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.is_odd fqNativeInst value
      ⦃ out => out = decide (decode fqPrime fqRadixInverse value.limbs % 2 = 1) ⦄ := by
  simpa only [fq_native_prime_eq] using
    is_odd_spec fqNativeInst fqNativeParameters value fqRadixInverse fq_radix_inverse
      (by rw [fq_native_prime_eq]; omega)

#print axioms fp_is_odd_spec

end UdonVerify.Native
