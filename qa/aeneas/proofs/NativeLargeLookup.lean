import NativeLargeOperations
import NativeLargeIndex

open Aeneas Std Result

namespace UdonVerify.LargeNativeBridge
set_option maxHeartbeats 10000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- The actual reduction, word cast, hash and indexed byte lookup recover the inverse byte. -/
@[step]
theorem large_inverse_lookup_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse root : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (table : Native.LargeTable M) (multiplier : U32)
    (hchecks : Native.largeProgressionChecks (val4 params.modulus) inverse root table)
    (hlookup : Native.largeInverseChecks (val4 params.modulus) multiplier.val table)
    (hroot : (root : ZMod (val4 params.modulus)) ^ (256 ^ 4) = 1)
    (value : Element M Loose) (hvalue : looseValid (val4 params.modulus) value)
    (exponent : Nat) (hexponent : exponent < 256)
    (hcorrect : fieldValue (val4 params.modulus) inverse value *
      (root : ZMod (val4 params.modulus)) ^ (exponent * 256 ^ 3) = 1) :
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish.closure.Insts.CoreOpsFunctionFnTuplePastaFieldMLooseU32.call
      inst (table, multiplier) value ⦃ out => out.val = exponent ⦄ := by
  unfold LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish.closure.Insts.CoreOpsFunctionFnTuplePastaFieldMLooseU32.call
  step -grind with (large_reduce_spec inst params inverse value hvalue)
    as ⟨canonical, hcanonicalBound, hcanonicalValue⟩
  simp only [LargeAlgorithms.zakura_udon.field.pasta.encoding.PastaField.montgomery_limbs, bind_ok]
  step +scalarTac -grind as ⟨word, hword⟩
  simp only [lift, bind_ok]
  step -grind with (Native.large_hash_spec (UScalar.cast .U32 word) multiplier)
    as ⟨index, hindex, hindexBound⟩
  step +scalarTac -grind as ⟨byte, hbyte⟩
  try simp only [WP.spec_ok, U8.cast_U32_val_eq]
  have hkey : (UScalar.cast .U32 word).val = val4 canonical.limbs % 2 ^ 32 := by
    calc
      (UScalar.cast .U32 word).val = word.val % 2 ^ 32 := by simp [UScalar.cast_val_eq]
      _ = val4 canonical.limbs % 2 ^ 32 := by
        simpa only [hword, Array.getElem!_Nat_eq,
          getElem!_pos canonical.limbs.val 0 (by simp)] using Native.large_low_word canonical.limbs
  have hcorrectRaw : ((val4 canonical.limbs : ZMod (val4 params.modulus)) *
      (inverse : ZMod (val4 params.modulus))) *
        (root : ZMod (val4 params.modulus)) ^ (exponent * 256 ^ 3) = 1 := by
    rw [← field_value_words, hcanonicalValue]
    exact hcorrect
  have htable := Native.large_inverse_table_value (val4 params.modulus) inverse root multiplier.val
    table hchecks hlookup hinverse hroot (val4 canonical.limbs) exponent hcanonicalBound hexponent hcorrectRaw
  have hslotBound : Native.largeHash (val4 canonical.limbs % 2 ^ 32) multiplier.val < 1024 := by
    simpa only [hindex, hkey] using hindexBound
  have hslotLength : Native.largeHash (val4 canonical.limbs % 2 ^ 32) multiplier.val <
      table.inverse.val.length := by simpa using hslotBound
  simp only [Array.getElem!_Nat_eq] at htable
  rw [getElem!_pos table.inverse.val
    (Native.largeHash (val4 canonical.limbs % 2 ^ 32) multiplier.val) hslotLength] at htable
  simpa only [hbyte, hindex, hkey] using htable

#print axioms large_inverse_lookup_spec

end UdonVerify.LargeNativeBridge
