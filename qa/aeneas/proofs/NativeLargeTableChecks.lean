import LargeAlgorithms.Funs
import NativeRootTables

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024

abbrev LargeElement := LargeAlgorithms.zakura_udon.field.pasta.PastaField
abbrev LargeReduced := LargeAlgorithms.zakura_udon.field.pasta.representation.Reduced
abbrev LargeTable (M : Type) :=
  LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTable (LargeElement M LargeReduced)

local instance {M S : Type} : Inhabited (LargeElement M S) :=
  ⟨{ limbs := Array.repeat 4#usize 0#u64, marker := () }⟩

noncomputable abbrev fpLargeTable := LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase.SQRT_TABLE
noncomputable abbrev fqLargeTable := LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar.SQRT_TABLE

/-- Extend the truncated fourth table using the order-256 element's negative half. -/
def largePowerWord {M : Type} (p : Nat) (table : LargeTable M) (digit index : Nat) : Nat :=
  match digit with
  | 0 => val4 table.g0[index]!.limbs
  | 1 => val4 table.g1[index]!.limbs
  | 2 => val4 table.g2[index]!.limbs
  | _ => if index < 129 then val4 table.g3[index]!.limbs
    else p - val4 table.g3[index - 128]!.limbs

def largeHash (key multiplier : Nat) : Nat := ((key * multiplier) % 2 ^ 32) / 2 ^ 22

/-- Finite checks of the shipped Montgomery words and each power progression. -/
def largeProgressionChecks {M : Type} (p inverse root : Nat) (table : LargeTable M) : Prop :=
  ∀ digit : Fin 4,
    largePowerWord p table digit.val 0 = R % p ∧
    (largePowerWord p table digit.val 1 * inverse) % p = powMod p root (256 ^ digit.val) ∧
    ∀ index : Fin 256,
      0 < largePowerWord p table digit.val index.val ∧
      largePowerWord p table digit.val index.val < p ∧
      (index.val < 255 → largePowerWord p table digit.val (index.val + 1) =
        (largePowerWord p table digit.val index.val *
          largePowerWord p table digit.val 1 * inverse) % p)

/-- Every order-256 subgroup value maps to its actual inverse-exponent byte. -/
def largeInverseChecks {M : Type} (p multiplier : Nat) (table : LargeTable M) : Prop :=
  ∀ index : Fin 256,
    table.inverse[largeHash (largePowerWord p table 3 index.val % 2 ^ 32) multiplier]!.val =
      (256 - index.val) % 256

theorem fp_large_progression_checks :
    largeProgressionChecks fpPrime fpRadixInverse
      (rootValue fpPrime fpRadixInverse fpRoots 32) fpLargeTable := by
  unfold largeProgressionChecks
  with_unfolding_all decide

theorem fq_large_progression_checks :
    largeProgressionChecks fqPrime fqRadixInverse
      (rootValue fqPrime fqRadixInverse fqRoots 32) fqLargeTable := by
  unfold largeProgressionChecks
  with_unfolding_all decide

theorem fp_large_inverse_checks : largeInverseChecks fpPrime 0x54c11db5 fpLargeTable := by
  unfold largeInverseChecks
  with_unfolding_all decide

theorem fq_large_inverse_checks : largeInverseChecks fqPrime 0x4b7fdd31 fqLargeTable := by
  unfold largeInverseChecks
  with_unfolding_all decide

#print axioms fp_large_progression_checks
#print axioms fq_large_progression_checks
#print axioms fp_large_inverse_checks
#print axioms fq_large_inverse_checks

end UdonVerify.Native
