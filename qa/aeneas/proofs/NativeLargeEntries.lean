import NativeLargeLookup

open Aeneas Std Result

namespace UdonVerify.LargeNativeBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

local instance {M S : Type} : Inhabited (Element M S) :=
  ⟨{ limbs := Array.repeat 4#usize 0#u64, marker := () }⟩

/-- A checked power-table entry is canonical and decodes to its stated power. -/
@[step]
theorem large_power_entry_spec {M : Type} (p inverse root : Nat) (table : Native.LargeTable M)
    (hchecks : Native.largeProgressionChecks p inverse root table)
    (hinverse : Nat.ModEq p (R * inverse) 1) (digit : Fin 4) (length : Usize)
    (entries : Array (Element M Reduced) length)
    (hwords : ∀ index < length.val,
      val4 entries[index]!.limbs = Native.largePowerWord p table digit.val index)
    (index : Usize) (hindex : index.val < length.val) (hbyte : index.val < 256) :
    Array.index_usize entries index
      ⦃ out => reducedValid p out ∧ fieldValue p inverse out =
        (root : ZMod p) ^ (index.val * 256 ^ digit.val) ⦄ := by
  step -grind with (Array.index_usize_spec entries index (by simpa using hindex))
    as ⟨entry, hentry⟩
  have hentryEq : entry = entries[index.val]! := by
    rw [hentry]
    simp only [Array.getElem!_Nat_eq]
    rw [getElem!_pos entries.val index.val (by simpa using hindex)]
  have hword : val4 entry.limbs = Native.largePowerWord p table digit.val index.val := by
    rw [hentryEq]
    exact hwords index.val hindex
  refine ⟨?_, ?_⟩
  · change val4 entry.limbs < p
    rw [hword]
    exact ((hchecks digit).2.2 ⟨index.val, hbyte⟩).2.1
  · rw [field_value_words, hword]
    exact Native.large_progression_power p inverse root table hchecks hinverse digit index.val hbyte

@[step]
theorem large_g0_entry_spec {M : Type} (p inverse root : Nat) (table : Native.LargeTable M)
    (hchecks : Native.largeProgressionChecks p inverse root table)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (index : Usize) (hindex : index.val < 256) :
    Array.index_usize table.g0 index
      ⦃ out => reducedValid p out ∧ fieldValue p inverse out =
        (root : ZMod p) ^ (index.val * 256 ^ 0) ⦄ := by
  apply large_power_entry_spec p inverse root table hchecks hinverse ⟨0, by decide⟩ 256#usize
  · intro i hi
    simp only [Native.largePowerWord, Fin.val_mk]
  · simpa using hindex
  · omega

@[step]
theorem large_g1_entry_spec {M : Type} (p inverse root : Nat) (table : Native.LargeTable M)
    (hchecks : Native.largeProgressionChecks p inverse root table)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (index : Usize) (hindex : index.val < 256) :
    Array.index_usize table.g1 index
      ⦃ out => reducedValid p out ∧ fieldValue p inverse out =
        (root : ZMod p) ^ (index.val * 256 ^ 1) ⦄ := by
  apply large_power_entry_spec p inverse root table hchecks hinverse ⟨1, by decide⟩ 256#usize
  · intro i hi
    simp only [Native.largePowerWord, Fin.val_mk]
  · simpa using hindex
  · omega

@[step]
theorem large_g2_entry_spec {M : Type} (p inverse root : Nat) (table : Native.LargeTable M)
    (hchecks : Native.largeProgressionChecks p inverse root table)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (index : Usize) (hindex : index.val < 256) :
    Array.index_usize table.g2 index
      ⦃ out => reducedValid p out ∧ fieldValue p inverse out =
        (root : ZMod p) ^ (index.val * 256 ^ 2) ⦄ := by
  apply large_power_entry_spec p inverse root table hchecks hinverse ⟨2, by decide⟩ 256#usize
  · intro i hi
    simp only [Native.largePowerWord, Fin.val_mk]
  · simpa using hindex
  · omega

@[step]
theorem large_g3_entry_spec {M : Type} (p inverse root : Nat) (table : Native.LargeTable M)
    (hchecks : Native.largeProgressionChecks p inverse root table)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (index : Usize) (hindex : index.val < 129) :
    Array.index_usize table.g3 index
      ⦃ out => reducedValid p out ∧ fieldValue p inverse out =
        (root : ZMod p) ^ (index.val * 256 ^ 3) ⦄ := by
  apply large_power_entry_spec p inverse root table hchecks hinverse ⟨3, by decide⟩ 129#usize
  · intro i hi
    simp only [Native.largePowerWord, if_pos (by simpa using hi : i < 129), Fin.val_mk]
  · simpa using hindex
  · omega

#print axioms large_power_entry_spec
#print axioms large_g0_entry_spec
#print axioms large_g1_entry_spec
#print axioms large_g2_entry_spec
#print axioms large_g3_entry_spec

end UdonVerify.LargeNativeBridge
