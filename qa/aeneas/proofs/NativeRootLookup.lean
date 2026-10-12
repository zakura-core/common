import NativeRootTables

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

local instance {M S : Type} : Inhabited (Element M S) :=
  ⟨{ limbs := Array.repeat 4#usize 0#u64, marker := () }⟩

/-- Lookup returns exactly the selected table entry, and rejects larger indices. -/
def rootLookupResult {M S : Type} (roots : RootTable M) (logSize : U32)
    (out : Option (Element M S)) : Prop :=
  match out with
  | none => 32 < logSize.val
  | some value => logSize.val ≤ 32 ∧ value.limbs = roots[logSize.val]!.limbs

@[step]
theorem root_of_unity_lookup_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst))
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S)
    (roots : RootTable M) (logSize : U32)
    (hroots : inst.sealedParametersInst.ROOTS = ok roots)
    (hbound : ∀ k : Fin 33, val4 roots[k.val]!.limbs < val4 params.modulus)
    (hconstructor : ∀ limbs : A4, val4 limbs < val4 params.modulus →
      NativeField.zakura_udon.field.pasta.PastaField.from_montgomery inst state limbs
        ⦃ out => out.limbs = limbs ⦄) :
    NativeField.zakura_udon.field.pasta.sqrt.PastaField.root_of_unity inst state logSize
      ⦃ out => rootLookupResult roots logSize out ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.sqrt.PastaField.root_of_unity
  simp only [NativeField.zakura_udon.field.pasta.TWO_ADICITY]
  split
  · simp only [WP.spec_ok, rootLookupResult]
    scalar_tac
  · have hindex : logSize.val < 33 := by scalar_tac
    rw [hroots]
    simp only [bind_ok]
    step -grind with (UScalar.cast_inBounds_spec .Usize logSize (by scalar_tac))
      as ⟨index, hindexVal⟩
    step -grind with (Array.index_usize_spec roots index (by simp; omega))
      as ⟨entry, hentry⟩
    have hentryEq : entry = roots[logSize.val]! := by
      rw [hentry]
      simp only [Array.getElem!_Nat_eq, hindexVal]
      rw [getElem!_pos roots.val logSize.val (by simpa using hindex)]
    have hentryBound : val4 entry.limbs < val4 params.modulus := by
      simpa only [hentryEq] using hbound ⟨logSize.val, hindex⟩
    step -grind with (hconstructor entry.limbs hentryBound) as ⟨value, hvalue⟩
    exact ⟨by omega, hvalue.trans (congrArg (fun e : Element M Reduced => e.limbs) hentryEq)⟩

@[step]
theorem root_of_unity_inverse_lookup_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst))
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S)
    (roots : RootTable M) (logSize : U32)
    (hroots : inst.sealedParametersInst.INVERSE_ROOTS = ok roots)
    (hbound : ∀ k : Fin 33, val4 roots[k.val]!.limbs < val4 params.modulus)
    (hconstructor : ∀ limbs : A4, val4 limbs < val4 params.modulus →
      NativeField.zakura_udon.field.pasta.PastaField.from_montgomery inst state limbs
        ⦃ out => out.limbs = limbs ⦄) :
    NativeField.zakura_udon.field.pasta.sqrt.PastaField.root_of_unity_inverse inst state logSize
      ⦃ out => rootLookupResult roots logSize out ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.sqrt.PastaField.root_of_unity_inverse
  simp only [NativeField.zakura_udon.field.pasta.TWO_ADICITY]
  split
  · simp only [WP.spec_ok, rootLookupResult]
    scalar_tac
  · have hindex : logSize.val < 33 := by scalar_tac
    rw [hroots]
    simp only [bind_ok]
    step -grind with (UScalar.cast_inBounds_spec .Usize logSize (by scalar_tac))
      as ⟨index, hindexVal⟩
    step -grind with (Array.index_usize_spec roots index (by simp; omega))
      as ⟨entry, hentry⟩
    have hentryEq : entry = roots[logSize.val]! := by
      rw [hentry]
      simp only [Array.getElem!_Nat_eq, hindexVal]
      rw [getElem!_pos roots.val logSize.val (by simpa using hindex)]
    have hentryBound : val4 entry.limbs < val4 params.modulus := by
      simpa only [hentryEq] using hbound ⟨logSize.val, hindex⟩
    step -grind with (hconstructor entry.limbs hentryBound) as ⟨value, hvalue⟩
    exact ⟨by omega, hvalue.trans (congrArg (fun e : Element M Reduced => e.limbs) hentryEq)⟩

#print axioms root_of_unity_lookup_spec
#print axioms root_of_unity_inverse_lookup_spec

end UdonVerify.Native
