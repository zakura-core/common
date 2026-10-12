import NativeRootLookup
import NativeRootOrder

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

local instance {M S : Type} : Inhabited (Element M S) :=
  ⟨{ limbs := Array.repeat 4#usize 0#u64, marker := () }⟩

def unityResult {M S : Type} (p inverse : Nat) (logSize : U32)
    (out : Option (Element M S)) : Prop :=
  match out with
  | none => 32 < logSize.val
  | some value => logSize.val ≤ 32 ∧ val4 value.limbs < p ∧
      decode p inverse value.limbs = powMod p 5 ((p - 1) / 2 ^ logSize.val) ∧
      IsPrimitiveRoot (decode p inverse value.limbs : ZMod p) (2 ^ logSize.val)

def unityInverseResult {M S : Type} (p inverse : Nat) (logSize : U32)
    (out : Option (Element M S)) : Prop :=
  match out with
  | none => 32 < logSize.val
  | some value => logSize.val ≤ 32 ∧ val4 value.limbs < p ∧
      (powMod p 5 ((p - 1) / 2 ^ logSize.val) * decode p inverse value.limbs) % p = 1 ∧
      IsPrimitiveRoot (decode p inverse value.limbs : ZMod p) (2 ^ logSize.val)

theorem unity_result_of_lookup {M S : Type} (p inverse : Nat)
    (roots inverseRoots : RootTable M) (logSize : U32) (out : Option (Element M S))
    (hp : 2 < p) (hchecks : rootTableChecks p inverse roots inverseRoots)
    (hlookup : rootLookupResult roots logSize out) : unityResult p inverse logSize out := by
  cases out with
  | none => exact hlookup
  | some value =>
    rcases hlookup with ⟨hlog, hlimbs⟩
    let k : Fin 33 := ⟨logSize.val, by omega⟩
    have hc := hchecks k
    refine ⟨hlog, ?_, ?_, ?_⟩
    · rw [hlimbs]
      exact hc.1
    · rw [hlimbs]
      exact hc.2.2.1
    · rw [hlimbs]
      exact checked_power_two_primitive p _ k.val hp hlog hc.2.2.2.2.1 hc.2.2.2.2.2.1

theorem unity_inverse_result_of_lookup {M S : Type} (p inverse : Nat)
    (roots inverseRoots : RootTable M) (logSize : U32) (out : Option (Element M S))
    (hp : 2 < p) (hchecks : rootTableChecks p inverse roots inverseRoots)
    (hlookup : rootLookupResult inverseRoots logSize out) : unityInverseResult p inverse logSize out := by
  cases out with
  | none => exact hlookup
  | some value =>
    rcases hlookup with ⟨hlog, hlimbs⟩
    let k : Fin 33 := ⟨logSize.val, by omega⟩
    have hc := hchecks k
    refine ⟨hlog, ?_, ?_, ?_⟩
    · rw [hlimbs]
      exact hc.2.1
    · rw [hlimbs]
      have hproduct := hc.2.2.2.1
      rw [hc.2.2.1] at hproduct
      exact hproduct
    · rw [hlimbs]
      exact checked_power_two_primitive p _ k.val hp hlog
        hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2

@[step]
theorem fp_root_of_unity_spec (logSize : U32) :
    NativeField.fp_root_of_unity logSize ⦃ out => unityResult fpPrime fpRadixInverse logSize out ⦄ := by
  unfold NativeField.fp_root_of_unity
  apply WP.spec_mono (root_of_unity_lookup_spec fpNativeInst fpNativeParameters looseInst
    fpRoots logSize (by with_unfolding_all rfl)
    (fun k => (fp_root_table_checks k).1)
    (fun limbs hlimbs => from_montgomery_loose_spec fpNativeInst fpNativeParameters limbs (by omega)))
  intro out hout
  exact unity_result_of_lookup _ _ fpRoots fpInverseRoots logSize out
    (by with_unfolding_all decide) fp_root_table_checks hout

#print axioms fp_root_of_unity_spec

@[step]
theorem fp_root_of_unity_reduced_spec (logSize : U32) :
    NativeField.zakura_udon.field.pasta.sqrt.PastaField.root_of_unity fpNativeInst reducedInst logSize ⦃ out => unityResult fpPrime fpRadixInverse logSize out ⦄ := by
  apply WP.spec_mono (root_of_unity_lookup_spec fpNativeInst fpNativeParameters reducedInst
    fpRoots logSize (by with_unfolding_all rfl)
    (fun k => (fp_root_table_checks k).1)
    (fun limbs hlimbs => from_montgomery_reduced_spec fpNativeInst fpNativeParameters limbs hlimbs))
  intro out hout
  exact unity_result_of_lookup _ _ fpRoots fpInverseRoots logSize out
    (by with_unfolding_all decide) fp_root_table_checks hout

#print axioms fp_root_of_unity_reduced_spec

@[step]
theorem fp_root_of_unity_inverse_spec (logSize : U32) :
    NativeField.fp_root_of_unity_inverse logSize ⦃ out => unityInverseResult fpPrime fpRadixInverse logSize out ⦄ := by
  unfold NativeField.fp_root_of_unity_inverse
  apply WP.spec_mono (root_of_unity_inverse_lookup_spec fpNativeInst fpNativeParameters looseInst
    fpInverseRoots logSize (by with_unfolding_all rfl)
    (fun k => (fp_root_table_checks k).2.1)
    (fun limbs hlimbs => from_montgomery_loose_spec fpNativeInst fpNativeParameters limbs (by omega)))
  intro out hout
  exact unity_inverse_result_of_lookup _ _ fpRoots fpInverseRoots logSize out
    (by with_unfolding_all decide) fp_root_table_checks hout

#print axioms fp_root_of_unity_inverse_spec

@[step]
theorem fp_root_of_unity_inverse_reduced_spec (logSize : U32) :
    NativeField.zakura_udon.field.pasta.sqrt.PastaField.root_of_unity_inverse fpNativeInst reducedInst logSize ⦃ out => unityInverseResult fpPrime fpRadixInverse logSize out ⦄ := by
  apply WP.spec_mono (root_of_unity_inverse_lookup_spec fpNativeInst fpNativeParameters reducedInst
    fpInverseRoots logSize (by with_unfolding_all rfl)
    (fun k => (fp_root_table_checks k).2.1)
    (fun limbs hlimbs => from_montgomery_reduced_spec fpNativeInst fpNativeParameters limbs hlimbs))
  intro out hout
  exact unity_inverse_result_of_lookup _ _ fpRoots fpInverseRoots logSize out
    (by with_unfolding_all decide) fp_root_table_checks hout

#print axioms fp_root_of_unity_inverse_reduced_spec

@[step]
theorem fq_root_of_unity_spec (logSize : U32) :
    NativeField.fq_root_of_unity logSize ⦃ out => unityResult fqPrime fqRadixInverse logSize out ⦄ := by
  unfold NativeField.fq_root_of_unity
  apply WP.spec_mono (root_of_unity_lookup_spec fqNativeInst fqNativeParameters looseInst
    fqRoots logSize (by with_unfolding_all rfl)
    (fun k => (fq_root_table_checks k).1)
    (fun limbs hlimbs => from_montgomery_loose_spec fqNativeInst fqNativeParameters limbs (by omega)))
  intro out hout
  exact unity_result_of_lookup _ _ fqRoots fqInverseRoots logSize out
    (by with_unfolding_all decide) fq_root_table_checks hout

#print axioms fq_root_of_unity_spec

@[step]
theorem fq_root_of_unity_reduced_spec (logSize : U32) :
    NativeField.zakura_udon.field.pasta.sqrt.PastaField.root_of_unity fqNativeInst reducedInst logSize ⦃ out => unityResult fqPrime fqRadixInverse logSize out ⦄ := by
  apply WP.spec_mono (root_of_unity_lookup_spec fqNativeInst fqNativeParameters reducedInst
    fqRoots logSize (by with_unfolding_all rfl)
    (fun k => (fq_root_table_checks k).1)
    (fun limbs hlimbs => from_montgomery_reduced_spec fqNativeInst fqNativeParameters limbs hlimbs))
  intro out hout
  exact unity_result_of_lookup _ _ fqRoots fqInverseRoots logSize out
    (by with_unfolding_all decide) fq_root_table_checks hout

#print axioms fq_root_of_unity_reduced_spec

@[step]
theorem fq_root_of_unity_inverse_spec (logSize : U32) :
    NativeField.fq_root_of_unity_inverse logSize ⦃ out => unityInverseResult fqPrime fqRadixInverse logSize out ⦄ := by
  unfold NativeField.fq_root_of_unity_inverse
  apply WP.spec_mono (root_of_unity_inverse_lookup_spec fqNativeInst fqNativeParameters looseInst
    fqInverseRoots logSize (by with_unfolding_all rfl)
    (fun k => (fq_root_table_checks k).2.1)
    (fun limbs hlimbs => from_montgomery_loose_spec fqNativeInst fqNativeParameters limbs (by omega)))
  intro out hout
  exact unity_inverse_result_of_lookup _ _ fqRoots fqInverseRoots logSize out
    (by with_unfolding_all decide) fq_root_table_checks hout

#print axioms fq_root_of_unity_inverse_spec

@[step]
theorem fq_root_of_unity_inverse_reduced_spec (logSize : U32) :
    NativeField.zakura_udon.field.pasta.sqrt.PastaField.root_of_unity_inverse fqNativeInst reducedInst logSize ⦃ out => unityInverseResult fqPrime fqRadixInverse logSize out ⦄ := by
  apply WP.spec_mono (root_of_unity_inverse_lookup_spec fqNativeInst fqNativeParameters reducedInst
    fqInverseRoots logSize (by with_unfolding_all rfl)
    (fun k => (fq_root_table_checks k).2.1)
    (fun limbs hlimbs => from_montgomery_reduced_spec fqNativeInst fqNativeParameters limbs hlimbs))
  intro out hout
  exact unity_inverse_result_of_lookup _ _ fqRoots fqInverseRoots logSize out
    (by with_unfolding_all decide) fq_root_table_checks hout

#print axioms fq_root_of_unity_inverse_reduced_spec

end UdonVerify.Native
