import NativeSqrtParameters

open Aeneas Std Result

namespace UdonVerify.SqrtNativeBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

local instance {M S : Type} : Inhabited (Element M S) :=
  ⟨{ limbs := Array.repeat 4#usize 0#u64, marker := () }⟩
local instance {M S : Type} : Inhabited (Native.Element M S) :=
  ⟨{ limbs := Array.repeat 4#usize 0#u64, marker := () }⟩

abbrev RootTable (M : Type) := Array (Element M Reduced) 33#usize
abbrev fpSqrtRoots : RootTable Base :=
  SqrtNative.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.ROOTS
abbrev fqSqrtRoots : RootTable Scalar :=
  SqrtNative.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.ROOTS

abbrev sqrtCallback {M : Type} (inst : Modulus M) :=
  SqrtNative.zakura_udon.field.pasta.sqrt.PastaFieldMReduced.sqrt.closure.Insts.CoreOpsFunctionFnTupleU32PastaFieldMLoose inst
abbrev finishCallback {M : Type} (inst : Modulus M) :=
  SqrtNative.zakura_udon.field.pasta.sqrt.finish.closure.Insts.CoreOpsFunctionFnTupleU32PastaFieldMLoose inst

theorem fp_sqrt_root_limbs : ∀ k : Fin 33,
    fpSqrtRoots[k.val]!.limbs = Native.fpRoots[k.val]!.limbs := by
  with_unfolding_all decide

theorem fq_sqrt_root_limbs : ∀ k : Fin 33,
    fqSqrtRoots[k.val]!.limbs = Native.fqRoots[k.val]!.limbs := by
  with_unfolding_all decide

@[step]
theorem sqrt_root_lookup_spec {M N : Type} (inst : Modulus M) (p inverse : Nat)
    (roots : RootTable M) (nativeRoots nativeInverseRoots : Native.RootTable N)
    (hroots : inst.sealedParametersInst.ROOTS = ok roots)
    (hlimbs : ∀ k : Fin 33, roots[k.val]!.limbs = nativeRoots[k.val]!.limbs)
    (hchecks : Native.rootTableChecks p inverse nativeRoots nativeInverseRoots)
    (k : U32) (hbound : k.val ≤ 32) :
    (sqrtCallback inst).call () k ⦃ out => looseValid p out ∧
      fieldValue p inverse out = (Native.rootValue p inverse nativeRoots k.val : ZMod p) ⦄ := by
  change SqrtNative.zakura_udon.field.pasta.sqrt.PastaFieldMReduced.sqrt.closure.Insts.CoreOpsFunctionFnTupleU32PastaFieldMLoose.call
    inst () k ⦃ out => _ ⦄
  unfold SqrtNative.zakura_udon.field.pasta.sqrt.PastaFieldMReduced.sqrt.closure.Insts.CoreOpsFunctionFnTupleU32PastaFieldMLoose.call
  rw [hroots]
  simp only [bind_ok]
  step -grind with (UScalar.cast_inBounds_spec .Usize k (by scalar_tac))
    as ⟨index, hindexVal⟩
  step -grind with (Array.index_usize_spec roots index (by simp; omega))
    as ⟨entry, hentry⟩
  have hentryEq : entry = roots[k.val]! := by
    rw [hentry]
    simp only [Array.getElem!_Nat_eq, hindexVal]
    rw [getElem!_pos roots.val k.val (by simp; omega)]
  have hentryLimbs : entry.limbs = nativeRoots[k.val]!.limbs :=
    (congrArg (fun e : Element M Reduced => e.limbs) hentryEq).trans
      (hlimbs ⟨k.val, by omega⟩)
  have hentryBound : val4 entry.limbs < p := by
    rw [hentryLimbs]
    exact (hchecks ⟨k.val, by omega⟩).1
  unfold SqrtNative.zakura_udon.field.pasta.PastaField.into_loose
  simp only [WP.spec_ok]
  refine ⟨by change val4 entry.limbs < 2 * p; omega, ?_⟩
  change (Native.decode p inverse entry.limbs : ZMod p) = _
  rw [hentryLimbs]
  rfl

theorem finish_callback_eq {M : Type} (inst : Modulus M) (k : U32) :
    (finishCallback inst).call () k = (sqrtCallback inst).call () k := by
  rfl

def fpRootsContract : Sqrt.Roots fpOperations (sqrtCallback fpSqrtInst) () 32#u32 where
  value k := (Native.rootValue Native.fpPrime Native.fpRadixInverse Native.fpRoots k : ZMod Native.fpPrime)
  lookup := by
    intro k _ hbound
    exact sqrt_root_lookup_spec fpSqrtInst Native.fpPrime Native.fpRadixInverse
      fpSqrtRoots Native.fpRoots Native.fpInverseRoots (by with_unfolding_all rfl)
      fp_sqrt_root_limbs Native.fp_root_table_checks k hbound
  half_power := by
    intro k hk hbound
    exact Native.root_half_power _ _ _ _ Native.fp_root_table_checks
      (by have hp := Native.fp_prime.two_le; omega) k hk hbound
  next_square := by
    intro k _ hbound
    exact Native.root_next_square _ _ _ _ Native.fp_root_table_checks k hbound

def fqRootsContract : Sqrt.Roots fqOperations (sqrtCallback fqSqrtInst) () 32#u32 where
  value k := (Native.rootValue Native.fqPrime Native.fqRadixInverse Native.fqRoots k : ZMod Native.fqPrime)
  lookup := by
    intro k _ hbound
    exact sqrt_root_lookup_spec fqSqrtInst Native.fqPrime Native.fqRadixInverse
      fqSqrtRoots Native.fqRoots Native.fqInverseRoots (by with_unfolding_all rfl)
      fq_sqrt_root_limbs Native.fq_root_table_checks k hbound
  half_power := by
    intro k hk hbound
    exact Native.root_half_power _ _ _ _ Native.fq_root_table_checks
      (by have hp := Native.fq_prime.two_le; omega) k hk hbound
  next_square := by
    intro k _ hbound
    exact Native.root_next_square _ _ _ _ Native.fq_root_table_checks k hbound

def fpFinishRoots : Sqrt.Roots fpOperations (finishCallback fpSqrtInst) () 32#u32 where
  value := fpRootsContract.value
  lookup := by
    intro k hk hb
    rw [finish_callback_eq]
    exact fpRootsContract.lookup k hk hb
  half_power := fpRootsContract.half_power
  next_square := fpRootsContract.next_square

def fqFinishRoots : Sqrt.Roots fqOperations (finishCallback fqSqrtInst) () 32#u32 where
  value := fqRootsContract.value
  lookup := by
    intro k hk hb
    rw [finish_callback_eq]
    exact fqRootsContract.lookup k hk hb
  half_power := fqRootsContract.half_power
  next_square := fqRootsContract.next_square

#print axioms fpRootsContract
#print axioms fqRootsContract
#print axioms fpFinishRoots
#print axioms fqFinishRoots

end UdonVerify.SqrtNativeBridge
