import NativeCanonical
import Pratt

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

abbrev RootTable (M : Type) := Array (Element M Reduced) 33#usize

local instance {M S : Type} : Inhabited (Element M S) :=
  ⟨{ limbs := Array.repeat 4#usize 0#u64, marker := () }⟩

abbrev fpRoots : RootTable Base :=
  NativeField.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.ROOTS
abbrev fqRoots : RootTable Scalar :=
  NativeField.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.ROOTS
abbrev fpInverseRoots : RootTable Base :=
  NativeField.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.INVERSE_ROOTS
abbrev fqInverseRoots : RootTable Scalar :=
  NativeField.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.INVERSE_ROOTS

def rootValue {M : Type} (p inverse : Nat) (roots : RootTable M) (k : Nat) : Nat :=
  decode p inverse roots[k]!.limbs

/-- Finite checks on the compiled tables, interpreted as ordinary field integers. -/
def rootTableChecks {M : Type} (p inverse : Nat)
    (roots inverseRoots : RootTable M) : Prop :=
  ∀ k : Fin 33,
    val4 roots[k.val]!.limbs < p ∧ val4 inverseRoots[k.val]!.limbs < p ∧
    rootValue p inverse roots k = powMod p 5 ((p - 1) / 2 ^ k.val) ∧
    (rootValue p inverse roots k * rootValue p inverse inverseRoots k) % p = 1 ∧
    powMod p (rootValue p inverse roots k) (2 ^ k.val) = 1 ∧
    (0 < k.val → powMod p (rootValue p inverse roots k) (2 ^ (k.val - 1)) = p - 1) ∧
    (k.val < 32 → (rootValue p inverse roots (k.val + 1)) ^ 2 % p =
      rootValue p inverse roots k) ∧
    powMod p (rootValue p inverse inverseRoots k) (2 ^ k.val) = 1 ∧
    (0 < k.val → powMod p (rootValue p inverse inverseRoots k) (2 ^ (k.val - 1)) = p - 1)

theorem fp_root_table_checks :
    rootTableChecks fpPrime fpRadixInverse fpRoots fpInverseRoots := by
  unfold rootTableChecks
  with_unfolding_all decide

theorem fq_root_table_checks :
    rootTableChecks fqPrime fqRadixInverse fqRoots fqInverseRoots := by
  unfold rootTableChecks
  with_unfolding_all decide

#print axioms fp_root_table_checks
#print axioms fq_root_table_checks

end UdonVerify.Native
