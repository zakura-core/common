import LargeAlgorithms.Funs
import NativeBasics
import NativeSquareRun

open Aeneas Std Result

namespace UdonVerify.LargeNativeBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev Modulus := LargeAlgorithms.zakura_udon.field.pasta.parameters.PrimeModulus
abbrev Element := LargeAlgorithms.zakura_udon.field.pasta.PastaField
abbrev Loose := LargeAlgorithms.zakura_udon.field.pasta.representation.Loose
abbrev Reduced := LargeAlgorithms.zakura_udon.field.pasta.representation.Reduced
abbrev looseInst :=
  LargeAlgorithms.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState

def toNative {M S : Type} (value : Element M S) : Native.Element M S :=
  { limbs := value.limbs, marker := () }

def fromNative {M S : Type} (value : Native.Element M S) : Element M S :=
  { limbs := value.limbs, marker := () }

def convertNative {M S T : Type} (value : Element M S) : Native.Element M T :=
  { limbs := value.limbs, marker := () }

def convertLarge {M S T : Type} (value : Native.Element M S) : Element M T :=
  { limbs := value.limbs, marker := () }

def nativeRootTable {M : Type} (roots : Array (Element M Reduced) 33#usize) :
    Array (Native.Element M Native.Reduced) 33#usize :=
  Array.from (roots.val.map convertNative) (by simp)

/-- Transfer the same parameter data; both marker representations are Unit. -/
def nativeModulus {M : Type} (inst : Modulus M) : Native.Modulus M where
  MODULUS := inst.MODULUS
  sealedSealedInst := {}
  coremarkerCopyInst := inst.coremarkerCopyInst
  corecmpEqInst := inst.corecmpEqInst
  sealedParametersInst := {
    ROOTS := do let roots ← inst.sealedParametersInst.ROOTS; ok (nativeRootTable roots)
    INVERSE_ROOTS := do let roots ← inst.sealedParametersInst.INVERSE_ROOTS; ok (nativeRootTable roots)
    TWICE_MODULUS := inst.sealedParametersInst.TWICE_MODULUS
    MONTGOMERY_INV := inst.sealedParametersInst.MONTGOMERY_INV
    R := inst.sealedParametersInst.R
    R2 := inst.sealedParametersInst.R2
    R3 := inst.sealedParametersInst.R3
    B448 := inst.sealedParametersInst.B448
    TWO_INVERSE := inst.sealedParametersInst.TWO_INVERSE
    DELTA := inst.sealedParametersInst.DELTA
    ZETA := inst.sealedParametersInst.ZETA
    ZETA_INVERSE := inst.sealedParametersInst.ZETA_INVERSE
    MODULUS_SIGNED62 := inst.sealedParametersInst.MODULUS_SIGNED62
    POWER_OF_TWO_INVERSES := inst.sealedParametersInst.POWER_OF_TWO_INVERSES
  }

theorem from_montgomery_bridge {M : Type} (inst : Modulus M) (limbs : UdonVerify.A4) :
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.from_montgomery inst looseInst limbs = (do
      let out ← NativeField.zakura_udon.field.pasta.PastaField.from_montgomery
        (nativeModulus inst) Native.looseInst limbs
      ok (convertLarge (T := Loose) out)) := by
  unfold LargeAlgorithms.zakura_udon.field.pasta.PastaField.from_montgomery
    NativeField.zakura_udon.field.pasta.PastaField.from_montgomery
  simp only [Std.bind_assoc, bind_ok]
  with_unfolding_all rfl

theorem montgomery_multiply_bridge {M : Type} (inst : Modulus M) (lhs rhs : UdonVerify.A4) :
    LargeAlgorithms.zakura_udon.field.pasta.montgomery.montgomery_multiply_loose inst lhs rhs =
      NativeField.zakura_udon.field.pasta.montgomery.montgomery_multiply_loose (nativeModulus inst) lhs rhs := by
  with_unfolding_all rfl

theorem multiply_bridge {M S T : Type} (inst : Modulus M) (lhs : Element M S) (rhs : Element M T) :
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.mul inst lhs rhs = (do
      let out ← NativeField.zakura_udon.field.pasta.PastaField.mul
        (nativeModulus inst) (toNative lhs) (toNative rhs)
      ok (convertLarge (T := Loose) out)) := by
  unfold LargeAlgorithms.zakura_udon.field.pasta.PastaField.mul
    NativeField.zakura_udon.field.pasta.PastaField.mul
  rw [montgomery_multiply_bridge]
  simp only [Std.bind_assoc]
  congr 1
  funext limbs
  exact from_montgomery_bridge inst limbs

theorem reduce_loose_bridge {M : Type} (inst : Modulus M) (value : Element M Loose) :
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.reduce inst looseInst value = (do
      let out ← NativeField.zakura_udon.field.pasta.PastaField.reduce
        (nativeModulus inst) Native.looseInst (convertNative (T := Native.Loose) value)
      ok (convertLarge (T := Reduced) out)) := by
  unfold LargeAlgorithms.zakura_udon.field.pasta.PastaField.reduce
    NativeField.zakura_udon.field.pasta.PastaField.reduce
  simp only [
    LargeAlgorithms.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED,
    NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED,
    bind_ok, Bool.false_eq_true, ↓reduceIte, Std.bind_assoc]
  with_unfolding_all rfl

theorem square_run_bridge {M : Type} (inst : Modulus M) (value : A4)
    (count : Usize) (factor : Option A4) :
    LargeAlgorithms.zakura_udon.field.pasta.montgomery.square_run inst value count factor =
      NativeField.zakura_udon.field.pasta.montgomery.square_run (nativeModulus inst) value count factor := by
  with_unfolding_all rfl

#print axioms from_montgomery_bridge
#print axioms multiply_bridge
#print axioms reduce_loose_bridge
#print axioms square_run_bridge

end UdonVerify.LargeNativeBridge
