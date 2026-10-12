module
public import Aeneas
public import LargePublic.Types
public import NativeField.Funs
public import LargeAlgorithms.Funs
@[expose] public section

open Aeneas Std Result

namespace LargePublic

noncomputable section

/-- Invoke the extracted Rust callback through its four-limb representation. -/
def zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.pow_sqrt_exponent
    (value : zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasBase zakura_udon.field.pasta.representation.Loose) :
    Result (zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasBase zakura_udon.field.pasta.representation.Loose) := do
  let input : NativeField.zakura_udon.field.pasta.PastaField NativeField.zakura_udon.field.pasta.parameters.PallasBase
      NativeField.zakura_udon.field.pasta.representation.Loose := { limbs := value.limbs, marker := () }
  let result ← NativeField.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.pow_sqrt_exponent input
  ok { limbs := result.limbs, marker := () }

/-- Invoke the extracted Rust callback through its four-limb representation. -/
def zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.pow_sqrt_exponent
    (value : zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasScalar zakura_udon.field.pasta.representation.Loose) :
    Result (zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasScalar zakura_udon.field.pasta.representation.Loose) := do
  let input : NativeField.zakura_udon.field.pasta.PastaField NativeField.zakura_udon.field.pasta.parameters.PallasScalar
      NativeField.zakura_udon.field.pasta.representation.Loose := { limbs := value.limbs, marker := () }
  let result ← NativeField.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.pow_sqrt_exponent input
  ok { limbs := result.limbs, marker := () }

/-- Invoke the separately extracted large-table Rust callback, preserving all four limbs. -/
def zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.sqrt_large
    (value : zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasBase zakura_udon.field.pasta.representation.Reduced)
    (w : zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasBase zakura_udon.field.pasta.representation.Loose) :
    Result (Option (zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasBase zakura_udon.field.pasta.representation.Reduced)) := do
  let input : LargeAlgorithms.zakura_udon.field.pasta.PastaField LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase LargeAlgorithms.zakura_udon.field.pasta.representation.Reduced :=
    { limbs := value.limbs, marker := () }
  let seed : LargeAlgorithms.zakura_udon.field.pasta.PastaField LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase LargeAlgorithms.zakura_udon.field.pasta.representation.Loose :=
    { limbs := w.limbs, marker := () }
  let result ← LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.sqrt_large input seed
  match result with
  | none => ok none
  | some root => ok (some { limbs := root.limbs, marker := () })

/-- Invoke the separately extracted finish-and-reduce callback with its original flag. -/
def zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.sqrt_finish_large
    (x t : zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasBase zakura_udon.field.pasta.representation.Loose) :
    Result (Bool × (zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasBase zakura_udon.field.pasta.representation.Reduced)) := do
  let input : LargeAlgorithms.zakura_udon.field.pasta.PastaField LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase LargeAlgorithms.zakura_udon.field.pasta.representation.Loose :=
    { limbs := x.limbs, marker := () }
  let subgroup : LargeAlgorithms.zakura_udon.field.pasta.PastaField LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase LargeAlgorithms.zakura_udon.field.pasta.representation.Loose :=
    { limbs := t.limbs, marker := () }
  let (flag, root) ← LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.sqrt_finish_large input subgroup
  ok (flag, { limbs := root.limbs, marker := () })

/-- Invoke the separately extracted large-table Rust callback, preserving all four limbs. -/
def zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.sqrt_large
    (value : zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasScalar zakura_udon.field.pasta.representation.Reduced)
    (w : zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasScalar zakura_udon.field.pasta.representation.Loose) :
    Result (Option (zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasScalar zakura_udon.field.pasta.representation.Reduced)) := do
  let input : LargeAlgorithms.zakura_udon.field.pasta.PastaField LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar LargeAlgorithms.zakura_udon.field.pasta.representation.Reduced :=
    { limbs := value.limbs, marker := () }
  let seed : LargeAlgorithms.zakura_udon.field.pasta.PastaField LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar LargeAlgorithms.zakura_udon.field.pasta.representation.Loose :=
    { limbs := w.limbs, marker := () }
  let result ← LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.sqrt_large input seed
  match result with
  | none => ok none
  | some root => ok (some { limbs := root.limbs, marker := () })

/-- Invoke the separately extracted finish-and-reduce callback with its original flag. -/
def zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.sqrt_finish_large
    (x t : zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasScalar zakura_udon.field.pasta.representation.Loose) :
    Result (Bool × (zakura_udon.field.pasta.PastaField zakura_udon.field.pasta.parameters.PallasScalar zakura_udon.field.pasta.representation.Reduced)) := do
  let input : LargeAlgorithms.zakura_udon.field.pasta.PastaField LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar LargeAlgorithms.zakura_udon.field.pasta.representation.Loose :=
    { limbs := x.limbs, marker := () }
  let subgroup : LargeAlgorithms.zakura_udon.field.pasta.PastaField LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar LargeAlgorithms.zakura_udon.field.pasta.representation.Loose :=
    { limbs := t.limbs, marker := () }
  let (flag, root) ← LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.sqrt_finish_large input subgroup
  ok (flag, { limbs := root.limbs, marker := () })

end
end LargePublic
