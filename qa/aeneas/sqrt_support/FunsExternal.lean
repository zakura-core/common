module
public import Aeneas
public import SqrtNative.Types
public import NativeField.Funs
public import KernelSlice.FunsExternal
public import SqrtSupport.RangeContains
@[expose] public section

open Aeneas Std Result

namespace SqrtNative

/-- Identity cloning for the zero-sized marker in this extraction. -/
def core.marker.PhantomData.Insts.CoreCloneClone.clone {T : Type}
    (marker : core.marker.PhantomData T) : Result (core.marker.PhantomData T) :=
  ok marker

/-- Core's map: invoke the owned callback once for Some, and preserve None. -/
def core.option.Option.map {T U F : Type}
    (inst : core.ops.function.FnOnce F T U) (source : Option T) (func : F) :
    Result (Option U) := do
  match source with
  | none => ok none
  | some value =>
    let out ← inst.call_once func value
    ok (some out)

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

end SqrtNative
