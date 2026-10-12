module
public import Aeneas
public import CommonDivsteps.Types
public import NativeField.Funs
public import SqrtSupport.RangeContains
@[expose] public section
open Aeneas Std Result
namespace CommonDivsteps

/-- The pinned lossless U32 to I64 cast. -/
def I64.Insts.CoreConvertFromU32.from (value : Std.U32) : Result Std.I64 :=
  ok (UScalar.hcast .I64 value)

/-- Reuse the extracted pinned standard-library absolute-value body. -/
def core.num.I64.unsigned_abs (value : Std.I64) : Result Std.U64 :=
  NativeField.core.num.I64.unsigned_abs value

/-- Reuse the extracted pinned standard-library wrapping-negation body. -/
def core.num.U64.wrapping_neg (value : Std.U64) : Result Std.U64 :=
  NativeField.core.num.U64.wrapping_neg value

/-- The Rust cttz intrinsic counts low zero bits and returns 64 for zero. -/
def core.num.U64.trailing_zeros (value : Std.U64) : Result Std.U32 :=
  ok ⟨value.bv.ctz.setWidth 32⟩

end CommonDivsteps
