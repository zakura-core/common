module
public import Aeneas
public import CommonInvHelpers.Types
@[expose] public section
open Aeneas Std Result
namespace CommonInvHelpers

/-- Preserve the backend string value while checking literal bounds in the kernel. -/
def toStr (s : String) (h : s.toByteArray.size ≤ U32.max := by
    simp only [String.size_toByteArray, U32.max, U32.numBits]
    decide +kernel) : Str := Aeneas.Std.toStr s h

def core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq (a b : Ordering) : Result Bool :=
  ok (a == b)

def Shared0T.Insts.CoreFmtDisplay.fmt {T : Type} (inst : core.fmt.Display T)
    (value : T) (formatter : core.fmt.Formatter) :
    Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  inst.fmt value formatter

/-- Formatting follows the backend's erased formatter model. The successful
    arithmetic paths never reach the diagnostic formatting branches. -/
def Str.Insts.CoreFmtDisplay.fmt (value : Str) (formatter : core.fmt.Formatter) :
    Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  core.fmt.Formatter.write_str formatter value

def I64.Insts.CoreOpsBitBitOrAssignShared0I64.bitor_assign (a b : Std.I64) : Result Std.I64 :=
  ok (a ||| b)

def core.num.I64.wrapping_neg (value : Std.I64) : Result Std.I64 :=
  ok (IScalar.wrapping_sub 0#i64 value)

end CommonInvHelpers
