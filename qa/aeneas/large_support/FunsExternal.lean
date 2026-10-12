module
public import Aeneas
public import KernelSlice.FunsExternal
public import LargeAlgorithms.Types
@[expose] public section

open Aeneas Std Result

namespace LargeAlgorithms

/-- Core's lazy Boolean helper invokes the owned closure exactly when the flag is true. -/
def core.bool.Bool.then {T F : Type} (inst : core.ops.function.FnOnce F Unit T)
    (flag : Bool) (closure : F) : Result (Option T) := do
  if flag then
    let out ← inst.call_once closure ()
    ok (some out)
  else
    ok none

end LargeAlgorithms
