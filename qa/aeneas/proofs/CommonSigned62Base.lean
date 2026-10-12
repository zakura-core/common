import NativeBits
import Signed62Native.Funs
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
abbrev Signed62 := Array I64 5#usize
def signedRadix : Int := 2^62
def signed62Value (a : Signed62) : Int :=
  a[0]!.val+signedRadix*a[1]!.val+signedRadix^2*a[2]!.val+
    signedRadix^3*a[3]!.val+signedRadix^4*a[4]!.val
def signed62Normalized (a : Signed62) : Prop :=
  ∀ k : Fin 4, 0≤a[k.val]!.val ∧ a[k.val]!.val<signedRadix
end UdonVerify.CommonSigned62
