import CommonInvHelpers.FunsExternal

open Aeneas Std Result
namespace UdonVerify.CommonSigned62

theorem inv_string_model_eq (value : String) (h : value.toByteArray.size ≤ U32.max) :
    CommonInvHelpers.toStr value h = Aeneas.Std.toStr value h := rfl

#print axioms inv_string_model_eq
end UdonVerify.CommonSigned62
