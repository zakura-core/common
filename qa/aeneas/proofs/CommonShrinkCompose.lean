import CommonShrinkControl

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def shrinkColumns (f g : Signed62) (len : Usize) : Result (Signed62 × Signed62 × Usize) := do
  let topIndex ← len - 1#usize
  let fTop ← Array.index_usize f topIndex
  let gTop ← Array.index_usize g topIndex
  let lengthMask ← shrinkLengthMask len
  let fMask ← fTop >>> 63#i32
  let gMask ← gTop >>> 63#i32
  if ((lengthMask ||| (fTop ^^^ fMask)) ||| (gTop ^^^ gMask)) = 0#i64 then
    let lowIndex ← len - 2#usize
    let fLow ← Array.index_usize f lowIndex
    let fDigit ← shrinkDigit fLow fTop
    let fOut ← Array.update f lowIndex fDigit
    let gLow ← Array.index_usize g lowIndex
    let gDigit ← shrinkDigit gLow gTop
    let gOut ← Array.update g lowIndex gDigit
    ok (fOut, gOut, topIndex)
  else ok (f, g, len)

theorem shrink_columns_bridge (f g : Signed62) (len : Usize) :
    CommonInvHelpers.field.pasta.safegcd.shrink_len f g len = shrinkColumns f g len := by
  unfold CommonInvHelpers.field.pasta.safegcd.shrink_len shrinkColumns shrinkLengthMask shrinkDigit
  simp only [lift, bind_ok, Bind.bind, Std.bind_assoc]

#print axioms shrink_columns_bridge
end UdonVerify.CommonSigned62
