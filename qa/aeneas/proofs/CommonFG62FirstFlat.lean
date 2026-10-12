import CommonFG62Sparse
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

noncomputable def fgFirstFlat (f g : Signed62)
    (t : CommonFG62First.field.pasta.safegcd.Trans2x2) : Result (Signed62 × Signed62) := do
  let cf0 ← fgRowTerm t.u t.v f[0]! g[0]!
  let cg0 ← fgRowTerm t.q t.r f[0]! g[0]!
  massert (IScalar.hcast .U64 cf0 &&& 4611686018427387903#u64 = 0#u64)
  massert (IScalar.hcast .U64 cg0 &&& 4611686018427387903#u64 = 0#u64)
  let cf1 ← cf0 >>> 62#i32
  let cg1 ← cg0 >>> 62#i32
  let tf1 ← fgRowTerm t.u t.v f[1]! g[1]!
  let cf2 ← cf1 + tf1
  let tg1 ← fgRowTerm t.q t.r f[1]! g[1]!
  let cg2 ← cg1 + tg1
  let cf3 ← cf2 >>> 62#i32
  let cg3 ← cg2 >>> 62#i32
  let tf2 ← fgSparseTerm t.u t.v g[2]! 1#i32
  let cf4 ← cf3 + tf2
  let tg2 ← fgSparseTerm t.q t.r g[2]! 1#i32
  let cg4 ← cg3 + tg2
  let cf5 ← cf4 >>> 62#i32
  let cg5 ← cg4 >>> 62#i32
  let tf3 ← fgZeroTerm t.v g[3]!
  let cf6 ← cf5 + tf3
  let tg3 ← fgZeroTerm t.r g[3]!
  let cg6 ← cg5 + tg3
  let cf7 ← cf6 >>> 62#i32
  let cg7 ← cg6 >>> 62#i32
  let tf4 ← fgSparseTerm t.u t.v g[4]! 6#i32
  let cf8 ← cf7 + tf4
  let tg4 ← fgSparseTerm t.q t.r g[4]! 6#i32
  let cg8 ← cg7 + tg4
  let cf9 ← cf8 >>> 62#i32
  let cg9 ← cg8 >>> 62#i32
  let ft ← fgRowTail cf9
  let gt ← fgRowTail cg9
  ok (((((f.set 0#usize (fgRowDigit cf2)).set 1#usize (fgRowDigit cf4)).set 2#usize (fgRowDigit cf6)).set 3#usize (fgRowDigit cf8)).set 4#usize ft, ((((g.set 0#usize (fgRowDigit cg2)).set 1#usize (fgRowDigit cg4)).set 2#usize (fgRowDigit cg6)).set 3#usize (fgRowDigit cg8)).set 4#usize gt)

theorem fg_first_flat_bridge {P : Type}
    (inst : CommonFG62First.field.pasta.safegcd.InvParams P) (f g : Signed62)
    (t : CommonFG62First.field.pasta.safegcd.Trans2x2)
    (hparam : inst.MODULUS_62 = ok f) :
    CommonFG62First.field.pasta.safegcd.update_fg_62_first inst f g t =
      fgFirstFlat f g t := by
  unfold CommonFG62First.field.pasta.safegcd.update_fg_62_first fgFirstFlat
    fgRowTerm fgSparseTerm fgZeroTerm fgRowTail fgRowDigit
  rw [hparam]
  simp only [bind_ok]
  rw [fg_array_self_eq, fg_first_mask_eq]
  simp (config := { maxSteps := 1000000 }) [lift, Bind.bind, Std.bind_assoc, massert,
    fg_index_eq, fg_update_eq, Array.getElem!_Nat_set_ne]
  try rfl

#print axioms fg_first_flat_bridge
end UdonVerify.CommonSigned62
