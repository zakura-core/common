import CommonFG62Arrays
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

noncomputable def fgFlat3 (f g : Signed62)
    (t : CommonFG62.field.pasta.safegcd.Trans2x2) : Result (Signed62 × Signed62) := do
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
  let tf2 ← fgRowTerm t.u t.v f[2]! g[2]!
  let cf4 ← cf3 + tf2
  let tg2 ← fgRowTerm t.q t.r f[2]! g[2]!
  let cg4 ← cg3 + tg2
  let cf5 ← cf4 >>> 62#i32
  let cg5 ← cg4 >>> 62#i32
  let ft ← fgRowTail cf5
  let gt ← fgRowTail cg5
  ok (((f.set 0#usize (fgRowDigit cf2)).set 1#usize (fgRowDigit cf4)).set 2#usize ft, ((g.set 0#usize (fgRowDigit cg2)).set 1#usize (fgRowDigit cg4)).set 2#usize gt)

theorem fg_flat_3_bridge (f g : Signed62)
    (t : CommonFG62.field.pasta.safegcd.Trans2x2) :
    CommonFG62.field.pasta.safegcd.update_fg_62_var 3#usize f g t = fgFlat3 f g t := by
  rw [fg_factored_bridge]
  unfold fgFactored fgFlat3 fgRowTail fgRowDigit
  simp only [core.ops.range.RangeInclusive.new, bind_ok]
  rw [fg_length_check_eq 3#usize (by decide), fg_mask_eq]
  have hn1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      { start := 1#usize, «end» := 3#usize } = ok (some 1#usize, { start := 2#usize, «end» := 3#usize }) := by
    exact fg_next_some_eq _ _ (by decide) (by decide)
  have hn2 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      { start := 2#usize, «end» := 3#usize } = ok (some 2#usize, { start := 3#usize, «end» := 3#usize }) := by
    exact fg_next_some_eq _ _ (by decide) (by decide)
  have hn3 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      { start := 3#usize, «end» := 3#usize } = ok (none, { start := 3#usize, «end» := 3#usize }) := by
    exact fg_next_none_eq _ (by decide)
  have hs1 : 1#usize - 1#usize = ok 0#usize :=
    fg_usize_sub_eq _ _ _ (by decide) (by decide)
  have hs2 : 2#usize - 1#usize = ok 1#usize :=
    fg_usize_sub_eq _ _ _ (by decide) (by decide)
  have hs3 : 3#usize - 1#usize = ok 2#usize :=
    fg_usize_sub_eq _ _ _ (by decide) (by decide)
  simp (config := { maxSteps := 100000 }) [lift, Bind.bind, bind_ok, Std.bind_assoc, massert, fg_index_eq, fg_index_mut_eq, fg_update_eq, hn1, hn2, hn3, hs1, hs2, hs3, Array.getElem!_Nat_set_ne]
  try rfl

#print axioms fg_flat_3_bridge
end UdonVerify.CommonSigned62
