import CommonFG62Arrays
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

noncomputable def fgFlat5 (f g : Signed62)
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
  let tf3 ← fgRowTerm t.u t.v f[3]! g[3]!
  let cf6 ← cf5 + tf3
  let tg3 ← fgRowTerm t.q t.r f[3]! g[3]!
  let cg6 ← cg5 + tg3
  let cf7 ← cf6 >>> 62#i32
  let cg7 ← cg6 >>> 62#i32
  let tf4 ← fgRowTerm t.u t.v f[4]! g[4]!
  let cf8 ← cf7 + tf4
  let tg4 ← fgRowTerm t.q t.r f[4]! g[4]!
  let cg8 ← cg7 + tg4
  let cf9 ← cf8 >>> 62#i32
  let cg9 ← cg8 >>> 62#i32
  let ft ← fgRowTail cf9
  let gt ← fgRowTail cg9
  ok (((((f.set 0#usize (fgRowDigit cf2)).set 1#usize (fgRowDigit cf4)).set 2#usize (fgRowDigit cf6)).set 3#usize (fgRowDigit cf8)).set 4#usize ft, ((((g.set 0#usize (fgRowDigit cg2)).set 1#usize (fgRowDigit cg4)).set 2#usize (fgRowDigit cg6)).set 3#usize (fgRowDigit cg8)).set 4#usize gt)

theorem fg_flat_5_bridge (f g : Signed62)
    (t : CommonFG62.field.pasta.safegcd.Trans2x2) :
    CommonFG62.field.pasta.safegcd.update_fg_62_var 5#usize f g t = fgFlat5 f g t := by
  rw [fg_factored_bridge]
  unfold fgFactored fgFlat5 fgRowTail fgRowDigit
  simp only [core.ops.range.RangeInclusive.new, bind_ok]
  rw [fg_length_check_eq 5#usize (by decide), fg_mask_eq]
  have hn1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      { start := 1#usize, «end» := 5#usize } = ok (some 1#usize, { start := 2#usize, «end» := 5#usize }) := by
    exact fg_next_some_eq _ _ (by decide) (by decide)
  have hn2 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      { start := 2#usize, «end» := 5#usize } = ok (some 2#usize, { start := 3#usize, «end» := 5#usize }) := by
    exact fg_next_some_eq _ _ (by decide) (by decide)
  have hn3 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      { start := 3#usize, «end» := 5#usize } = ok (some 3#usize, { start := 4#usize, «end» := 5#usize }) := by
    exact fg_next_some_eq _ _ (by decide) (by decide)
  have hn4 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      { start := 4#usize, «end» := 5#usize } = ok (some 4#usize, { start := 5#usize, «end» := 5#usize }) := by
    exact fg_next_some_eq _ _ (by decide) (by decide)
  have hn5 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      { start := 5#usize, «end» := 5#usize } = ok (none, { start := 5#usize, «end» := 5#usize }) := by
    exact fg_next_none_eq _ (by decide)
  have hs1 : 1#usize - 1#usize = ok 0#usize :=
    fg_usize_sub_eq _ _ _ (by decide) (by decide)
  have hs2 : 2#usize - 1#usize = ok 1#usize :=
    fg_usize_sub_eq _ _ _ (by decide) (by decide)
  have hs3 : 3#usize - 1#usize = ok 2#usize :=
    fg_usize_sub_eq _ _ _ (by decide) (by decide)
  have hs4 : 4#usize - 1#usize = ok 3#usize :=
    fg_usize_sub_eq _ _ _ (by decide) (by decide)
  have hs5 : 5#usize - 1#usize = ok 4#usize :=
    fg_usize_sub_eq _ _ _ (by decide) (by decide)
  simp (config := { maxSteps := 1000000 }) [lift, Bind.bind, bind_ok, Std.bind_assoc, massert, fg_index_eq, fg_index_mut_eq, fg_update_eq, hn1, hn2, hn3, hn4, hn5, hs1, hs2, hs3, hs4, hs5, Array.getElem!_Nat_set_ne]
  try rfl

#print axioms fg_flat_5_bridge
end UdonVerify.CommonSigned62
