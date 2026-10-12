import NativeSmallModel
open Aeneas Std Result
open NativeField.zakura_udon.field.pasta.small
namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false
attribute [local reducible] WP.Post

theorem small_outer_unfold {M : Type} (K : U64) (inst : Modulus M)
    (restore : core.slice.iter.IterMut U64 → A4) (iter : core.slice.iter.IterMut U64)
    (back : core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64) (carry : U64) :
    multiply_loop0 K inst restore iter back carry = (do
      let r ← multiply_loop0.body K inst restore iter back carry
      match r with
      | .done out => ok out
      | .cont (it,b,c) => multiply_loop0 K inst restore it b c) := by
  unfold multiply_loop0
  rw [loop]
  congr 1
  funext r
  cases r with
  | done r => rfl
  | cont r => rcases r with ⟨it,b,c⟩; rfl

theorem bind_ite_eq {α β : Type} (p : Prop) [Decidable p]
    (a b : Result α) (f : α → Result β) :
    Std.bind (if p then a else b) f = if p then Std.bind a f else Std.bind b f := by
  split <;> rfl

theorem small_restore_four (a0 a1 a2 a3 r0 r1 r2 r3 : U64) :
    Array.from_slice (Array.make 4#usize [a0,a1,a2,a3])
      (((((Slice.from [a0,a1,a2,a3] (by scalar_tac)).setAtNat 3 r3).setAtNat 2 r2).setAtNat 1 r1).setAtNat 0 r0)
      = Array.make 4#usize [r0,r1,r2,r3] := by
  apply Aeneas.Std.Array.ext
  simp [Array.from_slice, Slice.setAtNat]

theorem small_prefix {M : Type} (K : U64) (inst : Modulus M) (a0 a1 a2 a3 : U64)
    (hk0 : 0<K.val) (hk8 : K.val≤8) :
    multiply K inst (Array.make 4#usize [a0,a1,a2,a3]) = (do
      let (r0,c0) ← NativeField.zakura_udon.field.pasta.word.mac 0#u64 a0 K 0#u64
      let (r1,c1) ← NativeField.zakura_udon.field.pasta.word.mac 0#u64 a1 K c0
      let (r2,c2) ← NativeField.zakura_udon.field.pasta.word.mac 0#u64 a2 K c1
      let (r3,c3) ← NativeField.zakura_udon.field.pasta.word.mac 0#u64 a3 K c2
      smallFinish inst (Array.make 4#usize [r0,r1,r2,r3]) c3) := by
  have h0 : K>0#u64 := by scalar_tac
  have h8 : K≤8#u64 := by scalar_tac
  unfold multiply
  simp only [h0,h8,massert_True,bind_ok,
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter]
  change multiply_loop0 K inst
    (fun it => Array.from_slice (Array.make 4#usize [a0,a1,a2,a3]) it.slice)
    ⟨Slice.from [a0,a1,a2,a3] (by scalar_tac),0⟩ (fun it => it) 0#u64 = _
  with_unfolding_all rw [small_outer_unfold]
  unfold multiply_loop0.body
  simp [core.slice.iter.IteratorIterMut.next, Std.bind_assoc]
  congr 1
  funext pair
  rcases pair with ⟨r0,c0⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  change multiply_loop0 K inst
    (fun it => Array.from_slice (Array.make 4#usize [a0,a1,a2,a3]) it.slice)
    ⟨Slice.from [a0,a1,a2,a3] (by scalar_tac),1⟩
    (fun it => {it with slice := it.slice.setAtNat 0 r0}) c0 = _
  rw [small_outer_unfold]
  unfold multiply_loop0.body
  simp [core.slice.iter.IteratorIterMut.next, Std.bind_assoc]
  congr 1
  funext pair
  rcases pair with ⟨r1,c1⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  change multiply_loop0 K inst
    (fun it => Array.from_slice (Array.make 4#usize [a0,a1,a2,a3]) it.slice)
    ⟨Slice.from [a0,a1,a2,a3] (by scalar_tac),2⟩
    (fun it => {it with slice := ((it.slice).setAtNat 1 r1).setAtNat 0 r0}) c1 = _
  rw [small_outer_unfold]
  unfold multiply_loop0.body
  simp [core.slice.iter.IteratorIterMut.next, Std.bind_assoc]
  congr 1
  funext pair
  rcases pair with ⟨r2,c2⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  change multiply_loop0 K inst
    (fun it => Array.from_slice (Array.make 4#usize [a0,a1,a2,a3]) it.slice)
    ⟨Slice.from [a0,a1,a2,a3] (by scalar_tac),3⟩
    (fun it => {it with slice := (((it.slice).setAtNat 2 r2).setAtNat 1 r1).setAtNat 0 r0}) c2 = _
  rw [small_outer_unfold]
  unfold multiply_loop0.body
  simp [core.slice.iter.IteratorIterMut.next, Std.bind_assoc]
  congr 1
  funext pair
  rcases pair with ⟨r3,c3⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [small_outer_unfold]
  unfold multiply_loop0.body
  simp [core.slice.iter.IteratorIterMut.next, Std.bind_assoc]
  rw [small_restore_four]
  unfold smallFinish
  simp [Std.bind_assoc, Std.uncurry, bind_ite_eq]
  congr 1

#print axioms small_outer_unfold
#print axioms small_restore_four
#print axioms small_prefix
end UdonVerify.Native
