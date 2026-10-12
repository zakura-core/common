import NativeField.Funs
import Common
open Aeneas Std Result
namespace CommonVerify
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem mutable_array_into_iter_spec {T : Type} {N : Usize} (a : Array T N) :
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter a
      ⦃ it back => it.slice.val = a.val ∧ it.i = 0 ∧
        back = fun it' => Array.from_slice a it'.slice ⦄ := by
  simp [MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
    WP.spec_ok]

@[step]
theorem mutable_next_some_spec {T : Type} (it : core.slice.iter.IterMut T)
    (hi : it.i < it.slice.length) :
    core.slice.iter.IteratorIterMut.next it ⦃ item it' back =>
      item = some (it.slice[it.i]'hi) ∧ it'.slice = it.slice ∧ it'.i = it.i+1 ∧
      back = (fun nextItem value => match value with
        | none => nextItem
        | some v => {nextItem with slice := nextItem.slice.setAtNat it.i v}) ⦄ := by
  simp [core.slice.iter.IteratorIterMut.next, hi, WP.spec_ok]
  constructor <;> rfl

@[step]
theorem mutable_next_none_spec {T : Type} (it : core.slice.iter.IterMut T)
    (hi : it.slice.length ≤ it.i) :
    core.slice.iter.IteratorIterMut.next it ⦃ item it' back =>
      item = none ∧ it' = it ∧ back = (fun nextItem _ => nextItem) ⦄ := by
  simp [core.slice.iter.IteratorIterMut.next, show ¬it.i < it.slice.length by omega,
    WP.spec_ok]

theorem list_four_eta (values : List U64) (hlen : values.length=4) :
    values = [values[0]!,values[1]!,values[2]!,values[3]!] := by
  rcases values with _|⟨a0,values⟩
  · simp at hlen
  rcases values with _|⟨a1,values⟩
  · simp at hlen
  rcases values with _|⟨a2,values⟩
  · simp at hlen
  rcases values with _|⟨a3,values⟩
  · simp at hlen
  have hz : values=[] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_cons] at hlen
    omega
  subst values
  simp

theorem array_four_eta (a : UdonVerify.A4) :
    a = Array.make 4#usize [a[0]!,a[1]!,a[2]!,a[3]!] := by
  apply Aeneas.Std.Array.ext
  simpa using list_four_eta a.val (by simpa using a.property)

#print axioms mutable_array_into_iter_spec
#print axioms mutable_next_some_spec
#print axioms mutable_next_none_spec
#print axioms list_four_eta
#print axioms array_four_eta
end CommonVerify
