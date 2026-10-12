import NativeProductMergeLoop
open Aeneas Std Result
namespace UdonVerify.Native
set_option maxHeartbeats 200000

def finiteLoop {A C : Type} (body : A → Result (ControlFlow A C)) : Nat → A → Result C
  | 0,_ => fail .panic
  | fuel+1,state => do
    let flow ← body state
    match flow with
    | .done value => ok value
    | .cont next => finiteLoop body fuel next

theorem finite_loop_success_eq {A C : Type} (body : A → Result (ControlFlow A C))
    (fuel : Nat) (state : A) (value : C) (h : finiteLoop body fuel state=ok value) :
    loop body state=ok value := by
  induction fuel generalizing state with
  | zero => simp [finiteLoop] at h
  | succ fuel ih =>
    cases hbody : body state with
    | ret flow =>
      rw [loop,hbody]
      cases flow with
      | done out => simpa [finiteLoop,hbody] using h
      | cont next =>
        simp only [bind_ok]
        apply ih next
        simpa [finiteLoop,hbody] using h
    | div => simp [finiteLoop,hbody] at h
    | vis e k => simp [finiteLoop,hbody] at h

#print axioms finite_loop_success_eq
end UdonVerify.Native
