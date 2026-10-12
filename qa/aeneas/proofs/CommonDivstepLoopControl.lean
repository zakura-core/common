import CommonDivstepCheckpoint

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def nativeOddLoop (f0 g0 : U64) (eta : I64) (u v q r f g : U64) (remaining : U32) :
    Result DivWordOutput := do
  let flow ← nativeOdd f0 g0 eta u v q r f g remaining
  match flow with
  | .done out => ok out
  | .cont (eta1, u1, v1, q1, r1, f1, g1, rest) =>
    CommonDivsteps.field.pasta.safegcd.divsteps_62_var_loop eta1 f0 g0
      u1 v1 q1 r1 f1 g1 rest

theorem native_loop_head_bridge (eta : I64) (f0 g0 u v q r f g : U64) (remaining : U32) :
    CommonDivsteps.field.pasta.safegcd.divsteps_62_var_loop eta f0 g0 u v q r f g remaining =
      (do let (eta1, u1, v1, g1, rest, _) ← stripZeroState eta u v g remaining
          if rest = 0#u32 then ok (eta1, u1, v1, q, r)
          else nativeOddLoop f0 g0 eta1 u1 v1 q r f g1 rest) := by
  rw [native_loop_unfold, native_body_bridge]
  simp only [Std.bind_assoc]
  congr 1
  funext out
  rcases out with ⟨eta1, u1, v1, g1, rest, zeros⟩
  change (do let flow ← if rest = 0#u32 then ok (ControlFlow.done (eta1, u1, v1, q, r))
                        else nativeOdd f0 g0 eta1 u1 v1 q r f g1 rest
             match flow with
             | .done out => ok out
             | .cont (eta2, u2, v2, q2, r2, f2, g2, rest2) =>
               CommonDivsteps.field.pasta.safegcd.divsteps_62_var_loop eta2 f0 g0
                 u2 v2 q2 r2 f2 g2 rest2) =
    (if rest = 0#u32 then ok (eta1, u1, v1, q, r)
     else nativeOddLoop f0 g0 eta1 u1 v1 q r f g1 rest)
  split_ifs
  · simp only [bind_ok]
  · rfl

#print axioms native_loop_head_bridge
end UdonVerify.CommonSigned62
