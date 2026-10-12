import CommonDivstepMasks
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem nonnegative_eta_cast (eta : I64) (he : 0 ≤ eta.val ∧ eta.val ≤ 745) :
    (IScalar.hcast .U32 eta).val = eta.val.toNat := by
  rw [IScalar.hcast_val_eq]
  change (eta.val%(2^32)).toNat=eta.val.toNat
  rw [Int.emod_eq_of_lt he.1 (by omega)]

def etaLimit (eta : I64) (remaining : U32) : Result U32 := do
  let cast ← lift (IScalar.hcast .U32 eta)
  let plus ← cast+1#u32
  if plus>remaining then ok remaining
  else do
    let cast1 ← lift (IScalar.hcast .U32 eta)
    cast1+1#u32

@[step]
theorem eta_limit_spec (eta : I64) (remaining : U32)
    (he : 0 ≤ eta.val ∧ eta.val ≤ 745)
    (hr : 0 < remaining.val ∧ remaining.val ≤ 62) :
    etaLimit eta remaining ⦃ out =>
      out.val=min remaining.val (eta.val.toNat+1) ∧
      0 < out.val ∧ out.val ≤ 62 ⦄ := by
  unfold etaLimit
  simp only [lift,bind_ok]
  have hcast := nonnegative_eta_cast eta he
  step +scalarTac -grind with U32.add_spec as ⟨plus,hplus⟩
  rw [hcast] at hplus
  split_ifs with hgt
  · simp only [WP.spec_ok]
    have hgreater : eta.val.toNat+1>remaining.val := by scalar_tac
    exact ⟨(Nat.min_eq_left (by omega)).symm,hr⟩
  · try simp only [lift,bind_ok]
    step +scalarTac -grind with U32.add_spec as ⟨out,hout⟩
    rw [hcast] at hout
    have hle : eta.val.toNat+1≤remaining.val := by scalar_tac
    rw [hout,Nat.min_eq_right hle]
    exact ⟨rfl,by omega,by omega⟩

#print axioms nonnegative_eta_cast
#print axioms eta_limit_spec
end UdonVerify.CommonSigned62
