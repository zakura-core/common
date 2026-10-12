import CommonDivstepControl

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def NativeCancelRelation (eta : I64) (u v q r f g : U64) (remaining : U32)
    (out : DivCancelOutput) : Prop :=
  let (nextEta, nextU, nextV, nextQ, nextR, nextF, nextG, mask, w) := out
  ∃ n : Nat, 0 < n ∧ n ≤ remaining.val ∧ n ≤ nextEta.val.toNat + 1 ∧
    mask.val = 2 ^ n - 1 ∧ w.val < 2 ^ n ∧
    (nextG.val + nextF.val * w.val) % 2 ^ n = 0 ∧
    0 ≤ nextEta.val ∧ nextEta.val ≤ 745 ∧
    ((eta.val < 0 ∧ nextEta.val = -eta.val ∧
      nextU = q ∧ nextV = r ∧ nextQ = UScalar.wrapping_sub 0#u64 u ∧
      nextR = UScalar.wrapping_sub 0#u64 v ∧ nextF = g ∧
      nextG = UScalar.wrapping_sub 0#u64 f) ∨
     (0 ≤ eta.val ∧ nextEta = eta ∧ nextU = u ∧ nextV = v ∧
      nextQ = q ∧ nextR = r ∧ nextF = f ∧ nextG = g))

@[step]
theorem native_cancel_spec (eta : I64) (u v q r f g : U64) (remaining : U32)
    (he : -745 ≤ eta.val ∧ eta.val ≤ 745)
    (hr : 0 < remaining.val ∧ remaining.val ≤ 62)
    (hfodd : f.val % 2 = 1) (hgodd : g.val % 2 = 1) :
    nativeCancel eta u v q r f g remaining ⦃ out =>
      NativeCancelRelation eta u v q r f g remaining out ⦄ := by
  unfold nativeCancel
  split_ifs with hnegative
  · have hneg : eta.val < 0 := by scalar_tac
    step +scalarTac -grind as ⟨nextEta, hnextEta⟩
    have heNext : 0 ≤ nextEta.val ∧ nextEta.val ≤ 745 := by omega
    simp only [native_wrapping_neg_eq, bind_ok]
    step -grind with (eta_limit_spec nextEta remaining heNext hr)
      as ⟨limit, hlimit, hlimit0, hlimit62⟩
    rw [limit_range_check_eq limit (by omega)]
    simp only [bind_ok]
    step -grind with (cancellation_mask_result_spec limit 6 63#u64
      ⟨hlimit0, hlimit62⟩ (by decide)) as ⟨mask, hmask⟩
    let n := min limit.val 6
    have hn6 : n ≤ 6 := Nat.min_le_right _ _
    have hnl : n ≤ limit.val := Nat.min_le_left _ _
    have hni : limit.val ≤ remaining.val := by rw [hlimit]; exact Nat.min_le_left _ _
    have hne : limit.val ≤ nextEta.val.toNat + 1 := by rw [hlimit]; exact Nat.min_le_right _ _
    have hn0 : 0 < n := by dsimp [n]; omega
    rw [native_negative_eta_bridge]
    step -grind with (negative_eta_multiplier_spec g (UScalar.wrapping_sub 0#u64 f)
      mask n hn6 hmask hgodd) as ⟨w, hw, hcancel⟩
    try simp only [WP.spec_ok]
    refine ⟨n, hn0, by omega, by omega, hmask, hw, hcancel,
      heNext.1, heNext.2, Or.inl ?_⟩
    exact ⟨hneg, hnextEta, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have hnonneg : 0 ≤ eta.val := by scalar_tac
    have heNext : 0 ≤ eta.val ∧ eta.val ≤ 745 := ⟨hnonneg, he.2⟩
    step -grind with (eta_limit_spec eta remaining heNext hr)
      as ⟨limit, hlimit, hlimit0, hlimit62⟩
    rw [limit_range_check_eq limit (by omega)]
    simp only [bind_ok]
    step -grind with (cancellation_mask_result_spec limit 4 15#u64
      ⟨hlimit0, hlimit62⟩ (by decide)) as ⟨mask, hmask⟩
    let n := min limit.val 4
    have hn4 : n ≤ 4 := Nat.min_le_right _ _
    have hnl : n ≤ limit.val := Nat.min_le_left _ _
    have hni : limit.val ≤ remaining.val := by rw [hlimit]; exact Nat.min_le_left _ _
    have hne : limit.val ≤ eta.val.toNat + 1 := by rw [hlimit]; exact Nat.min_le_right _ _
    have hn0 : 0 < n := by dsimp [n]; omega
    step -grind with (positive_eta_multiplier_spec f g mask n hn4 hmask hfodd)
      as ⟨w, hw, hcancel⟩
    try simp only [WP.spec_ok]
    refine ⟨n, hn0, by omega, by omega, hmask, hw, hcancel,
      heNext.1, heNext.2, Or.inr ?_⟩
    exact ⟨hnonneg, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms native_cancel_spec
end UdonVerify.CommonSigned62
