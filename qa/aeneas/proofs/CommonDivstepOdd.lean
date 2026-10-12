import CommonDivstepWords

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def NativeOddRelation (eta : I64) (u v q r f g : U64) (remaining : U32)
    (flow : ControlFlow DivWordState DivWordOutput) : Prop :=
  ∃ cancel : DivCancelOutput,
    NativeCancelRelation eta u v q r f g remaining cancel ∧
      flow = (let (nextEta, nextU, nextV, nextQ, nextR, nextF, nextG, _, w) := cancel
        ControlFlow.cont (nextEta, nextU, nextV, addMulWord nextQ nextU w,
          addMulWord nextR nextV w, nextF, addMulWord nextG nextF w, remaining))

theorem word_low_bit_one (value : U64) (hodd : value.val % 2 = 1) :
    value &&& 1#u64 = 1#u64 := by
  apply UScalar.eq_of_val_eq
  change (value &&& 1#u64).val = 1
  rw [and_mask_mod value 1#u64 1 (by decide)]
  exact hodd

@[step]
theorem native_odd_spec (f0 g0 : U64) (eta : I64) (u v q r f g : U64) (remaining : U32)
    (he : -745 ≤ eta.val ∧ eta.val ≤ 745)
    (hr : 0 < remaining.val ∧ remaining.val ≤ 62)
    (hfodd : f.val % 2 = 1) (hgodd : g.val % 2 = 1)
    (hfirst : (rowWord u v f0 g0).bv = f.bv <<< (62 - remaining.val))
    (hsecond : (rowWord q r f0 g0).bv = g.bv <<< (62 - remaining.val)) :
    nativeOdd f0 g0 eta u v q r f g remaining ⦃ flow =>
      NativeOddRelation eta u v q r f g remaining flow ⦄ := by
  have hfbit := word_low_bit_one f hfodd
  have hgbit := word_low_bit_one g hgodd
  unfold nativeOdd
  step -grind
  step -grind
  step +scalarTac -grind with U32.sub_spec as ⟨performed, hperformed⟩
  step -grind with U64.ShiftLeft_spec as ⟨first, hfirstValue, hfirstBits⟩
  have hfirstEq : core.num.U64.wrapping_add (core.num.U64.wrapping_mul u f0)
      (core.num.U64.wrapping_mul v g0) = first := by
    apply U64.bv_eq_imp_eq
    change (rowWord u v f0 g0).bv = first.bv
    rw [hperformed] at hfirstBits
    exact hfirst.trans hfirstBits.symm
  step -grind
  step -grind with U64.ShiftLeft_spec as ⟨second, hsecondValue, hsecondBits⟩
  have hsecondEq : core.num.U64.wrapping_add (core.num.U64.wrapping_mul q f0)
      (core.num.U64.wrapping_mul r g0) = second := by
    apply U64.bv_eq_imp_eq
    change (rowWord q r f0 g0).bv = second.bv
    rw [hperformed] at hsecondBits
    exact hsecond.trans hsecondBits.symm
  step -grind
  rw [eta_range_check_eq eta he]
  simp only [bind_ok]
  apply WP.spec_bind (native_cancel_spec eta u v q r f g remaining he hr hfodd hgodd)
  intro cancel hrelation
  rcases cancel with ⟨nextEta, nextU, nextV, nextQ, nextR, nextF, nextG, mask, w⟩
  have h := hrelation
  unfold NativeCancelRelation at h
  rcases h with ⟨n, hn0, hni, hne, hmask, hw, hcancel, he0, he745, hcase⟩
  have hzero := add_mul_word_mask_zero nextG nextF w mask n (by omega) hmask hcancel
  have hzeroActual : core.num.U64.wrapping_add nextG
      (core.num.U64.wrapping_mul nextF w) &&& mask = 0#u64 := hzero
  step -grind
  try simp only [WP.spec_ok]
  unfold NativeOddRelation
  exact ⟨(nextEta, nextU, nextV, nextQ, nextR, nextF, nextG, mask, w), hrelation, rfl⟩

#print axioms word_low_bit_one
#print axioms native_odd_spec
end UdonVerify.CommonSigned62
