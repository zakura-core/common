import CommonDivstepLoop

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def NativeBatchResult (initial : State)
    (out : CommonDivsteps.field.pasta.safegcd.Trans2x2 × I64) : Prop :=
  out.1.u.val = (transitionMatrix 62 initial).u ∧
  out.1.v.val = (transitionMatrix 62 initial).v ∧
  out.1.q.val = (transitionMatrix 62 initial).q ∧
  out.1.r.val = (transitionMatrix 62 initial).r ∧
  out.2.val = -(iterate 62 initial).delta

theorem divstep_product_i128 (a b : Int) (ha : |a| ≤ signedRadix) (hb : |b| ≤ signedRadix) :
    -(2 ^ 127) ≤ a * b ∧ a * b < 2 ^ 127 := by
  have hp : |a * b| ≤ signedRadix ^ 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg a, abs_nonneg b]
  have h := abs_le.mp hp
  norm_num [signedRadix] at h ⊢
  omega

@[step]
theorem native_divsteps_spec (eta : I64) (f0 g0 : U64)
    (he : |eta.val| ≤ 683) (hf : f0.val % 2 = 1) :
    CommonDivsteps.field.pasta.safegcd.divsteps_62_var eta f0 g0
      ⦃ out => NativeBatchResult ⟨-eta.val, f0.val, g0.val⟩ out ⦄ := by
  let initial : State := ⟨-eta.val, f0.val, g0.val⟩
  have hiodd : initial.f % 2 = 1 := by dsimp [initial]; exact_mod_cast hf
  have hi : |initial.delta| ≤ 683 := by simpa [initial] using he
  unfold CommonDivsteps.field.pasta.safegcd.divsteps_62_var
  apply WP.spec_bind (native_loop_spec initial f0 g0 rfl rfl hiodd hi
    eta 1#u64 0#u64 0#u64 1#u64 f0 g0 62#u32 (by decide)
    (batch_match_initial eta f0 g0))
  intro output houtput
  rcases output with ⟨etaOut, u, v, q, r⟩
  rcases houtput with ⟨heta, hu, hv, hq, hr⟩
  have hrows := transition_matrix_rows 62 initial
  have huBound : |(transitionMatrix 62 initial).u| ≤ signedRadix := by
    have := abs_nonneg (transitionMatrix 62 initial).v
    simpa only [signedRadix] using (show |(transitionMatrix 62 initial).u| ≤ 2 ^ 62 by omega)
  have hvBound : |(transitionMatrix 62 initial).v| ≤ signedRadix := by
    have := abs_nonneg (transitionMatrix 62 initial).u
    simpa only [signedRadix] using (show |(transitionMatrix 62 initial).v| ≤ 2 ^ 62 by omega)
  have hqBound : |(transitionMatrix 62 initial).q| ≤ signedRadix := by
    have := abs_nonneg (transitionMatrix 62 initial).r
    simpa only [signedRadix] using (show |(transitionMatrix 62 initial).q| ≤ 2 ^ 62 by omega)
  have hrBound : |(transitionMatrix 62 initial).r| ≤ signedRadix := by
    have := abs_nonneg (transitionMatrix 62 initial).q
    simpa only [signedRadix] using (show |(transitionMatrix 62 initial).r| ≤ 2 ^ 62 by omega)
  have huValue := word_signed_value u _ huBound hu
  have hvValue := word_signed_value v _ hvBound hv
  have hqValue := word_signed_value q _ hqBound hq
  have hrValue := word_signed_value r _ hrBound hr
  have hfirstBounds := divstep_product_i128 (UScalar.hcast .I64 u).val (UScalar.hcast .I64 r).val
    (by rw [huValue]; exact huBound) (by rw [hrValue]; exact hrBound)
  have hsecondBounds := divstep_product_i128 (UScalar.hcast .I64 v).val (UScalar.hcast .I64 q).val
    (by rw [hvValue]; exact hvBound) (by rw [hqValue]; exact hqBound)
  have hdet : (UScalar.hcast .I64 u).val * (UScalar.hcast .I64 r).val -
      (UScalar.hcast .I64 v).val * (UScalar.hcast .I64 q).val = 2 ^ 62 := by
    rw [huValue, hvValue, hqValue, hrValue]
    exact transition_matrix_det 62 initial
  have hrowFirst : (UScalar.hcast .I64 u).val.natAbs +
      (UScalar.hcast .I64 v).val.natAbs ≤ 2 ^ 62 := by
    rw [huValue, hvValue]
    apply Int.ofNat_le.mp
    simpa only [Nat.cast_add, Int.natCast_natAbs, Nat.cast_pow, Nat.cast_ofNat] using hrows.1
  have hrowSecond : (UScalar.hcast .I64 q).val.natAbs +
      (UScalar.hcast .I64 r).val.natAbs ≤ 2 ^ 62 := by
    rw [hqValue, hrValue]
    apply Int.ofNat_le.mp
    simpa only [Nat.cast_add, Int.natCast_natAbs, Nat.cast_pow, Nat.cast_ofNat] using hrows.2
  simp only [lift, bind_ok]
  step +scalarTac -grind with I128.mul_spec as ⟨first, hfirst⟩
  simp only [core.convert.num.FromI128I64.from_val_eq] at hfirst
  step +scalarTac -grind with I128.mul_spec as ⟨second, hsecond⟩
  simp only [core.convert.num.FromI128I64.from_val_eq] at hsecond
  step +scalarTac -grind with I128.sub_spec as ⟨det, hdetValue⟩
  step -grind with I128.ShiftLeft_IScalar_spec as ⟨radix128, hradix128, _⟩
  have hdetEq : det = radix128 := by
    apply IScalar.eq_of_val_eq
    simp only [hdetValue, hfirst, hsecond, hdet]
    norm_num [Int.shiftLeft_eq, I128.size, I128.numBits, Int.bmod] at hradix128
    exact hradix128.symm
  step -grind
  step -grind with native_unsigned_abs_spec as ⟨absU, habsU⟩
  step -grind with native_unsigned_abs_spec as ⟨absV, habsV⟩
  step +scalarTac -grind with U64.add_spec as ⟨rowFirst, hrowFirstValue⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨radix64, hradix64, _⟩
  have hrowFirstLe : rowFirst ≤ radix64 := by
    norm_num [Nat.shiftLeft_eq] at hradix64
    scalar_tac
  step -grind
  step -grind with native_unsigned_abs_spec as ⟨absQ, habsQ⟩
  step -grind with native_unsigned_abs_spec as ⟨absR, habsR⟩
  step +scalarTac -grind with U64.add_spec as ⟨rowSecond, hrowSecondValue⟩
  have hrowSecondLe : rowSecond ≤ radix64 := by
    norm_num [Nat.shiftLeft_eq] at hradix64
    scalar_tac
  step -grind
  try simp only [WP.spec_ok]
  exact ⟨huValue, hvValue, hqValue, hrValue, heta⟩

#print axioms divstep_product_i128
#print axioms native_divsteps_spec
end UdonVerify.CommonSigned62
