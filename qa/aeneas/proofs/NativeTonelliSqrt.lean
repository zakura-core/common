import NativeTonelli

open Aeneas Std Result

namespace UdonVerify.Sqrt
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev sqrtLoop := @SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_with_roots_loop0
abbrev sqrtBody := @SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_with_roots_loop0.body

theorem normal_order_search_eq {F : Type} (inst : SqrtField F)
    (m i : U32) (squared : F) :
    SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_with_roots_loop0_loop0
      inst m i squared = orderSearch inst m i squared := by
  rfl

theorem maximal_order_nonsquare {F K T : Type} [Field K] (inst : SqrtField F)
    (ops : Operations (K := K) inst) (callback : Aeneas.Std.core.ops.function.Fn T U32 F)
    (table : T) (n : U32) (roots : Roots ops callback table n)
    (hnPositive : 1 ≤ n.val) (hnBound : n.val ≤ 64)
    (a : K) (x t : F) (hx : ops.valid x) (ht : ops.valid t)
    (hequation : ops.value x ^ 2 = a * ops.value t)
    (hpower : ops.value t ^ (2 ^ n.val) = 1)
    (hhalf : ops.value t ^ (2 ^ (n.val - 1)) ≠ 1)
    (ha : a ≠ 0) (hroot : ¬ IsSquare (roots.value n.val)) : ¬ IsSquare a := by
  rcases WP.spec_imp_exists (roots.lookup n hnPositive (Nat.le_refl _)) with
    ⟨r, _, hrValid, hrValue⟩
  rcases WP.spec_imp_exists (ops.mul x r hx hrValid) with
    ⟨nextX, _, hxValid, hxValue⟩
  rcases WP.spec_imp_exists (ops.mul t r ht hrValid) with
    ⟨nextT, _, htValid, htValue⟩
  have hnextHalf : ops.value nextT ^ (2 ^ (n.val - 1)) = 1 := by
    rw [htValue, hrValue]
    exact correction_lowers_order _ _ _ (by omega) hpower hhalf
      (roots.half_power _ hnPositive (Nat.le_refl _))
  have hnextPower : ops.value nextT ^ (2 ^ n.val) = 1 := by
    rw [← predecessor_power n.val (by omega), pow_mul, hnextHalf, one_pow]
  have hnextEquation : ops.value nextX ^ 2 =
      (a * roots.value n.val) * ops.value nextT := by
    rw [hxValue, htValue, hrValue]
    exact nonsquare_correction_preserves_square _ _ _ _ hequation
  have hnextInvariant : correctionInvariant ops roots a nextX nextT false n := by
    exact ⟨hxValid, htValid, hnextEquation, hnextPower, Nat.le_refl _, Or.inr hnextHalf⟩
  rcases WP.spec_imp_exists (correction_loop_spec inst ops callback table n roots
    hnPositive hnBound a nextX nextT false n hnextInvariant) with
    ⟨out, _, _, houtEquation, houtFlag⟩
  have hfalse : out.1 = false := by
    cases hflag : out.1
    · rfl
    · have h := houtFlag hflag
      contradiction
  rw [hfalse] at houtEquation
  exact nonsquare_of_alternate_root a (roots.value n.val) (ops.value out.2) ha hroot
    (by simpa using houtEquation)

def sqrtResult {F K : Type} [Field K] {inst : SqrtField F}
    (ops : Operations (K := K) inst) (a : K) (out : Option F) : Prop :=
  match out with
  | none => ¬ IsSquare a
  | some root => ops.valid root ∧ ops.value root ^ 2 = a

theorem sqrt_loop_unfold {F T : Type} (inst : SqrtField F)
    (callback : Aeneas.Std.core.ops.function.Fn T U32 F) (table : T)
    (x t : F) (m : U32) :
    sqrtLoop inst callback table x t m = (do
      let flow ← sqrtBody inst callback table x t m
      match flow with
      | .done out => ok out
      | .cont next => sqrtLoop inst callback table next.1 next.2.1 next.2.2) := by
  unfold sqrtLoop SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_with_roots_loop0
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done out => rfl
  | cont tuple => rcases tuple with ⟨nextX, nextT, nextM⟩; rfl

@[step]
theorem sqrt_loop_spec {F K T : Type} [Field K] (inst : SqrtField F)
    (ops : Operations (K := K) inst) (callback : Aeneas.Std.core.ops.function.Fn T U32 F)
    (table : T) (n : U32) (roots : Roots ops callback table n)
    (hnPositive : 1 ≤ n.val) (hnBound : n.val ≤ 64)
    (a : K) (ha : a ≠ 0) (hroot : ¬ IsSquare (roots.value n.val))
    (x t : F) (m : U32) (hinvariant : correctionInvariant ops roots a x t true m) :
    sqrtLoop inst callback table x t m ⦃ out => sqrtResult ops a out ⦄ := by
  generalize hmeasure : m.val = measure
  induction measure using Nat.strong_induction_on generalizing x t m with
  | h measure ih =>
    rcases hinvariant with ⟨hx, ht, hequation, hpower, hmBound, hguard⟩
    have hequation' : ops.value x ^ 2 = a * ops.value t := by
      simpa only [↓reduceIte, mul_one] using hequation
    rw [sqrt_loop_unfold]
    unfold sqrtBody SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_with_roots_loop0.body
    step -grind with (ops.one_test t ht) as ⟨isOne, htest⟩
    split
    · rename_i hone
      simp only [bind_ok, WP.spec_ok, sqrtResult]
      exact ⟨hx, by simpa only [htest.mp hone, mul_one] using hequation'⟩
    · rename_i hnotOne
      have htNotOne : ops.value t ≠ 1 := by
        intro h
        exact hnotOne (htest.mpr h)
      have hmPositive : 1 ≤ m.val := by
        by_contra h
        have hmZero : m.val = 0 := by omega
        simp only [hmZero, pow_zero, pow_one] at hpower
        exact htNotOne hpower
      step -grind with (ops.square t ht) as ⟨squared, hsValid, hsPower⟩
      rw [normal_order_search_eq]
      step -grind with (order_search_spec inst ops m 1#u32 squared (ops.value t)
        (by omega) (by decide) hmPositive hsValid
        (by change ops.value squared = ops.value t ^ 2; exact hsPower)
        (by change ops.value t ^ 1 ≠ 1; simpa only [pow_one] using htNotOne)
        hpower) as ⟨i, hiPositive, hiBound, hiPower, hiPrevious⟩
      split
      · rename_i him
        have hmn : m = n := by
          rcases hguard with ⟨_, hmn⟩ | hhalf
          · exact hmn
          · exact False.elim (hiPrevious (by simpa only [him] using hhalf))
        simp only [bind_ok, WP.spec_ok, sqrtResult]
        exact maximal_order_nonsquare inst ops callback table n roots hnPositive hnBound
          a x t hx ht hequation' (by simpa only [hmn] using hpower)
          (by simpa only [him, hmn] using hiPrevious) ha hroot
      · rename_i hinotm
        have hiLess : i.val < m.val := by
          have hiNe : i.val ≠ m.val := by
            intro h
            exact hinotm (UScalar.eq_of_val_eq h)
          omega
        step -grind with UScalar.add_spec as ⟨nextIndex, hnextIndex⟩
        have hnextIndexVal : nextIndex.val = i.val + 1 := by scalar_tac
        step -grind with (roots.lookup nextIndex (by omega) (by omega))
          as ⟨rootNext, hrootNextValid, hrootNextValue⟩
        step -grind with (roots.lookup i hiPositive (by omega))
          as ⟨rootI, hrootIValid, hrootIValue⟩
        step -grind with (ops.mul x rootNext hx hrootNextValid)
          as ⟨nextX, hxValid, hxValue⟩
        step -grind with (ops.mul t rootI ht hrootIValid)
          as ⟨nextT, htValid, htValue⟩
        have hnextHalf : ops.value nextT ^ (2 ^ (i.val - 1)) = 1 := by
          rw [htValue, hrootIValue]
          exact correction_lowers_order _ _ _ (by omega) hiPower hiPrevious
            (roots.half_power _ hiPositive (by omega))
        have hnextPower : ops.value nextT ^ (2 ^ i.val) = 1 := by
          rw [← predecessor_power i.val (by omega), pow_mul, hnextHalf, one_pow]
        have hnextEquation : ops.value nextX ^ 2 = a * ops.value nextT := by
          rw [hxValue, htValue, hrootNextValue, hrootIValue, hnextIndexVal]
          exact correction_preserves_square _ _ _ _ _ hequation'
            (roots.next_square _ hiPositive (by omega))
        have hnextInvariant : correctionInvariant ops roots a nextX nextT true i := by
          exact ⟨hxValid, htValid, by simpa only [↓reduceIte, mul_one] using hnextEquation,
            hnextPower, by omega, Or.inr hnextHalf⟩
        step -grind with (ih i.val (by omega) nextX nextT i hnextInvariant rfl)
          as ⟨out, hout⟩
        exact hout

@[step]
theorem tonelli_shanks_spec {F K T : Type} [Field K] (inst : SqrtField F)
    (ops : Operations (K := K) inst) (callback : Aeneas.Std.core.ops.function.Fn T U32 F)
    (table : T) (n : U32) (roots : Roots ops callback table n)
    (hnPositive : 1 ≤ n.val) (hnBound : n.val ≤ 64)
    (value w : F) (hvalue : ops.valid value) (hw : ops.valid w)
    (hpower : ops.value value ≠ 0 →
      (ops.value value * ops.value w ^ 2) ^ (2 ^ n.val) = 1)
    (hroot : ¬ IsSquare (roots.value n.val)) :
    SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_with_roots
      inst callback value w table n ⦃ out => sqrtResult ops (ops.value value) out ⦄ := by
  unfold SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_with_roots
  simp only [core.ops.range.RangeInclusive.new,bind_ok]
  rw [range_check_eq n hnPositive hnBound]
  simp only [bind_ok,Bool.true_eq,massert_True]
  step -grind with (ops.zero_test value hvalue) as ⟨isZero, htest⟩
  split
  · rename_i hzero
    rcases WP.spec_imp_exists ops.zero with ⟨zero, hzeroResult, hzeroValid, hzeroValue⟩
    rw [hzeroResult]
    simp only [bind_ok, WP.spec_ok, sqrtResult]
    exact ⟨hzeroValid, by simp only [hzeroValue, htest.mp hzero, pow_two, zero_mul]⟩
  · rename_i hnotZero
    have ha : ops.value value ≠ 0 := by
      intro h
      exact hnotZero (htest.mpr h)
    step -grind with (ops.mul w value hw hvalue) as ⟨x, hxValid, hxValue⟩
    step -grind with (ops.mul x w hxValid hw) as ⟨t, htValid, htValue⟩
    have htPower : ops.value t ^ (2 ^ n.val) = 1 := by
      have htEquation : ops.value t = ops.value value * ops.value w ^ 2 := by
        rw [htValue, hxValue]; ring
      rw [htEquation]
      exact hpower ha
    have hequation : ops.value x ^ 2 = ops.value value * ops.value t := by
      rw [htValue, hxValue]; ring
    have hinvariant : correctionInvariant ops roots (ops.value value) x t true n := by
      exact ⟨hxValid, htValid, by simpa only [↓reduceIte, mul_one] using hequation,
        htPower, Nat.le_refl _, Or.inl ⟨rfl, rfl⟩⟩
    step -grind with (sqrt_loop_spec inst ops callback table n roots hnPositive hnBound
      (ops.value value) ha hroot x t n hinvariant) as ⟨out, hout⟩
    exact hout

#print axioms maximal_order_nonsquare
#print axioms sqrt_loop_spec
#print axioms tonelli_shanks_spec

end UdonVerify.Sqrt
