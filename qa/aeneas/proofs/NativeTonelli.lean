import SqrtAlgorithms.Funs
import SqrtCorrectionMath
import RangeContainsProofs

open Aeneas Std Result

namespace UdonVerify.Sqrt
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev SqrtField := SqrtAlgorithms.field.pasta.algorithms.SqrtField
abbrev orderSearch :=
  @SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_alt_with_roots_loop0_loop0
abbrev orderSearchBody :=
  @SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_alt_with_roots_loop0_loop0.body
abbrev correctionLoop :=
  @SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_alt_with_roots_loop0
abbrev correctionBody :=
  @SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_alt_with_roots_loop0.body

/-- Representation invariants and field semantics supplied by the native proofs. -/
structure Operations {F K : Type} [Field K] (inst : SqrtField F) where
  value : F → K
  valid : F → Prop
  zero : inst.ZERO ⦃ out => valid out ∧ value out = 0 ⦄
  zero_test : ∀ x, valid x → inst.is_zero x ⦃ b => b = true ↔ value x = 0 ⦄
  one_test : ∀ x, valid x → inst.is_one x ⦃ b => b = true ↔ value x = 1 ⦄
  square : ∀ x, valid x → inst.FieldInst.square x
    ⦃ out => valid out ∧ value out = value x ^ 2 ⦄
  mul : ∀ x y, valid x → valid y → inst.FieldInst.mul x y
    ⦃ out => valid out ∧ value out = value x * value y ⦄

theorem order_search_unfold {F : Type} (inst : SqrtField F)
    (m i : U32) (squared : F) :
    orderSearch inst m i squared = (do
      let flow ← orderSearchBody inst m i squared
      match flow with
      | .done out => ok out
      | .cont (next, value) => orderSearch inst m next value) := by
  unfold orderSearch
    SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_alt_with_roots_loop0_loop0
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done out => rfl
  | cont pair => rcases pair with ⟨next, value⟩; rfl

@[step]
theorem order_search_spec {F K : Type} [Field K] (inst : SqrtField F)
    (ops : Operations (K := K) inst) (m i : U32) (squared : F) (t : K)
    (hm : m.val ≤ 64) (hi : 1 ≤ i.val) (him : i.val ≤ m.val)
    (hvalid : ops.valid squared) (hsquared : ops.value squared = t ^ (2 ^ i.val))
    (hprevious : t ^ (2 ^ (i.val - 1)) ≠ 1) (hpower : t ^ (2 ^ m.val) = 1) :
    orderSearch inst m i squared ⦃ out => 1 ≤ out.val ∧ out.val ≤ m.val ∧
      t ^ (2 ^ out.val) = 1 ∧ t ^ (2 ^ (out.val - 1)) ≠ 1 ⦄ := by
  generalize hn : m.val - i.val = n
  induction n using Nat.strong_induction_on generalizing i squared with
  | h n ih =>
    rw [order_search_unfold]
    unfold orderSearchBody
      SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_alt_with_roots_loop0_loop0.body
    split
    · rename_i hlt
      have hltv : i.val < m.val := by scalar_tac
      step -grind with (ops.one_test squared hvalid) as ⟨isOne, htest⟩
      split
      · rename_i hone
        simp only [bind_ok, WP.spec_ok]
        exact ⟨hi, him, hsquared.symm.trans (htest.mp hone), hprevious⟩
      · rename_i hnotOne
        have hnot : t ^ (2 ^ i.val) ≠ 1 := by
          intro h
          have hb := htest.mpr (hsquared.trans h)
          exact hnotOne hb
        step -grind with (ops.square squared hvalid) as ⟨nextSquare, hnextValid, hnextSquare⟩
        step -grind with UScalar.add_spec as ⟨next, hnext⟩
        have hnextVal : next.val = i.val + 1 := by scalar_tac
        have hnextPower : ops.value nextSquare = t ^ (2 ^ next.val) := by
          rw [hnextSquare, hsquared, ← pow_mul, hnextVal, pow_succ]
        step -grind with (ih (m.val - next.val) (by omega) next nextSquare
          (by omega) (by omega) hnextValid hnextPower
          (by simpa only [hnextVal, Nat.add_sub_cancel] using hnot) rfl)
          as ⟨out, houtPositive, houtBound, houtPower, houtPrevious⟩
        exact ⟨houtPositive, houtBound, houtPower, houtPrevious⟩
    · rename_i hge
      have heq : i.val = m.val := by scalar_tac
      simp only [bind_ok, WP.spec_ok]
      exact ⟨hi, him, by simpa only [heq] using hpower, hprevious⟩

#print axioms order_search_spec

/-- The extracted root callback and its checked table identities. -/
structure Roots {F K T : Type} [Field K] {inst : SqrtField F}
    (ops : Operations (K := K) inst) (callback : Aeneas.Std.core.ops.function.Fn T U32 F)
    (table : T) (n : U32) where
  value : Nat → K
  lookup : ∀ k : U32, 1 ≤ k.val → k.val ≤ n.val → callback.call table k
    ⦃ out => ops.valid out ∧ ops.value out = value k.val ⦄
  half_power : ∀ k, 1 ≤ k → k ≤ n.val → value k ^ (2 ^ (k - 1)) = -1
  next_square : ∀ k, 1 ≤ k → k < n.val → value (k + 1) ^ 2 = value k

def correctionInvariant {F K T : Type} [Field K] {inst : SqrtField F}
    (ops : Operations (K := K) inst) {callback : Aeneas.Std.core.ops.function.Fn T U32 F}
    {table : T} {n : U32} (roots : Roots ops callback table n)
    (a : K) (x t : F) (flag : Bool) (m : U32) : Prop :=
  ops.valid x ∧ ops.valid t ∧
  ops.value x ^ 2 = (a * if flag then 1 else roots.value n.val) * ops.value t ∧
  ops.value t ^ (2 ^ m.val) = 1 ∧ m.val ≤ n.val ∧
  ((flag = true ∧ m = n) ∨ ops.value t ^ (2 ^ (m.val - 1)) = 1)

theorem correction_loop_unfold {F T : Type} (inst : SqrtField F)
    (callback : Aeneas.Std.core.ops.function.Fn T U32 F) (table : T) (n : U32)
    (x t : F) (flag : Bool) (m : U32) :
    correctionLoop inst callback x t table n flag m = (do
      let flow ← correctionBody inst callback table n x t flag m
      match flow with
      | .done out => ok out
      | .cont next =>
        correctionLoop inst callback next.1 next.2.1 table n next.2.2.1 next.2.2.2) := by
  unfold correctionLoop
    SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_alt_with_roots_loop0
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done out => rfl
  | cont tuple => rcases tuple with ⟨nextX, nextT, nextFlag, nextM⟩; rfl

@[step]
theorem correction_loop_spec {F K T : Type} [Field K] (inst : SqrtField F)
    (ops : Operations (K := K) inst) (callback : Aeneas.Std.core.ops.function.Fn T U32 F)
    (table : T) (n : U32) (roots : Roots ops callback table n)
    (hnPositive : 1 ≤ n.val) (hnBound : n.val ≤ 64)
    (a : K) (x t : F) (flag : Bool) (m : U32)
    (hinvariant : correctionInvariant ops roots a x t flag m) :
    correctionLoop inst callback x t table n flag m ⦃ out =>
      ops.valid out.2 ∧ ops.value out.2 ^ 2 = a * (if out.1 then 1 else roots.value n.val) ∧
      (out.1 = true → flag = true) ⦄ := by
  generalize hrank : correctionRank m.val flag = rank
  induction rank using Nat.strong_induction_on generalizing x t flag m with
  | h rank ih =>
    rcases hinvariant with ⟨hx, ht, hequation, hpower, hmBound, hguard⟩
    rw [correction_loop_unfold]
    unfold correctionBody
      SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_alt_with_roots_loop0.body
    step -grind with (ops.one_test t ht) as ⟨isOne, htest⟩
    split
    · rename_i hone
      have htOne := htest.mp hone
      simp only [bind_ok, WP.spec_ok]
      refine ⟨hx, ?_, fun h => h⟩
      simpa only [htOne, mul_one] using hequation
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
      step -grind with (order_search_spec inst ops m 1#u32 squared (ops.value t)
        (by omega) (by decide) hmPositive hsValid
        (by change ops.value squared = ops.value t ^ 2; exact hsPower)
        (by change ops.value t ^ 1 ≠ 1; simpa only [pow_one] using htNotOne)
        hpower) as ⟨i, hiPositive, hiBound, hiPower, hiPrevious⟩
      have hassert : i = m → flag = true ∧ m = n := by
        intro him
        rcases hguard with hfirst | hhalf
        · exact hfirst
        · exact False.elim (hiPrevious (by simpa only [him] using hhalf))
      have hassertFlag : ((¬ (i = m)) || flag) = true := by
        by_cases him : i = m
        · simp only [him, (hassert him).1, Bool.or_true]
        · simp [him]
      have hassertN : ((¬ (i = m)) || (m = n)) = true := by
        by_cases him : i = m
        · simp only [him, (hassert him).2, Bool.or_true, decide_true]
        · simp [him]
      simp only [hassertFlag,hassertN,Bool.true_eq,massert_True,bind_ok]
      split
      · rename_i him
        have hflag : flag = true := by
          rcases hguard with ⟨hflag, hmn⟩ | hhalf
          · exact hflag
          · exact False.elim (hiPrevious (by simpa only [him] using hhalf))
        have hmn : m = n := by
          rcases hguard with ⟨hflag, hmn⟩ | hhalf
          · exact hmn
          · exact False.elim (hiPrevious (by simpa only [him] using hhalf))
        rw [hmn]
        step -grind with (roots.lookup n hnPositive (Nat.le_refl _)) as ⟨r, hrValid, hrValue⟩
        step -grind with (ops.mul x r hx hrValid) as ⟨nextX, hxValid, hxValue⟩
        step -grind with (ops.mul t r ht hrValid) as ⟨nextT, htValid, htValue⟩
        have hnextHalf : ops.value nextT ^ (2 ^ (n.val - 1)) = 1 := by
          rw [htValue, hrValue]
          apply correction_lowers_order
            (ops.value t) (roots.value n.val) n.val (by omega)
          · simpa only [him, hmn] using hiPower
          · simpa only [him, hmn] using hiPrevious
          · exact roots.half_power _ hnPositive (Nat.le_refl _)
        have hnextPower : ops.value nextT ^ (2 ^ n.val) = 1 := by
          rw [← predecessor_power n.val (by omega), pow_mul, hnextHalf, one_pow]
        have hnextEquation : ops.value nextX ^ 2 =
            (a * roots.value n.val) * ops.value nextT := by
          rw [hxValue, htValue, hrValue]
          apply nonsquare_correction_preserves_square
          simpa [hflag] using hequation
        have hnextInvariant : correctionInvariant ops roots a nextX nextT false n := by
          exact ⟨hxValid, htValid, hnextEquation, hnextPower, Nat.le_refl _, Or.inr hnextHalf⟩
        have hdecrease : correctionRank n.val false < rank := by
          rw [← hrank, hflag, hmn]
          exact nonsquare_correction_rank_decreases _
        step -grind with (ih (correctionRank n.val false) hdecrease nextX nextT false n
          hnextInvariant rfl) as ⟨out, houtValid, houtEquation, houtFlag⟩
        exact ⟨houtValid, houtEquation, fun _ => hflag⟩
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
        step -grind with (ops.mul x rootNext hx hrootNextValid)
          as ⟨nextX, hxValid, hxValue⟩
        step -grind with (roots.lookup i hiPositive (by omega))
          as ⟨rootI, hrootIValid, hrootIValue⟩
        step -grind with (ops.mul t rootI ht hrootIValid)
          as ⟨nextT, htValid, htValue⟩
        have hnextHalf : ops.value nextT ^ (2 ^ (i.val - 1)) = 1 := by
          rw [htValue, hrootIValue]
          exact correction_lowers_order (ops.value t) (roots.value i.val) i.val
            (by omega) hiPower hiPrevious (roots.half_power _ hiPositive (by omega))
        have hnextPower : ops.value nextT ^ (2 ^ i.val) = 1 := by
          rw [← predecessor_power i.val (by omega), pow_mul, hnextHalf, one_pow]
        have hnextEquation : ops.value nextX ^ 2 =
            (a * if flag then 1 else roots.value n.val) * ops.value nextT := by
          rw [hxValue, htValue, hrootNextValue, hrootIValue, hnextIndexVal]
          exact correction_preserves_square _ _ _ _ _ hequation
            (roots.next_square _ hiPositive (by omega))
        have hnextInvariant : correctionInvariant ops roots a nextX nextT flag i := by
          exact ⟨hxValid, htValid, hnextEquation, hnextPower, by omega, Or.inr hnextHalf⟩
        have hdecrease : correctionRank i.val flag < rank := by
          rw [← hrank]
          exact correction_rank_decreases _ _ _ hiLess
        step -grind with (ih (correctionRank i.val flag) hdecrease nextX nextT flag i
          hnextInvariant rfl) as ⟨out, houtValid, houtEquation, houtFlag⟩
        exact ⟨houtValid, houtEquation, houtFlag⟩

#print axioms correction_loop_spec

@[step]
theorem correction_spec {F K T : Type} [Field K] (inst : SqrtField F)
    (ops : Operations (K := K) inst) (callback : Aeneas.Std.core.ops.function.Fn T U32 F)
    (table : T) (n : U32) (roots : Roots ops callback table n)
    (hnPositive : 1 ≤ n.val) (hnBound : n.val ≤ 64)
    (a : K) (x t : F) (hx : ops.valid x) (ht : ops.valid t)
    (hequation : ops.value x ^ 2 = a * ops.value t)
    (hpower : ops.value t ^ (2 ^ n.val) = 1) :
    SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_alt_with_roots
      inst callback x t table n ⦃ out => ops.valid out.2 ∧
        ops.value out.2 ^ 2 = a * (if out.1 then 1 else roots.value n.val) ⦄ := by
  unfold SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_alt_with_roots
  simp only [core.ops.range.RangeInclusive.new,bind_ok]
  rw [range_check_eq n hnPositive hnBound]
  simp only [bind_ok,Bool.true_eq,massert_True]
  have hinvariant : correctionInvariant ops roots a x t true n := by
    exact ⟨hx, ht, by simpa only [↓reduceIte, mul_one] using hequation,
      hpower, Nat.le_refl _, Or.inl ⟨rfl, rfl⟩⟩
  step -grind with (correction_loop_spec inst ops callback table n roots hnPositive hnBound
    a x t true n hinvariant) as ⟨out, houtValid, houtEquation, houtFlag⟩
  exact ⟨houtValid, houtEquation⟩

@[step]
theorem correction_square_flag_spec {F K T : Type} [Field K] (inst : SqrtField F)
    (ops : Operations (K := K) inst) (callback : Aeneas.Std.core.ops.function.Fn T U32 F)
    (table : T) (n : U32) (roots : Roots ops callback table n)
    (hnPositive : 1 ≤ n.val) (hnBound : n.val ≤ 64)
    (a : K) (x t : F) (hx : ops.valid x) (ht : ops.valid t)
    (hequation : ops.value x ^ 2 = a * ops.value t)
    (hpower : ops.value t ^ (2 ^ n.val) = 1)
    (ha : a ≠ 0) (hroot : ¬ IsSquare (roots.value n.val)) :
    SqrtAlgorithms.field.pasta.algorithms.tonelli_shanks_alt_with_roots
      inst callback x t table n ⦃ out => ops.valid out.2 ∧
        ops.value out.2 ^ 2 = a * (if out.1 then 1 else roots.value n.val) ∧
        (out.1 = true ↔ IsSquare a) ⦄ := by
  apply WP.spec_mono (correction_spec inst ops callback table n roots hnPositive hnBound
    a x t hx ht hequation hpower)
  intro out hout
  exact ⟨hout.1, hout.2, square_flag_correct a (roots.value n.val) (ops.value out.2)
    out.1 ha hroot hout.2⟩

#print axioms correction_spec
#print axioms correction_square_flag_spec

end UdonVerify.Sqrt
