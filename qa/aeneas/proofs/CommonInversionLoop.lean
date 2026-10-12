import CommonInversionBody
import CommonInversionRangeIterator

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def BoundedInversionResult {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (out : A4 × U32) : Prop :=
  InversionResult params x out.1 ∧ 2 ≤ out.2.val ∧ out.2.val ≤ 12

def InversionLoopInvariant {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (state : InversionLoopState) : Prop :=
  match state with
  | (iter, f, g, d, e, eta, len) =>
    ∃ batches, (1 ≤ batches ∧ batches ≤ 11) ∧ iter = inversionRange iter.start ∧
      iter.start.val = batches + 1 ∧ InversionInvariant params x batches f g d e eta len

def inversionLoopMeasure (state : InversionLoopState) : Nat := 12 - state.1.start.val

theorem inversion_loop_body_progress {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int)
    (hx : 0 ≤ x ∧ x < signed62Value params.helpers.modulus)
    (hgcd : Int.gcd (signed62Value params.helpers.modulus) x = 1)
    (hconverges : (inversionTrace (signed62Value params.helpers.modulus) x 12).g = 0)
    (state : InversionLoopState) (hinv : InversionLoopInvariant params x state) :
    (let (iter, f, g, d, e, eta, len) := state;
      CommonInversion.field.pasta.safegcd.invert_counted_loop.body inst iter f g d e eta len) ⦃ flow =>
        match flow with
        | .done out => BoundedInversionResult params x out
        | .cont next => InversionLoopInvariant params x next ∧
            inversionLoopMeasure next < inversionLoopMeasure state ⦄ := by
  rcases state with ⟨iter, f, g, d, e, eta, len⟩
  rcases hinv with ⟨batches, hb, hiter, hstart, hinv⟩
  dsimp only
  by_cases hlast : batches = 11
  · have hs : iter.start = 12#u32 := UScalar.eq_of_val_eq (by change iter.start.val = 12; omega)
    have hi : iter = inversionRange 12#u32 := hiter.trans (congrArg inversionRange hs)
    subst iter
    apply WP.spec_mono (inversion_body_spec params x batches f g d e eta len hinv hb.2 hx hgcd
      _ ⟨12#u32, 12#u32, true⟩ 12#u32 inversion_range_next_last)
    intro flow hflow
    cases flow with
    | done out =>
      rcases out with ⟨out, count⟩
      change InversionResult params x out ∧ 2 ≤ count.val ∧ count.val ≤ 12
      exact ⟨hflow.1, by rw [hflow.2]; decide⟩
    | cont next =>
      rcases next with ⟨iter1, f1, g1, d1, e1, eta1, len1⟩
      exact False.elim (hflow.2.2 (by simpa only [hlast] using hconverges))
  · have hs : iter.start.val < 12 := by omega
    let next : U32 := UScalar.ofNatCore (iter.start.val + 1) (by
      norm_num [UScalarTy.numBits]
      omega)
    have hn : next.val = iter.start.val + 1 := UScalar.ofNatCore_val_eq _
    have hnext : core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next core.iter.range.StepU32 iter =
        ok (some iter.start, inversionRange next) := by
      conv_lhs => rw [hiter]
      exact inversion_range_next_lt _ next hs hn
    apply WP.spec_mono (inversion_body_spec params x batches f g d e eta len hinv hb.2 hx hgcd
      iter (inversionRange next) iter.start hnext)
    intro flow hflow
    cases flow with
    | done out =>
      rcases out with ⟨out, count⟩
      change InversionResult params x out ∧ 2 ≤ count.val ∧ count.val ≤ 12
      exact ⟨hflow.1, by rw [hflow.2]; constructor <;> omega⟩
    | cont state =>
      rcases state with ⟨iter1, f1, g1, d1, e1, eta1, len1⟩
      rcases hflow with ⟨hiter1, hnew, _⟩
      subst iter1
      constructor
      · exact ⟨batches + 1, by omega, rfl, by simpa only [inversionRange] using hn.trans (by omega), hnew⟩
      · simp only [inversionLoopMeasure, inversionRange]
        omega

@[step]
theorem inversion_loop_spec {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (batches : Nat) (start : U32)
    (f g d e : Signed62) (eta : I64) (len : Usize)
    (hb : 1 ≤ batches ∧ batches ≤ 11) (hstart : start.val = batches + 1)
    (hinv : InversionInvariant params x batches f g d e eta len)
    (hx : 0 ≤ x ∧ x < signed62Value params.helpers.modulus)
    (hgcd : Int.gcd (signed62Value params.helpers.modulus) x = 1)
    (hconverges : (inversionTrace (signed62Value params.helpers.modulus) x 12).g = 0) :
    CommonInversion.field.pasta.safegcd.invert_counted_loop inst (inversionRange start) f g d e eta len ⦃ out =>
      BoundedInversionResult params x out ⦄ := by
  unfold CommonInversion.field.pasta.safegcd.invert_counted_loop
  apply loop.spec_decr_nat inversionLoopMeasure (InversionLoopInvariant params x)
    (BoundedInversionResult params x)
  · intro state hstate
    rcases state with ⟨iter, f, g, d, e, eta, len⟩
    have hprogress := inversion_loop_body_progress params x hx hgcd hconverges (iter, f, g, d, e, eta, len) hstate
    simp only [Std.uncurry] at hprogress ⊢
    apply WP.spec_mono hprogress
    intro flow hflow
    cases flow <;> exact hflow
  · exact ⟨batches, hb, rfl, hstart, hinv⟩

#print axioms inversion_loop_body_progress
#print axioms inversion_loop_spec
end UdonVerify.CommonSigned62
