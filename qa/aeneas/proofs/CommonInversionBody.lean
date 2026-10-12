import CommonInversionChecks
import CommonInversionContinue
import CommonInversionFinish

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev InversionLoopState := core.ops.range.RangeInclusive U32 × Signed62 × Signed62 × Signed62 × Signed62 × I64 × Usize
abbrev InversionLoopFlow := ControlFlow InversionLoopState (A4 × U32)

def nativeInversionBody {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P)
    (iter : core.ops.range.RangeInclusive U32) (f g d e : Signed62) (eta : I64) (len : Usize) :
    Result InversionLoopFlow := do
  let (o, iter1) ← core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next core.iter.range.StepU32 iter
  match o with
  | none => fail .panic
  | some batch =>
    let fg ← nativeInversionBatch len f g eta
    let zero ← CommonInversion.field.pasta.safegcd.is_zero fg.g len
    if zero then
      let out ← nativeInversionFinish inst iter1 fg.f d e fg.matrix.u fg.matrix.v len
      ok (.done (out, batch))
    else
      let (d1, e1) ← CommonInversion.field.pasta.safegcd.update_de_62 inst d e fg.matrix
      CommonInversion.field.pasta.safegcd.checks.assert_fg_range inst fg.f fg.g len
      let (f1, g1, len1) ← CommonInversion.field.pasta.safegcd.shrink_len fg.f fg.g len
      ok (.cont (iter1, f1, g1, d1, e1, fg.eta, len1))

theorem inversion_body_bridge {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P)
    (iter : core.ops.range.RangeInclusive U32) (f g d e : Signed62) (eta : I64) (len : Usize) :
    CommonInversion.field.pasta.safegcd.invert_counted_loop.body inst iter f g d e eta len =
      nativeInversionBody inst iter f g d e eta len := by
  unfold CommonInversion.field.pasta.safegcd.invert_counted_loop.body nativeInversionBody
    nativeInversionBatch nativeInversionFinish nativeUnitCheck one62 make62
  simp only [lift, bind_ok, Std.bind_assoc]
  congr 1

def InversionBodyPost {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (batches : Nat)
    (iter : core.ops.range.RangeInclusive U32) (batch : U32) (flow : InversionLoopFlow) : Prop :=
  match flow with
  | .done (out, count) => InversionResult params x out ∧ count = batch
  | .cont (iter1, f, g, d, e, eta, len) =>
    iter1 = iter ∧ InversionInvariant params x (batches + 1) f g d e eta len ∧
      (inversionTrace (signed62Value params.helpers.modulus) x (batches + 1)).g ≠ 0

@[step]
theorem inversion_body_spec {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (batches : Nat) (f g d e : Signed62)
    (eta : I64) (len : Usize) (hinv : InversionInvariant params x batches f g d e eta len)
    (hb : batches ≤ 11) (hx : 0 ≤ x ∧ x < signed62Value params.helpers.modulus)
    (hgcd : Int.gcd (signed62Value params.helpers.modulus) x = 1)
    (iter iter1 : core.ops.range.RangeInclusive U32) (batch : U32)
    (hnext : core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next core.iter.range.StepU32 iter =
      ok (some batch, iter1)) :
    CommonInversion.field.pasta.safegcd.invert_counted_loop.body inst iter f g d e eta len ⦃ flow =>
      InversionBodyPost params x batches iter1 batch flow ⦄ := by
  rw [inversion_body_bridge]
  unfold nativeInversionBody
  rw [hnext]
  simp only [bind_ok]
  apply WP.spec_bind (native_inversion_batch_spec params x batches f g d e eta len hb hinv)
  intro fg hfg
  apply WP.spec_bind (inversion_is_zero_spec fg.g len hinv.length hfg.g_normalized)
  intro zero hzero
  cases zero with
  | true =>
    simp only [ite_true]
    apply WP.spec_bind (native_inversion_finish_spec params x batches f g d e eta len hinv fg hfg iter1 hgcd
      (hzero.mp rfl))
    intro out hout
    simp [InversionBodyPost, WP.spec_ok, hout]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hnonzero : (inversionTrace (signed62Value params.helpers.modulus) x (batches + 1)).g ≠ 0 := by
      intro h
      have hvalue : active62Value fg.g len.val = 0 := hfg.g_value.trans h
      exact Bool.false_ne_true (hzero.mpr hvalue)
    apply WP.spec_bind (native_coefficient_continue_spec params x batches f g d e eta len hinv fg hfg)
    intro de hde
    rcases de with ⟨d1, e1⟩
    dsimp only at hde ⊢
    rw [fg_result_eq (inversion_fg_range_spec params x (batches + 1) fg.f fg.g d1 e1 fg.eta len hde hx)]
    simp only [bind_ok]
    apply WP.spec_bind (shrink_inversion_spec params x (batches + 1) fg.f fg.g d1 e1 fg.eta len hde)
    intro result hresult
    rcases result with ⟨f1, g1, len1⟩
    simp [InversionBodyPost, WP.spec_ok, hresult, hnonzero]

#print axioms inversion_body_bridge
#print axioms inversion_body_spec
end UdonVerify.CommonSigned62
