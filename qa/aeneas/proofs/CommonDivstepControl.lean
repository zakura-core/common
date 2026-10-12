import CommonDivstepLimit
import CommonPositiveEta
import CommonNegativeEta
import CommonDivstepCompose

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev DivWordState := I64 × U64 × U64 × U64 × U64 × U64 × U64 × U32
abbrev DivWordOutput := I64 × U64 × U64 × U64 × U64
abbrev DivCancelOutput := I64 × U64 × U64 × U64 × U64 × U64 × U64 × U64 × U64

def positiveEtaMultiplier (f g mask : U64) : Result U64 := do
  let correction ← ((core.num.U64.wrapping_add f 1#u64 &&& 4#u64) <<< 1#i32)
  let inverse := core.num.U64.wrapping_add f correction
  let negative ← CommonDivsteps.core.num.U64.wrapping_neg inverse
  ok (core.num.U64.wrapping_mul negative g &&& mask)

def cancellationMask (limit : U32) (mask : U64) : Result U64 := do
  let shift ← 64#u32 - limit
  let full ← core.num.U64.MAX >>> shift
  ok (full &&& mask)

def etaRangeCheck (eta : I64) : Result Unit := do
  let range ← core.ops.range.RangeInclusive.new (-745)#i64 745#i64
  let inside ← core.ops.range.RangeInclusive.contains core.cmp.PartialOrdI64
    core.cmp.PartialOrdI64 core.cmp.PartialOrdI64 range eta
  massert inside

def limitRangeCheck (limit : U32) : Result Unit := do
  let range ← core.ops.range.RangeInclusive.new 1#u32 62#u32
  let inside ← core.ops.range.RangeInclusive.contains core.cmp.PartialOrdU32
    core.cmp.PartialOrdU32 core.cmp.PartialOrdU32 range limit
  massert inside

def nativeCancel (eta : I64) (u v q r f g : U64) (remaining : U32) : Result DivCancelOutput := do
  if eta < 0#i64 then
    let nextEta ← -. eta
    let nextG ← CommonDivsteps.core.num.U64.wrapping_neg f
    let nextQ ← CommonDivsteps.core.num.U64.wrapping_neg u
    let nextR ← CommonDivsteps.core.num.U64.wrapping_neg v
    let limit ← etaLimit nextEta remaining
    limitRangeCheck limit
    let mask ← cancellationMask limit 63#u64
    let w ← CommonDivsteps.field.pasta.safegcd.negative_eta_multiplier g nextG mask
    ok (nextEta, q, r, nextQ, nextR, g, nextG, mask, w)
  else
    let limit ← etaLimit eta remaining
    limitRangeCheck limit
    let mask ← cancellationMask limit 15#u64
    let w ← positiveEtaMultiplier f g mask
    ok (eta, u, v, q, r, f, g, mask, w)

def nativeOdd (f0 g0 : U64) (eta : I64) (u v q r f g : U64) (remaining : U32) :
    Result (ControlFlow DivWordState DivWordOutput) := do
  massert (f &&& 1#u64 = 1#u64)
  massert (g &&& 1#u64 = 1#u64)
  let performed ← 62#u32 - remaining
  let first ← f <<< performed
  massert (core.num.U64.wrapping_add (core.num.U64.wrapping_mul u f0)
    (core.num.U64.wrapping_mul v g0) = first)
  let second ← g <<< performed
  massert (core.num.U64.wrapping_add (core.num.U64.wrapping_mul q f0)
    (core.num.U64.wrapping_mul r g0) = second)
  etaRangeCheck eta
  let (eta1, u1, v1, q1, r1, f1, g1, mask, w) ← nativeCancel eta u v q r f g remaining
  let nextG := core.num.U64.wrapping_add g1 (core.num.U64.wrapping_mul f1 w)
  let nextQ := core.num.U64.wrapping_add q1 (core.num.U64.wrapping_mul u1 w)
  let nextR := core.num.U64.wrapping_add r1 (core.num.U64.wrapping_mul v1 w)
  massert (nextG &&& mask = 0#u64)
  ok (ControlFlow.cont (eta1, u1, v1, nextQ, nextR, f1, nextG, remaining))

theorem native_wrapping_neg_eq (value : U64) :
    CommonDivsteps.core.num.U64.wrapping_neg value = ok (UScalar.wrapping_sub 0#u64 value) := by
  rfl

@[step]
theorem positive_eta_multiplier_spec (f g mask : U64) (n : Nat) (hn : n ≤ 4)
    (hm : mask.val = 2 ^ n - 1) (hodd : f.val % 2 = 1) :
    positiveEtaMultiplier f g mask ⦃ out =>
      out.val < 2 ^ n ∧ (g.val + f.val * out.val) % 2 ^ n = 0 ⦄ := by
  unfold positiveEtaMultiplier
  step -grind with (positive_correction_shift f) as ⟨correction, hcorrection⟩
  simp only [hcorrection, native_wrapping_neg_eq, bind_ok, WP.spec_ok,
    core.num.U64.wrapping_add, core.num.U64.wrapping_mul]
  exact positive_eta_word_spec f g mask n hn hm hodd

@[step]
theorem cancellation_mask_result_spec (limit : U32) (cap : Nat) (mask : U64)
    (hl : 0 < limit.val ∧ limit.val ≤ 62) (hm : mask.val = 2 ^ cap - 1) :
    cancellationMask limit mask ⦃ out => out.val = 2 ^ (min limit.val cap) - 1 ⦄ := by
  exact cancellation_mask_spec limit cap mask hl hm

theorem eta_range_check_eq (eta : I64) (he : -745 ≤ eta.val ∧ eta.val ≤ 745) :
    etaRangeCheck eta = ok () := by
  simp [etaRangeCheck, core.ops.range.RangeInclusive.new,
    core.ops.range.RangeInclusive.contains, core.cmp.PartialOrdI64,
    core.cmp.impls.PartialOrdI64.le, liftFun2, Bind.bind, massert, he.1, he.2]

theorem limit_range_check_eq (limit : U32) (hl : 1 ≤ limit.val ∧ limit.val ≤ 62) :
    limitRangeCheck limit = ok () := by
  simp [limitRangeCheck, core.ops.range.RangeInclusive.new,
    core.ops.range.RangeInclusive.contains, core.cmp.PartialOrdU32,
    core.cmp.impls.PartialOrdU32.le, liftFun2, Bind.bind, massert, hl.1, hl.2]

theorem native_negative_eta_bridge (f g mask : U64) :
    CommonDivsteps.field.pasta.safegcd.negative_eta_multiplier f g mask =
      Signed62Native.field.pasta.safegcd.negative_eta_multiplier f g mask := by
  rfl

theorem native_body_bridge (f0 g0 : U64) (eta : I64) (u v q r f g : U64) (remaining : U32) :
    CommonDivsteps.field.pasta.safegcd.divsteps_62_var_loop.body f0 g0 eta u v q r f g remaining =
      (do let (eta1, u1, v1, g1, rest, _) ← stripZeroState eta u v g remaining
          if rest = 0#u32 then ok (ControlFlow.done (eta1, u1, v1, q, r))
          else nativeOdd f0 g0 eta1 u1 v1 q r f g1 rest) := by
  unfold CommonDivsteps.field.pasta.safegcd.divsteps_62_var_loop.body
    stripZeroState nativeOdd nativeCancel positiveEtaMultiplier cancellationMask etaLimit
    etaRangeCheck limitRangeCheck
  simp only [lift, bind_ok, Std.bind_assoc, Std.uncurry]
  try rfl

theorem native_loop_unfold (eta : I64) (f0 g0 u v q r f g : U64) (remaining : U32) :
    CommonDivsteps.field.pasta.safegcd.divsteps_62_var_loop eta f0 g0 u v q r f g remaining =
      (do let flow ← CommonDivsteps.field.pasta.safegcd.divsteps_62_var_loop.body
            f0 g0 eta u v q r f g remaining
          match flow with
          | .done out => ok out
          | .cont (eta1, u1, v1, q1, r1, f1, g1, rest) =>
            CommonDivsteps.field.pasta.safegcd.divsteps_62_var_loop eta1 f0 g0
              u1 v1 q1 r1 f1 g1 rest) := by
  unfold CommonDivsteps.field.pasta.safegcd.divsteps_62_var_loop
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done out => rfl
  | cont state => rcases state with ⟨eta1, u1, v1, q1, r1, f1, g1, rest⟩; rfl

#print axioms native_wrapping_neg_eq
#print axioms positive_eta_multiplier_spec
#print axioms cancellation_mask_result_spec
#print axioms eta_range_check_eq
#print axioms limit_range_check_eq
#print axioms native_negative_eta_bridge
#print axioms native_body_bridge
#print axioms native_loop_unfold
end UdonVerify.CommonSigned62
