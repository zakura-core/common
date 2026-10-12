import CommonInversionBatch
import CommonInversionUnitCheck
import CommonInversionFinishMath

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def InversionResult {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (out : A4) : Prop :=
  (val4 out : Int) < signed62Value params.helpers.modulus ∧
  Int.ModEq (signed62Value params.helpers.modulus) (x * (val4 out : Int)) (2 ^ 512)

def nativeInversionFinish {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P)
    (iter : core.ops.range.RangeInclusive U32) (f d e : Signed62) (u v : I64) (len : Usize) : Result A4 := do
  let d1 ← CommonInversion.field.pasta.safegcd.update_d_only_62 inst d e u v
  let _ ← nativeUnitCheck iter f len
  let index ← len - 1#usize
  let sign ← Array.index_usize f index
  let d2 ← CommonInversion.field.pasta.safegcd.normalize_62 inst d1 sign
  CommonInversion.field.pasta.safegcd.unpack62 d2

@[step]
theorem native_inversion_finish_spec {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (batches : Nat) (f g d e : Signed62)
    (eta : I64) (len : Usize) (hinv : InversionInvariant params x batches f g d e eta len)
    (fg : NativeFGOutput) (hfg : NativeFGPost params x batches len fg)
    (iter : core.ops.range.RangeInclusive U32)
    (hgcd : Int.gcd (signed62Value params.helpers.modulus) x = 1)
    (hzero : active62Value fg.g len.val = 0) :
    nativeInversionFinish inst iter fg.f d e fg.matrix.u fg.matrix.v len ⦃ out => InversionResult params x out ⦄ := by
  have htraceZero : (inversionTrace (signed62Value params.helpers.modulus) x (batches + 1)).g = 0 := by
    rwa [← hfg.g_value]
  have hunit : active62Value fg.f len.val = 1 ∨ active62Value fg.f len.val = -1 := by
    rw [hfg.f_value]
    exact inversion_terminal_unit (62 * (batches + 1)) _ _ params.odd hgcd htraceZero
  have hodd : (inversionTrace (signed62Value params.helpers.modulus) x batches).f % 2 = 1 :=
    iterate_odd (62 * batches) _ params.odd
  obtain ⟨hrowF, _, _, huv, _⟩ := native_batch_transition
    (inversionTrace (signed62Value params.helpers.modulus) x batches)
    (inversionDivstepMatrix fg.matrix, fg.eta) hfg.batch hodd
  change |fg.matrix.u.val| + |fg.matrix.v.val| ≤ signedRadix at huv
  have hfRow : signedRadix * active62Value fg.f len.val =
      fg.matrix.u.val * active62Value f len.val + fg.matrix.v.val * active62Value g len.val := by
    simpa only [inversionDivstepMatrix, hfg.f_value, hinv.f_value, hinv.g_value, inversion_trace_next] using hrowF.symm
  have hlength := hinv.length
  unfold nativeInversionFinish
  rw [inversion_coeff_terminal_bridge]
  apply WP.spec_bind (update_d_only_62_spec (inversionHelperDict inst) params.helpers d e fg.matrix.u fg.matrix.v
    hinv.d_normalized hinv.e_normalized hinv.d_range hinv.e_range huv)
  intro d1 hd1
  rcases hd1 with ⟨hnD, hrD, hmodD⟩
  have hdBezout := coefficient_row_bezout params.helpers x (signed62Value params.r2)
    (active62Value f len.val) (active62Value g len.val) (signed62Value d) (signed62Value e)
    (active62Value fg.f len.val) (signed62Value d1) fg.matrix.u.val fg.matrix.v.val
    hinv.d_bezout hinv.e_bezout hfRow hmodD
  rw [fg_result_eq (native_unit_check_spec params iter fg.f len hinv.length hfg.f_normalized hfg.f_digits hunit)]
  simp only [bind_ok]
  step +scalarTac -grind with Usize.sub_spec as ⟨index, hindex⟩
  rw [fg_index_eq fg.f index (by have := hinv.length; omega)]
  simp only [bind_ok]
  rw [inversion_normalize_bridge]
  apply WP.spec_bind (normalize_62_spec (inversionHelperDict inst) params.helpers d1 fg.f[index.val]! hnD hrD)
  intro normalized hn
  rcases hn with ⟨hnormal, hrange, hmod⟩
  have hsign : fg.f[index.val]!.val < 0 ↔ active62Value fg.f len.val < 0 := by
    rw [hindex]
    exact (active62_sign_iff fg.f len.val hinv.length hfg.f_normalized).symm
  have hweighted := inversion_normalized_bezout (signed62Value params.helpers.modulus) x (signed62Value params.r2)
    (active62Value fg.f len.val) (signed62Value d1) (signed62Value normalized)
    (fg.f[index.val]!.val < 0) hunit hsign hdBezout hmod
  have htop : 0 ≤ normalized[4]!.val ∧ normalized[4]!.val < 128 :=
    signed62_255_top_bound normalized hnormal ⟨hrange.1, by have := params.helpers.bound; omega⟩
  rw [inversion_unpack_bridge]
  apply WP.spec_mono (unpack62_spec normalized hnormal htop)
  intro out hout
  unfold InversionResult
  rw [hout]
  exact ⟨hrange.2, hweighted.trans params.r2_congruence⟩

#print axioms native_inversion_finish_spec
end UdonVerify.CommonSigned62
