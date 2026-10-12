import CommonCoeffStart
import CommonCoeffValue
import CommonCoeffRows

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

structure CoeffPrefix where
  md : I64
  me : I64
  cd : I128
  ce : I128

def coeffPrefix {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (d e : Signed62) (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2) : Result CoeffPrefix := do
  let md ← coeffSignStart t.u t.v d[4]! e[4]!
  let me ← coeffSignStart t.q t.r d[4]! e[4]!
  let cd ← fgRowTerm t.u t.v d[0]! e[0]!
  let ce ← fgRowTerm t.q t.r d[0]! e[0]!
  let mu ← inst.MU
  let md1 := coeffCorrectWord mu cd md
  let me1 := coeffCorrectWord mu ce me
  let modulus ← inst.MODULUS_62
  let modD0 ← coeffModTerm modulus[0]! md1
  let cd0 ← cd + modD0
  let modE0 ← coeffModTerm modulus[0]! me1
  let ce0 ← ce + modE0
  massert (IScalar.hcast .U64 cd0 &&& 4611686018427387903#u64 = 0#u64)
  massert (IScalar.hcast .U64 ce0 &&& 4611686018427387903#u64 = 0#u64)
  let cdCarry0 ← cd0 >>> 62#i32
  let ceCarry0 ← ce0 >>> 62#i32
  ok ⟨md1, me1, cdCarry0, ceCarry0⟩

def CoeffPrefixPost {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (d e : Signed62)
    (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2) (out : CoeffPrefix) : Prop :=
  out.md.val = coeffCorrection t.u.val t.v.val (signed62Value d) (signed62Value e)
    (t.u.val * d[0]!.val + t.v.val * e[0]!.val) params.mu.val ∧
  out.me.val = coeffCorrection t.q.val t.r.val (signed62Value d) (signed62Value e)
    (t.q.val * d[0]!.val + t.r.val * e[0]!.val) params.mu.val ∧
  |out.md.val| ≤ 2 * signedRadix ∧ |out.me.val| ≤ 2 * signedRadix ∧
  out.cd.val = fgCarry (coeffTerm t.u.val t.v.val out.md.val d e params.modulus) 0 ∧
  out.ce.val = fgCarry (coeffTerm t.q.val t.r.val out.me.val d e params.modulus) 0 ∧
  |out.cd.val| ≤ 3 * signedRadix + 5 ∧ |out.ce.val| ≤ 3 * signedRadix + 5 ∧
  coeffTerm t.u.val t.v.val out.md.val d e params.modulus 0 % signedRadix = 0 ∧
  coeffTerm t.q.val t.r.val out.me.val d e params.modulus 0 % signedRadix = 0

@[step]
theorem coeff_prefix_spec {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (params : InvHelperParameters inst) (d e : Signed62) (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (hnd : signed62Normalized d) (hne : signed62Normalized e)
    (hrd : -2 * signed62Value params.modulus < signed62Value d ∧ signed62Value d < signed62Value params.modulus)
    (hre : -2 * signed62Value params.modulus < signed62Value e ∧ signed62Value e < signed62Value params.modulus)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix) :
    coeffPrefix inst d e t ⦃ out => CoeffPrefixPost params d e t out ⦄ := by
  obtain ⟨hd, hdtop⟩ := inv_coefficient_digit_bounds inst params d hnd hrd
  obtain ⟨he, hetop⟩ := inv_coefficient_digit_bounds inst params e hne hre
  obtain ⟨hm, _⟩ := inv_modulus_digit_bounds inst params
  have hb : (256 : Int) ≤ signedRadix := by norm_num [signedRadix]
  unfold coeffPrefix
  step -grind with (coeff_sign_start_spec t.u t.v d[4]! e[4]! huv) as ⟨md, hmd, hmdBound⟩
  step -grind with (coeff_sign_start_spec t.q t.r d[4]! e[4]! hqr) as ⟨me, hme, hmeBound⟩
  step -grind with (fg_row_term_spec t.u t.v d[0]! e[0]! huv (hd ⟨0, by decide⟩) (he ⟨0, by decide⟩))
    as ⟨cd, hcd, hcdBound⟩
  step -grind with (fg_row_term_spec t.q t.r d[0]! e[0]! hqr (hd ⟨0, by decide⟩) (he ⟨0, by decide⟩))
    as ⟨ce, hce, hceBound⟩
  rw [params.mu_eq]
  simp only [bind_ok]
  generalize hmdDef : coeffCorrectWord params.mu cd md = md1
  generalize hmeDef : coeffCorrectWord params.mu ce me = me1
  obtain ⟨hmd1, hmdLo, hmdHi⟩ := coeff_correct_word_value params.mu cd md hmdBound
  obtain ⟨hme1, hmeLo, hmeHi⟩ := coeff_correct_word_value params.mu ce me hmeBound
  rw [hmdDef] at hmd1 hmdLo hmdHi
  rw [hmeDef] at hme1 hmeLo hmeHi
  have hmdFull : md.val = (if signed62Value d < 0 then t.u.val else 0) +
      (if signed62Value e < 0 then t.v.val else 0) := by
    simpa only [← signed62_sign_iff d hnd, ← signed62_sign_iff e hne] using hmd
  have hmeFull : me.val = (if signed62Value d < 0 then t.q.val else 0) +
      (if signed62Value e < 0 then t.r.val else 0) := by
    simpa only [← signed62_sign_iff d hnd, ← signed62_sign_iff e hne] using hme
  have hmdExact : md1.val = coeffCorrection t.u.val t.v.val (signed62Value d) (signed62Value e)
      (t.u.val * d[0]!.val + t.v.val * e[0]!.val) params.mu.val := by
    rw [hmd1, hmdFull, hcd]
    rfl
  have hmeExact : me1.val = coeffCorrection t.q.val t.r.val (signed62Value d) (signed62Value e)
      (t.q.val * d[0]!.val + t.r.val * e[0]!.val) params.mu.val := by
    rw [hme1, hmeFull, hce]
    rfl
  have hmdAbs := coeff_correction_abs md1 ⟨hmdLo, hmdHi⟩
  have hmeAbs := coeff_correction_abs me1 ⟨hmeLo, hmeHi⟩
  rw [params.modulus_eq]
  simp only [bind_ok]
  step -grind with (coeff_mod_term_spec params.modulus[0]! md1 (hm ⟨0, by decide⟩) hmdAbs)
    as ⟨modD0, hmodD0, hmodD0Bound⟩
  step -grind with (coeff_add_mod_spec cd modD0 (by nlinarith only [hcdBound, hb]) hmodD0Bound) as ⟨cd0, hcd0, hcd0Bound⟩
  step -grind with (coeff_mod_term_spec params.modulus[0]! me1 (hm ⟨0, by decide⟩) hmeAbs)
    as ⟨modE0, hmodE0, hmodE0Bound⟩
  step -grind with (coeff_add_mod_spec ce modE0 (by nlinarith only [hceBound, hb]) hmodE0Bound) as ⟨ce0, hce0, hce0Bound⟩
  let termD := coeffTerm t.u.val t.v.val md1.val d e params.modulus
  let termE := coeffTerm t.q.val t.r.val me1.val d e params.modulus
  have haccD0 : cd0.val = termD 0 := by rw [hcd0, hmodD0, hcd]; rfl
  have haccE0 : ce0.val = termE 0 := by rw [hce0, hmodE0, hce]; rfl
  have hzeroD : termD 0 % signedRadix = 0 := by
    dsimp only [termD, coeffTerm]
    rw [hmdExact]
    exact coeff_correction_cancels _ _ _ _ _ _ _ params.inverse
  have hzeroE : termE 0 % signedRadix = 0 := by
    dsimp only [termE, coeffTerm]
    rw [hmeExact]
    exact coeff_correction_cancels _ _ _ _ _ _ _ params.inverse
  have hbitD := fg_row_low_zero cd0 (by rw [haccD0]; exact hzeroD)
  have hbitE := fg_row_low_zero ce0 (by rw [haccE0]; exact hzeroE)
  simp only [hbitD, hbitE, massert, bind_ok, ite_true]
  step -grind with (coeff_shift_spec cd0 hcd0Bound) as ⟨cdCarry0, hcdCarry0, hcdCarry0Bound⟩
  step -grind with (coeff_shift_spec ce0 hce0Bound) as ⟨ceCarry0, hceCarry0, hceCarry0Bound⟩
  try simp only [WP.spec_ok]
  have hcarryD0 : cdCarry0.val = fgCarry termD 0 := by rw [hcdCarry0, haccD0]; rfl
  have hcarryE0 : ceCarry0.val = fgCarry termE 0 := by rw [hceCarry0, haccE0]; rfl
  exact ⟨hmdExact, hmeExact, hmdAbs, hmeAbs, hcarryD0, hcarryE0,
    hcdCarry0Bound, hceCarry0Bound, hzeroD, hzeroE⟩

#print axioms coeff_prefix_spec
end UdonVerify.CommonSigned62
