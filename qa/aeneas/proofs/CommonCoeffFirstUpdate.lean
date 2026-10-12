import CommonCoeffFirstCompose

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post CoeffRowMatches
attribute [local irreducible] storeCoeffRow

@[step]
theorem update_de_62_first_spec {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (params : InvHelperParameters inst) (e : Signed62) (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (hne : signed62Normalized e) (heNonnegative : 0 ≤ signed62Value e)
    (hre : -2 * signed62Value params.modulus < signed62Value e ∧ signed62Value e < signed62Value params.modulus)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix) :
    CommonInvHelpers.field.pasta.safegcd.update_de_62_first inst e t ⦃ out =>
      CoeffUpdateResult params.modulus zero62 e t out ⦄ := by
  have hrd : -2 * signed62Value params.modulus < signed62Value zero62 ∧
      signed62Value zero62 < signed62Value params.modulus := by
    rw [zero62_value]
    have := params.positive
    constructor <;> omega
  obtain ⟨he, hetop⟩ := inv_coefficient_digit_bounds inst params e hne hre
  obtain ⟨hm, _⟩ := inv_modulus_digit_bounds inst params
  rw [update_de_first_columns_bridge params]
  unfold updateDEFirstColumns
  rw [fg_result_eq (first_coeff_input_check_spec params e hne heNonnegative hre),
    fg_result_eq (assert_coeff_range_spec inst params e (CommonInvHelpers.toStr "e") hne hre)]
  simp only [bind_ok]
  apply WP.spec_bind (first_coeff_prefix_spec inst params e t hne heNonnegative hre huv hqr)
  intro p hp
  have hpSaved := hp
  rcases hp with ⟨hmdExact, hmeExact, hmdAbs, hmeAbs, hcarryD0, hcarryE0, hcd0Bound, hce0Bound, hzeroD, hzeroE⟩
  apply WP.spec_bind (first_coeff_column1_spec t e[1]! params.modulus[1]! p.md p.me
    p.cd p.ce huv hqr (he ⟨1, by decide⟩) (hm ⟨1, by decide⟩) hmdAbs hmeAbs hcd0Bound hce0Bound)
  intro c1 hc1
  have hc1Saved := hc1
  have hc1General : CoeffColumnPost
      (p.cd.val + t.u.val * zero62[1]!.val + t.v.val * e[1]!.val + params.modulus[1]!.val * p.md.val)
      (p.ce.val + t.q.val * zero62[1]!.val + t.r.val * e[1]!.val + params.modulus[1]!.val * p.me.val)
      (3 * signedRadix + 5) c1 := by
    simpa only [zero62_digit 1 (by decide), show (0#i64).val = 0 from by decide,
      mul_zero, add_zero] using hc1Saved
  rcases hc1 with ⟨haccD1, haccE1, hcarryD1Val, hcarryE1Val, hcd1Bound, hce1Bound⟩
  apply WP.spec_bind (first_coeff_column2_spec t e[2]! params.modulus[2]! p.md p.me
    c1.carryD c1.carryE huv hqr (he ⟨2, by decide⟩) (hm ⟨2, by decide⟩) hmdAbs hmeAbs hcd1Bound hce1Bound)
  intro c2 hc2
  have hc2Saved := hc2
  have hc2General : CoeffColumnPost
      (c1.carryD.val + t.u.val * zero62[2]!.val + t.v.val * e[2]!.val + 2 * p.md.val)
      (c1.carryE.val + t.q.val * zero62[2]!.val + t.r.val * e[2]!.val + 2 * p.me.val)
      (3 * signedRadix + 5) c2 := by
    simpa only [zero62_digit 2 (by decide), show (0#i64).val = 0 from by decide,
      mul_zero, add_zero] using hc2Saved
  rcases hc2 with ⟨haccD2, haccE2, hcarryD2Val, hcarryE2Val, hcd2Bound, hce2Bound⟩
  apply WP.spec_bind (first_coeff_column3_spec t e[3]! params.modulus[3]! p.md p.me
    c2.carryD c2.carryE huv hqr (he ⟨3, by decide⟩) (hm ⟨3, by decide⟩) hmdAbs hmeAbs hcd2Bound hce2Bound)
  intro c3 hc3
  have hc3Saved := hc3
  have hc3General : CoeffColumnPost
      (c2.carryD.val + t.u.val * zero62[3]!.val + t.v.val * e[3]!.val)
      (c2.carryE.val + t.q.val * zero62[3]!.val + t.r.val * e[3]!.val)
      (3 * signedRadix + 5) c3 := by
    simpa only [zero62_digit 3 (by decide), show (0#i64).val = 0 from by decide,
      mul_zero, add_zero] using hc3Saved
  rcases hc3 with ⟨haccD3, haccE3, hcarryD3Val, hcarryE3Val, hcd3Bound, hce3Bound⟩
  apply WP.spec_bind (first_coeff_column4_spec t e[4]! params.modulus[4]! p.md p.me
    c3.carryD c3.carryE huv hqr hetop (hm ⟨4, by decide⟩) hmdAbs hmeAbs hcd3Bound hce3Bound)
  intro c4 hc4
  have hc4Saved := hc4
  have hc4General : CoeffColumnPost
      (c3.carryD.val + t.u.val * zero62[4]!.val + t.v.val * e[4]!.val + 64 * p.md.val)
      (c3.carryE.val + t.q.val * zero62[4]!.val + t.r.val * e[4]!.val + 64 * p.me.val)
      (388) c4 := by
    simpa only [zero62_digit 4 (by decide), show (0#i64).val = 0 from by decide,
      mul_zero, add_zero] using hc4Saved
  rcases hc4 with ⟨haccD4, haccE4, hcarryD4Val, hcarryE4Val, hcd4Bound, hce4Bound⟩
  apply WP.spec_bind (fg_row_tail_spec c4.carryD (by norm_num only [signedRadix]; omega))
  intro dtail hdtail
  apply WP.spec_bind (fg_row_tail_spec c4.carryE (by norm_num only [signedRadix]; omega))
  intro etail hetail
  let dOut := storeCoeffRow zero62 c1.accD c2.accD c3.accD c4.accD dtail
  let eOut := storeCoeffRow zero62 c1.accE c2.accE c3.accE c4.accE etail
  have hout := coeff_output_spec params zero62 e t p c1 c2 c3 c4 dtail etail hrd hre huv hqr
    hpSaved hc1General hc2General hc3General hc4General hdtail hetail
  rw [← store_coeff_initial_irrelevant zero62 e c1.accE c2.accE c3.accE c4.accE etail] at hout
  have houtSaved := hout
  rcases hout with ⟨hnormalD, hnormalE, hrangeD, hrangeE, _, _⟩
  rw [fg_result_eq (assert_coeff_range_spec inst params dOut (CommonInvHelpers.toStr "new d") hnormalD hrangeD),
    fg_result_eq (assert_coeff_range_spec inst params eOut (CommonInvHelpers.toStr "new e") hnormalE hrangeE)]
  simpa only [bind_ok, WP.spec_ok] using houtSaved

#print axioms update_de_62_first_spec
end UdonVerify.CommonSigned62
