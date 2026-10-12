import CommonCoeffOutput

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post CoeffRowMatches
attribute [local irreducible] storeCoeffRow

@[step]
theorem update_de_62_spec {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (params : InvHelperParameters inst) (d e : Signed62) (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (hnd : signed62Normalized d) (hne : signed62Normalized e)
    (hrd : -2 * signed62Value params.modulus < signed62Value d ∧ signed62Value d < signed62Value params.modulus)
    (hre : -2 * signed62Value params.modulus < signed62Value e ∧ signed62Value e < signed62Value params.modulus)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix) :
    CommonInvHelpers.field.pasta.safegcd.update_de_62 inst d e t ⦃ out =>
      CoeffUpdateResult params.modulus d e t out ⦄ := by
  obtain ⟨hd, hdtop⟩ := inv_coefficient_digit_bounds inst params d hnd hrd
  obtain ⟨he, hetop⟩ := inv_coefficient_digit_bounds inst params e hne hre
  obtain ⟨hm, _⟩ := inv_modulus_digit_bounds inst params
  rw [update_de_flat_bridge, update_de_columns_bridge params]
  unfold updateDEColumns
  rw [fg_result_eq (assert_coeff_range_spec inst params d (CommonInvHelpers.toStr "d") hnd hrd),
    fg_result_eq (assert_coeff_range_spec inst params e (CommonInvHelpers.toStr "e") hne hre)]
  simp only [bind_ok]
  apply WP.spec_bind (coeff_prefix_spec inst params d e t hnd hne hrd hre huv hqr)
  intro p hp
  have hpSaved := hp
  rcases hp with ⟨hmdExact, hmeExact, hmdAbs, hmeAbs, hcarryD0, hcarryE0, hcd0Bound, hce0Bound, hzeroD, hzeroE⟩
  apply WP.spec_bind (coeff_column1_spec t d[1]! e[1]! params.modulus[1]! p.md p.me
    p.cd p.ce huv hqr (hd ⟨1, by decide⟩) (he ⟨1, by decide⟩) (hm ⟨1, by decide⟩) hmdAbs hmeAbs hcd0Bound hce0Bound)
  intro c1 hc1
  have hc1Saved := hc1
  rcases hc1 with ⟨haccD1, haccE1, hcarryD1Val, hcarryE1Val, hcd1Bound, hce1Bound⟩
  apply WP.spec_bind (coeff_column2_spec t d[2]! e[2]! params.modulus[2]! p.md p.me
    c1.carryD c1.carryE huv hqr (hd ⟨2, by decide⟩) (he ⟨2, by decide⟩) (hm ⟨2, by decide⟩) hmdAbs hmeAbs hcd1Bound hce1Bound)
  intro c2 hc2
  have hc2Saved := hc2
  rcases hc2 with ⟨haccD2, haccE2, hcarryD2Val, hcarryE2Val, hcd2Bound, hce2Bound⟩
  apply WP.spec_bind (coeff_column3_spec t d[3]! e[3]! params.modulus[3]! p.md p.me
    c2.carryD c2.carryE huv hqr (hd ⟨3, by decide⟩) (he ⟨3, by decide⟩) (hm ⟨3, by decide⟩) hmdAbs hmeAbs hcd2Bound hce2Bound)
  intro c3 hc3
  have hc3Saved := hc3
  rcases hc3 with ⟨haccD3, haccE3, hcarryD3Val, hcarryE3Val, hcd3Bound, hce3Bound⟩
  apply WP.spec_bind (coeff_column4_spec t d[4]! e[4]! params.modulus[4]! p.md p.me
    c3.carryD c3.carryE huv hqr hdtop hetop (hm ⟨4, by decide⟩) hmdAbs hmeAbs hcd3Bound hce3Bound)
  intro c4 hc4
  have hc4Saved := hc4
  rcases hc4 with ⟨haccD4, haccE4, hcarryD4Val, hcarryE4Val, hcd4Bound, hce4Bound⟩
  apply WP.spec_bind (fg_row_tail_spec c4.carryD (by norm_num only [signedRadix]; omega))
  intro dtail hdtail
  apply WP.spec_bind (fg_row_tail_spec c4.carryE (by norm_num only [signedRadix]; omega))
  intro etail hetail
  let dOut := storeCoeffRow d c1.accD c2.accD c3.accD c4.accD dtail
  let eOut := storeCoeffRow e c1.accE c2.accE c3.accE c4.accE etail
  have hout := coeff_output_spec params d e t p c1 c2 c3 c4 dtail etail hrd hre huv hqr
    hpSaved hc1Saved hc2Saved hc3Saved hc4Saved hdtail hetail
  have houtSaved := hout
  rcases hout with ⟨hnormalD, hnormalE, hrangeD, hrangeE, _, _⟩
  rw [fg_result_eq (assert_coeff_range_spec inst params dOut (CommonInvHelpers.toStr "new d") hnormalD hrangeD),
    fg_result_eq (assert_coeff_range_spec inst params eOut (CommonInvHelpers.toStr "new e") hnormalE hrangeE)]
  simpa only [bind_ok, WP.spec_ok] using houtSaved

#print axioms update_de_62_spec
end UdonVerify.CommonSigned62
