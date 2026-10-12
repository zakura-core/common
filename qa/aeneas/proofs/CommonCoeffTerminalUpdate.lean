import CommonCoeffTerminalCompose

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post CoeffRowMatches
attribute [local irreducible] storeCoeffRow

def CoeffTerminalResult (modulus d e : Signed62) (u v : I64) (out : Signed62) : Prop :=
  signed62Normalized out ∧
  (-2 * signed62Value modulus < signed62Value out ∧ signed62Value out < signed62Value modulus) ∧
  Int.ModEq (signed62Value modulus) (signedRadix * signed62Value out)
    (u.val * signed62Value d + v.val * signed62Value e)

@[step]
theorem update_d_only_62_spec {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (params : InvHelperParameters inst) (d e : Signed62) (u v : I64)
    (hnd : signed62Normalized d) (hne : signed62Normalized e)
    (hrd : -2 * signed62Value params.modulus < signed62Value d ∧ signed62Value d < signed62Value params.modulus)
    (hre : -2 * signed62Value params.modulus < signed62Value e ∧ signed62Value e < signed62Value params.modulus)
    (huv : |u.val| + |v.val| ≤ signedRadix) :
    CommonInvHelpers.field.pasta.safegcd.update_d_only_62 inst d e u v ⦃ out =>
      CoeffTerminalResult params.modulus d e u v out ⦄ := by
  obtain ⟨hd, hdtop⟩ := inv_coefficient_digit_bounds inst params d hnd hrd
  obtain ⟨he, hetop⟩ := inv_coefficient_digit_bounds inst params e hne hre
  obtain ⟨hm, _⟩ := inv_modulus_digit_bounds inst params
  rw [update_d_only_columns_bridge params]
  unfold updateDOnlyColumns
  rw [fg_result_eq (assert_coeff_range_spec inst params d (CommonInvHelpers.toStr "d") hnd hrd),
    fg_result_eq (assert_coeff_range_spec inst params e (CommonInvHelpers.toStr "e") hne hre)]
  simp only [bind_ok]
  apply WP.spec_bind (terminal_coeff_prefix_spec inst params d e u v hnd hne hrd hre huv)
  intro p hp
  rcases hp with ⟨hpmd, hpcarry, hpSaved⟩
  have hp := hpSaved
  rcases hp with ⟨hmdExact, hmeExact, hmdAbs, hmeAbs, hcarryD0, hcarryE0, hcd0Bound, hce0Bound, hzeroD, hzeroE⟩
  apply WP.spec_bind (terminal_coeff_column1_spec u v d[1]! e[1]! params.modulus[1]! p.md
    p.cd huv (hd ⟨1, by decide⟩) (he ⟨1, by decide⟩) (hm ⟨1, by decide⟩) hmdAbs hcd0Bound)
  intro c1 hc1
  rcases hc1 with ⟨hc1acc, hc1carry, hc1Post⟩
  have hc1Saved : CoeffColumnPost
      (p.cd.val + (duplicateCoeffRow u v).u.val * d[1]!.val + (duplicateCoeffRow u v).v.val * e[1]!.val + params.modulus[1]!.val * p.md.val)
      (p.ce.val + (duplicateCoeffRow u v).q.val * d[1]!.val + (duplicateCoeffRow u v).r.val * e[1]!.val + params.modulus[1]!.val * p.me.val)
      (3 * signedRadix + 5) c1 := by
    simp only [← hpmd, ← hpcarry]
    exact hc1Post
  have hc1 := hc1Post
  rcases hc1 with ⟨haccD1, haccE1, hcarryD1Val, hcarryE1Val, hcd1Bound, hce1Bound⟩
  apply WP.spec_bind (terminal_coeff_column2_spec u v d[2]! e[2]! params.modulus[2]! p.md
    c1.carryD huv (hd ⟨2, by decide⟩) (he ⟨2, by decide⟩) (hm ⟨2, by decide⟩) hmdAbs hcd1Bound)
  intro c2 hc2
  rcases hc2 with ⟨hc2acc, hc2carry, hc2Post⟩
  have hc2Saved : CoeffColumnPost
      (c1.carryD.val + (duplicateCoeffRow u v).u.val * d[2]!.val + (duplicateCoeffRow u v).v.val * e[2]!.val + 2 * p.md.val)
      (c1.carryE.val + (duplicateCoeffRow u v).q.val * d[2]!.val + (duplicateCoeffRow u v).r.val * e[2]!.val + 2 * p.me.val)
      (3 * signedRadix + 5) c2 := by
    simp only [← hpmd, ← hc1carry]
    exact hc2Post
  have hc2 := hc2Post
  rcases hc2 with ⟨haccD2, haccE2, hcarryD2Val, hcarryE2Val, hcd2Bound, hce2Bound⟩
  apply WP.spec_bind (terminal_coeff_column3_spec u v d[3]! e[3]! params.modulus[3]! p.md
    c2.carryD huv (hd ⟨3, by decide⟩) (he ⟨3, by decide⟩) (hm ⟨3, by decide⟩) hmdAbs hcd2Bound)
  intro c3 hc3
  rcases hc3 with ⟨hc3acc, hc3carry, hc3Post⟩
  have hc3Saved : CoeffColumnPost
      (c2.carryD.val + (duplicateCoeffRow u v).u.val * d[3]!.val + (duplicateCoeffRow u v).v.val * e[3]!.val)
      (c2.carryE.val + (duplicateCoeffRow u v).q.val * d[3]!.val + (duplicateCoeffRow u v).r.val * e[3]!.val)
      (3 * signedRadix + 5) c3 := by
    simp only [← hpmd, ← hc2carry]
    exact hc3Post
  have hc3 := hc3Post
  rcases hc3 with ⟨haccD3, haccE3, hcarryD3Val, hcarryE3Val, hcd3Bound, hce3Bound⟩
  apply WP.spec_bind (terminal_coeff_column4_spec u v d[4]! e[4]! params.modulus[4]! p.md
    c3.carryD huv hdtop hetop (hm ⟨4, by decide⟩) hmdAbs hcd3Bound)
  intro c4 hc4
  rcases hc4 with ⟨hc4acc, hc4carry, hc4Post⟩
  have hc4Saved : CoeffColumnPost
      (c3.carryD.val + (duplicateCoeffRow u v).u.val * d[4]!.val + (duplicateCoeffRow u v).v.val * e[4]!.val + 64 * p.md.val)
      (c3.carryE.val + (duplicateCoeffRow u v).q.val * d[4]!.val + (duplicateCoeffRow u v).r.val * e[4]!.val + 64 * p.me.val)
      (388) c4 := by
    simp only [← hpmd, ← hc3carry]
    exact hc4Post
  have hc4 := hc4Post
  rcases hc4 with ⟨haccD4, haccE4, hcarryD4Val, hcarryE4Val, hcd4Bound, hce4Bound⟩
  apply WP.spec_bind (fg_row_tail_spec c4.carryD (by norm_num only [signedRadix]; omega))
  intro tail htail
  let out := storeCoeffRow d c1.accD c2.accD c3.accD c4.accD tail
  have htailE : tail.val = c4.carryE.val := by rw [← hc4carry]; exact htail
  have hout := coeff_output_spec params d e (duplicateCoeffRow u v) p c1 c2 c3 c4 tail tail hrd hre
    huv huv hpSaved hc1Saved hc2Saved hc3Saved hc4Saved htail htailE
  have hresult : CoeffTerminalResult params.modulus d e u v out :=
    ⟨hout.1, hout.2.2.1, hout.2.2.2.2.1⟩
  rw [fg_result_eq (assert_coeff_range_spec inst params out (CommonInvHelpers.toStr "new d")
    hresult.1 hresult.2.1)]
  simpa only [bind_ok, WP.spec_ok] using hresult

#print axioms update_d_only_62_spec
end UdonVerify.CommonSigned62
