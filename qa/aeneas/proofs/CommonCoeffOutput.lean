import CommonCoeffCompose

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post CoeffRowMatches
attribute [local irreducible] storeCoeffRow

def CoeffUpdateResult (modulus d e : Signed62)
    (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2) (out : Signed62 × Signed62) : Prop :=
  signed62Normalized out.1 ∧ signed62Normalized out.2 ∧
  (-2 * signed62Value modulus < signed62Value out.1 ∧ signed62Value out.1 < signed62Value modulus) ∧
  (-2 * signed62Value modulus < signed62Value out.2 ∧ signed62Value out.2 < signed62Value modulus) ∧
  Int.ModEq (signed62Value modulus) (signedRadix * signed62Value out.1)
    (t.u.val * signed62Value d + t.v.val * signed62Value e) ∧
  Int.ModEq (signed62Value modulus) (signedRadix * signed62Value out.2)
    (t.q.val * signed62Value d + t.r.val * signed62Value e)


theorem coeff_output_spec {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (d e : Signed62) (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (p : CoeffPrefix) (c1 c2 c3 c4 : CoeffColumn) (dtail etail : I64)
    (hrd : -2 * signed62Value params.modulus < signed62Value d ∧ signed62Value d < signed62Value params.modulus)
    (hre : -2 * signed62Value params.modulus < signed62Value e ∧ signed62Value e < signed62Value params.modulus)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (hp : CoeffPrefixPost params d e t p)
    (hc1 : CoeffColumnPost (p.cd.val + t.u.val * d[1]!.val + t.v.val * e[1]!.val + params.modulus[1]!.val * p.md.val)
      (p.ce.val + t.q.val * d[1]!.val + t.r.val * e[1]!.val + params.modulus[1]!.val * p.me.val) (3 * signedRadix + 5) c1)
    (hc2 : CoeffColumnPost (c1.carryD.val + t.u.val * d[2]!.val + t.v.val * e[2]!.val + 2 * p.md.val)
      (c1.carryE.val + t.q.val * d[2]!.val + t.r.val * e[2]!.val + 2 * p.me.val) (3 * signedRadix + 5) c2)
    (hc3 : CoeffColumnPost (c2.carryD.val + t.u.val * d[3]!.val + t.v.val * e[3]!.val)
      (c2.carryE.val + t.q.val * d[3]!.val + t.r.val * e[3]!.val) (3 * signedRadix + 5) c3)
    (hc4 : CoeffColumnPost (c3.carryD.val + t.u.val * d[4]!.val + t.v.val * e[4]!.val + 64 * p.md.val)
      (c3.carryE.val + t.q.val * d[4]!.val + t.r.val * e[4]!.val + 64 * p.me.val) (388) c4)
    (hdtail : dtail.val = c4.carryD.val) (hetail : etail.val = c4.carryE.val) :
    CoeffUpdateResult params.modulus d e t
      (storeCoeffRow d c1.accD c2.accD c3.accD c4.accD dtail,
       storeCoeffRow e c1.accE c2.accE c3.accE c4.accE etail) := by
  rcases hp with ⟨hmdExact, hmeExact, hmdAbs, hmeAbs, hcarryD0, hcarryE0, hcd0Bound, hce0Bound, hzeroD, hzeroE⟩
  rcases hc1 with ⟨haccD1, haccE1, hcarryD1Val, hcarryE1Val, hcd1Bound, hce1Bound⟩
  rcases hc2 with ⟨haccD2, haccE2, hcarryD2Val, hcarryE2Val, hcd2Bound, hce2Bound⟩
  rcases hc3 with ⟨haccD3, haccE3, hcarryD3Val, hcarryE3Val, hcd3Bound, hce3Bound⟩
  rcases hc4 with ⟨haccD4, haccE4, hcarryD4Val, hcarryE4Val, hcd4Bound, hce4Bound⟩
  let termD := coeffTerm t.u.val t.v.val p.md.val d e params.modulus
  let termE := coeffTerm t.q.val t.r.val p.me.val d e params.modulus
  let dOut := storeCoeffRow d c1.accD c2.accD c3.accD c4.accD dtail
  have hstepD1 : c1.accD.val = fgCarry termD 0 + termD 1 := by
    rw [haccD1, hcarryD0]
    dsimp only [termD, coeffTerm]
    ring
  have hcarryD1 : c1.carryD.val = fgCarry termD 1 := by
    rw [hcarryD1Val, hstepD1]
    rfl
  have hstepD2 : c2.accD.val = fgCarry termD 1 + termD 2 := by
    rw [haccD2, hcarryD1]
    dsimp only [termD, coeffTerm]
    rw [params.sparse.1]
    ring
  have hcarryD2 : c2.carryD.val = fgCarry termD 2 := by
    rw [hcarryD2Val, hstepD2]
    rfl
  have hstepD3 : c3.accD.val = fgCarry termD 2 + termD 3 := by
    rw [haccD3, hcarryD2]
    dsimp only [termD, coeffTerm]
    rw [params.sparse.2.1]
    ring
  have hcarryD3 : c3.carryD.val = fgCarry termD 3 := by
    rw [hcarryD3Val, hstepD3]
    rfl
  have hstepD4 : c4.accD.val = fgCarry termD 3 + termD 4 := by
    rw [haccD4, hcarryD3]
    dsimp only [termD, coeffTerm]
    rw [params.sparse.2.2]
    ring
  have hcarryD4 : c4.carryD.val = fgCarry termD 4 := by
    rw [hcarryD4Val, hstepD4]
    rfl
  have htailD : dtail.val = fgCarry termD 4 := by rw [hdtail, hcarryD4]
  have hmatchesD : CoeffRowMatches t.u.val t.v.val p.md.val d e params.modulus dOut :=
    stored_coeff_row_matches d termD c1.accD c2.accD c3.accD c4.accD dtail
      hstepD1 hstepD2 hstepD3 hstepD4 htailD
  have hnormalD := coeff_matches_normalized t.u.val t.v.val p.md.val d e params.modulus dOut hmatchesD
  have hvalueD := coeff_matches_value t.u.val t.v.val p.md.val d e params.modulus dOut hzeroD hmatchesD
  have hrangeD : -2 * signed62Value params.modulus < signed62Value dOut ∧
      signed62Value dOut < signed62Value params.modulus := by
    apply coeff_matches_range t.u.val t.v.val (t.u.val * d[0]!.val + t.v.val * e[0]!.val) params.mu.val d e params.modulus dOut params.positive huv hrd hre
    · simpa only [← hmdExact] using hzeroD
    · simpa only [← hmdExact] using hmatchesD
  let eOut := storeCoeffRow e c1.accE c2.accE c3.accE c4.accE etail
  have hstepE1 : c1.accE.val = fgCarry termE 0 + termE 1 := by
    rw [haccE1, hcarryE0]
    dsimp only [termE, coeffTerm]
    ring
  have hcarryE1 : c1.carryE.val = fgCarry termE 1 := by
    rw [hcarryE1Val, hstepE1]
    rfl
  have hstepE2 : c2.accE.val = fgCarry termE 1 + termE 2 := by
    rw [haccE2, hcarryE1]
    dsimp only [termE, coeffTerm]
    rw [params.sparse.1]
    ring
  have hcarryE2 : c2.carryE.val = fgCarry termE 2 := by
    rw [hcarryE2Val, hstepE2]
    rfl
  have hstepE3 : c3.accE.val = fgCarry termE 2 + termE 3 := by
    rw [haccE3, hcarryE2]
    dsimp only [termE, coeffTerm]
    rw [params.sparse.2.1]
    ring
  have hcarryE3 : c3.carryE.val = fgCarry termE 3 := by
    rw [hcarryE3Val, hstepE3]
    rfl
  have hstepE4 : c4.accE.val = fgCarry termE 3 + termE 4 := by
    rw [haccE4, hcarryE3]
    dsimp only [termE, coeffTerm]
    rw [params.sparse.2.2]
    ring
  have hcarryE4 : c4.carryE.val = fgCarry termE 4 := by
    rw [hcarryE4Val, hstepE4]
    rfl
  have htailE : etail.val = fgCarry termE 4 := by rw [hetail, hcarryE4]
  have hmatchesE : CoeffRowMatches t.q.val t.r.val p.me.val d e params.modulus eOut :=
    stored_coeff_row_matches e termE c1.accE c2.accE c3.accE c4.accE etail
      hstepE1 hstepE2 hstepE3 hstepE4 htailE
  have hnormalE := coeff_matches_normalized t.q.val t.r.val p.me.val d e params.modulus eOut hmatchesE
  have hvalueE := coeff_matches_value t.q.val t.r.val p.me.val d e params.modulus eOut hzeroE hmatchesE
  have hrangeE : -2 * signed62Value params.modulus < signed62Value eOut ∧
      signed62Value eOut < signed62Value params.modulus := by
    apply coeff_matches_range t.q.val t.r.val (t.q.val * d[0]!.val + t.r.val * e[0]!.val) params.mu.val d e params.modulus eOut params.positive hqr hrd hre
    · simpa only [← hmeExact] using hzeroE
    · simpa only [← hmeExact] using hmatchesE
  refine ⟨hnormalD, hnormalE, hrangeD, hrangeE, ?_, ?_⟩
  · rw [hvalueD]
    simp [Int.ModEq, Int.add_emod, Int.mul_emod]
  · rw [hvalueE]
    simp [Int.ModEq, Int.add_emod, Int.mul_emod]

#print axioms coeff_output_spec
end UdonVerify.CommonSigned62
