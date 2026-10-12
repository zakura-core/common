import RedcRound

open Aeneas Std Result
open udon_kernel_slice.field.pasta
open udon_kernel_slice.field.pasta.montgomery

namespace UdonVerify
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem redc_four_identity (n0 n1 n2 n3 n4 k0 k1 k2 k3 p : Nat)
    (h0 : B*n1 = n0+k0*p) (h1 : B*n2 = n1+k1*p)
    (h2 : B*n3 = n2+k2*p) (h3 : B*n4 = n3+k3*p) :
    R*n4 = n0+(k0+B*k1+B^2*k2+B^3*k3)*p := by
  unfold R
  linear_combination h0+B*h1+B^2*h2+B^3*h3

theorem add_four_identity (a0 a1 a2 a3 b0 b1 b2 b3 o0 o1 o2 o3 c0 c1 c2 c3 : Nat)
    (h0 : o0+B*c0 = a0+b0) (h1 : o1+B*c1 = a1+b1+c0)
    (h2 : o2+B*c2 = a2+b2+c1) (h3 : o3+B*c3 = a3+b3+c2) :
    o0+B*o1+B^2*o2+B^3*o3+R*c3 =
      a0+B*a1+B^2*a2+B^3*a3 + (b0+B*b1+B^2*b2+B^3*b3) := by
  unfold R
  linear_combination h0+B*h1+B^2*h2+B^3*h3

theorem redc_loop_unfold {M : Type} (inst : PrimeModulus M)
    (iter : core.ops.range.Range I32) (r0 r1 r2 r3 : U64) :
    montgomery_reduce_unreduced_loop inst iter r0 r1 r2 r3 = (do
      let flow ← montgomery_reduce_unreduced_loop.body inst iter r0 r1 r2 r3
      match flow with
      | .done r => ok r
      | .cont (it, a, b, c, d) => montgomery_reduce_unreduced_loop inst it a b c d) := by
  unfold montgomery_reduce_unreduced_loop
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done r => rfl
  | cont r => rcases r with ⟨it, a, b, c, d⟩; rfl

@[step]
theorem montgomery_reduce_unreduced_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (limbs : A8)
    (hbound : val8 limbs < val4 params.modulus * R + val4 params.modulus ^ 2) :
    montgomery_reduce_unreduced inst limbs ⦃ out =>
      val4 out < 3 * val4 params.modulus ∧
      ∃ m : Nat, m < R ∧ R * val4 out = val8 limbs + m * val4 params.modulus ⦄ := by
  unfold montgomery_reduce_unreduced
  step +scalarTac -grind as ⟨r0, hr0⟩
  step +scalarTac -grind as ⟨r1, hr1⟩
  step +scalarTac -grind as ⟨r2, hr2⟩
  step +scalarTac -grind as ⟨r3, hr3⟩
  step +scalarTac -grind as ⟨t4, ht4⟩
  step +scalarTac -grind as ⟨t5, ht5⟩
  step +scalarTac -grind as ⟨t6, ht6⟩
  step +scalarTac -grind as ⟨t7, ht7⟩
  rw [redc_loop_unfold]
  step with (redc_round_spec inst params (range32 0#i32) (range32 1#i32) 0#i32 next_i32_0) as ⟨flow0, hflow0⟩
  cases flow0 with
  | done out => exact False.elim hflow0
  | cont state =>
    rcases state with ⟨iter0, s00, s01, s02, s03⟩
    rcases hflow0 with ⟨hiter0, k0, hk0, heq0⟩
    subst iter0
    simp only [bind_ok]
    rw [redc_loop_unfold]
    step with (redc_round_spec inst params (range32 1#i32) (range32 2#i32) 1#i32 next_i32_1) as ⟨flow1, hflow1⟩
    cases flow1 with
    | done out => exact False.elim hflow1
    | cont state =>
      rcases state with ⟨iter1, s10, s11, s12, s13⟩
      rcases hflow1 with ⟨hiter1, k1, hk1, heq1⟩
      subst iter1
      simp only [bind_ok]
      rw [redc_loop_unfold]
      step with (redc_round_spec inst params (range32 2#i32) (range32 3#i32) 2#i32 next_i32_2) as ⟨flow2, hflow2⟩
      cases flow2 with
      | done out => exact False.elim hflow2
      | cont state =>
        rcases state with ⟨iter2, s20, s21, s22, s23⟩
        rcases hflow2 with ⟨hiter2, k2, hk2, heq2⟩
        subst iter2
        simp only [bind_ok]
        rw [redc_loop_unfold]
        step with (redc_round_spec inst params (range32 3#i32) (range32 4#i32) 3#i32 next_i32_3) as ⟨flow3, hflow3⟩
        cases flow3 with
        | done out => exact False.elim hflow3
        | cont state =>
          rcases state with ⟨iter3, s30, s31, s32, s33⟩
          rcases hflow3 with ⟨hiter3, k3, hk3, heq3⟩
          subst iter3
          simp only [bind_ok]
          rw [redc_loop_unfold]
          unfold montgomery_reduce_unreduced_loop.body
          rw [next_i32_4]
          simp only [bind_ok]
          step with slice_adc_identity as ⟨lo0, carry0, hlo0⟩
          step with slice_adc_identity as ⟨lo1, carry1, hlo1⟩
          step with slice_adc_identity as ⟨lo2, carry2, hlo2⟩
          step with slice_adc_identity as ⟨lo3, carry3, hlo3⟩
          let m := k0 + B*k1 + B^2*k2 + B^3*k3
          have hm : m < R := by
            dsimp [m]
            norm_num [B, R] at hk0 hk1 hk2 hk3 ⊢
            omega
          have htotal :
              R * (digits4 lo0 lo1 lo2 lo3 + R * carry3.val) =
                val8 limbs + m * val4 params.modulus := by
            have hredc := redc_four_identity _ _ _ _ _ _ _ _ _ _ heq0 heq1 heq2 heq3
            have hadd := add_four_identity _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (by simpa only [Nat.add_zero] using hlo0) hlo1 hlo2 hlo3
            change digits4 lo0 lo1 lo2 lo3 + R*carry3.val =
              digits4 s30 s31 s32 s33 + digits4 t4 t5 t6 t7 at hadd
            rw [hadd, Nat.mul_add, hredc]
            dsimp [m]
            simp [digits4, val8, hr0, hr1, hr2, hr3, ht4, ht5, ht6, ht7]
            unfold R
            ring
          have hp0 := params.positive
          have hp3 := params.thrice_lt
          have hpR : val4 params.modulus < R := by omega
          have hpsq : val4 params.modulus * val4 params.modulus < val4 params.modulus * R :=
            Nat.mul_lt_mul_of_pos_left hpR hp0
          have hmp : m * val4 params.modulus < R * val4 params.modulus :=
            Nat.mul_lt_mul_of_pos_right hm hp0
          have hsum : val8 limbs + m * val4 params.modulus < 3 * val4 params.modulus * R := by
            nlinarith only [hbound, hmp, hpsq]
          have h3R : 3 * val4 params.modulus * R < R^2 := by
            have h := Nat.mul_lt_mul_of_pos_right hp3 (show 0 < R by norm_num [R, B])
            nlinarith only [h]
          have hcarry : carry3 = 0#u64 := by
            have hcval : carry3.val = 0 := by
              norm_num [R, B] at htotal hsum h3R
              omega
            scalar_tac
          step
          try simp only [WP.spec_ok]
          have htotal' : R * digits4 lo0 lo1 lo2 lo3 = val8 limbs + m * val4 params.modulus := by
            simpa [hcarry] using htotal
          have hout : digits4 lo0 lo1 lo2 lo3 < 3 * val4 params.modulus := by
            norm_num [R, B] at htotal' hsum
            omega
          refine ⟨?_, m, hm, ?_⟩
          · simpa [val4, digits4] using hout
          · simpa [val4, digits4] using htotal'

#print axioms montgomery_reduce_unreduced_spec

end UdonVerify
