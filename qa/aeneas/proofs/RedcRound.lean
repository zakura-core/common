import MontgomeryCommon
import Mathlib.Tactic.LinearCombination

open Aeneas Std Result
open udon_kernel_slice.field.pasta
open udon_kernel_slice.field.pasta.montgomery

namespace UdonVerify
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem redc_round_identity (r0 r1 r2 r3 p0 p1 k c c1 c2 c3 low high s0 s1 s2 s3 : Nat)
    (hc : B*c = r0+k*p0)
    (h0 : s0+B*c1 = r1+k*p1+c)
    (h1 : s1+B*c2 = r2+c1)
    (h2 : s2+B*c3 = r3+low+c2)
    (h3 : s3 = high+c3)
    (hshift : low+B*high = k*2^62) :
    B*(s0+B*s1+B^2*s2+B^3*s3) =
      r0+B*r1+B^2*r2+B^3*r3 + k*(p0+B*p1+B^3*2^62) := by
  linear_combination hc + B*h0 + B^2*h1 + B^3*h2 + B^4*h3 + B^3*hshift

@[step]
theorem redc_round_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst)
    (iter iter' : core.ops.range.Range I32) (index : I32)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepI32 iter = ok (some index, iter'))
    (r0 r1 r2 r3 : U64) :
    montgomery_reduce_unreduced_loop.body inst iter r0 r1 r2 r3 ⦃ flow =>
      match flow with
      | .done _ => False
      | .cont (next, s0, s1, s2, s3) =>
        next = iter' ∧ ∃ k : Nat, k < B ∧
          B * digits4 s0 s1 s2 s3 = digits4 r0 r1 r2 r3 + k * val4 params.modulus ⦄ := by
  let k := core.num.U64.wrapping_mul r0 params.inv
  have hk : k.val = (r0.val * params.inv.val) % B := by
    simp [k, U64.size, U64.numBits, B]
  unfold montgomery_reduce_unreduced_loop.body
  rw [hnext]
  simp only [bind_ok]
  rw [params.inv_ok, params.modulus_ok]
  simp only [bind_ok, lift]
  step as ⟨p0, hp0⟩
  step with slice_mac_identity as ⟨cancelled, carry, hfirst⟩
  have hfirst' : cancelled.val + B*carry.val = r0.val + k.val*p0.val := by
    simpa only [Nat.add_zero, Nat.zero_add, Nat.add_comm] using hfirst
  have hcancel : cancelled = 0#u64 := by
    have hi : (p0.val * params.inv.val + 1) % B = 0 := by
      simpa [hp0] using params.inverse
    have hc := cancel_low r0.val p0.val params.inv.val hi
    have hmod := congrArg (fun n : Nat => n % B) hfirst'
    rw [hk, hc] at hmod
    have hcb : cancelled.val < B := by simpa [B] using U64.lt_succ_max cancelled
    have hz : cancelled.val = 0 := by
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hcb] using hmod
    clear * - hz
    scalar_tac
  step
  step as ⟨p1, hp1⟩
  step with slice_mac_identity as ⟨s0, carry1, hs0⟩
  step with slice_adc_identity as ⟨s1, carry2, hs1⟩
  step as ⟨low, hlow, hlowbv⟩
  step with slice_adc_identity as ⟨s2, carry3, hs2⟩
  step as ⟨high, hhigh, hhighbv⟩
  have hcarry3 : carry3.val ≤ 2 := by
    clear * - hs2
    have h1 := U64.le_max r3
    have h2 := U64.le_max low
    have h3 := U64.le_max carry2
    norm_num [B] at hs2 ⊢
    omega
  have hhighlt : high.val < 2^62 := by
    clear * - hhigh
    have hb := U64.lt_succ_max (core.num.U64.wrapping_mul r0 params.inv)
    simp only [Nat.shiftRight_eq_div_pow] at hhigh
    norm_num only at hhigh ⊢
    omega
  have hsafe : high.val + carry3.val ≤ U64.max := by
    clear * - hcarry3 hhighlt
    norm_num [U64.max, U64.numBits] at hhighlt ⊢
    omega
  step -grind with (U64.add_spec hsafe) as ⟨s3, hs3⟩
  try simp only [WP.spec_ok]
  refine ⟨k.val, by simpa [B] using U64.lt_succ_max k, ?_⟩
  have hlow' : low.val = (k.val * 2^62) % B := by
    simpa only [Nat.shiftLeft_eq, U64.size, U64.numBits, UScalarTy.numBits, B] using hlow
  have hhigh' : high.val = k.val / 4 := by
    simpa only [Nat.shiftRight_eq_div_pow] using hhigh
  have hsplit : low.val + B*high.val = k.val*2^62 := by
    rw [hlow', hhigh']
    exact shift62_split k
  have hc : B*carry.val = r0.val + k.val*p0.val := by
    simpa [hcancel] using hfirst'
  have hz := params.zero_limb
  have hh := params.high_limb
  have hmath := redc_round_identity r0.val r1.val r2.val r3.val p0.val p1.val
    k.val carry.val carry1.val carry2.val carry3.val low.val high.val
    s0.val s1.val s2.val s3.val hc
    (by simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs0)
    (by simpa only [Nat.add_zero] using hs1) hs2 hs3 hsplit
  simp at hz hh
  simpa [digits4, val4, hp0, hp1, hz, hh] using hmath

#print axioms redc_round_spec

end UdonVerify
