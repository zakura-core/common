import MontgomeryInner
import RedcRound

open Aeneas Std Result
open udon_kernel_slice.field.pasta
open udon_kernel_slice.field.pasta.montgomery

namespace UdonVerify
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post UScalar.ofNat

theorem cios_redc_identity (a0 a1 a2 a3 upper p0 p1 k c c1 c2 c3 low high
    s0 s1 s2 s3 overflow : Nat)
    (hc : B*c = a0+k*p0)
    (h0 : s0+B*c1 = a1+k*p1+c)
    (h1 : s1+B*c2 = a2+c1)
    (h2 : s2+B*c3 = a3+low+c2)
    (h3 : s3+B*overflow = upper+high+c3)
    (hshift : low+B*high = k*2^62) :
    B*(s0+B*s1+B^2*s2+B^3*s3)+B*R*overflow =
      a0+B*a1+B^2*a2+B^3*a3+R*upper + k*(p0+B*p1+B^3*2^62) := by
  unfold R
  linear_combination hc+B*h0+B^2*h1+B^3*h2+B^4*h3+B^3*hshift

@[step]
theorem cios_round_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (lhs : A4) (acc : A5)
    (iter iter' : core.slice.iter.Iter U64) (rhs : U64)
    (hnext : core.slice.iter.IteratorSliceIter.next iter = ok (some rhs, iter')) :
    montgomery_multiply_loop0.body inst params.modulus lhs iter acc ⦃ flow =>
      match flow with
      | .done _ => False
      | .cont (next, out) => next = iter' ∧ ∃ k : Nat, k < B ∧
        B*val5 out = val5 acc + val4 lhs*rhs.val + k*val4 params.modulus ⦄ := by
  unfold montgomery_multiply_loop0.body
  rw [hnext]
  simp only [bind_ok]
  step -grind with multiply_inner_spec as ⟨acc1, carry, htop, hproduct⟩
  step +scalarTac -grind as ⟨oldtop, holdtop⟩
  step -grind with slice_adc_identity as ⟨upper, product_overflow, hupper⟩
  step +scalarTac -grind as ⟨acc2, hacc2⟩
  subst acc2
  step +scalarTac -grind as ⟨a0, ha0⟩
  rw [params.inv_ok]
  simp only [bind_ok, lift]
  let k := core.num.U64.wrapping_mul a0 params.inv
  have hk : k.val = (a0.val*params.inv.val)%B := by simp [k, U64.size, U64.numBits, B]
  step +scalarTac -grind as ⟨p0, hp0⟩
  step -grind with slice_mac_identity as ⟨cancelled, c, hc0⟩
  have hc : cancelled.val+B*c.val = a0.val+k.val*p0.val := by
    simpa only [Nat.add_zero, Nat.zero_add, Nat.add_comm] using hc0
  have hcancel : cancelled = 0#u64 := by
    have hi : (p0.val*params.inv.val+1)%B = 0 := by simpa [hp0] using params.inverse
    have hcmod := cancel_low a0.val p0.val params.inv.val hi
    have hmod := congrArg (fun n : Nat => n%B) hc
    rw [hk, hcmod] at hmod
    have hcb : cancelled.val < B := by simpa [B] using U64.lt_succ_max cancelled
    have hz : cancelled.val = 0 := by
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hcb] using hmod
    clear * - hz
    scalar_tac
  step
  step +scalarTac -grind as ⟨a1, ha1⟩
  step +scalarTac -grind as ⟨p1, hp1⟩
  step -grind with slice_mac_identity as ⟨s0, c1, hs0⟩
  step +scalarTac -grind as ⟨a2, ha2⟩
  step -grind with slice_adc_identity as ⟨s1, c2, hs1⟩
  step +scalarTac -grind as ⟨a3, ha3⟩
  step as ⟨low, hlow, hlowbv⟩
  step -grind with slice_adc_identity as ⟨s2, c3, hs2⟩
  step +scalarTac -grind as ⟨upper2, hupper2⟩
  step as ⟨high, hhigh, hhighbv⟩
  step -grind with slice_adc_identity as ⟨s3, reduction_overflow, hs3⟩
  have hpov : product_overflow.val ≤ 2 := by
    clear * - hupper
    have hb0 := U64.le_max oldtop
    have hb1 := U64.le_max carry
    norm_num [B] at hupper ⊢
    omega
  have hrov : reduction_overflow.val ≤ 2 := by
    clear * - hs3
    have hb0 := U64.le_max upper2
    have hb1 := U64.le_max high
    have hb2 := U64.le_max c3
    norm_num [B] at hs3 ⊢
    omega
  have hsafe : product_overflow.val + reduction_overflow.val ≤ U64.max := by
    clear * - hpov hrov
    norm_num [U64.max, U64.numBits]
    omega
  step -grind with (U64.add_spec hsafe) as ⟨top, htopval⟩
  try simp only [WP.spec_ok]
  refine ⟨k.val, by simpa [B] using U64.lt_succ_max k, ?_⟩
  have hlow' : low.val = (k.val*2^62)%B := by
    simpa only [Nat.shiftLeft_eq, U64.size, U64.numBits, UScalarTy.numBits, B] using hlow
  have hhigh' : high.val = k.val/4 := by simpa only [Nat.shiftRight_eq_div_pow] using hhigh
  have hsplit : low.val+B*high.val=k.val*2^62 := by rw [hlow',hhigh']; exact shift62_split k
  have hcancelled : B*c.val=a0.val+k.val*p0.val := by simpa [hcancel] using hc
  have hmath := cios_redc_identity a0.val a1.val a2.val a3.val upper2.val p0.val p1.val
    k.val c.val c1.val c2.val c3.val low.val high.val s0.val s1.val s2.val s3.val
    reduction_overflow.val hcancelled
    (by simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs0)
    (by simpa only [Nat.add_zero] using hs1) hs2 hs3 hsplit
  have hz := params.zero_limb
  have hh := params.high_limb
  simp at hz hh
  simp [ha0,ha1,ha2,ha3,hupper2,hp0,hp1] at hmath
  have hup : upper.val+B*product_overflow.val=acc1[4]!.val+carry.val := by
    simpa [holdtop] using hupper
  simp [val5, val4, htopval, hz, hh] at hproduct ⊢
  simp at hup
  unfold R at *
  linear_combination hmath + B^4*hup + hproduct

#print axioms cios_round_spec

end UdonVerify
