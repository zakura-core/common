import LooseRoundMath
import MontgomeryMultiply

open Aeneas Std Result
open udon_kernel_slice.field.pasta
open udon_kernel_slice.field.pasta.montgomery

namespace UdonVerify
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post UScalar.ofNat UScalar.cMax

@[step]
theorem loose_round_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (a0 a1 a2 a3 r0 r1 r2 r3 b : U64)
    (iter iter' : core.slice.iter.Iter U64)
    (hnext : core.slice.iter.IteratorSliceIter.next iter = ok (some b,iter'))
    (ha : digits4 a0 a1 a2 a3 < 2*val4 params.modulus)
    (hold : digits4 r0 r1 r2 r3 < digits4 a0 a1 a2 a3+val4 params.modulus) :
    montgomery_multiply_loose_rust_loop.body inst a0 a1 a2 a3 iter r0 r1 r2 r3
      ⦃ flow => match flow with
      | .done _ => False
      | .cont (next,n0,n1,n2,n3) => next=iter' ∧
        digits4 n0 n1 n2 n3 < digits4 a0 a1 a2 a3+val4 params.modulus ∧
        ∃ q : Nat,q<B ∧ B*digits4 n0 n1 n2 n3 =
          digits4 r0 r1 r2 r3+digits4 a0 a1 a2 a3*b.val+q*val4 params.modulus ⦄ := by
  unfold montgomery_multiply_loose_rust_loop.body
  rw [hnext]
  simp only [bind_ok]
  step -grind with slice_wide_mul_identity as ⟨l0,h0,hp0⟩
  step -grind with slice_wide_mul_identity as ⟨l1,h1,hp1⟩
  step -grind with slice_wide_mul_identity as ⟨l2,h2,hp2⟩
  step -grind with slice_wide_mul_identity as ⟨l3,h3,hp3⟩
  step -grind with slice_carry_add_spec as ⟨s0,c0,hs0⟩
  step -grind with slice_carry_add_spec as ⟨s1,c1,hs1⟩
  step -grind with slice_carry_add_spec as ⟨s2,c2,hs2⟩
  step -grind with slice_carry_add_spec as ⟨s3,c3,hs3⟩
  step -grind as ⟨s4,hs4⟩
  have hs4val : s4.val=c3.toNat := hs4
  step -grind with slice_carry_add_spec as ⟨s11,c4,hs11⟩
  step -grind with slice_carry_add_spec as ⟨s21,c5,hs21⟩
  step -grind with slice_carry_add_spec as ⟨s31,c6,hs31⟩
  step -grind with slice_carry_add_spec as ⟨s41,c7,hs41⟩
  have hproducts : (l0.val+B*l1.val+B^2*l2.val+B^3*l3.val)+
      B*(h0.val+B*h1.val+B^2*h2.val+B^3*h3.val) = digits4 a0 a1 a2 a3*b.val := by
    unfold digits4
    linear_combination hp0+B*hp1+B^2*hp2+B^3*hp3
  have hlow : s0.val+B*s1.val+B^2*s2.val+B^3*s3.val+R*s4.val =
      digits4 r0 r1 r2 r3+(l0.val+B*l1.val+B^2*l2.val+B^3*l3.val) := by
    rw [hs4val]
    simpa only [digits4,Bool.toNat_false,add_zero] using
      flag_chain_identity r0.val r1.val r2.val r3.val l0.val l1.val l2.val l3.val
        0 s0.val s1.val s2.val s3.val c0.toNat c1.toNat c2.toNat c3.toNat
        (by simpa using hs0) hs1 hs2 hs3
  have hhigh : s11.val+B*s21.val+B^2*s31.val+B^3*s41.val+R*c7.toNat =
      s1.val+B*s2.val+B^2*s3.val+B^3*s4.val+
        (h0.val+B*h1.val+B^2*h2.val+B^3*h3.val) := by
    simpa only [add_zero] using
      flag_chain_identity s1.val s2.val s3.val s4.val h0.val h1.val h2.val h3.val
        0 s11.val s21.val s31.val s41.val c4.toNat c5.toNat c6.toNat c7.toNat
        (by simpa using hs11) hs21 hs31 hs41
  have hrow := split_product_row_identity (digits4 a0 a1 a2 a3) b.val
    (digits4 r0 r1 r2 r3) _ _ s0.val s1.val s2.val s3.val s4.val
    s11.val s21.val s31.val s41.val c7.toNat hproducts hlow hhigh
  have hb : b.val < B := by simpa [B] using U64.lt_succ_max b
  have hrowlt := product_row_lt (digits4 a0 a1 a2 a3) (digits4 r0 r1 r2 r3) b.val
    (digits4_lt a0 a1 a2 a3) (digits4_lt r0 r1 r2 r3) hb
  have hc7 : c7=false := by
    cases c7
    · rfl
    · simp only [Bool.toNat_true,mul_one] at hrow
      norm_num only [B,R] at hrow hrowlt
      omega
  step -grind with (massert_spec (¬ c7) (by simp [hc7]))
  rw [params.inv_ok]
  simp only [bind_ok,lift]
  let q := core.num.U64.wrapping_mul s0 params.inv
  have hqval : q.val=(s0.val*params.inv.val)%B := by
    simp [q,U64.size,U64.numBits,B]
  have hq : q.val<B := by simpa [B] using U64.lt_succ_max q
  rw [params.modulus_ok]
  simp only [bind_ok]
  step -grind as ⟨p0,hp0read⟩
  step -grind with slice_wide_mul_identity as ⟨ql0,qh0,hqprod0⟩
  step -grind as ⟨p1,hp1read⟩
  step -grind with slice_wide_mul_identity as ⟨ql1,qh1,hqprod1⟩
  have hmodulus : val4 params.modulus = p0.val+B*p1.val+B^3*2^62 := by
    have hz := params.zero_limb
    have hh := params.high_limb
    simp at hz hh
    simp [val4,hp0read,hp1read,hz,hh]
  have hcancelmod : (s0.val+ql0.val)%B=0 := by
    have hi : (p0.val*params.inv.val+1)%B=0 := by simpa [hp0read] using params.inverse
    calc
      (s0.val+ql0.val)%B = (s0.val+q.val*p0.val)%B := by
        rw [← hqprod0]
        simp [Nat.add_mod,Nat.mul_mod,Nat.add_assoc]
      _ = 0 := by rw [hqval]; exact cancel_low s0.val p0.val params.inv.val hi
  have hcancel := cancelled_low_carry s0 ql0 hcancelmod
  have hap : digits4 a0 a1 a2 a3+val4 params.modulus<R := by
    have ht := params.thrice_lt
    omega
  have hfullBound : digits4 r0 r1 r2 r3+digits4 a0 a1 a2 a3*b.val+
      q.val*val4 params.modulus < B*R := by
    have h := cancelled_row_lt (digits4 a0 a1 a2 a3) (val4 params.modulus)
      (digits4 r0 r1 r2 r3) b.val q.val hold hb hq
    exact _root_.lt_trans h (Nat.mul_lt_mul_of_pos_left hap (by norm_num [B]))
  step -grind with slice_carry_add_spec as ⟨t1,c8,ht1⟩
  step -grind with slice_carry_add_spec as ⟨t2,c9,ht2⟩
  step -grind as ⟨low,hlowShift,hlowBV⟩
  step -grind with slice_carry_add_spec as ⟨t3,c10,ht3⟩
  step -grind with slice_carry_add_spec as ⟨t4,c11,ht4⟩
  have hlowVal : low.val=(q.val*2^62)%B := by
    simpa only [Nat.shiftLeft_eq,U64.size,U64.numBits,UScalarTy.numBits,B] using hlowShift
  have hshift : low.val+B*(q.val/4)=q.val*2^62 := by
    rw [hlowVal]
    exact shift62_split q
  have hlowChain : t1.val+B*t2.val+B^2*t3.val+B^3*t4.val+R*c11.toNat =
      s11.val+B*s21.val+B^2*s31.val+B^3*s41.val+ql1.val+B^2*low.val+
        (s0 != 0#u64).toNat := by
    simpa only [mul_zero,add_zero,Nat.add_assoc] using
      flag_chain_identity s11.val s21.val s31.val s41.val ql1.val 0 low.val 0
        (s0 != 0#u64).toNat t1.val t2.val t3.val t4.val
        c8.toNat c9.toNat c10.toNat c11.toNat ht1
        (by simpa using ht2) ht3 (by simpa using ht4)
  have hrowExact : s0.val+B*s11.val+B^2*s21.val+B^3*s31.val+R*s41.val =
      digits4 r0 r1 r2 r3+digits4 a0 a1 a2 a3*b.val := by
    simpa [hc7] using hrow
  have hpartial := split_modulus_low_identity s0.val s11.val s21.val s31.val s41.val
    p0.val p1.val q.val ql0.val qh0.val ql1.val qh1.val low.val (q.val/4)
    (s0 != 0#u64).toNat t1.val t2.val t3.val t4.val c11.toNat
    hqprod0 hqprod1 hcancel hshift hlowChain
  rw [← hmodulus,hrowExact] at hpartial
  have hc11 : c11=false := by
    cases c11
    · rfl
    · simp only [Bool.toNat_true,mul_one] at hpartial
      norm_num only [B,R] at hpartial hfullBound
      omega
  step -grind with (massert_spec (¬ c11) (by simp [hc11]))
  step -grind with slice_carry_add_spec as ⟨n0,c12,hn0⟩
  step -grind with slice_carry_add_spec as ⟨n1,c13,hn1⟩
  step -grind with slice_carry_add_spec as ⟨n2,c14,hn2⟩
  step -grind as ⟨high,hhighShift,hhighBV⟩
  step -grind with slice_carry_add_spec as ⟨n3,c15,hn3⟩
  have hhighVal : high.val=q.val/4 := by
    simpa only [Nat.shiftRight_eq_div_pow] using hhighShift
  have hhighChain : n0.val+B*n1.val+B^2*n2.val+B^3*n3.val+R*c15.toNat =
      t1.val+B*t2.val+B^2*t3.val+B^3*t4.val+qh0.val+B*qh1.val+B^3*(q.val/4) := by
    rw [← hhighVal]
    simpa only [Bool.toNat_false,mul_zero,add_zero,Nat.add_assoc] using
      flag_chain_identity t1.val t2.val t3.val t4.val qh0.val qh1.val 0 high.val
        0 n0.val n1.val n2.val n3.val c12.toNat c13.toNat c14.toNat c15.toNat
        (by simpa using hn0) hn1 (by simpa using hn2) hn3
  have hcert := split_modulus_row_identity s0.val s11.val s21.val s31.val s41.val
    p0.val p1.val q.val ql0.val qh0.val ql1.val qh1.val low.val (q.val/4)
    (s0 != 0#u64).toNat t1.val t2.val t3.val t4.val c11.toNat
    n0.val n1.val n2.val n3.val c15.toNat
    hqprod0 hqprod1 hcancel hshift hlowChain hhighChain
  rw [← hmodulus,hrowExact,hc11] at hcert
  simp only [Bool.toNat_false,zero_add] at hcert
  have hc15 : c15=false := by
    cases c15
    · rfl
    · simp only [Bool.toNat_true,mul_one] at hcert
      norm_num only [B,R] at hcert hfullBound
      omega
  step -grind with (massert_spec (¬ c15) (by simp [hc15]))
  try simp only [WP.spec_ok]
  have hfinal : B*digits4 n0 n1 n2 n3 = digits4 r0 r1 r2 r3+
      digits4 a0 a1 a2 a3*b.val+q.val*val4 params.modulus := by
    simpa only [digits4,hc15,Bool.toNat_false,mul_zero,add_zero] using hcert
  have hbound := cios_live_bound (digits4 a0 a1 a2 a3) (val4 params.modulus)
    (digits4 r0 r1 r2 r3) b.val q.val (digits4 n0 n1 n2 n3) hold hb hq hfinal
  exact ⟨hbound,q.val,hq,hfinal⟩

#print axioms loose_round_spec
end UdonVerify
