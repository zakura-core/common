import NativeSmallRepair
import NativePredicates

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev H : Nat := R/4

theorem small_modulus_shape {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) :
    val4 params.modulus = H+(params.modulus[0]!.val+B*params.modulus[1]!.val) ∧
    16*(params.modulus[0]!.val+B*params.modulus[1]!.val) < H := by
  constructor
  · simp only [val4,params.zero_limb,params.high_limb,mul_zero,add_zero]
    norm_num only [H,R,B]
    omega
  · norm_num only [H,R,B]
    scalar_tac

theorem small_repair (p c t raw borrow out carry : Nat)
    (hp : 0<p) (ht : t<p) (hc : c<p) (hraw : raw<R) (hout : out<R)
    (hb : borrow≤1) (hk : carry≤1) (hsub : raw+c=t+R*borrow)
    (hsum : out+R*carry=raw+p*borrow) :
    out<p ∧ out+c=t+p*borrow := by
  by_cases hz : borrow=0
  · simp only [hz,mul_zero,add_zero] at hsub hsum ⊢
    have hkzero : carry=0 := by
      norm_num only [R,B] at hraw hsum
      omega
    rw [hkzero,mul_zero,add_zero] at hsum
    omega
  · have hone : borrow=1 := by omega
    simp only [hone,mul_one] at hsub hsum ⊢
    have hkone : carry=1 := by
      norm_num only [R,B] at hout hraw hsub hsum
      omega
    rw [hkone,mul_one] at hsum
    norm_num only [R,B] at hraw hsub hsum
    omega

@[step]
theorem small_finish_spec {M : Type} (K : U64) (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (limbs product : A4) (carry : U64)
    (hk0 : 0<K.val) (hk8 : K.val≤8) (ha : val4 limbs<2*val4 params.modulus)
    (hproduct : val4 product+R*carry.val=K.val*val4 limbs) :
    smallFinish inst product carry ⦃ out =>
      val4 out.limbs<val4 params.modulus ∧
      Nat.ModEq (val4 params.modulus) (val4 out.limbs) (K.val*val4 limbs) ⦄ := by
  unfold smallFinish
  have hcarry : carry.val<8 := by
    have hlimbs := val4_lt limbs
    have hmul := Nat.mul_le_mul_right (val4 limbs) hk8
    have hbound := Nat.mul_lt_mul_of_pos_left hlimbs (by decide : 0<8)
    norm_num only [R,B] at hproduct hmul hbound
    omega
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨highCarry,hshift,hshiftb⟩
  step -grind with Array.index_usize_spec as ⟨high,hhigh⟩
  step -grind with U64.ShiftRight_IScalar_spec as ⟨highBits,hbits,hbitsb⟩
  step -grind with UScalar.or_spec as ⟨q,hq,hqb⟩
  have hshiftval : highCarry.val=4*carry.val := by
    simp only [Nat.shiftLeft_eq] at hshift
    norm_num only [U64.size,U64.numBits,UScalarTy.numBits] at hshift
    rw [Nat.mod_eq_of_lt (by omega)] at hshift
    omega
  have hbitsval : highBits.val=high.val/(2^62) := by
    simpa only [Nat.shiftRight_eq_div_pow] using hbits
  have hbitbound : high.val/(2^62)<4 := by scalar_tac
  have hqval : q.val=4*carry.val+high.val/(2^62) := by
    simp only [UScalar.val_or] at hq
    rw [hshiftval,hbitsval] at hq
    exact hq.trans (Nat.two_pow_add_eq_or_of_lt (i := 2) hbitbound carry.val).symm
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨power,hpower,hpowerb⟩
  have hpowerval : power.val=2^62 := by
    norm_num [Nat.shiftLeft_eq,U64.size,U64.numBits,UScalarTy.numBits] at hpower ⊢
    exact hpower
  step -grind with UScalar.sub_spec as ⟨mask,hmask⟩
  have hmaskval : mask.val=2^62-1 := by scalar_tac
  step -grind with UScalar.and_spec as ⟨top,htop,htopb⟩
  have htopval : top.val=high.val%(2^62) := by
    simp only [UScalar.val_and] at htop
    rw [hmaskval] at htop
    exact htop.trans (Nat.and_two_pow_sub_one_eq_mod high.val 62)
  step -grind with Array.update_spec as ⟨folded,hfolded⟩
  have hfoldvalue : val4 folded = product[0]!.val+B*product[1]!.val+
      B^2*product[2]!.val+B^3*(high.val%(2^62)) := by
    rw [hfolded]
    simp [val4,htopval,hhigh]
  have hsplit : val4 folded+H*q.val=K.val*val4 limbs := by
    have hd := Nat.mod_add_div high.val (2^62)
    rw [hfoldvalue,hqval]
    simp [val4,hhigh] at hproduct
    simp [hhigh] at hd ⊢
    norm_num [H,R,B,val4] at hproduct hd ⊢
    linear_combination hproduct + 2^192*hd
  let offset := params.modulus[0]!.val+B*params.modulus[1]!.val
  have hshape : val4 params.modulus=H+offset := (small_modulus_shape inst params).1
  have hoffset : 16*offset<H := (small_modulus_shape inst params).2
  have hx : K.val*val4 limbs<17*H := by
    have h1 := Nat.mul_lt_mul_of_pos_left ha hk0
    have h2 := Nat.mul_le_mul_right (2*val4 params.modulus) hk8
    rw [hshape] at h1 h2
    nlinarith only [h1,h2,hoffset]
  have hqbound : q.val≤16 := by
    norm_num only [H,R,B] at hsplit hx
    omega
  have hqc : q.val*offset<val4 params.modulus := by
    have h := Nat.mul_le_mul_right offset hqbound
    omega
  have hfoldbound : val4 folded<H := by
    rw [hfolded]
    simp [val4,htopval,hhigh]
    norm_num only [H,R,B]
    have htopbound := Nat.mod_lt high.val (by norm_num : 0<2^62)
    scalar_tac
  have hmodulus : inst.MODULUS=ok params.modulus := params.modulus_ok
  rw [hmodulus]
  simp only [bind_ok]
  step -grind with Array.index_usize_spec as ⟨p0,hp0⟩
  rw [mac_eq]
  step -grind with slice_mac_identity as ⟨c0,carry0,h0⟩
  step -grind with Array.index_usize_spec as ⟨p1,hp1⟩
  rw [mac_eq]
  step -grind with slice_mac_identity as ⟨c1,c2,h1⟩
  have hcoffset : c0.val+B*c1.val+B^2*c2.val=q.val*offset := by
    simp_all [offset]
    linear_combination h0+B*h1
  step -grind with Array.index_usize_spec as ⟨a0,ha0⟩
  rw [sbb_eq]
  step -grind with (slice_sbb_identity a0 c0 0#u64 (by decide)) as ⟨r0,b0,hb0,hs0⟩
  step -grind with Array.index_usize_spec as ⟨a1,ha1⟩
  rw [sbb_eq]
  step -grind with (slice_sbb_identity a1 c1 b0 hb0) as ⟨r1,b1,hb1,hs1⟩
  step -grind with Array.index_usize_spec as ⟨a2,ha2⟩
  rw [sbb_eq]
  step -grind with (slice_sbb_identity a2 c2 b1 hb1) as ⟨r2,b2,hb2,hs2⟩
  step -grind with Array.index_usize_spec as ⟨a3,ha3⟩
  rw [sbb_eq]
  step -grind with (slice_sbb_identity a3 0#u64 b2 hb2) as ⟨r3,borrow,hborrow,hs3⟩
  let raw := Array.make 4#usize [r0,r1,r2,r3]
  have hsub : val4 raw+q.val*offset=val4 folded+R*borrow.val := by
    rw [←hcoffset]
    simp only [raw,val4]
    simp [ha0,ha1,ha2,ha3] at *
    unfold R
    linear_combination hs0+B*hs1+B^2*hs2+B^3*hs3
  have hpost (repaired : A4) (carry : Nat) (hk : carry≤1)
      (hsum : val4 repaired+R*carry=val4 raw+val4 params.modulus*borrow.val) :
      val4 repaired<val4 params.modulus ∧
      Nat.ModEq (val4 params.modulus) (val4 repaired) (K.val*val4 limbs) := by
    have hr := small_repair (val4 params.modulus) (q.val*offset) (val4 folded) (val4 raw)
      borrow.val (val4 repaired) carry params.positive (by omega) hqc (val4_lt raw)
      (val4_lt repaired) hborrow hk hsub hsum
    refine ⟨hr.1,?_⟩
    have heq : val4 repaired+q.val*val4 params.modulus=
        K.val*val4 limbs+val4 params.modulus*borrow.val := by
      have hrepair := hr.2
      rw [hshape] at hrepair
      rw [hshape]
      linear_combination hrepair+hsplit
    have hcongr : Nat.ModEq (val4 params.modulus)
        (val4 repaired+q.val*val4 params.modulus)
        (K.val*val4 limbs+val4 params.modulus*borrow.val) := congrArg (fun n : Nat => n%val4 params.modulus) heq
    simpa [Nat.ModEq,Nat.add_mod] using hcongr
  split
  · have hbval : borrow.val=1 := by scalar_tac
    simp [lift, Array.to_slice_mut, Array.to_slice, core.slice.Slice.iter_mut,
      mutableZipCtor, NativeField.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter,
      _root_.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter]
    have hrepair := small_repair_loop_spec raw params.modulus
    simp only [Array.to_slice, raw, Array.make_val] at hrepair
    step -grind with hrepair as ⟨z,back,addCarry,haddCarry,hadd⟩
    let repaired := Array.from_slice raw (back z).fst.slice
    have hr := hpost repaired addCarry haddCarry (by simpa only [hbval,mul_one] using hadd)
    step -grind with (from_montgomery_loose_spec inst params repaired (by omega)) as ⟨out,hout⟩
    exact ⟨by simpa only [hout] using hr.1,by simpa only [hout] using hr.2⟩
  · have hbval : borrow.val=0 := by scalar_tac
    have hr := hpost raw 0 (by decide) (by simp [hbval])
    step -grind with (from_montgomery_loose_spec inst params raw (by omega)) as ⟨out,hout⟩
    exact ⟨by simpa only [hout] using hr.1,by simpa only [hout] using hr.2⟩


#print axioms small_finish_spec
end UdonVerify.Native
