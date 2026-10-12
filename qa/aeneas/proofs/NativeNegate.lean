import NativeSubtract

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem negate_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (value : Element M S)
    (ha : val4 value.limbs < 2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.neg inst value ⦃ out =>
      val4 out.limbs < 2*val4 params.modulus ∧
      Nat.ModEq (val4 params.modulus) (val4 out.limbs+val4 value.limbs) 0 ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.neg
  have htwice : inst.sealedParametersInst.TWICE_MODULUS = ok params.twice := params.twice_ok
  rw [htwice]
  simp only [bind_ok]
  rw [subtract_limbs_eq]
  step -grind with (slice_subtract_limbs_spec params.twice value.limbs) as ⟨limbs,borrow,hborrow,hsub⟩
  rw [params.twice_val] at hsub
  have hlimbs := val4_lt limbs
  have hborrow_zero : borrow=0#u64 := by
    have hval : borrow.val=0 := by
      norm_num only [R,B] at hsub hlimbs
      omega
    scalar_tac
  have hsum : val4 limbs+val4 value.limbs=2*val4 params.modulus := by
    simpa [hborrow_zero,add_comm] using hsub
  step -grind
  step -grind with Array.index_usize_spec as ⟨a0,ha0⟩
  step -grind with Array.index_usize_spec as ⟨a1,ha1⟩
  step -grind with UScalar.or_spec as ⟨n01,hn01,hn01b⟩
  step -grind with Array.index_usize_spec as ⟨a2,ha2⟩
  step -grind with UScalar.or_spec as ⟨n012,hn012,hn012b⟩
  step -grind with Array.index_usize_spec as ⟨a3,ha3⟩
  step -grind with UScalar.or_spec as ⟨nonzero,hn, hnb⟩
  have hn01eq : n01=a0 ||| a1 := UScalar.eq_of_val_eq hn01
  have hn012eq : n012=(a0 ||| a1) ||| a2 := by
    rw [hn01eq] at hn012
    exact UScalar.eq_of_val_eq hn012
  have hneq : nonzero=((a0 ||| a1) ||| a2) ||| a3 := by
    rw [hn012eq] at hn
    exact UScalar.eq_of_val_eq hn
  have hzero : nonzero=0#u64 ↔ val4 value.limbs=0 := by
    rw [hneq,or4_zero_iff,val4_zero_iff]
    simp [ha0,ha1,ha2,ha3]
  simp only [lift,bind_ok]
  let bit : U64 := core.convert.num.FromU64Bool.from (nonzero != 0#u64)
  have hbitval : bit.val = if nonzero=0#u64 then 0 else 1 := by
    unfold bit
    by_cases hz : nonzero=0#u64 <;> simp [core.convert.num.FromU64Bool.from,hz]
  have hbitbound : bit.val ≤ 1 := by rw [hbitval]; split <;> omega
  step -grind with (wrapping_neg_bit_spec bit hbitbound) as ⟨mask,hmask⟩
  step -grind with Array.index_usize_spec as ⟨l0,hl0⟩
  step -grind with Array.index_usize_spec as ⟨l1,hl1⟩
  step -grind with Array.index_usize_spec as ⟨l2,hl2⟩
  step -grind with Array.index_usize_spec as ⟨l3,hl3⟩
  let r0 := l0 &&& mask
  let r1 := l1 &&& mask
  let r2 := l2 &&& mask
  let r3 := l3 &&& mask
  have hmasked : val4 (Array.make 4#usize [r0,r1,r2,r3]) =
      if nonzero=0#u64 then 0 else val4 limbs := by
    rw [hbitval] at hmask
    by_cases hz : nonzero=0#u64
    · simp only [hz,↓reduceIte] at hmask
      simp_all [val4,and_zero,r0,r1,r2,r3]
    · simp only [hz,↓reduceIte] at hmask
      subst mask
      simp [hz,val4,r0,r1,r2,r3,and_full,hl0,hl1,hl2,hl3]
  have hbound : val4 (Array.make 4#usize [r0,r1,r2,r3]) < 2*val4 params.modulus := by
    rw [hmasked]
    split
    · have hp := params.positive
      omega
    · have hx : val4 value.limbs ≠ 0 := by
        intro hx
        exact ‹nonzero ≠ 0#u64› (hzero.mpr hx)
      omega
  step -grind with (from_montgomery_loose_spec inst params (Array.make 4#usize [r0,r1,r2,r3]) hbound)
    as ⟨out,hout⟩
  refine ⟨by simpa only [hout] using hbound,?_⟩
  rw [hout,hmasked]
  by_cases hz : nonzero=0#u64
  · simp [hz,hzero.mp hz,Nat.ModEq]
  · simp only [hz,↓reduceIte]
    rw [hsum]
    simp [Nat.ModEq]

@[step]
theorem fp_negate_spec (value : Element Base Loose) (ha : val4 value.limbs < 2*fpPrime) :
    NativeField.fp_neg value ⦃ out => val4 out.limbs < 2*fpPrime ∧
      decode fpPrime fpRadixInverse out.limbs =
        (fpPrime-decode fpPrime fpRadixInverse value.limbs)%fpPrime ⦄ := by
  unfold NativeField.fp_neg
  step -grind with (negate_spec fpNativeInst fpNativeParameters value ha) as ⟨out,hbound,hmod⟩
  refine ⟨hbound,?_⟩
  simpa only [decode,zero_mul,Nat.zero_mod,zero_add] using
    decoded_difference fpPrime fpRadixInverse 0 (val4 value.limbs) (val4 out.limbs) fpParameters.positive hmod

@[step]
theorem fq_negate_spec (value : Element Scalar Loose) (ha : val4 value.limbs < 2*fqPrime) :
    NativeField.fq_neg value ⦃ out => val4 out.limbs < 2*fqPrime ∧
      decode fqPrime fqRadixInverse out.limbs =
        (fqPrime-decode fqPrime fqRadixInverse value.limbs)%fqPrime ⦄ := by
  unfold NativeField.fq_neg
  step -grind with (negate_spec fqNativeInst fqNativeParameters value ha) as ⟨out,hbound,hmod⟩
  refine ⟨hbound,?_⟩
  simpa only [decode,zero_mul,Nat.zero_mod,zero_add] using
    decoded_difference fqPrime fqRadixInverse 0 (val4 value.limbs) (val4 out.limbs) fqParameters.positive hmod

#print axioms fp_negate_spec
#print axioms fq_negate_spec

end UdonVerify.Native
