import NativeProductOffsets
import NativeProductHigh
import RedcProofs

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- The common suffix of both extracted signed-product branches. -/
def productRestoreFinish {M : Type} (inst : Modulus M) (wide : A8)
    (borrow : U64) (reduced double : Bool) : Result (Element M Loose) := do
  let mask ← lift (core.num.U64.wrapping_sub 0#u64 borrow)
  let offset ← productOffset inst reduced double
  let (restored, carry) ←
    productRestoreWords wide mask offset
  massert (carry = borrow)
  let folded ← if reduced then ok restored else
    NativeField.zakura_udon.field.pasta.products.fold_high inst restored true
  let limbs ← NativeField.zakura_udon.field.pasta.montgomery.montgomery_reduce_unreduced inst folded
  NativeField.zakura_udon.field.pasta.PastaField.from_montgomery inst looseInst limbs

/-- Borrow reconstruction and bind reassociation preserve the extracted suffix. -/
theorem product_restore_finish_eq {M : Type} (inst : Modulus M) (wide : A8)
    (borrow : U64) (reduced double : Bool) :
    productRestoreFinish inst wide borrow reduced double = (do
      let offset ← productOffset inst reduced double
      let (s,index_back) ← core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U64))
        wide {start:=4#usize}
      let (carry,z,back) ←
        NativeField.zakura_udon.field.pasta.products.PastaField.product_difference_loop2
          ⟨⟨s,0⟩,⟨offset.to_slice,0⟩⟩ (fun z=>z)
          (core.num.U64.wrapping_sub 0#u64 borrow) 0#u64
      massert (carry=borrow)
      let folded ← if reduced then ok (index_back (back z).fst.slice) else
        NativeField.zakura_udon.field.pasta.products.fold_high inst
          (index_back (back z).fst.slice) true
      let limbs ← NativeField.zakura_udon.field.pasta.montgomery.montgomery_reduce_unreduced inst folded
      NativeField.zakura_udon.field.pasta.PastaField.from_montgomery inst looseInst limbs) := by
  unfold productRestoreFinish productRestoreWords
  simp only [lift, bind_ok, Std.bind_assoc, Std.uncurry,
    core.slice.Slice.iter_mut, mutableZipCtor,
    NativeField.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter,
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter]
  with_unfolding_all rfl

/-- Restoration cancels the wrapping borrow and leaves a valid wide REDC input. -/
@[step]
theorem product_restore_finish_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (wide : A8) (borrow : U64)
    (reduced double : Bool) (left right : Nat) (hborrow : borrow.val ≤ 1)
    (hsub : val8 wide + right = left + R ^ 2 * borrow.val)
    (hleft : left < R * (productOffsetScale reduced double * val4 params.modulus))
    (hright : right < R * (productOffsetScale reduced double * val4 params.modulus)) :
    productRestoreFinish inst wide borrow reduced double
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (R * val4 out.limbs + right) left ⦄ := by
  unfold productRestoreFinish
  simp only [lift, bind_ok]
  step -grind with (product_offset_spec inst params reduced double) as ⟨offset, hoffset⟩
  step -grind with (product_restore_loop_spec wide
    (core.num.U64.wrapping_sub 0#u64 borrow) offset)
    as ⟨restored, carry, hcarry, hadd⟩
  rw [product_masked_offset offset borrow hborrow] at hadd
  obtain ⟨hcarryValue, hrestore, hrestoredBound⟩ :=
    product_restoration_math left right (val8 wide) (val8 restored) (val4 offset)
      borrow.val carry.val hborrow hcarry (val8_lt wide) (val8_lt restored)
      (by simpa only [hoffset] using hleft)
      (by simpa only [hoffset] using hright) (val4_lt offset) hsub
      (by simpa only [mul_assoc] using hadd)
  have hcarryEq : carry = borrow := by scalar_tac
  step -grind
  have hrestoredMod : Nat.ModEq (val4 params.modulus) (val8 restored + right) left := by
    rw [hrestore, hoffset]
    simp [Nat.ModEq, Nat.add_mod, Nat.mul_mod]
  have hfold : (if reduced then ok restored else
      NativeField.zakura_udon.field.pasta.products.fold_high inst restored true)
      ⦃ out => val8 out < val4 params.modulus * R ∧
        Nat.ModEq (val4 params.modulus) (val8 out) (val8 restored) ⦄ := by
    cases reduced with
    | true =>
      rw [if_pos (show (true : Bool) = true from rfl)]
      simp only [WP.spec_ok]
      refine ⟨?_, Nat.ModEq.refl _⟩
      simpa [hoffset, productOffsetScale, mul_comm] using hrestoredBound
    | false =>
      rw [if_neg (by decide : ¬ ((false : Bool) = true))]
      have hscale : productOffsetScale false double < 4 := by cases double <;> decide
      have hpR : 0 < val4 params.modulus * R :=
        Nat.mul_pos params.positive (by norm_num [B, R])
      have hscaleLimit : R * (productOffsetScale false double * val4 params.modulus) <
          R * (4 * val4 params.modulus) := by
        convert Nat.mul_lt_mul_of_pos_right hscale hpR using 1 <;> ring
      have hhigh : val4 (productHigh restored) < 4 * val4 params.modulus := by
        apply Nat.lt_of_mul_lt_mul_left (a := R)
        calc
          R * val4 (productHigh restored) ≤ val8 restored := by
            rw [product_halves_value]
            omega
          _ < R * (productOffsetScale false double * val4 params.modulus) := by
            simpa only [hoffset] using hrestoredBound
          _ < R * (4 * val4 params.modulus) := hscaleLimit
      step -grind with (product_fold_high_spec inst params restored true (by simpa using hhigh))
        as ⟨folded, hbound, hmod⟩
      exact ⟨hbound, hmod⟩
  step -grind with hfold as ⟨folded, hfoldedBound, hfoldedMod⟩
  rw [redc_unreduced_eq]
  have hredc : val8 folded < val4 params.modulus * R + val4 params.modulus ^ 2 :=
    _root_.lt_of_lt_of_le hfoldedBound (Nat.le_add_right _ _)
  step -grind with (montgomery_reduce_unreduced_spec (kernelInst inst) params folded hredc)
    as ⟨limbs, hthree, m, hm, hcert⟩
  have hmp : m * val4 params.modulus < R * val4 params.modulus :=
    Nat.mul_lt_mul_of_pos_right hm params.positive
  have hloose : val4 limbs < 2 * val4 params.modulus := by
    have hmul : R * val4 limbs < R * (2 * val4 params.modulus) := by
      nlinarith only [hcert, hfoldedBound, hmp]
    exact Nat.lt_of_mul_lt_mul_left hmul
  step -grind with (from_montgomery_loose_spec inst params limbs hloose) as ⟨out, hout⟩
  rw [hout]
  refine ⟨hloose, ?_⟩
  exact ((certificate_congruence _ _ _ _ hcert).trans hfoldedMod).add_right right |>.trans hrestoredMod

#print axioms product_restore_finish_spec
#print axioms product_restore_finish_eq

end UdonVerify.Native
