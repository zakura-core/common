import NativeProductRestoration
import NativeProductDouble
import NativeProductSubtractLoop
import WideMultiply

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- The extracted routine computes either signed product difference for every operand state. -/
@[step]
theorem product_difference_spec {M S T U V : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst))
    (si : ProductState S) (ti : ProductState T) (ui : ProductState U) (vi : ProductState V)
    (ss : ProductRepresentation si) (ts : ProductRepresentation ti)
    (us : ProductRepresentation ui) (vs : ProductRepresentation vi)
    (double : Bool) (a : Element M S) (b : Element M T)
    (c : Element M U) (d : Element M V)
    (ha : val4 a.limbs < productRepresentationBound (val4 params.modulus) ss)
    (hb : val4 b.limbs < productRepresentationBound (val4 params.modulus) ts)
    (hc : val4 c.limbs < productRepresentationBound (val4 params.modulus) us)
    (hd : val4 d.limbs < productRepresentationBound (val4 params.modulus) vs) :
    NativeField.zakura_udon.field.pasta.products.PastaField.product_difference
      double inst si ti ui vi a b c d
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus)
          (R * val4 out.limbs + productScale double * (val4 c.limbs * val4 d.limbs))
          (val4 a.limbs * val4 b.limbs) ⦄ := by
  have hinput := product_difference_input_bounds inst params
    (val4 a.limbs) (val4 b.limbs) (val4 c.limbs) (val4 d.limbs)
    ss.reduced ts.reduced us.reduced vs.reduced double ha hb hc hd
  have hcd := product_pair_value_bounds (val4 params.modulus)
    (val4 c.limbs) (val4 d.limbs) params.positive us.reduced vs.reduced hc hd
  have hflags := product_reduced_flags si ti ui vi ss ts us vs
  simp only [ss.reduced_ok, bind_ok] at hflags
  unfold NativeField.zakura_udon.field.pasta.products.PastaField.product_difference
  rw [ss.reduced_ok]
  simp only [bind_ok]
  rw [hflags]
  simp only [bind_ok]
  rw [wide_multiply_eq]
  step -grind with (slice_multiply_wide_spec a.limbs b.limbs) as ⟨wide, hwide⟩
  rw [wide_multiply_eq]
  step -grind with (slice_multiply_wide_spec c.limbs d.limbs) as ⟨product, hproduct⟩
  cases double with
  | true =>
    rw [if_pos (show (true : Bool) = true from rfl)]
    simp only [MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
      bind_ok, Std.uncurry_apply_pair]
    obtain ⟨pair,hresult,hspec⟩ := WP.spec_imp_exists (product_double_loop_spec product)
    rcases pair with ⟨carry,doubledIter⟩
    rcases hspec with ⟨hcarry,hdouble⟩
    simp only [Array.to_slice] at hresult
    rw [hresult]
    simp only [bind_ok,Std.uncurry_apply_pair]
    let doubled := Array.from_slice product doubledIter.slice
    change val8 doubled+R^2*carry.val=2*val8 product at hdouble
    have hdoubleBound : 2 * val8 product < R ^ 2 := by
      rw [hproduct]
      nlinarith only [hcd, product_double_loose_limit inst params]
    have hcarryValue : carry.val = 0 := by
      norm_num [B, R] at hdouble hdoubleBound
      omega
    have hcarryEq : carry = 0#u64 := by scalar_tac
    step -grind
    have hdoubled : val8 doubled = 2 * (val4 c.limbs * val4 d.limbs) := by
      simpa only [hcarryValue, mul_zero, add_zero, hproduct] using hdouble
    simp only [Array.to_slice_mut, lift, core.slice.Slice.iter_mut, mutableZipCtor,
      Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
      bind_ok, Std.uncurry_apply_pair]
    obtain ⟨pair,hresult,hspec⟩ := WP.spec_imp_exists (product_subtract_loop_spec wide doubled)
    rcases pair with ⟨borrow,subtractBack⟩
    rcases hspec with ⟨hborrow,hsub⟩
    simp only [Array.to_slice] at hresult ⊢
    rw [hresult]
    simp only [bind_ok,Std.uncurry_apply_pair]
    let wrapped := Array.from_slice wide (subtractBack ⟨⟨wide.to_slice,0⟩,⟨doubled.to_slice,0⟩⟩).fst.slice
    change val8 wrapped+val8 doubled=val8 wide+R^2*borrow.val at hsub
    rw [hwide, hdoubled] at hsub
    have hfinish := product_restore_finish_spec inst params wrapped borrow
      (ss.reduced && ts.reduced && us.reduced && vs.reduced) true
      (val4 a.limbs * val4 b.limbs) (productScale true * (val4 c.limbs * val4 d.limbs))
      hborrow hsub hinput.1 hinput.2
    rw [product_restore_finish_eq] at hfinish
    simp only [productOffset,Array.to_slice] at hfinish
    with_unfolding_all exact hfinish
  | false =>
    rw [if_neg (by decide : ¬ ((false : Bool) = true))]
    simp only [Array.to_slice_mut, lift, core.slice.Slice.iter_mut, mutableZipCtor,
      Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
      bind_ok, Std.uncurry_apply_pair]
    simp only [product_second_subtract_eq]
    obtain ⟨pair,hresult,hspec⟩ := WP.spec_imp_exists (product_subtract_loop_spec wide product)
    rcases pair with ⟨borrow,subtractBack⟩
    rcases hspec with ⟨hborrow,hsub⟩
    simp only [Array.to_slice] at hresult ⊢
    rw [hresult]
    simp only [bind_ok,Std.uncurry_apply_pair]
    let wrapped := Array.from_slice wide (subtractBack ⟨⟨wide.to_slice,0⟩,⟨product.to_slice,0⟩⟩).fst.slice
    change val8 wrapped+val8 product=val8 wide+R^2*borrow.val at hsub
    rw [hwide, hproduct] at hsub
    simp only [product_second_restore_eq]
    have hfinish := product_restore_finish_spec inst params wrapped borrow
      (ss.reduced && ts.reduced && us.reduced && vs.reduced) false
      (val4 a.limbs * val4 b.limbs) (productScale false * (val4 c.limbs * val4 d.limbs))
      hborrow (by simpa [productScale] using hsub) hinput.1 hinput.2
    rw [product_restore_finish_eq] at hfinish
    simp only [productOffset,Array.to_slice] at hfinish
    with_unfolding_all exact hfinish

#print axioms product_difference_spec

end UdonVerify.Native
