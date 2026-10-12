import NativeProductFold
import NativeProductSquareLoop
import NativeProductMergeLoop
import SquareProofs

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem product_square_eq (value : A4) :
    NativeField.zakura_udon.field.pasta.word.square_wide value =
      udon_kernel_slice.field.pasta.word.square_wide value := by
  rfl

@[step]
theorem product_add_square_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (sum : Sum M) (value : Element M S) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_square inst sum value
      ⦃ out => Nat.ModEq (val4 params.modulus) (sumInteger out)
        (sumInteger sum + val4 value.limbs ^ 2) ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.products.ProductSum.add_square
  rw [product_square_eq]
  step -grind with (slice_square_wide_spec value.limbs) as ⟨square, hsquare⟩
  simp only [lift,Array.to_slice_mut,core.slice.Slice.iter_mut,mutableZipCtor,
    _root_.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,Array.to_slice,Std.bind_assoc,bind_ok,Std.uncurry]
  obtain ⟨result,hresultLoop,hpost⟩ := WP.spec_imp_exists (add_square_loop_spec sum.wide square)
  rcases result with ⟨carry,z⟩
  rcases hpost with ⟨hcarry,hloop⟩
  simp only [Array.to_slice] at hresultLoop
  with_unfolding_all rw [hresultLoop]
  simp only [bind_ok,Std.uncurry]
  let middle : Sum M := {sum with wide:=Array.from_slice sum.wide z.fst.slice}
  obtain ⟨sumCarry,overflow,hresult,hvalue⟩ := product_adc_result sum.carry 0#u64 carry
  rw [hresult]
  simp only [bind_ok,Std.uncurry]
  have hoverflow : overflow.val ≤ 1 :=
    adc_carry_le_one middle.carry 0#u64 carry sumCarry overflow hcarry hvalue
  let raw : Sum M := { middle with carry := sumCarry }
  have hraw : sumInteger raw + B ^ 9 * overflow.val =
      sumInteger sum + val4 value.limbs ^ 2 := by
    rw [hsquare] at hloop
    simp only [raw, sumInteger, accumulatorValue]
    norm_num [B, R] at hloop hvalue ⊢
    nlinarith only [hloop, hvalue]
  step -grind with (product_fold_overflow_spec inst params constants raw overflow hoverflow)
    as ⟨out, hout⟩
  change Nat.ModEq (val4 params.modulus) (sumInteger out)
    (sumInteger raw + B ^ 9 * overflow.val) at hout
  rw [hraw] at hout
  exact hout

@[step]
theorem product_merge_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (sum other : Sum M) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.merge inst sum other
      ⦃ out => Nat.ModEq (val4 params.modulus) (sumInteger out)
        (sumInteger sum + sumInteger other) ⦄ := by
  rw [merge_expansion_eq,merge_expansion_raw_eq]
  obtain ⟨result,hresultRaw,hpost⟩ := WP.spec_imp_exists (merge_raw_spec sum.wide other.wide)
  rcases result with ⟨wide,carry⟩
  rcases hpost with ⟨hcarry,hloop⟩
  rw [hresultRaw]
  simp only [bind_ok,Std.uncurry]
  let middle : Sum M := {sum with wide}
  obtain ⟨sumCarry,overflow,hresult,hvalue⟩ := product_adc_result sum.carry other.carry carry
  rw [hresult]
  simp only [bind_ok,Std.uncurry]
  have hoverflow : overflow.val ≤ 1 :=
    adc_carry_le_one middle.carry other.carry carry sumCarry overflow hcarry hvalue
  let raw : Sum M := { middle with carry := sumCarry }
  have hraw : sumInteger raw + B ^ 9 * overflow.val =
      sumInteger sum + sumInteger other := by
    simp only [raw, sumInteger, accumulatorValue]
    norm_num [B, R] at hloop hvalue ⊢
    nlinarith only [hloop, hvalue]
  step -grind with (product_fold_overflow_spec inst params constants raw overflow hoverflow)
    as ⟨out, hout⟩
  change Nat.ModEq (val4 params.modulus) (sumInteger out)
    (sumInteger raw + B ^ 9 * overflow.val) at hout
  rw [hraw] at hout
  exact hout

#print axioms product_add_square_spec
#print axioms product_merge_spec

end UdonVerify.Native
