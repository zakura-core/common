import CommonProductPortablePrimitives
import NativeProductMergeLoop

open Aeneas Std Result
namespace UdonVerify.ProductPortable
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def mergeCore {M : Type} (inst : Modulus M) (sum other : Sum M) : Result (Sum M) := do
  let (wide, carry) ← Native.mergeRaw sum.wide other.wide
  let (carry, overflow) ← NativeField.zakura_udon.field.pasta.word.adc sum.carry other.carry carry
  CommonProductsPortable.field.pasta.products.ProductSum.fold_overflow inst { sum with wide, carry } overflow

attribute [local irreducible] Std.bind NativeField.zakura_udon.field.pasta.word.adc

/-- All eight copied ADC payloads and the exhaustion guard agree with the native adder. -/
theorem portable_merge_core_eq {M : Type} (inst : Modulus M) (sum other : Sum M) :
    CommonProductsPortable.field.pasta.products.ProductSum.merge inst sum other = mergeCore inst sum other := by
  rcases sum with ⟨a, carry, marker⟩
  rcases other with ⟨b, otherCarry, otherMarker⟩
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,ha⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : U64,
      a = Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7] :=
    ⟨a[0]!,a[1]!,a[2]!,a[3]!,a[4]!,a[5]!,a[6]!,a[7]!,Native.array_eight_eta a⟩
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,hb⟩ : ∃ b0 b1 b2 b3 b4 b5 b6 b7 : U64,
      b = Array.make 8#usize [b0,b1,b2,b3,b4,b5,b6,b7] :=
    ⟨b[0]!,b[1]!,b[2]!,b[3]!,b[4]!,b[5]!,b[6]!,b[7]!,Native.array_eight_eta b⟩
  subst a b
  unfold CommonProductsPortable.field.pasta.products.ProductSum.merge mergeCore Native.mergeRaw
  simp (config := { maxSteps := 1000000 }) [lift,Array.to_slice_mut,Array.to_slice,core.slice.Slice.iter_mut,
    mutableZipCtor,SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter,
    SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.slice.iter.IteratorIterMut.next,core.slice.iter.IteratorSliceIter.next,
    portable_adc_bridge,Bind.bind,bind_tc_eq,Std.uncurry,Std.bind_assoc,bind_ok,
    Aeneas.Std.Slice.getElem_Nat_eq, Aeneas.Std.Slice.from_val,Array.from_slice,Slice.setAtNat]
  with_unfolding_all rfl

theorem portable_fold_zero {M : Type} (inst : Modulus M) (sum : Sum M) :
    CommonProductsPortable.field.pasta.products.ProductSum.fold_overflow inst sum 0#u64 = ok sum := by
  unfold CommonProductsPortable.field.pasta.products.ProductSum.fold_overflow
  simp

@[step]
theorem portable_merge_exact_spec {M : Type} (inst : Modulus M) (sum other : Sum M)
    (hbound : sumInteger sum + sumInteger other < B ^ 9) :
    CommonProductsPortable.field.pasta.products.ProductSum.merge inst sum other ⦃ out =>
      sumInteger out = sumInteger sum + sumInteger other ⦄ := by
  rw [portable_merge_core_eq]
  unfold mergeCore
  obtain ⟨pair,hresultRaw,hpost⟩ := WP.spec_imp_exists (Native.merge_raw_spec sum.wide other.wide)
  rcases pair with ⟨wide,lowCarry⟩
  rcases hpost with ⟨hcarry,hwide⟩
  rw [hresultRaw]
  simp only [bind_ok,Std.uncurry]
  obtain ⟨carry,overflow,hresult,hvalue⟩ := Native.product_adc_result sum.carry other.carry lowCarry
  rw [hresult]
  simp only [bind_ok,Std.uncurry]
  let raw : Sum M := { sum with wide, carry }
  have hraw : sumInteger raw + B ^ 9 * overflow.val = sumInteger sum + sumInteger other := by
    simp only [raw, sumInteger, sumToNative, Native.sumInteger, Native.accumulatorValue]
    norm_num [B,R] at hwide hvalue ⊢
    nlinarith only [hwide,hvalue]
  have hzero : overflow.val = 0 := by
    norm_num [B] at hraw hbound
    omega
  have hoverflow : overflow = 0#u64 := by scalar_tac
  subst overflow
  rw [portable_fold_zero]
  simp only [WP.spec_ok]
  simpa only [show (0#u64).val = 0 from rfl, mul_zero, add_zero] using hraw

#print axioms portable_merge_core_eq
#print axioms portable_fold_zero
#print axioms portable_merge_exact_spec
end UdonVerify.ProductPortable
