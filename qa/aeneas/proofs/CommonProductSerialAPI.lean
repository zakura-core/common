import CommonProductSerialLoop
import NativeCanonical

open Aeneas Std Result
namespace UdonVerify.ProductSerial
open UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev State := CommonProductSerial.field.pasta.representation.ReductionState

@[step]
theorem serial_slice_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (left : State S) (right : State T)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length = rhs.length) (hmin : 4 ≤ lhs.length) (hmax : lhs.length < 64) :
    CommonProductSerial.field.pasta.products.PastaField.sum_of_products_slice
      (serialDict inst) left right lhs rhs ⦃ out =>
        val4 out.limbs < 2 * val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (R * val4 out.limbs)
          (rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val) ⦄ := by
  have hlenU : Aeneas.Std.Slice.len lhs = Aeneas.Std.Slice.len rhs :=
    UScalar.eq_of_val_eq (by simpa only [Aeneas.Std.Slice.len_val] using hlen)
  have hnotOne : Aeneas.Std.Slice.len lhs ≠ 1#usize := by scalar_tac
  have hnotShort : ¬ Aeneas.Std.Slice.len lhs ≤ 3#usize := by scalar_tac
  have hlt : Aeneas.Std.Slice.len lhs < 64#usize := by scalar_tac
  have hnotEmpty : lhs.length ≠ 0 := by omega
  have hbits : core.num.Usize.BITS ≤ 64#u32 := by
    change (core.num.Usize.BITS).val ≤ 64
    simpa [core.num.Usize.BITS] using System.Platform.numBits_le
  have hsumBound := bounded_sum_fits_accumulator (fun a => val4 a.limbs) (fun b => val4 b.limbs)
    lhs.val rhs.val hlen (show lhs.val.length < B from _root_.lt_trans hmax (by norm_num [B]))
    (fun a _ => val4_lt a.limbs) (fun b _ => val4_lt b.limbs)
  unfold CommonProductSerial.field.pasta.products.PastaField.sum_of_products_slice
  simp only [←hlenU]
  simp [hbits, hnotOne, hnotShort, hlt, hnotEmpty, core.slice.Slice.is_empty, massert,
    CommonProductSerial.field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD]
  simp only [CommonProductSerial.zakura_udon.field.pasta.products.ProductSum.new, bind_ok,
    core.slice.Slice.iter, core.iter.traits.iterator.Iterator.zip.trait_default,
    core.iter.traits.iterator.Iterator.zip.default,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    Bind.bind, bind_ok]
  have hzero : sumInteger (CommonProductSerial.field.pasta.products.ProductSum.mk (M := M)
      (Array.repeat 8#usize 0#u64) 0#u64 ()) = 0 := by
    simp [sumInteger, sumToNative, Native.sumInteger, Native.accumulatorValue, val8]
  step -grind with (serial_accumulation_spec inst params constants lhs rhs
    (CommonProductSerial.field.pasta.products.ProductSum.mk (M := M) (Array.repeat 8#usize 0#u64) 0#u64 ()) hlen (by simpa [hzero] using hsumBound))
    as ⟨sum,hsum⟩
  step -grind with (serial_finish_spec inst params constants sum) as ⟨out,hbound,hcert⟩
  exact ⟨hbound, by simpa only [hsum,hzero,zero_add] using hcert⟩

def decodedSum {M S T : Type} (p inverse : Nat)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) : Nat :=
  rawSum (fun a => Native.decode p inverse a.limbs)
    (fun b => Native.decode p inverse b.limbs) lhs.val rhs.val % p

@[step]
theorem serial_slice_value_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (left : State S) (right : State T)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length = rhs.length) (hmin : 4 ≤ lhs.length) (hmax : lhs.length < 64)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1) :
    CommonProductSerial.field.pasta.products.PastaField.sum_of_products_slice
      (serialDict inst) left right lhs rhs ⦃ out =>
        val4 out.limbs < 2 * val4 params.modulus ∧
        Native.decode (val4 params.modulus) inverse out.limbs =
          decodedSum (val4 params.modulus) inverse lhs rhs ⦄ := by
  apply WP.spec_mono (serial_slice_spec inst params constants left right lhs rhs hlen hmin hmax)
  intro out hout
  refine ⟨hout.1,?_⟩
  have hscaled := Native.decoded_product_sum _ _ _ _ hinverse hout.2
  have hdecoded := raw_sum_decoded (fun a => val4 a.limbs) (fun b => val4 b.limbs)
    (val4 params.modulus) inverse lhs.val rhs.val
  exact hscaled.trans hdecoded.symm

theorem serial_slice_lengths_mismatch {M S T : Type} (inst : Modulus M) (left : State S) (right : State T)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length ≠ rhs.length) :
    CommonProductSerial.field.pasta.products.PastaField.sum_of_products_slice inst left right lhs rhs =
      fail Error.panic := by
  have hne : Aeneas.Std.Slice.len lhs ≠ Aeneas.Std.Slice.len rhs := by
    intro h
    exact hlen (by simpa using congrArg UScalar.val h)
  unfold CommonProductSerial.field.pasta.products.PastaField.sum_of_products_slice
  simp [hne, massert, core.fmt.Arguments.from_str]

#print axioms serial_slice_spec
#print axioms serial_slice_value_spec
#print axioms serial_slice_lengths_mismatch
end UdonVerify.ProductSerial
