import NativeWideDecode

open Aeneas Std

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem byteValue_zeros (count : Nat) : byteValue (List.replicate count 0#u8) = 0 := by
  induction count with
  | zero => simp [byteValue, Nat.ofDigits]
  | succ n ih => simpa [byteValue, Nat.ofDigits] using ih

theorem byteValue_zero_padding (bytes : List U8) (count : Nat) :
    byteValue (bytes ++ List.replicate count 0#u8) = byteValue bytes := by
  rw [byteValue_append, byteValue_zeros]
  simp

theorem byteValue_padded_prefix (bytes : List U8) (count : Nat) (hfit : bytes.length ≤ count) :
    byteValue ((List.replicate count 0#u8).setSlice! 0 bytes) = byteValue bytes := by
  have hset := setSlice_append_suffix ([] : List U8) bytes (List.replicate count 0#u8)
    0 (by simp) (by simpa using hfit)
  simpa only [List.nil_append, List.drop_replicate, byteValue_zero_padding] using
    congrArg byteValue hset

theorem byteValue_drop_step (bytes : Aeneas.Std.Slice U8) (start finish : Nat)
    (hstep : finish = start + 32) (hfit : finish ≤ bytes.length) :
    byteValue (bytes.val.drop start) = byteValue (bytes.val.slice start finish) +
      R * byteValue (bytes.val.drop finish) := by
  have hsplit : bytes.val.drop start = bytes.val.slice start finish ++ bytes.val.drop finish := by
    rw [List.slice, hstep, Nat.add_sub_cancel_left]
    conv_rhs => rhs; rw [← List.drop_drop]
    exact (List.take_append_drop 32 (bytes.val.drop start)).symm
  have hlen : (bytes.val.slice start finish).length = 32 := by
    simp only [List.slice_length, hstep, Nat.add_sub_cancel_left]
    have hsize : bytes.val.length = bytes.length := rfl
    omega
  conv_lhs => rw [hsplit]
  rw [byteValue_append, hlen]
  norm_num [R, B]

theorem montgomery_of_decode (p inverse raw value : Nat)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (hdecode : (raw * inverse) % p = value % p) :
    Nat.ModEq p raw (R * value) := by
  have hc : Nat.ModEq p (raw * inverse) value := hdecode
  have hl : Nat.ModEq p ((raw * inverse) * R) raw := by
    convert hinverse.mul_left raw using 1 <;> ring
  convert hl.symm.trans (hc.mul_right R) using 1 <;> ring

theorem decode_of_montgomery (p inverse raw value : Nat)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (hraw : Nat.ModEq p raw (R * value)) :
    (raw * inverse) % p = value % p := by
  have hr : Nat.ModEq p ((R * value) * inverse) value := by
    convert hinverse.mul_right value using 1 <;> ring
  exact (hraw.mul_right inverse).trans hr

theorem raw_result_congruence (p inverse product out m result : Nat)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (hproduct : Nat.ModEq p product (R * result))
    (hcert : R * out = product + m * p) : Nat.ModEq p out result := by
  have hc := (certificate_congruence p product m out hcert).trans hproduct
  have hscaled : Nat.ModEq p ((R * inverse) * out) ((R * inverse) * result) := by
    convert hc.mul_right inverse using 1 <;> ring
  have hl : Nat.ModEq p ((R * inverse) * out) out := by
    simpa only [one_mul] using hinverse.mul_right out
  have hr : Nat.ModEq p ((R * inverse) * result) result := by
    simpa only [one_mul] using hinverse.mul_right result
  exact hl.symm.trans (hscaled.trans hr)

#print axioms byteValue_padded_prefix
#print axioms byteValue_drop_step
#print axioms montgomery_of_decode
#print axioms decode_of_montgomery
#print axioms raw_result_congruence

end UdonVerify.Native
