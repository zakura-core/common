import NativeByteMath

open Aeneas Std

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

theorem byteValue_append (a b : List U8) :
    byteValue (a ++ b) = byteValue a + 256 ^ a.length * byteValue b := by
  simp only [byteValue, List.map_append, Nat.ofDigits_append, List.length_map]

theorem setSlice_append_suffix {α : Type} (kept chunk suffix : List α) (offset : Nat)
    (hprefix : kept.length = offset) (hfit : chunk.length ≤ suffix.length) :
    (kept ++ suffix).setSlice! offset chunk = kept ++ chunk ++ suffix.drop chunk.length := by
  subst offset
  simp [List.setSlice!, List.take_append, List.drop_append, Nat.min_eq_left hfit]

theorem four_byte_slices (bytes : Array U8 32#usize) :
    bytes.val = bytes.val.slice 0 8 ++ bytes.val.slice 8 16 ++
      bytes.val.slice 16 24 ++ bytes.val.slice 24 32 := by
  have h32 : bytes.val.take 32 = bytes.val := by simp
  calc
    bytes.val = bytes.val.take 32 := h32.symm
    _ = bytes.val.take 24 ++ (bytes.val.drop 24).take 8 :=
      List.take_add (i := 24) (j := 8)
    _ = (bytes.val.take 16 ++ (bytes.val.drop 16).take 8) ++
          (bytes.val.drop 24).take 8 := by rw [List.take_add (i := 16) (j := 8)]
    _ = ((bytes.val.take 8 ++ (bytes.val.drop 8).take 8) ++
          (bytes.val.drop 16).take 8) ++ (bytes.val.drop 24).take 8 := by
      rw [List.take_add (i := 8) (j := 8)]
    _ = _ := by simp [List.slice]

theorem byteValue_four_chunks (bytes : Array U8 32#usize) :
    byteValue bytes.val = byteValue (bytes.val.slice 0 8) +
      B * byteValue (bytes.val.slice 8 16) +
      B ^ 2 * byteValue (bytes.val.slice 16 24) +
      B ^ 3 * byteValue (bytes.val.slice 24 32) := by
  have h0 : (bytes.val.slice 0 8).length = 8 := by simp [List.slice_length]
  have h1 : (bytes.val.slice 8 16).length = 8 := by simp [List.slice_length]
  have h2 : (bytes.val.slice 16 24).length = 8 := by simp [List.slice_length]
  have h3 : (bytes.val.slice 24 32).length = 8 := by simp [List.slice_length]
  conv_lhs => rw [four_byte_slices bytes]
  simp only [byteValue_append, List.length_append, h0, h1, h2, h3]
  norm_num [B]

end UdonVerify.Native
