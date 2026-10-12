import NativeField.Funs
import NativeWideDecode

open Aeneas Std Result
namespace UdonVerify.Native
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def bytePrefix (bytes : Aeneas.Std.Slice U8) (count : Nat) : Aeneas.Std.Slice U8 :=
  Slice.from (bytes.val.take count)
    (by have := bytes.property; simp only [List.length_take]; omega)

def byteSuffix (bytes : Aeneas.Std.Slice U8) (count : Nat) : Aeneas.Std.Slice U8 :=
  Slice.from (bytes.val.drop count)
    (by have := bytes.property; simp only [List.length_drop]; omega)

theorem marker_clone_inert {S : Type} (marker : NativeField.core.marker.PhantomData S) :
    core.marker.PhantomData.Insts.CoreCloneClone.clone (T := S) marker = ok marker := by rfl

#print axioms marker_clone_inert

abbrev chunksBack :=
  _root_.core.slice.iter.Chunks.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedSlice.next_back (T := U8)

theorem chunks_back_multiple_eq (bytes : Aeneas.Std.Slice U8)
    (hmultiple : bytes.length % 32 = 0) :
    chunksBack ⟨bytes,32#usize⟩ =
      if bytes.length = 0 then ok (none,⟨bytes,32#usize⟩)
      else ok (some (byteSuffix bytes (bytes.length-32)),
        ⟨bytePrefix bytes (bytes.length-32),32#usize⟩) := by
  unfold chunksBack
  simp [_root_.core.slice.iter.Chunks.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedSlice.next_back,
    hmultiple,bytePrefix,byteSuffix]

theorem full_chunk_facts (bytes : Aeneas.Std.Slice U8)
    (hmultiple : bytes.length % 32 = 0) (hpositive : 0 < bytes.length) :
    32 ≤ bytes.length ∧ (byteSuffix bytes (bytes.length-32)).length=32 ∧
      (bytePrefix bytes (bytes.length-32)).length=bytes.length-32 ∧
      (bytePrefix bytes (bytes.length-32)).length % 32 = 0 ∧
      (bytePrefix bytes (bytes.length-32)).length < bytes.length := by
  have hsize : 32 ≤ bytes.length := by omega
  have hs : bytes.val.length=bytes.length := rfl
  simp only [byteSuffix,bytePrefix,Slice.length,Slice.from_val,List.length_drop,List.length_take]
  omega

theorem byteValue_prefix_suffix (bytes : Aeneas.Std.Slice U8) (count : Nat)
    (hcount : count ≤ bytes.length) :
    byteValue bytes.val = byteValue (bytePrefix bytes count).val +
      256^count * byteValue (byteSuffix bytes count).val := by
  have hsplit := (List.take_append_drop count bytes.val).symm
  conv_lhs => rw [hsplit]
  rw [byteValue_append]
  simp only [bytePrefix,byteSuffix,Slice.from_val]
  have hlen : (bytes.val.take count).length=count := by
    simp only [List.length_take]
    exact min_eq_left hcount
  rw [hlen]

def initialSplit (bytes : Aeneas.Std.Slice U8) : Nat :=
  bytes.length-(if bytes.length % 32 ≠ 0 then bytes.length % 32 else 32)

theorem chunks_back_initial_eq (bytes : Aeneas.Std.Slice U8) (hpositive : 0 < bytes.length) :
    chunksBack ⟨bytes,32#usize⟩ =
      ok (some (byteSuffix bytes (initialSplit bytes)),
        ⟨bytePrefix bytes (initialSplit bytes),32#usize⟩) := by
  unfold chunksBack
  simp [_root_.core.slice.iter.Chunks.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedSlice.next_back,
    show bytes.length ≠ 0 by omega,initialSplit,bytePrefix,byteSuffix]

theorem initial_chunk_facts (bytes : Aeneas.Std.Slice U8) (hpositive : 0 < bytes.length) :
    initialSplit bytes ≤ bytes.length ∧
      0 < (byteSuffix bytes (initialSplit bytes)).length ∧
      (byteSuffix bytes (initialSplit bytes)).length ≤ 32 ∧
      (bytePrefix bytes (initialSplit bytes)).length = initialSplit bytes ∧
      (bytePrefix bytes (initialSplit bytes)).length % 32 = 0 := by
  have hmod : bytes.length % 32 < 32 := Nat.mod_lt _ (by decide)
  have hle : bytes.length % 32 ≤ bytes.length := Nat.mod_le _ _
  have hs : bytes.val.length=bytes.length := rfl
  simp only [byteSuffix,bytePrefix,Slice.length,Slice.from_val,List.length_drop,List.length_take]
  by_cases hrem : bytes.length % 32 = 0 <;> simp [initialSplit,hrem] <;> omega

#print axioms chunks_back_initial_eq
#print axioms initial_chunk_facts
#print axioms chunks_back_multiple_eq
#print axioms full_chunk_facts
#print axioms byteValue_prefix_suffix
end UdonVerify.Native
