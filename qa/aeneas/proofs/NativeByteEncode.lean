import NativeByteDecode
open Aeneas Std Result
namespace UdonVerify.Native
open NativeField.zakura_udon.field.pasta.uint.CanonicalUint
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def limbBytes (limbs : A4) (index : Nat) : List U8 :=
  (core.num.U64.to_le_bytes limbs[index]!).val

theorem limbBytes_length (limbs : A4) (index : Nat) :
    (limbBytes limbs index).length = 8 := by simp [limbBytes]

theorem limbBytes_value (limbs : A4) (index : Nat) :
    byteValue (limbBytes limbs index) = limbs[index]!.val := by
  have h := bitvec_from_le_value (limbBytes limbs index)
  rw [← h]
  have hmap : (limbBytes limbs index).map U8.bv = limbs[index]!.bv.toLEBytes := by
    simp [limbBytes, core.num.U64.to_le_bytes, List.map_map]
  rw [hmap, BitVec.fromLEBytes_toLEBytes (by decide)]
  simp only [BitVec.toNat_cast]
  rfl

abbrev ChunkZip := core.iter.adapters.zip.Zip (_root_.core.slice.iter.ChunksExactMut U8)
  (_root_.core.array.iter.IntoIter U64 4#usize)

theorem encode_loop_unfold (iter : ChunkZip) (back : ChunkZip → ChunkZip) :
    to_le_bytes_loop iter back = (do
      let result ← to_le_bytes_loop.body iter back
      match result with
      | .done result => ok result
      | .cont (next,back') => to_le_bytes_loop next back') := by
  unfold to_le_bytes_loop
  rw [loop]
  congr 1
  funext result
  cases result with
  | done result => rfl
  | cont result => rcases result with ⟨next,back'⟩; rfl

@[step]
theorem encode_body_spec (bytes : Aeneas.Std.Slice U8) (limbs : A4) (index : Nat)
    (hlen : bytes.length=32) (hi : index<4) (back : ChunkZip → ChunkZip) :
    to_le_bytes_loop.body
      ⟨⟨bytes,index*8,8#usize⟩,⟨Array.to_slice limbs,index⟩⟩ back
      ⦃ result => result=.cont
        (⟨⟨bytes,(index+1)*8,8#usize⟩,⟨Array.to_slice limbs,index+1⟩⟩,
          fun z => back {z with fst := {z.fst with
            slice := z.fst.slice.setSlice! (index*8) (limbBytes limbs index)}}) ⦄ := by
  unfold to_le_bytes_loop.body
  simp only [mutableZipNext,
    Aeneas.Std.core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice,
    _root_.core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next]
  have hc : 0<(8#usize).val ∧ index*8+(8#usize).val≤bytes.length := by
    change 0<8 ∧ index*8+8≤bytes.val.length
    change bytes.val.length=32 at hlen
    omega
  have hf : 8≤32-index*8 := by omega
  simp only [hc,↓reduceDIte,Std.uncurry_apply_pair,bind_ok]
  simp [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorSliceIter.next,hi,Array.to_slice,Slice.len,
    Std.bind_assoc,hlen,hc,lift,core.slice.Slice.copy_from_slice,
    Nat.min_eq_left hf,limbBytes,Nat.add_mul]

theorem set_four_chunks {T : Type} (bytes a b c d : List T)
    (hbytes : bytes.length=32) (ha : a.length=8) (hb : b.length=8)
    (hc : c.length=8) (hd : d.length=8) :
    ((((bytes.setSlice! 24 d).setSlice! 16 c).setSlice! 8 b).setSlice! 0 a)=a++b++c++d := by
  have hta : a.take 8=a := by rw [←ha]; exact List.take_length
  have htb : b.take 8=b := by rw [←hb]; exact List.take_length
  have htc : c.take 8=c := by rw [←hc]; exact List.take_length
  have htd : d.take 8=d := by rw [←hd]; exact List.take_length
  simp [List.setSlice!,ha,hb,hc,hd,hbytes,List.take_append,List.drop_append,
    List.take_take,List.drop_drop,hta,htb,htc,htd]

theorem encode_body_done (bytes : Aeneas.Std.Slice U8) (limbs : A4)
    (hlen : bytes.length=32) (back : ChunkZip → ChunkZip) :
    to_le_bytes_loop.body ⟨⟨bytes,32,8#usize⟩,⟨Array.to_slice limbs,4⟩⟩ back =
      ok (.done (back ⟨⟨bytes,32,8#usize⟩,⟨Array.to_slice limbs,4⟩⟩)) := by
  simp [to_le_bytes_loop.body,mutableZipNext,
    Aeneas.Std.core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice,
    _root_.core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next,
    hlen]

@[step]
theorem encode_loop_spec (bytes : Aeneas.Std.Slice U8) (limbs : A4) (hlen : bytes.length=32) :
    to_le_bytes_loop ⟨⟨bytes,0,8#usize⟩,⟨Array.to_slice limbs,0⟩⟩ (fun z=>z)
      ⦃ out => out.fst.slice.val=limbBytes limbs 0++limbBytes limbs 1++
        limbBytes limbs 2++limbBytes limbs 3 ⦄ := by
  rw [encode_loop_unfold]
  step -grind with (encode_body_spec bytes limbs 0 hlen (by decide) _) as ⟨r0,hr0⟩
  subst r0
  simp only [bind_ok]
  rw [encode_loop_unfold]
  step -grind with (encode_body_spec bytes limbs 1 hlen (by decide) _) as ⟨r1,hr1⟩
  subst r1
  simp only [bind_ok]
  rw [encode_loop_unfold]
  step -grind with (encode_body_spec bytes limbs 2 hlen (by decide) _) as ⟨r2,hr2⟩
  subst r2
  simp only [bind_ok]
  rw [encode_loop_unfold]
  step -grind with (encode_body_spec bytes limbs 3 hlen (by decide) _) as ⟨r3,hr3⟩
  subst r3
  simp only [bind_ok]
  rw [encode_loop_unfold,encode_body_done bytes limbs hlen]
  simp only [bind_ok,WP.spec_ok]
  simp only [Slice.setSlice!,Slice.from_val]
  exact set_four_chunks bytes.val _ _ _ _ hlen
    (limbBytes_length _ _) (limbBytes_length _ _) (limbBytes_length _ _) (limbBytes_length _ _)

#print axioms encode_loop_spec

@[step]
theorem uint_to_bytes_spec (value : CanonicalUint) :
    to_le_bytes value ⦃ out => byteValue out.val=val4 value.limbs ⦄ := by
  unfold to_le_bytes
  simp [lift,Array.to_slice_mut,Array.to_slice,core.slice.Slice.chunks_exact_mut,
    mutableZipCtor,_root_.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    massert_True,NativeField.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter]
  have hloop := encode_loop_spec (Array.to_slice (Array.repeat 32#usize 0#u8))
    value.limbs (by simp)
  simp [Array.to_slice,Array.repeat] at hloop
  with_unfolding_all step -grind with hloop as ⟨out,hout⟩
  have hlen : out.fst.slice.val.length=32 := by
    rw [hout]
    simp [limbBytes_length]
  simp [Array.from_slice,hlen,hout,limbBytes_length]
  change byteValue (limbBytes value.limbs 0++(limbBytes value.limbs 1++
    (limbBytes value.limbs 2++limbBytes value.limbs 3)))=val4 value.limbs
  rw [byteValue_append,byteValue_append,byteValue_append]
  simp only [limbBytes_length,limbBytes_value]
  norm_num [B,val4]
  ring

#print axioms uint_to_bytes_spec

end UdonVerify.Native
