import NativeDouble
open Aeneas Std Result
open NativeField
open NativeField.zakura_udon.field.pasta.small
namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def smallFinish {M : Type} (inst : Modulus M) (limbs : A4) (carry : U64) :
    Result (Element M Loose) := do
  let i ← carry <<< 2#i32
  let i1 ← Array.index_usize limbs 3#usize
  let i2 ← i1 >>> 62#i32
  let q ← lift (i ||| i2)
  let i3 ← 1#u64 <<< 62#i32
  let i4 ← i3 - 1#u64
  let i5 ← lift (i1 &&& i4)
  let limbs1 ← Array.update limbs 3#usize i5
  let a ← inst.MODULUS
  let i6 ← Array.index_usize a 0#usize
  let (c0, carry1) ← NativeField.zakura_udon.field.pasta.word.mac 0#u64 i6 q 0#u64
  let i7 ← Array.index_usize a 1#usize
  let (c1, c2) ← NativeField.zakura_udon.field.pasta.word.mac 0#u64 i7 q carry1
  let i8 ← Array.index_usize limbs1 0#usize
  let (r0, borrow) ← NativeField.zakura_udon.field.pasta.word.sbb i8 c0 0#u64
  let i9 ← Array.index_usize limbs1 1#usize
  let (r1, borrow1) ← NativeField.zakura_udon.field.pasta.word.sbb i9 c1 borrow
  let i10 ← Array.index_usize limbs1 2#usize
  let (r2, borrow2) ← NativeField.zakura_udon.field.pasta.word.sbb i10 c2 borrow1
  let i11 ← Array.index_usize limbs1 3#usize
  let (r3, borrow3) ← NativeField.zakura_udon.field.pasta.word.sbb i11 0#u64 borrow2
  if borrow3 != 0#u64
  then
    let (s, to_slice_mut_back) ←
      lift (Array.to_slice_mut (Array.make 4#usize [ r0, r1, r2, r3 ]))
    let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
    let (iter3, trait_default_back) ←
      mutableZipCtor
        (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
        Std.U64) (Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter
        Std.U64 4#usize) im a
    let (z, back1) ←
      NativeField.zakura_udon.field.pasta.small.multiply_loop0_loop0 iter3 (fun z1 => z1)
        0#u64
    let z1 := back1 z
    let im1 := trait_default_back z1
    let s1 := iter_mut_back im1
    let limbs2 := to_slice_mut_back s1
    let pf ←
      NativeField.zakura_udon.field.pasta.PastaField.from_montgomery
        inst
        NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState
        limbs2
    ok pf
  else
    let pf ←
      NativeField.zakura_udon.field.pasta.PastaField.from_montgomery
        inst
        NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState
        (Array.make 4#usize [ r0, r1, r2, r3 ])
    ok pf

end UdonVerify.Native
