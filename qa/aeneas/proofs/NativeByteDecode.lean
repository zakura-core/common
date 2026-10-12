import NativeCanonical
import NativeBytePartition
import NativeField.Funs

open Aeneas Std Result
namespace UdonVerify.Native
open NativeField.zakura_udon.field.pasta.uint
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev Bytes32 := Array U8 32#usize

def chunkValue (bytes : Bytes32) (index : Nat) : Nat :=
  byteValue (bytes.val.slice (index*8) ((index+1)*8))

@[step]
theorem decode_closure_spec (bytes : Bytes32) (index : Usize) (hi : index.val<4) :
    CanonicalUint.from_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut bytes index
      ⦃ word state => word.val=chunkValue bytes index.val ∧ state=bytes ⦄ := by
  unfold CanonicalUint.from_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  step -grind as ⟨start,hstart⟩
  step -grind as ⟨index',hindex⟩
  step -grind as ⟨finish,hfinish⟩
  step -grind as ⟨chunk,hchunk,hchunklen⟩
  step -grind as ⟨r,hr⟩
  have hchunk8 : chunk.length=8 := by omega
  cases r with
  | Err err => cases err; simp only at hr; omega
  | Ok a =>
    simp only at hr
    simp only [core.result.Result.unwrap,bind_ok]
    step -grind as ⟨word,hword⟩
    have hw : word.val=byteValue a.val := by
      simpa only [UScalar.val,BitVec.toNat_cast,bitvec_from_le_value] using
        congrArg BitVec.toNat hword
    rw [hw,hr.1,hchunk]
    simp [Array.to_slice,chunkValue,hstart,hfinish,hindex]

theorem array_from_fn_four_eq {T F : Type} (inst : core.ops.function.FnMut F Usize T) (f : F) :
    core.array.from_fn 4#usize inst f = (do
      let (a,f0) ← inst.call_mut f 0#usize
      let (b,f1) ← inst.call_mut f0 1#usize
      let (c,f2) ← inst.call_mut f1 2#usize
      let (d,_) ← inst.call_mut f2 3#usize
      ok (Array.make 4#usize [a,b,c,d])) := by
  have h0 : (0:Nat)<2^UScalarTy.Usize.numBits := by scalar_tac
  have h1 : (1:Nat)<2^UScalarTy.Usize.numBits := by scalar_tac
  have h2 : (2:Nat)<2^UScalarTy.Usize.numBits := by scalar_tac
  have h3 : (3:Nat)<2^UScalarTy.Usize.numBits := by scalar_tac
  unfold core.array.from_fn
  change Std.bind (core.array.from_fn_loop inst 0 4 f)
    (fun pair => ok ({list:=pair.1} : Array T 4#usize)) = _
  simp only [core.array.from_fn_loop,h0,h1,h2,h3,↓reduceDIte]
  simp only [Std.bind_assoc,bind_ok,Std.uncurry_apply_pair]
  congr 1
  funext pair0
  rcases pair0 with ⟨a0,f0⟩
  simp only [Std.uncurry_apply_pair,bind_ok,Std.bind_assoc]
  congr 1
  funext pair1
  rcases pair1 with ⟨a1,f1⟩
  simp only [Std.uncurry_apply_pair,bind_ok,Std.bind_assoc]
  congr 1
  funext pair2
  rcases pair2 with ⟨a2,f2⟩
  simp only [Std.uncurry_apply_pair,bind_ok,Std.bind_assoc]
  congr 1
  funext pair3
  rcases pair3 with ⟨a3,f3⟩
  simp only [Std.uncurry_apply_pair,bind_ok,Std.bind_assoc]
  rfl

@[step]
theorem uint_from_bytes_spec (bytes : Bytes32) :
    CanonicalUint.from_le_bytes bytes ⦃ out => val4 out.limbs=byteValue bytes.val ⦄ := by
  unfold CanonicalUint.from_le_bytes
  rw [array_from_fn_four_eq]
  step -grind with (decode_closure_spec bytes 0#usize (by decide)) as ⟨pair0,hw0,hs0⟩
  rcases pair0 with ⟨w0,s0⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  change s0=bytes at hs0
  subst s0
  step -grind with (decode_closure_spec bytes 1#usize (by decide)) as ⟨pair1,hw1,hs1⟩
  rcases pair1 with ⟨w1,s1⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  change s1=bytes at hs1
  subst s1
  step -grind with (decode_closure_spec bytes 2#usize (by decide)) as ⟨pair2,hw2,hs2⟩
  rcases pair2 with ⟨w2,s2⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  change s2=bytes at hs2
  subst s2
  step -grind with (decode_closure_spec bytes 3#usize (by decide)) as ⟨pair3,hw3,hs3⟩
  rcases pair3 with ⟨w3,s3⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  simp only [Std.uncurry_apply_pair,bind_ok,WP.spec_ok]
  change w0.val+B*w1.val+B^2*w2.val+B^3*w3.val=byteValue bytes.val
  change w0.val=chunkValue bytes 0 at hw0
  change w1.val=chunkValue bytes 1 at hw1
  change w2.val=chunkValue bytes 2 at hw2
  change w3.val=chunkValue bytes 3 at hw3
  rw [hw0,hw1,hw2,hw3]
  simpa [chunkValue] using (byteValue_four_chunks bytes).symm

#print axioms decode_closure_spec
#print axioms uint_from_bytes_spec
end UdonVerify.Native
