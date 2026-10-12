module
public import Aeneas
public import KernelSlice.FunsExternal
public import NativeField.Types
@[expose] public section

open Aeneas Std Result

/-- Cloning the zero-sized marker preserves its sole value. -/
@[rust_fun
  "core::marker::{core::clone::Clone<core::marker::PhantomData<@T>>}::clone"]
def core.marker.PhantomData.Insts.CoreCloneClone.clone {T : Type}
    (marker : NativeField.core.marker.PhantomData T) :
    Result (NativeField.core.marker.PhantomData T) :=
  ok marker

def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next {T : Type} {N : Usize}
    (it : core.array.iter.IntoIter T N) := core.slice.iter.IteratorSliceIter.next it

def Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter {T : Type} {N : Usize}
    (a : Array T N) : Result (core.array.iter.IntoIter T N) := ok ⟨Slice.from a.val (by scalar_tac),0⟩

def MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter {T : Type} {N : Usize}
    (a : Array T N) : Result (core.slice.iter.IterMut T × (core.slice.iter.IterMut T → Array T N)) :=
  ok (⟨Slice.from a.val (by scalar_tac),0⟩,fun it => Array.from_slice a it.slice)

def MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter {T : Type}
    (s : Aeneas.Std.Slice T) : Result (core.slice.iter.IterMut T ×
      (core.slice.iter.IterMut T → Aeneas.Std.Slice T)) :=
  ok (⟨s,0⟩,fun it => it.slice)

structure MutableIterator (Self Item : Type) where
  next : Self → Result (Option Item × Self × (Self → Option Item → Self))

namespace Aeneas.Std

def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT (T : Type) :
    MutableIterator (core.slice.iter.IterMut T) T := ⟨core.slice.iter.IteratorIterMut.next⟩

end Aeneas.Std

def mutableZipCtor {A U X Y B : Type} (_a : MutableIterator A X)
    (b : core.iter.traits.collect.IntoIterator U Y B) (it : A) (other : U) :
    Result (core.iter.adapters.zip.Zip A B × (core.iter.adapters.zip.Zip A B → A)) := do
  let other' ← b.into_iter other
  ok (⟨it,other'⟩,fun z => z.fst)

def mutableZipNext {A B X Y : Type} (a : MutableIterator A X)
    (b : core.iter.traits.iterator.Iterator B Y) (it : core.iter.adapters.zip.Zip A B) :
    Result (Option (X × Y) × core.iter.adapters.zip.Zip A B ×
      (core.iter.adapters.zip.Zip A B → Option (X × Y) → core.iter.adapters.zip.Zip A B)) := do
  let (oa,ia,backa) ← a.next it.fst
  match oa with
  | none => ok (none,⟨ia,it.snd⟩,fun z _ => {z with fst := backa z.fst none})
  | some x =>
    let (ob,ib) ← b.next it.snd
    match ob with
    | none => ok (none,⟨ia,ib⟩,fun z _ => {z with fst := backa z.fst none})
    | some y => ok (some (x,y),⟨ia,ib⟩,
        fun z op => {z with fst := backa z.fst (op.map Prod.fst)})

namespace Aeneas.Std

def core.bool.Bool.then {T F : Type} (fnInst : core.ops.function.FnOnce F Unit T)
    (condition : Bool) (f : F) : Result (Option T) :=
  if condition then do
    let value ← fnInst.call_once f ()
    ok (some value)
  else ok none

def core.option.Option.Insts.CoreCmpPartialEqOption.eq {T : Type}
    (inst : core.cmp.PartialEq T T) (left right : Option T) : Result Bool :=
  match left,right with
  | some a,some b => inst.eq a b
  | none,none => ok true
  | _,_ => ok false

end Aeneas.Std

def core.array.from_fn_loop {T F : Type} (inst : core.ops.function.FnMut F Usize T)
    (index : Nat) : (remaining : Nat) → F → Result (Aeneas.Data.ListN.ListN T remaining × F)
  | 0,f => ok (.nil,f)
  | n+1,f =>
    if h : index < 2^UScalarTy.Usize.numBits then do
      let (item,f') ← inst.call_mut f (Usize.ofNatCore index h)
      let (rest,f'') ← core.array.from_fn_loop inst (index+1) n f'
      ok (.cons item rest,f'')
    else fail .integerOverflow

def core.array.from_fn {T F : Type} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (f : F) : Result (Array T N) := do
  let (items,_) ← core.array.from_fn_loop inst 0 N.val f
  ok ⟨items⟩

def core.slice.Slice.chunks_exact_mut {T : Type} (s : Aeneas.Std.Slice T) (size : Usize) :
    Result (core.slice.iter.ChunksExactMut T × (core.slice.iter.ChunksExactMut T → Aeneas.Std.Slice T)) := do
  massert (size.val ≠ 0)
  ok (⟨s,0,size⟩,fun it => it.slice)

def core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next {T : Type}
    (it : core.slice.iter.ChunksExactMut T) : Result (Option (Aeneas.Std.Slice T) ×
      core.slice.iter.ChunksExactMut T ×
      (core.slice.iter.ChunksExactMut T → Option (Aeneas.Std.Slice T) → core.slice.iter.ChunksExactMut T)) :=
  if h : it.chunkSize.val > 0 ∧ it.index + it.chunkSize.val ≤ it.slice.length then
    let part := Aeneas.Std.Slice.from (it.slice.val.drop it.index |>.take it.chunkSize.val)
      (by have := it.slice.property; simp only [List.length_take,List.length_drop]; omega)
    ok (some part,{it with index := it.index+it.chunkSize.val},
      fun next op => match op with
      | none => next
      | some updated => {next with slice := next.slice.setSlice! it.index updated.val})
  else ok (none,it,fun next _ => next)

namespace Aeneas.Std

def core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice (T : Type) :
    MutableIterator (_root_.core.slice.iter.ChunksExactMut T) (Aeneas.Std.Slice T) :=
  ⟨_root_.core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next⟩

end Aeneas.Std

/-- Read-only chunks retain the unconsumed slice and the nonzero chunk size. -/
def core.slice.Slice.chunks {T : Type} (s : Aeneas.Std.Slice T) (size : Usize) :
    Result (core.slice.iter.Chunks T) := do
  massert (size.val ≠ 0)
  ok ⟨s,size⟩

def core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next {T : Type}
    (it : core.slice.iter.Chunks T) : Result (Option (Aeneas.Std.Slice T) × core.slice.iter.Chunks T) :=
  if it.slice.length = 0 then ok (none,it)
  else
    let count := min it.slice.length it.chunkSize.val
    let part := Aeneas.Std.Slice.from (it.slice.val.take count)
      (by have := it.slice.property; simp only [List.length_take]; omega)
    let rest := Aeneas.Std.Slice.from (it.slice.val.drop count)
      (by have := it.slice.property; simp only [List.length_drop]; omega)
    ok (some part,{it with slice := rest})

def core.slice.iter.Chunks.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedSlice.next_back {T : Type}
    (it : core.slice.iter.Chunks T) : Result (Option (Aeneas.Std.Slice T) × core.slice.iter.Chunks T) :=
  if it.slice.length = 0 then ok (none,it)
  else if it.chunkSize.val = 0 then fail .divisionByZero
  else
    let remainder := it.slice.length % it.chunkSize.val
    let count := if remainder ≠ 0 then remainder else it.chunkSize.val
    let split := it.slice.length-count
    let part := Aeneas.Std.Slice.from (it.slice.val.drop split)
      (by have := it.slice.property; simp only [List.length_drop]; omega)
    let rest := Aeneas.Std.Slice.from (it.slice.val.take split)
      (by have := it.slice.property; simp only [List.length_take]; omega)
    ok (some part,{it with slice := rest})
