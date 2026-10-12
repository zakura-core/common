import CommonFG62Digits
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
noncomputable def fgFactored
  (len : Usize) (f g : CommonFG62.field.pasta.safegcd.Signed62)
  (t : CommonFG62.field.pasta.safegcd.Trans2x2) :
  Result (CommonFG62.field.pasta.safegcd.Signed62 × CommonFG62.field.pasta.safegcd.Signed62) := do
  let ri ← core.ops.range.RangeInclusive.new 1#usize 5#usize
  let b ←
    core.ops.range.RangeInclusive.contains core.cmp.PartialOrdUsize
      core.cmp.PartialOrdUsize core.cmp.PartialOrdUsize ri len
  massert b
  let fi ← Array.index_usize f 0#usize
  let gi ← Array.index_usize g 0#usize
  let cf ← fgRowTerm t.u t.v fi gi
  let cg ← fgRowTerm t.q t.r fi gi
  let i12 ← lift (IScalar.hcast .U64 cf)
  let i13 ← CommonFG62.field.pasta.safegcd.MASK62
  let i14 ← lift (i12 &&& i13)
  massert (i14 = 0#u64)
  let i15 ← lift (IScalar.hcast .U64 cg)
  let i16 ← lift (i15 &&& i13)
  massert (i16 = 0#u64)
  let cf1 ← cf >>> 62#i32
  let cg1 ← cg >>> 62#i32
  let (o, iter) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
      { start := 1#usize, «end» := len }
  match o with
  | none =>
    let i17 ← lift (IScalar.cast .I64 cf1)
    let i18 ← lift (core.convert.num.FromI128I64.from i17)
    massert (cf1 = i18)
    let i19 ← lift (IScalar.cast .I64 cg1)
    let i20 ← lift (core.convert.num.FromI128I64.from i19)
    massert (cg1 = i20)
    let i21 ← len - 1#usize
    let i22 ← lift (IScalar.cast .I64 cf1)
    let a ← Array.update f i21 i22
    let i23 ← lift (IScalar.cast .I64 cg1)
    let a1 ← Array.update g i21 i23
    ok (a, a1)
  | some j =>
    let fi1 ← Array.index_usize f j
    let gi1 ← Array.index_usize g j
    let i23 ← fgRowTerm t.u t.v fi1 gi1
    let cf2 ← cf1 + i23
    let i30 ← fgRowTerm t.q t.r fi1 gi1
    let cg2 ← cg1 + i30
    let i31 ← lift (IScalar.hcast .U64 cf2)
    let i32 ← lift (i31 &&& i13)
    let i33 ← j - 1#usize
    let (_, index_mut_back) ← Array.index_mut_usize f i33
    let i34 ← lift (UScalar.hcast .I64 i32)
    let cf3 ← cf2 >>> 62#i32
    let i35 ← lift (IScalar.hcast .U64 cg2)
    let i36 ← lift (i35 &&& i13)
    let (_, index_mut_back1) ← Array.index_mut_usize g i33
    let i37 ← lift (UScalar.hcast .I64 i36)
    let cg3 ← cg2 >>> 62#i32
    let (o1, iter1) ←
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
    match o1 with
    | none =>
      let i38 ← lift (IScalar.cast .I64 cf3)
      let i39 ← lift (core.convert.num.FromI128I64.from i38)
      massert (cf3 = i39)
      let i40 ← lift (IScalar.cast .I64 cg3)
      let i41 ← lift (core.convert.num.FromI128I64.from i40)
      massert (cg3 = i41)
      let i42 ← len - 1#usize
      let a := index_mut_back i34
      let i43 ← lift (IScalar.cast .I64 cf3)
      let a1 ← Array.update a i42 i43
      let a2 := index_mut_back1 i37
      let i44 ← lift (IScalar.cast .I64 cg3)
      let a3 ← Array.update a2 i42 i44
      ok (a1, a3)
    | some j1 =>
      let a := index_mut_back i34
      let fi2 ← Array.index_usize a j1
      let a1 := index_mut_back1 i37
      let gi2 ← Array.index_usize a1 j1
      let i44 ← fgRowTerm t.u t.v fi2 gi2
      let cf4 ← cf3 + i44
      let i51 ← fgRowTerm t.q t.r fi2 gi2
      let cg4 ← cg3 + i51
      let i52 ← lift (IScalar.hcast .U64 cf4)
      let i53 ← lift (i52 &&& i13)
      let i54 ← j1 - 1#usize
      let (_, index_mut_back2) ← Array.index_mut_usize a i54
      let i55 ← lift (UScalar.hcast .I64 i53)
      let cf5 ← cf4 >>> 62#i32
      let i56 ← lift (IScalar.hcast .U64 cg4)
      let i57 ← lift (i56 &&& i13)
      let (_, index_mut_back3) ← Array.index_mut_usize a1 i54
      let i58 ← lift (UScalar.hcast .I64 i57)
      let cg5 ← cg4 >>> 62#i32
      let (o2, iter2) ←
        core.iter.range.IteratorRange.next core.iter.range.StepUsize iter1
      match o2 with
      | none =>
        let i59 ← lift (IScalar.cast .I64 cf5)
        let i60 ← lift (core.convert.num.FromI128I64.from i59)
        massert (cf5 = i60)
        let i61 ← lift (IScalar.cast .I64 cg5)
        let i62 ← lift (core.convert.num.FromI128I64.from i61)
        massert (cg5 = i62)
        let i63 ← len - 1#usize
        let a2 := index_mut_back2 i55
        let i64 ← lift (IScalar.cast .I64 cf5)
        let a3 ← Array.update a2 i63 i64
        let a4 := index_mut_back3 i58
        let i65 ← lift (IScalar.cast .I64 cg5)
        let a5 ← Array.update a4 i63 i65
        ok (a3, a5)
      | some j2 =>
        let a2 := index_mut_back2 i55
        let fi3 ← Array.index_usize a2 j2
        let a3 := index_mut_back3 i58
        let gi3 ← Array.index_usize a3 j2
        let i65 ← fgRowTerm t.u t.v fi3 gi3
        let cf6 ← cf5 + i65
        let i72 ← fgRowTerm t.q t.r fi3 gi3
        let cg6 ← cg5 + i72
        let i73 ← lift (IScalar.hcast .U64 cf6)
        let i74 ← lift (i73 &&& i13)
        let i75 ← j2 - 1#usize
        let (_, index_mut_back4) ← Array.index_mut_usize a2 i75
        let i76 ← lift (UScalar.hcast .I64 i74)
        let cf7 ← cf6 >>> 62#i32
        let i77 ← lift (IScalar.hcast .U64 cg6)
        let i78 ← lift (i77 &&& i13)
        let (_, index_mut_back5) ← Array.index_mut_usize a3 i75
        let i79 ← lift (UScalar.hcast .I64 i78)
        let cg7 ← cg6 >>> 62#i32
        let (o3, iter3) ←
          core.iter.range.IteratorRange.next core.iter.range.StepUsize iter2
        match o3 with
        | none =>
          let i80 ← lift (IScalar.cast .I64 cf7)
          let i81 ← lift (core.convert.num.FromI128I64.from i80)
          massert (cf7 = i81)
          let i82 ← lift (IScalar.cast .I64 cg7)
          let i83 ← lift (core.convert.num.FromI128I64.from i82)
          massert (cg7 = i83)
          let i84 ← len - 1#usize
          let a4 := index_mut_back4 i76
          let i85 ← lift (IScalar.cast .I64 cf7)
          let a5 ← Array.update a4 i84 i85
          let a6 := index_mut_back5 i79
          let i86 ← lift (IScalar.cast .I64 cg7)
          let a7 ← Array.update a6 i84 i86
          ok (a5, a7)
        | some j3 =>
          let a4 := index_mut_back4 i76
          let fi4 ← Array.index_usize a4 j3
          let a5 := index_mut_back5 i79
          let gi4 ← Array.index_usize a5 j3
          let i86 ← fgRowTerm t.u t.v fi4 gi4
          let cf8 ← cf7 + i86
          let i93 ← fgRowTerm t.q t.r fi4 gi4
          let cg8 ← cg7 + i93
          let i94 ← lift (IScalar.hcast .U64 cf8)
          let i95 ← lift (i94 &&& i13)
          let i96 ← j3 - 1#usize
          let (_, index_mut_back6) ← Array.index_mut_usize a4 i96
          let i97 ← lift (UScalar.hcast .I64 i95)
          let cf9 ← cf8 >>> 62#i32
          let i98 ← lift (IScalar.hcast .U64 cg8)
          let i99 ← lift (i98 &&& i13)
          let (_, index_mut_back7) ← Array.index_mut_usize a5 i96
          let i100 ← lift (UScalar.hcast .I64 i99)
          let cg9 ← cg8 >>> 62#i32
          let (o4, _) ←
            core.iter.range.IteratorRange.next core.iter.range.StepUsize iter3
          match o4 with
          | none =>
            let i101 ← lift (IScalar.cast .I64 cf9)
            let i102 ← lift (core.convert.num.FromI128I64.from i101)
            massert (cf9 = i102)
            let i103 ← lift (IScalar.cast .I64 cg9)
            let i104 ← lift (core.convert.num.FromI128I64.from i103)
            massert (cg9 = i104)
            let i105 ← len - 1#usize
            let a6 := index_mut_back6 i97
            let i106 ← lift (IScalar.cast .I64 cf9)
            let a7 ← Array.update a6 i105 i106
            let a8 := index_mut_back7 i100
            let i107 ← lift (IScalar.cast .I64 cg9)
            let a9 ← Array.update a8 i105 i107
            ok (a7, a9)
          | some j4 =>
            let a6 := index_mut_back6 i97
            let fi5 ← Array.index_usize a6 j4
            let a7 := index_mut_back7 i100
            let gi5 ← Array.index_usize a7 j4
            let i107 ← fgRowTerm t.u t.v fi5 gi5
            let cf10 ← cf9 + i107
            let i114 ← fgRowTerm t.q t.r fi5 gi5
            let cg10 ← cg9 + i114
            let i115 ← j4 - 1#usize
            let _ ← Array.index_mut_usize a6 i115
            let _ ← cf10 >>> 62#i32
            let _ ← Array.index_mut_usize a7 i115
            let _ ← cg10 >>> 62#i32
            fail Error.panic


theorem fg_factored_bridge (len : Usize) (f g : CommonFG62.field.pasta.safegcd.Signed62)
    (t : CommonFG62.field.pasta.safegcd.Trans2x2) :
    CommonFG62.field.pasta.safegcd.update_fg_62_var len f g t = fgFactored len f g t := by
  unfold CommonFG62.field.pasta.safegcd.update_fg_62_var fgFactored fgRowTerm
  simp only [lift,bind_ok,Std.bind_assoc]
  try rfl

#print axioms fg_factored_bridge
end UdonVerify.CommonSigned62
