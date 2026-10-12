import CommonCoeffRows
import CommonCoeffValue

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem coeff_sign_shift_eq (value : I64) : value >>> 63#i32 = ok (signMask value) :=
  fg_result_eq (signed_sign_mask_spec value)

def updateDEFlat {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (d e : Signed62) (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2) : Result (Signed62 × Signed62) := do
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst d (CommonInvHelpers.toStr "d")
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst e (CommonInvHelpers.toStr "e")
  let md ← coeffSignStart t.u t.v d[4]! e[4]!
  let me ← coeffSignStart t.q t.r d[4]! e[4]!
  let cd ← fgRowTerm t.u t.v d[0]! e[0]!
  let ce ← fgRowTerm t.q t.r d[0]! e[0]!
  let mu ← inst.MU
  let md1 := coeffCorrectWord mu cd md
  let me1 := coeffCorrectWord mu ce me
  let modulus ← inst.MODULUS_62
  let modD0 ← coeffModTerm modulus[0]! md1
  let cd0 ← cd + modD0
  let modE0 ← coeffModTerm modulus[0]! me1
  let ce0 ← ce + modE0
  massert (IScalar.hcast .U64 cd0 &&& 4611686018427387903#u64 = 0#u64)
  massert (IScalar.hcast .U64 ce0 &&& 4611686018427387903#u64 = 0#u64)
  let cdCarry0 ← cd0 >>> 62#i32
  let ceCarry0 ← ce0 >>> 62#i32
  let rowD1 ← fgRowTerm t.u t.v d[1]! e[1]!
  let cdRow1 ← cdCarry0 + rowD1
  let rowE1 ← fgRowTerm t.q t.r d[1]! e[1]!
  let ceRow1 ← ceCarry0 + rowE1
  let modD1 ← coeffModTerm modulus[1]! md1
  let cd1 ← cdRow1 + modD1
  let modE1 ← coeffModTerm modulus[1]! me1
  let ce1 ← ceRow1 + modE1
  let d1 := d.set 0#usize (fgRowDigit cd1)
  let cdCarry1 ← cd1 >>> 62#i32
  let e1 := e.set 0#usize (fgRowDigit ce1)
  let ceCarry1 ← ce1 >>> 62#i32
  let rowD2 ← fgRowTerm t.u t.v d[2]! e[2]!
  let cdRow2 ← cdCarry1 + rowD2
  let rowE2 ← fgRowTerm t.q t.r d[2]! e[2]!
  let ceRow2 ← ceCarry1 + rowE2
  let modD2 ← core.convert.num.FromI128I64.from md1 <<< 1#i32
  let cd2 ← cdRow2 + modD2
  let modE2 ← core.convert.num.FromI128I64.from me1 <<< 1#i32
  let ce2 ← ceRow2 + modE2
  let d2 := d1.set 1#usize (fgRowDigit cd2)
  let cdCarry2 ← cd2 >>> 62#i32
  let e2 := e1.set 1#usize (fgRowDigit ce2)
  let ceCarry2 ← ce2 >>> 62#i32
  let rowD3 ← fgRowTerm t.u t.v d[3]! e[3]!
  let cd3 ← cdCarry2 + rowD3
  let rowE3 ← fgRowTerm t.q t.r d[3]! e[3]!
  let ce3 ← ceCarry2 + rowE3
  let d3 := d2.set 2#usize (fgRowDigit cd3)
  let cdCarry3 ← cd3 >>> 62#i32
  let e3 := e2.set 2#usize (fgRowDigit ce3)
  let ceCarry3 ← ce3 >>> 62#i32
  let rowD4 ← fgRowTerm t.u t.v d[4]! e[4]!
  let cdRow4 ← cdCarry3 + rowD4
  let rowE4 ← fgRowTerm t.q t.r d[4]! e[4]!
  let ceRow4 ← ceCarry3 + rowE4
  let modD4 ← core.convert.num.FromI128I64.from md1 <<< 6#i32
  let cd4 ← cdRow4 + modD4
  let modE4 ← core.convert.num.FromI128I64.from me1 <<< 6#i32
  let ce4 ← ceRow4 + modE4
  let d4 := d3.set 3#usize (fgRowDigit cd4)
  let cdCarry4 ← cd4 >>> 62#i32
  let e4 := e3.set 3#usize (fgRowDigit ce4)
  let ceCarry4 ← ce4 >>> 62#i32
  let dtail ← fgRowTail cdCarry4
  let etail ← fgRowTail ceCarry4
  let dOut := d4.set 4#usize dtail
  let eOut := e4.set 4#usize etail
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst dOut (CommonInvHelpers.toStr "new d")
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst eOut (CommonInvHelpers.toStr "new e")
  ok (dOut, eOut)

theorem update_de_flat_bridge {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (d e : Signed62) (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2) :
    CommonInvHelpers.field.pasta.safegcd.update_de_62 inst d e t = updateDEFlat inst d e t := by
  unfold CommonInvHelpers.field.pasta.safegcd.update_de_62 updateDEFlat
    coeffSignStart fgRowTerm coeffModTerm fgRowTail coeffCorrectWord coeffResidueDigit coeffResidue fgRowDigit
  simp (config := { maxSteps := 1000000 }) [lift, Bind.bind, bind_ok, Std.bind_assoc,
    fg_index_eq, fg_update_eq, coeff_sign_shift_eq, inv_helpers_mask_eq,
    core.num.U64.wrapping_add, core.num.U64.wrapping_mul, core.num.I64.wrapping_sub]

#print axioms coeff_sign_shift_eq
#print axioms update_de_flat_bridge
end UdonVerify.CommonSigned62
