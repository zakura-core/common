import CommonInversionFirst

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option allowUnsafeReducibility true
attribute [local irreducible] Std.bind

theorem inversion_first_bind_eq {P α : Type}
    (inst : CommonInversion.field.pasta.safegcd.InvParams P) (modulus g r2 : Signed62)
    (k : InversionReady → Result α) :
    (do let first ← nativeInversionFirst inst modulus g r2; k first) =
    (do
      let f0 ← Array.index_usize modulus 0#usize
      let g0 ← Array.index_usize g 0#usize
      let (t, eta) ← CommonInversion.field.pasta.safegcd.divsteps_62_var (-1)#i64
        (IScalar.hcast .U64 f0) (IScalar.hcast .U64 g0)
      let (f1, g1) ← CommonInversion.field.pasta.safegcd.update_fg_62_first inst modulus g t
      let zero ← CommonInversion.field.pasta.safegcd.is_zero g1 5#usize
      massert (¬ zero)
      let (d, e) ← CommonInversion.field.pasta.safegcd.update_de_62_first inst r2 t
      CommonInversion.field.pasta.safegcd.checks.assert_fg_range inst f1 g1 5#usize
      let (f2, g2, len) ← CommonInversion.field.pasta.safegcd.shrink_len f1 g1 5#usize
      k ⟨f2, g2, d, e, eta, len⟩) := by
  unfold nativeInversionFirst nativeInversionFirstFG
  simp only [Bind.bind, Std.bind_assoc, bind_ok]
  apply congrArg (Std.bind (Array.index_usize modulus 0#usize))
  funext f0
  apply congrArg (Std.bind (Array.index_usize g 0#usize))
  funext g0
  apply congrArg (Std.bind (CommonInversion.field.pasta.safegcd.divsteps_62_var (-1)#i64
    (IScalar.hcast .U64 f0) (IScalar.hcast .U64 g0)))
  funext tm
  rcases tm with ⟨t, eta⟩
  simp only [Std.uncurry_apply_pair]
  apply congrArg (Std.bind (CommonInversion.field.pasta.safegcd.update_fg_62_first inst modulus g t))
  funext fg
  rcases fg with ⟨f1, g1⟩
  simp only [Std.uncurry_apply_pair]
  apply congrArg (Std.bind (CommonInversion.field.pasta.safegcd.is_zero g1 5#usize))
  funext zero
  apply congrArg (Std.bind (massert (¬ zero)))
  funext checked
  apply congrArg (Std.bind (CommonInversion.field.pasta.safegcd.update_de_62_first inst r2 t))
  funext de
  rcases de with ⟨d, e⟩
  simp only [Std.uncurry_apply_pair, Bind.bind, Std.bind_assoc, bind_ok]
  apply congrArg (Std.bind (CommonInversion.field.pasta.safegcd.checks.assert_fg_range inst f1 g1 5#usize))
  funext rangeChecked
  apply congrArg (Std.bind (CommonInversion.field.pasta.safegcd.shrink_len f1 g1 5#usize))
  funext shrunken
  rcases shrunken with ⟨f2, g2, len⟩
  simp only [Std.uncurry_apply_pair, Bind.bind, Std.bind_assoc, bind_ok]

#print axioms inversion_first_bind_eq
end UdonVerify.CommonSigned62
