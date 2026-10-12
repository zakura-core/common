import CommonCoeffTerminalPrefix

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def terminalCoeffColumn1 (u v d e m md : I64) (cd : I128) : Result CoeffColumn := do
  let row ← fgRowTerm u v d e
  let add ← cd + row
  let mod ← coeffModTerm m md
  let acc ← add + mod
  let carry ← acc >>> 62#i32
  ok ⟨acc, acc, carry, carry⟩

@[step]
theorem terminal_coeff_column1_spec (u v d e m md : I64) (cd : I128)
    (huv : |u.val| + |v.val| ≤ signedRadix)
    (hd : |d.val| ≤ signedRadix) (he : |e.val| ≤ signedRadix) (hm : |m.val| ≤ signedRadix)
    (hmd : |md.val| ≤ 2 * signedRadix) (hcd : |cd.val| ≤ 3 * signedRadix + 5) :
    terminalCoeffColumn1 u v d e m md cd ⦃ out =>
      out.accD = out.accE ∧ out.carryD = out.carryE ∧
      CoeffColumnPost (cd.val + u.val * d.val + v.val * e.val + m.val * md.val)
        (cd.val + u.val * d.val + v.val * e.val + m.val * md.val) (3 * signedRadix + 5) out ⦄ := by
  unfold terminalCoeffColumn1
  step -grind with (fg_row_term_spec u v d e huv hd he) as ⟨row, hrow, hrowBound⟩
  step -grind with (coeff_add_row_spec cd row hcd hrowBound) as ⟨add, hadd, haddBound⟩
  step -grind with (coeff_mod_term_spec m md hm hmd) as ⟨mod, hmod, hmodBound⟩
  step -grind with (coeff_add_mod_spec add mod haddBound hmodBound) as ⟨acc, hacc, haccBound⟩
  step -grind with (coeff_shift_spec acc
    (by norm_num only [signedRadix] at haccBound ⊢; omega)) as ⟨carry, hcarry, hcarryBound⟩
  try simp only [WP.spec_ok]
  have hexact : acc.val = cd.val + u.val * d.val + v.val * e.val + m.val * md.val := by
    rw [hacc, hadd, hrow, hmod]
    ring
  exact ⟨hexact, hexact, hcarry, hcarry, hcarryBound, hcarryBound⟩

#print axioms terminal_coeff_column1_spec

def terminalCoeffColumn2 (u v d e m md : I64) (cd : I128) : Result CoeffColumn := do
  let row ← fgRowTerm u v d e
  let add ← cd + row
  let mod ← core.convert.num.FromI128I64.from md <<< 1#i32
  let acc ← add + mod
  let carry ← acc >>> 62#i32
  ok ⟨acc, acc, carry, carry⟩

@[step]
theorem terminal_coeff_column2_spec (u v d e m md : I64) (cd : I128)
    (huv : |u.val| + |v.val| ≤ signedRadix)
    (hd : |d.val| ≤ signedRadix) (he : |e.val| ≤ signedRadix) (hm : |m.val| ≤ signedRadix)
    (hmd : |md.val| ≤ 2 * signedRadix) (hcd : |cd.val| ≤ 3 * signedRadix + 5) :
    terminalCoeffColumn2 u v d e m md cd ⦃ out =>
      out.accD = out.accE ∧ out.carryD = out.carryE ∧
      CoeffColumnPost (cd.val + u.val * d.val + v.val * e.val + 2 * md.val)
        (cd.val + u.val * d.val + v.val * e.val + 2 * md.val) (3 * signedRadix + 5) out ⦄ := by
  unfold terminalCoeffColumn2
  step -grind with (fg_row_term_spec u v d e huv hd he) as ⟨row, hrow, hrowBound⟩
  step -grind with (coeff_add_row_spec cd row hcd hrowBound) as ⟨add, hadd, haddBound⟩
  step -grind with (fg_widen_shift_spec md 1#i32 (Or.inl rfl)) as ⟨mod, hmod⟩
  change mod.val = md.val * 2 at hmod
  have hmodBound : |mod.val| ≤ 2 * signedRadix ^ 2 := by
    rw [hmod, abs_mul]
    norm_num
    norm_num only [signedRadix] at hmd ⊢
    omega
  step -grind with (coeff_add_mod_spec add mod haddBound hmodBound) as ⟨acc, hacc, haccBound⟩
  step -grind with (coeff_shift_spec acc
    (by norm_num only [signedRadix] at haccBound ⊢; omega)) as ⟨carry, hcarry, hcarryBound⟩
  try simp only [WP.spec_ok]
  have hexact : acc.val = cd.val + u.val * d.val + v.val * e.val + 2 * md.val := by
    rw [hacc, hadd, hrow, hmod]
    ring
  exact ⟨hexact, hexact, hcarry, hcarry, hcarryBound, hcarryBound⟩

#print axioms terminal_coeff_column2_spec

def terminalCoeffColumn3 (u v d e m md : I64) (cd : I128) : Result CoeffColumn := do
  let row ← fgRowTerm u v d e
  let acc ← cd + row
  let carry ← acc >>> 62#i32
  ok ⟨acc, acc, carry, carry⟩

@[step]
theorem terminal_coeff_column3_spec (u v d e m md : I64) (cd : I128)
    (huv : |u.val| + |v.val| ≤ signedRadix)
    (hd : |d.val| ≤ signedRadix) (he : |e.val| ≤ signedRadix) (hm : |m.val| ≤ signedRadix)
    (hmd : |md.val| ≤ 2 * signedRadix) (hcd : |cd.val| ≤ 3 * signedRadix + 5) :
    terminalCoeffColumn3 u v d e m md cd ⦃ out =>
      out.accD = out.accE ∧ out.carryD = out.carryE ∧
      CoeffColumnPost (cd.val + u.val * d.val + v.val * e.val)
        (cd.val + u.val * d.val + v.val * e.val) (3 * signedRadix + 5) out ⦄ := by
  unfold terminalCoeffColumn3
  step -grind with (fg_row_term_spec u v d e huv hd he) as ⟨row, hrow, hrowBound⟩
  step -grind with (coeff_add_row_spec cd row hcd hrowBound) as ⟨acc, hacc, haccBound⟩
  step -grind with (coeff_shift_spec acc
    (by norm_num only [signedRadix] at haccBound ⊢; omega)) as ⟨carry, hcarry, hcarryBound⟩
  try simp only [WP.spec_ok]
  have hexact : acc.val = cd.val + u.val * d.val + v.val * e.val := by
    rw [hacc, hrow]
    ring
  exact ⟨hexact, hexact, hcarry, hcarry, hcarryBound, hcarryBound⟩

#print axioms terminal_coeff_column3_spec

def terminalCoeffColumn4 (u v d e m md : I64) (cd : I128) : Result CoeffColumn := do
  let row ← fgRowTerm u v d e
  let add ← cd + row
  let mod ← core.convert.num.FromI128I64.from md <<< 6#i32
  let acc ← add + mod
  let carry ← acc >>> 62#i32
  ok ⟨acc, acc, carry, carry⟩

@[step]
theorem terminal_coeff_column4_spec (u v d e m md : I64) (cd : I128)
    (huv : |u.val| + |v.val| ≤ signedRadix)
    (hd : |d.val| ≤ 256) (he : |e.val| ≤ 256) (hm : |m.val| ≤ signedRadix)
    (hmd : |md.val| ≤ 2 * signedRadix) (hcd : |cd.val| ≤ 3 * signedRadix + 5) :
    terminalCoeffColumn4 u v d e m md cd ⦃ out =>
      out.accD = out.accE ∧ out.carryD = out.carryE ∧
      CoeffColumnPost (cd.val + u.val * d.val + v.val * e.val + 64 * md.val)
        (cd.val + u.val * d.val + v.val * e.val + 64 * md.val) (388) out ⦄ := by
  unfold terminalCoeffColumn4
  step -grind with (coeff_top_term_spec u v d e huv hd he) as ⟨row, hrow, hrowBound⟩
  step -grind with (coeff_top_add_row_spec cd row hcd hrowBound) as ⟨add, hadd, haddBound⟩
  step -grind with (fg_widen_shift_spec md 6#i32 (Or.inr rfl)) as ⟨mod, hmod⟩
  change mod.val = md.val * 64 at hmod
  have hmodBound : |mod.val| ≤ 128 * signedRadix := by
    rw [hmod, abs_mul]
    norm_num
    norm_num only [signedRadix] at hmd ⊢
    omega
  step -grind with (coeff_top_add_mod_spec add mod haddBound hmodBound) as ⟨acc, hacc, haccBound⟩
  step -grind with (coeff_top_shift_spec acc
    (by norm_num only [signedRadix] at haccBound ⊢; omega)) as ⟨carry, hcarry, hcarryBound⟩
  try simp only [WP.spec_ok]
  have hexact : acc.val = cd.val + u.val * d.val + v.val * e.val + 64 * md.val := by
    rw [hacc, hadd, hrow, hmod]
    ring
  exact ⟨hexact, hexact, hcarry, hcarry, hcarryBound, hcarryBound⟩

#print axioms terminal_coeff_column4_spec

end UdonVerify.CommonSigned62
