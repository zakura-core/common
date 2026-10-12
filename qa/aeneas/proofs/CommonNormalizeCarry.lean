import CommonNormalizeWords

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def make62 (r0 r1 r2 r3 r4 : I64) : Signed62 := Array.make 5#usize [r0, r1, r2, r3, r4]

@[simp] theorem make62_get0 (r0 r1 r2 r3 r4 : I64) : (make62 r0 r1 r2 r3 r4)[0]! = r0 := rfl
@[simp] theorem make62_get1 (r0 r1 r2 r3 r4 : I64) : (make62 r0 r1 r2 r3 r4)[1]! = r1 := rfl
@[simp] theorem make62_get2 (r0 r1 r2 r3 r4 : I64) : (make62 r0 r1 r2 r3 r4)[2]! = r2 := rfl
@[simp] theorem make62_get3 (r0 r1 r2 r3 r4 : I64) : (make62 r0 r1 r2 r3 r4)[3]! = r3 := rfl
@[simp] theorem make62_get4 (r0 r1 r2 r3 r4 : I64) : (make62 r0 r1 r2 r3 r4)[4]! = r4 := rfl

def normalizeCarry (r : Signed62) : Result Signed62 := do
  let c0 ← r[0]! >>> 62#i32
  let a1 ← r[1]! + c0
  let c1 ← a1 >>> 62#i32
  let a2 ← r[2]! + c1
  let c2 ← a2 >>> 62#i32
  let a3 ← r[3]! + c2
  let c3 ← a3 >>> 62#i32
  let a4 ← r[4]! + c3
  ok (make62 (normalizeDigit r[0]!) (normalizeDigit a1) (normalizeDigit a2) (normalizeDigit a3) a4)

@[step]
theorem normalize_carry_spec (r : Signed62)
    (hr : ∀ k : Fin 4, -2 * signedRadix + 2 ≤ r[k.val]!.val ∧ r[k.val]!.val ≤ 2 * signedRadix - 2)
    (ht : |r[4]!.val| ≤ 1024) :
    normalizeCarry r ⦃ out => signed62Normalized out ∧ signed62Value out = signed62Value r ∧
      |out[4]!.val| ≤ 1026 ⦄ := by
  have h0 := hr ⟨0, by decide⟩
  have h1 := hr ⟨1, by decide⟩
  have h2 := hr ⟨2, by decide⟩
  have h3 := hr ⟨3, by decide⟩
  change -2 * signedRadix + 2 ≤ r[0]!.val ∧ r[0]!.val ≤ 2 * signedRadix - 2 at h0
  change -2 * signedRadix + 2 ≤ r[1]!.val ∧ r[1]!.val ≤ 2 * signedRadix - 2 at h1
  change -2 * signedRadix + 2 ≤ r[2]!.val ∧ r[2]!.val ≤ 2 * signedRadix - 2 at h2
  change -2 * signedRadix + 2 ≤ r[3]!.val ∧ r[3]!.val ≤ 2 * signedRadix - 2 at h3
  have h4 := abs_le.mp ht
  unfold normalizeCarry
  step -grind with (normalize_shift_spec r[0]!) as ⟨c0, hc0⟩
  have hc0B : -2 ≤ c0.val ∧ c0.val ≤ 1 := by
    rw [hc0]
    norm_num only [signedRadix] at h0 ⊢
    constructor <;> omega
  step -grind with (normalize_i64_add_spec r[1]! c0 (-2 * signedRadix) (2 * signedRadix - 1)
    (by omega) (by omega) (by norm_num [signedRadix])) as ⟨a1, ha1, ha1L, ha1H⟩
  step -grind with (normalize_shift_spec a1) as ⟨c1, hc1⟩
  have hc1B : -2 ≤ c1.val ∧ c1.val ≤ 1 := by
    rw [hc1]
    norm_num only [signedRadix] at ha1L ha1H ⊢
    constructor <;> omega
  step -grind with (normalize_i64_add_spec r[2]! c1 (-2 * signedRadix) (2 * signedRadix - 1)
    (by omega) (by omega) (by norm_num [signedRadix])) as ⟨a2, ha2, ha2L, ha2H⟩
  step -grind with (normalize_shift_spec a2) as ⟨c2, hc2⟩
  have hc2B : -2 ≤ c2.val ∧ c2.val ≤ 1 := by
    rw [hc2]
    norm_num only [signedRadix] at ha2L ha2H ⊢
    constructor <;> omega
  step -grind with (normalize_i64_add_spec r[3]! c2 (-2 * signedRadix) (2 * signedRadix - 1)
    (by omega) (by omega) (by norm_num [signedRadix])) as ⟨a3, ha3, ha3L, ha3H⟩
  step -grind with (normalize_shift_spec a3) as ⟨c3, hc3⟩
  have hc3B : -2 ≤ c3.val ∧ c3.val ≤ 1 := by
    rw [hc3]
    norm_num only [signedRadix] at ha3L ha3H ⊢
    constructor <;> omega
  step -grind with (normalize_i64_add_spec r[4]! c3 (-1026) 1026
    (by omega) (by omega) (by norm_num)) as ⟨a4, ha4, ha4L, ha4H⟩
  try simp only [WP.spec_ok]
  have hd0 := normalize_digit_value r[0]!
  have hd1 := normalize_digit_value a1
  have hd2 := normalize_digit_value a2
  have hd3 := normalize_digit_value a3
  refine ⟨?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · simpa only [make62_get0] using hd0.2
    · simpa only [make62_get1] using hd1.2
    · simpa only [make62_get2] using hd2.2
    · simpa only [make62_get3] using hd3.2
  · simp only [signed62Value, make62_get0, make62_get1, make62_get2, make62_get3, make62_get4,
      hd0.1, hd1.1, hd2.1, hd3.1]
    have e0 := Int.emod_add_ediv r[0]!.val signedRadix
    have e1 := Int.emod_add_ediv a1.val signedRadix
    have e2 := Int.emod_add_ediv a2.val signedRadix
    have e3 := Int.emod_add_ediv a3.val signedRadix
    rw [← hc0] at e0
    rw [← hc1] at e1
    rw [← hc2] at e2
    rw [← hc3] at e3
    norm_num only [signedRadix] at e0 e1 e2 e3 ⊢
    omega
  · simp only [make62_get4, abs_le]
    exact ⟨ha4L, ha4H⟩

#print axioms make62_get0
#print axioms make62_get1
#print axioms make62_get2
#print axioms make62_get3
#print axioms make62_get4
#print axioms normalize_carry_spec
end UdonVerify.CommonSigned62
