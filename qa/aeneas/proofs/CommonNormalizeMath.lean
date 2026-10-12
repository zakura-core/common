import CommonNormalizeCarry

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem normalize_first_range (r m : Int) (hm : 0 < m) (hr : -2 * m < r ∧ r < m) :
    -m < r + (if r < 0 then m else 0) ∧ r + (if r < 0 then m else 0) < m := by
  split_ifs <;> constructor <;> omega

theorem normalize_signed_range (r m : Int) (hr : -m < r ∧ r < m) (negative : Prop) [Decidable negative] :
    -m < (if negative then -r else r) ∧ (if negative then -r else r) < m := by
  split_ifs <;> constructor <;> omega

theorem normalize_final_range (r m : Int) (hm : 0 < m) (hr : -m < r ∧ r < m) :
    0 ≤ r + (if r < 0 then m else 0) ∧ r + (if r < 0 then m else 0) < m := by
  split_ifs <;> constructor <;> omega

theorem normalize_add_congruence (r m : Int) :
    Int.ModEq m (r + (if r < 0 then m else 0)) r := by
  split_ifs <;> simp [Int.ModEq, Int.add_emod]

theorem normalize_canonical_digits {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (r : Signed62) (hn : signed62Normalized r)
    (hr : 0 ≤ signed62Value r ∧ signed62Value r < signed62Value params.modulus) :
    ∀ k : Fin 5, 0 ≤ r[k.val]!.val ∧ r[k.val]!.val < signedRadix := by
  have hrange : -2 * signed62Value params.modulus < signed62Value r ∧
      signed62Value r < signed62Value params.modulus := by
    have := params.positive
    constructor <;> omega
  have ht := (inv_coefficient_digit_bounds inst params r hn hrange).2
  have hs := signed62_sign_iff r hn
  have htop0 : 0 ≤ r[4]!.val := by omega
  have htop : r[4]!.val < signedRadix := by
    have := abs_le.mp ht
    norm_num only [signedRadix]
    omega
  intro k
  by_cases hk : k.val < 4
  · exact hn ⟨k.val, hk⟩
  · have hk4 : k.val = 4 := by have := k.isLt; omega
    rw [hk4]
    exact ⟨htop0, htop⟩

#print axioms normalize_first_range
#print axioms normalize_signed_range
#print axioms normalize_final_range
#print axioms normalize_add_congruence
#print axioms normalize_canonical_digits
end UdonVerify.CommonSigned62
