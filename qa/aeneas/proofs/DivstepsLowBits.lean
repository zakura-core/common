import DivstepsMatrix
import Mathlib.Data.Int.ModEq

namespace UdonVerify.SafeGcd
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

/-- The unsigned-word recurrence, expressed over integers before connecting
    its wrapping operations to the extracted Rust scalar model. -/
def lowStep (state : State) : State :=
  match chooseBranch state.delta state.g with
  | .swap => ⟨1 - state.delta, state.g, ((state.g - state.f) % (2 ^ 64)) / 2⟩
  | .add => ⟨state.delta + 1, state.f, ((state.g + state.f) % (2 ^ 64)) / 2⟩
  | .even => ⟨state.delta + 1, state.f, state.g / 2⟩

def LowMatches (bits : Nat) (full low : State) : Prop :=
  low.delta = full.delta ∧
    low.f ≡ full.f [ZMOD (2 ^ bits)] ∧ low.g ≡ full.g [ZMOD (2 ^ bits)]

def iterateLow : Nat → State → State
  | 0, state => state
  | n + 1, state => lowStep (iterateLow n state)

theorem modEq_parity (bits : Nat) (a b : Int)
    (h : a ≡ b [ZMOD (2 ^ (bits + 1))]) : a % 2 = b % 2 := by
  have htwo : (2 : Int) ∣ 2 ^ (bits + 1) := by
    simpa only [pow_one] using pow_dvd_pow (2 : Int) (by omega : 1 ≤ bits + 1)
  exact h.of_dvd htwo

theorem modEq_half (bits : Nat) (a b : Int)
    (ha : a % 2 = 0) (hb : b % 2 = 0)
    (h : a ≡ b [ZMOD (2 ^ (bits + 1))]) :
    a / 2 ≡ b / 2 [ZMOD (2 ^ bits)] := by
  have htwice : 2 * (a / 2) ≡ 2 * (b / 2) [ZMOD (2 * 2 ^ bits)] := by
    rw [half_exact a ha, half_exact b hb]
    simpa only [pow_succ, mul_comm] using h
  exact Int.ModEq.mul_left_cancel' (by decide : (2 : Int) ≠ 0) htwice

theorem wrapped_modEq (bits : Nat) (value : Int) (hbits : bits ≤ 64) :
    value % (2 ^ 64) ≡ value [ZMOD (2 ^ bits)] := by
  exact (Int.mod_modEq value (2 ^ 64)).of_dvd (pow_dvd_pow (2 : Int) hbits)

theorem low_step_matches (bits : Nat) (full low : State) (hbits : bits < 64)
    (hodd : full.f % 2 = 1) (hmatch : LowMatches (bits + 1) full low) :
    LowMatches bits (integerStep full) (lowStep low) := by
  rcases hmatch with ⟨hdelta, hf, hg⟩
  have hfParity := modEq_parity bits low.f full.f hf
  have hgParity := modEq_parity bits low.g full.g hg
  have hchoice : chooseBranch low.delta low.g = chooseBranch full.delta full.g := by
    simp only [chooseBranch, hdelta, hgParity]
  have hreduce : (2 : Int) ^ bits ∣ 2 ^ (bits + 1) := pow_dvd_pow 2 (by omega)
  have hwrap (value : Int) := wrapped_modEq (bits + 1) value (by omega)
  unfold LowMatches lowStep integerStep
  rw [hchoice]
  unfold chooseBranch
  split_ifs with heven hpositive
  · dsimp only
    refine ⟨by omega, hf.of_dvd hreduce, ?_⟩
    exact modEq_half bits low.g full.g (by omega) heven hg
  · dsimp only
    have hgOdd : full.g % 2 = 1 := by omega
    have hwrapped := (hwrap (low.g - low.f)).trans (hg.sub hf)
    have hwrappedEven : ((low.g - low.f) % (2 ^ 64)) % 2 = 0 := by
      have h := modEq_parity bits _ _ hwrapped
      omega
    refine ⟨by omega, hg.of_dvd hreduce, ?_⟩
    exact modEq_half bits _ _ hwrappedEven (by omega) hwrapped
  · dsimp only
    have hgOdd : full.g % 2 = 1 := by omega
    have hwrapped := (hwrap (low.g + low.f)).trans (hg.add hf)
    have hwrappedEven : ((low.g + low.f) % (2 ^ 64)) % 2 = 0 := by
      have h := modEq_parity bits _ _ hwrapped
      omega
    refine ⟨by omega, hf.of_dvd hreduce, ?_⟩
    exact modEq_half bits _ _ hwrappedEven (by omega) hwrapped

#print axioms low_step_matches

theorem low_iterate_matches (bits n : Nat) (hbits : bits ≤ 64) (hn : n ≤ bits) (full low : State)
    (hodd : full.f % 2 = 1) (hmatch : LowMatches bits full low) :
    LowMatches (bits - n) (iterate n full) (iterateLow n low) := by
  induction n with
  | zero => simpa only [Nat.sub_zero, iterate, iterateLow] using hmatch
  | succ n ih =>
      have hprevious := ih (by omega)
      have hremaining : bits - (n + 1) + 1 = bits - n := by omega
      have h := low_step_matches (bits - (n + 1)) (iterate n full) (iterateLow n low)
        (by omega) (iterate_odd n full hodd) (by simpa only [hremaining] using hprevious)
      simpa only [iterate, iterateLow] using h

theorem low_iterate_branch (bits n : Nat) (hbits : bits ≤ 64) (hn : n < bits) (full low : State)
    (hodd : full.f % 2 = 1) (hmatch : LowMatches bits full low) :
    chooseBranch (iterateLow n low).delta (iterateLow n low).g =
      chooseBranch (iterate n full).delta (iterate n full).g := by
  have h := low_iterate_matches bits n hbits (by omega) full low hodd hmatch
  have hremaining : bits - n = (bits - (n + 1)) + 1 := by omega
  have hg := modEq_parity (bits - (n + 1)) _ _ (by simpa only [hremaining] using h.2.2)
  simp only [chooseBranch, h.1, hg]

#print axioms low_iterate_matches
#print axioms low_iterate_branch

end UdonVerify.SafeGcd
