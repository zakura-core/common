import CommonDivstepOdd

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

structure DivWordMatch (bits : Nat) (state : State) (matrix : Matrix)
    (eta : I64) (u v q r f g : U64) : Prop where
  eta_value : eta.val = -state.delta
  u_mod : Int.ModEq (2 ^ 64) (u.val : Int) matrix.u
  v_mod : Int.ModEq (2 ^ 64) (v.val : Int) matrix.v
  q_mod : Int.ModEq (2 ^ 64) (q.val : Int) matrix.q
  r_mod : Int.ModEq (2 ^ 64) (r.val : Int) matrix.r
  f_mod : Int.ModEq (2 ^ bits) (f.val : Int) state.f
  g_mod : Int.ModEq (2 ^ bits) (g.val : Int) state.g

theorem modEq_two_pow_reduce (small large : Nat) (a b : Int)
    (h : Int.ModEq (2 ^ large) a b) (hbits : small ≤ large) :
    Int.ModEq (2 ^ small) a b :=
  h.of_dvd (pow_dvd_pow 2 hbits)

theorem matched_word_odd (bits : Nat) (word : U64) (value : Int)
    (hbits : 0 < bits) (h : Int.ModEq (2 ^ bits) (word.val : Int) value)
    (hodd : value % 2 = 1) : word.val % 2 = 1 := by
  have htwo := modEq_two_pow_reduce 1 bits (word.val : Int) value h (by omega)
  norm_num only [pow_one, Int.ModEq, Int.natCast_emod, Int.cast_ofNat_Int] at htwo
  omega

theorem matched_integer_odd (bits : Nat) (word : U64) (value : Int)
    (hbits : 0 < bits) (h : Int.ModEq (2 ^ bits) (word.val : Int) value)
    (hodd : word.val % 2 = 1) : value % 2 = 1 := by
  have htwo := modEq_two_pow_reduce 1 bits (word.val : Int) value h (by omega)
  norm_num only [pow_one, Int.ModEq, Int.natCast_emod, Int.cast_ofNat_Int] at htwo
  omega

theorem add_mul_word_mod (g f w : U64) (bits : Nat) (hbits : bits ≤ 64) :
    Int.ModEq (2 ^ bits) ((addMulWord g f w).val : Int)
      ((g.val : Int) + (f.val : Int) * w.val) := by
  exact (wrapping_add_mod_pow g (UScalar.wrapping_mul f w) bits hbits).trans
    ((Int.ModEq.refl (g.val : Int)).add (wrapping_mul_mod_pow f w bits hbits))

theorem matched_add (bits : Nat) (state : State) (matrix : Matrix)
    (eta : I64) (u v q r f g w : U64) (hbits : bits ≤ 64)
    (h : DivWordMatch bits state matrix eta u v q r f g) :
    DivWordMatch bits ⟨state.delta, state.f, state.g + state.f * w.val⟩
      (matrixMul ⟨1, 0, w.val, 1⟩ matrix) eta u v
      (addMulWord q u w) (addMulWord r v w) f (addMulWord g f w) := by
  refine ⟨h.eta_value, ?_, ?_, ?_, ?_, h.f_mod, ?_⟩
  · simpa [matrixMul] using h.u_mod
  · simpa [matrixMul] using h.v_mod
  · simpa [matrixMul, mul_comm, add_comm] using
      (add_mul_word_mod q u w 64 (by decide)).trans
        (h.q_mod.add (h.u_mod.mul_right (w.val : Int)))
  · simpa [matrixMul, mul_comm, add_comm] using
      (add_mul_word_mod r v w 64 (by decide)).trans
        (h.r_mod.add (h.v_mod.mul_right (w.val : Int)))
  · exact (add_mul_word_mod g f w bits hbits).trans
      (h.g_mod.add (h.f_mod.mul_right (w.val : Int)))

theorem matched_shift (bits z : Nat) (state : State) (matrix : Matrix)
    (eta nextEta : I64) (u v q r f g nextU nextV nextG : U64)
    (hbits : bits ≤ 64) (hz : z ≤ bits)
    (h : DivWordMatch bits state matrix eta u v q r f g)
    (heta : nextEta.val = eta.val - (z : Int))
    (hu : nextU.bv = u.bv <<< z) (hv : nextV.bv = v.bv <<< z)
    (hg : nextG.val = g.val / 2 ^ z) (hzero : g.val % 2 ^ z = 0) :
    (2 ^ z : Int) ∣ state.g ∧
    DivWordMatch (bits - z) ⟨state.delta + z, state.f, state.g / 2 ^ z⟩
      (matrixMul ⟨2 ^ z, 0, 0, 1⟩ matrix) nextEta nextU nextV q r f nextG := by
  have hwordDiv : (2 ^ z : Int) ∣ (g.val : Int) := by
    exact_mod_cast (Nat.dvd_of_mod_eq_zero hzero)
  have hreduce := modEq_two_pow_reduce z bits (g.val : Int) state.g h.g_mod hz
  have hfullDiv := (hreduce.dvd_iff).mp hwordDiv
  refine ⟨hfullDiv, ?_⟩
  refine ⟨by dsimp; rw [heta, h.eta_value]; ring, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [matrixMul, mul_comm] using
      (word_shift_bv_mod u nextU z hu).trans (h.u_mod.mul_right (2 ^ z : Int))
  · simpa [matrixMul, mul_comm] using
      (word_shift_bv_mod v nextV z hv).trans (h.v_mod.mul_right (2 ^ z : Int))
  · simpa [matrixMul] using h.q_mod
  · simpa [matrixMul] using h.r_mod
  · exact modEq_two_pow_reduce (bits - z) bits _ _ h.f_mod (by omega)
  · have hsum : z + (bits - z) = bits := by omega
    have hquot := modEq_div_pow (bits - z) z (g.val : Int) state.g
      (by simpa only [hsum] using h.g_mod) hwordDiv hfullDiv
    rw [hg]
    simpa only [Int.natCast_ediv, Int.natCast_pow, Int.cast_ofNat_Int] using hquot

#print axioms modEq_two_pow_reduce
#print axioms matched_word_odd
#print axioms matched_integer_odd
#print axioms add_mul_word_mod
#print axioms matched_add
#print axioms matched_shift
end UdonVerify.CommonSigned62
