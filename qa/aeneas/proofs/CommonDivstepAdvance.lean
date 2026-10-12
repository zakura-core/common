import CommonDivstepFrame

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem cancel_shift_matrix (z : Nat) (w : Int) (matrix : Matrix) :
    matrixMul ⟨2 ^ z, 0, 0, 1⟩ (matrixMul ⟨1, 0, w, 1⟩ matrix) =
      matrixMul ⟨2 ^ z, 0, w, 1⟩ matrix := by
  dsimp only [matrixMul]
  congr 1 <;> ring

theorem native_cancel_advance (state : State) (matrix : Matrix)
    (eta : I64) (u v q r f g : U64) (remaining : U32)
    (nextEta : I64) (nextU nextV nextQ nextR nextF nextG mask w : U64)
    (stripEta : I64) (stripU stripV stripG : U64) (zeros : U32)
    (hr : 0 < remaining.val ∧ remaining.val ≤ 62)
    (h : DivWordMatch (remaining.val + 2) state matrix eta u v q r f g)
    (hfodd : f.val % 2 = 1) (hgodd : g.val % 2 = 1)
    (hc : NativeCancelRelation eta u v q r f g remaining
      (nextEta, nextU, nextV, nextQ, nextR, nextF, nextG, mask, w))
    (hz : zeros.val = trailingZeros64 (sentinelWord (addMulWord nextG nextF w) remaining.val))
    (hzbound : zeros.val ≤ remaining.val)
    (he : stripEta.val = nextEta.val - (zeros.val : Int))
    (hu : stripU.bv = nextU.bv <<< zeros.val)
    (hv : stripV.bv = nextV.bv <<< zeros.val)
    (hg : stripG.val = (addMulWord nextG nextF w).val / 2 ^ zeros.val)
    (hzero : (addMulWord nextG nextF w).val % 2 ^ zeros.val = 0) :
    0 < zeros.val ∧
    DivWordMatch (remaining.val + 2 - zeros.val) (iterate zeros.val state)
      (matrixMul (transitionMatrix zeros.val state) matrix)
      stripEta stripU stripV (addMulWord nextQ nextU w) (addMulWord nextR nextV w)
      nextF stripG := by
  obtain ⟨n, pre, preMatrix, hn0, hni, _, hw, hcancel, hdelta, hodd, hpre, hframe⟩ :=
    native_cancel_match (remaining.val + 2) state matrix eta u v q r f g remaining
      nextEta nextU nextV nextQ nextR nextF nextG mask w (by omega) h hfodd hgodd hc
  have hlow := add_mul_word_low_zero nextG nextF w n (by omega) hcancel
  have hzn := sentinel_count_ge_of_low_zero (addMulWord nextG nextF w) remaining.val n
    (by omega) hni hlow
  rw [← hz] at hzn
  have hz0 : 0 < zeros.val := by omega
  have hadd := matched_add (remaining.val + 2) pre preMatrix nextEta
    nextU nextV nextQ nextR nextF nextG w (by omega) hpre
  obtain ⟨hdiv, hshift⟩ := matched_shift (remaining.val + 2) zeros.val
    ⟨pre.delta, pre.f, pre.g + pre.f * w.val⟩
    (matrixMul ⟨1, 0, w.val, 1⟩ preMatrix)
    nextEta stripEta nextU nextV (addMulWord nextQ nextU w) (addMulWord nextR nextV w)
    nextF (addMulWord nextG nextF w) stripU stripV stripG
    (by omega) (by omega) hadd he hu hv hg hzero
  obtain ⟨hstate, hmatrix⟩ := no_swap_extended n zeros.val pre (w.val : Int)
    hzn hdelta hodd ⟨by positivity, by exact_mod_cast hw⟩ hdiv
  refine ⟨hz0, ?_⟩
  rw [hframe.states zeros.val hz0, hstate, hframe.matrices zeros.val hz0,
    hmatrix]
  simpa only [cancel_shift_matrix] using hshift

#print axioms cancel_shift_matrix
#print axioms native_cancel_advance
end UdonVerify.CommonSigned62
