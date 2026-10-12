import CommonDivstepMatrix
open UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem even_quotient_pow (g : Int) (n : Nat) (hdiv : (2^(n+1):Int) ∣ g) :
    (g/2^n)%2=0 := by
  obtain ⟨k,hk⟩ := hdiv
  rw [hk,pow_succ]
  have hp : (2^n:Int)≠0 := by positivity
  have heq : (2^n*2*k:Int)/2^n=2*k := by
    rw [mul_assoc,Int.mul_ediv_cancel_left _ hp]
  rw [heq]
  omega

theorem even_block (n : Nat) (state : State) (hdiv : (2^n:Int) ∣ state.g) :
    iterate n state=⟨state.delta+n,state.f,state.g/2^n⟩ ∧
      transitionMatrix n state=⟨2^n,0,0,1⟩ := by
  induction n with
  | zero => simp [iterate,transitionMatrix,identityMatrix]
  | succ n ih =>
    have hd : (2^n:Int) ∣ state.g := dvd_trans (pow_dvd_pow 2 (by omega : n≤n+1)) hdiv
    obtain ⟨hs,hm⟩ := ih hd
    have heven := even_quotient_pow state.g n hdiv
    have hchoose : chooseBranch (iterate n state).delta (iterate n state).g=Branch.even := by
      rw [hs]
      simp only [chooseBranch,heven,if_true]
    constructor
    · rw [iterate]
      unfold integerStep
      rw [hchoose,hs]
      have hp : ¬(2^n:Int)<0 := not_lt_of_ge (show (0:Int)≤2^n from by positivity)
      simp only [Int.ediv_ediv,pow_succ,Nat.cast_succ,hp,false_and,if_false,sub_zero]
      congr 1 <;> ring
    · rw [transitionMatrix,hchoose,hm]
      dsimp only [matrixStep]
      rw [pow_succ]
      congr 1 <;> ring

#print axioms even_quotient_pow
#print axioms even_block
end UdonVerify.CommonSigned62
