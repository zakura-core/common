import CommonDivstepBatches
open UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def matrixMul (a b : Matrix) : Matrix :=
  ⟨a.u*b.u+a.v*b.q,a.u*b.v+a.v*b.r,a.q*b.u+a.r*b.q,a.q*b.v+a.r*b.r⟩

def matrixDet (a : Matrix) : Int := a.u*a.r-a.v*a.q

theorem matrix_step_mul (branch : Branch) (a b : Matrix) :
    matrixStep branch (matrixMul a b) = matrixMul (matrixStep branch a) b := by
  cases branch <;> dsimp only [matrixStep,matrixMul] <;> congr 1 <;> ring

theorem matrix_step_det (branch : Branch) (a : Matrix) :
    matrixDet (matrixStep branch a)=2*matrixDet a := by
  cases branch <;> dsimp only [matrixStep,matrixDet] <;> ring

theorem transition_matrix_det (n : Nat) (state : State) :
    matrixDet (transitionMatrix n state)=2^n := by
  induction n with
  | zero => norm_num [transitionMatrix,identityMatrix,matrixDet]
  | succ n ih => rw [transitionMatrix,matrix_step_det,ih,pow_succ];ring

def swapPreState (state : State) : State := ⟨-state.delta,state.g,-state.f⟩
def rotationMatrix : Matrix := ⟨0,1,-1,0⟩

theorem swap_pre_step (state : State) (hdelta : 0<state.delta)
    (hoddF : state.f%2=1) (hoddG : state.g%2=1) :
    integerStep state=integerStep (swapPreState state) := by
  have hg : state.g%2≠0 := by omega
  have hf : (-state.f)%2≠0 := by omega
  have hd : ¬0< -state.delta := by omega
  simp only [integerStep,chooseBranch,swapPreState,hg,hf,hdelta,hd,if_false,if_true]
  congr 1 <;> simp [sub_eq_add_neg,add_comm]

theorem swap_pre_iterate (n : Nat) (state : State) (hn : 0<n)
    (hdelta : 0<state.delta) (hoddF : state.f%2=1) (hoddG : state.g%2=1) :
    iterate n state=iterate n (swapPreState state) := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  subst n
  have h1 := swap_pre_step state hdelta hoddF hoddG
  have hl : iterate (1+k) state=iterate k (integerStep state) := by
    simpa only [iterate] using iterate_add 1 k state
  have hr : iterate (1+k) (swapPreState state)=iterate k (integerStep (swapPreState state)) := by
    simpa only [iterate] using iterate_add 1 k (swapPreState state)
  simpa only [Nat.add_comm] using (hl.trans ((congrArg (iterate k) h1).trans hr.symm))

theorem swap_pre_matrix (n : Nat) (state : State) (hn : 0<n)
    (hdelta : 0<state.delta) (hoddF : state.f%2=1) (hoddG : state.g%2=1) :
    transitionMatrix n state=matrixMul (transitionMatrix n (swapPreState state)) rotationMatrix := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n=0
    · subst n
      have hg : state.g%2≠0 := by omega
      have hf : (-state.f)%2≠0 := by omega
      have hd : ¬0< -state.delta := by omega
      simp only [transitionMatrix,iterate,chooseBranch,swapPreState,hg,hf,hdelta,hd,if_false,if_true,
        matrixStep,identityMatrix,matrixMul,rotationMatrix]
      norm_num
    · rw [transitionMatrix,transitionMatrix,ih (by omega),
        swap_pre_iterate n state (by omega) hdelta hoddF hoddG,matrix_step_mul]

theorem swap_batch_matrix (n : Nat) (state : State) (w : Int) (hn : 0<n)
    (hdelta : 0<state.delta) (hlimit : (n:Int)≤state.delta+1)
    (hoddF : state.f%2=1) (hoddG : state.g%2=1)
    (hw : 0≤w ∧ w<2^n) (hc : Int.ModEq (2^n) (-state.f+state.g*w) 0) :
    transitionMatrix n state=⟨0,2^n,-1,w⟩ := by
  have hb := no_swap_batch_matrix n (swapPreState state) w (by dsimp [swapPreState];omega)
    hoddG hw hc
  rw [swap_pre_matrix n state hn hdelta hoddF hoddG,hb]
  simp [matrixMul,rotationMatrix]

#print axioms transition_matrix_det
#print axioms swap_pre_step
#print axioms swap_pre_iterate
#print axioms swap_pre_matrix
#print axioms swap_batch_matrix
end UdonVerify.CommonSigned62
