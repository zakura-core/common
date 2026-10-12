import DivstepsMatrix
import CommonCancellationMath
open UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem no_swap_step (state : State) (hdelta : state.delta ≤ 0) :
    (integerStep state).delta = state.delta+1 ∧ (integerStep state).f=state.f := by
  by_cases heven : state.g%2=0 <;>
    simp [integerStep,chooseBranch,heven,not_lt_of_ge hdelta]

theorem no_swap_block (n : Nat) (state : State) (hdelta : state.delta+(n:Int) ≤ 1) :
    (iterate n state).delta=state.delta+n ∧ (iterate n state).f=state.f ∧
      (transitionMatrix n state).u=2^n ∧ (transitionMatrix n state).v=0 ∧
      (transitionMatrix n state).r=1 ∧
      0 ≤ (transitionMatrix n state).q ∧ (transitionMatrix n state).q<2^n := by
  induction n with
  | zero => simp [iterate,transitionMatrix,identityMatrix]
  | succ n ih =>
    obtain ⟨hd,hf,hu,hv,hr,hq0,hq1⟩ := ih (by omega)
    have hnonpos : (iterate n state).delta ≤ 0 := by rw [hd];omega
    obtain ⟨hdnext,hfnext⟩ := no_swap_step (iterate n state) hnonpos
    have hchoose : chooseBranch (iterate n state).delta (iterate n state).g =
        (if (iterate n state).g%2=0 then Branch.even else Branch.add) := by
      simp only [chooseBranch,not_lt_of_ge hnonpos,if_false]
    simp only [iterate,transitionMatrix,hdnext,hfnext,hchoose]
    by_cases heven : (iterate n state).g%2=0
    all_goals simp only [heven,if_true,if_false,matrixStep,hu,hv,hr,zero_add,mul_zero,one_mul,add_zero,hd,hf,true_and]
    all_goals
      rw [pow_succ]
      have hp : (0:Int)<2^n := by positivity
      push_cast
      omega

theorem canonical_cancellation_unique (f g a b : Int) (n : Nat) (hodd : f%2=1)
    (ha : 0≤a ∧ a<2^n) (hb : 0≤b ∧ b<2^n)
    (hac : Int.ModEq (2^n) (g+f*a) 0) (hbc : Int.ModEq (2^n) (g+f*b) 0) :
    a=b := by
  have hprod : Int.ModEq (2^n) (f*a) (f*b) :=
    Int.ModEq.add_left_cancel' g (hac.trans hbc.symm)
  have hcop : Int.gcd (2^n) f=1 :=
    Int.gcd_pow_left_of_gcd_eq_one (by simpa only [Int.gcd_comm] using gcd_two_of_odd f hodd)
  have h := Int.ModEq.cancel_left_div_gcd (by positivity) hprod
  rw [hcop] at h
  simp only [Nat.cast_one,Int.ediv_one] at h
  have haDiv : a/(2^n)=0 := Int.ediv_eq_zero_of_lt ha.1 ha.2
  have hbDiv : b/(2^n)=0 := Int.ediv_eq_zero_of_lt hb.1 hb.2
  exact (Int.modEq_iff_eq_of_div_eq (by rw [haDiv,hbDiv])).mp h

theorem no_swap_block_cancellation (n : Nat) (state : State) (hdelta : state.delta+(n:Int) ≤ 1)
    (hodd : state.f%2=1) :
    Int.ModEq (2^n) (state.g+state.f*(transitionMatrix n state).q) 0 := by
  obtain ⟨hd,hf,hu,hv,hr,hq0,hq1⟩ := no_swap_block n state hdelta
  have haction := congrArg Vertex.y (transition_matrix_action n state hodd)
  dsimp only [matrixAction,scaleVertex] at haction
  rw [hr] at haction
  apply Int.modEq_zero_iff_dvd.mpr
  refine ⟨(iterate n state).g,?_⟩
  simpa only [one_mul,mul_one,add_comm,mul_comm] using haction

theorem no_swap_batch_matrix (n : Nat) (state : State) (w : Int)
    (hdelta : state.delta+(n:Int) ≤ 1) (hodd : state.f%2=1)
    (hw : 0≤w ∧ w<2^n) (hcancel : Int.ModEq (2^n) (state.g+state.f*w) 0) :
    transitionMatrix n state = ⟨2^n,0,w,1⟩ := by
  obtain ⟨hd,hf,hu,hv,hr,hq0,hq1⟩ := no_swap_block n state hdelta
  have hq := canonical_cancellation_unique state.f state.g
    (transitionMatrix n state).q w n hodd ⟨hq0,hq1⟩ hw
    (no_swap_block_cancellation n state hdelta hodd) hcancel
  cases hm : transitionMatrix n state
  simp only [hm] at hu hv hr hq
  simp_all

#print axioms no_swap_block
#print axioms canonical_cancellation_unique
#print axioms no_swap_block_cancellation
#print axioms no_swap_batch_matrix
end UdonVerify.CommonSigned62
