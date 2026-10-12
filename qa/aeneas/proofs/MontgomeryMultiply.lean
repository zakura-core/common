import MontgomeryRound
import MontgomerySemantics

open Aeneas Std Result
open udon_kernel_slice.field.pasta
open udon_kernel_slice.field.pasta.montgomery

namespace UdonVerify
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post UScalar.ofNat

abbrev iter4 (rhs : A4) (i : Nat) : core.slice.iter.Iter U64 :=
  ⟨rhs.to_slice, i⟩

theorem next_slice4_0 (rhs : A4) : core.slice.iter.IteratorSliceIter.next (iter4 rhs 0) =
    ok (some rhs[0]!,iter4 rhs 1) := by
  simp [iter4,core.slice.iter.IteratorSliceIter.next, Array.to_slice]

theorem next_slice4_1 (rhs : A4) : core.slice.iter.IteratorSliceIter.next (iter4 rhs 1) =
    ok (some rhs[1]!,iter4 rhs 2) := by
  simp [iter4,core.slice.iter.IteratorSliceIter.next, Array.to_slice]

theorem next_slice4_2 (rhs : A4) : core.slice.iter.IteratorSliceIter.next (iter4 rhs 2) =
    ok (some rhs[2]!,iter4 rhs 3) := by
  simp [iter4,core.slice.iter.IteratorSliceIter.next, Array.to_slice]

theorem next_slice4_3 (rhs : A4) : core.slice.iter.IteratorSliceIter.next (iter4 rhs 3) =
    ok (some rhs[3]!,iter4 rhs 4) := by
  simp [iter4,core.slice.iter.IteratorSliceIter.next, Array.to_slice]

theorem next_slice4_4 (rhs : A4) : core.slice.iter.IteratorSliceIter.next (iter4 rhs 4) =
    ok (none,iter4 rhs 4) := by
  simp [iter4,core.slice.iter.IteratorSliceIter.next, Array.to_slice]

theorem cios_live_bound (a p old rhs k next : Nat)
    (hold : old < a+p) (hrhs : rhs < B) (hk : k < B)
    (h : B*next = old+a*rhs+k*p) : next < a+p := by
  have ha := Nat.mul_le_mul_left a (Nat.succ_le_of_lt hrhs)
  have hp := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hk)
  have hm : B*next < B*(a+p) := by nlinarith only [hold,ha,hp,h]
  exact Nat.lt_of_mul_lt_mul_left hm

theorem cios_four_identity (n0 n1 n2 n3 n4 b0 b1 b2 b3 k0 k1 k2 k3 a p : Nat)
    (h0 : B*n1=n0+a*b0+k0*p) (h1 : B*n2=n1+a*b1+k1*p)
    (h2 : B*n3=n2+a*b2+k2*p) (h3 : B*n4=n3+a*b3+k3*p) :
    R*n4=n0+a*(b0+B*b1+B^2*b2+B^3*b3)+(k0+B*k1+B^2*k2+B^3*k3)*p := by
  unfold R
  linear_combination h0+B*h1+B^2*h2+B^3*h3

theorem cios_loop_unfold {M : Type} (inst : PrimeModulus M)
    (p lhs : A4) (iter : core.slice.iter.Iter U64) (acc : A5) :
    montgomery_multiply_loop0 inst p iter lhs acc = (do
      let flow ← montgomery_multiply_loop0.body inst p lhs iter acc
      match flow with
      | .done r => ok r
      | .cont (it,a) => montgomery_multiply_loop0 inst p it lhs a) := by
  unfold montgomery_multiply_loop0
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done r => rfl
  | cont r => rcases r with ⟨it,a⟩; rfl

@[step]
theorem cios_full_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (lhs rhs : A4) :
    montgomery_multiply_loop0 inst params.modulus (iter4 rhs 0) lhs (Array.repeat 5#usize 0#u64)
    ⦃ out => val5 out < val4 lhs+val4 params.modulus ∧
      ∃ m : Nat,m < R ∧ R*val5 out=val4 lhs*val4 rhs+m*val4 params.modulus ⦄ := by
  have hstart : val5 (Array.repeat 5#usize 0#u64) < val4 lhs+val4 params.modulus := by
    simp [val5]
    have hp := params.positive
    omega
  rw [cios_loop_unfold]
  step -grind with (cios_round_spec inst params lhs _ (iter4 rhs 0) (iter4 rhs 1) rhs[0]! (next_slice4_0 rhs)) as ⟨flow0,hflow0⟩
  cases flow0 with
  | done out => exact False.elim hflow0
  | cont state =>
    rcases state with ⟨iter0,acc0⟩
    rcases hflow0 with ⟨hiter0,k0,hk0,heq0⟩
    subst iter0
    have hbound0 := cios_live_bound (val4 lhs) (val4 params.modulus) _ rhs[0]!.val k0 (val5 acc0)
      hstart (by simpa [B] using U64.lt_succ_max rhs[0]!) hk0 heq0
    try simp only [bind_ok]
    rw [cios_loop_unfold]
    step -grind with (cios_round_spec inst params lhs _ (iter4 rhs 1) (iter4 rhs 2) rhs[1]! (next_slice4_1 rhs)) as ⟨flow1,hflow1⟩
    cases flow1 with
    | done out => exact False.elim hflow1
    | cont state =>
      rcases state with ⟨iter1,acc1⟩
      rcases hflow1 with ⟨hiter1,k1,hk1,heq1⟩
      subst iter1
      have hbound1 := cios_live_bound (val4 lhs) (val4 params.modulus) _ rhs[1]!.val k1 (val5 acc1)
        hbound0 (by simpa [B] using U64.lt_succ_max rhs[1]!) hk1 heq1
      try simp only [bind_ok]
      rw [cios_loop_unfold]
      step -grind with (cios_round_spec inst params lhs _ (iter4 rhs 2) (iter4 rhs 3) rhs[2]! (next_slice4_2 rhs)) as ⟨flow2,hflow2⟩
      cases flow2 with
      | done out => exact False.elim hflow2
      | cont state =>
        rcases state with ⟨iter2,acc2⟩
        rcases hflow2 with ⟨hiter2,k2,hk2,heq2⟩
        subst iter2
        have hbound2 := cios_live_bound (val4 lhs) (val4 params.modulus) _ rhs[2]!.val k2 (val5 acc2)
          hbound1 (by simpa [B] using U64.lt_succ_max rhs[2]!) hk2 heq2
        try simp only [bind_ok]
        rw [cios_loop_unfold]
        step -grind with (cios_round_spec inst params lhs _ (iter4 rhs 3) (iter4 rhs 4) rhs[3]! (next_slice4_3 rhs)) as ⟨flow3,hflow3⟩
        cases flow3 with
        | done out => exact False.elim hflow3
        | cont state =>
          rcases state with ⟨iter3,acc3⟩
          rcases hflow3 with ⟨hiter3,k3,hk3,heq3⟩
          subst iter3
          have hbound3 := cios_live_bound (val4 lhs) (val4 params.modulus) _ rhs[3]!.val k3 (val5 acc3)
            hbound2 (by simpa [B] using U64.lt_succ_max rhs[3]!) hk3 heq3
          try simp only [bind_ok]
          rw [cios_loop_unfold]
          unfold montgomery_multiply_loop0.body
          rw [next_slice4_4]
          simp only [bind_ok]
          simp only [Std.uncurry_apply_pair, bind_ok, WP.spec_ok]
          let m := k0+B*k1+B^2*k2+B^3*k3
          have hm : m < R := by
            dsimp [m]
            norm_num [B,R] at hk0 hk1 hk2 hk3 ⊢
            omega
          have hmath := cios_four_identity _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq0 heq1 heq2 heq3
          have hcert : R*val5 acc3=val4 lhs*val4 rhs+m*val4 params.modulus := by
            simpa [val5,val4,m] using hmath
          change val5 acc3 < val4 lhs+val4 params.modulus ∧
            ∃ m : Nat,m < R ∧ R*val5 acc3=val4 lhs*val4 rhs+m*val4 params.modulus
          exact ⟨hbound3,m,hm,hcert⟩


theorem val5_top_zero (a : A5) (h : val5 a < R) : a[4]! = 0#u64 := by
  have hle : R*a[4]!.val ≤ val5 a := by unfold val5; omega
  have hmul : R*a[4]!.val < R*1 := by simpa using _root_.lt_of_le_of_lt hle h
  have ht : a[4]!.val < 1 := Nat.lt_of_mul_lt_mul_left hmul
  clear * - ht
  scalar_tac

@[step]
theorem montgomery_multiply_bounded_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (lhs rhs : A4)
    (hinputs : (val4 lhs < 2*val4 params.modulus ∧ val4 rhs < 2*val4 params.modulus) ∨
      val4 lhs*val4 rhs < val4 params.modulus*R) :
    montgomery_multiply inst lhs rhs ⦃ out => val4 out < 2*val4 params.modulus ∧
      ∃ m : Nat,m < R ∧ R*val4 out=val4 lhs*val4 rhs+m*val4 params.modulus ⦄ := by
  unfold montgomery_multiply
  rw [params.modulus_ok]
  simp only [bind_ok]
  step +scalarTac -grind as ⟨p2,hp2⟩
  have hp2zero : p2 = 0#u64 := by
    have hz := params.zero_limb
    have hp2val : p2.val = 0 := by simpa [hp2] using hz
    clear * - hp2val
    scalar_tac
  step
  step +scalarTac -grind as ⟨p3,hp3⟩
  step as ⟨shift,hshift,hshiftbv⟩
  have hp3shift : p3 = shift := by
    have hh := params.high_limb
    have hp3val : p3.val = 2^62 := by simpa [hp3] using hh
    have hsh : shift.val=2^62 := by
      simpa [Nat.shiftLeft_eq,U64.size,U64.numBits] using hshift
    clear * - hp3val hsh
    scalar_tac
  step
  unfold SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
  simp only [bind_ok]
  change (do
    let accumulator1 ← montgomery_multiply_loop0 inst params.modulus (iter4 rhs 0) lhs
      (Array.repeat 5#usize 0#u64)
    let left_val2 ← Array.index_usize accumulator1 4#usize
    massert (left_val2 = 0#u64)
    let s ← core.slice.index.SliceIndexRangeToUsizeSlice.index { «end» := 4#usize } accumulator1.to_slice
    let r ← core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU64 s
    core.result.Result.unwrap core.fmt.DebugTryFromSliceError r) ⦃ out =>
      val4 out < 2*val4 params.modulus ∧ ∃ m : Nat,m < R ∧
      R*val4 out=val4 lhs*val4 rhs+m*val4 params.modulus ⦄
  step -grind with (cios_full_spec inst params lhs rhs) as ⟨acc,haccbound,m,hm,hcert⟩
  have hacc2 : val5 acc < 2*val4 params.modulus := by
    rcases hinputs with ⟨ha,hb⟩ | hprod
    · exact pasta_loose_bound params (val4 lhs) (val4 rhs) m (val5 acc) ha hb hm hcert
    · have hmp := Nat.mul_lt_mul_of_pos_right hm params.positive
      have hmul : R*val5 acc < R*(2*val4 params.modulus) := by
        nlinarith only [hcert,hprod,hmp]
      exact Nat.lt_of_mul_lt_mul_left hmul
  have haccR : val5 acc < R := by
    have hp3 := params.thrice_lt
    omega
  have htop := val5_top_zero acc haccR
  step +scalarTac -grind as ⟨top,htopread⟩
  have htop0 : top = 0#u64 := by simpa [htopread] using htop
  step
  step +scalarTac -grind as ⟨slice,hsliceval,hslicelen⟩
  step -grind as ⟨result,hresult⟩
  cases result with
  | Err err =>
    cases err
    exact False.elim (hresult (by simpa using hslicelen))
  | Ok out =>
    rcases hresult with ⟨houtval,houtlen⟩
    unfold core.result.Result.unwrap
    simp only [WP.spec_ok]
    have hv : val4 out=val5 acc := by
      simp [val4,val5,houtval,hsliceval,htop,List.slice]
    refine ⟨?_,m,hm,?_⟩
    · simpa [hv] using hacc2
    · simpa [hv] using hcert

@[step]
theorem montgomery_multiply_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (lhs rhs : A4)
    (ha : val4 lhs < 2*val4 params.modulus) (hb : val4 rhs < 2*val4 params.modulus) :
    montgomery_multiply inst lhs rhs ⦃ out => val4 out < 2*val4 params.modulus ∧
      ∃ m : Nat,m < R ∧ R*val4 out=val4 lhs*val4 rhs+m*val4 params.modulus ⦄ :=
  montgomery_multiply_bounded_spec inst params lhs rhs (Or.inl ⟨ha,hb⟩)

#print axioms cios_full_spec
#print axioms montgomery_multiply_spec

end UdonVerify
