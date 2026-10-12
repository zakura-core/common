import LooseRound

open Aeneas Std Result
open udon_kernel_slice.field.pasta
open udon_kernel_slice.field.pasta.montgomery

namespace UdonVerify
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post UScalar.ofNat UScalar.cMax

theorem loose_loop_unfold {M : Type} (inst : PrimeModulus M)
    (iter : core.slice.iter.Iter U64) (a0 a1 a2 a3 r0 r1 r2 r3 : U64) :
    montgomery_multiply_loose_rust_loop inst iter a0 a1 a2 a3 r0 r1 r2 r3 = (do
      let flow ← montgomery_multiply_loose_rust_loop.body inst a0 a1 a2 a3 iter r0 r1 r2 r3
      match flow with
      | .done result => ok result
      | .cont (next,n0,n1,n2,n3) =>
        montgomery_multiply_loose_rust_loop inst next a0 a1 a2 a3 n0 n1 n2 n3) := by
  unfold montgomery_multiply_loose_rust_loop
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done result => rfl
  | cont state => rcases state with ⟨next,n0,n1,n2,n3⟩; rfl

@[step]
theorem loose_full_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (a0 a1 a2 a3 : U64) (rhs : A4)
    (ha : digits4 a0 a1 a2 a3 < 2*val4 params.modulus) :
    montgomery_multiply_loose_rust_loop inst (iter4 rhs 0) a0 a1 a2 a3 0#u64 0#u64 0#u64 0#u64
      ⦃ out => digits4 out.1 out.2.1 out.2.2.1 out.2.2.2 <
          digits4 a0 a1 a2 a3+val4 params.modulus ∧
        ∃ m : Nat,m<R ∧ R*digits4 out.1 out.2.1 out.2.2.1 out.2.2.2 =
          digits4 a0 a1 a2 a3*val4 rhs+m*val4 params.modulus ⦄ := by
  have hstart : digits4 0#u64 0#u64 0#u64 0#u64 <
      digits4 a0 a1 a2 a3+val4 params.modulus := by
    simp [digits4]
    have hp := params.positive
    omega
  rw [loose_loop_unfold]
  step -grind with (loose_round_spec inst params a0 a1 a2 a3 0#u64 0#u64 0#u64 0#u64 rhs[0]!
      (iter4 rhs 0) (iter4 rhs 1) (next_slice4_0 rhs) ha hstart) as ⟨flow0,hflow0⟩
  cases flow0 with
  | done out => exact False.elim hflow0
  | cont state =>
    rcases state with ⟨iter0,s00,s01,s02,s03⟩
    rcases hflow0 with ⟨hiter0,hbound0,q0,hq0,hcert0⟩
    subst iter0
    try simp only [bind_ok]
    rw [loose_loop_unfold]
    step -grind with (loose_round_spec inst params a0 a1 a2 a3 s00 s01 s02 s03 rhs[1]!
        (iter4 rhs 1) (iter4 rhs 2) (next_slice4_1 rhs) ha hbound0) as ⟨flow1,hflow1⟩
    cases flow1 with
    | done out => exact False.elim hflow1
    | cont state =>
      rcases state with ⟨iter1,s10,s11,s12,s13⟩
      rcases hflow1 with ⟨hiter1,hbound1,q1,hq1,hcert1⟩
      subst iter1
      try simp only [bind_ok]
      rw [loose_loop_unfold]
      step -grind with (loose_round_spec inst params a0 a1 a2 a3 s10 s11 s12 s13 rhs[2]!
          (iter4 rhs 2) (iter4 rhs 3) (next_slice4_2 rhs) ha hbound1) as ⟨flow2,hflow2⟩
      cases flow2 with
      | done out => exact False.elim hflow2
      | cont state =>
        rcases state with ⟨iter2,s20,s21,s22,s23⟩
        rcases hflow2 with ⟨hiter2,hbound2,q2,hq2,hcert2⟩
        subst iter2
        try simp only [bind_ok]
        rw [loose_loop_unfold]
        step -grind with (loose_round_spec inst params a0 a1 a2 a3 s20 s21 s22 s23 rhs[3]!
            (iter4 rhs 3) (iter4 rhs 4) (next_slice4_3 rhs) ha hbound2) as ⟨flow3,hflow3⟩
        cases flow3 with
        | done out => exact False.elim hflow3
        | cont state =>
          rcases state with ⟨iter3,s30,s31,s32,s33⟩
          rcases hflow3 with ⟨hiter3,hbound3,q3,hq3,hcert3⟩
          subst iter3
          try simp only [bind_ok]
          rw [loose_loop_unfold]
          unfold montgomery_multiply_loose_rust_loop.body
          rw [next_slice4_4]
          simp only [Std.uncurry_apply_pair,bind_ok,WP.spec_ok]
          let m := q0+B*q1+B^2*q2+B^3*q3
          have hm : m<R := by
            dsimp [m]
            norm_num [B,R] at hq0 hq1 hq2 hq3 ⊢
            omega
          refine ⟨hbound3,m,hm,?_⟩
          have h := cios_four_identity 0 (digits4 s00 s01 s02 s03)
            (digits4 s10 s11 s12 s13) (digits4 s20 s21 s22 s23) (digits4 s30 s31 s32 s33)
            rhs[0]!.val rhs[1]!.val rhs[2]!.val rhs[3]!.val q0 q1 q2 q3
            (digits4 a0 a1 a2 a3) (val4 params.modulus)
            (by simpa [digits4] using hcert0) hcert1 hcert2 hcert3
          simpa only [val4,m,zero_add] using h


@[step]
theorem montgomery_multiply_loose_rust_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (lhs rhs : A4)
    (ha : val4 lhs < 2*val4 params.modulus) (hb : val4 rhs < 2*val4 params.modulus) :
    montgomery_multiply_loose_rust inst lhs rhs ⦃ out =>
      val4 out < 2*val4 params.modulus ∧
      ∃ m : Nat,m<R ∧ R*val4 out=val4 lhs*val4 rhs+m*val4 params.modulus ⦄ := by
  unfold montgomery_multiply_loose_rust
  step -grind as ⟨a0,ha0⟩
  step -grind as ⟨a1,ha1⟩
  step -grind as ⟨a2,ha2⟩
  step -grind as ⟨a3,ha3⟩
  have haval : digits4 a0 a1 a2 a3=val4 lhs := by simp [digits4,val4,ha0,ha1,ha2,ha3]
  unfold SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
  simp only [bind_ok]
  change (do
    let (r0,r1,r2,r3) ← montgomery_multiply_loose_rust_loop inst (iter4 rhs 0)
      a0 a1 a2 a3 0#u64 0#u64 0#u64 0#u64
    ok (Array.make 4#usize [r0,r1,r2,r3])) ⦃ out =>
      val4 out < 2*val4 params.modulus ∧
      ∃ m : Nat,m<R ∧ R*val4 out=val4 lhs*val4 rhs+m*val4 params.modulus ⦄
  step -grind with (loose_full_spec inst params a0 a1 a2 a3 rhs (by simpa [haval] using ha))
    as ⟨r0,r1,r2,r3,hbound,m,hm,hcert⟩
  have hloose := pasta_loose_bound params (val4 lhs) (val4 rhs) m
    (digits4 r0 r1 r2 r3) ha hb hm (by simpa [haval] using hcert)
  try simp only [WP.spec_ok]
  have hout : val4 (Array.make 4#usize [r0,r1,r2,r3])=digits4 r0 r1 r2 r3 := by
    simp [val4,digits4,Array.make]
  exact ⟨by simpa [hout] using hloose,m,hm,by simpa [hout,haval] using hcert⟩

#print axioms loose_full_spec
#print axioms montgomery_multiply_loose_rust_spec
end UdonVerify
