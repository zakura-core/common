import MontgomeryMultiply
import LooseMultiplyPublic
import MontgomeryWrappers

open Aeneas Std Result
open udon_kernel_slice.field.pasta
open udon_kernel_slice.field.pasta.montgomery

namespace UdonVerify
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post UScalar.ofNat

theorem weighted_square_step (p x y z n : Nat)
    (hsquare : Nat.ModEq p (R*y) (x^2))
    (hrun : Nat.ModEq p (R^(2^n-1)*z) (y^(2^n))) :
    Nat.ModEq p (R^(2^(n+1)-1)*z) (x^(2^(n+1))) := by
  have hpos : 0 < 2^n := pow_pos (by decide) n
  have hpow : 2^(n+1)=2^n*2 := pow_succ _ _
  have hexp : 2^n+(2^n-1)=2^(n+1)-1 := by omega
  have hl := hrun.mul_left (R^(2^n))
  rw [←mul_assoc,←pow_add,hexp,←mul_pow] at hl
  have hp := hsquare.pow (2^n)
  have hr : (x^2)^(2^n)=x^(2^(n+1)) := by
    rw [←pow_mul,hpow]
    congr 1
    ring
  rw [hr] at hp
  exact hl.trans hp

theorem square_loop_unfold {M : Type} (inst : PrimeModulus M)
    (iter : core.ops.range.Range Usize) (value : A4) :
    square_run_loop inst iter value = (do
      let flow ← square_run_loop.body inst iter value
      match flow with
      | .done r => ok r
      | .cont (it,v) => square_run_loop inst it v) := by
  unfold square_run_loop
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done r => rfl
  | cont r => rcases r with ⟨it,v⟩; rfl

@[step]
theorem square_run_loop_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (iter : core.ops.range.Range Usize) (value : A4)
    (horder : iter.start.val ≤ iter.end.val) (hvalue : val4 value < 2*val4 params.modulus) :
    square_run_loop inst iter value ⦃ out => val4 out < 2*val4 params.modulus ∧
      Nat.ModEq (val4 params.modulus) (R^(2^(iter.end.val-iter.start.val)-1)*val4 out)
        (val4 value^(2^(iter.end.val-iter.start.val))) ⦄ := by
  generalize hn : iter.end.val-iter.start.val = n
  induction n using Nat.strong_induction_on generalizing iter value with
  | h n ih =>
    rw [square_loop_unfold]
    unfold square_run_loop.body
    by_cases hlt : iter.start.val < iter.end.val
    · have hnext := WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec iter hlt)
      rcases hnext with ⟨⟨opt,it⟩,hnext,hopt,hstart,hend⟩
      subst opt
      rw [hnext]
      simp only [bind_ok,Std.uncurry_apply_pair,Std.bind_assoc]
      rw [←Std.bind_assoc]
      change (do
        let v ← montgomery_square inst value
        square_run_loop inst it v) ⦃ out => val4 out < 2*val4 params.modulus ∧
          Nat.ModEq (val4 params.modulus) (R^(2^n-1)*val4 out) (val4 value^(2^n)) ⦄
      step -grind with (montgomery_square_spec inst params value hvalue) as ⟨v,hv,m,hm,hcert⟩
      have horder' : it.start.val ≤ it.end.val := by rw [hstart,hend]; omega
      have hdiff : it.end.val-it.start.val=n-1 := by rw [hstart,hend]; omega
      have hn0 : 0 < n := by omega
      have hs : n-1 < n := by omega
      step -grind with (ih (n-1) hs it v horder' hv hdiff) as ⟨out,hout,hpow⟩
      try simp only [WP.spec_ok]
      have hsq := certificate_congruence (val4 params.modulus) (val4 value^2) m (val4 v) hcert
      have h := weighted_square_step (val4 params.modulus) (val4 value) (val4 v) (val4 out) (n-1) hsq hpow
      have hsucc : n-1+1=n := by omega
      rw [hsucc] at h
      exact ⟨hout,h⟩
    · have hnext := WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec iter (by omega))
      rcases hnext with ⟨⟨opt,it⟩,hnext,hopt,hiter⟩
      subst opt
      subst it
      rw [hnext]
      simp only [bind_ok,Std.uncurry_apply_pair,WP.spec_ok]
      have hn0 : n=0 := by omega
      subst n
      have hdiff0 : iter.end.val-iter.start.val=0 := by omega
      rw [hdiff0]
      simpa using And.intro hvalue (Nat.ModEq.refl (val4 value) (n := val4 params.modulus))

theorem weighted_factor_step (p origin intermediate out factor n : Nat)
    (hpow : Nat.ModEq p (R^(2^n-1)*intermediate) (origin^(2^n)))
    (hmul : Nat.ModEq p (R*out) (intermediate*factor)) :
    Nat.ModEq p (R^(2^n)*out) (origin^(2^n)*factor) := by
  have hpos : 0 < 2^n := pow_pos (by decide) n
  have hexp : (2^n-1)+1=2^n := by omega
  have hm := hmul.mul_left (R^(2^n-1))
  have hp := hpow.mul_right factor
  have hl : R^(2^n-1)*(R*out)=R^(2^n)*out := by
    rw [←mul_assoc,←pow_succ,hexp]
  have hr : R^(2^n-1)*(intermediate*factor)=(R^(2^n-1)*intermediate)*factor := by ring
  rw [hl,hr] at hm
  exact hm.trans hp

@[step]
theorem square_run_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (value : A4) (count : Usize) (factor : Option A4)
    (hvalue : val4 value < 2*val4 params.modulus)
    (hfactor : match factor with | none => True | some f => val4 f < 2*val4 params.modulus) :
    square_run inst value count factor ⦃ out => val4 out < 2*val4 params.modulus ∧
      match factor with
      | none => Nat.ModEq (val4 params.modulus) (R^(2^count.val-1)*val4 out) (val4 value^(2^count.val))
      | some f => Nat.ModEq (val4 params.modulus) (R^(2^count.val)*val4 out) (val4 value^(2^count.val)*val4 f) ⦄ := by
  unfold square_run
  step -grind with (square_run_loop_spec inst params { start := 0#usize, «end» := count }
    value (by change 0 ≤ count.val; exact Nat.zero_le _) hvalue) as ⟨v,hv,hpow⟩
  change Nat.ModEq (val4 params.modulus) (R^(2^count.val-1)*val4 v)
    (val4 value^(2^count.val)) at hpow
  cases factor with
  | none => simpa only [WP.spec_ok] using And.intro hv hpow
  | some f =>
    step -grind with (montgomery_multiply_loose_spec inst params v f hv hfactor) as ⟨out,hout,m,hm,hcert⟩
    try simp only [WP.spec_ok]
    have hmul := certificate_congruence (val4 params.modulus) (val4 v*val4 f) m (val4 out) hcert
    exact ⟨hout,weighted_factor_step _ _ _ _ _ _ hpow hmul⟩

#print axioms square_run_spec

end UdonVerify
