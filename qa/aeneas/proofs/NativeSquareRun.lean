import NativeArithmetic
import SquareRun

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem decoded_square_run (p inverse a u n : Nat)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (hcongruence : Nat.ModEq p (R ^ (2 ^ n - 1) * u) (a ^ (2 ^ n))) :
    (u * inverse) % p = ((a * inverse) % p) ^ (2 ^ n) % p := by
  have hpos : 0 < 2 ^ n := pow_pos (by decide) _
  have hsuccessor : 2 ^ n - 1 + 1 = 2 ^ n := by omega
  have hinversePow : inverse ^ (2 ^ n) = inverse ^ (2 ^ n - 1) * inverse := by
    simpa only [hsuccessor] using pow_succ inverse (2 ^ n - 1)
  have hlhs : (R ^ (2 ^ n - 1) * u) * inverse ^ (2 ^ n) =
      (R * inverse) ^ (2 ^ n - 1) * (u * inverse) := by
    rw [hinversePow, mul_pow]
    ring
  have hc := hcongruence.mul_right (inverse ^ (2 ^ n))
  rw [hlhs, ← mul_pow] at hc
  have hi := (hinverse.pow (2 ^ n - 1)).mul_right (u * inverse)
  simp only [one_pow, one_mul] at hi
  have h := hi.symm.trans hc
  exact h.trans (Nat.pow_mod (a * inverse) (2 ^ n) p)

theorem decoded_square_run_factor (p inverse a f u n : Nat)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (hcongruence : Nat.ModEq p (R ^ (2 ^ n) * u) (a ^ (2 ^ n) * f)) :
    (u * inverse) % p = (((a * inverse) % p) ^ (2 ^ n) * ((f * inverse) % p)) % p := by
  have hlhs : (R ^ (2 ^ n) * u) * inverse ^ (2 ^ n + 1) =
      (R * inverse) ^ (2 ^ n) * (u * inverse) := by
    rw [pow_succ, mul_pow]
    ring
  have hrhs : (a ^ (2 ^ n) * f) * inverse ^ (2 ^ n + 1) =
      (a * inverse) ^ (2 ^ n) * (f * inverse) := by
    rw [pow_succ, mul_pow]
    ring
  have hc := hcongruence.mul_right (inverse ^ (2 ^ n + 1))
  rw [hlhs, hrhs] at hc
  have hi := (hinverse.pow (2 ^ n)).mul_right (u * inverse)
  simp only [one_pow, one_mul] at hi
  have h := hi.symm.trans hc
  change (u * inverse) % p = ((a * inverse) ^ (2 ^ n) * (f * inverse)) % p at h
  rw [h]
  simp only [Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]

theorem native_square_run_eq {M : Type} (inst : Modulus M)
    (value : A4) (count : Usize) (factor : Option A4) :
    NativeField.zakura_udon.field.pasta.montgomery.square_run inst value count factor =
      udon_kernel_slice.field.pasta.montgomery.square_run (kernelInst inst) value count factor := by
  rfl

@[step]
theorem native_square_run_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (value : A4) (count : Usize) (factor : Option A4)
    (hvalue : val4 value < 2 * val4 params.modulus)
    (hfactor : match factor with | none => True | some f => val4 f < 2 * val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.montgomery.square_run inst value count factor
      ⦃ out => val4 out < 2 * val4 params.modulus ∧
        decode (val4 params.modulus) inverse out =
          match factor with
          | none => decode (val4 params.modulus) inverse value ^ (2 ^ count.val) % val4 params.modulus
          | some f => (decode (val4 params.modulus) inverse value ^ (2 ^ count.val) *
              decode (val4 params.modulus) inverse f) % val4 params.modulus ⦄ := by
  rw [native_square_run_eq]
  step -grind with (square_run_spec (kernelInst inst) params value count factor hvalue hfactor)
    as ⟨out, hbound, hcongruence⟩
  refine ⟨hbound, ?_⟩
  cases factor with
  | none => exact decoded_square_run _ inverse _ _ count.val hinverse hcongruence
  | some f => exact decoded_square_run_factor _ inverse _ _ _ count.val hinverse hcongruence

#print axioms native_square_run_spec

end UdonVerify.Native
