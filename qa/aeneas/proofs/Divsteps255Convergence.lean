import Divsteps255Checks
import DivstepsCertificate

namespace UdonVerify.SafeGcd
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024

theorem divsteps255_converges (modulus x : Int)
    (hmodulus : 0 < modulus) (hbound : modulus ≤ 2 ^ 255)
    (hodd : modulus % 2 = 1) (hx : 0 ≤ x) (hxBound : x ≤ modulus) :
    (iterate 732 ⟨1, modulus, x⟩).g = 0 := by
  apply certificate_convergence modulus (2 ^ 255) x 732 Cert255.stages
    hmodulus hbound hodd hx hxBound
  · rfl
  · exact Cert255.all_steps_valid
  · decide +kernel

theorem divsteps255_converges_744 (modulus x : Int)
    (hmodulus : 0 < modulus) (hbound : modulus ≤ 2 ^ 255)
    (hodd : modulus % 2 = 1) (hx : 0 ≤ x) (hxBound : x ≤ modulus) :
    (iterate 744 ⟨1, modulus, x⟩).g = 0 := by
  rw [show 744 = 732 + 12 from by decide, iterate_add]
  exact iterate_zero 12 _ (divsteps255_converges modulus x hmodulus hbound hodd hx hxBound)

#print axioms divsteps255_converges
#print axioms divsteps255_converges_744

end UdonVerify.SafeGcd
