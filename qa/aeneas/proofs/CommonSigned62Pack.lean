import CommonSigned62Packing
open Aeneas Std Result
open Signed62Native.field.pasta.safegcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem pack62_spec (limbs : A4) (hbound : val4 limbs<2^255) :
    pack62 limbs ⦃ out => signed62Normalized out ∧ signed62Value out=(val4 limbs:Int) ∧
      0≤out[4]!.val ∧ out[4]!.val<128 ⦄ := by
  unfold pack62
  step -grind with (to_signed62_spec limbs hbound) as ⟨out,hn,hval,htop0,htop⟩
  step +scalarTac -grind as ⟨top,htopEq⟩
  have htopValue : top.val=out[4]!.val := by
    rw [htopEq]
    simp [Array.getElem!_Nat_eq,out.property]
  step +scalarTac -grind
  step +scalarTac -grind
  try simp only [WP.spec_ok]
  exact ⟨hn,hval,htop0,htop⟩

#print axioms pack62_spec
end UdonVerify.CommonSigned62
