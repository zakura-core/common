import CommonProductPortableLanes

open Aeneas Std Result
namespace UdonVerify.ProductPortable
open UdonVerify.Products
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem raw_sum_four {M S T : Type}
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (ha : lhs.length = 4) (hb : rhs.length = 4) :
    rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val =
      val4 lhs[0]!.limbs * val4 rhs[0]!.limbs + val4 lhs[1]!.limbs * val4 rhs[1]!.limbs +
      val4 lhs[2]!.limbs * val4 rhs[2]!.limbs + val4 lhs[3]!.limbs * val4 rhs[3]!.limbs := by
  obtain ⟨a0,a1,a2,a3,hlhs⟩ := List.length_eq_four.mp ha
  obtain ⟨b0,b1,b2,b3,hrhs⟩ := List.length_eq_four.mp hb
  simp [rawSum, Aeneas.Std.Slice.getElem!_Nat_eq, hlhs, hrhs, Nat.add_assoc]

@[step]
theorem add_four_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (lanes : Lanes M) (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (ha : lhs.length = 4) (hb : rhs.length = 4)
    (hbound : lanesInteger lanes + rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val < B ^ 9) :
    addFour (portableDict inst) lanes lhs rhs ⦃ out =>
      lanesInteger out = lanesInteger lanes +
        rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val ⦄ := by
  have hraw := raw_sum_four lhs rhs ha hb
  have htotal := hbound
  rw [hraw] at htotal
  unfold lanesInteger at htotal
  unfold addFour
  step -grind with (portable_inner_bounded_spec inst params constants lanes[0]! lhs[0]! rhs[0]! (by omega))
    as ⟨a,haValue⟩
  step -grind with (portable_inner_bounded_spec inst params constants lanes[1]! lhs[1]! rhs[1]! (by omega))
    as ⟨b,hbValue⟩
  step -grind with (portable_inner_bounded_spec inst params constants lanes[2]! lhs[2]! rhs[2]! (by omega))
    as ⟨c,hcValue⟩
  step -grind with (portable_inner_bounded_spec inst params constants lanes[3]! lhs[3]! rhs[3]! (by omega))
    as ⟨d,hdValue⟩
  change lanesInteger (Array.make 4#usize [a,b,c,d]) = lanesInteger lanes +
    rawSum (fun x => val4 x.limbs) (fun y => val4 y.limbs) lhs.val rhs.val
  have hout : lanesInteger (Array.make 4#usize [a,b,c,d]) =
      sumInteger a + sumInteger b + sumInteger c + sumInteger d := by simp [lanesInteger]
  rw [hout,hraw]
  unfold lanesInteger
  omega

#print axioms raw_sum_four
#print axioms add_four_spec
end UdonVerify.ProductPortable
