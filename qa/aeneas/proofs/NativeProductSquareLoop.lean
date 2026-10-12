import NativeProductWords
open Aeneas Std Result
namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem add_square_loop_eq (it : WideZip) (back : WideZip → WideZip) (carry : U64) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_square_loop it back carry =
      NativeField.zakura_udon.field.pasta.encoding.raw_product_sum_loop it back carry := by rfl

@[step]
theorem add_square_loop_spec (a square : A8) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_square_loop
      ⟨⟨a.to_slice,0⟩,⟨square.to_slice,0⟩⟩ (fun z => z) 0#u64
      ⦃ carry z => carry.val ≤ 1 ∧
        val8 (Array.from_slice a z.fst.slice)+R^2*carry.val=val8 a+val8 square ⦄ := by
  rw [add_square_loop_eq]
  step -grind with (raw_add_loop_spec a square) as ⟨carry,z,hvalue⟩
  have ha := val8_lt a
  have hb := val8_lt square
  constructor
  · norm_num [R,B] at hvalue ha hb
    omega
  · exact hvalue

#print axioms add_square_loop_eq
#print axioms add_square_loop_spec
end UdonVerify.Native
