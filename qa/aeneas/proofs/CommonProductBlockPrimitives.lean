import CommonProductAarch64Dictionaries
import CommonProductBlockMath
import CommonProductPortableLanes

open Aeneas Std Result
namespace UdonVerify.ProductBlock
open UdonVerify.ProductAarch64 UdonVerify.CommonComba
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

instance elementInhabited {M S : Type} : Inhabited (Element M S) :=
  ⟨⟨Array.repeat 4#usize 0#u64, ()⟩⟩

theorem add_product_bridge (column : BatchColumn) (lhs rhs : U64) :
    CommonProductsAarch64.field.pasta.products.add_product column lhs rhs =
      CommonComba.field.pasta.products.add_product column lhs rhs := by rfl

theorem start_column_bridge (a b c : U64) :
    CommonProductsAarch64.field.pasta.products.start_column a b c =
      CommonComba.field.pasta.products.start_column a b c := by rfl

theorem start_columns_bridge (a b c : U64) :
    CommonProductsAarch64.field.pasta.products.start_columns a b c =
      CommonComba.field.pasta.products.start_columns a b c := by rfl

theorem merge_columns_bridge (columns : BatchColumns) :
    CommonProductsAarch64.field.pasta.products.merge_columns columns =
      CommonComba.field.pasta.products.merge_columns columns := by rfl

/-- Replacing a Comba lane changes only that lane's integer contribution. -/
theorem columns_set_value (columns : BatchColumns) (index : Usize)
    (hindex : index.val < 4) (value : BatchColumn) :
    batchColumnsInteger (columns.set index value) + batchColumnInteger columns[index.val]! =
      batchColumnsInteger columns + batchColumnInteger value := by
  rw [UdonVerify.ProductPortable.array_four_eta_generic columns]
  have hcases : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 ∨ index.val = 3 := by omega
  rcases hcases with hv | hv | hv | hv <;>
    simp [batchColumnsInteger, Array.set, Array.make, Array.getElem!_Nat_eq, hv] <;> omega

/-- One original mutable-array update, factored without changing its operations. -/
def addAt {M S T : Type} (lane i j : Usize) (columns : BatchColumns)
    (lhs : Element M S) (rhs : Element M T) : Result BatchColumns := do
  let (column,back) ← Array.index_mut_usize columns lane
  let a ← Array.index_usize lhs.limbs i
  let b ← Array.index_usize rhs.limbs j
  let out ← CommonProductsAarch64.field.pasta.products.add_product column a b
  ok (back out)

@[step]
theorem add_at_spec {M S T : Type} (lane i j : Usize) (columns : BatchColumns)
    (lhs : Element M S) (rhs : Element M T)
    (hlane : lane.val < 4) (hi : i.val < 4) (hj : j.val < 4)
    (hbound : batchColumnsInteger columns + lhs.limbs[i.val]!.val * rhs.limbs[j.val]!.val < B ^ 3) :
    addAt lane i j columns lhs rhs ⦃ out =>
      batchColumnsInteger out = batchColumnsInteger columns +
        lhs.limbs[i.val]!.val * rhs.limbs[j.val]!.val ⦄ := by
  have hframe := columns_set_value columns lane hlane
  have hold : batchColumnInteger columns[lane.val]! ≤ batchColumnsInteger columns := by
    have hzero := hframe (Array.repeat 3#usize 0#u64)
    have hz : batchColumnInteger (Array.repeat 3#usize 0#u64) = 0 := by simp [batchColumnInteger,Array.repeat]
    rw [hz, Nat.add_zero] at hzero
    omega
  unfold addAt
  step +scalarTac -grind as ⟨column,back,hcolumn,hback⟩
  step +scalarTac -grind as ⟨a,ha⟩
  step +scalarTac -grind as ⟨b,hb⟩
  have hcolumn' : column = columns[lane.val]! := by
    simpa only [Array.getElem!_Nat_eq, getElem!_pos columns.val lane.val (by simpa using hlane)] using hcolumn
  have ha' : a = lhs.limbs[i.val]! := by
    simpa only [Array.getElem!_Nat_eq, getElem!_pos lhs.limbs.val i.val (by simpa using hi)] using ha
  have hb' : b = rhs.limbs[j.val]! := by
    simpa only [Array.getElem!_Nat_eq, getElem!_pos rhs.limbs.val j.val (by simpa using hj)] using hb
  rw [add_product_bridge]
  step -grind with (batch_column_add_spec column a b (by rw [hcolumn',ha',hb']; omega)) as ⟨out,hout⟩
  rw [hback]
  have hset := hframe out
  rw [hcolumn',ha',hb'] at hout
  omega

#print axioms add_product_bridge
#print axioms start_column_bridge
#print axioms start_columns_bridge
#print axioms merge_columns_bridge
#print axioms columns_set_value
#print axioms add_at_spec
end UdonVerify.ProductBlock
