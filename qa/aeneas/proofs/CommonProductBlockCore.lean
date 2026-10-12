import CommonProductBlockPartition
import CommonProductBlockBridges
import CommonProductBlockArrayOps

open Aeneas Std Result
namespace UdonVerify.ProductBlock
open UdonVerify.ProductAarch64 UdonVerify.CommonComba
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- The source block after proved in-bounds array operations and helper bridges. -/
def blockCore
  {M : Type} {T1 : Type} {T2 : Type} (self : Sum M)
  (lhs : Aeneas.Std.Slice (Element M T1))
  (rhs : Aeneas.Std.Slice (Element M T2)) :
  Result (Sum M)
  := do
  let left_val := Slice.len lhs
  let right_val := Slice.len rhs
  massert (left_val = right_val)
  let i := self.wide[0]!
  let a := Array.repeat 3#usize 0#u64
  let a1 := Array.repeat 3#usize 0#u64
  let a2 := Array.repeat 3#usize 0#u64
  let columns ←
    accumulateColumn 0#usize 0#usize
      (Array.make 4#usize [
        Array.make 3#usize [ i, 0#u64, 0#u64 ], a, a1, a2
        ]) lhs rhs
  let column ← CommonComba.field.pasta.products.merge_columns columns
  let i1 := column[0]!
  let a3 := self.wide.set 0#usize i1
  let i2 := self.wide[1]!
  let i3 := column[1]!
  let i4 := column[2]!
  let columns1 ← CommonComba.field.pasta.products.start_columns i2 i3 i4
  let columns2 ← accumulateColumn 0#usize 1#usize columns1 lhs rhs
  let columns3 ← accumulateColumn 1#usize 0#usize columns2 lhs rhs
  let column1 ← CommonComba.field.pasta.products.merge_columns columns3
  let i5 := column1[0]!
  let a4 := a3.set 1#usize i5
  let i6 := self.wide[2]!
  let i7 := column1[1]!
  let i8 := column1[2]!
  let columns4 ← CommonComba.field.pasta.products.start_columns i6 i7 i8
  let columns5 ← accumulateColumn 0#usize 2#usize columns4 lhs rhs
  let columns6 ← accumulateColumn 1#usize 1#usize columns5 lhs rhs
  let columns7 ← accumulateColumn 2#usize 0#usize columns6 lhs rhs
  let column2 ← CommonComba.field.pasta.products.merge_columns columns7
  let i9 := column2[0]!
  let a5 := a4.set 2#usize i9
  let i10 := self.wide[3]!
  let i11 := column2[1]!
  let i12 := column2[2]!
  let columns8 ← CommonComba.field.pasta.products.start_columns i10 i11 i12
  let columns9 ← accumulateColumn 0#usize 3#usize columns8 lhs rhs
  let columns10 ← accumulateColumn 1#usize 2#usize columns9 lhs rhs
  let columns11 ← accumulateColumn 2#usize 1#usize columns10 lhs rhs
  let columns12 ← accumulateColumn 3#usize 0#usize columns11 lhs rhs
  let column3 ← CommonComba.field.pasta.products.merge_columns columns12
  let i13 := column3[0]!
  let a6 := a5.set 3#usize i13
  let i14 := self.wide[4]!
  let i15 := column3[1]!
  let i16 := column3[2]!
  let columns13 ← CommonComba.field.pasta.products.start_columns i14 i15 i16
  let columns14 ← accumulateColumn 1#usize 3#usize columns13 lhs rhs
  let columns15 ← accumulateColumn 2#usize 2#usize columns14 lhs rhs
  let columns16 ← accumulateColumn 3#usize 1#usize columns15 lhs rhs
  let column4 ← CommonComba.field.pasta.products.merge_columns columns16
  let i17 := column4[0]!
  let a7 := a6.set 4#usize i17
  let i18 := self.wide[5]!
  let i19 := column4[1]!
  let i20 := column4[2]!
  let columns17 ← CommonComba.field.pasta.products.start_columns i18 i19 i20
  let columns18 ← accumulateColumn 2#usize 3#usize columns17 lhs rhs
  let columns19 ← accumulateColumn 3#usize 2#usize columns18 lhs rhs
  let column5 ← CommonComba.field.pasta.products.merge_columns columns19
  let i21 := column5[0]!
  let a8 := a7.set 5#usize i21
  let i22 := self.wide[6]!
  let i23 := column5[1]!
  let i24 := column5[2]!
  let columns20 ← CommonComba.field.pasta.products.start_columns i22 i23 i24
  let columns21 ← accumulateColumn 3#usize 3#usize columns20 lhs rhs
  let column6 ← CommonComba.field.pasta.products.merge_columns columns21
  let i25 := column6[0]!
  let a9 := a8.set 6#usize i25
  let i26 := self.wide[7]!
  let i27 := column6[1]!
  let i28 := column6[2]!
  let column7 ← CommonComba.field.pasta.products.start_column i26 i27 i28
  let i29 := column7[0]!
  let a10 := a9.set 7#usize i29
  let left_val1 := column7[2]!
  massert (left_val1 = 0#u64)
  let i30 := column7[1]!
  let (carry, overflow) ← lift (core.num.U64.overflowing_add self.carry i30)
  massert (¬ overflow)
  ok { self with wide := a10, carry }

theorem block_core_eq {M S T : Type} (sum : Sum M)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.ProductSum.add_product_block sum lhs rhs =
      blockCore sum lhs rhs := by
  unfold CommonProductsAarch64.field.pasta.products.ProductSum.add_product_block blockCore
  simp (disch := decide) only [block_index_eq,block_update_eq,bind_ok,Std.uncurry,
    Array.getElem!_Nat_set_ne,
    start_column_bridge,start_columns_bridge,merge_columns_bridge,
    outlined_block_00_bridge,outlined_block_01_bridge,outlined_block_02_bridge,outlined_block_03_bridge,
    outlined_block_04_bridge,outlined_block_05_bridge,outlined_block_06_bridge,outlined_block_07_bridge,
    outlined_block_08_bridge,outlined_block_09_bridge,outlined_block_10_bridge,outlined_block_11_bridge,
    outlined_block_12_bridge,outlined_block_13_bridge,outlined_block_14_bridge,outlined_block_15_bridge ]
  simp only [show (0#usize).val = 0 from rfl, show (1#usize).val = 1 from rfl, show (2#usize).val = 2 from rfl, show (3#usize).val = 3 from rfl, show (4#usize).val = 4 from rfl, show (5#usize).val = 5 from rfl, show (6#usize).val = 6 from rfl, show (7#usize).val = 7 from rfl]

#print axioms block_core_eq
end UdonVerify.ProductBlock
