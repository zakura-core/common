import CommonProductBlockLoops

open Aeneas Std Result
namespace UdonVerify.ProductBlock
open UdonVerify.ProductAarch64 UdonVerify.CommonComba
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

theorem outlined_block_00_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_00 columns lhs rhs =
      accumulateColumn 0#usize 0#usize columns lhs rhs := by rfl

#print axioms outlined_block_00_bridge

theorem outlined_block_01_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_01 columns lhs rhs =
      accumulateColumn 0#usize 1#usize columns lhs rhs := by rfl

#print axioms outlined_block_01_bridge

theorem outlined_block_02_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_02 columns lhs rhs =
      accumulateColumn 1#usize 0#usize columns lhs rhs := by rfl

#print axioms outlined_block_02_bridge

theorem outlined_block_03_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_03 columns lhs rhs =
      accumulateColumn 0#usize 2#usize columns lhs rhs := by rfl

#print axioms outlined_block_03_bridge

theorem outlined_block_04_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_04 columns lhs rhs =
      accumulateColumn 1#usize 1#usize columns lhs rhs := by rfl

#print axioms outlined_block_04_bridge

theorem outlined_block_05_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_05 columns lhs rhs =
      accumulateColumn 2#usize 0#usize columns lhs rhs := by rfl

#print axioms outlined_block_05_bridge

theorem outlined_block_06_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_06 columns lhs rhs =
      accumulateColumn 0#usize 3#usize columns lhs rhs := by rfl

#print axioms outlined_block_06_bridge

theorem outlined_block_07_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_07 columns lhs rhs =
      accumulateColumn 1#usize 2#usize columns lhs rhs := by rfl

#print axioms outlined_block_07_bridge

theorem outlined_block_08_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_08 columns lhs rhs =
      accumulateColumn 2#usize 1#usize columns lhs rhs := by rfl

#print axioms outlined_block_08_bridge

theorem outlined_block_09_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_09 columns lhs rhs =
      accumulateColumn 3#usize 0#usize columns lhs rhs := by rfl

#print axioms outlined_block_09_bridge

theorem outlined_block_10_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_10 columns lhs rhs =
      accumulateColumn 1#usize 3#usize columns lhs rhs := by rfl

#print axioms outlined_block_10_bridge

theorem outlined_block_11_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_11 columns lhs rhs =
      accumulateColumn 2#usize 2#usize columns lhs rhs := by rfl

#print axioms outlined_block_11_bridge

theorem outlined_block_12_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_12 columns lhs rhs =
      accumulateColumn 3#usize 1#usize columns lhs rhs := by rfl

#print axioms outlined_block_12_bridge

theorem outlined_block_13_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_13 columns lhs rhs =
      accumulateColumn 2#usize 3#usize columns lhs rhs := by rfl

#print axioms outlined_block_13_bridge

theorem outlined_block_14_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_14 columns lhs rhs =
      accumulateColumn 3#usize 2#usize columns lhs rhs := by rfl

#print axioms outlined_block_14_bridge

theorem outlined_block_15_bridge {M S T : Type} (columns : BatchColumns)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductsAarch64.field.pasta.products.outlined_block_15 columns lhs rhs =
      accumulateColumn 3#usize 3#usize columns lhs rhs := by rfl

#print axioms outlined_block_15_bridge

end UdonVerify.ProductBlock
