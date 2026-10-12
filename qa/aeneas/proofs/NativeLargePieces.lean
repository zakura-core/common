import NativeLargeEntries

open Aeneas Std Result

namespace UdonVerify.LargeNativeBridge
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def largeAppend (low digit : U32) (count : I32) : Result U32 := do
  let aligned ← digit <<< count
  lift (low ||| aligned)

def largeLowIndex (value : U32) : Result Usize :=
  lift (UScalar.cast .Usize (value &&& 255#u32))

def largeDigitIndex (value : U32) (count : I32) : Result Usize := do
  let shifted ← value >>> count
  lift (UScalar.cast .Usize (shifted &&& 255#u32))

def largeTopIndex (value : U32) (count : I32) : Result Usize := do
  let shifted ← value >>> count
  lift (UScalar.cast .Usize shifted)

/-- The extracted finish routine's exponent-recovery prefix, regrouped without changing its calls. -/
def largeRecover {M : Type} (parametersPrimeModulusInst : Modulus M)
    (self : Native.LargeTable M) (t : Element M Loose) (multiplier : U32) : Result U32 := do
  let x2 ←
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish.closure_1.Insts.CoreOpsFunctionFnTuplePastaFieldMLoosePastaFieldMLoose.call
      parametersPrimeModulusInst () t
  let x1 ←
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish.closure_1.Insts.CoreOpsFunctionFnTuplePastaFieldMLoosePastaFieldMLoose.call
      parametersPrimeModulusInst () x2
  let x0 ←
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish.closure_1.Insts.CoreOpsFunctionFnTuplePastaFieldMLoosePastaFieldMLoose.call
      parametersPrimeModulusInst () x1
  let e ←
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish.closure.Insts.CoreOpsFunctionFnTuplePastaFieldMLooseU32.call
      parametersPrimeModulusInst (self, multiplier) x0
  let i ← lift (UScalar.cast .Usize e)
  let pf ← Array.index_usize self.g2 i
  let alpha ←
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.mul parametersPrimeModulusInst x1 pf
  let i1 ←
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish.closure.Insts.CoreOpsFunctionFnTuplePastaFieldMLooseU32.call
      parametersPrimeModulusInst (self, multiplier) alpha
  let e1 ← largeAppend e i1 8#i32
  let i4 ← largeLowIndex e1
  let pf1 ← Array.index_usize self.g1 i4
  let pf2 ←
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.mul parametersPrimeModulusInst x2 pf1
  let i6 ← largeTopIndex e1 8#i32
  let pf3 ← Array.index_usize self.g2 i6
  let alpha1 ←
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.mul parametersPrimeModulusInst pf2 pf3
  let i7 ←
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish.closure.Insts.CoreOpsFunctionFnTuplePastaFieldMLooseU32.call
      parametersPrimeModulusInst (self, multiplier) alpha1
  let e2 ← largeAppend e1 i7 16#i32
  let i10 ← largeLowIndex e2
  let pf4 ← Array.index_usize self.g0 i10
  let pf5 ←
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.mul parametersPrimeModulusInst t pf4
  let i13 ← largeDigitIndex e2 8#i32
  let pf6 ← Array.index_usize self.g1 i13
  let pf7 ←
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.mul parametersPrimeModulusInst pf5 pf6
  let i15 ← largeTopIndex e2 16#i32
  let pf8 ← Array.index_usize self.g2 i15
  let alpha2 ←
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.mul parametersPrimeModulusInst pf7 pf8
  let i16 ←
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish.closure.Insts.CoreOpsFunctionFnTuplePastaFieldMLooseU32.call
      parametersPrimeModulusInst (self, multiplier) alpha2
  let e3 ← largeAppend e2 i16 24#i32
  ok e3

/-- The extracted finish routine's correction suffix. -/
def largeCorrect {M : Type} (parametersPrimeModulusInst : Modulus M)
    (self : Native.LargeTable M) (x : Element M Loose) (exponent : U32) :
    Result (Bool × Element M Loose) := do
  let i18 ← lift (exponent &&& 1#u32)
  let e4 ← LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.half_exponent exponent
  let i20 ← largeLowIndex e4
  let pf9 ← Array.index_usize self.g0 i20
  let pf10 ←
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.mul parametersPrimeModulusInst x pf9
  let i23 ← largeDigitIndex e4 8#i32
  let pf11 ← Array.index_usize self.g1 i23
  let pf12 ←
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.mul parametersPrimeModulusInst pf10 pf11
  let i26 ← largeDigitIndex e4 16#i32
  let pf13 ← Array.index_usize self.g2 i26
  let pf14 ←
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.mul parametersPrimeModulusInst pf12 pf13
  let i28 ← largeTopIndex e4 24#i32
  let pf15 ← Array.index_usize self.g3 i28
  let candidate ←
    LargeAlgorithms.zakura_udon.field.pasta.PastaField.mul parametersPrimeModulusInst pf14 pf15
  ok (i18 = 0#u32, candidate)

theorem large_finish_bridge {M : Type} (inst : Modulus M) (table : Native.LargeTable M)
    (x t : Element M Loose) (multiplier : U32) :
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish
      inst table x t multiplier = (do
        let exponent ← largeRecover inst table t multiplier
        largeCorrect inst table x exponent) := by
  unfold LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish
    largeRecover largeCorrect largeAppend largeLowIndex largeDigitIndex largeTopIndex
  simp only [lift, bind_ok, Std.bind_assoc]

#print axioms large_finish_bridge

end UdonVerify.LargeNativeBridge
