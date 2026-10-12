import CommonProductDotIter.Funs
import CommonProductPairs.Funs

open Aeneas Std Result
namespace UdonVerify.ProductWrappers.DotBridge
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

theorem core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator :
    @CommonProductDotIter.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator = @CommonProductPairs.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator := by
  unfold CommonProductDotIter.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator CommonProductPairs.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
  rfl

theorem Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter :
    @CommonProductDotIter.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter = @CommonProductPairs.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter := by
  unfold CommonProductDotIter.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter CommonProductPairs.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter
  simp only [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator] <;> rfl

theorem core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair :
    @CommonProductDotIter.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair = @CommonProductPairs.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair := by
  unfold CommonProductDotIter.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair CommonProductPairs.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
  rfl

theorem field.pasta.PastaField.ZERO :
    @CommonProductDotIter.field.pasta.PastaField.ZERO = @CommonProductPairs.field.pasta.PastaField.ZERO := by
  unfold CommonProductDotIter.field.pasta.PastaField.ZERO CommonProductPairs.field.pasta.PastaField.ZERO
  rfl

theorem field.pasta.word.compare_limbs_loop.body :
    @CommonProductDotIter.field.pasta.word.compare_limbs_loop.body = @CommonProductPairs.field.pasta.word.compare_limbs_loop.body := by
  unfold CommonProductDotIter.field.pasta.word.compare_limbs_loop.body CommonProductPairs.field.pasta.word.compare_limbs_loop.body
  rfl

theorem field.pasta.word.compare_limbs_loop :
    @CommonProductDotIter.field.pasta.word.compare_limbs_loop = @CommonProductPairs.field.pasta.word.compare_limbs_loop := by
  unfold CommonProductDotIter.field.pasta.word.compare_limbs_loop CommonProductPairs.field.pasta.word.compare_limbs_loop
  simp only [field.pasta.word.compare_limbs_loop.body] <;> rfl

theorem field.pasta.word.compare_limbs :
    @CommonProductDotIter.field.pasta.word.compare_limbs = @CommonProductPairs.field.pasta.word.compare_limbs := by
  unfold CommonProductDotIter.field.pasta.word.compare_limbs CommonProductPairs.field.pasta.word.compare_limbs
  simp only [field.pasta.word.compare_limbs_loop] <;> rfl

theorem field.pasta.PastaField.BOUND :
    @CommonProductDotIter.field.pasta.PastaField.BOUND = @CommonProductPairs.field.pasta.PastaField.BOUND := by
  unfold CommonProductDotIter.field.pasta.PastaField.BOUND CommonProductPairs.field.pasta.PastaField.BOUND
  rfl

theorem field.pasta.PastaField.from_montgomery :
    @CommonProductDotIter.field.pasta.PastaField.from_montgomery = @CommonProductPairs.field.pasta.PastaField.from_montgomery := by
  unfold CommonProductDotIter.field.pasta.PastaField.from_montgomery CommonProductPairs.field.pasta.PastaField.from_montgomery
  simp only [field.pasta.word.compare_limbs, field.pasta.PastaField.BOUND] <;> rfl

theorem field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED :
    @CommonProductDotIter.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED = @CommonProductPairs.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED := by
  unfold CommonProductDotIter.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED CommonProductPairs.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED
  rfl

theorem field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed :
    @CommonProductDotIter.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed = @CommonProductPairs.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed := by
  unfold CommonProductDotIter.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed CommonProductPairs.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed
  simp only [field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED] <;> rfl

theorem field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose.eq :
    @CommonProductDotIter.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose.eq = @CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose.eq := by
  unfold CommonProductDotIter.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose.eq CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose.eq
  rfl

theorem field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose :
    @CommonProductDotIter.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose = @CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose := by
  unfold CommonProductDotIter.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose
  simp only [field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose.eq] <;> rfl

theorem field.pasta.representation.Loose.Insts.CoreCmpEq :
    @CommonProductDotIter.field.pasta.representation.Loose.Insts.CoreCmpEq = @CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCmpEq := by
  unfold CommonProductDotIter.field.pasta.representation.Loose.Insts.CoreCmpEq CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCmpEq
  simp only [field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose] <;> rfl

theorem field.pasta.representation.Loose.Insts.CoreCloneClone.clone :
    @CommonProductDotIter.field.pasta.representation.Loose.Insts.CoreCloneClone.clone = @CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCloneClone.clone := by
  unfold CommonProductDotIter.field.pasta.representation.Loose.Insts.CoreCloneClone.clone CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCloneClone.clone
  rfl

theorem field.pasta.representation.Loose.Insts.CoreCloneClone :
    @CommonProductDotIter.field.pasta.representation.Loose.Insts.CoreCloneClone = @CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCloneClone := by
  unfold CommonProductDotIter.field.pasta.representation.Loose.Insts.CoreCloneClone CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCloneClone
  simp only [field.pasta.representation.Loose.Insts.CoreCloneClone.clone] <;> rfl

theorem field.pasta.representation.Loose.Insts.CoreMarkerCopy :
    @CommonProductDotIter.field.pasta.representation.Loose.Insts.CoreMarkerCopy = @CommonProductPairs.field.pasta.representation.Loose.Insts.CoreMarkerCopy := by
  unfold CommonProductDotIter.field.pasta.representation.Loose.Insts.CoreMarkerCopy CommonProductPairs.field.pasta.representation.Loose.Insts.CoreMarkerCopy
  simp only [field.pasta.representation.Loose.Insts.CoreCloneClone] <;> rfl

theorem field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState :
    @CommonProductDotIter.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState = @CommonProductPairs.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState := by
  unfold CommonProductDotIter.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState CommonProductPairs.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState
  simp only [field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed, field.pasta.representation.Loose.Insts.CoreCmpEq, field.pasta.representation.Loose.Insts.CoreMarkerCopy] <;> rfl

theorem field.pasta.word.wide_mul :
    @CommonProductDotIter.field.pasta.word.wide_mul = @CommonProductPairs.field.pasta.word.wide_mul := by
  unfold CommonProductDotIter.field.pasta.word.wide_mul CommonProductPairs.field.pasta.word.wide_mul
  rfl

theorem field.pasta.word.carry_add :
    @CommonProductDotIter.field.pasta.word.carry_add = @CommonProductPairs.field.pasta.word.carry_add := by
  unfold CommonProductDotIter.field.pasta.word.carry_add CommonProductPairs.field.pasta.word.carry_add
  rfl

theorem field.pasta.montgomery.montgomery_multiply_loose_rust_loop.body :
    @CommonProductDotIter.field.pasta.montgomery.montgomery_multiply_loose_rust_loop.body = @CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose_rust_loop.body := by
  unfold CommonProductDotIter.field.pasta.montgomery.montgomery_multiply_loose_rust_loop.body CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose_rust_loop.body
  simp only [field.pasta.word.wide_mul, field.pasta.word.carry_add] <;> rfl

theorem field.pasta.montgomery.montgomery_multiply_loose_rust_loop :
    @CommonProductDotIter.field.pasta.montgomery.montgomery_multiply_loose_rust_loop = @CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose_rust_loop := by
  unfold CommonProductDotIter.field.pasta.montgomery.montgomery_multiply_loose_rust_loop CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose_rust_loop
  simp only [field.pasta.montgomery.montgomery_multiply_loose_rust_loop.body] <;> rfl

theorem field.pasta.montgomery.montgomery_multiply_loose_rust :
    @CommonProductDotIter.field.pasta.montgomery.montgomery_multiply_loose_rust = @CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose_rust := by
  unfold CommonProductDotIter.field.pasta.montgomery.montgomery_multiply_loose_rust CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose_rust
  simp only [field.pasta.montgomery.montgomery_multiply_loose_rust_loop] <;> rfl

theorem field.pasta.montgomery.montgomery_multiply_loose :
    @CommonProductDotIter.field.pasta.montgomery.montgomery_multiply_loose = @CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose := by
  unfold CommonProductDotIter.field.pasta.montgomery.montgomery_multiply_loose CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose
  simp only [field.pasta.word.compare_limbs, field.pasta.montgomery.montgomery_multiply_loose_rust] <;> rfl

theorem field.pasta.PastaField.mul :
    @CommonProductDotIter.field.pasta.PastaField.mul = @CommonProductPairs.field.pasta.PastaField.mul := by
  unfold CommonProductDotIter.field.pasta.PastaField.mul CommonProductPairs.field.pasta.PastaField.mul
  simp only [field.pasta.PastaField.from_montgomery, field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState, field.pasta.montgomery.montgomery_multiply_loose] <;> rfl

theorem field.pasta.word.sbb :
    @CommonProductDotIter.field.pasta.word.sbb = @CommonProductPairs.field.pasta.word.sbb := by
  unfold CommonProductDotIter.field.pasta.word.sbb CommonProductPairs.field.pasta.word.sbb
  rfl

theorem field.pasta.word.subtract_limbs_loop.body :
    @CommonProductDotIter.field.pasta.word.subtract_limbs_loop.body = @CommonProductPairs.field.pasta.word.subtract_limbs_loop.body := by
  unfold CommonProductDotIter.field.pasta.word.subtract_limbs_loop.body CommonProductPairs.field.pasta.word.subtract_limbs_loop.body
  simp only [field.pasta.word.sbb] <;> rfl

theorem field.pasta.word.subtract_limbs_loop :
    @CommonProductDotIter.field.pasta.word.subtract_limbs_loop = @CommonProductPairs.field.pasta.word.subtract_limbs_loop := by
  unfold CommonProductDotIter.field.pasta.word.subtract_limbs_loop CommonProductPairs.field.pasta.word.subtract_limbs_loop
  simp only [field.pasta.word.subtract_limbs_loop.body] <;> rfl

theorem field.pasta.word.subtract_limbs :
    @CommonProductDotIter.field.pasta.word.subtract_limbs = @CommonProductPairs.field.pasta.word.subtract_limbs := by
  unfold CommonProductDotIter.field.pasta.word.subtract_limbs CommonProductPairs.field.pasta.word.subtract_limbs
  simp only [field.pasta.word.subtract_limbs_loop] <;> rfl

theorem field.pasta.montgomery.reduce_once :
    @CommonProductDotIter.field.pasta.montgomery.reduce_once = @CommonProductPairs.field.pasta.montgomery.reduce_once := by
  unfold CommonProductDotIter.field.pasta.montgomery.reduce_once CommonProductPairs.field.pasta.montgomery.reduce_once
  simp only [field.pasta.word.subtract_limbs] <;> rfl

theorem field.pasta.montgomery.reduce_twice_modulus :
    @CommonProductDotIter.field.pasta.montgomery.reduce_twice_modulus = @CommonProductPairs.field.pasta.montgomery.reduce_twice_modulus := by
  unfold CommonProductDotIter.field.pasta.montgomery.reduce_twice_modulus CommonProductPairs.field.pasta.montgomery.reduce_twice_modulus
  simp only [field.pasta.word.subtract_limbs] <;> rfl

theorem field.pasta.word.mac :
    @CommonProductDotIter.field.pasta.word.mac = @CommonProductPairs.field.pasta.word.mac := by
  unfold CommonProductDotIter.field.pasta.word.mac CommonProductPairs.field.pasta.word.mac
  rfl

theorem field.pasta.word.adc :
    @CommonProductDotIter.field.pasta.word.adc = @CommonProductPairs.field.pasta.word.adc := by
  unfold CommonProductDotIter.field.pasta.word.adc CommonProductPairs.field.pasta.word.adc
  rfl

theorem field.pasta.montgomery.montgomery_reduce_unreduced_loop.body :
    @CommonProductDotIter.field.pasta.montgomery.montgomery_reduce_unreduced_loop.body = @CommonProductPairs.field.pasta.montgomery.montgomery_reduce_unreduced_loop.body := by
  unfold CommonProductDotIter.field.pasta.montgomery.montgomery_reduce_unreduced_loop.body CommonProductPairs.field.pasta.montgomery.montgomery_reduce_unreduced_loop.body
  simp only [field.pasta.word.mac, field.pasta.word.adc] <;> rfl

theorem field.pasta.montgomery.montgomery_reduce_unreduced_loop :
    @CommonProductDotIter.field.pasta.montgomery.montgomery_reduce_unreduced_loop = @CommonProductPairs.field.pasta.montgomery.montgomery_reduce_unreduced_loop := by
  unfold CommonProductDotIter.field.pasta.montgomery.montgomery_reduce_unreduced_loop CommonProductPairs.field.pasta.montgomery.montgomery_reduce_unreduced_loop
  simp only [field.pasta.montgomery.montgomery_reduce_unreduced_loop.body] <;> rfl

theorem field.pasta.montgomery.montgomery_reduce_unreduced :
    @CommonProductDotIter.field.pasta.montgomery.montgomery_reduce_unreduced = @CommonProductPairs.field.pasta.montgomery.montgomery_reduce_unreduced := by
  unfold CommonProductDotIter.field.pasta.montgomery.montgomery_reduce_unreduced CommonProductPairs.field.pasta.montgomery.montgomery_reduce_unreduced
  simp only [field.pasta.word.adc, field.pasta.montgomery.montgomery_reduce_unreduced_loop] <;> rfl

theorem field.pasta.word.multiply_wide_loop0_loop0.body :
    @CommonProductDotIter.field.pasta.word.multiply_wide_loop0_loop0.body = @CommonProductPairs.field.pasta.word.multiply_wide_loop0_loop0.body := by
  unfold CommonProductDotIter.field.pasta.word.multiply_wide_loop0_loop0.body CommonProductPairs.field.pasta.word.multiply_wide_loop0_loop0.body
  simp only [field.pasta.word.mac] <;> rfl

theorem field.pasta.word.multiply_wide_loop0_loop0 :
    @CommonProductDotIter.field.pasta.word.multiply_wide_loop0_loop0 = @CommonProductPairs.field.pasta.word.multiply_wide_loop0_loop0 := by
  unfold CommonProductDotIter.field.pasta.word.multiply_wide_loop0_loop0 CommonProductPairs.field.pasta.word.multiply_wide_loop0_loop0
  simp only [field.pasta.word.multiply_wide_loop0_loop0.body] <;> rfl

theorem field.pasta.word.multiply_wide_loop0.body :
    @CommonProductDotIter.field.pasta.word.multiply_wide_loop0.body = @CommonProductPairs.field.pasta.word.multiply_wide_loop0.body := by
  unfold CommonProductDotIter.field.pasta.word.multiply_wide_loop0.body CommonProductPairs.field.pasta.word.multiply_wide_loop0.body
  simp only [field.pasta.word.multiply_wide_loop0_loop0] <;> rfl

theorem field.pasta.word.multiply_wide_loop0 :
    @CommonProductDotIter.field.pasta.word.multiply_wide_loop0 = @CommonProductPairs.field.pasta.word.multiply_wide_loop0 := by
  unfold CommonProductDotIter.field.pasta.word.multiply_wide_loop0 CommonProductPairs.field.pasta.word.multiply_wide_loop0
  simp only [field.pasta.word.multiply_wide_loop0.body] <;> rfl

theorem field.pasta.word.multiply_wide :
    @CommonProductDotIter.field.pasta.word.multiply_wide = @CommonProductPairs.field.pasta.word.multiply_wide := by
  unfold CommonProductDotIter.field.pasta.word.multiply_wide CommonProductPairs.field.pasta.word.multiply_wide
  simp only [field.pasta.word.multiply_wide_loop0] <;> rfl

theorem field.pasta.products.fold_high :
    @CommonProductDotIter.field.pasta.products.fold_high = @CommonProductPairs.field.pasta.products.fold_high := by
  unfold CommonProductDotIter.field.pasta.products.fold_high CommonProductPairs.field.pasta.products.fold_high
  simp only [field.pasta.montgomery.reduce_once, field.pasta.montgomery.reduce_twice_modulus] <;> rfl

theorem field.pasta.products.ProductSum.new :
    @CommonProductDotIter.field.pasta.products.ProductSum.new = @CommonProductPairs.field.pasta.products.ProductSum.new := by
  unfold CommonProductDotIter.field.pasta.products.ProductSum.new CommonProductPairs.field.pasta.products.ProductSum.new
  rfl

theorem field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut
  simp only [field.pasta.products.ProductSum.new] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum.call_once :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum.call_once = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum.call_once := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum.call_once CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum.call_once
  simp only [field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum
  simp only [field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum.call_once] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum
  simp only [field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut, field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD
  rfl

theorem field.pasta.products.PastaField.sum_of_products_slice.LANES :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice.LANES = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.LANES := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice.LANES CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.LANES
  rfl

theorem field.pasta.products.ProductSum.partial_reduce :
    @CommonProductDotIter.field.pasta.products.ProductSum.partial_reduce = @CommonProductPairs.field.pasta.products.ProductSum.partial_reduce := by
  unfold CommonProductDotIter.field.pasta.products.ProductSum.partial_reduce CommonProductPairs.field.pasta.products.ProductSum.partial_reduce
  simp only [field.pasta.word.mac, field.pasta.word.adc] <;> rfl

theorem field.pasta.products.ProductSum.finish :
    @CommonProductDotIter.field.pasta.products.ProductSum.finish = @CommonProductPairs.field.pasta.products.ProductSum.finish := by
  unfold CommonProductDotIter.field.pasta.products.ProductSum.finish CommonProductPairs.field.pasta.products.ProductSum.finish
  simp only [field.pasta.PastaField.from_montgomery, field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState, field.pasta.montgomery.montgomery_reduce_unreduced, field.pasta.products.ProductSum.partial_reduce] <;> rfl

theorem field.pasta.products.ProductSum.fold_overflow_loop0.body :
    @CommonProductDotIter.field.pasta.products.ProductSum.fold_overflow_loop0.body = @CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop0.body := by
  unfold CommonProductDotIter.field.pasta.products.ProductSum.fold_overflow_loop0.body CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop0.body
  simp only [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator, field.pasta.word.adc] <;> rfl

theorem field.pasta.products.ProductSum.fold_overflow_loop0 :
    @CommonProductDotIter.field.pasta.products.ProductSum.fold_overflow_loop0 = @CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop0 := by
  unfold CommonProductDotIter.field.pasta.products.ProductSum.fold_overflow_loop0 CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop0
  simp only [field.pasta.products.ProductSum.fold_overflow_loop0.body] <;> rfl

theorem field.pasta.products.ProductSum.fold_overflow_loop1.body :
    @CommonProductDotIter.field.pasta.products.ProductSum.fold_overflow_loop1.body = @CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop1.body := by
  unfold CommonProductDotIter.field.pasta.products.ProductSum.fold_overflow_loop1.body CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop1.body
  simp only [field.pasta.word.adc] <;> rfl

theorem field.pasta.products.ProductSum.fold_overflow_loop1 :
    @CommonProductDotIter.field.pasta.products.ProductSum.fold_overflow_loop1 = @CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop1 := by
  unfold CommonProductDotIter.field.pasta.products.ProductSum.fold_overflow_loop1 CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop1
  simp only [field.pasta.products.ProductSum.fold_overflow_loop1.body] <;> rfl

theorem field.pasta.products.ProductSum.fold_overflow :
    @CommonProductDotIter.field.pasta.products.ProductSum.fold_overflow = @CommonProductPairs.field.pasta.products.ProductSum.fold_overflow := by
  unfold CommonProductDotIter.field.pasta.products.ProductSum.fold_overflow CommonProductPairs.field.pasta.products.ProductSum.fold_overflow
  simp only [Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter, field.pasta.products.ProductSum.partial_reduce, field.pasta.products.ProductSum.fold_overflow_loop0, field.pasta.products.ProductSum.fold_overflow_loop1] <;> rfl

theorem field.pasta.products.ProductSum.merge :
    @CommonProductDotIter.field.pasta.products.ProductSum.merge = @CommonProductPairs.field.pasta.products.ProductSum.merge := by
  unfold CommonProductDotIter.field.pasta.products.ProductSum.merge CommonProductPairs.field.pasta.products.ProductSum.merge
  simp only [field.pasta.word.adc, field.pasta.products.ProductSum.fold_overflow] <;> rfl

theorem field.pasta.products.ProductSum.add_product_inner :
    @CommonProductDotIter.field.pasta.products.ProductSum.add_product_inner = @CommonProductPairs.field.pasta.products.ProductSum.add_product_inner := by
  unfold CommonProductDotIter.field.pasta.products.ProductSum.add_product_inner CommonProductPairs.field.pasta.products.ProductSum.add_product_inner
  simp only [field.pasta.word.mac, field.pasta.word.adc, field.pasta.products.ProductSum.fold_overflow] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop0.body :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop0.body = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop0.body := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop0.body CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop0.body
  simp only [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator, Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter, field.pasta.word.adc, field.pasta.word.multiply_wide] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop0 :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop0 = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop0 := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop0 CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop0
  simp only [field.pasta.products.PastaField.sum_of_products_slice_loop0.body] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop1.body :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop1.body = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop1.body := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop1.body CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop1.body
  simp only [field.pasta.products.ProductSum.add_product_inner] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop1 :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop1 = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop1 := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop1 CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop1
  simp only [field.pasta.products.PastaField.sum_of_products_slice_loop1.body] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop2.body :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop2.body = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop2.body := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop2.body CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop2.body
  simp only [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair, field.pasta.products.ProductSum.add_product_inner] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop2 :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop2 = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop2 := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop2 CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop2
  simp only [field.pasta.products.PastaField.sum_of_products_slice_loop2.body] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop3.body :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop3.body = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop3.body := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop3.body CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop3.body
  simp only [field.pasta.products.ProductSum.add_product_inner] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop3 :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop3 = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop3 := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop3 CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop3
  simp only [field.pasta.products.PastaField.sum_of_products_slice_loop3.body] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop4.body :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop4.body = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop4.body := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop4.body CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop4.body
  simp only [field.pasta.products.ProductSum.merge] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop4 :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop4 = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop4 := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice_loop4 CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop4
  simp only [field.pasta.products.PastaField.sum_of_products_slice_loop4.body] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice = @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_products_slice CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice
  simp only [field.pasta.PastaField.ZERO, field.pasta.PastaField.from_montgomery, field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState, field.pasta.PastaField.mul, field.pasta.montgomery.montgomery_reduce_unreduced, field.pasta.products.fold_high, field.pasta.products.ProductSum.new, field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum, field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD, field.pasta.products.PastaField.sum_of_products_slice.LANES, field.pasta.products.ProductSum.finish, field.pasta.products.PastaField.sum_of_products_slice_loop0, field.pasta.products.PastaField.sum_of_products_slice_loop1, field.pasta.products.PastaField.sum_of_products_slice_loop2, field.pasta.products.PastaField.sum_of_products_slice_loop3, field.pasta.products.PastaField.sum_of_products_slice_loop4] <;> rfl

theorem field.pasta.products.ProductSum.add_product :
    @CommonProductDotIter.field.pasta.products.ProductSum.add_product = @CommonProductPairs.field.pasta.products.ProductSum.add_product := by
  unfold CommonProductDotIter.field.pasta.products.ProductSum.add_product CommonProductPairs.field.pasta.products.ProductSum.add_product
  simp only [field.pasta.products.ProductSum.add_product_inner] <;> rfl

theorem field.pasta.products.PastaField.sum_of_product_pairs_loop.body :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_product_pairs_loop.body = @CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs_loop.body := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_product_pairs_loop.body CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs_loop.body
  simp only [field.pasta.products.ProductSum.add_product] <;> rfl

theorem field.pasta.products.PastaField.sum_of_product_pairs_loop :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_product_pairs_loop = @CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs_loop := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_product_pairs_loop CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs_loop
  simp only [field.pasta.products.PastaField.sum_of_product_pairs_loop.body] <;> rfl

theorem field.pasta.products.PastaField.sum_of_product_pairs :
    @CommonProductDotIter.field.pasta.products.PastaField.sum_of_product_pairs = @CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs := by
  unfold CommonProductDotIter.field.pasta.products.PastaField.sum_of_product_pairs CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs
  simp only [field.pasta.PastaField.ZERO, field.pasta.PastaField.mul, field.pasta.products.ProductSum.new, field.pasta.products.ProductSum.finish, field.pasta.products.ProductSum.add_product_inner, field.pasta.products.PastaField.sum_of_products_slice, field.pasta.products.PastaField.sum_of_product_pairs_loop] <;> rfl

#print axioms core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
#print axioms Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter
#print axioms core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
#print axioms field.pasta.PastaField.ZERO
#print axioms field.pasta.word.compare_limbs_loop.body
#print axioms field.pasta.word.compare_limbs_loop
#print axioms field.pasta.word.compare_limbs
#print axioms field.pasta.PastaField.BOUND
#print axioms field.pasta.PastaField.from_montgomery
#print axioms field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED
#print axioms field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed
#print axioms field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose.eq
#print axioms field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose
#print axioms field.pasta.representation.Loose.Insts.CoreCmpEq
#print axioms field.pasta.representation.Loose.Insts.CoreCloneClone.clone
#print axioms field.pasta.representation.Loose.Insts.CoreCloneClone
#print axioms field.pasta.representation.Loose.Insts.CoreMarkerCopy
#print axioms field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState
#print axioms field.pasta.word.wide_mul
#print axioms field.pasta.word.carry_add
#print axioms field.pasta.montgomery.montgomery_multiply_loose_rust_loop.body
#print axioms field.pasta.montgomery.montgomery_multiply_loose_rust_loop
#print axioms field.pasta.montgomery.montgomery_multiply_loose_rust
#print axioms field.pasta.montgomery.montgomery_multiply_loose
#print axioms field.pasta.PastaField.mul
#print axioms field.pasta.word.sbb
#print axioms field.pasta.word.subtract_limbs_loop.body
#print axioms field.pasta.word.subtract_limbs_loop
#print axioms field.pasta.word.subtract_limbs
#print axioms field.pasta.montgomery.reduce_once
#print axioms field.pasta.montgomery.reduce_twice_modulus
#print axioms field.pasta.word.mac
#print axioms field.pasta.word.adc
#print axioms field.pasta.montgomery.montgomery_reduce_unreduced_loop.body
#print axioms field.pasta.montgomery.montgomery_reduce_unreduced_loop
#print axioms field.pasta.montgomery.montgomery_reduce_unreduced
#print axioms field.pasta.word.multiply_wide_loop0_loop0.body
#print axioms field.pasta.word.multiply_wide_loop0_loop0
#print axioms field.pasta.word.multiply_wide_loop0.body
#print axioms field.pasta.word.multiply_wide_loop0
#print axioms field.pasta.word.multiply_wide
#print axioms field.pasta.products.fold_high
#print axioms field.pasta.products.ProductSum.new
#print axioms field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut
#print axioms field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum.call_once
#print axioms field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum
#print axioms field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum
#print axioms field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD
#print axioms field.pasta.products.PastaField.sum_of_products_slice.LANES
#print axioms field.pasta.products.ProductSum.partial_reduce
#print axioms field.pasta.products.ProductSum.finish
#print axioms field.pasta.products.ProductSum.fold_overflow_loop0.body
#print axioms field.pasta.products.ProductSum.fold_overflow_loop0
#print axioms field.pasta.products.ProductSum.fold_overflow_loop1.body
#print axioms field.pasta.products.ProductSum.fold_overflow_loop1
#print axioms field.pasta.products.ProductSum.fold_overflow
#print axioms field.pasta.products.ProductSum.merge
#print axioms field.pasta.products.ProductSum.add_product_inner
#print axioms field.pasta.products.PastaField.sum_of_products_slice_loop0.body
#print axioms field.pasta.products.PastaField.sum_of_products_slice_loop0
#print axioms field.pasta.products.PastaField.sum_of_products_slice_loop1.body
#print axioms field.pasta.products.PastaField.sum_of_products_slice_loop1
#print axioms field.pasta.products.PastaField.sum_of_products_slice_loop2.body
#print axioms field.pasta.products.PastaField.sum_of_products_slice_loop2
#print axioms field.pasta.products.PastaField.sum_of_products_slice_loop3.body
#print axioms field.pasta.products.PastaField.sum_of_products_slice_loop3
#print axioms field.pasta.products.PastaField.sum_of_products_slice_loop4.body
#print axioms field.pasta.products.PastaField.sum_of_products_slice_loop4
#print axioms field.pasta.products.PastaField.sum_of_products_slice
#print axioms field.pasta.products.ProductSum.add_product
#print axioms field.pasta.products.PastaField.sum_of_product_pairs_loop.body
#print axioms field.pasta.products.PastaField.sum_of_product_pairs_loop
#print axioms field.pasta.products.PastaField.sum_of_product_pairs
end UdonVerify.ProductWrappers.DotBridge
