import CommonProductPairs.Funs
import CommonProductsPortable.Funs

open Aeneas Std Result
namespace UdonVerify.ProductPairs.PortableBridge
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

theorem core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator :
    @CommonProductPairs.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator = @CommonProductsPortable.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator := by
  unfold CommonProductPairs.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator CommonProductsPortable.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
  rfl

theorem Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter :
    @CommonProductPairs.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter = @CommonProductsPortable.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter := by
  unfold CommonProductPairs.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter CommonProductsPortable.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter
  simp only [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator] <;> rfl

theorem core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair :
    @CommonProductPairs.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair = @CommonProductsPortable.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair := by
  unfold CommonProductPairs.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair CommonProductsPortable.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
  rfl

theorem field.pasta.PastaField.ZERO :
    @CommonProductPairs.field.pasta.PastaField.ZERO = @CommonProductsPortable.field.pasta.PastaField.ZERO := by
  unfold CommonProductPairs.field.pasta.PastaField.ZERO CommonProductsPortable.field.pasta.PastaField.ZERO
  rfl

theorem field.pasta.word.compare_limbs_loop.body :
    @CommonProductPairs.field.pasta.word.compare_limbs_loop.body = @CommonProductsPortable.field.pasta.word.compare_limbs_loop.body := by
  unfold CommonProductPairs.field.pasta.word.compare_limbs_loop.body CommonProductsPortable.field.pasta.word.compare_limbs_loop.body
  rfl

theorem field.pasta.word.compare_limbs_loop :
    @CommonProductPairs.field.pasta.word.compare_limbs_loop = @CommonProductsPortable.field.pasta.word.compare_limbs_loop := by
  unfold CommonProductPairs.field.pasta.word.compare_limbs_loop CommonProductsPortable.field.pasta.word.compare_limbs_loop
  simp only [field.pasta.word.compare_limbs_loop.body] <;> rfl

theorem field.pasta.word.compare_limbs :
    @CommonProductPairs.field.pasta.word.compare_limbs = @CommonProductsPortable.field.pasta.word.compare_limbs := by
  unfold CommonProductPairs.field.pasta.word.compare_limbs CommonProductsPortable.field.pasta.word.compare_limbs
  simp only [field.pasta.word.compare_limbs_loop] <;> rfl

theorem field.pasta.PastaField.BOUND :
    @CommonProductPairs.field.pasta.PastaField.BOUND = @CommonProductsPortable.field.pasta.PastaField.BOUND := by
  unfold CommonProductPairs.field.pasta.PastaField.BOUND CommonProductsPortable.field.pasta.PastaField.BOUND
  rfl

theorem field.pasta.PastaField.from_montgomery :
    @CommonProductPairs.field.pasta.PastaField.from_montgomery = @CommonProductsPortable.field.pasta.PastaField.from_montgomery := by
  unfold CommonProductPairs.field.pasta.PastaField.from_montgomery CommonProductsPortable.field.pasta.PastaField.from_montgomery
  simp only [field.pasta.word.compare_limbs, field.pasta.PastaField.BOUND] <;> rfl

theorem field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED :
    @CommonProductPairs.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED = @CommonProductsPortable.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED := by
  unfold CommonProductPairs.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED CommonProductsPortable.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED
  rfl

theorem field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed :
    @CommonProductPairs.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed = @CommonProductsPortable.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed := by
  unfold CommonProductPairs.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed CommonProductsPortable.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed
  simp only [field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED] <;> rfl

theorem field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose.eq :
    @CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose.eq = @CommonProductsPortable.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose.eq := by
  unfold CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose.eq CommonProductsPortable.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose.eq
  rfl

theorem field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose :
    @CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose = @CommonProductsPortable.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose := by
  unfold CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose CommonProductsPortable.field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose
  simp only [field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose.eq] <;> rfl

theorem field.pasta.representation.Loose.Insts.CoreCmpEq :
    @CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCmpEq = @CommonProductsPortable.field.pasta.representation.Loose.Insts.CoreCmpEq := by
  unfold CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCmpEq CommonProductsPortable.field.pasta.representation.Loose.Insts.CoreCmpEq
  simp only [field.pasta.representation.Loose.Insts.CoreCmpPartialEqLoose] <;> rfl

theorem field.pasta.representation.Loose.Insts.CoreCloneClone.clone :
    @CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCloneClone.clone = @CommonProductsPortable.field.pasta.representation.Loose.Insts.CoreCloneClone.clone := by
  unfold CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCloneClone.clone CommonProductsPortable.field.pasta.representation.Loose.Insts.CoreCloneClone.clone
  rfl

theorem field.pasta.representation.Loose.Insts.CoreCloneClone :
    @CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCloneClone = @CommonProductsPortable.field.pasta.representation.Loose.Insts.CoreCloneClone := by
  unfold CommonProductPairs.field.pasta.representation.Loose.Insts.CoreCloneClone CommonProductsPortable.field.pasta.representation.Loose.Insts.CoreCloneClone
  simp only [field.pasta.representation.Loose.Insts.CoreCloneClone.clone] <;> rfl

theorem field.pasta.representation.Loose.Insts.CoreMarkerCopy :
    @CommonProductPairs.field.pasta.representation.Loose.Insts.CoreMarkerCopy = @CommonProductsPortable.field.pasta.representation.Loose.Insts.CoreMarkerCopy := by
  unfold CommonProductPairs.field.pasta.representation.Loose.Insts.CoreMarkerCopy CommonProductsPortable.field.pasta.representation.Loose.Insts.CoreMarkerCopy
  simp only [field.pasta.representation.Loose.Insts.CoreCloneClone] <;> rfl

theorem field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState :
    @CommonProductPairs.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState = @CommonProductsPortable.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState := by
  unfold CommonProductPairs.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState CommonProductsPortable.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState
  simp only [field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed, field.pasta.representation.Loose.Insts.CoreCmpEq, field.pasta.representation.Loose.Insts.CoreMarkerCopy] <;> rfl

theorem field.pasta.word.wide_mul :
    @CommonProductPairs.field.pasta.word.wide_mul = @CommonProductsPortable.field.pasta.word.wide_mul := by
  unfold CommonProductPairs.field.pasta.word.wide_mul CommonProductsPortable.field.pasta.word.wide_mul
  rfl

theorem field.pasta.word.carry_add :
    @CommonProductPairs.field.pasta.word.carry_add = @CommonProductsPortable.field.pasta.word.carry_add := by
  unfold CommonProductPairs.field.pasta.word.carry_add CommonProductsPortable.field.pasta.word.carry_add
  rfl

theorem field.pasta.montgomery.montgomery_multiply_loose_rust_loop.body :
    @CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose_rust_loop.body = @CommonProductsPortable.field.pasta.montgomery.montgomery_multiply_loose_rust_loop.body := by
  unfold CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose_rust_loop.body CommonProductsPortable.field.pasta.montgomery.montgomery_multiply_loose_rust_loop.body
  simp only [field.pasta.word.wide_mul, field.pasta.word.carry_add] <;> rfl

theorem field.pasta.montgomery.montgomery_multiply_loose_rust_loop :
    @CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose_rust_loop = @CommonProductsPortable.field.pasta.montgomery.montgomery_multiply_loose_rust_loop := by
  unfold CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose_rust_loop CommonProductsPortable.field.pasta.montgomery.montgomery_multiply_loose_rust_loop
  simp only [field.pasta.montgomery.montgomery_multiply_loose_rust_loop.body] <;> rfl

theorem field.pasta.montgomery.montgomery_multiply_loose_rust :
    @CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose_rust = @CommonProductsPortable.field.pasta.montgomery.montgomery_multiply_loose_rust := by
  unfold CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose_rust CommonProductsPortable.field.pasta.montgomery.montgomery_multiply_loose_rust
  simp only [field.pasta.montgomery.montgomery_multiply_loose_rust_loop] <;> rfl

theorem field.pasta.montgomery.montgomery_multiply_loose :
    @CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose = @CommonProductsPortable.field.pasta.montgomery.montgomery_multiply_loose := by
  unfold CommonProductPairs.field.pasta.montgomery.montgomery_multiply_loose CommonProductsPortable.field.pasta.montgomery.montgomery_multiply_loose
  simp only [field.pasta.word.compare_limbs, field.pasta.montgomery.montgomery_multiply_loose_rust] <;> rfl

theorem field.pasta.PastaField.mul :
    @CommonProductPairs.field.pasta.PastaField.mul = @CommonProductsPortable.field.pasta.PastaField.mul := by
  unfold CommonProductPairs.field.pasta.PastaField.mul CommonProductsPortable.field.pasta.PastaField.mul
  simp only [field.pasta.PastaField.from_montgomery, field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState, field.pasta.montgomery.montgomery_multiply_loose] <;> rfl

theorem field.pasta.word.sbb :
    @CommonProductPairs.field.pasta.word.sbb = @CommonProductsPortable.field.pasta.word.sbb := by
  unfold CommonProductPairs.field.pasta.word.sbb CommonProductsPortable.field.pasta.word.sbb
  rfl

theorem field.pasta.word.subtract_limbs_loop.body :
    @CommonProductPairs.field.pasta.word.subtract_limbs_loop.body = @CommonProductsPortable.field.pasta.word.subtract_limbs_loop.body := by
  unfold CommonProductPairs.field.pasta.word.subtract_limbs_loop.body CommonProductsPortable.field.pasta.word.subtract_limbs_loop.body
  simp only [field.pasta.word.sbb] <;> rfl

theorem field.pasta.word.subtract_limbs_loop :
    @CommonProductPairs.field.pasta.word.subtract_limbs_loop = @CommonProductsPortable.field.pasta.word.subtract_limbs_loop := by
  unfold CommonProductPairs.field.pasta.word.subtract_limbs_loop CommonProductsPortable.field.pasta.word.subtract_limbs_loop
  simp only [field.pasta.word.subtract_limbs_loop.body] <;> rfl

theorem field.pasta.word.subtract_limbs :
    @CommonProductPairs.field.pasta.word.subtract_limbs = @CommonProductsPortable.field.pasta.word.subtract_limbs := by
  unfold CommonProductPairs.field.pasta.word.subtract_limbs CommonProductsPortable.field.pasta.word.subtract_limbs
  simp only [field.pasta.word.subtract_limbs_loop] <;> rfl

theorem field.pasta.montgomery.reduce_once :
    @CommonProductPairs.field.pasta.montgomery.reduce_once = @CommonProductsPortable.field.pasta.montgomery.reduce_once := by
  unfold CommonProductPairs.field.pasta.montgomery.reduce_once CommonProductsPortable.field.pasta.montgomery.reduce_once
  simp only [field.pasta.word.subtract_limbs] <;> rfl

theorem field.pasta.montgomery.reduce_twice_modulus :
    @CommonProductPairs.field.pasta.montgomery.reduce_twice_modulus = @CommonProductsPortable.field.pasta.montgomery.reduce_twice_modulus := by
  unfold CommonProductPairs.field.pasta.montgomery.reduce_twice_modulus CommonProductsPortable.field.pasta.montgomery.reduce_twice_modulus
  simp only [field.pasta.word.subtract_limbs] <;> rfl

theorem field.pasta.word.mac :
    @CommonProductPairs.field.pasta.word.mac = @CommonProductsPortable.field.pasta.word.mac := by
  unfold CommonProductPairs.field.pasta.word.mac CommonProductsPortable.field.pasta.word.mac
  rfl

theorem field.pasta.word.adc :
    @CommonProductPairs.field.pasta.word.adc = @CommonProductsPortable.field.pasta.word.adc := by
  unfold CommonProductPairs.field.pasta.word.adc CommonProductsPortable.field.pasta.word.adc
  rfl

theorem field.pasta.montgomery.montgomery_reduce_unreduced_loop.body :
    @CommonProductPairs.field.pasta.montgomery.montgomery_reduce_unreduced_loop.body = @CommonProductsPortable.field.pasta.montgomery.montgomery_reduce_unreduced_loop.body := by
  unfold CommonProductPairs.field.pasta.montgomery.montgomery_reduce_unreduced_loop.body CommonProductsPortable.field.pasta.montgomery.montgomery_reduce_unreduced_loop.body
  simp only [field.pasta.word.mac, field.pasta.word.adc] <;> rfl

theorem field.pasta.montgomery.montgomery_reduce_unreduced_loop :
    @CommonProductPairs.field.pasta.montgomery.montgomery_reduce_unreduced_loop = @CommonProductsPortable.field.pasta.montgomery.montgomery_reduce_unreduced_loop := by
  unfold CommonProductPairs.field.pasta.montgomery.montgomery_reduce_unreduced_loop CommonProductsPortable.field.pasta.montgomery.montgomery_reduce_unreduced_loop
  simp only [field.pasta.montgomery.montgomery_reduce_unreduced_loop.body] <;> rfl

theorem field.pasta.montgomery.montgomery_reduce_unreduced :
    @CommonProductPairs.field.pasta.montgomery.montgomery_reduce_unreduced = @CommonProductsPortable.field.pasta.montgomery.montgomery_reduce_unreduced := by
  unfold CommonProductPairs.field.pasta.montgomery.montgomery_reduce_unreduced CommonProductsPortable.field.pasta.montgomery.montgomery_reduce_unreduced
  simp only [field.pasta.word.adc, field.pasta.montgomery.montgomery_reduce_unreduced_loop] <;> rfl

theorem field.pasta.word.multiply_wide_loop0_loop0.body :
    @CommonProductPairs.field.pasta.word.multiply_wide_loop0_loop0.body = @CommonProductsPortable.field.pasta.word.multiply_wide_loop0_loop0.body := by
  unfold CommonProductPairs.field.pasta.word.multiply_wide_loop0_loop0.body CommonProductsPortable.field.pasta.word.multiply_wide_loop0_loop0.body
  simp only [field.pasta.word.mac] <;> rfl

theorem field.pasta.word.multiply_wide_loop0_loop0 :
    @CommonProductPairs.field.pasta.word.multiply_wide_loop0_loop0 = @CommonProductsPortable.field.pasta.word.multiply_wide_loop0_loop0 := by
  unfold CommonProductPairs.field.pasta.word.multiply_wide_loop0_loop0 CommonProductsPortable.field.pasta.word.multiply_wide_loop0_loop0
  simp only [field.pasta.word.multiply_wide_loop0_loop0.body] <;> rfl

theorem field.pasta.word.multiply_wide_loop0.body :
    @CommonProductPairs.field.pasta.word.multiply_wide_loop0.body = @CommonProductsPortable.field.pasta.word.multiply_wide_loop0.body := by
  unfold CommonProductPairs.field.pasta.word.multiply_wide_loop0.body CommonProductsPortable.field.pasta.word.multiply_wide_loop0.body
  simp only [field.pasta.word.multiply_wide_loop0_loop0] <;> rfl

theorem field.pasta.word.multiply_wide_loop0 :
    @CommonProductPairs.field.pasta.word.multiply_wide_loop0 = @CommonProductsPortable.field.pasta.word.multiply_wide_loop0 := by
  unfold CommonProductPairs.field.pasta.word.multiply_wide_loop0 CommonProductsPortable.field.pasta.word.multiply_wide_loop0
  simp only [field.pasta.word.multiply_wide_loop0.body] <;> rfl

theorem field.pasta.word.multiply_wide :
    @CommonProductPairs.field.pasta.word.multiply_wide = @CommonProductsPortable.field.pasta.word.multiply_wide := by
  unfold CommonProductPairs.field.pasta.word.multiply_wide CommonProductsPortable.field.pasta.word.multiply_wide
  simp only [field.pasta.word.multiply_wide_loop0] <;> rfl

theorem field.pasta.products.fold_high :
    @CommonProductPairs.field.pasta.products.fold_high = @CommonProductsPortable.field.pasta.products.fold_high := by
  unfold CommonProductPairs.field.pasta.products.fold_high CommonProductsPortable.field.pasta.products.fold_high
  simp only [field.pasta.montgomery.reduce_once, field.pasta.montgomery.reduce_twice_modulus] <;> rfl

theorem field.pasta.products.ProductSum.new :
    @CommonProductPairs.field.pasta.products.ProductSum.new = @CommonProductsPortable.field.pasta.products.ProductSum.new := by
  unfold CommonProductPairs.field.pasta.products.ProductSum.new CommonProductsPortable.field.pasta.products.ProductSum.new
  rfl

theorem field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut
  simp only [field.pasta.products.ProductSum.new] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum.call_once :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum.call_once = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum.call_once := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum.call_once CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum.call_once
  simp only [field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum
  simp only [field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum.call_once] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum
  simp only [field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut, field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeProductSum] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD
  rfl

theorem field.pasta.products.PastaField.sum_of_products_slice.LANES :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.LANES = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.LANES := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice.LANES CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.LANES
  rfl

theorem field.pasta.products.ProductSum.partial_reduce :
    @CommonProductPairs.field.pasta.products.ProductSum.partial_reduce = @CommonProductsPortable.field.pasta.products.ProductSum.partial_reduce := by
  unfold CommonProductPairs.field.pasta.products.ProductSum.partial_reduce CommonProductsPortable.field.pasta.products.ProductSum.partial_reduce
  simp only [field.pasta.word.mac, field.pasta.word.adc] <;> rfl

theorem field.pasta.products.ProductSum.finish :
    @CommonProductPairs.field.pasta.products.ProductSum.finish = @CommonProductsPortable.field.pasta.products.ProductSum.finish := by
  unfold CommonProductPairs.field.pasta.products.ProductSum.finish CommonProductsPortable.field.pasta.products.ProductSum.finish
  simp only [field.pasta.PastaField.from_montgomery, field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState, field.pasta.montgomery.montgomery_reduce_unreduced, field.pasta.products.ProductSum.partial_reduce] <;> rfl

theorem field.pasta.products.ProductSum.fold_overflow_loop0.body :
    @CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop0.body = @CommonProductsPortable.field.pasta.products.ProductSum.fold_overflow_loop0.body := by
  unfold CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop0.body CommonProductsPortable.field.pasta.products.ProductSum.fold_overflow_loop0.body
  simp only [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator, field.pasta.word.adc] <;> rfl

theorem field.pasta.products.ProductSum.fold_overflow_loop0 :
    @CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop0 = @CommonProductsPortable.field.pasta.products.ProductSum.fold_overflow_loop0 := by
  unfold CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop0 CommonProductsPortable.field.pasta.products.ProductSum.fold_overflow_loop0
  simp only [field.pasta.products.ProductSum.fold_overflow_loop0.body] <;> rfl

theorem field.pasta.products.ProductSum.fold_overflow_loop1.body :
    @CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop1.body = @CommonProductsPortable.field.pasta.products.ProductSum.fold_overflow_loop1.body := by
  unfold CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop1.body CommonProductsPortable.field.pasta.products.ProductSum.fold_overflow_loop1.body
  simp only [field.pasta.word.adc] <;> rfl

theorem field.pasta.products.ProductSum.fold_overflow_loop1 :
    @CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop1 = @CommonProductsPortable.field.pasta.products.ProductSum.fold_overflow_loop1 := by
  unfold CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop1 CommonProductsPortable.field.pasta.products.ProductSum.fold_overflow_loop1
  simp only [field.pasta.products.ProductSum.fold_overflow_loop1.body] <;> rfl

theorem field.pasta.products.ProductSum.fold_overflow :
    @CommonProductPairs.field.pasta.products.ProductSum.fold_overflow = @CommonProductsPortable.field.pasta.products.ProductSum.fold_overflow := by
  unfold CommonProductPairs.field.pasta.products.ProductSum.fold_overflow CommonProductsPortable.field.pasta.products.ProductSum.fold_overflow
  simp only [Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter, field.pasta.products.ProductSum.partial_reduce, field.pasta.products.ProductSum.fold_overflow_loop0, field.pasta.products.ProductSum.fold_overflow_loop1] <;> rfl

theorem field.pasta.products.ProductSum.merge :
    @CommonProductPairs.field.pasta.products.ProductSum.merge = @CommonProductsPortable.field.pasta.products.ProductSum.merge := by
  unfold CommonProductPairs.field.pasta.products.ProductSum.merge CommonProductsPortable.field.pasta.products.ProductSum.merge
  simp only [field.pasta.word.adc, field.pasta.products.ProductSum.fold_overflow] <;> rfl

theorem field.pasta.products.ProductSum.add_product_inner :
    @CommonProductPairs.field.pasta.products.ProductSum.add_product_inner = @CommonProductsPortable.field.pasta.products.ProductSum.add_product_inner := by
  unfold CommonProductPairs.field.pasta.products.ProductSum.add_product_inner CommonProductsPortable.field.pasta.products.ProductSum.add_product_inner
  simp only [field.pasta.word.mac, field.pasta.word.adc, field.pasta.products.ProductSum.fold_overflow] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop0.body :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop0.body = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop0.body := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop0.body CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop0.body
  simp only [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator, Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter, field.pasta.word.adc, field.pasta.word.multiply_wide] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop0 :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop0 = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop0 := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop0 CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop0
  simp only [field.pasta.products.PastaField.sum_of_products_slice_loop0.body] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop1.body :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop1.body = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop1.body := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop1.body CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop1.body
  simp only [field.pasta.products.ProductSum.add_product_inner] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop1 :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop1 = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop1 := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop1 CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop1
  simp only [field.pasta.products.PastaField.sum_of_products_slice_loop1.body] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop2.body :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop2.body = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop2.body := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop2.body CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop2.body
  simp only [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair, field.pasta.products.ProductSum.add_product_inner] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop2 :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop2 = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop2 := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop2 CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop2
  simp only [field.pasta.products.PastaField.sum_of_products_slice_loop2.body] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop3.body :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop3.body = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop3.body := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop3.body CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop3.body
  simp only [field.pasta.products.ProductSum.add_product_inner] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop3 :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop3 = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop3 := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop3 CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop3
  simp only [field.pasta.products.PastaField.sum_of_products_slice_loop3.body] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop4.body :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop4.body = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop4.body := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop4.body CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop4.body
  simp only [field.pasta.products.ProductSum.merge] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice_loop4 :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop4 = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop4 := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice_loop4 CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop4
  simp only [field.pasta.products.PastaField.sum_of_products_slice_loop4.body] <;> rfl

theorem field.pasta.products.PastaField.sum_of_products_slice :
    @CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice = @CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice
  simp only [field.pasta.PastaField.ZERO, field.pasta.PastaField.from_montgomery, field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState, field.pasta.PastaField.mul, field.pasta.montgomery.montgomery_reduce_unreduced, field.pasta.products.fold_high, field.pasta.products.ProductSum.new, field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum, field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD, field.pasta.products.PastaField.sum_of_products_slice.LANES, field.pasta.products.ProductSum.finish, field.pasta.products.PastaField.sum_of_products_slice_loop0, field.pasta.products.PastaField.sum_of_products_slice_loop1, field.pasta.products.PastaField.sum_of_products_slice_loop2, field.pasta.products.PastaField.sum_of_products_slice_loop3, field.pasta.products.PastaField.sum_of_products_slice_loop4] <;> rfl

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
end UdonVerify.ProductPairs.PortableBridge
