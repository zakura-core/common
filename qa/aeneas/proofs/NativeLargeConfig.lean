import NativeLargeSqrt
import NativeRootOrder
import NativeSqrtMath

open Aeneas Std Result

namespace UdonVerify.LargeNativeBridge
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024

abbrev fpLargeInst :=
  LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersPrimeModulus

def fpLargeParameters : PastaParameters (Native.kernelInst (nativeModulus fpLargeInst)) :=
  Native.transferParameters (Native.kernelInst (nativeModulus fpLargeInst)) fpParameters
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

theorem fp_large_prime_eq : val4 fpLargeParameters.modulus = Native.fpPrime := by rfl

abbrev fpLargeRoot := Native.rootValue Native.fpPrime Native.fpRadixInverse Native.fpRoots 32

theorem fp_large_root_primitive :
    IsPrimitiveRoot (fpLargeRoot : ZMod (val4 fpLargeParameters.modulus)) (256 ^ 4) := by
  change IsPrimitiveRoot
    (Native.rootValue Native.fpPrime Native.fpRadixInverse Native.fpRoots 32 : ZMod Native.fpPrime) (256 ^ 4)
  simpa only [show (2 : Nat) ^ 32 = 256 ^ 4 from by decide] using
    Native.fp_root_table_primitive ⟨32, by decide⟩

theorem fp_large_root_nonsquare :
    ¬ IsSquare (fpLargeRoot : ZMod (val4 fpLargeParameters.modulus)) := by
  change ¬ IsSquare
    (Native.rootValue Native.fpPrime Native.fpRadixInverse Native.fpRoots 32 : ZMod Native.fpPrime)
  exact Native.fp_sqrt_nonsquare

abbrev fqLargeInst :=
  LargeAlgorithms.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersPrimeModulus

def fqLargeParameters : PastaParameters (Native.kernelInst (nativeModulus fqLargeInst)) :=
  Native.transferParameters (Native.kernelInst (nativeModulus fqLargeInst)) fqParameters
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

theorem fq_large_prime_eq : val4 fqLargeParameters.modulus = Native.fqPrime := by rfl

abbrev fqLargeRoot := Native.rootValue Native.fqPrime Native.fqRadixInverse Native.fqRoots 32

theorem fq_large_root_primitive :
    IsPrimitiveRoot (fqLargeRoot : ZMod (val4 fqLargeParameters.modulus)) (256 ^ 4) := by
  change IsPrimitiveRoot
    (Native.rootValue Native.fqPrime Native.fqRadixInverse Native.fqRoots 32 : ZMod Native.fqPrime) (256 ^ 4)
  simpa only [show (2 : Nat) ^ 32 = 256 ^ 4 from by decide] using
    Native.fq_root_table_primitive ⟨32, by decide⟩

theorem fq_large_root_nonsquare :
    ¬ IsSquare (fqLargeRoot : ZMod (val4 fqLargeParameters.modulus)) := by
  change ¬ IsSquare
    (Native.rootValue Native.fqPrime Native.fqRadixInverse Native.fqRoots 32 : ZMod Native.fqPrime)
  exact Native.fq_sqrt_nonsquare

#print axioms fp_large_prime_eq
#print axioms fp_large_root_primitive
#print axioms fp_large_root_nonsquare
#print axioms fq_large_prime_eq
#print axioms fq_large_root_primitive
#print axioms fq_large_root_nonsquare

end UdonVerify.LargeNativeBridge
