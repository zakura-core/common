import NativeLargePublicCallbacks

open Aeneas Std Result

namespace UdonVerify.LargePublicBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

noncomputable def fpConfiguration : Configuration fpSqrtInst fpSqrtParameters Native.fpRadixInverse where
  inverse_mod := Native.fp_radix_inverse
  exponent := fpSqrtExponent
  topRoot := (LargeNativeBridge.fpLargeRoot : ZMod Native.fpPrime)
  power_spec := fp_sqrt_power_spec
  starting_power := fp_sqrt_starting_power
  sqrt_spec value hv ha w hw hpower := fp_large_callback_spec value w hv ha hw hpower
  finish_spec := fp_large_finish_spec

#print axioms fpConfiguration

noncomputable def fqConfiguration : Configuration fqSqrtInst fqSqrtParameters Native.fqRadixInverse where
  inverse_mod := Native.fq_radix_inverse
  exponent := fqSqrtExponent
  topRoot := (LargeNativeBridge.fqLargeRoot : ZMod Native.fqPrime)
  power_spec := fq_sqrt_power_spec
  starting_power := fq_sqrt_starting_power
  sqrt_spec value hv ha w hw hpower := fq_large_callback_spec value w hv ha hw hpower
  finish_spec := fq_large_finish_spec

#print axioms fqConfiguration

end UdonVerify.LargePublicBridge
