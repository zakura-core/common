/*
 * Copyright Supranational LLC
 * Licensed under the Apache License, Version 2.0, see LICENSE for details.
 * SPDX-License-Identifier: Apache-2.0
 * Modified by Zakura to select only checked-in CPU assembly.
 */

#if defined(__x86_64) || defined(__x86_64__)
# if defined(__ELF__)
#  include "elf/ct_inverse_mod_256-x86_64.s"
#  include "elf/pasta_add-x86_64.s"
#  if defined(__ADX__) && !defined(__PASTA_PORTABLE__)
#   include "elf/pasta_mulx-x86_64.s"
#  else
#   include "elf/pasta_mulq-x86_64.s"
#  endif
# elif defined(_WIN64) || defined(__CYGWIN__)
#  include "coff/ct_inverse_mod_256-x86_64.s"
#  include "coff/pasta_add-x86_64.s"
#  if defined(__ADX__) && !defined(__PASTA_PORTABLE__)
#   include "coff/pasta_mulx-x86_64.s"
#  else
#   include "coff/pasta_mulq-x86_64.s"
#  endif
# elif defined(__APPLE__)
#  include "mach-o/ct_inverse_mod_256-x86_64.s"
#  include "mach-o/pasta_add-x86_64.s"
#  if defined(__ADX__) && !defined(__PASTA_PORTABLE__)
#   include "mach-o/pasta_mulx-x86_64.s"
#  else
#   include "mach-o/pasta_mulq-x86_64.s"
#  endif
# endif
#elif defined(__aarch64__)
# if defined(__ELF__)
#  include "elf/ct_inverse_mod_256-armv8.S"
#  include "elf/pasta_add-armv8.S"
#  include "elf/pasta_mul-armv8.S"
# elif defined(_WIN64)
#  include "coff/ct_inverse_mod_256-armv8.S"
#  include "coff/pasta_add-armv8.S"
#  include "coff/pasta_mul-armv8.S"
# elif defined(__APPLE__)
#  include "mach-o/ct_inverse_mod_256-armv8.S"
#  include "mach-o/pasta_add-armv8.S"
#  include "mach-o/pasta_mul-armv8.S"
# endif
#else
# error "unsupported platform"
#endif
