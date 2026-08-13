#!/usr/bin/env perl
#
# Copyright Supranational LLC
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# Modified by Zakura for reproducible vendored assembly generation.

$flavour = shift;
$output  = shift;

if ($flavour && $flavour ne "void") {
    $0 =~ m/(.*[\/\\])[^\/\\]+$/; $dir=$1;
    ( $xlate="${dir}arm-xlate.pl" and -f $xlate ) or
    ( $xlate="${dir}../../perlasm/arm-xlate.pl" and -f $xlate) or
    die "can't locate arm-xlate.pl";

    open STDOUT,"| \"$^X\" $xlate $flavour $output";
} else {
    open STDOUT,">$output";
}

($r_ptr,$a_ptr,$b_ptr,$n_ptr,$n0) = map("x$_", 0..4);

@mod=map("x$_",(5..8));
$bi="x9";
@a=map("x$_",(10..13));
@tmp=map("x$_",(14..17));
@acc=map("x$_",(19..24));
$m0=$n_ptr;

$code.=<<___;
.text

.globl	mul_mont_pasta
.hidden	mul_mont_pasta
.type	mul_mont_pasta,%function
.align	5
mul_mont_pasta:
	stp	x29,x30,[sp,#-64]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]
	stp	x21,x22,[sp,#32]
	stp	x23,x24,[sp,#48]

	ldp	@a[0],@a[1],[$a_ptr]
	ldr	$bi,        [$b_ptr]
	ldp	@a[2],@a[3],[$a_ptr,#16]

	mul	@acc[0],@a[0],$bi
	ldp	@mod[0],@mod[1],[$n_ptr]
	mul	@acc[1],@a[1],$bi
	ldp	@mod[2],@mod[3],[$n_ptr,#16]
	mul	@acc[2],@a[2],$bi
	mul	@acc[3],@a[3],$bi

	 umulh	@tmp[0],@a[0],$bi
	 umulh	@tmp[1],@a[1],$bi
	mul	$m0,$n0,@acc[0]
	 umulh	@tmp[2],@a[2],$bi
	 umulh	@tmp[3],@a[3],$bi
	 adds	@acc[1],@acc[1],@tmp[0]
	//mul	@tmp[0],@mod[0],$m0
	 adcs	@acc[2],@acc[2],@tmp[1]
	mul	@tmp[1],@mod[1],$m0
	 adcs	@acc[3],@acc[3],@tmp[2]
	//mul	@tmp[2],@mod[2],$m0	//@mod[2]==0
	 adc	@acc[4],xzr,    @tmp[3]
	lsl	@tmp[3],$m0,#62		//mul	@tmp[3],@mod[3],$m0
___
for ($i=1;$i<4;$i++) {
$code.=<<___;
	ldr	$bi,[$b_ptr,8*$i]
	subs	xzr,@acc[0],#1		//adds	@acc[0],@acc[0],@tmp[0]
	 umulh	@tmp[0],@mod[0],$m0
	adcs	@acc[1],@acc[1],@tmp[1]
	 umulh	@tmp[1],@mod[1],$m0
	adcs	@acc[2],@acc[2],xzr	//@tmp[2]
	//umulh	@tmp[2],@mod[2],$m0	//@mod[2]==0
	adcs	@acc[3],@acc[3],@tmp[3]
	 lsr	@tmp[3],$m0,#2		//umulh	@tmp[3],@mod[3],$m0
	adc	@acc[4],@acc[4],xzr

	 adds	@acc[0],@acc[1],@tmp[0]
	mul	@tmp[0],@a[0],$bi
	 adcs	@acc[1],@acc[2],@tmp[1]
	mul	@tmp[1],@a[1],$bi
	 adcs	@acc[2],@acc[3],xzr	//@tmp[2]
	mul	@tmp[2],@a[2],$bi
	 adcs	@acc[3],@acc[4],@tmp[3]
	mul	@tmp[3],@a[3],$bi
	 adc	@acc[4],xzr,xzr

	adds	@acc[0],@acc[0],@tmp[0]
	 umulh	@tmp[0],@a[0],$bi
	adcs	@acc[1],@acc[1],@tmp[1]
	 umulh	@tmp[1],@a[1],$bi
	adcs	@acc[2],@acc[2],@tmp[2]
	mul	$m0,$n0,@acc[0]
	 umulh	@tmp[2],@a[2],$bi
	adcs	@acc[3],@acc[3],@tmp[3]
	 umulh	@tmp[3],@a[3],$bi
	adc	@acc[4],@acc[4],xzr

	 adds	@acc[1],@acc[1],@tmp[0]
	//mul	@tmp[0],@mod[0],$m0
	 adcs	@acc[2],@acc[2],@tmp[1]
	mul	@tmp[1],@mod[1],$m0
	 adcs	@acc[3],@acc[3],@tmp[2]
	//mul	@tmp[2],@mod[2],$m0	//@mod[2]==0
	 adc	@acc[4],@acc[4],@tmp[3]
	lsl	@tmp[3],$m0,#62		//mul	@tmp[3],@mod[3],$m0
___
}
$code.=<<___;
	subs	xzr,@acc[0],#1		//adds	@acc[0],@acc[0],@tmp[0]
	 umulh	@tmp[0],@mod[0],$m0
	adcs	@acc[1],@acc[1],@tmp[1]
	 umulh	@tmp[1],@mod[1],$m0
	adcs	@acc[2],@acc[2],xzr	//@tmp[2]
	//umulh	@tmp[2],@mod[2],$m0	//@mod[2]==0
	adcs	@acc[3],@acc[3],@tmp[3]
	 lsr	@tmp[3],$m0,#2		//umulh	@tmp[3],@mod[3],$m0
	adc	@acc[4],@acc[4],xzr

	 adds	@acc[0],@acc[1],@tmp[0]
	 adcs	@acc[1],@acc[2],@tmp[1]
	 adcs	@acc[2],@acc[3],xzr	//@tmp[2]
	 adcs	@acc[3],@acc[4],@tmp[3]
	 adc	@acc[4],xzr,xzr

	subs	@tmp[0],@acc[0],@mod[0]
	sbcs	@tmp[1],@acc[1],@mod[1]
	sbcs	@tmp[2],@acc[2],xzr	//@mod[2]
	sbcs	@tmp[3],@acc[3],@mod[3]
	sbcs	xzr,    @acc[4],xzr

	csel	@acc[0],@acc[0],@tmp[0],lo
	csel	@acc[1],@acc[1],@tmp[1],lo
	csel	@acc[2],@acc[2],@tmp[2],lo
	csel	@acc[3],@acc[3],@tmp[3],lo

	stp	@acc[0],@acc[1],[$r_ptr]
	stp	@acc[2],@acc[3],[$r_ptr,#16]

	ldp	x19,x20,[x29,#16]
	ldp	x21,x22,[x29,#32]
	ldp	x23,x24,[x29,#48]
	ldr	x29,[sp],#64
	ret
.size	mul_mont_pasta,.-mul_mont_pasta
___
{
my @acc = (@a,@acc[0..3]);
my @a = @mod;

$code.=<<___;
.globl	sqr_mont_pasta
.hidden	sqr_mont_pasta
.type	sqr_mont_pasta,%function
.align	5
sqr_mont_pasta:
	paciasp
	stp	x29,x30,[sp,#-48]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]
	stp	x21,x22,[sp,#32]

	ldp	@a[0],@a[1],[$a_ptr]
	ldp	@a[2],@a[3],[$a_ptr,#16]
	mov	$n0,$n_ptr

	////////////////////////////////////////////////////////////////
	//  |  |  |  |  |  |a1*a0|  |
	//  |  |  |  |  |a2*a0|  |  |
	//  |  |a3*a2|a3*a0|  |  |  |
	//  |  |  |  |a2*a1|  |  |  |
	//  |  |  |a3*a1|  |  |  |  |
	// *|  |  |  |  |  |  |  | 2|
	// +|a3*a3|a2*a2|a1*a1|a0*a0|
	//  |--+--+--+--+--+--+--+--|
	//  |A7|A6|A5|A4|A3|A2|A1|A0|, where Ax is @acc[x]
	//
	//  "can't overflow" below mark carrying into high part of
	//  multiplication result, which can't overflow, because it
	//  can never be all ones.

	mul	@acc[1],@a[1],@a[0]	// a[1]*a[0]
	umulh	@tmp[1],@a[1],@a[0]
	mul	@acc[2],@a[2],@a[0]	// a[2]*a[0]
	umulh	@tmp[2],@a[2],@a[0]
	mul	@acc[3],@a[3],@a[0]	// a[3]*a[0]
	umulh	@acc[4],@a[3],@a[0]

	adds	@acc[2],@acc[2],@tmp[1]	// accumulate high parts of multiplication
	 mul	@tmp[0],@a[2],@a[1]	// a[2]*a[1]
	 umulh	@tmp[1],@a[2],@a[1]
	adcs	@acc[3],@acc[3],@tmp[2]
	 mul	@tmp[2],@a[3],@a[1]	// a[3]*a[1]
	 umulh	@tmp[3],@a[3],@a[1]
	adc	@acc[4],@acc[4],xzr	// can't overflow

	mul	@acc[5],@a[3],@a[2]	// a[3]*a[2]
	umulh	@acc[6],@a[3],@a[2]

	adds	@tmp[1],@tmp[1],@tmp[2]	// accumulate high parts of multiplication
	 mul	@acc[0],@a[0],@a[0]	// a[0]*a[0]
	adc	@tmp[2],@tmp[3],xzr	// can't overflow

	adds	@acc[3],@acc[3],@tmp[0]	// accumulate low parts of multiplication
	 umulh	@a[0],@a[0],@a[0]
	adcs	@acc[4],@acc[4],@tmp[1]
	 mul	@tmp[1],@a[1],@a[1]	// a[1]*a[1]
	adcs	@acc[5],@acc[5],@tmp[2]
	 umulh	@a[1],@a[1],@a[1]
	adc	@acc[6],@acc[6],xzr	// can't overflow

	adds	@acc[1],@acc[1],@acc[1]	// acc[1-6]*=2
	 mul	@tmp[2],@a[2],@a[2]	// a[2]*a[2]
	adcs	@acc[2],@acc[2],@acc[2]
	 umulh	@a[2],@a[2],@a[2]
	adcs	@acc[3],@acc[3],@acc[3]
	 mul	@tmp[3],@a[3],@a[3]	// a[3]*a[3]
	adcs	@acc[4],@acc[4],@acc[4]
	 umulh	@a[3],@a[3],@a[3]
	adcs	@acc[5],@acc[5],@acc[5]
	adcs	@acc[6],@acc[6],@acc[6]
	adc	@acc[7],xzr,xzr

	adds	@acc[1],@acc[1],@a[0]	// +a[i]*a[i]
	adcs	@acc[2],@acc[2],@tmp[1]
	adcs	@acc[3],@acc[3],@a[1]
	adcs	@acc[4],@acc[4],@tmp[2]
	adcs	@acc[5],@acc[5],@a[2]
	adcs	@acc[6],@acc[6],@tmp[3]
	adc	@acc[7],@acc[7],@a[3]

	bl	__mul_by_1_mont_pasta
	ldr	x30,[x29,#8]

	adds	@acc[0],@acc[0],@acc[4]	// accumulate upper half
	adcs	@acc[1],@acc[1],@acc[5]
	adcs	@acc[2],@acc[2],@acc[6]
	adcs	@acc[3],@acc[3],@acc[7]
	adc	@acc[4],xzr,xzr

	subs	@tmp[0],@acc[0],@mod[0]
	sbcs	@tmp[1],@acc[1],@mod[1]
	sbcs	@tmp[2],@acc[2],@mod[2]
	sbcs	@tmp[3],@acc[3],@mod[3]
	sbcs	xzr,    @acc[4],xzr

	csel	@acc[0],@acc[0],@tmp[0],lo
	csel	@acc[1],@acc[1],@tmp[1],lo
	csel	@acc[2],@acc[2],@tmp[2],lo
	csel	@acc[3],@acc[3],@tmp[3],lo

	stp	@acc[0],@acc[1],[$r_ptr]
	stp	@acc[2],@acc[3],[$r_ptr,#16]

	ldp	x19,x20,[x29,#16]
	ldp	x21,x22,[x29,#32]
	ldr	x29,[sp],#48
	autiasp
	ret
.size	sqr_mont_pasta,.-sqr_mont_pasta
___
}
{
my @a = (@a, $bi);

$code.=<<___;
.globl	from_mont_pasta
.hidden	from_mont_pasta
.type	from_mont_pasta,%function
.align	5
from_mont_pasta:
	paciasp
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	mov	$n0,$n_ptr
	ldp	@a[0],@a[1],[$a_ptr]
	ldp	@a[2],@a[3],[$a_ptr,#16]

	bl	__mul_by_1_mont_pasta
	ldr	x30,[x29,#8]

	subs	@tmp[0],@a[0],@mod[0]
	sbcs	@tmp[1],@a[1],@mod[1]
	sbcs	@tmp[2],@a[2],@mod[2]
	sbcs	@tmp[3],@a[3],@mod[3]

	csel	@a[0],@a[0],@tmp[0],lo
	csel	@a[1],@a[1],@tmp[1],lo
	csel	@a[2],@a[2],@tmp[2],lo
	csel	@a[3],@a[3],@tmp[3],lo

	stp	@a[0],@a[1],[$r_ptr]
	stp	@a[2],@a[3],[$r_ptr,#16]

	ldr	x29,[sp],#16
	autiasp
	ret
.size	from_mont_pasta,.-from_mont_pasta

.globl	redc_mont_pasta
.hidden	redc_mont_pasta
.type	redc_mont_pasta,%function
.align	5
redc_mont_pasta:
	paciasp
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	mov	$n0,$n_ptr
	ldp	@a[0],@a[1],[$a_ptr]
	ldp	@a[2],@a[3],[$a_ptr,#16]

	bl	__mul_by_1_mont_pasta
	ldr	x30,[x29,#8]

	ldp	@tmp[0],@tmp[1],[$a_ptr,#32]
	ldp	@tmp[2],@tmp[3],[$a_ptr,#48]

	adds	@a[0],@a[0],@tmp[0]
	adcs	@a[1],@a[1],@tmp[1]
	adcs	@a[2],@a[2],@tmp[2]
	adcs	@a[3],@a[3],@tmp[3]
	adc	@a[4],xzr,xzr

	subs	@tmp[0],@a[0],@mod[0]
	sbcs	@tmp[1],@a[1],@mod[1]
	sbcs	@tmp[2],@a[2],@mod[2]
	sbcs	@tmp[3],@a[3],@mod[3]
	sbcs	xzr,    @a[4],xzr

	csel	@a[0],@a[0],@tmp[0],lo
	csel	@a[1],@a[1],@tmp[1],lo
	csel	@a[2],@a[2],@tmp[2],lo
	csel	@a[3],@a[3],@tmp[3],lo

	stp	@a[0],@a[1],[$r_ptr]
	stp	@a[2],@a[3],[$r_ptr,#16]

	ldr	x29,[sp],#16
	autiasp
	ret
.size	redc_mont_pasta,.-redc_mont_pasta

.type	__mul_by_1_mont_pasta,%function
.align	5
__mul_by_1_mont_pasta:
	mul	$m0,$n0,@a[0]
	ldp	@mod[0],@mod[1],[$b_ptr]
	ldp	@mod[2],@mod[3],[$b_ptr,#16]
___
for ($i=1;$i<4;$i++) {
$code.=<<___;
	//mul	@tmp[0],@mod[0],$m0
	mul	@tmp[1],@mod[1],$m0
	//mul	@tmp[2],@mod[2],$m0	//mod[2]==0
	lsl	@tmp[3],$m0,#62		//mul	@tmp[3],@mod[3],$m0
	subs	xzr,@a[0],#1		//adds	@a[0],@a[0],@tmp[0]
	 umulh	@tmp[0],@mod[0],$m0
	adcs	@a[1],@a[1],@tmp[1]
	 umulh	@tmp[1],@mod[1],$m0
	adcs	@a[2],@a[2],xzr		//@tmp[2]
	//umulh	@tmp[2],@mod[2],$m0	//@mod[2]==0
	adcs	@a[3],@a[3],@tmp[3]
	 lsr	@tmp[3],$m0,#2		//umulh	@tmp[3],@mod[3],$m0
	adc	@a[4],xzr,xzr

	 adds	@a[0],@a[1],@tmp[0]
	 adcs	@a[1],@a[2],@tmp[1]
	 adcs	@a[2],@a[3],xzr		//@tmp[2]
	mul	$m0,$n0,@a[0]
	 adc	@a[3],@a[4],@tmp[3]
___
}
$code.=<<___;
	//mul	@tmp[0],@mod[0],$m0
	mul	@tmp[1],@mod[1],$m0
	//mul	@tmp[2],@mod[2],$m0	//mod[2]==0
	lsl	@tmp[3],$m0,#62		//mul	@tmp[3],@mod[3],$m0
	subs	xzr,@a[0],#1		//adds	@a[0],@a[0],@tmp[0]
	 umulh	@tmp[0],@mod[0],$m0
	adcs	@a[1],@a[1],@tmp[1]
	 umulh	@tmp[1],@mod[1],$m0
	adcs	@a[2],@a[2],xzr		//@tmp[2]
	//umulh	@tmp[2],@mod[2],$m0	//@mod[2]==0
	adcs	@a[3],@a[3],@tmp[3]
	 lsr	@tmp[3],$m0,#2		//umulh	@tmp[3],@mod[3],$m0
	adc	@a[4],xzr,xzr

	 adds	@a[0],@a[1],@tmp[0]
	 adcs	@a[1],@a[2],@tmp[1]
	 adcs	@a[2],@a[3],xzr		//@tmp[2]
	 adc	@a[3],@a[4],@tmp[3]

	ret
.size	__mul_by_1_mont_pasta,.-__mul_by_1_mont_pasta
___
}

if (1) {
my ($r_ptr,$a_ptr,$cnt,$b_ptr,$n_ptr,$n0) = map("x$_", 0..5);
my @a=map("x$_",(6..9));
my @acc=map("x$_",(10..17));
my @tmp=map("x$_",(19..22));
my @mod=map("x$_",(23..26));	# assuming @mod[2]==0 yields ~16%, and
				# @mod[3]==1<<62 - further ~15% on Cortex-A57
my ($bi,$m0) = ($a_ptr,$n_ptr);

$code.=<<___;
.globl	sqr_n_mul_mont_pasta
.hidden	sqr_n_mul_mont_pasta
.type	sqr_n_mul_mont_pasta,%function
.align	5
sqr_n_mul_mont_pasta:
	stp	x29,x30,[sp,#-80]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]
	stp	x21,x22,[sp,#32]
	stp	x23,x24,[sp,#48]
	//stp	x25,x26,[sp,#64]

	ldp	@a[0],@a[1],[$a_ptr]
	ldp	@a[2],@a[3],[$a_ptr,#16]

	ldp	@mod[0],@mod[1],[$n_ptr]
	//ldp	@mod[2],@mod[3],[$n_ptr,#16]

.Loop_sqr_pasta:
	sub	$cnt,$cnt,#1

	////////////////////////////////////////////////////////////////
	//  |  |  |  |  |  |a1*a0|  |
	//  |  |  |  |  |a2*a0|  |  |
	//  |  |a3*a2|a3*a0|  |  |  |
	//  |  |  |  |a2*a1|  |  |  |
	//  |  |  |a3*a1|  |  |  |  |
	// *|  |  |  |  |  |  |  | 2|
	// +|a3*a3|a2*a2|a1*a1|a0*a0|
	//  |--+--+--+--+--+--+--+--|
	//  |A7|A6|A5|A4|A3|A2|A1|A0|, where Ax is @acc[x]
	//
	//  "can't overflow" below mark carrying into high part of
	//  multiplication result, which can't overflow, because it
	//  can never be all ones.

	mul	@acc[1],@a[1],@a[0]	// a[1]*a[0]
	umulh	@tmp[1],@a[1],@a[0]
	mul	@acc[2],@a[2],@a[0]	// a[2]*a[0]
	umulh	@tmp[2],@a[2],@a[0]
	mul	@acc[3],@a[3],@a[0]	// a[3]*a[0]
	umulh	@acc[4],@a[3],@a[0]

	adds	@acc[2],@acc[2],@tmp[1]	// accumulate high parts of multiplication
	 mul	@tmp[0],@a[2],@a[1]	// a[2]*a[1]
	 umulh	@tmp[1],@a[2],@a[1]
	adcs	@acc[3],@acc[3],@tmp[2]
	 mul	@tmp[2],@a[3],@a[1]	// a[3]*a[1]
	 umulh	@tmp[3],@a[3],@a[1]
	adc	@acc[4],@acc[4],xzr	// can't overflow

	mul	@acc[5],@a[3],@a[2]	// a[3]*a[2]
	umulh	@acc[6],@a[3],@a[2]

	adds	@tmp[1],@tmp[1],@tmp[2]	// accumulate high parts of multiplication
	 mul	@acc[0],@a[0],@a[0]	// a[0]*a[0]
	adc	@tmp[2],@tmp[3],xzr	// can't overflow

	adds	@acc[3],@acc[3],@tmp[0]	// accumulate low parts of multiplication
	 umulh	@a[0],@a[0],@a[0]
	adcs	@acc[4],@acc[4],@tmp[1]
	 mul	@tmp[1],@a[1],@a[1]	// a[1]*a[1]
	adcs	@acc[5],@acc[5],@tmp[2]
	 umulh	@a[1],@a[1],@a[1]
	adc	@acc[6],@acc[6],xzr	// can't overflow

	adds	@acc[1],@acc[1],@acc[1]	// acc[1-6]*=2
	 mul	@tmp[2],@a[2],@a[2]	// a[2]*a[2]
	adcs	@acc[2],@acc[2],@acc[2]
	 umulh	@a[2],@a[2],@a[2]
	adcs	@acc[3],@acc[3],@acc[3]
	 mul	@tmp[3],@a[3],@a[3]	// a[3]*a[3]
	adcs	@acc[4],@acc[4],@acc[4]
	 umulh	@a[3],@a[3],@a[3]
	adcs	@acc[5],@acc[5],@acc[5]
	adcs	@acc[6],@acc[6],@acc[6]
	adc	@acc[7],xzr,xzr

	mul	$m0,$n0,@acc[0]

	adds	@acc[1],@acc[1],@a[0]	// +a[i]*a[i]
	adcs	@acc[2],@acc[2],@tmp[1]
	adcs	@acc[3],@acc[3],@a[1]
	adcs	@acc[4],@acc[4],@tmp[2]
	adcs	@acc[5],@acc[5],@a[2]
	adcs	@acc[6],@acc[6],@tmp[3]
	adc	@acc[7],@acc[7],@a[3]
___
for ($i=0;$i<4;$i++) {
$code.=<<___;
	//mul	@tmp[0],@mod[0],$m0
	mul	@tmp[1],@mod[1],$m0
	//mul	@tmp[2],@mod[2],$m0	//@mod[2]==0
	lsl	@tmp[3],$m0,#62		//mul	@tmp[3],@mod[3],$m0
	subs	xzr,@acc[0],#1		//adds	@a[0],@a[0],@tmp[0]
	 umulh	@tmp[0],@mod[0],$m0
	adcs	@acc[1],@acc[1],@tmp[1]
	 umulh	@tmp[1],@mod[1],$m0
	adcs	@acc[2],@acc[2],xzr	//@tmp[2]
	//umulh	@tmp[2],@mod[2],$m0	//@mod[2]==0
	adcs	@acc[3],@acc[3],@tmp[3]
	 lsr	@tmp[3],$m0,#2		//umulh	@tmp[3],@mod[3],$m0
	adc	$bi,xzr,xzr

	 adds	@acc[0],@acc[1],@tmp[0]
	 adcs	@acc[1],@acc[2],@tmp[1]
	 adcs	@acc[2],@acc[3],xzr	//@tmp[2]
___
$code.=<<___	if ($i<3);
	mul	$m0,$n0,@acc[0]
___
$code.=<<___;
	 adc	@acc[3],$bi,@tmp[3]
___
}
$code.=<<___;
	adds	@a[0],@acc[0],@acc[4]	// accumulate upper half
	adcs	@a[1],@acc[1],@acc[5]
	adcs	@a[2],@acc[2],@acc[6]
	adc	@a[3],@acc[3],@acc[7]

	cbnz	$cnt,.Loop_sqr_pasta

	ldr	$bi,[$b_ptr]		// b[0]

	mul	@acc[0],@a[0],$bi
	mul	@acc[1],@a[1],$bi
	mul	@acc[2],@a[2],$bi
	mul	@acc[3],@a[3],$bi

	 umulh	@tmp[0],@a[0],$bi
	 umulh	@tmp[1],@a[1],$bi
	mul	$m0,$n0,@acc[0]
	 umulh	@tmp[2],@a[2],$bi
	 umulh	@tmp[3],@a[3],$bi
	 adds	@acc[1],@acc[1],@tmp[0]
	//mul	@tmp[0],@mod[0],$m0
	 adcs	@acc[2],@acc[2],@tmp[1]
	mul	@tmp[1],@mod[1],$m0
	 adcs	@acc[3],@acc[3],@tmp[2]
	//mul	@tmp[2],@mod[2],$m0	//@mod[2]==0
	 adc	@acc[4],xzr,    @tmp[3]
	lsl	@tmp[3],$m0,#62		//mul	@tmp[3],@mod[3],$m0
___
for ($i=1;$i<4;$i++) {
$code.=<<___;
	ldr	$bi,[$b_ptr,8*$i]	// b[$i]
	subs	xzr,@acc[0],#1		//adds	@acc[0],@acc[0],@tmp[0]
	 umulh	@tmp[0],@mod[0],$m0
	adcs	@acc[1],@acc[1],@tmp[1]
	 umulh	@tmp[1],@mod[1],$m0
	adcs	@acc[2],@acc[2],xzr	//@tmp[2]
	//umulh	@tmp[2],@mod[2],$m0	//@mod[2]==0
	adcs	@acc[3],@acc[3],@tmp[3]
	 lsr	@tmp[3],$m0,#2		//umulh	@tmp[3],@mod[3],$m0
	adc	@acc[4],@acc[4],xzr

	 adds	@acc[0],@acc[1],@tmp[0]
	mul	@tmp[0],@a[0],$bi
	 adcs	@acc[1],@acc[2],@tmp[1]
	mul	@tmp[1],@a[1],$bi
	 adcs	@acc[2],@acc[3],xzr	//@tmp[2]
	mul	@tmp[2],@a[2],$bi
	 adcs	@acc[3],@acc[4],@tmp[3]
	mul	@tmp[3],@a[3],$bi
	 adc	@acc[4],xzr,xzr

	adds	@acc[0],@acc[0],@tmp[0]
	 umulh	@tmp[0],@a[0],$bi
	adcs	@acc[1],@acc[1],@tmp[1]
	 umulh	@tmp[1],@a[1],$bi
	adcs	@acc[2],@acc[2],@tmp[2]
	mul	$m0,$n0,@acc[0]
	 umulh	@tmp[2],@a[2],$bi
	adcs	@acc[3],@acc[3],@tmp[3]
	 umulh	@tmp[3],@a[3],$bi
	adc	@acc[4],@acc[4],xzr

	 adds	@acc[1],@acc[1],@tmp[0]
	//mul	@tmp[0],@mod[0],$m0
	 adcs	@acc[2],@acc[2],@tmp[1]
	mul	@tmp[1],@mod[1],$m0
	 adcs	@acc[3],@acc[3],@tmp[2]
	//mul	@tmp[2],@mod[2],$m0	//@mod[2]==0
	 adc	@acc[4],@acc[4],@tmp[3]
	lsl	@tmp[3],$m0,#62		//mul	@tmp[3],@mod[3],$m0
___
}
$code.=<<___;
	subs	xzr,@acc[0],#1		//adds	@acc[0],@acc[0],@tmp[0]
	 umulh	@tmp[0],@mod[0],$m0
	adcs	@acc[1],@acc[1],@tmp[1]
	 umulh	@tmp[1],@mod[1],$m0
	adcs	@acc[2],@acc[2],xzr	//@tmp[2]
	//umulh	@tmp[2],@mod[2],$m0	//@mod[2]==0
	adcs	@acc[3],@acc[3],@tmp[3]
	 lsr	@tmp[3],$m0,#2		//umulh	@tmp[3],@mod[3],$m0
	adc	@acc[4],@acc[4],xzr

	 adds	@acc[0],@acc[1],@tmp[0]
	 adcs	@acc[1],@acc[2],@tmp[1]
	 adcs	@acc[2],@acc[3],xzr	//@tmp[2]
	 adc	@acc[3],@acc[4],@tmp[3]

	subs	@tmp[0],@acc[0],@mod[0]
	mov	@tmp[3],#1<<62
	sbcs	@tmp[1],@acc[1],@mod[1]
	sbcs	@tmp[2],@acc[2],xzr	//@mod[2]==0
	sbcs	@tmp[3],@acc[3],@tmp[3]

	csel	@acc[0],@acc[0],@tmp[0],lo
	csel	@acc[1],@acc[1],@tmp[1],lo
	csel	@acc[2],@acc[2],@tmp[2],lo
	csel	@acc[3],@acc[3],@tmp[3],lo

	stp	@acc[0],@acc[1],[$r_ptr]
	stp	@acc[2],@acc[3],[$r_ptr,#16]

	ldp	x19,x20,[x29,#16]
	ldp	x21,x22,[x29,#32]
	ldp	x23,x24,[x29,#48]
	//ldp	x25,x26,[x29,#64]
	ldr	x29,[sp],#80
	ret
.size	sqr_n_mul_mont_pasta,.-sqr_n_mul_mont_pasta
___
}

print $code;

close STDOUT;
