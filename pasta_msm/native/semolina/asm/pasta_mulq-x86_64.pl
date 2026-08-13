#!/usr/bin/env perl
#
# Copyright Supranational LLC
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# Modified by Zakura for reproducible vendored assembly generation.

$flavour = shift;
$output  = shift;
if ($flavour =~ /\./) { $output = $flavour; undef $flavour; }

$win64=0; $win64=1 if ($flavour =~ /[nm]asm|mingw64/ || $output =~ /\.asm$/);

$0 =~ m/(.*[\/\\])[^\/\\]+$/; $dir=$1;
( $xlate="${dir}x86_64-xlate.pl" and -f $xlate ) or
( $xlate="${dir}../../perlasm/x86_64-xlate.pl" and -f $xlate) or
die "can't locate x86_64-xlate.pl";

open STDOUT,"| \"$^X\" \"$xlate\" $flavour \"$output\""
    or die "can't call $xlate: $!";

# common argument layout
($r_ptr,$a_ptr,$b_org,$n_ptr,$n0) = ("%rdi","%rsi","%rdx","%rcx","%r8");
$b_ptr = "%rbx";

{ ############################################################## 256 bits
my @acc=map("%r$_",(9..15));

{ ############################################################## mulq
my ($hi, $a0) = ("%rbp", $r_ptr);

$code.=<<___;
.text

.globl	mul_mont_pasta
.hidden	mul_mont_pasta
.type	mul_mont_pasta,\@function,5,"unwind"
.align	32
mul_mont_pasta:
.cfi_startproc
	push	%rbp
.cfi_push	%rbp
	push	%rbx
.cfi_push	%rbx
	push	%r12
.cfi_push	%r12
	push	%r13
.cfi_push	%r13
	push	%r14
.cfi_push	%r14
	push	%r15
.cfi_push	%r15
	push	$r_ptr
.cfi_adjust_cfa_offset	8
.cfi_end_prologue

	mov	8*0($b_org), %rax
	mov	8*0($a_ptr), @acc[4]
	mov	8*1($a_ptr), @acc[5]
	mov	8*2($a_ptr), @acc[3]
	mov	8*3($a_ptr), $hi
	mov	$b_org, $b_ptr		# evacuate from %rdx

	mov	%rax, @acc[6]
	mulq	@acc[4]			# a[0]*b[0]
	mov	%rax, @acc[0]
	mov	@acc[6], %rax
	mov	%rdx, @acc[1]
	call	__mulq_mont_pasta

	mov	8(%rsp),%r15
.cfi_restore	%r15
	mov	16(%rsp),%r14
.cfi_restore	%r14
	mov	24(%rsp),%r13
.cfi_restore	%r13
	mov	32(%rsp),%r12
.cfi_restore	%r12
	mov	40(%rsp),%rbx
.cfi_restore	%rbx
	mov	48(%rsp),%rbp
.cfi_restore	%rbp
	lea	56(%rsp),%rsp
.cfi_adjust_cfa_offset	-56
.cfi_epilogue
	ret
.cfi_endproc
.size	mul_mont_pasta,.-mul_mont_pasta

.globl	sqr_mont_pasta
.hidden	sqr_mont_pasta
.type	sqr_mont_pasta,\@function,4,"unwind"
.align	32
sqr_mont_pasta:
.cfi_startproc
	push	%rbp
.cfi_push	%rbp
	push	%rbx
.cfi_push	%rbx
	push	%r12
.cfi_push	%r12
	push	%r13
.cfi_push	%r13
	push	%r14
.cfi_push	%r14
	push	%r15
.cfi_push	%r15
	push	$r_ptr
.cfi_adjust_cfa_offset	8
.cfi_end_prologue

	mov	8*0($a_ptr), %rax
	mov	$n_ptr, $n0
	mov	8*1($a_ptr), @acc[5]
	mov	$b_org, $n_ptr
	mov	8*2($a_ptr), @acc[3]
	lea	($a_ptr), $b_ptr
	mov	8*3($a_ptr), $hi

	mov	%rax, @acc[6]
	mulq	%rax			# a[0]*a[0]
	mov	%rax, @acc[0]
	mov	@acc[6], %rax
	mov	%rdx, @acc[1]
	call	__mulq_mont_pasta

	mov	8(%rsp),%r15
.cfi_restore	%r15
	mov	16(%rsp),%r14
.cfi_restore	%r14
	mov	24(%rsp),%r13
.cfi_restore	%r13
	mov	32(%rsp),%r12
.cfi_restore	%r12
	mov	40(%rsp),%rbx
.cfi_restore	%rbx
	mov	48(%rsp),%rbp
.cfi_restore	%rbp
	lea	56(%rsp),%rsp
.cfi_adjust_cfa_offset	-56
.cfi_epilogue
	ret
.cfi_endproc
.size	sqr_mont_pasta,.-sqr_mont_pasta
___
{
my @acc=@acc;
$code.=<<___;
.type	__mulq_mont_pasta,\@abi-omnipotent
.align	32
__mulq_mont_pasta:
	mulq	@acc[5]			# a[1]*b[0]
	add	%rax, @acc[1]
	mov	@acc[6], %rax
	adc	\$0, %rdx
	mov	%rdx, @acc[2]

	mulq	@acc[3]			# a[2]*b[0]
	add	%rax, @acc[2]
	mov	@acc[6], %rax
	adc	\$0, %rdx
	mov	%rdx, @acc[3]

	mulq	$hi			# a[3]*b[0]
	add	%rax, @acc[3]
	 mov	8($b_ptr), %rax
	adc	\$0, %rdx
	xor	@acc[5], @acc[5]
	mov	%rdx, @acc[4]

___
for (my $i=1; $i<4; $i++) {
my $b_next = $i<3 ? 8*($i+1)."($b_ptr)" : @acc[1];
$code.=<<___;
	mov	@acc[0], $a0
	imulq	$n0, @acc[0]

	################################# Multiply by b[$i]
	mov	%rax, @acc[6]
	mulq	8*0($a_ptr)
	add	%rax, @acc[1]
	mov	@acc[6], %rax
	adc	\$0, %rdx
	mov	%rdx, $hi

	mulq	8*1($a_ptr)
	add	%rax, @acc[2]
	mov	@acc[6], %rax
	adc	\$0, %rdx
	add	$hi, @acc[2]
	adc	\$0, %rdx
	mov	%rdx, $hi

	mulq	8*2($a_ptr)
	add	%rax, @acc[3]
	mov	@acc[6], %rax
	adc	\$0, %rdx
	add	$hi, @acc[3]
	adc	\$0, %rdx
	mov	%rdx, $hi

	mulq	8*3($a_ptr)
	add	%rax, @acc[4]
	 mov	@acc[0], %rax
	adc	\$0, %rdx
	add	$hi, @acc[4]
	adc	\$0, %rdx		# can't overflow
	mov	%rdx, @acc[5]

	################################# reduction
	mulq	8*0($n_ptr)
	add	%rax, $a0		# guaranteed to be zero
	mov	@acc[0], %rax
	adc	%rdx, $a0

	mulq	8*1($n_ptr)
	add	%rax, @acc[1]
	mov	@acc[0], %rax
	adc	\$0, %rdx

	xor	$hi, $hi
	add	$a0, @acc[1]
	adc	%rdx, @acc[2]
	adc	\$0, $hi

	mulq	8*3($n_ptr)
	add	%rax, @acc[3]
	 mov	$b_next, %rax
	adc	\$0, %rdx
	add	$hi, @acc[3]
	adc	\$0, %rdx
	add	%rdx, @acc[4]
	adc	\$0, @acc[5]
___
    push(@acc,shift(@acc));
}
$code.=<<___;
	imulq	$n0, %rax
	mov	8(%rsp), $a_ptr		# restore $r_ptr
	xor	@acc[5], @acc[5]

	################################# last reduction
	mov	%rax, @acc[6]
	mulq	8*0($n_ptr)
	add	%rax, @acc[0]		# guaranteed to be zero
	mov	@acc[6], %rax
	adc	%rdx, @acc[0]

	mulq	8*1($n_ptr)
	add	%rax, @acc[1]
	mov	@acc[6], %rax
	adc	\$0, %rdx

	xor	$hi, $hi
	add	@acc[0], @acc[1]
	adc	%rdx, @acc[2]
	adc	\$0, $hi

	mulq	8*3($n_ptr)
	 mov	@acc[2], $b_ptr
	add	$hi, @acc[3]
	adc	\$0, %rdx
	add	%rax, @acc[3]
	 mov	@acc[1], %rax
	adc	\$0, %rdx
	add	%rdx, @acc[4]
	adc	\$0, @acc[5]

	#################################
	# Branch-less conditional subtraction of modulus

	 mov	@acc[3], @acc[0]
	sub	8*0($n_ptr), @acc[1]
	sbb	8*1($n_ptr), @acc[2]
	sbb	8*2($n_ptr), @acc[3]
	 mov	@acc[4], $hi
	sbb	8*3($n_ptr), @acc[4]
	sbb	\$0, @acc[5]

	cmovc	%rax, @acc[1]
	cmovc	$b_ptr, @acc[2]
	cmovc	@acc[0], @acc[3]
	mov	@acc[1], 8*0($a_ptr)
	cmovc	$hi, @acc[4]
	mov	@acc[2], 8*1($a_ptr)
	mov	@acc[3], 8*2($a_ptr)
	mov	@acc[4], 8*3($a_ptr)

	ret
.cfi_endproc
.size	__mulq_mont_pasta,.-__mulq_mont_pasta
___
} }
{ my ($n_ptr, $n0)=($b_ptr, $n_ptr);	# arguments are "shifted"

$code.=<<___;
.globl	from_mont_pasta
.hidden	from_mont_pasta
.type	from_mont_pasta,\@function,4,"unwind"
.align	32
from_mont_pasta:
.cfi_startproc
	push	%rbp
.cfi_push	%rbp
	push	%rbx
.cfi_push	%rbx
	push	%r12
.cfi_push	%r12
	push	%r13
.cfi_push	%r13
	push	%r14
.cfi_push	%r14
	push	%r15
.cfi_push	%r15
	sub	\$8, %rsp
.cfi_adjust_cfa_offset	8
.cfi_end_prologue

	mov	$b_org, $n_ptr
	call	__mulq_by_1_mont_pasta

	#################################
	# Branch-less conditional acc[0:3] - modulus

	#mov	@acc[4], %rax		# __mulq_by_1_mont_pasta does it
	mov	@acc[5], @acc[1]
	mov	@acc[6], @acc[2]
	mov	@acc[0], @acc[3]

	sub	8*0($n_ptr), @acc[4]
	sbb	8*1($n_ptr), @acc[5]
	sbb	8*2($n_ptr), @acc[6]
	sbb	8*3($n_ptr), @acc[0]

	cmovnc	@acc[4], %rax
	cmovnc	@acc[5], @acc[1]
	cmovnc	@acc[6], @acc[2]
	mov	%rax,    8*0($r_ptr)
	cmovnc	@acc[0], @acc[3]
	mov	@acc[1], 8*1($r_ptr)
	mov	@acc[2], 8*2($r_ptr)
	mov	@acc[3], 8*3($r_ptr)

	mov	8(%rsp),%r15
.cfi_restore	%r15
	mov	16(%rsp),%r14
.cfi_restore	%r14
	mov	24(%rsp),%r13
.cfi_restore	%r13
	mov	32(%rsp),%r12
.cfi_restore	%r12
	mov	40(%rsp),%rbx
.cfi_restore	%rbx
	mov	48(%rsp),%rbp
.cfi_restore	%rbp
	lea	56(%rsp),%rsp
.cfi_adjust_cfa_offset	-56
.cfi_epilogue
	ret
.cfi_endproc
.size	from_mont_pasta,.-from_mont_pasta

.globl	redc_mont_pasta
.hidden	redc_mont_pasta
.type	redc_mont_pasta,\@function,4,"unwind"
.align	32
redc_mont_pasta:
.cfi_startproc
	push	%rbp
.cfi_push	%rbp
	push	%rbx
.cfi_push	%rbx
	push	%r12
.cfi_push	%r12
	push	%r13
.cfi_push	%r13
	push	%r14
.cfi_push	%r14
	push	%r15
.cfi_push	%r15
	sub	\$8, %rsp
.cfi_adjust_cfa_offset	8
.cfi_end_prologue

	mov	$b_org, $n_ptr
	call	__mulq_by_1_mont_pasta

	add	8*4($a_ptr), @acc[4]	# accumulate upper half
	adc	8*5($a_ptr), @acc[5]
	mov	@acc[4], %rax
	adc	8*6($a_ptr), @acc[6]
	mov	@acc[5], @acc[1]
	adc	8*7($a_ptr), @acc[0]
	sbb	$a_ptr, $a_ptr

	#################################
	# Branch-less conditional acc[0:4] - modulus

	mov	@acc[6], @acc[2]
	sub	8*0($n_ptr), @acc[4]
	sbb	8*1($n_ptr), @acc[5]
	sbb	8*2($n_ptr), @acc[6]
	mov	@acc[0], @acc[3]
	sbb	8*3($n_ptr), @acc[0]
	sbb	\$0, $a_ptr

	cmovnc	@acc[4], %rax
	cmovnc	@acc[5], @acc[1]
	cmovnc	@acc[6], @acc[2]
	mov	%rax,    8*0($r_ptr)
	cmovnc	@acc[0], @acc[3]
	mov	@acc[1], 8*1($r_ptr)
	mov	@acc[2], 8*2($r_ptr)
	mov	@acc[3], 8*3($r_ptr)

	mov	8(%rsp),%r15
.cfi_restore	%r15
	mov	16(%rsp),%r14
.cfi_restore	%r14
	mov	24(%rsp),%r13
.cfi_restore	%r13
	mov	32(%rsp),%r12
.cfi_restore	%r12
	mov	40(%rsp),%rbx
.cfi_restore	%rbx
	mov	48(%rsp),%rbp
.cfi_restore	%rbp
	lea	56(%rsp),%rsp
.cfi_adjust_cfa_offset	-56
.cfi_epilogue
	ret
.cfi_endproc
.size	redc_mont_pasta,.-redc_mont_pasta
___
{
my @acc=@acc;

$code.=<<___;
.type	__mulq_by_1_mont_pasta,\@abi-omnipotent
.align	32
__mulq_by_1_mont_pasta:
	mov	8*0($a_ptr), %rax
	mov	8*1($a_ptr), @acc[1]
	mov	8*2($a_ptr), @acc[2]
	mov	8*3($a_ptr), @acc[3]

	mov	%rax, @acc[4]
	imulq	$n0, %rax
	mov	%rax, @acc[0]
___
for (my $i=0; $i<4; $i++) {
my $hi = "%rbp";
$code.=<<___;
	################################# reduction $i
	mulq	8*0($n_ptr)
	add	%rax, @acc[4]		# guaranteed to be zero
	mov	@acc[0], %rax
	adc	%rdx, @acc[4]

	mulq	8*1($n_ptr)
	add	%rax, @acc[1]
	mov	@acc[0], %rax
	adc	\$0, %rdx

	xor	$hi, $hi
	add	@acc[4], @acc[1]
	adc	%rdx, @acc[2]
	adc	\$0, $hi

___
$code.=<<___	if ($i<3);
	 mov	@acc[1], @acc[5]
	 imulq	$n0, @acc[1]
___
$code.=<<___;

	mulq	8*3($n_ptr)
	add	%rax, @acc[3]
	mov	@acc[1], %rax
	adc	\$0, %rdx
	add	$hi, @acc[3]
	adc	\$0, %rdx
	mov	%rdx, @acc[4]
___
    push(@acc,shift(@acc));
}
$code.=<<___;
	ret
.size	__mulq_by_1_mont_pasta,.-__mulq_by_1_mont_pasta
___
} } }

if (1) {
($r_ptr,$a_ptr,$cnt,$b_ptr,$n_ptr,$n0) = ("%rdi","%rsi","%rdx","%rcx","%r8","%r9");

my $hi = "%rbx";
my @a=("%rcx","%rbp","%rdi","%rsi");
my @acc=map("%r$_",(9..15));

$code.=<<___;
.globl	sqr_n_mul_mont_pasta
.hidden	sqr_n_mul_mont_pasta
.type	sqr_n_mul_mont_pasta,\@function,6,"unwind"
.align	32
sqr_n_mul_mont_pasta:
.cfi_startproc
	push	%rbp
.cfi_push	%rbp
	push	%rbx
.cfi_push	%rbx
	push	%r12
.cfi_push	%r12
	push	%r13
.cfi_push	%r13
	push	%r14
.cfi_push	%r14
	push	%r15
.cfi_push	%r15
	sub	\$40, %rsp
.cfi_adjust_cfa_offset	40
.cfi_end_prologue
	mov	$b_ptr, 16(%rsp)
	mov	$r_ptr, 24(%rsp)

	mov	8*0($a_ptr), %rax
	mov	8*1($a_ptr), @a[1]
	mov	8*2($a_ptr), @a[2]
	mov	8*3($a_ptr), @a[3]
	mov	$cnt, $hi		# evacuate %rdx
	mov	$n0, (%rsp)
	mov	%rax, @a[0]
	jmp	.Loop_sqrq_pasta

.align	32
.Loop_sqrq_pasta:
	mov	$hi, 8(%rsp)		# offload counter value

	mulq	%rax			# a[0]*a[0]
	mov	%rax, @acc[0]
	mov	@a[0], %rax
	mov	%rdx, @acc[1]

	mulq	@a[1]			# a[0]*a[1]
	add	%rax, @acc[1]
	mov	@a[0], %rax
	adc	\$0, %rdx
	mov	%rdx, @acc[2]

	mulq	@a[2]			# a[0]*a[2]
	add	%rax, @acc[2]
	mov	@a[0], %rax
	adc	\$0, %rdx
	mov	%rdx, @acc[3]

	mulq	@a[3]			# a[0]*a[3]
	add	%rax, @acc[3]
	mov	@a[1], %rax
	adc	\$0, %rdx
	mov	%rdx, @acc[4]
___
for (my $i=1; $i<4; $i++) {
my $b_next = $i<3 ? @a[$i+1] : @acc[1];
$code.=<<___;
	mov	@acc[0], @acc[6]
	imulq	(%rsp), @acc[0]

	################################# Multiply by a[$i]
	mulq	@a[0]
	add	%rax, @acc[1]
	mov	@a[$i], %rax
	adc	\$0, %rdx
	mov	%rdx, $hi

	mulq	@a[1]
	add	%rax, @acc[2]
	mov	@a[$i], %rax
	adc	\$0, %rdx
	add	$hi, @acc[2]
	adc	\$0, %rdx
	mov	%rdx, $hi

	mulq	@a[2]
	add	%rax, @acc[3]
	mov	@a[$i], %rax
	adc	\$0, %rdx
	add	$hi, @acc[3]
	adc	\$0, %rdx
	mov	%rdx, $hi

	mulq	@a[3]
	add	%rax, @acc[4]
	 mov	@acc[0], %rax
	adc	\$0, %rdx
	add	$hi, @acc[4]
	adc	\$0, %rdx
	mov	%rdx, @acc[5]

	################################# reduction
	mulq	8*0($n_ptr)
	add	%rax, @acc[6]		# guaranteed to be zero
	mov	@acc[0], %rax
	adc	%rdx, @acc[6]

	mulq	8*1($n_ptr)
	add	%rax, @acc[1]
	mov	@acc[0], %rax
	adc	\$0, %rdx

	xor	$hi, $hi
	add	@acc[6], @acc[1]
	adc	%rdx, @acc[2]
	adc	\$0, $hi

	mulq	8*3($n_ptr)
	add	%rax, @acc[3]
	 mov	$b_next, %rax
	adc	\$0, %rdx
	add	$hi, @acc[3]
	adc	%rdx, @acc[4]
	adc	\$0, @acc[5]
___
    push(@acc,shift(@acc));
}
$code.=<<___;
	imulq	(%rsp), %rax
	mov	@acc[1], @a[0]
	mov	@acc[2], @a[1]
	mov	8(%rsp), $hi		# counter value
	mov	@acc[4], @a[3]
	mov	16(%rsp), @acc[6]	# speculatively load b_ptr

	################################# last reduction
	mov	%rax, @acc[5]
	mulq	8*0($n_ptr)
	add	%rax, @acc[0]		# guaranteed to be zero
	mov	@acc[5], %rax
	adc	%rdx, @acc[0]

	mulq	8*1($n_ptr)
	add	%rax, @a[0]
	mov	@acc[5], %rax
	adc	\$0, %rdx

	xor	@a[2], @a[2]
	add	@acc[0], @a[0]
	adc	%rdx, @a[1]
	adc	\$0, @a[2]

	mulq	8*3($n_ptr)
	add	%rax, @a[2]
	mov	@a[0], %rax
	adc	\$0, %rdx
	add	@acc[3], @a[2]
	adc	%rdx, @a[3]

	sub	\$1, $hi
	jnz	.Loop_sqrq_pasta
___
$b_ptr = @acc[6];
@acc[6] = @a[0];
$code.=<<___;
	mulq	8*0($b_ptr)
	mov	%rax, @acc[0]
	mov	@a[0], %rax
	mov	%rdx, @acc[1]

	mulq	8*1($b_ptr)
	add	%rax, @acc[1]
	mov	@a[0], %rax
	adc	\$0, %rdx
	mov	%rdx, @acc[2]

	mulq	8*2($b_ptr)
	add	%rax, @acc[2]
	mov	@a[0], %rax
	adc	\$0, %rdx
	mov	%rdx, @acc[3]

	mulq	8*3($b_ptr)
	add	%rax, @acc[3]
	mov	@a[1], %rax
	adc	\$0, %rdx
	mov	%rdx, @acc[4]
___
for (my $i=1; $i<4; $i++) {
my $b_next = $i<3 ? @a[$i+1] : @acc[1];
$code.=<<___;
	mov	@acc[0], @acc[6]
	imulq	(%rsp), @acc[0]

	################################# Multiply by a[$i]
	mulq	8*0($b_ptr)
	add	%rax, @acc[1]
	mov	@a[$i], %rax
	adc	\$0, %rdx
	mov	%rdx, $hi

	mulq	8*1($b_ptr)
	add	%rax, @acc[2]
	mov	@a[$i], %rax
	adc	\$0, %rdx
	add	$hi, @acc[2]
	adc	\$0, %rdx
	mov	%rdx, $hi

	mulq	8*2($b_ptr)
	add	%rax, @acc[3]
	mov	@a[$i], %rax
	adc	\$0, %rdx
	add	$hi, @acc[3]
	adc	\$0, %rdx
	mov	%rdx, $hi

	mulq	8*3($b_ptr)
	add	%rax, @acc[4]
	 mov	@acc[0], %rax
	adc	\$0, %rdx
	add	$hi, @acc[4]
	adc	\$0, %rdx
	mov	%rdx, @acc[5]

	################################# reduction
	mulq	8*0($n_ptr)
	add	%rax, @acc[6]		# guaranteed to be zero
	mov	@acc[0], %rax
	adc	%rdx, @acc[6]

	mulq	8*1($n_ptr)
	add	%rax, @acc[1]
	mov	@acc[0], %rax
	adc	\$0, %rdx

	xor	$hi, $hi
	add	@acc[6], @acc[1]
	adc	%rdx, @acc[2]
	adc	\$0, $hi

	mulq	8*3($n_ptr)
	add	%rax, @acc[3]
	 mov	$b_next, %rax
	adc	\$0, %rdx
	add	$hi, @acc[3]
	adc	%rdx, @acc[4]
	adc	\$0, @acc[5]
___
    push(@acc,shift(@acc));
}
$code.=<<___;
	imulq	(%rsp), %rax
	mov	24(%rsp), $r_ptr

	################################# last reduction
	mov	%rax, @acc[6]
	mulq	8*0($n_ptr)
	add	%rax, @acc[0]		# guaranteed to be zero
	mov	@acc[6], %rax
	adc	%rdx, @acc[0]

	mulq	8*1($n_ptr)
	add	%rax, @acc[1]
	mov	@acc[6], %rax
	adc	\$0, %rdx

	xor	$hi, $hi
	add	@acc[0], @acc[1]
	adc	%rdx, @acc[2]
	adc	\$0, $hi

	mulq	8*3($n_ptr)
	 mov	@acc[1], @acc[5]
	add	$hi, @acc[3]
	adc	\$0, %rdx
	 mov	@acc[2], @acc[6]
	add	%rax, @acc[3]
	adc	%rdx, @acc[4]

	#################################
	# Branch-less conditional subtraction of modulus

	 mov	@acc[3], @acc[0]
	sub	8*0($n_ptr), @acc[1]
	sbb	8*1($n_ptr), @acc[2]
	sbb	8*2($n_ptr), @acc[3]
	 mov	@acc[4], $hi
	sbb	8*3($n_ptr), @acc[4]

	cmovc	@acc[5], @acc[1]
	cmovc	@acc[6], @acc[2]
	cmovc	@acc[0], @acc[3]
	mov	@acc[1], 8*0($r_ptr)
	cmovc	$hi, @acc[4]
	mov	@acc[2], 8*1($r_ptr)
	mov	@acc[3], 8*2($r_ptr)
	mov	@acc[4], 8*3($r_ptr)

	mov	40(%rsp),%r15
.cfi_restore	%r15
	mov	48(%rsp),%r14
.cfi_restore	%r14
	mov	56(%rsp),%r13
.cfi_restore	%r13
	mov	64(%rsp),%r12
.cfi_restore	%r12
	mov	72(%rsp),%rbx
.cfi_restore	%rbx
	mov	80(%rsp),%rbp
.cfi_restore	%rbp
	lea	88(%rsp),%rsp
.cfi_adjust_cfa_offset	-88
.cfi_epilogue
	ret
.cfi_endproc
.size	sqr_n_mul_mont_pasta,.-sqr_n_mul_mont_pasta
___
}

print $code;
close STDOUT;
