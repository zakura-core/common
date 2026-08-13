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

{ ############################################################## 255 bits
my @acc=map("%r$_",(10..15));

{ ############################################################## mulq
my ($lo,$hi)=("%rbp","%r9");

$code.=<<___;
.text

.globl	mulx_mont_pasta
.hidden	mulx_mont_pasta
.type	mulx_mont_pasta,\@function,5,"unwind"
.align	32
mulx_mont_pasta:
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
	sub	\$8,%rsp
.cfi_adjust_cfa_offset	8
.cfi_end_prologue

	mov	$b_org, $b_ptr		# evacuate from %rdx
	mov	8*0($b_org), %rdx
	mov	8*0($a_ptr), @acc[4]
	mov	8*1($a_ptr), @acc[5]
	mov	8*2($a_ptr), $lo
	mov	8*3($a_ptr), $hi
	lea	-128($a_ptr), $a_ptr	# control u-op density
	lea	-128($n_ptr), $n_ptr	# control u-op density

	mulx	@acc[4], %rax, @acc[1]	# a[0]*b[0]
	call	__mulx_mont_pasta

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
.size	mulx_mont_pasta,.-mulx_mont_pasta

.globl	sqrx_mont_pasta
.hidden	sqrx_mont_pasta
.type	sqrx_mont_pasta,\@function,4,"unwind"
.align	32
sqrx_mont_pasta:
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
	sub	\$8,%rsp
.cfi_adjust_cfa_offset	8
.cfi_end_prologue

	mov	$a_ptr, $b_ptr
	mov	$n_ptr, $n0
	mov	$b_org, $n_ptr
	mov	8*0($a_ptr), %rdx
	mov	8*1($a_ptr), @acc[5]
	mov	8*2($a_ptr), $lo
	mov	8*3($a_ptr), $hi
	lea	-128($b_ptr), $a_ptr	# control u-op density
	lea	-128($n_ptr), $n_ptr	# control u-op density

	mulx	%rdx, %rax, @acc[1]	# a[0]*a[0]
	call	__mulx_mont_pasta

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
.size	sqrx_mont_pasta,.-sqrx_mont_pasta
___
{
my @acc=@acc;
$code.=<<___;
.type	__mulx_mont_pasta,\@abi-omnipotent
.align	32
__mulx_mont_pasta:
	mulx	@acc[5], @acc[5], @acc[2]
	mulx	$lo, $lo, @acc[3]
	add	@acc[5], @acc[1]
	mulx	$hi, $hi, @acc[4]
	 mov	8($b_ptr), %rdx
	adc	$lo, @acc[2]
	adc	$hi, @acc[3]
	adc	\$0, @acc[4]

___
for (my $i=1; $i<4; $i++) {
my $b_next = $i<3 ? 8*($i+1)."($b_ptr)" : "%rax";
$code.=<<___;
	 mov	%rax, @acc[0]
	 imulq	$n0, %rax

	################################# Multiply by b[$i]
	xor	@acc[5], @acc[5]	# @acc[5]=0, cf=0, of=0
	mulx	8*0+128($a_ptr), $lo, $hi
	adox	$lo, @acc[1]
	adcx	$hi, @acc[2]

	mulx	8*1+128($a_ptr), $lo, $hi
	adox	$lo, @acc[2]
	adcx	$hi, @acc[3]

	mulx	8*2+128($a_ptr), $lo, $hi
	adox	$lo, @acc[3]
	adcx	$hi, @acc[4]

	mulx	8*3+128($a_ptr), $lo, $hi
	 mov	%rax, %rdx
	adox	$lo, @acc[4]
	adcx	@acc[5], $hi 		# cf=0
	adox	$hi, @acc[5]		# of=0

	################################# reduction
	mulx	8*0+128($n_ptr), $lo, %rax
	adcx	$lo, @acc[0]		# guaranteed to be zero
	adox	@acc[1], %rax

	mulx	8*1+128($n_ptr), $lo, $hi
	adcx	$lo, %rax		# @acc[1]
	adox	$hi, @acc[2]

	adcx	@acc[0], @acc[2]
	adox	@acc[0], @acc[3]

	mulx	8*3+128($n_ptr), $lo, $hi
	 mov	$b_next, %rdx
	adcx	$lo, @acc[3]
	adox	$hi, @acc[4]
	adcx	@acc[0], @acc[4]
	adox	@acc[0], @acc[5]	# of=0
	adcx	@acc[0], @acc[5]	# cf=0
___
    push(@acc,shift(@acc));
}
$code.=<<___;
	imulq	$n0, %rdx

	################################# last reduction
	xor	@acc[5], @acc[5]	# @acc[5]=0, cf=0, of=0
	mulx	8*0+128($n_ptr), @acc[0], $hi
	adcx	%rax, @acc[0]		# guaranteed to be zero
	adox	$hi, @acc[1]

	mulx	8*1+128($n_ptr), $lo, $hi
	adcx	$lo, @acc[1]
	adox	$hi, @acc[2]

	adcx	@acc[0], @acc[2]
	adox	@acc[0], @acc[3]

	mulx	8*3+128($n_ptr), $lo, $hi
	 mov	@acc[1], %rdx
	 lea	128($n_ptr), $n_ptr
	adcx	$lo, @acc[3]
	adox	$hi, @acc[4]
	 mov	@acc[2], %rax
	adcx	@acc[0], @acc[4]
	adox	@acc[0], @acc[5]
	adc	\$0, @acc[5]

	#################################
	# Branch-less conditional acc[1:5] - modulus

	 mov	@acc[3], $lo
	sub	8*0($n_ptr), @acc[1]
	sbb	8*1($n_ptr), @acc[2]
	sbb	8*2($n_ptr), @acc[3]
	 mov	@acc[4], $hi
	sbb	8*3($n_ptr), @acc[4]
	sbb	\$0, @acc[5]

	cmovc	%rdx, @acc[1]
	cmovc	%rax, @acc[2]
	cmovc	$lo,  @acc[3]
	mov	@acc[1], 8*0($r_ptr)
	cmovc	$hi,  @acc[4]
	mov	@acc[2], 8*1($r_ptr)
	mov	@acc[3], 8*2($r_ptr)
	mov	@acc[4], 8*3($r_ptr)

	ret
.size	__mulx_mont_pasta,.-__mulx_mont_pasta
___
} }
{ my ($n_ptr, $n0)=($b_ptr, $n_ptr);	# arguments are "shifted"

$code.=<<___;
.globl	fromx_mont_pasta
.hidden	fromx_mont_pasta
.type	fromx_mont_pasta,\@function,4,"unwind"
.align	32
fromx_mont_pasta:
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
	call	__mulx_by_1_mont_pasta

	#################################
	# Branch-less conditional acc[0:3] - modulus

	#mov	@acc[4], %rax		# __mulq_by_1_mont_pasta does it
	mov	@acc[5], %rdx
	mov	@acc[0], @acc[2]
	mov	@acc[1], @acc[3]

	sub	8*0($n_ptr), @acc[4]
	sbb	8*1($n_ptr), @acc[5]
	sbb	8*2($n_ptr), @acc[0]
	sbb	8*3($n_ptr), @acc[1]

	cmovnc	@acc[4], %rax
	cmovnc	@acc[5], %rdx
	cmovnc	@acc[0], @acc[2]
	mov	%rax,    8*0($r_ptr)
	cmovnc	@acc[1], @acc[3]
	mov	%rdx,    8*1($r_ptr)
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
.size	fromx_mont_pasta,.-fromx_mont_pasta

.globl	redcx_mont_pasta
.hidden	redcx_mont_pasta
.type	redcx_mont_pasta,\@function,4,"unwind"
.align	32
redcx_mont_pasta:
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
	call	__mulx_by_1_mont_pasta

	add	8*4($a_ptr), @acc[4]	# accumulate upper half
	adc	8*5($a_ptr), @acc[5]
	mov	@acc[4], %rax
	adc	8*6($a_ptr), @acc[0]
	mov	@acc[5], %rdx
	adc	8*7($a_ptr), @acc[1]
	sbb	$a_ptr, $a_ptr

	#################################
	# Branch-less conditional acc[0:4] - modulus

	mov	@acc[0], @acc[2]
	sub	8*0($n_ptr), @acc[4]
	sbb	8*1($n_ptr), @acc[5]
	sbb	8*2($n_ptr), @acc[0]
	mov	@acc[1], @acc[3]
	sbb	8*3($n_ptr), @acc[1]
	sbb	\$0, $a_ptr

	cmovnc	@acc[4], %rax
	cmovnc	@acc[5], %rdx
	cmovnc	@acc[0], @acc[2]
	mov	%rax,    8*0($r_ptr)
	cmovnc	@acc[1], @acc[3]
	mov	%rdx,    8*1($r_ptr)
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
.size	redcx_mont_pasta,.-redcx_mont_pasta
___
{
my @acc=@acc;

$code.=<<___;
.type	__mulx_by_1_mont_pasta,\@abi-omnipotent
.align	32
__mulx_by_1_mont_pasta:
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
.size	__mulx_by_1_mont_pasta,.-__mulx_by_1_mont_pasta
___
} } }

if (1) {
($r_ptr,$a_ptr,$cnt,$b_ptr,$n_ptr,$n0) = ("%rdi","%rsi","%rdx","%rcx","%r8","%r9");

my ($lo, $hi) = ("%r9", "%rbx");
my @a=("%rcx","%rbp","%rdi","%rsi");
my @acc=map("%r$_",(10..15));

$code.=<<___;
.globl	sqrx_n_mul_mont_pasta
.hidden	sqrx_n_mul_mont_pasta
.type	sqrx_n_mul_mont_pasta,\@function,6,"unwind"
.align	32
sqrx_n_mul_mont_pasta:
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
	lea	-128($b_ptr), $b_ptr
	lea	-128($n_ptr), $n_ptr
	mov	$b_ptr, 16(%rsp)
	mov	$r_ptr, 24(%rsp)
	mov	$cnt, $hi		# evacuate %rdx

	mov	8*0($a_ptr), %rdx
	mov	8*1($a_ptr), @a[1]
	mov	8*2($a_ptr), @a[2]
	mov	8*3($a_ptr), @a[3]
	mov	$n0, (%rsp)
	mov	%rdx, @a[0]
	jmp	.Loop_sqrx_pasta

.align	32
.Loop_sqrx_pasta:
	mov	$hi, 8(%rsp)		# counter value

	mulx	%rdx, %rax, @acc[0]	# a[0]*a[0]
	xor	@acc[5], @acc[5]
	mulx	@a[1], @acc[1], $lo	# a[0]*a[1]
	adcx	@acc[0], @acc[1]
	mulx	@a[2], @acc[2], $hi	# a[0]*a[2]
	adcx	$lo, @acc[2]
	mulx	@a[3], @acc[3], @acc[4]	# a[0]*a[3]
	mov	@a[1], %rdx
	adcx	$hi, @acc[3]
	adcx	@acc[5], @acc[4]
___
for (my $i=1; $i<4; $i++) {
my $b_next = $i<3 ? @a[$i+1] : "%rax";
$code.=<<___;
	mov	%rax, @acc[0]
	imulq	(%rsp), %rax

	################################# Multiply by a[$i]
	xor	@acc[5], @acc[5]	# @acc[5]=0, cf=0, of=0
	mulx	@a[0], $lo, $hi
	adox	$lo, @acc[1]
	adcx	$hi, @acc[2]

	mulx	@a[1], $lo, $hi
	adox	$lo, @acc[2]
	adcx	$hi, @acc[3]

	mulx	@a[2], $lo, $hi
	adox	$lo, @acc[3]
	adcx	$hi, @acc[4]

	mulx	@a[3], $lo, $hi
	 mov	%rax, %rdx
	adox	$lo, @acc[4]
	adcx	@acc[5], $hi 		# cf=0
	adox	$hi, @acc[5]		# of=0

	################################# reduction
	mulx	8*0+128($n_ptr), $lo, %rax
	xor	$hi, $hi
	adcx	$lo, @acc[0]		# guaranteed to be zero
	adox	@acc[1], %rax

	mulx	8*1+128($n_ptr), $lo, $hi
	adcx	$lo, %rax		# @acc[1]
	adox	$hi, @acc[2]

	adcx	@acc[0], @acc[2]
	adox	@acc[0], @acc[3]

	mulx	8*3+128($n_ptr), $lo, $hi
	 mov	$b_next, %rdx
	adcx	$lo, @acc[3]
	adox	$hi, @acc[4]
	adcx	@acc[0], @acc[4]
	adox	@acc[0], @acc[5]	# of=0
	adcx	@acc[0], @acc[5]	# cf=0
___
    push(@acc,shift(@acc));
}
$code.=<<___;
	imulq	(%rsp), %rdx
	mov	8(%rsp), $hi		# counter value
	mov	16(%rsp), @acc[5]	# speculatively load b_ptr

	################################# last reduction
	xor	@a[2], @a[2]		# @a[2]=0, cf=0, of=0
	mulx	8*0+128($n_ptr), $lo, @a[0]
	adcx	$lo, %rax		# guaranteed to be zero
	adox	@acc[1], @a[0]

	mulx	8*1+128($n_ptr), $lo, @a[1]
	adcx	$lo, @a[0]
	adox	@acc[2], @a[1]

	adcx	%rax, @a[1]
	adox	@acc[3], @a[2]

	mulx	8*3+128($n_ptr), $lo, @a[3]
	 mov	@a[0], %rdx
	adcx	$lo, @a[2]
	adox	@acc[4], @a[3]
	adcx	%rax, @a[3]

	sub	\$1, $hi
	jnz	.Loop_sqrx_pasta
___
$b_ptr = @acc[5];
@acc[5] = @a[0];
$code.=<<___;
	mulx	8*0+128($b_ptr), %rax, @acc[0]		# a[0]*b[0]
	xor	@acc[5], @acc[5]
	mulx	8*1+128($b_ptr), @acc[1], $lo		# a[0]*b[1]
	adcx	@acc[0], @acc[1]
	mulx	8*2+128($b_ptr), @acc[2], $hi		# a[0]*b[2]
	adcx	$lo, @acc[2]
	mulx	8*3+128($b_ptr), @acc[3], @acc[4]	# a[0]*b[3]
	mov	@a[1], %rdx
	adcx	$hi, @acc[3]
	adcx	@acc[5], @acc[4]
___
for (my $i=1; $i<4; $i++) {
my $b_next = $i<3 ? @a[$i+1] : "%rax";
$code.=<<___;
	mov	%rax, @acc[0]
	imulq	(%rsp), %rax

	################################# Multiply by b[$i]
	xor	@acc[5], @acc[5]	# @acc[5]=0, cf=0, of=0
	mulx	8*0+128($b_ptr), $lo, $hi
	adox	$lo, @acc[1]
	adcx	$hi, @acc[2]

	mulx	8*1+128($b_ptr), $lo, $hi
	adox	$lo, @acc[2]
	adcx	$hi, @acc[3]

	mulx	8*2+128($b_ptr), $lo, $hi
	adox	$lo, @acc[3]
	adcx	$hi, @acc[4]

	mulx	8*3+128($b_ptr), $lo, $hi
	 mov	%rax, %rdx
	adox	$lo, @acc[4]
	adcx	@acc[5], $hi 		# cf=0
	adox	$hi, @acc[5]		# of=0

	################################# reduction
	mulx	8*0+128($n_ptr), $lo, %rax
	adcx	$lo, @acc[0]		# guaranteed to be zero
	adox	@acc[1], %rax

	mulx	8*1+128($n_ptr), $lo, $hi
	adcx	$lo, %rax		# @acc[1]
	adox	$hi, @acc[2]

	adcx	@acc[0], @acc[2]
	adox	@acc[0], @acc[3]

	mulx	8*3+128($n_ptr), $lo, $hi
	 mov	$b_next, %rdx
	adcx	$lo, @acc[3]
	adox	$hi, @acc[4]
	adcx	@acc[0], @acc[4]
	adox	@acc[0], @acc[5]	# of=0
	adcx	@acc[0], @acc[5]	# cf=0
___
    push(@acc,shift(@acc));
}
$code.=<<___;
	imulq	(%rsp), %rdx
	mov	24(%rsp), $r_ptr

	################################# last reduction
	xor	@acc[5], @acc[5]	# @acc[5]=0, cf=0, of=0
	mulx	8*0+128($n_ptr), $lo, $hi
	adcx	$lo, %rax		# guaranteed to be zero
	adox	$hi, @acc[1]

	mulx	8*1+128($n_ptr), $lo, $hi
	adcx	$lo, @acc[1]
	adox	$hi, @acc[2]

	 #mov	@acc[1], %rax
	adcx	@acc[5], @acc[2]
	adox	@acc[5], @acc[3]

	mulx	8*3+128($n_ptr), $lo, $hi
	 #lea	128($n_ptr), $n_ptr
	 #mov	@acc[2], %rdx
	adcx	$lo, @acc[3]
	adox	$hi, @acc[4]
	adcx	@acc[5], @acc[4]

	#################################
	# Branch-less conditional subtraction of modulus

	 #mov	@acc[3], $lo
	#sub	8*0($n_ptr), @acc[1]
	#sbb	8*1($n_ptr), @acc[2]
	#sbb	8*2($n_ptr), @acc[3]
	 #mov	@acc[4], $hi
	#sbb	8*3($n_ptr), @acc[4]

	#cmovc	%rax, @acc[1]
	#cmovc	%rdx, @acc[2]
	#cmovc	$lo, @acc[3]
	mov	@acc[1], 8*0($r_ptr)
	#cmovc	$hi, @acc[4]
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
.size	sqrx_n_mul_mont_pasta,.-sqrx_n_mul_mont_pasta
___
}

print $code;
close STDOUT;
