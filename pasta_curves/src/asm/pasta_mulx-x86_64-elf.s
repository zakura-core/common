# Copyright Supranational LLC
# Licensed under the Apache License, Version 2.0; see LICENSE-APACHE.
# SPDX-License-Identifier: Apache-2.0
#
# Adapted from Semolina v0.1.4, commit
# 13ffc78074a6fbec44a4fd12b7f585a0bc1dc154:
# https://github.com/supranational/semolina
#
# Montgomery multiplication and its helper are generated from
# pasta_mulx-x86_64.pl. The specialized square is a direct x86-64 translation
# of pasta_mul-armv8.S. Symbols are crate-prefixed.
# The routines have no secret-dependent branches or memory accesses. Their
# reduction specializes the shared high limbs of the two Pasta moduli.

.text

.globl	pasta_curves_mulx_mont
.hidden	pasta_curves_mulx_mont
.type	pasta_curves_mulx_mont,@function
.align	32
pasta_curves_mulx_mont:
.cfi_startproc
	.byte	0xf3,0x0f,0x1e,0xfa


	pushq	%rbp
.cfi_adjust_cfa_offset	8
.cfi_offset	%rbp,-16
	pushq	%rbx
.cfi_adjust_cfa_offset	8
.cfi_offset	%rbx,-24
	pushq	%r12
.cfi_adjust_cfa_offset	8
.cfi_offset	%r12,-32
	pushq	%r13
.cfi_adjust_cfa_offset	8
.cfi_offset	%r13,-40
	pushq	%r14
.cfi_adjust_cfa_offset	8
.cfi_offset	%r14,-48
	pushq	%r15
.cfi_adjust_cfa_offset	8
.cfi_offset	%r15,-56
	subq	$8,%rsp
.cfi_adjust_cfa_offset	8


	movq	%rdx,%rbx
	movq	0(%rdx),%rdx
	movq	0(%rsi),%r14
	movq	8(%rsi),%r15
	movq	16(%rsi),%rbp
	movq	24(%rsi),%r9
	leaq	-128(%rsi),%rsi
	leaq	-128(%rcx),%rcx

	mulxq	%r14,%rax,%r11
	call	__pasta_curves_mulx_mont

	movq	8(%rsp),%r15
.cfi_restore	%r15
	movq	16(%rsp),%r14
.cfi_restore	%r14
	movq	24(%rsp),%r13
.cfi_restore	%r13
	movq	32(%rsp),%r12
.cfi_restore	%r12
	movq	40(%rsp),%rbx
.cfi_restore	%rbx
	movq	48(%rsp),%rbp
.cfi_restore	%rbp
	leaq	56(%rsp),%rsp
.cfi_adjust_cfa_offset	-56

	.byte	0xf3,0xc3
.cfi_endproc
.size	pasta_curves_mulx_mont,.-pasta_curves_mulx_mont

.globl	pasta_curves_sqrx_mont
.hidden	pasta_curves_sqrx_mont
.type	pasta_curves_sqrx_mont,@function
.align	32
pasta_curves_sqrx_mont:
.cfi_startproc
	.byte	0xf3,0x0f,0x1e,0xfa

	pushq	%rbp
.cfi_adjust_cfa_offset	8
.cfi_offset	%rbp,-16
	pushq	%rbx
.cfi_adjust_cfa_offset	8
.cfi_offset	%rbx,-24
	pushq	%r12
.cfi_adjust_cfa_offset	8
.cfi_offset	%r12,-32
	pushq	%r13
.cfi_adjust_cfa_offset	8
.cfi_offset	%r13,-40
	pushq	%r14
.cfi_adjust_cfa_offset	8
.cfi_offset	%r14,-48
	pushq	%r15
.cfi_adjust_cfa_offset	8
.cfi_offset	%r15,-56
	subq	$40,%rsp
.cfi_adjust_cfa_offset	40

	movq	%rdi,%rbx
	movq	%rdx,%rbp

	# Form the six off-diagonal products once.
	movq	0(%rsi),%rdx
	mulxq	8(%rsi),%r9,%rax
	mulxq	16(%rsi),%r10,%rdi
	addq	%rax,%r10
	adcq	$0,%rdi
	mulxq	24(%rsi),%r11,%r12
	addq	%rdi,%r11
	adcq	$0,%r12

	movq	8(%rsi),%rdx
	mulxq	16(%rsi),%rax,%rdi
	addq	%rax,%r11
	adcq	$0,%rdi
	mulxq	24(%rsi),%rax,%r13
	addq	%r12,%rax
	adcq	$0,%r13
	addq	%rdi,%rax
	adcq	$0,%r13
	movq	%rax,%r12

	movq	16(%rsi),%rdx
	mulxq	24(%rsi),%rax,%r14
	addq	%r13,%rax
	adcq	$0,%r14
	movq	%rax,%r13

	# Double the off-diagonal half of the square.
	xorq	%r15,%r15
	addq	%r9,%r9
	adcq	%r10,%r10
	adcq	%r11,%r11
	adcq	%r12,%r12
	adcq	%r13,%r13
	adcq	%r14,%r14
	adcq	%r15,%r15

	# Add the four diagonal products.
	movq	0(%rsi),%rdx
	mulxq	%rdx,%r8,%rax
	addq	%rax,%r9
	movq	8(%rsi),%rdx
	mulxq	%rdx,%rax,%rdi
	adcq	%r10,%rax
	adcq	$0,%rdi
	movq	%rax,%r10
	addq	%rdi,%r11
	movq	16(%rsi),%rdx
	mulxq	%rdx,%rax,%rdi
	adcq	%r12,%rax
	adcq	$0,%rdi
	movq	%rax,%r12
	addq	%rdi,%r13
	movq	24(%rsi),%rdx
	mulxq	%rdx,%rax,%rdi
	adcq	%r14,%rax
	adcq	$0,%rdi
	movq	%rax,%r14
	addq	%rdi,%r15

	# Preserve the upper half while reducing the lower half by R.
	movq	%r12,0(%rsp)
	movq	%r13,8(%rsp)
	movq	%r14,16(%rsp)
	movq	%r15,24(%rsp)
	movq	0(%rbp),%r12
	movq	8(%rbp),%r13

	# Montgomery cancellation 0. The p[2] product is zero and the
	# p[3] = 2^62 product is formed with shifts.
	movq	%r8,%rdx
	imulq	%rcx,%rdx
	mulxq	%r13,%r15,%rdi
	mulxq	%r12,%rax,%r14
	movq	%rdx,%rax
	shlq	$62,%rax
	shrq	$2,%rdx
	negq	%r8
	adcq	%r15,%r9
	adcq	$0,%r10
	adcq	%rax,%r11
	movq	$0,%r8
	adcq	$0,%r8
	addq	%r14,%r9
	adcq	%rdi,%r10
	adcq	$0,%r11
	adcq	%rdx,%r8

	# Montgomery cancellation 1.
	movq	%r9,%rdx
	imulq	%rcx,%rdx
	mulxq	%r13,%r15,%rdi
	mulxq	%r12,%rax,%r14
	movq	%rdx,%rax
	shlq	$62,%rax
	shrq	$2,%rdx
	negq	%r9
	adcq	%r15,%r10
	adcq	$0,%r11
	adcq	%rax,%r8
	movq	$0,%r9
	adcq	$0,%r9
	addq	%r14,%r10
	adcq	%rdi,%r11
	adcq	$0,%r8
	adcq	%rdx,%r9

	# Montgomery cancellation 2.
	movq	%r10,%rdx
	imulq	%rcx,%rdx
	mulxq	%r13,%r15,%rdi
	mulxq	%r12,%rax,%r14
	movq	%rdx,%rax
	shlq	$62,%rax
	shrq	$2,%rdx
	negq	%r10
	adcq	%r15,%r11
	adcq	$0,%r8
	adcq	%rax,%r9
	movq	$0,%r10
	adcq	$0,%r10
	addq	%r14,%r11
	adcq	%rdi,%r8
	adcq	$0,%r9
	adcq	%rdx,%r10

	# Montgomery cancellation 3.
	movq	%r11,%rdx
	imulq	%rcx,%rdx
	mulxq	%r13,%r15,%rdi
	mulxq	%r12,%rax,%r14
	movq	%rdx,%rax
	shlq	$62,%rax
	shrq	$2,%rdx
	negq	%r11
	adcq	%r15,%r8
	adcq	$0,%r9
	adcq	%rax,%r10
	movq	$0,%r11
	adcq	$0,%r11
	addq	%r14,%r8
	adcq	%rdi,%r9
	adcq	$0,%r10
	adcq	%rdx,%r11

	# Add the untouched upper half and capture a possible 257th bit.
	addq	0(%rsp),%r8
	adcq	8(%rsp),%r9
	adcq	16(%rsp),%r10
	adcq	24(%rsp),%r11
	movq	$0,%rsi
	adcq	$0,%rsi

	# Canonicalize with one constant-time conditional subtraction.
	movq	%r8,%r14
	movq	%r9,%r15
	movq	%r10,%rax
	movq	%r11,%rdi
	subq	%r12,%r8
	sbbq	%r13,%r9
	sbbq	$0,%r10
	sbbq	24(%rbp),%r11
	sbbq	$0,%rsi
	cmovcq	%r14,%r8
	cmovcq	%r15,%r9
	cmovcq	%rax,%r10
	cmovcq	%rdi,%r11
	movq	%r8,0(%rbx)
	movq	%r9,8(%rbx)
	movq	%r10,16(%rbx)
	movq	%r11,24(%rbx)

	movq	40(%rsp),%r15
.cfi_restore	%r15
	movq	48(%rsp),%r14
.cfi_restore	%r14
	movq	56(%rsp),%r13
.cfi_restore	%r13
	movq	64(%rsp),%r12
.cfi_restore	%r12
	movq	72(%rsp),%rbx
.cfi_restore	%rbx
	movq	80(%rsp),%rbp
.cfi_restore	%rbp
	leaq	88(%rsp),%rsp
.cfi_adjust_cfa_offset	-88

	.byte	0xf3,0xc3
.cfi_endproc
.size	pasta_curves_sqrx_mont,.-pasta_curves_sqrx_mont
.type	__pasta_curves_mulx_mont,@function
.align	32
__pasta_curves_mulx_mont:
.cfi_startproc
	.byte	0xf3,0x0f,0x1e,0xfa

	mulxq	%r15,%r15,%r12
	mulxq	%rbp,%rbp,%r13
	addq	%r15,%r11
	mulxq	%r9,%r9,%r14
	movq	8(%rbx),%rdx
	adcq	%rbp,%r12
	adcq	%r9,%r13
	adcq	$0,%r14

	movq	%rax,%r10
	imulq	%r8,%rax


	xorq	%r15,%r15
	mulxq	0+128(%rsi),%rbp,%r9
	adoxq	%rbp,%r11
	adcxq	%r9,%r12

	mulxq	8+128(%rsi),%rbp,%r9
	adoxq	%rbp,%r12
	adcxq	%r9,%r13

	mulxq	16+128(%rsi),%rbp,%r9
	adoxq	%rbp,%r13
	adcxq	%r9,%r14

	mulxq	24+128(%rsi),%rbp,%r9
	movq	%rax,%rdx
	adoxq	%rbp,%r14
	adcxq	%r15,%r9
	adoxq	%r9,%r15


	mulxq	0+128(%rcx),%rbp,%rax
	adcxq	%rbp,%r10
	adoxq	%r11,%rax

	mulxq	8+128(%rcx),%rbp,%r9
	adcxq	%rbp,%rax
	adoxq	%r9,%r12

	adcxq	%r10,%r12
	adoxq	%r10,%r13

	mulxq	24+128(%rcx),%rbp,%r9
	movq	16(%rbx),%rdx
	adcxq	%rbp,%r13
	adoxq	%r9,%r14
	adcxq	%r10,%r14
	adoxq	%r10,%r15
	adcxq	%r10,%r15
	movq	%rax,%r11
	imulq	%r8,%rax


	xorq	%r10,%r10
	mulxq	0+128(%rsi),%rbp,%r9
	adoxq	%rbp,%r12
	adcxq	%r9,%r13

	mulxq	8+128(%rsi),%rbp,%r9
	adoxq	%rbp,%r13
	adcxq	%r9,%r14

	mulxq	16+128(%rsi),%rbp,%r9
	adoxq	%rbp,%r14
	adcxq	%r9,%r15

	mulxq	24+128(%rsi),%rbp,%r9
	movq	%rax,%rdx
	adoxq	%rbp,%r15
	adcxq	%r10,%r9
	adoxq	%r9,%r10


	mulxq	0+128(%rcx),%rbp,%rax
	adcxq	%rbp,%r11
	adoxq	%r12,%rax

	mulxq	8+128(%rcx),%rbp,%r9
	adcxq	%rbp,%rax
	adoxq	%r9,%r13

	adcxq	%r11,%r13
	adoxq	%r11,%r14

	mulxq	24+128(%rcx),%rbp,%r9
	movq	24(%rbx),%rdx
	adcxq	%rbp,%r14
	adoxq	%r9,%r15
	adcxq	%r11,%r15
	adoxq	%r11,%r10
	adcxq	%r11,%r10
	movq	%rax,%r12
	imulq	%r8,%rax


	xorq	%r11,%r11
	mulxq	0+128(%rsi),%rbp,%r9
	adoxq	%rbp,%r13
	adcxq	%r9,%r14

	mulxq	8+128(%rsi),%rbp,%r9
	adoxq	%rbp,%r14
	adcxq	%r9,%r15

	mulxq	16+128(%rsi),%rbp,%r9
	adoxq	%rbp,%r15
	adcxq	%r9,%r10

	mulxq	24+128(%rsi),%rbp,%r9
	movq	%rax,%rdx
	adoxq	%rbp,%r10
	adcxq	%r11,%r9
	adoxq	%r9,%r11


	mulxq	0+128(%rcx),%rbp,%rax
	adcxq	%rbp,%r12
	adoxq	%r13,%rax

	mulxq	8+128(%rcx),%rbp,%r9
	adcxq	%rbp,%rax
	adoxq	%r9,%r14

	adcxq	%r12,%r14
	adoxq	%r12,%r15

	mulxq	24+128(%rcx),%rbp,%r9
	movq	%rax,%rdx
	adcxq	%rbp,%r15
	adoxq	%r9,%r10
	adcxq	%r12,%r10
	adoxq	%r12,%r11
	adcxq	%r12,%r11
	imulq	%r8,%rdx


	xorq	%r12,%r12
	mulxq	0+128(%rcx),%r13,%r9
	adcxq	%rax,%r13
	adoxq	%r9,%r14

	mulxq	8+128(%rcx),%rbp,%r9
	adcxq	%rbp,%r14
	adoxq	%r9,%r15

	adcxq	%r13,%r15
	adoxq	%r13,%r10

	mulxq	24+128(%rcx),%rbp,%r9
	movq	%r14,%rdx
	leaq	128(%rcx),%rcx
	adcxq	%rbp,%r10
	adoxq	%r9,%r11
	movq	%r15,%rax
	adcxq	%r13,%r11
	adoxq	%r13,%r12
	adcq	$0,%r12




	movq	%r10,%rbp
	subq	0(%rcx),%r14
	sbbq	8(%rcx),%r15
	sbbq	16(%rcx),%r10
	movq	%r11,%r9
	sbbq	24(%rcx),%r11
	sbbq	$0,%r12

	cmovcq	%rdx,%r14
	cmovcq	%rax,%r15
	cmovcq	%rbp,%r10
	movq	%r14,0(%rdi)
	cmovcq	%r9,%r11
	movq	%r15,8(%rdi)
	movq	%r10,16(%rdi)
	movq	%r11,24(%rdi)

	.byte	0xf3,0xc3
.cfi_endproc
.size	__pasta_curves_mulx_mont,.-__pasta_curves_mulx_mont

.section	.note.gnu.property,"a",@note
	.long	4,2f-1f,5
	.byte	0x47,0x4E,0x55,0
1:	.long	0xc0000002,4,3
.align	8
2:

.section .note.GNU-stack,"",@progbits
