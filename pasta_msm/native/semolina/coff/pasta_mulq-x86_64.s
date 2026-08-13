# Copyright Supranational LLC
# Licensed under the Apache License, Version 2.0.
# SPDX-License-Identifier: Apache-2.0
# Modified by Zakura; generated from the attributed source.

.text

.globl	mul_mont_pasta

.def	mul_mont_pasta;	.scl 2;	.type 32;	.endef
.p2align	5
mul_mont_pasta:
	.byte	0xf3,0x0f,0x1e,0xfa
	movq	%rdi,8(%rsp)
	movq	%rsi,16(%rsp)
	movq	%rsp,%r11
.LSEH_begin_mul_mont_pasta:
	movq	%rcx,%rdi
	movq	%rdx,%rsi
	movq	%r8,%rdx
	movq	%r9,%rcx
	movq	40(%rsp),%r8


	pushq	%rbp

	pushq	%rbx

	pushq	%r12

	pushq	%r13

	pushq	%r14

	pushq	%r15

	pushq	%rdi

.LSEH_body_mul_mont_pasta:


	movq	0(%rdx),%rax
	movq	0(%rsi),%r13
	movq	8(%rsi),%r14
	movq	16(%rsi),%r12
	movq	24(%rsi),%rbp
	movq	%rdx,%rbx

	movq	%rax,%r15
	mulq	%r13
	movq	%rax,%r9
	movq	%r15,%rax
	movq	%rdx,%r10
	call	__mulq_mont_pasta

	movq	8(%rsp),%r15

	movq	16(%rsp),%r14

	movq	24(%rsp),%r13

	movq	32(%rsp),%r12

	movq	40(%rsp),%rbx

	movq	48(%rsp),%rbp

	leaq	56(%rsp),%rsp

.LSEH_epilogue_mul_mont_pasta:
	mov	8(%rsp),%rdi
	mov	16(%rsp),%rsi

	.byte	0xf3,0xc3

.LSEH_end_mul_mont_pasta:

.globl	sqr_mont_pasta

.def	sqr_mont_pasta;	.scl 2;	.type 32;	.endef
.p2align	5
sqr_mont_pasta:
	.byte	0xf3,0x0f,0x1e,0xfa
	movq	%rdi,8(%rsp)
	movq	%rsi,16(%rsp)
	movq	%rsp,%r11
.LSEH_begin_sqr_mont_pasta:
	movq	%rcx,%rdi
	movq	%rdx,%rsi
	movq	%r8,%rdx
	movq	%r9,%rcx


	pushq	%rbp

	pushq	%rbx

	pushq	%r12

	pushq	%r13

	pushq	%r14

	pushq	%r15

	pushq	%rdi

.LSEH_body_sqr_mont_pasta:


	movq	0(%rsi),%rax
	movq	%rcx,%r8
	movq	8(%rsi),%r14
	movq	%rdx,%rcx
	movq	16(%rsi),%r12
	leaq	(%rsi),%rbx
	movq	24(%rsi),%rbp

	movq	%rax,%r15
	mulq	%rax
	movq	%rax,%r9
	movq	%r15,%rax
	movq	%rdx,%r10
	call	__mulq_mont_pasta

	movq	8(%rsp),%r15

	movq	16(%rsp),%r14

	movq	24(%rsp),%r13

	movq	32(%rsp),%r12

	movq	40(%rsp),%rbx

	movq	48(%rsp),%rbp

	leaq	56(%rsp),%rsp

.LSEH_epilogue_sqr_mont_pasta:
	mov	8(%rsp),%rdi
	mov	16(%rsp),%rsi

	.byte	0xf3,0xc3

.LSEH_end_sqr_mont_pasta:
.def	__mulq_mont_pasta;	.scl 3;	.type 32;	.endef
.p2align	5
__mulq_mont_pasta:
	.byte	0xf3,0x0f,0x1e,0xfa

	mulq	%r14
	addq	%rax,%r10
	movq	%r15,%rax
	adcq	$0,%rdx
	movq	%rdx,%r11

	mulq	%r12
	addq	%rax,%r11
	movq	%r15,%rax
	adcq	$0,%rdx
	movq	%rdx,%r12

	mulq	%rbp
	addq	%rax,%r12
	movq	8(%rbx),%rax
	adcq	$0,%rdx
	xorq	%r14,%r14
	movq	%rdx,%r13

	movq	%r9,%rdi
	imulq	%r8,%r9


	movq	%rax,%r15
	mulq	0(%rsi)
	addq	%rax,%r10
	movq	%r15,%rax
	adcq	$0,%rdx
	movq	%rdx,%rbp

	mulq	8(%rsi)
	addq	%rax,%r11
	movq	%r15,%rax
	adcq	$0,%rdx
	addq	%rbp,%r11
	adcq	$0,%rdx
	movq	%rdx,%rbp

	mulq	16(%rsi)
	addq	%rax,%r12
	movq	%r15,%rax
	adcq	$0,%rdx
	addq	%rbp,%r12
	adcq	$0,%rdx
	movq	%rdx,%rbp

	mulq	24(%rsi)
	addq	%rax,%r13
	movq	%r9,%rax
	adcq	$0,%rdx
	addq	%rbp,%r13
	adcq	$0,%rdx
	movq	%rdx,%r14


	mulq	0(%rcx)
	addq	%rax,%rdi
	movq	%r9,%rax
	adcq	%rdx,%rdi

	mulq	8(%rcx)
	addq	%rax,%r10
	movq	%r9,%rax
	adcq	$0,%rdx

	xorq	%rbp,%rbp
	addq	%rdi,%r10
	adcq	%rdx,%r11
	adcq	$0,%rbp

	mulq	24(%rcx)
	addq	%rax,%r12
	movq	16(%rbx),%rax
	adcq	$0,%rdx
	addq	%rbp,%r12
	adcq	$0,%rdx
	addq	%rdx,%r13
	adcq	$0,%r14
	movq	%r10,%rdi
	imulq	%r8,%r10


	movq	%rax,%r9
	mulq	0(%rsi)
	addq	%rax,%r11
	movq	%r9,%rax
	adcq	$0,%rdx
	movq	%rdx,%rbp

	mulq	8(%rsi)
	addq	%rax,%r12
	movq	%r9,%rax
	adcq	$0,%rdx
	addq	%rbp,%r12
	adcq	$0,%rdx
	movq	%rdx,%rbp

	mulq	16(%rsi)
	addq	%rax,%r13
	movq	%r9,%rax
	adcq	$0,%rdx
	addq	%rbp,%r13
	adcq	$0,%rdx
	movq	%rdx,%rbp

	mulq	24(%rsi)
	addq	%rax,%r14
	movq	%r10,%rax
	adcq	$0,%rdx
	addq	%rbp,%r14
	adcq	$0,%rdx
	movq	%rdx,%r15


	mulq	0(%rcx)
	addq	%rax,%rdi
	movq	%r10,%rax
	adcq	%rdx,%rdi

	mulq	8(%rcx)
	addq	%rax,%r11
	movq	%r10,%rax
	adcq	$0,%rdx

	xorq	%rbp,%rbp
	addq	%rdi,%r11
	adcq	%rdx,%r12
	adcq	$0,%rbp

	mulq	24(%rcx)
	addq	%rax,%r13
	movq	24(%rbx),%rax
	adcq	$0,%rdx
	addq	%rbp,%r13
	adcq	$0,%rdx
	addq	%rdx,%r14
	adcq	$0,%r15
	movq	%r11,%rdi
	imulq	%r8,%r11


	movq	%rax,%r10
	mulq	0(%rsi)
	addq	%rax,%r12
	movq	%r10,%rax
	adcq	$0,%rdx
	movq	%rdx,%rbp

	mulq	8(%rsi)
	addq	%rax,%r13
	movq	%r10,%rax
	adcq	$0,%rdx
	addq	%rbp,%r13
	adcq	$0,%rdx
	movq	%rdx,%rbp

	mulq	16(%rsi)
	addq	%rax,%r14
	movq	%r10,%rax
	adcq	$0,%rdx
	addq	%rbp,%r14
	adcq	$0,%rdx
	movq	%rdx,%rbp

	mulq	24(%rsi)
	addq	%rax,%r15
	movq	%r11,%rax
	adcq	$0,%rdx
	addq	%rbp,%r15
	adcq	$0,%rdx
	movq	%rdx,%r9


	mulq	0(%rcx)
	addq	%rax,%rdi
	movq	%r11,%rax
	adcq	%rdx,%rdi

	mulq	8(%rcx)
	addq	%rax,%r12
	movq	%r11,%rax
	adcq	$0,%rdx

	xorq	%rbp,%rbp
	addq	%rdi,%r12
	adcq	%rdx,%r13
	adcq	$0,%rbp

	mulq	24(%rcx)
	addq	%rax,%r14
	movq	%r12,%rax
	adcq	$0,%rdx
	addq	%rbp,%r14
	adcq	$0,%rdx
	addq	%rdx,%r15
	adcq	$0,%r9
	imulq	%r8,%rax
	movq	8(%rsp),%rsi
	xorq	%r10,%r10


	movq	%rax,%r11
	mulq	0(%rcx)
	addq	%rax,%r12
	movq	%r11,%rax
	adcq	%rdx,%r12

	mulq	8(%rcx)
	addq	%rax,%r13
	movq	%r11,%rax
	adcq	$0,%rdx

	xorq	%rbp,%rbp
	addq	%r12,%r13
	adcq	%rdx,%r14
	adcq	$0,%rbp

	mulq	24(%rcx)
	movq	%r14,%rbx
	addq	%rbp,%r15
	adcq	$0,%rdx
	addq	%rax,%r15
	movq	%r13,%rax
	adcq	$0,%rdx
	addq	%rdx,%r9
	adcq	$0,%r10




	movq	%r15,%r12
	subq	0(%rcx),%r13
	sbbq	8(%rcx),%r14
	sbbq	16(%rcx),%r15
	movq	%r9,%rbp
	sbbq	24(%rcx),%r9
	sbbq	$0,%r10

	cmovcq	%rax,%r13
	cmovcq	%rbx,%r14
	cmovcq	%r12,%r15
	movq	%r13,0(%rsi)
	cmovcq	%rbp,%r9
	movq	%r14,8(%rsi)
	movq	%r15,16(%rsi)
	movq	%r9,24(%rsi)

	.byte	0xf3,0xc3


.globl	from_mont_pasta

.def	from_mont_pasta;	.scl 2;	.type 32;	.endef
.p2align	5
from_mont_pasta:
	.byte	0xf3,0x0f,0x1e,0xfa
	movq	%rdi,8(%rsp)
	movq	%rsi,16(%rsp)
	movq	%rsp,%r11
.LSEH_begin_from_mont_pasta:
	movq	%rcx,%rdi
	movq	%rdx,%rsi
	movq	%r8,%rdx
	movq	%r9,%rcx


	pushq	%rbp

	pushq	%rbx

	pushq	%r12

	pushq	%r13

	pushq	%r14

	pushq	%r15

	subq	$8,%rsp

.LSEH_body_from_mont_pasta:


	movq	%rdx,%rbx
	call	__mulq_by_1_mont_pasta





	movq	%r14,%r10
	movq	%r15,%r11
	movq	%r9,%r12

	subq	0(%rbx),%r13
	sbbq	8(%rbx),%r14
	sbbq	16(%rbx),%r15
	sbbq	24(%rbx),%r9

	cmovncq	%r13,%rax
	cmovncq	%r14,%r10
	cmovncq	%r15,%r11
	movq	%rax,0(%rdi)
	cmovncq	%r9,%r12
	movq	%r10,8(%rdi)
	movq	%r11,16(%rdi)
	movq	%r12,24(%rdi)

	movq	8(%rsp),%r15

	movq	16(%rsp),%r14

	movq	24(%rsp),%r13

	movq	32(%rsp),%r12

	movq	40(%rsp),%rbx

	movq	48(%rsp),%rbp

	leaq	56(%rsp),%rsp

.LSEH_epilogue_from_mont_pasta:
	mov	8(%rsp),%rdi
	mov	16(%rsp),%rsi

	.byte	0xf3,0xc3

.LSEH_end_from_mont_pasta:

.globl	redc_mont_pasta

.def	redc_mont_pasta;	.scl 2;	.type 32;	.endef
.p2align	5
redc_mont_pasta:
	.byte	0xf3,0x0f,0x1e,0xfa
	movq	%rdi,8(%rsp)
	movq	%rsi,16(%rsp)
	movq	%rsp,%r11
.LSEH_begin_redc_mont_pasta:
	movq	%rcx,%rdi
	movq	%rdx,%rsi
	movq	%r8,%rdx
	movq	%r9,%rcx


	pushq	%rbp

	pushq	%rbx

	pushq	%r12

	pushq	%r13

	pushq	%r14

	pushq	%r15

	subq	$8,%rsp

.LSEH_body_redc_mont_pasta:


	movq	%rdx,%rbx
	call	__mulq_by_1_mont_pasta

	addq	32(%rsi),%r13
	adcq	40(%rsi),%r14
	movq	%r13,%rax
	adcq	48(%rsi),%r15
	movq	%r14,%r10
	adcq	56(%rsi),%r9
	sbbq	%rsi,%rsi




	movq	%r15,%r11
	subq	0(%rbx),%r13
	sbbq	8(%rbx),%r14
	sbbq	16(%rbx),%r15
	movq	%r9,%r12
	sbbq	24(%rbx),%r9
	sbbq	$0,%rsi

	cmovncq	%r13,%rax
	cmovncq	%r14,%r10
	cmovncq	%r15,%r11
	movq	%rax,0(%rdi)
	cmovncq	%r9,%r12
	movq	%r10,8(%rdi)
	movq	%r11,16(%rdi)
	movq	%r12,24(%rdi)

	movq	8(%rsp),%r15

	movq	16(%rsp),%r14

	movq	24(%rsp),%r13

	movq	32(%rsp),%r12

	movq	40(%rsp),%rbx

	movq	48(%rsp),%rbp

	leaq	56(%rsp),%rsp

.LSEH_epilogue_redc_mont_pasta:
	mov	8(%rsp),%rdi
	mov	16(%rsp),%rsi

	.byte	0xf3,0xc3

.LSEH_end_redc_mont_pasta:
.def	__mulq_by_1_mont_pasta;	.scl 3;	.type 32;	.endef
.p2align	5
__mulq_by_1_mont_pasta:
	.byte	0xf3,0x0f,0x1e,0xfa

	movq	0(%rsi),%rax
	movq	8(%rsi),%r10
	movq	16(%rsi),%r11
	movq	24(%rsi),%r12

	movq	%rax,%r13
	imulq	%rcx,%rax
	movq	%rax,%r9

	mulq	0(%rbx)
	addq	%rax,%r13
	movq	%r9,%rax
	adcq	%rdx,%r13

	mulq	8(%rbx)
	addq	%rax,%r10
	movq	%r9,%rax
	adcq	$0,%rdx

	xorq	%rbp,%rbp
	addq	%r13,%r10
	adcq	%rdx,%r11
	adcq	$0,%rbp

	movq	%r10,%r14
	imulq	%rcx,%r10

	mulq	24(%rbx)
	addq	%rax,%r12
	movq	%r10,%rax
	adcq	$0,%rdx
	addq	%rbp,%r12
	adcq	$0,%rdx
	movq	%rdx,%r13

	mulq	0(%rbx)
	addq	%rax,%r14
	movq	%r10,%rax
	adcq	%rdx,%r14

	mulq	8(%rbx)
	addq	%rax,%r11
	movq	%r10,%rax
	adcq	$0,%rdx

	xorq	%rbp,%rbp
	addq	%r14,%r11
	adcq	%rdx,%r12
	adcq	$0,%rbp

	movq	%r11,%r15
	imulq	%rcx,%r11

	mulq	24(%rbx)
	addq	%rax,%r13
	movq	%r11,%rax
	adcq	$0,%rdx
	addq	%rbp,%r13
	adcq	$0,%rdx
	movq	%rdx,%r14

	mulq	0(%rbx)
	addq	%rax,%r15
	movq	%r11,%rax
	adcq	%rdx,%r15

	mulq	8(%rbx)
	addq	%rax,%r12
	movq	%r11,%rax
	adcq	$0,%rdx

	xorq	%rbp,%rbp
	addq	%r15,%r12
	adcq	%rdx,%r13
	adcq	$0,%rbp

	movq	%r12,%r9
	imulq	%rcx,%r12

	mulq	24(%rbx)
	addq	%rax,%r14
	movq	%r12,%rax
	adcq	$0,%rdx
	addq	%rbp,%r14
	adcq	$0,%rdx
	movq	%rdx,%r15

	mulq	0(%rbx)
	addq	%rax,%r9
	movq	%r12,%rax
	adcq	%rdx,%r9

	mulq	8(%rbx)
	addq	%rax,%r13
	movq	%r12,%rax
	adcq	$0,%rdx

	xorq	%rbp,%rbp
	addq	%r9,%r13
	adcq	%rdx,%r14
	adcq	$0,%rbp


	mulq	24(%rbx)
	addq	%rax,%r15
	movq	%r13,%rax
	adcq	$0,%rdx
	addq	%rbp,%r15
	adcq	$0,%rdx
	movq	%rdx,%r9
	.byte	0xf3,0xc3

.globl	sqr_n_mul_mont_pasta

.def	sqr_n_mul_mont_pasta;	.scl 2;	.type 32;	.endef
.p2align	5
sqr_n_mul_mont_pasta:
	.byte	0xf3,0x0f,0x1e,0xfa
	movq	%rdi,8(%rsp)
	movq	%rsi,16(%rsp)
	movq	%rsp,%r11
.LSEH_begin_sqr_n_mul_mont_pasta:
	movq	%rcx,%rdi
	movq	%rdx,%rsi
	movq	%r8,%rdx
	movq	%r9,%rcx
	movq	40(%rsp),%r8
	movq	48(%rsp),%r9


	pushq	%rbp

	pushq	%rbx

	pushq	%r12

	pushq	%r13

	pushq	%r14

	pushq	%r15

	subq	$40,%rsp

.LSEH_body_sqr_n_mul_mont_pasta:

	movq	%rcx,16(%rsp)
	movq	%rdi,24(%rsp)

	movq	0(%rsi),%rax
	movq	8(%rsi),%rbp
	movq	16(%rsi),%rdi
	movq	24(%rsi),%rsi
	movq	%rdx,%rbx
	movq	%r9,(%rsp)
	movq	%rax,%rcx
	jmp	.Loop_sqrq_pasta

.p2align	5
.Loop_sqrq_pasta:
	movq	%rbx,8(%rsp)

	mulq	%rax
	movq	%rax,%r9
	movq	%rcx,%rax
	movq	%rdx,%r10

	mulq	%rbp
	addq	%rax,%r10
	movq	%rcx,%rax
	adcq	$0,%rdx
	movq	%rdx,%r11

	mulq	%rdi
	addq	%rax,%r11
	movq	%rcx,%rax
	adcq	$0,%rdx
	movq	%rdx,%r12

	mulq	%rsi
	addq	%rax,%r12
	movq	%rbp,%rax
	adcq	$0,%rdx
	movq	%rdx,%r13
	movq	%r9,%r15
	imulq	(%rsp),%r9


	mulq	%rcx
	addq	%rax,%r10
	movq	%rbp,%rax
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	%rbp
	addq	%rax,%r11
	movq	%rbp,%rax
	adcq	$0,%rdx
	addq	%rbx,%r11
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	%rdi
	addq	%rax,%r12
	movq	%rbp,%rax
	adcq	$0,%rdx
	addq	%rbx,%r12
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	%rsi
	addq	%rax,%r13
	movq	%r9,%rax
	adcq	$0,%rdx
	addq	%rbx,%r13
	adcq	$0,%rdx
	movq	%rdx,%r14


	mulq	0(%r8)
	addq	%rax,%r15
	movq	%r9,%rax
	adcq	%rdx,%r15

	mulq	8(%r8)
	addq	%rax,%r10
	movq	%r9,%rax
	adcq	$0,%rdx

	xorq	%rbx,%rbx
	addq	%r15,%r10
	adcq	%rdx,%r11
	adcq	$0,%rbx

	mulq	24(%r8)
	addq	%rax,%r12
	movq	%rdi,%rax
	adcq	$0,%rdx
	addq	%rbx,%r12
	adcq	%rdx,%r13
	adcq	$0,%r14
	movq	%r10,%r9
	imulq	(%rsp),%r10


	mulq	%rcx
	addq	%rax,%r11
	movq	%rdi,%rax
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	%rbp
	addq	%rax,%r12
	movq	%rdi,%rax
	adcq	$0,%rdx
	addq	%rbx,%r12
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	%rdi
	addq	%rax,%r13
	movq	%rdi,%rax
	adcq	$0,%rdx
	addq	%rbx,%r13
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	%rsi
	addq	%rax,%r14
	movq	%r10,%rax
	adcq	$0,%rdx
	addq	%rbx,%r14
	adcq	$0,%rdx
	movq	%rdx,%r15


	mulq	0(%r8)
	addq	%rax,%r9
	movq	%r10,%rax
	adcq	%rdx,%r9

	mulq	8(%r8)
	addq	%rax,%r11
	movq	%r10,%rax
	adcq	$0,%rdx

	xorq	%rbx,%rbx
	addq	%r9,%r11
	adcq	%rdx,%r12
	adcq	$0,%rbx

	mulq	24(%r8)
	addq	%rax,%r13
	movq	%rsi,%rax
	adcq	$0,%rdx
	addq	%rbx,%r13
	adcq	%rdx,%r14
	adcq	$0,%r15
	movq	%r11,%r10
	imulq	(%rsp),%r11


	mulq	%rcx
	addq	%rax,%r12
	movq	%rsi,%rax
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	%rbp
	addq	%rax,%r13
	movq	%rsi,%rax
	adcq	$0,%rdx
	addq	%rbx,%r13
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	%rdi
	addq	%rax,%r14
	movq	%rsi,%rax
	adcq	$0,%rdx
	addq	%rbx,%r14
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	%rsi
	addq	%rax,%r15
	movq	%r11,%rax
	adcq	$0,%rdx
	addq	%rbx,%r15
	adcq	$0,%rdx
	movq	%rdx,%r9


	mulq	0(%r8)
	addq	%rax,%r10
	movq	%r11,%rax
	adcq	%rdx,%r10

	mulq	8(%r8)
	addq	%rax,%r12
	movq	%r11,%rax
	adcq	$0,%rdx

	xorq	%rbx,%rbx
	addq	%r10,%r12
	adcq	%rdx,%r13
	adcq	$0,%rbx

	mulq	24(%r8)
	addq	%rax,%r14
	movq	%r12,%rax
	adcq	$0,%rdx
	addq	%rbx,%r14
	adcq	%rdx,%r15
	adcq	$0,%r9
	imulq	(%rsp),%rax
	movq	%r13,%rcx
	movq	%r14,%rbp
	movq	8(%rsp),%rbx
	movq	%r9,%rsi
	movq	16(%rsp),%r11


	movq	%rax,%r10
	mulq	0(%r8)
	addq	%rax,%r12
	movq	%r10,%rax
	adcq	%rdx,%r12

	mulq	8(%r8)
	addq	%rax,%rcx
	movq	%r10,%rax
	adcq	$0,%rdx

	xorq	%rdi,%rdi
	addq	%r12,%rcx
	adcq	%rdx,%rbp
	adcq	$0,%rdi

	mulq	24(%r8)
	addq	%rax,%rdi
	movq	%rcx,%rax
	adcq	$0,%rdx
	addq	%r15,%rdi
	adcq	%rdx,%rsi

	subq	$1,%rbx
	jnz	.Loop_sqrq_pasta
	mulq	0(%r11)
	movq	%rax,%r12
	movq	%rcx,%rax
	movq	%rdx,%r13

	mulq	8(%r11)
	addq	%rax,%r13
	movq	%rcx,%rax
	adcq	$0,%rdx
	movq	%rdx,%r14

	mulq	16(%r11)
	addq	%rax,%r14
	movq	%rcx,%rax
	adcq	$0,%rdx
	movq	%rdx,%r15

	mulq	24(%r11)
	addq	%rax,%r15
	movq	%rbp,%rax
	adcq	$0,%rdx
	movq	%rdx,%r9
	movq	%r12,%rcx
	imulq	(%rsp),%r12


	mulq	0(%r11)
	addq	%rax,%r13
	movq	%rbp,%rax
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	8(%r11)
	addq	%rax,%r14
	movq	%rbp,%rax
	adcq	$0,%rdx
	addq	%rbx,%r14
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	16(%r11)
	addq	%rax,%r15
	movq	%rbp,%rax
	adcq	$0,%rdx
	addq	%rbx,%r15
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	24(%r11)
	addq	%rax,%r9
	movq	%r12,%rax
	adcq	$0,%rdx
	addq	%rbx,%r9
	adcq	$0,%rdx
	movq	%rdx,%r10


	mulq	0(%r8)
	addq	%rax,%rcx
	movq	%r12,%rax
	adcq	%rdx,%rcx

	mulq	8(%r8)
	addq	%rax,%r13
	movq	%r12,%rax
	adcq	$0,%rdx

	xorq	%rbx,%rbx
	addq	%rcx,%r13
	adcq	%rdx,%r14
	adcq	$0,%rbx

	mulq	24(%r8)
	addq	%rax,%r15
	movq	%rdi,%rax
	adcq	$0,%rdx
	addq	%rbx,%r15
	adcq	%rdx,%r9
	adcq	$0,%r10
	movq	%r13,%r12
	imulq	(%rsp),%r13


	mulq	0(%r11)
	addq	%rax,%r14
	movq	%rdi,%rax
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	8(%r11)
	addq	%rax,%r15
	movq	%rdi,%rax
	adcq	$0,%rdx
	addq	%rbx,%r15
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	16(%r11)
	addq	%rax,%r9
	movq	%rdi,%rax
	adcq	$0,%rdx
	addq	%rbx,%r9
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	24(%r11)
	addq	%rax,%r10
	movq	%r13,%rax
	adcq	$0,%rdx
	addq	%rbx,%r10
	adcq	$0,%rdx
	movq	%rdx,%rcx


	mulq	0(%r8)
	addq	%rax,%r12
	movq	%r13,%rax
	adcq	%rdx,%r12

	mulq	8(%r8)
	addq	%rax,%r14
	movq	%r13,%rax
	adcq	$0,%rdx

	xorq	%rbx,%rbx
	addq	%r12,%r14
	adcq	%rdx,%r15
	adcq	$0,%rbx

	mulq	24(%r8)
	addq	%rax,%r9
	movq	%rsi,%rax
	adcq	$0,%rdx
	addq	%rbx,%r9
	adcq	%rdx,%r10
	adcq	$0,%rcx
	movq	%r14,%r13
	imulq	(%rsp),%r14


	mulq	0(%r11)
	addq	%rax,%r15
	movq	%rsi,%rax
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	8(%r11)
	addq	%rax,%r9
	movq	%rsi,%rax
	adcq	$0,%rdx
	addq	%rbx,%r9
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	16(%r11)
	addq	%rax,%r10
	movq	%rsi,%rax
	adcq	$0,%rdx
	addq	%rbx,%r10
	adcq	$0,%rdx
	movq	%rdx,%rbx

	mulq	24(%r11)
	addq	%rax,%rcx
	movq	%r14,%rax
	adcq	$0,%rdx
	addq	%rbx,%rcx
	adcq	$0,%rdx
	movq	%rdx,%r12


	mulq	0(%r8)
	addq	%rax,%r13
	movq	%r14,%rax
	adcq	%rdx,%r13

	mulq	8(%r8)
	addq	%rax,%r15
	movq	%r14,%rax
	adcq	$0,%rdx

	xorq	%rbx,%rbx
	addq	%r13,%r15
	adcq	%rdx,%r9
	adcq	$0,%rbx

	mulq	24(%r8)
	addq	%rax,%r10
	movq	%r15,%rax
	adcq	$0,%rdx
	addq	%rbx,%r10
	adcq	%rdx,%rcx
	adcq	$0,%r12
	imulq	(%rsp),%rax
	movq	24(%rsp),%rdi


	movq	%rax,%r14
	mulq	0(%r8)
	addq	%rax,%r15
	movq	%r14,%rax
	adcq	%rdx,%r15

	mulq	8(%r8)
	addq	%rax,%r9
	movq	%r14,%rax
	adcq	$0,%rdx

	xorq	%rbx,%rbx
	addq	%r15,%r9
	adcq	%rdx,%r10
	adcq	$0,%rbx

	mulq	24(%r8)
	movq	%r9,%r13
	addq	%rbx,%rcx
	adcq	$0,%rdx
	movq	%r10,%r14
	addq	%rax,%rcx
	adcq	%rdx,%r12




	movq	%rcx,%r15
	subq	0(%r8),%r9
	sbbq	8(%r8),%r10
	sbbq	16(%r8),%rcx
	movq	%r12,%rbx
	sbbq	24(%r8),%r12

	cmovcq	%r13,%r9
	cmovcq	%r14,%r10
	cmovcq	%r15,%rcx
	movq	%r9,0(%rdi)
	cmovcq	%rbx,%r12
	movq	%r10,8(%rdi)
	movq	%rcx,16(%rdi)
	movq	%r12,24(%rdi)

	movq	40(%rsp),%r15

	movq	48(%rsp),%r14

	movq	56(%rsp),%r13

	movq	64(%rsp),%r12

	movq	72(%rsp),%rbx

	movq	80(%rsp),%rbp

	leaq	88(%rsp),%rsp

.LSEH_epilogue_sqr_n_mul_mont_pasta:
	mov	8(%rsp),%rdi
	mov	16(%rsp),%rsi

	.byte	0xf3,0xc3

.LSEH_end_sqr_n_mul_mont_pasta:
.section	.pdata
.p2align	2
.rva	.LSEH_begin_mul_mont_pasta
.rva	.LSEH_body_mul_mont_pasta
.rva	.LSEH_info_mul_mont_pasta_prologue

.rva	.LSEH_body_mul_mont_pasta
.rva	.LSEH_epilogue_mul_mont_pasta
.rva	.LSEH_info_mul_mont_pasta_body

.rva	.LSEH_epilogue_mul_mont_pasta
.rva	.LSEH_end_mul_mont_pasta
.rva	.LSEH_info_mul_mont_pasta_epilogue

.rva	.LSEH_begin_sqr_mont_pasta
.rva	.LSEH_body_sqr_mont_pasta
.rva	.LSEH_info_sqr_mont_pasta_prologue

.rva	.LSEH_body_sqr_mont_pasta
.rva	.LSEH_epilogue_sqr_mont_pasta
.rva	.LSEH_info_sqr_mont_pasta_body

.rva	.LSEH_epilogue_sqr_mont_pasta
.rva	.LSEH_end_sqr_mont_pasta
.rva	.LSEH_info_sqr_mont_pasta_epilogue

.rva	.LSEH_begin_from_mont_pasta
.rva	.LSEH_body_from_mont_pasta
.rva	.LSEH_info_from_mont_pasta_prologue

.rva	.LSEH_body_from_mont_pasta
.rva	.LSEH_epilogue_from_mont_pasta
.rva	.LSEH_info_from_mont_pasta_body

.rva	.LSEH_epilogue_from_mont_pasta
.rva	.LSEH_end_from_mont_pasta
.rva	.LSEH_info_from_mont_pasta_epilogue

.rva	.LSEH_begin_redc_mont_pasta
.rva	.LSEH_body_redc_mont_pasta
.rva	.LSEH_info_redc_mont_pasta_prologue

.rva	.LSEH_body_redc_mont_pasta
.rva	.LSEH_epilogue_redc_mont_pasta
.rva	.LSEH_info_redc_mont_pasta_body

.rva	.LSEH_epilogue_redc_mont_pasta
.rva	.LSEH_end_redc_mont_pasta
.rva	.LSEH_info_redc_mont_pasta_epilogue

.rva	.LSEH_begin_sqr_n_mul_mont_pasta
.rva	.LSEH_body_sqr_n_mul_mont_pasta
.rva	.LSEH_info_sqr_n_mul_mont_pasta_prologue

.rva	.LSEH_body_sqr_n_mul_mont_pasta
.rva	.LSEH_epilogue_sqr_n_mul_mont_pasta
.rva	.LSEH_info_sqr_n_mul_mont_pasta_body

.rva	.LSEH_epilogue_sqr_n_mul_mont_pasta
.rva	.LSEH_end_sqr_n_mul_mont_pasta
.rva	.LSEH_info_sqr_n_mul_mont_pasta_epilogue

.section	.xdata
.p2align	3
.LSEH_info_mul_mont_pasta_prologue:
.byte	1,0,5,0x0b
.byte	0,0x74,1,0
.byte	0,0x64,2,0
.byte	0,0x03
.byte	0,0
.LSEH_info_mul_mont_pasta_body:
.byte	1,0,17,0
.byte	0x00,0xf4,0x01,0x00
.byte	0x00,0xe4,0x02,0x00
.byte	0x00,0xd4,0x03,0x00
.byte	0x00,0xc4,0x04,0x00
.byte	0x00,0x34,0x05,0x00
.byte	0x00,0x54,0x06,0x00
.byte	0x00,0x74,0x08,0x00
.byte	0x00,0x64,0x09,0x00
.byte	0x00,0x62
.byte	0x00,0x00
.LSEH_info_mul_mont_pasta_epilogue:
.byte	1,0,4,0
.byte	0x00,0x74,0x01,0x00
.byte	0x00,0x64,0x02,0x00
.byte	0x00,0x00,0x00,0x00

.LSEH_info_sqr_mont_pasta_prologue:
.byte	1,0,5,0x0b
.byte	0,0x74,1,0
.byte	0,0x64,2,0
.byte	0,0x03
.byte	0,0
.LSEH_info_sqr_mont_pasta_body:
.byte	1,0,17,0
.byte	0x00,0xf4,0x01,0x00
.byte	0x00,0xe4,0x02,0x00
.byte	0x00,0xd4,0x03,0x00
.byte	0x00,0xc4,0x04,0x00
.byte	0x00,0x34,0x05,0x00
.byte	0x00,0x54,0x06,0x00
.byte	0x00,0x74,0x08,0x00
.byte	0x00,0x64,0x09,0x00
.byte	0x00,0x62
.byte	0x00,0x00
.LSEH_info_sqr_mont_pasta_epilogue:
.byte	1,0,4,0
.byte	0x00,0x74,0x01,0x00
.byte	0x00,0x64,0x02,0x00
.byte	0x00,0x00,0x00,0x00

.LSEH_info_from_mont_pasta_prologue:
.byte	1,0,5,0x0b
.byte	0,0x74,1,0
.byte	0,0x64,2,0
.byte	0,0x03
.byte	0,0
.LSEH_info_from_mont_pasta_body:
.byte	1,0,17,0
.byte	0x00,0xf4,0x01,0x00
.byte	0x00,0xe4,0x02,0x00
.byte	0x00,0xd4,0x03,0x00
.byte	0x00,0xc4,0x04,0x00
.byte	0x00,0x34,0x05,0x00
.byte	0x00,0x54,0x06,0x00
.byte	0x00,0x74,0x08,0x00
.byte	0x00,0x64,0x09,0x00
.byte	0x00,0x62
.byte	0x00,0x00
.LSEH_info_from_mont_pasta_epilogue:
.byte	1,0,4,0
.byte	0x00,0x74,0x01,0x00
.byte	0x00,0x64,0x02,0x00
.byte	0x00,0x00,0x00,0x00

.LSEH_info_redc_mont_pasta_prologue:
.byte	1,0,5,0x0b
.byte	0,0x74,1,0
.byte	0,0x64,2,0
.byte	0,0x03
.byte	0,0
.LSEH_info_redc_mont_pasta_body:
.byte	1,0,17,0
.byte	0x00,0xf4,0x01,0x00
.byte	0x00,0xe4,0x02,0x00
.byte	0x00,0xd4,0x03,0x00
.byte	0x00,0xc4,0x04,0x00
.byte	0x00,0x34,0x05,0x00
.byte	0x00,0x54,0x06,0x00
.byte	0x00,0x74,0x08,0x00
.byte	0x00,0x64,0x09,0x00
.byte	0x00,0x62
.byte	0x00,0x00
.LSEH_info_redc_mont_pasta_epilogue:
.byte	1,0,4,0
.byte	0x00,0x74,0x01,0x00
.byte	0x00,0x64,0x02,0x00
.byte	0x00,0x00,0x00,0x00

.LSEH_info_sqr_n_mul_mont_pasta_prologue:
.byte	1,0,5,0x0b
.byte	0,0x74,1,0
.byte	0,0x64,2,0
.byte	0,0x03
.byte	0,0
.LSEH_info_sqr_n_mul_mont_pasta_body:
.byte	1,0,17,0
.byte	0x00,0xf4,0x05,0x00
.byte	0x00,0xe4,0x06,0x00
.byte	0x00,0xd4,0x07,0x00
.byte	0x00,0xc4,0x08,0x00
.byte	0x00,0x34,0x09,0x00
.byte	0x00,0x54,0x0a,0x00
.byte	0x00,0x74,0x0c,0x00
.byte	0x00,0x64,0x0d,0x00
.byte	0x00,0xa2
.byte	0x00,0x00
.LSEH_info_sqr_n_mul_mont_pasta_epilogue:
.byte	1,0,4,0
.byte	0x00,0x74,0x01,0x00
.byte	0x00,0x64,0x02,0x00
.byte	0x00,0x00,0x00,0x00
