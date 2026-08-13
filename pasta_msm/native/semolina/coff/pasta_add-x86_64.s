# Copyright Supranational LLC
# Licensed under the Apache License, Version 2.0.
# SPDX-License-Identifier: Apache-2.0
# Modified by Zakura; generated from the attributed source.

.text

.globl	pasta_add

.def	pasta_add;	.scl 2;	.type 32;	.endef
.p2align	5
pasta_add:
	.byte	0xf3,0x0f,0x1e,0xfa
	movq	%rdi,8(%rsp)
	movq	%rsi,16(%rsp)
	movq	%rsp,%r11
.LSEH_begin_pasta_add:
	movq	%rcx,%rdi
	movq	%rdx,%rsi
	movq	%r8,%rdx
	movq	%r9,%rcx


	pushq	%rbp

	pushq	%rbx

	subq	$8,%rsp

.LSEH_body_pasta_add:


	movq	0(%rsi),%r8
	movq	8(%rsi),%r9
	movq	16(%rsi),%r10
	movq	24(%rsi),%r11

.Loaded_a_pasta_add:
	addq	0(%rdx),%r8
	adcq	8(%rdx),%r9
	movq	%r8,%rax
	adcq	16(%rdx),%r10
	movq	%r9,%rsi
	adcq	24(%rdx),%r11
	sbbq	%rdx,%rdx

	movq	%r10,%rbx
	subq	0(%rcx),%r8
	sbbq	8(%rcx),%r9
	sbbq	16(%rcx),%r10
	movq	%r11,%rbp
	sbbq	24(%rcx),%r11
	sbbq	$0,%rdx

	cmovcq	%rax,%r8
	cmovcq	%rsi,%r9
	movq	%r8,0(%rdi)
	cmovcq	%rbx,%r10
	movq	%r9,8(%rdi)
	cmovcq	%rbp,%r11
	movq	%r10,16(%rdi)
	movq	%r11,24(%rdi)

	movq	8(%rsp),%rbx

	movq	16(%rsp),%rbp

	leaq	24(%rsp),%rsp

.LSEH_epilogue_pasta_add:
	mov	8(%rsp),%rdi
	mov	16(%rsp),%rsi

	.byte	0xf3,0xc3

.LSEH_end_pasta_add:


.globl	pasta_cneg

.def	pasta_cneg;	.scl 2;	.type 32;	.endef
.p2align	5
pasta_cneg:
	.byte	0xf3,0x0f,0x1e,0xfa
	movq	%rdi,8(%rsp)
	movq	%rsi,16(%rsp)
	movq	%rsp,%r11
.LSEH_begin_pasta_cneg:
	movq	%rcx,%rdi
	movq	%rdx,%rsi
	movq	%r8,%rdx
	movq	%r9,%rcx


	pushq	%rbp

	pushq	%rbx

	pushq	%r12

.LSEH_body_pasta_cneg:


	movq	0(%rsi),%r12
	movq	8(%rsi),%r9
	movq	16(%rsi),%r10
	movq	%r12,%r8
	movq	24(%rsi),%r11
	orq	%r9,%r12
	orq	%r10,%r12
	orq	%r11,%r12
	movq	$-1,%rbp

	movq	0(%rcx),%rax
	cmovnzq	%rbp,%r12
	movq	8(%rcx),%rsi
	movq	16(%rcx),%rbx
	andq	%r12,%rax
	movq	24(%rcx),%rbp
	andq	%r12,%rsi
	andq	%r12,%rbx
	andq	%r12,%rbp

	subq	%r8,%rax
	sbbq	%r9,%rsi
	sbbq	%r10,%rbx
	sbbq	%r11,%rbp

	orq	%rdx,%rdx

	cmovzq	%r8,%rax
	cmovzq	%r9,%rsi
	movq	%rax,0(%rdi)
	cmovzq	%r10,%rbx
	movq	%rsi,8(%rdi)
	cmovzq	%r11,%rbp
	movq	%rbx,16(%rdi)
	movq	%rbp,24(%rdi)

	movq	0(%rsp),%r12

	movq	8(%rsp),%rbx

	movq	16(%rsp),%rbp

	leaq	24(%rsp),%rsp

.LSEH_epilogue_pasta_cneg:
	mov	8(%rsp),%rdi
	mov	16(%rsp),%rsi

	.byte	0xf3,0xc3

.LSEH_end_pasta_cneg:


.globl	pasta_sub

.def	pasta_sub;	.scl 2;	.type 32;	.endef
.p2align	5
pasta_sub:
	.byte	0xf3,0x0f,0x1e,0xfa
	movq	%rdi,8(%rsp)
	movq	%rsi,16(%rsp)
	movq	%rsp,%r11
.LSEH_begin_pasta_sub:
	movq	%rcx,%rdi
	movq	%rdx,%rsi
	movq	%r8,%rdx
	movq	%r9,%rcx


	pushq	%rbp

	pushq	%rbx

	subq	$8,%rsp

.LSEH_body_pasta_sub:


	movq	0(%rsi),%r8
	movq	8(%rsi),%r9
	movq	16(%rsi),%r10
	movq	24(%rsi),%r11

	subq	0(%rdx),%r8
	movq	0(%rcx),%rax
	sbbq	8(%rdx),%r9
	movq	8(%rcx),%rsi
	sbbq	16(%rdx),%r10
	movq	16(%rcx),%rbx
	sbbq	24(%rdx),%r11
	movq	24(%rcx),%rbp
	sbbq	%rdx,%rdx

	andq	%rdx,%rax
	andq	%rdx,%rsi
	andq	%rdx,%rbx
	andq	%rdx,%rbp

	addq	%rax,%r8
	adcq	%rsi,%r9
	movq	%r8,0(%rdi)
	adcq	%rbx,%r10
	movq	%r9,8(%rdi)
	adcq	%rbp,%r11
	movq	%r10,16(%rdi)
	movq	%r11,24(%rdi)

	movq	8(%rsp),%rbx

	movq	16(%rsp),%rbp

	leaq	24(%rsp),%rsp

.LSEH_epilogue_pasta_sub:
	mov	8(%rsp),%rdi
	mov	16(%rsp),%rsi

	.byte	0xf3,0xc3

.LSEH_end_pasta_sub:

.def	__lshift_mod_256;	.scl 3;	.type 32;	.endef
.p2align	5
__lshift_mod_256:
	.byte	0xf3,0x0f,0x1e,0xfa

	addq	%r8,%r8
	adcq	%r9,%r9
	movq	%r8,%rax
	adcq	%r10,%r10
	movq	%r9,%rsi
	adcq	%r11,%r11
	sbbq	%r12,%r12

	movq	%r10,%rbx
	subq	0(%rcx),%r8
	sbbq	8(%rcx),%r9
	sbbq	16(%rcx),%r10
	movq	%r11,%rbp
	sbbq	24(%rcx),%r11
	sbbq	$0,%r12

	cmovcq	%rax,%r8
	cmovcq	%rsi,%r9
	cmovcq	%rbx,%r10
	cmovcq	%rbp,%r11

	.byte	0xf3,0xc3



.globl	pasta_lshift

.def	pasta_lshift;	.scl 2;	.type 32;	.endef
.p2align	5
pasta_lshift:
	.byte	0xf3,0x0f,0x1e,0xfa
	movq	%rdi,8(%rsp)
	movq	%rsi,16(%rsp)
	movq	%rsp,%r11
.LSEH_begin_pasta_lshift:
	movq	%rcx,%rdi
	movq	%rdx,%rsi
	movq	%r8,%rdx
	movq	%r9,%rcx


	pushq	%rbp

	pushq	%rbx

	pushq	%r12

.LSEH_body_pasta_lshift:


	movq	0(%rsi),%r8
	movq	8(%rsi),%r9
	movq	16(%rsi),%r10
	movq	24(%rsi),%r11

.Loop_lshift_mod_256:
	call	__lshift_mod_256
	decl	%edx
	jnz	.Loop_lshift_mod_256

	movq	%r8,0(%rdi)
	movq	%r9,8(%rdi)
	movq	%r10,16(%rdi)
	movq	%r11,24(%rdi)

	movq	0(%rsp),%r12

	movq	8(%rsp),%rbx

	movq	16(%rsp),%rbp

	leaq	24(%rsp),%rsp

.LSEH_epilogue_pasta_lshift:
	mov	8(%rsp),%rdi
	mov	16(%rsp),%rsi

	.byte	0xf3,0xc3

.LSEH_end_pasta_lshift:


.globl	pasta_rshift

.def	pasta_rshift;	.scl 2;	.type 32;	.endef
.p2align	5
pasta_rshift:
	.byte	0xf3,0x0f,0x1e,0xfa
	movq	%rdi,8(%rsp)
	movq	%rsi,16(%rsp)
	movq	%rsp,%r11
.LSEH_begin_pasta_rshift:
	movq	%rcx,%rdi
	movq	%rdx,%rsi
	movq	%r8,%rdx
	movq	%r9,%rcx


	pushq	%rbp

	pushq	%rbx

	subq	$8,%rsp

.LSEH_body_pasta_rshift:


	movq	0(%rsi),%rbp
	movq	8(%rsi),%r9
	movq	16(%rsi),%r10
	movq	24(%rsi),%r11

.Loop_rshift_mod_256:
	movq	%rbp,%r8
	andq	$1,%rbp
	movq	0(%rcx),%rax
	negq	%rbp
	movq	8(%rcx),%rsi
	movq	16(%rcx),%rbx

	andq	%rbp,%rax
	andq	%rbp,%rsi
	andq	%rbp,%rbx
	andq	24(%rcx),%rbp

	addq	%rax,%r8
	adcq	%rsi,%r9
	adcq	%rbx,%r10
	adcq	%rbp,%r11
	sbbq	%rax,%rax

	shrq	$1,%r8
	movq	%r9,%rbp
	shrq	$1,%r9
	movq	%r10,%rbx
	shrq	$1,%r10
	movq	%r11,%rsi
	shrq	$1,%r11

	shlq	$63,%rbp
	shlq	$63,%rbx
	orq	%r8,%rbp
	shlq	$63,%rsi
	orq	%rbx,%r9
	shlq	$63,%rax
	orq	%rsi,%r10
	orq	%rax,%r11

	decl	%edx
	jnz	.Loop_rshift_mod_256

	movq	%rbp,0(%rdi)
	movq	%r9,8(%rdi)
	movq	%r10,16(%rdi)
	movq	%r11,24(%rdi)

	movq	8(%rsp),%rbx

	movq	16(%rsp),%rbp

	leaq	24(%rsp),%rsp

.LSEH_epilogue_pasta_rshift:
	mov	8(%rsp),%rdi
	mov	16(%rsp),%rsi

	.byte	0xf3,0xc3

.LSEH_end_pasta_rshift:
.section	.pdata
.p2align	2
.rva	.LSEH_begin_pasta_add
.rva	.LSEH_body_pasta_add
.rva	.LSEH_info_pasta_add_prologue

.rva	.LSEH_body_pasta_add
.rva	.LSEH_epilogue_pasta_add
.rva	.LSEH_info_pasta_add_body

.rva	.LSEH_epilogue_pasta_add
.rva	.LSEH_end_pasta_add
.rva	.LSEH_info_pasta_add_epilogue

.rva	.LSEH_begin_pasta_cneg
.rva	.LSEH_body_pasta_cneg
.rva	.LSEH_info_pasta_cneg_prologue

.rva	.LSEH_body_pasta_cneg
.rva	.LSEH_epilogue_pasta_cneg
.rva	.LSEH_info_pasta_cneg_body

.rva	.LSEH_epilogue_pasta_cneg
.rva	.LSEH_end_pasta_cneg
.rva	.LSEH_info_pasta_cneg_epilogue

.rva	.LSEH_begin_pasta_sub
.rva	.LSEH_body_pasta_sub
.rva	.LSEH_info_pasta_sub_prologue

.rva	.LSEH_body_pasta_sub
.rva	.LSEH_epilogue_pasta_sub
.rva	.LSEH_info_pasta_sub_body

.rva	.LSEH_epilogue_pasta_sub
.rva	.LSEH_end_pasta_sub
.rva	.LSEH_info_pasta_sub_epilogue

.rva	.LSEH_begin_pasta_lshift
.rva	.LSEH_body_pasta_lshift
.rva	.LSEH_info_pasta_lshift_prologue

.rva	.LSEH_body_pasta_lshift
.rva	.LSEH_epilogue_pasta_lshift
.rva	.LSEH_info_pasta_lshift_body

.rva	.LSEH_epilogue_pasta_lshift
.rva	.LSEH_end_pasta_lshift
.rva	.LSEH_info_pasta_lshift_epilogue

.rva	.LSEH_begin_pasta_rshift
.rva	.LSEH_body_pasta_rshift
.rva	.LSEH_info_pasta_rshift_prologue

.rva	.LSEH_body_pasta_rshift
.rva	.LSEH_epilogue_pasta_rshift
.rva	.LSEH_info_pasta_rshift_body

.rva	.LSEH_epilogue_pasta_rshift
.rva	.LSEH_end_pasta_rshift
.rva	.LSEH_info_pasta_rshift_epilogue

.section	.xdata
.p2align	3
.LSEH_info_pasta_add_prologue:
.byte	1,0,5,0x0b
.byte	0,0x74,1,0
.byte	0,0x64,2,0
.byte	0,0x03
.byte	0,0
.LSEH_info_pasta_add_body:
.byte	1,0,9,0
.byte	0x00,0x34,0x01,0x00
.byte	0x00,0x54,0x02,0x00
.byte	0x00,0x74,0x04,0x00
.byte	0x00,0x64,0x05,0x00
.byte	0x00,0x22
.byte	0x00,0x00
.LSEH_info_pasta_add_epilogue:
.byte	1,0,4,0
.byte	0x00,0x74,0x01,0x00
.byte	0x00,0x64,0x02,0x00
.byte	0x00,0x00,0x00,0x00

.LSEH_info_pasta_cneg_prologue:
.byte	1,0,5,0x0b
.byte	0,0x74,1,0
.byte	0,0x64,2,0
.byte	0,0x03
.byte	0,0
.LSEH_info_pasta_cneg_body:
.byte	1,0,11,0
.byte	0x00,0xc4,0x00,0x00
.byte	0x00,0x34,0x01,0x00
.byte	0x00,0x54,0x02,0x00
.byte	0x00,0x74,0x04,0x00
.byte	0x00,0x64,0x05,0x00
.byte	0x00,0x22
.byte	0x00,0x00,0x00,0x00,0x00,0x00
.LSEH_info_pasta_cneg_epilogue:
.byte	1,0,4,0
.byte	0x00,0x74,0x01,0x00
.byte	0x00,0x64,0x02,0x00
.byte	0x00,0x00,0x00,0x00

.LSEH_info_pasta_sub_prologue:
.byte	1,0,5,0x0b
.byte	0,0x74,1,0
.byte	0,0x64,2,0
.byte	0,0x03
.byte	0,0
.LSEH_info_pasta_sub_body:
.byte	1,0,9,0
.byte	0x00,0x34,0x01,0x00
.byte	0x00,0x54,0x02,0x00
.byte	0x00,0x74,0x04,0x00
.byte	0x00,0x64,0x05,0x00
.byte	0x00,0x22
.byte	0x00,0x00
.LSEH_info_pasta_sub_epilogue:
.byte	1,0,4,0
.byte	0x00,0x74,0x01,0x00
.byte	0x00,0x64,0x02,0x00
.byte	0x00,0x00,0x00,0x00

.LSEH_info_pasta_lshift_prologue:
.byte	1,0,5,0x0b
.byte	0,0x74,1,0
.byte	0,0x64,2,0
.byte	0,0x03
.byte	0,0
.LSEH_info_pasta_lshift_body:
.byte	1,0,11,0
.byte	0x00,0xc4,0x00,0x00
.byte	0x00,0x34,0x01,0x00
.byte	0x00,0x54,0x02,0x00
.byte	0x00,0x74,0x04,0x00
.byte	0x00,0x64,0x05,0x00
.byte	0x00,0x22
.byte	0x00,0x00,0x00,0x00,0x00,0x00
.LSEH_info_pasta_lshift_epilogue:
.byte	1,0,4,0
.byte	0x00,0x74,0x01,0x00
.byte	0x00,0x64,0x02,0x00
.byte	0x00,0x00,0x00,0x00

.LSEH_info_pasta_rshift_prologue:
.byte	1,0,5,0x0b
.byte	0,0x74,1,0
.byte	0,0x64,2,0
.byte	0,0x03
.byte	0,0
.LSEH_info_pasta_rshift_body:
.byte	1,0,9,0
.byte	0x00,0x34,0x01,0x00
.byte	0x00,0x54,0x02,0x00
.byte	0x00,0x74,0x04,0x00
.byte	0x00,0x64,0x05,0x00
.byte	0x00,0x22
.byte	0x00,0x00
.LSEH_info_pasta_rshift_epilogue:
.byte	1,0,4,0
.byte	0x00,0x74,0x01,0x00
.byte	0x00,0x64,0x02,0x00
.byte	0x00,0x00,0x00,0x00
