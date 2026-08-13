; Copyright Supranational LLC
; Licensed under the Apache License, Version 2.0.
; SPDX-License-Identifier: Apache-2.0
; Modified by Zakura; generated from the attributed source.

OPTION	DOTNAME
.text$	SEGMENT ALIGN(256) 'CODE'

PUBLIC	mul_mont_pasta


ALIGN	32
mul_mont_pasta	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_mul_mont_pasta::
	mov	rdi,rcx
	mov	rsi,rdx
	mov	rdx,r8
	mov	rcx,r9
	mov	r8,QWORD PTR[40+rsp]



	push	rbp

	push	rbx

	push	r12

	push	r13

	push	r14

	push	r15

	push	rdi

$L$SEH_body_mul_mont_pasta::


	mov	rax,QWORD PTR[rdx]
	mov	r13,QWORD PTR[rsi]
	mov	r14,QWORD PTR[8+rsi]
	mov	r12,QWORD PTR[16+rsi]
	mov	rbp,QWORD PTR[24+rsi]
	mov	rbx,rdx

	mov	r15,rax
	mul	r13
	mov	r9,rax
	mov	rax,r15
	mov	r10,rdx
	call	__mulq_mont_pasta

	mov	r15,QWORD PTR[8+rsp]

	mov	r14,QWORD PTR[16+rsp]

	mov	r13,QWORD PTR[24+rsp]

	mov	r12,QWORD PTR[32+rsp]

	mov	rbx,QWORD PTR[40+rsp]

	mov	rbp,QWORD PTR[48+rsp]

	lea	rsp,QWORD PTR[56+rsp]

$L$SEH_epilogue_mul_mont_pasta::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_mul_mont_pasta::
mul_mont_pasta	ENDP

PUBLIC	sqr_mont_pasta


ALIGN	32
sqr_mont_pasta	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_sqr_mont_pasta::
	mov	rdi,rcx
	mov	rsi,rdx
	mov	rdx,r8
	mov	rcx,r9



	push	rbp

	push	rbx

	push	r12

	push	r13

	push	r14

	push	r15

	push	rdi

$L$SEH_body_sqr_mont_pasta::


	mov	rax,QWORD PTR[rsi]
	mov	r8,rcx
	mov	r14,QWORD PTR[8+rsi]
	mov	rcx,rdx
	mov	r12,QWORD PTR[16+rsi]
	lea	rbx,QWORD PTR[rsi]
	mov	rbp,QWORD PTR[24+rsi]

	mov	r15,rax
	mul	rax
	mov	r9,rax
	mov	rax,r15
	mov	r10,rdx
	call	__mulq_mont_pasta

	mov	r15,QWORD PTR[8+rsp]

	mov	r14,QWORD PTR[16+rsp]

	mov	r13,QWORD PTR[24+rsp]

	mov	r12,QWORD PTR[32+rsp]

	mov	rbx,QWORD PTR[40+rsp]

	mov	rbp,QWORD PTR[48+rsp]

	lea	rsp,QWORD PTR[56+rsp]

$L$SEH_epilogue_sqr_mont_pasta::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_sqr_mont_pasta::
sqr_mont_pasta	ENDP

ALIGN	32
__mulq_mont_pasta	PROC PRIVATE
	DB	243,15,30,250
	mul	r14
	add	r10,rax
	mov	rax,r15
	adc	rdx,0
	mov	r11,rdx

	mul	r12
	add	r11,rax
	mov	rax,r15
	adc	rdx,0
	mov	r12,rdx

	mul	rbp
	add	r12,rax
	mov	rax,QWORD PTR[8+rbx]
	adc	rdx,0
	xor	r14,r14
	mov	r13,rdx

	mov	rdi,r9
	imul	r9,r8


	mov	r15,rax
	mul	QWORD PTR[rsi]
	add	r10,rax
	mov	rax,r15
	adc	rdx,0
	mov	rbp,rdx

	mul	QWORD PTR[8+rsi]
	add	r11,rax
	mov	rax,r15
	adc	rdx,0
	add	r11,rbp
	adc	rdx,0
	mov	rbp,rdx

	mul	QWORD PTR[16+rsi]
	add	r12,rax
	mov	rax,r15
	adc	rdx,0
	add	r12,rbp
	adc	rdx,0
	mov	rbp,rdx

	mul	QWORD PTR[24+rsi]
	add	r13,rax
	mov	rax,r9
	adc	rdx,0
	add	r13,rbp
	adc	rdx,0
	mov	r14,rdx


	mul	QWORD PTR[rcx]
	add	rdi,rax
	mov	rax,r9
	adc	rdi,rdx

	mul	QWORD PTR[8+rcx]
	add	r10,rax
	mov	rax,r9
	adc	rdx,0

	xor	rbp,rbp
	add	r10,rdi
	adc	r11,rdx
	adc	rbp,0

	mul	QWORD PTR[24+rcx]
	add	r12,rax
	mov	rax,QWORD PTR[16+rbx]
	adc	rdx,0
	add	r12,rbp
	adc	rdx,0
	add	r13,rdx
	adc	r14,0
	mov	rdi,r10
	imul	r10,r8


	mov	r9,rax
	mul	QWORD PTR[rsi]
	add	r11,rax
	mov	rax,r9
	adc	rdx,0
	mov	rbp,rdx

	mul	QWORD PTR[8+rsi]
	add	r12,rax
	mov	rax,r9
	adc	rdx,0
	add	r12,rbp
	adc	rdx,0
	mov	rbp,rdx

	mul	QWORD PTR[16+rsi]
	add	r13,rax
	mov	rax,r9
	adc	rdx,0
	add	r13,rbp
	adc	rdx,0
	mov	rbp,rdx

	mul	QWORD PTR[24+rsi]
	add	r14,rax
	mov	rax,r10
	adc	rdx,0
	add	r14,rbp
	adc	rdx,0
	mov	r15,rdx


	mul	QWORD PTR[rcx]
	add	rdi,rax
	mov	rax,r10
	adc	rdi,rdx

	mul	QWORD PTR[8+rcx]
	add	r11,rax
	mov	rax,r10
	adc	rdx,0

	xor	rbp,rbp
	add	r11,rdi
	adc	r12,rdx
	adc	rbp,0

	mul	QWORD PTR[24+rcx]
	add	r13,rax
	mov	rax,QWORD PTR[24+rbx]
	adc	rdx,0
	add	r13,rbp
	adc	rdx,0
	add	r14,rdx
	adc	r15,0
	mov	rdi,r11
	imul	r11,r8


	mov	r10,rax
	mul	QWORD PTR[rsi]
	add	r12,rax
	mov	rax,r10
	adc	rdx,0
	mov	rbp,rdx

	mul	QWORD PTR[8+rsi]
	add	r13,rax
	mov	rax,r10
	adc	rdx,0
	add	r13,rbp
	adc	rdx,0
	mov	rbp,rdx

	mul	QWORD PTR[16+rsi]
	add	r14,rax
	mov	rax,r10
	adc	rdx,0
	add	r14,rbp
	adc	rdx,0
	mov	rbp,rdx

	mul	QWORD PTR[24+rsi]
	add	r15,rax
	mov	rax,r11
	adc	rdx,0
	add	r15,rbp
	adc	rdx,0
	mov	r9,rdx


	mul	QWORD PTR[rcx]
	add	rdi,rax
	mov	rax,r11
	adc	rdi,rdx

	mul	QWORD PTR[8+rcx]
	add	r12,rax
	mov	rax,r11
	adc	rdx,0

	xor	rbp,rbp
	add	r12,rdi
	adc	r13,rdx
	adc	rbp,0

	mul	QWORD PTR[24+rcx]
	add	r14,rax
	mov	rax,r12
	adc	rdx,0
	add	r14,rbp
	adc	rdx,0
	add	r15,rdx
	adc	r9,0
	imul	rax,r8
	mov	rsi,QWORD PTR[8+rsp]
	xor	r10,r10


	mov	r11,rax
	mul	QWORD PTR[rcx]
	add	r12,rax
	mov	rax,r11
	adc	r12,rdx

	mul	QWORD PTR[8+rcx]
	add	r13,rax
	mov	rax,r11
	adc	rdx,0

	xor	rbp,rbp
	add	r13,r12
	adc	r14,rdx
	adc	rbp,0

	mul	QWORD PTR[24+rcx]
	mov	rbx,r14
	add	r15,rbp
	adc	rdx,0
	add	r15,rax
	mov	rax,r13
	adc	rdx,0
	add	r9,rdx
	adc	r10,0




	mov	r12,r15
	sub	r13,QWORD PTR[rcx]
	sbb	r14,QWORD PTR[8+rcx]
	sbb	r15,QWORD PTR[16+rcx]
	mov	rbp,r9
	sbb	r9,QWORD PTR[24+rcx]
	sbb	r10,0

	cmovc	r13,rax
	cmovc	r14,rbx
	cmovc	r15,r12
	mov	QWORD PTR[rsi],r13
	cmovc	r9,rbp
	mov	QWORD PTR[8+rsi],r14
	mov	QWORD PTR[16+rsi],r15
	mov	QWORD PTR[24+rsi],r9

	DB	0F3h,0C3h		;repret

__mulq_mont_pasta	ENDP
PUBLIC	from_mont_pasta


ALIGN	32
from_mont_pasta	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_from_mont_pasta::
	mov	rdi,rcx
	mov	rsi,rdx
	mov	rdx,r8
	mov	rcx,r9



	push	rbp

	push	rbx

	push	r12

	push	r13

	push	r14

	push	r15

	sub	rsp,8

$L$SEH_body_from_mont_pasta::


	mov	rbx,rdx
	call	__mulq_by_1_mont_pasta





	mov	r10,r14
	mov	r11,r15
	mov	r12,r9

	sub	r13,QWORD PTR[rbx]
	sbb	r14,QWORD PTR[8+rbx]
	sbb	r15,QWORD PTR[16+rbx]
	sbb	r9,QWORD PTR[24+rbx]

	cmovnc	rax,r13
	cmovnc	r10,r14
	cmovnc	r11,r15
	mov	QWORD PTR[rdi],rax
	cmovnc	r12,r9
	mov	QWORD PTR[8+rdi],r10
	mov	QWORD PTR[16+rdi],r11
	mov	QWORD PTR[24+rdi],r12

	mov	r15,QWORD PTR[8+rsp]

	mov	r14,QWORD PTR[16+rsp]

	mov	r13,QWORD PTR[24+rsp]

	mov	r12,QWORD PTR[32+rsp]

	mov	rbx,QWORD PTR[40+rsp]

	mov	rbp,QWORD PTR[48+rsp]

	lea	rsp,QWORD PTR[56+rsp]

$L$SEH_epilogue_from_mont_pasta::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_from_mont_pasta::
from_mont_pasta	ENDP

PUBLIC	redc_mont_pasta


ALIGN	32
redc_mont_pasta	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_redc_mont_pasta::
	mov	rdi,rcx
	mov	rsi,rdx
	mov	rdx,r8
	mov	rcx,r9



	push	rbp

	push	rbx

	push	r12

	push	r13

	push	r14

	push	r15

	sub	rsp,8

$L$SEH_body_redc_mont_pasta::


	mov	rbx,rdx
	call	__mulq_by_1_mont_pasta

	add	r13,QWORD PTR[32+rsi]
	adc	r14,QWORD PTR[40+rsi]
	mov	rax,r13
	adc	r15,QWORD PTR[48+rsi]
	mov	r10,r14
	adc	r9,QWORD PTR[56+rsi]
	sbb	rsi,rsi




	mov	r11,r15
	sub	r13,QWORD PTR[rbx]
	sbb	r14,QWORD PTR[8+rbx]
	sbb	r15,QWORD PTR[16+rbx]
	mov	r12,r9
	sbb	r9,QWORD PTR[24+rbx]
	sbb	rsi,0

	cmovnc	rax,r13
	cmovnc	r10,r14
	cmovnc	r11,r15
	mov	QWORD PTR[rdi],rax
	cmovnc	r12,r9
	mov	QWORD PTR[8+rdi],r10
	mov	QWORD PTR[16+rdi],r11
	mov	QWORD PTR[24+rdi],r12

	mov	r15,QWORD PTR[8+rsp]

	mov	r14,QWORD PTR[16+rsp]

	mov	r13,QWORD PTR[24+rsp]

	mov	r12,QWORD PTR[32+rsp]

	mov	rbx,QWORD PTR[40+rsp]

	mov	rbp,QWORD PTR[48+rsp]

	lea	rsp,QWORD PTR[56+rsp]

$L$SEH_epilogue_redc_mont_pasta::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_redc_mont_pasta::
redc_mont_pasta	ENDP

ALIGN	32
__mulq_by_1_mont_pasta	PROC PRIVATE
	DB	243,15,30,250
	mov	rax,QWORD PTR[rsi]
	mov	r10,QWORD PTR[8+rsi]
	mov	r11,QWORD PTR[16+rsi]
	mov	r12,QWORD PTR[24+rsi]

	mov	r13,rax
	imul	rax,rcx
	mov	r9,rax

	mul	QWORD PTR[rbx]
	add	r13,rax
	mov	rax,r9
	adc	r13,rdx

	mul	QWORD PTR[8+rbx]
	add	r10,rax
	mov	rax,r9
	adc	rdx,0

	xor	rbp,rbp
	add	r10,r13
	adc	r11,rdx
	adc	rbp,0

	mov	r14,r10
	imul	r10,rcx

	mul	QWORD PTR[24+rbx]
	add	r12,rax
	mov	rax,r10
	adc	rdx,0
	add	r12,rbp
	adc	rdx,0
	mov	r13,rdx

	mul	QWORD PTR[rbx]
	add	r14,rax
	mov	rax,r10
	adc	r14,rdx

	mul	QWORD PTR[8+rbx]
	add	r11,rax
	mov	rax,r10
	adc	rdx,0

	xor	rbp,rbp
	add	r11,r14
	adc	r12,rdx
	adc	rbp,0

	mov	r15,r11
	imul	r11,rcx

	mul	QWORD PTR[24+rbx]
	add	r13,rax
	mov	rax,r11
	adc	rdx,0
	add	r13,rbp
	adc	rdx,0
	mov	r14,rdx

	mul	QWORD PTR[rbx]
	add	r15,rax
	mov	rax,r11
	adc	r15,rdx

	mul	QWORD PTR[8+rbx]
	add	r12,rax
	mov	rax,r11
	adc	rdx,0

	xor	rbp,rbp
	add	r12,r15
	adc	r13,rdx
	adc	rbp,0

	mov	r9,r12
	imul	r12,rcx

	mul	QWORD PTR[24+rbx]
	add	r14,rax
	mov	rax,r12
	adc	rdx,0
	add	r14,rbp
	adc	rdx,0
	mov	r15,rdx

	mul	QWORD PTR[rbx]
	add	r9,rax
	mov	rax,r12
	adc	r9,rdx

	mul	QWORD PTR[8+rbx]
	add	r13,rax
	mov	rax,r12
	adc	rdx,0

	xor	rbp,rbp
	add	r13,r9
	adc	r14,rdx
	adc	rbp,0


	mul	QWORD PTR[24+rbx]
	add	r15,rax
	mov	rax,r13
	adc	rdx,0
	add	r15,rbp
	adc	rdx,0
	mov	r9,rdx
	DB	0F3h,0C3h		;repret
__mulq_by_1_mont_pasta	ENDP
PUBLIC	sqr_n_mul_mont_pasta


ALIGN	32
sqr_n_mul_mont_pasta	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_sqr_n_mul_mont_pasta::
	mov	rdi,rcx
	mov	rsi,rdx
	mov	rdx,r8
	mov	rcx,r9
	mov	r8,QWORD PTR[40+rsp]
	mov	r9,QWORD PTR[48+rsp]



	push	rbp

	push	rbx

	push	r12

	push	r13

	push	r14

	push	r15

	sub	rsp,40

$L$SEH_body_sqr_n_mul_mont_pasta::

	mov	QWORD PTR[16+rsp],rcx
	mov	QWORD PTR[24+rsp],rdi

	mov	rax,QWORD PTR[rsi]
	mov	rbp,QWORD PTR[8+rsi]
	mov	rdi,QWORD PTR[16+rsi]
	mov	rsi,QWORD PTR[24+rsi]
	mov	rbx,rdx
	mov	QWORD PTR[rsp],r9
	mov	rcx,rax
	jmp	$L$oop_sqrq_pasta

ALIGN	32
$L$oop_sqrq_pasta::
	mov	QWORD PTR[8+rsp],rbx

	mul	rax
	mov	r9,rax
	mov	rax,rcx
	mov	r10,rdx

	mul	rbp
	add	r10,rax
	mov	rax,rcx
	adc	rdx,0
	mov	r11,rdx

	mul	rdi
	add	r11,rax
	mov	rax,rcx
	adc	rdx,0
	mov	r12,rdx

	mul	rsi
	add	r12,rax
	mov	rax,rbp
	adc	rdx,0
	mov	r13,rdx
	mov	r15,r9
	imul	r9,QWORD PTR[rsp]


	mul	rcx
	add	r10,rax
	mov	rax,rbp
	adc	rdx,0
	mov	rbx,rdx

	mul	rbp
	add	r11,rax
	mov	rax,rbp
	adc	rdx,0
	add	r11,rbx
	adc	rdx,0
	mov	rbx,rdx

	mul	rdi
	add	r12,rax
	mov	rax,rbp
	adc	rdx,0
	add	r12,rbx
	adc	rdx,0
	mov	rbx,rdx

	mul	rsi
	add	r13,rax
	mov	rax,r9
	adc	rdx,0
	add	r13,rbx
	adc	rdx,0
	mov	r14,rdx


	mul	QWORD PTR[r8]
	add	r15,rax
	mov	rax,r9
	adc	r15,rdx

	mul	QWORD PTR[8+r8]
	add	r10,rax
	mov	rax,r9
	adc	rdx,0

	xor	rbx,rbx
	add	r10,r15
	adc	r11,rdx
	adc	rbx,0

	mul	QWORD PTR[24+r8]
	add	r12,rax
	mov	rax,rdi
	adc	rdx,0
	add	r12,rbx
	adc	r13,rdx
	adc	r14,0
	mov	r9,r10
	imul	r10,QWORD PTR[rsp]


	mul	rcx
	add	r11,rax
	mov	rax,rdi
	adc	rdx,0
	mov	rbx,rdx

	mul	rbp
	add	r12,rax
	mov	rax,rdi
	adc	rdx,0
	add	r12,rbx
	adc	rdx,0
	mov	rbx,rdx

	mul	rdi
	add	r13,rax
	mov	rax,rdi
	adc	rdx,0
	add	r13,rbx
	adc	rdx,0
	mov	rbx,rdx

	mul	rsi
	add	r14,rax
	mov	rax,r10
	adc	rdx,0
	add	r14,rbx
	adc	rdx,0
	mov	r15,rdx


	mul	QWORD PTR[r8]
	add	r9,rax
	mov	rax,r10
	adc	r9,rdx

	mul	QWORD PTR[8+r8]
	add	r11,rax
	mov	rax,r10
	adc	rdx,0

	xor	rbx,rbx
	add	r11,r9
	adc	r12,rdx
	adc	rbx,0

	mul	QWORD PTR[24+r8]
	add	r13,rax
	mov	rax,rsi
	adc	rdx,0
	add	r13,rbx
	adc	r14,rdx
	adc	r15,0
	mov	r10,r11
	imul	r11,QWORD PTR[rsp]


	mul	rcx
	add	r12,rax
	mov	rax,rsi
	adc	rdx,0
	mov	rbx,rdx

	mul	rbp
	add	r13,rax
	mov	rax,rsi
	adc	rdx,0
	add	r13,rbx
	adc	rdx,0
	mov	rbx,rdx

	mul	rdi
	add	r14,rax
	mov	rax,rsi
	adc	rdx,0
	add	r14,rbx
	adc	rdx,0
	mov	rbx,rdx

	mul	rsi
	add	r15,rax
	mov	rax,r11
	adc	rdx,0
	add	r15,rbx
	adc	rdx,0
	mov	r9,rdx


	mul	QWORD PTR[r8]
	add	r10,rax
	mov	rax,r11
	adc	r10,rdx

	mul	QWORD PTR[8+r8]
	add	r12,rax
	mov	rax,r11
	adc	rdx,0

	xor	rbx,rbx
	add	r12,r10
	adc	r13,rdx
	adc	rbx,0

	mul	QWORD PTR[24+r8]
	add	r14,rax
	mov	rax,r12
	adc	rdx,0
	add	r14,rbx
	adc	r15,rdx
	adc	r9,0
	imul	rax,QWORD PTR[rsp]
	mov	rcx,r13
	mov	rbp,r14
	mov	rbx,QWORD PTR[8+rsp]
	mov	rsi,r9
	mov	r11,QWORD PTR[16+rsp]


	mov	r10,rax
	mul	QWORD PTR[r8]
	add	r12,rax
	mov	rax,r10
	adc	r12,rdx

	mul	QWORD PTR[8+r8]
	add	rcx,rax
	mov	rax,r10
	adc	rdx,0

	xor	rdi,rdi
	add	rcx,r12
	adc	rbp,rdx
	adc	rdi,0

	mul	QWORD PTR[24+r8]
	add	rdi,rax
	mov	rax,rcx
	adc	rdx,0
	add	rdi,r15
	adc	rsi,rdx

	sub	rbx,1
	jnz	$L$oop_sqrq_pasta
	mul	QWORD PTR[r11]
	mov	r12,rax
	mov	rax,rcx
	mov	r13,rdx

	mul	QWORD PTR[8+r11]
	add	r13,rax
	mov	rax,rcx
	adc	rdx,0
	mov	r14,rdx

	mul	QWORD PTR[16+r11]
	add	r14,rax
	mov	rax,rcx
	adc	rdx,0
	mov	r15,rdx

	mul	QWORD PTR[24+r11]
	add	r15,rax
	mov	rax,rbp
	adc	rdx,0
	mov	r9,rdx
	mov	rcx,r12
	imul	r12,QWORD PTR[rsp]


	mul	QWORD PTR[r11]
	add	r13,rax
	mov	rax,rbp
	adc	rdx,0
	mov	rbx,rdx

	mul	QWORD PTR[8+r11]
	add	r14,rax
	mov	rax,rbp
	adc	rdx,0
	add	r14,rbx
	adc	rdx,0
	mov	rbx,rdx

	mul	QWORD PTR[16+r11]
	add	r15,rax
	mov	rax,rbp
	adc	rdx,0
	add	r15,rbx
	adc	rdx,0
	mov	rbx,rdx

	mul	QWORD PTR[24+r11]
	add	r9,rax
	mov	rax,r12
	adc	rdx,0
	add	r9,rbx
	adc	rdx,0
	mov	r10,rdx


	mul	QWORD PTR[r8]
	add	rcx,rax
	mov	rax,r12
	adc	rcx,rdx

	mul	QWORD PTR[8+r8]
	add	r13,rax
	mov	rax,r12
	adc	rdx,0

	xor	rbx,rbx
	add	r13,rcx
	adc	r14,rdx
	adc	rbx,0

	mul	QWORD PTR[24+r8]
	add	r15,rax
	mov	rax,rdi
	adc	rdx,0
	add	r15,rbx
	adc	r9,rdx
	adc	r10,0
	mov	r12,r13
	imul	r13,QWORD PTR[rsp]


	mul	QWORD PTR[r11]
	add	r14,rax
	mov	rax,rdi
	adc	rdx,0
	mov	rbx,rdx

	mul	QWORD PTR[8+r11]
	add	r15,rax
	mov	rax,rdi
	adc	rdx,0
	add	r15,rbx
	adc	rdx,0
	mov	rbx,rdx

	mul	QWORD PTR[16+r11]
	add	r9,rax
	mov	rax,rdi
	adc	rdx,0
	add	r9,rbx
	adc	rdx,0
	mov	rbx,rdx

	mul	QWORD PTR[24+r11]
	add	r10,rax
	mov	rax,r13
	adc	rdx,0
	add	r10,rbx
	adc	rdx,0
	mov	rcx,rdx


	mul	QWORD PTR[r8]
	add	r12,rax
	mov	rax,r13
	adc	r12,rdx

	mul	QWORD PTR[8+r8]
	add	r14,rax
	mov	rax,r13
	adc	rdx,0

	xor	rbx,rbx
	add	r14,r12
	adc	r15,rdx
	adc	rbx,0

	mul	QWORD PTR[24+r8]
	add	r9,rax
	mov	rax,rsi
	adc	rdx,0
	add	r9,rbx
	adc	r10,rdx
	adc	rcx,0
	mov	r13,r14
	imul	r14,QWORD PTR[rsp]


	mul	QWORD PTR[r11]
	add	r15,rax
	mov	rax,rsi
	adc	rdx,0
	mov	rbx,rdx

	mul	QWORD PTR[8+r11]
	add	r9,rax
	mov	rax,rsi
	adc	rdx,0
	add	r9,rbx
	adc	rdx,0
	mov	rbx,rdx

	mul	QWORD PTR[16+r11]
	add	r10,rax
	mov	rax,rsi
	adc	rdx,0
	add	r10,rbx
	adc	rdx,0
	mov	rbx,rdx

	mul	QWORD PTR[24+r11]
	add	rcx,rax
	mov	rax,r14
	adc	rdx,0
	add	rcx,rbx
	adc	rdx,0
	mov	r12,rdx


	mul	QWORD PTR[r8]
	add	r13,rax
	mov	rax,r14
	adc	r13,rdx

	mul	QWORD PTR[8+r8]
	add	r15,rax
	mov	rax,r14
	adc	rdx,0

	xor	rbx,rbx
	add	r15,r13
	adc	r9,rdx
	adc	rbx,0

	mul	QWORD PTR[24+r8]
	add	r10,rax
	mov	rax,r15
	adc	rdx,0
	add	r10,rbx
	adc	rcx,rdx
	adc	r12,0
	imul	rax,QWORD PTR[rsp]
	mov	rdi,QWORD PTR[24+rsp]


	mov	r14,rax
	mul	QWORD PTR[r8]
	add	r15,rax
	mov	rax,r14
	adc	r15,rdx

	mul	QWORD PTR[8+r8]
	add	r9,rax
	mov	rax,r14
	adc	rdx,0

	xor	rbx,rbx
	add	r9,r15
	adc	r10,rdx
	adc	rbx,0

	mul	QWORD PTR[24+r8]
	mov	r13,r9
	add	rcx,rbx
	adc	rdx,0
	mov	r14,r10
	add	rcx,rax
	adc	r12,rdx




	mov	r15,rcx
	sub	r9,QWORD PTR[r8]
	sbb	r10,QWORD PTR[8+r8]
	sbb	rcx,QWORD PTR[16+r8]
	mov	rbx,r12
	sbb	r12,QWORD PTR[24+r8]

	cmovc	r9,r13
	cmovc	r10,r14
	cmovc	rcx,r15
	mov	QWORD PTR[rdi],r9
	cmovc	r12,rbx
	mov	QWORD PTR[8+rdi],r10
	mov	QWORD PTR[16+rdi],rcx
	mov	QWORD PTR[24+rdi],r12

	mov	r15,QWORD PTR[40+rsp]

	mov	r14,QWORD PTR[48+rsp]

	mov	r13,QWORD PTR[56+rsp]

	mov	r12,QWORD PTR[64+rsp]

	mov	rbx,QWORD PTR[72+rsp]

	mov	rbp,QWORD PTR[80+rsp]

	lea	rsp,QWORD PTR[88+rsp]

$L$SEH_epilogue_sqr_n_mul_mont_pasta::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_sqr_n_mul_mont_pasta::
sqr_n_mul_mont_pasta	ENDP
.text$	ENDS
.pdata	SEGMENT READONLY ALIGN(4)
ALIGN	4
	DD	imagerel $L$SEH_begin_mul_mont_pasta
	DD	imagerel $L$SEH_body_mul_mont_pasta
	DD	imagerel $L$SEH_info_mul_mont_pasta_prologue

	DD	imagerel $L$SEH_body_mul_mont_pasta
	DD	imagerel $L$SEH_epilogue_mul_mont_pasta
	DD	imagerel $L$SEH_info_mul_mont_pasta_body

	DD	imagerel $L$SEH_epilogue_mul_mont_pasta
	DD	imagerel $L$SEH_end_mul_mont_pasta
	DD	imagerel $L$SEH_info_mul_mont_pasta_epilogue

	DD	imagerel $L$SEH_begin_sqr_mont_pasta
	DD	imagerel $L$SEH_body_sqr_mont_pasta
	DD	imagerel $L$SEH_info_sqr_mont_pasta_prologue

	DD	imagerel $L$SEH_body_sqr_mont_pasta
	DD	imagerel $L$SEH_epilogue_sqr_mont_pasta
	DD	imagerel $L$SEH_info_sqr_mont_pasta_body

	DD	imagerel $L$SEH_epilogue_sqr_mont_pasta
	DD	imagerel $L$SEH_end_sqr_mont_pasta
	DD	imagerel $L$SEH_info_sqr_mont_pasta_epilogue

	DD	imagerel $L$SEH_begin_from_mont_pasta
	DD	imagerel $L$SEH_body_from_mont_pasta
	DD	imagerel $L$SEH_info_from_mont_pasta_prologue

	DD	imagerel $L$SEH_body_from_mont_pasta
	DD	imagerel $L$SEH_epilogue_from_mont_pasta
	DD	imagerel $L$SEH_info_from_mont_pasta_body

	DD	imagerel $L$SEH_epilogue_from_mont_pasta
	DD	imagerel $L$SEH_end_from_mont_pasta
	DD	imagerel $L$SEH_info_from_mont_pasta_epilogue

	DD	imagerel $L$SEH_begin_redc_mont_pasta
	DD	imagerel $L$SEH_body_redc_mont_pasta
	DD	imagerel $L$SEH_info_redc_mont_pasta_prologue

	DD	imagerel $L$SEH_body_redc_mont_pasta
	DD	imagerel $L$SEH_epilogue_redc_mont_pasta
	DD	imagerel $L$SEH_info_redc_mont_pasta_body

	DD	imagerel $L$SEH_epilogue_redc_mont_pasta
	DD	imagerel $L$SEH_end_redc_mont_pasta
	DD	imagerel $L$SEH_info_redc_mont_pasta_epilogue

	DD	imagerel $L$SEH_begin_sqr_n_mul_mont_pasta
	DD	imagerel $L$SEH_body_sqr_n_mul_mont_pasta
	DD	imagerel $L$SEH_info_sqr_n_mul_mont_pasta_prologue

	DD	imagerel $L$SEH_body_sqr_n_mul_mont_pasta
	DD	imagerel $L$SEH_epilogue_sqr_n_mul_mont_pasta
	DD	imagerel $L$SEH_info_sqr_n_mul_mont_pasta_body

	DD	imagerel $L$SEH_epilogue_sqr_n_mul_mont_pasta
	DD	imagerel $L$SEH_end_sqr_n_mul_mont_pasta
	DD	imagerel $L$SEH_info_sqr_n_mul_mont_pasta_epilogue

.pdata	ENDS
.xdata	SEGMENT READONLY ALIGN(8)
ALIGN	8
$L$SEH_info_mul_mont_pasta_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_mul_mont_pasta_body::
DB	1,0,17,0
DB	000h,0f4h,001h,000h
DB	000h,0e4h,002h,000h
DB	000h,0d4h,003h,000h
DB	000h,0c4h,004h,000h
DB	000h,034h,005h,000h
DB	000h,054h,006h,000h
DB	000h,074h,008h,000h
DB	000h,064h,009h,000h
DB	000h,062h
DB	000h,000h
$L$SEH_info_mul_mont_pasta_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h

$L$SEH_info_sqr_mont_pasta_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_sqr_mont_pasta_body::
DB	1,0,17,0
DB	000h,0f4h,001h,000h
DB	000h,0e4h,002h,000h
DB	000h,0d4h,003h,000h
DB	000h,0c4h,004h,000h
DB	000h,034h,005h,000h
DB	000h,054h,006h,000h
DB	000h,074h,008h,000h
DB	000h,064h,009h,000h
DB	000h,062h
DB	000h,000h
$L$SEH_info_sqr_mont_pasta_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h

$L$SEH_info_from_mont_pasta_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_from_mont_pasta_body::
DB	1,0,17,0
DB	000h,0f4h,001h,000h
DB	000h,0e4h,002h,000h
DB	000h,0d4h,003h,000h
DB	000h,0c4h,004h,000h
DB	000h,034h,005h,000h
DB	000h,054h,006h,000h
DB	000h,074h,008h,000h
DB	000h,064h,009h,000h
DB	000h,062h
DB	000h,000h
$L$SEH_info_from_mont_pasta_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h

$L$SEH_info_redc_mont_pasta_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_redc_mont_pasta_body::
DB	1,0,17,0
DB	000h,0f4h,001h,000h
DB	000h,0e4h,002h,000h
DB	000h,0d4h,003h,000h
DB	000h,0c4h,004h,000h
DB	000h,034h,005h,000h
DB	000h,054h,006h,000h
DB	000h,074h,008h,000h
DB	000h,064h,009h,000h
DB	000h,062h
DB	000h,000h
$L$SEH_info_redc_mont_pasta_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h

$L$SEH_info_sqr_n_mul_mont_pasta_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_sqr_n_mul_mont_pasta_body::
DB	1,0,17,0
DB	000h,0f4h,005h,000h
DB	000h,0e4h,006h,000h
DB	000h,0d4h,007h,000h
DB	000h,0c4h,008h,000h
DB	000h,034h,009h,000h
DB	000h,054h,00ah,000h
DB	000h,074h,00ch,000h
DB	000h,064h,00dh,000h
DB	000h,0a2h
DB	000h,000h
$L$SEH_info_sqr_n_mul_mont_pasta_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h


.xdata	ENDS
END
