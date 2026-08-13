; Copyright Supranational LLC
; Licensed under the Apache License, Version 2.0.
; SPDX-License-Identifier: Apache-2.0
; Modified by Zakura; generated from the attributed source.

OPTION	DOTNAME
.text$	SEGMENT ALIGN(256) 'CODE'

PUBLIC	mulx_mont_pasta


ALIGN	32
mulx_mont_pasta	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_mulx_mont_pasta::
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

	sub	rsp,8

$L$SEH_body_mulx_mont_pasta::


	mov	rbx,rdx
	mov	rdx,QWORD PTR[rdx]
	mov	r14,QWORD PTR[rsi]
	mov	r15,QWORD PTR[8+rsi]
	mov	rbp,QWORD PTR[16+rsi]
	mov	r9,QWORD PTR[24+rsi]
	lea	rsi,QWORD PTR[((-128))+rsi]
	lea	rcx,QWORD PTR[((-128))+rcx]

	mulx	r11,rax,r14
	call	__mulx_mont_pasta

	mov	r15,QWORD PTR[8+rsp]

	mov	r14,QWORD PTR[16+rsp]

	mov	r13,QWORD PTR[24+rsp]

	mov	r12,QWORD PTR[32+rsp]

	mov	rbx,QWORD PTR[40+rsp]

	mov	rbp,QWORD PTR[48+rsp]

	lea	rsp,QWORD PTR[56+rsp]

$L$SEH_epilogue_mulx_mont_pasta::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_mulx_mont_pasta::
mulx_mont_pasta	ENDP

PUBLIC	sqrx_mont_pasta


ALIGN	32
sqrx_mont_pasta	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_sqrx_mont_pasta::
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

$L$SEH_body_sqrx_mont_pasta::


	mov	rbx,rsi
	mov	r8,rcx
	mov	rcx,rdx
	mov	rdx,QWORD PTR[rsi]
	mov	r15,QWORD PTR[8+rsi]
	mov	rbp,QWORD PTR[16+rsi]
	mov	r9,QWORD PTR[24+rsi]
	lea	rsi,QWORD PTR[((-128))+rbx]
	lea	rcx,QWORD PTR[((-128))+rcx]

	mulx	r11,rax,rdx
	call	__mulx_mont_pasta

	mov	r15,QWORD PTR[8+rsp]

	mov	r14,QWORD PTR[16+rsp]

	mov	r13,QWORD PTR[24+rsp]

	mov	r12,QWORD PTR[32+rsp]

	mov	rbx,QWORD PTR[40+rsp]

	mov	rbp,QWORD PTR[48+rsp]

	lea	rsp,QWORD PTR[56+rsp]

$L$SEH_epilogue_sqrx_mont_pasta::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_sqrx_mont_pasta::
sqrx_mont_pasta	ENDP

ALIGN	32
__mulx_mont_pasta	PROC PRIVATE
	DB	243,15,30,250
	mulx	r12,r15,r15
	mulx	r13,rbp,rbp
	add	r11,r15
	mulx	r14,r9,r9
	mov	rdx,QWORD PTR[8+rbx]
	adc	r12,rbp
	adc	r13,r9
	adc	r14,0

	mov	r10,rax
	imul	rax,r8


	xor	r15,r15
	mulx	r9,rbp,QWORD PTR[((0+128))+rsi]
	adox	r11,rbp
	adcx	r12,r9

	mulx	r9,rbp,QWORD PTR[((8+128))+rsi]
	adox	r12,rbp
	adcx	r13,r9

	mulx	r9,rbp,QWORD PTR[((16+128))+rsi]
	adox	r13,rbp
	adcx	r14,r9

	mulx	r9,rbp,QWORD PTR[((24+128))+rsi]
	mov	rdx,rax
	adox	r14,rbp
	adcx	r9,r15
	adox	r15,r9


	mulx	rax,rbp,QWORD PTR[((0+128))+rcx]
	adcx	r10,rbp
	adox	rax,r11

	mulx	r9,rbp,QWORD PTR[((8+128))+rcx]
	adcx	rax,rbp
	adox	r12,r9

	adcx	r12,r10
	adox	r13,r10

	mulx	r9,rbp,QWORD PTR[((24+128))+rcx]
	mov	rdx,QWORD PTR[16+rbx]
	adcx	r13,rbp
	adox	r14,r9
	adcx	r14,r10
	adox	r15,r10
	adcx	r15,r10
	mov	r11,rax
	imul	rax,r8


	xor	r10,r10
	mulx	r9,rbp,QWORD PTR[((0+128))+rsi]
	adox	r12,rbp
	adcx	r13,r9

	mulx	r9,rbp,QWORD PTR[((8+128))+rsi]
	adox	r13,rbp
	adcx	r14,r9

	mulx	r9,rbp,QWORD PTR[((16+128))+rsi]
	adox	r14,rbp
	adcx	r15,r9

	mulx	r9,rbp,QWORD PTR[((24+128))+rsi]
	mov	rdx,rax
	adox	r15,rbp
	adcx	r9,r10
	adox	r10,r9


	mulx	rax,rbp,QWORD PTR[((0+128))+rcx]
	adcx	r11,rbp
	adox	rax,r12

	mulx	r9,rbp,QWORD PTR[((8+128))+rcx]
	adcx	rax,rbp
	adox	r13,r9

	adcx	r13,r11
	adox	r14,r11

	mulx	r9,rbp,QWORD PTR[((24+128))+rcx]
	mov	rdx,QWORD PTR[24+rbx]
	adcx	r14,rbp
	adox	r15,r9
	adcx	r15,r11
	adox	r10,r11
	adcx	r10,r11
	mov	r12,rax
	imul	rax,r8


	xor	r11,r11
	mulx	r9,rbp,QWORD PTR[((0+128))+rsi]
	adox	r13,rbp
	adcx	r14,r9

	mulx	r9,rbp,QWORD PTR[((8+128))+rsi]
	adox	r14,rbp
	adcx	r15,r9

	mulx	r9,rbp,QWORD PTR[((16+128))+rsi]
	adox	r15,rbp
	adcx	r10,r9

	mulx	r9,rbp,QWORD PTR[((24+128))+rsi]
	mov	rdx,rax
	adox	r10,rbp
	adcx	r9,r11
	adox	r11,r9


	mulx	rax,rbp,QWORD PTR[((0+128))+rcx]
	adcx	r12,rbp
	adox	rax,r13

	mulx	r9,rbp,QWORD PTR[((8+128))+rcx]
	adcx	rax,rbp
	adox	r14,r9

	adcx	r14,r12
	adox	r15,r12

	mulx	r9,rbp,QWORD PTR[((24+128))+rcx]
	mov	rdx,rax
	adcx	r15,rbp
	adox	r10,r9
	adcx	r10,r12
	adox	r11,r12
	adcx	r11,r12
	imul	rdx,r8


	xor	r12,r12
	mulx	r9,r13,QWORD PTR[((0+128))+rcx]
	adcx	r13,rax
	adox	r14,r9

	mulx	r9,rbp,QWORD PTR[((8+128))+rcx]
	adcx	r14,rbp
	adox	r15,r9

	adcx	r15,r13
	adox	r10,r13

	mulx	r9,rbp,QWORD PTR[((24+128))+rcx]
	mov	rdx,r14
	lea	rcx,QWORD PTR[128+rcx]
	adcx	r10,rbp
	adox	r11,r9
	mov	rax,r15
	adcx	r11,r13
	adox	r12,r13
	adc	r12,0




	mov	rbp,r10
	sub	r14,QWORD PTR[rcx]
	sbb	r15,QWORD PTR[8+rcx]
	sbb	r10,QWORD PTR[16+rcx]
	mov	r9,r11
	sbb	r11,QWORD PTR[24+rcx]
	sbb	r12,0

	cmovc	r14,rdx
	cmovc	r15,rax
	cmovc	r10,rbp
	mov	QWORD PTR[rdi],r14
	cmovc	r11,r9
	mov	QWORD PTR[8+rdi],r15
	mov	QWORD PTR[16+rdi],r10
	mov	QWORD PTR[24+rdi],r11

	DB	0F3h,0C3h		;repret
__mulx_mont_pasta	ENDP
PUBLIC	fromx_mont_pasta


ALIGN	32
fromx_mont_pasta	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_fromx_mont_pasta::
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

$L$SEH_body_fromx_mont_pasta::


	mov	rbx,rdx
	call	__mulx_by_1_mont_pasta





	mov	rdx,r15
	mov	r12,r10
	mov	r13,r11

	sub	r14,QWORD PTR[rbx]
	sbb	r15,QWORD PTR[8+rbx]
	sbb	r10,QWORD PTR[16+rbx]
	sbb	r11,QWORD PTR[24+rbx]

	cmovnc	rax,r14
	cmovnc	rdx,r15
	cmovnc	r12,r10
	mov	QWORD PTR[rdi],rax
	cmovnc	r13,r11
	mov	QWORD PTR[8+rdi],rdx
	mov	QWORD PTR[16+rdi],r12
	mov	QWORD PTR[24+rdi],r13

	mov	r15,QWORD PTR[8+rsp]

	mov	r14,QWORD PTR[16+rsp]

	mov	r13,QWORD PTR[24+rsp]

	mov	r12,QWORD PTR[32+rsp]

	mov	rbx,QWORD PTR[40+rsp]

	mov	rbp,QWORD PTR[48+rsp]

	lea	rsp,QWORD PTR[56+rsp]

$L$SEH_epilogue_fromx_mont_pasta::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_fromx_mont_pasta::
fromx_mont_pasta	ENDP

PUBLIC	redcx_mont_pasta


ALIGN	32
redcx_mont_pasta	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_redcx_mont_pasta::
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

$L$SEH_body_redcx_mont_pasta::


	mov	rbx,rdx
	call	__mulx_by_1_mont_pasta

	add	r14,QWORD PTR[32+rsi]
	adc	r15,QWORD PTR[40+rsi]
	mov	rax,r14
	adc	r10,QWORD PTR[48+rsi]
	mov	rdx,r15
	adc	r11,QWORD PTR[56+rsi]
	sbb	rsi,rsi




	mov	r12,r10
	sub	r14,QWORD PTR[rbx]
	sbb	r15,QWORD PTR[8+rbx]
	sbb	r10,QWORD PTR[16+rbx]
	mov	r13,r11
	sbb	r11,QWORD PTR[24+rbx]
	sbb	rsi,0

	cmovnc	rax,r14
	cmovnc	rdx,r15
	cmovnc	r12,r10
	mov	QWORD PTR[rdi],rax
	cmovnc	r13,r11
	mov	QWORD PTR[8+rdi],rdx
	mov	QWORD PTR[16+rdi],r12
	mov	QWORD PTR[24+rdi],r13

	mov	r15,QWORD PTR[8+rsp]

	mov	r14,QWORD PTR[16+rsp]

	mov	r13,QWORD PTR[24+rsp]

	mov	r12,QWORD PTR[32+rsp]

	mov	rbx,QWORD PTR[40+rsp]

	mov	rbp,QWORD PTR[48+rsp]

	lea	rsp,QWORD PTR[56+rsp]

$L$SEH_epilogue_redcx_mont_pasta::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_redcx_mont_pasta::
redcx_mont_pasta	ENDP

ALIGN	32
__mulx_by_1_mont_pasta	PROC PRIVATE
	DB	243,15,30,250
	mov	rax,QWORD PTR[rsi]
	mov	r11,QWORD PTR[8+rsi]
	mov	r12,QWORD PTR[16+rsi]
	mov	r13,QWORD PTR[24+rsi]

	mov	r14,rax
	imul	rax,rcx
	mov	r10,rax

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

	mov	r10,r12
	imul	r12,rcx

	mul	QWORD PTR[24+rbx]
	add	r14,rax
	mov	rax,r12
	adc	rdx,0
	add	r14,rbp
	adc	rdx,0
	mov	r15,rdx

	mul	QWORD PTR[rbx]
	add	r10,rax
	mov	rax,r12
	adc	r10,rdx

	mul	QWORD PTR[8+rbx]
	add	r13,rax
	mov	rax,r12
	adc	rdx,0

	xor	rbp,rbp
	add	r13,r10
	adc	r14,rdx
	adc	rbp,0

	mov	r11,r13
	imul	r13,rcx

	mul	QWORD PTR[24+rbx]
	add	r15,rax
	mov	rax,r13
	adc	rdx,0
	add	r15,rbp
	adc	rdx,0
	mov	r10,rdx

	mul	QWORD PTR[rbx]
	add	r11,rax
	mov	rax,r13
	adc	r11,rdx

	mul	QWORD PTR[8+rbx]
	add	r14,rax
	mov	rax,r13
	adc	rdx,0

	xor	rbp,rbp
	add	r14,r11
	adc	r15,rdx
	adc	rbp,0


	mul	QWORD PTR[24+rbx]
	add	r10,rax
	mov	rax,r14
	adc	rdx,0
	add	r10,rbp
	adc	rdx,0
	mov	r11,rdx
	DB	0F3h,0C3h		;repret
__mulx_by_1_mont_pasta	ENDP
PUBLIC	sqrx_n_mul_mont_pasta


ALIGN	32
sqrx_n_mul_mont_pasta	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_sqrx_n_mul_mont_pasta::
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

$L$SEH_body_sqrx_n_mul_mont_pasta::

	lea	rcx,QWORD PTR[((-128))+rcx]
	lea	r8,QWORD PTR[((-128))+r8]
	mov	QWORD PTR[16+rsp],rcx
	mov	QWORD PTR[24+rsp],rdi
	mov	rbx,rdx

	mov	rdx,QWORD PTR[rsi]
	mov	rbp,QWORD PTR[8+rsi]
	mov	rdi,QWORD PTR[16+rsi]
	mov	rsi,QWORD PTR[24+rsi]
	mov	QWORD PTR[rsp],r9
	mov	rcx,rdx
	jmp	$L$oop_sqrx_pasta

ALIGN	32
$L$oop_sqrx_pasta::
	mov	QWORD PTR[8+rsp],rbx

	mulx	r10,rax,rdx
	xor	r15,r15
	mulx	r9,r11,rbp
	adcx	r11,r10
	mulx	rbx,r12,rdi
	adcx	r12,r9
	mulx	r14,r13,rsi
	mov	rdx,rbp
	adcx	r13,rbx
	adcx	r14,r15
	mov	r10,rax
	imul	rax,QWORD PTR[rsp]


	xor	r15,r15
	mulx	rbx,r9,rcx
	adox	r11,r9
	adcx	r12,rbx

	mulx	rbx,r9,rbp
	adox	r12,r9
	adcx	r13,rbx

	mulx	rbx,r9,rdi
	adox	r13,r9
	adcx	r14,rbx

	mulx	rbx,r9,rsi
	mov	rdx,rax
	adox	r14,r9
	adcx	rbx,r15
	adox	r15,rbx


	mulx	rax,r9,QWORD PTR[((0+128))+r8]
	xor	rbx,rbx
	adcx	r10,r9
	adox	rax,r11

	mulx	rbx,r9,QWORD PTR[((8+128))+r8]
	adcx	rax,r9
	adox	r12,rbx

	adcx	r12,r10
	adox	r13,r10

	mulx	rbx,r9,QWORD PTR[((24+128))+r8]
	mov	rdx,rdi
	adcx	r13,r9
	adox	r14,rbx
	adcx	r14,r10
	adox	r15,r10
	adcx	r15,r10
	mov	r11,rax
	imul	rax,QWORD PTR[rsp]


	xor	r10,r10
	mulx	rbx,r9,rcx
	adox	r12,r9
	adcx	r13,rbx

	mulx	rbx,r9,rbp
	adox	r13,r9
	adcx	r14,rbx

	mulx	rbx,r9,rdi
	adox	r14,r9
	adcx	r15,rbx

	mulx	rbx,r9,rsi
	mov	rdx,rax
	adox	r15,r9
	adcx	rbx,r10
	adox	r10,rbx


	mulx	rax,r9,QWORD PTR[((0+128))+r8]
	xor	rbx,rbx
	adcx	r11,r9
	adox	rax,r12

	mulx	rbx,r9,QWORD PTR[((8+128))+r8]
	adcx	rax,r9
	adox	r13,rbx

	adcx	r13,r11
	adox	r14,r11

	mulx	rbx,r9,QWORD PTR[((24+128))+r8]
	mov	rdx,rsi
	adcx	r14,r9
	adox	r15,rbx
	adcx	r15,r11
	adox	r10,r11
	adcx	r10,r11
	mov	r12,rax
	imul	rax,QWORD PTR[rsp]


	xor	r11,r11
	mulx	rbx,r9,rcx
	adox	r13,r9
	adcx	r14,rbx

	mulx	rbx,r9,rbp
	adox	r14,r9
	adcx	r15,rbx

	mulx	rbx,r9,rdi
	adox	r15,r9
	adcx	r10,rbx

	mulx	rbx,r9,rsi
	mov	rdx,rax
	adox	r10,r9
	adcx	rbx,r11
	adox	r11,rbx


	mulx	rax,r9,QWORD PTR[((0+128))+r8]
	xor	rbx,rbx
	adcx	r12,r9
	adox	rax,r13

	mulx	rbx,r9,QWORD PTR[((8+128))+r8]
	adcx	rax,r9
	adox	r14,rbx

	adcx	r14,r12
	adox	r15,r12

	mulx	rbx,r9,QWORD PTR[((24+128))+r8]
	mov	rdx,rax
	adcx	r15,r9
	adox	r10,rbx
	adcx	r10,r12
	adox	r11,r12
	adcx	r11,r12
	imul	rdx,QWORD PTR[rsp]
	mov	rbx,QWORD PTR[8+rsp]
	mov	r12,QWORD PTR[16+rsp]


	xor	rdi,rdi
	mulx	rcx,r9,QWORD PTR[((0+128))+r8]
	adcx	rax,r9
	adox	rcx,r14

	mulx	rbp,r9,QWORD PTR[((8+128))+r8]
	adcx	rcx,r9
	adox	rbp,r15

	adcx	rbp,rax
	adox	rdi,r10

	mulx	rsi,r9,QWORD PTR[((24+128))+r8]
	mov	rdx,rcx
	adcx	rdi,r9
	adox	rsi,r11
	adcx	rsi,rax

	sub	rbx,1
	jnz	$L$oop_sqrx_pasta
	mulx	r13,rax,QWORD PTR[((0+128))+r12]
	xor	rcx,rcx
	mulx	r9,r14,QWORD PTR[((8+128))+r12]
	adcx	r14,r13
	mulx	rbx,r15,QWORD PTR[((16+128))+r12]
	adcx	r15,r9
	mulx	r11,r10,QWORD PTR[((24+128))+r12]
	mov	rdx,rbp
	adcx	r10,rbx
	adcx	r11,rcx
	mov	r13,rax
	imul	rax,QWORD PTR[rsp]


	xor	rcx,rcx
	mulx	rbx,r9,QWORD PTR[((0+128))+r12]
	adox	r14,r9
	adcx	r15,rbx

	mulx	rbx,r9,QWORD PTR[((8+128))+r12]
	adox	r15,r9
	adcx	r10,rbx

	mulx	rbx,r9,QWORD PTR[((16+128))+r12]
	adox	r10,r9
	adcx	r11,rbx

	mulx	rbx,r9,QWORD PTR[((24+128))+r12]
	mov	rdx,rax
	adox	r11,r9
	adcx	rbx,rcx
	adox	rcx,rbx


	mulx	rax,r9,QWORD PTR[((0+128))+r8]
	adcx	r13,r9
	adox	rax,r14

	mulx	rbx,r9,QWORD PTR[((8+128))+r8]
	adcx	rax,r9
	adox	r15,rbx

	adcx	r15,r13
	adox	r10,r13

	mulx	rbx,r9,QWORD PTR[((24+128))+r8]
	mov	rdx,rdi
	adcx	r10,r9
	adox	r11,rbx
	adcx	r11,r13
	adox	rcx,r13
	adcx	rcx,r13
	mov	r14,rax
	imul	rax,QWORD PTR[rsp]


	xor	r13,r13
	mulx	rbx,r9,QWORD PTR[((0+128))+r12]
	adox	r15,r9
	adcx	r10,rbx

	mulx	rbx,r9,QWORD PTR[((8+128))+r12]
	adox	r10,r9
	adcx	r11,rbx

	mulx	rbx,r9,QWORD PTR[((16+128))+r12]
	adox	r11,r9
	adcx	rcx,rbx

	mulx	rbx,r9,QWORD PTR[((24+128))+r12]
	mov	rdx,rax
	adox	rcx,r9
	adcx	rbx,r13
	adox	r13,rbx


	mulx	rax,r9,QWORD PTR[((0+128))+r8]
	adcx	r14,r9
	adox	rax,r15

	mulx	rbx,r9,QWORD PTR[((8+128))+r8]
	adcx	rax,r9
	adox	r10,rbx

	adcx	r10,r14
	adox	r11,r14

	mulx	rbx,r9,QWORD PTR[((24+128))+r8]
	mov	rdx,rsi
	adcx	r11,r9
	adox	rcx,rbx
	adcx	rcx,r14
	adox	r13,r14
	adcx	r13,r14
	mov	r15,rax
	imul	rax,QWORD PTR[rsp]


	xor	r14,r14
	mulx	rbx,r9,QWORD PTR[((0+128))+r12]
	adox	r10,r9
	adcx	r11,rbx

	mulx	rbx,r9,QWORD PTR[((8+128))+r12]
	adox	r11,r9
	adcx	rcx,rbx

	mulx	rbx,r9,QWORD PTR[((16+128))+r12]
	adox	rcx,r9
	adcx	r13,rbx

	mulx	rbx,r9,QWORD PTR[((24+128))+r12]
	mov	rdx,rax
	adox	r13,r9
	adcx	rbx,r14
	adox	r14,rbx


	mulx	rax,r9,QWORD PTR[((0+128))+r8]
	adcx	r15,r9
	adox	rax,r10

	mulx	rbx,r9,QWORD PTR[((8+128))+r8]
	adcx	rax,r9
	adox	r11,rbx

	adcx	r11,r15
	adox	rcx,r15

	mulx	rbx,r9,QWORD PTR[((24+128))+r8]
	mov	rdx,rax
	adcx	rcx,r9
	adox	r13,rbx
	adcx	r13,r15
	adox	r14,r15
	adcx	r14,r15
	imul	rdx,QWORD PTR[rsp]
	mov	rdi,QWORD PTR[24+rsp]


	xor	r15,r15
	mulx	rbx,r9,QWORD PTR[((0+128))+r8]
	adcx	rax,r9
	adox	r11,rbx

	mulx	rbx,r9,QWORD PTR[((8+128))+r8]
	adcx	r11,r9
	adox	rcx,rbx


	adcx	rcx,r15
	adox	r13,r15

	mulx	rbx,r9,QWORD PTR[((24+128))+r8]


	adcx	r13,r9
	adox	r14,rbx
	adcx	r14,r15














	mov	QWORD PTR[rdi],r11

	mov	QWORD PTR[8+rdi],rcx
	mov	QWORD PTR[16+rdi],r13
	mov	QWORD PTR[24+rdi],r14

	mov	r15,QWORD PTR[40+rsp]

	mov	r14,QWORD PTR[48+rsp]

	mov	r13,QWORD PTR[56+rsp]

	mov	r12,QWORD PTR[64+rsp]

	mov	rbx,QWORD PTR[72+rsp]

	mov	rbp,QWORD PTR[80+rsp]

	lea	rsp,QWORD PTR[88+rsp]

$L$SEH_epilogue_sqrx_n_mul_mont_pasta::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_sqrx_n_mul_mont_pasta::
sqrx_n_mul_mont_pasta	ENDP
.text$	ENDS
.pdata	SEGMENT READONLY ALIGN(4)
ALIGN	4
	DD	imagerel $L$SEH_begin_mulx_mont_pasta
	DD	imagerel $L$SEH_body_mulx_mont_pasta
	DD	imagerel $L$SEH_info_mulx_mont_pasta_prologue

	DD	imagerel $L$SEH_body_mulx_mont_pasta
	DD	imagerel $L$SEH_epilogue_mulx_mont_pasta
	DD	imagerel $L$SEH_info_mulx_mont_pasta_body

	DD	imagerel $L$SEH_epilogue_mulx_mont_pasta
	DD	imagerel $L$SEH_end_mulx_mont_pasta
	DD	imagerel $L$SEH_info_mulx_mont_pasta_epilogue

	DD	imagerel $L$SEH_begin_sqrx_mont_pasta
	DD	imagerel $L$SEH_body_sqrx_mont_pasta
	DD	imagerel $L$SEH_info_sqrx_mont_pasta_prologue

	DD	imagerel $L$SEH_body_sqrx_mont_pasta
	DD	imagerel $L$SEH_epilogue_sqrx_mont_pasta
	DD	imagerel $L$SEH_info_sqrx_mont_pasta_body

	DD	imagerel $L$SEH_epilogue_sqrx_mont_pasta
	DD	imagerel $L$SEH_end_sqrx_mont_pasta
	DD	imagerel $L$SEH_info_sqrx_mont_pasta_epilogue

	DD	imagerel $L$SEH_begin_fromx_mont_pasta
	DD	imagerel $L$SEH_body_fromx_mont_pasta
	DD	imagerel $L$SEH_info_fromx_mont_pasta_prologue

	DD	imagerel $L$SEH_body_fromx_mont_pasta
	DD	imagerel $L$SEH_epilogue_fromx_mont_pasta
	DD	imagerel $L$SEH_info_fromx_mont_pasta_body

	DD	imagerel $L$SEH_epilogue_fromx_mont_pasta
	DD	imagerel $L$SEH_end_fromx_mont_pasta
	DD	imagerel $L$SEH_info_fromx_mont_pasta_epilogue

	DD	imagerel $L$SEH_begin_redcx_mont_pasta
	DD	imagerel $L$SEH_body_redcx_mont_pasta
	DD	imagerel $L$SEH_info_redcx_mont_pasta_prologue

	DD	imagerel $L$SEH_body_redcx_mont_pasta
	DD	imagerel $L$SEH_epilogue_redcx_mont_pasta
	DD	imagerel $L$SEH_info_redcx_mont_pasta_body

	DD	imagerel $L$SEH_epilogue_redcx_mont_pasta
	DD	imagerel $L$SEH_end_redcx_mont_pasta
	DD	imagerel $L$SEH_info_redcx_mont_pasta_epilogue

	DD	imagerel $L$SEH_begin_sqrx_n_mul_mont_pasta
	DD	imagerel $L$SEH_body_sqrx_n_mul_mont_pasta
	DD	imagerel $L$SEH_info_sqrx_n_mul_mont_pasta_prologue

	DD	imagerel $L$SEH_body_sqrx_n_mul_mont_pasta
	DD	imagerel $L$SEH_epilogue_sqrx_n_mul_mont_pasta
	DD	imagerel $L$SEH_info_sqrx_n_mul_mont_pasta_body

	DD	imagerel $L$SEH_epilogue_sqrx_n_mul_mont_pasta
	DD	imagerel $L$SEH_end_sqrx_n_mul_mont_pasta
	DD	imagerel $L$SEH_info_sqrx_n_mul_mont_pasta_epilogue

.pdata	ENDS
.xdata	SEGMENT READONLY ALIGN(8)
ALIGN	8
$L$SEH_info_mulx_mont_pasta_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_mulx_mont_pasta_body::
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
$L$SEH_info_mulx_mont_pasta_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h

$L$SEH_info_sqrx_mont_pasta_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_sqrx_mont_pasta_body::
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
$L$SEH_info_sqrx_mont_pasta_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h

$L$SEH_info_fromx_mont_pasta_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_fromx_mont_pasta_body::
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
$L$SEH_info_fromx_mont_pasta_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h

$L$SEH_info_redcx_mont_pasta_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_redcx_mont_pasta_body::
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
$L$SEH_info_redcx_mont_pasta_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h

$L$SEH_info_sqrx_n_mul_mont_pasta_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_sqrx_n_mul_mont_pasta_body::
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
$L$SEH_info_sqrx_n_mul_mont_pasta_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h


.xdata	ENDS
END
