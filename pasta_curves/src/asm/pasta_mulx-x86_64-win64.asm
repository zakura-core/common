; Copyright Supranational LLC
; Licensed under the Apache License, Version 2.0; see LICENSE-APACHE.
; SPDX-License-Identifier: Apache-2.0
;
; Adapted from Semolina v0.1.4, commit
; 13ffc78074a6fbec44a4fd12b7f585a0bc1dc154:
; https://github.com/supranational/semolina
;
; Montgomery multiplication and its helper are generated from
; pasta_mulx-x86_64.pl. The specialized square is a direct x86-64 translation
; of pasta_mul-armv8.S. Symbols are crate-prefixed.
; The routines have no secret-dependent branches or memory accesses. Their
; reduction specializes the shared high limbs of the two Pasta moduli.

OPTION	DOTNAME
.text$	SEGMENT ALIGN(256) 'CODE'

PUBLIC	pasta_curves_mulx_mont


ALIGN	32
pasta_curves_mulx_mont	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_pasta_curves_mulx_mont::
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

$L$SEH_body_pasta_curves_mulx_mont::


	mov	rbx,rdx
	mov	rdx,QWORD PTR[rdx]
	mov	r14,QWORD PTR[rsi]
	mov	r15,QWORD PTR[8+rsi]
	mov	rbp,QWORD PTR[16+rsi]
	mov	r9,QWORD PTR[24+rsi]
	lea	rsi,QWORD PTR[((-128))+rsi]
	lea	rcx,QWORD PTR[((-128))+rcx]

	mulx	r11,rax,r14
	call	__pasta_curves_mulx_mont

	mov	r15,QWORD PTR[8+rsp]

	mov	r14,QWORD PTR[16+rsp]

	mov	r13,QWORD PTR[24+rsp]

	mov	r12,QWORD PTR[32+rsp]

	mov	rbx,QWORD PTR[40+rsp]

	mov	rbp,QWORD PTR[48+rsp]

	lea	rsp,QWORD PTR[56+rsp]

$L$SEH_epilogue_pasta_curves_mulx_mont::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_pasta_curves_mulx_mont::
pasta_curves_mulx_mont	ENDP

PUBLIC	pasta_curves_sqrx_mont


ALIGN	32
pasta_curves_sqrx_mont	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_pasta_curves_sqrx_mont::
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

	sub	rsp,40

$L$SEH_body_pasta_curves_sqrx_mont::

	mov	rbx,rdi
	mov	rbp,rdx

	; Form the six off-diagonal products once.
	mov	rdx,QWORD PTR[rsi]
	mulx	rax,r9,QWORD PTR[8+rsi]
	mulx	rdi,r10,QWORD PTR[16+rsi]
	add	r10,rax
	adc	rdi,0
	mulx	r12,r11,QWORD PTR[24+rsi]
	add	r11,rdi
	adc	r12,0

	mov	rdx,QWORD PTR[8+rsi]
	mulx	rdi,rax,QWORD PTR[16+rsi]
	add	r11,rax
	adc	rdi,0
	mulx	r13,rax,QWORD PTR[24+rsi]
	add	rax,r12
	adc	r13,0
	add	rax,rdi
	adc	r13,0
	mov	r12,rax

	mov	rdx,QWORD PTR[16+rsi]
	mulx	r14,rax,QWORD PTR[24+rsi]
	add	rax,r13
	adc	r14,0
	mov	r13,rax

	; Double the off-diagonal half of the square.
	xor	r15,r15
	add	r9,r9
	adc	r10,r10
	adc	r11,r11
	adc	r12,r12
	adc	r13,r13
	adc	r14,r14
	adc	r15,r15

	; Add the four diagonal products.
	mov	rdx,QWORD PTR[rsi]
	mulx	rax,r8,rdx
	add	r9,rax
	mov	rdx,QWORD PTR[8+rsi]
	mulx	rdi,rax,rdx
	adc	rax,r10
	adc	rdi,0
	mov	r10,rax
	add	r11,rdi
	mov	rdx,QWORD PTR[16+rsi]
	mulx	rdi,rax,rdx
	adc	rax,r12
	adc	rdi,0
	mov	r12,rax
	add	r13,rdi
	mov	rdx,QWORD PTR[24+rsi]
	mulx	rdi,rax,rdx
	adc	rax,r14
	adc	rdi,0
	mov	r14,rax
	add	r15,rdi

	; Preserve the upper half while reducing the lower half by R.
	mov	QWORD PTR[rsp],r12
	mov	QWORD PTR[8+rsp],r13
	mov	QWORD PTR[16+rsp],r14
	mov	QWORD PTR[24+rsp],r15
	mov	r12,QWORD PTR[rbp]
	mov	r13,QWORD PTR[8+rbp]

	; Montgomery cancellation 0. The p[2] product is zero and the
	; p[3] = 2^62 product is formed with shifts.
	mov	rdx,r8
	imul	rdx,rcx
	mulx	rdi,r15,r13
	mulx	r14,rax,r12
	mov	rax,rdx
	shl	rax,62
	shr	rdx,2
	neg	r8
	adc	r9,r15
	adc	r10,0
	adc	r11,rax
	mov	r8,0
	adc	r8,0
	add	r9,r14
	adc	r10,rdi
	adc	r11,0
	adc	r8,rdx

	; Montgomery cancellation 1.
	mov	rdx,r9
	imul	rdx,rcx
	mulx	rdi,r15,r13
	mulx	r14,rax,r12
	mov	rax,rdx
	shl	rax,62
	shr	rdx,2
	neg	r9
	adc	r10,r15
	adc	r11,0
	adc	r8,rax
	mov	r9,0
	adc	r9,0
	add	r10,r14
	adc	r11,rdi
	adc	r8,0
	adc	r9,rdx

	; Montgomery cancellation 2.
	mov	rdx,r10
	imul	rdx,rcx
	mulx	rdi,r15,r13
	mulx	r14,rax,r12
	mov	rax,rdx
	shl	rax,62
	shr	rdx,2
	neg	r10
	adc	r11,r15
	adc	r8,0
	adc	r9,rax
	mov	r10,0
	adc	r10,0
	add	r11,r14
	adc	r8,rdi
	adc	r9,0
	adc	r10,rdx

	; Montgomery cancellation 3.
	mov	rdx,r11
	imul	rdx,rcx
	mulx	rdi,r15,r13
	mulx	r14,rax,r12
	mov	rax,rdx
	shl	rax,62
	shr	rdx,2
	neg	r11
	adc	r8,r15
	adc	r9,0
	adc	r10,rax
	mov	r11,0
	adc	r11,0
	add	r8,r14
	adc	r9,rdi
	adc	r10,0
	adc	r11,rdx

	; Add the untouched upper half and capture a possible 257th bit.
	add	r8,QWORD PTR[rsp]
	adc	r9,QWORD PTR[8+rsp]
	adc	r10,QWORD PTR[16+rsp]
	adc	r11,QWORD PTR[24+rsp]
	mov	rsi,0
	adc	rsi,0

	; Canonicalize with one constant-time conditional subtraction.
	mov	r14,r8
	mov	r15,r9
	mov	rax,r10
	mov	rdi,r11
	sub	r8,r12
	sbb	r9,r13
	sbb	r10,0
	sbb	r11,QWORD PTR[24+rbp]
	sbb	rsi,0
	cmovc	r8,r14
	cmovc	r9,r15
	cmovc	r10,rax
	cmovc	r11,rdi
	mov	QWORD PTR[rbx],r8
	mov	QWORD PTR[8+rbx],r9
	mov	QWORD PTR[16+rbx],r10
	mov	QWORD PTR[24+rbx],r11

	mov	r15,QWORD PTR[40+rsp]

	mov	r14,QWORD PTR[48+rsp]

	mov	r13,QWORD PTR[56+rsp]

	mov	r12,QWORD PTR[64+rsp]

	mov	rbx,QWORD PTR[72+rsp]

	mov	rbp,QWORD PTR[80+rsp]

	lea	rsp,QWORD PTR[88+rsp]

$L$SEH_epilogue_pasta_curves_sqrx_mont::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_pasta_curves_sqrx_mont::
pasta_curves_sqrx_mont	ENDP

ALIGN	32
__pasta_curves_mulx_mont	PROC PRIVATE
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
__pasta_curves_mulx_mont	ENDP
.text$	ENDS
.pdata	SEGMENT READONLY ALIGN(4)
ALIGN	4
	DD	imagerel $L$SEH_begin_pasta_curves_mulx_mont
	DD	imagerel $L$SEH_body_pasta_curves_mulx_mont
	DD	imagerel $L$SEH_info_pasta_curves_mulx_mont_prologue

	DD	imagerel $L$SEH_body_pasta_curves_mulx_mont
	DD	imagerel $L$SEH_epilogue_pasta_curves_mulx_mont
	DD	imagerel $L$SEH_info_pasta_curves_mulx_mont_body

	DD	imagerel $L$SEH_epilogue_pasta_curves_mulx_mont
	DD	imagerel $L$SEH_end_pasta_curves_mulx_mont
	DD	imagerel $L$SEH_info_pasta_curves_mulx_mont_epilogue

	DD	imagerel $L$SEH_begin_pasta_curves_sqrx_mont
	DD	imagerel $L$SEH_body_pasta_curves_sqrx_mont
	DD	imagerel $L$SEH_info_pasta_curves_sqrx_mont_prologue

	DD	imagerel $L$SEH_body_pasta_curves_sqrx_mont
	DD	imagerel $L$SEH_epilogue_pasta_curves_sqrx_mont
	DD	imagerel $L$SEH_info_pasta_curves_sqrx_mont_body

	DD	imagerel $L$SEH_epilogue_pasta_curves_sqrx_mont
	DD	imagerel $L$SEH_end_pasta_curves_sqrx_mont
	DD	imagerel $L$SEH_info_pasta_curves_sqrx_mont_epilogue

.pdata	ENDS
.xdata	SEGMENT READONLY ALIGN(8)
ALIGN	8
$L$SEH_info_pasta_curves_mulx_mont_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_pasta_curves_mulx_mont_body::
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
$L$SEH_info_pasta_curves_mulx_mont_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h

$L$SEH_info_pasta_curves_sqrx_mont_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_pasta_curves_sqrx_mont_body::
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
$L$SEH_info_pasta_curves_sqrx_mont_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h


.xdata	ENDS
END
