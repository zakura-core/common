; Copyright Supranational LLC
; Licensed under the Apache License, Version 2.0.
; SPDX-License-Identifier: Apache-2.0
; Modified by Zakura; generated from the attributed source.

OPTION	DOTNAME
.text$	SEGMENT ALIGN(256) 'CODE'

PUBLIC	pasta_add


ALIGN	32
pasta_add	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_pasta_add::
	mov	rdi,rcx
	mov	rsi,rdx
	mov	rdx,r8
	mov	rcx,r9



	push	rbp

	push	rbx

	sub	rsp,8

$L$SEH_body_pasta_add::


	mov	r8,QWORD PTR[rsi]
	mov	r9,QWORD PTR[8+rsi]
	mov	r10,QWORD PTR[16+rsi]
	mov	r11,QWORD PTR[24+rsi]

$L$oaded_a_pasta_add::
	add	r8,QWORD PTR[rdx]
	adc	r9,QWORD PTR[8+rdx]
	mov	rax,r8
	adc	r10,QWORD PTR[16+rdx]
	mov	rsi,r9
	adc	r11,QWORD PTR[24+rdx]
	sbb	rdx,rdx

	mov	rbx,r10
	sub	r8,QWORD PTR[rcx]
	sbb	r9,QWORD PTR[8+rcx]
	sbb	r10,QWORD PTR[16+rcx]
	mov	rbp,r11
	sbb	r11,QWORD PTR[24+rcx]
	sbb	rdx,0

	cmovc	r8,rax
	cmovc	r9,rsi
	mov	QWORD PTR[rdi],r8
	cmovc	r10,rbx
	mov	QWORD PTR[8+rdi],r9
	cmovc	r11,rbp
	mov	QWORD PTR[16+rdi],r10
	mov	QWORD PTR[24+rdi],r11

	mov	rbx,QWORD PTR[8+rsp]

	mov	rbp,QWORD PTR[16+rsp]

	lea	rsp,QWORD PTR[24+rsp]

$L$SEH_epilogue_pasta_add::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_pasta_add::
pasta_add	ENDP


PUBLIC	pasta_cneg


ALIGN	32
pasta_cneg	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_pasta_cneg::
	mov	rdi,rcx
	mov	rsi,rdx
	mov	rdx,r8
	mov	rcx,r9



	push	rbp

	push	rbx

	push	r12

$L$SEH_body_pasta_cneg::


	mov	r12,QWORD PTR[rsi]
	mov	r9,QWORD PTR[8+rsi]
	mov	r10,QWORD PTR[16+rsi]
	mov	r8,r12
	mov	r11,QWORD PTR[24+rsi]
	or	r12,r9
	or	r12,r10
	or	r12,r11
	mov	rbp,-1

	mov	rax,QWORD PTR[rcx]
	cmovnz	r12,rbp
	mov	rsi,QWORD PTR[8+rcx]
	mov	rbx,QWORD PTR[16+rcx]
	and	rax,r12
	mov	rbp,QWORD PTR[24+rcx]
	and	rsi,r12
	and	rbx,r12
	and	rbp,r12

	sub	rax,r8
	sbb	rsi,r9
	sbb	rbx,r10
	sbb	rbp,r11

	or	rdx,rdx

	cmovz	rax,r8
	cmovz	rsi,r9
	mov	QWORD PTR[rdi],rax
	cmovz	rbx,r10
	mov	QWORD PTR[8+rdi],rsi
	cmovz	rbp,r11
	mov	QWORD PTR[16+rdi],rbx
	mov	QWORD PTR[24+rdi],rbp

	mov	r12,QWORD PTR[rsp]

	mov	rbx,QWORD PTR[8+rsp]

	mov	rbp,QWORD PTR[16+rsp]

	lea	rsp,QWORD PTR[24+rsp]

$L$SEH_epilogue_pasta_cneg::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_pasta_cneg::
pasta_cneg	ENDP


PUBLIC	pasta_sub


ALIGN	32
pasta_sub	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_pasta_sub::
	mov	rdi,rcx
	mov	rsi,rdx
	mov	rdx,r8
	mov	rcx,r9



	push	rbp

	push	rbx

	sub	rsp,8

$L$SEH_body_pasta_sub::


	mov	r8,QWORD PTR[rsi]
	mov	r9,QWORD PTR[8+rsi]
	mov	r10,QWORD PTR[16+rsi]
	mov	r11,QWORD PTR[24+rsi]

	sub	r8,QWORD PTR[rdx]
	mov	rax,QWORD PTR[rcx]
	sbb	r9,QWORD PTR[8+rdx]
	mov	rsi,QWORD PTR[8+rcx]
	sbb	r10,QWORD PTR[16+rdx]
	mov	rbx,QWORD PTR[16+rcx]
	sbb	r11,QWORD PTR[24+rdx]
	mov	rbp,QWORD PTR[24+rcx]
	sbb	rdx,rdx

	and	rax,rdx
	and	rsi,rdx
	and	rbx,rdx
	and	rbp,rdx

	add	r8,rax
	adc	r9,rsi
	mov	QWORD PTR[rdi],r8
	adc	r10,rbx
	mov	QWORD PTR[8+rdi],r9
	adc	r11,rbp
	mov	QWORD PTR[16+rdi],r10
	mov	QWORD PTR[24+rdi],r11

	mov	rbx,QWORD PTR[8+rsp]

	mov	rbp,QWORD PTR[16+rsp]

	lea	rsp,QWORD PTR[24+rsp]

$L$SEH_epilogue_pasta_sub::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_pasta_sub::
pasta_sub	ENDP


ALIGN	32
__lshift_mod_256	PROC PRIVATE
	DB	243,15,30,250
	add	r8,r8
	adc	r9,r9
	mov	rax,r8
	adc	r10,r10
	mov	rsi,r9
	adc	r11,r11
	sbb	r12,r12

	mov	rbx,r10
	sub	r8,QWORD PTR[rcx]
	sbb	r9,QWORD PTR[8+rcx]
	sbb	r10,QWORD PTR[16+rcx]
	mov	rbp,r11
	sbb	r11,QWORD PTR[24+rcx]
	sbb	r12,0

	cmovc	r8,rax
	cmovc	r9,rsi
	cmovc	r10,rbx
	cmovc	r11,rbp

	DB	0F3h,0C3h		;repret
__lshift_mod_256	ENDP


PUBLIC	pasta_lshift


ALIGN	32
pasta_lshift	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_pasta_lshift::
	mov	rdi,rcx
	mov	rsi,rdx
	mov	rdx,r8
	mov	rcx,r9



	push	rbp

	push	rbx

	push	r12

$L$SEH_body_pasta_lshift::


	mov	r8,QWORD PTR[rsi]
	mov	r9,QWORD PTR[8+rsi]
	mov	r10,QWORD PTR[16+rsi]
	mov	r11,QWORD PTR[24+rsi]

$L$oop_lshift_mod_256::
	call	__lshift_mod_256
	dec	edx
	jnz	$L$oop_lshift_mod_256

	mov	QWORD PTR[rdi],r8
	mov	QWORD PTR[8+rdi],r9
	mov	QWORD PTR[16+rdi],r10
	mov	QWORD PTR[24+rdi],r11

	mov	r12,QWORD PTR[rsp]

	mov	rbx,QWORD PTR[8+rsp]

	mov	rbp,QWORD PTR[16+rsp]

	lea	rsp,QWORD PTR[24+rsp]

$L$SEH_epilogue_pasta_lshift::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_pasta_lshift::
pasta_lshift	ENDP


PUBLIC	pasta_rshift


ALIGN	32
pasta_rshift	PROC PUBLIC
	DB	243,15,30,250
	mov	QWORD PTR[8+rsp],rdi	;WIN64 prologue
	mov	QWORD PTR[16+rsp],rsi
	mov	r11,rsp
$L$SEH_begin_pasta_rshift::
	mov	rdi,rcx
	mov	rsi,rdx
	mov	rdx,r8
	mov	rcx,r9



	push	rbp

	push	rbx

	sub	rsp,8

$L$SEH_body_pasta_rshift::


	mov	rbp,QWORD PTR[rsi]
	mov	r9,QWORD PTR[8+rsi]
	mov	r10,QWORD PTR[16+rsi]
	mov	r11,QWORD PTR[24+rsi]

$L$oop_rshift_mod_256::
	mov	r8,rbp
	and	rbp,1
	mov	rax,QWORD PTR[rcx]
	neg	rbp
	mov	rsi,QWORD PTR[8+rcx]
	mov	rbx,QWORD PTR[16+rcx]

	and	rax,rbp
	and	rsi,rbp
	and	rbx,rbp
	and	rbp,QWORD PTR[24+rcx]

	add	r8,rax
	adc	r9,rsi
	adc	r10,rbx
	adc	r11,rbp
	sbb	rax,rax

	shr	r8,1
	mov	rbp,r9
	shr	r9,1
	mov	rbx,r10
	shr	r10,1
	mov	rsi,r11
	shr	r11,1

	shl	rbp,63
	shl	rbx,63
	or	rbp,r8
	shl	rsi,63
	or	r9,rbx
	shl	rax,63
	or	r10,rsi
	or	r11,rax

	dec	edx
	jnz	$L$oop_rshift_mod_256

	mov	QWORD PTR[rdi],rbp
	mov	QWORD PTR[8+rdi],r9
	mov	QWORD PTR[16+rdi],r10
	mov	QWORD PTR[24+rdi],r11

	mov	rbx,QWORD PTR[8+rsp]

	mov	rbp,QWORD PTR[16+rsp]

	lea	rsp,QWORD PTR[24+rsp]

$L$SEH_epilogue_pasta_rshift::
	mov	rdi,QWORD PTR[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD PTR[16+rsp]

	DB	0F3h,0C3h		;repret

$L$SEH_end_pasta_rshift::
pasta_rshift	ENDP
.text$	ENDS
.pdata	SEGMENT READONLY ALIGN(4)
ALIGN	4
	DD	imagerel $L$SEH_begin_pasta_add
	DD	imagerel $L$SEH_body_pasta_add
	DD	imagerel $L$SEH_info_pasta_add_prologue

	DD	imagerel $L$SEH_body_pasta_add
	DD	imagerel $L$SEH_epilogue_pasta_add
	DD	imagerel $L$SEH_info_pasta_add_body

	DD	imagerel $L$SEH_epilogue_pasta_add
	DD	imagerel $L$SEH_end_pasta_add
	DD	imagerel $L$SEH_info_pasta_add_epilogue

	DD	imagerel $L$SEH_begin_pasta_cneg
	DD	imagerel $L$SEH_body_pasta_cneg
	DD	imagerel $L$SEH_info_pasta_cneg_prologue

	DD	imagerel $L$SEH_body_pasta_cneg
	DD	imagerel $L$SEH_epilogue_pasta_cneg
	DD	imagerel $L$SEH_info_pasta_cneg_body

	DD	imagerel $L$SEH_epilogue_pasta_cneg
	DD	imagerel $L$SEH_end_pasta_cneg
	DD	imagerel $L$SEH_info_pasta_cneg_epilogue

	DD	imagerel $L$SEH_begin_pasta_sub
	DD	imagerel $L$SEH_body_pasta_sub
	DD	imagerel $L$SEH_info_pasta_sub_prologue

	DD	imagerel $L$SEH_body_pasta_sub
	DD	imagerel $L$SEH_epilogue_pasta_sub
	DD	imagerel $L$SEH_info_pasta_sub_body

	DD	imagerel $L$SEH_epilogue_pasta_sub
	DD	imagerel $L$SEH_end_pasta_sub
	DD	imagerel $L$SEH_info_pasta_sub_epilogue

	DD	imagerel $L$SEH_begin_pasta_lshift
	DD	imagerel $L$SEH_body_pasta_lshift
	DD	imagerel $L$SEH_info_pasta_lshift_prologue

	DD	imagerel $L$SEH_body_pasta_lshift
	DD	imagerel $L$SEH_epilogue_pasta_lshift
	DD	imagerel $L$SEH_info_pasta_lshift_body

	DD	imagerel $L$SEH_epilogue_pasta_lshift
	DD	imagerel $L$SEH_end_pasta_lshift
	DD	imagerel $L$SEH_info_pasta_lshift_epilogue

	DD	imagerel $L$SEH_begin_pasta_rshift
	DD	imagerel $L$SEH_body_pasta_rshift
	DD	imagerel $L$SEH_info_pasta_rshift_prologue

	DD	imagerel $L$SEH_body_pasta_rshift
	DD	imagerel $L$SEH_epilogue_pasta_rshift
	DD	imagerel $L$SEH_info_pasta_rshift_body

	DD	imagerel $L$SEH_epilogue_pasta_rshift
	DD	imagerel $L$SEH_end_pasta_rshift
	DD	imagerel $L$SEH_info_pasta_rshift_epilogue

.pdata	ENDS
.xdata	SEGMENT READONLY ALIGN(8)
ALIGN	8
$L$SEH_info_pasta_add_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_pasta_add_body::
DB	1,0,9,0
DB	000h,034h,001h,000h
DB	000h,054h,002h,000h
DB	000h,074h,004h,000h
DB	000h,064h,005h,000h
DB	000h,022h
DB	000h,000h
$L$SEH_info_pasta_add_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h

$L$SEH_info_pasta_cneg_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_pasta_cneg_body::
DB	1,0,11,0
DB	000h,0c4h,000h,000h
DB	000h,034h,001h,000h
DB	000h,054h,002h,000h
DB	000h,074h,004h,000h
DB	000h,064h,005h,000h
DB	000h,022h
DB	000h,000h,000h,000h,000h,000h
$L$SEH_info_pasta_cneg_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h

$L$SEH_info_pasta_sub_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_pasta_sub_body::
DB	1,0,9,0
DB	000h,034h,001h,000h
DB	000h,054h,002h,000h
DB	000h,074h,004h,000h
DB	000h,064h,005h,000h
DB	000h,022h
DB	000h,000h
$L$SEH_info_pasta_sub_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h

$L$SEH_info_pasta_lshift_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_pasta_lshift_body::
DB	1,0,11,0
DB	000h,0c4h,000h,000h
DB	000h,034h,001h,000h
DB	000h,054h,002h,000h
DB	000h,074h,004h,000h
DB	000h,064h,005h,000h
DB	000h,022h
DB	000h,000h,000h,000h,000h,000h
$L$SEH_info_pasta_lshift_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h

$L$SEH_info_pasta_rshift_prologue::
DB	1,0,5,00bh
DB	0,074h,1,0
DB	0,064h,2,0
DB	0,003h
DB	0,0
$L$SEH_info_pasta_rshift_body::
DB	1,0,9,0
DB	000h,034h,001h,000h
DB	000h,054h,002h,000h
DB	000h,074h,004h,000h
DB	000h,064h,005h,000h
DB	000h,022h
DB	000h,000h
$L$SEH_info_pasta_rshift_epilogue::
DB	1,0,4,0
DB	000h,074h,001h,000h
DB	000h,064h,002h,000h
DB	000h,000h,000h,000h


.xdata	ENDS
END
