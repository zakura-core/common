// Fused x86-64 lazy-squaring chain for the Pasta fields.
//
// The loop is the instruction schedule generated for the interleaved
// `portable::square_reduce_lazy_pasta` implementation. Its four-limb
// accumulator remains in registers across iterations. When `by` is non-null,
// the closing Montgomery multiplication follows in this same leaf function
// and consumes those four accumulator limbs directly from registers. The only
// conditional subtraction is the one at the end of that multiplication.

#if defined(__APPLE__)
#define C_SYMBOL(name) _##name
#else
#define C_SYMBOL(name) name
#endif

    .text
    .p2align 4
    .globl C_SYMBOL(pasta_x86_64_sqr_n)
#if defined(__APPLE__)
    .private_extern C_SYMBOL(pasta_x86_64_sqr_n)
#else
    .hidden C_SYMBOL(pasta_x86_64_sqr_n)
    .type C_SYMBOL(pasta_x86_64_sqr_n), @function
#endif
C_SYMBOL(pasta_x86_64_sqr_n):
    .cfi_startproc
    pushq %rbp
    .cfi_def_cfa_offset 16
    .cfi_offset %rbp, -16
    movq %rsp, %rbp
    .cfi_def_cfa_register %rbp
    pushq %r15
    pushq %r14
    pushq %r13
    pushq %r12
    pushq %rbx
    .cfi_offset %rbx, -56
    .cfi_offset %r12, -48
    .cfi_offset %r13, -40
    .cfi_offset %r14, -32
    .cfi_offset %r15, -24

    // Fixed state in the red zone. This is a leaf function on every target
    // for which it is built (Unix x86-64).
    movq %rdi, -88(%rbp)       // output pointer
    movq %rcx, -128(%rbp)      // optional closing multiplier
    movq (%r8), %rdi
    movq %rdi, -64(%rbp)       // modulus[0]
    movq 8(%r8), %rdi
    movq %rdi, -56(%rbp)       // modulus[1]
    movq %r9, -48(%rbp)        // Montgomery inverse

    // The lazy accumulator stays in r11:rbx:r12:rax (little-endian).
    movq (%rsi), %r11
    movq 8(%rsi), %rbx
    movq 16(%rsi), %r12
    movq 24(%rsi), %rax
    testl %edx, %edx
    je .Lsquare_done

    .p2align 4
.Lsquare_loop:
    movl %edx, -68(%rbp)

    // Low off-diagonal products and the low diagonal terms.
    movq %r11, %rdx
    mulxq %rbx, %r9, %rcx
    mulxq %r12, %r14, %rsi
    addq %rcx, %r14
    mulxq %rax, %r10, %r8
    movq %rbx, %rdx
    mulxq %r12, %rdi, %r15
    adcq %rsi, %r10
    mulxq %rax, %rcx, %rdx
    adcq %r8, %rcx
    adcq $0, %rdx
    movq %rdx, %rsi
    movq %r11, %rdx
    mulxq %r11, %r13, %r8
    movq %rbx, %rdx
    mulxq %rbx, %rdx, %rbx
    addq %r10, %rdi
    adcq %r15, %rcx
    movq %rcx, -80(%rbp)
    adcq $0, %rsi
    movq %rsi, -120(%rbp)
    movq %rdi, %r11
    shldq $1, %r14, %r11
    shldq $1, %r9, %r14
    addq %r9, %r9
    addq %rdx, %r14
    adcq $0, %rbx
    addq %r8, %r9
    adcq $0, %r14
    adcq $0, %rbx

    // Montgomery round 0.
    movq -48(%rbp), %r8
    imulq %r13, %r8
    movq -64(%rbp), %rdx
    mulxq %r8, %rcx, %rsi
    movq -56(%rbp), %rdx
    mulxq %r8, %r10, %r15
    addq %r9, %r10
    adcq $0, %r15
    addq %r13, %rcx
    adcq %rsi, %r10
    adcq $0, %r15
    movq %r8, %rcx
    shlq $62, %rcx
    shrq $2, %r8

    // Independent upper diagonal work overlaps the reduction.
    movq -80(%rbp), %rdx
    shrdq $63, %rdx, %rdi
    movq %r12, %rdx
    mulxq %r12, %rdx, %rsi
    addq %rdi, %rdx
    adcq $0, %rsi
    addq %r11, %rbx
    adcq $0, %rdx
    movq %rdx, -112(%rbp)
    adcq $0, %rsi
    movq %rsi, -104(%rbp)
    addq %r14, %r15
    adcq %rcx, %rbx
    adcq $0, %r8

    // Montgomery round 1.
    movq -48(%rbp), %r9
    movq %r9, %r11
    imulq %r10, %r11
    movq %r11, %rdx
    movq -64(%rbp), %r13
    mulxq %r13, %rsi, %rcx
    movq %rcx, -96(%rbp)
    movq -56(%rbp), %rcx
    mulxq %rcx, %rdi, %r14
    addq %r15, %rdi
    adcq $0, %r14
    addq %r10, %rsi
    adcq -96(%rbp), %rdi
    adcq $0, %r14
    movq %r11, %r10
    shlq $62, %r10
    shrq $2, %r11
    addq %rbx, %r14
    adcq %r8, %r10
    adcq $0, %r11

    // Montgomery round 2.
    movq %r9, %rbx
    imulq %rdi, %rbx
    movq %rbx, %rdx
    mulxq %r13, %rsi, %r9
    mulxq %rcx, %r8, %r13
    addq %r14, %r8
    adcq $0, %r13
    addq %rdi, %rsi
    adcq %r9, %r8
    adcq $0, %r13
    movq %rbx, %r15
    shlq $62, %r15
    shrq $2, %rbx
    addq %r10, %r13
    adcq %r11, %r15
    adcq $0, %rbx

    // Montgomery round 3.
    movq -48(%rbp), %r14
    imulq %r8, %r14
    movq %r14, %rdx
    mulxq -64(%rbp), %rsi, %rcx
    mulxq -56(%rbp), %r11, %rdi
    addq %r13, %r11
    adcq $0, %rdi
    addq %r8, %rsi
    adcq %rcx, %r11
    adcq $0, %rdi
    movq %r14, %r8
    shlq $62, %r8
    shrq $2, %r14
    addq %r15, %rdi
    adcq %rbx, %r8

    // Finish the upper off-diagonal products and fold the high half.
    movq %r12, %rdx
    mulxq %rax, %rbx, %rcx
    adcq $0, %r14
    addq -120(%rbp), %rbx
    adcq $0, %rcx
    movq %rcx, %rsi
    shldq $1, %rbx, %rcx
    movq %rax, %rdx
    mulxq %rax, %r12, %rax
    movl -68(%rbp), %edx
    movq -80(%rbp), %r10
    shldq $1, %r10, %rbx
    shrq $63, %rsi
    addq %rcx, %r12
    adcq $0, %rax
    addq -104(%rbp), %rbx
    adcq $0, %r12
    adcq %rsi, %rax
    addq -112(%rbp), %r11
    adcq %rdi, %rbx
    adcq %r8, %r12
    adcq %r14, %rax
    decl %edx
    jne .Lsquare_loop

.Lsquare_done:
    cmpq $0, -128(%rbp)
    je .Lstore_lazy

    // Reassign the live lazy accumulator as fixed multiplier limbs:
    // rax:rbx:rcx:rdi. This avoids a boundary spill and all sixteen lhs
    // reloads in the four multiplication rows.
    movq %rax, %rdi
    movq %r12, %rcx
    movq %r11, %rax
    movq -128(%rbp), %rsi

    // Round 0: initialize a five-limb accumulator with lazy * by[0].
    movq (%rsi), %rdx
    mulxq %rax, %r8, %r9
    mulxq %rbx, %r13, %r10
    addq %r13, %r9
    mulxq %rcx, %r13, %r11
    adcq %r13, %r10
    mulxq %rdi, %r13, %r12
    adcq %r13, %r11
    adcq $0, %r12

    // Montgomery step 0.
    movq %r8, %rdx
    imulq -48(%rbp), %rdx
    mulxq -56(%rbp), %r13, %r14
    movq %rdx, %r15
    shlq $62, %r15
    negq %r8
    adcq %r13, %r9
    adcq $0, %r10
    adcq %r15, %r11
    adcq $0, %r12
    mulxq -64(%rbp), %r15, %r13
    movq %rdx, %r15
    shrq $2, %r15
    movq $0, %r8
    addq %r13, %r9
    adcq %r14, %r10
    adcq $0, %r11
    adcq %r15, %r12
    adcq $0, %r8

    // Round 1, using CF and OF as independent product carry chains.
    movq 8(%rsi), %rdx
    xorq %r13, %r13
    mulxq %rax, %r13, %r14
    adcxq %r13, %r9
    adoxq %r14, %r10
    mulxq %rbx, %r13, %r14
    adcxq %r13, %r10
    adoxq %r14, %r11
    mulxq %rcx, %r13, %r14
    adcxq %r13, %r11
    adoxq %r14, %r12
    mulxq %rdi, %r13, %r14
    adcxq %r13, %r12
    adoxq %r14, %r8
    movq $0, %r13
    adcxq %r13, %r8
    adoxq %r13, %r8

    // Montgomery step 1.
    movq %r9, %rdx
    imulq -48(%rbp), %rdx
    mulxq -56(%rbp), %r13, %r14
    movq %rdx, %r15
    shlq $62, %r15
    negq %r9
    adcq %r13, %r10
    adcq $0, %r11
    adcq %r15, %r12
    adcq $0, %r8
    mulxq -64(%rbp), %r15, %r13
    movq %rdx, %r15
    shrq $2, %r15
    movq $0, %r9
    addq %r13, %r10
    adcq %r14, %r11
    adcq $0, %r12
    adcq %r15, %r8
    adcq $0, %r9

    // Round 2.
    movq 16(%rsi), %rdx
    xorq %r13, %r13
    mulxq %rax, %r13, %r14
    adcxq %r13, %r10
    adoxq %r14, %r11
    mulxq %rbx, %r13, %r14
    adcxq %r13, %r11
    adoxq %r14, %r12
    mulxq %rcx, %r13, %r14
    adcxq %r13, %r12
    adoxq %r14, %r8
    mulxq %rdi, %r13, %r14
    adcxq %r13, %r8
    adoxq %r14, %r9
    movq $0, %r13
    adcxq %r13, %r9
    adoxq %r13, %r9

    // Montgomery step 2.
    movq %r10, %rdx
    imulq -48(%rbp), %rdx
    mulxq -56(%rbp), %r13, %r14
    movq %rdx, %r15
    shlq $62, %r15
    negq %r10
    adcq %r13, %r11
    adcq $0, %r12
    adcq %r15, %r8
    adcq $0, %r9
    mulxq -64(%rbp), %r15, %r13
    movq %rdx, %r15
    shrq $2, %r15
    movq $0, %r10
    addq %r13, %r11
    adcq %r14, %r12
    adcq $0, %r8
    adcq %r15, %r9
    adcq $0, %r10

    // Round 3.
    movq 24(%rsi), %rdx
    xorq %r13, %r13
    mulxq %rax, %r13, %r14
    adcxq %r13, %r11
    adoxq %r14, %r12
    mulxq %rbx, %r13, %r14
    adcxq %r13, %r12
    adoxq %r14, %r8
    mulxq %rcx, %r13, %r14
    adcxq %r13, %r8
    adoxq %r14, %r9
    mulxq %rdi, %r13, %r14
    adcxq %r13, %r9
    adoxq %r14, %r10
    movq $0, %r13
    adcxq %r13, %r10
    adoxq %r13, %r10

    // Montgomery step 3.
    movq %r11, %rdx
    imulq -48(%rbp), %rdx
    mulxq -56(%rbp), %r13, %r14
    movq %rdx, %r15
    shlq $62, %r15
    negq %r11
    adcq %r13, %r12
    adcq $0, %r8
    adcq %r15, %r9
    adcq $0, %r10
    mulxq -64(%rbp), %r15, %r13
    movq %rdx, %r15
    shrq $2, %r15
    addq %r13, %r12
    adcq %r14, %r8
    adcq $0, %r9
    adcq %r15, %r10

    // The chain's sole conditional subtraction.
    movabsq $0x4000000000000000, %rdx
    movq %r12, %r13
    movq %r8, %r14
    movq %r9, %r15
    movq %r10, %r11
    subq -64(%rbp), %r13
    sbbq -56(%rbp), %r14
    sbbq $0, %r15
    sbbq %rdx, %r11
    cmovncq %r13, %r12
    cmovncq %r14, %r8
    cmovncq %r15, %r9
    cmovncq %r11, %r10

    movq -88(%rbp), %rdi
    movq %r12, (%rdi)
    movq %r8, 8(%rdi)
    movq %r9, 16(%rdi)
    movq %r10, 24(%rdi)
    jmp .Lreturn

.Lstore_lazy:
    movq -88(%rbp), %rdi
    movq %r11, (%rdi)
    movq %rbx, 8(%rdi)
    movq %r12, 16(%rdi)
    movq %rax, 24(%rdi)

.Lreturn:
    popq %rbx
    popq %r12
    popq %r13
    popq %r14
    popq %r15
    popq %rbp
    retq
    .cfi_endproc

#if !defined(__APPLE__)
    .size C_SYMBOL(pasta_x86_64_sqr_n), .-C_SYMBOL(pasta_x86_64_sqr_n)
    .section .note.GNU-stack,"",@progbits
#endif
