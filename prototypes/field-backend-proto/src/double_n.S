// Prototype 3: fused Jacobian point doubling (see lib docs).
// ---------------------------------------------------------------------------
// Prototype: fused Jacobian point doubling for Pallas (Fp), dbl-2009-l, a = 0.
//
//   _proto_double_n(x0 = xyz [12 little-endian limbs X,Y,Z in Montgomery
//   form, canonical], x1 = n >= 1)
//
// Doubles the point n times in place. All field values live in fixed stack
// slots; every field operation is a macro-inlined Montgomery routine (no
// calls, no ABI traffic). The field macro bodies are register-renamed
// transcriptions of the verified sqr_n_mul loop/tail in this file.
//
// Fixed registers: x26 = p[0], x27 = p[1], x28 = inv (Fp constants,
// materialized at entry). p[2] = 0 and p[3] = 2^62 are implicit.
// Macros use x4..x22; x0 = pointer, x1 = counter.
// ---------------------------------------------------------------------------

// Montgomery square: slot \src -> slot \dst (canonical in, canonical out).
.macro MSQR src, dst
    ldp x6,x7,[sp,#\src]
    ldp x8,x9,[sp,#(\src+16)]

    mul x11,x7,x6
    umulh x20,x7,x6
    mul x12,x8,x6
    umulh x21,x8,x6
    mul x13,x9,x6
    umulh x14,x9,x6
    adds x12,x12,x20
    mul x19,x8,x7
    umulh x20,x8,x7
    adcs x13,x13,x21
    mul x21,x9,x7
    umulh x22,x9,x7
    adc x14,x14,xzr
    mul x15,x9,x8
    umulh x16,x9,x8
    adds x20,x20,x21
    mul x10,x6,x6
    adc x21,x22,xzr
    adds x13,x13,x19
    umulh x6,x6,x6
    adcs x14,x14,x20
    mul x20,x7,x7
    adcs x15,x15,x21
    umulh x7,x7,x7
    adc x16,x16,xzr
    adds x11,x11,x11
    mul x21,x8,x8
    adcs x12,x12,x12
    umulh x8,x8,x8
    adcs x13,x13,x13
    mul x22,x9,x9
    adcs x14,x14,x14
    umulh x9,x9,x9
    adcs x15,x15,x15
    adcs x16,x16,x16
    adc x17,xzr,xzr
    mul x4,x28,x10
    adds x11,x11,x6
    adcs x12,x12,x20
    adcs x13,x13,x7
    adcs x14,x14,x21
    adcs x15,x15,x8
    adcs x16,x16,x22
    adc x17,x17,x9

    mul x20,x27,x4
    lsl x22,x4,#62
    subs xzr,x10,#1
    umulh x19,x26,x4
    adcs x11,x11,x20
    umulh x20,x27,x4
    adcs x12,x12,xzr
    adcs x13,x13,x22
    lsr x22,x4,#2
    adc x5,xzr,xzr
    adds x10,x11,x19
    adcs x11,x12,x20
    adcs x12,x13,xzr
    mul x4,x28,x10
    adc x13,x5,x22

    mul x20,x27,x4
    lsl x22,x4,#62
    subs xzr,x10,#1
    umulh x19,x26,x4
    adcs x11,x11,x20
    umulh x20,x27,x4
    adcs x12,x12,xzr
    adcs x13,x13,x22
    lsr x22,x4,#2
    adc x5,xzr,xzr
    adds x10,x11,x19
    adcs x11,x12,x20
    adcs x12,x13,xzr
    mul x4,x28,x10
    adc x13,x5,x22

    mul x20,x27,x4
    lsl x22,x4,#62
    subs xzr,x10,#1
    umulh x19,x26,x4
    adcs x11,x11,x20
    umulh x20,x27,x4
    adcs x12,x12,xzr
    adcs x13,x13,x22
    lsr x22,x4,#2
    adc x5,xzr,xzr
    adds x10,x11,x19
    adcs x11,x12,x20
    adcs x12,x13,xzr
    mul x4,x28,x10
    adc x13,x5,x22

    mul x20,x27,x4
    lsl x22,x4,#62
    subs xzr,x10,#1
    umulh x19,x26,x4
    adcs x11,x11,x20
    umulh x20,x27,x4
    adcs x12,x12,xzr
    adcs x13,x13,x22
    lsr x22,x4,#2
    adc x5,xzr,xzr
    adds x10,x11,x19
    adcs x11,x12,x20
    adcs x12,x13,xzr
    adc x13,x5,x22

    adds x6,x10,x14
    adcs x7,x11,x15
    adcs x8,x12,x16
    adc x9,x13,x17

    // Candidate < 1.25p for canonical input; one conditional subtraction.
    mov x4,#0x4000000000000000
    subs x10,x6,x26
    sbcs x11,x7,x27
    sbcs x12,x8,xzr
    sbcs x13,x9,x4
    csel x6,x6,x10,lo
    csel x7,x7,x11,lo
    csel x8,x8,x12,lo
    csel x9,x9,x13,lo
    stp x6,x7,[sp,#\dst]
    stp x8,x9,[sp,#(\dst+16)]
.endm

// Montgomery multiply: slot \a * slot \b -> slot \dst (canonical throughout).
.macro MMUL a, b, dst
    ldp x6,x7,[sp,#\a]
    ldp x8,x9,[sp,#(\a+16)]
    ldr x5,[sp,#\b]

    mul x10,x6,x5
    mul x11,x7,x5
    mul x12,x8,x5
    mul x13,x9,x5
    umulh x19,x6,x5
    umulh x20,x7,x5
    mul x4,x28,x10
    umulh x21,x8,x5
    umulh x22,x9,x5
    adds x11,x11,x19
    adcs x12,x12,x20
    mul x20,x27,x4
    adcs x13,x13,x21
    adc x14,xzr,x22
    lsl x22,x4,#62
    ldr x5,[sp,#(\b+8)]
    subs xzr,x10,#1
    umulh x19,x26,x4
    adcs x11,x11,x20
    umulh x20,x27,x4
    adcs x12,x12,xzr
    adcs x13,x13,x22
    lsr x22,x4,#2
    adc x14,x14,xzr

    adds x10,x11,x19
    mul x19,x6,x5
    adcs x11,x12,x20
    mul x20,x7,x5
    adcs x12,x13,xzr
    mul x21,x8,x5
    adcs x13,x14,x22
    mul x22,x9,x5
    adc x14,xzr,xzr

    adds x10,x10,x19
    umulh x19,x6,x5
    adcs x11,x11,x20
    umulh x20,x7,x5
    adcs x12,x12,x21
    mul x4,x28,x10
    umulh x21,x8,x5
    adcs x13,x13,x22
    umulh x22,x9,x5
    adc x14,x14,xzr
    adds x11,x11,x19
    adcs x12,x12,x20
    mul x20,x27,x4
    adcs x13,x13,x21
    adc x14,x14,x22
    lsl x22,x4,#62
    ldr x5,[sp,#(\b+16)]
    subs xzr,x10,#1
    umulh x19,x26,x4
    adcs x11,x11,x20
    umulh x20,x27,x4
    adcs x12,x12,xzr
    adcs x13,x13,x22
    lsr x22,x4,#2
    adc x14,x14,xzr

    adds x10,x11,x19
    mul x19,x6,x5
    adcs x11,x12,x20
    mul x20,x7,x5
    adcs x12,x13,xzr
    mul x21,x8,x5
    adcs x13,x14,x22
    mul x22,x9,x5
    adc x14,xzr,xzr

    adds x10,x10,x19
    umulh x19,x6,x5
    adcs x11,x11,x20
    umulh x20,x7,x5
    adcs x12,x12,x21
    mul x4,x28,x10
    umulh x21,x8,x5
    adcs x13,x13,x22
    umulh x22,x9,x5
    adc x14,x14,xzr
    adds x11,x11,x19
    adcs x12,x12,x20
    mul x20,x27,x4
    adcs x13,x13,x21
    adc x14,x14,x22
    lsl x22,x4,#62
    ldr x5,[sp,#(\b+24)]
    subs xzr,x10,#1
    umulh x19,x26,x4
    adcs x11,x11,x20
    umulh x20,x27,x4
    adcs x12,x12,xzr
    adcs x13,x13,x22
    lsr x22,x4,#2
    adc x14,x14,xzr

    adds x10,x11,x19
    mul x19,x6,x5
    adcs x11,x12,x20
    mul x20,x7,x5
    adcs x12,x13,xzr
    mul x21,x8,x5
    adcs x13,x14,x22
    mul x22,x9,x5
    adc x14,xzr,xzr

    adds x10,x10,x19
    umulh x19,x6,x5
    adcs x11,x11,x20
    umulh x20,x7,x5
    adcs x12,x12,x21
    mul x4,x28,x10
    umulh x21,x8,x5
    adcs x13,x13,x22
    umulh x22,x9,x5
    adc x14,x14,xzr
    adds x11,x11,x19
    adcs x12,x12,x20
    mul x20,x27,x4
    adcs x13,x13,x21
    adc x14,x14,x22
    lsl x22,x4,#62
    subs xzr,x10,#1
    umulh x19,x26,x4
    adcs x11,x11,x20
    umulh x20,x27,x4
    adcs x12,x12,xzr
    adcs x13,x13,x22
    lsr x22,x4,#2
    adc x14,x14,xzr

    adds x10,x11,x19
    adcs x11,x12,x20
    adcs x12,x13,xzr
    adc x13,x14,x22

    subs x19,x10,x26
    mov x22,#0x4000000000000000
    sbcs x20,x11,x27
    sbcs x21,x12,xzr
    sbcs x22,x13,x22
    csel x10,x10,x19,lo
    csel x11,x11,x20,lo
    csel x12,x12,x21,lo
    csel x13,x13,x22,lo
    stp x10,x11,[sp,#\dst]
    stp x12,x13,[sp,#(\dst+16)]
.endm

// Modular add: slot \a + slot \b -> slot \dst.
.macro MADDMOD a, b, dst
    ldp x6,x7,[sp,#\a]
    ldp x8,x9,[sp,#(\a+16)]
    ldp x10,x11,[sp,#\b]
    ldp x12,x13,[sp,#(\b+16)]
    adds x6,x6,x10
    adcs x7,x7,x11
    adcs x8,x8,x12
    adc x9,x9,x13
    mov x4,#0x4000000000000000
    subs x10,x6,x26
    sbcs x11,x7,x27
    sbcs x12,x8,xzr
    sbcs x13,x9,x4
    csel x6,x6,x10,lo
    csel x7,x7,x11,lo
    csel x8,x8,x12,lo
    csel x9,x9,x13,lo
    stp x6,x7,[sp,#\dst]
    stp x8,x9,[sp,#(\dst+16)]
.endm

// Modular double: 2 * slot \a -> slot \dst.
.macro MDBLMOD a, dst
    ldp x6,x7,[sp,#\a]
    ldp x8,x9,[sp,#(\a+16)]
    adds x6,x6,x6
    adcs x7,x7,x7
    adcs x8,x8,x8
    adc x9,x9,x9
    mov x4,#0x4000000000000000
    subs x10,x6,x26
    sbcs x11,x7,x27
    sbcs x12,x8,xzr
    sbcs x13,x9,x4
    csel x6,x6,x10,lo
    csel x7,x7,x11,lo
    csel x8,x8,x12,lo
    csel x9,x9,x13,lo
    stp x6,x7,[sp,#\dst]
    stp x8,x9,[sp,#(\dst+16)]
.endm

// Modular subtract: slot \a - slot \b -> slot \dst.
.macro MSUBMOD a, b, dst
    ldp x6,x7,[sp,#\a]
    ldp x8,x9,[sp,#(\a+16)]
    ldp x10,x11,[sp,#\b]
    ldp x12,x13,[sp,#(\b+16)]
    subs x6,x6,x10
    sbcs x7,x7,x11
    sbcs x8,x8,x12
    sbcs x9,x9,x13
    // On borrow (cc), add p back.
    mov x4,#0x4000000000000000
    csel x10,x26,xzr,cc
    csel x11,x27,xzr,cc
    csel x13,x4,xzr,cc
    adds x6,x6,x10
    adcs x7,x7,x11
    adcs x8,x8,xzr
    adc x9,x9,x13
    stp x6,x7,[sp,#\dst]
    stp x8,x9,[sp,#(\dst+16)]
.endm

// Stack slots (relative to sp after the frame is built).
#define SX 96
#define SY 128
#define SZ 160
#define S3 192
#define S4 224
#define S5 256

.globl _proto_double_n
.private_extern _proto_double_n

.align 5
_proto_double_n:
    stp x29,x30,[sp,#-288]!
    add x29,sp,#0
    stp x19,x20,[sp,#16]
    stp x21,x22,[sp,#32]
    stp x23,x24,[sp,#48]
    stp x25,x26,[sp,#64]
    stp x27,x28,[sp,#80]

    // Materialize Fp constants: p[0], p[1], inv.
    movz x26,#0x0001
    movk x26,#0x30ed,lsl#32
    movk x26,#0x992d,lsl#48
    movz x27,#0xf91b
    movk x27,#0x094c,lsl#16
    movk x27,#0x98fc,lsl#32
    movk x27,#0x2246,lsl#48
    movz x28,#0xffff
    movk x28,#0xffff,lsl#16
    movk x28,#0x30ec,lsl#32
    movk x28,#0x992d,lsl#48

    // Copy the point into the working slots.
    ldp x6,x7,[x0]
    ldp x8,x9,[x0,#16]
    stp x6,x7,[sp,#SX]
    stp x8,x9,[sp,#(SX+16)]
    ldp x6,x7,[x0,#32]
    ldp x8,x9,[x0,#48]
    stp x6,x7,[sp,#SY]
    stp x8,x9,[sp,#(SY+16)]
    ldp x6,x7,[x0,#64]
    ldp x8,x9,[x0,#80]
    stp x6,x7,[sp,#SZ]
    stp x8,x9,[sp,#(SZ+16)]

L$proto_double_loop:
    // dbl-2009-l with a = 0. Slots: SX=X, SY=Y, SZ=Z, S3/S4/S5 scratch.
    MSQR SY, S3            // B  = Y^2
    MSQR S3, S4            // C  = B^2
    MADDMOD SX, S3, S5     // t  = X + B
    MSQR SX, S3            // A  = X^2         (B dead; X dead after this)
    MMUL SY, SZ, SZ        // Y*Z              (Y dead after this)
    MDBLMOD SZ, SZ         // Z3 = 2*Y*Z
    MSQR S5, S5            // t^2
    MSUBMOD S5, S3, S5     // t^2 - A
    MSUBMOD S5, S4, S5     // t^2 - A - C
    MDBLMOD S5, S5         // D  = 2*(t^2 - A - C)
    MDBLMOD S3, SY         // 2A               (into dead Y slot)
    MADDMOD SY, S3, S3     // E  = 3A
    MSQR S3, SX            // F  = E^2         (into dead X slot)
    MSUBMOD SX, S5, SX     // F - D
    MSUBMOD SX, S5, SX     // X3 = F - 2D
    MSUBMOD S5, SX, S5     // D - X3
    MMUL S3, S5, SY        // E*(D - X3)       (into Y slot)
    MDBLMOD S4, S4         // 2C
    MDBLMOD S4, S4         // 4C
    MDBLMOD S4, S4         // 8C
    MSUBMOD SY, S4, SY     // Y3 = E*(D - X3) - 8C

    sub x1,x1,#1
    cbnz x1,L$proto_double_loop

    // Write the doubled point back.
    ldp x6,x7,[sp,#SX]
    ldp x8,x9,[sp,#(SX+16)]
    stp x6,x7,[x0]
    stp x8,x9,[x0,#16]
    ldp x6,x7,[sp,#SY]
    ldp x8,x9,[sp,#(SY+16)]
    stp x6,x7,[x0,#32]
    stp x8,x9,[x0,#48]
    ldp x6,x7,[sp,#SZ]
    ldp x8,x9,[sp,#(SZ+16)]
    stp x6,x7,[x0,#64]
    stp x8,x9,[x0,#80]

    ldp x19,x20,[x29,#16]
    ldp x21,x22,[x29,#32]
    ldp x23,x24,[x29,#48]
    ldp x25,x26,[x29,#64]
    ldp x27,x28,[x29,#80]
    ldp x29,x30,[sp],#288
    ret
