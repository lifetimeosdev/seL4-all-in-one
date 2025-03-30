#define BEGIN_FUNC(_name) \
    .global _name ; \
    .type _name, %function ; \
_name:

#define END_FUNC(_name) \
    .size _name, .-_name

.macro lsp_i _tmp
    mrs     \_tmp, tpidr_el1
    mov     sp, \_tmp
.endm

.macro ventry label
.align 7
    b       \label
.endm

BEGIN_FUNC(arm_vector_table)

    ventry  invalid_vector_entry           // Synchronous EL1t/EL2t
    ventry  invalid_vector_entry           // IRQ EL1t/EL2t
    ventry  invalid_vector_entry           // FIQ EL1t/EL2t
    ventry  invalid_vector_entry           // SError EL1t/EL2t

    ventry  cur_el_sync                    // Current EL Synchronous (EL1/2)
    ventry  cur_el_irq                     // IRQ
    ventry  invalid_vector_entry           // FIQ
    ventry  cur_el_serr                    // SError

    ventry  lower_el_sync                  // Synchronous 64-bit EL0/EL1
    ventry  lower_el_irq                   // IRQ 64-bit EL0/EL1
    ventry  invalid_vector_entry           // FIQ 64-bit EL0/EL1
    ventry  lower_el_serr                  // SError 64-bit EL0/EL1

    ventry  invalid_vector_entry           // Synchronous 32-bit EL0/EL1
    ventry  invalid_vector_entry           // IRQ 32-bit EL0/EL1
    ventry  invalid_vector_entry           // FIQ 32-bit EL0/EL1
    ventry  invalid_vector_entry           // SError 32-bit EL0/EL1

END_FUNC(arm_vector_table)

.section .vectors.text

.macro kernel_enter
    /* Storing thread's stack frame */
    stp     x0,  x1,  [sp, #16 * 0]
    stp     x2,  x3,  [sp, #16 * 1]
    stp     x4,  x5,  [sp, #16 * 2]
    stp     x6,  x7,  [sp, #16 * 3]
    stp     x8,  x9,  [sp, #16 * 4]
    stp     x10, x11, [sp, #16 * 5]
    stp     x12, x13, [sp, #16 * 6]
    stp     x14, x15, [sp, #16 * 7]
    stp     x16, x17, [sp, #16 * 8]
    stp     x18, x19, [sp, #16 * 9]
    stp     x20, x21, [sp, #16 * 10]
    stp     x22, x23, [sp, #16 * 11]
    stp     x24, x25, [sp, #16 * 12]
    stp     x26, x27, [sp, #16 * 13]
    stp     x28, x29, [sp, #16 * 14]

    /* Store thread's SPSR, LR, and SP */
    mrs     x21, sp_el0
    mrs     x22, elr_el1
    mrs     x23, spsr_el1
    stp     x30, x21, [sp, #(30*8)]
    stp     x22, x23, [sp, #(32*8)]
.endm

BEGIN_FUNC(invalid_vector_entry)
    lsp_i   x19
    b       halt
END_FUNC(invalid_vector_entry)

BEGIN_FUNC(cur_el_sync)
    lsp_i   x19
    /* Read esr and branch to respective labels */
    mrs     x25, esr_el1
    lsr     x24, x25, #26
    cmp     x24, #0x25
    b.eq    cur_el_da
    cmp     x24, #0x21
    b.eq    cur_el_ia
    b       cur_el_inv

cur_el_da:
    mrs     x0, elr_el1
    bl      kernelDataAbort
    b       halt

cur_el_ia:
    mrs     x0, elr_el1
    bl      kernelPrefetchAbort
    b       halt

cur_el_inv:
    b       invalid_vector_entry
END_FUNC(cur_el_sync)

/*
 * This is only called if ksCurThread is idle thread.
 *
 * No need to store the state of idle thread and simply call c_handle_interrupt to
 * activate ksCurThread when returning from interrupt as long as idle thread is stateless.
 */
BEGIN_FUNC(cur_el_irq)
    lsp_i   x19
    b       c_handle_interrupt
END_FUNC(cur_el_irq)

BEGIN_FUNC(cur_el_serr)
    b       invalid_vector_entry
END_FUNC(cur_el_serr)

BEGIN_FUNC(lower_el_sync)
    kernel_enter

    /* Read esr and branch to respective labels */
    mrs     x25, esr_el1
    lsr     x24, x25, #26
    cmp     x24, #0x24
    b.eq    lel_da
    cmp     x24, #0x20
    b.eq    lel_ia
    cmp     x24, #0x15
    b.eq    lel_syscall

    cmp     x24, #0x7
    b.eq    el0_enfp
    b       el0_user

lel_da:
    mrs     x20, elr_el1
    str     x20, [sp, #(34*8)]

    lsp_i   x19
    b       c_handle_data_fault

lel_ia:
    mrs     x20, elr_el1
    str     x20, [sp, #(34*8)]

    lsp_i   x19
    b       c_handle_instruction_fault

lel_syscall:
    mrs     x20, elr_el1
    sub     x20, x20, #4
    str     x20, [sp, #(34*8)]

    lsp_i   x19

    cmp     x7, #(-1)
    b.eq    c_handle_fastpath_call
    cmp     x7, #(-1)
    b.eq    c_handle_fastpath_reply_recv

    mov     x2, x7
    b       c_handle_syscall

el0_enfp:
    lsp_i   x19
    b       c_handle_enfp

el0_user:
    mrs     x20, elr_el1
    str     x20, [sp, #(34*8)]

    lsp_i   x19
    b       c_handle_undefined_instruction
END_FUNC(lower_el_sync)

BEGIN_FUNC(lower_el_irq)
    kernel_enter
    mrs     x20, elr_el1
    str     x20, [sp, #(34*8)]

    lsp_i   x19
    b       c_handle_interrupt
END_FUNC(lower_el_irq)

BEGIN_FUNC(lower_el_serr)
    b       invalid_vector_entry
END_FUNC(lower_el_serr)


BEGIN_FUNC(lockTLBEntry)
    ret
END_FUNC(lockTLBEntry)
