#define BEGIN_FUNC(_name) \
    .global _name ; \
    .type _name, %function ; \
_name:

#define END_FUNC(_name) \
    .size _name, .-_name

.section .boot.text
BEGIN_FUNC(_start)
    /* Save x4 and x5 so we don't clobber it */
    mov     x7, x4
    mov     x8, x5

    /* Make sure interrupts are disable */
    msr daifset, #0xf

    /* Initialise sctlr_el1 or sctlr_el2 register */
    msr     spsel, #1
    mrs     x4, sctlr_el2
    ldr     x19, =0x8060000058
    ldr     x20, =0x8060000060
    orr     x4, x4, x19
    bic     x4, x4, x20
    msr     sctlr_el2, x4

    ldr    x4, =0x8060000068
    mov    sp, x4

    /* Attempt to workaround any known ARM errata. */
    stp     x0, x1, [sp, #-16]!
    stp     x2, x3, [sp, #-16]!
    stp     x7, x8, [sp, #-16]!
    bl arm_errata
    ldp     x4, x5, [sp], #16
    ldp     x2, x3, [sp], #16
    ldp     x0, x1, [sp], #16

    /* Call bootstrapping implemented in C with parameters:
     *  x0: user image physical start address
     *  x1: user image physical end address
     *  x2: physical/virtual offset
     *  x3: user image virtual entry address
     *  x4: DTB physical address (0 if there is none)
     *  x5: DTB size (0 if there is none)
     */
    bl      init_kernel

    /* Restore the initial thread. Note that the function restore_user_context()
     * could technically also be called at the end of init_kernel() directly,
     * there is no need to return to the assembly code here at all. However, for
     * verification things are a lot easier when init_kernel() is a normal C
     * function that returns. The function restore_user_context() is not a
     * normal C function and thus handled specially in verification, it does
     * highly architecture specific things to exit to user mode.
     */
    b restore_user_context

END_FUNC(_start)
