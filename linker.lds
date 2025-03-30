ENTRY(_start)
KERNEL_OFFSET = ((0x0000008000000000 - 0x0) + 0x60000000) - 0x60000000;
SECTIONS
{
    . = ((0x0000008000000000 - 0x0) + 0x60000000);
    .boot . : AT(ADDR(.boot) - KERNEL_OFFSET)
    {
        *(.boot.text)
        *(.boot.rodata)
        *(.boot.data)
        . = ALIGN(64K);
    }
    ki_boot_end = .;
    .text . : AT(ADDR(.text) - KERNEL_OFFSET)
    {
        /* Sit inside a large frame */
        . = ALIGN(64K);
        *(.vectors)
        /* Fastpath code */
        *(.vectors.fastpath_call)
        *(.vectors.fastpath_reply_recv)
        *(.vectors.text)
        /* Anything else that should be in the vectors page. */
        *(.vectors.*)
        /* Hopefully all that fits into 4K! */
        /* Standard kernel */
        *(.text)
    }
    .rodata . : AT(ADDR(.rodata) - KERNEL_OFFSET)
    {
        *(.rodata)
        *(.rodata.*)
    }
    .data . : AT(ADDR(.data) - KERNEL_OFFSET)
    {
        *(.data)
    }
    .bss . : AT(ADDR(.bss) - KERNEL_OFFSET)
    {
        *(.bss)
        *(COMMON) /* fallback in case '-fno-common' is not used */
        /* 4k breakpoint stack */
        _breakpoint_stack_bottom = .;
        . = . + 4K;
        _breakpoint_stack_top = .;
        /* large data such as the globals frame and global PD */
        *(.bss.aligned)
    }
    . = ALIGN(4K);
    ki_end = .;
    /DISCARD/ :
    {
        *(.note.gnu.build-id)
        *(.comment)
    }
}
