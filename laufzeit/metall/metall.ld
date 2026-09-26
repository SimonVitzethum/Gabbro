/* laufzeit/metall/metall.ld -- the image layout (Opus agent I, 2026-09-26).
 *
 * Loaded at 1 MiB, identity mapped (start.S maps the low 4 GiB 1:1), so every
 * virtual address is its physical address and `-mcmodel=small -fno-pie`
 * reaches every symbol. The Multiboot1 header is the first thing in `.text`,
 * well inside the first 8 KiB of the file the protocol searches. The AP
 * trampoline lives in `.text` like any code and is COPIED to 0x8000 at run
 * time (start.S `T(x)`), so no section needs a load address apart from its
 * run address. */
ENTRY(_start)

SECTIONS
{
    . = 1M;
    .text ALIGN(4096) : {
        KEEP(*(.multiboot))
        *(.text .text.*)
    }
    .rodata ALIGN(4096) : { *(.rodata .rodata.*) }
    .data ALIGN(4096) : { *(.data .data.*) }
    .bss ALIGN(4096) : { *(.bss .bss.*) *(COMMON) }
    /DISCARD/ : { *(.eh_frame) *(.note .note.*) *(.comment) }
}
