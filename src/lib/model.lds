SECTIONS
{
    .text : { *(.text .text.*) }
    .data : { *(.data .data.*) }
    .rodata : { *(.rodata .rodata.*) }
    .bss : { *(.bss .bss.*) }
}
