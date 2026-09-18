OUTPUT_ARCH("riscv")
ENTRY(start)


/* see https://github.com/qemu/qemu/blob/b6df314a4ed91a0d02862a4a081dbe4d7b67b8e3/hw/riscv/virt.c */

SECTIONS
{
  . = 0x80000000; /* dram */
  .text : { 
      KEEP(*flash.s.o(.text))
    *(.text*)
  } 

  . = ALIGN(0x1000);
  .rodata : { *(.rodata*) }
  .data : { *(.data*) }
  .bss :{ *(.bss* .bss.*) }
  __stack_top__ = 0x100000000;

}