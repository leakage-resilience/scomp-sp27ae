ENTRY(start)

/* The virt chip is pretty much undocumented but I found the relevant sections here:
       https://github.com/qemu/qemu/blob/b6df314a4ed91a0d02862a4a081dbe4d7b67b8e3/hw/arm/virt.c */

SECTIONS
{
    /* We use the -kernel, so the entrypoint is in ram which 
       starts at 0x40000000 (see virt.c) but the kernel entrypoint
       is at an offset of 0x00010000. See KERNEL_LOAD_ADDR in 
         https://github.com/qemu/qemu/blob/b6df314a4ed91a0d02862a4a081dbe4d7b67b8e3/hw/arm/boot.c#L164
       flash.s may not be thumb!!!!! */

    . = 0x40000000 + 0x00010000;
    .text : {
      KEEP(*flash.s.o(.text))
      *(.text*)
    }
    . = ALIGN(0x1000);
    .rodata : { *(.rodata*) }
    .data : { *(.data*) }
    .bss : { *(.bss COMMON) }
   __stack_top__ = 0x80000000;
}
