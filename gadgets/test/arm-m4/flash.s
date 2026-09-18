  .text
  .global start
  .global qemu_exit

start:
    ldr r0, =__stack_top__
    mov sp, r0

    bl entry

  .thumb_func
qemu_exit:
# https://github.com/ARM-software/abi-aa/blob/main/semihosting/semihosting.rst#sys-exit-extended-0x20

    ldr r1,=_exit_data_success
    cmp r0, #0
    beq .skip
    ldr r1,=_exit_data_error
  .skip:

    ldr r0, =0x20
    HLT #0x3C

    b .

_exit_data_error:
  .word 0x20026
  .word 0x1

_exit_data_success:
  .word 0x20026
  .word 0x0
