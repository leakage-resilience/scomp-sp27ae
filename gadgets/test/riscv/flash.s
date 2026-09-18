  .text
  .global start
  .global qemu_exit

start:
    la sp, __stack_top__
    j entry


.equ QEMU_TEST_BASE, 0x100000
.equ QEMU_EXIT_FAILURE, 0x3333
.equ QEMU_EXIT_SUCCESS, 0x5555
.equ QEMU_EXIT_RESET, 0x7777
.equ QEMU_EXIT_SHIFT, 16

qemu_exit:
    beqz a0, _qemu_exit__success

_qemu_exit__failure:
    sll a0, a0, QEMU_EXIT_SHIFT
    li t0, QEMU_EXIT_FAILURE
    or a0, a0, t0
    li t0, QEMU_TEST_BASE
    sw a0, 0(t0)
    j halt

_qemu_exit__success:
    li t0, QEMU_TEST_BASE
    li a0, QEMU_EXIT_SUCCESS
    sw a0, 0(t0)
    j halt

halt: j halt
