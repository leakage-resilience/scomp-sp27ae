// Copyright 2022 - NXP
// SPDX-License-Identifier: BSD-3-Clause-Clear WITH modifications

w32 x0;
w32 ra;
w32 sp;
w32 x3;
w32 x4;
w32 t0;
w32 t1;
w32 t2;
w32 t3;
w32 s0;
w32 s1;
w32 s2;
w32 a0;
w32 a1;
w32 a2;
w32 a3;
w32 a4;
w32 a5;
w32 a6;
w32 a7;

w32 pc;


mem [];

macro add3 (w32 dst, w32 op1, w32 op2)
{
  dst <- op1 +w32 op2;
  x0 <- (w32) 0;
}

macro and3 (w32 dst, w32 op1, w32 op2)
{
  dst <- op1 &w32 op2;
  x0 <- (w32) 0;
}

macro xor3 (w32 dst, w32 op1, w32 op2)
{
  dst <- op1 ^w32 op2;
  x0 <- (w32) 0;
}

macro addi3 (w32 dst, w32 op1, w32 imm)
{
  dst <- op1 +w32 imm;
  x0 <- (w32) 0;
}

macro andi3 (w32 dst, w32 op1, w32 imm)
{
  dst <- op1 &w32 imm;
  x0 <- (w32) 0;
}

macro sll3 (w32 dst, w32 op1, w32 op2)
{
  dst <- op1 <<w32 (uint) op2;
  x0 <- (w32) 0;
}

macro slli3 (w32 dst, w32 op1, w32 imm)
{
  dst <- op1 <<w32 (uint) imm;
  x0 <- (w32) 0;
}

macro srl3 (w32 dst, w32 op1, w32 op2)
{
  dst <- op1 >>uw32 (uint) op2;
  x0 <- (w32) 0;
}

macro srli3 (w32 dst, w32 op1, w32 imm)
{
  dst <- op1 >>uw32 (uint) imm;
  x0 <- (w32) 0;
}

macro not2 (w32 dst, w32 op)
{
  dst <- !w32 op;
  x0 <- (w32) 0;
}

macro li2 (w32 dst, w32 imm)
{
  dst <- imm;
  x0 <- (w32) 0;
}

macro auipc2 (w32 dst, w32 imm)
{
  dst <- pc +w32 (imm <<w32 (uint) 12);
  x0 <- (w32) 0;
}

macro mv2 (w32 dst, w32 op)
{
  addi3(dst, op, (w32) 0);
}

macro lw3 (w32 dst, w32 ofs, w32 adr)
{
  dst <- [w32 mem (int) (adr +w32 ofs)];
  x0 <- (w32) 0;
}

macro sw3 (w32 dst, w32 ofs, w32 adr)
{
  [w32 mem (int) (adr +w32 ofs)] <- dst;
}

macro jal2 (w32 lr, label dst)
{
  if (!(lr =name= x0)) {
    lr <- pc +w32 (w32) 4;
  }
  goto dst;
}

macro jalr3 (w32 lr, w32 dst, w32 ofs)
{
  if (!(lr =name= x0)) {
    lr <- pc +w32 (w32) 4;
  }
  pc <- dst +w32 ofs;
}

macro jalr1 (w32 dst)
{
  jalr3(ra, dst, (w32) 0);
}

macro ret0 ()
{
  jalr3(x0, ra, (w32) 0);
}