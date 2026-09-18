macro add3_leak (w32 dst, w32 op1, w32 op2)
{
  leak addCompResult (op1, op2, op1 +w32 op2);
  leak addTransition (dst, op1 +w32 op2);
}

macro and3_leak (w32 dst, w32 op1, w32 op2)
{
  leak andCompResult (op1, op2, op1 &w32 op2);
  leak andTransition (dst, op1 &w32 op2);
}

macro xor3_leak (w32 dst, w32 op1, w32 op2)
{
  leak xorCompResult (op1, op2, op1 ^w32 op2);
  leak xorTransition (dst, op1 ^w32 op2);
}

macro sll3_leak (w32 dst, w32 op1, w32 op2)
{
  leak sllCompResult (op1, op2, op1 <<w32 (uint) op2);
  leak sllTransition (dst, op1 <<w32 (uint) op2);
}

macro srl3_leak (w32 dst, w32 op1, w32 op2)
{
  leak srlCompResult (op1, op2, op1 >>uw32 (uint) op2);
  leak srlTransition (dst, op1 >>uw32 (uint) op2);
}

macro addi3_leak (w32 dst, w32 op1, w32 imm)
{
  leak addCompResult (op1, imm, op1 +w32 imm);
  leak addTransition (dst, op1 +w32 imm);
}

macro andi3_leak (w32 dst, w32 op1, w32 imm)
{
  leak andCompResult (op1, imm, op1 &w32 imm);
  leak andTransition (dst, op1 &w32 imm);
}

macro slli3_leak (w32 dst, w32 op1, w32 imm)
{
  leak sllCompResult (op1, imm, op1 <<w32 (uint) imm);
  leak sllTransition (dst, op1 <<w32 (uint) imm);
}

macro srli3_leak (w32 dst, w32 op1, w32 imm)
{
  leak srlCompResult (op1, imm, op1 >>uw32 (uint) imm);
  leak srlTransition (dst, op1 >>uw32 (uint) imm);
}

// `not rd, rs` is pseudo for `xori rd, rs, -1`.
macro not2_leak (w32 dst, w32 op)
{
  leak notCompResult (op, !w32 op);
  leak notTransition (dst, !w32 op);
}

macro mv2_leak (w32 dst, w32 op)
{
  leak movCompResult (op);
  leak movTransition (dst, op);
}

macro li2_leak (w32 dst, w32 imm)
{
  leak movCompResult (imm);
  leak movTransition (dst, imm);
}

macro auipc2_leak (w32 dst, w32 imm)
{
  leak movCompResult (imm);
  leak movTransition (dst, pc +w32 (imm <<w32 (uint) 12));
}

macro lw3_leak (w32 dst, w32 ofs, w32 adr)
  w32 val
{
  val <- [w32 mem (int) (adr +w32 ofs)];
  leak ldrCompResult (val, adr, ofs);
  leak ldrTransition (dst, val, adr, ofs);
}

macro sw3_leak (w32 val, w32 ofs, w32 adr)
{
  leak strCompResult (val);
}

macro jal2_leak (w32 lr, label dst) {}
macro jalr3_leak (w32 lr, w32 dst, w32 ofs) {}
macro jalr1_leak (w32 dst) {}
macro ret0_leak () {}
