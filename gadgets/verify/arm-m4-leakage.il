macro eors2_leak (w32 op1, w32 op2)
{
  leak eorsCompResult (op1, op2, op1 ^w32 op2);
  leak eorsTransition (op1, op1 ^w32 op2);
}

macro ands2_leak (w32 op1, w32 op2)
{
  leak andsCompResult (op1, op2, op1 &w32 op2);
  leak andsTransition (op1, op1 &w32 op2);
}

macro ldr3_leak (w32 dst, w32 adr, w32 ofs)
  w32 val
{
  val <- [w32 mem (int) (adr +w32 ofs)];

  leak ldrCompResult(val, adr, ofs);
  leak ldrTransition(dst, val, adr, ofs);
}

macro ldrd3_leak (w32 dst1, w32 dst2, w32 adr)
  w32 adr_c
{ adr_c <- adr;
  ldr3_leak (dst1, adr_c, (w32) 0);
  ldr3_leak (dst2, adr_c, (w32) 0);
}


macro str3_leak (w32 val, w32 adr, w32 ofs)
{
  leak strCompResult (val);
}

macro strd3_leak (w32 op1, w32 op2, w32 adr)
{
  str3_leak(op1, adr, (w32) 0);
  str3_leak(op2, adr, (w32) 4);
}


macro mov2_leak (w32 dst, w32 src)
{
  leak movCompResult (src);
  leak movTransition (dst, src);
}

macro movs2_leak (w32 dst, w32 src)
{
  mov2_leak(dst, src);
}

macro adds3_leak (w32 dst, w32 op1, w32 op2)
{
  leak addsCompResult (op1, op2, op1 +w32 op2);
  leak addsTransition (dst, op1 +w32 op2);
}

macro add3_leak (w32 dst, w32 op1, w32 op2)
{
  leak addsCompResult (op1, op2, op1 +w32 op2);
  leak addsTransition (dst, op1 +w32 op2);
}

macro add2_leak (w32 op1, w32 op2)
{ adds3_leak(op1, op1, op2); }

macro adds2_leak (w32 op1, w32 op2)
{ adds3_leak(op1, op1, op2); }

macro addw3_leak (w32 dst, w32 op1, w32 op2)
{ add3_leak(dst, op1, op2); }

macro mvns2_leak (w32 dst, w32 src)
{
  leak movCompResult (src, !w32 src);
  leak movTransition (dst, !w32 src);
}

macro movw2_leak (w32 dst, w32 src)
{
  mov2_leak(dst, src);
}

macro ldrw3_leak (w32 dst, w32 adr, w32 ofs)
{
  ldr3_leak(dst, adr, ofs);
}

macro ldrw2_leak (w32 dst, w32 adr)
{
  ldrw3_leak(dst, adr, (w32) 0);
}

macro strw3_leak (w32 val, w32 adr, w32 ofs)
{
  str3_leak(val, adr, ofs);
}

macro strw2_leak (w32 val, w32 adr)
{
  strw3_leak(val, adr, (w32) 0);
}

macro andw3_leak (w32 dst, w32 op1, w32 op2)
{
  leak andsCompResult (op1, op2, op1 &w32 op2);
  leak andsTransition (dst, op1 &w32 op2);
}

macro eorw3_leak (w32 dst, w32 op1, w32 op2)
{
  leak eorsCompResult (op1, op2, op1 ^w32 op2);
  leak eorsTransition (dst, op1 ^w32 op2);
}

macro bicw3_leak (w32 dst, w32 op1, w32 op2)
{
  leak bicCompResult (op1, op2, op1 &w32 !w32 op2);
  leak bicTransition (dst, op1 &w32 !w32 op2);
}

macro lslw3_leak (w32 dst, w32 op1, w32 shift)
{
  leak lslCompResult (op1, shift, op1 <<w32 (uint) shift);
  leak lslTransition (dst, op1 <<w32 (uint) shift);
}

macro lsls3_leak (w32 dst, w32 op1, w32 shift)
{ lslw3_leak(dst, op1, shift); }

macro lsrw3_leak (w32 dst, w32 op1, w32 shift)
{
  leak lsrCompResult (op1, shift, op1 >>uw32 (uint) shift);
  leak lsrTransition (dst, op1 >>uw32 (uint) shift);
}

macro sub3_leak (w32 dst, w32 op1, w32 op2)
{
  leak subCompResult (op1, op2);
  leak subTransition (dst, op1, op2);
}

macro subw3_leak (w32 dst, w32 op1, w32 op2)
{ sub3_leak(dst, op1, op2); }

macro sub2_leak (w32 op1, w32 op2)
{ sub3_leak(op1, op1, op2); }

macro cmp2_leak (w32 op1, w32 op2)
{
  leak cmpCompResult (op1, op2, op1 -w32 op2);
}


macro bn1_leak (label l) {}
macro blen1_leak (label l) {}
macro bl1_leak (label l) {}
macro bx1_leak (w32 adr) {}
macro nop0_leak () {}

macro push1_leak (w32 op1)
{ leak strCompResult (op1); }

macro push2_leak (w32 op1, w32 op2)
{ leak strCompResult (op1); leak strCompResult (op2); }

macro push3_leak (w32 op1, w32 op2, w32 op3)
{ leak strCompResult (op1); leak strCompResult (op2); leak strCompResult (op3); }

macro push4_leak (w32 op1, w32 op2, w32 op3, w32 op4)
{ leak strCompResult (op1); leak strCompResult (op2); leak strCompResult (op3);
  leak strCompResult (op4); }

macro push5_leak (w32 op1, w32 op2, w32 op3, w32 op4, w32 op5)
{ leak strCompResult (op1); leak strCompResult (op2); leak strCompResult (op3);
  leak strCompResult (op4); leak strCompResult (op5); }

macro push6_leak (w32 op1, w32 op2, w32 op3, w32 op4, w32 op5, w32 op6)
{ leak strCompResult (op1); leak strCompResult (op2); leak strCompResult (op3);
  leak strCompResult (op4); leak strCompResult (op5); leak strCompResult (op6); }

macro push7_leak (w32 op1, w32 op2, w32 op3, w32 op4, w32 op5, w32 op6, w32 op7)
{ leak strCompResult (op1); leak strCompResult (op2); leak strCompResult (op3);
  leak strCompResult (op4); leak strCompResult (op5); leak strCompResult (op6);
  leak strCompResult (op7); }

macro push8_leak (w32 op1, w32 op2, w32 op3, w32 op4, w32 op5, w32 op6, w32 op7, w32 op8)
{ leak strCompResult (op1); leak strCompResult (op2); leak strCompResult (op3);
  leak strCompResult (op4); leak strCompResult (op5); leak strCompResult (op6);
  leak strCompResult (op7); leak strCompResult (op8); }

macro push9_leak (w32 op1, w32 op2, w32 op3, w32 op4, w32 op5, w32 op6, w32 op7, w32 op8, w32 op9)
{ leak strCompResult (op1); leak strCompResult (op2); leak strCompResult (op3);
  leak strCompResult (op4); leak strCompResult (op5); leak strCompResult (op6);
  leak strCompResult (op7); leak strCompResult (op8); leak strCompResult (op9); }

macro pop1_leak (w32 op1)
  w32 v1
{
  v1 <- [w32 mem (int) sp];
  leak ldrCompResult (v1, sp); leak ldrTransition (op1, v1, sp);
}

macro pop2_leak (w32 op1, w32 op2)
  w32 v1, w32 v2
{
  v1 <- [w32 mem (int) sp];
  v2 <- [w32 mem (int) (sp +w32 (w32) 4)];
  leak ldrCompResult (v1, sp); leak ldrTransition (op1, v1, sp);
  leak ldrCompResult (v2, sp); leak ldrTransition (op2, v2, sp);
}

macro pop3_leak (w32 op1, w32 op2, w32 op3)
  w32 v1, w32 v2, w32 v3
{
  v1 <- [w32 mem (int) sp];
  v2 <- [w32 mem (int) (sp +w32 (w32) 4)];
  v3 <- [w32 mem (int) (sp +w32 (w32) 8)];
  leak ldrCompResult (v1, sp); leak ldrTransition (op1, v1, sp);
  leak ldrCompResult (v2, sp); leak ldrTransition (op2, v2, sp);
  leak ldrCompResult (v3, sp); leak ldrTransition (op3, v3, sp);
}

macro pop4_leak (w32 op1, w32 op2, w32 op3, w32 op4)
  w32 v1, w32 v2, w32 v3, w32 v4
{
  v1 <- [w32 mem (int) sp];
  v2 <- [w32 mem (int) (sp +w32 (w32) 4)];
  v3 <- [w32 mem (int) (sp +w32 (w32) 8)];
  v4 <- [w32 mem (int) (sp +w32 (w32) 12)];
  leak ldrCompResult (v1, sp); leak ldrTransition (op1, v1, sp);
  leak ldrCompResult (v2, sp); leak ldrTransition (op2, v2, sp);
  leak ldrCompResult (v3, sp); leak ldrTransition (op3, v3, sp);
  leak ldrCompResult (v4, sp); leak ldrTransition (op4, v4, sp);
}

macro pop5_leak (w32 op1, w32 op2, w32 op3, w32 op4, w32 op5)
  w32 v1, w32 v2, w32 v3, w32 v4, w32 v5
{
  v1 <- [w32 mem (int) sp];
  v2 <- [w32 mem (int) (sp +w32 (w32) 4)];
  v3 <- [w32 mem (int) (sp +w32 (w32) 8)];
  v4 <- [w32 mem (int) (sp +w32 (w32) 12)];
  v5 <- [w32 mem (int) (sp +w32 (w32) 16)];
  leak ldrCompResult (v1, sp); leak ldrTransition (op1, v1, sp);
  leak ldrCompResult (v2, sp); leak ldrTransition (op2, v2, sp);
  leak ldrCompResult (v3, sp); leak ldrTransition (op3, v3, sp);
  leak ldrCompResult (v4, sp); leak ldrTransition (op4, v4, sp);
  leak ldrCompResult (v5, sp); leak ldrTransition (op5, v5, sp);
}

macro pop6_leak (w32 op1, w32 op2, w32 op3, w32 op4, w32 op5, w32 op6)
  w32 v1, w32 v2, w32 v3, w32 v4, w32 v5, w32 v6
{
  v1 <- [w32 mem (int) sp];
  v2 <- [w32 mem (int) (sp +w32 (w32) 4)];
  v3 <- [w32 mem (int) (sp +w32 (w32) 8)];
  v4 <- [w32 mem (int) (sp +w32 (w32) 12)];
  v5 <- [w32 mem (int) (sp +w32 (w32) 16)];
  v6 <- [w32 mem (int) (sp +w32 (w32) 20)];
  leak ldrCompResult (v1, sp); leak ldrTransition (op1, v1, sp);
  leak ldrCompResult (v2, sp); leak ldrTransition (op2, v2, sp);
  leak ldrCompResult (v3, sp); leak ldrTransition (op3, v3, sp);
  leak ldrCompResult (v4, sp); leak ldrTransition (op4, v4, sp);
  leak ldrCompResult (v5, sp); leak ldrTransition (op5, v5, sp);
  leak ldrCompResult (v6, sp); leak ldrTransition (op6, v6, sp);
}

macro pop7_leak (w32 op1, w32 op2, w32 op3, w32 op4, w32 op5, w32 op6, w32 op7)
  w32 v1, w32 v2, w32 v3, w32 v4, w32 v5, w32 v6, w32 v7
{
  v1 <- [w32 mem (int) sp];
  v2 <- [w32 mem (int) (sp +w32 (w32) 4)];
  v3 <- [w32 mem (int) (sp +w32 (w32) 8)];
  v4 <- [w32 mem (int) (sp +w32 (w32) 12)];
  v5 <- [w32 mem (int) (sp +w32 (w32) 16)];
  v6 <- [w32 mem (int) (sp +w32 (w32) 20)];
  v7 <- [w32 mem (int) (sp +w32 (w32) 24)];
  leak ldrCompResult (v1, sp); leak ldrTransition (op1, v1, sp);
  leak ldrCompResult (v2, sp); leak ldrTransition (op2, v2, sp);
  leak ldrCompResult (v3, sp); leak ldrTransition (op3, v3, sp);
  leak ldrCompResult (v4, sp); leak ldrTransition (op4, v4, sp);
  leak ldrCompResult (v5, sp); leak ldrTransition (op5, v5, sp);
  leak ldrCompResult (v6, sp); leak ldrTransition (op6, v6, sp);
  leak ldrCompResult (v7, sp); leak ldrTransition (op7, v7, sp);
}

macro pop8_leak (w32 op1, w32 op2, w32 op3, w32 op4, w32 op5, w32 op6, w32 op7, w32 op8)
  w32 v1, w32 v2, w32 v3, w32 v4, w32 v5, w32 v6, w32 v7, w32 v8
{
  v1 <- [w32 mem (int) sp];
  v2 <- [w32 mem (int) (sp +w32 (w32) 4)];
  v3 <- [w32 mem (int) (sp +w32 (w32) 8)];
  v4 <- [w32 mem (int) (sp +w32 (w32) 12)];
  v5 <- [w32 mem (int) (sp +w32 (w32) 16)];
  v6 <- [w32 mem (int) (sp +w32 (w32) 20)];
  v7 <- [w32 mem (int) (sp +w32 (w32) 24)];
  v8 <- [w32 mem (int) (sp +w32 (w32) 28)];
  leak ldrCompResult (v1, sp); leak ldrTransition (op1, v1, sp);
  leak ldrCompResult (v2, sp); leak ldrTransition (op2, v2, sp);
  leak ldrCompResult (v3, sp); leak ldrTransition (op3, v3, sp);
  leak ldrCompResult (v4, sp); leak ldrTransition (op4, v4, sp);
  leak ldrCompResult (v5, sp); leak ldrTransition (op5, v5, sp);
  leak ldrCompResult (v6, sp); leak ldrTransition (op6, v6, sp);
  leak ldrCompResult (v7, sp); leak ldrTransition (op7, v7, sp);
  leak ldrCompResult (v8, sp); leak ldrTransition (op8, v8, sp);
}

macro pop9_leak (w32 op1, w32 op2, w32 op3, w32 op4, w32 op5, w32 op6, w32 op7, w32 op8, w32 op9)
  w32 v1, w32 v2, w32 v3, w32 v4, w32 v5, w32 v6, w32 v7, w32 v8, w32 v9
{
  v1 <- [w32 mem (int) sp];
  v2 <- [w32 mem (int) (sp +w32 (w32) 4)];
  v3 <- [w32 mem (int) (sp +w32 (w32) 8)];
  v4 <- [w32 mem (int) (sp +w32 (w32) 12)];
  v5 <- [w32 mem (int) (sp +w32 (w32) 16)];
  v6 <- [w32 mem (int) (sp +w32 (w32) 20)];
  v7 <- [w32 mem (int) (sp +w32 (w32) 24)];
  v8 <- [w32 mem (int) (sp +w32 (w32) 28)];
  v9 <- [w32 mem (int) (sp +w32 (w32) 32)];
  leak ldrCompResult (v1, sp); leak ldrTransition (op1, v1, sp);
  leak ldrCompResult (v2, sp); leak ldrTransition (op2, v2, sp);
  leak ldrCompResult (v3, sp); leak ldrTransition (op3, v3, sp);
  leak ldrCompResult (v4, sp); leak ldrTransition (op4, v4, sp);
  leak ldrCompResult (v5, sp); leak ldrTransition (op5, v5, sp);
  leak ldrCompResult (v6, sp); leak ldrTransition (op6, v6, sp);
  leak ldrCompResult (v7, sp); leak ldrTransition (op7, v7, sp);
  leak ldrCompResult (v8, sp); leak ldrTransition (op8, v8, sp);
  leak ldrCompResult (v9, sp); leak ldrTransition (op9, v9, sp);
}
