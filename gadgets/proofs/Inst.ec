require Gadgets.

require import Array2 Array1.

require import
  Array2 Array3 Array8 Array12 WArray8 WArray12 ArrayWords8W8 ArrayWords12W8
  ArrayWords2W32 ArrayWords3W32 SubArrayDirect8W8_2W32 SubArrayDirect12W8_3W32
  SubArrayDirect2W32_8W8 SubArrayDirect3W32_12W8.

require import
  Array3 Array4 Array6 Array12 Array24 WArray12 WArray16 WArray24
  ArrayWords12W8 ArrayWords24W8 ArrayWords3W32 ArrayWords6W32
  SubArrayDirect12W8_3W32 SubArrayDirect24W8_6W32 SubArrayDirect3W32_12W8
  SubArrayDirect6W32_24W8.

require import
  Array4 Array5 Array10 Array16 Array40 WArray16 WArray20 WArray40
  ArrayWords16W8 ArrayWords40W8 ArrayWords4W32 ArrayWords10W32
  SubArrayDirect16W8_4W32 SubArrayDirect40W8_10W32 SubArrayDirect4W32_16W8
  SubArrayDirect10W32_40W8.


(* TODO: shift, inplace, not *)

theory InstOrder1.
  require import Order1.
  clone import Gadgets
  with
    op order <- 1,
    op RandAndSize <- 1,
    theory ArrayN <- Array2,
    theory ArrayPN <- Array1,
    theory ArrayRandAnd <- Array1
  proof ge0_order' by done.

  equiv n_rec_correct:
    M(Syscall).lm_reconstruct ~ MSpec._g_reconstruct : ={arg} ==> ={res}.
  proc. inline. sim. qed.

  equiv n_g_share_correct:
    M(Syscall)._g_share ~ MSpec._g_share : ={arg} ==> ={res}.
  proc. auto. while (={i, inc, randomness, x, res_0}); auto. qed.

  equiv n_share_correct:
    M(Syscall).lm_share_derand ~ MSpec._g_share : ={arg} ==> ={res}.
  proof.
    transitivity M(Syscall)._g_share (={arg} ==> ={res}) (={arg} ==> ={res}).
    progress. by exists arg{2}. auto.
    proc; inline; sim.
    exact n_g_share_correct.
  qed.

  equiv n_xor_correct:
    M(Syscall).lm_xor ~ MSpec._g_xor : ={arg} ==> ={res}.
  proc. inline. sim. qed.

  equiv n_g_and_correct:
    M(Syscall)._g_and ~ MSpec._g_and : ={arg} ==> ={res}.
  proc. auto.
    while(={i, inc, rand_counter, randomness, a, b, c}); auto.
    while(={i, j, inc_0, rand_counter, randomness, a, b, c}); auto.
    while(={i, inc, rand_counter, randomness, a, b, c}); auto.
  qed.

  equiv n_and_correct:
    M(Syscall).lm_and_derand ~ MSpec._g_and : ={arg} ==> ={res}.
  proof.
    transitivity M(Syscall)._g_and (={arg} ==> ={res}) (={arg} ==> ={res}).
    progress. by exists arg{2}. auto.
    proc; inline; sim.
    exact n_g_and_correct.
  qed.

  equiv n_ref_correct:
    M(Syscall).lm_ref_derand ~ MSpec._g_ref : ={arg} ==> ={res}.
  proc. inline M(Syscall)._g_ref. auto. call n_g_and_correct. sim. qed.
end InstOrder1.


theory InstOrder2.
  require import Order2.
  clone import Gadgets
  with
    op order <- 2,
    op RandAndSize <- 3,
    theory ArrayN <- Array3,
    theory ArrayPN <- Array2,
    theory ArrayRandAnd <- Array3
  proof ge0_order' by done.

    equiv n_rec_correct:
    M(Syscall).lm_reconstruct ~ MSpec._g_reconstruct : ={arg} ==> ={res}.
  proc. inline. sim. qed.

  equiv n_g_share_correct:
    M(Syscall)._g_share ~ MSpec._g_share : ={arg} ==> ={res}.
  proc. auto. while (={i, inc, randomness, x, res_0}); auto. qed.

  equiv n_share_correct:
    M(Syscall).lm_share_derand ~ MSpec._g_share : ={arg} ==> ={res}.
  proof.
    transitivity M(Syscall)._g_share (={arg} ==> ={res}) (={arg} ==> ={res}).
    progress. by exists arg{2}. auto.
    proc; inline; sim.
    exact n_g_share_correct.
  qed.

  equiv n_xor_correct:
    M(Syscall).lm_xor ~ MSpec._g_xor : ={arg} ==> ={res}.
  proc. inline. sim. qed.

  equiv n_g_and_correct:
    M(Syscall)._g_and ~ MSpec._g_and : ={arg} ==> ={res}.
  proc. auto.
    while(={i, inc, rand_counter, randomness, a, b, c}); auto.
    while(={i, j, inc_0, rand_counter, randomness, a, b, c}); auto.
    while(={i, inc, rand_counter, randomness, a, b, c}); auto.
  qed.

  equiv n_and_correct:
    M(Syscall).lm_and_derand ~ MSpec._g_and : ={arg} ==> ={res}.
  proof.
    transitivity M(Syscall)._g_and (={arg} ==> ={res}) (={arg} ==> ={res}).
    progress. by exists arg{2}. auto.
    proc; inline; sim.
    exact n_g_and_correct.
  qed.

  equiv n_ref_correct:
    M(Syscall).lm_ref_derand ~ MSpec._g_ref : ={arg} ==> ={res}.
  proc. inline M(Syscall)._g_ref. auto. call n_g_and_correct. sim. qed.
end InstOrder2.


theory InstOrder3.
  require import Order3.
  clone import Gadgets
  with
    op order <- 3,
    op RandAndSize <- 6,
    theory ArrayN <- Array4,
    theory ArrayPN <- Array3,
    theory ArrayRandAnd <- Array6
  proof ge0_order' by done.

    equiv n_rec_correct:
    M(Syscall).lm_reconstruct ~ MSpec._g_reconstruct : ={arg} ==> ={res}.
  proc. inline. sim. qed.

  equiv n_g_share_correct:
    M(Syscall)._g_share ~ MSpec._g_share : ={arg} ==> ={res}.
  proc. auto. while (={i, inc, randomness, x, res_0}); auto. qed.

  equiv n_share_correct:
    M(Syscall).lm_share_derand ~ MSpec._g_share : ={arg} ==> ={res}.
  proof.
    transitivity M(Syscall)._g_share (={arg} ==> ={res}) (={arg} ==> ={res}).
    progress. by exists arg{2}. auto.
    proc; inline; sim.
    exact n_g_share_correct.
  qed.

  equiv n_xor_correct:
    M(Syscall).lm_xor ~ MSpec._g_xor : ={arg} ==> ={res}.
  proc. inline. sim. qed.

  equiv n_g_and_correct:
    M(Syscall)._g_and ~ MSpec._g_and : ={arg} ==> ={res}.
  proc. auto.
    while(={i, inc, rand_counter, randomness, a, b, c}); auto.
    while(={i, j, inc_0, rand_counter, randomness, a, b, c}); auto.
    while(={i, inc, rand_counter, randomness, a, b, c}); auto.
  qed.

  equiv n_and_correct:
    M(Syscall).lm_and_derand ~ MSpec._g_and : ={arg} ==> ={res}.
  proof.
    transitivity M(Syscall)._g_and (={arg} ==> ={res}) (={arg} ==> ={res}).
    progress. by exists arg{2}. auto.
    proc; inline; sim.
    exact n_g_and_correct.
  qed.

  equiv n_ref_correct:
    M(Syscall).lm_ref_derand ~ MSpec._g_ref : ={arg} ==> ={res}.
  proc. inline M(Syscall)._g_ref. auto. call n_g_and_correct. sim. qed.
end InstOrder3.


theory InstOrder4.
  require import Order4.
  clone import Gadgets
  with
    op order <- 4,
    op RandAndSize <- 10,
    theory ArrayN <- Array5,
    theory ArrayPN <- Array4,
    theory ArrayRandAnd <- Array10
  proof ge0_order' by done.

    equiv n_rec_correct:
    M(Syscall).lm_reconstruct ~ MSpec._g_reconstruct : ={arg} ==> ={res}.
  proc. inline. sim. qed.

  equiv n_g_share_correct:
    M(Syscall)._g_share ~ MSpec._g_share : ={arg} ==> ={res}.
  proc. auto. while (={i, inc, randomness, x, res_0}); auto. qed.

  equiv n_share_correct:
    M(Syscall).lm_share_derand ~ MSpec._g_share : ={arg} ==> ={res}.
  proof.
    transitivity M(Syscall)._g_share (={arg} ==> ={res}) (={arg} ==> ={res}).
    progress. by exists arg{2}. auto.
    proc; inline; sim.
    exact n_g_share_correct.
  qed.

  equiv n_xor_correct:
    M(Syscall).lm_xor ~ MSpec._g_xor : ={arg} ==> ={res}.
  proc. inline. sim. qed.

  equiv n_g_and_correct:
    M(Syscall)._g_and ~ MSpec._g_and : ={arg} ==> ={res}.
  proc. auto.
    while(={i, inc, rand_counter, randomness, a, b, c}); auto.
    while(={i, j, inc_0, rand_counter, randomness, a, b, c}); auto.
    while(={i, inc, rand_counter, randomness, a, b, c}); auto.
  qed.

  equiv n_and_correct:
    M(Syscall).lm_and_derand ~ MSpec._g_and : ={arg} ==> ={res}.
  proof.
    transitivity M(Syscall)._g_and (={arg} ==> ={res}) (={arg} ==> ={res}).
    progress. by exists arg{2}. auto.
    proc; inline; sim.
    exact n_g_and_correct.
  qed.

  equiv n_ref_correct:
    M(Syscall).lm_ref_derand ~ MSpec._g_ref : ={arg} ==> ={res}.
  proc. inline M(Syscall)._g_ref. auto. call n_g_and_correct. sim. qed.
end InstOrder4.
