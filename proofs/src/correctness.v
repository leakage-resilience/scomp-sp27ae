(* -------------------------------------------------------------------------- *)
(* Compiler correctness *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From Coq.Bool Require Import Bool.
From mathcomp Require Import all_ssreflect.

Require Import
  language
  utils
  utils_facts
  safety
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

(* -------------------------------------------------------------------------- *)

Section CORRECTNESS.

Context
  {input : Type}
  {output : Type}
  {Ls Lt : Language input output}
  {compile : compiler (input := input) (Ls := Ls) (Lt := Lt)}
.

Definition compile_correct : Prop :=
  forall p_s p_t inp ots_s ovs_s out_s,
    compile p_s = Some p_t ->
    forall (Hsem_s : bsem_p p_s inp ots_s ovs_s out_s),
    exists ots_t ovs_t out_t (Hsem_t : bsem_p p_t inp ots_t ovs_t out_t),
      outputs p_s out_s (bsem_p_final Hsem_s)
      = outputs p_t out_t (bsem_p_final Hsem_t).

End CORRECTNESS.
