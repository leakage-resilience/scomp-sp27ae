(* -------------------------------------------------------------------------- *)
(* Composition of compiler preserves_obs and preserves obs. *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From Coq.Bool Require Import Bool.
From mathcomp Require Import all_ssreflect.

Require Import
  language
  semantics_facts
  utils
  utils_facts
  safety
  preservation_obs
  ni_preservation
  correctness
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

(* -------------------------------------------------------------------------- *)

Section PASS_COMPOSITION.

Context
  {input : Type}
  {output : Type}
  {L1 L2 L3 : Language input output}
  {c1: compiler (input := input) (Ls := L1) (Lt := L2)}
  {c2: compiler (input := input) (Ls := L2) (Lt := L3)}
.

Definition cc (p1: prog (L := L1)) :=
  match c1 p1 with
  | Some p2 => c2 p2
  | None => None
  end.

Lemma compose_intermediate (p1: prog (L := L1)) (p3 : prog (L := L3)) :
  cc p1 = Some p3 -> exists p2, c1 p1 = Some p2 /\ c2 p2 = Some p3.
Proof.
  rewrite /cc.
  case (c1 p1) => [p2 H|//].
  by exists p2.
Qed.

Lemma compile_correct_compose :
  @compile_correct input output L1 L2 c1 ->
  @compile_correct input output L2 L3 c2 ->
  @compile_correct input output L1 L3 cc.
Proof.
  move => Hcc1 Hcc2.
  move => p1 p3 inp ots1 ovs1 out1 Hc Hsem1.
  case: (compose_intermediate Hc) => p2 [] Hc1 Hc2.
  move: (Hcc1 p1 p2 inp ots1 ovs1 out1 Hc1 Hsem1) => [] ots2 [] ovs2 [] out2 [] Hsem2 Hout1.
  move: (Hcc2 p2 p3 inp ots2 ovs2 out2 Hc2 Hsem2) => [] ots3 [] ovs3 [] out3 [] Hsem3 Hout2.
  exists ots3, ovs3, out3, Hsem3.
  by rewrite Hout1 Hout2.
Qed.

Context
  {simT1 : SimT (Ls := L1) (Lt := L2)}
  {simT2 : SimT (Ls := L2) (Lt := L3)}
  {simVIdx1 : SimVIdx (Ls := L1)}
  {simVIdx2 : SimVIdx (Ls := L2)}
  {simV1 : SimV (Ls := L1) (Lt := L2)}
  {simV2 : SimV (Ls := L2) (Lt := L3)}
  .

Definition simT p1 ots1 :=
  match c1 p1 with
  | Some p2 =>
      let ots2 := simT1 p1 ots1 in
      simT2 p2 ots2
  | None => [::]
  end.

Definition simVIdx p1 ots1 i3 :=
  match c1 p1 with
  | Some p2 =>
      let ots2 := simT1 p1 ots1 in
      let i2 := simVIdx2 p2 ots2 i3 in
      simVIdx1 p1 ots1 i2
  | None => O
  end.

Definition simV p1 ots1 i3 ov1 :=
  match c1 p1 with
  | Some p2 =>
      let ots2 := simT1 p1 ots1 in
      let i2 := simVIdx2 p2 ots2 i3 in
      let ov2 := simV1 p1 ots1 i2 ov1 in
      simV2 p2 ots2 i3 ov2
  | None => v_dummy_observation
  end.

Lemma preserves_obs_compose :
  @preserves_obs input output L1 L2 c1 simT1 simVIdx1 simV1 ->
  @preserves_obs input output L2 L3 c2 simT2 simVIdx2 simV2 ->
  @preserves_obs input output L1 L3 cc simT simVIdx simV.
Proof.
  move => Hp1 Hp2.
  move => p1 p3 inp ots1 ovs1 out1 Hc Hsem1.
  case: (compose_intermediate Hc) => p2 [] Hc1 Hc2.
  move: (Hp1 p1 p2 inp ots1 ovs1 out1 Hc1 Hsem1) => [] ots2 [] ovs2 [] out2 [] Hsem2 Hots2 Hovs2.
  move: (Hp2 p2 p3 inp ots2 ovs2 out2 Hc2 Hsem2) => [] ots3 [] ovs3 [] out3 [] Hsem3 Hots3 Hovs3.
  exists ots3, ovs3, out3.
  split; first by apply Hsem3.
  + by rewrite /simT Hc1 -Hots2 -Hots3.
  move => i_t /=.
  by rewrite /simVIdx /simV Hc1 -Hovs2 -Hots2 -Hovs3.
Qed.

End PASS_COMPOSITION.
