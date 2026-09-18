(* -------------------------------------------------------------------------- *)
(* Preservation of Non-Interference Notions *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From Coq.Bool Require Import Bool.
From mathcomp Require Import all_ssreflect.

Require Import
  language
  utils
  utils_facts
  safety
  preservation_obs
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

(* -------------------------------------------------------------------------- *)

Section PRESERVATION_NI.

Context
  {input : Type}
  {output : Type}
  {Ls Lt : Language input output}
  {compile : compiler (input := input) (Ls := Ls) (Lt := Lt)}
  {simT: @SimT input output Ls Lt}
  {simVIdx: @SimVIdx input output Ls}
  {simV: @SimV input output Ls Lt}
.

Definition constant_time {L: Language input output} (p: prog (L := L)) (pred: input -> Prop) :=
  exists ots, forall inp, pred inp -> exists ovs out, bsem_p p inp ots ovs out.

Lemma constant_time_impl {L: Language input output}
  (p: prog (L := L)) (pred1 pred2: input -> Prop) :
  (forall inp, pred1 inp -> pred2 inp) ->
  constant_time p pred2 ->
  constant_time p pred1.
Proof.
  move => H [] ots H2; exists ots => inp H1.
  by apply /H2 /H.
Qed.

Definition deterministic_ni
  {L: Language input output}
  (phi: seq nat -> relation input)
  (p: prog (L := L)) :
  Prop :=
  forall (probes: seq nat) inp1 inp2 ots1 ots2 ovs1 ovs2 out1 out2,
    phi probes inp1 inp2 ->
    bsem_p p inp1 ots1 ovs1 out1 ->
    bsem_p p inp2 ots2 ovs2 out2 ->
    ots1 = ots2 /\
      get_ovs ovs1 probes = get_ovs ovs2 probes.

Definition preserves_detni
  (p_s : prog (L := Ls)) (p_t : prog (L := Lt)) (phi_s: seq nat -> relation input): Prop :=
    deterministic_ni phi_s p_s ->
    exists (i_s: nat -> nat),
      let phi_t i_t := phi_s (map i_s i_t) in
      deterministic_ni phi_t p_t.

Lemma preserves_obs_detni:
  forall
    (p_s: prog (L := Ls))
    (p_t: prog (L := Lt))
    (phi: relation input)
    (phi_s: seq nat -> relation input),
    compile p_s = Some p_t ->
    preserves_obs_w (compile := compile) (simT := simT) (simVIdx := simVIdx) (simV := simV) ->
    (forall i, rel_implies (phi_s i) phi) ->
    constant_time p_s (any_rel phi) ->
    preserves_detni p_s p_t phi_s.
Proof.
  move => p_s p_t phi phi_s Hcompile Hpre Himpl [] ots_s Hsafe Hni.
  pose i_s_fun i := simVIdx p_s ots_s i.
  exists i_s_fun.
  move => /= i_t inp1 inp2 ots_t1 ots_t2 ovs_t1 ovs_t2 out_t1 out_t2 Hphi_s Hsem_t1 Hsem_t2.
  set (i_s := map i_s_fun i_t) in *.
  (* Get source executions *)
  have Hphi_rel1: any_rel phi inp1 by apply (any_rel_implies (Himpl i_s)); exists inp2; left.
  have Hphi_rel2: any_rel phi inp2 by apply (any_rel_implies (Himpl i_s)); exists inp1; right.
  move: (Hsafe _ Hphi_rel1) => [] ovs_s1 [] out_s1 Hsem_s1.
  move: (Hsafe _ Hphi_rel2) => [] ovs_s2 [] out_s2 Hsem_s2.
  clear Hphi_rel1 Hphi_rel2 Hsafe.
  (* Link source and target *)
  move: (Hni i_s inp1 inp2 ots_s ots_s ovs_s1 ovs_s2 out_s1 out_s2 Hphi_s Hsem_s1 Hsem_s2) => [] _ Hovs_s {Hni}.
  specialize (Hpre p_s p_t).
  move: (Hpre inp1 ots_s ovs_s1 out_s1 ots_t1 ovs_t1 out_t1 Hcompile Hsem_s1 Hsem_t1) => [] -> Hovs1.
  move: (Hpre inp2 ots_s ovs_s2 out_s2 ots_t2 ovs_t2 out_t2 Hcompile Hsem_s2 Hsem_t2) => [] -> Hovs2.
  clear Hpre Hsem_t1 Hsem_t2.
  split; first done.
  (* Value leakage *)
  rewrite -eq_in_map in Hovs_s.
  apply eq_in_map => probe_t hprobe_t.
  rewrite Hovs1 Hovs2 Hovs_s => //.
  by apply map_f.
Qed.

End PRESERVATION_NI.

Section PRESERVATION_SNI.

  Context
    {value : Type}
    {output : Type}
    {outshidx : Type}
    {get_outputshare : output -> outshidx -> value}.

  Context
    {input : Type}
      {Ls Lt : Language input output}
      {compile : compiler (input := input) (Ls := Ls) (Lt := Lt)}
      {simT: @SimT input output Ls Lt}
      {simVIdx: @SimVIdx input output Ls}
      {simV: @SimV input output Ls Lt}
  .

  Definition get_outputshares
    {L: Language input output} (output: output) (i: seq outshidx): seq value :=
    map (get_outputshare output) i.

  Definition deterministic_sni
    {L: Language input output}
    (phi: seq nat (* intprobes *) -> seq outshidx (* outprobes *) -> relation input)
    (p: prog (L := L)) :
    Prop :=
    forall (intprobes: seq nat) (outprobes: seq outshidx) inp1 inp2 ots1 ots2 ovs1 ovs2 out1 out2,
      phi intprobes outprobes inp1 inp2 ->
      forall (sem1: bsem_p p inp1 ots1 ovs1 out1)
             (sem2: bsem_p p inp2 ots2 ovs2 out2),
      [/\ ots1 = ots2
        , get_ovs ovs1 intprobes = get_ovs ovs2 intprobes
        & get_outputshares (outputs p out1 (bsem_p_final sem1)) outprobes = get_outputshares (outputs p out2 (bsem_p_final sem2)) outprobes
      ].

Definition preserves_detsni
  (p_s : prog (L := Ls))
  (p_t : prog (L := Lt))
  (phi_s: seq nat -> seq outshidx -> relation input)
  : Prop :=
  deterministic_sni phi_s p_s ->
  exists (i_s: nat -> nat),
    let phi_t i_t := phi_s (map i_s i_t) in
    deterministic_sni phi_t p_t.

Definition compile_correct : Prop :=
  forall p_s p_t inp ots_s ovs_s out_s ots_t ovs_t out_t
         (Hsem_s : bsem_p p_s inp ots_s ovs_s out_s)
         (Hsem_t : bsem_p p_t inp ots_t ovs_t out_t),
    compile p_s = Some p_t ->
    outputs p_s out_s (bsem_p_final Hsem_s)
    = outputs p_t out_t (bsem_p_final Hsem_t).

Lemma preserves_obs_detsni :
  forall
    (p_s: prog (L := Ls))
    (p_t: prog (L := Lt))
    (phi: relation input)
    (phi_s: seq nat -> seq outshidx -> relation input),
    compile p_s = Some p_t ->
    compile_correct ->
    preserves_obs_w (compile := compile) (simT := simT) (simVIdx := simVIdx) (simV := simV) ->
    (forall i o, rel_implies (phi_s i o) phi) ->
    constant_time p_s (any_rel phi) ->
    preserves_detsni p_s p_t phi_s.
Proof.
  move => p_s p_t phi phi_s Hcompile Hccor Hpre Himpl [] ots_s Hsafe Hni.
  pose i_s_fun i := simVIdx p_s ots_s i.
  exists i_s_fun.
  move => /= i_t o_t inp1 inp2 ots_t1 ots_t2 ovs_t1 ovs_t2 out_t1 out_t2 Hphi_s Hsem_t1 Hsem_t2.
  set (i_s := map i_s_fun i_t) in *.
  (* Get source executions *)
  have Hphi_rel1: any_rel phi inp1 by apply (any_rel_implies (Himpl i_s o_t)); exists inp2; left.
  have Hphi_rel2: any_rel phi inp2 by apply (any_rel_implies (Himpl i_s o_t)); exists inp1; right.
  move: (Hsafe _ Hphi_rel1) => [] ovs_s1 [] out_s1 Hsem_s1.
  move: (Hsafe _ Hphi_rel2) => [] ovs_s2 [] out_s2 Hsem_s2.
  clear Hphi_rel1 Hphi_rel2 Hsafe.
  (* Link source and target *)
  move: (Hni i_s o_t inp1 inp2 ots_s ots_s ovs_s1 ovs_s2 out_s1 out_s2 Hphi_s Hsem_s1 Hsem_s2) => [] _ Hovs_s {Hni}.
  specialize (Hpre p_s p_t).
  move: (Hpre inp1 ots_s ovs_s1 out_s1 ots_t1 ovs_t1 out_t1 Hcompile Hsem_s1 Hsem_t1) => [] Hots1 Hovs1.
  move: (Hpre inp2 ots_s ovs_s2 out_s2 ots_t2 ovs_t2 out_t2 Hcompile Hsem_s2 Hsem_t2) => [] Hots2 Hovs2.
  clear Hpre.
  intro Heqout.
  split; first by subst.
  + (* Intermediate value leakages *)
    rewrite -eq_in_map in Hovs_s.
    apply eq_in_map => probe_t hprobe_t.
    rewrite Hovs1 Hovs2 Hovs_s => //.
    by apply map_f.
 + (* Output shares eq *)
   move: (Hccor _ _ inp1 _ _ _ _ _ _ Hsem_s1 Hsem_t1 Hcompile) => <-.
   move: (Hccor _ _ inp2 _ _ _ _ _ _ Hsem_s2 Hsem_t2 Hcompile) => <-.
   exact: Heqout.
Qed.

End PRESERVATION_SNI.
