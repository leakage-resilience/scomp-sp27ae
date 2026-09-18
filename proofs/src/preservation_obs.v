(* -------------------------------------------------------------------------- *)
(* Generic preservation of observable leakage. *)
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

Section PRESERVATION.

  Context
    {input : Type}
    {output : Type}
  .

  Definition get_ov
    {L: Language input output} (ovs: seq (v_obs (L := L))) (i: nat): v_obs (L := L) :=
    nth v_dummy_observation ovs i.

  Definition get_ovs
    {L: Language input output} (ovs: seq (v_obs (L := L))) (i: seq nat): seq (v_obs (L := L)) :=
    map (get_ov ovs) i.

  Context
    {Ls Lt : Language input output}
      {compile : compiler (input := input) (Ls := Ls) (Lt := Lt)}
  .

  Section MULTISTEP.

  Definition SimT : Type :=
    prog (L := Ls) -> (* source program *)
    seq (t_obs (L := Ls)) (* Source timing leakage *) ->
    seq (t_obs (L := Lt)) (* Target timing leakage *).

  Definition SimVIdx : Type :=
    prog (L := Ls) -> (* source program *)
    seq (t_obs (L := Ls)) (* Source timing leakage *) ->
    nat (* Target step probed *) ->
    nat (* Source step needed *).

  Definition SimV : Type :=
    prog (L := Ls) -> (* source program *)
    seq (t_obs (L := Ls)) -> (* Source timing leakage *)
    nat (* Target step probed *) ->
    v_obs (L := Ls) (* Source value leakage *) ->
    v_obs (L := Lt) (* Target value leakage *).

  Context
      {simT: SimT}
      {simVIdx: SimVIdx}
      {simV: SimV}
  .

  Definition preserves_obs_w: Prop :=
    forall p_s p_t inp ots_s ovs_s out_s ots_t ovs_t out_t,
      compile p_s = Some p_t ->
      bsem_p p_s inp ots_s ovs_s out_s ->
      bsem_p p_t inp ots_t ovs_t out_t ->
      ots_t = simT p_s ots_s /\
        forall i_t,
          let i_s := simVIdx p_s ots_s i_t in
          get_ov ovs_t i_t = simV p_s ots_s i_t (get_ov ovs_s i_s).

  Definition preserves_obs: Prop :=
    forall p_s p_t inp ots_s ovs_s out_s,
      compile p_s = Some p_t ->
      bsem_p p_s inp ots_s ovs_s out_s ->
      exists ots_t ovs_t out_t,
        [/\ bsem_p p_t inp ots_t ovs_t out_t
          , ots_t = simT p_s ots_s
            & forall i_t,
              let i_s := simVIdx p_s ots_s i_t in
              get_ov ovs_t i_t = simV p_s ots_s i_t (get_ov ovs_s i_s)
        ].

  Lemma preserves_obs_of_fw:
    preserves_obs ->
    preserves_obs_w.
  Proof.
    move => H p_s p_t inp ots_s ovs_s out_s ots_t ovs_t out_t Hc Hsem_s Hsem_t.
    destruct (H p_s p_t inp ots_s ovs_s out_s Hc Hsem_s) as [ots_t' [ovs_t' [out_t' [Hsem_t' Hots_t' Hovs_t']]]].
    case: (sem_deterministic Hsem_t Hsem_t') => -> -> _.
    by split.
  Qed.

  End MULTISTEP.

  Section STEP.
    (* forward simulation releation where exactly one step in source is related to an arbitrary number of steps in target. *)

  Definition eq_states :=
    state (L := Ls) ->
    state (L := Lt) ->
    Prop.

  Definition SimT1 : Type :=
    prog_pc (L := Ls) ->
    t_obs (L := Ls) (* Source timing leakage *) ->
    seq (t_obs (L := Lt)) (* Target timing leakage *)
  .

  Definition SimV1 : Type :=
    prog_pc (L := Ls) ->
    t_obs (L := Ls) (* Source timing leakage *) ->
    v_obs (L := Ls) (* Source value leakage *) ->
    seq (v_obs (L := Lt)) (* Target value leakage *)
  .

  Definition step_preserves_obs
    (eq_s: eq_states)
    (simT1: SimT1)
    (simV1: SimV1)
    : Prop :=
    forall s t ot_s ov_s s',
      eq_s s t ->
      step s ot_s ov_s s' ->
      exists ots_t ovs_t t',
        [/\ sem t ots_t ovs_t t'
          , ots_t = simT1 (get_pc s) ot_s
          , ovs_t = simV1 (get_pc s) ot_s ov_s
          & eq_s s' t'
        ].

  Fixpoint _simT_of_simT1
    (simT1: SimT1)
    (pc_s: prog_pc (L := Ls))
    (ots_s: seq (t_obs (L := Ls)))
    : seq (t_obs (L := Lt)) :=
    match ots_s with
    | [::] => [::]
    | ot_s::ots_s' =>
        match execn_pc pc_s [::ot_s] with
        | None => [::] (* failure *)
        | Some pc_s' =>
            simT1 pc_s ot_s ++ _simT_of_simT1 simT1 pc_s' ots_s'
        end
    end.

  Definition _simT simT1 : SimT :=
    fun p_s => _simT_of_simT1 simT1 (init_pc p_s).

  Fixpoint _simV_of_sim1
    (simT1: SimT1)
    (simV1: SimV1)
    (pc_s: prog_pc (L := Ls))
    (ots_s: seq (t_obs (L := Ls)))
    (i_t: nat)
    (ov_s: v_obs (L := Ls))
    : v_obs (L := Lt) :=
    match ots_s with
    | [::] =>
        v_dummy_observation
    | ot_s::ots_s' =>
        let ots_t := simT1 pc_s ot_s in
        let ovs_t := simV1 pc_s ot_s ov_s in
        if (i_t < size ots_t)%N then
          nth v_dummy_observation ovs_t i_t
        else
          let i_t' := (i_t - size ots_t)%N in
          match execn_pc pc_s [:: ot_s] with
          | None => v_dummy_observation (* Invalid ots_s *)
          | Some pc_s' =>
              _simV_of_sim1 simT1 simV1 pc_s' ots_s' i_t' ov_s
          end
    end.

  Definition _simV simT1 simV1 : SimV :=
    fun p_s =>
      _simV_of_sim1 simT1 simV1 (init_pc p_s).

  Fixpoint _simVIdx_of_simT1
    (simT1: SimT1)
    (pc_s: prog_pc (L := Ls))
    (ots_s: seq (t_obs (L := Ls)))
    (i_t: nat)
    : nat :=
    match ots_s with
    | [::] =>
        O (* Invalid ots_s *)
    | ot_s::ots_s' =>
        let ots_t := simT1 pc_s ot_s in
        if (i_t < size ots_t)%N then
          O
        else
          let i_t' := (i_t - size ots_t)%N in
          match execn_pc pc_s [::ot_s] with
          | None => O (* Invalid ots_s *)
          | Some pc_s' =>
              (_simVIdx_of_simT1 simT1 pc_s' ots_s' i_t').+1
          end
    end.

  Definition _simVIdx simT1 : SimVIdx :=
    fun p_s =>
      _simVIdx_of_simT1 simT1 (init_pc p_s).

  Definition eq_s_initial (eq_s: eq_states) :=
    forall p_s p_t inp,
      compile p_s = Some p_t ->
      eq_s (initial_state p_s inp) (initial_state p_t inp).

  Definition eq_s_final (eq_s: eq_states) :=
    forall s t,
      eq_s s t ->
      final s ->
      final t.

  Lemma lift_step_preserves_obs (eq_s: eq_states) (simT1: SimT1) (simV1: SimV1):
    eq_s_initial eq_s ->
    eq_s_final eq_s ->
    step_preserves_obs eq_s simT1 simV1 ->
    preserves_obs (simT := _simT simT1) (simVIdx := _simVIdx simT1) (simV := _simV simT1 simV1).
  Proof.
    intros Heq Heqf Hpres ? ? ? ? ? ? Hcompile.
    rewrite !/bsem_p !bsem_sem; move=> [] Hsems Hfins.
    unfold step_preserves_obs in Hpres.
    specialize (Heq _ _ inp Hcompile).
    pose t := (initial_state p_t inp).
    pose s := (initial_state p_s inp).
    rewrite /_simT /_simT_of_simT1 /_simV /_simV_of_sim1 /_simVIdx /_simVIdx_of_simT1-(pc_init p_s inp) -/t -/s. (* This makes it very ugly *)
    rewrite -/t -/s in Heq Hsems.
    rewrite -/t -/s.
    move: t Heq.
    induction (Hsems) as [s | s s' s'' ot_s ov_s ots_s ovs_s Hsteps Hsems' Hind]; intros t Heq.
    {
      (* no step in source *)
      specialize (Heqf _ _ Heq Hfins).
      have Hsemt := bsem_final Heqf. inversion Hsemt.
      exists [::], [::], t.
      split => //=.
        + intro i_t. by rewrite /get_ov nth_nil.
    }
    {
      (* induction *)
      specialize (Hpres _ _ _ _ _ Heq Hsteps).
      destruct Hpres as [ ots_t [ ovs_t [ t' [Hsemt Hots_t Hovs_t Heq']]]].
      specialize (Hind Hfins Hsems' _ Heq').
      destruct Hind as [ots_t2 [ovs_t2 [out_t [Hsemt2 Hots_t2 Hovs_t2]]]].
      apply sem_trans1, sem_pcE, sem_execn_pc in Hsteps.
      exists (ots_t++ots_t2), (ovs_t++ovs_t2), out_t.
      split.
      + apply bsem_sem. apply bsem_sem in Hsemt2. destruct Hsemt2 as [Hsemt2 Hfint].
        split; last by[].
        apply (sem_cat Hsemt Hsemt2).
      + subst. by rewrite Hsteps /=.
      + intro i_t. rewrite -!Hots_t /get_ov Hovs_t nth_cat.
        destruct (i_t < size ots_t)%N eqn:Hb.
        -- by rewrite -!Hovs_t -(sem_eq_size_leaks Hsemt) !Hb. (* probe on target steps corresponding to first step in source *)
        -- rewrite -!Hovs_t -(sem_eq_size_leaks Hsemt) !Hb !Hsteps /=. specialize (Hovs_t2 (i_t - size ots_t)%N). rewrite /get_ov in Hovs_t2. rewrite Hovs_t2. simpl. reflexivity. (* probes on inductive steps *)
    }
Qed.

End STEP.

End PRESERVATION.
