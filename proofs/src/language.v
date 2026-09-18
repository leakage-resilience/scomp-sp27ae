From Coq Require Import Utf8 ZArith.
From Coq.Bool Require Import Bool.
From mathcomp Require Import all_ssreflect.

Require Import utils.
Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

Class Language (input: Type) (output: Type) :=
  {
    prog : Type;
    t_obs : eqType;
    t_dummy_observation : t_obs;
    v_obs : eqType;
    v_dummy_observation : v_obs;
    state : Type;
    initial_state : prog -> input -> state;
    step :
      state ->
      t_obs ->
      v_obs ->
      state ->
      Prop;
    final : state -> bool;
    outputs : prog -> forall (s: state), final s -> output;
    step_final : forall s ot ov s', step s ot ov s' -> ~final s;
    step_deterministic : forall s s1 s2 ot1 ot2 ov1 ov2, step s ot1 ov1 s1 -> step s ot2 ov2 s2 -> [/\ ot1 = ot2, ov1 = ov2 & s1 = s2];
    safe_step : state -> Prop;
    (* what follows is for convenience and not strictly necessary. removing it would just require more proofs since
       the existence of exec_step follows from determinism and safety. *)
    exec_step: state -> option (t_obs * v_obs * state);
    exec_stepE:
        forall (s: state) (ot: t_obs) (ov: v_obs) (s': state),
          step s ot ov s' <-> exec_step s = Some (ot, ov, s');
    (* program + current instruction *)
    prog_pc : Type;
    get_pc : state -> prog_pc;
    init_pc : prog -> prog_pc;
    pc_init : forall (p: prog) (inp: input),
      get_pc (initial_state p inp) = init_pc p;
    pc_same_step: forall s1 s2 ot ov ov' s1' s2', step s1 ot ov s1' -> step s2 ot ov' s2' -> get_pc s1 = get_pc s2 -> get_pc s1' = get_pc s2';
    step_pc : prog_pc -> t_obs -> prog_pc -> Prop;
    step_pcE: forall s ot ov s', step s ot ov s' -> step_pc (get_pc s) ot (get_pc s');
    (* Same comments as for exec_step. *)
    exec_step_pc: prog_pc -> t_obs -> option prog_pc;
    exec_step_pcE:
        forall (pc: prog_pc) (ot: t_obs) (pc': prog_pc),
          step_pc pc ot pc' <-> exec_step_pc pc ot = Some pc';
  }.

Arguments prog {_ _} {L} : rename.
Arguments t_obs {_ _} {L} : rename.
Arguments v_obs {_ _} {L} : rename.
Arguments state {_ _} {L} : rename.
Arguments initial_state {_ _} {L} : rename.
Arguments outputs {_ _} {L} : rename.
Arguments step {_ _} {L} : rename.
Arguments final {_ _} {L} : rename.
Arguments safe_step {_ _} {L} : rename.
Arguments step_final {_ _} {L} : rename.
Arguments step_deterministic {_ _} {L} : rename.
Arguments prog_pc {_ _} {L} : rename.

Section SEM.

Context
  {input : Type}
  {output : Type}
  {L : Language input output}
.

Inductive sem :
  state -> seq t_obs -> seq v_obs -> state -> Prop :=
  | sem_refl :
    forall s, sem s [::] [::] s

  | sem_trans :
    forall s s' s'' ot ov ots ovs,
      step s ot ov s' ->
      sem s' ots ovs s'' ->
      sem s (ot :: ots) (ov :: ovs) s''
.

Inductive sem_pc :
  prog_pc -> seq t_obs -> prog_pc -> Prop :=
  | sem_pc_refl :
    forall s, sem_pc s [::] s

  | sem_pc_trans :
    forall s s' s'' ot ots,
      step_pc s ot s' ->
      sem_pc s' ots s'' ->
      sem_pc s (ot :: ots) s''
.

Definition sem_p
  (p : prog)
  (inp : input)
  (ots : seq t_obs)
  (ovs : seq v_obs)
  (s' : state) :
  Prop :=
  sem (initial_state p inp) ots ovs s'.

Definition step_p
  (p : prog)
  (inp : input)
  (ot : t_obs)
  (ov : v_obs)
  (s' : state) :
  Prop :=
  step (initial_state p inp) ot ov s'.

Inductive bsem :
  state -> seq t_obs -> seq v_obs -> state -> Prop :=
  | bsem_final :
    forall s, final s -> bsem s [::] [::] s

  | bsem_trans :
    forall s s' s'' ot ov ots ovs,
      step s ot ov s' ->
      bsem s' ots ovs s'' ->
      bsem s (ot :: ots) (ov :: ovs) s''
  .

Lemma bsem_sem s ots ovs s':
  bsem s ots ovs s' <-> sem s ots ovs s' /\ final s'.
Proof.
  split.
  + move => H.
    induction H.
    + by split; first apply sem_refl.
    move: IHbsem => [] Hsem Hf.
    split; last done.
    by apply (sem_trans H Hsem).
  move => [] Hsem Hfinal.
  induction Hsem.
  + by apply bsem_final.
  by apply /(bsem_trans H) /IHHsem.
Qed.

Lemma bsem_final' s ots ovs s':
  bsem s ots ovs s' -> final s'.
Proof.
  rewrite bsem_sem. by move=> [] _ ? .
Qed.

Definition bsem_p
  (p : prog)
  (inp : input)
  (ots : seq t_obs)
  (ovs : seq v_obs)
  (s' : state) :
  Prop :=
  bsem (initial_state p inp) ots ovs s'.

Lemma bsem_p_final {p inp ots ovs s'}:
  bsem_p p inp ots ovs s' -> final s'.
Proof.
  rewrite /bsem_p bsem_sem. by move=> [] _ ? .
Qed.

Inductive sem_safe : state -> Prop :=
  | safe_trans : forall s s' ots ovs, bsem s ots ovs s' -> sem_safe s.

Definition sem_safe_p (p : prog) (inp : input) := sem_safe (initial_state p inp).

Lemma sem_safeI (s : state) :
  sem_safe s <-> exists ots ovs s', bsem s ots ovs s'.
Proof.
  split => [[] ? s' ots ovs Hsem|[] ots [] ovs [] s' Hsem].
  + by exists ots, ovs, s'.
  by apply (safe_trans Hsem).
Qed.

Lemma sem_safe_pI (p: prog) (inp: input) :
  sem_safe_p p inp <-> exists ots ovs out, bsem_p p inp ots ovs out.
Proof. apply sem_safeI. Qed.

Fixpoint execn (s: state) (n: nat): option (seq t_obs * seq v_obs * state) :=
  match n with
    | O => Some ([::], [::], s)
    | S n' =>
        if exec_step s is Some (ot, ov, s') then
            if execn s' n' is Some (ots, ovs, s'') then
              Some (ot :: ots, ov :: ovs, s'')
            else
              None
        else
          None
    end.

Definition execn_p (p: prog) (inp: input) (n: nat): option (seq t_obs * seq v_obs * state) :=
  execn (initial_state p inp) n.

Fixpoint execn_pc (pc: prog_pc) (ots: seq t_obs): option prog_pc :=
  match ots with
  | [::] => Some pc
  | ot :: ots' =>
      match exec_step_pc pc ot with
      | None => None
      | Some pc' => execn_pc pc' ots'
      end
  end.

End SEM.

Section FACTS.

Context
  {input : Type}
  {output : Type}
  {L : Language input output}
.

(* inversion lemma *)
Lemma semI s ots ovs s' :
  sem s ots ovs s' <->
    match ots with
    | [::] => ovs = [::] /\ s' = s
    | ot :: ots' =>
       exists ov ovs',
         [/\ ovs = ov :: ovs'
           & exists2 si, step s ot ov si & sem si ots' ovs' s'
         ]
    end.
Proof.
  split; move=> H.
  { destruct H; eauto. }
  { destruct ots.
    { destruct H as [H H0]; subst; econstructor. }
    { destruct H as [ov [ovs' [H H0]]]; subst.
      destruct H0 as [si H1 H].
      eapply sem_trans; eauto.
    }
  }
Qed.

Lemma sem_trans1 s ot ov s' :
  step s ot ov s' ->
  sem s [:: ot] [:: ov] s'.
Proof.
  move=> hstep.
  apply: sem_trans; first exact: hstep. apply: sem_refl.
Qed.

Lemma sem_cat s s' s'' OT OT' OV OV' :
  sem s OT OV s' ->
  sem s' OT' OV' s'' ->
  sem s (OT ++ OT') (OV ++ OV') s''.
Proof.
  elim: OT OT' OV OV' s s' s'' =>  [ | O OT ih ] OT' OV OV' s s' s'' /semI.
  - by case => -> ->.
  case => ov [] ovs [] -> {OV} [] si hstep /ih{}ih/ih{}ih.
  exact: sem_trans hstep ih.
Qed.

Lemma sem_cat_rev n s s'' ots ovs:
  (n <= size ots)%N ->
  sem s ots ovs s'' ->
  exists s' ots1 ots2 ovs1 ovs2,
  [/\ sem s ots1 ovs1 s'
    , sem s' ots2 ovs2 s''
    , ots = ots1++ots2
    , ovs = ovs1++ovs2
    & size ots1 = n].
Proof.
  move: s ots ovs.
  elim n.
  + move => s ots ovs _ Hsem.
    exists s, [::], ots, [::], ovs.
    by split => //; apply sem_refl.
  move => {}n Hind s ots ovs Hn Hsem.
  inversion Hsem.
  + subst.
    exists s'', [::], [::], [::], [::].
    by split => //; apply sem_refl.
  subst s0 ots ovs s''0.
  rewrite /= ltnS in Hn.
  move: (Hind s' _ _ Hn H0) => [] s'0 [] ots1 [] ots2 [] ovs1 [] ovs2 [] Hsem1 Hsem2 ? ? Hots1.
  subst ots0 ovs0.
  exists s'0, (ot::ots1), ots2, (ov::ovs1), ovs2.
  split => //.
  + by apply (sem_trans H Hsem1).
  by rewrite /= Hots1.
Qed.

Lemma sem_execn (s: state) (ots: seq t_obs) (ovs: seq v_obs) (s': state):
  sem s ots ovs s' <-> execn s (size ots) = Some (ots, ovs, s').
Proof.
  split. {
    move: s ovs.
    elim: ots. {
      move => s ovs.
      rewrite semI.
      by move => [-> ->].
    }
    move => ot ots Hind s ovs.
    move => Hsem.
    dependent destruction Hsem.
    move => /=.
    move: (exec_stepE s ot ov s') => [Hexec _].
    by rewrite (Hexec H) (Hind s' ovs Hsem).
  }
  move: s ovs.
  elim: ots. {
    move => s ovs /=.
    case => <- <-.
    by rewrite semI.
  }
  move => ot ots Hind s ovs /=.
  destruct (exec_step s) as [[[ot0 ov0] s0]|] eqn:STEP; last by discriminate.
  destruct (execn s0 (size ots)) as [[[ots0 ovs0] ?]|] eqn:EXECS; last by discriminate.
  move => H.
  move: EXECS STEP.
  injection H => -> <- -> -> => Hexec Hexec_step.
  specialize (Hind s0 ovs0 Hexec).
  apply exec_stepE in Hexec_step.
  apply semI.
  exists ov0; exists ovs0; split; first done.
  by exists s0.
Qed.

Lemma execn_size n s ots ovs s':
  execn s n = Some (ots, ovs, s') -> n = size ots.
Proof.
  move: s ots ovs.
  elim: n.
  + by move => s ots ovs; rewrite /execn /= => H; injection H => _ _ <-.
  move => n Hind s ots ovs.
  rewrite /execn -/execn.
  case: (exec_step s); last by discriminate.
  move => [[ot ov] s''].
  destruct (execn s'' n) as [[[ots' ovs'] s''']|] eqn:H; last by discriminate.
  move => H'; move: H Hind; injection H'.
  move => -> _ <- Hexecn Hind.
  by rewrite (Hind s'' ots' ovs' Hexecn).
Qed.

Lemma execn_sem_size (s : state) (ots : seq t_obs) (ovs : seq v_obs) (s' : state) (n: nat):
  execn s n = Some (ots, ovs, s') <-> sem s ots ovs s' /\ size ots = n.
Proof.
  split. {
    move => H.
    have ? := (execn_size H); subst.
    split => //.
    by apply sem_execn.
  }
  by move => [] /sem_execn <- <-.
Qed.

Lemma sem_deterministic' s s1 s2 ots1 ots2 ovs1 ovs2:
  sem s ots1 ovs1 s1 ->
  sem s ots2 ovs2 s2 ->
  size ots1 = size ots2 ->
  [/\ ots1 = ots2, ovs1 = ovs2 & s1 = s2].
Proof.
  rewrite !sem_execn.
  move => H1 H2 Hsz.
  rewrite -Hsz H1 in H2.
  by inversion H2.
Qed.


Lemma sem_deterministic s s1 s2 ots1 ots2 ovs1 ovs2:
  bsem s ots1 ovs1 s1 ->
  bsem s ots2 ovs2 s2 ->
  [/\ ots1 = ots2, ovs1 = ovs2 & s1 = s2].
Proof.
  elim: ots1 ots2 ovs1 ovs2 s.
  + move => ots2 ovs1 ovs2 s Hsem1 Hsem2.
    inversion Hsem1; subst.
    inversion Hsem2; subst => //.
    by move: (step_final _ _ _ _ H0).
  move => ot1 ots1 IH ots2 ovs1 ovs2 s Hsem1 Hsem2.
  inversion Hsem2; inversion Hsem1; subst.
  + by move: (step_final _ _ _ _ H7).
  move: (step_deterministic _ _ _ _ _ _ _ H H8) => [] ? ? ?; subst.
  by move: (IH ots ovs0 ovs s'0 H11 H0) => [] ? ? ?; subst.
Qed.

Lemma sem_sub s ots ovs out_s ots1 ovs1 s1:
  bsem s ots ovs out_s ->
  sem s ots1 ovs1 s1 ->
  (size ots1 <= size ots)%N.
Proof.
  elim: ots ots1 ovs ovs1 s.
  + move=> ots1 ovs ovs1 s Hsem1 Hsem2.
    inversion Hsem1; subst.
    inversion Hsem2; subst => //.
    by move: (step_final _ _ _ _ H0). (* contradiction *)
  + move=> ot ots IH ots1 ovs ovs1 s Hsem1 Hsem2.
    inversion Hsem2; inversion Hsem1; subst.
    + by[].
    + move: (step_deterministic _ _ _ _ _ _ _ H H8) => [] ? ? ?; subst.
      by apply (IH _ _ _ _ H11 H0).
Qed.

Lemma sem_sub' s ots ovs out_s ots1 ovs1 s1:
  sem s ots ovs out_s ->
  final out_s ->
  sem s ots1 ovs1 s1 ->
  (size ots1 <= size ots)%N.
Proof.
  move=> Hsems Hfin Hsems1.
  have Hsems' : (bsem s ots ovs out_s).
  apply/bsem_sem; split; by [].
  apply (sem_sub Hsems' Hsems1).
Qed.

Lemma sem_catI (s s1 s2 : state) (ots1 ots2 : seq t_obs) (ovs1 ovs2 : seq v_obs) :
  sem s ots1 ovs1 s1 -> sem s (ots1 ++ ots2) (ovs1 ++ ovs2) s2 -> sem s1 ots2 ovs2 s2.
Proof.
  move => Hsem1 Hsem.
  have Hn: (size ots1 <= size (ots1++ots2))%N.
  + by rewrite size_cat; apply leq_addr.
  move: (sem_cat_rev Hn Hsem) => [] s1' [] ots1' [] ots2' [] ovs1' [] ovs2' [] Hsem1' Hsem2' Hots Hovs H.
  move: (sem_deterministic' Hsem1' Hsem1 H) => [] ? ? ?; subst.
  have:= congr1 (drop (size ots1)) Hots.
  have:= congr1 (drop (size ovs1)) Hovs.
  by rewrite !drop_cat !drop_size !subnn !drop0 !ltnn => -> ->.
Qed.

Lemma execn_sum n1 n2 (ots1 ots2: seq t_obs) ovs1 ovs2 (s s1 s2: state):
  execn s n1 = Some (ots1, ovs1, s1) ->
  execn s1 n2 = Some (ots2, ovs2, s2) <->
  execn s (n1+n2) = Some (ots1++ots2, ovs1++ovs2, s2).
Proof.
  rewrite !execn_sem_size; move => [] H1 Hs1.
  split. {
    move => [] H2 Hs2.
    subst.
    split.
    + by apply (sem_cat H1 H2).
    by apply size_cat.
  }
  move => [] H2 Hs2.
  split.
  + by apply (sem_catI H1 H2).
  move: Hs1 Hs2.
  rewrite size_cat => ->.
  elim n1 => // n H.
  rewrite !addSnnS !addnS => H'.
  apply H.
  by inversion H'.
Qed.

Lemma execn_pre n n' ots ovs (s s': state):
  (n' < n)%N ->
  execn s n = Some (ots, ovs, s') ->
  exists s'', execn s n' = Some (take n' ots, take n' ovs, s'').
Proof.
  move: n' ots ovs s.
  elim n.
  + discriminate.
  move => {}n Hind n' ots ovs s Hn /=.
  case_eq (exec_step s) => // [] [] [] ot ov s1 Hstep.
  case_eq (execn s1 n) => // [] [] [] ots' ovs' s1' Hexec.
  move => [] ? ? ?; subst.
  case_eq n'.
  + by exists s; rewrite !take0.
  move => n'' Hn'.
  have Hn'': (n''<n)%N.
  + by rewrite Hn' -(add1n n'') -(add1n n) ltn_add2l in Hn.
  move: (Hind n'' ots' ovs' s1 Hn'' Hexec) => [] s'' Hexec'.
  exists s'' => /=.
  by rewrite Hstep Hexec'.
Qed.

Lemma execn_pre_take (s s1 s2: state) n1 n2 ots1 ovs1 ots2 ovs2:
  (n1 < n2)%N ->
  execn s n1 = Some (ots1, ovs1, s1) ->
  execn s n2 = Some (ots2, ovs2, s2) ->
  take n1 ots2 = ots1.
Proof.
  move => Hn H1 H2.
  move: (execn_pre Hn H2) => [] s1'.
  by rewrite H1 => [] [] ? ? ?; subst.
Qed.

Lemma sem_execn_p (p: prog) (inp: input) (ots: seq t_obs) (ovs: seq v_obs) (s': state):
  sem_p p inp ots ovs s' <-> execn_p p inp (size ots) = Some (ots, ovs, s').
Proof.
  rewrite /sem_p /execn_p.
  by apply sem_execn.
Qed.

Lemma execn_p_size p inp n ots ovs s':
  execn_p p inp n = Some (ots, ovs, s') -> n = size ots.
Proof. by apply execn_size. Qed.

Lemma sem_eq_size_leaks s ots ovs s':
  sem s ots ovs s' -> size ots = size ovs.
Proof.
  rewrite semI.
  elim: ots ovs s.
  + move=> ovs s [] -> _ //.
  + move=> ot' ots' Hind.
    move=> ovs s [ov' [ovs']] [] -> [si] Hstep Hsem.
    rewrite semI in Hsem.
    specialize (Hind ovs' si Hsem).
    by rewrite /= Hind.
Qed.

Lemma sem_pcI pc ots pc' :
  sem_pc pc ots pc' <->
    match ots with
    | [::] => pc' = pc
    | ot :: ots' =>
           exists2 pci, step_pc pc ot pci & sem_pc pci ots' pc'
    end.
Proof.
  split; move=> H.
  { destruct H; eauto. }
  { destruct ots.
    { subst; econstructor. }
    { destruct H as [H H0].
      eapply sem_pc_trans; eauto.
    }
  }
Qed.

Lemma sem_execn_pc (pc: prog_pc) (ots: seq t_obs) (pc': prog_pc):
  sem_pc pc ots pc' <-> execn_pc pc ots = Some (pc').
Proof.
  split. {
    move: pc.
    elim: ots.
    + move => pc.
      by rewrite sem_pcI => ->.
    move => ot ots Hind pc Hsem.
    dependent destruction Hsem => /=.
    move: (exec_step_pcE s ot s') => [Hexec _].
    by rewrite (Hexec H) (Hind _ Hsem).
  }
  move: pc.
  elim: ots. {
    move => pc /= [] ->.
    by apply sem_pc_refl.
  }
  move => ot ots Hind pc /=.
  case_eq (exec_step_pc pc ot); last discriminate.
  move => pc0 Hstep Hsem.
  specialize (Hind pc0 Hsem) => {Hsem}.
  rewrite -exec_step_pcE in Hstep.
  apply (sem_pc_trans Hstep Hind).
Qed.

Lemma sem_pcE s ots ovs s':
  sem s ots ovs s' -> sem_pc (get_pc s) ots (get_pc s').
Proof.
  rewrite sem_execn sem_execn_pc.
  elim: ots s ovs.
  + by move => s ovs /= [] _ ->.
  move => ot ots Hind s ovs /=.
  case_eq (exec_step s); last discriminate.
  move => [] [] ot_i ov_i s_i Hstep.
  case_eq (execn s_i (size ots)); last discriminate.
  move => [] [] ots_i ovs_i s_i' Hexecn.
  move => [] ? ? ? ?; subst.
  rewrite -exec_stepE in Hstep.
  apply step_pcE in Hstep.
  move /exec_step_pcE: Hstep ->.
  by apply (Hind _ _ Hexecn).
Qed.


End FACTS.

Section COMPILE.

Context
  {input : Type}
  {output : Type}
  {Ls Lt : Language input output}
.

Definition compiler : Type := prog (L := Ls) -> option (prog (L := Lt)).

End COMPILE.

Section COMPOSITION.

Context
  {input : Type}
  {output : Type}
  {L0 L1 L2 : Language input output}
  (compile2 : compiler (Ls := L1) (Lt := L2))
  (compile1 : compiler (Ls := L0) (Lt := L1))
.

Definition compose : compiler (Ls := L0) (Lt := L2) :=
  fun p_s =>
    match compile1 p_s with
    | Some p => compile2 p
    | None => None
    end.

End COMPOSITION.
