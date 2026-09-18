(* -------------------------------------------------------------------------- *)
(* Dead branch elimination. *)
(* Removes If instructions whose guard is a constant (keeps only the
      corresponding branch) and loops whose guard is the constant false *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  syntax
  utils
  var
  semantics
  semantics_facts
  utils_facts
  language
.

Existing Instance Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

Section PASS.

Section CMD.

  Context (dead_branch_i : iinfo -> instr -> code).

  Definition dead_branch_ii (i : instr_i) : code :=
    dead_branch_i (annot i) (unannot i).

  Fixpoint dead_branch_c (c : code) :=
    match c with
    | [::] => [::]
    | i :: c => dead_branch_ii i ++ dead_branch_c c
    end.

End CMD.

Definition is_bool (e : expr) :=
  if e is Ebool b then Some b else None.

Fixpoint dead_branch_i (a:iinfo) (i : instr) : code :=
  match i with
  | Iif e c1 c0 =>
    let c1 := dead_branch_c dead_branch_i c1 in
    let c0 := dead_branch_c dead_branch_i c0 in
    if is_bool e is Some b then (if b then c1 else c0)
    else [:: {| annot := a; unannot := Iif e c1 c0 |} ]

  | Iwhile e c1 =>
    let c1 := dead_branch_c dead_branch_i c1 in
    if is_bool e is Some false then [::]
    else [:: {| annot := a; unannot := Iwhile e c1 |} ]

  | _ => [:: {| annot := a; unannot := i |} ]
  end.

Definition dead_branch_p (p : prog) : prog :=
  map_p_prog (fun c => dead_branch_c dead_branch_i c) p.

Definition is_deadbranch (c : code) : bool :=
  match c with
  | {| unannot := Iif e c1 c0 |} :: _ =>
    if is_bool e is Some _ then true
    else false

  | {| unannot := Iwhile e c |} :: _ =>
    if is_bool e is Some false then true
    else false
  (* | [::] => true *)
  | _ => false
  end.

Section PROOF.

Context
  (p_s p_t : prog)
  (hcompile : dead_branch_p p_s = p_t)
.

Definition eq_s (s t : state) :=
  [/\ s_c t = dead_branch_c dead_branch_i (s_c s)
    , s_vm s = s_vm t
    & s_mem s = s_mem t ]
.

Section Tdir_i.

Let Pi (i: instr) : Prop :=
  forall s t a c,
    eq_s s t ->
    s_c s = {|annot := a; unannot := i|} :: c ->
    exists s' ots ovs c',
      [/\ sem s ots ovs s'
        , eq_s s' t
        , s_c s' = c' ++ c
        & ~~is_deadbranch c' ].

Let Pii (i: instr_i) : Prop :=
  Pi (unannot i).

Let Pc (c: code) : Prop :=
  forall s t c1,
    eq_s s t ->
    s_c s = c ++ c1 ->
    exists s' ots ovs c',
      [/\ sem s ots ovs s'
        , eq_s s' t
        , s_c s' = c' ++ c1
        & ~~is_deadbranch c' ].

Lemma Hassign : forall x e, Pi (Iassign x e).
Proof.
  move=> x e s t an c heqm hmc /=.
  exists s, [::], [::], [:: {| annot := an; unannot := Iassign x e |}]; split => //.
  exact (sem_refl _).
Qed.

Lemma Hload : forall x a e, Pi (Iload x a e).
Proof.
  move=> x a e s t an c heqm hmc /=.
  exists s, [::], [::], [:: {| annot := an; unannot := Iload x a e|}]; split => //.
  exact (sem_refl _).
Qed.

Lemma Hstore : forall a e x, Pi (Istore a e x).
Proof.
  move=> a e x s t an c heqm hmc /=.
  exists s, [::], [::], [:: {| annot := an; unannot := Istore a e x |}]; split => //.
  exact (sem_refl _).
Qed.

Lemma Hmop : forall xs mop os, Pi (Imop xs mop os).
Proof.
  move => xs mop os s t an c heqml hmc /=.
  exists s, [::], [::], [:: {| annot := an; unannot := Imop xs mop os |}]; split =>//.
  exact (sem_refl _).
Qed.

Lemma is_boolP e b : is_bool e = Some b -> e = Ebool b.
Proof. by case: e => //= ? [->]. Qed.

Lemma dead_branch_c_cat c1 c2 :
  dead_branch_c dead_branch_i (c1 ++ c2) =
  dead_branch_c dead_branch_i c1 ++ dead_branch_c dead_branch_i c2.
Proof. by elim: c1 => //= i c1 ->; rewrite catA. Qed.

Lemma Hif : forall e c1 c0, Pc c1 -> Pc c0 -> Pi (Iif e c1 c0).
Proof.
  clear.
  move=> e c1 c0 hrec1 hrec0 s t an c heqs hmc /=.
  case heq : (is_bool e) => [b | ].
  - have ? := (is_boolP heq); subst e => {heq}.
    pose s' := with_c s ((if b then c1 else c0) ++ c).
    have Hstep : step s (OTbranch b) (OVval [:: Vbool b]) s'.
    { apply /stepI. rewrite hmc. exists b. split=>//=. }
    destruct b.
    + have s_c_s' : s_c s' = c1 ++ c by subst s'.
      have heq_s'_t : eq_s s' t.
      { split=>//=.
        rewrite dead_branch_c_cat.
        move : heqs => [] -> _ _.
        by rewrite hmc -cat1s dead_branch_c_cat //= cats0.
        by move : heqs=>[].
        by move : heqs=>[].
      }
      have [s'' [ots [ovs [c' [Hsem]]]]] :=
        (hrec1 s' t c heq_s'_t s_c_s').
      move=> Heqs Hsc Hdead.
      exists s'', ((OTbranch true) :: ots),
        (OVval [:: Vbool true] :: ovs), c'.
      split=>//=.
      exact (sem_trans Hstep Hsem).
    + have s_c_s' : s_c s' = c0 ++ c by subst s'.
      have heq_s'_t : eq_s s' t.
      { split=>//=.
        rewrite dead_branch_c_cat.
        move : heqs => [] -> _ _.
        by rewrite hmc -cat1s dead_branch_c_cat //= cats0.
        by move : heqs=>[].
        by move : heqs=>[].
      }
      have [s'' [ots [ovs [c' [Hsem ]]]]] :=
        (hrec0 s' t c heq_s'_t s_c_s').
      move=> Heqs Hsc Hdead.
      exists s'', ((OTbranch false) :: ots),
        (OVval [:: Vbool false] :: ovs), c'.
      split=>//=.
      exact (sem_trans Hstep Hsem).
  - exists s, [::], [::], [:: {| annot := an; unannot := Iif e c1 c0 |}].
    split=>//=.
    + exact (sem_refl _).
    + by rewrite heq.
Qed.

Lemma Hwhile : forall e c1, Pc c1 -> Pi (Iwhile e c1).
Proof.
  clear.
  move=> e c1 hrec s t an c heqs hmc /=.
  case heq : (is_bool e) => [b |].
  - have ? := (is_boolP heq); subst e => {heq}.
    destruct b.
    + exists s, [::], [::],
        [:: {| annot := an; unannot := Iwhile (Ebool true) c1 |}].
      split=>//=.
      exact (sem_refl _).

    + pose s' := with_c s c.
      have Hstep : step s (OTbranch false) (OVval [:: Vbool false]) s'.
      { apply/stepI. rewrite hmc. exists false. split=>//=. }
      have s_c_s' : s_c s' = c by subst s'.
      have heq_s'_t : eq_s s' t.
      { split=>//=.
        move : heqs=>[] + _ _.
        by rewrite hmc -cat1s dead_branch_c_cat //=.
        by move : heqs=>[].
        by move : heqs=>[].
      }
      unfold Pc in hrec.
      exists s', [:: (OTbranch false)], [:: OVval [:: Vbool false]], [::].
      split=>//=.
      exact (sem_trans Hstep (sem_refl _)).
  - exists s, [::], [::], [:: {| annot := an; unannot := Iwhile e c1 |}].
    split=>//=.
    + exact (sem_refl _).
    + by rewrite heq.
Qed.

Lemma Hnil : Pc [::].
Proof.
  move=> s t c heqm hmc /=.
  exists s, [::], [::], [::].
  split=>//.
  exact (sem_refl s).
Qed.

Lemma Hcons : forall i c, Pii i -> Pc c -> Pc (i::c).
Proof.
  move=> [an i] c hi hc s t c1 heqs hsc /=.
  unfold Pii, Pi in *.
  specialize (hi s t an (c++c1) heqs hsc).
  destruct hi as [s'' [ots [ovs [c'' [Hsem Heq Hcode Hdead]]]]].

  destruct c''; first last.
  { exists s'', ots, ovs, (a :: c'' ++ c).
    split=>//=.
    rewrite cat_cons in Hcode.
    by rewrite -catA. }

  simpl in Hcode.
  specialize (hc s'' t c1 Heq Hcode).
  destruct hc as [s''' [ots' [ovs' [c''' [Hsem' Heq' Hcode' Hdead']]]]].
  exists s''', (ots++ots'), (ovs++ovs'), c'''.
  split=>//=.
  apply (sem_cat Hsem Hsem').
Qed.

Lemma Hannot : forall i a, Pi i -> Pii {|annot := a; unannot := i |}.
Proof.
  move=> i c hi s t c1 an /= heqm hmc /=.
  apply (hi _ _ _ _ heqm hmc).
Qed.

Lemma TcP : forall c, Pc c.
Proof.
  apply (@ind_c Pi Pii Pc).
  + apply Hassign.
  + apply Hload.
  + apply Hstore.
  + apply Hmop.
  + apply Hif.
  + apply Hwhile.
  + apply Hnil.
  + apply Hcons.
  + apply Hannot.
Qed.

End Tdir_i.

Lemma dead_step s s' t ot ov:
  eq_s s t ->
  is_deadbranch (s_c s) ->
  step s ot ov s' ->
  eq_s s' t.
Proof.
  move=> [].
  case H: (s_c s) => //= [[? i] c].
  case: i H => //.
  - case => //=.
    move=> b ct cf Hcs Hct Hvm Hmem _ /stepI.
    rewrite Hcs.
    move=> [b' [Heval Hot Hov Hcs']] //.
    have Hbb' : b = b' by move: Heval => //= [= ->].
    subst.
    split => //.
    rewrite Hct.
    case b'
    ; unfold dead_branch_ii
    ; simpl
    ; symmetry
    ; by apply dead_branch_c_cat.
  - case => //=.
    case => //=.
    move=> l Hcs Hct Hvm Hmem _ /stepI.
    rewrite Hcs.
    move=> [b' [Heval Hot hov Hcs']] //.
    subst.
    split => //.
    rewrite Hct.
    rewrite ifF => //=.
    by move: Heval => //= [=].
Qed.


Lemma live_step s s' t ot ov:
  eq_s s t ->
  ~~ is_deadbranch (s_c s) ->
  step s ot ov s' ->
  exists t', step t ot ov t' /\ eq_s s' t'.
Proof.
  move=> [] Hct Hvm Hmem Hnd Hstep.
  destruct (s_c s) eqn:Hcs
  ; first by rewrite stepI Hcs in Hstep.

  destruct a as [ia i].
  simpl in Hct.
  unfold dead_branch_ii, unannot, annot in Hct.

  set simple_instr := fun i => match i with
                               | Iwhile _ _ => false
                               | Iif _ _ _ => false
                               | _ => true
                               end.

  have simple_suff : simple_instr i ->
                     exists t' : semantics.state, semantics.step t ot ov t' /\ eq_s s' t'.
  { move=> Hsimple.
    have Hdb : dead_branch_i ia i = [:: {| unannot := i ; annot := ia |}]
      by destruct i.
    move: Hct.
    rewrite Hdb => //= Hct.
    have [t' Ht'] := step_deterministic' Hstep Hmem Hvm Hcs Hct.
    exists t'.
    do ? (split; try by destruct Ht').
    move : Ht' => [] Hstep' Hvm' Hmem' Hct'.
    rewrite Hct' (step_code' Hcs Hstep).
    by destruct i.
  }

  induction i
  ; try by apply simple_suff.
  - move : Hnd Hct => //=.
    case (is_bool e); first done.
    move=>_.
    apply stepI in Hstep.
    move : Hstep.
    rewrite Hcs.
    move=> [b [Heval -> -> Hs']] //= Hct.
    rewrite Hvm.
    eexists.
    split.
    + eapply step_if.
      * exact Hct.
      * by rewrite <-Hvm.
      * reflexivity.
    + split; simpl; try by subst.
      subst s' => //=.
      case b; by rewrite dead_branch_c_cat.

  - move : Hnd Hct => //=.
    case He : (is_bool e == Some false)
    ; move: He =>/eqP //
    ; first by move->.
    move=> Ne Hnd Hct'.
    have Hct : s_c t
               = [:: {| annot := ia; unannot := Iwhile e (dead_branch_c dead_branch_i l0) |}]
                   ++ dead_branch_c dead_branch_i l
      by destruct (is_bool e); [by destruct b | done].
    apply stepI in Hstep.
    move : Hstep.
    rewrite Hcs.
    move=> [b [Heval -> -> Hs']] //=.
    rewrite Hvm.
    eexists.
    split.
    + eapply step_while.
      * exact Hct.
      * by rewrite <-Hvm.
      * reflexivity.
    + split; simpl; try by subst.
      subst.
      destruct b; try done.
      rewrite dead_branch_c_cat Hct //= /dead_branch_ii //=.
      destruct (is_bool e) as [b|]; try done.
      by destruct b.
Qed.

End PROOF.

End PASS.

Require Import language preservation_obs.

Section PRESERVATION.

Definition pass : compiler := fun p_s => Some (dead_branch_p p_s).

Definition _simT1 : SimT1 :=
  fun pc_s ot_s =>
    match pc_s with
    | [::] => [::]
    | i :: c =>
        if is_deadbranch (i :: c) then
          [::]
        else
          [:: ot_s]
    end.

Definition _simV1 : SimV1 :=
  fun pc_s ot_s ov_s =>
    match pc_s with
    | [::] => [::]
    | i :: c =>
        if is_deadbranch (i :: c) then
          [::]
        else
          [:: ov_s]
    end.


Lemma step_preservation:
  step_preserves_obs eq_s _simT1 _simV1.
Proof.
  unfold step_preserves_obs.
  move=> s t ot ov s' Heqs Hstep => //=.
  case Hsc : (s_c s) => [| i c]; first by rewrite stepI Hsc in Hstep.
  case Hdead : (is_deadbranch (s_c s)).
  - rewrite Hsc in Hdead.
    do 3 eexists.
    split; first exact (sem_refl t).
    + unfold _simT1.
      by rewrite Hdead.
    + unfold _simV1.
      by rewrite Hdead.
    + rewrite <-Hsc in Hdead.
      by apply (dead_step Heqs Hdead Hstep).
  - exists [:: ot], [:: ov].
    have [t' [Hstept Heqs']] := (live_step Heqs (negbT Hdead) Hstep).
    exists t'.
    rewrite Hsc in Hdead.
    split; try exact.
    + by apply sem_step1.
    + unfold _simT1.
      by rewrite Hdead.
    + unfold _simV1.
      by rewrite Hdead.
Qed.


Lemma H_eq_s_initial:
  eq_s_initial (compile := pass) eq_s.
Proof.
  move=> ps pt inp [= pass].
  split => //; move: pass; destruct pt.
  - by move=> [=] -> //.
  - by move=> [=] //= _ -> _ //.
Qed.


Lemma H_eq_s_final:
  eq_s_final eq_s.
Proof.
  move=> s t [Hct Hvm Hmem] //=.
  move/eqP/size0nil => Hsc.
  move: Hsc Hct => -> //=.
  by unfold semantics.final => -> //.
Qed.


Lemma preservation_obs:
  preserves_obs (compile := pass) (simT := _simT _simT1) (simVIdx := _simVIdx _simT1) (simV := _simV _simT1 _simV1).
Proof.
  apply (lift_step_preserves_obs H_eq_s_initial H_eq_s_final step_preservation).
Qed.


End PRESERVATION.
