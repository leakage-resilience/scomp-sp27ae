From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.
From Coq Require Import Equality.


Require Import
  semantics
  syntax
  utils
  utils_facts
  var
.
Require Import language.
Existing Instance Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(* Equality on a set of variables. *)

Lemma eq_onS s_out s s':
  eq_on s_out s s' -> eq_on s_out s' s.
Proof.
  unfold eq_on.
  intros Heq x Hmem.
  symmetry.
  apply Heq.
  apply Hmem.
Qed.

Lemma eq_onT s_out s s' s'':
  eq_on s_out s s' -> eq_on s_out s' s'' -> eq_on s_out s s''.
Proof.
  unfold eq_on.
  intros Hss' Hs's'' x Hmem.
  transitivity (Mr.get s' x).
  + apply Hss'. apply Hmem.
  + apply Hs's''. apply Hmem.
Qed.

Lemma eq_on_cat s0 s1 vm vm' :
  eq_on (Sr.union s0 s1) vm vm' ->
  eq_on s0 vm vm' /\ eq_on s1 vm vm'.
Proof.
  move=> h. split=> y hy; apply: h; by rewrite SrD.F.union_b hy // orbT.
Qed.

Lemma eq_on_add elt s vm vm' :
  eq_on (Sr.add elt s) vm vm' ->
  eq_on s vm vm'.
Proof.
  move => h x hmem.
  apply h.
  by apply SrP.add_mem_3.
Qed.

Lemma get_eq_on vm vm' i S:
  eq_on (Sr.add i S) vm vm' ->
  Mr.get vm i = Mr.get vm' i.
Proof.
  rewrite /eq_on => Heq.
  specialize (Heq i).
  apply Heq, SrExtra.SvP.add_mem_1.
Qed.

Lemma eval_e_eq_on vm vm' e :
  eq_on (free_variables e) vm vm' ->
  eval_e vm e = eval_e vm' e.
Proof.
  elim: e => [// | // | x | op e hind | op e0 hind0 e1 hind1] /=.
  - move=> -> //. by rewrite SrD.F.singleton_b SrExtra.eqbP eqxx.
  - by move=> /hind ->.
  by move=> /eq_on_cat [] /hind0 -> /hind1 ->.
Qed.

Lemma leaks_e_eq_on vm vm' e :
  eq_on (free_variables e) vm vm' ->
  leaks_e vm e = leaks_e vm' e.
Proof.
  elim: e => [// | // | x | op e hind | op e0 hind0 e1 hind1] /=.
  - move=> -> //. by rewrite SrD.F.singleton_b SrExtra.eqbP eqxx.
  - move=> Heq. case op; rewrite (hind Heq) (eval_e_eq_on Heq) => //=.
  - move=> /eq_on_cat [] Heq0 Heq1. specialize (hind0 Heq0). specialize (hind1 Heq1). rewrite (eval_e_eq_on Heq0). rewrite (eval_e_eq_on Heq1).
    by rewrite hind0 hind1.
Qed.

Lemma leaks_mop_eq_on : forall vm vm' xs m os,
    eq_on (SrExtra.sv_of_list id os) vm vm' ->
    leaks_mop vm xs m os = leaks_mop vm' xs m os.
Proof.
  move=>vm vm' xs m os Heq.
  apply leaks_mop_eq.
  split. done.
  induction os as [|o os IH].
  - done.
  - simpl. apply/andP.
    split.
    rewrite (Heq o). done.
    apply: SrExtra.sv_of_list_mem_head.
    apply IH. intros el Hel.
    apply: (Heq el).
    by apply: SrExtra.sv_of_list_mem_tail.
Qed.

Lemma eval_e_set vm e x v' :
  ~~ Sr.mem x (free_variables e) ->
  eval_e (Mr.set vm x v') e = eval_e vm e.
Proof.
  move=> hx.
  apply: eval_e_eq_on => y hy.
  rewrite Mr.set_neq //.
  apply/eqP => ?; subst y.
  by rewrite hy in hx.
Qed.

(* -------------------------------------------------------------------------- *)
(* Facts about leaks_e. *)

Lemma leaks_e_size_ge0 vm e:
  (0 < (size (leaks_e vm e)))%N.
Proof.
  destruct e; rewrite /leaks_e.
  - by lazy.
  - by lazy.
  - by lazy.
  - destruct o;
    destruct (eval_e vm e);
    rewrite size_cat;
    rewrite /size;
    apply ltn_addl;
    exact (ltn0Sn 0).
  - destruct o;
    destruct (eval_e vm e1);
    destruct (eval_e vm e2);
    rewrite size_cat size_cat;
    rewrite /size;
    apply ltn_addl;
    apply ltn_addl;
    exact (ltn0Sn 0).
Qed.

Lemma last_leaks_eval vm e :
  last Vundef (leaks_e vm e) = eval_e vm e.
Proof.
  destruct e.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct o;
    rewrite /leaks_e;
    destruct (eval_e vm e) eqn:eqe;
    rewrite last_cat //= eqe;
    reflexivity.
  - destruct o;
    rewrite /leaks_e;
    destruct (eval_e vm e1) eqn:eq1;
    destruct (eval_e vm e2) eqn:eq2;
    by rewrite !last_cat //= eq1 // eq2 //.
Qed.

(* -------------------------------------------------------------------------- *)
(* Program semantics. *)

Section SEM_PROP.

Let step_prop s ot ov s' :=
  match s_c s with
  | {| unannot := Iassign x e; |} :: c =>
      [/\ ot = OTnone,
        ov = OVval (leaks_e (s_vm s) e)
        & s' = s_after_assign s c x e
      ]

  | {| unannot := Iload x a e; |} :: c =>
      exists i,
        [/\ eval_e (s_vm s) e = Vint i
          , in_bounds a i
          , is_defined_mem (s_mem s) a i
          , ot = OTaddr a i
          , ov = OVval ((leaks_e (s_vm s) e) ++ [:: Mem.read (s_mem s) a i])
          & s' = s_after_load s c x a i
        ]

  | {| unannot := Istore a e x; |} :: c =>
      exists i,
        [/\ eval_e (s_vm s) e = Vint i
          , in_bounds a i
          , is_defined (Mr.get (s_vm s) x)
          , ot = OTaddr a i
          , ov = OVval ((leaks_e (s_vm s) e)  ++ [:: Mr.get (s_vm s) x])
          & s' = s_after_store s c a i x
        ]

  | {| unannot := Imop rs mop es; |} :: c =>
      exists yvs,
      [/\ eval_mop (s_vm s) mop es yvs
        , length rs = length yvs
        , ot = OTnone
        , ov = OVval (leaks_mop (s_vm s) rs mop es)
          & s' = s_after_regwrites s c (zip rs yvs)
      ]

  | {| unannot := Iif e c0 c1; |} :: c =>
      exists b,
        [/\ eval_e (s_vm s) e = Vbool b
          , ot = OTbranch b
          , ov = OVval (leaks_e (s_vm s) e)
          & s' = with_c s ((if b then c0 else c1) ++ c)
        ]

  | {| unannot := Iwhile e c0; |} :: c =>
      exists b,
        [/\ eval_e (s_vm s) e = Vbool b
          , ot = OTbranch b
          , ov = OVval (leaks_e (s_vm s) e)
          & s' = with_c s (if b then c0 ++ (s_c s) else c)
        ]

  | [::] => False
  end.

Lemma stepI s ot ov s' :
  step s ot ov s' <-> step_prop s ot ov s'.
Proof.
  split; unfold step_prop; intro H.
  { destruct H; simpl in *; rewrite H; subst;
      try eeauto; try (rewrite H; eeauto).
  }
  { remember (s_c s) as SC.
    symmetry in HeqSC.
    destruct SC; try intuition.
    destruct a; clear X0.
    remember unannot as UA.
    destruct UA; simpl; eauto.
    { destruct H as [ ]; subst; econstructor; eauto. }
    { destruct H as [? []]; subst; econstructor; eauto. }
    { destruct H as [? []]; subst; eapply step_store; eauto. }
    { destruct H as [? []]; subst; econstructor; eauto. }
    { destruct H as [? []]; subst; econstructor; eauto. }
    { destruct H as [b []]; subst; eapply step_while; eauto.
      destruct b; simpl; eauto.
      rewrite HeqSC; auto.
    }
  }
Qed.

Lemma step_code s ot ov s':
  step s ot ov s' ->
  exists i c,
    s_c s = i::c.
Proof.
  intros Hstep.
  case Hni: (s_c s) => [| i c].
  + apply stepI in Hstep. unfold step_prop in Hstep. rewrite Hni in Hstep. contradiction.
  + exists i, c. reflexivity.
Qed.

End SEM_PROP.

Lemma sem_step1 s ot ov s' :
  step s ot ov s' -> sem s [:: ot] [:: ov] s'.
Proof.
  intros.
  destruct H; eauto; subst; simpl;
  solve [ (econstructor; eauto;
           econstructor; eauto;
           econstructor; eauto)
        | (econstructor; eauto;
           eapply step_while; eauto;
           econstructor; eauto) ].
Qed.

Lemma sem_step1It s s' ot ovs :
  sem s [:: ot] ovs s' ->
  exists2 ov, ovs = [:: ov] & step s ot ov s'.
Proof.
  intros H.
  dependent destruction H.
  dependent destruction H0.
  eexists; eauto.
Qed.

Lemma sem_step1Iv s s' ots ov :
  sem s ots [:: ov] s' ->
  exists2 ot, ots = [:: ot] & step s ot ov s'.
Proof.
  intros H.
  dependent destruction H.
  dependent destruction H0.
  eexists; eauto.
Qed.

Lemma sem_trans s s' s'' OT OT' OV OV' :
  sem s OT OV s' ->
  sem s' OT' OV' s'' ->
  sem s (OT ++ OT') (OV ++ OV') s''.
Proof.
  intros H.
  induction H; intros; simpl; eauto.
  econstructor; eauto.
Qed.

Lemma sem_obs_len :
  forall s s' ots ovs,
    sem s ots ovs s' -> size ots = size ovs.
Proof.
  move => s s' ots ovs sem.
  induction sem. trivial.
  simpl. auto.
Qed.

Lemma surj_machine s :
  {| s_c := s_c s; s_vm := s_vm s; s_mem := s_mem s; |} = s.
Proof. by move: s => []. Qed.

(*
Lemma initial_machineP p st :
  is_initial_machine p (initial_machine p st).
Proof. done. Qed.

Lemma is_initial_machineI p m :
  is_initial_machine p m ->
  m = initial_machine p (m_st m).
Proof.
  rewrite /is_initial_machine /initial_machine => <-.
  by rewrite surj_machine.
Qed.
*)

(* TODO: adapt
Lemma get_initial_state p xs vs x :
  has (fun y => y == x) xs ->
  Mr.get (s_vm (initial_state p xs vs)) x = nth Vundef vs (find (fun y => y == x) xs).
Proof.
  rewrite /=.
  elim: vs xs => [ | v vs ih ] [ | r xs ] //.
  - by rewrite Mr.get_const nth_nil.
  rewrite /= Mr.get_set; case: eqP => //.
  by move => ? /ih{}ih.
Qed.
*)

Lemma deterministic_eval_mops' s1 s2 mop0 os vs1 vs2 :
  eval_mop (s_vm s1) mop0 os vs1 ->
  eval_mop (s_vm s2) mop0 os vs2 ->
  eq_on (SrExtra.sv_of_list id os) (s_vm s1) (s_vm s2) ->
  vs1 = vs2.
Proof.
  have solve_unary: forall rx x1 x2,
      x1 = Mr.get (s_vm s1) rx ->
      x2 = Mr.get (s_vm s2) rx ->
      eq_on (SrExtra.sv_of_list id [:: rx]) (s_vm s1) (s_vm s2) ->
      x1 = x2. {
    move => rx x1 x2 -> -> Heq_on.
    move: (Heq_on rx) => Heq_rx.
    rewrite SrExtra.sv_of_listE /= in Heq_rx.
    by rewrite (Heq_rx (mem_head _ _)) /=.
  }
  have solve_binary: forall rx ry x1 y1 x2 y2,
      x1 = Mr.get (s_vm s1) rx ->
      y1 = Mr.get (s_vm s1) ry ->
      x2 = Mr.get (s_vm s2) rx ->
      y2 = Mr.get (s_vm s2) ry ->
      eq_on (SrExtra.sv_of_list id [:: rx; ry]) (s_vm s1) (s_vm s2) ->
      x1 = x2 /\ y1 = y2. {
    move => rx ry x1 y1 x2 y2 -> -> -> -> Heq_on.
    move: (Heq_on rx) => Heq_rx.
    rewrite SrExtra.sv_of_listE /= in Heq_rx.
    rewrite (Heq_rx (mem_head _ _)) /=.
    move: (Heq_on ry) => Heq_ry.
    rewrite SrExtra.sv_of_listE /= in Heq_ry.
    have Hmem : ry \in [:: rx; ry]. {
      rewrite !in_cons eq_refl.
      apply /orP; right.
      by apply /orP; left.
    }
    by rewrite (Heq_ry Hmem).
  }

  move => H.
  dependent destruction H.

  1-2: by (
    intro K; dependent destruction K => Heq_on;
    move: (solve_unary _ _ _ H H0 Heq_on) => [=] ->
  ).
  all: by (
    intro K; dependent destruction K => Heq_on;
    move: (solve_binary _ _ _ _ _ _ H H0 H1 H2 Heq_on) => [] [=] -> [=] ->
  ).
Qed.

(* TODO: could be already in a list library *)
Lemma length_nil T (ls: seq T) : length ls = 0%nat -> ls = nil.
  destruct ls; simpl; intros; auto with *; eauto.
Qed.

Lemma sem_reflI s :
  s_c s = [::] -> sem s [::] [::] s.
Proof.
  intros; econstructor.
Qed.

Lemma sem_reflI_inv s s' :
  s_c s = [::] -> sem s [::] [::] s' -> s = s'.
Proof.
  intros H H0; destruct s; subst.
  dependent destruction H0; subst; auto.
Qed.

Lemma sem_reflI_inv_ots s s' ovs:
  sem s [::] ovs s' -> ovs = [::].
Proof.
  intros H; dependent destruction H; simpl; auto.
Qed.

Lemma sem_reflI_inv_ovs s s' ots:
  sem s ots [::] s' -> ots = [::].
Proof.
  intros H; dependent destruction H; simpl; auto.
Qed.

(* TODO: Superseeded by same lemma in language.v *)
Lemma deterministic_sem s s1 s2 ots1 ots2 ovs1 ovs2 :
  sem s ots1 ovs1 s1 ->
  sem s ots2 ovs2 s2 ->
  length ots1 = length ots2 ->
  ots1 = ots2 /\ ovs1 = ovs2 /\ s1 = s2.
Proof.
  remember (length ots1) as n.
  revert Heqn s s1 s2 ovs1 ots2 ovs2.
  revert ots1.
  induction n; simpl.
  { intros ots1 Heqn s s1 s2 ovs1 ots2 ovs2 H H0 H1.
    symmetry in H1, Heqn.
    eapply length_nil in H1; eauto; subst.
    eapply length_nil in Heqn; eauto; subst.
    dependent destruction H0; auto.
    dependent destruction H; auto. }
  { intros ots1 Heqn s s1 s2 ovs1 ots2 ovs2 H H0 H1.
    destruct ots2; simpl in *.
    auto with *.
    inversion H1; subst; clear H1.
    specialize (IHn ots2 erefl).
    destruct ots1; simpl in *.
    auto with *.
    inversion Heqn; subst.
    dependent destruction H.
    dependent destruction H1.
    have H4 : [/\ t = t0, ov0 = ov & s'0 = s'].
    { eapply (step_deterministic s s'0 s'); eauto. }
    destruct H4 as [H4 H5 H6]; subst; clear H H1.
    have H4 : ots2 = ots1 /\ ovs0 = ovs /\ s2 = s1.
    { eapply IHn; eauto. }
    destruct H4 as [H4 [H5 H6]]; subst; auto. }
Qed.






Lemma step_deterministic' s t i ia cr cr' s' ot ov:
  step s ot ov s' ->
  s_mem s = s_mem t ->
  s_vm s = s_vm t ->
  s_c s = {| unannot := i ; annot := ia |} :: cr ->
  s_c t = {| unannot := i ; annot := ia |} :: cr' ->
  exists t',
    [/\ step t ot ov t'
      , s_vm s' = s_vm t'
      , s_mem s' = s_mem t'
        & s_c t' = match i with
                   | Iwhile b c =>
                       if eval_e (s_vm s) b is Vbool true
                       then c ++ s_c t
                       else cr'
                   | Iif b ct ce =>
                       (if eval_e (s_vm s) b is Vbool true
                        then ct
                        else ce)
                         ++ cr'
                   | _ => cr'
                   end
    ].
Proof.
  move=> Hstep Hmem Hvm Hcs Hct.
  move: Hstep.
  rewrite stepI Hcs.
  rewrite Hvm.
  destruct i.
  - move => [] -> -> ->.
    eexists.
    split
    ; first (eapply step_assign; exact Hct)
    ; try easy.
    by rewrite //= Hvm.
  - move => [] i [] ? ? ? -> -> ?.
    eexists.
    split.
    + eapply step_load
      ; first exact Hct
      ; try easy.
      * by rewrite <-Hmem.
      * by rewrite Hmem.
    + subst s' => //=.
      by rewrite <-Hvm, <-Hmem.
    + by subst s'.
    + done.
  - move => [] i [] ? ? ? -> -> ?.
    eexists.
    split
    ; first eapply step_store
    ; first exact Hct
    ; try easy.
    + by subst s' => //=.
    + subst s'.
      by rewrite //= Hmem Hvm.
  - move => [] i [] Hemop ? -> -> ?.
    eexists.
    split
    ; first by eapply step_mop
    ; first exact Hct
    ; first exact Hemop.
    + subst s'.
      induction (zip l i) => //.
      by rewrite //= IHl1.
    + subst s'.
      by induction (zip l i).
    + done.
  - move => [] b [] Heval -> -> ?.
    eexists.
    split.
    + eapply step_if.
      * exact Hct.
      * exact Heval.
      * done.
    + by subst s'.
    + by subst s'.
    + by rewrite Heval.
  - move => [] b [] Heval -> -> ?.
    eexists.
    split.
    + eapply step_while.
      * exact Hct.
      * exact Heval.
      * done.
    + by subst s'.
    + by subst s'.
    + by rewrite Heval.
Qed.



Lemma step_code' s ot ov s' i c:
  s_c s = i :: c ->
  step s ot ov s' ->
  s_c s' =  match unannot i with
            | Iwhile b l =>
                if eval_e (s_vm s) b is Vbool true
                then l ++ (i :: c)
                else c
            | Iif b ct ce =>
                (if eval_e (s_vm s) b is Vbool true
                 then ct
                 else ce)
                  ++ c
            | _ => c
            end.
Proof.
  move=> Hc Hstep.
  destruct i as [ia ii].
  have [s'' [Hstep' Hvm' Hmem' Hss']] := (step_deterministic' Hstep erefl erefl Hc Hc).
  suff -> : s' = s'' by destruct ii ; last rewrite Hss' Hc.
  eapply step_deterministic
  ; [ exact Hstep
    | exact Hstep' ].
Qed.
