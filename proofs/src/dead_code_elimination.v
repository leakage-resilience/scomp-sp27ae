(* -------------------------------------------------------------------------- *)
(* Dead code elimination. *)
(* Given a set of variables, remove all code that is not necessary to compute
   their value.
   We only remove assignments, mops and loads.
*)
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

(* Return [s_in]. *)
Context (analyze_i : iinfo -> Sr.t).

Section CMD.
  Context (check_i : Sr.t -> instr -> Sr.t -> bool).

  Definition check_ii (i : instr_i) (after : Sr.t) : bool :=
     check_i (analyze_i (annot i)) (unannot i) after.

  Definition get_current (c : code) (s_out : Sr.t) :=
    match c with
    | [::] => s_out
    | i :: _ => analyze_i (annot i)
    end.

  Fixpoint check_c (c : code) (s_out : Sr.t) : bool :=
    match c with
    | [::] => true
    | i::c => check_ii i (get_current c s_out) && check_c c s_out
    end.

  Context (dead_code_i : Sr.t -> instr -> Sr.t -> seq instr).

  Definition dead_code_ii (i : instr_i) (s_out : Sr.t) : code :=
    map
      (mk_annotated (annot i))
      (dead_code_i (analyze_i (annot i)) (unannot i) s_out).

  Fixpoint dead_code_c (c : code) (s_out : Sr.t) :=
    match c with
    | [::] => [::]
    | i :: c => dead_code_ii i (get_current c s_out) ++ dead_code_c c s_out
    end.

End CMD.

(* Ensure correctness of the analysis *)
Fixpoint check_i (before : Sr.t) (i : instr) (after : Sr.t) : bool :=
  match i with
  | Iassign x e =>
    let pre :=
      if Sr.mem x after then
        Sr.union (Sr.remove x after) (free_variables e)
      else after in
    Sr.subset pre before

  | Iload x a e =>
    let pre :=
     if Sr.mem x after then
       Sr.union (Sr.remove x after) (free_variables e)
     else after
    in
    Sr.subset pre before

  | Istore a e x =>
    let pre := Sr.union after (Sr.add x (free_variables e)) in
    Sr.subset pre before

  | Imop rs mop es =>
    let rs := (SrExtra.sv_of_list id rs) in
    let es := (SrExtra.sv_of_list id es) in
    let pre :=
      if Sr.disjoint rs after
      then after
      else Sr.union (Sr.diff after rs) es
    in Sr.subset pre before

  | Iif e c1 c0 =>
    [&& Sr.subset (get_current c1 after) before
      , Sr.subset (get_current c0 after) before
      , Sr.subset (free_variables e) before
      , check_c check_i c1 after
      & check_c check_i c0 after]

  | Iwhile e c =>
    [&& Sr.subset (get_current c before) before
      , Sr.subset after before
      , Sr.subset (free_variables e) before
      & check_c check_i c before]
  end.

Definition is_dead_instr (i : instr) (livevars : Sr.t) : bool :=
  match i with
  | Iassign x _ | Iload x _ _ =>
    ~~ Sr.mem x livevars

  | Imop rs _ _ =>
    let rs := (SrExtra.sv_of_list id rs) in
    Sr.disjoint rs livevars

  | _ => false
  end.

Fixpoint dead_code_i (s_in : Sr.t) (i : instr) (livevars : Sr.t) : seq instr :=
  if is_dead_instr i livevars then [::]
  else match i with
  | Iif e c1 c0 =>
      let c1 := dead_code_c dead_code_i c1 livevars in
      let c0 := dead_code_c dead_code_i c0 livevars in
      [:: Iif e c1 c0 ]

  | Iwhile e c => [:: Iwhile e (dead_code_c dead_code_i c s_in) ]

  | _ => [:: i]
  end.

Definition dead_code_p (s_out : Sr.t) (p : prog) : prog :=
  map_p_prog (fun c => dead_code_c dead_code_i c s_out) p.

Section PROOF.

Context
  (*(p_s p_t : prog)*)
  (p_out : Sr.t)
  (*(hcompile : dead_code_p p_out p_s = p_t)*)
.

Lemma dead_code_iE s_in i s_out :
 dead_code_i s_in i s_out =
  if is_dead_instr i s_out then [::]
  else match i with
  | Iif e c1 c0 =>
      let c1 := dead_code_c dead_code_i c1 s_out in
      let c0 := dead_code_c dead_code_i c0 s_out in
      [:: Iif e c1 c0 ]

  | Iwhile e c => [:: Iwhile e (dead_code_c dead_code_i c s_in) ]

  | _ => [:: i]
  end.
Proof. by case: i. Qed.

Fixpoint all_dead (c : code) (s_out : Sr.t) :=
  match c with
  | [::] => true
  | i :: c => is_dead_instr (unannot i) (get_current c s_out) && all_dead c s_out
  end.


Definition Tvobs (ov : v_obs) : v_obs := ov.

Definition eq_s (s t : state) :=
  [/\ s_c t = dead_code_c dead_code_i (s_c s) p_out
    , eq_on (get_current (s_c s) p_out) (s_vm s) (s_vm t)
    , s_mem s = s_mem t
    & check_c check_i (s_c s) p_out].

Lemma eq_s_final s t:
  eq_s s t ->
  final s ->
  final t.
Proof.
  intros [Hc _ _ _] Hfins.
  rewrite (finsc Hfins) /= in Hc.
  rewrite /final /Source /semantics.final Hc //=.
Qed.

Fixpoint n_step_dead (c : code) : nat :=
  match c with
  | [::] => 0
  | i::c_rest =>
    if is_dead_instr (unannot i) (get_current c_rest p_out)
    then S (n_step_dead (c_rest))
    else 0%nat
  end
.

(* maybe use get_current instead of analyze_i *)
Definition  n_step_fun (c : code) : nat :=
  S (n_step_dead c)
.

Fixpoint next_c_fun (c : code) (ots : seq t_obs) : code :=
  match c with
  | [::] => [::]
  | i::c_rest => if is_dead_instr (unannot i) (analyze_i (annot i))
                 then next_c_fun c_rest (List.tl ots)
                 else match (unannot i) with (* match i, decide which branch to take in if/while depending on timing observation, then do c1::c_rest *)
                      | Iif e c1 c0 => match ots with
                                       | [:: OTbranch b ; _] => if b then c1++c_rest else c0++c_rest
                                       | _ => [::] (* this can never happen *)
                                       end
                      | Iwhile e cbody => match ots with
                                          | [:: OTbranch b ; _] => if b then cbody ++ [:: i] ++ c_rest else c_rest
                                          | _ => [::] (* this can never happen *)
                                          end
                      | _ => c_rest
                      end
  end
.

Definition next_is_dead s :=
  match (s_c s) with
    | [::] => false
    | i :: c => is_dead_instr (unannot i) (get_current c p_out)
  end.


Lemma eq_s_dead_write x s_out s v:
  ~ Sr.In x s_out ->
  eq_on s_out (s_vm s) (s_vm (write_reg s x v)).
Proof.
  move=>hnin z zmem.
  rewrite Mr.get_set.
  case: ifP=>// /eqP xz.
  move: xz hnin=>->/SrExtra.Sv_memP /negP //.
Qed.

(* TODO: move these four to utils *)
Lemma length_eq_size {T} (xs : list T):
  length xs = size xs.
Proof.
  rewrite -![length _]/(size _).
  reflexivity.
Qed.

Lemma get_current_cat c1 c2 s_out :
  get_current (c1 ++ c2) s_out = get_current c1 (get_current c2 s_out).
Proof. by case: c1. Qed.

Lemma check_c_cat c1 c2 s_out :
 check_c check_i (c1 ++ c2) s_out =
  check_c check_i c1 (get_current c2 s_out) &&
  check_c check_i c2 s_out.
Proof. by elim: c1 => //= i c1 ->; rewrite andbA get_current_cat. Qed.

Lemma check_c_cat1 c1 c2 s_out :
 check_c check_i (c1 ++ c2) s_out ->
 check_c check_i c1 (get_current c2 s_out).
Proof. by rewrite check_c_cat => /andP []. Qed.

Lemma dead_code_cat c1 c2 s_out :
  dead_code_c dead_code_i (c1 ++ c2) s_out =
  dead_code_c dead_code_i c1 (get_current c2 s_out) ++ dead_code_c dead_code_i c2 s_out.
Proof. by elim: c1 => //= i l ->; rewrite get_current_cat catA. Qed.

Lemma eq_on_write S vm1 vm2 x v :
  eq_on (Sr.remove x S) vm1 vm2 ->
  eq_on S (Mr.set vm1 x v) (Mr.set vm2 x v).
Proof.
  move=> heqs. unfold eq_on => x' hxmem.
  rewrite !Mr.get_set.
  case: eqP => // hne.
  apply Sr.mem_spec in hxmem.
  apply/heqs/Sr.mem_spec/Sr.remove_spec; split; auto.
Qed.

Lemma eq_onI S S' vm1 vm2 : Sr.Subset S S' -> eq_on S' vm1 vm2 -> eq_on S vm1 vm2.
Proof. by move=> hsub heq z /Sr.mem_spec hz; apply/heq/Sr.mem_spec/hsub. Qed.


(* c can always be split in a sequence of dead instructions followed by the rest of c (empty or at least one alive instructions followed by arbitrary dead or alive instructions). *)
Lemma check_all_dead c :
  check_c check_i c p_out ->
  exists cd ca,
  [/\ c = cd ++ ca
    , all_dead cd (get_current ca p_out)
    & if ca is i :: c1 then ~is_dead_instr (unannot i) (get_current c1 p_out) else true].
Proof.
  elim: c => //=.
  + by move=> _; exists [::], [::].
  move=> i c' hrec. rewrite /check_ii /= => /andP[] hchi hch.
  case: (boolP (is_dead_instr (unannot i) (get_current c' p_out))).
  + move=> hdi. have [cd' [ca' [hc' hcd' hca']] ] := hrec hch. subst c'.
    exists (i::cd'), ca'; split => //=.
    + by rewrite -get_current_cat hdi.
  by move=> /negP hn; exists [::], (i::c').
Qed.

Lemma eq_s_dead_writes xs s_out s c xvs:
  length xs = length xvs ->
  Sr.disjoint (SrExtra.sv_of_list id xs) s_out ->
    eq_on s_out (s_vm s) (s_vm (s_after_regwrites s c (zip xs xvs))).
Proof.
  unfold s_after_regwrites.
  elim: xs xvs => [| a xs IH] [| b ys] //=.
  specialize (IH ys).
  move=> Hlen Hdisj x xmem //=.
  rewrite Mr.get_set ifF.
  + rewrite IH =>//=.
    * by apply eq_add_S.
    * apply (@SrExtra.disjoint_w _ (SrExtra.sv_of_list id (a :: xs)) _) => //=.
      unfold SrExtra.Sv.Subset => el /SrExtra.Sv_memP elin.
      apply/SrExtra.Sv_memP.
      rewrite SrExtra.sv_of_list_cons.
      by apply SrP.add_mem_3.
  + suff : ~~ Sr.mem a s_out.
    - move=> Hnmem.
      apply /eqP => eqxa.
      rewrite <-eqxa in xmem.
      move: Hnmem=> /negP.
      contradiction.

    have : Sr.mem a (SrExtra.sv_of_list id (a :: xs))
      by rewrite SrExtra.sv_of_list_mem_head.
    move=> Hmema.
    rewrite <- SrExtra.disjoint_singleton.
    apply (@SrExtra.disjoint_w _ (SrExtra.sv_of_list id (a :: xs)) _) => //=.
    unfold SrExtra.Sv.Subset => xelt xina.
    have -> : xelt = a
      by symmetry; apply SrExtra.SvF.singleton_1.
    apply /SrExtra.Sv_memP.
    by rewrite SrExtra.sv_of_list_mem_head.
Qed.

Lemma eq_mem_on_dead_write s c rsvs:
  s_mem (s_after_regwrites s c rsvs) = s_mem s.
Proof. elim : rsvs => //=. Qed.

Lemma step_next_dead s s' t ot ov:
  step s ot ov s' ->
  next_is_dead s ->
  eq_s s t ->
  eq_s s' t.
Proof.
  rewrite /eq_s /next_is_dead.
  intros Hsteps Hdeadstep [Hcc Heqst Heqstmem Hcheck].
  case Hc: (s_c s) Hsteps Hdeadstep => [| [ii i] c] => //.
  rewrite stepI Hc.
  case Hi: i => // [ x e | x a e | ys m xs ].
  {
    move => []Hot Hov ->.
    rewrite /unannot /annot => Hidead.
    split.
    (* TODO: make it a lemma for the other instruction *)
    + rewrite Hcc Hc /=.
      rewrite /dead_code_ii /=.
      by rewrite dead_code_iE Hi Hidead /=.
    + simpl in Hidead.
      rewrite /s_after_assign /=.
      apply: eq_onT.
      apply eq_onS.
      apply eq_s_dead_write.
      move => /Sr.mem_spec K.
      by rewrite K in Hidead.
      (* s ~ t at i but we need to show s ~ t at c *)

      apply: eq_onI Heqst.
      move: Hcheck.
      rewrite Hc Hi /= /check_ii /=.
      by rewrite (negbTE Hidead) => /andP [] /Sr.subset_spec.
    + done.
    + move: Hcheck.
      by rewrite Hc /= => /andP [_ me].
  }
  {
    move => []idx [] Hval Hinbounds Hdefined Hot Hov ->.
    rewrite /unannot /annot => Hidead.
    split.
    + rewrite Hcc Hc /=. (* same as in Iassign *)
      rewrite /dead_code_ii /=.
      by rewrite dead_code_iE Hi Hidead /=.
    + simpl in Hidead. (* same as in Iassign *)
      rewrite /s_after_assign /=.
      apply: eq_onT.
      apply eq_onS.
      apply eq_s_dead_write.
      move => /Sr.mem_spec K.
      by rewrite K in Hidead.
      (* s ~ t at i but we need to show s ~ t at c *)
      apply: eq_onI Heqst.
      move: Hcheck.
      rewrite Hc Hi /= /check_ii /=.
      by rewrite (negbTE Hidead) => /andP [] /Sr.subset_spec.
    + done. (* same as in Iassign *)
    + move: Hcheck. (* same as in Iassign *)
      by rewrite Hc /= => /andP [_ me].
  }
  {
    move => []yvs [] Hyvs Hylen Hot Hov ->.
    rewrite /unannot /annot => Hidead.
    split.
    + rewrite Hcc Hc /=. (* same as in Iassign *)
      rewrite /dead_code_ii /=.
      by rewrite dead_code_iE Hi Hidead /=.
    + simpl in Hidead. (* NOT THE same as in Iassign *)
      apply: eq_onT.
      apply eq_onS.
      apply (eq_s_dead_writes s c Hylen Hidead).
      (* s ~ t at i but we need to show s ~ t at c *)
      apply: eq_onI Heqst.
      move: Hcheck.
      rewrite Hc Hi /= /check_ii /=.
      by rewrite Hidead => /= => /andP [] /Sr.subset_spec.
    + rewrite -Heqstmem. apply /eq_mem_on_dead_write.
    + move: Hcheck. (* same as in Iassign *)
      by rewrite Hc /= => /andP [_ me].
  }
Qed.

Lemma onedeadstep s s' ot ov:
  step s ot ov s' ->
  next_is_dead s ->
  (match s_c s with
    | [::] => [::]
    | i::c => c
   end) = s_c s'.
Proof.
  move => /stepI.
  rewrite /next_is_dead.
  case: (s_c s)=> [| i c]//.
  rewrite /is_dead_instr.
  case: i => // ia [] //=.
  + by move => > [] _ _ ->.
  + by move => > [] ? [] _ _ _ _ _ ->.
  by move => > [] ? [] _  _ _ _  ->.
Qed.

Lemma nstep_dead_next s s' ot ov:
  step s ot ov s' ->
  next_is_dead s ->
  n_step_dead (s_c s) = (n_step_dead (s_c s')) .+1.
Proof.
  intros Hstep Hnextdead.
  have h:=(onedeadstep Hstep Hnextdead).
  move: Hnextdead.
  rewrite /next_is_dead /n_step_dead.
  case hc : (s_c s) => //.
  move => ->.
  rewrite -h hc.
  done.
Qed.

Lemma dead_step:
  forall s s' t ots_s ovs_s,
  eq_s s t  ->
  sem s ots_s ovs_s s' ->
  size ots_s = n_step_fun (s_c s) ->
  exists s_d ots_sd ovs_sd ot_l ov_l,
    [/\ sem s ots_sd ovs_sd s_d
      , size ots_sd = n_step_dead (s_c s)
      , negb (next_is_dead s_d)
      , step s_d ot_l ov_l s'
      , ots_s = ots_sd ++ [::ot_l]
      , ovs_s = ovs_sd ++ [::ov_l]
      & eq_s s_d t].
  Proof.
    intros s s' t ots_s ovs_s.
    elim: ots_s s s' t ovs_s => //.
    intros ot_s ots_s Hrec s s' t ovs_s.
    move => Heq /semI []ov []ovs_s' [] -> [] si.
    move => Hstepi /semI.
    case Hots_s: ots_s => [| ot_sj ots_sj]. {
      move => []-> -> /= [] zero_dead.
      exists s, [::], [::], ot_s, ov.
      split => //; first by apply /semI.
      rewrite /next_is_dead.
      case: (s_c s) zero_dead => //= i c.
      case: ifP => //.
    }
    move => [] ov_sj [] ovs_sj.
    move => [] -> [] sj Hstepj Hsemj /= [] Hdeadj.
    have Hnext_dead: next_is_dead s. {
      rewrite /next_is_dead.
      case: (s_c s) Hdeadj => //= i c.
      by case: ifP.
    }
    have Heq':= step_next_dead Hstepi Hnext_dead Heq.
    subst ots_s.
    rewrite (nstep_dead_next Hstepi) // in Hdeadj.
    have := Hrec _ _ _ _ Heq' (sem_trans Hstepj Hsemj) Hdeadj.
    move => [] sd [] ots_sd [] ovs_sd [] ot_l [] ov_l [].
    move => Hsemd Hnstepd Hnext_dead_sd Hstepd.
    move => -> -> Heq_sd.
    exists sd, (ot_s :: ots_sd), (ov :: ovs_sd), ot_l, ov_l.
    split => //.
    by apply sem_trans with (s' := si).
    by rewrite (nstep_dead_next Hstepi) //= Hnstepd.
Qed.

(* TODO: move this to the right place*)
Lemma sem_reflI_inv' s s' ots ovs:
  s_c s = [::] -> sem s ots ovs s' -> s = s'.
Proof.
  intros H H0.
  elim: H0 H => //.
  move: s s' ots ovs => _ _ _ _.
  move => s s' s'' ot ov ots ovs /stepI Hstep Hsem Hs' Hs.
  move: Hstep.
  by rewrite Hs.
Qed.

(* TODO: move this to the right place*)
Lemma sem_reflI_inv'' s s' ots ovs:
  s_c s = [::] -> sem s ots ovs s' ->
  [/\ s = s'
    , ots =[::]
    & ovs= [::]].
Proof.
  intros H H0.
  elim: H0 H => //.
  move: s s' ots ovs => _ _ _ _.
  move => s s' s'' ot ov ots ovs /stepI Hstep Hsem Hs' Hs.
  move: Hstep.
  by rewrite Hs.
Qed.

Lemma isdead_n_step_fun s:
  negb (next_is_dead s) ->
  n_step_fun (s_c s)= 1%N.
Proof.
  move => H_notdead.
  rewrite /n_step_fun /n_step_dead.
  rewrite /next_is_dead in H_notdead.
  case: (s_c s) H_notdead => [//| i c] /=.
  move /negbTE => Hnd.
  by rewrite Hnd; reflexivity.
Qed.

Lemma live_head_instr:
  forall i c_rest p_out,
    is_dead_instr (unannot i) (get_current c_rest p_out) = false ->
    let livevars := (get_current c_rest p_out) in
    let s_in := (analyze_i (annot i)) in
   let i_t : instr :=  match unannot i with
   | Iif e c1 c0 =>
       let c2 := dead_code_c dead_code_i c1 livevars in
       let c3 := dead_code_c dead_code_i c0 livevars in  Iif e c2 c3
   | Iwhile e c => Iwhile e (dead_code_c dead_code_i c s_in)
   | _ =>  (unannot i)
   end in
   dead_code_c dead_code_i (i :: c_rest) p_out = (mk_annotated (annot i) i_t)  :: dead_code_c dead_code_i c_rest p_out.
(* maybe there is still something not working? Reason: dismatch later in  *)
Proof.
  intros [annot ii] c_rest pout notdead_i.
  simpl.
  unfold is_dead_instr.
  destruct ii; try easy; unfold dead_code_ii; simpl in *.
  + rewrite notdead_i. easy.
  + rewrite notdead_i. easy.
  + rewrite notdead_i. easy.
Qed.

Lemma step_nonempty s ot_s ov_s s' :
  step s ot_s ov_s s' ->
    exists i rest, s_c s = i :: rest.
Proof.
  intro H.
  destruct s as [s_c s_vm s_mem] eqn : s_eq in |-.
  destruct s_c as [| [annot i] c_rest] eqn : s_c_eqn in |-.
  + unfold step in H.
    simpl in H.
    destruct H; rewrite s_eq s_c_eqn in H; easy.
  exists ({| annot := annot; unannot := i |}), c_rest.
  unfold semantics.s_c.
  rewrite s_eq.
  exact.
Qed.

Definition Pi (i: instr) :=
  forall a c t ot_t ov_t t' s ot_s ov_s s',
    s_c s = {| annot := a; unannot := i|} :: c ->
    eq_s s t ->
    step t ot_t ov_t t' ->
    step s ot_s ov_s s' ->
    n_step_fun (s_c s) = 1%nat ->
    [/\ ot_s = ot_t
      , ov_s = ov_t
     & eq_s s' t'].

Definition Pii i := Pi (unannot i).
Definition Pc c :=
  forall t ot_t ov_t t' s ot_s ov_s s',
    s_c s = c ->
    eq_s s t ->
    step t ot_t ov_t t' ->
    step s ot_s ov_s s' ->
    n_step_fun (s_c s) = 1%nat ->
    [/\ ot_s = ot_t
      , ov_s = ov_t
     & eq_s s' t'].

Lemma step_fun_not_dead c s_c_i s_c_ii s_c_rest:
  c = ({| annot := s_c_ii; unannot := s_c_i |} :: s_c_rest) ->
  n_step_fun c = 1%nat ->
  is_dead_instr s_c_i (get_current s_c_rest p_out) = false.
Proof.
  move=> ->.
  rewrite /n_step_fun /n_step_dead.
  by case :ifP.
Qed.

Lemma Sr_subset_union_rw s s' s'':
  Sr.subset (Sr.union s s') s''
  -> Sr.subset s s'' /\ Sr.subset s' s''.
Proof.
  move=>/eqP/eqP H.
  rewrite Sr.subset_spec in H.
  split.
  apply Sr.subset_spec=> el Hel.
  apply (@SrP.MP.in_subset (Sr.union s s')).
  + by apply SrExtra.SvF.union_2.
  + done.
  apply Sr.subset_spec=> el Hel.
  apply (@SrP.MP.in_subset (Sr.union s s')).
  + by apply SrExtra.SvF.union_3.
  + done.
Qed.

Lemma inst_eq cs ct sa si sc:
  cs = ({| annot := sa; unannot := si |} :: sc) ->
  n_step_fun cs = 1%nat ->
  ct = dead_code_c dead_code_i cs p_out ->
  exists ta ti tc,
    ct = {| annot := ta; unannot := ti |} :: tc
    /\ [\/ ti = si
      , (exists e c c', si = Iwhile e c /\ ti = Iwhile e c')
       | (exists c et ef et' ef', si = Iif c et ef /\ ti = Iif c et' ef') ].
Proof.
  move=> Hcs hdead hc.
  apply (step_fun_not_dead Hcs) in hdead.
  pose sinstr := {| annot := sa; unannot := si |}.
  have Huii : (unannot sinstr) = si by done.
  rewrite <-Huii in hdead.
  unfold dead_code_c.
  pose proof (live_head_instr hdead) as H.
  simpl in H.
  move : hc.
  unfold dead_code_c.
  rewrite Hcs H.
  case ct; first easy.
  move=> [ta ti] tc.
  unfold mk_annotated=>[= Hannot_eq Hinst_eq Hc_eq].
  exists ta, ti, tc.
  split; first done.
  destruct si; try by apply Or31.
  + apply Or33. exists e, l, l0. eauto.
  + apply Or32. eauto.
Qed.

Lemma Hassign : forall x e, Pi (Iassign x e).
Proof.
  move=> x e a c t ot_t ov_t t' s ot_s ov_s s' Hsc [Hdead_code Hvm Hmem Hcheck] + + Hnsf.
  have [ta [ti [tc [Htc ]]]] := (inst_eq Hsc Hnsf Hdead_code).
  case=>[Hti | []?[]?[]?[]// | []?[]?[]?[]?[]?[]//].
  rewrite !stepI Hsc Htc Hti.
  move=>[-> -> Htalive] [-> -> Hsalive].
  have //= /Bool.negb_false_iff Hnotdead := step_fun_not_dead Hsc Hnsf.

  move: Hcheck.
  rewrite Hsc /check_c {1}/check_i {1}/check_ii /unannot /annot // Hnotdead => /andP [Hcheck Hcheck'].
  have [Hremove_x Hfv_alive] := (Sr_subset_union_rw Hcheck).

  split; try done.
  - congr OVval.
    apply leaks_e_eq_on.
    apply: eq_onI.
    apply /Sr.subset_spec.
    exact Hfv_alive.
  - move: Hvm.
    by rewrite /get_current Hsc /annot.
  - split; try by subst.
    + subst.
      move: Hdead_code.
      rewrite /dead_code_c Htc Hsc /dead_code_i /dead_code_ii //= Hnotdead //=.
      by move=>[= _ ->].
    + subst.
      rewrite /s_after_assign /with_c /s_c //=.
      rewrite (@eval_e_eq_on (s_vm s) (s_vm t)).
      * apply eq_on_write.
        apply: eq_onI.
        by move: Hremove_x => /Sr.subset_spec // H; exact H.
        by move: Hvm; rewrite Hsc /get_current.
      * apply: eq_onI.
        move: Hfv_alive => /Sr.subset_spec // H; exact H.
        by move: Hvm; rewrite Hsc /get_current.
Qed.

Lemma Sr_Subset_union (a b c : Sr.t) :
  Sr.subset (Sr.union a b) c ->
  Sr.subset a c.
Proof. move: (SrP.union_subset_1 a b). apply SrP.subset_trans. Qed.

Lemma Sr_Subset_union2 (a b c : Sr.t) :
  Sr.subset (Sr.union a b) c ->
  Sr.subset b c.
Proof.
  move=> hsub.
  specialize (SrP.union_subset_2 a b).
  move=> hunion.
  move: hsub.
  move: hunion.
  apply SrP.subset_trans.
Qed.



Lemma Hload : forall x a e, Pi (Iload x a e).
Proof.
  move=> x a e ii c t ot_t ov_t t' s ot_s ov_s s' Hsc [Hdead_code Hvm Hmem Hcheck] + + Hnsf.
  have [ta [ti [tc [Htc ]]]] := (inst_eq Hsc Hnsf Hdead_code).
  case=>[Hti | []?[]?[]?[]// | []?[]?[]?[]?[]?[]//].
  rewrite !stepI Hsc Htc Hti.
  move=> [i [Hevali _ _ -> -> Htalive]] [i' [Hevali' _ _ -> -> Htalive']].
  have //= /Bool.negb_false_iff Hnotdead := step_fun_not_dead Hsc Hnsf.

  move: Hcheck.
  rewrite Hsc /check_c {1}/check_i {1}/check_ii /unannot /annot // Hnotdead => /andP [Hcheck Hcheck'].
  have [Hremove_x /Sr.subset_spec Hfv_alive] := (Sr_subset_union_rw Hcheck).

  pose proof eval_e_eq_on.
  specialize (H (s_vm s) (s_vm t) e).

  have eq_on_fv: eq_on (free_variables e) (s_vm s) (s_vm t).
  - apply: eq_onI.
    exact Hfv_alive.
    move: Hvm.
    by rewrite /get_current Hsc.

  have Hii' : i = i'.
  - move: Hevali Hevali'.
    by rewrite H; first by move=> -> [= ->].
  rewrite Hii'.
  split; try done.
  - subst. rewrite Hmem. congr OVval. congr cat.
    by apply leaks_e_eq_on.

  split; try by subst.
  - move: Hdead_code.
    subst.
    rewrite Hsc Htc /dead_code_c /s_after_load /with_c /s_c /dead_code_ii {1}/dead_code_i //= Hnotdead //=.
    by move=>[=].
  - subst.
    simpl.
    rewrite Hmem.
    apply eq_on_write.
    move=> el Hel.
    apply Hvm.
    rewrite /get_current Hsc /annot.
    apply: SrP.subset_mem_2.
    exact Hremove_x.
    done.
Qed.

Lemma Hstore : forall a e x, Pi (Istore a e x).
Proof.
  move=> a e x ii c t ot_t ov_t t' s ot_s ov_s s' Hsc [Hdead_code Hvm Hmem Hcheck] + + Hnsf.
  have [ta [ti [tc [Htc ]]]] := (inst_eq Hsc Hnsf Hdead_code).
  case=>[Hti | []?[]?[]?[]// | []?[]?[]?[]?[]?[]//].
  rewrite !stepI Hsc Htc Hti.
  move=> [i [Hevali _ _ -> -> Htalive]] [i' [Hevali' _ _ -> -> Htalive']].
  rewrite Hsc /get_current /annot in Hvm.

  move: Hcheck.
  rewrite Hsc /check_c {1}/check_i {1}/check_ii /unannot /annot //  => /andP [Hcheck Hcheck'].
  have [Hremove_x Hfv_alive] := (Sr_subset_union_rw Hcheck).

  pose proof eval_e_eq_on.
  specialize (H (s_vm s) (s_vm t) e).

  have x_alive: Sr.mem x (analyze_i ii).
  - apply: SrP.subset_mem_2.
    exact Hfv_alive.
    by apply SrP.add_mem_1.

  have eq_on_fv: eq_on (free_variables e) (s_vm s) (s_vm t).
  - move=> el Hel. apply Hvm.
    apply: SrP.subset_mem_2.
    exact Hfv_alive.
    by apply SrP.add_mem_3.

  have Hii' : i = i'.
  - move: Hevali Hevali'.
    by rewrite H; first by move=> -> [= ->].
  rewrite Hii'.

  split; try done.
  - subst. congr OVval.
    rewrite (@leaks_e_eq_on (s_vm s) (s_vm t)); last done.
    congr cat. congr cons.
    by apply Hvm.

  split; try by subst.
  - move: Hdead_code.
    subst.
    rewrite Hsc Htc /dead_code_c /s_after_load /with_c /s_c /dead_code_ii {1}/dead_code_i //=.
    by move=>[=].
  - subst => //= el Hel.
    by apply Hvm, (SrP.subset_mem_2 _ _ Hremove_x).
  - subst => //=.
    rewrite Hmem.
    congr Mem.write.
    by apply Hvm.
Qed.



Lemma mutual_induction : forall T T' P,
    P [::] [::]
    -> (forall xs ys, P xs ys -> forall (x : T) (y : T'), P (x::xs) (y::ys))
    -> forall x y, size x = size y -> P x y.
Proof.
  move=>?? P P0 PS.
  suff : forall n x y, size x = n -> size y = n -> P x y
      by move=>H x ? ?;  apply (H (size x)).
  elim.
  - move=>[]//[]//.
  - move=>n hyp []// x xs []// y ys [= sx] [= sy].
    by apply PS, hyp.
Qed.

Lemma Hmop : forall xs mop os, Pi (Imop xs mop os).
Proof.
  move=> xs mop os ii c t ot_t ov_t t' s ot_s ov_s s' Hsc [Hdead_code Hvm Hmem Hcheck] + + Hnsf.
  have [ta [ti [tc [Htc ]]]] := (inst_eq Hsc Hnsf Hdead_code).
  case=>[Hti | []?[]?[]?[]// | []?[]?[]?[]?[]?[]//].
  rewrite !stepI Hsc Htc Hti.
  move=> [yvs [Heval Hlen -> -> Htalive]] [yvs' [Heval' _ -> -> Htalive']].
  rewrite Hsc /get_current /annot in Hvm.

  have //= Hnotdead := step_fun_not_dead Hsc Hnsf.

  move: Hcheck.
  rewrite Hsc /check_c {1}/check_i {1}/check_ii /unannot /annot // Hnotdead /= => /andP [Hcheck Hcheck'].
  have [Hremove_x Hfv_alive] := (Sr_subset_union_rw Hcheck).

  have Hvalseq : yvs = yvs'.
  { apply (@deterministic_eval_mops' t s mop os).
    done. done. move=>el Hel. symmetry. apply Hvm.
    by apply (SrP.subset_mem_2 _ _ Hfv_alive).
  }

  split; try done.
  - congr OVval. apply leaks_mop_eq_on.
    apply: eq_onI.
    apply Sr.subset_spec in Hfv_alive.
    exact Hfv_alive.
    done.

  split; try by subst.
  - move: Hdead_code.
    subst.
    rewrite Hsc Htc /dead_code_c /s_after_load /with_c /s_c /dead_code_ii {1}/dead_code_i //= Hnotdead //=.
    by move=>[=].
  - subst => el Hel.
    case Hel_in_x : (Sr.mem el (SrExtra.sv_of_list id xs)).
    + simpl.
      move: Hlen Hel_in_x.
      clear.
      rewrite !length_eq_size.
      move: xs yvs'.
      refine (@mutual_induction regvar value _ _ _); first done.
      move=> xs ys IH x y Hmem.
      rewrite !Mr.get_set.
      case: ifP => //= /eqP x_not_el.
      apply IH.
      rewrite SrExtra.sv_of_list_cons SrExtra.Sv_mem_add in Hmem.
      by move: Hmem x_not_el => /orP [] // /eqP -> /eqP //.
    + simpl.
      suff : Mr.get (s_vm s) el = Mr.get (s_vm t) el.
      { move: Hlen Hel_in_x.
        clear.
        rewrite !length_eq_size.
        move: xs yvs'.
        refine (@mutual_induction regvar value _ _ _).
        + by unfold SrExtra.sv_of_list=>_ H.
        + move=>xs ys IH x y Hmem Hmem'.
          rewrite !Mr.get_set.
          case: ifP=>//xelt_not_x.
          rewrite IH //.
          rewrite SrExtra.sv_of_list_cons SrExtra.Sv_mem_add in Hmem.
          rewrite eq_sym in xelt_not_x.
          by rewrite xelt_not_x in Hmem. }
      apply Hvm.
      simpl in *.
      apply (SrP.subset_mem_2 _ _ Hcheck).
      rewrite SrP.union_mem.
      apply /orP.
      left.
      rewrite SrP.diff_mem.
      by rewrite Hel_in_x Hel.

  - subst => //=.
    unfold write_reg, with_vm.
    clear -Hmem.
    by induction zip.
Qed.

Lemma Hif : forall e c1 c0, Pc c1 -> Pc c0 -> Pi (Iif e c1 c0).
Proof.
  move=> e c1 c0 HI1 Hi0 ii c t ot_t ov_t t' s ot_s ov_s s' Hsc [Hdead_code Hvm Hmem Hcheck] + + Hnsf.
  have [ta [ti [tc [Htc HIeq]]]] := (inst_eq Hsc Hnsf Hdead_code).
  have [ce [et [ef [et' [ef' [[= He Hc1et Hc0ef] Hti]]]]]] :
    exists c2 et ef et' ef',
      Iif e c1 c0 = Iif c2 et ef /\ ti = Iif c2 et' ef'
      by case HIeq;
      [ move=>->; by exists e, c1, c0, c1, c0
      | move=>[]?[]?[]? // [] //
      |done ].
  subst; clear HIeq.
  rewrite !stepI Htc Hsc.
  move=> [b [Heval -> -> Htafter]] [b' [Heval' -> -> Hsafter]].
  rewrite Hsc /get_current /annot in Hvm.

  move: Hcheck.
  rewrite Hsc /check_c {1}/check_i {1}/check_ii /unannot /annot /=.
  move=>/andP [+ Hcheck'] => /and5P //= [Hetlive Heflive Hcondlive Hcheck_et Hcheck_ef].

  pose proof eval_e_eq_on.
  specialize (H (s_vm s) (s_vm t) ce).

  have Hdet : b = b'.
  - move: Heval Heval'.
    rewrite H => [-> [= ->] // | el elt].
    by apply Hvm, (SrP.subset_mem_2 _ _ Hcondlive).

  rewrite Hdet.
  split; try done.
  - congr OVval.
    apply leaks_e_eq_on.
    move=>el elt.
    by apply Hvm, (SrP.subset_mem_2 _ _ Hcondlive).

  split; try by subst.
  - move: Hdead_code.
    subst.
    rewrite !dead_code_cat.
    case b'
    ; rewrite {1}/dead_code_c Hsc Htc {1}/dead_code_i {1}/dead_code_ii /annot //=
    ; [ by move=>[= _ -> _] ->
      | by move=>[= _ _ ->] -> ].

  - subst.
    move=>el hel.
    apply Hvm.
    case Hel_cond : (Sr.mem el (free_variables ce)).
    + by apply (SrP.subset_mem_2 _ _ Hcondlive).
    + rewrite get_current_cat in hel.
      destruct b';
      [ by apply (SrP.subset_mem_2 _ _ Hetlive)
      | by apply (SrP.subset_mem_2 _ _ Heflive) ].

  - rewrite Hsafter /s_c /with_c check_c_cat.
    rewrite /check_c {1}/check_i {1}/check_ii /with_c /s_c.
    apply /andP.
    split; last done.
    case b'; [apply Hcheck_et | apply Hcheck_ef].
Qed.

Lemma Hwhile : forall e c1, Pc c1 -> Pi (Iwhile e c1).
Proof.
  move=> e c1 HI ii c t ot_t ov_t t' s ot_s ov_s s' Hsc [Hdead_code Hvm Hmem Hcheck] + + Hnsf.
  have [ta [ti [tc [Htc HIeq]]]] := (inst_eq Hsc Hnsf Hdead_code).
  have [ce [eb [eb' [[= Hce Hbebe'] Hti]]]] :
    exists e0 c c', Iwhile e c1 = Iwhile e0 c /\ ti = Iwhile e0 c'
      by case HIeq; [eauto | eauto| move=>[]?[]?[]?[]?[]?[]//].
  subst; clear HIeq.

  rewrite !stepI Htc Hsc.
  move=> [b [Heval -> -> Htafter]] [b' [Heval' -> -> Hsafter]].
  rewrite Hsc /get_current /annot in Hvm.

  have Hcheck_cp := Hcheck.
  move: Hcheck.
  rewrite Hsc /check_c {1}/check_i {1}/check_ii /unannot /annot /=.
  move=>/andP [+ Hcheck'] => /and4P //= [Hbodylive Hcheckc Hcondlive Hcheckeb].

  pose proof eval_e_eq_on.
  specialize (H (s_vm s) (s_vm t) ce).

  have Hdet : b = b'.
  - move: Heval Heval'.
    rewrite H => [-> [= ->] // | el elt].
    by apply Hvm, (SrP.subset_mem_2 _ _ Hcondlive).

  rewrite Hdet.
  split; try done.
  - congr OVval.
    apply leaks_e_eq_on.
    move=>el elt.
    by apply Hvm, (SrP.subset_mem_2 _ _ Hcondlive).

  split; try by subst.
  - move: Hdead_code.
    subst.
    case b';
      [ rewrite Htc Hsc //= dead_code_cat => [= -> -> ->]; by congr cat
      | by rewrite Htc Hsc //= => [= _ _ ->] ].

  - subst.
    rewrite /s_c /with_c //=.
    move=>el Hel.
    apply Hvm.
    destruct b'.
    + rewrite get_current_cat in Hel.
      by apply (SrP.subset_mem_2 _ _ Hbodylive).
    + by apply (SrP.subset_mem_2 _ _ Hcheckc).

  - rewrite Hsafter //=.
    destruct b'; last done.
    rewrite check_c_cat.
    apply/andP.
    split; [ done | by rewrite Hsc in Hcheck_cp ].
Qed.

Lemma Hnil : Pc [::].
Proof.
  move=>t ot_t ov_t t' s ot_s ov_s s' Hempty Heq Hst Hss Hn.
  destruct (step_nonempty Hss) as [i [c Hc]].
  move: Hempty Hc => ->//.
Qed.

Lemma Hcons : forall i c, Pii i -> Pc c -> Pc (i::c).
Proof.
  move=> [an i] c Hi Hc t ot_t ov_t t' s ot_s ov_s s' Hsc Heq Hst Hss Hsf/=.
  unfold Pii, Pi in *.  by apply (Hi _ _ _ _ _ _ _ _ _ _ Hsc Heq Hst Hss Hsf).
Qed.

Lemma Hannot : forall i a, Pi i -> Pii {| annot := a; unannot := i |}.
Proof. done. Qed.

Lemma live_step' i: Pi i.
Proof.
  apply (@ind_i Pi Pii Pc).
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

Lemma live_step s t ot_s ov_s s':
  eq_s s t ->
  step s ot_s ov_s s' ->
  ~~ next_is_dead s ->
  exists ot_t ov_t t',
  [/\ step t ot_t ov_t t'
    , ot_s = ot_t
    , ov_s = ov_t
    & eq_s s' t'].
Proof.
  move => Heqs Hstep /negPf Hnd.
  have [Hct Hvm Hmem Hcheck] := Heqs.
  have Hnsf := isdead_n_step_fun (negbT Hnd).

  have c := s_c t.
  destruct (s_c s) as [| [ii i] cr] eqn:Hc.
  { apply stepI in Hstep.
    rewrite Hc in Hstep.
    contradiction. }
  rewrite /next_is_dead Hc in Hnd.
  unfold dead_code_c, dead_code_i, dead_code_ii in Hct.
  unfold is_dead_instr in Hnd.

  exists ot_s, ov_s.
  suff Hstep_t_t' : exists t', step t ot_s ov_s t'.
  { rewrite <-Hc in Hnsf.
    destruct Hstep_t_t' as [t' Hstep_t_t'].
    exists t'.
    have H := live_step' Hc Heqs Hstep_t_t' Hstep Hnsf.
    destruct H; by split. }

  (* Holds for any instruction *)
  rewrite stepI Hc in Hstep.
  set t_c := dead_code_c dead_code_i cr p_out.
  destruct i
    ; simpl in Hct, Hnd
    ; try rewrite Hnd in Hct.
  { exists (s_after_assign t t_c s0 e).
    move : Hstep => [] -> -> Hs'.

    suff -> : leaks_e (s_vm s) e = leaks_e (s_vm t) e
      by apply (@step_assign t ii s0 e).
    apply leaks_e_eq_on.

    move: Hcheck.
    rewrite /check_c {1}/check_i {1}/check_ii /unannot /annot // (negbFE Hnd)
            => /andP [Hcheck Hcheck'] el Hel.
    apply Hvm => //=.
    rewrite (SrP.subset_mem_2 _ _ Hcheck) // SrP.union_mem Hel orbT //. }

  { have [i Hstep'] := Hstep.
    set t' := (s_after_load t t_c s0 s1 i).
    exists t'.
    move : Hstep' => [Heval Hib Hdef Hot Hov Hs'].
    rewrite Hot Hov.

    have eq_on_free : eq_on (free_variables e) (s_vm t) (s_vm s).
    { move: Hcheck.
      rewrite /check_c {1}/check_i {1}/check_ii /unannot /annot // (negbFE Hnd)
              => /andP [Hcheck Hcheck'] el Hel.
      symmetry.
      apply Hvm => //=.
      by rewrite (SrP.subset_mem_2 _ _ Hcheck) // SrP.union_mem Hel orbT //.
    }

    suff [Hleaks Hread] : leaks_e (s_vm s) e = leaks_e (s_vm t) e
                          /\ Mem.read (s_mem s) s1 i = Mem.read (s_mem t) s1 i.
    - rewrite Hleaks.
      apply (@step_load t t' ii s0 s1 e t_c) => //.
      + rewrite <-Heval. by apply eval_e_eq_on.
      + move : Hdef.
        unfold is_defined_mem, is_defined.
        by rewrite Hread.
    - split.
      + apply leaks_e_eq_on.
        exact (eq_onS eq_on_free).
      + by rewrite Hmem.
  }

  { have [i Hstep'] := Hstep.
    set t' := (s_after_store t t_c s0 i s1).
    exists t'.
    move : Hstep' => [Heval Hib Hdef Hot Hov Hs'].
    rewrite Hot Hov.

    have [eq_on_free eq_on_s1] : eq_on (free_variables e) (s_vm t) (s_vm s)
                      /\ Mr.get (s_vm t) s1 = Mr.get (s_vm s) s1.
    { move: Hcheck.
      rewrite /check_c {1}/check_i {1}/check_ii /unannot /annot //
              => /andP [Hcheck Hcheck'].
      split
      ; [ move => el Hel |]
      ; symmetry
      ; apply Hvm
      ; simpl
      ; rewrite (SrP.subset_mem_2 _ _ Hcheck) // SrP.union_mem
      ; apply /orP; right
      ; [ by apply SrP.add_mem_3
        | by apply SrP.add_mem_1 ].
    }

    suff [Hleaks Hread] : leaks_e (s_vm s) e = leaks_e (s_vm t) e
                          /\ Mr.get (s_vm s) s1 = Mr.get (s_vm t) s1.
    - rewrite Hread Hleaks.
      apply (@step_store t t' ii s0 e s1 t_c i (Mr.get (s_vm t) s1)) => //.
      + rewrite <-Heval. by apply eval_e_eq_on.
      + move : Hdef.
        unfold is_defined_mem, is_defined.
        by rewrite Hread.
    - split; try done.
      apply leaks_e_eq_on.
      exact (eq_onS eq_on_free).
  }

  { have [vs Hstep'] := Hstep.
    set t' := (s_after_regwrites t t_c (zip l vs)).
    exists t'.
    move : Hstep' => [Heval Hlen Hot Hov Hs'].
    rewrite Hot Hov.

    have eq_on_params : eq_on (SrExtra.sv_of_list id l0) (s_vm s) (s_vm t).
    { move: Hcheck.
      rewrite /check_c {1}/check_i {1}/check_ii /unannot /annot // Hnd
              => /andP [Hcheck Hcheck'] el Hel.
      apply Hvm.
      rewrite (SrP.subset_mem_2 _ _ Hcheck) // SrP.union_mem.
      by apply /orP; right.
    }

    have eq_on_eval_mop : eval_mop (s_vm t) m l0 vs.
    - (* construct witnesses for eval_mop per machine operation *)
      destruct Heval as
        [ ?? H | ?? H | ???? H H' | ???? H H' | ???? H H']
      ; [ apply eval_mop_neg
        | apply eval_mop_not
        | apply eval_mop_add
        | apply eval_mop_and
        | apply eval_mop_cmp ]
      ; (try rewrite H
         ; try rewrite H'
         ; apply eq_on_params
         ; do ? ((try by rewrite SrExtra.sv_of_list_mem_head)
                 ; rewrite SrExtra.sv_of_list_cons
                 ; apply SrP.add_mem_3)).
    - rewrite (@leaks_mop_eq_on (s_vm s) (s_vm t) l m).
      + apply (@step_mop t t' ii l m l0 t_c vs) => //.
      + exact.
  }

  { have [b Hstep'] := Hstep.
    set l' := (dead_code_c dead_code_i l (get_current cr p_out)).
    set l0' := (dead_code_c dead_code_i l0 (get_current cr p_out)).
    set t' := (with_c t ((if b then l' else l0') ++ t_c)).
    exists t'.

    move : Hstep' => [Heval Hot Hov Hs'].
    rewrite Hot Hov.

    suff [Heval_eq ->] : eval_e (s_vm s) e = eval_e (s_vm t) e
                          /\ leaks_e (s_vm s) e = leaks_e (s_vm t) e.
    - apply (@step_if t t' ii e l' l0' t_c b) => //.
      by rewrite <-Heval.
    - split
      ; [ apply eval_e_eq_on
        | apply leaks_e_eq_on ]
      ; move : Hcheck
      ; rewrite /check_c {1}/check_i {1}/check_ii /unannot /annot //
                => /andP [ /and4P [_ _ Hfv _ ] Hcheck'] el Hel
      ; apply Hvm => //=
      ; by apply (SrP.subset_mem_2 _ _ Hfv).
  }

  { have [b Hstep'] := Hstep.
    set l' := (dead_code_c dead_code_i l (analyze_i ii)).
    set t' := (with_c t (if b then l' ++ {| annot := ii; unannot := Iwhile e l' |} :: t_c else t_c)).
    exists t'.

    move : Hstep' => [Heval Hot Hov Hs'].
    rewrite Hot Hov.

    suff [Heval_eq ->] : eval_e (s_vm s) e = eval_e (s_vm t) e
                          /\ leaks_e (s_vm s) e = leaks_e (s_vm t) e.
    - apply (@step_while t t' ii e l' t_c b) => //.
      by rewrite <-Heval.
      subst t'.
      by rewrite Hct.
    - split
      ; [ apply eval_e_eq_on
        | apply leaks_e_eq_on ]
      ; move : Hcheck
      ; rewrite /check_c {1}/check_i {1}/check_ii /unannot /annot //
                => /andP [ /and4P [_ _ Hfv _ ] Hcheck'] el Hel
      ; apply Hvm => //=
      ; by apply (SrP.subset_mem_2 _ _ Hfv).
  }
Qed.

End PROOF.

End PASS.

Require Import
  preservation_obs
  ni_preservation.

Existing Instance Source.

Section PRESERVATION.

Context
  (analyze_i : iinfo -> Sr.t)
  (p_out : Sr.t)
.

Definition pass : compiler (input := input) (Ls := Source) (Lt := Source) :=
  fun p_s =>
    if check_c analyze_i (check_i analyze_i) (p_prog p_s) p_out then
      Some (dead_code_p analyze_i p_out p_s)
    else
      None
    .

Definition _simT1 : SimT1 :=
  fun pc_s ot_s =>
    match pc_s with
    | [::] => [::]
    | i :: c =>
        if is_dead_instr (unannot i) (get_current analyze_i c p_out) then
          [::]
        else
          [:: ot_s]
    end.

Definition _simV1 : SimV1 :=
  fun pc_s ot_s ov_s =>
    match pc_s with
    | [::] => [::]
    | i :: c =>
        if is_dead_instr (unannot i) (get_current analyze_i c p_out) then
          [::]
        else
          [:: Tvobs ov_s]
    end.

Lemma step_preservation:
  step_preserves_obs (eq_s analyze_i p_out) _simT1 _simV1.
Proof.
  unfold step_preserves_obs.
  move=> s t ot_s ov_s s' Heq Hsteps.
  case Hnd: (next_is_dead analyze_i p_out s).
  { (* next step in source is dead *)
    have Heq' := step_next_dead Hsteps Hnd Heq.
    exists [::], [::], t.
    destruct (step_code Hsteps) as [i [c Hc]].
    rewrite /next_is_dead Hc in Hnd.
    split.
    + apply sem_refl.
    + by rewrite /_simT1 /= Hc Hnd.
    + by rewrite /_simV1 /= Hc Hnd.
    + assumption.
  }
  { (* next step in source is alive *)
    destruct (live_step Heq Hsteps (negbT Hnd)) as [ot_t [ov_t [t' [Hstept Hot Hov Heq']]]].
    destruct (step_nonempty Hsteps) as [i [c Hsc]].
    apply sem_step1 in Hstept.
    exists [::ot_t], [::ov_t], t'.
    rewrite /next_is_dead Hsc in Hnd.
    split => //=.
    + by rewrite /_simT1 Hsc Hnd Hot.
    + by rewrite /_simV1 Hsc Hnd Hov /Tvobs.
  }
Qed.

Lemma eq_s_initial:
  eq_s_initial (compile := pass) (eq_s analyze_i p_out).
Proof.
  intros p_s p_t inp.
  rewrite /pass => Hcompile.
  case Hcheck: (check_c analyze_i (check_i analyze_i) (p_prog p_s) p_out); last by rewrite Hcheck in Hcompile.
  rewrite Hcheck in Hcompile. injection Hcompile as Hp_t.
  rewrite /eq_s /initial_state /Source.
  split.
  1: by rewrite /_initial_state /semantics.initial_state -Hp_t /=.
  1-2: by rewrite /_initial_state /semantics.initial_state -Hp_t /dead_code_p /= /eq_on.
  1: by[].
Qed.

Lemma eq_s_final':
  eq_s_final (eq_s analyze_i p_out).
Proof.
  intros s t [Hc _ _ _] Hfins.
  rewrite (finsc Hfins) /get_pc /Source /= in Hc.
  rewrite /final /Source /semantics.final Hc //=.
Qed.

Lemma preservation_obs:
  preserves_obs (compile := pass) (simT := _simT _simT1) (simVIdx := _simVIdx _simT1) (simV := _simV _simT1 _simV1).
Proof.
  apply (lift_step_preserves_obs eq_s_initial eq_s_final' step_preservation).
Qed.

End PRESERVATION.

