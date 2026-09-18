(* -------------------------------------------------------------------------- *)
(* Flattening of assignments. *)
(* Transform expressions with nested operations into multiple operations, e.g.,
   x <- a + (b + c);
   is conceptually transformed to
   t <- b + c;
   x <- a + t;
   More specifically, for an assigment `x <- e` the following steps take place:
   1. the untrusted oracle `choose` determines an expression `s`,
   2. the oracle `free_var` defines a variable `v` not occuring in `e`,
   3. any occurence of `s` in `e` is replaced by `Evar v`
      with the resulting expression denoted `r`,
   4. `x <- e` is replaced by `v <- s; x <- r`.
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
  dead_code_elimination
  preservation_obs
.

Existing Instance Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

Section PASS.

  Context
    (decide_i : iinfo -> expr) (* Oracle determining which expression to flatten within a given instruction. *)
    (free_var : iinfo -> regvar). (* Oracle providing a fresh or free (:= dead) variable that can be (re-)used. *)

  Section CMD.

    (* Whether the next instruction can be flattened. *)
    Definition eligible_i i : bool :=
      match unannot i with
      | Iassign x e =>
          subexpr (decide_i (annot i)) e
      | _ => false
      end.

    (* Whether the next instruction can be flattened. *)
    Definition next_i_eligible (s: state) : bool :=
      match (s_c s) with
      | [::] => false
      | i :: c =>
          eligible_i i
      end.

    Section FLATTEN_C.
      Context (flatten_fn : instr_i -> code).

      Fixpoint flatten_c (c : code) : code :=
        match c with
        | [::] => [::]
        | i :: c => flatten_fn i ++ flatten_c c
        end.
    End FLATTEN_C.

    (* Each instruction is flattened at most once.
       Multi-flattening is achieved by repeating the pass. *)
    Fixpoint flatten_instr (a : iinfo) (i : instr) {struct i} : seq instr :=
      let flatten_ii ii :=
        map (mk_annotated (annot ii)) (flatten_instr (annot ii) (unannot ii)) in
      match i with
      | Iassign x e =>
          if subexpr (decide_i a) e then
            let s := decide_i a in
            let v := free_var a in
            [:: Iassign v s; Iassign x (substitute s (Evar v) e)]
          else [:: i]
      | Iif e c1 c0 =>
          [:: Iif e (flatten_c flatten_ii c1) (flatten_c flatten_ii c0)]
      | Iwhile e c =>
          [:: Iwhile e (flatten_c flatten_ii c)]
      | _ => [:: i]
      end.

    Definition flatten_i (i : instr_i) : code :=
      map (mk_annotated (annot i)) (flatten_instr (annot i) (unannot i)).

    Definition flatten_p (p : prog) : prog :=
      map_p_prog (fun c => flatten_c flatten_i c) p.

  End CMD.

Context
  (liveness : iinfo -> Sr.t). (* liveness analysis oracle (called analyze_i in dead-code elim) *)

  (* Ensure correctness of free_var oracle *)
  Definition check_fvari (live_vars_before_i : Sr.t) (i : instr_i) (live_vars_after_i : Sr.t) : bool :=
    ~~ Sr.mem (free_var (annot i)) live_vars_before_i.

  Section CHECK_FVAR_C.
    Context (check_fvar_fn : instr_i -> Sr.t -> bool).

    Fixpoint check_fvar (c : code) (s_out : Sr.t) : bool :=
      match c with
      | [::] => true
      | i::c => check_fvar_fn i (get_current liveness c s_out) && check_fvar c s_out
      end.
  End CHECK_FVAR_C.

  Fixpoint check_fvar_instr (a : iinfo) (i : instr) (after : Sr.t) {struct i} : bool :=
    let check_fvar_ii ii after' :=
      ~~ Sr.mem (free_var (annot ii)) (liveness (annot ii)) &&
      check_fvar_instr (annot ii) (unannot ii) after' in
    match i with
    | Iif e c1 c0 =>
        check_fvar check_fvar_ii c1 after &&
        check_fvar check_fvar_ii c0 after
    | Iwhile e c =>
        check_fvar check_fvar_ii c (liveness a)
    | _ => true
    end.

  Definition check_fvarii (i : instr_i) (live_vars_after_i : Sr.t) : bool :=
    check_fvari (liveness (annot i)) i live_vars_after_i &&
    check_fvar_instr (annot i) (unannot i) live_vars_after_i.

Fixpoint check_i (before : Sr.t) (i : instr) (after : Sr.t) : bool :=
  let get_current := get_current liveness in
  let check_c := check_c liveness in
  match i with
  | Iassign x e =>
    let pre := (* Always consider free variables in assigments as live
                  -- whether the assignment is live or not --
                  which is in contrast to dead_code elim which considers
                  only free variables of live assigments as live. *)
      Sr.union (Sr.remove x after) (free_variables e) in
    Sr.subset pre before

  | Iload x a e =>
    let pre := (* Always consider free variables as live, same as Iassign. *)
      Sr.union (Sr.remove x after) (free_variables e) in
    Sr.subset pre before

  | Istore a e x =>
    let pre := Sr.union after (Sr.add x (free_variables e)) in
    Sr.subset pre before

  | Imop rs mop es =>
    let rs := (SrExtra.sv_of_list id rs) in
    let es := (SrExtra.sv_of_list id es) in
    let pre := (* Always consider operands as live, same as Iassign. *)
      Sr.union (Sr.diff after rs) es in
    Sr.subset pre before

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

  Section PROOF.

Ltac case_match :=
  lazymatch goal with
  | |- context [match ?x with _ => _ end] =>
      let Hm := fresh "Hm" in
      case Hm: x => //=
  end.

Ltac destruct_match :=
  lazymatch goal with
  | |- context [match ?x with _ => _ end] =>
      let Hm := fresh "Hm" in
      destruct x eqn:Hm => //
  end.


Context
  (p_out : Sr.t)
.

Definition simT1 : SimT1 :=
  fun pc_s ot_s =>
    match pc_s with
    | [::] => [::]
    | i :: c =>
        if eligible_i i then
          [:: OTnone; ot_s]
        else
          [:: ot_s]
    end.

Definition drop_last {T : Type} (s : seq T) :=
  take (size s).-1 s.

Definition take_last {T : Type} (s : seq T) :=
  drop (size s).-1 s.

Fixpoint leakage_of_sub (sub e : expr) (ovvs : seq value) : seq value :=
  if expr_beq sub e then
    let llen_sub := size (leaks_e vmap_empty sub) in
    take llen_sub ovvs
  else
    let ovvs' := drop_last ovvs in
    match e with
    | Econst _
    | Ebool _
    | Evar _ =>
        [::] (* sub not a subexpression of e *)
    | Eop1 o ei =>
        leakage_of_sub sub ei ovvs'
    | Eop2 o ei1 ei2 =>
        let llen_ei1 := size (leaks_e vmap_empty ei1) in
        let ovvs_ei1 := take llen_ei1 ovvs in
        let lhs := leakage_of_sub sub ei1 ovvs_ei1 in
        if lhs != [::] then
          lhs
        else
          let ovvs'' := drop llen_ei1 ovvs' in
          leakage_of_sub sub ei2 ovvs''
    end.

Fixpoint leakage_of_subst_expr
  (sub e : expr)
  (ovvs : seq value)
  (ovvs_sub : seq value)
  : seq value :=
  if expr_beq sub e then
    take_last ovvs_sub
  else
    match e with
    | Econst _
    | Ebool _
    | Evar _ => take 1 ovvs (* the take 1's are redundant since we mantain the invariant that ovvs is the leakage belonging to `e` *)
    | Eop1 o ei =>
        let llen_ei := size (leaks_e vmap_empty ei) in
        let lks_ei := leakage_of_subst_expr sub ei (drop_last ovvs) ovvs_sub in
        let lks_op := take 1 (drop llen_ei ovvs) in
        lks_ei ++ lks_op
    | Eop2 o ei1 ei2 =>
        let llen_ei1 := size (leaks_e vmap_empty ei1) in
        let llen_ei2 := size (leaks_e vmap_empty ei2) in
        let lks_ei1 := leakage_of_subst_expr sub ei1 (take llen_ei1 ovvs) ovvs_sub in
        let ovvs' := drop llen_ei1 (drop_last ovvs) in
        let lks_ei2 := leakage_of_subst_expr sub ei2 ovvs' ovvs_sub in
        let lks_op := take 1 (drop (llen_ei1 + llen_ei2) ovvs) in
        lks_ei1 ++ lks_ei2 ++ lks_op
    end.

Definition simV1 : SimV1 :=
  fun pc_s ot_s ov_s =>
    match pc_s with
    | [::] => [:: ov_s]
    | i :: c =>
        if eligible_i i then
          match unannot i with
          | Iassign _ e =>
              let sub := decide_i (annot i) in
              let '(OVval ovvs) := ov_s in
              let lks_sub := leakage_of_sub sub e ovvs in
              let lks_subst_e := leakage_of_subst_expr sub e ovvs lks_sub in
              [:: OVval lks_sub; OVval lks_subst_e]
          | _ => [::] (* absurd *)
          end
        else
          [:: ov_s]
    end.

Definition eq_s (s t : state) :=
  [/\ s_c t = flatten_c flatten_i (s_c s)
    , eq_on (get_current liveness (s_c s) p_out) (s_vm s) (s_vm t)
    , s_mem s = s_mem t
    , check_c liveness check_i (s_c s) p_out (* liveness oracle correct *)
    & check_fvar check_fvarii (s_c s) p_out (* free_var oracle correct *)
  ].

Lemma leaks_e_size vm1 vm2 e:
  size (leaks_e vm1 e) = size (leaks_e vm2 e).
Proof.
  elim He: e => [|||on en Hsen|on en1 Hsen1 en2 Hsen2] //=.
  + case on; case (eval_e vm1 en); case (eval_e vm2 en); intros;
      by rewrite size_cat size_cat Hsen.
  + case on; case (eval_e vm1 en1); case (eval_e vm1 en2);
      case (eval_e vm2 en1); case (eval_e vm2 en2); intros;
      by rewrite catA size_cat size_cat catA size_cat size_cat Hsen1 Hsen2.
Qed.

Lemma take_size_cat (T : Type) (s1 s2 : seq T) :
  take (size s1) (s1 ++ s2) = s1.
Proof.
  elim s1 => [|h tl IH].
  + by rewrite /= take0.
  + by rewrite /= IH.
Qed.

Lemma drop_lastP (T : Type) (s : seq T) (a : T) :
  drop_last (s ++ [:: a]) = s.
Proof. by rewrite /drop_last take_cat size_cat addn1 /= ltnn subnn /= cats0. Qed.

Lemma take_lastP (T : Type) (s : seq T) (a : T) :
  take_last (s ++ [:: a]) = [:: a].
Proof. by rewrite /take_last drop_cat size_cat addn1 /= ltnn subnn. Qed.

Lemma drop_size1_cat (s1 s2 : seq value) :
  (size s1 <> 0)%N ->
  drop (size s1).-1 (s1 ++ s2) = [:: last Vundef s1] ++ s2.
Proof.
  elim s1.
  + move=> /=. by move=> H; case: H.
  + move=> hd tl Hind Hsize /=.
    case: tl Hind Hsize => [|tlhd tltl] Hind Hsize.
    ++ by[].
    ++ by apply Hind.
Qed.

Lemma drop_size_cat (T : Type) (s1 s2 : seq T) :
  drop (size s1) (s1 ++ s2) = s2.
Proof.
  elim s1 => [|h tl IH].
  + by rewrite /= drop0.
  + by rewrite /= IH.
Qed.

Lemma free_variables_subexpr (se e : expr) s:
  subexpr se e ->
  Sr.subset (free_variables e) s
  -> Sr.Subset (free_variables se) s.
Proof.
  elim: e se => [z|b|v|o e IHe|o e1 IHe1 e2 IHe2] se /=.
  1-3: rewrite /subexpr;
       destruct se => //=;
       rewrite -Sr.subset_spec.
  1-2: by move=>_ /eqP/eqP.
  1: by move/eqP -> => /eqP/eqP.
  {
    rewrite /subexpr.
    move/orP => H.
    case: H => H.
    + destruct se => //=; try by[].
      move/andP in H; destruct H as [Ho Hei].
      move/eqP in Ho.
      rewrite expr_eq in Hei.
      subst. apply IHe.
      exact: subexprR.
    + apply (IHe _ H).
  }
  {
    move/orP => []. move/orP => [].
    destruct se => //=.
    + move/andP => [] /andP [] => _.
      rewrite !expr_eq.
      move=> -> -> H.
      by rewrite -Sr.subset_spec.
    + move=>H Hs.
      specialize (IHe1 _ H).
      apply IHe1.
      by rewrite (Sr_Subset_union Hs).
    + move=>H Hs.
      specialize (IHe2 _ H).
      apply IHe2.
      by rewrite (Sr_Subset_union2 Hs).
  }
Qed.

Lemma mem_singleton_neq v s:
  ~~ SrExtra.Sv.mem v (Sr.singleton s) ->
      v <> s.
Proof.
  move=> H.
  case Hv: (s == v); move/eqP in Hv; subst.
  + by rewrite SrP.singleton_mem_1 /= in H.
  + by apply not_eq_sym in Hv.
Qed.

(* substituting a subexpression by its evaluation in the same context yields the same result *)
Lemma eval_e_subexpr_subst vm v e sub:
  ~~ Sr.mem v (free_variables e) ->
  eval_e vm e = eval_e (Mr.set vm v (eval_e vm sub)) (substitute sub (Evar v) e).
Proof.
  elim He: e => [z|b|x|oi ei Hind|oi ei1 Hind1 ei2 Hind2] /=.
  { destruct sub => _ //=.
    all: try (by move=> <- /=).
    case: ifP.
    + move/eqP => ->.
      by rewrite /= Mr.get_set eqxx.
    + by move=> _ /=.
  }
  { destruct sub => _ //=.
    all: try (by move=> <- /=).
    case: ifP.
    + move/eqP => ->.
      by rewrite /= Mr.get_set eqxx.
    + by move=> _ /=.
  }
  {
    destruct sub => Hvx //=.
    all: try by(
      move=> /=;
      rewrite Mr.get_set;
      case: ifP => //=;
      move/eqP => H; subst;
      contradict Hvx;
      rewrite SrP.singleton_mem_1).
    case: ifP.
    + move/eqP => H; subst.
      by rewrite /= Mr.get_set eqxx.
    + move=> Hxs.
      rewrite /= Mr.get_set.
      case: ifP => //=.
      move/eqP => H; subst.
      contradict Hvx.
      by rewrite SrP.singleton_mem_1.
  }
  {
    move=> Hlv.
    rewrite (Hind Hlv) /=.
    case: ifP.
    + destruct sub => //.
      move/andP => [] /eqP Ho /expr_eq Hei; subst.
      by rewrite -(Hind Hlv) /= Mr.get_set eqxx.
    + move=> Hsub; subst.
      case oi => //=.
  }
  {
    rewrite SrExtra.SvP.union_mem; move/norP => [] Hlv1 Hlv2.
    case: ifP => //=.
    + destruct sub => //.
      move/andP => [] /andP [] /eqP ? /expr_eq ? /expr_eq ?; subst.
      by rewrite /= Mr.get_set eqxx.
    + move=> _; subst.
      by rewrite /= -(Hind1 Hlv1) -(Hind2 Hlv2).
  }
Qed.

Lemma leakage_of_sub_empty sub e vm :
  leakage_of_sub sub e (leaks_e vm e) = [::] ->
  ~ subexpr sub e.
Proof.
  elim: e => [z|b|v|o e IH|o e IH e' IH'].
  1-3: simpl; case: ifP => //; first (by move/expr_eq => ->).
  1-3: destruct sub => //; move=> /= /negP Hneq _; by rewrite eq_sym.
  { simpl; case: ifP => //.
    { move/expr_eq => ?; subst.
      rewrite (leaks_e_size vmap_empty vm).
      simpl; destruct o; destruct (eval_e vm e).
      all: rewrite take_size; move=>H; contradict H.
      all: by case: (leaks_e vm e).
    } {
      move=> Hneq.
      destruct o; destruct (eval_e vm e).
      all: rewrite drop_lastP => H.
      all: destruct sub => //.
      all: try exact (IH H).
      all: move/orP => []; try apply (IH H).
      all: move/andP => [/eqP Ho /expr_eq He]; subst; by rewrite expr_beqR in Hneq.
    }
  }
  { simpl; case: ifP => //.
   { move/expr_eq => ?; subst.
     rewrite (leaks_e_size vmap_empty vm).
     simpl; destruct o; destruct (eval_e vm e); destruct (eval_e vm e').
     all: rewrite take_size; move=>H; contradict H.
     all: by case: (leaks_e vm e); case: (leaks_e vm e').
   } {
     move=> Hneq.
     destruct o; destruct (eval_e vm e); destruct (eval_e vm e').
     all: rewrite (leaks_e_size vmap_empty vm) take_size_cat !catA drop_lastP drop_size_cat.
     all: case: ifP; first (by move=> H1 H2; rewrite H2 in H1).
     all: move=> H H'; move/negbFE/eqP in H; specialize (IH H); specialize (IH' H'); clear H H'.
     all: move/orP => []; last by[]; move/orP => []; last by[]; destruct sub => //.
     all: move/andP => [] /andP [] /eqP ? /expr_eq ? /expr_eq ?; subst; contradict Hneq.
     all: by rewrite expr_beqR.
   }
  }
Qed.

Lemma leakage_of_sub_match sub e vm :
  leakage_of_sub sub e (leaks_e vm e) != [::] ->
  subexpr sub e.
Proof.
  elim: e => [z|b|v|o e IH|o e IH e' IH'].
  1-3: simpl; case: ifP => //; first (by move/expr_eq => ->).
  { simpl; case: ifP => //.
    { move/expr_eq => ?; subst.
      rewrite (leaks_e_size vmap_empty vm).
      simpl; destruct o; destruct (eval_e vm e).
      all: by rewrite take_size; move=>_ /=; rewrite expr_beqR.
    } {
      move=> Hneq.
      destruct o; destruct (eval_e vm e).
      all: rewrite drop_lastP => H.
      all: destruct sub => //=.
      all: rewrite (IH H) /=; try done.
      all: by rewrite orbT.
    }
  }
  { simpl; case: ifP => //.
   { move/expr_eq => ?; subst.
     rewrite (leaks_e_size vmap_empty vm).
     simpl; destruct o; destruct (eval_e vm e); destruct (eval_e vm e').
     all: by rewrite take_size; move=>_ /=; rewrite !expr_beqR.
   } {
     move=> Hneq.
     destruct o; destruct (eval_e vm e); destruct (eval_e vm e').
     all: rewrite (leaks_e_size vmap_empty vm) take_size_cat !catA drop_lastP drop_size_cat.
     all: case: ifP; first (by move=> H _; rewrite (IH H) orbT).
     all: by move=> H H'; move/negbFE/eqP in H; rewrite (IH' H') orbT.
   }
  }
Qed.

Lemma leakage_of_sub_leaks_e sub e vm :
  subexpr sub e ->
  leakage_of_sub sub e (leaks_e vm e) = leaks_e vm sub.
Proof.
  elim e => [z|b|v|o ei IH|o ei1 IH1 ei2 IH2] /=.
  1-3: by destruct sub => //=; move/eqP => ->; rewrite eqxx //.
  { rewrite (leaks_e_size vmap_empty vm).
    move/orP => [].
    + destruct sub => //. move/andP => [] /eqP ->. rewrite expr_eq => H; subst. rewrite expr_beqR /=.
      by destruct o0 => //; case_match; rewrite take_size /=; case: (leaks_e vm sub).
    + move=> Hsub.
      specialize (IH Hsub).
      case: ifP.
    + rewrite expr_eq => Hsub'; subst. contradict Hsub. by rewrite subexpr_of_child_op1.
    + by move=> _; destruct o; case_match; rewrite drop_lastP.
  }
  { rewrite (leaks_e_size vmap_empty vm).
    intro Hsub.
    case: ifP.
    { rewrite expr_eq => Hsub'; subst; simpl.
      destruct o; case (eval_e vm ei1); case (eval_e vm ei2); intros.
      all: rewrite take_size.
      all: by case (leaks_e vm ei1); case (leaks_e vm ei2).
    }
    intro Hneq.
    rewrite (leaks_e_size vmap_empty vm).
    destruct o; destruct (eval_e vm ei1); destruct (eval_e vm ei2); intros.
    all: rewrite take_size_cat catA drop_lastP drop_size_cat.
    all: case: ifP => Hif; first by rewrite (IH1 (leakage_of_sub_match Hif)).
    all: move/orP: Hsub => []; last (move=> H; exact: (IH2 H)).
    all: move/orP => []; last (move=> H; move/eqP in Hif; apply leakage_of_sub_empty in Hif;
                               contradict Hif; exact H).
    all: destruct sub => //; move/andP=> [] /andP [] /eqP ? /expr_eq ? /expr_eq ?; subst;
         contradict Hneq; simpl; by rewrite !expr_beqR.
    }
Qed.

Lemma leakage_of_sub_exists sub e vm :
  subexpr sub e ->
  leakage_of_sub sub e (leaks_e vm e) != [::].
Proof.
  move=> /leakage_of_sub_leaks_e ->.
  elim sub => [z|b|v|o s IH|o s IH1 s' IH2] //=.
  + destruct o; destruct (eval_e vm s); intros => //;
    by case: (leaks_e vm s).
  + destruct o; destruct (eval_e vm s); destruct (eval_e vm s'); intros => //;
    by case: (leaks_e vm s); case: (leaks_e vm s').
Qed.

Lemma flattening_step s t ot_s ov_s s':
  eq_s s t ->
  step s ot_s ov_s s' ->
  next_i_eligible s ->
  exists ots_t ovs_t t',
    [/\ sem t ots_t ovs_t t'
      , ots_t = simT1 (get_pc s) ot_s
      , ovs_t = simV1 (get_pc s) ot_s ov_s
      & eq_s s' t'].
Proof.
  move => Heqs Hstep Hnf.
  have [Hct Hvm Hmem Hchecklv Hcheckfv] := Heqs.

  destruct (s_c s) as [| [ii i] cr] eqn:Hc.
  { apply stepI in Hstep.
    rewrite Hc in Hstep.
    contradiction. }

  rewrite /next_i_eligible Hc in Hnf.
  (*move/andP: Hnf => [Hdec Hnes].**)

  case Hi: i => [ x e |||||]; rewrite Hi in Hnf.
  (* i must be an assignment *)
  2-6: by contradict Hnf.
  have Hnf' : subexpr (decide_i ii) e by move: Hnf; rewrite /eligible_i /=.
  rewrite /flatten_c /flatten_i /flatten_instr /= Hi /= Hnf' /= in Hct.
  clear Hnf'.

  (* derive facts from step in source *)
  rewrite stepI Hc Hi in Hstep.
  destruct Hstep as [-> -> ->].

  have Hcheckfv2 := Hcheckfv.
  move: Hcheckfv2.
  rewrite /check_fvar {1}/check_fvarii {1}/check_fvari /= => /andP [/andP [Hfree_var _] _].

  have Hchecklv2 := Hchecklv.
  move: Hchecklv2.
  rewrite /get_current /= in Hvm.
  rewrite /check_c {1}/check_ii {1}/check_i Hi => /andP [Hlive _].
  have Hsub : Sr.subset (free_variables e) (liveness ii); first by apply (Sr_subset_union_rw Hlive).
  clear Hlive.

  (* prepare first step in target *)
  destruct (exec_step t) as [[[ot_t1 ov_t1] ti]|] eqn:STEP;
    last by (rewrite /exec_step /exec_step /= in STEP; unfold semantics.exec_step in STEP; rewrite Hct //= in STEP).
  have Hstept1 : step t ot_t1 ov_t1 ti.
  by apply exec_stepE.
  clear STEP.
  have Hstept1' := Hstept1.
  rewrite stepI Hct /= in Hstept1'.
  destruct Hstept1' as [Hot_t1 Hov_t1 Hti].

  (* prepare second step in target *)
  destruct (exec_step ti) as [[[ot_t2 ov_t2] t']|] eqn:STEP;
    last by (rewrite /exec_step /exec_step /= in STEP; unfold semantics.exec_step in STEP; rewrite Hti //= in STEP).
  have Hstept2 : step ti ot_t2 ov_t2 t'.
  by apply exec_stepE.
  clear STEP.
  have Hstept2' := Hstept2.
  rewrite stepI Hti /= in Hstept2'.
  destruct Hstept2' as [Hot_t2 Hov_t2 Ht'].

  (* now prove the required facts *)
  exists [:: ot_t1;ot_t2].
  exists [:: ov_t1;ov_t2].
  exists t'.
  split.
  + by apply (sem_trans Hstept1 (sem_trans1 Hstept2)).
  + rewrite /simT1 /get_pc /= Hc Hi Hnf.
    by subst.
  { rewrite /simV1 /get_pc /= Hc Hi Hnf /=.
    clear Hi Ht' Hti Hct.
    congr (_::_).
    { (* leakage of substituted expression *)
      rewrite Hov_t1; clear Hov_t1 Hov_t2; congr OVval.
      rewrite /eligible_i /= in Hnf.
      elim: e Hnf Hsub => [z|b|v|o ei|o ei Hindei ei' Hindei'] /=.
      1-4: case: ifP; try by rewrite expr_eq => ->.
      1-2,4: by case: (decide_i ii) => // _ /[swap] /eqP <- /= /eqP.
      + move/expr_eq => -> Hel Hvlv //=.
        have h : Sr.mem v (liveness ii).
        + apply SrExtra.Sv_mem_singleton.
          rewrite -Sr.subset_spec.
          exact: Hvlv.
        by rewrite (Hvm v h).
      + move/expr_eq => -> Hind Hel Heilv.
        rewrite (leaks_e_size vmap_empty (s_vm s)) /=.
        rewrite take_size.
        have h: eq_on (free_variables ei) (s_vm s) (s_vm t).
        + move/Sr.subset_spec in Heilv.
          exact: (eq_onI Heilv Hvm).
        rewrite (eval_e_eq_on h).
        by rewrite (leaks_e_eq_on h).
      + move/negP/expr_eq => Hneq Hind Hel Heilv.
        rewrite /eligible_i /= in Hel.
        move/orP in Hel.
        destruct Hel as [Hell|Helr].
        + exfalso.
          have := Hell.
          case_match.
          move/andP=> [/eqP Ho' He'].
          move/expr_eq in He'.
          apply: Hneq.
          by rewrite Hm Ho' He'.
        + rewrite (Hind Helr Heilv).
          by case_match; case_match => /=; rewrite drop_lastP.
      + remember (decide_i _) as sub eqn:Hsub; subst.
        (* proof following structure of leakage_of_sub *)
        intros Hsub Hsubset.
        case Heq: (expr_beq (decide_i ii) (Eop2 o ei ei')).
        + rewrite (leaks_e_size vmap_empty (s_vm s)) => /=.
          move/expr_eq in Heq; rewrite Heq /=.
          have -> : (eval_e (s_vm t) ei = eval_e (s_vm s) ei).
          + apply eval_e_eq_on.
            move/Sr_Subset_union in Hsubset.
            apply: (eq_onI _ (eq_onS Hvm)).
            rewrite -Sr.subset_spec.
            exact: Hsubset.
          have -> : (eval_e (s_vm t) ei' = eval_e (s_vm s) ei').
          + apply eval_e_eq_on.
            move/Sr_Subset_union2 in Hsubset.
            apply: (eq_onI _ (eq_onS Hvm)).
            rewrite -Sr.subset_spec.
            exact: Hsubset.
            have -> : (leaks_e (s_vm t) ei = leaks_e (s_vm s) ei).
            + apply leaks_e_eq_on.
              move/Sr_Subset_union in Hsubset.
              apply: (eq_onI _ (eq_onS Hvm)).
              rewrite -Sr.subset_spec.
              exact: Hsubset.
            have -> : (leaks_e (s_vm t) ei' = leaks_e (s_vm s) ei').
            + apply leaks_e_eq_on.
              move/Sr_Subset_union2 in Hsubset.
              apply: (eq_onI _ (eq_onS Hvm)).
              rewrite -Sr.subset_spec.
              exact: Hsubset.
          by destruct o; case (eval_e (s_vm s) ei); case (eval_e (s_vm s) ei'); intros;
          rewrite catA take_size.
        + rewrite (leaks_e_size vmap_empty (s_vm s)).
          destruct o; case (eval_e (s_vm s) ei); case (eval_e (s_vm s) ei'); intros.
          all: rewrite take_size_cat catA drop_lastP drop_size_cat.
          all: case Hif: (leakage_of_sub (decide_i ii) ei (leaks_e (s_vm s) ei) != [::]);
               first (apply (Hindei (leakage_of_sub_match Hif) (Sr_Subset_union Hsubset))).
          all: apply: (Hindei' _ (Sr_Subset_union2 Hsubset));
               move/eqP in Hif;
               move/orP: Hsub.
          all: have -> /= : subexpr (decide_i ii) ei = false;
                first (by apply/negP; apply: (leakage_of_sub_empty Hif)).
          all: destruct (decide_i ii) => //; move/orP => //=;
              move/orP => []; try move/orP => [] //; trivial; try discriminate;
              move/andP => [] /andP [] /eqP ?; subst;
              move/expr_eq => Hbeq1 /expr_eq Hbeq2;
              contradict Heq;
              by rewrite Hbeq1 Hbeq2 !expr_beqR.
    }
    { (* second assignment/step *)
      move: Hsub => Hsubset.
      congr (_ :: _); subst; congr OVval.
      rewrite /eligible_i /= in Hnf.
      rewrite (leakage_of_sub_leaks_e (s_vm s) Hnf).
      clear Hstept1 Hstept2 Hnf.
      elim: e (decide_i ii) Hsubset => [z|b|v|o ei Hind|o ei Hindei ei' Hindei'] => sub Hsubset.
      { case Hsub: (expr_beq sub (Econst z)).
        + move/expr_eq: Hsub => ->.
          by rewrite /= eqxx /= Mr.get_set eqxx.
        + destruct sub => //=.
          rewrite eq_sym.
          by have -> : z0 == z = false; first (by move: Hsub => /=).
      }
      { case Hsub: (expr_beq sub (Ebool b)).
        + move/expr_eq: Hsub => ->.
          by rewrite /= eqxx /= Mr.get_set eqxx.
        + destruct sub => //=.
          rewrite eq_sym.
          by have -> : b0 == b = false; first (by move: Hsub => /=).
      }
      { case Hsub: (expr_beq sub (Evar v)).
        + move/expr_eq: Hsub => ->.
          rewrite /= eqxx /= Mr.get_set eqxx.
          congr (_::_).
          symmetry; apply Hvm.
          apply SrExtra.Sv_mem_singleton.
          by rewrite -Sr.subset_spec.
        + rewrite /= Hsub. move/negP/expr_eq in Hsub.
          case: ifP => /=.
          + rewrite Mr.get_set eqxx.
            destruct sub => //=.
            move/eqP => ?. subst; congr (_::_).
            symmetry; apply Hvm.
            apply SrExtra.Sv_mem_singleton.
            by rewrite -Sr.subset_spec.
          + destruct sub => //=.
            all: move/eqP => ?; subst; congr (_::_).
            all: rewrite Mr.get_set.
            all: case: ifP;
              first(move/eqP => ?; subst;
                    contradict Hfree_var;
                    move/Sr.subset_spec in Hsubset;
                    move/SrExtra.Sv_mem_singleton in Hsubset;
                    by rewrite Hsubset).
            all: by (move=> _; symmetry; apply Hvm, SrExtra.Sv_mem_singleton;
                     rewrite -Sr.subset_spec).
      }
      { (* Eop1 *)
        case Hsub: (expr_beq sub (Eop1 o ei)).
        { move/expr_eq in Hsub; subst.
          rewrite /= !expr_beqR Bool.andb_true_r eqxx.
          have -> : eval_e (s_vm t) ei = eval_e (s_vm s) ei.
          + move/Sr.subset_spec in Hsubset; apply eval_e_eq_on, (eq_onI Hsubset), eq_onS; exact: Hvm.
          destruct o; case (eval_e (s_vm s) ei); intros.
          all: by rewrite take_lastP /= Mr.get_set eqxx.
        } {
          simpl; case: ifP.
          + destruct sub => //.
            move/andP => [] /eqP ?; subst. rewrite expr_eq => ?; subst.
            contradict Hsub.
            by rewrite expr_beqR.
          + move=> Hsubexpr.
            have <- : eval_e (s_vm t) ei = eval_e (s_vm s) ei.
            + apply eval_e_eq_on.
              apply: (eq_onI _ (eq_onS Hvm)).
              rewrite -Sr.subset_spec.
              exact: Hsubset.
            have h' : ~~ Sr.mem (free_var ii) (free_variables ei).
            + apply/negP => Hfvmem.
              move/negP: Hfree_var; apply.
              exact: (SrP.subset_mem_2 _ _ Hsubset _ Hfvmem).
            destruct o => //; destruct (eval_e (s_vm t) ei) eqn:Hevei; intros.
            all: rewrite Hsub drop_lastP (leaks_e_size vmap_empty (s_vm s)) drop_size_cat -(Hind sub Hsubset).
            all: by rewrite /= -(eval_e_subexpr_subst (s_vm t) sub h') Hevei.
        }
      }
      { (* Eop2 *)
        case Hsub: (expr_beq sub (Eop2 o ei ei')).
        { move/expr_eq in Hsub; subst.
          rewrite /= !expr_beqR Bool.andb_true_r eqxx (leaks_e_size vmap_empty (s_vm s)) /=.
          have -> : (eval_e (s_vm t) ei = eval_e (s_vm s) ei).
          + apply eval_e_eq_on.
            move/Sr_Subset_union in Hsubset.
            apply: (eq_onI _ (eq_onS Hvm)).
            rewrite -Sr.subset_spec.
            exact: Hsubset.
          have -> : (eval_e (s_vm t) ei' = eval_e (s_vm s) ei').
          + apply eval_e_eq_on.
            move/Sr_Subset_union2 in Hsubset.
            apply: (eq_onI _ (eq_onS Hvm)).
            rewrite -Sr.subset_spec.
            exact: Hsubset.
          destruct o; case (eval_e (s_vm s) ei); case (eval_e (s_vm s) ei'); intros.
          all: by rewrite Mr.get_set eqxx catA take_lastP.
        } {
          simpl; case: ifP.
          + destruct sub => //.
            move/andP => [] /andP [] /eqP ?; rewrite !expr_eq => ? ?; subst.
            contradict Hsub.
            by rewrite expr_beqR.
          { move=> Hsubexpr.
            have <- : (eval_e (s_vm t) ei = eval_e (s_vm s) ei).
            + apply eval_e_eq_on.
              move/Sr_Subset_union in Hsubset.
              apply: (eq_onI _ (eq_onS Hvm)).
              rewrite -Sr.subset_spec.
              exact: Hsubset.
            have <- : (eval_e (s_vm t) ei' = eval_e (s_vm s) ei').
            + apply eval_e_eq_on.
              move/Sr_Subset_union2 in Hsubset.
              apply: (eq_onI _ (eq_onS Hvm)).
              rewrite -Sr.subset_spec.
              exact: Hsubset.
            have hei : ~~ Sr.mem (free_var ii) (free_variables ei).
            + apply/negP => Hfvmem.
              move/negP: Hfree_var; apply.
              exact: (SrP.subset_mem_2 _ _ (Sr_Subset_union Hsubset) _ Hfvmem).
            have hei' : ~~ Sr.mem (free_var ii) (free_variables ei').
            + apply/negP => Hfvmem.
              move/negP: Hfree_var; apply.
              exact: (SrP.subset_mem_2 _ _ (Sr_Subset_union2 Hsubset) _ Hfvmem).
            destruct o; case (eval_e (s_vm t) ei) eqn:Hevei; case (eval_e (s_vm t) ei') eqn:Hevei'; intros.
            all: rewrite Hsub !(leaks_e_size vmap_empty (s_vm s)) take_size_cat !catA drop_lastP -size_cat -catA !drop_size_cat.
            all: rewrite -(Hindei sub (Sr_Subset_union Hsubset)) -(Hindei' sub (Sr_Subset_union2 Hsubset)).
            all: rewrite /= -(eval_e_subexpr_subst (s_vm t) sub hei) Hevei; try done.
            all: by rewrite -(eval_e_subexpr_subst (s_vm t) sub hei') Hevei'.
          }
        }
      }
    }
  }
  (* correctness: eq_s is preserved after steps in target *)
  split.
  + by rewrite Ht'.
  {
    have Hev : (eval_e (s_vm t) e = eval_e (s_vm s) e).
    + apply eval_e_eq_on. apply: (eq_onI _ (eq_onS Hvm)).
      apply: free_variables_subexpr Hsub.
      rewrite /subexpr //. exact: subexprR.
      set sub := decide_i ii;
      set tvar := free_var ii.
    clear Hti Hct Hot_t1 Hov_t1 Hot_t2 Hov_t2.
    have hfv : ~~ Sr.mem tvar (free_variables e).
    + unfold tvar in *; clear tvar Ht'.
      rewrite /check_fvar in Hcheckfv.
      move/andP in Hcheckfv.
      destruct Hcheckfv as [Hfvnlv _].
      rewrite /check_fvarii /check_fvari /= in Hfvnlv.
      move/andP in Hfvnlv. destruct Hfvnlv as [Hfvnlv _].
      apply/negP => Hmemfv.
      move/negP: Hfvnlv => Hfvnlv.
      apply: Hfvnlv.
      exact: (SrP.subset_mem_2 _ _ Hsub _ Hmemfv).
    rewrite /= Ht' /=; clear Ht'.
    rewrite -(eval_e_subexpr_subst _ _ hfv).
    rewrite /eq_on => v Hv.
    rewrite Mr.get_set.
    case: ifP.
    + move/eqP => H; subst. by rewrite Mr.set_eq.
    + move/eqP => H.
      rewrite Mr.get_set.
      case: ifP.
      + move/eqP. by[].
      + move/eqP => _.
        rewrite /= in Hchecklv.
        move/andP in Hchecklv.
        destruct Hchecklv as [Hlv _].
        rewrite /check_ii /check_i Hi /= in Hlv.
        apply Sr_Subset_union in Hlv.
        rewrite Mr.get_set; case: ifP.
        + (* v = tvar => contradiction v in liveset but tvar not*)
          unfold tvar in *; clear tvar.
          move/eqP => Htvar; symmetry in Htvar; subst.
          exfalso.
          move/negP: Hfree_var => Hnotlive.
          apply: Hnotlive.
          apply (SrP.subset_mem_2 _ _ Hlv).
          apply/SrExtra.Sv_memP.
          apply (SrD.F.remove_2 H).
          apply/SrExtra.Sv_memP.
          exact: Hv.
        + move/eqP => Htvar.
          apply (Hvm v).
          apply (SrP.subset_mem_2 _ _ Hlv).
          apply/SrExtra.Sv_memP.
          apply (SrD.F.remove_2 H).
          apply/SrExtra.Sv_memP.
          exact: Hv.
  }
  + by rewrite /= Hmem Ht' /=.
  all: simpl; clear Ht' Hti Hct.
  + rewrite /= in Hchecklv.
    move/andP in Hchecklv.
    destruct Hchecklv as [_ H].
    exact: H.
  + rewrite /= in Hcheckfv.
    move/andP in Hcheckfv.
    destruct Hcheckfv as [_ H].
    exact: H.
Qed.

Definition nfPi (i : instr) :=
  forall a c s t ot_s ov_s s',
    s_c s = {| annot := a; unannot := i |} :: c ->
    eq_s s t ->
    step s ot_s ov_s s' ->
    ~~ eligible_i {| annot := a; unannot := i |} ->
    exists ot_t ov_t t',
    [/\ step t ot_t ov_t t'
      , ot_s = ot_t
      , ov_s = ov_t
     & eq_s s' t'].

Definition nfPii i := nfPi (unannot i).

Definition nfPc c :=
  forall s t ot_s ov_s s',
    s_c s = c ->
    eq_s s t ->
    step s ot_s ov_s s' ->
    ~~ next_i_eligible s ->
    exists ot_t ov_t t',
    [/\ step t ot_t ov_t t'
      , ot_s = ot_t
      , ov_s = ov_t
     & eq_s s' t'].

Lemma nfHassign : forall x e, nfPi (Iassign x e).
Proof.
  move=> x e a c s t ot_s ov_s s' Hsc Heqs Hstep Hnel.
  have [Hct Hvm Hmem Hchecklv Hcheckfv] := Heqs.
  rewrite stepI Hsc /= in Hstep.
  destruct Hstep as [Hot_s Hov_s Hs'].
  have Hct' : s_c t = {| annot := a; unannot := Iassign x e |} :: flatten_c flatten_i c.
  { have /negbTE Hnel' : ~~ subexpr (decide_i a) e by move: Hnel; rewrite /eligible_i /=.
    by rewrite Hct Hsc /flatten_c /= /flatten_i /= /flatten_instr /= Hnel'. }
  rewrite Hsc /= in Hvm.
  move: (Hchecklv); rewrite Hsc /= => /andP [Hlive Hchecklv_c].
  have [Hremove_x Hfv] := Sr_subset_union_rw Hlive.
  exists OTnone, (OVval (leaks_e (s_vm t) e)), (s_after_assign t (flatten_c flatten_i c) x e).
  split.
  - econstructor. exact Hct'.
  - done.
  - subst. congr OVval.
    apply leaks_e_eq_on.
    apply: (eq_onI _ Hvm).
    by rewrite -Sr.subset_spec.
  - subst. split.
    + by rewrite /s_after_assign /with_c /=.
    + rewrite /s_after_assign /write_reg /with_c /with_vm /=.
      rewrite (@eval_e_eq_on (s_vm s) (s_vm t) e).
      * apply eq_on_write.
        apply: (eq_onI _ Hvm).
        by rewrite -Sr.subset_spec.
      * apply: (eq_onI _ Hvm).
        by rewrite -Sr.subset_spec.
    + by rewrite /s_after_assign /with_c /=.
    + by rewrite /s_after_assign /with_c /=.
    + rewrite /s_after_assign /with_c /=.
      by move: Hcheckfv; rewrite Hsc /= => /andP [].
Qed.

Lemma nfHload : forall x a e, nfPi (Iload x a e).
Proof.
  move=> x ar e a c s t ot_s ov_s s' Hsc Heqs Hstep Hnel.
  have [Hct Hvm Hmem Hchecklv Hcheckfv] := Heqs.
  rewrite stepI Hsc /= in Hstep.
  destruct Hstep as [i [Heval Hib Hdef Hot_s Hov_s Hs']].
  have Hct' : s_c t = {| annot := a; unannot := Iload x ar e |} :: flatten_c flatten_i c.
  { by rewrite Hct Hsc /=. }
  rewrite Hsc /= in Hvm.
  move: (Hchecklv); rewrite Hsc /= => /andP [Hlive Hchecklv_c].
  move: (Hcheckfv); rewrite Hsc /= => /andP [_ Hcheckfv_c].
  rewrite /check_ii /check_i /= in Hlive.
  have [Hremove_x Hfv] := Sr_subset_union_rw Hlive.
  have Heq_fv : eq_on (free_variables e) (s_vm s) (s_vm t).
  { apply: (eq_onI _ Hvm). by rewrite -Sr.subset_spec. }
  have Heval_t : eval_e (s_vm t) e = Vint i by rewrite -(eval_e_eq_on Heq_fv).
  exists (OTaddr ar i), (OVval (leaks_e (s_vm t) e ++ [:: Mem.read (s_mem t) ar i])),
         (s_after_load t (flatten_c flatten_i c) x ar i).
  split; [| done | |].
  { eapply step_load; try eassumption. by rewrite -Hmem. done. done. }
  { subst; rewrite Hmem (leaks_e_eq_on Heq_fv); done. }
  subst; split.
  + by rewrite /s_after_load /with_c /=.
  + rewrite /s_after_load /write_reg /with_c /with_vm /=; rewrite Hmem.
    apply eq_on_write; apply: (eq_onI _ Hvm); by rewrite -Sr.subset_spec.
  + by rewrite /s_after_load /with_c /=.
  + by rewrite /s_after_load /with_c /=.
  + rewrite /s_after_load /with_c /=.
    by move: Hcheckfv; rewrite Hsc /= => /andP [].
Qed.

Lemma nfHstore : forall a e x, nfPi (Istore a e x).
Proof.
  move=> ar e x a c s t ot_s ov_s s' Hsc Heqs Hstep Hnel.
  have [Hct Hvm Hmem Hchecklv Hcheckfv] := Heqs.
  rewrite stepI Hsc /= in Hstep.
  destruct Hstep as [i [Heval Hib Hdef Hot_s Hov_s Hs']].
  have Hct' : s_c t = {| annot := a; unannot := Istore ar e x |} :: flatten_c flatten_i c.
  { by rewrite Hct Hsc /=. }
  rewrite Hsc /= in Hvm.
  move: (Hchecklv); rewrite Hsc /= => /andP [Hlive Hchecklv_c].
  move: (Hcheckfv); rewrite Hsc /= => /andP [_ Hcheckfv_c].
  rewrite /check_ii /check_i /= in Hlive.
  have [Hafter Hxfv] := Sr_subset_union_rw Hlive.
  have Hx_live : Sr.mem x (liveness a).
  { apply: (SrP.subset_mem_2 _ _ Hxfv). by apply SrP.add_mem_1. }
  have Heq_fv : eq_on (free_variables e) (s_vm s) (s_vm t).
  { move=> el Hel. apply Hvm. apply: (SrP.subset_mem_2 _ _ Hxfv).
    by apply SrP.add_mem_3. }
  have Heval_t : eval_e (s_vm t) e = Vint i by rewrite -(eval_e_eq_on Heq_fv).
  exists (OTaddr ar i), (OVval (leaks_e (s_vm t) e ++ [:: Mr.get (s_vm t) x])),
         (s_after_store t (flatten_c flatten_i c) ar i x).
  split.
  - eapply step_store; try eassumption. by rewrite -(Hvm _ Hx_live). done. done.
  - done.
  - subst; rewrite (leaks_e_eq_on Heq_fv) (Hvm _ Hx_live); done.
  - subst; split.
    + by rewrite /s_after_store /with_c /=.
    + rewrite /s_after_store /write_mem /with_c /with_vm /=.
      move=> el Hel; apply Hvm; apply: (SrP.subset_mem_2 _ _ Hafter); exact Hel.
    + rewrite /s_after_store /write_mem /with_c /with_vm /=.
      rewrite -Hmem; congr Mem.write; by apply (Hvm _ Hx_live).
    + by rewrite /s_after_store /with_c /=.
    + rewrite /s_after_store /with_c /=.
      by move: Hcheckfv; rewrite Hsc /= => /andP [].
Qed.

Lemma nfHmop : forall xs mop os, nfPi (Imop xs mop os).
Proof.
  move=> xs mop os a c s t ot_s ov_s s' Hsc Heqs Hstep Hnel.
  have [Hct Hvm Hmem Hchecklv Hcheckfv] := Heqs.
  rewrite stepI Hsc /= in Hstep.
  destruct Hstep as [yvs [Heval Hlen Hot_s Hov_s Hs']].
  have Hct' : s_c t = {| annot := a; unannot := Imop xs mop os |} :: flatten_c flatten_i c.
  { by rewrite Hct Hsc /=. }
  rewrite Hsc /= in Hvm.
  move: (Hchecklv); rewrite Hsc /= => /andP [Hlive Hchecklv_c].
  move: (Hcheckfv); rewrite Hsc /= => /andP [_ Hcheckfv_c].
  rewrite /check_ii /check_i /= in Hlive.
  have [Hdiff Hes] := Sr_subset_union_rw Hlive.
  have Heq_os : eq_on (SrExtra.sv_of_list id os) (s_vm s) (s_vm t).
  { apply: (eq_onI _ Hvm). by rewrite -Sr.subset_spec. }
  have Hyvs : eval_mop (s_vm t) mop os yvs.
  { have Heval' : eval_mop' (s_vm s) mop os = Some yvs by apply/eval_mopE.
    suff Heq : eval_mop' (s_vm t) mop os = eval_mop' (s_vm s) mop os.
    { apply/eval_mopE. by rewrite Heq. }
    clear -Heq_os.
    suff Hget : forall r, r \in os -> Mr.get (s_vm s) r = Mr.get (s_vm t) r.
    { rewrite /eval_mop'.
      destruct mop; destruct os as [|r1 [|r2 [|r3 os']]]; try done;
        try (rewrite (Hget r1); [done | apply mem_head]);
        rewrite (Hget r1) ?(Hget r2); try done;
        try apply mem_head; try (rewrite in_cons; apply/orP; right; apply mem_head). }
    move=> r Hr. apply Heq_os. rewrite SrExtra.sv_of_listE map_id. exact Hr. }
  exists OTnone, (OVval (leaks_mop (s_vm t) xs mop os)),
         (s_after_regwrites t (flatten_c flatten_i c) (zip xs yvs)).
  split.
  - eapply step_mop; try eassumption. done.
  - done.
  - subst. congr OVval. apply leaks_mop_eq_on. exact Heq_os.
  - subst; split.
    + by rewrite /s_after_regwrites /with_c /=.
    + rewrite /s_after_regwrites /with_c /=.
      clear -Hvm Hdiff Hlen.
      rewrite !length_eq_size in Hlen.
      move=> el Hel.
      case Hel_in_x : (Sr.mem el (SrExtra.sv_of_list id xs)).
      * simpl. move: Hlen Hel_in_x. clear. move: xs yvs.
        refine (@mutual_induction regvar value _ _ _); first done.
        move=> xs' yvs' IH x' y' Hmem.
        rewrite /write_reg /with_vm !Mr.get_set.
        case: ifP => //= /eqP x_not_el. apply IH.
        rewrite SrExtra.sv_of_list_cons SrExtra.Sv_mem_add in Hmem.
        by move: Hmem x_not_el => /orP [] // /eqP -> /eqP //.
      * suff : Mr.get (s_vm s) el = Mr.get (s_vm t) el.
        { clear -Hlen Hel_in_x.
          move: xs yvs Hlen Hel_in_x.
          refine (@mutual_induction regvar value _ _ _).
          - by unfold SrExtra.sv_of_list => _ H.
          - move=> xs' yvs' IH x' y' Hlen' Hmem'.
            rewrite /write_reg /with_vm !Mr.get_set.
            case: ifP => // xelt_not_x.
            rewrite IH //.
            rewrite SrExtra.sv_of_list_cons SrExtra.Sv_mem_add in Hlen'.
            rewrite eq_sym in xelt_not_x.
            by rewrite xelt_not_x in Hlen'. }
        apply Hvm. apply (SrP.subset_mem_2 _ _ Hdiff).
        rewrite SrP.diff_mem. by rewrite Hel_in_x Hel.
    + rewrite /s_after_regwrites /with_c /=.
      unfold write_reg, with_vm. clear -Hmem. by induction (zip xs yvs).
    + by rewrite /s_after_regwrites /with_c /=.
    + rewrite /s_after_regwrites /with_c /=.
      by move: Hcheckfv; rewrite Hsc /= => /andP [].
Qed.

Lemma nfHif : forall e c1 c0, nfPc c1 -> nfPc c0 -> nfPi (Iif e c1 c0).
Proof.
  move=> e c1 c0 _ _ a c s t ot_s ov_s s' Hsc Heqs Hstep Hnel.
  have [Hct Hvm Hmem Hchecklv Hcheckfv] := Heqs.
  rewrite stepI Hsc /= in Hstep.
  destruct Hstep as [b [Heval Hot_s Hov_s Hs']].
  have Hct' : s_c t = {| annot := a; unannot := Iif e (flatten_c flatten_i c1) (flatten_c flatten_i c0) |} :: flatten_c flatten_i c.
  { by rewrite Hct Hsc /= /flatten_i /flatten_instr /=. }
  rewrite Hsc /= in Hvm.
  move: (Hchecklv); rewrite Hsc /= => /andP [Hlive Hchecklv_c].
  move: (Hcheckfv); rewrite Hsc /= => /andP [Hcheckfv_head Hcheckfv_c].
  rewrite /check_ii /check_i /= in Hlive.
  move/and5P: Hlive => [Hc1live Hc0live Hcondlive Hcheck_c1 Hcheck_c0].
  have Heq_cond : eq_on (free_variables e) (s_vm s) (s_vm t).
  { apply: (eq_onI _ Hvm). by rewrite -Sr.subset_spec. }
  have Heval_t : eval_e (s_vm t) e = Vbool b by rewrite -(eval_e_eq_on Heq_cond).
  have flatten_c_cat : forall f c1' c2', flatten_c f (c1' ++ c2') = flatten_c f c1' ++ flatten_c f c2'.
  { move=> f. elim=> //= i' c' IH c2'. by rewrite IH catA. }
  have check_c_cat' : forall ci co so,
    check_c liveness check_i (ci ++ co) so =
    check_c liveness check_i ci (get_current liveness co so) && check_c liveness check_i co so.
  { move=> ci. elim: ci => //= i' ci IH co so. by rewrite IH get_current_cat andbA. }
  have check_fvar_cat : forall fn ci co so,
    check_fvar fn (ci ++ co) so =
    check_fvar fn ci (get_current liveness co so) && check_fvar fn co so.
  { move=> fn ci. elim: ci => //= i' ci IH co so. by rewrite IH get_current_cat andbA. }
  exists (OTbranch b), (OVval (leaks_e (s_vm t) e)),
         (with_c t ((if b then flatten_c flatten_i c1 else flatten_c flatten_i c0) ++ flatten_c flatten_i c)).
  split.
  - eapply step_if; try eassumption. done.
  - done.
  - subst. congr OVval. by apply leaks_e_eq_on.
  - subst. split.
    + rewrite /with_c /=. by rewrite flatten_c_cat; case b.
    + rewrite /with_c /=. move=> el Hel. apply Hvm.
      rewrite get_current_cat in Hel.
      by destruct b; [apply (SrP.subset_mem_2 _ _ Hc1live) | apply (SrP.subset_mem_2 _ _ Hc0live)].
    + by rewrite /with_c /=.
    + rewrite /with_c /=. rewrite check_c_cat'. apply/andP. split; last done.
      by destruct b.
    + rewrite /with_c /=. rewrite check_fvar_cat. apply/andP. split; last done.
      rewrite /check_fvarii /check_fvari /check_fvar_instr /= in Hcheckfv_head.
      move/andP: Hcheckfv_head => [_ Hcheckfv_subs].
      by move/andP: Hcheckfv_subs => [Hcfv_c1 Hcfv_c0]; destruct b.
Qed.

Lemma nfHwhile : forall e c1, nfPc c1 -> nfPi (Iwhile e c1).
Proof.
  move=> e cw _ a c s t ot_s ov_s s' Hsc Heqs Hstep Hnel.
  have [Hct Hvm Hmem Hchecklv Hcheckfv] := Heqs.
  rewrite stepI Hsc /= in Hstep.
  destruct Hstep as [b [Heval Hot_s Hov_s Hs']].
  have Hct' : s_c t = {| annot := a; unannot := Iwhile e (flatten_c flatten_i cw) |} :: flatten_c flatten_i c.
  { by rewrite Hct Hsc /= /flatten_i /flatten_instr /=. }
  rewrite Hsc /= in Hvm.
  move: (Hchecklv); rewrite Hsc /= => /andP [Hlive Hchecklv_c].
  move: (Hcheckfv); rewrite Hsc /= => /andP [Hcheckfv_head Hcheckfv_c].
  rewrite /check_ii /check_i /= in Hlive.
  move/and4P: Hlive => [Hbodylive Hafterlive Hcondlive Hcheck_cw].
  have Heq_cond : eq_on (free_variables e) (s_vm s) (s_vm t).
  { apply: (eq_onI _ Hvm). by rewrite -Sr.subset_spec. }
  have Heval_t : eval_e (s_vm t) e = Vbool b by rewrite -(eval_e_eq_on Heq_cond).
  have flatten_c_cat : forall f c1' c2', flatten_c f (c1' ++ c2') = flatten_c f c1' ++ flatten_c f c2'.
  { move=> f. elim=> //= i' c' IH c2'. by rewrite IH catA. }
  have check_c_cat' : forall ci co so,
    check_c liveness check_i (ci ++ co) so =
    check_c liveness check_i ci (get_current liveness co so) && check_c liveness check_i co so.
  { move=> ci. elim: ci => //= i' ci IH co so. by rewrite IH get_current_cat andbA. }
  have check_fvar_cat : forall fn ci co so,
    check_fvar fn (ci ++ co) so =
    check_fvar fn ci (get_current liveness co so) && check_fvar fn co so.
  { move=> fn ci. elim: ci => //= i' ci IH co so. by rewrite IH get_current_cat andbA. }
  exists (OTbranch b), (OVval (leaks_e (s_vm t) e)),
         (with_c t (if b then flatten_c flatten_i cw ++ s_c t else flatten_c flatten_i c)).
  split.
  - eapply step_while; try eassumption. rewrite Hct' /=. by case b.
  - done.
  - subst. congr OVval. by apply leaks_e_eq_on.
  - subst. split.
    + rewrite /with_c /=. destruct b; last done. by rewrite flatten_c_cat Hct'.
    + rewrite /with_c /=. move=> el Hel. apply Hvm.
      destruct b.
      * rewrite get_current_cat in Hel. by apply (SrP.subset_mem_2 _ _ Hbodylive).
      * by apply (SrP.subset_mem_2 _ _ Hafterlive).
    + by rewrite /with_c /=.
    + rewrite /with_c /=. destruct b; last done.
      rewrite check_c_cat'. apply/andP. split; first done. by rewrite Hsc in Hchecklv.
    + rewrite /with_c /=. destruct b; last done.
      rewrite check_fvar_cat. apply/andP. split.
      * rewrite /check_fvarii /check_fvari /check_fvar_instr /= in Hcheckfv_head.
        by move/andP: Hcheckfv_head => [_ Hcfv_cw].
      * by rewrite Hsc in Hcheckfv.
Qed.

Lemma nfHnil : nfPc [::].
Proof.
  move=> s t ot_s ov_s s' Hsc _ Hss _.
  exfalso. apply stepI in Hss. by rewrite Hsc in Hss.
Qed.

Lemma nfHcons : forall i c, nfPii i -> nfPc c -> nfPc (i :: c).
Proof.
  move=> [an i] c Hi _ s t ot_s ov_s s' Hsc Heq Hss Hel.
  rewrite /nfPii /nfPi in Hi.
  have Heli : ~~ eligible_i {| annot := an; unannot := i |}.
  { by rewrite /next_i_eligible Hsc in Hel. }
  exact: (Hi _ _ _ _ _ _ _ Hsc Heq Hss Heli).
Qed.

Lemma nfHannot : forall i a, nfPi i -> nfPii {| annot := a; unannot := i |}.
Proof. done. Qed.

Lemma nf_step' i : nfPi i.
Proof.
  apply (@ind_i nfPi nfPii nfPc).
  + exact nfHassign.
  + exact nfHload.
  + exact nfHstore.
  + exact nfHmop.
  + exact nfHif.
  + exact nfHwhile.
  + exact nfHnil.
  + exact nfHcons.
  + exact nfHannot.
Qed.

Lemma non_flattening_step s t ot_s ov_s s':
  eq_s s t ->
  step s ot_s ov_s s' ->
  next_i_eligible s = false ->
  exists ots_t ovs_t t',
    [/\ sem t ots_t ovs_t t'
      , ots_t = simT1 (get_pc s) ot_s
      , ovs_t = simV1 (get_pc s) ot_s ov_s
        & eq_s s' t'].
Proof.
  move=> Heqs Hstep Hnel.
  have [Hct Hvm Hmem Hchecklv Hcheckfv] := Heqs.

  destruct (s_c s) as [| [ii i] cr] eqn:Hc.
  { exfalso. apply stepI in Hstep. by rewrite Hc in Hstep. }

  have Hnel' : eligible_i {| annot := ii; unannot := i |} = false.
  { by move: Hnel; rewrite /next_i_eligible Hc. }

  have [ot_t [ov_t [t' [Hstep_t Hot Hov Heqs']]]] :=
    nf_step' (a := ii) (c := cr) Hc Heqs Hstep (negbT Hnel').

  exists [:: ot_t], [:: ov_t], t'; split.
  + exact: sem_trans1.
  + by rewrite /simT1 /get_pc /= Hc Hnel' Hot.
  + by rewrite /simV1 /get_pc /= Hc Hnel' Hov.
  + done.
Qed.


End PROOF.

End PASS.

Require Import
  preservation_obs
  ni_preservation.

Existing Instance Source.

Section PRESERVATION.

Context
  (decide_i : iinfo -> expr) (* Untrusted compiler function determining which expression to flatten within a given instruction. *)
  (free_var : iinfo -> regvar) (* Untrusted compiler function providing a fresh or free (:= dead) variable that can be (re-)used. *)
  (liveness : iinfo -> Sr.t) (* Untrusted compiler function for liveness analysis (called analyze_i in dead-code elim) *)
  (p_out : Sr.t)
.

Definition pass : compiler (input := input) (Ls := Source) (Lt := Source) :=
  fun p_s =>
    if check_c liveness (check_i liveness) (p_prog p_s) p_out && check_fvar liveness (check_fvarii free_var liveness) (p_prog p_s) p_out then
      Some (flatten_p decide_i free_var p_s)
    else
      None
.

Lemma step_preservation:
  step_preserves_obs (eq_s decide_i free_var liveness p_out) (simT1 decide_i) (simV1 decide_i).
Proof.
  unfold step_preserves_obs.
  move=> s t ot_s ov_s s' Heq Hsteps.
  case Hel: (next_i_eligible decide_i s).
  + (* next step is rewritten by the pass; scenario covered in `flattening_step` *)
    exact: (flattening_step Heq Hsteps Hel).
  + (* next step remains unchanged *)
    exact: (non_flattening_step Heq Hsteps Hel).
Qed.

(* Prove that any initial states are related by `eq_s` *)
Lemma eq_s_initial:
  eq_s_initial (compile := pass) (eq_s decide_i free_var liveness p_out).
Proof.
  intros p_s p_t inp.
  rewrite /pass => Hcompile.
  case Hchkl: (check_c liveness (check_i liveness) (p_prog p_s) p_out); rewrite Hchkl in Hcompile; last done.
  case Hchkf: (check_fvar liveness (check_fvarii free_var liveness) (p_prog p_s) p_out); rewrite Hchkf in Hcompile; last done.
  injection Hcompile as Hp_t.
  rewrite /eq_s /initial_state /Source.
  split.
  + by rewrite /_initial_state /semantics.initial_state -Hp_t /=.
  1-2: by rewrite /_initial_state /semantics.initial_state -Hp_t /dead_code_p /= /eq_on.
  1-2: by[].
Qed.

Lemma eq_s_final':
  eq_s_final (eq_s decide_i free_var liveness p_out).
Proof.
  intros s t [Hc _ _ _] Hfins.
  rewrite (finsc Hfins) /get_pc /Source /= in Hc.
  rewrite /final /Source /semantics.final Hc //=.
Qed.

Lemma preservation_obs:
  preserves_obs
    (compile := pass)
    (simT := _simT (simT1 decide_i))
    (simVIdx := _simVIdx (simT1 decide_i))
    (simV := _simV (simT1 decide_i) (simV1 decide_i)).
Proof.
  apply (lift_step_preserves_obs eq_s_initial eq_s_final' step_preservation).
Qed.

End PRESERVATION.
