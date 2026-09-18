From Coq Require Import NArith ZArith Lia Nat.
From mathcomp Require Import all_ssreflect.

Require Import
  utils
  utils_facts
  var
  syntax
  semantics
  semantics_facts
  preservation_obs
.
Require Import language.
Existing Instance Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

Definition reuse_tbl : Type := PMa.t arrvar.

Context (analyze_i : iinfo -> reuse_tbl).

Section PASS.
  Section MAP.

    Definition incl (tbl1 tbl2 : reuse_tbl) : bool := PMa.incl tbl1 tbl2.

    Lemma incl_get tbl1 tbl2 e s :
      incl tbl1 tbl2 -> PMa.get tbl1 e = Some s -> PMa.get tbl2 e = Some s.
    Proof.
      move/PMa.inclP.
      exact.
    Qed.

    Definition filter m x_t : reuse_tbl := PMa.MoreMap.filter (fun _ e => x_t != e) m.

    Definition add m x_s x_t := PMa.set (filter m x_t) x_s x_t.

    Lemma get_add m x y v :
      PMa.get (add m x v) y = (if x == y then Some v else PMa.get (filter m v) y).
    Proof.
      rewrite /PMa.get /add /PMa.set /filter PMa.Facts.add_o /=.
      case: PMa.MoreMap.F.eq_dec; first by move => /cmp_eq ->; rewrite eqxx.
      case: eqP; last by [].
      move => ->; elim; reflexivity.
    Qed.

    Lemma filter_x m x y v : PMa.get (filter m x) y = Some v -> x != v.
    Proof.
      rewrite /PMa.get /filter -PMa.Facts.find_mapsto_iff => /PMa.MoreMap.filter_iff[]; last by [].
      by move => ?? _ ?? ->.
    Qed.

    Lemma filter_same m x y v : PMa.get (filter m x) y = Some v -> PMa.get m y = Some v.
    Proof.
      rewrite /PMa.get /filter -PMa.Facts.find_mapsto_iff => /PMa.MoreMap.filter_iff[].
      - by move => ?? _ ?? ->.
        by move/PMa.Facts.find_mapsto_iff.
    Qed.
  End MAP.

  Section CMD.
    Variable check_i : reuse_tbl -> instr -> reuse_tbl -> bool.
    Variable reuse_i : reuse_tbl -> instr -> option instr.

    Definition get_current (c : code) (tbl : reuse_tbl) : reuse_tbl :=
      match c with
      | [::] => tbl
      | i :: _ => analyze_i (annot i)
      end.

    Lemma get_current_cat c c' tbl :
      get_current (c ++ c') tbl = get_current c (get_current c' tbl).
    Proof.
      case c; rewrite /get_current //=.
    Qed.

    Fixpoint reuse_c' (c : code) : option code :=
      match c with
      | [::] => Some [::]
      | i :: c =>
          let tbl := (analyze_i (annot i)) in
          let%opt ui' := reuse_i tbl (unannot i) in
          let%opt c' := reuse_c' c in
          Some ({| annot := annot i; unannot := ui' |} :: c')
      end.

    Definition check_ii (i : instr_i) (tbl' : reuse_tbl) : bool :=
      check_i (analyze_i (annot i)) (unannot i) tbl'.

    Fixpoint check_c' (c : code) (tbl_out : reuse_tbl) : bool :=
      match c with
      | [::] => true
      | i :: c => check_ii i (get_current c tbl_out) && check_c' c tbl_out
      end.
  End CMD.

  Fixpoint check_i (tbl : reuse_tbl) (i : instr) (tbl' : reuse_tbl) : bool :=
    match i with
    | Iassign x e => incl tbl' tbl
    | Iload x a e => incl tbl' tbl
    | Istore a e x =>
        if PMa.get tbl a is Some a' then
          incl tbl' (add tbl a a')
        else false
    | Imop xs mop vs => incl tbl' tbl
    | Iif e c1 c0 =>
        [&& incl (get_current c1 tbl') tbl
          , incl (get_current c0 tbl') tbl
          , check_c' check_i c1 tbl'
          & check_c' check_i c0 tbl']
    | Iwhile e c =>
        [&& incl (get_current c tbl) tbl
          , incl tbl' tbl
          & check_c' check_i c tbl]
    end.

  Definition check_c := check_c' check_i.

  Definition check_p (p : prog) (tbl_out : reuse_tbl) :=
    check_c (p_prog p) tbl_out.

  Lemma check_c_compose c1 c2 tbl_out :
    check_c c1 (get_current c2 tbl_out) -> check_c c2 tbl_out ->
    check_c (c1 ++ c2) tbl_out.
  Proof.
    move => hcc1 hcc2.
    induction c1 => //=.
    simpl in hcc1.
    move: hcc1 => /andP [hcci hccc].
    apply /andP.
    split.
    - by rewrite get_current_cat.
    - exact (IHc1 hccc).
  Qed.

  Fixpoint reuse_i (tbl : reuse_tbl) (i : instr) : option instr :=
    match i with
    | Iassign x e => Some i
    | Iload x a e =>
        match PMa.get tbl a with
        | Some a' => Some (Iload x a' e)
        | None => None
        end
    | Istore a e x =>
        match PMa.get tbl a with
        | Some a' => Some (Istore a' e x)
        | None => None
        end
    | Imop xs mop vs => Some i
    | Iif e c1 c0 =>
        let%opt c1' := reuse_c' reuse_i c1 in
        let%opt c0' := reuse_c' reuse_i c0 in
        Some (Iif e c1' c0')
    | Iwhile e c =>
        let%opt c' := reuse_c' reuse_i c in
        Some (Iwhile e c')
    end.

  Definition reuse_c := reuse_c' reuse_i.

  Definition reuse_p (p : prog) : option prog :=
    let%opt c' := reuse_c (p_prog p) in
    Some {|
        p_prog := c';
        p_inputs := (p_inputs p);
        p_outputs := (p_outputs p);
      |}.

  Lemma reuse_c_cat c1 c2 c1' c2' :
    reuse_c c1 = Some c1' ->
    reuse_c c2 = Some c2' ->
    reuse_c (c1 ++ c2) = Some (c1' ++ c2').
  Proof.
    move: c1'.
    induction c1 as [| i c IH].
    - by move => ? [=] <-.
    - move => c1'.
      apply: obindP => i' hreuse_i.
      apply: obindP => c' hreuse_c [=] hc1' hreuse_c2.
      have hih := (IH c' hreuse_c hreuse_c2).
      rewrite /reuse_c in hih.
      by rewrite cat_cons /reuse_c /= hreuse_i /= hih /= -hc1'.
  Qed.

  Section PROOF.
    Context (tbl_out : reuse_tbl).

    Definition Ttob (ot : t_obs) (c : code) : t_obs :=
      let tbl := get_current c tbl_out in
      match ot with
      | OTaddr a i =>
          if PMa.get tbl a is some a' then
            OTaddr a' i
          else ot
      | _ => ot
      end.

    Definition compiler_checks (tbl : reuse_tbl) : Prop :=
      forall a,
        if PMa.get tbl a is Some a' then
          arrlen a = arrlen a'
        else True.

    Lemma compiler_checks_incl tbl tbl' :
      incl tbl' tbl -> compiler_checks tbl -> compiler_checks tbl'.
    Proof.
      move => hincl hcc a.
      case PMa.get as [a'|] eqn:hget => //.
      apply (incl_get hincl) in hget.
      specialize (hcc a).
      by rewrite hget in hcc.
    Qed.

    Definition compiler_checks_dec (tbl : reuse_tbl) : bool :=
      PMa.MoreMap.for_all (fun a a' => arrlen a == arrlen a') tbl.

    Lemma compiler_checksE tbl :
      reflect (compiler_checks tbl) (compiler_checks_dec tbl).
    Proof.
      case hcc : compiler_checks_dec.
      - constructor.
        move => a.
        case PMa.get as [a'|] eqn:hget => //.
        eapply PMa.MoreMap.for_all_iff in hcc.
        * move: hcc => /eqP hcc.
          exact hcc.
        * by move => ?? /Sa.Raw.L.MO.compare_eq -> ?? ->.
        * by apply PMa.Map.find_2.
      - constructor.
        intro hcc'.
        move /Bool.negb_true_iff /negP : hcc.
        apply.
        apply PMa.MoreMap.for_all_iff.
        * by move => ?? /Sa.Raw.L.MO.compare_eq -> ?? ->.
        * move => a a' hget.
          apply PMa.Map.find_1 in hget.
          specialize (hcc' a).
          unfold PMa.get in hcc'.
          rewrite hget in hcc'.
          by apply /eqP.
    Qed.

    Lemma in_bounds_tbl tbl a i :
      compiler_checks tbl ->
      in_bounds a i ->
      if PMa.get tbl a is Some a' then
        in_bounds a' i = true
      else True.
    Proof.
      rewrite /in_bounds.
      case PMa.get as [a'|] eqn:hget => // /(_ a) hcc.
      rewrite hget in hcc.
      by rewrite hcc.
    Qed.

    Definition is_array_renaming (tbl : reuse_tbl) (ms mt : Mem.t) : Prop :=
      forall a i,
        in_bounds a i ->
        if PMa.get tbl a is Some a'
        then Mem.read ms a i = Mem.read mt a' i
        else True.

    Lemma arr_rename_incl tbl tbl' ms mt :
      incl tbl' tbl ->
      is_array_renaming tbl ms mt ->
      is_array_renaming tbl' ms mt.
    Proof.
      move => hincl harr a i hinb.
      specialize (harr a i hinb).
      case (PMa.get tbl') as [a'|] eqn:hget => //.
      by rewrite (incl_get hincl hget) in harr.
    Qed.

    Lemma arr_rename_write tbl tbl' a a' i ms mt v :
      compiler_checks tbl ->
      PMa.get tbl a = Some a' ->
      in_bounds a i ->
      incl tbl' (add tbl a a') ->
      is_array_renaming tbl ms mt ->
      is_array_renaming tbl' (Mem.write ms a i v) (Mem.write mt a' i v).
    Proof.
      move => hcc hget hinb /PMa.inclP hincl harr ai ii hinb'.
      case (PMa.get tbl') as [ai'|] eqn:hgeti => //.
      rewrite !Mem.read_write.
      apply hincl in hgeti.
      - case: eqP => heq_a.
        + rewrite get_add heq_a eqxx in hgeti.
          move: hgeti => [=] <-.
          rewrite eqxx /=.
          case: eqP => // _.
          rewrite -heq_a in hinb'.
          specialize (harr a ii hinb').
          by rewrite hget heq_a in harr.
        + rewrite get_add in hgeti.
          move: hgeti.
          case: ifP => /eqP // _ hget_filter.
          have hgeti := (filter_same hget_filter).
          move: hget_filter => /filter_x /eqP /=.
          case: eqP => //= heq_a' _.
          specialize (harr ai ii hinb').
          by rewrite hgeti in harr.
      - have hinb_ := in_bounds_tbl hcc hinb.
        by rewrite hget in hinb_.
      - exact hinb.
    Qed.

    Definition is_valid_tbl (tbl : reuse_tbl) (s t : state) : Prop :=
      is_array_renaming tbl (s_mem s) (s_mem t) /\ compiler_checks tbl.

    Definition eq_s (s t : state) :=
      [/\ reuse_c (s_c s) = Some (s_c t)
        , is_valid_tbl (get_current (s_c s) tbl_out) s t
        , s_vm s = s_vm t
        & check_c (s_c s) tbl_out].

    Definition Pifw (i : instr) :=
      forall a c s ot_s ov s' t,
        s_c s = {| annot := a; unannot := i |} :: c ->
        eq_s s t ->
        step s ot_s ov s' ->
        exists2 t',
          step t (Ttob ot_s (s_c s)) ov t' &
          eq_s s' t'.

    Lemma Hassign : forall x e, Pifw (Iassign x e).
    Proof.
      move => x e ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /=.
      apply: obindP => c' hreuse [=] htc.
      move => [/= harr hcc] hvm /andP [hincl hcheck_c].
      rewrite /check_ii /= in hincl.
      move/stepI => //= [-> -> ->] /=.
      eexists.
      - apply stepI.
        subst; simpl.
        split; done.
      - split; subst; try done.
        split; simpl.
        + exact (arr_rename_incl hincl harr).
        + exact (compiler_checks_incl hincl hcc).
    Qed.

    Lemma Hload : forall x a e, Pifw (Iload x a e).
    Proof.
      move => x a e ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /=.
      apply: obindP => i'.
      case PMa.get as [a'|] eqn:hget => // [=] hi'.
      apply: obindP => c' hreuse [=] htc.
      move => [/= harr hcc] hvm /andP [hincl hcheck_c].
      rewrite /check_ii /= in hincl.
      move/stepI => //= [addr [heval hinb hdef -> -> ->]] /=.
      have hread := harr a addr hinb.
      rewrite hget in hread.
      eexists.
      - apply stepI.
        subst; simpl.
        exists addr.
        split; try done.
        + have hinb' := in_bounds_tbl hcc hinb.
          by rewrite hget in hinb'.
        + rewrite /is_defined_mem.
          by rewrite -hread.
        + by rewrite hget.
        + by rewrite hread.
      - split; try done.
        + split; simpl.
          * exact (arr_rename_incl hincl harr).
          * exact (compiler_checks_incl hincl hcc).
        + simpl.
          by rewrite hvm hread.
    Qed.

    Lemma Hstore : forall a e x, Pifw (Istore a e x).
    Proof.
      move => a e x ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /=.
      apply: obindP => i'.
      case PMa.get as [a'|] eqn:hget => // [=] hi'.
      apply: obindP => c' hreuse [=] htc.
      move => [/= harr hcc] hvm /andP [hincl hcheck_c].
      rewrite /check_ii /= hget in hincl.
      move/stepI => //= [addr [heval hinb hdef -> -> ->]] /=.
      eexists.
      - apply stepI.
        subst; simpl.
        exists addr.
        split; try done.
        + have hinb' := in_bounds_tbl hcc hinb.
          by rewrite hget in hinb'.
        + by rewrite hget.
      - split; try done.
        split; simpl.
        + rewrite hvm.
          exact (arr_rename_write (Mr.get tvm x) hcc hget hinb hincl harr).
        + apply (compiler_checks_incl hincl).
          move => acc.
          case (PMa.get _ acc) as [acc'|] eqn:hgetcc => //.
          rewrite get_add in hgetcc.
          move: hgetcc.
          case: ifP => /eqP.
          * move => <- [=] <-.
            specialize (hcc a).
            by rewrite hget in hcc.
          * move => heqn /filter_same hgetcc.
            specialize (hcc acc).
            by rewrite hgetcc in hcc.
    Qed.

    Lemma Hmop : forall xs mop vs, Pifw (Imop xs mop vs).
    Proof.
      move => xs mop vs ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /=.
      apply: obindP => c' hreuse [=] htc.
      move => [/= harr hcc] hvm /andP [hincl hcheck_c].
      rewrite /check_ii /= in hincl.
      move/stepI => //= [ys [heval hlen -> -> ->]] /=.
      eexists.
      - apply stepI.
        subst; simpl.
        exists ys.
        split; done.
      - split; try done.
        + split; simpl.
          * induction (zip xs ys); last exact IHl.
            exact (arr_rename_incl hincl harr).
          * exact (compiler_checks_incl hincl hcc).
        + simpl.
          induction (zip xs ys) => /=.
          * exact hvm.
          * by rewrite IHl.
    Qed.

    Lemma Hif : forall e c1 c0, Pifw (Iif e c1 c0).
    Proof.
      move => e c1 c0 ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /=.
      apply: obindP => i'.
      apply: obindP => c1' hreuse1.
      apply: obindP => c0' hreuse0 [=] hi'.
      apply: obindP => c' hreuse [=] htc.
      move => [/= harr hcc] hvm /andP [hcheck_i hcheck_c].
      rewrite /check_ii /= in hcheck_i.
      move: hcheck_i => /and4P [hincl1 hincl0 hcheck1 hcheck0].
      move/stepI => //= [b [heval -> -> ->]] //=.
      eexists.
      - apply stepI.
        subst; simpl.
        exists b.
        split; done.
      - split; try done; simpl.
        + case b; by apply reuse_c_cat.
        + split; simpl; case b; rewrite get_current_cat.
          * exact (arr_rename_incl hincl1 harr).
          * exact (arr_rename_incl hincl0 harr).
          * exact (compiler_checks_incl hincl1 hcc).
          * exact (compiler_checks_incl hincl0 hcc).
        + case b; by apply check_c_compose.
    Qed.

    Lemma Hwhile : forall e cw, Pifw (Iwhile e cw).
    Proof.
      move => e cw ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /=.
      apply: obindP => i'.
      apply: obindP => cw' hreuse_w [=] hi'.
      apply: obindP => c' hreuse [=] htc.
      move => [/= harr hcc] hvm /andP [hcheck_i hcheck_c].
      rewrite /check_ii /= in hcheck_i.
      move: hcheck_i => /and3P [hincl_w hincl hcheck].
      move/stepI => //= [b [heval -> -> ->]].
      eexists.
      - apply stepI.
        subst; simpl.
        exists b.
        split; done.
      - split; try done; simpl.
        + case b.
          * apply reuse_c_cat; first exact hreuse_w.
            by rewrite /= hreuse_w hreuse /= -htc -hi'.
          * exact hreuse.
        + split; simpl; case b.
          * rewrite get_current_cat.
            exact (arr_rename_incl hincl_w harr).
          * exact (arr_rename_incl hincl harr).
          * rewrite get_current_cat.
            exact (compiler_checks_incl hincl_w hcc).
          * exact (compiler_checks_incl hincl hcc).
        + case b.
          * apply check_c_compose; try done.
            apply /andP.
            split; try assumption.
            rewrite /check_ii /=.
            apply /and3P.
            split; assumption.
          * exact hcheck_c.
    Qed.

    Lemma forward_lock_step_diagram : forall i, Pifw i.
    Proof.
      elim.
      - exact Hassign.
      - exact Hload.
      - exact Hstore.
      - exact Hmop.
      - exact Hif.
      - exact Hwhile.
    Qed.
  End PROOF.
End PASS.

Section PRESERVATION.
  Context (tbl_out : reuse_tbl).

  Definition pass : compiler (input := input) (Ls := Source) (Lt := Source) :=
    fun p_s =>
      if compiler_checks_dec (get_current (p_prog p_s) tbl_out)
      then
        if check_c (p_prog p_s) tbl_out
        then reuse_p p_s
        else None
      else None.

  Definition simT1 : SimT1 :=
    fun pc_s ot_s => [:: Ttob tbl_out ot_s pc_s].

  Definition simV1 : SimV1 :=
    fun pc_s ot_s ov_s => [:: ov_s].

  Lemma step_preservation :
    step_preserves_obs (eq_s tbl_out) simT1 simV1.
  Proof.
    move => s t ot_s ov_s s' heq_s sstep.
    have [[a i] [c hc]] := step_code sstep.
    have [t' tstep heq_s'] := forward_lock_step_diagram hc heq_s sstep.
    eexists _, _, _.
    split.
    - exact (sem_step1 tstep).
    - by rewrite /simT1 /=.
    - by rewrite /simV1 /=.
    - exact heq_s'.
  Qed.

  Lemma eq_s_initial :
    eq_s_initial (compile := pass) (eq_s tbl_out).
  Proof.
    move => p_s p_t inp.
    unfold pass.
    case: ifP => // hcc.
    case: ifP => // hcheck.
    apply: obindP => c' hreuse [=] hpt.
    split; try done.
    - simpl.
      by rewrite -hpt /=.
    - split; simpl.
      + move => a i hinb.
        case: PMa.get => //.
        move => a'.
        by rewrite !Mem.undefP.
      + apply /compiler_checksE.
        exact hcc.
    - simpl.
      by rewrite -hpt /=.
  Qed.

  Lemma eq_s_final :
    eq_s_final (eq_s tbl_out).
  Proof.
    move => s t [hreuse _ _ _].
    simpl.
    rewrite /semantics.final.
    move/eqP/size0nil => hfin.
    by move: hfin hreuse => -> /= [=] <-.
  Qed.

  Lemma preservation_obs :
    preserves_obs (compile := pass) (simT := _simT simT1) (simVIdx := _simVIdx simT1) (simV := _simV simT1 simV1).
  Proof.
    exact (lift_step_preserves_obs eq_s_initial eq_s_final step_preservation).
  Qed.
End PRESERVATION.
