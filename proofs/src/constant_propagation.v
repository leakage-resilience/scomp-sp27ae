(* -------------------------------------------------------------------------- *)
(* Constant propagation. *)
(* Replace variables by their value.
   This pass is parameterized by an oracle that associates a map from variables
   to optional values at each program point.
   We require that the oracle is stable w.r.t. [step], and that the map for
   the first instruction is correct. *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  syntax
  semantics
  semantics_facts
  utils
  var
  preservation_obs
.
Require Import language.
Existing Instance Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

Definition cmap := PMr.t (Z + bool).
Context (analyze_i : iinfo -> cmap).

Section PASS.
  Section MAP.
    (* m1 is a submap of m2 *)
    Definition incl (m1 m2 : cmap) : bool := PMr.incl m1 m2.

    Lemma incl_get m1 m2 e s: incl m1 m2 -> PMr.get m1 e = Some s -> PMr.get m2 e = Some s.
    Proof. move/PMr.inclP; exact. Qed.

    Definition filter m x_t : cmap := PMr.MoreMap.filter (fun _ e => x_t != e) m.

    Definition add m x_s x_t := PMr.set (filter m x_t) x_s x_t.

    Lemma get_add m x y v :
      PMr.get (add m x v) y = (if x == y then Some v else PMr.get (filter m v) y).
    Proof.
      rewrite /PMr.get /add /PMr.set /filter PMr.Facts.add_o /=.
      case: PMr.MoreMap.F.eq_dec; first by move => /cmp_eq ->; rewrite eqxx.
      case: eqP; last by [].
      move => ->; elim; reflexivity.
    Qed.

    Lemma filter_x m x y v : PMr.get (filter m x) y = Some v -> x != v.
    Proof.
      rewrite /PMr.get /filter -PMr.Facts.find_mapsto_iff => /PMr.MoreMap.filter_iff[]; last by [].
      by move => ?? _ ?? ->.
    Qed.

    Lemma filter_same m x y v : PMr.get (filter m x) y = Some v -> PMr.get m y = Some v.
    Proof.
      rewrite /PMr.get /filter -PMr.Facts.find_mapsto_iff => /PMr.MoreMap.filter_iff[].
      - by move => ?? _ ?? ->.
        by move/PMr.Facts.find_mapsto_iff.
    Qed.
  End MAP.

  Section CMD.
    Variable check_i : cmap -> instr -> cmap -> bool.
    Variable const_prop_i : cmap -> instr -> instr.

    Definition get_current (c : code) (cm : cmap) : cmap :=
      match c with
      | [::] => cm
      | i :: _ => analyze_i (annot i)
      end.

    Lemma get_current_cat c c' tbl :
      get_current (c ++ c') tbl = get_current c (get_current c' tbl).
    Proof.
      case c; rewrite /get_current //=.
    Qed.

    Fixpoint const_prop_c' (c : code) : code :=
      match c with
      | [::] => [::]
      | i :: c =>
          let cm := (analyze_i (annot i)) in
          let ui' := const_prop_i cm (unannot i) in
          let c' := const_prop_c' c in
          {| annot := annot i; unannot := ui'|} :: c'
      end.

    Definition check_ii (i : instr_i) (cm' : cmap) : bool :=
      check_i (analyze_i (annot i)) (unannot i) cm'.

    Fixpoint check_c' (c : code) (cm_out : cmap) : bool :=
      match c with
      | [::] => true
      | i :: c => check_ii i (get_current c cm_out) && check_c' c cm_out
      end.
  End CMD.

  Definition check_e (cm : cmap) (e : expr) (val : Z + bool) : bool :=
    match e with
    | Econst z =>
        match val with
        | inl z' => z == z'
        | _ => false
        end
    | Ebool b =>
        match val with
        | inr b' => b == b'
        | _ => false
        end
    | Evar x =>
        if PMr.get cm x is some x' then
          x' == val
        else false
    | _ => false
    end.

  Definition check_r (cm : cmap) (xs : seq regvar) : bool :=
    foldr (fun x acc =>
             if PMr.get cm x is some val then
               false
             else acc) true xs.

  Fixpoint check_i (cm : cmap) (i : instr) (cm' : cmap) : bool :=
    match i with
    | Iassign x e =>
        if PMr.get cm' x is some val then
          check_e cm e val && incl cm' (add cm x val)
        else
          incl cm' cm
    | Iload x a e =>
        if PMr.get cm' x is some val then
          false
        else
          incl cm' cm
    | Istore a e x => incl cm' cm
    | Imop xs mop vs => check_r cm' xs && incl cm' cm
    | Iif e c1 c0 =>
        [&& incl (get_current c1 cm') cm
          , incl (get_current c0 cm') cm
          , check_c' check_i c1 cm'
          & check_c' check_i c0 cm']
    | Iwhile e c =>
        [&& incl (get_current c cm) cm
          , incl cm' cm
          & check_c' check_i c cm]
    end.

  Definition check_c := check_c' check_i.

  Definition check_p (p : prog) (cm_out : cmap) :=
    check_c (p_prog p) cm_out.

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

  Fixpoint const_prop_e (e : expr) (cm : cmap) : expr :=
    match e with
    | Econst _ | Ebool _ => e
    | Evar x =>
        match PMr.get cm x with
        | Some (inl z) => Econst z
        | Some (inr b) => Ebool b
        | None => e
        end
    | Eop1 op e => Eop1 op (const_prop_e e cm)
    | Eop2 op e0 e1 =>
        let e0 := const_prop_e e0 cm in
        let e1 := const_prop_e e1 cm in
        Eop2 op e0 e1
    end.

  Fixpoint const_prop_i (cm : cmap) (i : instr) : instr :=
    match i with
    | Iassign x e => const_prop_e e cm |> Iassign x
    | Iload x a e => const_prop_e e cm |> Iload x a
    | Istore a e x =>
        let e := const_prop_e e cm in
        Istore a e x
    | Imop xs mop os => Imop xs mop os
    | Iwhile e c =>
        let e := const_prop_e e cm in
        Iwhile e (const_prop_c' const_prop_i c)
    | Iif e c1 c0 =>
        let e := const_prop_e e cm in
        Iif e (const_prop_c' const_prop_i c1) (const_prop_c' const_prop_i c0)
    end.

  Definition const_prop_c := const_prop_c' const_prop_i.

  Definition const_prop_p := map_p_prog const_prop_c.

  Lemma const_prop_c_cat c1 c2 c1' c2' :
    const_prop_c c1 = c1' ->
    const_prop_c c2 = c2' ->
    const_prop_c (c1 ++ c2) = c1' ++ c2'.
  Proof.
    move: c1'.
    induction c1.
    - rewrite /const_prop_c /const_prop_c' /=.
      by move => c1' <-.
    - rewrite /const_prop_c /const_prop_c' /=.
      case => // i' c' [=] hi' hc' hc2'.
      specialize (IHc1 c' hc' hc2').
      congr cons; exact.
  Qed.

  Section PROOF.
    Context (cm_out : cmap).

    Definition ok_cmap_vmap (cm : cmap) (vm : vmap) : Prop :=
      forall x,
        match PMr.get cm x with
        | Some (inl z) => Mr.get vm x = Vint z
        | Some (inr b) => Mr.get vm x = Vbool b
        | None => True
        end.

    Lemma ok_cv_eval cm vm e :
      ok_cmap_vmap cm vm ->
      eval_e vm (const_prop_e e cm) = eval_e vm e.
    Proof.
      elim: e => [|| x | op e hind | op e- hind0 e1 hind1] //.
      - move => /(_ x).
        rewrite /const_prop_e.
        case: PMr.get => x' //.
        case: x' => [z | b].
        1-2: rewrite /eval_e //.
      - by move => /hind /= ->.
      - move => hok.
        by rewrite /= (hind0 hok) (hind1 hok).
    Qed.

    Lemma ok_cv_leak cm vm e :
      ok_cmap_vmap cm vm ->
      leaks_e vm (const_prop_e e cm) = leaks_e vm e.
    Proof.
      elim: e => [|| x | op e hind | op e0 hind0 e1 hind1] //.
      - move => /(_ x).
        rewrite /leaks_e /=.
        case: PMr.get => x' //.
        case: x' => [z | b].
        1-2: by move ->.
      - move => hok /=.
        by rewrite (hind hok) (ok_cv_eval e hok).
      - move => hok /=.
        by rewrite (hind0 hok) (hind1 hok) (ok_cv_eval e0 hok) (ok_cv_eval e1 hok).
    Qed.

    Lemma ok_cv_incl cm cm' vm :
      incl cm' cm ->
      ok_cmap_vmap cm vm ->
      ok_cmap_vmap cm' vm.
    Proof.
      move => hincl hok x.
      specialize (hok x).
      case (PMr.get cm' x) as [x' |] eqn:hget; last trivial.
      by rewrite (incl_get hincl hget) in hok.
    Qed.

    Definition eq_s (s t : state) :=
      [/\ s_c t = const_prop_c (s_c s)
        , s_vm t = s_vm s
        , s_mem t = s_mem s
        , ok_cmap_vmap (get_current (s_c s) cm_out) (s_vm s)
        & check_c (s_c s) cm_out].

    Definition Pifw (i : instr) :=
      forall a c s ot ov s' t,
        s_c s = {| annot := a; unannot := i |} :: c ->
        eq_s s t ->
        step s ot ov s' ->
        exists2 t',
          step t ot ov t' &
          eq_s s' t'.

    Lemma Hassign : forall x e, Pifw (Iassign x e).
    Proof.
      move => x e ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /= htc hvm hmem hok /andP [hcheck_i hcheck_c].
      move/stepI => //=.
      move => [-> -> ->].
      eexists.
      - apply stepI.
        subst; simpl.
        split; try done.
        by rewrite (ok_cv_leak e hok).
      - split; try done; simpl.
        + by rewrite hvm (ok_cv_eval e hok).
        + rewrite /check_ii /check_i /= in hcheck_i.
          case PMr.get as [x' | ] eqn:hget in hcheck_i.
          * move: hcheck_i => /andP [hcheck_e hincl] xok.
            case (PMr.get _ xok) as [xok' | ] eqn:hget_ok; last done.
            rewrite Mr.get_set.
            case: ifP => /eqP => heq.
            -- move: heq hget_ok hget hcheck_e => -> -> [=] ->.
               case e => [ z | b | x'' ||] //=.
               ++ 1-2: by case x' => // v' /eqP ->.
               ++ case PMr.get as [v'' | ] eqn:hget' => // /eqP <-.
                  specialize (hok x'').
                  by rewrite hget' in hok.
            -- specialize (hok xok).
               move: hincl => /PMr.inclP /(_ xok xok' hget_ok).
               rewrite get_add.
               case: ifP => /eqP // _.
               move => /filter_same hget'.
               by rewrite hget' in hok.
          * move => xok.
            case (PMr.get _ xok) as [xok' | ] eqn:hget_ok; last done.
            rewrite Mr.get_set.
            case: ifP => /eqP => heq.
            -- by rewrite heq hget_ok in hget.
            -- specialize (hok xok).
               by rewrite (incl_get hcheck_i hget_ok) in hok.
    Qed.

    Lemma Hload : forall x a e, Pifw (Iload x a e).
    Proof.
      move => x a e ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /= htc hvm hmem hok /andP [hcheck_i hcheck_c].
      move/stepI => //= [addr [heval hinb hdef -> -> ->]].
      eexists.
      - apply stepI.
        subst; simpl.
        exists addr.
        split; try done.
        + by rewrite (ok_cv_eval e hok).
        + by rewrite (ok_cv_leak e hok).
      - split; subst; try done; simpl.
        rewrite /check_ii /check_i /= in hcheck_i.
        case PMr.get eqn:hget in hcheck_i => //.
        apply (ok_cv_incl hcheck_i) in hok.
        move => xok.
        case (PMr.get _ xok) as [xok' |] eqn:hget_ok; last done.
        specialize (hok xok).
        rewrite hget_ok in hok.
        rewrite Mr.get_set.
        case: ifP => /eqP heq; last done.
        by rewrite heq hget_ok in hget.
    Qed.

    Lemma Hstore : forall a e x, Pifw (Istore a e x).
    Proof.
      move => a e x ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /= htc hvm hmem hok /andP [hcheck_i hcheck_c].
      move/stepI => //= [addr [heval hinb hef -> -> ->]].
      eexists.
      - apply stepI.
        subst; simpl.
        exists addr.
        split; try done.
        + by rewrite (ok_cv_eval e hok).
        + by rewrite (ok_cv_leak e hok).
      - split; subst; try done; simpl.
        rewrite /check_ii /check_i /= in hcheck_i.
        by apply (ok_cv_incl hcheck_i).
    Qed.

    Lemma size_length T (l : seq T) :
      size l = length l.
    Proof. reflexivity. Qed.

    Lemma Hmop : forall xs mop vs, Pifw (Imop xs mop vs).
    Proof.
      move => xs mop vs ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /= htc hvm hmem hok /andP [hcheck_i hcheck_c].
      move/stepI => //= [ys [heval hlen -> -> ->]].
      eexists.
      - apply stepI.
        subst; simpl.
        exists ys.
        split; try done.
      - split; try done; simpl.
        + induction (zip xs ys); first by rewrite hvm.
          simpl.
          by rewrite IHl.
        + induction (zip xs ys); first by rewrite hmem.
          simpl.
          by rewrite IHl.
        + rewrite /check_ii /check_i /= in hcheck_i.
          move: hcheck_i => /andP [hcheck_r hincl].
          rewrite /check_r in hcheck_r.
          rewrite -(@unzip1_zip regvar value xs ys) in hcheck_r;
            last by rewrite !size_length hlen.
          induction (zip xs ys) as [| xy xys IH]; first exact (ok_cv_incl hincl hok).
          move: hcheck_r => /=.
          case PMr.get as [xy' |] eqn:hget => // hcheck_r xok.
          case (PMr.get _ xok) as [xok' |] eqn:hget_ok; last done.
          rewrite Mr.get_set.
          case: ifP => /eqP heq.
          * by rewrite heq hget_ok in hget.
          * specialize (IH hcheck_r xok).
            by rewrite hget_ok in IH.
    Qed.

    Lemma Hif : forall e c1 c0, Pifw (Iif e c1 c0).
    Proof.
      move => e c1 c0 ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /= htc hvm hmem hok /andP [hcheck_i hcheck_c].
      move/stepI => //= [b [heval -> -> ->]].
      eexists.
      - apply stepI.
        subst; simpl.
        exists b.
        split; try done.
        + by rewrite (ok_cv_eval e hok).
        + by rewrite (ok_cv_leak e hok).
      - rewrite /check_ii /check_i /= in hcheck_i.
        fold check_i in hcheck_i.
        move: hcheck_i => /and4P [hincl1 hincl0 hcheck1 hcheck0].
        split; try done; simpl.
        + case b.
          * rewrite (@const_prop_c_cat c1 c (const_prop_c c1) (const_prop_c c)); done.
          * rewrite (@const_prop_c_cat c0 c (const_prop_c c0) (const_prop_c c)); done.
        + case b; rewrite get_current_cat.
          * exact (ok_cv_incl hincl1 hok).
          * exact (ok_cv_incl hincl0 hok).
        + case b; apply check_c_compose; done.
    Qed.

    Lemma Hwhile : forall e cw, Pifw (Iwhile e cw).
    Proof.
      move => e cw ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /= htc hvm hmem hok /andP [hcheck_i hcheck_c].
      move/stepI => //= [b [heval -> -> ->]].
      eexists.
      - apply stepI.
        subst; simpl.
        exists b.
        split; try done.
        + by rewrite (ok_cv_eval e hok).
        + by rewrite (ok_cv_leak e hok).
      - rewrite /check_ii /check_i /= in hcheck_i.
        fold check_i in hcheck_i.
        move: hcheck_i => /and3P [hincl_w hincl hcheck_w].
        split; try done; simpl.
        + case b; try done.
          rewrite (@const_prop_c_cat cw _ (const_prop_c cw) tc); done.
        + case b.
          * rewrite get_current_cat /=.
            exact (ok_cv_incl hincl_w hok).
          * exact (ok_cv_incl hincl hok).
        + case b; try done.
          apply check_c_compose; try done.
          simpl.
          apply /andP.
          split; try assumption.
          rewrite /check_ii /=.
          apply /and3P.
          split; assumption.
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
  Context (cm_out : cmap).

  Definition pass : compiler (input := input) (Ls := Source) (Lt := Source) :=
    fun p_s =>
      if PMr.is_empty (get_current (p_prog p_s) cm_out)
      then
        if check_c (p_prog p_s) cm_out
        then some (const_prop_p p_s)
        else None
      else None.

  Definition simT1 : SimT1 := fun pc_s ot_s => [:: ot_s].

  Definition simV1 : SimV1 := fun pc_s ot_s ov_s => [:: ov_s].

  Lemma step_preservation :
    step_preserves_obs (eq_s cm_out) simT1 simV1.
  Proof.
    move => s t ot ov s' heq_s sstep.
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
    eq_s_initial (compile := pass) (eq_s cm_out).
  Proof.
    move => p_s p_t inp.
    unfold pass.
    case: ifP => // hempty.
    case: ifP => // hcheck [=] hmerge.
    split; simpl; try done.
    - by rewrite -hmerge /=.
    - rewrite /const_prop_p /map_p_prog /with_p_prog in hmerge.
      have pass_inp := f_equal p_inputs hmerge; simpl in pass_inp.
      by rewrite pass_inp.
    - move => x.
      case PMr.get as [x' |] eqn:hget; try done.
      move: hempty hget => /PMr.is_emptyP /(_ x) -> //.
  Qed.

  Lemma eq_s_final :
    eq_s_final (eq_s cm_out).
  Proof.
    move => s t [hmerge _ _ _ _].
    simpl.
    rewrite /semantics.final.
    move/eqP/size0nil => hfin.
    by move: hfin hmerge => -> /= ->.
  Qed.

  Lemma preservation_obs:
    preserves_obs (compile := pass) (simT := _simT simT1) (simVIdx := _simVIdx simT1) (simV := _simV simT1 simV1).
  Proof.
    exact (lift_step_preserves_obs eq_s_initial eq_s_final step_preservation).
  Qed.

End PRESERVATION.
