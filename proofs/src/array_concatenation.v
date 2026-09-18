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

Definition merge_tbl : Type := PMa.t (arrvar * Z).
Context (analyze_i : iinfo -> merge_tbl).

Section PASS.
  Section MAP.
    (* tbl1 is a submap of tbl2 *)
    Definition incl (tbl1 tbl2 : merge_tbl) : bool := PMa.incl tbl1 tbl2.

    Lemma incl_get tbl1 tbl2 e s :
      incl tbl1 tbl2 -> PMa.get tbl1 e = Some s -> PMa.get tbl2 e = Some s.
    Proof.
      move/PMa.inclP.
      exact.
    Qed.
  End MAP.

  Section CMD.
    Variable check_i : merge_tbl -> instr -> merge_tbl -> bool.
    Variable merge_i : merge_tbl -> instr -> option instr.

    Definition get_current (c : code) (tbl : merge_tbl) : merge_tbl :=
      match c with
      | [::] => tbl
      | i :: _ => analyze_i (annot i)
      end.

    Lemma get_current_cat c c' tbl :
      get_current (c ++ c') tbl = get_current c (get_current c' tbl).
    Proof.
      case c; rewrite /get_current //=.
    Qed.

    Fixpoint merge_c' (c : code) : option code :=
      match c with
      | [::] => some [::]
      | i :: c =>
          let tbl := (analyze_i (annot i)) in
          let%opt ui' := merge_i tbl (unannot i) in
          let%opt c' := merge_c' c in
          some ({| annot := annot i; unannot := ui' |} :: c')
      end.

    Definition check_ii (i : instr_i) (tbl' : merge_tbl) : bool :=
      check_i (analyze_i (annot i)) (unannot i) tbl'.

    Fixpoint check_c' (c : code) (tbl_out : merge_tbl) : bool :=
      match c with
      | [::] => true
      | i :: c => check_ii i (get_current c tbl_out) && check_c' c tbl_out
      end.
  End CMD.

  Fixpoint check_i (tbl : merge_tbl) (i : instr) (tbl' : merge_tbl) : bool :=
    match i with
    | Iassign x e => incl tbl' tbl
    | Iload x a e => incl tbl' tbl
    | Istore a e x => incl tbl' tbl
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

  Definition check_p (p : prog) (tbl_out : merge_tbl) :=
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

  Fixpoint merge_i (tbl : merge_tbl) (i : instr) : option instr :=
    match i with
    | Iassign x e => some i
    | Iload x a e =>
        let%opt a' := PMa.get tbl a in
        some (Iload x a'.1 (eaddi e a'.2))
    | Istore a e x =>
        let%opt a' := PMa.get tbl a in
        some (Istore a'.1 (eaddi e a'.2) x)
    | Imop xs mop vs => some i
    | Iif e c1 c0 =>
        let%opt c1' := merge_c' merge_i c1 in
        let%opt c0' := merge_c' merge_i c0 in
        some (Iif e c1' c0')
    | Iwhile e c =>
        let%opt c' := merge_c' merge_i c in
        some (Iwhile e c')
    end.

  Definition merge_c := merge_c' merge_i.

  Definition merge_p (p : prog) : option prog :=
      let%opt c' := merge_c (p_prog p) in
      some {|
          p_prog := c';
          p_inputs := (p_inputs p);
          p_outputs := (p_outputs p)
        |}.

  Lemma merge_c_cat c1 c2 c1' c2' :
    merge_c c1 = some c1' ->
    merge_c c2 = some c2' ->
    merge_c (c1 ++ c2) = some (c1' ++ c2').
  Proof.
    move: c1'.
    induction c1.
    - rewrite /merge_c /merge_c' /=.
      move => c1' [=] hc1'.
      by rewrite -hc1'.
    - rewrite /merge_c /merge_c' /=.
      move => c1'.
      apply: obindP => i' hmerge_i.
      apply: obindP => c' hmerge_c [=] hc1' hmerge_c2.
      have hih := (IHc1 c' hmerge_c hmerge_c2).
      rewrite /merge_c /merge_c' in hih.
      by rewrite hih hmerge_i -hc1' /=.
  Qed.

  Section PROOF.
    Context (tbl_out : merge_tbl).

    Definition Ttob (ot : t_obs) (c : code) : t_obs :=
      let tbl := get_current c tbl_out in
      match ot with
      | OTaddr a i =>
          if PMa.get tbl a is some a' then
            OTaddr a'.1 (i + a'.2)
          else ot (* dummy *)
      | _ => ot
      end.

    Definition Tvob (ot : t_obs) (ov : v_obs) (c : code) : v_obs :=
      let tbl := get_current c tbl_out in
      match ot with
      | OTaddr a i =>
          if PMa.get tbl a is some a' then
            match ov with
            | OVval vs =>
                let v := last Vundef vs in
                OVval ((take (size vs).-1 vs) ++ [:: Vint a'.2; Vint (i + a'.2); v])
            end
          else ov (* dummy *)
      | _ => ov
      end.

    Definition disjoint_range (start1 len1 start2 len2 : Z) : bool :=
      (start1 + len1 <=? start2) || (start2 + len2 <=? start1).

    Record compiler_checks (tbl : merge_tbl) :=
      {
        tbl_in_bound : forall a,
          if PMa.get tbl a is Some a' then
            [/\ 0 <= a'.2 & a'.2 + arrlen a < arrlen a'.1]
          else True;

        tbl_no_overlap : forall a b,
          a <> b ->
          if PMa.get tbl a is Some a' then
            if PMa.get tbl b is Some b' then
              a'.1 <> b'.1 \/ disjoint_range a'.2 (arrlen a) b'.2 (arrlen b)
            else True
          else True;
      }.

    Lemma compiler_checks_incl tbl tbl' :
      incl tbl' tbl -> compiler_checks tbl -> compiler_checks tbl'.
    Proof.
      move => hincl hcc.
      split.
      - destruct hcc as [hcc _].
        move => a.
        case (PMa.get tbl' a) as [a' | ] eqn:hget; last trivial.
        apply (incl_get hincl) in hget.
        specialize (hcc a).
        rewrite hget /= in hcc.
        exact hcc.
      - destruct hcc as [_ hcc].
        move => a b hneq.
        case (PMa.get tbl' a) as [a' | ] eqn:hgeta; last trivial.
        case (PMa.get tbl' b) as [b' | ] eqn:hgetb; last trivial.
        apply (incl_get hincl) in hgeta, hgetb.
        specialize (hcc a b hneq).
        rewrite hgeta hgetb /= in hcc.
        exact hcc.
    Qed.

    Definition compiler_checks_dec (tbl : merge_tbl) : bool :=
      (PMa.MoreMap.for_all (fun a a' =>
        (0 <=? a'.2) && (a'.2 + arrlen a <? arrlen a'.1)) tbl) &&
      (PMa.MoreMap.for_all (fun a a' =>
        PMa.MoreMap.for_all (fun b b' =>
          (a == b) || (a'.1 != b'.1) ||
          (disjoint_range a'.2 (arrlen a) b'.2 (arrlen b))) tbl) tbl).

    Lemma compiler_checksE tbl :
      reflect (compiler_checks tbl) (compiler_checks_dec tbl).
    Proof.
      case hcc : compiler_checks_dec.
      - constructor.
        move: hcc => /andP [hinb hlap].
        split.
        + move => a.
          destruct (PMa.get tbl a) as [a'|] eqn:hget; last done.
          eapply PMa.MoreMap.for_all_iff in hinb.
          * move: hinb => /andP [/Z.leb_le hinb1 /Z.ltb_lt hinb2].
            split; eassumption.
          * by move => ?? /Sa.Raw.L.MO.compare_eq -> ?? ->.
          * by apply PMa.Map.find_2.
        + move => a b hneq.
          destruct (PMa.get tbl a) as [a'|] eqn:hget_a; last done.
          destruct (PMa.get tbl b) as [b'|] eqn:hget_b; last done.
          eapply PMa.MoreMap.for_all_iff in hlap.
          eapply PMa.MoreMap.for_all_iff in hlap.
          * move/orP : hlap => [/orP [hlap | hlap] | hlap].
            -- exfalso.
               apply hneq.
               apply/eqP : hlap.
            -- left.
               move/eqP : hlap. exact id.
            -- by right.
          * 1,3: by move => ?? /Sa.Raw.L.MO.compare_eq -> ?? ->.
          * 1,2: by apply PMa.Map.find_2.
      - constructor.
        intro hcc'.
        move /Bool.negb_true_iff /negP : hcc.
        apply.
        case : hcc'.
        move => hcc1 hcc2.
        apply /andP.
        split.
        + apply PMa.MoreMap.for_all_iff.
          * by move => ?? /Sa.Raw.L.MO.compare_eq -> ?? ->.
          * move => a a' hget.
            apply PMa.Map.find_1 in hget.
            specialize (hcc1 a).
            unfold PMa.get in hcc1.
            rewrite hget in hcc1.
            destruct hcc1 as [hcc11 hcc12].
            apply /andP.
            split
            ; [ by apply /Z.leb_le
              | by apply /Z.ltb_lt
              ].
        + apply PMa.MoreMap.for_all_iff.
          * by move => ?? /Sa.Raw.L.MO.compare_eq -> ?? ->.
          * move => a a' hget_a.
            apply PMa.MoreMap.for_all_iff.
            -- by move => ?? /Sa.Raw.L.MO.compare_eq -> ?? ->.
            -- move => b b' hget_b.
               case heq: (a == b); first done.
               simpl.
               move/eqP : heq => heq.
               specialize (hcc2 a b heq).
               unfold PMa.get in hcc2.
               apply PMa.Map.find_1 in hget_a.
               apply PMa.Map.find_1 in hget_b.
               rewrite hget_a hget_b in hcc2.
               apply /orP.
               case: hcc2
               ; [left; by apply /eqP
                 | by right
                 ].
    Qed.

    Lemma in_bounds_tbl tbl a i :
      compiler_checks tbl ->
      in_bounds a i ->
      if PMa.get tbl a is Some a' then
        in_bounds a'.1 (i + a'.2) = true
      else True.
    Proof.
      rewrite /in_bounds.
      move => hcc /andP [/Z.leb_le h1 /Z.ltb_lt h2].
      destruct (PMa.get tbl a) eqn:hget; last trivial.
      destruct hcc as [hinb _].
      specialize (hinb a).
      rewrite hget /= in hinb.
      destruct hinb as [hinb1 hinb2].
      apply /andP.
      split.
      - apply Z.leb_le.
        lia.
      - apply Z.ltb_lt.
        lia.
    Qed.


    Definition is_array_renaming (tbl : merge_tbl) (ms mt : Mem.t) : Prop :=
      forall a i,
        in_bounds a i ->
        if PMa.get tbl a is Some a'
        then Mem.read ms a i = Mem.read mt a'.1 (i + a'.2)
        else True.

    Lemma arr_rename_incl tbl tbl' mem1 mem2 :
      incl tbl tbl' ->
      is_array_renaming tbl' mem1 mem2 ->
      is_array_renaming tbl mem1 mem2.
    Proof.
      rewrite /is_array_renaming.
      move => h1 h2 a i hin.
      destruct (PMa.get tbl a) eqn: H1; last by trivial.
      have h3 := incl_get h1 H1.
      move : (h2 a i hin).
      rewrite h3 => //=.
    Qed.

    Lemma arr_rename_write m m' a a' mem mem' v i :
      compiler_checks m ->
      PMa.get m a = Some a' ->
      in_bounds a i ->
      is_array_renaming m mem mem' ->
      incl m' m ->
      is_array_renaming m' (Mem.write mem a i v) (Mem.write mem' a'.1 (i + a'.2) v).
    Proof.
      move => hcc hget hin ok_mem /PMa.inclP h ai ii hini.
      destruct (PMa.get m' ai) as [a_t|] eqn:hget'; last trivial.
      have hget'' := h ai _ hget'.
      rewrite !Mem.read_write.
      case: eqP => heq_a.
      - rewrite heq_a hget'' /Some_inj in hget.
        move: hget => /Some_inj ha_t.
        rewrite ha_t eqxx /=.
        case: eqP => eq_i.
        + by rewrite eq_i eqxx.
        + case: eqP => [hw | _]; first lia.
          have hok := ok_mem ai ii hini.
          by rewrite hget'' ha_t /= in hok.
      - simpl.
        destruct hcc as [hib hnoo].
        specialize (hnoo a ai heq_a).
        rewrite hget hget'' /= in hnoo.
        move: hnoo => [hnoo1 | /orP [/Z.leb_le hnoo2 | /Z.leb_le hnoo3]].
        + case: eqP => [hw | _]; first contradiction.
          simpl.
          have hok := ok_mem ai ii hini.
          by rewrite hget'' /= in hok.
        + unfold disjoint_range in hnoo2.
          unfold in_bounds in hini.
          unfold in_bounds in hin.
          case hc: ((a'.1 == a_t.1) && (i + a'.2 == ii + a_t.2)).
          * have hib' := hib a.
            rewrite hget /= in hib'.
            destruct hib' as [hib'1 hib'2].
            specialize (hib ai).
            rewrite hget'' in hib.
            destruct hib as [hib1 hib2].
            move: hini => /andP [/Z.leb_le hini1 /Z.ltb_lt hini2].
            move: hin => /andP [/Z.leb_le hin1 /Z.ltb_lt hin2].
            move: hc => /andP [/eqP hc1 /eqP hc2].
            lia.
          * have hok := ok_mem ai ii hini.
            by rewrite hget'' /= in hok.
        + unfold disjoint_range in hnoo3.
          unfold in_bounds in hini.
          unfold in_bounds in hin.
          case hc: ((a'.1 == a_t.1) && (i + a'.2 == ii + a_t.2)).
          * have hib' := hib a.
            rewrite hget /= in hib'.
            destruct hib' as [hib'1 hib'2].
            specialize (hib ai).
            rewrite hget'' in hib.
            destruct hib as [hib1 hib2].
            move: hini => /andP [/Z.leb_le hini1 /Z.ltb_lt hini2].
            move: hin => /andP [/Z.leb_le hin1 /Z.ltb_lt hin2].
            move: hc => /andP [/eqP hc1 /eqP hc2].
            lia.
          * have hok := ok_mem ai ii hini.
            by rewrite hget'' /= in hok.
        have hin' := in_bounds_tbl hcc hin.
        rewrite hget /= in hin'.
        exact hin'.
        exact hin.
    Qed.

    Definition is_valid_tbl (tbl : merge_tbl) (s t : state) : Prop :=
      is_array_renaming tbl (s_mem s) (s_mem t) /\ compiler_checks tbl.

    Definition eq_s (s t : state) :=
      [/\ merge_c (s_c s) = some (s_c t)
        , is_valid_tbl (get_current (s_c s) tbl_out) s t
        , s_vm s = s_vm t
        & check_c (s_c s) tbl_out].

    Definition Pifw (i : instr) :=
      forall a c s ot_s ov_s s' t,
        s_c s = {| annot := a; unannot := i |} :: c ->
        eq_s s t ->
        step s ot_s ov_s s' ->
        exists2 t',
          step t (Ttob ot_s (s_c s)) (Tvob ot_s ov_s (s_c s)) t' &
          eq_s s' t'.

    Lemma Hassign : forall x e, Pifw (Iassign x e).
    Proof.
      move => x e ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /=.
      apply: obindP => c' hmerge [=] htc.
      move => [] /= harr hcc hvm /andP [hcheck_i hcheck_r].
      move/stepI => //=.
      rewrite /check_ii /= in hcheck_i.
      move => [] -> -> ->.
      eexists.
      - apply stepI.
        subst; simpl.
        split; trivial.
      - split; trivial.
        + split; simpl.
          * exact (arr_rename_incl hcheck_i harr).
          * exact (compiler_checks_incl hcheck_i hcc).
        + by rewrite hvm.
    Qed.

    Lemma Hload : forall x a e, Pifw (Iload x a e).
    Proof.
      move => x a e ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /=.
      apply: obindP => i'.
      apply: obindP => a' hget [=] hi'.
      apply: obindP => c' hmerge [=] htc.
      move => [] /= harr hcc hvm /andP [hcheck_i hcheck_r].
      move/stepI => //=.
      rewrite /check_ii /= in hcheck_i.
      move => [addr [] heval hinb hdef hot hov ->] //=.
      eexists.
      - apply stepI.
        subst; simpl.
        exists (addr + a'.2).
        split; trivial.
        + by rewrite heval.
        + have hinb' := in_bounds_tbl hcc hinb.
          by rewrite hget in hinb'.
        + specialize (harr a addr hinb).
          rewrite hget in harr.
          unfold is_defined_mem in hdef.
          by rewrite harr in hdef.
        + by rewrite hget.
        + rewrite hget heval /=.
          congr OVval.
          rewrite takel_cat; last by rewrite size_cat /= addn1.
          rewrite cats1 size_rcons /=.
          rewrite take_size last_rcons -catA /=.
          congr cat.
          do! congr cons.
          specialize (harr a addr hinb).
          by rewrite hget in harr.
      - split; trivial.
        + split; simpl.
          * exact (arr_rename_incl hcheck_i harr).
          * exact (compiler_checks_incl hcheck_i hcc).
        + simpl.
          specialize (harr a addr hinb).
          rewrite hget in harr.
          by rewrite hvm harr.
    Qed.

    Lemma Hstore : forall a e x, Pifw (Istore a e x).
    Proof.
      move => a e x ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /=.
      apply: obindP => i'.
      apply: obindP => a' hget [=] hi'.
      apply: obindP => c' hmerge [=] htc.
      move => [] /= harr hcc hvm /andP [hcheck_i hcheck_r].
      move/stepI => //=.
      rewrite /check_ii /= in hcheck_i.
      move => [addr [] heval hinb hdef hot hov ->] //=.
      eexists.
      - apply stepI.
        subst; simpl.
        exists (addr + a'.2).
        split; trivial.
        + by rewrite heval.
        + have hinb' := in_bounds_tbl hcc hinb.
          by rewrite hget in hinb'.
        + by rewrite hget.
        + rewrite hget heval /=.
          congr OVval.
          rewrite takel_cat; last by rewrite size_cat /= addn1.
          rewrite cats1 size_rcons /=.
          by rewrite take_size last_rcons -catA /=.
      - split; trivial.
        split; simpl.
        + rewrite hvm.
          exact (arr_rename_write (Mr.get tvm x) hcc hget hinb harr hcheck_i).
        + exact (compiler_checks_incl hcheck_i hcc).
    Qed.

    Lemma Hmop : forall xs mop vs, Pifw (Imop xs mop vs).
    Proof.
      move => xs mop vs ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /=.
      apply: obindP => c' hmerge [=] htc.
      move => [] /= harr hcc hvm /andP [hcheck_i hcheck_r].
      move/stepI => //=.
      rewrite /check_ii /= in hcheck_i.
      move => [ys [] heval hlen hot hov ->] //=.
      eexists.
      - apply stepI.
        subst; simpl.
        exists ys.
        split; trivial.
      - split; trivial.
        + split; simpl.
          * induction (zip xs ys); first exact (arr_rename_incl hcheck_i harr).
            exact IHl.
          * exact (compiler_checks_incl hcheck_i hcc).
        + simpl.
          induction (zip xs ys); first trivial.
          simpl.
          by rewrite IHl.
    Qed.

    Lemma Hif : forall e c1 c0, Pifw (Iif e c1 c0).
    Proof.
      move => e c1 c0 ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /=.
      apply: obindP => i'.
      apply: obindP => c1' hmerge1.
      apply: obindP => c0' hmerge0 [=] hi'.
      apply: obindP => c' hmerge [=] htc.
      move => [] /= harr hcc hvm /andP [hcheck_i hcheck_r].
      move/stepI => //=.
      rewrite /check_ii /= in hcheck_i.
      move: hcheck_i => /and4P [hincl1 hincl0 hcheck1 hcheck0].
      move => [b [] heval hot hov ->] //=.
      eexists.
      - apply stepI.
        subst; simpl.
        exists b.
        split; trivial.
      - split; trivial; simpl.
        + case b; by apply merge_c_cat.
        + split; simpl; case b.
          * rewrite get_current_cat.
            exact (arr_rename_incl hincl1 harr).
          * rewrite get_current_cat.
            exact (arr_rename_incl hincl0 harr).
          * rewrite get_current_cat.
            exact (compiler_checks_incl hincl1 hcc).
          * rewrite get_current_cat.
            exact (compiler_checks_incl hincl0 hcc).
        + case b; by apply check_c_compose.
    Qed.

    Lemma Hwhile : forall e cw, Pifw (Iwhile e cw).
    Proof.
      move => e cw ai c s ot ov s' t.
      move: s t => [sc svm smem] [tc tvm tmem] /= -> [] /=.
      apply: obindP => i'.
      apply: obindP => cw' hmerge_w [=] hi'.
      apply: obindP => c' hmerge [=] htc.
      move => [] /= harr hcc hvm /andP [hcheck_i hcheck_r].
      move/stepI => //=.
      rewrite /check_ii /= in hcheck_i.
      move: hcheck_i => /and3P [hincl_w hincl hcheck].
      move => [b [] heval hot hov ->] //=.
      eexists.
      - apply stepI.
        subst; simpl.
        exists b.
        split; trivial.
      - split; trivial; simpl.
        + case b.
          * apply merge_c_cat; first exact hmerge_w.
            by rewrite /= hmerge_w hmerge /= -htc -hi'.
          * exact hmerge.
        + split; simpl; case b.
          * rewrite get_current_cat.
            exact (arr_rename_incl hincl_w harr).
          * exact (arr_rename_incl hincl harr).
          * rewrite get_current_cat.
            exact (compiler_checks_incl hincl_w hcc).
          * exact (compiler_checks_incl hincl hcc).
        + case b.
          * apply check_c_compose; try done.
            simpl.
            apply /andP.
            split; try assumption.
            rewrite /check_ii /=.
            apply /and3P.
            split; assumption.
          * exact hcheck_r.
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
  Context (tbl_out : merge_tbl).

  Definition pass : compiler (input := input) (Ls := Source) (Lt := Source) :=
    fun p_s =>
      if compiler_checks_dec (get_current (p_prog p_s) tbl_out)
      then
        if check_c (p_prog p_s) tbl_out
        then merge_p p_s
        else None
      else None.

  Definition simT1 : SimT1 :=
    fun pc_s ot_s => [:: Ttob tbl_out ot_s pc_s].

  Definition simV1 : SimV1 :=
    fun pc_s ot_s ov_s => [:: Tvob tbl_out ot_s ov_s pc_s].

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
    case : ifP => // hcc.
    case : ifP => // hcheck.
    apply : obindP => c' hmerge [=] hpt.
    split.
    - simpl.
      by rewrite -hpt /=.
    - split; simpl.
      + move => a i hinb.
        case: PMa.get; last done.
        move => a'.
        by rewrite !Mem.undefP.
      + apply /compiler_checksE.
        exact hcc.
    - simpl.
      by rewrite -hpt /=.
    - simpl.
      exact hcheck.
  Qed.

  Lemma eq_s_final :
    eq_s_final (eq_s tbl_out).
  Proof.
    move => s t [hmerge _ _ _].
    simpl.
    rewrite /semantics.final.
    move/eqP/size0nil => hfin.
    by move: hfin hmerge => -> /= [=] <-.
  Qed.

  Lemma preservation_obs:
    preserves_obs (compile := pass) (simT := _simT simT1) (simVIdx := _simVIdx simT1) (simV := _simV simT1 simV1).
  Proof.
    exact (lift_step_preserves_obs eq_s_initial eq_s_final step_preservation).
  Qed.

End PRESERVATION.
