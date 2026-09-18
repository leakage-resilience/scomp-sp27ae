(* -------------------------------------------------------------------------- *)
(* Register allocation. *)
(* Check that two programs are alpha-equivalent. *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import Utf8 ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  semantics
  syntax
  utils
  var
  preservation_obs
  ni_preservation.

Require Import language.
Existing Instance Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

Definition regpmap := PMr.t regvar.
Context (analyze_i : iinfo -> regpmap).

Section PASS.

Definition check_r (m : regpmap) (x_s x_t : regvar) : bool :=
  PMr.get m x_s == Some x_t.

Definition check_r_pw (m : regpmap) (xss xst : seq regvar) : bool :=
  (size xss == size xst) && foldr (fun '(s, t) => andb (check_r m s t)) true (zip xss xst).

Lemma check_r_pw_cons m a l a' l'
  : check_r m a a' /\ check_r_pw m l l' <-> check_r_pw m (a :: l) (a' :: l').
Proof.
  split.
  - move=>[] H /andP [/eqP Heq Hs].
    apply/andP.
    split.
    by rewrite /= Heq.
    simpl. by apply/andP.
  - move=> /andP [Hs /= /andP [Hcr Hcrs]].
    split. done.
    by apply/andP.
Qed.

Lemma check_r_pw_size m x y : check_r_pw m x y -> size x = size y.
Proof.
  move: x y.
  elim. by case.
  move=> a l H [//| a' l'].
  rewrite -check_r_pw_cons.
  move=>[] _ /andP [/eqP /= -> _] //.
Qed.

Fixpoint check_e (m : regpmap) (e_s e_t : expr) : bool :=
  match e_s, e_t with
  | Econst n_s, Econst n_t => n_s == n_t
  | Ebool b_s, Ebool b_t => b_s == b_t
  | Evar x_s, Evar x_t => check_r m x_s x_t
  | Eop1 op_s e_s, Eop1 op_t e_t => [&& op_s == op_t & check_e m e_s e_t ]
  | Eop2 op_s e0_s e1_s, Eop2 op_t e0_t e1_t =>
      [&& op_s == op_t, check_e m e0_s e0_t & check_e m e1_s e1_t ]
  | _, _ => false
  end.


Section MAP.
  (* m1 is a submap of m2 *)
  Definition incl (m1 m2 : regpmap) : bool := PMr.incl m1 m2.

  Lemma incl_trans m1 m2 m3 : incl m1 m2 -> incl m2 m3 -> incl m1 m3.
  Proof. by move => /PMr.inclP A /PMr.inclP B; apply/PMr.inclP; firstorder. Qed.

  Lemma incl_get m1 m2 e s: incl m1 m2 -> PMr.get m1 e = Some s -> PMr.get m2 e = Some s.
  Proof. move/PMr.inclP; exact. Qed.

  Lemma incl_id x : incl x x.
  Proof. exact/PMr.inclP. Qed.

  (* intersection! of two regpmaps, not union *)
  Definition merge  (m1 m2: regpmap) :=
    PMr.Map.map2
      (fun a b =>   match a, b with
                    | None, _ => None
                    | _, None => None
                    | Some x, Some y => if x == y then Some x else None
                    end)
      m1 m2.

  Lemma get_mergeE (p q: regpmap) k r :
    PMr.get (merge p q) k = r ->
    if r is Some x then [/\ PMr.get p k = Some x & PMr.get q k = Some x]
    else [\/ PMr.get p k = None, PMr.get q k = None | PMr.get p k <> PMr.get q k ].
  Proof.
    rewrite /PMr.get /merge => <-; rewrite PMr.Facts.map2_1bis //.
    case: PMr.Map.find => [ x | ]; last exact: Or31.
    case: PMr.Map.find => [ y | ]; last exact: Or32.
    case: eqP => [ -> | ne ] //; apply: Or33; congruence.
  Qed.

  Lemma merge_incl1 m1 m2: incl (merge m1 m2) m2.
  Proof. by apply/PMr.inclP => k r /get_mergeE []. Qed.

  Lemma merge_incl2 m1 m2: incl (merge m1 m2) m1.
  Proof. by apply/PMr.inclP => k r /get_mergeE []. Qed.

  Lemma merge_incl3 m1 m2 m3: incl m2 (merge m1 m3) -> incl m2 m1.
  Proof. by move => /PMr.inclP h; apply/PMr.inclP => ?? /h /get_mergeE []. Qed.

  Lemma merge_incl33 m1 m2 m3: incl m2 (merge m1 m3) -> incl m2 m3.
  Proof. by move => /PMr.inclP h; apply/PMr.inclP => ?? /h /get_mergeE []. Qed.

  Lemma merge_incl4 m1 m2 x e: incl m1 m2 -> PMr.get m1 x = Some e -> PMr.get m2 x = Some e.
  Proof. by move/PMr.inclP => h /h. Qed.

  Definition filter m x_t : regpmap := PMr.MoreMap.filter (fun _ e => x_t != e) m.

  Definition add m x_s x_t :=  PMr.set (filter m x_t) x_s x_t.

  Definition add_all m xss xst := foldr (fun '(s,t) m => add m s t) m (zip xss xst).

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

  Lemma incl_filter a b x':
    incl a b
    -> incl (filter a x') (filter b x').
  Proof.
    move => H.
    apply/PMr.inclP => k t Hk.
    rewrite -PMr.Facts.find_mapsto_iff.
    apply/PMr.MoreMap.filter_iff => []; first easy.
    split.
    * rewrite PMr.Facts.find_mapsto_iff.
      exact (incl_get H (filter_same Hk)).
    * exact (filter_x Hk).
  Qed.

  Lemma get_filter m x y v :
    x <> v -> PMr.get m y = some v -> PMr.get (filter m x) y = some v.
  Proof.
    intros h hg.
    rewrite -PMr.Facts.find_mapsto_iff.
    apply/PMr.MoreMap.filter_iff => []; first easy.
    split.
    * move: hg.
      by rewrite -PMr.Facts.find_mapsto_iff.
    * by move/eqP:h.
  Qed.

  Lemma incl_add a b x x':
    incl a b
    -> incl (add a x x') (add b x x').
  Proof.
    move=>H.
    apply/PMr.inclP=> k t.
    rewrite !get_add.
    case: (x == k) => //.
    refine (incl_get _).
    by apply incl_filter.
  Qed.

End MAP.


Section CMD.

  Variable check_i : regpmap -> instr -> instr -> regpmap -> Prop.
  Variable reg_renaming_i : regpmap -> instr -> regpmap -> option instr.

  Fixpoint reg_renaming_e (rs : regpmap) (e : expr) : option expr :=
    match e with
    | Econst z => some (Econst z)
    | Ebool b => some (Ebool b)
    | Evar x => let%opt x' := PMr.get rs x in some (Evar x')
    | Eop1 op e => let%opt e' := reg_renaming_e rs e in some (Eop1 op e')
    | Eop2 op el er =>
        let%opt el' := reg_renaming_e rs el in
        let%opt er' := reg_renaming_e rs er in
        some (Eop2 op el' er')
    end.

  Fixpoint reg_renaming_params (rs : regpmap) (x : seq regvar) : option (seq regvar) :=
    match x with
    | [::] => some [::]
    | x :: xs =>
        let%opt x' := PMr.get rs x in
        let%opt xs' := reg_renaming_params rs xs in
        some (x' :: xs')
    end.

  Definition get_current_c (c : code) (rs : regpmap) : regpmap :=
    match c with
    | [::] => rs
    | i :: _ => analyze_i (annot i)
    end.


  Fixpoint reg_renaming_c (c : code) (rs : regpmap) : option code :=
    match c with
    | [::] => if incl (get_current_c c rs) rs then
                some [::]
              else
                None
    | i :: c =>
        let mi := (get_current_c c rs) in
        let mj := (analyze_i (annot i)) in
        let%opt ui' := reg_renaming_i mj (unannot i) mi in
        let%opt c' := reg_renaming_c c rs in
        if incl mj (get_current_c (i :: c) rs) then
          some ({| annot := annot i; unannot := ui' |} :: c')
        else
          None
    end.


  (* congruence closure of check_i *)
  Inductive check_c_aux : regpmap -> code -> code -> regpmap -> Prop :=
  | Check_c_nul : forall m m', incl m' m -> check_c_aux m [::] [::] m'
  | Check_c_cons : forall m1 m2 m3 m4 c1 c2 l1 l2,
      incl m2 m1 ->
      check_i m2 (unannot c1) (unannot c2) m3 ->
      check_c_aux m3 l1 l2 m4 ->
      check_c_aux m1 (c1 :: l1) (c2 :: l2) m4.

  Lemma check_c_aux_singl m1 m2 a b:
    check_i m1 (unannot a) (unannot b) m2 -> check_c_aux m1 [::a] [::b] m2.
  Proof.
    move => h.
    eapply Check_c_cons.
    apply incl_id.
    apply h.
    apply Check_c_nul.
    apply incl_id.
  Qed.

  Fixpoint check_c' m p q m' : Prop :=
    match p, q with
    | [::], [::] => incl m' m
    | i :: p, j :: q => exists mi mj, [/\ incl mi m, check_i mi (unannot i) (unannot j) mj & check_c' mj p q m' ]
    | _, _ => False
    end.

  Lemma check_c'E m p q m' :
    check_c_aux m p q m' <-> check_c' m p q m'.
  Proof.
    split.
    - elim => { m p q m' } //.
      by move => m mi mj m' i j p q A B _ C; exists mi, mj.
      elim: p q m => [ | i p ih ] [ ] //.
    - by move => m /= h; constructor.
      by move => j q m /= [] mi [] mj [] A B /ih C; econstructor; eassumption.
  Qed.
End CMD.


Theorem reg_renaming_e_check_e {rs e e'} : reg_renaming_e rs e = some e' -> check_e rs e e'.
Proof.
  elim: e e'.
  - by move=> z; case=>//=?[=->].
  - by move=> z; case=>//=?[=->].
  - move=>s//=. rewrite/check_r. case: (PMr.get rs s)=>//a e'. by case: e'=>//=?[=]->.
  - move=>o e//=. case: (reg_renaming_e rs e)=>//=a ih. case=>//=o' e' [=]->ae.
    apply/andP. split; first done. apply:ih. by subst.
  - move=>o el//=.
    case: (reg_renaming_e rs el)=>//=al il er.
    case: (reg_renaming_e rs er)=>//=ar ir.
    case=>//=o' el' er' [=-> Hl Hr].
    apply/andP. split; first done.
    apply/andP. split; [apply il | apply ir]; by subst.
Qed.


Inductive check_i : regpmap -> instr -> instr -> regpmap -> Prop :=
| Check_i_Iassign :
  forall m1 m2 e1 e2 x1 x2,
    check_e m1 e1 e2 ->
    incl m2 (add m1 x1 x2) ->
    check_i m1 (Iassign x1 e1) (Iassign x2 e2) m2
| Check_i_Iload :
  forall m1 m2 e1 e2 x1 x2 a1 a2,
    check_e m1 e1 e2 ->
    check_r m1 x1 x2 ->
    incl m2 (add m1 x1 x2) ->
    a1 == a2 ->
    check_i m1 (Iload x1 a1 e1) (Iload x2 a2 e2) m2
| Check_i_Istore :
  forall m1 m2 a1 a2 e1 e2 x1 x2,
    a1 == a2 ->
    check_e m1 e1 e2 ->
    check_r m1 x1 x2 ->
    incl m2 m1 ->
    check_i m1 (Istore a1 e1 x1) (Istore a2 e2 x2) m2
| Check_i_Imop :
  forall m1 m2 vs1 vs2 mop1 mop2 xs1 xs2,
    mop1 = mop2 ->
    size xs1 == size xs2 ->
    check_r_pw m1 vs1 vs2 ->
    incl m2 (add_all m1 xs1 xs2) ->
    check_i m1 (Imop xs1 mop1 vs1) (Imop xs2 mop2 vs2) m2
| Check_i_Iif :
  forall m m1 m2 m3 e1 e2 c1 c2 c3 c4,
    check_e m e1 e2 ->
    check_c_aux check_i m c1 c3 m1 ->
    check_c_aux check_i m c2 c4 m2 ->
    incl m3 (merge m1 m2) ->
    check_i m (Iif e1 c1 c2) (Iif e2 c3 c4) m3
| Check_i_Iwhile_done:
  forall m m1 e1 e2 c1 c2,
    check_e m e1 e2 ->
    check_c_aux check_i m c1 c2 m ->
    incl m m1 ->
    incl m1 m ->
    check_i m (Iwhile e1 c1) (Iwhile e2 c2) m1.

Definition check_c := check_c' check_i.

Lemma eq_check_r m1 m2 e1 e2 :
  incl m1 m2 ->
  check_r m1 e1 e2 -> check_r m2 e1 e2.
Proof.
  unfold check_r.
  move => h1 h2.
  destruct (PMr.get m1 e1) eqn: H => //=.
  have h3 :=  incl_get h1 H.
  rewrite h3 => //=.
Qed.

Lemma eq_check_e m1 m2 e1 e2 :
  incl m1 m2 ->
  check_e m1 e1 e2 = true -> check_e m2 e1 e2 = true.
Proof.
  move => h1; move: e2.
  induction e1 => //=; destruct e2 => //=.
  rewrite /check_r.
  destruct (PMr.get m1 s) eqn: H => //.
  move : (merge_incl4 h1 H) -> => //=.
  destruct (o == o0) => //=.
  apply IHe1.
  destruct (o == o0) => //=.
  move => h.
  apply Bool.andb_true_iff.
  apply Bool.andb_true_iff in h.
  destruct h.
  auto.
Qed.

Lemma check_c'_incl check_instr m1 m2 m3 l1 l2 :
  incl m1 m2 -> check_c' check_instr m1 l1 l2 m3 -> check_c' check_instr m2 l1 l2 m3.
Proof.
  move => h1.
  case: l1 l2 => [ | i1 l1 ] [] //=.
  + move => H; exact: (incl_trans H h1).
  by move => i2 l2 [] mi [] mj [] A B C; exists mi, mj; split; first exact: (incl_trans A h1).
Qed.

Lemma check_c_incl m1 m2 m3 l1 l2 :
  incl m1 m2 -> check_c m1 l1 l2 m3 -> check_c m2 l1 l2 m3.
Proof. exact: check_c'_incl. Qed.

Lemma check_c_compose m1 m2 m3 l1 l2 l3 l4 :
  check_c m1 l1 l3 m3 ->  check_c m3 l2 l4 m2 ->
  check_c m1 (l1 ++ l2) (l3 ++ l4) m2.
Proof.
  move => /check_c'E h1 h2.
  induction h1 => /=.
  + exact: check_c_incl H h2.
  exists m0, m3; split => //.
  exact: IHh1.
Qed.

Fixpoint check_params (m : regpmap) (xs1 xs2 : seq regvar)  : regpmap :=
  match xs1, xs2 with
  | [::], _ | _, [::] => m
  | x1 :: xs1, x2 :: xs2 => add (check_params m xs1 xs2) x1 x2
  end.

Definition check_p (* rs *) (p_s p_t : prog) :=
  let rs := check_params (PMr.empty _) (p_inputs p_s) (p_inputs p_t) in
  [/\ (exists rs', check_c rs (p_prog p_s) (p_prog p_t) rs')
    & size (p_inputs p_s) = size (p_inputs p_t)].

Variant ex2_3 (A B: Type) (P Q R : A -> B -> Prop) : Prop :=
  | Ex2_3 a b of P a b & Q a b & R a b.

Variant ex2_4 (A B: Type) (P Q R S : A -> B -> Prop) : Prop :=
  | Ex2_4 a b of P a b & Q a b & R a b & S a b.

Fixpoint check_instr rs i j rs' : Prop :=
  match i with
  | Iassign x e =>
      exists x' e', [/\ j = Iassign x' e', check_e rs e e' & incl rs' (add rs x x')]
  | Iload x a e =>
      exists x' e', [/\ j = Iload x' a e', check_e rs e e', check_r rs x x' & incl rs' (add rs x x')]
  | Istore a e x =>
      incl rs' rs /\
      exists e' x', [/\ j = Istore a e' x', check_e rs e e' & check_r rs x x']
  | Imop xs mop vs =>
      exists xs' vs', [/\ j = Imop xs' mop vs', size xs == size xs', check_r_pw rs vs vs' & incl rs' (add_all rs xs xs')]
  | Iif e th el =>
      exists2 e',
        check_e rs e e'
        & exists th',
          exists2 rs_th,
            check_c' check_instr rs th th' rs_th
            & exists el' rs_el,
              [/\ check_c' check_instr rs el el' rs_el, incl rs' (merge rs_th rs_el) & j = Iif e' th' el']
  | Iwhile e c =>
      exists2 e', check_e rs e e'
        & exists c',
          [/\ check_c' check_instr rs c c' rs,  incl rs' rs, incl rs rs' & j = Iwhile e' c']
  end.

Section CHECK_IE.
  Let Pi i := ∀ j rs rs', check_i rs i j rs' <-> check_instr rs i j rs'.
  Let Pii i := Pi (unannot i).
  Let Pc cs := ∀ ct rs rs', check_c rs cs ct rs' <-> check_c' check_instr rs cs ct rs'.

  Local Ltac ps := repeat match goal with H : is_true (_ == _) |- _ => move/eqP: H => H; subst end.

  Lemma check_iE rs i j rs' :
    check_i rs i j rs' <-> check_instr rs i j rs'.
  Proof.
    apply: {rs i j rs'} (@ind_i Pi Pii Pc) => //; cycle -1.
    - rewrite /Pii /Pi /Pc => - [] ii i cs hi hc [] // j ct rs rs'; split => /= - [] mi [] mj [] *; exists mi, mj; split; try eassumption.
      1, 3: apply/hi; assumption.
      1, 2: apply/hc; assumption.
    all: move => >.
    5: move => ih1 ih2.
    6: move => ih.
    all: split.
    - 1, 3: by inversion 1; ps; do ? eexists.
    - 1, 2: by move=>[]?[]?[]->*; constructor.
    - by inversion 1; ps; split; first assumption; do ? eexists.
    - by do 4! move=> []? ; subst=>*; constructor.
    - by inversion 1; do ? eexists; subst.
    - by do 3! (move=> []?); subst; constructor.
    - inversion 1; eexists; first eassumption.
      eexists _, _.
      + apply/ih1/check_c'E; eassumption.
      eexists _, _; split; last reflexivity.
      + apply/ih2/check_c'E; eassumption.
      done.
    - rewrite /= => - [] ?? [] ? [] ?? [] ? [] ? [] ?? ->.
      econstructor; only 1, 4: eassumption.
      + exact/check_c'E/ih1.
      exact/check_c'E/ih2.
    -inversion 1; ps; subst. eexists. eassumption.
      eexists. split ; try done. apply ih. exact/check_c'E.
    - move=>[]??[]?[]????. subst. econstructor; try done.
      apply/check_c'E. apply ih. done.
  Qed.

  Lemma check_cE cs ct rs rs' :
    check_c rs cs ct rs' <-> check_c' check_instr rs cs ct rs'.
  Proof.
    apply: {cs ct rs rs'} (@ind_c_aux Pi Pii Pc) => //; last by move => ???; exact: check_iE.
    rewrite /Pii /Pi /Pc => - [] ii i cs hi hc [] // j ct rs rs'; split => /= - [] mi [] mj [] *; exists mi, mj; split; try eassumption.
    1, 3: apply/hi; assumption.
    1, 2: apply/hc; assumption.
  Qed.

End CHECK_IE.

End PASS.

(* -------------------------------------------------------------------------- *)
(* Backward simulation. *)
(* T__T *)
(* -------------------------------------------------------------------------- *)

Require Import
  semantics_facts
  semantics_facts
  utils_facts
.

Section PROOF.

Context
  (p_s p_t : prog)
  (hcompile : check_p p_s p_t)
.

Definition is_vm_renaming (rs : regpmap) (vm_s vm_t : vmap) : Prop :=
    forall x,
        if PMr.get rs x is Some y
        then Mr.get vm_s x = Mr.get vm_t y
        else True.

Lemma eq_eval r vm_s vm_t e1 e2 :
  is_vm_renaming r vm_s vm_t -> check_e r e1 e2 ->
  eval_e vm_s e1 = eval_e vm_t e2.
Proof.
move => h1.
move: e2.
induction e1 => //=; destruct e2 => //=.
- move => H; case (eqP H); reflexivity.
- move => H; case (eqP H); reflexivity.
- move => H.
  have h2 := h1 s.
  unfold check_r in H.
  destruct (PMr.get r s) eqn: H1 => //=.
  by move : H => /eqP [= <-].
- move => h.
  have [H4 H5] := andb_prop _ _ h.
  case (eqP H4) => //=.
  by destruct o; move: (IHe1 _ H5) ->; destruct (eval_e vm_t e2) => //=.
- move => h.
  have [H4 H5] := andb_prop _ _ h.
  have [H6 H7] := andb_prop _ _ H5.
  case (eqP H4) => //=.
  by destruct o; move: (IHe1_1 _ H6) ->; move: (IHe1_2 _ H7) ->;
  destruct (eval_e vm_t e2_1) => //=; destruct (evcheck_p al vm_t e2_2).
Qed.

Definition is_allocation (rs : regpmap) (s t : state) : Prop :=
  [/\ exists rs', check_c rs (s_c s) (s_c t) rs'
    , is_vm_renaming rs (s_vm s) (s_vm t)
    & s_mem s = s_mem t
  ].

Lemma vm_incl m1 m2 a b:
  incl m1 m2 ->
  is_vm_renaming m2 a b ->
  is_vm_renaming m1 a b.
Proof.
  rewrite /is_vm_renaming.
  move => h1 h2 x.
  destruct (PMr.get m1 x) eqn: H1; last by [].
  have h3 := merge_incl4 h1 H1.
  move : (h2 x); rewrite h3 => //=.
Qed.

Lemma is_vm_renaming_set m m' x x' vm vm' v :
  is_vm_renaming m vm vm' ->
  incl m' (add m x x') ->
  is_vm_renaming m' (Mr.set vm x v) (Mr.set vm' x' v).
Proof.
  move => ok_vm /PMr.inclP h k.
  case: PMr.get {h} (h k) => // ? /(_ _ erefl).
  rewrite get_add !Mr.get_set.
  case: eqP => ?.
  + by move => /Some_inj <-; rewrite eqxx.
  move => /[dup] /filter_same h /filter_x /negbTE ->.
  have := ok_vm k.
  by rewrite h.
Qed.

Lemma check_r_get rs x x' m m' :
  is_vm_renaming rs m m' ->
  check_r rs x x' ->
  Mr.get m x = Mr.get m' x'.
Proof.
  rewrite /check_r => /(_ x).
  move => H /eqP H'.
  by rewrite H' in H.
Qed.

Lemma leaks_eq mi rs svm tvm e e':
  is_vm_renaming rs svm tvm
  -> incl mi rs
  -> check_e mi e e'
  -> leaks_e svm e = leaks_e tvm e'.
Proof.
  move=> Hvmrenaming Hincl.
  move: e' e.
  elim => //=.
  + by move=>? [] //= ? /eqP -> //.
  + by move=>? [] //= ? /eqP -> //.
  + move=>s [] //= s'.
    unfold check_r => /eqP Hmi.
    by move: Hmi (vm_incl Hincl Hvmrenaming s') => -> ->//.
  + move=> o e ih [] //= ? e' /andP [/eqP -> Hcheck].
    rewrite (ih e' Hcheck).
    suff : eval_e svm e' = eval_e tvm e by move=>->//.
    apply (eq_eval Hvmrenaming).
    exact (eq_check_e Hincl Hcheck).
  + move=> o el ihl er ihr [] //= o' el' er'.
    move=> /andP [/eqP -> /andP [Hcl Hcr]] //=.
    rewrite (ihl el' Hcl) (ihr er' Hcr).
    suff : eval_e svm el' = eval_e tvm el
           /\ eval_e svm er' = eval_e tvm er
      by move=> [-> ->] //.
    split
    ; apply (eq_eval Hvmrenaming)
    ; [ exact (eq_check_e Hincl Hcl)
      | exact (eq_check_e Hincl Hcr) ].
Qed.

End PROOF.

Section FLSD.

Definition Pifw (i: instr) :=
  forall a c rs s ot ov s' t,
    s_c s = {| unannot := i; annot := a |} :: c ->
    is_allocation rs s t ->
    step s ot ov s' ->
    exists2 t', step t ot ov t' & exists rs', is_allocation rs' s' t'.

Lemma Hassign : forall x e, Pifw (Iassign x e).
Proof.
  move=>x e a c rs s ot ov s' t Hss.
  move=>[] [] rs'.
  move: s t Hss => [sc svm smem] [tc tvm tmem] /= ->.
  move=> Hcheck Hvmrenaming Hmem.
  move/stepI=>//=.
  destruct tc as [| [a' i'] c'] => //=.
  move : Hcheck => [mi [mj [Hincl -]]] //= => Hci Hrest [->->->].
  move : Hci.
  move/check_iE => [] x' [e' [-> H]] Hincl'.

  eexists.
  - apply stepI.
    subst; rewrite (leaks_eq Hvmrenaming Hincl H); easy.
  - eexists.
    split; try by subst.
    + exists rs'=>/=.
      exact Hrest.
    + subst; simpl.
      rewrite (eq_eval Hvmrenaming (eq_check_e Hincl H)).
      apply (is_vm_renaming_set _ Hvmrenaming).
      apply (incl_trans Hincl').
      by apply incl_add.
Qed.

Lemma Hload : forall a e x, Pifw (Iload a e x).
Proof.
  move=>a e x ia c rs s ot ov s' t Hss.
  move=>[] [] rs'.
  move: s t Hss => [sc svm smem] [tc tvm tmem] /= ->.
  move=> Hcheck Hvmrenaming Hmem.
  move/stepI=>//=.
  destruct tc as [| [a' i'] c'] => //=.
  move : Hcheck => [mi [mj [Hincl -]]] //= => Hci Hrest.
  move=> [addr [] He Hb Hdef -> -> ->] //=.

  move/check_iE : Hci => [] ? [] e' [] -> Hce Hcr Hincl'.
  subst.
  eexists.
  - apply stepI => //=.
    exists addr; split => //=.
    + move : He => <-; symmetry.
      by apply (eq_eval Hvmrenaming), (eq_check_e Hincl Hce).
    + by rewrite (leaks_eq Hvmrenaming Hincl Hce).
  - eexists; split => //=.
    + eexists; eassumption.
    + apply: vm_incl; first eassumption.
      apply: is_vm_renaming_set.
      by apply: (vm_incl Hincl).
      apply incl_id.
Qed.

Lemma Hstore : forall a e x, Pifw (Istore a e x).
Proof.
  move=>a e x ia c rs s ot ov s' t Hss.
  move=>[] [] rs'.
  move: s t Hss => [sc svm smem] [tc tvm tmem] /= ->.
  move=> Hcheck Hvmrenaming Hmem.
  move/stepI=>//=.
  destruct tc as [| [a' i'] c'] => //=.
  move : Hcheck => [mi [mj [Hincl -]]] //= => Hci Hrest.
  move=> [addr [] He Hb Hdef -> -> ->] //=.

  move/check_iE : Hci => [] ? [] e' [] x' []-> Hce Hcr.
  subst.
  eexists.
  - apply stepI => //=.
    erewrite <-(check_r_get Hvmrenaming); first last.
    apply: eq_check_r. eassumption. exact Hcr.
    exists addr; split => //=.
    + move : He => <-; symmetry.
      by apply (eq_eval Hvmrenaming), (eq_check_e Hincl Hce).
    + erewrite leaks_eq; first reflexivity; eassumption.
  - eexists; split => //=.
    + eexists; eassumption.
    + apply: vm_incl. apply: incl_trans; eassumption. done.
    + erewrite <-(check_r_get Hvmrenaming); first last.
      apply: eq_check_r. eassumption. exact Hcr.
      done.
Qed.

Lemma eval_mop_varmap mop rs xs ys v vmx vmy :
  is_vm_renaming rs vmx vmy
  -> check_r_pw rs xs ys
  -> eval_mop vmx mop xs v
  -> eval_mop vmy mop ys v.
Proof.
  move=> H Hc.
  rewrite !eval_mopE => <-.
  elim: mop
  ; simpl
  ; elim: xs ys Hc => [[]//|a l IH [//|a' l']]
  ; rewrite -check_r_pw_cons=> -[Hc Hcs]
  .
  1-2:
    destruct l, l' => //
    ; by rewrite (check_r_get H Hc)=> //
  .
  1-3:
    destruct l, l' => //
    ; destruct l, l' => //
    ; rewrite (check_r_get H Hc)
    ; case (Mr.get vmy a') =>// z
    ; move/check_r_pw_cons: Hcs => [Hc' _]
    ; by rewrite (check_r_get H Hc')
  .
Qed.

Lemma size_length {T} (x : seq T): length x = size x.
Proof. done. Qed.

Lemma vm_renaming_after_regwrites yvs mj xs xs' c c' svm tvm smem tmem :
  size xs = size xs'
  -> size xs = size yvs
  -> is_vm_renaming mj svm tvm
  -> is_vm_renaming (add_all mj xs xs')
    (s_vm
       (s_after_regwrites
          {|
            s_c := c; s_vm := svm; s_mem := smem
          |} c (zip xs yvs)))
    (s_vm
       (s_after_regwrites
          {|
            s_c := c'; s_vm := tvm; s_mem := tmem
          |} c' (zip xs' yvs))).
Proof.
  move: yvs xs xs' c c'.
  elim.
  - by destruct xs, xs'.
  - move=>yv yvs IH.
    destruct xs, xs'; try done.
    move=>c c' Hs Hs' Hren x.
    simpl.
    apply: is_vm_renaming_set.
    apply IH.
    + by move: Hs => /=[=].
    + by move: Hs'=> /=[=].
    + done.
    + by apply incl_id.
Qed.

Lemma mem_after_regwrites yvs xs xs' c c' svm tvm mem :
  size xs = size xs'
  -> size xs = size yvs
  -> s_mem
       (s_after_regwrites
          {|
            s_c := c; s_vm := svm; s_mem := mem
          |} c (zip xs yvs))
     = s_mem
         (s_after_regwrites
            {|
              s_c := c'; s_vm := tvm; s_mem := mem
            |} c' (zip xs' yvs)).
Proof.
  move: yvs xs xs' c c'.
  elim.
  - by destruct xs, xs'.
  - move=>yv yvs IH [//|??] [//|??] c c' Hs Hs'.
    apply IH.
    + by move: Hs => /=[=].
    + by move: Hs'=> /=[=].
Qed.


Lemma Hmop xs mop vs : Pifw (Imop xs mop vs).
Proof.
  move=> ia c rs s ot ov s' t Hss [] [] rs'.
  move: s t Hss => [sc svm smem] [tc tvm tmem] /= -> Hcheck Hvmrenaming Hmem.
  move/stepI=>//=.
  destruct tc as [| [a' i'] c'] => //=.

  move : Hcheck => [mi [mj [Hincl -]]] //= => Hci Hrest.
  move/check_iE: Hci
      => //= [] xs' [vs' []] -> /eqP Hsize Hcr Hincl' [yvs []] Heval Hlen -> -> ->.
  eexists.
  - apply stepI => //=.
    eexists yvs; split=>//=.
    + apply: eval_mop_varmap.
      * apply: (vm_incl Hincl); eassumption.
      * eassumption.
      * exact.
    + rewrite -Hlen size_length//.
    + erewrite leaks_mop_eq. reflexivity.
      move: Hcr => /andP [/eqP Hs Heq]. split. done.
      elim: (zip vs vs') Heq =>// - [al ar] l /= H /andP [H1 H2].
      apply/andP.
      split. erewrite (check_r_get); last exact H1. done. apply: vm_incl; eassumption.
      by apply H.
   - eexists; split.
    + eexists. eassumption.
    + subst. simpl.
      apply: vm_incl. exact Hincl'.
      apply vm_renaming_after_regwrites.
      done. done.
      apply: vm_incl; eassumption.
    + subst. simpl.
      by apply mem_after_regwrites.
Qed.

Lemma Hif : forall b th el, Pifw (Iif b th el).
Proof.
  move=>a e x ia c rs s ot ov s' t Hss.
  move=>[] [] rs'.
  move: s t Hss => [sc svm smem] [tc tvm tmem] /= ->.
  move=> Hcheck Hvmrenaming Hmem.
  move/stepI=>//=.
  destruct tc as [| [a' i'] c'] => //=.

  move : Hcheck => [mi [mj [Hincl -]]] //= => Hci Hrest.
  move/check_iE : Hci
      => //= [] e' Hce [] th' [] rs_th Hc_th [] el' [] rs_el [] Hc_el Hincl' ?.
  move=> [b [He Hot Hov Hs']]; subst.
  simpl.
  eexists=>//.
  - apply stepI => //=.
    exists b; split => //=.
    + move: He => <-; symmetry.
      by apply (eq_eval Hvmrenaming), (eq_check_e Hincl Hce).
    + by rewrite (leaks_eq Hvmrenaming Hincl Hce).
  - eexists; split => //=; last exact Hvmrenaming.
    eexists.
    destruct b.
    apply: check_c_compose.
    * apply: (check_c_incl Hincl).
      apply (check_cE) ; exact Hc_th.
    * apply: check_c_incl.
      apply (merge_incl3 Hincl').
      exact Hrest.
      apply: check_c_compose.
    * apply: (check_c_incl Hincl).
      apply (check_cE) ; exact Hc_el.
    * apply: check_c_incl.
      apply (merge_incl33 Hincl').
      exact Hrest.
Qed.

Lemma Hwhile : ∀ e c , Pifw (Iwhile e c).
Proof.
  move=> e cb ia c rs s ot ov s' t Hss.
  move=>[] [] rs'.
  move: s t Hss => [sc svm smem] [tc tvm tmem] /= ->.
  move=> Hcheck Hvmrenaming Hmem.
  move/stepI=>//=.
  destruct tc as [| [a' i'] c'] => //=.

  move : Hcheck => [mi [mj [Hincl -]]] //= => Hci Hrest.
  move/check_iE : Hci => //= [] e' Hce [] ? []  Hc Hincll Hinclr ?.
  move=> [b [He Hot Hov Hs']]; subst.

  eexists =>//.
  - apply stepI => //=.
    exists b; split => //=.
    + move: He => <-; symmetry.
      by apply (eq_eval Hvmrenaming), (eq_check_e Hincl Hce).
    + by rewrite (leaks_eq Hvmrenaming Hincl Hce).
  - eexists; split => //=.
    + eexists; simpl.
      destruct b; last exact Hrest.
      apply: check_c_compose.
      apply: check_c_incl; first last.
      rewrite check_cE. exact Hc.
      exact.
      apply: check_c_incl. eassumption.
      simpl.
      eexists _, _. split; last exact Hrest.
      eassumption.
      apply/check_iE.
      simpl.
      eexists. eassumption. eexists. split; try done.
      assumption.
    + apply: vm_incl.
      exact Hincll.
      apply: vm_incl.
      exact Hincl.
      exact.
Qed.

(*
Lemma forward_lock_step_diagram rs s ot ov s' t :
  is_allocation rs s t ->
  step s ot ov s' ->
  exists2 t', step t ot ov t' & exists rs', is_allocation rs' s' t'.
Proof.
  *)

Lemma forward_lock_step_diagram' : forall i, Pifw i.
Proof.
  elim.
  - exact Hassign.
  - exact Hload.
  - exact Hstore.
  - exact Hmop.
  - exact Hif.
  - exact Hwhile.
Qed.

End FLSD.

Definition sim_rel s t : Prop :=
  ∃ rs, is_allocation rs s t.

Lemma forward_lock_step_diagram s ot ov s' t :
  sim_rel s t ->
  step s ot ov s' ->
  exists2 t', step t ot ov t' & sim_rel s' t'.
Proof.
  move=> rel step.
  have [[a i] [c Hc]] := step_code step.
  move: rel step.
  case => rs.
  apply: forward_lock_step_diagram'.
  exact Hc.
Qed.

Existing Instance Source.

Fixpoint reg_renaming_r_pw (rs : regpmap) (xs : seq regvar) : option (seq regvar)
  := match xs with
     | [::] => some [::]
     | x :: xs => let%opt x' := PMr.get rs x in
                  let%opt xs' := reg_renaming_r_pw rs xs in
                  some (x' :: xs')
     end.

Theorem reg_renaming_r_pw_check_r_pw rs x y:
  reg_renaming_r_pw rs x = some y -> check_r_pw rs x y.
Proof.
  elim: x y. by case.
  move=> x xs IH [|y ys]
  ; simpl
  ; apply: obindP=> x' Hx'
  ; apply: obindP=> xs' Hxs'
  ; first done.
  move=>[=] <- <-.
  apply check_r_pw_cons.
  split. rewrite/check_r. exact/eqP.
  apply IH. done.
Qed.

Theorem reg_renaming_r_pw_size rs x y:
  reg_renaming_r_pw rs x = some y -> size x = size y.
Proof.
  intro H.
  exact (check_r_pw_size (reg_renaming_r_pw_check_r_pw H)).
Qed.

Fixpoint reg_renaming_i (rs : regpmap) (i : instr) (rs' : regpmap) : option instr
  := match i with
     | Iassign x e =>
         let%opt e' := reg_renaming_e rs e in
         let%opt x' := PMr.get rs x in
         if incl rs' (add rs x x') then some (Iassign x' e') else None
     | Iload x a e =>
         let%opt e' := reg_renaming_e rs e in
         let%opt x' := PMr.get rs x in
         if incl rs' (add rs x x') then some (Iload x' a e') else None
     | Istore a e x =>
         let%opt e' := reg_renaming_e rs e in
         let%opt x' := PMr.get rs x in
         if incl rs' rs then some (Istore a e' x') else None (* maybe make eqType *)
     | Imop xs mop vs =>
         let%opt vs' := reg_renaming_r_pw rs vs in
         let%opt xs' := reg_renaming_r_pw rs xs in
         if incl rs' (add_all rs xs xs') then some (Imop xs' mop vs') else None
     | Iif e ct ce =>
         let%opt e' := reg_renaming_e rs e in
         let rs_th := rs' in (* TODO; seperate regpmap for then and else case. *)
         let%opt ct' := reg_renaming_c reg_renaming_i ct rs_th in
         let rs_el := rs' in
         let%opt ce' := reg_renaming_c reg_renaming_i ce rs_el in
         if incl (get_current_c ct rs_th) rs then
           if incl (get_current_c ce rs_el) rs then
             if incl rs' (merge rs_th rs_el) then some (Iif e' ct' ce') else None
           else
             None
         else
           None
     | Iwhile b c =>
         let%opt b' := reg_renaming_e rs b in
         let%opt c' := reg_renaming_c reg_renaming_i c rs in
         if incl (get_current_c c rs) rs' then
           if incl rs rs' then
             if incl rs' rs then
               some (Iwhile b' c')
             else
               None
           else
             None
         else
           None
     end.

Definition reg_renaming_ii (i : instr_i) (rs' : regpmap) : option instr_i :=
  let%opt ut := reg_renaming_i (analyze_i (annot i)) (unannot i) rs' in
  some {| annot := annot i; unannot := ut |}.


Section PI.
  Definition Pi i := forall rs i' rs_out,
      reg_renaming_i rs i rs_out = some i'
      -> check_i rs i i' rs_out.

  Definition Pii ii := forall i' rs_out,
      reg_renaming_i (analyze_i (annot ii)) (unannot ii) rs_out = some i'
      -> check_i (analyze_i (annot ii)) (unannot ii) i' rs_out.

  Definition Pc c := forall rs c' rs_out,
      reg_renaming_c reg_renaming_i c rs_out = some c'
      -> incl (get_current_c c rs_out) rs
      -> check_c rs c c' rs_out.

  Theorem reg_renaming_c_nil : Pc [::].
  Proof. rewrite/Pc=>?. elim. move=>?//=.
         move=>i c ? rs_out //=. by case: ifP. Qed.

  Theorem reg_renaming_c_cons:
    forall (i : instr_i) (c : code), Pii i → Pc c → Pc (i :: c).
  Proof.
    rewrite/Pii/Pc. move=>i c ih ich c' rs rs_out.
    unfold reg_renaming_c.
    apply:obindP=>//=??.
    apply:obindP=>//= cs Hcs.
    rewrite incl_id.
    move=>[=]<-.
    exists (analyze_i (annot i)), (get_current_c c rs_out).
    split. exact.
    apply ih. exact.
    apply ich. exact.
    apply incl_id.
  Qed.

  Theorem reg_renaming_i_check_i : forall i, Pi i.
  Proof.
    apply: (@ind_i Pi Pii Pc).
    unfold Pi, Pii, Pc.
    - move=> x e rs i' rs_out.
      apply:obindP => e' he'.
      apply:obindP => x' hx'.
      case: ifP => // hrs.
      case: i'=>//?? [=] <- <-.
      apply check_iE. eexists _, _.
      by rewrite reg_renaming_e_check_e.
    - move=> x a e rs i' rs_out.
      apply:obindP => e' he'.
      apply:obindP => x' hx'.
      case: ifP => // hrs.
      case: i'=>//??? [=] *. subst.
      apply check_iE. eexists _, _.
      rewrite reg_renaming_e_check_e.
      split; try done. by apply/eqP. done.
    - move=> a e x rs i' rs_out.
      apply:obindP => e' he'.
      apply:obindP => x' hx'.
      case: ifP => // hrs.
      case: i'=>//??? [=] *; subst.
      apply check_iE.
      split; first done. eexists _, _.
      by split; [done|rewrite reg_renaming_e_check_e|apply/eqP].
    - move=> xs o es rs i' rs_out.
      apply:obindP => e' he'.
      apply:obindP => x' hx'.
      case: ifP => // hrs.
      case: i'=>//??? [=] *; subst.
      apply check_iE.
      eexists. eexists; split=>//.
      apply /eqP.
      apply: reg_renaming_r_pw_size. eassumption.
      apply reg_renaming_r_pw_check_r_pw. done.
    - move=> e ct ce ict ice rs i' rs_out.
      apply:obindP => e' he'.
      apply:obindP => ct' hct'.
      apply:obindP => cf' hcf'.
      case: ifP => // hrs_t.
      case: ifP => // hrs_f.
      case: ifP => // hrs_after.
      case: i'=>//??? [=] <-<-<-.
      apply check_iE => //=.
      exists e'. exact (reg_renaming_e_check_e he').
      exists ct', rs_out.
      apply check_cE. apply ict. exact hct'. exact.
      exists cf', rs_out. split.
      apply check_cE. apply ice. exact hcf'. exact.
      exact.
      reflexivity.
    - move=> e c ic rs i' rs_out.
      apply:obindP=>e' he'.
      apply:obindP=>c' hc'.
      case: ifP => // hincl.
      case: ifP => // hincl'.
      case: ifP => // hincl''.
      case: i'=>//?? [=] <-<-.
      apply check_iE =>//=.
      exists e'.
      exact (reg_renaming_e_check_e he').
      exists c'. split; try exact.
      apply check_cE.
      apply: (check_c_incl hincl'').
      by apply ic.
    - exact reg_renaming_c_nil.
    - exact reg_renaming_c_cons.
    - rewrite/Pi/Pii=>i a h.
      move=>i' rs_out//=.
      exact (h (analyze_i a) i' rs_out).
  Qed.

  Theorem reg_renaming_c_check_c c rs_out c':
    reg_renaming_c reg_renaming_i c rs_out = some c'
    -> check_c (get_current_c c rs_out) c c' rs_out.
  Proof.
    elim: c c'.
    - by move=> c' //=; case: ifP => // ? [=] <-.
    - move=>i c H [//=|i' c'] //.
      + apply:obindP=>??.
        apply:obindP=>??.
        case:ifP=>//.
      + apply:obindP=>i'' Hi''.
        apply:obindP=>c'' Hc''.
        case:ifP=>// Hincl [=] ??. subst.
        simpl.
        eexists (analyze_i (annot i)), (get_current_c c rs_out).
        split. apply incl_id.
        apply reg_renaming_i_check_i. exact.
        apply H. exact.
  Qed.

  Definition reg_renaming_p (p : prog) (rs : regpmap): option prog :=
    let%opt c' := reg_renaming_c reg_renaming_i (p_prog p) rs in
    let%opt i' := reg_renaming_params (get_current_c (p_prog p) rs) (p_inputs p) in
    let%opt o' := reg_renaming_params rs (p_outputs p) in
    if incl (get_current_c (p_prog p) rs) (check_params (PMr.empty regvar) (p_inputs p) i') then
      some {| p_prog := c'; p_inputs := i'; p_outputs := o' |}
    else
      None.

  Theorem reg_renaming_p_check_p p rs p':
    reg_renaming_p p rs = some p'
    -> check_p p p'.
  Proof.
    apply:obindP=>c' Hc'.
    apply:obindP=>in' Hin'.
    apply:obindP=>out' Hout'.
    case:ifP=>// Hincl [=] <-.
    split.
    - exists rs.
      simpl.
      apply: check_c_incl.
      + exact Hincl.
      + exact (reg_renaming_c_check_c Hc').
      move: Hin'.
      clear Hincl.
      elim: (p_inputs p) in'. by case.
      move=>a l IH in'.
      apply:obindP=>??.
      apply:obindP=>? Hren.
      case: in' => //a' l' [=] * //=.
      congr (_).+1.
      apply IH. by subst.
  Qed.
End PI.

Section PRESERVATION.

Context (rs : regpmap).

Definition pass : compiler (input := input) (Ls := Source) (Lt := Source) :=
  fun p_s => reg_renaming_p p_s rs.

Definition _simT1 : SimT1 :=
  fun pc_s ot_s => [:: ot_s].

Definition _simV1 : SimV1 :=
  fun pc_s ot_s ov_s => [:: ov_s].

Definition eq_s s t := exists rs, is_allocation rs s t.

Lemma step_preservation:
  step_preserves_obs eq_s _simT1 _simV1.
Proof.
  move=>s t ot_s ov_s s' [rs_in Halloc] sstep.
  have Hsr: sim_rel s t by exists rs_in.
  have [t' tstep [rs' Halloc']] :=  (forward_lock_step_diagram Hsr sstep).
  exists [:: ot_s], [:: ov_s], t'.
  split
  ; [ exact (sem_step1 tstep)
    | done
    | done
    | by exists rs'
    ].
Qed.

Theorem eq_s_initial:
  eq_s_initial (compile := pass) eq_s.
Proof.
  move=>p_s p_t inp.
  apply:obindP=>c Hc.
  apply:obindP=>i Hi.
  apply:obindP=>o Ho.
  case:ifP=>// Hincl [=<-].
  eexists. split; last done.
  - eexists. by apply (reg_renaming_c_check_c Hc).
  - simpl.
    apply: vm_incl. exact Hincl. clear -Hi.
    set i' := p_inputs p_s in Hi |- *.
    set rs_in := (get_current_c (p_prog p_s) rs) in Hi |- *.
    move=> x.
    destruct (PMr.get (check_params (PMr.empty regvar) i' i) x) eqn:eq => //.
    elim: inp i' i Hi eq; first by move=>[|??][].
    move=> //= inp inps H [[]//|a l [//=| a' l']] Hren Heq.
    simpl.
    rewrite !Mr.get_set.
    case:ifP=>Hax.
    + move: Heq=>//=. rewrite get_add Hax => [=] <-. by rewrite eq_refl.
    + move: Heq=>//=. rewrite get_add Hax => Hget.
      move: (filter_x Hget) => /negbTE ->.
      apply H.
      * move: Hren => //=.
        apply:obindP=>//=??.
        apply:obindP=>//=??[=]*. by subst.
      * exact (filter_same Hget).
Qed.

Theorem eq_s_final: eq_s_final eq_s.
Proof.
  move=>s t [rs_in [[rs_out Hc] Hrn]].
  simpl. unfold semantics.final.
  by destruct (s_c s), (s_c t).
Qed.

Theorem preservation_obs:
  preserves_obs (compile := pass) (simT := _simT _simT1) (simVIdx := _simVIdx _simT1) (simV := _simV _simT1 _simV1).
Proof.
  exact (lift_step_preserves_obs eq_s_initial eq_s_final step_preservation).
Qed.

End PRESERVATION.
