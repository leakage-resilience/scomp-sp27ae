(* -------------------------------------------------------------------------- *)
(* Semantics. *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From Coq Require Relations.
From mathcomp Require Import all_ssreflect.
From Coq Require Import Equality.

Require Import
  syntax
  utils
  utils_facts
  var
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.


(* -------------------------------------------------------------------------- *)
(* Values. *)

Variant value :=
  | Vint of Z
  | Vbool of bool
  | Vundef
.

Scheme Equality for value.

Lemma value_eq_axiom : Equality.axiom value_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_value_dec_bl internal_value_dec_lb).
Qed.

Definition value_eqMixin := Equality.Mixin value_eq_axiom.
Canonical value_eqType := EqType value value_eqMixin.

Definition is_defined (v : value) : bool := if v is Vundef then false else true.


(* -------------------------------------------------------------------------- *)
(* Variable maps. *)

Definition vmap := Mr.t value.

(* -------------------------------------------------------------------------- *)
(* Memory. *)
(* We have a segmented memory (in arrays) and reads or writes that are out of
   bounds always return [Vundef]. *)

Definition in_bounds (a : arrvar) (i : Z) :=
  [&& 0 <=? i & i <? arrlen a ]%Z.

Module Type MemT.
  Parameter t : Type.
  Parameter read : t -> arrvar -> Z -> value.
  Parameter write : t  -> arrvar -> Z -> value -> t.
  Parameter undef : t.

  Parameter undefP :
    forall a i,
      read undef a i = Vundef.

  Parameter read_write :
    forall m a i b j v,
      in_bounds a i
      -> read (write m a i v) b j
         = if [&& a == b & i == j ] then v else read m b j.
End MemT.

Module Mem : MemT.
  Record _t :=
    {
      mem_map : arrvar -> Z -> value;
    }.

  Definition t := _t.
  Definition undef : t :=
    {| mem_map := fun _ _ => Vundef; |}.

  Definition read (m : t) (a : arrvar) (i : Z) : value :=
    if in_bounds a i then mem_map m a i else Vundef.

  Definition write (m : t) (a : arrvar) (i : Z) (v : value) : t :=
    if in_bounds a i
    then
      let map' a' i' :=
        if [&& a' == a & i == i' ] then v else mem_map m a' i'
      in
      {| mem_map := map'; |}
    else
      undef.

  Lemma undefP a i : read undef a i = Vundef.
  Proof. by rewrite /read if_same. Qed.

  Lemma read_write m a i b j v :
    in_bounds a i
    -> read (write m a i v) b j
       = if [&& a == b & i == j ] then v else read m b j.
  Proof.
    move=> hi.
    rewrite /write hi /read /= /in_bounds /= -/(in_bounds b j) eq_sym.
    case: andP; last done.
    move=> [/eqP ? /Z.eqb_eq ?]; subst b j.
    by rewrite hi.
  Qed.

End Mem.

Definition is_defined_mem (mem : Mem.t) (a : arrvar) (i : Z) : bool :=
  is_defined (Mem.read mem a i).


(* -------------------------------------------------------------------------- *)
(* States. *)

Record state :=
  {
    s_c : code;
    s_vm : vmap;
    s_mem : Mem.t;
  }.

Definition with_c st c :=
  {|
    s_c := c;
    s_vm := s_vm st;
    s_mem := s_mem st;
  |}.

Definition with_vm st vm :=
  {|
    s_c := s_c st;
    s_vm := vm;
    s_mem := s_mem st;
  |}.

Definition with_mem st mem :=
  {|
    s_c := s_c st;
    s_vm := s_vm st;
    s_mem := mem;
  |}.

(* -------------------------------------------------------------------------- *)
(* Writing. *)

Definition write_reg (st : state) (x : regvar) (v : value) : state :=
  Mr.set (s_vm st) x v |> with_vm st.

Definition write_mem (st : state) (a : arrvar) (i : Z) (v : value) : state :=
  Mem.write (s_mem st) a i v |> with_mem st.


(* -------------------------------------------------------------------------- *)
(* Evaluating expressions. *)

Fixpoint eval_e (vm : vmap) (e : expr) : value :=
  match e with
  | Econst z => Vint z
  | Ebool b => Vbool b
  | Evar x => Mr.get vm x
  | Eop1 Onot e => if eval_e vm e is Vbool b then Vbool (~~ b) else Vundef
  | Eop1 Oneg e => if eval_e vm e is Vint z then Vint (- z)%Z else Vundef
  | Eop2 op e0 e1 =>
      match op, eval_e vm e0, eval_e vm e1 with
      | Oadd, Vint z0, Vint z1 => Vint (z0 + z1)
      | Oeq, Vint z0, Vint z1 => Vbool (z0 == z1)%Z
      | Olt, Vint z0, Vint z1 => Vbool (z0 <? z1)%Z
      | Oeq, Vbool b0, Vbool b1 => Vbool (b0 == b1)
      | Oand, Vbool b0, Vbool b1 => Vbool (b0 && b1)
      | _, _, _ => Vundef
      end
  end.

Fixpoint leaks_e (vm : vmap) (e : expr) : seq value :=
  match e with
  | Econst z => [:: Vint z]
  | Ebool b => [:: Vbool b]
  | Evar x => [:: Mr.get vm x]
  | Eop1 op e =>
      match op, eval_e vm e with
      | Onot, Vbool b => (leaks_e vm e) ++ [:: Vbool (~~ b)]
      | Oneg, Vint z => (leaks_e vm e) ++ [:: Vint (- z)%Z]
      | _, _ => (leaks_e vm e) ++ [:: Vundef]
      end
(*  | Eop1 Onot e => (leaks_e vm e) ++ [:: if eval_e vm e is Vbool b then Vbool (~~ b) else Vundef]
  | Eop1 Oneg e => (leaks_e vm e) ++ [:: if eval_e vm e is Vint z then Vint (- z)%Z else Vundef]*)
  | Eop2 op e0 e1 =>
      match op, eval_e vm e0, eval_e vm e1 with
      | Oadd, Vint z0, Vint z1 => (leaks_e vm e0) ++ (leaks_e vm e1) ++ [:: Vint (z0 + z1)]
      | Oeq, Vint z0, Vint z1 => (leaks_e vm e0) ++ (leaks_e vm e1) ++ [:: Vbool (z0 == z1)%Z]
      | Olt, Vint z0, Vint z1 => (leaks_e vm e0) ++ (leaks_e vm e1) ++ [:: Vbool (z0 <? z1)%Z]
      | Oeq, Vbool b0, Vbool b1 => (leaks_e vm e0) ++ (leaks_e vm e1) ++ [:: Vbool (b0 == b1)]
      | Oand, Vbool b0, Vbool b1 => (leaks_e vm e0) ++ (leaks_e vm e1) ++ [:: Vbool (b0 && b1)]
      | _, _, _ => (leaks_e vm e0) ++ (leaks_e vm e1) ++ [:: Vundef]
      end
  end.

Definition eq_on (s : Sr.t) (vm vm' : vmap) : Prop :=
  forall x, Sr.mem x s -> Mr.get vm x = Mr.get vm' x.

Definition eq_on2 (s s' : seq regvar) (vm vm' : vmap) : Prop :=
  size s = size s' /\
  all (fun '(x, x') => Mr.get vm x == Mr.get vm' x') (zip s s').

Axiom leaks_mop: vmap -> seq regvar (* xs *) -> mop -> seq regvar -> seq value.

Axiom leaks_mop_eq : forall vm vm' dst dst' m op op',
  eq_on2 op op' vm vm'
  -> leaks_mop vm dst m op = leaks_mop vm' dst' m op'.

Definition eval_es (vm : vmap) (es : seq expr) : seq value :=
  map (eval_e vm) es
.


Variant eval_mop (vm : vmap) : mop -> seq regvar -> seq value -> Prop :=
  | eval_mop_neg :
    forall r z,
    Vint z = Mr.get vm r
    -> eval_mop vm Mneg [:: r] [:: Vint (- z)%Z]

  | eval_mop_not :
    forall r b,
    Vbool b = Mr.get vm r
    -> eval_mop vm Mnot [:: r] [:: Vbool (~~ b)]

  | eval_mop_add :
    forall rn rm zn zm,
      Vint zn = Mr.get vm rn
      -> Vint zm = Mr.get vm rm
      -> eval_mop vm Madd [:: rn; rm] [:: Vint (zn + zm)]

  | eval_mop_and :
    forall rn rm zn zm,
      Vbool zn = Mr.get vm rn
      -> Vbool zm = Mr.get vm rm
      -> eval_mop vm Mand [:: rn; rm] [:: Vbool (zn && zm)]

  | eval_mop_cmp :
    forall rn rm zn zm,
      Vint zn = Mr.get vm rn
      -> Vint zm = Mr.get vm rm
      -> eval_mop vm Mcmp [:: rn; rm] [:: Vbool (zn == zm)%Z; Vbool (zn <? zm)%Z]
.

Definition eval_mop' (vm : vmap) (op : mop) (rs : seq regvar): option (seq value) :=
  match op with
  (* eval_mop_neg *)
  | Mneg =>
      match rs with
      | [:: r] =>
          match Mr.get vm r with
          | Vbool _ | Vundef => None
          | Vint z =>
              Some [:: Vint (- z)%Z]
          end
      | _ => None
      end
  (* eval_mop_not *)
  | Mnot =>
      match rs with
      | [:: r] =>
          match Mr.get vm r with
          | Vint _ | Vundef => None
          | Vbool b => Some [:: Vbool (~~ b)]
          end
      | _ => None
      end
  (* eval_mop_add *)
  | Madd =>
      match rs with
      | [:: rn; rm] =>
          match (Mr.get vm rn, Mr.get vm rm) with
          | (Vint zn, Vint zm) => Some [:: Vint (zn + zm)]
          | _ => None
          end
      | _ => None
      end
  (* eval_mop_and *)
  | Mand =>
      match rs with
      | [:: rn; rm] =>
          match (Mr.get vm rn, Mr.get vm rm) with
          | (Vbool bn, Vbool bm) => Some [:: Vbool (bn && bm)]
          | _ => None
          end
      | _ => None
      end
  (* eval_mop_cmp *)
  | Mcmp =>
      match rs with
      | [:: rn; rm] =>
          match (Mr.get vm rn, Mr.get vm rm) with
          | (Vint zn, Vint zm) => Some [:: Vbool (zn == zm)%Z; Vbool (zn <? zm)%Z]
          | _ => None
          end
      | _ => None
      end
  end.

Lemma eval_mopE (vm : vmap) (op : mop) (rs : seq regvar) (vs : seq value):
  eval_mop vm op rs vs <-> eval_mop' vm op rs = Some vs.
Proof.
  split. {
    move => H; rewrite /eval_mop'.
    by inversion H; subst; try rewrite -H0; try rewrite -H1.
  }
  rewrite /eval_mop'.
  case op; case rs => // s l; case l => //.
  + destruct (Mr.get vm s) eqn:H => // [] [] <-.
    by apply eval_mop_neg.
  + destruct (Mr.get vm s) eqn:H => // [] [] <-.
    by apply eval_mop_not.
  + move => s' l'; destruct l' => //.
    destruct (Mr.get vm s) eqn:H => //; destruct (Mr.get vm s') eqn:H' => // => [] [] <-.
    by apply eval_mop_add.
  + move => s' l'; destruct l' => //.
    destruct (Mr.get vm s) eqn:H => //; destruct (Mr.get vm s') eqn:H' => // => [] [] <-.
    by apply eval_mop_and.
  + move => s' l'; destruct l' => //.
    destruct (Mr.get vm s) eqn:H => //; destruct (Mr.get vm s') eqn:H' => // => [] [] <-.
    by apply eval_mop_cmp.
Qed.
(* -------------------------------------------------------------------------- *)
(* Small step semantics. *)

(* Check fun (a b : arrvar) => a == b. *)

(* cache-timing side-channel observations *)
Variant t_obs :=
  | OTnone
  | OTaddr of arrvar & Z
  | OTbranch of bool.

Definition t_obs_eq (a b : t_obs) : bool :=
  match a, b with
    | OTnone, OTnone => true
    | OTaddr xa ia, OTaddr xb ib => [&& xa == xb & ia == ib]
    | OTbranch ba, OTbranch bb => ba == bb
    | _, _ => false
  end.

Lemma t_obs_eq_axiom : Equality.axiom t_obs_eq.
Proof.
  case => [ | a i | b ] [ | a' i' | b' ].
  1: by left.
  1-3, 5-7: by right.
  all: rewrite /=; case: eqP => [ -> /= | ne ].
  3: by left.
  case: eqP => [ -> /= | ne' ]; first by left.
  all: right; congruence.
Qed.

Definition t_obs_eqMixin := Equality.Mixin t_obs_eq_axiom.
Canonical t_obs_eqType := EqType t_obs t_obs_eqMixin.

(* power side-channel observation according to value leakage model *)
Variant v_obs :=
  | OVval of seq value.

Definition v_obs_eq (a b : v_obs) : bool :=
  let 'OVval osa := a in
  let 'OVval osb := b in
  osa == osb.

Lemma v_obs_eq_axiom : Equality.axiom v_obs_eq.
Proof.
  case => osa [] osb /=.
  by case: eqP => [ -> | ne ]; [ left | right; congruence ].
Qed.

Definition v_obs_eqMixin := Equality.Mixin v_obs_eq_axiom.
Canonical v_obs_eqType := EqType v_obs v_obs_eqMixin.

Definition s_after_assign s c x e :=
  let v := eval_e (s_vm s) e in
  let s' := write_reg s x v in
  with_c s' c.

Definition s_after_regwrites s c xsvs :=
  let s' := foldr (fun p s => write_reg s p.1 p.2) s xsvs in
  with_c s' c.

Definition s_after_load s c x a i :=
  let v := Mem.read (s_mem s) a i in
  let s' := write_reg s x v in
  with_c s' c.

Definition s_after_store s c a i x :=
  let v := Mr.get (s_vm s) x in
  let s' := write_mem s a i v in
  with_c s' c.

Section WITH_PROG.

Variant step :
  state -> t_obs -> v_obs -> state -> Prop :=
  | step_assign :
    forall s ii x e c,
      s_c s = {| annot := ii; unannot := Iassign x e; |} :: c
      -> step s OTnone (OVval (leaks_e (s_vm s) e)) (s_after_assign s c x e)

  | step_load :
    forall s s' ii x a e c i v,
      s_c s = {| annot := ii; unannot := Iload x a e; |} :: c
      -> eval_e (s_vm s) e = Vint i
      -> in_bounds a i
      -> is_defined_mem (s_mem s) a i
      -> s' = s_after_load s c x a i
      -> v = Mem.read (s_mem s) a i
      -> step s (OTaddr a i) (OVval ((leaks_e (s_vm s) e) ++ [:: v])) s'

  | step_store :
    forall s s' ii a e x c i v,
      s_c s = {| annot := ii; unannot := Istore a e x; |} :: c
      -> eval_e (s_vm s) e = Vint i
      -> in_bounds a i
      -> is_defined (Mr.get (s_vm s) x)
      -> s' = s_after_store s c a i x
      -> v = Mr.get (s_vm s) x
      -> step s (OTaddr a i) (OVval ((leaks_e (s_vm s) e)  ++ [:: v])) s'

  | step_mop :
    forall s s' ii xs mop os c vs,
      s_c s = {| annot := ii; unannot := Imop xs mop os; |} :: c
      -> eval_mop (s_vm s) mop os vs
      -> length xs = length vs
      -> s' = s_after_regwrites s c (zip xs vs)
      -> step s OTnone (OVval (leaks_mop (s_vm s) xs mop os)) s'

  | step_if :
    forall s s' ii e c1 c0 c b,
      s_c s = {| annot := ii; unannot := Iif e c1 c0; |} :: c
      -> eval_e (s_vm s) e = Vbool b
      -> s' = with_c s ((if b then c1 else c0) ++ c)
      -> step s (OTbranch b) (OVval (leaks_e (s_vm s) e)) s'

  | step_while :
    forall s s' ii e cw c b,
      s_c s = {| annot := ii; unannot := Iwhile e cw; |} :: c
      -> eval_e (s_vm s) e = Vbool b
      -> s' = with_c s (if b then cw ++ (s_c s) else c)
      -> step s (OTbranch b) (OVval (leaks_e (s_vm s) e)) s'
.

Definition exec_step (s : state) : option (t_obs * v_obs * state) :=
  match s_c s with
  | [::] => None
  (* step_assign *)
  | {| annot := ii; unannot := Iassign x e; |} :: c =>
      Some (OTnone, OVval (leaks_e (s_vm s) e), s_after_assign s c x e)
  (* step_load *)
  | {| annot := ii; unannot := Iload x a e; |} :: c =>
      match eval_e (s_vm s) e with
      | Vbool _ | Vundef => None
      | Vint i =>
          if [&& in_bounds a i & is_defined_mem (s_mem s) a i] then
            let v := Mem.read (s_mem s) a i in
            Some (OTaddr a i, OVval ((leaks_e (s_vm s) e) ++ [:: v]), s_after_load s c x a i)
          else
            None
      end
  (* step_store *)
  | {| annot := ii; unannot := Istore a e x; |} :: c =>
      match eval_e (s_vm s) e with
      | Vbool _ | Vundef => None
      | Vint i =>
          if [&& in_bounds a i & is_defined (Mr.get (s_vm s) x)] then
            let v := Mr.get (s_vm s) x in
            Some (OTaddr a i, OVval ((leaks_e (s_vm s) e) ++ [:: v]), s_after_store s c a i x)
          else
            None
      end
  (* step_mop *)
  | {| annot := ii; unannot := Imop xs mop os; |} :: c =>
      match eval_mop' (s_vm s) mop os with
      | None => None
      | Some vs =>
          if (length xs =? length vs)%nat then
            Some (OTnone, OVval (leaks_mop (s_vm s) xs mop os), s_after_regwrites s c (zip xs vs))
          else
            None
      end
  (* step_if *)
  | {| annot := ii; unannot := Iif e c1 c0; |} :: c =>
      match eval_e (s_vm s) e with
      | Vint _ | Vundef => None
      | Vbool b =>
          Some (OTbranch b, OVval (leaks_e (s_vm s) e), with_c s ((if b then c1 else c0) ++ c))
      end
  (* step_while *)
  | {| annot := ii; unannot := Iwhile e cw; |} :: c =>
      match eval_e (s_vm s) e with
      | Vint _ | Vundef => None
      | Vbool b =>
          Some (OTbranch b, OVval (leaks_e (s_vm s) e), with_c s (if b then cw ++ (s_c s) else c))
      end
  end.

Lemma exec_stepE (s: state) (ot: t_obs) (ov: v_obs) (s': state):
    step s ot ov s' <-> exec_step s = Some (ot, ov, s').
Proof.
  split. {
    move => H; rewrite /exec_step.
    destruct H; rewrite H; (try rewrite H0; try rewrite H1; try rewrite H2; try rewrite H3; try rewrite H4) => /= //.
    + by move /eval_mopE: H0 => ->; rewrite Nat.eqb_refl.
    by rewrite H.
  }
  rewrite /exec_step.
  case_eq (s_c s); first discriminate.
  move => i c H.
  case_eq i => annot ii hi.
  case_eq ii.
  + move => r e hii [] *.
    subst.
    by apply (step_assign H).
  + move => r r' e hii.
    destruct (eval_e (s_vm s) e) as [i'| |] eqn:Hev => //.
    case H': (in_bounds r' i' && is_defined_mem (s_mem s) r' i') => //.
    move/andP : H' => [] H1 H2 [] <- <- <-.
    rewrite hi hii in H.
    by apply (step_load H Hev H1 H2).
  + move => r r' e hii.
    destruct (eval_e (s_vm s) r') as [i'| |] eqn:Hev => //.
    case H': (in_bounds r i' && is_defined (Mr.get (s_vm s) e)) => //.
    move/andP : H' => [] H1 H2 [] <- <- <-.
    rewrite hi hii in H.
    by apply (step_store H Hev H1 H2).
  + move => l m l' hii.
    destruct (eval_mop' (s_vm s) m l') as [vs|] eqn:Hev => //.
    case H': (length l =? length vs)%N => //.
    move/eqP: H' => H1 [] <- <- <-.
    rewrite hi hii in H.
    apply eval_mopE in Hev.
    by apply (step_mop H Hev H1).
  + move => e cT cF hii.
    destruct (eval_e (s_vm s) e) as [b| |] eqn:Hev => //.
    move => [] <- <- <-.
    rewrite hi hii in H.
    by apply (step_if H Hev).
  + move => e cW hii.
    destruct (eval_e (s_vm s) e) as [b| |] eqn:Hev => //.
    move => [] <- <- <-.
    rewrite hi hii in H.
    eapply (step_while H Hev).
    by rewrite H.
Qed.

Definition exec_step_pc (c : code) (ots : t_obs): option code :=
  match c with
  | [::] => None
  (* step_assign *)
  | {| annot := ii; unannot := Iassign x e; |} :: c' => Some c'
  (* step_load *)
  | {| annot := ii; unannot := Iload x a e; |} :: c' => Some c'
  (* step_store *)
  | {| annot := ii; unannot := Istore a e x; |} :: c' => Some c'
  (* step_mop *)
  | {| annot := ii; unannot := Imop xs mop os; |} :: c' => Some c'
  (* step_if *)
  | {| annot := ii; unannot := Iif e c1 c0; |} :: c' =>
      match ots with
      | OTbranch b => Some ((if b then c1 else c0) ++ c')
      | _ => None
      end
  (* step_while *)
  | {| annot := ii; unannot := Iwhile e cw; |} :: c' =>
      match ots with
      | OTbranch b => Some (if b then cw ++ c else c')
      | _ => None
      end
  end.

Definition step_pc (c : code) (ot: t_obs) (c' : code) := exec_step_pc c ot = Some c'.

Lemma exec_step_pcE (c: code) (ot: t_obs) (c': code):
  step_pc c ot c' <-> exec_step_pc c ot = Some c'.
Proof.
  by rewrite /step_pc.
Qed.

Lemma step_pcE s ot ov s': step s ot ov s' -> step_pc (s_c s) ot (s_c s').
Proof.
  move => H.
  rewrite /step_pc /exec_step_pc.
  by inversion H; subst; rewrite H0.
Qed.

End WITH_PROG.

Definition final (s : state) : bool := nilp (s_c s).

Definition safe_step (s : state) := [\/ final s | exists s' ot ov, step s ot ov s'].

Section LANGUAGE_FACTS.

Lemma deterministic_eval_mops s mop0 os vs1 vs2 :
  eval_mop (s_vm s) mop0 os vs1 ->
  eval_mop (s_vm s) mop0 os vs2 ->
  vs1 = vs2.
Proof.
  intros H.
  dependent destruction H; intro K; dependent destruction K;
    try (rewrite <- H in H0; inversion H0; subst; auto);
    try (rewrite <- H in H1;
         inversion H1; subst;
         rewrite <- H0 in H2;
         inversion H2; subst; auto).
Qed.

Lemma step_deterministic s s1 s2 ot1 ot2 ov1 ov2 :
  step s ot1 ov1 s1 ->
  step s ot2 ov2 s2 ->
  [/\ ot1 = ot2, ov1 = ov2 & s1 = s2].
Proof.
  intros H H0.
  destruct H; destruct H0; simpl in *; subst; split;
    try congruence;
    try (rewrite H in H0; inversion H0; subst; auto);
    try (rewrite H1 in H6; inversion H6; subst; auto);
    try (rewrite H1 in H3; inversion H3; subst; auto);
    try (eapply deterministic_eval_mops in H1; eauto; subst; auto).
Qed.

Lemma step_final s ot ov s': step s ot ov s' -> ~final s.
Proof.
  rewrite /final /nilp => Hstep.
  by case: Hstep => s0; set (c := s_c s0) in *; clearbody c; intros; subst c.
Qed.

Lemma finsc s:
  final s ->
  s_c s = [::].
Proof.
  rewrite /final /final /nilp.
  move/eqP.
  apply size0nil.
Qed.

End LANGUAGE_FACTS.

(* -------------------------------------------------------------------------- *)

Require language.

Section INSTANCE.

Definition input : Type := seq value.
Definition output : Type := seq value.

Definition vmap_empty : vmap := Mr.const Vundef.

Definition initial_state (c : code) (xs : seq regvar) (inp : input) : state :=
  {|
    s_c := c;
    s_vm := foldr (fun '(x, v) vm => Mr.set vm x v) vmap_empty (zip xs inp);
    s_mem := Mem.undef;
  |}.

Definition _initial_state (p : prog) (inp : input) : state :=
  initial_state (p_prog p) (p_inputs p) inp.

Definition outputs_of_state (p : prog) (s : state) (_ : final s) : output :=
  map (Mr.get (s_vm s)) (p_outputs p)
.

Lemma s_c_code (p : prog) (inp : input):
  s_c (_initial_state p inp) = p_prog p.
Proof.
  done.
Qed.

Lemma s_c_same_step s1 s2 ot ov ov' s1' s2':
  step s1 ot ov s1' -> step s2 ot ov' s2' -> s_c s1 = s_c s2 -> s_c s1' = s_c s2'.
Proof.
  move => H1 H2 Heq.
  inversion H1; inversion H2; subst; simpl in * => //; try congruence;
  inversion H12; case b; congruence.
Qed.

#[local]
Instance Source : language.Language input output :=
  {|
    language.state := state;
    language.initial_state := _initial_state;
    language.step := step;
    language.final := final;
    language.safe_step := safe_step;
    language.step_deterministic := step_deterministic;
    language.step_final := step_final;
    language.outputs := outputs_of_state;
    language.exec_step := exec_step;
    language.exec_stepE := exec_stepE;
    language.t_dummy_observation := OTnone;
    language.v_dummy_observation := OVval [::];
    language.prog_pc := code;
    language.get_pc := s_c;
    language.pc_init := s_c_code;
    language.pc_same_step := s_c_same_step;
    language.step_pcE := step_pcE;
    language.exec_step_pc := exec_step_pc;
    language.exec_step_pcE := exec_step_pcE;
  |}.

Lemma finpc s:
  language.final s ->
  language.get_pc s = [::].
Proof.
  rewrite /language.final /language.get_pc /Source /semantics.final /nilp.
  move/eqP.
  apply size0nil.
Qed.

End INSTANCE.
