(* -------------------------------------------------------------------------- *)
(* Source syntax. *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  var
  utils
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.


(* -------------------------------------------------------------------------- *)
(* Expressions. *)

Variant op1 :=
  | Onot
  | Oneg
.

Scheme Equality for op1.

Lemma op1_eq_axiom : Equality.axiom op1_beq.
Proof. exact: (eq_axiom_of_scheme internal_op1_dec_bl internal_op1_dec_lb). Qed.

Definition op1_eqMixin := Equality.Mixin op1_eq_axiom.
Canonical op1_eqType := Eval hnf in EqType op1 op1_eqMixin.

Variant op2 :=
  | Oadd
  | Oeq
  | Oand
  | Olt
.

Scheme Equality for op2.

Lemma op2_eq_axiom : Equality.axiom op2_beq.
Proof. exact: (eq_axiom_of_scheme internal_op2_dec_bl internal_op2_dec_lb). Qed.

Definition op2_eqMixin := Equality.Mixin op2_eq_axiom.
Canonical op2_eqType := Eval hnf in EqType op2 op2_eqMixin.

Inductive expr :=
  | Econst of Z
  | Ebool of bool
  | Evar of regvar
  | Eop1 of op1 & expr
  | Eop2 of op2 & expr & expr
.

Fixpoint expr_beq (e1 e2 : expr) : bool :=
  match e1, e2 with
  | Econst z1, Econst z2 => z1 == z2
  | Ebool b1, Ebool b2 => b1 == b2
  | Evar v1, Evar v2 => v1 == v2
  | Eop1 o1 e1, Eop1 o2 e2 =>
      (o1 == o2) && expr_beq e1 e2
  | Eop2 o1 e11 e12, Eop2 o2 e21 e22 =>
      (o1 == o2) && expr_beq e11 e21 && expr_beq e12 e22
  | _, _ => false
  end.

(* TODO: fails due to regvar
Scheme Equality for expr.

Lemma expr_eq_axiom : Equality.axiom expr_beq.
Proof. exact: (eq_axiom_of_scheme internal_expr_dec_bl internal_expr_dec_lb). Qed.

Definition expr_eqMixin := Equality.Mixin expr_eq_axiom.
Canonical expr_eqType := Eval hnf in EqType expr expr_eqMixin.
 *)

Lemma expr_eq e e':
  expr_beq e e' <-> e = e'.
Proof.
  split. {
    elim: e e' => [z|b|v|o e IHe|o e1 IHe1 e2 IHe2] e' /=.
    all: destruct e'; try by[].
    1-3: by move/eqP => ->.
    + move/andP => [] /eqP => ->.
      move=> H.
      by rewrite (IHe _ H).
    + move/andP => [] /andP [] /eqP ->.
      move=> He1 He2.
      rewrite (IHe1 _ He1).
      by rewrite (IHe2 _ He2).
  } {
    move=> ->.
    elim e' => [|||o ei IH|o ei1 IHei1 ei2 IHei2] //=.
    + by rewrite eqxx IH /=.
    + by rewrite eqxx IHei1 IHei2 /=.
  }
Qed.

Lemma expr_beqS e e':
  expr_beq e e' <-> expr_beq e' e.
Proof.
  rewrite !expr_eq.
  split; by symmetry.
Qed.

Lemma expr_beqR e :
  expr_beq e e = true.
Proof. apply /expr_eq. reflexivity. Qed.

Fixpoint subexpr (sub e : expr) :=
  match e with
  | Econst _
  | Ebool _
  | Evar _ => expr_beq e sub
  | Eop1 _ e' => expr_beq e sub || subexpr sub e'
  | Eop2 _ e1 e2 => expr_beq e sub ||  subexpr sub e1 || subexpr sub e2
  end.

Lemma subexprR e:
  subexpr e e.
Proof.
  elim: e => [z|b|v|o e IHe|o e1 IHe1 e2 IHe2] //=; rewrite eqxx /=.
  + apply/orP; left.
    by apply/expr_eq.
  + apply/orP; left. apply/orP; left.
    apply/andP; split; apply/expr_eq; by [].
Qed.

Fixpoint expr_size (e : expr) : nat :=
  match e with
  | Econst _ => 1
  | Ebool _ => 1
  | Evar _ => 1
  | Eop1 _ e' => (expr_size e').+1
  | Eop2 _ e1 e2 => (expr_size e1 + expr_size e2).+1
  end.

Lemma expr_size_pos e : (0 < expr_size e)%N.
Proof. by elim: e. Qed.

Lemma expr_beq_size e1 e2 :
  expr_beq e1 e2 -> expr_size e1 = expr_size e2.
Proof.
  move/expr_eq => ->. done.
Qed.

Lemma subexpr_size sub e :
  subexpr sub e -> (expr_size sub <= expr_size e)%N.
Proof.
  elim: e => [z|b|v|o' e' IH|o' e1 IH1 e2 IH2] /=.
  1-3: destruct sub => //.
  { move/orP => []. destruct sub => //. move/andP => [] /eqP ? /expr_eq ?; by subst.
    move/IH.
    apply leqW.
  } {
    move/orP => []. move/orP => [].
    + destruct sub => //. by move/andP => [] /andP [] /eqP ? /expr_eq ? /expr_eq ?; subst.
    + intro H. apply leqW. apply (leq_trans (IH1 H)). apply leq_addr.
    + intro H. apply leqW. apply (leq_trans (IH2 H)). apply leq_addl.
  }
Qed.

Lemma subexpr_of_child_op1 o e :
  subexpr (Eop1 o e) e = false.
Proof.
  apply/negP => /subexpr_size.
  rewrite /= ltnNge => /negP. apply.
  done.
Qed.

Fixpoint substitute (sub rep e: expr) :=
  if expr_beq e sub then
    rep
  else
    match e with
    | Econst _
    | Ebool _
    | Evar _ => e
    | Eop1 o e => Eop1 o (substitute sub rep e)
    | Eop2 o e1 e2 => Eop2 o (substitute sub rep e1) (substitute sub rep e2)
    end.

Definition enot (e : expr) : expr := Eop1 Onot e.
Definition eaddi (e : expr) (i : Z) : expr := Eop2 Oadd e (Econst i).

Fixpoint free_variables (e : expr) : Sr.t :=
  match e with
  | Econst _ => Sr.empty
  | Ebool _ => Sr.empty
  | Evar x => Sr.singleton x
  | Eop1 _ e => free_variables e
  | Eop2 _ e0 e1 => Sr.union (free_variables e0) (free_variables e1)
  end.

(* Machine operations *)
Inductive mop :=
  | Mneg (* rd = #NEG(rn) *)
  | Mnot (* rd = #NOT(rn) *)
  | Madd (* rd = #ADD(rn, rm) *)
  | Mand (* rd = #AND(rn, rm) *)
  | Mcmp (* (req, rlt) = #CMP(rn, rm) *)
  .

(* -------------------------------------------------------------------------- *)
(* Instructions. *)
Inductive instr :=
  | Iassign of regvar & expr
  | Iload of regvar & arrvar & expr
  | Istore of arrvar & expr & regvar
  | Imop of seq regvar (* destination *) & mop & seq regvar (* operands *) (* machine op instruction, e.g., rd = #XOR(rn, rm) *)
  | Iif of expr & (seq (annotated instr)) & (seq (annotated instr))
  | Iwhile of expr & (seq (annotated instr))
.

Notation instr_i := (annotated instr)%type.
Notation code := (seq instr_i).

Definition map_instr (f : instr -> instr) (i : instr_i) : instr_i :=
  {| annot := annot i; unannot := f (unannot i); |}.


(* -------------------------------------------------------------------------- *)
(* Programs. *)

Record prog :=
  {
    p_prog : code;
    p_inputs : seq regvar;
    p_outputs : seq regvar;
  }.

Definition with_p_prog (p : prog) (c : code) : prog :=
  {|
    p_prog := c;
    p_inputs := p_inputs p;
    p_outputs := p_outputs p;
  |}.

Definition map_p_prog (f : code -> code) (p : prog) : prog :=
  with_p_prog p (p_prog p |> f).

(* -------------------------------------------------------------------------- *)
(* Equality. *)

Context
  (instr_beq : instr -> instr -> bool)
  (instr_eq_axiom : Equality.axiom instr_beq)
.

Definition instr_eqMixin := Equality.Mixin instr_eq_axiom.
Canonical instr_eqType :=
  Eval hnf in EqType instr instr_eqMixin.

Section IND.

Context (Pi : instr -> Prop) (Pii : annotated instr -> Prop) (Pc : code -> Prop).

Context (Hassign : forall x e, Pi (Iassign x e))
        (Hload : forall x a e, Pi (Iload x a e))
        (Hstore : forall a e x, Pi (Istore a e x))
        (Hmop : forall xs o es, Pi (Imop xs o es))
        (Hif : forall e c1 c0, Pc c1 -> Pc c0 -> Pi (Iif e c1 c0))
        (Hwhile : forall e c1, Pc c1 -> Pi (Iwhile e c1))
        (Hnil : Pc [::])
        (Hcons : forall i c, Pii i -> Pc c -> Pc (i::c))
        (Hannot : forall i a, Pi i -> Pii {|annot := a; unannot := i |}).

Section CODE.

Context (ind_i : forall i, Pi i).

Fixpoint ind_c_aux (c : code) : Pc c :=
  match c return Pc c with
  | [::] => Hnil
  | {|annot := a; unannot := i |} :: c =>
    Hcons (Hannot a (ind_i i)) (ind_c_aux c)
  end.

End CODE.

Fixpoint ind_i (i : instr) : Pi i :=
  match i return Pi i with
  | Iassign x e => Hassign x e
  | Iload x a e => Hload x a e
  | Istore a e x => Hstore a e x
  | Imop xs o es => Hmop xs o es
  | Iif e c1 c0 =>
     Hif e (ind_c_aux ind_i c1) (ind_c_aux ind_i c0)
  | Iwhile e c1 =>
     Hwhile e (ind_c_aux ind_i c1)
  end.

Definition ind_c := ind_c_aux ind_i.

End IND.

