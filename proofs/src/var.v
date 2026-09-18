From Coq Require Import
  Structures.Equalities
  ZArith
.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import utils Fsets.
Export Fsets.

Open Scope Z.

(* -------------------------------------------------------------------------- *)
(* Variables. *)
(* -------------------------------------------------------------------------- *)

Module Type VarT := CmpType.

Module DefaultVar : VarT.
  Definition t : eqType := nat_eqType.
  Definition cmp := Nat.compare.

  Definition cmpO : Cmp cmp.
  Proof.
    rewrite /cmp; constructor.
    + by move=> *; rewrite Nat.compare_antisym.
    + move=> y x z.
      case: (Nat.compare_spec x y).
      + by move=> -> ? /ctrans_Eq.
      + move=> hxy c; rewrite /ctrans; case: (Nat.compare_spec y z) => //=.
        + by move=> <- [<-]; apply/nat_compare_lt.
        by move=> hyz [<-]; apply/nat_compare_lt; apply: Nat.lt_trans hxy hyz.
      move=> hxy c; rewrite /ctrans; case: (Nat.compare_spec y z) => //=.
      + by move=> <- [<-]; rewrite Nat.compare_antisym CompOpp_iff; apply/nat_compare_lt.
      move=> hyz [<-]; rewrite Nat.compare_antisym CompOpp_iff.
      apply/nat_compare_lt; apply: Nat.lt_trans hyz hxy.
    by apply Nat.compare_eq.
  Qed.

End DefaultVar.

Module RegisterVar : VarT := DefaultVar.
Definition regvar := RegisterVar.t.

Module SrExtra := SExtra(RegisterVar).
Module Sr := SrExtra.Sv.
Module SrP := SrExtra.SvP.
Module SrD := SrExtra.SvD.

Module Mr := MMake(RegisterVar).
#[global] Opaque Mr.get.
#[global] Opaque Mr.set.
#[global] Opaque Mr.map.

Module PMr := PMMake(RegisterVar).

Module Type ArrT.
  Parameter t : eqType.
  Parameter len : t -> Z.
  Parameter cmp : t -> t -> comparison.
  Parameter cmpO : Cmp cmp.
End ArrT.

Module ArrayVar : ArrT.
  Definition t := [eqType of DefaultVar.t * Z].
  Definition len (a : t) := a.2.
  Definition cmp (x y : t) := lex DefaultVar.cmp Z.compare x y.
  Definition cmpO : Cmp cmp := LexO DefaultVar.cmpO ZO.
End ArrayVar.

Definition arrvar := ArrayVar.t.
Definition arrlen := ArrayVar.len.

Module SaExtra := SExtra(ArrayVar).
Module Sa := SaExtra.Sv.
Module SaP := SaExtra.SvP.
Module SaD := SaExtra.SvD.

Module Ma := MMake(ArrayVar).
#[global] Opaque Ma.get.
#[global] Opaque Ma.set.
#[global] Opaque Ma.map.

Module PMa := PMMake(ArrayVar).

Module InstrInfo : VarT := DefaultVar.
Definition iinfo := InstrInfo.t.

Record annotated (T : Type) : Type :=
  {
    annot : iinfo;
    unannot : T;
  }.

Definition mk_annotated {T : Type} (ii : iinfo) (x : T) : annotated T :=
  {| annot := ii; unannot := x; |}.

Definition with_annot
  {T : Type} (a : annotated T) (ii : iinfo) : annotated T :=
  {| annot := ii; unannot := unannot a; |}.

Definition with_unannot
  {T T' : Type} (a : annotated T) (x : T') : annotated T' :=
  {| annot := annot a; unannot := x; |}.

Module Label : VarT := DefaultVar.
Definition label := Label.t.
