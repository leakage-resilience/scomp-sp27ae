From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "x |> f" := (f x) (only parsing, at level 25).

Definition Z_eqMixin := EqMixin Z.eqb_spec.
Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.

Definition relation A := A -> A -> Prop.

Notation "'let%opt' x ':=' ox 'in' body" :=
  (obind (fun x => body) ox)
  (x strict pattern, at level 25).
Notation "'let%opt '_' ':=' ox 'in' body" :=
  (obind (fun 'tt => body) ox)
  (at level 25).

Definition oassert (b : bool) : option unit :=
  if b then Some tt else None.

Lemma eq_axiom_of_scheme X (beq : X -> X -> bool) :
  (forall x y : X, beq x y -> x = y) ->
  (forall x y : X, x = y -> beq x y) ->
  Equality.axiom beq.
Proof. move=> hbl hlb x y. apply: (iffP idP); first exact: hbl. exact: hlb. Qed.

Definition incl (X : eqType) (xs ys : seq X) : bool :=
  all (fun x => x \in ys) xs.

Definition flat_map (X Y : Type) (f : X -> seq Y) (xs : seq X) : seq Y :=
  flatten (map f xs).

Notation Lex u v :=
  match u with
  | Lt => Lt
  | Eq => v
  | Gt => Gt
  end.

(* -------------------------------------------------------------------- *)

Scheme Equality for comparison.

Lemma comparison_beqP : Equality.axiom comparison_beq.
Proof.
  exact:
    (eq_axiom_of_scheme internal_comparison_dec_bl internal_comparison_dec_lb).
Qed.

Canonical comparison_eqMixin := EqMixin comparison_beqP.
Canonical comparison_eqType := Eval hnf in EqType comparison comparison_eqMixin.

Section CTRANS.

  Definition ctrans c1 c2 := nosimpl (
    match c1, c2 with
    | Eq, _  => Some c2
    | _ , Eq => Some c1
    | Lt, Lt => Some Lt
    | Gt, Gt => Some Gt
    | _ , _  => None
    end).

  Lemma ctransI c : ctrans c c = Some c.
  Proof. by case: c. Qed.

  Lemma ctransC c1 c2 : ctrans c1 c2 = ctrans c2 c1.
  Proof. by case: c1 c2 => -[]. Qed.

  Lemma ctrans_Eq c1 c2 : ctrans Eq c1 = Some c2 <-> c1 = c2.
  Proof. by rewrite /ctrans;case:c1=> //=;split=>[[]|->]. Qed.

  Lemma ctrans_Lt c1 c2 : ctrans Lt c1 = Some c2 -> Lt = c2.
  Proof. by rewrite /ctrans;case:c1=> //= -[] <-. Qed.

  Lemma ctrans_Gt c1 c2 : ctrans Gt c1 = Some c2 -> Gt = c2.
  Proof. by rewrite /ctrans;case:c1=> //= -[] <-. Qed.

End CTRANS.

Class Cmp {T:Type} (cmp:T -> T -> comparison) := {
    cmp_sym    : forall x y, cmp x y = CompOpp (cmp y x);
    cmp_ctrans : forall y x z c, ctrans (cmp x y) (cmp y z) = Some c -> cmp x z = c;
    cmp_eq     : forall {x y}, cmp x y = Eq -> x = y;
  }.


Section LEX.

  Variables (T1 T2:Type) (cmp1:T1 -> T1 -> comparison) (cmp2:T2 -> T2 -> comparison).

  Definition lex x y := Lex (cmp1 x.1 y.1) (cmp2 x.2 y.2).

  Lemma Lex_lex x1 x2 y1 y2 : Lex (cmp1 x1 y1) (cmp2 x2 y2) = lex (x1,x2) (y1,y2).
  Proof. done. Qed.

  Lemma lex_sym x y :
    cmp1 x.1 y.1 = CompOpp (cmp1 y.1 x.1) ->
    cmp2 x.2 y.2 = CompOpp (cmp2 y.2 x.2) ->
    lex  x y = CompOpp (lex  y x).
  Proof.
    by move=> H1 H2;rewrite /lex H1;case: cmp1=> //=;apply H2.
  Qed.

  Lemma lex_trans y x z:
    (forall c, ctrans (cmp1 x.1 y.1) (cmp1 y.1 z.1) = Some c -> cmp1 x.1 z.1 = c) ->
    (forall c, ctrans (cmp2 x.2 y.2) (cmp2 y.2 z.2) = Some c -> cmp2 x.2 z.2 = c) ->
    forall  c, ctrans (lex x y) (lex y z) = Some c -> lex x z = c.
  Proof.
    rewrite /lex=> Hr1 Hr2 c;case: cmp1 Hr1.
    + move=> H;rewrite (H (cmp1 y.1 z.1));last by rewrite ctrans_Eq.
      (case: cmp1;first by apply Hr2);
        rewrite ctransC; [apply ctrans_Lt | apply ctrans_Gt].
    + move=> H1 H2;rewrite (H1 Lt);move:H2;first by apply: ctrans_Lt.
      by case: cmp1.
    move=> H1 H2;rewrite (H1 Gt);move:H2;first by apply: ctrans_Gt.
    by case: cmp1.
  Qed.

  Lemma lex_eq x y :
    lex x y = Eq -> cmp1 x.1 y.1 = Eq /\ cmp2 x.2 y.2 = Eq.
  Proof.
    case: x y => [x1 x2] [y1 y2] /=.
    by rewrite /lex;case:cmp1 => //;case:cmp2.
  Qed.

  Lemma LexO (C1:Cmp cmp1) (C2:Cmp cmp2) : Cmp lex.
  Proof.
    constructor=> [x y | y x z | x y].
    + by apply /lex_sym;apply /cmp_sym.
    + by apply /lex_trans;apply /cmp_ctrans.
    by case: x y => ?? [??] /lex_eq /= [] /(@cmp_eq _ _ C1) -> /(@cmp_eq _ _ C2) ->.
  Qed.

End LEX.

#[global]
Instance ZO : Cmp Z.compare.
Proof.
  constructor.
  + by move=> ??;rewrite Z.compare_antisym.
  + move=> ????;case:Z.compare_spec=> [->|H1|H1];
    case:Z.compare_spec=> H2 //= -[] <- //;subst;
    rewrite ?Z.compare_lt_iff ?Z.compare_gt_iff //.
    + by apply: Z.lt_trans H1 H2.
    by apply: Z.lt_trans H2 H1.
  apply Z.compare_eq.
Qed.

(* Find an element of a lattice whose image is greater.
   Return the element and its image. *)
Section FIND_LOOP.

Context
  (X extra : Type)
  (le : X -> X -> bool)
  (meet : X -> X -> X)
  (get : X -> option (X * extra))
.

Fixpoint find_loop_aux (fuel : nat) (x : X) : option (X * X * extra) :=
  if fuel is S fuel
  then
    let%opt (x', e) := get x in
    if le x x'
    then Some (x, x', e)
    else find_loop_aux fuel (meet x x')
  else
    None.

Definition find_loop := find_loop_aux 100.

End FIND_LOOP.

Fixpoint ofold2
  (A B R : Type)
  (f : A -> B -> R -> option R)
  (la : seq A)
  (lb : seq B)
  (r : R) :
  option R :=
  match la, lb with
  | [::], [::] => Some r
  | a :: la, b :: lb => let%opt r' := f a b r in ofold2 f la lb r'
  | _, _ => None
  end.

Section SEM_PROPERTIES.

Context
  (prog machine directive observation : Type)
  (sem :
     prog ->
     machine ->
     seq directive ->
     seq observation ->
     option machine ->
     Prop)
.

Definition sem_total : Prop :=
  forall p s ds, exists os s', sem p s ds os s'.

Definition sem_deterministic_observations : Prop :=
  forall p m ds os1 os2 m1 m2,
    sem p m ds os1 m1 ->
    sem p m ds os2 m2 ->
    os1 = os2.

End SEM_PROPERTIES.

Definition rel_implies X (p q : relation X) : Prop :=
  forall x y, p x y -> q x y.

Definition any_rel {T: Type} (phi: relation T) (x: T) := exists (y: T), phi x y \/ phi y x.

Lemma any_rel_implies {T: Type} (phi1 phi2: relation T) (x: T) :
  rel_implies phi1 phi2 -> any_rel phi1 x -> any_rel phi2 x.
Proof.
  rewrite /rel_implies /any_rel => Himpl [] y H1.
  exists y.
  by case H1 => H; [left|right]; apply Himpl.
Qed.

Lemma any_rel_left {T: Type} (phi: relation T) (x y: T):
  phi x y -> any_rel phi x.
Proof.
  by move => H; exists y; left.
Qed.

Lemma any_rel_right {T: Type} (phi: relation T) (x y: T):
  phi y x -> any_rel phi x.
Proof.
  by move => H; exists y; right.
Qed.
