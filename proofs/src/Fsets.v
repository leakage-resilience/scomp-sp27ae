From Coq Require Import
  FMaps FMapAVL FSetAVL MSetEqProperties
  Structures.Equalities
  ZArith
.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import utils.

Open Scope Z.


Definition gcmp {T:Type} {cmp:T -> T -> comparison} {C:Cmp cmp} := cmp.

Section CMP.

  Context {T:Type} {cmp:T -> T -> comparison} {C:Cmp cmp}.

  Lemma cmp_trans y x z c:
    cmp x y = c -> cmp y z = c -> cmp x z = c.
  Proof.
    by move=> H1 H2;apply (@cmp_ctrans _ _ C y);rewrite H1 H2 ctransI.
  Qed.

  Lemma cmp_refl x : cmp x x = Eq.
  Proof. by have := @cmp_sym _ _ C x x;case: (cmp x x). Qed.

  Definition cmp_lt x1 x2 := gcmp x1 x2 == Lt.

  Definition cmp_le x1 x2 := gcmp x2 x1 != Lt.

  Lemma cmp_le_refl x : cmp_le x x.
  Proof. by rewrite /cmp_le /gcmp cmp_refl. Qed.

  Lemma cmp_lt_trans y x z : cmp_lt x y -> cmp_lt y z -> cmp_lt x z.
  Proof.
    rewrite /cmp_lt /gcmp => /eqP h1 /eqP h2;apply /eqP;apply (@cmp_ctrans _ _ C y).
    by rewrite h1 h2.
  Qed.

  Lemma cmp_le_trans y x z : cmp_le x y -> cmp_le y z -> cmp_le x z.
  Proof.
    rewrite /cmp_le /gcmp => h1 h2;have := (@cmp_ctrans _ _ C y z x).
    by case: cmp h1 => // _;case: cmp h2 => //= _;rewrite /ctrans => /(_ _ erefl) ->.
  Qed.

  Lemma cmp_nle_lt x y: ~~ (cmp_le x y) = cmp_lt y x.
  Proof. by rewrite /cmp_le /cmp_lt /gcmp Bool.negb_involutive. Qed.

  Lemma cmp_nlt_le x y: ~~ (cmp_lt x y) = cmp_le y x.
  Proof. done. Qed.

  Lemma cmp_lt_le_trans y x z: cmp_lt x y -> cmp_le y z -> cmp_lt x z.
  Proof.
    rewrite /cmp_le /cmp_lt /gcmp (cmp_sym z) => h1 h2.
    have := (@cmp_ctrans _ _ C y x z).
    by case: cmp h1 => // _;case: cmp h2 => //= _;rewrite /ctrans => /(_ _ erefl) ->.
  Qed.

  Lemma cmp_le_lt_trans y x z: cmp_le x y -> cmp_lt y z -> cmp_lt x z.
  Proof.
    rewrite /cmp_le /cmp_lt /gcmp (cmp_sym y) => h1 h2.
    have := (@cmp_ctrans _ _ C y x z).
    by case: cmp h1 => // _;case: cmp h2 => //= _;rewrite /ctrans => /(_ _ erefl) ->.
  Qed.

  Lemma cmp_lt_le x y : cmp_lt x y -> cmp_le x y.
  Proof.
    rewrite /cmp_lt /cmp_le /gcmp => /eqP h.
    by rewrite cmp_sym h.
  Qed.

  Lemma cmp_nle_le x y : ~~ (cmp_le x y) -> cmp_le y x.
  Proof. by rewrite cmp_nle_lt; apply: cmp_lt_le. Qed.

End CMP.

Declare Scope cmp_scope.
Notation "m < n" := (cmp_lt m n) : cmp_scope.
Notation "m <= n" := (cmp_le m n) : cmp_scope.
Delimit Scope cmp_scope with CMP.

#[global]
Hint Resolve cmp_le_refl : core.


Module Type CmpType.

  Parameter t : eqType.

  Parameter cmp : t -> t -> comparison.

  Parameter cmpO : Cmp cmp.

End CmpType.

Module MkOrdT (T:CmpType) <: OrderedType.

#[global]
  Existing Instance T.cmpO | 1.

  Definition t := Equality.sort T.t.

  Definition eq x y := T.cmp x y = Eq.
  Definition lt x y := T.cmp x y = Lt.

  Lemma eq_refl x: eq x x.
  Proof. apply: cmp_refl. Qed.

  Lemma eq_sym x y: eq x y -> eq y x.
  Proof. by rewrite /eq=> Heq;rewrite cmp_sym Heq. Qed.

  Lemma eq_trans x y z: eq x y -> eq y z -> eq x z.
  Proof. apply cmp_trans. Qed.

  Lemma lt_trans x y z: lt x y -> lt y z -> lt x z.
  Proof. apply cmp_trans. Qed.

  Lemma lt_not_eq x y: lt x y -> ~ eq x y.
  Proof. by rewrite /lt /eq => ->. Qed.

  Lemma gt_lt x y : T.cmp x y = Gt -> lt y x.
  Proof. by rewrite /lt=> H;rewrite cmp_sym H. Qed.

  Definition compare x y : Compare lt eq x y :=
    let c := T.cmp x y in
    match c as c0 return c = c0 -> Compare lt eq x y with
    | Lt => @LT t lt eq x y
    | Eq => @EQ t lt eq x y
    | Gt => fun h => @GT t lt eq x y (gt_lt h)
    end (erefl c).

  Definition eq_dec x y: {eq x y} + {~ eq x y}.
  Proof. (rewrite /eq;case:T.cmp;first by left); by right. Qed.

End MkOrdT.

Module MkMOrdT (T:CmpType) <: Orders.OrderedType.
#[global]
  Existing Instance T.cmpO | 1.

  Definition t := Equality.sort T.t.

  Definition eq := @Logic.eq t.

  Lemma eq_equiv : Equivalence eq.
  Proof. by auto. Qed.

  Definition lt x y := T.cmp x y = Lt.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    + by move=> x;rewrite /complement /lt cmp_refl.
    move=> ???;apply cmp_trans.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. by rewrite /eq;move=> ?? -> ?? ->. Qed.

  Definition compare : t -> t -> comparison := T.cmp.

  Lemma compare_spec :
     forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    move=> x y;rewrite /compare /eq /lt (cmp_sym y x).
    case: T.cmp (@cmp_eq _ _ T.cmpO x y);constructor;auto.
  Qed.

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    by move=> x y;case:(x =P y);[left | right].
  Qed.

End MkMOrdT.

Module Smake (T:CmpType).
  Module Ordered := MkMOrdT T.
  Include (MSetAVL.Make Ordered).
End Smake.

Module SExtra (T : CmpType).

Module Sv.
  Include (Smake T).
  Definition disjoint (s1 s2 : t) : bool := is_empty (inter s1 s2).
  Definition superset (s1 s2 : t) : bool := subset s2 s1.

  Lemma disjointP s1 s2 :
    reflect (forall x, In x s1 -> ~ In x s2) (disjoint s1 s2).
  Proof.
    case: (@idP (disjoint s1 s2)) => hdisj; constructor.
    + move=> x h1 h2.
      move: hdisj.
      rewrite /disjoint => /is_empty_spec /(_ x) /inter_spec.
      by apply.
    move=> h; apply: hdisj.
    rewrite /disjoint.
    by apply /is_empty_spec => x /inter_spec []; apply h.
  Qed.
End Sv.

Module SvP := MSetEqProperties.EqProperties Sv.
Module SvD := MSetDecide.WDecide Sv.
Module SvF := MSetFacts.WFactsOn(Sv.E)(Sv).

Lemma Sv_memP x s: reflect (Sv.In x s) (Sv.mem x s).
Proof.
  apply: (@equivP (Sv.mem x s));first by apply idP.
  by rewrite -Sv.mem_spec.
Qed.

Lemma Sv_elemsP x s : reflect (Sv.In x s) (x \in Sv.elements s).
Proof.
  apply: (equivP idP);rewrite SvD.F.elements_iff.
  elim: (Sv.elements s) => /= [|v vs H]; split => //=.
  + by move /SetoidList.InA_nil.
  + by rewrite inE => /orP [ /eqP -> | /H];auto.
  case/SetoidList.InA_cons => [ -> |]; rewrite inE ?eq_refl //.
  by move /H => ->; rewrite orbT.
Qed.

Lemma Sv_elems_eq x s : Sv.mem x s = (x \in (Sv.elements s)).
Proof. by apply: sameP (Sv_memP x s) (Sv_elemsP x s). Qed.

#[global]
Instance disjoint_m :
  Proper (Sv.Equal ==> Sv.Equal ==> eq) Sv.disjoint.
Proof.
  by move => s1 s1' Heq1 s2 s2' Heq2;rewrite /Sv.disjoint Heq1 Heq2.
Qed.

#[global]
Instance disjoint_sym : Symmetric Sv.disjoint.
Proof.
  move=> x y h; rewrite/Sv.disjoint.
  erewrite SvD.F.is_empty_m. exact h.
  SvD.fsetdec.
Qed.

Lemma disjoint_w x x' y :
  Sv.Subset x x' ->
  Sv.disjoint x' y ->
  Sv.disjoint x y.
Proof.
  move=> le e; apply SvD.F.is_empty_iff in e.
  apply SvD.F.is_empty_iff.
  SvD.fsetdec.
Qed.

Lemma disjoint_diff A B :
  Sv.disjoint A B ->
  Sv.Equal (Sv.diff B A) B.
Proof.
  rewrite /Sv.disjoint /is_true Sv.is_empty_spec.
  SvD.fsetdec.
Qed.

Lemma in_disjoint_diff x a b c :
  Sv.In x a ->
  Sv.In x b ->
  Sv.disjoint a (Sv.diff b c) ->
  Sv.In x c.
Proof. rewrite /Sv.disjoint /is_true Sv.is_empty_spec; SvD.fsetdec. Qed.

(* ---------------------------------------------------------------- *)
Lemma Sv_mem_add (s: Sv.t) (x y: Sv.elt) :
  Sv.mem x (Sv.add y s) = (x == y) || Sv.mem x s.
Proof.
  case: eqP.
  - move => <-; exact: SvP.add_mem_1.
  move => ne; exact: (SvD.F.add_neq_b _ (not_eq_sym ne)).
Qed.

Lemma Sv_Subset_union_left (a b c: Sv.t) :
  Sv.Subset a b -> Sv.Subset a (Sv.union b c).
Proof. SvD.fsetdec. Qed.

Lemma Sv_Subset_union_right (a b c: Sv.t) :
  Sv.Subset a c -> Sv.Subset a (Sv.union b c).
Proof. SvD.fsetdec. Qed.

Lemma Sv_union_empty (a : Sv.t) :
  Sv.Equal (Sv.union Sv.empty a) a.
Proof. SvD.fsetdec. Qed.

Lemma Sv_Subset_union (a b c : Sv.t) :
  Sv.subset (Sv.union a b) c ->
  Sv.subset a c.
Proof. move: (SvP.union_subset_1 a b). apply SvP.subset_trans. Qed.

(* ---------------------------------------------------------------- *)

Definition sv_of_option (oa : option Sv.elt) : Sv.t :=
  oapp Sv.singleton Sv.empty oa.

(* ---------------------------------------------------------------- *)
Definition sv_of_list T (f: T -> Sv.elt) : seq T -> Sv.t :=
  foldl (fun s r => Sv.add (f r) s) Sv.empty.

Lemma sv_of_listE T (f: T -> Sv.elt) x m :
  Sv.mem x (sv_of_list f m) = (x \in map f m).
Proof.
  suff h : forall s, Sv.mem x (foldl (fun (s : Sv.t) (r : T) => Sv.add (f r) s) s m) = (x \in map f m) || Sv.mem x s by rewrite h orbF.
  elim: m => //= z m hrec s.
  rewrite hrec in_cons SvD.F.add_b /SvD.F.eqb.
  case: SvD.F.eq_dec => [-> | /eqP]; first by rewrite eqxx /= orbT.
  by rewrite eq_sym => /negbTE ->.
Qed.

Lemma sv_of_listP T (f: T -> Sv.elt) x m :
  reflect (Sv.In x (sv_of_list f m)) (x \in map f m).
Proof. rewrite -sv_of_listE; apply Sv_memP. Qed.

Lemma sv_of_list_map A B (f: A -> B) (g: B -> Sv.elt) m :
  sv_of_list g (map f m) = sv_of_list (g \o f) m.
Proof.
  rewrite /sv_of_list.
  elim: m Sv.empty => // a m ih z.
  by rewrite /= ih.
Qed.

Lemma sv_of_list_mem_head X f (x : X) xs :
  Sv.mem (f x) (sv_of_list f (x :: xs)).
Proof. rewrite sv_of_listE. exact: mem_head. Qed.

Lemma sv_of_list_mem_tail X f v (x : X) xs :
  Sv.mem v (sv_of_list f xs)
  -> Sv.mem v (sv_of_list f (x :: xs)).
Proof.
  rewrite !sv_of_listE.
  rewrite in_cons.
  move=> ->.
  exact: orbT.
Qed.

Lemma sv_of_list_fold T f l s :
  Sv.Equal (foldl (fun (s : Sv.t) (r : T) => Sv.add (f r) s) s l) (Sv.union s (sv_of_list f l)).
Proof.
  rewrite /sv_of_list; elim: l s => //= [ | a l hrec] s; first by SvD.fsetdec.
  rewrite hrec (hrec (Sv.add _ _)); SvD.fsetdec.
Qed.

Lemma sv_of_list_cons T (f : T -> _) x l :
  Sv.Equal (sv_of_list f (x::l)) (Sv.add (f x) (sv_of_list f l)).
Proof. rewrite /sv_of_list /= sv_of_list_fold; SvD.fsetdec. Qed.

Lemma disjoint_subset_diff xs ys :
  Sv.disjoint xs ys ->
  Sv.Subset xs (Sv.diff xs ys).
Proof.
  move=> /disjoint_sym /disjoint_diff /SvP.MP.equal_sym.
  exact: SvP.MP.subset_equal.
Qed.

Lemma in_add_singleton x y :
  Sv.In x (Sv.add y (Sv.singleton x)).
Proof. apply: SvD.F.add_2. exact: SvD.F.singleton_2. Qed.

Lemma disjoint_union xs ys zs :
  Sv.disjoint (Sv.union xs ys) zs ->
  Sv.disjoint xs zs /\ Sv.disjoint ys zs.
Proof.
 move=> /Sv.is_empty_spec H.
 split;
   apply/Sv.is_empty_spec;
   SvD.fsetdec.
Qed.

Lemma disjoint_add x xs ys :
  Sv.disjoint (Sv.add x xs) ys
  -> Sv.disjoint (Sv.singleton x) ys /\ Sv.disjoint xs ys.
Proof.
  move=> /Sv.is_empty_spec h.
  split;
    apply/Sv.is_empty_spec;
    SvD.fsetdec.
Qed.

Lemma union_disjoint xs ys zs :
  Sv.disjoint xs zs
  -> Sv.disjoint ys zs
  -> Sv.disjoint (Sv.union xs ys) zs.
Proof.
  rewrite /disjoint.
  move=> /Sv.is_empty_spec h0.
  move=> /Sv.is_empty_spec h1.
  apply/Sv.is_empty_spec.
  move: h0 h1.
  clear.
  SvD.fsetdec.
Qed.

Lemma disjoint_singleton x s :
  Sv.disjoint (Sv.singleton x) s = ~~ Sv.mem x s.
Proof.
  case: Sv.disjointP; case: Sv_memP => //.
  - move => H K; elim: (K _ _ H); SvD.fsetdec.
  by move => H K; elim: K => y /Sv.singleton_spec ->.
Qed.

Lemma Sv_equal_add_add x s :
  Sv.Equal (Sv.add x (Sv.add x s)) (Sv.add x s).
Proof. SvD.fsetdec. Qed.

Lemma Sv_neq_not_in_singleton x y :
  x <> y
  -> ~ Sv.In y (Sv.singleton x).
Proof. SvD.fsetdec. Qed.

Lemma Sv_mem_singleton x s: Sv.Subset (Sv.singleton x) s -> Sv.mem x s.
Proof.
  rewrite /Sv.Subset => H.
  apply /Sv_memP.
  apply (H x).
  by rewrite Sv.singleton_spec.
Qed.

Lemma Sv_add_subset x s: Sv.Subset s (Sv.add x s).
Proof.
  rewrite /Sv.subset_spec /Sv.Subset => y Hy.
  by apply SvD.F.add_2.
Qed.

Lemma Sv_subset_remove s x :
  Sv.subset (Sv.remove x s) s.
Proof. apply/Sv.subset_spec. by apply: SvP.MP.subset_remove_3. Qed.

Lemma Sv_diff_empty s :
  Sv.Equal (Sv.diff s Sv.empty) s.
Proof. SvD.fsetdec. Qed.

(* Deduce inequalities from [~ Sv.In x (Sv.add y0 (... (Sv.add yn s)))]. *)
Ltac t_notin_add :=
  repeat (move=> /Sv.add_spec /Decidable.not_or [] ?);
  move=> ?.

Lemma eqP x y : reflect (x = y) (SvD.F.eqb x y).
Proof. by rewrite /SvD.F.eqb /SvD.F.eq_dec; case Sv.Ordered.eq_dec; constructor. Qed.

Lemma eqbP x y : (SvD.F.eqb x y) = (x == y).
Proof. 
  case: eqP => [-> | ]. 
  + by rewrite eqxx. 
  by move=> hne; apply/sym_eq/introF; [apply: eqtype.eqP | ].
Qed.

End SExtra.

Module Type MapT.
  Declare Module K : CmpType.

  Parameter t : Type -> Type.
  Parameter const : forall {T}, T -> t T.
  Parameter get : forall {T}, t T -> K.t -> T.
  Parameter set : forall {T}, t T -> K.t -> T -> t T.
  Parameter map : forall {T1 T2}, t T1 -> (T1 -> T2) -> t T2.

  Parameter get_const : forall T (t: T) x, get (const t) x = t.

  Parameter get_set :
    forall T (m : t T) x y (v : T),
      get (set m x v) y = if x == y then v else get m y.

  Parameter set_eq :
    forall T (m : t T) x (v : T),
      get (set m x v) x = v.

  Parameter set_neq :
    forall T (m : t T) x y (v : T),
      x != y -> get (set m x v) y = get m y.

  Parameter mapP :
    forall T1 T2 (f : T1 -> T2) (m : t T1) (x : K.t),
      get (map m f) x = f (get m x).
End MapT.

Module MMake(_K : CmpType) <: MapT.
  Module K := _K.

  Definition t (T : Type) : Type := K.t -> T.
  Definition const {T} (x : T) : t T := fun _ => x.
  Definition get {T} (m : t T) (x : K.t) := m x.
  Definition set {T} (m : t T) (x : K.t) (v : T) : t T :=
    fun y => if x == y then v else m y.

  Lemma get_const T (t: T) x : get (const t) x = t.
  Proof. by []. Qed.

  Lemma get_set T (m : t T) x y v :
    get (set m x v) y = if x == y then v else get m y.
  Proof. done. Qed.

  Definition map T1 T2 (m : t T1) (f : T1 -> T2) := fun x => f (m x).

  Lemma set_eq T m  x (v : T) :
    get (set m x v) x = v.
  Proof. by rewrite get_set eqxx. Qed.

  Lemma set_neq T m x y (v : T) :
    x != y ->
    get (set m x v) y = get m y.
  Proof. by rewrite get_set => /negPf ->. Qed.

  Lemma mapP T1 T2 (f : T1 -> T2) m x :
    get (map m f) x = f (get m x).
  Proof. done. Qed.
End MMake.

(* Partial maps. *)
Module Type PMapT.
  Declare Module K : CmpType.

  Parameter t : Type -> Type.
  Parameter empty : forall T, t T.
  Parameter is_empty : forall T, t T -> bool.
  Parameter get : forall {T}, t T -> K.t -> option T.
  Parameter set : forall {T}, t T -> K.t -> T -> t T.
  Parameter map : forall {T1 T2}, (T1 -> T2) -> t T1 -> t T2.
  Parameter incl : forall {T:eqType}, t T -> t T -> bool.

  Parameter merge : forall {T1 T2 T3}, (option T1 -> option T2 -> option T3) -> t T1 -> t T2 -> t T3.

  Parameter get_empty :
    forall T x,
      get (empty T) x = None.

  Parameter is_emptyP :
    forall T (m : t T),
    reflect (forall x, get m x = None) (is_empty m).

  Parameter get_set :
    forall T (m : t T) x y (v : T),
    get (set m x v) y = if x == y then Some v else get m y.

  Parameter set_eq :
    forall T (m : t T) x (v : T),
      get (set m x v) x = Some v.

  Parameter set_neq :
    forall T (m : t T) x y (v : T),
      x != y -> get (set m x v) y = get m y.

  Parameter mapP :
    forall T1 T2 (f : T1 -> T2) (m : t T1) (x : K.t),
    get (map f m) x = omap f (get m x).

  Parameter mergeP : 
    forall {T1 T2 T3} (f : option T1 -> option T2 -> option T3) m1 m2 (k: K.t), 
    f None None = None ->
    get (merge f m1 m2) k = f (get m1 k) (get m2 k).

  Parameter inclP : 
    forall (T : eqType) (m1 m2: t T),
    reflect 
      (forall k t, get m1 k = Some t -> get m2 k = Some t)
      (incl m1 m2).

End PMapT.

Module PMMake(_K : CmpType) <: PMapT.
  Module K := _K.
  Module Ordered := MkOrdT K.
  Module Map := FMapAVL.Make Ordered.
  Module Facts := WFacts_fun Ordered Map.

  Definition t (T : Type) : Type := Map.t T.
  Definition empty T : t T := Map.empty T.
  Definition is_empty T (m : t T) := Map.is_empty m.
  Definition get {T} (m : t T) (x : K.t) := Map.find x m.
  Definition set {T} (m : t T) (x : K.t) (v : T) : t T := Map.add x v m.
  Definition map := Map.map.
  Definition merge := Map.map2.
  
  Lemma get_empty T x : get (empty T) x = None.
  Proof. by rewrite /empty /get Facts.empty_o. Qed.

  Lemma is_emptyP T (m : t T) :
    reflect (forall x, get m x = None) (is_empty m).
  Proof.
    rewrite /is_empty /get /Map.find /Map.Empty /Map.is_empty.
    case heq: Map.Raw.is_empty; constructor.
    + move=> x; have h := Map.Raw.Proofs.is_empty_2 heq.
      case heq1:  Map.Raw.find => [ e | //].
      by have /h := Map.Raw.Proofs.find_2 heq1.
    move=> h.
    rewrite Map.Raw.Proofs.is_empty_1 in heq => //.
    rewrite /Map.Raw.Proofs.Empty => k e hm.
    have := Map.Raw.Proofs.find_1 (Map.is_bst m) hm.
    by rewrite h.
  Qed.

  Lemma get_set T m x y (v : T) :
    get (set m x v) y = if x == y then Some v else get m y.
  Proof.
    rewrite /set /get /=.
    case: eqP=> H.
    + by rewrite Facts.add_eq_o // H cmp_refl.
    by rewrite Facts.add_neq_o // => H1;apply H;apply cmp_eq.
  Qed.

  Lemma set_eq T m  x (v : T) :
    get (set m x v) x = Some v.
  Proof. by rewrite get_set eqxx. Qed.

  Lemma set_neq T m x y (v : T) :
    x != y ->
    get (set m x v) y = get m y.
  Proof. by rewrite get_set => /negPf ->. Qed.

  Lemma mapP T1 T2 (f : T1 -> T2) m x :
    get (map f m) x = omap f (get m x).
  Proof. by rewrite /map /get Facts.map_o. Qed.

  Lemma mergeP {T1 T2 T3} (f : option T1 -> option T2 -> option T3) m1 m2 (k: K.t):
    f None None = None ->
    get (merge f m1 m2) k = f (get m1 k) (get m2 k).
  Proof.
    rewrite /get /merge.
    apply Facts.map2_1bis.
  Qed.

  Module MoreMap := WProperties_fun Ordered Map.

  Definition incl (T : eqType) (m1 m2: t T) :=
    MoreMap.for_all
      (fun k v =>
         match Map.find k m2 with
         | None => false
         | Some t => v == t
         end) m1.

  Lemma inclP (T : eqType) (m1 m2: t T):
    reflect
      (forall k t, get m1 k = Some t -> get m2 k = Some t)
      (incl m1 m2).
  Proof.
    apply: iff_reflect; rewrite /incl.
    rewrite -> MoreMap.for_all_iff; last first.
    + move => ?? /Facts.find_o h ? _ <-; by rewrite h.
    rewrite /get; split.
    + by move => h k e /Facts.find_mapsto_iff /h ->; rewrite eqxx.
    by move => h k e /Facts.find_mapsto_iff /h; case: Map.find => // _ /eqP <-.
  Qed.

End PMMake.
