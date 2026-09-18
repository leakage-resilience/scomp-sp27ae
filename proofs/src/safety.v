(* -------------------------------------------------------------------------- *)
(* Safety *)
(* -------------------------------------------------------------------------- *)

From Coq.Bool Require Import Bool.
From mathcomp Require Import all_ssreflect.

Require Import
  language
  utils
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)

Section SAFETY.

  Context
    {input : Type}
    {output : Type}
      {L : Language input output}
  .

  Definition safe_execn_p (p: prog) (n: nat) (inp: input) : Prop :=
    Is_true (isSome (execn_p p inp n)).

  Lemma safe_execn_pE (p: prog) (n: nat) (inp: input):
    safe_execn_p p n inp <->
    (exists ots ovs s', execn_p p inp n = Some (ots, ovs, s')).
  Proof.
    rewrite /safe_execn_p.
    split.
    + destruct (execn_p p inp n) as [[[ots ovs] s']|] eqn:Hexec => [H | //].
      by exists ots; exists ovs; exists s'.
    by case => ots; case => ovs; case => s' => ->.
  Qed.

  Lemma sem_safe_execn_p (p : prog) (n: nat) (inp : input):
    (exists ots ovs s', n = size ots /\ sem_p p inp ots ovs s') <-> 
    safe_execn_p p n inp.
  Proof.
    rewrite safe_execn_pE.
    split; case => ots; case => ovs; case => s' H; exists ots; exists ovs; exists s'.
    + by move: H => [] -> Hsem; apply sem_execn_p.
    split.
    + by eapply execn_p_size; apply H.
    apply sem_execn_p.
    by rewrite -(execn_p_size H).
  Qed.

  (*
  Definition sequential_safe (p : prog) (s : state) : Prop :=
    forall ots ovs s', sem s ots ovs s' -> sequential_safe1 p s'.

  Lemma sequential_safe_sem p s s' ots ovs :
    sequential_safe p s ->
    sem s ots ovs s' ->
    sequential_safe p s'.
  Proof.
    move=> hsafe hsem ots' ovs' s'' hsem'.
    by have/hsafe := sem_cat hsem hsem'.
  Qed.

  Lemma sequential_safe_step p s s' ot ov :
    sequential_safe p s ->
    step s ot ov s' ->
    sequential_safe p s'.
  Proof.
    move=> hsafe hstep.
    apply: sequential_safe_sem; first exact: hsafe.
    apply: sem_trans1.
    exact: hstep.
  Qed.

  Definition sequential_safe_inp
    {input : Type}
    {L : Language input}
    (p : prog)
    (inp: input):
    Prop :=
    sequential_safe p (initial_state p inp).

  Definition sequential_safe_phi
    {input : Type}
    {L : Language input}
    (p : prog)
    (phi : relation input) :
    Prop :=
    forall inp1 inp2,
      phi inp1 inp2 ->
      [/\ sequential_safe p (initial_state p inp1)
       & sequential_safe p (initial_state p inp2)
      ].
      *)

Section PRESERVATION.

(*
  Context
    {input history : Type}
    {Ls Lt : Language input}
    (compile : compiler (Ls := Ls) (Lt := Lt))
  .

  Definition preserves_safety (phi : relation input) : Prop :=
    forall p_s p_t,
      compile p_s p_t ->
      sequential_safe_phi p_s phi ->
      sequential_safe_phi p_t phi.

Lemma has_safe_bw_simulation_preserves_sct phi :
  has_safe_bw_simulation compile ->
  preserves_sct phi.
Proof.
  move=> hbw p_s p_t hcomp hsafe hsct ds os1 os2 inp1 inp2 out1 out2 hphi
    hsem_t1 hsem_t2.
  have [hist [sim [Tdir [Tobs [hinit {}hbw]]]]] := hbw p_s p_t hcomp.
  have {}hbw := lift_step_preserves_sim hbw.
  have [hsafe1 hsafe2] := hsafe _ _ hphi.
  have [s1' [os_s1 [hsem_s1 ?]]] := hbw _ _ _ _ _ _ (hinit inp1) hsafe1 hsem_t1;
    subst os1.
  have [s2' [os_s2 [hsem_s2 ?]]] := hbw _ _ _ _ _ _ (hinit inp2) hsafe2 hsem_t2;
    subst os2.
  by rewrite (hsct _ _ _ _ _ _ _ hphi hsem_s1 hsem_s2).
Qed.
   *)

Section COMPOSITION.
(*
  Context
    {input : Type}
      {L0 L1 L2 : Language input}
      (compile2 : compiler (Ls := L1) (Lt := L2))
      (compile1 : compiler (Ls := L0) (Lt := L1))
  .

  Lemma compose_safety phi :
    preserves_safety compile2 phi ->
    preserves_safety compile1 phi ->
    preserves_safety (compose compile2 compile1) phi.
  Proof.
    move=> hpsafe2 hpsafe1 p_s p_t [p_i h1 h2] hsafe.
    apply: (hpsafe2 _ _ h2).
    exact: (hpsafe1 _ _ h1).
  Qed.
 *)
End COMPOSITION.

End PRESERVATION.

End SAFETY.
