(* -------------------------------------------------------------------------- *)
(* Loop peeling. *)
(* Perform one peeling of annotated loops. *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.
From Coq Require Import Equality. (* Maybe not needed *)

Require Import
  semantics
  syntax
  utils
  var
.
Require Import language ni_preservation.
Existing Instance Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

Section PASS.

Context (should_peel : iinfo -> bool).

(*
  Performs loop peeling on an instruction i given the instruction info ii
  - If i is a while instruction
    - It is peeled if the should_peel oracle returns true
    - Loop peeling is performed on the loop body
  - If i is an if instruction, loop peeling is performed on both branch bodies
  - Otherwise, the instruction remains unchanged
*)
Fixpoint peel_i (i : instr) (ii : iinfo) : instr :=
  let peel_ai ai := peel_i (unannot ai) (annot ai) |> with_unannot ai in
  let peel_c c := map peel_ai c in
  match i with
  | Iwhile e c =>
      let c := peel_c c in
      if should_peel ii
      then
        let a := {| annot := ii; unannot := Iwhile e c; |} in
        Iif e (c ++ [:: a ]) [::]
      else Iwhile e c
  | Iif e c1 c0 => Iif e (peel_c c1) (peel_c c0)
  | _ => i
  end.

(* Perform loop peeling on an annotated instruction *)
Definition peel_ai (ai : instr_i) : instr_i :=
  peel_i (unannot ai) (annot ai) |> with_unannot ai.
(* Perform loop peeling an all instructions in the given code c *)
Definition peel_c (c : code) : code := map peel_ai c.
(* Perform loop peeling on all instructions in the code of program p *)
Definition peel_p (p : prog) : prog := map_p_prog peel_c p.

End PASS.

Require Import
  semantics_facts
  utils_facts
.

Section PROOF.

Context
  (should_peel : iinfo -> bool)
  (p_s p_t : prog)
  (hcompile : peel_p should_peel p_s = p_t)
.

Notation peel_i := (peel_i should_peel).
Notation peel_ai := (peel_ai should_peel).
Notation peel_c := (peel_c should_peel).

Section SIM.

(*
  Relation for lock-step: Target code is either the compilation of the source's or a peeled loop after the first iteration
  - No code relates to no code
  - Target code is compilation of the source's (if the rest of the code is in relation and first instruction of target is the compiled first instruction of source, the whole code is in relation)
  - Peeled loop after first iteration (if first instruction is a while instruction for both target and source, the sources body is in relation with targets body and the rest of the code is in relation, the whole code is in relation)

  The relation is not just c_t = peel_c c_s, because only the first iteration of a while loop is peeled
*)
Inductive sim_c : code -> code -> Prop :=
| Sim_nil :
  sim_c [::] [::]

| Sim_cons :
  forall ai c_s c_t,
    sim_c c_s c_t ->
    sim_c (ai :: c_s) (peel_ai ai :: c_t)

| Sim_while :
  forall e cbody_s cbody_t ann c_s c_t,
    let: ai_s := {| annot := ann; unannot := Iwhile e cbody_s; |} in
    let: ai_t := {| annot := ann; unannot := Iwhile e cbody_t; |} in
    sim_c cbody_s cbody_t ->
    sim_c c_s c_t ->
    sim_c (ai_s :: c_s) (ai_t :: c_t)
.

(*
  Other definition of sim_c, that is easier to use in some cases
*)
Let sim_c_prop c_s c_t :=
  match c_s with
  | [::] => c_t = [::]
  | ai_s :: c_s =>
      exists ai_t c_t',
        [/\ c_t = ai_t :: c_t'
          , [\/ ai_t = peel_ai ai_s
              | exists e cbody_s cbody_t ann,
                  [/\ ai_s = {| annot := ann; unannot := Iwhile e cbody_s; |}
                    , ai_t = {| annot := ann; unannot := Iwhile e cbody_t; |}
                    & sim_c cbody_s cbody_t
                  ]
              ]
          & sim_c c_s c_t'
        ]
  end.

(* Proof that sim_c and sim_c_prop are equivalent *)
Lemma sim_cP c_s c_t :
  sim_c c_s c_t <-> sim_c_prop c_s c_t.
Proof.
  split.
  - case; by eeauto.
  case: c_s => [|ai_s c_s];
    case: c_t => [|ai_t c_t] //=.
  - move=> _. exact: Sim_nil.
  - by move=> [] ? [] ? [] //.
  move=> [ai_t0 [c_t0 [[??] hai]]]; subst ai_t0 c_t0.
  case: hai => [?|].
  - subst ai_t. exact: Sim_cons.
  move=> [e [cbody_s [cbody_t [ann [?? hsim]]]]].
  subst ai_s ai_t.
  exact: Sim_while.
Qed.

(*
  Two states are in sim relation if:
  - Their code is in relation on sim_c
  - Their variable map is the same
  - Their memory is the same
*)
Definition sim (s t : state) : Prop :=
  [/\ sim_c (s_c s) (s_c t)
    , s_vm s = s_vm t
    & s_mem s = s_mem t
  ].

End SIM.

(*
  Peeled code stands in sim_c relation to its source
*)
Lemma sim_c_comp c :
  sim_c c (peel_c c).
Proof.
  elim: c => [|ai c hind].
  - by apply/sim_cP.
  exact: Sim_cons.
Qed.

(*
  Concatenating two pairs of related code blocks preserves the relation
*)
Lemma sim_c_cat c_s c_t c_s' c_t' :
  sim_c c_s c_t ->
  sim_c c_s' c_t' ->
  sim_c (c_s ++ c_s') (c_t ++ c_t').
Proof.
  move=> hsim hsim'.
  elim: c_s c_t hsim => [|[ann i_s] c_s hind] c_t /sim_cP.
  - by move=> ->.
  move=> [ai_t [c_t'' [? hai hsim]]]; subst c_t.
  case: hai => [?|].
  - subst ai_t. apply: Sim_cons. exact: hind.
  move=> [e [cbody_s [cbody_t [ann0 [[??] ? hsim0]]]]]; subst i_s ai_t ann0.
  apply: Sim_while; first exact: hsim0.
  exact: hind.
Qed.

(*
  If state s and t are in relation and s can step to s' with the given observations,
  there is a state t' that t steps to with the same observations and is in relation to s'
*)
Lemma single_step_security s s' t ot ov :
  sim s t ->
  step s ot ov s' ->
  exists t', step t ot ov t' /\ sim s' t'.
Proof.
  move=> [/sim_cP hsimc hvm hmem] /stepI.
  case hc_s: (s_c s) hsimc => [|[ann i] c_s] /=.
  - contradiction.
  move=> [ai_t [c_t [hc_t hai hsim]]].
  case: hai => [?|]; first last.

  (* Second time we enter a peeled loop. *)
  - move=> [e [cbody_s [cbody_t [ann0 [[??] ? hsim']]]]].
    subst ann0 i ai_t.
    move=> [b [hb ???]].
    subst ot ov s'.
    set ai_t := {| annot := ann; unannot := Iwhile e cbody_t; |}.
    set t' :=
      let: c' := if b then cbody_t ++ ai_t :: c_t else c_t in
      with_c t c'.
    exists t'.
    subst t'.
    split.
    + apply stepI.
      rewrite hc_t -hvm hb.
      by exists b.
    + split; auto.
      case b.
      * apply sim_c_cat.
        exact hsim'.
        exact: Sim_while.
      * exact hsim.

  (* Peel loop *)
  subst ai_t.
  clear hc_s.
  case: i hc_t => //=.

  (* assign instruction *)
  - move=> x e hc [???]; subst ot ov s'.
    exists (s_after_assign t c_t x e).
    split.
    + apply/stepI.
      by rewrite hvm hc.
    by rewrite /s_after_assign /write_reg hvm.

  (* load instruction *)
  - move=> x a e hc [i [hi hbi hdef ???]]; subst ot ov s'.
    exists (s_after_load t c_t x a i).
    split.
    + apply/stepI.
      rewrite hc.
      exists i.
      by rewrite -hvm -hmem.
    by rewrite /s_after_load /write_reg hvm hmem.

  (* store instruction *)
  - move=> a e x hc [i [ hi hbi hdef ???]]; subst ot ov s'.
    exists (s_after_store t c_t a i x).
    split.
    + apply/stepI.
      rewrite hc.
      exists i.
      by rewrite -hvm.
    by rewrite /s_after_store /write_mem hvm hmem.

  (* mop instruction *)
  - move=> xs m ys hc [vs [hvs hl ???]]; subst ot ov s'.
    exists (s_after_regwrites t c_t (zip xs vs)).
    split.
    + apply/stepI.
      rewrite hc.
      exists vs.
      by rewrite -hvm.
    rewrite  /s_after_regwrites /write_reg /foldr.
    induction (zip xs vs).
    + split; auto.
    + split; auto.
      * move: IHl => [_ IHvm _].
        simpl.
        simpl in IHvm.
        by rewrite IHvm.
      * move: IHl => [_ _ IHmem].
        simpl.
        simpl in IHmem.
        by rewrite IHmem.

  (* if instruction *)
  - move=> e c1 c0 hc [b [hb ???]]; subst ot ov s'.
    exists (
      let: c' := (if b then (peel_c c1) else (peel_c c0)) ++ c_t in
      with_c t c'
    ).
    split.
    + apply/stepI.
      rewrite hc.
      exists b.
      rewrite -hvm.
      split; auto.
    split=> //=.
    apply: sim_c_cat => //.
    move: b hb => [|] hb; exact: sim_c_comp.

  (* while instruction *)
  - move=> e cbody hc [b [hb ???]]; subst ot ov s'.
    exists (
      let: unc_while := {| annot := ann; unannot := Iwhile e (peel_c cbody) |} in
      let: c' := if b then (peel_c cbody) ++ unc_while :: c_t else c_t in
      with_c t c'
    ).
    split.
    + apply/stepI.
      rewrite hc.
      simpl.
      case sp_ann: should_peel.
      * exists b.
        split; do? rewrite -hvm; auto.
        f_equal.
        case b; auto.
        by rewrite cats1 cat_rcons.
      * exists b.
        split; do? rewrite -hvm; auto.
        f_equal.
        case b; auto.
        rewrite /peel_ai /with_unannot /peel_i.
        simpl.
        by rewrite sp_ann.
    + split; auto.
      simpl.
      case b.
      * apply sim_c_cat.
        exact (sim_c_comp cbody).
        apply Sim_while.
        exact (sim_c_comp cbody).
        exact hsim.
      * exact hsim.
Qed.

End PROOF.

Require Import preservation_obs.

Section PRESERVATION.

  Context
    {analyze : iinfo -> bool}
  .

  Definition pass : compiler := fun p_s => some (peel_p analyze p_s).

  Definition simT1 : SimT1 := fun _ ot => [:: ot].

  Definition simV1 : SimV1 := fun _ _ ov => [:: ov].

  Definition eq_s := (sim analyze).

  Lemma step_preservation : step_preserves_obs eq_s simT1 simV1.
  Proof.
    move => s t ot_s ov_s s' hsim sstep.
    have sssec := single_step_security hsim sstep.
    destruct sssec as [t' [tstep hsim']].
    exists [:: ot_s], [:: ov_s], t'.
    split; trivial.
    apply sem_step1.
    exact tstep.
  Qed.

  Lemma eq_s_initial : eq_s_initial (compile := pass) eq_s.
  Proof.
    move => p_s p_t inp hpass.
    split; auto.
    - simpl.
      rewrite /pass /peel_p /map_p_prog /with_p_prog in hpass.
      move: hpass => [=] hpass.
      have pass_prog := f_equal p_prog hpass; simpl in pass_prog.
      clear hpass.
      rewrite -pass_prog.
      by apply sim_c_comp.
    - simpl.
      rewrite /pass /peel_p /map_p_prog /with_p_prog in hpass.
      move: hpass => [=] hpass.
      have pass_inp := f_equal p_inputs hpass; simpl in pass_inp.
      by rewrite pass_inp.
  Qed.

  Lemma eq_s_final : eq_s_final eq_s.
  Proof.
    move => s t heq_s.
    simpl.
    rewrite /semantics.final.
    rewrite /eq_s /sim in heq_s.
    destruct heq_s as [hsim_c _ _].
    move/eqP/size0nil => hfin.
    apply sim_cP in hsim_c.
    rewrite hfin in hsim_c.
    rewrite hsim_c.
    by trivial.
  Qed.

  Lemma preservation_obs: preserves_obs (compile := pass) (simT := _simT simT1) (simVIdx := _simVIdx simT1) (simV := _simV simT1 simV1).
  Proof.
    exact (lift_step_preserves_obs eq_s_initial eq_s_final step_preservation).
  Qed.

End PRESERVATION.
