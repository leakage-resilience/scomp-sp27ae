From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  syntax
  semantics
  semantics_facts
  preservation_obs
  utils
  var
.
Require Import language.
Existing Instance Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PASS.

Fixpoint const_eval (e : expr) : option value :=
  match e with
  | Econst i => some (Vint i)
  | Ebool b => some (Vbool b)
  | Evar _ => None
  | Eop1 Onot x =>
      match const_eval x with
      | Some (Vbool b) => some (Vbool (~~ b))
      | _ => None
      end
  | Eop1 Oneg x =>
      match const_eval x with
      | Some (Vint i) => some (Vint (- i))
      | _ => None
      end
  | Eop2 Oadd e0 e1 =>
      match const_eval e0 with
      | Some (Vint z0) =>
          match const_eval e1 with
          | Some (Vint z1) => some (Vint (z0 + z1))
          | _ => None
          end
      | _ => None
      end
  | Eop2 Oeq e0 e1 =>
      match const_eval e0 with
      | Some (Vint z0) =>
          match const_eval e1 with
          | Some (Vint z1) => Some (Vbool (z0 == z1))
          | _ => None
          end
      | Some (Vbool b0) =>
          match const_eval e1 with
          | Some (Vbool b1) => Some (Vbool (b0 == b1))
          | _ => None
          end
      | _ => None
      end
  | Eop2 Oand e0 e1 =>
      match const_eval e0 with
      | Some (Vbool b0) =>
          match const_eval e1 with
          | Some (Vbool b1) => Some (Vbool (b0 && b1))
          | _ => None
          end
      | _ => None
      end
  | Eop2 Olt e0 e1 =>
      match const_eval e0 with
      | Some (Vint z0) =>
          match const_eval e1 with
          | Some (Vint z1) => Some (Vbool (z0 <? z1))
          | _ => None
          end
      | _ => None
      end
  end.

Lemma const_eval_e_eval_e x y vm :
  const_eval x = some y -> eval_e vm x = y.
Proof.
  elim: x y; try done.
  - move=> z y [=] <- //=.
  - move=> b y [=] <- //=.
  - move=> [] o IH y /=.
    destruct (const_eval o) => //.
    destruct v => // [=] <-.
    rewrite (IH _ erefl). done.
    destruct (const_eval o) => //.
    destruct v => // [=] <-.
    rewrite (IH _ erefl). done.
  - move=> [] yl IHl yr IHr y /=.
    1-4: destruct (const_eval yl) => //
         ; destruct v => //
         ; destruct (const_eval yr) => //
         ; destruct v => // [=] <-
         ; rewrite (IHl _ erefl); rewrite (IHr _ erefl); done.
Qed.

Lemma const_eval_undef e : ~ const_eval e = Some (Vundef).
Proof.
  elim: e; try done.
  move=>[]/= e; case: (const_eval e)=>//; by case.
  move=>[]/= e; case: (const_eval e)=>// a? e' ; case: (const_eval e')=>// a'?.
  1-8: by destruct a, a'.
Qed.


(* Evaluates if constant expression, otherwise leaves unchanged *)
Definition reduce_e (e : expr) : expr :=
  match const_eval e with
  | None => e
  | Some (Vint z) => Econst z
  | Some (Vbool b) => Ebool b
  | Some Vundef => e (* absurd *)
  end.

Lemma reduce_eval e vm :
  eval_e vm (reduce_e e) = eval_e vm e.
Proof.
  rewrite/reduce_e.
  destruct (const_eval e) eqn:h => //=.
  destruct v => /= *; by rewrite (const_eval_e_eval_e _ h).
Qed.

Lemma reduce_last_leaks e vm :
  last Vundef (leaks_e vm e) = eval_e vm (reduce_e e).
Proof. by rewrite reduce_eval last_leaks_eval. Qed.

Section Pass.
  Variable const_eval_i : instr -> instr.

  Definition const_eval_ii (ii : instr_i) : instr_i :=
    {| annot := annot ii; unannot := const_eval_i (unannot ii) |}.

  Fixpoint const_eval_c (c : code) : code :=
    match c with
    | [::] => [::]
    | i :: c' => const_eval_ii i :: (const_eval_c c')
    end.
End Pass.

Fixpoint const_eval_i (i : instr) : instr :=
  match i with
  | Iassign x e => Iassign x (reduce_e e)
  | Iload x a e => Iload x a (reduce_e e)
  | Istore a e x => Istore a (reduce_e e) x
  | Imop xs o os => Imop xs o os
  | Iif b th el
    => Iif (reduce_e b) (const_eval_c const_eval_i th) (const_eval_c const_eval_i el)
  | Iwhile b c => Iwhile (reduce_e b) (const_eval_c const_eval_i c)
  end.

Definition const_eval_p := map_p_prog (const_eval_c const_eval_i).

End PASS.

Lemma const_eval_c_cons i c:
  const_eval_c const_eval_i (i :: c) =
    {| annot := annot i; unannot := const_eval_i (unannot i) |}
      :: const_eval_c const_eval_i c.
Proof. done. Qed.

Lemma const_eval_c_cat c c':
  const_eval_c const_eval_i (c ++ c') =
    const_eval_c const_eval_i c ++ const_eval_c const_eval_i c'.
Proof.
  elim: c c'. done.
  move=> /= i c IH c'. by rewrite IH.
Qed.

Definition sim s t := t = with_c s (const_eval_c const_eval_i (s_c s)).

Definition is_fold e := isSome (const_eval e).

Definition expr_of_i i :=
  match i with
  | Iassign x e => e
  | Iload x a e => e
  | Istore a e x => e
  | Imop xs o os => Ebool false (* dummy *)
  | Iif e th el => e
  | Iwhile e c => e
  end.

(* Wether we fold in the expression that is *immediately* evaluated (i.e., within one step) *)
Definition fold_step i :=
  match i with
  | Iassign x e => is_fold e
  | Iload x a e => is_fold e
  | Istore a e x => is_fold e
  | Imop xs o os => false
  | Iif e th el => is_fold e
  | Iwhile e c => is_fold e
  end.

Lemma not_is_fold_const_eval_e e : ~ is_fold e -> reduce_e e = e.
Proof. unfold reduce_e, is_fold. case (const_eval e) => //. Qed.

Lemma fold_step_eval_e i vm :
  ~fold_step i -> leaks_e vm (expr_of_i i) = leaks_e vm (reduce_e (expr_of_i i)).
Proof.
  destruct i => /= H; try rewrite not_is_fold_const_eval_e //.
  done.
Qed.

Theorem step_nofold s t s' ot ov i c :
  s_c s = i :: c
  -> ~ fold_step (unannot i)
  -> sim s t
  -> step s ot ov s'
  -> exists t', semantics.step t ot ov t' /\ sim s' t'.
Proof.
  move: s => [] s_c s_vm s_mem /= ->.
  move: t => [] t_c t_vm t_mem /=.
  move=> Hsame [-> -> ->].
  clear -Hsame.
  have Hrw := fold_step_eval_e s_vm Hsame.
  destruct i as [a i].
  move/stepI.
  Set Warnings "-spurious-ssr-injection".
  destruct i.
  1-6: do ? (case; intro).
  1-6: eexists.
  1-6: split; first
      ( apply/stepI
      ; simpl in *
      ; do ? econstructor
      ; subst
      ; try done
      ; try eassumption
      ; try by rewrite Hrw ).
  1-10: try by rewrite reduce_eval.

  1-6: subst; try rewrite reduce_eval.
  1-6: try done.

  by rewrite/s_after_assign/with_c /= reduce_eval.

  rewrite/s_after_regwrites/sim/with_c /=. congr Build_state.
  clear. induction (zip l x) as [|? ? IH]. done. by rewrite /= IH.
  clear. induction (zip l x) as [|? ? IH]. done. by rewrite /= IH.

  rewrite/sim/with_c /= const_eval_c_cat; by case x.

  rewrite/sim/with_c /=. case x; first rewrite const_eval_c_cat; done.
Qed.

Definition leak_const e :=
  match const_eval e with
  | Some v => [:: v]
  | None => [::] (* dummy *)
  end.

Definition leakage_transformer (i : instr) (v : v_obs) :=
  let '(OVval v) := v in
  match i with
  | Iassign x e  => OVval (leak_const e)
  | Iload x a e  => OVval (leak_const e ++ [:: last Vundef v])
  | Istore a e x => OVval (leak_const e ++ [:: last Vundef v])
  | Imop _ _ _   => v_dummy_observation
  | Iif e th el  => OVval (leak_const e)
  | Iwhile e c   => OVval (leak_const e)
  end.

Lemma leaks_const_eval_e_fold e vm :
  is_fold e
  -> leak_const e = leaks_e vm (reduce_e e).
Proof.
  intro H.
  rewrite/is_fold/reduce_e/leak_const.
  destruct (const_eval e) eqn:h =>//.
  destruct v => //.
  contradiction (const_eval_undef h).
  move: H.
  rewrite /is_fold h //.
Qed.


Theorem step_fold i :
  forall a s t s' ot ov c,
    let i := {| annot := a; unannot := i |} in
    s_c s = i :: c
    -> fold_step (unannot i)
    -> sim s t
    -> step s ot ov s'
    -> exists t', semantics.step t ot (leakage_transformer (unannot i) ov) t' /\ sim s' t'.
Proof.
  elim: i =>
        [ x e
        | x a e | a e x | xs mop os | cond th el | cond bo ].
  1-6: move=> ia [] s_c s_vm s_mem [] t_c t_vm t_mem s' ot ov c /= -> Hsame [-> -> ->].
  1-6: clear -Hsame.
  1-6: move/stepI => /=.
  Set Warnings "-spurious-ssr-injection".
  1-6: do ? (case; intro) ; subst.
  1-6: eexists; split; first (apply/stepI; simpl; do ? econstructor; try eassumption).
  1-16: try done.
  1-12: try by rewrite reduce_eval.
  1-8: try by rewrite -leaks_const_eval_e_fold //; apply (isimple Hsame).
  1-5: try by rewrite last_cat /=; rewrite -leaks_const_eval_e_fold //; apply (isimple Hsame).

  unfold sim, s_after_assign, with_c. simpl.
  by rewrite reduce_eval.

  unfold sim, with_c. rewrite !const_eval_c_cat. simpl.
  by case x.

  unfold sim, with_c.
  by case x; first rewrite const_eval_c_cat.
Qed.

Section PRESERVATION.

Definition pass : compiler (input := input) (Ls := Source) (Lt := Source) :=
  fun p_s => Some (const_eval_p p_s).

Definition _simT1 : SimT1 :=
  fun pc_s ot_s => [:: ot_s].

Definition _simV1 : SimV1 :=
  fun pc_s _ ov_s => match pc_s with
                | [::] => [::]
                | i :: c =>
                    if fold_step (unannot i) then
                      [:: leakage_transformer (unannot i) ov_s]
                    else
                      [:: ov_s]
                end.

Definition eq_s := sim.

Lemma step_preservation:
  step_preserves_obs eq_s _simT1 _simV1.
Proof.
  move=>[] [| i c] s_vm s_mem t ot_s ov_s s' Heq sstep.
  - by move/stepI:sstep.

  case h: (fold_step (unannot i)).
  - have /= H := (step_fold _ h Heq sstep).
    destruct i.
    have [t' [tstep Heq']] := (H _ _ erefl).
    eexists _, _, t'.
    split.
    exact (sem_step1 tstep).
    done. rewrite h. done. done.

  - move/negP: h => h.
    have /= H := (step_nofold _ h Heq sstep).
    destruct i.
    have [t' [tstep Heq']] := (H _ erefl).
    eexists _, _, t'.
    split.
    exact (sem_step1 tstep).
    done. rewrite ifF //. exact/negP. done.
Qed.

Theorem eq_s_initial:
  eq_s_initial (compile := pass) eq_s.
Proof.
  by move=>p_s p_t inp [=] <-.
Qed.

Theorem eq_s_final: eq_s_final eq_s.
Proof.
  move=>s t ->.
  simpl. unfold semantics.final.
  by case (s_c s).
Qed.

Theorem preservation_obs:
  preserves_obs (compile := pass) (simT := _simT _simT1) (simVIdx := _simVIdx _simT1) (simV := _simV _simT1 _simV1).
Proof.
  exact (lift_step_preserves_obs eq_s_initial eq_s_final step_preservation).
Qed.

End PRESERVATION.
