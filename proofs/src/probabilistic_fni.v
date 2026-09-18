(* -------------------------------------------------------------------------- *)
(* Preservation of various Non-Interference Notions                           *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From Coq.Bool Require Import Bool.
From mathcomp Require Import all_ssreflect.

Require Import
  language
  semantics_facts
  utils
  utils_facts
  safety
  preservation_obs
  ni_preservation
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

(* -------------------------------------------------------------------------- *)

Section PROBABILISTIC_FNI.

Context
  {ninputs: nat} (* Number of encoded inputs, i.e., sharings, a gadget is taking *)
    {nshares: nat} (* Number of shares per encoded input a.k.a. sharing *)
    {share: eqType} (* A share within an encoding *)
    {random: predArgType} (* Randomness tape *)
    {public: eqType} (* Public input *)
    {pinput: Type} (* Input of languages *)
.

(* a.k.a. (randomized) encoding *)
Definition sharing := nshares.-tuple share.

(* clarification of `nshares`:
 a gadget taking shares a0, a1, a2 encoding secret value a
 and shares b0, b1, b2 encoding secret value b as input
 has `ninputs = 2` and `nshares = 3`.
 *)

Record input := {
    shares : ninputs.-tuple sharing;
    pub : public;
  }.

Record poutput :=
  {outshares : sharing} (* Output of languages; for simplicity a single encoded output *)
.

Context
  {make_pinput: input -> random -> pinput}
  {Ls Lt : Language pinput poutput}
  {compile : compiler (input := pinput) (Ls := Ls) (Lt := Lt)}
  {simT: @SimT pinput poutput Ls Lt}
  {simVIdx: @SimVIdx pinput poutput Ls}
  {simV: @SimV pinput poutput Ls Lt}
.

(* equality on selected shares of one sharing *)
Definition eq_shares (idxs: seq 'I_nshares) (sh1 sh2: sharing) :=
  all (fun idx => tnth sh1 idx == tnth sh2 idx) idxs.

(* equality on selected shares for each encoded input *)
Definition eq_shares_inp (idxss: seq (seq 'I_nshares)) (shs1 shs2: seq sharing) :=
  [&& size idxss == size shs1
    , size shs1 == size shs2
      & all
          (fun '(idxs, (sh1, sh2)) => eq_shares idxs sh1 sh2)
          (zip idxss (zip shs1 shs2))].

Definition phi_pub (ipub: public) (inp1 inp2 : input) :=
  pub inp1 = ipub /\ pub inp2 = ipub.

Definition eq_input (ipub: public) (idxs: seq (seq 'I_nshares)) (inp1 inp2: input) :=
  eq_shares_inp idxs (shares inp1) (shares inp2) /\ phi_pub ipub inp1 inp2.

Context
  {t: nat} (* security order, i.e, total number of tolerated probes. *)
.

(* parametric f-NI function, it asserts the number of shares the simulator is allowed
   to use for simulating the input, internal and output probes. *)
Definition pfun : Type := nat -> nat -> nat.

(* `SimShIdxs` returns the shares (for each input separately) required for simulating a given set of probes.
   This may depend on the public inputs since we require programs to be constant-time. *)
Definition SimShIdxs :=
  public ->
  seq nat (* input and internal probe positions *) ->
  seq 'I_nshares (* output probe positions *) ->
  ninputs.-tuple (seq 'I_nshares).

(* The simulator is partial, for a total of at most `t` probes to simulate it
   requires at most as many input shares per encoded input as asserted by `f`. *)
Definition sim_fNI (f: pfun) (simShIdxs: SimShIdxs) : Prop :=
  forall pub intprobes outprobes,
    (size intprobes + size outprobes <= t)%N ->
    let shares_inp := simShIdxs pub intprobes outprobes in
    all (fun shares => (size shares <= f (size intprobes) (size outprobes))%N) shares_inp.

(* `phi_input` holds iff the public values in inputs `inp1,inp2` are equal and additionally
   the subset of shares required for the simulation of `probes` (indicated by simShIdxs) agree in the inputs. *)
Definition phi_input
  (pub: public)
  (simShIdxs: SimShIdxs)
  (intprobes: seq nat)
  (outprobes: seq 'I_nshares)
  (inp1 inp2: input) :=
  eq_input pub (simShIdxs pub intprobes outprobes) inp1 inp2.

Variant pinput_make (pR: input -> random -> Prop): pinput -> Prop :=
  | mkpinput :
    forall (inp : input) (r : random),
      pR inp r -> pinput_make pR (make_pinput inp r).

Definition pinput_pubrnd (ipub: public) (rnd_pR: random -> bool) :=
  pinput_make (fun inp r => (pub inp) = ipub /\ rnd_pR r).

Variant proba_phi
  (phi: relation input)
  (bij: input -> input -> random -> random)
  (pR: random -> Prop)
  : relation pinput :=
  | pphi' :
    forall (inp1 inp2: input) (r1 r2: random),
      phi inp1 inp2 ->
      pR r1 ->
      r1 = bij inp1 inp2 r2 ->
      proba_phi phi bij pR (make_pinput inp1 r1) (make_pinput inp2 r2).

Definition phi_fNI
  (pub: public)
  (simShIdxs: SimShIdxs)
  (pR: random -> Prop)
  (bij: seq nat (* intprobes *) -> seq 'I_nshares (* outprobes *) -> input -> input -> random -> random)
  (intprobes: seq nat)
  (outprobes: seq 'I_nshares)
  : relation pinput :=
  proba_phi (phi_input pub simShIdxs intprobes outprobes) (bij intprobes outprobes) pR.

(* What we strictly need for the proof is forall x, p (f x) -> p x.
   The rest of the property is trivially carried from assumption to conclusion. *)
Definition bijective_on (T: Type) (f: T -> T) (p: T -> Prop) : Prop :=
  [/\ bijective f
    , forall x, p x -> p (f x)
    & forall x, p (f x) -> p x].

Definition get_outputshare {L: Language pinput poutput} (output: poutput) (i: 'I_nshares)
  : share :=
  tnth (outshares output) i.

(* parametric f-NI notion that encompasses t-NI and t-SNI when provided the respective `f`. *)
Definition f_non_interfering
  {L: Language pinput poutput}
  (f: pfun)
  (pub: public)
  (simShIdxs: SimShIdxs)
  (p: prog (L := L))
  (pR: random -> Prop) :=
  sim_fNI f simShIdxs
  /\ (exists (bij: seq nat (* intprobes *) -> seq 'I_nshares (* outprobes *) -> input -> input -> random -> random),
         deterministic_sni (value := share) (get_outputshare := get_outputshare) (phi_fNI pub simShIdxs pR bij) p
         /\ forall intprobes outprobes inp1 inp2,
           bijective_on (bij intprobes outprobes inp1 inp2) pR).

(* Preservation of f-NI for two programs. *)
Definition preserves_fNI
  {f: pfun}
  (p_s: prog (L := Ls))
  (p_t: prog (L := Lt))
  (pub: public)
  (simShIdxs_s: SimShIdxs)
  (pR: random -> bool) :=
  f_non_interfering f pub simShIdxs_s p_s pR ->
  exists (simShIdxs_t: SimShIdxs),
    f_non_interfering f pub simShIdxs_t p_t pR.

(* Our main result: preserves_obs, correctness of compiler passes and constant-timeness of the source program
   is sufficient to prove that the f-NI security of the source program is preserved to the compiled program. *)
Lemma preserves_obs_fNI :
  forall (f: pfun) (p_s: prog (L := Ls)) (p_t: prog (L := Lt)) (simShIdxs_s: SimShIdxs) (ipub: public) (rnd_pR: random -> bool),
    compile p_s = Some p_t ->
    compile_correct (compile := compile) ->
    preserves_obs_w (compile := compile) (simT := simT) (simVIdx := simVIdx) (simV := simV) ->
    constant_time p_s (pinput_pubrnd ipub rnd_pR) ->
    preserves_fNI (f := f) p_s p_t ipub simShIdxs_s rnd_pR.
Proof.
  move => f p_s p_t simShIdxs_s ipub rnd_pR Hcompile Hccor Hpre Hct [] Hsims [] bij [] Hni_s Hbij.
  set (pR := pinput_pubrnd ipub rnd_pR) in *.
  pose phi x y := pR x /\ pR y.

  have Himpl: forall intprobes outprobes, rel_implies (phi_fNI ipub simShIdxs_s rnd_pR bij intprobes outprobes) phi.
  + move => intprobes outprobes inp1 inp2 Hni.
    unfold phi_fNI in Hni.
    case: Hni => inp inp' r1 r2 [] _ [] ? ? Hrnd_pR Hr.
    split; apply mkpinput; [done | split; [done|]].
    case: (Hbij intprobes outprobes inp inp') => _ _ -> //.
    by rewrite -Hr.

  have HpR_phi: forall inp : pinput, any_rel phi inp -> pR inp by move => inp [] inp' [] [].
  have Hct': constant_time p_s (any_rel phi) by apply (constant_time_impl HpR_phi Hct).
  move: (preserves_obs_detsni Hcompile Hccor Hpre Himpl Hct' Hni_s) => [] Tprobe /= Hni_t.

  pose simShIdxs_t inpub i_t := simShIdxs_s inpub (map Tprobe i_t).
  have Hsim: forall inp1 i_t, (simShIdxs_s ipub [seq Tprobe i | i <- i_t]) = simShIdxs_t ipub i_t.
  + by rewrite /simShIdxs_t /=.
  exists simShIdxs_t.
  split.
  + rewrite  /simShIdxs_t => pub probes Hprobes.
    specialize (Hsims pub ([seq Tprobe i | i <- probes])). rewrite size_map in Hsims. apply (Hsims Hprobes).
  + exists (fun probes => (bij (map Tprobe probes))).
    split => [//|i].
    by apply Hbij.
Qed.

(* -------------------------------------------------------------------------- *)
(* Concrete instantiations for t-NI                                           *)
(* -------------------------------------------------------------------------- *)

(* NI: f(ti,to) := ti + to *)
Definition f_NI : nat -> nat -> nat := fun ti to => (ti + to)%N.

(* A t-NI simulator is a f-NI simulator specialized to `f_NI` *)
Definition sim_tNI
  (simShIdxs: SimShIdxs) : Prop :=
  sim_fNI f_NI simShIdxs.

(* Prove that this is equivalent to the expected form by spelling it out *)
Lemma sim_tNI_derived_as_expected (simShIdxs : SimShIdxs) :
  sim_tNI simShIdxs =
    (forall pub intprobes outprobes,
        (size intprobes + size outprobes <= t)%N ->
        let shares_inp := simShIdxs pub intprobes outprobes in
        all (fun shares =>
               (size shares <= (size intprobes + size outprobes))%N) shares_inp).
Proof. by reflexivity. Qed.

Definition preserves_tNI :=
  [eta preserves_fNI (f := f_NI)].

(* Now prove the obvious: if f-NI is preserved, i.e., `preserves_fNI`, then the specific instance for f := t-NI is preserved as well. *)
Lemma preserves_fNI_includes_tNI :
  forall
    (p_s: prog (L := Ls))
    (p_t: prog (L := Lt))
    (pub: public)
    (simShIdxs_s: SimShIdxs)
    (pR: random -> bool),
    (forall f, preserves_fNI (f := f) p_s p_t pub simShIdxs_s pR) ->
    preserves_tNI p_s p_t pub simShIdxs_s pR.
Proof.
  intros ? ? ? ? ? Hpfni.
  by specialize (Hpfni f_NI).
Qed.

(* -------------------------------------------------------------------------- *)
(* Concrete instantiations for t-SNI                                          *)
(* -------------------------------------------------------------------------- *)

(* SNI: f(ti,to) := ti *)
Definition f_SNI : nat -> nat -> nat := fun ti _to => ti.

(* A t-SNI simulator is a f-NI simulator specialized to `f_SNI` *)
Definition sim_tSNI
  (simShIdxs: SimShIdxs) : Prop :=
  sim_fNI f_SNI simShIdxs.

(* Prove that this is equivalent to the expected form by spelling it out *)
Lemma sim_tSNI_derived_as_expected (simShIdxs : SimShIdxs) :
  sim_tSNI simShIdxs =
    (forall pub intprobes outprobes,
        (size intprobes + size outprobes <= t)%N ->
        let shares_inp := simShIdxs pub intprobes outprobes in
        all (fun shares => (size shares <= size intprobes)%N) shares_inp).
Proof. by reflexivity. Qed.

Definition preserves_tSNI :=
  [eta preserves_fNI (f := f_SNI)].

(* Now prove the obvious: if f-NI is preserved, i.e., `preserves_fNI`, then the specific instance for f := t-SNI is preserved as well. *)
Lemma preserves_fNI_includes_tSNI :
  forall
    (p_s: prog (L := Ls))
    (p_t: prog (L := Lt))
    (pub: public)
    (simShIdxs_s: SimShIdxs)
    (pR: random -> bool),
    (forall f, preserves_fNI (f := f) p_s p_t pub simShIdxs_s pR) ->
    preserves_tSNI p_s p_t pub simShIdxs_s pR.
Proof.
  intros ? ? ? ? ? Hpfni.
  by specialize (Hpfni f_SNI).
Qed.

End PROBABILISTIC_FNI.
