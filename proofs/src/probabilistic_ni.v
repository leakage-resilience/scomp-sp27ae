(* -------------------------------------------------------------------------- *)
(* Preservation of Non-Interference Notions *)
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

Section PROBABILISTIC_NI.

Context
  {ninputs: nat} (* Number of encoded inputs, i.e., sharings, a gadget is taking *)
    {nshares: nat} (* Number of shares per encoded input a.k.a. sharing *)
    {share: eqType} (* A share within an encoding *)
    {rnd_item: predArgType} (* Randomness tape element *)
    {public: eqType} (* Public input *)
    {pinput: Type} (* Input of languages *)
    {poutput: Type} (* Output of languages *)
.

(* Randomness tape *)
Definition random := nat -> rnd_item.

(* a.k.a. (randomized) encoding *)
Definition sharing := nshares.-tuple share.

(* clarfication of `nshares`:
 a gadget taking shares a0, a1, a2 encoding secret value a and shares b0, b1, b2 encoding secret value b
 as input has `ninputs = 2` and `nshares = 3`
 *)

Record input := {
    shares : ninputs.-tuple sharing;
    pub : public;
  }.

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
  {t: nat} (* Security order *)
.

(* `SimShIdxs` returns the shares (for each input separately) required for simulating a given set of probes.
   This may depend on the public inputs since we require programs to be constant-time. *)
Definition SimShIdxs := public -> seq nat (* probe positions (outputs are probed as internal) *) -> ninputs.-tuple (seq 'I_nshares).

(* The simulator is partial, for at most `nshares-1` probes to simulate it
   requires at most as many shares as probes to simulate. *)
Definition sim_tNI (simShIdxs: SimShIdxs) :=
  forall pub probes,
    (size probes <= t)%N ->
    let shares_inp := simShIdxs pub probes in
    all (fun shares => (size shares <= size probes)%N) shares_inp.

(* `phi_input` holds iff the public values in inputs `inp1,inp2` are equal and additionally
   the subset of shares required for the simulation of `probes` (indicated by simShIdxs) agree in the inputs. *)
Definition phi_input (pub: public) (simShIdxs: SimShIdxs) (probes: seq nat) (inp1 inp2: input) :=
  eq_input pub (simShIdxs pub probes) inp1 inp2.

Variant pinput_make (pR: input -> random -> Prop): pinput -> Prop :=
  | mkpinput :
    forall (inp : input) (r : random),
      pR inp r -> pinput_make pR (make_pinput inp r).

Definition pinput_pubrnd (ipub: public) (rnd_pR: random -> bool) :=
  pinput_make (fun inp r => (pub inp) = ipub /\ rnd_pR r).

Definition rndmap := rnd_item -> rnd_item.
Definition rndtapemap := nat -> rndmap.
Definition rndtapemap2tapemap (map: nat -> rndmap) (tape: random): random :=
  fun i => map i (tape i).

Variant proba_phi
  (phi: relation input)
  (bij: input -> input -> rndtapemap)
  (pR: random -> Prop)
  : relation pinput :=
  | pphi' :
    forall (inp1 inp2: input) (r1 r2: random),
      phi inp1 inp2 ->
      pR r1 ->
      r1 = rndtapemap2tapemap (bij inp1 inp2) r2 ->
      proba_phi phi bij pR (make_pinput inp1 r1) (make_pinput inp2 r2).

Definition phi_tNI
  (pub: public)
  (simShIdxs: SimShIdxs)
  (pR: random -> Prop)
  (bij: seq nat (* probes *) -> input -> input -> rndtapemap)
  (probes: seq nat)
  : relation pinput :=
  proba_phi (phi_input pub simShIdxs probes) (bij probes) pR.

(* What we strictly need for the proof is forall x, p (f x) -> p x.
The rest of the property is trivially carried from assumption to conclusion.
*)
(*
Definition bijrnd (T: Type) (f: T -> T) (p: T -> Prop) : Prop :=
  [/\ bijective f, forall x, p x -> p (f x) & forall x, p (f x) -> p x].
*)

Definition bijrnd (f: rndtapemap) (p: random -> Prop) : Prop :=
  [/\
     forall i, bijective (f i),
     forall x, p x -> p ((rndtapemap2tapemap f) x) &
     forall x, p ((rndtapemap2tapemap f) x) -> p x
  ].

(* masking t-NI *)
Definition shares_tni
  {L: Language pinput poutput}
  (pub: public)
  (simShIdxs: SimShIdxs)
  (p: prog (L := L))
  (pR: random -> Prop) :=
  sim_tNI simShIdxs /\
  exists (bij: seq nat -> input -> input -> rndtapemap),
    deterministic_ni (phi_tNI pub simShIdxs pR bij) p /\
      forall probes inp1 inp2,
        bijrnd (bij probes inp1 inp2) pR.

Definition preserves_tNI
  (p_s: prog (L := Ls)) (p_t: prog (L := Lt))
  (pub: public)
  (simShIdxs_s: SimShIdxs)
  (pR: random -> bool) :=
  shares_tni pub simShIdxs_s p_s pR ->
  exists (simShIdxs_t: SimShIdxs),
    shares_tni pub simShIdxs_t p_t pR.

Lemma preserves_obs_tNI :
  forall (p_s: prog (L := Ls)) (p_t: prog (L := Lt)) (simShIdxs_s: SimShIdxs) (ipub: public) (rnd_pR: random -> bool),
    compile p_s = Some p_t ->
    preserves_obs (compile := compile) (simT := simT) (simVIdx := simVIdx) (simV := simV) ->
    constant_time p_s (pinput_pubrnd ipub rnd_pR) ->
    preserves_tNI p_s p_t ipub simShIdxs_s rnd_pR.
Proof.
  move => p_s p_t simShIdxs_s ipub rnd_pR Hcompile Hpre Hct [] Hsims [] bij [] Hni_s Hbij.
  set (pR := pinput_pubrnd ipub rnd_pR) in *.
  pose phi x y := pR x /\ pR y.

  have Himpl: forall probes, rel_implies (phi_tNI ipub simShIdxs_s rnd_pR bij probes) phi.
  + move => probes inp1 inp2 Hni.
    unfold phi_tNI in Hni.
    case: Hni => inp inp' r1 r2 [] _ [] ? ? Hrnd_pR Hr.
    split; apply mkpinput; [done | split; [done|]].
    case: (Hbij probes inp inp') => _ _ -> //.
    by rewrite -Hr.

  have HpR_phi: forall inp : pinput, any_rel phi inp -> pR inp by move => inp [] inp' [] [].
  have Hct': constant_time p_s (any_rel phi) by apply (constant_time_impl HpR_phi Hct).
  move: (preserves_obs_detni Hcompile (preserves_obs_of_fw Hpre) Himpl Hct' Hni_s) => [] Tprobe /= Hni_t.

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

End PROBABILISTIC_NI.
