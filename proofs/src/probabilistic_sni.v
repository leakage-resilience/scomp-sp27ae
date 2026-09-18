(* -------------------------------------------------------------------------- *)
(* Preservation of the Strong Non-Interference Notion                         *)
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

Section PROBABILISTIC_SNI.

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
  {t: nat} (* Security order *)
.

(* `SimShIdxs` returns the shares (for each input separately) required for simulating a given set of probes.
   This may depend on the public inputs since we require programs to be constant-time. *)
Definition SimShIdxs :=
  public ->
  seq nat (* input and internal probe positions *) ->
  seq 'I_nshares (* output probe positions *) ->
  ninputs.-tuple (seq 'I_nshares).

(* The simulator is partial, for a total of at most `t` probes to simulate it
   requires at most as many shares as internal probes to simulate. *)
Definition sim_tSNI (simShIdxs: SimShIdxs) :=
  forall pub intprobes outprobes,
    (size intprobes + size outprobes <= t)%N ->
    let shares_inp := simShIdxs pub intprobes outprobes in
    all (fun shares => (size shares <= size intprobes)%N) shares_inp.

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

Definition phi_tSNI
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
  [/\ bijective f, forall x, p x -> p (f x) & forall x, p (f x) -> p x].

Definition get_outputshare {L: Language pinput poutput} (output: poutput) (i: 'I_nshares)
  : share :=
  tnth (outshares output) i.

(* masking t-SNI *)
Definition shares_tsni
  {L: Language pinput poutput}
  (pub: public)
  (simShIdxs: SimShIdxs)
  (p: prog (L := L))
  (pR: random -> Prop) :=
  sim_tSNI simShIdxs /\
    exists (bij: seq nat (* intprobes *) -> seq 'I_nshares (* outprobes *) -> input -> input -> random -> random),
      deterministic_sni (value := share) (get_outputshare := get_outputshare) (phi_tSNI pub simShIdxs pR bij) p /\
      forall intprobes outprobes inp1 inp2,
        bijective_on (bij intprobes outprobes inp1 inp2) pR.

Definition preserves_tSNI
  (p_s: prog (L := Ls)) (p_t: prog (L := Lt))
  (pub: public)
  (simShIdxs_s: SimShIdxs)
  (pR: random -> bool) :=
  shares_tsni pub simShIdxs_s p_s pR ->
  exists (simShIdxs_t: SimShIdxs),
    shares_tsni pub simShIdxs_t p_t pR.

Lemma preserves_obs_tSNI :
  forall (p_s: prog (L := Ls)) (p_t: prog (L := Lt)) (simShIdxs_s: SimShIdxs) (ipub: public) (rnd_pR: random -> bool),
    compile p_s = Some p_t ->
    compile_correct (compile := compile) ->
    preserves_obs_w (compile := compile) (simT := simT) (simVIdx := simVIdx) (simV := simV) ->
    constant_time p_s (pinput_pubrnd ipub rnd_pR) ->
    preserves_tSNI p_s p_t ipub simShIdxs_s rnd_pR.
Proof.
  move => p_s p_t simShIdxs_s ipub rnd_pR Hcompile Hccor Hpre Hct [] Hsims [] bij [] Hni_s Hbij.
  set (pR := pinput_pubrnd ipub rnd_pR) in *.
  pose phi x y := pR x /\ pR y.

  have Himpl: forall intprobes outprobes, rel_implies (phi_tSNI ipub simShIdxs_s rnd_pR bij intprobes outprobes) phi.
  + move => intprobes outprobes inp1 inp2 Hni.
    unfold phi_tSNI in Hni.
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

End PROBABILISTIC_SNI.
