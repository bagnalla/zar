(** * The goldfish-piranha program. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Streams Basics QArith String Lqa.
Local Open Scope program_scope.
Local Open Scope string_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From cwp Require Import
  compile cotree cotcwp cpGCL cpo cwp equidistribution eR misc itree order tactics tree.
Local Open Scope cpGCL_scope.

Require Import prelude.

(** STATS:
  n:                   10000000
  # true:              6665372
  % true:              0.6665372
  time elapsed:        8.282017s
  avg time per sample: 8.282017e-07
  random bit total:    26663474
  avg bits per sample: 2.6663474
*)

(** The goldfish-piranha program. *)
Definition gp : cpGCL :=
  flip "f" (1#2);
  CChoice (const (1#2))
    (fun b => if b then 
             "r" <-- (fun s => s "f")
           else
             "r" <-- const true);
  obs (fun s => s "r").

(** Goldfish-piranha is a well-formed program. *)
Lemma wf_gp : wf_cpGCL gp.
Proof. repeat constructor; unfold const; try lra; intros []; constructor. Qed.

(** Goldfish-piranha equidistribution theorem. *)
Section gp_equidistribution.
  Context (env : SamplingEnvironment) (P : St -> bool) (samples : nat -> St).
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i) (cpGCL_to_itree gp empty).

  Theorem gp_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (cwp gp (fun s => if P s then 1 else 0) empty).
  Proof. eapply cpGCL_samples_equidistributed; eauto; apply wf_gp. Qed.
End gp_equidistribution.

(** Extracting the sampler. *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
Definition sampler : itree boolE bool :=
  ITree.map (fun s => as_bool (s "f")) (cpGCL_to_itree gp empty).
Extraction "extract/gp/gp.ml" sampler.

(* Definition gp_cotree : cotree bool bool := icotree sampler. *)
(* Definition gp_chain (n : nat) : atree bool bool := tprefix n gp_cotree. *)
(* Eval compute in (List.map (Qred ∘ btwpQ (fun b : bool => if b then 1%Q else 0%Q)) (misc.prefix gp_chain 30)). *)
