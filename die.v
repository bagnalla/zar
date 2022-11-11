(** * Uniform die program. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Streams Basics QArith String Lqa.
Local Open Scope program_scope.
Local Open Scope string_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From zar Require Import
  compile cotree cotcwp cpGCL cpo cwp equidistribution eR misc itree order tactics tree.
Local Open Scope cpGCL_scope.

Require Import prelude.

(** Negative binomial distribution with r=1. *)
Definition die (out : string) (n : nat) : cpGCL :=
  CUniform (const n) (fun m => out <-- S m).

Lemma wf_die (out : string) (n : nat) :
  (0 < n)%nat ->
  wf_cpGCL (die out n).
Proof. intro Hlt; repeat constructor; auto. Qed.

Section die_equidistribution.
  Context (env : SamplingEnvironment) (P : St -> bool) (samples : nat -> St).
  Context (out : string) (n : nat) (Hn : (0 < n)%nat).
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i)
           (cpGCL_to_itree (die out n) empty).

  Theorem die_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (cwp (die out n) (fun s => if P s then 1 else 0) empty).
  Proof.
    eapply cpGCL_samples_equidistributed; eauto; apply wf_die; auto.
  Qed.
End die_equidistribution.

(* (** Extracting the sampler. *) *)
(* From Coq Require Import ExtrOcamlBasic ExtrOcamlString. *)
(* Definition sampler (n : nat) : itree boolE nat := *)
(*   ITree.map (fun s => as_nat (s "n")) (cpGCL_to_itree (die "n" n) empty). *)
(* Extraction "extract/die/sampler.ml" sampler. *)

(** Extracting the sampler. *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
Definition sampler (n : nat) : itree boolE nat :=
  ITree.map (fun s => as_nat (s "n")) (cpGCL_to_itree (die "n" n) empty).
Extraction "extract/uniform/sampler.ml" sampler.
