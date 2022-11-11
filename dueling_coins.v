(** * Dueling coins. *)

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

Definition dueling_coins (p : Q) : cpGCL :=
  "a" <-- false;
  "b" <-- false;
  while (fun s => Bool.eqb (as_bool (s "a")) (as_bool (s "b"))) do
    flip "a" p;
    flip "b" p
  end.

Lemma wf_dueling_coins (p : Q) :
  (0 <= p <= 1)%Q ->
  wf_cpGCL (dueling_coins p).
Proof. repeat constructor; unfold const; lra. Qed.

Section dueling_coins_equidistribution.
  Context (env : SamplingEnvironment) (P : St -> bool) (samples : nat -> St).
  Context (p : Q) (Hp : (0 <= p <= 1)%Q).
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i)
           (cpGCL_to_itree (dueling_coins p) empty).

  Theorem gp_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (cwp (dueling_coins p) (fun s => if P s then 1 else 0) empty).
  Proof.
    eapply cpGCL_samples_equidistributed; eauto; apply wf_dueling_coins; auto.
  Qed.
End dueling_coins_equidistribution.

(** Extracting the sampler. *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
Definition sampler : itree boolE bool :=
  ITree.map (fun s => as_bool (s "a")) (cpGCL_to_itree (dueling_coins (1#20)) empty).
Extraction "extract/dueling_coins/dueling_coins.ml" sampler.
