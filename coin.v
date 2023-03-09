(** * Biased coin program. *)

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
  compile cotree cocwp cpGCL cpo cwp equidistribution eR misc itree order tactics tree.
Local Open Scope cpGCL_scope.

Require Import prelude.

Definition coin (out : string) (p : Q) : cpGCL :=
  CChoice (const p) (fun b => if b then out <-- true else out <-- false).

Lemma wf_coin (out : string) (p : Q) :
  (0 <= p <= 1)%Q ->
  wf_cpGCL (coin out p).
Proof.
  intros [H0 H1]; constructor; intro; auto.
  destruct b; constructor.
Qed.

(** The probability of assigning `true` to the output variable is
    equal to p. *)
Lemma coin_correct (out : string) (p : Q) :
  (p <= 1)%Q ->
  cwp (coin out p) (fun s => if as_bool (s out) then 1 else 0) empty = Q2eR p.
Proof.
  intro Hp.
  unfold cwp, coin, wp, wlp, const; simpl; eRauto.
  unfold upd; simpl.
  rewrite String.eqb_refl; simpl; eRauto.
Qed.

Section coin_equidistribution.
  Context (env : SamplingEnvironment) (P : St -> bool) (samples : nat -> St).
  Context (out : string) (p : Q) (Hp : (0 <= p <= 1)%Q).
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i)
           (cpGCL_to_itree (coin out p) empty).

  Theorem coin_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (cwp (coin out p) (fun s => if P s then 1 else 0) empty).
  Proof.
    eapply cpGCL_samples_equidistributed; eauto; apply wf_coin; auto.
  Qed.
End coin_equidistribution.

(** Extracting the sampler. *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
Definition sampler (p : Q) : itree boolE bool :=
  ITree.map (fun s => as_bool (s "b")) (cpGCL_to_itree (coin "b" p) empty).
Extraction "extract/coin/coin.ml" sampler.
