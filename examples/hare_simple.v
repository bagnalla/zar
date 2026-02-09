(** * Hare and tortoise without discrete gaussian. *)

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
  compile cotree cotcwp cpGCL cpGCLNotations cpo cwp debias equidistribution eR misc
  itree order tactics tree.
Local Open Scope cpGCL_scope.

Require Import prelude.

Definition hare_tortoise : cpGCL :=
  "h" <-- 0%nat;
  "t" <-- 5%nat;
  while (fun s => Nat.ltb (as_nat (s "h")) (as_nat (s "t"))) do
    incr "t";
    CUniform (const 3%nat) (fun n => "h" <-- (fun s => as_nat (s "h") + S n)%nat)
  end;
  obs (fun s => Nat.ltb 10%nat (as_nat (s "t"))).

Lemma wf_hare_tortoise : wf_cpGCL hare_tortoise.
Proof. repeat constructor. Qed.

Section hare_tortoise_equidistribution.
  Context (env : SamplingEnvironment) (P : St -> bool) (samples : nat -> St).
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i)
           (cpGCL_to_itree hare_tortoise empty).

  Theorem hare_tortoise_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (cwp hare_tortoise (fun s => if P s then 1 else 0) empty).
  Proof.
    eapply cpGCL_samples_equidistributed; eauto; apply wf_hare_tortoise; auto.
  Qed.
End hare_tortoise_equidistribution.

(** Extracting the sampler. *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
Definition sampler : itree boolE nat :=
  ITree.map (fun s => as_nat (s "t")) (cpGCL_to_itree hare_tortoise empty).
(* ITree.map (fun s => as_nat (s "n")) (cpGCL_to_itree (geometric (5#6)) empty). *)

Definition biased_tree : tree := elim_choices (compile hare_tortoise empty).
Definition unbiased_tree : tree := debias biased_tree.

Extraction "extract/hare_simple/hare.ml" biased_tree unbiased_tree sampler.
