(** * The binomial distribution program. *)

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

Definition binomial (p : Q) (n : nat) : cpGCL :=
  "i" <-- O;
  "k" <-- O;
  while (fun s => Nat.ltb (as_nat (s "i")) n) do
    CChoice (const p) (fun b => if b then incr "k" else skip);
    incr "i"
  end.

Lemma wf_binomial (p : Q) (n : nat) :
  (0 <= p <= 1)%Q ->
  wf_cpGCL (binomial p n).
Proof. repeat constructor; unfold const; try lra; intros []; constructor. Qed.

Section binomial_equidistribution.
  Context (env : SamplingEnvironment) (P : St -> bool) (samples : nat -> St).
  Context (n : nat) (p : Q) (Hp : (0 <= p <= 1)%Q).
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i)
           (cpGCL_to_itree (binomial p n) empty).

  Theorem binomial_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (cwp (binomial p n) (fun s => if P s then 1 else 0) empty).
  Proof.
    eapply cpGCL_samples_equidistributed; eauto; apply wf_binomial; auto.
  Qed.
End binomial_equidistribution.

(** Extracting the sampler. *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
Definition sampler : itree boolE nat :=
  ITree.map (fun s => as_nat (s "n")) (cpGCL_to_itree (binomial (1#2) 8) empty).
Extraction "extract/binomial/binomial.ml" sampler.
