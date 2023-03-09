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

From zar Require Import
  compile cotree cpGCL cpo cwp equidistribution eR misc itree order tactics tree.
Local Open Scope cpGCL_scope.

Require Import prelude.

Definition binomial (x : string) (p : Q) (n : nat) : cpGCL :=
  "i" <-- O;
  x <-- O;
  while (fun s => Nat.ltb (as_nat (s "i")) n) do
    CChoice (const p) (fun b => if b then incr x else skip);
    incr "i"
  end.

Lemma wf_binomial (x : string) (p : Q) (n : nat) :
  (0 <= p <= 1)%Q ->
  wf_cpGCL (binomial x p n).
Proof. repeat constructor; unfold const; try lra; intros []; constructor. Qed.

Section binomial_equidistribution.
  Context (env : SamplingEnvironment) (P : St -> bool) (samples : nat -> St).
  Context (x : string) (n : nat) (p : Q) (Hp : (0 <= p <= 1)%Q).
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i)
           (cpGCL_to_itree (binomial x p n) empty).

  Theorem binomial_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (cwp (binomial x p n) (fun s => if P s then 1 else 0) empty).
  Proof.
    eapply cpGCL_samples_equidistributed; eauto; apply wf_binomial; auto.
  Qed.
End binomial_equidistribution.

(** Extracting the sampler. *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
Definition sampler : itree boolE nat :=
  ITree.map (fun s => as_nat (s "k")) (cpGCL_to_itree (binomial "k" (1#2) 8) empty).
Extraction "extract/binomial/binomial.ml" sampler.
