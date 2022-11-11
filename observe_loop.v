(** * The geometric distribution program. *)

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

(** Negative binomial distribution with r=1. *)
Definition prog : cpGCL :=
  "n" <-- O;
  CUniform (const 6%nat) (fun m =>
    
    skip).

(* Lemma wf_geometric (p : Q) : *)
(*   (0 <= p <= 1)%Q -> *)
(*   wf_cpGCL (geometric p). *)
(* Proof. repeat constructor; unfold const; lra. Qed. *)

(* Section geometric_equidistribution. *)
(*   Context (env : SamplingEnvironment) (P : St -> bool) (samples : nat -> St). *)
(*   Context (p : Q) (Hp : (0 <= p <= 1)%Q). *)
(*   Hypothesis bitstreams_samples : *)
(*     forall i, iproduces (eq (samples i)) (env.(bitstreams) i) *)
(*            (cpGCL_to_itree (geometric p) empty). *)

(*   Theorem geometric_samples_equidistributed : *)
(*     converges (freq (is_true ∘ P) ∘ prefix samples) *)
(*       (cwp (geometric p) (fun s => if P s then 1 else 0) empty). *)
(*   Proof. *)
(*     eapply cpGCL_samples_equidistributed; eauto; apply wf_geometric; auto. *)
(*   Qed. *)
(* End geometric_equidistribution. *)

(* (** Extracting the sampler. *) *)
(* From Coq Require Import ExtrOcamlBasic ExtrOcamlString. *)
(* Definition sampler : itree boolE nat := *)
(*   ITree.map (fun s => as_nat (s "n")) (cpGCL_to_itree (geometric (1#2)) empty). *)
(*   (* ITree.map (fun s => as_nat (s "n")) (cpGCL_to_itree (geometric (5#6)) empty). *) *)
(* Extraction "extract/geometric/geometric.ml" sampler. *)
