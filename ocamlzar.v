(** * Zar OCaml package constructions and proofs. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Streams Basics QArith String Lia Lqa List.
Local Open Scope program_scope.
Local Open Scope string_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From zar Require Import
  cotree cocwp cpo equidistribution eR findist itree misc order tactics
  tree tcwp uniform_Z.

Record SamplerPackage : Type :=
  mkSamplers 
    { coin_sampler : Q -> itree boolE bool
    ; die_sampler : Z -> itree boolE Z
    ; findist_sampler : list Z -> itree boolE Z }.

From zar Require Import cpGCL prelude.
Local Open Scope cpGCL_scope.

(** Biased coin. *)

Definition coin_itree (p : Q) : itree boolE bool :=
  to_itree (bernoulli_tree (Qred p)).

(** Uses cotwp_map in cocwp_facts.v. *)
Theorem coin_itree_correct (p : Q) :
  (0 <= p <= 1)%Q ->
  itwp (fun b : bool => if b then 1 else 0) (coin_itree p) = Q2eR p.
Proof.
  intros [H0 H1].
  unfold coin_itree.
  rewrite <- tcwp_itwp.
  - unfold tcwp.
    rewrite twlp_const_1_bernoulli_tree; eRauto.
    replace (Q2eR p) with (Q2eR (Qred p)).
    2: { apply Proper_Q2eR, Qred_correct. }
    apply bernoulli_tree_twp_p.
    + apply Qred_complete, Qred_correct.
    + rewrite Qred_correct; lra.
  - apply wf_tree_bernoulli_tree.
  - apply tree_unbiased_bernoulli_tree.
  - rewrite twlp_const_1_bernoulli_tree; eRauto.
Qed.

Section coin_equidistribution.
  Context (env : SamplingEnvironment) (samples : nat -> bool) (p : Q).
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i) (coin_itree p).

  Theorem coin_samples_equidistributed :
    converges (freq is_true ∘ prefix samples)
      (itwp (fun b : bool => if b then 1 else 0) (coin_itree p)).
  Proof.
    eapply itree_samples_equidistributed; eauto.
    destruct env; auto.
  Qed.
End coin_equidistribution.

Corollary coin_true_converges
  (env : SamplingEnvironment) (samples : nat -> bool) (p : Q) :
  (forall i, iproduces (eq (samples i)) (env.(bitstreams) i) (coin_itree p)) ->
  (0 <= p <= 1)%Q ->
  converges (freq is_true ∘ prefix samples) (Q2eR p).
Proof.
  intros Hsamples Hp.
  erewrite <- coin_itree_correct; eauto.
  eapply coin_samples_equidistributed; eauto.
Qed.

(** N-sided die *)

Definition die_itree (n : Z) : itree boolE Z :=
  to_itree (uniform_tree n).

Theorem die_itree_correct (n m : Z) :
  (0 <= m < n)%Z ->
  itwp (fun x : Z => if eqb m x then 1 else 0) (die_itree n) = 1 / IZeR n.
Proof.
  intros [H0 H1].
  unfold die_itree.
  rewrite <- tcwp_itwp.
  - unfold tcwp.
    rewrite twlp_const_1_uniform_tree; eRauto.
    replace (fun x : Z => if eqb m x then 1 else 0) with
      (fun x : Z => if eqb x m then 1 else 0).
    2: { ext z; rewrite Z.eqb_sym; auto. }
    apply twp_uniform_tree; lia.
  - apply wf_tree_uniform_tree.
  - apply tree_unbiased_uniform_tree.
  - rewrite twlp_const_1_uniform_tree; eRauto.
Qed.

Section die_equidistribution.
  Context (env : SamplingEnvironment)
    (P : Z -> bool) (samples : nat -> Z) (n : Z).
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i) (die_itree n).

  Theorem die_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (itwp (fun x => if P x then 1 else 0) (die_itree n)).
  Proof.
    eapply itree_samples_equidistributed; eauto; destruct env; auto.
  Qed.
End die_equidistribution.

Corollary die_eq_n_converges
  (env : SamplingEnvironment) (samples : nat -> Z) (n m : Z) :
  (forall i, iproduces (eq (samples i)) (env.(bitstreams) i) (die_itree n)) ->
  (0 <= m < n)%Z ->
  converges (freq (is_true ∘ eqb m) ∘ prefix samples) (1 / IZeR n).
Proof.
  intros Hsamples Hlt.
  erewrite <- die_itree_correct; eauto.
  eapply die_samples_equidistributed; eauto.
Qed.

(** Finite distribution. *)

Theorem findist_itree_correct (weights : list Z) (n : Z) :
  (0 <= n)%Z ->
  Forall (fun x => 0 <= x)%Z weights ->
  Exists (fun w => (0 < w)%Z) weights ->
  (Z.to_nat n < length weights)%nat ->
  itwp (fun x : Z => if eqb n x then 1 else 0) (findist_itree weights) =
    IZeR (nth (Z.to_nat n) weights Z0) / IZeR (list_sum_Z weights).
Proof.
  intros Hn Hall Hex Hlt.
  unfold findist_itree.
  rewrite <- tcwp_itwp.
  - apply findist_tree_correct; auto.
  - unfold findist_tree.
    constructor.
    + intros ?; eauto with tree.
    + intros []; constructor.
  - constructor.
    + intros ?; apply tree_unbiased_btree_to_tree.
    + intros []; constructor.
  - rewrite twlp_const_1_findist_tree; eRauto.
Qed.

Section findist_equidistribution.
  Context (env : SamplingEnvironment)
    (P : Z -> bool) (samples : nat -> Z) (weights : list Z).
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i)
           (findist_itree weights).

  Theorem findist_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (itwp (fun x => if P x then 1 else 0) (findist_itree weights)).
  Proof.
    eapply itree_samples_equidistributed; eauto.
    destruct env; auto.
  Qed.
End findist_equidistribution.

Corollary findist_eq_n_converges
  (env : SamplingEnvironment) (samples : nat -> Z) (weights : list Z) (n : Z) :
  (forall i, iproduces (eq (samples i)) (env.(bitstreams) i) (findist_itree weights)) ->
  (0 <= n)%Z ->
  Forall (fun x => 0 <= x)%Z weights ->
  Exists (fun w => (0 < w)%Z) weights ->
  (Z.to_nat n < length weights)%nat ->
  converges (freq (is_true ∘ eqb n) ∘ prefix samples)
    (IZeR (nth (Z.to_nat n) weights Z0) / IZeR (list_sum_Z weights)).
Proof.
  intros Hn Hsamples Hall Hex Hlt.
  erewrite <- findist_itree_correct; eauto.
  eapply findist_samples_equidistributed; eauto.
Qed.

(** Extraction. *)

From Coq Require Import ExtrOcamlBasic ExtrOcamlString.

Definition samplers : SamplerPackage :=
  mkSamplers coin_itree die_itree findist_itree.

(* Extraction "ocaml/zar/lib/samplers.ml" samplers. *)

(* From Coq Require Import ExtrHaskellBasic. *)
(* Extraction Language Haskell. *)
(* Extraction "haskell/zar/src/Samplers.hs" samplers. *)
