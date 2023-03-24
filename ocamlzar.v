(** * Zarpy package constructions and proofs. *)

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
  compile cotree cocwp cpo cwp equidistribution eR findist itree misc
  order tactics tree.

Record Samplers : Type :=
  mkSamplers 
    { coin_sampler : Q -> itree boolE bool
    ; die_sampler : nat -> itree boolE nat
    ; findist_sampler : list nat -> itree boolE nat }.

From zar Require Import cpGCL prelude.
Local Open Scope cpGCL_scope.

(** Biased coin. *)

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

Definition coin_itree (p : Q) : itree boolE bool :=
  ITree.map (fun s => as_bool (s "b")) (cpGCL_to_itree (coin "b" p) empty).

(** Uses cotwp_map in cocwp_facts.v. *)
Theorem coin_itree_correct (p : Q) :
  (0 <= p <= 1)%Q ->
  itwp (fun b : bool => if b then 1 else 0) (coin_itree p) = Q2eR p.
Proof.
  intros [H0 H1].
  unfold coin_itree; rewrite itwp_map.
  unfold compose; rewrite <- cwp_itwp.
  - apply coin_correct; auto.
  - apply wf_coin; auto.
  - unfold wlp; simpl; unfold const; eRauto.
Qed.

Section coin_equidistribution.
  Context (env : SamplingEnvironment) (samples : nat -> bool).
  Context (p : Q) (Hp : (0 <= p <= 1)%Q).
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

Definition die (out : string) (n : nat) : cpGCL :=
  CUniform (const n) (fun m => out <-- m).

Lemma wf_die (out : string) (n : nat) :
  (0 < n)%nat ->
  wf_cpGCL (die out n).
Proof. intro Hlt; repeat constructor; auto. Qed.

From zar Require Import tcwp cwp_tcwp uniform.

(** The probability of assigning any m < n to the output variable is
    equal to 1/n. *)
Lemma die_correct (out : string) (n m : nat) :
  (m < n)%nat ->
  cwp (die out n) (fun s => if eqb m (as_nat (s out)) then 1 else 0) empty =
    1 / INeR n.
Proof.
  intro Hn.
  unfold cwp, die, wp, wlp, const; simpl; eRauto.
  unfold upd; simpl.  
  rewrite String.eqb_refl; simpl.
  assert (H: sum (List.map (fun _ : nat => 1 / INeR n) (range n)) = 1).
  { rewrite sum_map_const with (c := 1 / INeR n).
    - rewrite range_length.
      unfold eRdiv.
      eRauto.
      rewrite eRinv_r; eRauto.
      destruct n.
      + inv Hn.
      + apply not_0_INeR; lia.
    - apply List.Forall_impl with (P := const True); auto.
      apply Forall_const_true. }
  rewrite H; clear H.
  eRauto.
  unfold eRdiv.
  rewrite sum_map_scalar_r.
  f_equal.
  induction n; simpl.
  { inv Hn. }
  rewrite List.map_app; simpl.
  rewrite sum_app; simpl; eRauto.
  destruct (Nat.eqb_spec m n); subst.
  - rewrite sum_map_count.
    rewrite Forall_not_in_countb_list_0.
    + rewrite INeR_0; eRauto.
    + apply List_forall_neq_range.
  - rewrite IHn; eRauto; lia.
Qed.

Definition die_itree (n : nat) : itree boolE nat :=
  ITree.map (fun s => as_nat (s "n")) (cpGCL_to_itree (die "n" n) empty).

Theorem die_itree_correct (n m : nat) :
  (m < n)%nat ->
  itwp (fun x : nat => if eqb m x then 1 else 0) (die_itree n) = 1 / INeR n.
Proof.
  intro Hlt.
  unfold die_itree; rewrite itwp_map.
  unfold compose; rewrite <- cwp_itwp.
  - apply die_correct; auto.
  - apply wf_die; auto; lia.
  - unfold wlp; simpl; unfold const.
    apply sum_positive.
    apply List.Exists_exists.
    exists (1 / INeR n); split.
    + set (f := fun _ : nat => 1 / INeR n).
      replace (1 / INeR n) with (f O); auto.
      apply List.in_map, in_range; lia.
    + apply eRlt_0_eRdiv; eRauto.
Qed.

Section die_equidistribution.
  Context (env : SamplingEnvironment) (P : nat -> bool) (samples : nat -> nat).
  Context (n : nat) (Hn : (0 < n)%nat).
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i) (die_itree n).

  Theorem die_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (itwp (fun x => if P x then 1 else 0) (die_itree n)).
  Proof.
    eapply itree_samples_equidistributed; eauto.
    destruct env; auto.
  Qed.
End die_equidistribution.

Corollary die_eq_n_converges
  (env : SamplingEnvironment) (samples : nat -> nat) (n m : nat) :
  (forall i, iproduces (eq (samples i)) (env.(bitstreams) i) (die_itree n)) ->
  (m < n)%nat ->
  converges (freq (is_true ∘ eqb m) ∘ prefix samples) (1 / INeR n).
Proof.
  intros Hsamples Hlt.
  erewrite <- die_itree_correct; eauto.
  eapply die_samples_equidistributed; eauto.
Qed.

(** Finite distribution. *)

Theorem findist_itree_correct (weights : list nat) (n : nat) :
  Exists (fun w => (0 < w)%nat) weights ->
  (n < length weights)%nat ->
  itwp (fun x : nat => if eqb n x then 1 else 0) (findist_itree weights) =
    INeR (nth n weights O) / INeR (list_sum weights).
Proof.
  intros Hex Hlt.
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
  Context (env : SamplingEnvironment) (P : nat -> bool) (samples : nat -> nat).
  Context (weights : list nat) (Hweights : Exists (fun w => (0 < w)%nat) weights).
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
  (env : SamplingEnvironment) (samples : nat -> nat) (weights : list nat) (n : nat) :
  (forall i, iproduces (eq (samples i)) (env.(bitstreams) i) (findist_itree weights)) ->
  Exists (fun w => (0 < w)%nat) weights ->
  (n < length weights)%nat ->
  converges (freq (is_true ∘ eqb n) ∘ prefix samples)
    (INeR (nth n weights O) / INeR (list_sum weights)).
Proof.
  intros Hsamples Hex Hlt.
  erewrite <- findist_itree_correct; eauto.
  eapply findist_samples_equidistributed; eauto.
Qed.

(** Extraction. *)

From Coq Require Import ExtrOcamlBasic ExtrOcamlString.

Definition coin_die_samplers : Samplers :=
  mkSamplers
    (fun p => ITree.map (fun s => as_bool (s "b"))
             (cpGCL_to_itree (coin "b" p) empty))
    (fun n => ITree.map (fun s => as_nat (s "n"))
             (cpGCL_to_itree (die "n" n) empty))
    findist_itree.

Extraction "extract/ocamlzar/samplers.ml" coin_die_samplers.
