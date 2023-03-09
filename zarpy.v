(** * Zarpy package constructions and proofs. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Streams Basics QArith String Lia Lqa.
Local Open Scope program_scope.
Local Open Scope string_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From zar Require Import
  compile cotree cocwp cpo cwp equidistribution eR misc itree order tactics tree.

Record Samplers : Type :=
  mkSamplers 
    { coin_sampler : Q -> itree boolE bool
    ; die_sampler : nat -> itree boolE nat }.

From zar Require Import cpGCL.
Local Open Scope cpGCL_scope.

Require Import prelude.

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
Theorem coin_correct (out : string) (p : Q) :
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

(** N-sided die *)

Definition die (out : string) (n : nat) : cpGCL :=
  CUniform (const n) (fun m => out <-- m).

Lemma wf_die (out : string) (n : nat) :
  (0 < n)%nat ->
  wf_cpGCL (die out n).
Proof. intro Hlt; repeat constructor; auto. Qed.

(** The probability of assigning any m < n to the output variable is
    equal to 1/n. *)
Theorem die_correct (out : string) (n m : nat) :
  (m < n)%nat ->
  cwp (die out n) (fun s => if Nat.eqb (as_nat (s out)) m then 1 else 0) empty =
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
  destruct (Nat.eqb_spec n m); subst.
  - rewrite sum_map_count.
    rewrite Forall_not_in_countb_list_0.
    + rewrite INeR_0; eRauto.
    + apply List_forall_neq_range.
  - rewrite IHn; eRauto; lia.
Qed.

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

(** Extraction. *)

From Coq Require Import ExtrOcamlBasic ExtrOcamlString.

(* Definition coin_sampler (p : Q) : itree boolE bool := *)
(*   ITree.map (fun s => as_bool (s "b")) (cpGCL_to_itree (coin "b" p) empty). *)

(* Definition die_sampler (n : nat) : itree boolE nat := *)
(*   ITree.map (fun s => as_nat (s "n")) (cpGCL_to_itree (die "n" n) empty). *)

(* Definition samplers : Samplers := *)
(*   {| coin_sampler := *)
(*       ITree.map (fun s => as_bool (s "b")) (cpGCL_to_itree (coin "b" p) empty) *)
(*    ; die_sampler := *)
(*       ITree.map (fun s => as_nat (s "n")) (cpGCL_to_itree (die "n" n) empty) |}. *)

Definition coin_die_samplers : Samplers :=
  mkSamplers
    (fun p => ITree.map (fun s => as_bool (s "b")) (cpGCL_to_itree (coin "b" p) empty))
    (fun n => ITree.map (fun s => as_nat (s "n")) (cpGCL_to_itree (die "n" n) empty)).

Extraction "extract/zarpy/samplers.ml" coin_die_samplers.
