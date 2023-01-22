(** * Equidistribution theorems for cotrees, itrees, CF trees, and cpGCL. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Streams
  Basics
  List
  Morphisms
  Equality
  Lia
.

Import ListNotations.
Local Open Scope program_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From Paco Require Import paco.

From zar Require Import
  aCPO
  axioms
  compile
  cocwp
  cocwp_facts
  cotree
  cpo
  cwp
  cwp_tcwp
  debias
  itree
  misc
  mu
  order
  eR
  tactics
  tcwp
  tree
.

Local Open Scope eR_scope.

Definition Sigma01 : Type := cotree bool (list bool).

Definition measure (U : Sigma01) : eR :=
  tcosum (fun bs => 1 / 2 ^ length bs) U.

Fixpoint count {A} (P : A -> Prop) (l : list A) : nat :=
  match l with
  | [] => O
  | x :: xs => if classicT (P x) then S (count P xs) else count P xs
  end.

Inductive is_stream_prefix {A} : list A -> Stream A -> Prop :=
| is_stream_prefix_nil : forall s, is_stream_prefix [] s
| is_stream_prefix_cons : forall x l s,
    is_stream_prefix l s ->
    is_stream_prefix (x :: l) (Cons x s).

Definition freq {A} (P : A -> Prop) (l : list A) :=
  INeR (count P l) / INeR (length l).

Definition in_Sigma01 (U : Sigma01) (s : Stream bool) : Prop :=
  cotree_some (fun l => is_stream_prefix l s) U.

Definition uniform (bitstreams : nat -> Stream bool) : Prop :=
  forall U : Sigma01,
    cotree_disjoint U ->
    converges (freq (in_Sigma01 U) ∘ prefix bitstreams) (measure U).

Inductive produces {A} (P : A -> Prop) : Stream bool -> cotree bool A -> Prop :=
| produces_leaf : forall bs x, P x -> produces P bs (coleaf x)
| produces_tau : forall bs t, produces P bs t -> produces P bs (cotau t)
| produces_node : forall b bs k,
    produces P bs (k b) ->
    produces P (Cons b bs) (conode k).

Lemma list_rel_count {A B} (P : A -> Prop) (Q : B -> Prop) (l1 : list A) (l2 : list B) :
  list_rel (fun x y => P x <-> Q y) l1 l2 ->
  count P l1 = count Q l2.
Proof.
  induction 1; simpl; auto.
  repeat destruct_classic; auto.
  - apply H in p; congruence.
  - apply H in q; congruence.
Qed.

Lemma produces_in_sigma01 {A} (x : A) (bs : Stream bool) (P : A -> bool) (t : cotree bool A) :
  produces (eq x) bs t ->
  in_Sigma01 (cotree_preimage P t) bs <-> is_true (P x).
Proof.
  unfold in_Sigma01.
  induction 1; subst.
  - rewrite cotree_preimage_leaf.
    split.
    + intro Hsome.
      destruct (P x0); auto.
      apply co_elim in Hsome; eauto with cotree order.
      destruct Hsome as [i Hsome].
      destruct i; inv Hsome.
    + unfold is_true; intro HP.
      destruct (P x0); try congruence.
      apply co_intro with (S O); eauto with cotree order.
      constructor; constructor.
  - rewrite cotree_preimage_tau; auto.
  - rewrite cotree_preimage_node; split.
    + intro Hsome.
      apply co_elim in Hsome; eauto with cotree order.
      destruct Hsome as [i Hsome].
      apply IHproduces.
      apply atree_some_exists in Hsome.
      destruct Hsome as [l [H1 H2]].
      apply atree_some_exists in H1.
      destruct H1 as [l' [Hsome Hl]]; subst.
      inv H2.
      { destruct i; simpl in Hsome.
        - inv Hsome.
        - inv Hsome.
          unfold compose in H1. simpl in H1.
          rewrite tprefix_map in H1.
          apply atree_some_map in H1.
          unfold compose in H1.
          apply atree_some_exists in H1.
          destruct H1 as [l [H1 Heq]].
          inv Heq. }
      destruct i.
      { inv Hsome. }
      { simpl in Hsome; unfold flip in Hsome; simpl in Hsome.
        unfold compose in Hsome.
        inv Hsome.
        rewrite tprefix_map in H1.
        apply atree_some_map in H1.
        unfold compose in H1.
        apply atree_some_exists in H1.
        destruct H1 as [l' [Hsome Hl']].
        inv Hl'.
        eapply co_intro; eauto with cotree order.
        apply atree_some_exists; exists l'; split; eauto.
        apply Hsome. }
    + unfold is_true; intro HPx.
      unfold cotree_some.
      apply IHproduces in HPx.
      apply co_elim in HPx; eauto with cotree order.
      destruct HPx as [i Hi].
      apply co_intro with (S i); eauto with cotree order.
      simpl; unfold flip; simpl.
      econstructor.
      unfold compose.
      rewrite tprefix_map.
      apply atree_map_some.
      unfold compose.
      eapply atree_some_impl; try apply Hi.
      intros l Hl; constructor; auto.
Qed.

Record SamplingEnvironment : Type :=
  mkSampleEnvironment
    { bitstreams : nat -> Stream bool
    ; bitstreams_uniform : uniform bitstreams }.

Require Import cpGCL.

(** Cotree sampling theorem. *)
Section cotree_equidistribution.
  Context (env : SamplingEnvironment) (t : cotree bool St) (P : St -> bool).

  Variable samples : nat -> St.
  Hypothesis bitstreams_samples : forall i, produces (eq (samples i)) (env.(bitstreams) i) t.

  Lemma cotree_freq_bitstreams_samples (n : nat) :
    freq (in_Sigma01 (cotree_preimage P t)) (prefix env.(bitstreams) n) =
      freq (fun x : St => is_true (P x)) (prefix samples n).
  Proof.
    unfold freq; f_equal.
    2: { f_equal; rewrite 2!length_prefix; reflexivity. }
    f_equal; apply list_rel_count, list_rel_prefix.
    intro i; specialize (@bitstreams_samples i).
    apply produces_in_sigma01; auto.
  Qed.

  Theorem cotree_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (cotwp (fun s => if P s then 1 else 0) t).
  Proof.
    intros eps Heps.
    pose proof env.(bitstreams_uniform) as Huniform.
    specialize (Huniform _ (disjoint_cotree_preimage P t) _ Heps).
    destruct Huniform as [n0 Huniform].
    exists n0; intros n Hn; specialize (Huniform n Hn).
    unfold compose in *.
    rewrite cotwp_tcosum_preimage'.
    unfold measure in Huniform.
    rewrite <- cotree_freq_bitstreams_samples; apply Huniform.
  Qed.
End cotree_equidistribution.

(* Print Assumptions cotree_samples_equidistributed. *)

Inductive iproduces {A} (P : A -> Prop) : Stream bool -> itree boolE A -> Prop :=
| iproduces_leaf : forall bs x t,
    observe t = RetF x ->
    P x ->
    iproduces P bs t
| iproduces_tau : forall bs t t',
    observe t = TauF t' ->
    iproduces P bs t' ->
    iproduces P bs t
| iproduces_node : forall b bs t k,
    observe t = VisF GetBool k ->
    iproduces P bs (k b) ->
    iproduces P (Cons b bs) t.

Lemma iproduces_produces_icotree {A} (P : A -> Prop) bs (t : itree boolE A) :
  iproduces P bs t ->
  produces P bs (icotree t).
Proof.
  induction 1; rewrite unf_eq; simpl; rewrite H; constructor; auto.
Qed.

Corollary disjoint_itree_preimage {A} (P : A -> bool) (t : itree boolE A) :
  cotree_disjoint (itree_preimage P t).
Proof. apply disjoint_cotree_preimage. Qed.

(** ITree equidistribution theorem. *)
Section itree_equidistribution.
  Context (t : itree boolE St) (P : St -> bool)
    (bitstreams : nat -> Stream bool) (samples : nat -> St).

  Hypothesis bitstreams_uniform : uniform bitstreams.
  Hypothesis bitstreams_samples : forall i, iproduces (eq (samples i)) (bitstreams i) t.

  Lemma itree_freq_bitstreams_samples (n : nat) :
    freq (in_Sigma01 (itree_preimage P t)) (prefix bitstreams n) =
      freq (fun x : St => is_true (P x)) (prefix samples n).
  Proof.
    unfold freq; f_equal.
    2: { f_equal; rewrite 2!length_prefix; reflexivity. }
    f_equal; apply list_rel_count, list_rel_prefix.
    intro i; specialize (@bitstreams_samples i).
    apply produces_in_sigma01; auto.
    apply iproduces_produces_icotree; auto.
  Qed.

  Theorem itree_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (itwp (fun s => if P s then 1 else 0) t).
  Proof.
    intros eps Heps.
    pose proof bitstreams_uniform as Huniform.
    specialize (Huniform _ (@disjoint_itree_preimage _ P t) _ Heps).
    destruct Huniform as [n0 Huniform].
    exists n0; intros n Hn; specialize (Huniform n Hn).
    unfold compose in *.
    erewrite itwp_cotwp.
    2: { apply itree_cotree_icotree. }
    rewrite cotwp_tcosum_preimage'.
    unfold measure in Huniform.
    rewrite <- itree_freq_bitstreams_samples; apply Huniform.
  Qed.
End itree_equidistribution.

Lemma itree_cotree_eq_iproduces_produces (P : St -> Prop)
  (it : itree boolE St) (ct : cotree bool St) (bs : Stream bool) :
  itree_cotree_eq it ct ->
  iproduces P bs it ->
  produces P bs ct.
Proof.
  intros H0 H1.
  revert H0.
  revert ct.
  induction H1; intros ct Heq; punfold Heq; inv Heq; try congruence.
  - obs_inv; constructor; auto.
  - obs_inv; constructor; dupaco; auto.
  - obs_inv; constructor; specialize (H2 b); dupaco; auto.
Qed.

Inductive aproduces {A} (P : A -> Prop) : Stream bool -> atree bool A -> Prop :=
| aproduces_leaf : forall bs x, P x -> aproduces P bs (aleaf x)
| aproduces_tau : forall bs t, aproduces P bs t -> aproduces P bs (atau t)
| aproduces_node : forall b bs k,
    aproduces P bs (k b) ->
    aproduces P (Cons b bs) (anode k).

Definition produces' {A} (P : A -> Prop) (bs : Stream bool) : cotree bool A -> Prop :=
  co (aproduces P bs).

#[global]
  Instance monotone_aproduces {A} (P : A -> Prop) bs
  : Proper (leq ==> leq) (aproduces P bs).
Proof.
  intro a; revert P bs; induction a; intros P bs b Hab Hp; inv Hab; inv Hp.
  - constructor; auto.
  - constructor; apply IHa; auto.
  - constructor; eapply H; eauto; apply H1.
Qed.
#[global] Hint Resolve monotone_aproduces : cotree.

Lemma produces'_tau {A} (P : A -> Prop) bs t :
  produces' P bs t ->
  produces' P bs (cotau t).
Proof.
  intro Ht; coelim Ht; eauto with cotree order.
  destruct Ht as [i Ht].
  apply co_intro with (S i); eauto with cotree order.
  constructor; auto.
Qed.

Lemma produces'_node {A} (P : A -> Prop) b bs k :
  produces' P bs (k b) ->
  produces' P (Cons b bs) (conode k).
Proof.
  intro Ht; coelim Ht; eauto with cotree order.
  destruct Ht as [i Ht].
  apply co_intro with (S i); eauto with cotree order.
  constructor; auto.
Qed.

Lemma atree_cotree_le_aproduces_produces {A} (P : A -> Prop) bs a b :
  atree_cotree_le a b ->
  aproduces P bs a ->
  produces P bs b.
Proof.
  revert P bs b; induction a;
    intros P bs b Hab Ha; inv Hab; inv Ha; constructor; eauto.
Qed.

Lemma produces_produces' {A} (P : A -> Prop) bs t :
  produces P bs t <-> produces' P bs t.
Proof.
  split.
  - induction 1.
    + apply co_intro with (S O); eauto with cotree order.
      constructor; auto.
    + apply produces'_tau; auto.
    + apply produces'_node; auto.
  - intro Ht; apply co_elim in Ht; eauto with cotree order.
    destruct Ht as [i Ht].
    eapply atree_cotree_le_aproduces_produces; eauto.
    apply atree_cotree_le_ideal; reflexivity.
Qed.

Lemma aproduces_bind {A B} (P : B -> Prop) bs (t : atree bool A) k :
  produces P bs (atree_cotree_bind k t) ->
  exists x bs' bs'', aproduces (eq x) bs' t /\ produces P bs'' (k x).
Proof.
  unfold atree_cotree_bind, cofold.
  revert P bs k; induction t; simpl; intros P bs k Ht.
  - inv Ht.
  - exists a, (Streams.const false), bs; split; auto.
    constructor; reflexivity.
  - inv Ht; apply IHt in H1.
    firstorder; repeat eexists; eauto; constructor; eauto.
  - inv Ht; apply H in H2.
    firstorder; repeat eexists; eauto; constructor; eauto.
Qed.

Lemma produces_bind {A B} (P : B -> Prop) bs (t : cotree bool A) k :
  produces P bs (cotree_bind t k) ->
  exists x bs' bs'', produces (eq x) bs' t /\ produces P bs'' (k x).
Proof.
  intro Hp.
  apply produces_produces' in Hp.
  unfold cotree_bind in Hp.
  apply co_coP in Hp; eauto with cotree order.
  unfold produces' in Hp.
  coelim Hp.
  2: { apply monotone_compose; eauto with cotree order.
       apply monotone_co; eauto with cotree. }
  2: { apply continuous_co; eauto with cotree order. }
  destruct Hp as [i Hi].
  unfold compose in Hi.
  apply produces_produces' in Hi.
  apply aproduces_bind in Hi.
  destruct Hi as [x [bs' [bs'' [Hi Hi']]]].
  exists x, bs', bs''; split; auto.
  eapply atree_cotree_le_aproduces_produces; eauto.
  apply atree_cotree_le_ideal; reflexivity.
Qed.

Lemma produces_impl {A} (P Q : A -> Prop) bs t :
  produces P bs t ->
  (forall x, P x -> Q x) ->
  produces Q bs t.
Proof. intros H HPQ; dependent induction H; constructor; auto. Qed.

Lemma produces_iter_n {A} (P : A -> Prop) bs t i :
  produces P bs (iter_n (cotree_iter_F (const t)) (const cobot) i tt) ->
  exists bs' : Stream bool, produces (cotuple (const False) P) bs' t.
Proof.
  revert P bs t; induction i; simpl; unfold const; intros P bs t Hp.
  { inv Hp. }
  unfold cotree_iter_F in Hp.
  apply produces_bind in Hp.
  destruct Hp as [[[]|a] [bs' [bs'' [Hp Hp']]]]; inv Hp'.
  - apply IHi in H1; destruct H1 as [bs''' H1]; eexists; eauto.
  - exists bs'; eapply produces_impl; eauto; intros [[]|b] Heq; inv Heq; auto.
Qed.

Lemma produces_iter {A} (P : A -> Prop) bs t :
  produces P bs (cotree_iter (const t) tt) ->
  exists bs', produces (cotuple (const False) P) bs' t.
Proof.
  intro Hp.
  apply produces_produces' in Hp.
  unfold cotree_iter in Hp.
  unfold iter in Hp.
  unfold produces' in Hp.
  rewrite dsup_apply_ext in Hp.
  2: { apply chain_directed, chain_iter_n';
       auto with cotree order; intro; constructor. }
  apply continuous_supP in Hp.
  2: { apply continuous_co; eauto with cotree order. }
  2: { apply chain_directed; intro i; generalize tt as u; apply leq_arrow.
       apply chain_iter_n'; eauto with cotree order; intro; constructor. }
  unfold compose in  Hp.
  apply dsup_elim in Hp.
  2: { apply monotone_directed.
       - intros i j Hij H.
         coelim H; eauto with cotree order.
         destruct H as [k Hk].
         apply co_intro with k; eauto with cotree order.
         eapply monotone_aproduces; eauto.
         apply monotone_ideal.
         generalize tt as u; apply leq_arrow.
         apply chain_leq; auto.
         apply chain_iter_n'; eauto with cotree order.
         constructor.
       - intros i j; exists (max i j); split; simpl; lia. }
  destruct Hp as [i Hi].
  apply produces_produces' in Hi.
  eapply produces_iter_n; eauto.
Qed.

Lemma produces_0_lt_cowlp {A} (P : A -> Prop) bs t :
  produces (cotuple (const False) P) bs t ->
  0 < cowlp (const 1) t.
Proof.
  unfold cowlp.
  induction 1.
  - destruct x as [[]|a].
    + inv H.
    + rewrite cotwlp_leaf; eRauto.
      intros [[]|b]; eRauto.
  - rewrite cotwlp_tau; auto; intros [[]|a]; eRauto.
  - rewrite cotwlp_node.
    2: { intros [[]|a]; eRauto. }
    apply eRlt_0_eRdiv; eRauto.
    destruct b.
    + apply eRlt_0_plus_r; auto.
    + apply eRlt_0_plus_l; auto.
Qed.

Lemma produces_to_cotree_0_lt_cowlp (P : St -> Prop) (bs : Stream bool) (t : tree) :
  produces P bs (to_cotree t) ->
  0 < cowlp (const 1) (to_cotree_open t).
Proof.
  unfold to_cotree, compose, tie_cotree, cotree_iter, cotree_iter_F.
  simpl; intro Hp; apply produces_iter in Hp.
  destruct Hp as [bs' Hbs]; eapply produces_0_lt_cowlp; eauto.
Qed.

(** CF tree equidistribution theorem. *)
Section tree_equidistribution.
  Context (env : SamplingEnvironment) (t : tree) (P : St -> bool).
  Hypothesis unbiased_t : tree_unbiased t.

  Variable samples : nat -> St.
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i) (to_itree t).

  Theorem tree_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (tcwp t (fun s => if P s then 1 else 0)).
  Proof.
    rewrite tcwp_cotcwp; auto.
    rewrite cocwp_cotwp_tie_cotree.
    2: { rewrite cofail_cowlp.
         apply eRminus_pos_lt; eRauto.
         specialize (@bitstreams_samples O).
         eapply itree_cotree_eq_iproduces_produces in bitstreams_samples.
         2: { apply to_itree_to_cotree. }
         eapply produces_to_cotree_0_lt_cowlp; eauto. }
    eapply cotree_samples_equidistributed; eauto.
    intro i; eapply itree_cotree_eq_iproduces_produces; eauto.
    unfold to_itree, compose, tie_itree, tie_cotree.
    apply itree_cotree_eq_iter; intros []; apply to_itree_open_to_cotree_open.
  Qed.
End tree_equidistribution.

(* Print Assumptions tree_samples_equidistributed. *)

(** cpGCL equidistribution theorem. *)
Section cpGCL_equidistribution.
  Context (env : SamplingEnvironment) (c : cpGCL) (st : St ) (P : St -> bool).
  Hypothesis wf_c : wf_cpGCL c.

  Variable samples : nat -> St.
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i) (cpGCL_to_itree c st).

  Theorem cpGCL_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (cwp c (fun s => if P s then 1 else 0) st).
  Proof.
    rewrite <- cwp_tcwp; auto.
    rewrite <- tcwp_elim_choices.
    2: { apply compile_wf; auto. }
    rewrite <- tcwp_debias.
    2: { apply wf_tree'_elim_choices, compile_wf; auto. }
    rewrite <- tcwp_opt.
    2: { apply wf_tree'_debias, wf_tree'_elim_choices, compile_wf; auto. }
    eapply tree_samples_equidistributed; eauto.
    apply tree_unbiased_opt, tree_unbiased_debias.
  Qed.
End cpGCL_equidistribution.

Print Assumptions cpGCL_samples_equidistributed.
