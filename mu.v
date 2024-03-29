(** Sigma01 sets as cotrees and the standard measure on them. *)

Set Implicit Arguments.

From Coq Require Import
  Basics
  Nat
  QArith
  Lra
  Lia
  List
  Equivalence
.
Import ListNotations.
Local Open Scope equiv_scope.
Local Open Scope program_scope.

From Coq Require Import
  Reals
  Raxioms
  Rpower
  FunctionalExtensionality
  ClassicalChoice
.

From zar Require Import
  aCPO
  cocwp
  cocwp_facts
  cotree
  cpo
  misc
  order
  R
  eR
  tactics
.

Local Open Scope eR_scope.

Create HintDb mu.

Definition asum {A} (f : A -> eR) : atree bool A -> eR :=
  fold 0 f id (fun f => f false + f true).

Definition tcosum {A} (f : A -> eR) : cotree bool A -> eR :=
  co (asum f).

#[export]
  Instance monotone_asum {A} (f : A -> eR) : Proper (leq ==> leq) (asum f).
Proof.
  apply monotone_fold.
  { intros; eRauto. }
  { apply monotone_id. }
  intros g g' Hg; apply eRplus_le_compat; apply Hg.
Qed.
#[export] Hint Resolve monotone_asum : mu.

Lemma tcosum_bot {A} (f : A -> eR) :
  tcosum f bot = 0.
Proof. apply co_fold_bot'. Qed.

Lemma tcosum_leaf {A} (f : A -> eR) (a : A) :
  tcosum f (coleaf a) = f a.
Proof. apply co_tfold_leaf'; eRauto. Qed.

Lemma tcosum_node {A} (f : A -> eR) (k : bool -> cotree bool A) :
  tcosum f (conode k) = tcosum f (k false) + tcosum f (k true).
Proof. 
  unfold tcosum, asum; rewrite co_fold_node'; eRauto.
  { apply monotone_id. }
  apply wcontinuous_sum; apply wcontinuous_apply.
Qed.

Definition atree_lang {A} : atree bool A -> cotree bool (list bool) :=
  fold cobot (const (coleaf [])) id (fun k => conode (fun b => cotree_map (cons b) (k b))).

Definition cotree_lang {A} : cotree bool A -> cotree bool (list bool) :=
  co atree_lang.

Definition cotree_preimage {A} (P : A -> bool) : cotree bool A -> cotree bool (list bool) :=
  cotree_lang ∘ cotree_filter P.

(** Computation lemmas for cotree_lang. *)

Lemma cotree_lang_bot {A} :
  @cotree_lang A cobot = cobot.
Proof.
  apply cotree_equ_eq.
  unfold cotree_lang, atree_lang.
  rewrite co_fold_bot; reflexivity.
Qed.

Lemma cotree_lang_leaf {A} (x : A) :
  cotree_lang (coleaf x) = coleaf [].
Proof.
  apply cotree_equ_eq.
  unfold cotree_lang, atree_lang.
  rewrite co_fold_leaf; try reflexivity; constructor.
Qed.

Lemma cotree_lang_tau {A} (t : cotree bool A) :
  cotree_lang (cotau t) = cotree_lang t.
Proof.
  apply cotree_equ_eq.
  unfold cotree_lang, atree_lang.
  rewrite co_fold_tau; try reflexivity; auto with order.
  2: { intros; constructor. }
  intros a b Hab; constructor; intro b'.
  apply leq_cotree_le.
  apply monotone_co; auto.
  apply monotone_atree_cotree_map.
Qed.

Lemma cotree_lang_node {A} (k : bool -> cotree bool A) :
  cotree_lang (conode k) =
    conode (fun b => cotree_map (cons b) (cotree_lang (k b))).
Proof.
  apply cotree_equ_eq.
  unfold cotree_lang, atree_lang.
  rewrite co_fold_node; try reflexivity; auto with order.
  intros ch Hch s Hs.
  unfold compose.
  apply conode_supremum.
  intro b; unfold flip.
  apply continuous_co.
  { apply monotone_atree_cotree_map. }
  { apply chain_directed; intro i; apply Hch. }
  { apply apply_supremum; auto. }
  { intros; constructor. }
  { constructor. }
Qed.

(** Computation lemmas for cotree_preimage. *)

Lemma cotree_preimage_bot {A} (P : A -> bool) :
  cotree_preimage P cobot = cobot.
Proof.
  apply cotree_equ_eq.
  unfold cotree_preimage, compose.
  rewrite cotree_filter_bot, cotree_lang_bot; reflexivity.
Qed.

Lemma cotree_preimage_leaf {A} (P : A -> bool) (x : A) :
  cotree_preimage P (coleaf x) = if P x then coleaf [] else cobot.
Proof.
  apply cotree_equ_eq.
  unfold cotree_preimage, compose.
  rewrite cotree_filter_leaf.
  destruct (P x).
  - rewrite cotree_lang_leaf; reflexivity.
  - rewrite cotree_lang_bot; reflexivity.
Qed.

Lemma cotree_preimage_tau {A} (P : A -> bool) (t : cotree bool A) :
  cotree_preimage P (cotau t) = cotree_preimage P t.
Proof.
  apply cotree_equ_eq.
  unfold cotree_preimage, compose.
  rewrite cotree_filter_tau, cotree_lang_tau; reflexivity.
Qed.

Lemma cotree_preimage_node {A} (P : A -> bool) (k : bool -> cotree bool A) :
  cotree_preimage P (conode k) =
    conode (fun b => cotree_map (cons b) (cotree_preimage P (k b))).
Proof.
  apply cotree_equ_eq.
  unfold cotree_preimage, compose.
  rewrite cotree_filter_node, cotree_lang_node; reflexivity.
Qed.

Lemma asum_scalar {A} (f : A -> eR) (t : atree bool A) (c : eR) :
  c * asum f t = asum (fun x => c * f x) t.
Proof.
  revert f c; induction t; intros f c; simpl; eRauto.
  unfold asum in *; simpl; unfold compose.
  rewrite eRmult_plus_distr_l; rewrite 2!H; reflexivity.
Qed.

Lemma atreeR_asum {A B} (f : A -> eR) (g : B -> eR) (R : A -> B -> Prop)
  (a : atree bool A) (b : atree bool B) :
  (forall x y, R x y -> f x = g y) ->
  atreeR R a b ->
  asum f a = asum g b.
Proof.
  intros Hfg Hab.
  revert Hfg; revert f g.
  induction Hab; intros f' g' Hfg.
  - reflexivity.
  - apply Hfg; auto.
  - apply IHHab; auto.
  - unfold asum in *; simpl; unfold compose; erewrite 2!H0; eauto.
Qed.

Lemma monotone_atree_lang {A} :
  monotone (@atree_lang A).
Proof.
  apply monotone_fold.
  { intros; constructor. }
  { apply monotone_id. }
  intros a b Hab.
  apply monotone_conode; intro x.
  apply monotone_co; auto; apply monotone_fold.
  { intros; constructor. }
  { apply monotone_cotau. }
  { apply monotone_conode. }
Qed.
#[export] Hint Resolve monotone_atree_lang : mu.

Theorem cotwp_mu_lang {A} :
  @cotwp A (const 1) = tcosum (fun bs => 1 / 2 ^ length bs) ∘ cotree_lang.
Proof
  with eauto with aCPO cocwp order mu.
  unfold cotwp, tcosum, cotree_lang.
  apply equ_f_eR.  
  rewrite co_co...
  apply Proper_co...
  { apply monotone_compose...
    apply monotone_co, monotone_asum. }
  unfold compose.
  apply equ_arrow; intro a.
  apply equ_eR.
  unfold btwp, asum.
  induction a; simpl.
  - unfold atree_lang; simpl; unfold asum.
    apply equ_eR; rewrite co_fold_bot; reflexivity.
  - unfold atree_lang, asum, const; simpl; apply equ_eR.
    rewrite co_fold_leaf; simpl; eRauto.
  - apply IHa.
  - unfold asum, atree_lang; simpl; apply equ_eR.
    rewrite co_fold_node; auto.
    2: { apply monotone_id. }
    2: { apply wcontinuous_sum; apply wcontinuous_apply. }
    2: { intros; eRauto. }
    2: { eRauto. }
    unfold compose.
    rewrite 2!H.
    rewrite <- eRplus_combine_fract.
    unfold atree_lang.
    assert (Heq: forall b, tcosum (fun bs => 1 / 2 ^ length bs) (atree_lang (a b)) / 2 =
                        tcosum (fun bs => 1 / 2 ^ length bs)
                          (cotree_map (cons b) (atree_lang (a b)))).
    { intro b; unfold tcosum, co, eRdiv.
      rewrite eRmult_comm.
      rewrite sup_scalar.
      f_equal; ext i.
      unfold compose.
      rewrite asum_scalar.
      apply atreeR_asum with
        (R := fun x y => cons b x = y).
      * intros bs bs' Hbs; simpl in *; subst; simpl.
        destr; try lra.
        rewrite eRmult_comm.
        rewrite eRmult_assoc.
        f_equal.
        rewrite eRinv_distr_mult; eRauto.
        rewrite eRmult_comm; f_equal.
        unfold eRinv.
        simpl.
        destr; try lra.
        apply eR_eq; lra.
      * unfold ideal; simpl; unfold flip.
        rewrite tprefix_map.
        apply atreeR_map. }
    unfold tcosum in Heq.
    unfold compose.
    unfold atree_lang in Heq.
    rewrite 2!Heq; reflexivity.
  - apply continuous_wcontinuous, continuous_co, monotone_asum.
Qed.

Theorem cotwp_tcosum_preimage {A} (P : A -> bool) :
  cotwp (fun x => if P x then 1 else 0) ===
    tcosum (fun bs => 1 / 2 ^ length bs) ∘ cotree_preimage P.
Proof.
  rewrite cotwp_filter.
  unfold tcosum, cotree_preimage, cotree_lang, cotree_filter.
  rewrite <- Combinators.compose_assoc.
  apply Proper_compose_l.
  { apply Proper_monotone_equ, monotone_co, monotone_btwp. }
  { reflexivity. }
  rewrite cotwp_mu_lang; reflexivity.
Qed.

(* Pointwise variant. *)
Corollary cotwp_tcosum_preimage' {A} (P : A -> bool) (t : cotree bool A) :
  cotwp (fun x => if P x then 1 else 0) t =
    tcosum (fun bs => 1 / 2 ^ length bs) (cotree_preimage P t).
Proof.
  apply equ_eR; revert t; apply equ_arrow, cotwp_tcosum_preimage.
Qed.

Lemma incomparable_cons {A} (a : A) (b c : list A) :
  incomparable b c ->
  incomparable (a :: b) (a :: c).
Proof.
  unfold incomparable.
  intros Hinc []; inv H; apply Hinc.
  - left; auto.
  - right; auto.
Qed.

Lemma itree_all_incomparable_map_cons {A} (t : atree bool (list A)) l a :
  atree_all (incomparable l) t ->
  atree_all (incomparable (a :: l)) (atree_map (cons a) t).
Proof.
  unfold atree_all.
  revert l a; induction t; simpl; intros l b Hall.
  - constructor.
  - apply incomparable_cons; auto.
  - unfold id in *; eauto.
  - intros []; apply H, Hall.
Qed.

Lemma atree_pairwise_disjoint_map {A} (t : atree bool (list A)) (a : A) :
  atree_pairwise_disjoint t ->
  atree_pairwise_disjoint (atree_map (cons a) t).
Proof.
  revert a; induction t; intros a' Hdisj; simpl; inv Hdisj; constructor; auto.
  - intro b; apply H; auto.
  - destruct H2 as [Ht Hf]; split; apply atree_all_map; unfold compose;
      eapply atree_all_impl; eauto; intro;
      apply itree_all_incomparable_map_cons; auto.
Qed.

Lemma atree_pairwise_disjoint_lang {A} (t : atree bool A) (i : nat ) :
  atree_pairwise_disjoint (ideal (atree_lang t) i).
Proof.
  revert i; induction t; intros i.
  - destruct i; constructor.
  - destruct i; constructor.
  - auto.
  - destruct i.
    + constructor.
    + simpl; unfold flip; simpl.
      constructor.
      * intro b; unfold compose.
        specialize (H b i).
        unfold ideal in H; simpl in H; unfold flip in H.
        rewrite tprefix_map.
        apply atree_pairwise_disjoint_map; auto.
      * unfold compose.
        rewrite 2!tprefix_map.
        split; apply atree_all_map, atree_all_true'; intro bs;
          apply atree_all_map, atree_all_true';
          intros bs' [HC|HC]; inv HC; congruence.
Qed.

Theorem pairwise_disjoint_cotree_preimage {A} (P : A -> bool) (t : cotree bool A) :
  cotree_pairwise_disjoint (cotree_preimage P t).
Proof with eauto with cotree order mu aCPO.
  unfold cotree_disjoint, cotree_preimage, compose, cotree_filter, cotree_lang.
  apply co_coopP...
  cointro.
  { apply monotone_antimonotone_compose... }
  intro i; cointro...
  intro j; cointro...
  apply atree_pairwise_disjoint_lang.
Qed.
