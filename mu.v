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
  misc
  order
  R
  eR
  tactics
.

Local Open Scope eR_scope.

Create HintDb mu.

Definition amu {A} (f : A -> eR) : atree bool A -> eR :=
  fold 0 f id (fun f => f false + f true).

Definition mu {A} (f : A -> eR) : cotree bool A -> eR :=
  co (amu f).

#[global]
  Instance monotone_amu {A} (f : A -> eR) : Proper (leq ==> leq) (amu f).
Proof.
  apply monotone_fold.
  { intros; eRauto. }
  { apply monotone_id. }
  intros g g' Hg; apply eRplus_le_compat; apply Hg.
Qed.
#[global] Hint Resolve monotone_amu : mu.

Definition atree_lang {A} : atree bool A -> cotree bool (list bool) :=
  fold cobot (const (coleaf [])) id (fun k => conode (fun b => cotree_map' (cons b) (k b))).

Definition cotree_lang {A} : cotree bool A -> cotree bool (list bool) :=
  co atree_lang.

Definition cotree_preimage {A} (P : A -> bool) : cotree bool A -> cotree bool (list bool) :=
  cotree_lang ∘ cotree_filter' P.

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
    conode (fun b => cotree_map' (cons b) (cotree_lang (k b))).
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
  rewrite cotree_filter'_bot, cotree_lang_bot; reflexivity.
Qed.

Lemma cotree_preimage_leaf {A} (P : A -> bool) (x : A) :
  cotree_preimage P (coleaf x) = if P x then coleaf [] else cobot.
Proof.
  apply cotree_equ_eq.
  unfold cotree_preimage, compose.
  rewrite cotree_filter'_leaf.
  destruct (P x).
  - rewrite cotree_lang_leaf; reflexivity.
  - rewrite cotree_lang_bot; reflexivity.
Qed.

Lemma cotree_preimage_tau {A} (P : A -> bool) (t : cotree bool A) :
  cotree_preimage P (cotau t) = cotree_preimage P t.
Proof.
  apply cotree_equ_eq.
  unfold cotree_preimage, compose.
  rewrite cotree_filter'_tau, cotree_lang_tau; reflexivity.
Qed.

Lemma cotree_preimage_node {A} (P : A -> bool) (k : bool -> cotree bool A) :
  cotree_preimage P (conode k) =
    conode (fun b => cotree_map' (cons b) (cotree_preimage P (k b))).
Proof.
  apply cotree_equ_eq.
  unfold cotree_preimage, compose.
  rewrite cotree_filter'_node, cotree_lang_node; reflexivity.
Qed.

Lemma amu_scalar {A} (f : A -> eR) (t : atree bool A) (c : eR) :
  c * amu f t = amu (fun x => c * f x) t.
Proof.
  revert f c; induction t; intros f c; simpl; eRauto.
  unfold amu in *; simpl; unfold compose.
  rewrite eRmult_plus_distr_l; rewrite 2!H; reflexivity.
Qed.

Lemma atreeR_amu {A B} (f : A -> eR) (g : B -> eR) (R : A -> B -> Prop)
  (a : atree bool A) (b : atree bool B) :
  (forall x y, R x y -> f x = g y) ->
  atreeR R a b ->
  amu f a = amu g b.
Proof.
  intros Hfg Hab.
  revert Hfg; revert f g.
  induction Hab; intros f' g' Hfg.
  - reflexivity.
  - apply Hfg; auto.
  - apply IHHab; auto.
  - unfold amu in *; simpl; unfold compose; erewrite 2!H0; eauto.
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
#[global] Hint Resolve monotone_atree_lang : mu.

Theorem cotwp_mu_lang {A} :
  @cotwp A (const 1) = mu (fun bs => 1 / 2 ^ length bs) ∘ cotree_lang.
Proof
  with eauto with aCPO cotcwp order mu.
  unfold cotwp, mu, cotree_lang.
  apply equ_f_eR.  
  rewrite co_co...
  apply Proper_co...
  { apply monotone_compose...
    apply monotone_co, monotone_amu. }
  unfold compose.
  apply equ_arrow; intro a.
  apply equ_eR.
  unfold btwp, amu.
  induction a; simpl.
  - unfold atree_lang; simpl; unfold amu.
    apply equ_eR; rewrite co_fold_bot; reflexivity.
  - unfold atree_lang, amu, const; simpl; apply equ_eR.
    rewrite co_fold_leaf; simpl; eRauto.
  - apply IHa.
  - unfold amu, atree_lang; simpl; apply equ_eR.
    rewrite co_fold_node; auto.
    2: { apply monotone_id. }
    2: { apply wcontinuous_sum; apply wcontinuous_apply. }
    2: { intros; eRauto. }
    2: { eRauto. }
    unfold compose.
    rewrite 2!H.
    rewrite <- eRplus_combine_fract.
    unfold atree_lang.
    assert (Heq: forall b, mu (fun bs => 1 / 2 ^ length bs) (atree_lang (a b)) / 2 =
                             mu (fun bs => 1 / 2 ^ length bs)
                               (cotree_map' (cons b) (atree_lang (a b)))).
    { intro b; unfold mu, co, eRdiv.
      rewrite eRmult_comm.
      rewrite sup_scalar.
      f_equal; ext i.
      unfold compose.
      rewrite amu_scalar.
      apply atreeR_amu with
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
    unfold mu in Heq.
    unfold compose.
    unfold atree_lang in Heq.
    rewrite 2!Heq; reflexivity.
  - apply continuous_wcontinuous, continuous_co, monotone_amu.
Qed.

Theorem cotwp_mu_preimage {A} (P : A -> bool) :
  cotwp (fun x => if P x then 1 else 0) ===
    mu (fun bs => 1 / 2 ^ length bs) ∘ cotree_preimage P.
Proof.
  rewrite cotwp_filter.
  unfold mu, cotree_preimage, cotree_lang, cotree_filter'.
  rewrite <- Combinators.compose_assoc.
  apply Proper_compose_l.
  { apply Proper_monotone_equ, monotone_co, monotone_btwp. }
  { reflexivity. }
  rewrite cotwp_mu_lang; reflexivity.
Qed.

(* Pointwise variant. *)
Corollary cotwp_mu_preimage' {A} (P : A -> bool) (t : cotree bool A) :
  cotwp (fun x => if P x then 1 else 0) t =
    mu (fun bs => 1 / 2 ^ length bs) (cotree_preimage P t).
Proof.
  apply equ_eR; revert t; apply equ_arrow, cotwp_mu_preimage.
Qed.

Lemma atree_disjoint_map {A} (t : atree bool (list A)) (a : A) :
  atree_disjoint t ->
  atree_disjoint (atree_map (cons a) t).
Proof.
  revert a; induction t; intros a' Hdisj; simpl; inv Hdisj; constructor; auto.
  - intro b; apply H; auto.
  - intros b b' Hneq bs Hsome.
    unfold compose in *.
    apply atree_some_map in Hsome.
    apply atree_all_map.
    destruct bs.
    { apply atree_some_exists in Hsome.
      destruct Hsome as [? [? HC]]; inv HC. }
    eapply H2 with (x:=bs) in Hneq.
    { eapply atree_all_impl.
      2: { apply Hneq. }
      intros bs' Hbs'; unfold compose.
      intros [HC|HC]; inv HC; auto. }
    eapply atree_some_impl.
    2: { apply Hsome. }
    intros bs' Hbs'.
    inv Hbs'; reflexivity.
Qed.

Lemma atree_disjoint_lang {A} (t : atree bool A) (i : nat ) :
  atree_disjoint (ideal (atree_lang t) i).
Proof.
  revert i; induction t; intros i.
  - destruct i; constructor.
  - destruct i; constructor.
  - apply IHt.
  - destruct i.
    + constructor.
    + simpl; unfold flip; simpl.
      constructor; intro b.
      * unfold compose.
        specialize (H b i).
        unfold ideal in H; simpl in H; unfold flip in H.
        rewrite tprefix_map.
        apply atree_disjoint_map; auto.
      * unfold compose; intros b' Hneq bs Hsome.
        rewrite tprefix_map in Hsome.
        rewrite tprefix_map.
        apply atree_some_map in Hsome.
        apply atree_all_map.
        apply atree_some_exists in Hsome.
        destruct Hsome as [bs' [Hsome Hbs']].
        unfold compose in Hbs'.
        inv Hbs'.
        clear H0.
        apply atree_all_impl with (const True).
        { intros bs _.
          unfold compose.
          unfold incomparable.
          intros [HC|HC]; inv HC; congruence. }
        apply atree_all_true.
Qed.

Theorem disjoint_cotree_preimage {A} (P : A -> bool) (t : cotree bool A) :
  cotree_disjoint (cotree_preimage P t).
Proof.
  unfold cotree_disjoint, cotree_preimage.
  unfold compose.
  unfold cotree_filter', cotree_lang.
  apply co_coopP; eauto with cotree order mu aCPO.
  { apply cocontinuous_coop; eauto with cotree order. }
  cointro.
  { apply monotone_antimonotone_compose; eauto with cotree order aCPO mu.
    apply antimonotone_coop; eauto with cotree order. }
  intro i.
  cointro; eauto with cotree order.
  intro j.
  cointro; eauto with cotree order.
  apply atree_disjoint_lang.
Qed.
