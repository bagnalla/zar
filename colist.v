(** * Coinductive lists (colists) algebraic CPO. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  Equivalence
  Lia
  Morphisms
  Equality
  List
  Nat
.
Local Open Scope program_scope.
Local Open Scope equiv_scope.
Import ListNotations.

From Coq Require Import
  Reals
  Raxioms
  Rpower
  FunctionalExtensionality
  ClassicalChoice
.

From zar Require Import aCPO axioms cpo misc order tactics.

Local Open Scope order_scope.

Create HintDb colist.

Inductive alist (A : Type) : Type :=
| anil : alist A
| atau : alist A -> alist A
| acons : A -> alist A -> alist A.

CoInductive colist (A : Type) : Type :=
| conil : colist A
| cotau : colist A -> colist A
| cocons : A -> colist A -> colist A.

Definition unf {A} (l : colist A) :=
  match l with
  | conil => conil
  | cotau l => cotau l
  | cocons x xs => cocons x xs
  end.

Lemma unf_eq {A} (l : colist A) : l = unf l.
Proof. destruct l; auto. Qed.

CoInductive colist_le {A} : colist A -> colist A -> Prop :=
| colist_le_conil : forall l, colist_le conil l
| colist_le_tau : forall l1 l2,
    colist_le l1 l2 ->
    colist_le (cotau l1) (cotau l2)
| colist_le_cocons : forall x l1 l2,
    colist_le l1 l2 ->
    colist_le (cocons x l1) (cocons x l2).

#[export]
  Instance Reflexive_colist_le {A} : Reflexive (@colist_le A).
Proof. cofix CH; intros []; constructor; eauto. Qed.

#[export]
  Instance Transitive_colist_le {A} : Transitive (@colist_le A).
Proof.
  cofix CH; intros x y z Hxy Hyz; inv Hxy.
  - constructor.
  - inv Hyz; constructor; eauto.
  - inv Hyz; constructor; eauto.
Qed.

#[export]
  Instance PreOrder_colist_le {A} : PreOrder (@colist_le A).
Proof. constructor; typeclasses eauto. Qed.

#[export]
  Instance OType_colist {A} : OType (colist A) :=
  { leq := colist_le }.

Lemma conil_le {A} (l : colist A) :
  conil ⊑ l.
Proof. constructor. Qed.

CoInductive colist_eq {A} : colist A -> colist A -> Prop :=
| colist_eq_nil : colist_eq conil conil
| colist_eq_tau : forall l l',
    colist_eq l l' ->
    colist_eq (cotau l) (cotau l')
| colist_eq_cons : forall x l l',
    colist_eq l l' ->
    colist_eq (cocons x l) (cocons x l').

(** Extensionality axiom for colists. *)
Axiom colist_ext : forall {A} (a b : colist A), colist_eq a b -> a = b.

Lemma colist_eq_refl {A} (t : colist A) :
  colist_eq t t.
Proof. revert t; cofix CH; intros []; constructor; eauto. Qed.

#[export]
  Instance Reflexive_colist_eq {A} : Reflexive (@colist_eq A).
Proof. intro t; apply colist_eq_refl. Qed.

Lemma colist_eq_equ {A} (a b : colist A) :
  colist_eq a b -> a === b.
Proof.
  intro Hab; split; revert Hab; revert a b; cofix CH;
    intros a b Hab; inv Hab; constructor; apply CH; auto.
Qed.

Lemma equ_colist_eq {A} (a b : colist A) :
  a === b -> colist_eq a b.
Proof.
  revert a b; cofix CH; intros a b [Hab Hba].
  inv Hab; inv Hba; constructor; apply CH; split; auto.
Qed.

#[export]
  Instance ExtType_colist {A} : ExtType (colist A).
Proof.
  constructor; intros a b Hab; apply colist_ext, equ_colist_eq; auto.
Qed.

Fixpoint prefix {A} (n : nat) (l : colist A) : alist A :=
  match n with
  | O => anil
  | S n' => match l with
           | conil => anil
           | cotau l' => atau (prefix n' l')
           | cocons x xs => acons x (prefix n' xs)
           end
  end.

Fixpoint coprefix {A} (n : nat) (l : colist A) : colist A :=
  match n with
  | O => conil
  | S n' => match l with
           | conil => conil
           | cotau l' => cotau (coprefix n' l')
           | cocons x xs => cocons x (coprefix n' xs)
           end
  end.

#[export]
  Instance Proper_colist_le {A} : Proper (equ ==> equ ==> flip impl) (@colist_le A).
Proof.
  intros a b [Hab Hba] c d [Hcd Hdc] Hle.
  etransitivity; eauto; etransitivity; eauto.
Qed.

#[export]
  Instance Proper_colist_le' {A}
  : Proper (colist_eq ==> colist_eq ==> flip impl) (@colist_le A).
Proof.
  intros a b Hab c d Hcd Hle.
  apply colist_eq_equ in Hab; destruct Hab.
  apply colist_eq_equ in Hcd; destruct Hcd.
  etransitivity; eauto; etransitivity; eauto.
Qed.

Lemma continuous_cocons {A} (a : A) : continuous (cocons a).
Proof.
  intros ch Hch s Hs; split.
  - intro i; constructor; apply Hs.
  - intros x Hx.
    destruct x; try solve [specialize (Hx (S O)); inv Hx].
    pose proof Hx as Hx'.
    specialize (Hx' (S O)).
    inv Hx'.
    constructor; apply Hs.
    intro i; specialize (Hx i); inv Hx; auto.
Qed.
#[export] Hint Resolve continuous_cocons : colist.

Inductive alist_le {A} : alist A -> alist A -> Prop :=
| alist_le_conil : forall l, alist_le anil l
| alist_le_tau : forall l1 l2,
    alist_le l1 l2 ->
    alist_le (atau l1) (atau l2)
| alist_le_cocons : forall x l1 l2,
    alist_le l1 l2 ->
    alist_le (acons x l1) (acons x l2).

#[export]
  Instance Reflexive_alist_le {A} : Reflexive (@alist_le A).
Proof. intro l; induction l; constructor; auto. Qed.

#[export]
  Instance Transitive_alist_le {A} : Transitive (@alist_le A).
Proof.
  intro a; induction a; intros b c Hab Hbc.
  - constructor.
  - inv Hab; inv Hbc; constructor; eapply IHa; eauto.
  - inv Hab; inv Hbc; constructor; eapply IHa; eauto.
Qed.

#[export]
  Instance PreOrder_alist_le {A} : PreOrder (@alist_le A).
Proof. constructor; typeclasses eauto. Qed.

#[export]
  Instance OType_alist {A} : OType (alist A) :=
  { leq := alist_le }.

Lemma nil_le {A} (l : alist A) :
  anil ⊑ l.
Proof. constructor. Qed.

#[export]
  Instance ExtType_alist {A} : ExtType (alist A).
Proof.
  constructor; intro a; induction a; intros b [H0 H1]; inv H0; inv H1; auto.
  - f_equal; apply IHa; split; auto.
  - f_equal; apply IHa; split; auto.
Qed.

Lemma prefix_monotone {A} (n : nat) :
  monotone (@prefix A n).
Proof.
  induction n; intros a b Hab; simpl; try constructor.
  destruct a; inv Hab; constructor; apply IHn; auto.
Qed.

Lemma prefix_monotone' {A} (l : colist A) :
  monotone (fun n => prefix n l).
Proof.
  intro i; revert l; induction i; intros l j Hij; simpl.
  - constructor.
  - destruct l.
    + constructor.
    + destruct j; simpl.
      * inv Hij.
      * constructor; apply IHi; inv Hij.
        { reflexivity. }
        simpl; lia.
    + destruct j; simpl.
      * inv Hij.
      * constructor; apply IHi; inv Hij.
        { reflexivity. }
        simpl; lia.
Qed.

Lemma chain_prefix {A} (l : colist A) :
  chain (fun n : nat => prefix n l).
Proof.
  apply monotone_chain.
  - apply prefix_monotone'.
  - intro i; simpl; lia.
Qed.

Lemma supremum_conil {A} (ch : nat -> colist A) :
  supremum conil ch ->
  ch = const conil.
Proof.
  intros [Hub Hlub]; ext i; unfold const.
  specialize (Hub i); inv Hub; reflexivity.
Qed.

Definition not_conil {A} (l : colist A) : Prop :=
  match l with
  | conil => False
  | _ => True
  end.

Definition not_anil {A} (l : alist A) : Prop :=
  match l with
  | anil => False
  | _ => True
  end.

Lemma not_conil_dec {A} (t : colist A) : { not_conil t } + { ~ not_conil t }.
Proof.
  destruct t.
  - right; intro HC; inv HC.
  - left; constructor.
  - left; constructor.
Qed.

Lemma not_anil_dec {A} (t : alist A) : { not_anil t } + { ~ not_anil t }.
Proof.
  destruct t.
  - right; intro HC; inv HC.
  - left; constructor.
  - left; constructor.
Qed.

Definition step {A} (l : colist A) : colist A :=
  match l with
  | conil => conil
  | cotau xs => xs
  | cocons _ xs => xs
  end.

Definition lstep {A} (l : alist A) : alist A :=
  match l with
  | anil => anil
  | atau xs => xs
  | acons _ xs => xs
  end.

(** The supremum of a chain of colists. Uses strong LPO. *)
CoFixpoint colist_sup {A} (ch : nat -> colist A) : colist A :=
  match LPO_option (fun n => not_conil_dec (ch n)) with
  | Some n => match ch n with
             | conil => conil
             | cotau _ => cotau (colist_sup (step ∘ ch))
             | cocons x xs => cocons x (colist_sup (step ∘ ch))
             end
  | None => conil
  end.

Lemma chain_step {A} (ch : nat -> colist A) :
  chain ch ->
  chain (step ∘ ch).
Proof.
  intros Hch i; unfold compose; simpl.
  destruct (ch i) eqn:Hchi; simpl; try constructor.
  - specialize (Hch i); rewrite Hchi in Hch; inv Hch; simpl; auto.
  - specialize (Hch i); rewrite Hchi in Hch; inv Hch; simpl; auto.
Qed.

#[export]
  Instance monotone_step {A} : Proper (leq ==> leq) (@step A).
Proof.
  intro a; revert a; cofix CH; intros x b Hab; inv Hab; auto; constructor.
Qed.

#[export]
  Instance monotone_lstep {A} : Proper (leq ==> leq) (@lstep A).
Proof.
  intro a; induction a; intros b Hab; inv Hab; simpl; auto; constructor.
Qed.

Lemma directed_step {A} (ch : nat -> colist A) :
  directed ch ->
  directed (step ∘ ch).
Proof.
  intros Hch i j; unfold compose; simpl.
  specialize (Hch i j); destruct Hch as [k [H0 H1]].
  exists k; split; apply monotone_step; auto.
Qed.

Lemma directed_lstep {A} (ch : nat -> alist A) :
  directed ch ->
  directed (lstep ∘ ch).
Proof.
  intros Hch i j; unfold compose; simpl.
  specialize (Hch i j); destruct Hch as [k [H0 H1]].
  exists k; split; apply monotone_lstep; auto.
Qed.

Lemma chain_lstep {A} (ch : nat -> alist A) :
  chain ch ->
  chain (lstep ∘ ch).
Proof.
  intros Hch i; unfold compose; simpl.
  destruct (ch i) eqn:Hchi; simpl; try constructor.
  - specialize (Hch i); rewrite Hchi in Hch; inv Hch; simpl; auto.
  - specialize (Hch i); rewrite Hchi in Hch; inv Hch; simpl; auto.
Qed.

(* Lemma cocons_chain_inv {A} (x y : A) (l l' : colist A) (i j : nat) (ch : nat -> colist A) : *)
(*   chain ch -> *)
(*   ch i = cocons x l -> *)
(*   ch j = cocons y l' -> *)
(*   x = y. *)
(* Proof. *)
(*   intros Hch Hi Hj. *)
(*   destruct (Nat.leb_spec i j). *)
(*   - eapply chain_leq in H; eauto. *)
(*     rewrite Hi, Hj in H; inv H; reflexivity. *)
(*   - apply Nat.lt_le_incl in H. *)
(*     eapply chain_leq in H; eauto. *)
(*     rewrite Hi, Hj in H; inv H; reflexivity. *)
(* Qed. *)

Lemma directed_cotau_cocons {A} (ch : nat -> colist A) i j a l1 l2 :
  directed ch ->
  ch i = cotau l1 ->
  ch j = cocons a l2 ->
  False.
Proof.
  intros Hch Hi Hj.
  specialize (Hch i j); destruct Hch as [l [Hl Hl']].
  rewrite Hi in Hl; rewrite Hj in Hl'.
  inv Hl; rewrite <- H0 in Hl'; inv Hl'.
Qed.

Lemma directed_atau_acons {A} (ch : nat -> alist A) i j a l1 l2 :
  directed ch ->
  ch i = atau l1 ->
  ch j = acons a l2 ->
  False.
Proof.
  intros Hch Hi Hj.
  specialize (Hch i j); destruct Hch as [l [Hl Hl']].
  rewrite Hi in Hl; rewrite Hj in Hl'.
  inv Hl; rewrite <- H0 in Hl'; inv Hl'.
Qed.

Lemma colist_sup_ub {A} (ch : nat -> colist A) :
  directed ch ->
  upper_bound (colist_sup ch) ch.
Proof.
  revert ch.
  cofix CH; intros ch Hch i.
  simpl.
  replace (colist_sup ch) with (unf (colist_sup ch)).
  2: { rewrite <- unf_eq; reflexivity. }
  simpl.
  destruct (LPO_option (fun n : nat => not_conil_dec (ch n))) eqn:Ho.
  - apply LPO_option_some in Ho.
    destruct (ch n) eqn:Hchn.
    + inv Ho.
    + clear Ho.
      destruct (ch i) eqn:Hchi.
      { constructor. }
      { pose proof Hch as Hch'.
        specialize (Hch n i); destruct Hch as [k [H0 H1]].
        rewrite Hchn in H0; inv H0.
        rewrite Hchi in H1; inv H1.
        rewrite <- H2 in H0; inv H0. 
        constructor; auto.
        replace c0 with ((step ∘ ch) i).
        2: { unfold compose; rewrite Hchi; reflexivity. }
        apply CH, directed_step; auto. }
      { eapply directed_cotau_cocons in Hchn; eauto; contradiction. }
    + clear Ho.
      destruct (ch i) eqn:Hchi.
      { constructor. }
      { eapply directed_cotau_cocons in Hchn; eauto; try contradiction. }
      { pose proof Hch as Hch'.
        specialize (Hch n i); destruct Hch as [k [H0 H1]].
        rewrite Hchn in H0; inv H0.
        rewrite Hchi in H1; inv H1.
        rewrite <- H4 in H5; inv H5.
        constructor.
        replace c0 with ((step ∘ ch) i).
        2: { unfold compose; rewrite Hchi; reflexivity. }
        apply CH, directed_step; auto. }
  - apply LPO_option_none with (n:=i) in Ho.
    destruct (ch i); try constructor; exfalso; apply Ho; constructor.
Qed.

Lemma upper_bound_step_tau {A} (l : colist A) (ch : nat -> colist A) :
  upper_bound (cotau l) ch ->
  upper_bound l (step ∘ ch).
Proof.
  intros Hub i; specialize (Hub i); unfold compose.
  destruct (ch i) eqn:Hchi.
  - constructor.
  - inv Hub; auto.
  - inv Hub; auto.
Qed.

Lemma upper_bound_step_cons {A} (x : A) (l : colist A) (ch : nat -> colist A) :
  upper_bound (cocons x l) ch ->
  upper_bound l (step ∘ ch).
Proof.
  intros Hub i; specialize (Hub i); unfold compose.
  destruct (ch i) eqn:Hchi.
  - constructor.
  - inv Hub; auto.
  - inv Hub; auto.
Qed.

Lemma colist_sup_const {A} (l : colist A) :
  colist_eq (colist_sup (fun _ : nat => l)) l.
Proof.
  revert l; cofix CH; intro l.
  rewrite unf_eq; simpl.
  destruct (LPO_option (fun _ : nat => not_conil_dec l)) eqn:H.
  - apply LPO_option_some in H.
    destruct l; constructor; unfold compose; apply CH.
  - apply LPO_option_none with (n:=O) in H.
    destruct l; try constructor; exfalso; apply H; constructor.
Qed.

Lemma colist_sup_lub {A} (ch : nat -> colist A) (ub : colist A) :
  directed ch ->
  upper_bound ub ch ->
  colist_sup ch ⊑ ub.
Proof.
  revert ch ub.
  cofix CH; intros ch ub Hch Hub.
  destruct ub.
  - replace ch with (fun _ : nat => @conil A).
    + rewrite colist_sup_const; reflexivity.
    + ext i; specialize (Hub i); destruct (ch i); auto; inv Hub.
  - rewrite unf_eq; simpl.
    destruct (LPO_option (fun n : nat => not_conil_dec (ch n))) eqn:Ho.
    2: { constructor. }
    destruct (ch n) eqn:Hchn.
    + constructor.
    (* + specialize (Hub n); rewrite Hchn in Hub; inv Hub. *)
    + constructor; apply CH.
      * apply directed_step; auto.
      * apply upper_bound_step_tau; auto.
    + specialize (Hub n); rewrite Hchn in Hub; inv Hub.
  - rewrite unf_eq; simpl.
    destruct (LPO_option (fun n : nat => not_conil_dec (ch n))) eqn:Ho.
    2: { constructor. }
    destruct (ch n) eqn:Hchn.
    + constructor.
    + specialize (Hub n); rewrite Hchn in Hub; inv Hub.
    + pose proof Hub as Hub'.
      specialize (Hub n); rewrite Hchn in Hub; inv Hub.
      constructor; apply CH; auto.
      * apply directed_step; auto.
      * eapply upper_bound_step_cons; eauto.
Qed.

Lemma colist_sup_supremum {A} (ch : nat -> colist A) :
  directed ch ->
  supremum (colist_sup ch) ch.
Proof.
  intro Hch; split.
  - apply colist_sup_ub; auto.
  - intros; apply colist_sup_lub; auto.
Qed.

#[export]
  Instance dCPO_colist {A} : dCPO (@colist A).
Proof.
  constructor; intros ch Hch.
  exists (colist_sup ch); apply colist_sup_supremum; auto.
Qed.

Fixpoint inj {A} (l : alist A) : colist A :=
  match l with
  | anil => conil
  | atau xs => cotau (inj xs)
  | acons x xs => cocons x (inj xs)
  end.

Lemma inj_prefix_coprefix {A} (t : colist A) (n : nat) :
  inj (prefix n t) = coprefix n t.
Proof.
  revert t; induction n; intro t; simpl; auto.
  destruct t; simpl; auto; rewrite IHn; auto.
Qed.

Lemma list_le_antisym {A} (a b : alist A) :
  a ⊑ b ->
  b ⊑ a ->
  a = b.
Proof.
  intro H; induction H; intro Hle; inv Hle; auto; rewrite IHalist_le; auto.
Qed.

Lemma equ_alist {A} (a b : alist A) :
  a === b -> a = b.
Proof. intro Heq; apply list_le_antisym; apply Heq. Qed.

Lemma supremum_lstep_tau {A} (l : alist A) (ch : nat -> alist A) :
  supremum (atau l) ch ->
  supremum l (lstep ∘ ch).
Proof.
  intros [Hub Hlub]; split.
  - intro i; specialize (Hub i); unfold compose.
    inv Hub; simpl; auto; constructor.
  - unfold compose; intros y Hy.
    unfold upper_bound in Hy.
    simpl in Hy.
    assert (H: upper_bound (atau y) ch).
    { intro i.
      specialize (Hy i); simpl in Hy.
      destruct (ch i) eqn:Hchi.
      - constructor.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub.
        constructor; auto.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub. }
    apply Hlub in H; inv H; auto.
Qed.

Lemma supremum_lstep_cons {A} (a : A) (l : alist A) (ch : nat -> alist A) :
  supremum (acons a l) ch ->
  supremum l (lstep ∘ ch).
Proof.
  intros [Hub Hlub]; split.
  - intro i; specialize (Hub i); unfold compose.
    inv Hub; simpl; auto; constructor.
  - unfold compose; intros y Hy.
    unfold upper_bound in Hy.
    simpl in Hy.
    assert (H: upper_bound (acons a y) ch).
    { intro i.
      specialize (Hy i); simpl in Hy.
      destruct (ch i) eqn:Hchi.
      - constructor.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub.
        constructor; auto. }
    apply Hlub in H; inv H; auto.
Qed.

Lemma supremum_atau {A} (l : alist A) (ch : nat -> alist A) :
  supremum (atau l) ch ->
  exists i l', ch i = atau l'.
Proof.
  intros [Hub Hlub].
  destruct (strong_LPO (fun n => not_anil_dec (ch n))).
  - destruct e as [n H].
    specialize (Hub n).
    destruct (ch n) eqn:Hchn.
    + inv H.
    + exists n, a; auto.
    + inv Hub.
  - assert (H: upper_bound anil ch).
    { intro i; specialize (Hub i); destruct (ch i) eqn:Hchi.
      + constructor.
      + exfalso; apply n; exists i; rewrite Hchi; constructor.
      + inv Hub. }
    apply Hlub in H; inv H.
Qed.

Lemma supremum_atau' {A} (l : alist A) (ch : nat -> alist A) :
  supremum (atau l) ch ->
  exists i l', ch i = atau l' /\ l' ⊑ l.
Proof.
  intros [Hub Hlub].
  destruct (strong_LPO (fun n => not_anil_dec (ch n))).
  - destruct e as [n H].
    specialize (Hub n).
    destruct (ch n) eqn:Hchn; inv H; inv Hub; exists n, a; split; auto.
  - assert (H: upper_bound anil ch).
    { intro i; specialize (Hub i); destruct (ch i) eqn:Hchi.
      + constructor.
      + exfalso; apply n; exists i; rewrite Hchi; constructor.
      + inv Hub. }
    apply Hlub in H; inv H.
Qed.

Lemma supremum_acons' {A} (a : A) (l : alist A) (ch : nat -> alist A) :
  supremum (acons a l) ch ->
  exists i l', ch i = acons a l' /\ l' ⊑ l.
Proof.
  intros [Hub Hlub].
  destruct (strong_LPO (fun n => not_anil_dec (ch n))).
  - destruct e as [n H].
    specialize (Hub n).
    inv Hub.
    + rewrite <- H1 in H; inv H.
    + exists n, l1; auto.
  - assert (H: upper_bound anil ch).
    { intro i; specialize (Hub i); destruct (ch i) eqn:Hchi.
      + constructor.
      + inv Hub.
      + exfalso; apply n; exists i; rewrite Hchi; constructor. }
    apply Hlub in H; inv H.
Qed.

Lemma supremum_cotau {A} (t : colist A) (ch : nat -> colist A) :
  supremum (cotau t) ch ->
  exists i t', ch i = cotau t'.
Proof.
  intros [Hub Hlub].
  destruct (strong_LPO (fun n => not_conil_dec (ch n))).
  - destruct e as [n H].
    specialize (Hub n).
    destruct (ch n) eqn:Hchn.
    + inv H.
    + exists n, c; auto.
    + inv Hub.
  - assert (H: upper_bound conil ch).
    { intro i; specialize (Hub i); destruct (ch i) eqn:Hchi.
      + constructor.
      + exfalso; apply n; exists i; rewrite Hchi; constructor.
      + inv Hub. }
    apply Hlub in H; inv H.
Qed.

Lemma supremum_cocons' {A} (a : A) (l : colist A) (ch : nat -> colist A) :
  supremum (cocons a l) ch ->
  exists i l', ch i = cocons a l' /\ l' ⊑ l.
Proof.
  intros [Hub Hlub].
  destruct (strong_LPO (fun n => not_conil_dec (ch n))).
  - destruct e as [n H].
    specialize (Hub n).
    inv Hub.
    + rewrite <- H1 in H; inv H.
    + exists n, l1; auto.
  - assert (H: upper_bound conil ch).
    { intro i; specialize (Hub i); destruct (ch i) eqn:Hchi.
      + constructor.
      + inv Hub.
      + exfalso; apply n; exists i; rewrite Hchi; constructor. }
    apply Hlub in H; inv H.
Qed.

Lemma alist_compact {A} (l : alist A) (ch : nat -> alist A) :
  directed ch ->
  supremum l ch ->
  exists i, ch i = l.
Proof.
  revert ch; induction l; intros ch Hch Hl.
  - exists O; apply equ_alist; split; try constructor; apply Hl.
  - pose proof Hl as Hl'.
    apply supremum_lstep_tau in Hl.
    apply IHl in Hl; clear IHl.
    2: { apply directed_lstep; auto. }
    destruct Hl as [j Hj].
    unfold compose in Hj.
    unfold lstep in Hj.
    destruct (ch j) eqn:Hchj; subst.
    + apply supremum_atau' in Hl'.
      destruct Hl' as [i [l' [Hi Hl']]]; inv Hl'; exists i; auto.
    + exists j; auto.
    + apply supremum_atau in Hl'; destruct Hl' as [i [l' Hl']].
      exfalso; eapply directed_atau_acons; eauto.
  - pose proof Hl as Hl'.
    apply supremum_lstep_cons in Hl.
    apply IHl in Hl; clear IHl.
    2: { apply directed_lstep; auto. }
    destruct Hl as [j Hj].
    unfold compose in Hj.
    unfold lstep in Hj.
    destruct (ch j) eqn:Hchj; subst.
    + apply supremum_acons' in Hl'.
      destruct Hl' as [i [l' [Hi Hl']]]; inv Hl'; exists i; auto.
    + destruct Hl' as [H0 H1]; specialize (H0 j).
      rewrite Hchj in H0; inv H0; exists j; auto.
    + destruct Hl' as [H0 H1]; specialize (H0 j).
      rewrite Hchj in H0; inv H0; exists j; auto.
Qed.

Lemma list_le_colist_le {A} (a b : alist A) :
  a ⊑ b ->
  inj a ⊑ inj b.
Proof.
  revert b; induction a; simpl; intros b Hab.
  - constructor.
  - destruct b; inv Hab; constructor; apply IHa; auto.
  - destruct b; inv Hab; constructor; apply IHa; auto.
Qed.

Lemma colist_le_list_le {A} (a b : alist A) :
  inj a ⊑ inj b ->
  a ⊑ b.
Proof.
  revert b; induction a; simpl; intros b Hab.
  - constructor.
  - destruct b; inv Hab; constructor; apply IHa; auto.
  - destruct b; inv Hab; constructor; apply IHa; auto.
Qed.

Lemma supremum_step_tau {A} (t : colist A) (ch : nat -> colist A) :
  supremum (cotau t) ch ->
  supremum t (step ∘ ch).
Proof.
  intros [Hub Hlub]; split.
  - intro i; specialize (Hub i); unfold compose.
    inv Hub; simpl; auto; constructor.
  - unfold compose; intros y Hy.
    unfold upper_bound in Hy.
    simpl in Hy.
    assert (H: upper_bound (cotau y) ch).
    { intro i.
      specialize (Hy i); simpl in Hy.
      destruct (ch i) eqn:Hchi.
      - constructor.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub.
        constructor; auto.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub. }
    apply Hlub in H; inv H; auto.
Qed.

Lemma supremum_step_cons {A} (a : A) (l : colist A) (ch : nat -> colist A) :
  supremum (cocons a l) ch ->
  supremum l (step ∘ ch).
Proof.
  intros [Hub Hlub]; split.
  - intro i; specialize (Hub i); unfold compose.
    inv Hub; simpl; auto; constructor.
  - unfold compose; intros y Hy.
    unfold upper_bound in Hy.
    simpl in Hy.
    assert (H: upper_bound (cocons a y) ch).
    { intro i.
      specialize (Hy i); simpl in Hy.
      destruct (ch i) eqn:Hchi.
      - constructor.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub.
      - specialize (Hub i); simpl in Hub; rewrite Hchi in Hub; inv Hub.
        constructor; auto. }
    apply Hlub in H; inv H; auto.
Qed.

Lemma prefix_continuous {A} (n : nat) :
  continuous (@prefix A n).
Proof.
  induction n; intros ch Hch x Hx; unfold compose; simpl.
  { apply supremum_const. }
  destruct x.
  - apply supremum_conil in Hx.
    apply supremum_const'.
    apply equ_arrow; intro i; rewrite Hx; reflexivity.
  - assert (Hc: supremum x (step ∘ ch)).
    { apply supremum_step_tau; auto. }
    split.
    + intro i; destruct (ch i) eqn:Hchi; simpl.
      * constructor.
      * destruct Hx as [Hub Hlub].
        specialize (Hub i).
        rewrite Hchi in Hub.
        inv Hub.
        constructor.
        apply prefix_monotone; auto.
      * destruct Hx as [Hub Hlub].
        specialize (Hub i); rewrite Hchi in Hub; inv Hub.
    + intros ub Hub; destruct ub.
      * assert (H: forall i, ch i = conil).
        { intro i; specialize (Hub i); simpl in Hub.
          destruct (ch i); auto; inv Hub. }
        assert (supremum conil ch).
        { apply supremum_const'; apply equ_arrow; intro i.
          unfold const; rewrite H; reflexivity. }
        eapply supremum_unique in Hx; eauto.
        apply equ_colist_eq in Hx; inv Hx.
      * constructor.
        eapply IHn.
        2: { eauto. }
        { apply directed_step; auto. }
        intro i; specialize (Hub i); simpl in Hub.
        unfold compose.
        destruct (ch i) eqn:Hchi; simpl.
        { destruct n; constructor. }
        { inv Hub; auto. }
        { inv Hub. }
      * apply supremum_cotau in Hx.
        destruct Hx as [i [t Ht] ].
        specialize (Hub i); simpl in Hub; rewrite Ht in Hub; inv Hub.  
  - assert (Hc: supremum x (step ∘ ch)).
    { eapply supremum_step_cons; eauto. }
    split.
    + intro i; destruct (ch i) eqn:Hchi; simpl.
      * constructor.
      * destruct Hx as [Hub Hlub].
        specialize (Hub i); rewrite Hchi in Hub; inv Hub.
      * destruct Hx as [Hub Hlub].
        specialize (Hub i).
        rewrite Hchi in Hub.
        inv Hub.
        constructor.
        apply prefix_monotone; auto.
    + intros ub Hub; destruct ub.
      * assert (H: forall i, ch i = conil).
        { intro i; specialize (Hub i); simpl in Hub.
          destruct (ch i); auto; inv Hub. }
        assert (supremum conil ch).
        { apply supremum_const'; apply equ_arrow; intro i.
          unfold const; rewrite H; reflexivity. }
        eapply supremum_unique in Hx; eauto.
        apply equ_colist_eq in Hx; inv Hx.
      * pose proof Hx as Hx'.
        apply supremum_cocons' in Hx'.
        destruct Hx' as [i [l' [Hx' Hx'']]].
        pose proof Hub as Hub'.
        specialize (Hub' i).
        simpl in Hub'.
        rewrite Hx' in Hub'.
        inv Hub'.
      * pose proof Hx as Hx'.
        apply supremum_cocons' in Hx'.
        destruct Hx' as [i [l' [Hx' Hx'']]].
        pose proof Hub as Hub'.
        specialize (Hub' i).
        simpl in Hub'.
        rewrite Hx' in Hub'.
        inv Hub'.
        clear Hx' i.
        constructor.
        eapply IHn.
        2: { eauto. }
        { apply directed_step; auto. }
        intro i; specialize (Hub i); simpl in Hub.
        unfold compose.
        destruct (ch i) eqn:Hchi; simpl.
        { destruct n; constructor. }
        { inv Hub. }
        { inv Hub; auto. }
Qed.

Lemma coprefix_le {A} (l : colist A) (n : nat) :
  coprefix n l ⊑ l.
Proof.
  revert l; induction n; intro l; simpl; try constructor.
  destruct l; constructor; apply IHn.
Qed.

Lemma coprefix_supremum {A} (l : colist A) :
  supremum l (fun n => coprefix n l).
Proof.
  split.
  - intro i. apply coprefix_le.
  - revert l; cofix CH; intros l ub Hub.
    destruct ub.
    + specialize (Hub (S O)).
      destruct l; inv Hub; constructor.
    + destruct l.
      * constructor.
      * pose proof Hub as Hub'.
        specialize (Hub' (S O)).
        inv Hub'.
        constructor; apply CH.
        intro i.
        specialize (Hub (S i)); simpl in Hub.
        inv Hub; auto.
      * specialize (Hub (S O)).
        destruct l; inv Hub; constructor.
    + destruct l.
      * constructor.
      * specialize (Hub (S O)).
        destruct l; inv Hub; constructor.
      * pose proof Hub as Hub'.
        specialize (Hub' (S O)).
        inv Hub'.
        constructor; apply CH.
        intro i.
        specialize (Hub (S i)); simpl in Hub.
        inv Hub; auto.
Qed.

#[export]
  Instance Compact_alist {A} : Compact (alist A).
Proof. constructor; intros a f Hf Ha; apply alist_compact; auto. Qed.

#[export]
  Instance Dense_colist {A} : Dense (colist A) (alist A) :=
  { incl := inj
  ; ideal := flip prefix }.

#[export]
  Instance aCPO_colist {A} : aCPO (colist A) (alist A).
Proof.
  constructor.
  - intros a b; split.
    + apply list_le_colist_le.
    + apply colist_le_list_le.
  - apply chain_prefix.
  - intros a b Hab i; apply prefix_monotone; auto.
  - apply prefix_continuous.
  - intro a; simpl; unfold compose, flip.
    replace (fun i => inj (prefix i a)) with (fun i => coprefix i a).
    + apply coprefix_supremum.
    + ext i; rewrite inj_prefix_coprefix; reflexivity.
Qed.

Fixpoint afold {A B} (z : B) (f : B -> B) (g : A -> B -> B) (l : alist A) : B :=
  match l with
  | anil => z
  | atau xs => f (afold z f g xs)
  | acons x xs => g x (afold z f g xs)
  end.

#[export]
  Instance monotone_afold {A B} `{OType B} (z : B) (f : B -> B) (g : A -> B -> B)
  {Hz : forall b, z ⊑ afold z f g b}
  {Hf : Proper (leq ==> leq) f}
  {Hg : forall a, Proper (leq ==> leq) (g a)}
  : Proper (leq ==> leq) (afold z f g).
Proof.
  intro a; revert Hz Hf Hg; revert f;
    induction a; intros f Hz Hf Hg b Hab; inv Hab; simpl.
  - apply Hz.
  - apply Hf; auto.
  - apply Hg, IHa; auto.
Qed.
#[export] Hint Resolve monotone_afold : colist.

#[export]
  Instance antimonotone_afold {A B} `{OType B} (z : B) (f : B -> B) (g : A -> B -> B)
  {Hz : forall b, afold z f g b ⊑ z}
  {Hf : Proper (leq ==> leq) f}
  {Hg : forall a, Proper (leq ==> leq) (g a)}
  : Proper (leq ==> flip leq) (afold z f g).
Proof.
  intro a; revert Hz Hf Hg; revert f;
    induction a; intros f Hz Hf Hg b Hab; inv Hab; simpl.
  - apply Hz.
  - apply Hf, IHa; auto.
  - apply Hg, IHa; auto.
Qed.
#[export] Hint Resolve antimonotone_afold : colist.

(** Computation lemmas for cofolds. *)

Lemma co_fold_nil {A B} `{dCPO B} (z : B) (f : B -> B) (g : A -> B -> B) :
  co (afold z f g) conil === z.
Proof.
  apply supremum_sup, supremum_const', equ_arrow; intros []; reflexivity.
Qed.

Lemma co_fold_tau {A B} `{dCPO B}
  (z : B) (f : B -> B) (g : A -> B -> B) (l : colist A) :
  (forall b, z ⊑ afold z f g b) ->
  continuous f ->
  (forall a, monotone (g a)) ->
  z ⊑ f z ->
  co (afold z f g) (cotau l) === f (co (afold z f g) l).
Proof.
  intros Hg Hf Hz Hgz.
  assert (Hf': monotone f).
  { apply continuous_monotone; auto. }
  apply supremum_sup.
  apply shift_supremum'' with (f := fun i => f (afold z f g (ideal l i))); auto.
  { apply Hf.
    { apply monotone_directed; auto with colist order.
      apply chain_directed, chain_ideal. }
    { apply dsup_spec.
      { apply monotone_directed; auto with colist order.
        apply chain_directed, chain_ideal. } } }
  apply equ_arrow; intro i; reflexivity.
Qed.

Lemma co_fold_cons {A B} `{dCPO B}
  (z : B) (f : B -> B) (g : A -> B -> B) (a : A) (l : colist A) :
  (forall b, z ⊑ afold z f g b) ->
  monotone f ->
  (forall a, continuous (g a)) ->
  z ⊑ g a z ->
  co (afold z f g) (cocons a l) === g a (co (afold z f g) l).
Proof.
  intros Hz Hf Hg Hfaz.
  apply supremum_sup.
  apply shift_supremum'' with (f := fun i => g a (afold z f g (ideal l i))); auto.
  { apply Hg.
    { apply monotone_directed; auto with colist order.
      apply chain_directed, chain_ideal. }
    { apply dsup_spec.
      { apply monotone_directed; auto with colist order.
        apply chain_directed, chain_ideal. } } }
  apply equ_arrow; intro i; reflexivity.
Qed.

(** Equality computaton lemmas for cofolds. *)

Lemma co_fold_nil' {A B} {o : OType B} `{@ExtType B o} `{@dCPO B o}
  (z : B) (f : B -> B) (g : A -> B -> B) :
  co (afold z f g) conil = z.
Proof. apply ext, co_fold_nil. Qed.

Lemma co_fold_tau' {A B} {o : OType B} `{@ExtType B o} `{@dCPO B o}
  (z : B) (f : B -> B) (g : A -> B -> B) (l : colist A) :
  (forall b, z ⊑ afold z f g b) ->
  continuous f ->
  (forall a, monotone (g a)) ->
  z ⊑ f z ->
  co (afold z f g) (cotau l) = f (co (afold z f g) l).
Proof. intros Hz Hf Hg Hfaz; apply ext, co_fold_tau; auto. Qed.

Lemma co_fold_cons' {A B} {o : OType B} `{@ExtType B o} `{@dCPO B o}
  (z : B) (f : B -> B) (g : A -> B -> B) (a : A) (l : colist A) :
  (forall b, z ⊑ afold z f g b) ->
  monotone f ->
  (forall a, continuous (g a)) ->
  z ⊑ g a z ->
  co (afold z f g) (cocons a l) = g a (co (afold z f g) l).
Proof. intros Hz Hf Hg Hfaz; apply ext, co_fold_cons; auto. Qed.
