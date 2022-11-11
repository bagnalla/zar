(** * Ordered types, suprema/infima, continuity, etc. *)

(** See cpo.v and aCPO.v for more order-theoretic definitions that
  build upon those here. *)

From Coq Require Import
  Basics
  Morphisms
  PeanoNat
  Relation_Definitions
  Lia
  Equivalence
  PropExtensionality
.

Local Open Scope program_scope.
Local Open Scope equiv_scope.

From zar Require Import
  axioms
  misc
  tactics
.

Create HintDb order.

(** Ordered types. *)
Class OType (A : Type) : Type :=
  { leq : relation A
  ; leq_preorder : PreOrder leq
  }.

#[global]
  Instance OType_Reflexive A `{o : OType A} : Reflexive leq.
Proof. destruct o; typeclasses eauto. Qed.

#[global]
  Instance OType_Transitive A `{o : OType A} : Transitive leq.
Proof. destruct o; typeclasses eauto. Qed.

Definition gt {A : Type} `{OType A} : relation A := fun x y => not (leq x y).

Definition lt {A : Type} `{OType A} : relation A := fun x y => leq x y /\ not (leq y x).

#[global]
  Instance Transitive_lt A `{o : OType A} : Transitive lt.
Proof.
  destruct o as [R [Hrefl Htrans]].
  intros x y z [H0 H1] [H2 H3].
  unfold lt; simpl in *; split.
  - eapply Htrans; eauto.
  - intro HC; apply H3.
    eapply Htrans; eauto.
Qed.

Declare Scope order_scope.
Notation "x '⊑' y" := (leq x y) (at level 70, no associativity) : order_scope.
Notation "x '⊏' y" := (lt x y) (at level 70, no associativity) : order_scope.
Local Open Scope order_scope.

(* [a] is an upper bound of [f] *)
Definition upper_bound {I A : Type} `{OType A} (a : A) (f : I -> A) :=
  forall i, f i ⊑ a.

(* [a] is a lower bound of [f] *)
Definition lower_bound {I A : Type} `{OType A} (a : A) (f : I -> A) :=
  forall i, a ⊑ f i.

(* [a] is the least upper bound of [f]. *)
Definition supremum {I A : Type} `{OType A} (a : A) (f : I -> A) :=
  upper_bound a f /\ forall x, upper_bound x f -> a ⊑ x.

(* [a] is the greatest lower bound of [f]. *)
Definition infimum {I A : Type} `{OType A} (a : A) (f : I -> A) :=
  lower_bound a f /\ forall x, lower_bound x f -> x ⊑ a.

(* f is an ascending ω-chain *)
Definition chain {A : Type} `{o : OType A} (f : nat -> A) : Prop :=
  forall i, f i ⊑ f (S i).

(* f is a descending ω-chain *)
Definition dec_chain {A : Type} `{o : OType A} (f : nat -> A) : Prop :=
  forall i, f (S i) ⊑ f i.

(* f is upward-directed. *)
(* When the order relation is interpreted as an approximation
relation, we can think of directed sets as sets of elements that are
all ultimately approximating the same thing. *)
Definition directed {I A : Type} `{OType A} (f : I -> A) : Prop :=
  forall i j : I, exists k : I, f i ⊑ f k /\ f j ⊑ f k.

(* f is downward-directed. *)
Definition downward_directed {I A : Type} `{OType A} (f : I -> A) : Prop :=
  forall i j : I, exists k : I, f k ⊑ f i /\ f k ⊑ f j.

#[global]
  Program Instance OType_Prop : OType Prop := {| leq := impl |}.
Next Obligation. constructor; intuition. Qed.

#[global]
  Program Instance OType_arrow A B {oB : OType B} : OType (A -> B) :=
  {| leq := fun f g => forall x, leq (f x) (g x) |}.
Next Obligation.
  constructor.
  - intros f x; reflexivity.
  - intros ?; etransitivity; eauto.
Qed.

#[global]
  Instance OType_nat : OType nat := {| leq := Nat.le |}.

#[global]
  Instance OType_list A : OType (list A) :=
  {| leq := is_prefix |}.

Definition equ {A : Type} `{OType A} (x y : A) := x ⊑ y /\ y ⊑ x.

#[global]
  Instance Reflexive_equ A `{o : OType A} : Reflexive equ.
Proof. destruct o as [? [Hrefl ?]]; split; apply Hrefl. Qed.

#[global]
  Instance Transitive_equ A `{o : OType A} : Transitive equ.
Proof.
  intros x y z Hxy Hyz.
  destruct o as [? [? Htrans]]; split.
  - etransitivity. apply Hxy. apply Hyz.
  - etransitivity. apply Hyz. apply Hxy.
Qed.

#[global]
  Instance Symmetric_equ A `{OType A} : Symmetric equ.
Proof. unfold Symmetric, equ; intuition. Qed.

#[global]
  Program Instance Equivalence_equ A `{OType A} : Equivalence equ.

#[global]
  Instance Proper_leq {A} `{OType A} : Proper (equ ==> equ ==> flip impl) leq.
Proof.
  intros x y [Hxy Hyx] a b [Hab Hba] Hle.
  etransitivity; eauto.
  etransitivity; eauto.
Qed.

#[global]
  Instance Proper_monotone_equ {A B} `{OType A} `{OType B} (f : A -> B)
  {pf: Proper (leq ==> leq) f} : Proper (equ ==> equ) f.
Proof. intros a b Hab; split; apply pf, Hab. Qed.

#[global]
  Instance Proper_antimonotone_equ {A B} `{OType A} `{OType B} (f : A -> B)
  {pf: Proper (leq ==> flip leq) f} : Proper (equ ==> equ) f.
Proof. intros a b Hab; split; apply pf, Hab. Qed.

Definition incomparable {A} `{OType A} (x y : A) : Prop :=
  ~ (x ⊑ y \/ y ⊑ x).

Definition bounded_above {A B : Type} `{OType B} (f : A -> B) :=
  exists b, upper_bound b f.

Definition eventually_constant_at {A} `{OType A} (f : nat -> A) (x : A) : Prop :=
  exists n0, forall n, (n0 <= n)%nat -> f n === x.

Lemma infimum_unique {A B : Type} `{o : OType B} (x y : B) (f : A -> B) :
  infimum x f -> infimum y f -> x === y.
Proof.
  intros [H0 H1] [H2 H3]; split.
  - apply H3; auto.
  - apply H1; auto.
Qed.

Lemma supremum_unique {A B : Type} `{o : OType B} (x y : B) (f : A -> B) :
  supremum x f -> supremum y f -> x === y.
Proof.
  intros [H0 H1] [H2 H3]; split.
  - apply H1; auto.
  - apply H3; auto.
Qed.

(* [f] is monotone whenever it is order-preserving. *)
Definition monotone {A B : Type} `{OType A} `{OType B} (f : A -> B) :=
  Proper (leq ==> leq) f.
#[global] Hint Unfold monotone : order.

(* [f] is antimonotone whenever it is order-reversing. *)
Definition antimonotone {A B : Type} `{OType A} `{OType B} (f : A -> B) :=
  Proper (leq ==> flip leq) f.
#[global] Hint Unfold antimonotone : order.

Lemma monotone_chain {A B : Type} `{OType A} `{OType B} (f : A -> B) (g : nat -> A) :
  monotone f ->
  chain g ->
  chain (f ∘ g).
Proof. intros Hmono Hg i; apply Hmono, Hg. Qed.

Lemma monotone_directed {I A B : Type} `{OType A} `{OType B} (f : A -> B) (g : I -> A) :
  monotone f ->
  directed g ->
  directed (f ∘ g).
Proof.
  intros Hf Hg i j.
  specialize (Hg i j); destruct Hg as [k [Hk Hk']].
  exists k; split; eauto.
Qed.
#[global] Hint Resolve monotone_directed : order.

Lemma antimonotone_directed {I A B : Type} `{OType A} `{OType B} (f : A -> B) (g : I -> A) :
  antimonotone f ->
  downward_directed g ->
  directed (f ∘ g).
Proof.
  intros Hf Hg i j.
  specialize (Hg i j); destruct Hg as [k [Hk Hk']].
  exists k; split; apply Hf; auto.
Qed.
#[global] Hint Resolve antimonotone_directed : order.

Lemma monotone_downward_directed {I A B : Type} `{OType A} `{OType B}
  (f : A -> B) (g : I -> A) :
  monotone f ->
  downward_directed g ->
  downward_directed (f ∘ g).
Proof.
  intros Hf Hg i j.
  specialize (Hg i j); destruct Hg as [k [Hk Hk']].
  exists k; split; apply Hf; auto.
Qed.
#[global] Hint Resolve monotone_downward_directed : order.

Lemma antimonotone_downward_directed {I A B : Type} `{OType A} `{OType B}
  (f : A -> B) (g : I -> A) :
  antimonotone f ->
  directed g ->
  downward_directed (f ∘ g).
Proof.
  intros Hf Hg i j.
  specialize (Hg i j); destruct Hg as [k [Hk Hk']].
  exists k; split; apply Hf; auto.
Qed.
#[global] Hint Resolve antimonotone_downward_directed : order.

Lemma monotone_dec_chain {A B : Type} `{OType A} `{OType B} (f : A -> B) (g : nat -> A) :
  monotone f ->
  dec_chain g ->
  dec_chain (f ∘ g).
Proof. intros Hmono Hg i; apply Hmono, Hg. Qed.

Lemma antimonotone_dec_chain {A B : Type} `{OType A} `{OType B} (f : A -> B) (g : nat -> A) :
  antimonotone f ->
  chain g ->
  dec_chain (f ∘ g).
Proof. intros Hmono Hg i; apply Hmono, Hg. Qed.

Lemma antimonotone_chain {A B : Type} `{OType A} `{OType B} (f : A -> B) (g : nat -> A) :
  antimonotone f ->
  dec_chain g ->
  chain (f ∘ g).
Proof. intros Hmono Hg i; apply Hmono, Hg. Qed.

Lemma monotone_compose {A B C : Type} `{OType A} `{OType B} `{OType C}
  (f : A -> B) (g : B -> C) :
  monotone f ->
  monotone g ->
  monotone (g ∘ f).
Proof. intros Hf Hg x y Hleq; apply Hg, Hf; auto. Qed.
#[global] Hint Resolve monotone_compose : order.

Lemma monotone_antimonotone_compose {A B C : Type} `{OType A} `{OType B} `{OType C}
  (f : A -> B) (g : B -> C) :
  monotone f ->
  antimonotone g ->
  antimonotone (g ∘ f).
Proof. intros Hf Hg x y Hleq; apply Hg, Hf; auto. Qed.

Lemma antimonotone_compose {A B C : Type}
  `{OType A} `{OType B} `{OType C} (f : A -> B) (g : B -> C) :
  antimonotone f ->
  antimonotone g ->
  monotone (g ∘ f).
Proof. intros Hf Hg x y Hleq; apply Hg, Hf; auto. Qed.
#[global] Hint Resolve antimonotone_compose : order.

Lemma chain_leq {A : Type} `{o : OType A} (f : nat -> A) (n m : nat) :
  chain f ->
  (n <= m)%nat ->
  leq (f n) (f m).
Proof.
  intros Hchain Hle; induction m.
  - assert (n = O). lia. subst; reflexivity.
  - destruct (Nat.eqb_spec n (S m)); subst.
    + reflexivity.
    + assert (H': (n <= m)%nat). lia.
      etransitivity. apply IHm; auto.
      apply Hchain.
Qed.

Lemma dec_chain_leq {A : Type} `{o : OType A} (f : nat -> A) (n m : nat) :
  dec_chain f ->
  (n <= m)%nat ->
  leq (f m) (f n).
Proof.
  intros Hchain Hle; induction m.
  - assert (n = O). lia. subst; reflexivity.
  - destruct (Nat.eqb_spec n (S m)); subst.
    + reflexivity.
    + assert (H': (n <= m)%nat). lia.
      etransitivity. apply Hchain. apply IHm; auto.
Qed.

Lemma const_infimum {A : Type} {o : OType A} (ch : nat -> A) (c : A) :
  (forall i, ch i === c) -> infimum c ch.
Proof.
  intros Hequ; split.
  - intro; apply Hequ.
  - intros lb Hlb.
    specialize (Hlb O); specialize (Hequ O).
    etransitivity; eauto; apply Hequ.
Qed.

Lemma const_supremum {A : Type} {o : OType A} (f : nat -> A) (x : A) :
  (forall i, f i === x) -> supremum x f.
Proof.
  intros Hequ; split.
  - intro; apply Hequ.
  - intros ub Hub.
    specialize (Hub O); specialize (Hequ O).
    etransitivity; eauto; apply Hequ.
Qed.

Lemma const_supremum'' {A : Type} `{o : OType A} (f : nat -> A) (x : A) :
  upper_bound x f ->
  (exists n, f n === x) ->
  supremum x f.
Proof.
  intros Hx [n0 Hequ].
  split; auto.
  - intros ub Hub.
    transitivity (f n0).
    apply Hequ; auto.
    apply Hub.
Qed.

#[global]
  Instance Proper_infimum {A B : Type} {oB : OType B}
  : Proper (equ ==> equ ==> iff) (@infimum A B oB).
Proof.
  intros x y [Hequ0 Hequ1] f g [Hequ0' Hequ1'].
  split; intros [Hlb Hglb].
  - split.
    + intro z.
      transitivity x; auto.
      transitivity (f z); auto.
    + intros lb Hlb'.
      transitivity x; auto.
      apply Hglb.
      intro z; transitivity (g z); auto.
  - split.
    + intro z.
      transitivity y; auto.
      transitivity (g z); auto.
    + intros lb Hlb'.
      transitivity y; auto.
      apply Hglb.
      intro z; transitivity (f z); auto.
Qed.

#[global]
  Instance Proper_supremum {A B : Type} {oB : OType B}
  : Proper (equ ==> equ ==> iff) (@supremum A B oB).
Proof.
  intros x y [Hequ0 Hequ1] f g [Hequ0' Hequ1'].
  split; intros [Hub Hlub].
  - split.
    + intro z.
      transitivity x; auto.
      transitivity (f z); auto.
    + intros ub Hub'.
      transitivity x; auto.
      apply Hlub.
      intro z; transitivity (g z); auto.
  - split.
    + intro z.
      transitivity y; auto.
      transitivity (g z); auto.
    + intros lb Hub'.
      transitivity y; auto.
      apply Hlub.
      intro z; transitivity (f z); auto.
Qed.

Definition continuous {A B : Type} `{OType A} `{OType B} (f : A -> B) :=
  forall g : nat -> A,
    directed g ->
    forall a : A,
      supremum a g ->
      supremum (f a) (f ∘ g).

(* A function is cocontinuous when it is continuous wrt the opposite
   order relation. *)
Definition cocontinuous {A B : Type} `{OType A} `{OType B} (f : A -> B) :=
  forall g : nat -> A,
    directed g ->
    forall a : A,
      supremum a g ->
      infimum (f a) (f ∘ g).

(* ω-continuity is a weaker notion in general than directed-continuity
   (e.g., in the CPO of reals). In general, a function that is
   d-continuous is also ω-continuous, but the converse may not
   hold. *)
Definition wcontinuous {A B : Type} `{OType A} `{OType B} (f : A -> B) :=
  forall g : nat -> A,
    chain g ->
    forall a : A,
      supremum a g ->
      supremum (f a) (f ∘ g).

Definition wcocontinuous {A B : Type} `{OType A} `{OType B} (f : A -> B) :=
  forall g : nat -> A,
    chain g ->
    forall a : A,
      supremum a g ->
      infimum (f a) (f ∘ g).

Definition dec_continuous {A B : Type} `{OType A} `{OType B} (f : A -> B) :=
  forall g : nat -> A,
    downward_directed g ->
    forall a : A,
      infimum a g ->
      infimum (f a) (f ∘ g).

Definition dec_cocontinuous {A B : Type} `{OType A} `{OType B} (f : A -> B) :=
  forall g : nat -> A,
    downward_directed g ->
    forall a : A,
      infimum a g ->
      supremum (f a) (f ∘ g).

Definition dec_wcontinuous {A B : Type} `{OType A} `{OType B} (f : A -> B) :=
  forall g : nat -> A,
    dec_chain g ->
    forall inf : A,
      infimum inf g ->
      infimum (f inf) (f ∘ g).

Lemma chain_directed {A} `{OType A} (f : nat -> A) :
  chain f ->
  directed f.
Proof.
  intros Hch i j.
  exists (max i j); split; apply chain_leq; auto.
  - apply Nat.le_max_l.
  - apply Nat.le_max_r.
Qed.
#[global] Hint Resolve chain_directed : order.

Lemma dec_chain_downward_directed {A} `{OType A} (f : nat -> A) :
  dec_chain f ->
  downward_directed f.
Proof.
  intros Hch i j.
  exists (max i j); split; apply dec_chain_leq; auto.
  - apply Nat.le_max_l.
  - apply Nat.le_max_r.
Qed.
#[global] Hint Resolve dec_chain_downward_directed : order.

Lemma continuous_wcontinuous {A B} `{OType A} `{OType B} (f : A -> B) :
  continuous f ->
  wcontinuous f.
Proof.
  intros Hf ch Hch s Hs; apply Hf; auto; apply chain_directed; auto.
Qed.
#[global] Hint Resolve continuous_wcontinuous : order.

Lemma dec_continuous_dec_wcontinuous {A B} `{OType A} `{OType B} (f : A -> B) :
  dec_continuous f ->
  dec_wcontinuous f.
Proof.
  intros Hf ch Hch s Hs; apply Hf; auto; apply dec_chain_downward_directed; auto.
Qed.
#[global] Hint Resolve continuous_wcontinuous : order.

Lemma upper_bound_const {A B} `{OType A} (a : A) :
  upper_bound a (@const A B a).
Proof. intro b; reflexivity. Qed.

Lemma lower_bound_const {A B} `{OType A} (a : A) :
  lower_bound a (@const A B a).
Proof. intro b; reflexivity. Qed.

Lemma supremum_const {A B} `{OType A} `{Inhabited B} (a : A) :
  supremum a (fun _ : B => a).
Proof.
  split.
  - apply upper_bound_const.
  - unfold upper_bound.
    unfold const. intros x H1.
    destruct H0; apply H1; auto.
Qed.
#[global] Hint Resolve supremum_const : order.

Lemma supremum_const' {A B} `{OType A} `{Inhabited B} (a : A) (f : nat -> A) :
  f === const a ->
  supremum a f.
Proof. intros ->; apply supremum_const. Qed.

Lemma infimum_const {A B} `{OType A} `{Inhabited B} (a : A) :
  infimum a (fun _ : B => a).
Proof.
  split.
  - apply lower_bound_const.
  - unfold const; intros x H1.
    destruct H0; apply H1; auto.
Qed.
#[global] Hint Resolve infimum_const : order.

Lemma infimum_const' {A B} `{OType A} `{Inhabited B} (a : A) (f : nat -> A) :
  f === const a ->
  infimum a f.
Proof. intros ->; apply infimum_const. Qed.

Lemma leq_arrow {A B} `{OType B} (f g : A -> B) :
  f ⊑ g -> forall x, f x ⊑ g x.
Proof. auto. Qed.

Lemma equ_arrow {A B} `{OType B} (f g : A -> B) :
  f === g <-> forall x, f x === g x.
Proof.
  split.
  - intros [Hfg Hgf] x; split; auto.
  - intros Hfg; split; intro x; apply Hfg.
Qed.

Lemma directed_const {I A} `{OType A} (x : A) :
  directed (fun _ : I => x).
Proof. intros _ j; exists j; split; reflexivity. Qed.
#[global] Hint Resolve directed_const : order.

Lemma downward_directed_const {I A} `{OType A} (x : A) :
  downward_directed (fun _ : I => x).
Proof. intros _ j; exists j; split; reflexivity. Qed.
#[global] Hint Resolve downward_directed_const : order.

Lemma eq_equ {A} `{OType A} x y :
  x = y -> x === y.
Proof. intro; subst; reflexivity. Qed.

Lemma pointwise_le_supremum_le {A} `{OType A} (f g : nat -> A) (a b : A) :
  (forall i, f i ⊑ g i) ->
  supremum a f ->
  supremum b g ->
  a ⊑ b.
Proof.
  intros Hle [Ha Ha'] [Hb Hb'].
  eapply Ha'; intro i; etransitivity; eauto.
Qed.

Lemma pointwise_le_infimum_le {A} `{OType A} (f g : nat -> A) (a b : A) :
  (forall i, f i ⊑ g i) ->
  infimum a f ->
  infimum b g ->
  a ⊑ b.
Proof.
  intros Hle [Ha Ha'] [Hb Hb'].
  eapply Hb'; intro i; etransitivity; eauto.
Qed.

Lemma apply_supremum {I A B} `{OType B}
  (f : A -> B) (ch : I -> A -> B) (x : A) :
  supremum f ch -> supremum (f x) (fun i => ch i x).
Proof.
  intros [Hub Hlub]; split.
  - intro i; apply Hub.
  - intros y Hy.
    simpl in Hlub.
    unfold upper_bound in Hy.
    simpl in *.
    destruct (classicT (f x ⊑ y)); auto.
    set (f' := fun a => if classicT (a = x) then y else f a).
    assert (Hf': upper_bound f' ch).
    { intros i a; unfold f'; simpl.
      destruct_classic; subst; auto; apply Hub. }
    specialize (Hlub f' Hf' x); unfold f' in Hlub.
    destruct_classic; auto; congruence.
Qed.

Corollary wcontinuous_apply {A B} `{OType B} (x : A) :
  wcontinuous (fun f : A -> B => f x).
Proof. intros ch Hch s Hs; apply apply_supremum; auto. Qed.

Lemma supremum_apply {I A B} `{Inhabited I} `{OType B} (f : A -> B) (ch : I -> A -> B) :
  (forall x, supremum (f x) (fun i => ch i x)) -> supremum f ch.
Proof.
  intro Hsup; split.
  - intros i x; apply Hsup.
  - intros g Hg x; apply Hsup; intro i; apply Hg.
Qed.

Lemma infimum_apply {I A B} `{Inhabited I} `{OType B} (f : A -> B) (ch : I -> A -> B) :
  (forall x, infimum (f x) (fun i => ch i x)) -> infimum f ch.
Proof.
  intro Hsup; split.
  - intros i x; apply Hsup.
  - intros g Hg x; apply Hsup; intro i; apply Hg.
Qed.

Lemma apply_infimum {I A B} `{Inhabited I} `{OType B}
  (f : A -> B) (ch : I -> A -> B) (x : A) :
  infimum f ch -> infimum (f x) (fun i => ch i x).
Proof.
  intros [Hlb Hglb]; split.
  - intro i; apply Hlb.
  - intros y Hy.
    simpl in Hglb.
    unfold lower_bound in Hy.
    simpl in *.
    destruct (classicT (y ⊑ f x)); auto.
    set (f' := fun a => if classicT (a = x) then y else f a).
    assert (Hf': lower_bound f' ch).
    { intros i a; unfold f'; simpl.
      destruct_classic; subst; auto; apply Hlb. }
    specialize (Hglb f' Hf' x); unfold f' in Hglb.
    destruct_classic; auto; congruence.
Qed.

Lemma continuous_monotone {A B} `{OType A} `{OType B} (f : A -> B) :
  continuous f ->
  Proper (leq ==> leq) f.
Proof.
  unfold continuous, monotone, Proper, respectful.
  intros Hf x y Hxy.
  set (ch := fun i => match i with
                   | O => x
                   | _ => y
                   end).
  assert (Hch: directed ch).
  { intros i j; unfold ch; exists (max i j); split;
      destruct i, j; simpl; auto; reflexivity. }
  assert (supremum y ch).
  { split.
    - intro i; unfold ch; destruct i; auto; reflexivity.
    - intros z Hz; specialize (Hz (S O)); auto. }
  apply Hf in H1; auto.
  destruct H1 as [Hub Hlub]; apply (Hub O).
Qed.
#[global] Hint Resolve continuous_monotone : order.

Lemma cocontinuous_antimonotone {A B} `{OType A} `{OType B} (f : A -> B) :
  cocontinuous f ->
  Proper (leq ==> flip leq) f.
Proof.
  unfold cocontinuous, antimonotone, Proper, respectful.
  intros Hf x y Hxy.
  set (ch := fun i => match i with
                   | O => x
                   | _ => y
                   end).
  assert (Hch: directed ch).
  { intros i j; unfold ch; exists (max i j); split;
      destruct i, j; simpl; auto; reflexivity. }
  assert (supremum y ch).
  { split.
    - intro i; unfold ch; destruct i; auto; reflexivity.
    - intros z Hz; specialize (Hz (S O)); auto. }
  apply Hf in H1; auto.
  destruct H1 as [Hub Hlub]; apply (Hub O).
Qed.
#[global] Hint Resolve cocontinuous_antimonotone : order.

Lemma wcontinuous_monotone {A B} `{OType A} `{OType B} (f : A -> B) :
  wcontinuous f ->
  Proper (leq ==> leq) f.
Proof.
  unfold wcontinuous, monotone, Proper, respectful.
  intros Hf x y Hxy.
  set (ch := fun i => match i with
                      | O => x
                      | _ => y
                      end).
  assert (Hch: chain ch).
  { intros []; auto; reflexivity. }
  assert (supremum y ch).
  { split.
    - intro i; unfold ch; destruct i; auto; reflexivity.
    - intros z Hz; specialize (Hz (S O)); auto. }
  apply Hf in H1; auto.
  destruct H1 as [Hub Hlub]; apply (Hub O).
Qed.
#[global] Hint Resolve wcontinuous_monotone : order.

Lemma dec_continuous_monotone {A B} `{OType A} `{OType B} (f : A -> B) :
  dec_continuous f ->
  Proper (leq ==> leq) f.
Proof.
  unfold dec_continuous, monotone, Proper, respectful.
  intros Hf x y Hxy.
  set (ch := fun i => match i with
                   | O => y
                   | _ => x
                   end).
  assert (Hch: downward_directed ch).
  { intros i j; unfold ch; exists (max i j); split;
      destruct i, j; simpl; auto; reflexivity. }
  assert (infimum x ch).
  { split.
    - intro i; unfold ch; destruct i; auto; reflexivity.
    - intros z Hz; specialize (Hz (S O)); auto. }
  apply Hf in H1; auto.
  destruct H1 as [Hlb Hglb]; apply (Hlb O).
Qed.
#[global] Hint Resolve dec_continuous_monotone : order.

Lemma dec_wcontinuous_monotone {A B} `{OType A} `{OType B} (f : A -> B) :
  dec_wcontinuous f ->
  Proper (leq ==> leq) f.
Proof.
  unfold dec_continuous, monotone, Proper, respectful.
  intros Hf x y Hxy.
  set (ch := fun i => match i with
                   | O => y
                   | _ => x
                   end).
  assert (Hch: dec_chain ch).
  { intros []; auto; reflexivity. }
  assert (infimum x ch).
  { split.
    - intro i; unfold ch; destruct i; auto; reflexivity.
    - intros z Hz; specialize (Hz (S O)); auto. }
  apply Hf in H1; auto.
  destruct H1 as [Hlb Hglb]; apply (Hlb O).
Qed.
#[global] Hint Resolve dec_wcontinuous_monotone : order.

Lemma continuous_compose {A B C} `{OType A} `{OType B} `{OType C}
  (f : A -> B) (g : B -> C) :
  continuous f ->
  continuous g ->
  continuous (g ∘ f).
Proof.
  unfold continuous.
  intros Hf Hg ch Hch x Hx; unfold compose in *.
  apply Hg.
  - apply monotone_directed; auto.
    apply continuous_monotone; auto.
  - apply Hf; auto.
Qed.

Lemma supremum_eventually_constant_at {A} `{OType A} (f : nat -> A) (x : A) :
  chain f ->
  eventually_constant_at f x ->
  supremum x f.
Proof.
  intros Hch [n0 Hn0]; split.
  - intro i.
    destruct (Nat.leb_spec n0 i).
    + specialize (Hn0 i H0); apply Hn0.
    + specialize (Hn0 n0 (le_n n0)).
      rewrite <- Hn0.
      apply chain_leq; auto; lia.
  - intros ub Hub.
    specialize (Hub n0).
    specialize (Hn0 n0 (le_n n0)); rewrite <- Hn0; auto.
Qed.

Lemma infimum_eventually_constant_at {A} `{OType A} (f : nat -> A) (x : A) :
  dec_chain f ->
  eventually_constant_at f x ->
  infimum x f.
Proof.
  intros Hch [n0 Hn0]; split.
  - intro i.
    destruct (Nat.leb_spec n0 i).
    + specialize (Hn0 i H0); apply Hn0.
    + specialize (Hn0 n0 (le_n n0)).
      rewrite <- Hn0.
      apply dec_chain_leq; auto; lia.
  - intros ub Hub.
    specialize (Hub n0).
    specialize (Hn0 n0 (le_n n0)); rewrite <- Hn0; auto.
Qed.

Lemma supremum_shift {A} `{OType A} (f : nat -> A) (a : A) :
  chain f ->
  supremum a f ->
  supremum a (shift f).
Proof.
  intros Hf [Hub Hlub]; split.
  - intro i; apply Hub.
  - intros x Hx; apply Hlub; intro i; etransitivity; eauto.
Qed.

Lemma Proper_compose_l {A B C} `{OType A} `{OType B} `{OType C}
  (f f' : A -> B) (g g' : B -> C) :
  Proper (equ ==> equ) g ->
  f === f' ->
  g === g' ->
  g ∘ f === g' ∘ f'.
Proof.
  intros Hg Hf' Hg'.
  unfold compose; apply equ_arrow; intro x.
  rewrite equ_arrow in Hf'.
  rewrite Hf'.
  rewrite equ_arrow in Hg'.
  apply Hg'.
Qed.

Lemma infimum_shift {A} `{OType A} (a : A) (f : nat -> A) :
  dec_chain f ->
  infimum a f ->
  infimum a (shift f).
Proof.
  unfold shift; intros Hch [Hlb Hglb]; split.
  - intro i; apply Hlb.
  - intros x Hx; apply Hglb; intro i; etransitivity; eauto.
Qed.

Lemma shift_supremum {A} `{OType A} (a : A) (f : nat -> A) :
  f 0 ⊑ a ->
  supremum a (shift f) ->
  supremum a f.
Proof.
  unfold shift; intros Hf0 [Hub Hlub]; split.
  - intros []; auto.
  - intros x Hx; apply Hlub; intro i; apply Hx.
Qed.

Lemma shift_supremum' {A} `{OType A} (a : A) (f g : nat -> A) :
  (exists i, g 0 ⊑ g (S i)) ->
  supremum a f ->
  shift g === f ->
  supremum a g.
Proof.
  intros Hg01 Ha Hgf.
  rewrite <- Hgf in Ha.
  apply shift_supremum; auto.
  destruct Hg01 as [i Hi].
  etransitivity; eauto.
  apply Ha.
Qed.

Corollary shift_supremum'' {A} `{OType A} (a : A) (f g : nat -> A) :
  g 0 ⊑ g 1 ->
  supremum a f ->
  shift g === f ->
  supremum a g.
Proof. intros Hg01 Ha Hgf; eapply shift_supremum'; eauto. Qed.

Lemma shift_infimum {A} `{OType A} (a : A) (f : nat -> A) :
  a ⊑ f 0 ->
  infimum a (shift f) ->
  infimum a f.
Proof.
  unfold shift; intros Hf0 [Hub Hlub]; split.
  - intros []; auto.
  - intros x Hx; apply Hlub; intro i; apply Hx.
Qed.

Lemma shift_infimum' {A} `{OType A} (a : A) (f g : nat -> A) :
  (exists i, g (S i) ⊑ g O) ->
  infimum a f ->
  shift g === f ->
  infimum a g.
Proof.
  intros Hg01 Ha Hgf.
  rewrite <- Hgf in Ha.
  apply shift_infimum; auto.
  destruct Hg01 as [i Hi].
  etransitivity; eauto.
  apply Ha.
Qed.

Corollary shift_infimum'' {A} `{OType A} (a : A) (f g : nat -> A) :
  g 1 ⊑ g 0 ->
  infimum a f ->
  shift g === f ->
  infimum a g.
Proof. intros Hg01 Ha Hgf; eapply shift_infimum'; eauto. Qed.

#[global]
  Instance monotone_id {A} `{OType A} : Proper (leq ==> leq) id.
Proof. intros ? ? Hle; apply Hle. Qed.
#[global] Hint Resolve monotone_id : order.

Lemma continuous_id {A} `{OType A} : continuous id.
Proof. intros ch Hch s Hs; apply Hs. Qed.
#[global] Hint Resolve continuous_id : order.

Lemma dec_continuous_id {A} `{OType A} : dec_continuous id.
Proof. intros ch Hch s Hs; apply Hs. Qed.
#[global] Hint Resolve dec_continuous_id : order.

Fixpoint iter_n {A} (F : A -> A) (z : A) (n : nat) : A :=
  match n with
  | O => z
  | S n' => F (iter_n F z n')
  end.

Lemma chain_iter_n' {A} `{OType A} (f : A -> A) (z : A) :
  z ⊑ f z ->
  monotone f ->
  chain (iter_n f z).
Proof. intros Hz Hf i; induction i; simpl; auto. Qed.

Lemma dec_chain_iter_n' {A} `{OType A} (f : A -> A) (z : A) :
  f z ⊑ z ->
  monotone f ->
  dec_chain (iter_n f z).
Proof. intros Hz Hf i; induction i; simpl; auto. Qed.

Lemma monotone_iter_n {A} `{OType A} (f g : A -> A) (x y : A) (i : nat) :
  (forall x y, x ⊑ y -> f x ⊑ g y) ->
  x ⊑ y ->
  iter_n f x i ⊑ iter_n g y i.
Proof. revert f g x y; induction i; intros f g x y; simpl; auto. Qed.

Lemma leq_impl (P Q : Prop) :
  P ⊑ Q ->
  P -> Q.
Proof. intro H; apply H. Qed.

Lemma equ_iff (P Q : Prop) :
  P === Q ->
  P <-> Q.
Proof. firstorder. Qed.

Lemma iter_n_eq {A} `{OType A} (F G : A -> A) (a b : A) (i : nat) :
  (forall x y, x === y -> F x === G y) ->
  a === b ->
  iter_n F a i === iter_n G b i.
Proof. revert F G a b; induction i; intros F G a b HFG Hab; simpl; auto. Qed.

Lemma chain_id {A} `{OType A} :
  chain (fun i : nat => i).
Proof. intro i; simpl; lia. Qed.
#[global] Hint Resolve chain_id : order.

Lemma supremum_cond {A} `{OType A} (b : bool) (x y : A) (f g : nat -> A) :
  supremum x f ->
  supremum y g ->
  supremum (if b then x else y) (fun i => if b then f i else g i).
Proof. intros Hf Hg; destruct b; auto. Qed.

Lemma infimum_cond {A} `{OType A} (b : bool) (x y : A) (f g : nat -> A) :
  infimum x f ->
  infimum y g ->
  infimum (if b then x else y) (fun i => if b then f i else g i).
Proof. intros Hf Hg; destruct b; auto. Qed.

Lemma iter_n_const {A} `{OType A} (F : A -> A) (z : A) (n : nat) :
  Proper (leq ==> leq) F ->  
  F z === z ->
  iter_n F z n === z.
Proof.
  intros Hmono HFz.
  induction n; simpl; try reflexivity.
  rewrite IHn; auto.
Qed.

(* Pointwise variant for function spaces. *)
Corollary iter_n_const' {A B} `{OType B}
  (F : (A -> B) -> A -> B) (z : A -> B) (n : nat) (x : A) :
  Proper (leq ==> leq) F ->
  F z === z ->
  iter_n F z n x === z x.
Proof. intros Hmono HFz; apply equ_arrow; apply iter_n_const; auto. Qed.

Lemma iter_n_bounded {A} `{OType A} (F : A -> A) (z ub : A) (n : nat) :
  z ⊑ ub ->
  (forall x, x ⊑ ub -> F x ⊑ ub) ->
  iter_n F z n ⊑ ub.
Proof. revert z ub; induction n; intros z ub Hz HF; simpl; auto. Qed.

(* Types for which the symmetric closure of the order relation
   coincides with propositional equality. Obviously, depends on the
   choice of order relation. *)
Class ExtType (A : Type) `{OType A} : Type :=
  { ext : forall (a b : A), a === b -> a = b }.

#[global]
  Instance ExtType_Proper {A B} `{ExtType A} `{OType B} (f : A -> B)
  : Proper (equ ==> equ) f.
Proof. intros x y Hxy; eapply ext in Hxy; subst; reflexivity. Qed.

#[global]
  Instance ExtType_arrow {A B} `{ExtType B} : ExtType (A -> B).
Proof.
  constructor; intros f g Hfg.
  ext x; rewrite equ_arrow in Hfg; specialize (Hfg x); apply ext; auto.
Qed.

#[global]
  Instance ExtType_Prop : ExtType Prop.
Proof. constructor; apply propositional_extensionality. Qed.

Lemma continuous_cocontinuous_compose {A B C} `{OType A} `{OType B} `{OType C}
  (f : A -> B) (g : B -> C) :
  continuous f ->
  cocontinuous g ->
  cocontinuous (g ∘ f).
Proof.
  unfold continuous, cocontinuous.
  intros Hf Hg ch Hch x Hx; unfold compose in *.
  apply Hg.
  - apply monotone_directed; auto.
    apply continuous_monotone; auto.
  - apply Hf; auto.
Qed.

Lemma supremum_Prop (P : Prop) (f : nat -> Prop) :
  (P <-> exists i, f i) ->
  supremum P f.
Proof.
  intros [H0 H1]; split.
  - intros i Hfi; apply H1; exists i; auto.
  - intros Q HQ HP.
    apply H0 in HP.
    destruct HP as [i Hfi].
    eapply HQ; eauto.
Qed.

Lemma infimum_Prop (P : Prop) (f : nat -> Prop) :
  (P <-> forall i, f i) ->
  infimum P f.
Proof.
  intros [H0 H1]; split.
  - intros i Hfi; apply H0; auto.
  - intros Q HQ HP; apply H1; intro i; apply HQ; auto.
Qed.

Lemma equ_list {A} (l1 l2 : list A) :
  l1 === l2 -> l1 = l2.
Proof. intros []; apply is_prefix_antisym; auto. Qed.
