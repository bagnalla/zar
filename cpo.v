(** * Complete partial orders and suprema/infima operators. *)

From Coq Require Import
  Basics
  PeanoNat
  Equivalence
  ClassicalChoice
  IndefiniteDescription (* for suprema/infima *)
.

Local Open Scope program_scope.
Local Open Scope equiv_scope.

From zar Require Import
  axioms
  misc
  order
.

Local Open Scope order_scope.

(** [A] is a CPO (complete partial order) whenever suprema of countable
    collections exist. *)
Class CPO (A : Type) `{OType A} : Prop :=
  { exists_sup : forall f : nat -> A, exists s, supremum s f }.

(** [A] is a dCPO (directed-complete partial order) whenever suprema of
    directed countable collections exist. *)
Class dCPO (A : Type) `{OType A} : Prop :=
  { exists_dsup : forall f : nat -> A, directed f -> exists s, supremum s f }.

(** [A] is a lCPO (lower-complete partial order) whenever infima of
    countable collections exist. *)
Class lCPO (A : Type) `{OType A} : Prop :=
  { exists_inf : forall f : nat -> A, exists s, infimum s f }.

(** [A] is a ldCPO (lower-directed-complete partial order) whenever
    infima of downward-directed countable collections exist. *)
Class ldCPO (A : Type) `{OType A} : Prop :=
  { exists_dinf : forall f : nat -> A, downward_directed f -> exists s, infimum s f }.

(* Definition sup_prim {A} `{OType A} (f : nat -> A) *)
(*   : { a : A | (exists b, supremum b f) -> supremum a f }. *)
(* Proof. *)
(*   apply constructive_indefinite_description. *)
(*   destruct (classic (exists a, supremum a f)). *)
(*   - destruct H0 as [a Ha]; exists a; intros; auto. *)
(*   - exists (f O); intros [a Ha]; exfalso; apply H0; exists a; auto. *)
(* Qed. *)

Lemma ex_ex_supremum {A} `{OType A} (f : nat -> A) :
  exists x : A, (exists b : A, supremum b f) -> supremum x f.
Proof.
  destruct (classic (exists a, supremum a f)).
  - destruct H0 as [a Ha]; exists a; intros; auto.
  - exists (f O); intros [a Ha]; exfalso; apply H0; exists a; auto.
Qed.

(** Primitive non-constructive supremum operation for ordered type
    [A]. Given a countable collection [f] of elements of type [A],
    produce an element [a] such that [a] is the supremum of [f]
    whenever such a supremum provably exists. Derived from excluded
    middle + indefinite description. *)
Definition sup_prim {A} `{OType A} (f : nat -> A)
  : { a : A | (exists b, supremum b f) -> supremum a f } :=
  constructive_indefinite_description _ (ex_ex_supremum _).

Lemma ex_ex_infimum {A} `{OType A} (f : nat -> A) :
  exists x : A, (exists b : A, infimum b f) -> infimum x f.
Proof.
  destruct (classic (exists a, infimum a f)).
  - destruct H0 as [a Ha]; exists a; intros; auto.
  - exists (f O); intros [a Ha]; exfalso; apply H0; exists a; auto.
Qed.

(* See above. *)
Definition inf_prim {A} `{OType A} (f : nat -> A)
  : { a : A | (exists b, infimum b f) -> infimum a f } :=
  constructive_indefinite_description _ (ex_ex_infimum _).

(* Take the supremum of countable collection [f]. *)
Definition sup {A} `{OType A} (f : nat -> A) : A := proj1_sig (sup_prim f).

(* [sup f] is the supremum of [f] whenever [A] is a CPO. *)
Lemma sup_spec {A} `{CPO A} (f : nat -> A) : supremum (sup f) f.
Proof. unfold sup; destruct (sup_prim f) as [a Ha]; apply Ha, H0. Qed.

(* [sup f] is the supremum of [f] whenever [A] is a dCPO and [f] is
   directed. *)
Lemma dsup_spec {A} `{dCPO A} (f : nat -> A) :
  directed f -> supremum (sup f) f.
Proof. intro Hf; unfold sup; destruct sup_prim; simpl; apply s, H0; auto. Qed.

(* Take the infimum of countable collection [f]. *)
Definition inf {A} `{OType A} (f : nat -> A) : A := proj1_sig (inf_prim f).

(* [inf f] is the infimum of [f] whenever [A] is an lCPO. *)
Lemma inf_spec {A} `{lCPO A} (f : nat -> A) : infimum (inf f) f.
Proof. unfold inf; destruct (inf_prim f) as [a Ha]; apply Ha, H0. Qed.

(* [inf f] is the infimum of [f] whenever [A] is an ldCPO and [f] is
   downward-directed. *)
Lemma dinf_spec {A} `{ldCPO A} (f : nat -> A) :
  downward_directed f -> infimum (inf f) f.
Proof. intro Hf; unfold inf; destruct inf_prim; simpl; apply i, H0; auto. Qed.

#[global]
  Instance CPO_dCPO {A} `{CPO A} : dCPO A.
Proof. constructor; intros f Hf; apply H0. Qed.

#[global]
  Instance lCPO_ldCPO {A} `{lCPO A} : ldCPO A.
Proof. constructor; intros f Hf; apply H0. Qed.

(** [Prop] has suprema and infima. *)

#[global]
  Instance CPO_Prop : CPO Prop.
Proof.
  constructor; intro f; exists (exists i, f i); split.
  - intros i Hi; exists i; auto.
  - intros ub Hub [i Hi]; eapply Hub; eauto.
Qed.

#[global]
  Instance LCPO_Prop : lCPO Prop.
Proof.
  constructor; intros f; exists (forall i, f i); split.
  - intros i Hi; auto.
  - intros ub Hub x i; apply Hub; auto.
Qed.

Lemma ge_inf {A} `{lCPO A} (f : nat -> A) (a : A) (i : nat) :
  f i ⊑ a ->
  inf f ⊑ a.
Proof.
  intros Hleq; generalize (inf_spec f); intros [Hub Hlub]; auto.
  etransitivity; eauto.
Qed.

Lemma le_inf {A} `{lCPO A} (f : nat -> A) (a : A) :
  lower_bound a f ->
  a ⊑ inf f.
Proof. intros Hbound; generalize (inf_spec f); intros [Hlb Hglb]; auto. Qed.

Lemma ge_sup {A} `{CPO A} (f : nat -> A) (a : A) :
  upper_bound a f ->
  sup f ⊑ a.
Proof. intros Hbound; generalize (sup_spec f); intros [Hub Hlub]; auto. Qed.

Lemma le_sup {A} `{CPO A} (f : nat -> A) (a : A) (i : nat) :
  a ⊑ f i ->
  a ⊑ sup f.
Proof.
  intros Hleq; generalize (sup_spec f); intros [Hub Hlub]; auto.
  etransitivity; eauto.
Qed.

#[global]
  Instance ldCPO_arrow {A B} `{ldCPO B} : ldCPO (A -> B).
Proof.
  constructor; intros f Hf.
  exists (fun x => inf (fun n => f n x)).
  assert (Hf': forall x, downward_directed (fun i => f i x)).
  { intros x j k.
    specialize (Hf j k); destruct Hf as [l [Hl Hl']].
    exists l; auto. }
  split.
  - intros i x; specialize (Hf' x).
    apply dinf_spec in Hf'; apply Hf'.
  - intros g Hlb x.
    specialize (Hf' x).
    apply dinf_spec in Hf'.
    apply Hf'; intro; apply Hlb.
Qed.

#[global]
  Instance lCPO_arrow {A B} `{lCPO B} : lCPO (A -> B).
Proof.
  constructor; intros f.
  exists (fun x => inf (fun n => f n x)).
  split.
  - intros i x; eapply ge_inf; reflexivity.
  - intros g Hg x; apply le_inf; intro i; apply Hg.
Qed.

#[global]
  Instance dCPO_arrow {A B} `{dCPO B} : dCPO (A -> B).
Proof.
  constructor; intros f Hf.
  exists (fun x => sup (fun n => f n x)).
  assert (Hf': forall x, directed (fun i => f i x)).
  { intros x j k.
    specialize (Hf j k); destruct Hf as [l [Hl Hl']].
    exists l; auto. }
  split.
  - intros i x; specialize (Hf' x).
    apply dsup_spec in Hf'; apply Hf'.
  - intros g Hub x.
    specialize (Hf' x).
    apply dsup_spec in Hf'.
    apply Hf'; intro; apply Hub.
Qed.

#[global]
  Instance CPO_arrow {A B} `{CPO B} : CPO (A -> B).
Proof.
  constructor; intros f.
  exists (fun x => sup (fun n => f n x)).
  split.
  - intros i x; eapply le_sup; reflexivity.
  - intros g Hg x; apply ge_sup; intro i; apply Hg.
Qed.

Lemma sup_const {A} `{CPO A} (a : A) :
  sup (fun _ => a) === a.
Proof.
  eapply supremum_unique.
  { apply sup_spec; auto with order. }
  apply supremum_const.
Qed.

Lemma sup_const' {A} `{CPO A} (f : nat -> A) (a : A) :
  f === const a ->
  sup f === a.
Proof.
  intro Hf.
  rewrite equ_arrow in Hf.
  unfold const in Hf.
  eapply supremum_unique.
  - apply sup_spec; intros ? j; exists j; split; rewrite !Hf; reflexivity.
  - apply supremum_const'; apply equ_arrow; intro i; apply Hf.
Qed.

Lemma inf_const {A} `{lCPO A} (a : A) :
  inf (fun _ => a) === a.
Proof.
  eapply infimum_unique.
  { apply inf_spec; auto with order. }
  apply infimum_const.
Qed.

Lemma inf_const' {A} `{lCPO A} (f : nat -> A) (a : A) :
  f === const a ->
  inf f === a.
Proof.
  intro Hf.
  rewrite equ_arrow in Hf.
  unfold const in Hf.
  eapply infimum_unique.
  - apply inf_spec; intros ? j; exists j; split; rewrite !Hf; reflexivity.
  - apply infimum_const'; apply equ_arrow; intro i; apply Hf.
Qed.

Lemma le_dsup {A} `{dCPO A} (f : nat -> A) (a : A) (i : nat) :
  directed f ->
  a ⊑ f i ->
  a ⊑ sup f.
Proof.
  intros Hf Hleq.
  generalize (dsup_spec f); intros [Hub Hlub]; auto.
  etransitivity; eauto.
Qed.

Lemma le_dinf {A} `{ldCPO A} (f : nat -> A) (a : A) :
  downward_directed f ->
  lower_bound a f ->
  a ⊑ inf f.
Proof.
  intros Hf Hbound; generalize (dinf_spec f); intros [Hlb Hglb]; auto.
Qed.

Lemma ge_dsup {A} `{dCPO A} (f : nat -> A) (a : A) :
  directed f ->
  upper_bound a f ->
  sup f ⊑ a.
Proof.
  intros Hf Hbound; generalize (dsup_spec f); intros [Hub Hlub]; auto.
Qed.

Lemma ge_dinf {A} `{ldCPO A} (f : nat -> A) (a : A) (i : nat) :
  downward_directed f ->
  f i ⊑ a ->
  inf f ⊑ a.
Proof.
  intros Hf Hleq.
  generalize (dinf_spec f); intros [Hub Hlub]; auto.
  etransitivity; eauto.
Qed.

Lemma supremum_sup {A} `{dCPO A} (f : nat -> A) (a : A) :
  supremum a f ->
  sup f === a.
Proof.
  intros Hsup; eapply supremum_unique; eauto.
  unfold sup; destruct (sup_prim f); apply s; exists a; auto.
Qed.

Lemma infimum_inf {A} `{ldCPO A} (f : nat -> A) (a : A) :
  infimum a f ->
  inf f === a.
Proof.
  intros Hinf; eapply infimum_unique; eauto.
  unfold inf; destruct (inf_prim f); apply i; exists a; auto.
Qed.

Lemma sup_apply {A B} `{CPO B} (f : nat -> A -> B) (x : A) :
  sup f x === sup (fun i => f i x).
Proof.
  symmetry.
  apply supremum_sup; auto with order.
  apply apply_supremum, sup_spec; auto.
Qed.

Lemma dsup_apply {A B} `{dCPO B} (f : nat -> A -> B) (x : A) :
  directed f ->
  sup f x === sup (fun i => f i x).
Proof.
  intro Hf; symmetry; apply supremum_sup, apply_supremum, dsup_spec; auto.
Qed.

Lemma inf_apply {A B} `{lCPO B} (f : nat -> A -> B) (x : A) :
  inf f x === inf (fun i => f i x).
Proof.
  symmetry; apply infimum_inf; auto with order.
  apply apply_infimum, inf_spec; auto.
Qed.

Lemma continuous_sup {A B} `{dCPO A} `{dCPO B} (f : A -> B) (ch : nat -> A) :
  continuous f ->
  directed ch ->
  f (sup ch) === sup (f ∘ ch).
Proof.
  intros Hf Hch; symmetry.
  apply supremum_sup, Hf; auto.
  apply dsup_spec; auto.
Qed.

Lemma cocontinuous_sup {A B} `{dCPO A} `{ldCPO B} (f : A -> B) (ch : nat -> A) :
  cocontinuous f ->
  directed ch ->
  f (sup ch) === inf (f ∘ ch).
Proof.
  intros Hf Hch; symmetry.
  apply infimum_inf, Hf; auto.
  apply dsup_spec; auto.
Qed.

Lemma wcontinuous_sup {A B} `{dCPO A} `{dCPO B} (f : A -> B) (ch : nat -> A) :
  wcontinuous f ->
  chain ch ->
  f (sup ch) === sup (f ∘ ch).
Proof.
  intros Hf Hch; symmetry.
  apply supremum_sup, Hf; auto.
  apply dsup_spec; auto with order.
Qed.

Lemma dec_continuous_inf {A B} `{ldCPO A} `{ldCPO B} (f : A -> B) (ch : nat -> A) :
  dec_continuous f ->
  downward_directed ch ->
  f (inf ch) === inf (f ∘ ch).
Proof.
  intros Hf Hch; symmetry.
  apply infimum_inf, Hf; auto.
  apply dinf_spec; auto.
Qed.

Lemma dec_cocontinuous_inf {A B} `{ldCPO A} `{dCPO B} (f : A -> B) (ch : nat -> A) :
  dec_cocontinuous f ->
  downward_directed ch ->
  f (inf ch) === sup (f ∘ ch).
Proof.
  intros Hf Hch; symmetry.
  apply supremum_sup, Hf; auto.
  apply dinf_spec; auto.
Qed.

Lemma dec_wcontinuous_inf {A B} `{ldCPO A} `{ldCPO B} (f : A -> B) (ch : nat -> A) :
  dec_wcontinuous f ->
  dec_chain ch ->
  f (inf ch) === inf (f ∘ ch).
Proof.
  intros Hf Hch; symmetry.
  apply infimum_inf, Hf; auto.
  apply dinf_spec; auto with order.
Qed.

Lemma Proper_sup {A} `{CPO A} (f g : nat -> A) :
  directed f ->
  directed g ->
  f === g ->
  sup f === sup g.
Proof.
  intros Hf Hg Hfg.
  eapply supremum_unique.
  - apply sup_spec; auto.
  - rewrite Hfg; apply sup_spec; auto.
Qed.

Lemma sup_shift {A} `{CPO A} (f : nat -> A) :
  chain f ->
  sup (shift f) === sup f.
Proof.
  intro Hf; apply supremum_sup; auto with order.
  apply supremum_shift; auto.
  apply sup_spec; auto with order.
Qed.

Lemma sup_shift' {A} `{dCPO A} (f g : nat -> A) :
  chain f ->
  g === shift f ->
  sup f === sup g.
Proof.
  intros Hch Heq; subst.
  symmetry.
  apply supremum_sup.
  rewrite Heq; apply supremum_shift, dsup_spec; auto with order.
Qed.

Lemma inf_shift' {A} `{ldCPO A} (f g : nat -> A) :
  dec_chain f ->
  g === shift f ->
  inf f === inf g.
Proof.
  intros Hch Heq; subst.
  symmetry.
  apply infimum_inf.
  rewrite Heq; apply infimum_shift, dinf_spec; auto with order.
Qed.

Lemma dsup_intro (P : nat -> Prop) (i : nat) :
  directed P ->
  P i ->
  sup P.
Proof.
  intros Hdir HP.
  generalize (dsup_spec _ Hdir); intros [Hub Hlub].
  eapply Hub; eauto.
Qed.

Lemma dsup_elim (P : nat -> Prop) :
  directed P ->
  sup P ->
  exists i, P i.
Proof.
  intros Hdir HP.
  generalize (dsup_spec _ Hdir); intros [Hub Hlub].
  apply Hlub; auto.
  intros i H'; exists i; apply H'.
Qed.

(** Compute the least fixed point of F by taking the supremum of the
    chain obtained by repeated iteration of F starting from z. *)
Definition iter {A} `{OType A} (F : A -> A) (z : A) : A :=
  sup (iter_n F z).

(** Compute the greatest fixed point of F by taking the infimum of the
    decreasing chain obtained by repeated iteration of F starting from z. *)
Definition dec_iter {A} `{OType A} (F : A -> A) (z : A) : A :=
  inf (iter_n F z).

(** [iter F z] is a fixed point of [F]. *)
Lemma iter_unfold {A} `{dCPO A} (F : A -> A) (z : A) :
  wcontinuous F ->
  z ⊑ F z ->
  iter F z === F (iter F z).
Proof.
  unfold iter.
  intros HF Hle.
  assert (Hchain: chain (iter_n F z)).
  { apply chain_iter_n'; auto.
    apply wcontinuous_monotone; auto. }
  eapply wcontinuous_sup in HF.
  2: { eauto. }
  rewrite HF; clear HF Hle.
  unfold compose.
  apply sup_shift'; auto.
  apply equ_arrow; intro i; reflexivity.
Qed.

(** [dec_iter F z] is a fixed point of [F]. *)
Lemma dec_iter_unfold {A} `{lCPO A} (F : A -> A) (z : A) :
  dec_wcontinuous F ->
  F z ⊑ z ->
  dec_iter F z === F (dec_iter F z).
Proof.
  unfold dec_iter.
  intros HF Hle.
  assert (Hchain: dec_chain (iter_n F z)).
  { apply dec_chain_iter_n'; auto.
    apply dec_wcontinuous_monotone; auto. }
  eapply dec_wcontinuous_inf in HF; eauto.
  rewrite HF; clear HF Hle.
  unfold compose.
  apply inf_shift'; auto.
  apply equ_arrow; intro i; reflexivity.
Qed.

Lemma dsup_apply_ext {A B} `{dCPO B} {_ : ExtType B} (f : nat -> A -> B) (x : A) :
  directed f ->
  sup f x = sup (fun i => f i x).
Proof.
  intro Hf; symmetry; apply ext, supremum_sup, apply_supremum, dsup_spec; auto.
Qed.

Lemma monotone_dsup {A} `{dCPO A} (f g : nat -> A) :
  directed f ->
  directed g ->
  (forall i, f i ⊑ g i) ->
  sup f ⊑ sup g.
Proof.
  intros Hf Hg Hfg; apply ge_dsup; auto.
  intro i; etransitivity; eauto; apply dsup_spec; auto.
Qed.

Lemma monotone_sup {A} `{CPO A} (f g : nat -> A) :
  (forall i, f i ⊑ g i) ->
  sup f ⊑ sup g.
Proof.
  intros Hfg; apply ge_sup; auto.
  intro i; etransitivity; eauto; apply sup_spec; auto.
Qed.

Lemma monotone_dinf {A} `{ldCPO A} (f g : nat -> A) :
  downward_directed f ->
  downward_directed g ->
  (forall i, f i ⊑ g i) ->
  inf f ⊑ inf g.
Proof.
  intros Hf Hg Hfg; apply le_dinf; auto.
  intro i; etransitivity; eauto; apply dinf_spec; auto.
Qed.

Lemma monotone_inf {A} `{lCPO A} (f g : nat -> A) :
  (forall i, f i ⊑ g i) ->
  inf f ⊑ inf g.
Proof.
  intros Hfg; apply le_inf; auto.
  intro i; etransitivity; eauto; apply inf_spec; auto.
Qed.

Lemma Proper_inf {A} `{ldCPO A} (f g : nat -> A) :
  downward_directed f ->
  downward_directed g ->
  f === g ->
  inf f === inf g.
Proof.
  intros Hf Hg Hfg; split; apply monotone_dinf; auto; intro i; apply Hfg.
Qed.

Lemma continuous_supP {A} `{dCPO A} (f : A -> Prop) (ch : nat -> A) :
  continuous f ->
  directed ch ->
  f (sup ch) <-> sup (f ∘ ch).
Proof.
  intros Hf Hch.
  apply equ_iff, continuous_sup; auto.
Qed.
