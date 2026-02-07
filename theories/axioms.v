(** * Axioms and tactics for non-constructive reasoning. *)

(** We assume excluded middle and indefinite description, together
  allowing non-computable case analysis in the universe Set. Elsewhere
  we also use function extensionality and an extensionality axiom for
  cotrees (cotree.v). *)

From Coq Require Import
  ClassicalChoice
  IndefiniteDescription
.

From zar Require Import
  misc
  tactics
.

Lemma classicT' : forall (P : Prop), { x : {P} + {~ P} | True }.
Proof.
  intro P; apply constructive_indefinite_description.
  destruct (classic P) as [H|H].
  - exists (left H); auto.
  - exists (right H); auto.
Qed.

(** Strong excluded middle. *)
Theorem classicT : forall (P : Prop), {P} + {~ P}.
Proof. intro P; generalize (classicT' P); intros []; auto. Qed.

(** Strong limited principle of omniscience. Follows trivially from
  excluded middle, even without the decidability of [P], but we leave
  it in this form so it can easily be changed to an axiom if the use
  of excluded middle is ever eliminated from the development. *)
Theorem strong_LPO : forall {P : nat -> Prop},
    (forall n, {P n} + {~ P n}) ->
    {exists n, P n} + {~ exists n, P n}.
Proof. intros P H; apply classicT. Qed.

(** Optional variant of strong LPO. *)
Definition LPO_option {P : nat -> Prop} (H : forall n, {P n} + {~ P n}) : option nat :=
  match strong_LPO H with
  | left pf => Some (proj1_sig (constructive_indefinite_description _ pf))
  | right _ => None
  end.

Ltac destruct_LPO :=
  match goal with
  | [ H: context[if strong_LPO ?y then _ else _] |- _] =>
    destruct (strong_LPO y)
  | [ |- context[if strong_LPO ?y then _ else _] ] =>
      destruct (strong_LPO y)
  | [ |- context[match strong_LPO ?y with _ => _ end] ] =>
    destruct (strong_LPO y)
  end.

Lemma LPO_option_some {P : nat -> Prop} (H : forall n, {P n} + {~ P n}) (n : nat) :
  LPO_option H = Some n ->
  P n.
Proof.
  unfold LPO_option.
  destruct_LPO; intro Heq; inv Heq.
  destruct (constructive_indefinite_description P e); auto.
Qed.

Lemma LPO_option_none {P : nat -> Prop} (H : forall n, {P n} + {~ P n}) (n : nat) :
  LPO_option H = None ->
  ~ P n.
Proof.
  unfold LPO_option.
  destruct_LPO; intro Heq; inv Heq.
  intro HC; apply n0; exists n; auto.
Qed.

Ltac destruct_classic :=
  match goal with
  | [ H: context[if classicT ?y then _ else _] |- _] =>
    destruct (classicT y)
  | [ |- context[if classicT ?y then _ else _] ] =>
    destruct (classicT y)
  end.

Ltac contra H :=
  match goal with
  | [ |- ?x ] => destruct (classic x) as [?|H]; auto; exfalso
  end.

Lemma contrapositive (P Q : Prop) :
  (~ Q -> ~ P) ->
  P -> Q.
Proof. intros H HP. destruct (classic Q); intuition. Qed.
