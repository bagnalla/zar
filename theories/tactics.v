(** * Useful tactics. *)

From Coq Require Import
  Eqdep
  FunctionalExtensionality
  Lra
.

Require Import ITree.ITree.
Require Import Paco.paco.

Ltac existT_inv :=
  repeat match goal with
    | [ H : existT ?a ?b ?c = existT ?d ?e ?f |- _] =>
        apply inj_pair2 in H; inversion H; clear H; subst
    end.

Ltac obs_sym :=
  repeat match goal with
    | [ H : ?x = observe ?y |- _ ] => symmetry in H
    end.

Ltac obs_inv :=
  obs_sym;
  match goal with
  | [ H1 : observe ?t = RetF ?x, H2 : observe ?t = RetF ?y |- _] =>
      rewrite H1 in H2; inversion H2; subst; clear H2
  | [ H1 : observe ?t = TauF ?x, H2 : observe ?t = TauF ?y |- _] =>
      rewrite H1 in H2; inversion H2; subst; clear H2
  | [ H1 : observe ?t = VisF ?a ?b, H2 : observe ?t = VisF ?c ?d |- _] =>
      rewrite H1 in H2; inversion H2; subst; clear H2; existT_inv
  end.

Ltac destruct_upaco :=
  repeat match goal with
    | [ H: context[upaco1 _ bot1 _] |- _] =>
        destruct H as [H | H]; try solve[inversion H]
    | [ H: context[upaco2 _ bot2 _ _] |- _] =>
        destruct H as [H | H]; try solve[inversion H]
    end.

Ltac dupaco := destruct_upaco.

Ltac iauto :=
  obs_sym;
  match goal with
  | [ H : observe ?t = ?x |- context[observe ?t] ] => rewrite H
  end;
  auto.

Ltac inv H := inversion H; subst; clear H.

Ltac ext i := extensionality i.

Ltac dq H :=
  destruct H as [Hq Hq'];
  apply Qreals.Qle_Rle in Hq;
  apply Qreals.Qle_Rle in Hq'.

Ltac destr :=
  match goal with
  | [ |- context[match ?x with _ => _ end] ] => destruct x
  end.

(* Taken from itree library. *)
Ltac rewrite_everywhere lem :=
  progress ((repeat match goal with [H: _ |- _] => rewrite lem in H end); repeat rewrite lem).
Ltac rewrite_everywhere_except lem X :=
  progress ((repeat match goal with [H: _ |- _] =>
                                      match H with X => fail 1 | _ => rewrite lem in H end
               end); repeat rewrite lem).

Ltac refl := reflexivity.

(* For proving well-formedness of cpGCL programs. *)
Ltac wf := constructor; try solve [repeat constructor]; auto.
