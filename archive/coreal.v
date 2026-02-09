(** * Real number algebraic CPO. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  Equivalence
  Lia
  Morphisms
  Equality
.
Local Open Scope program_scope.
Local Open Scope equiv_scope.

From Coq Require Import
  Reals
  Raxioms
  Rpower
  FunctionalExtensionality
  ClassicalChoice
.

From cwp Require Import
  aCPO
  axioms
  cpo
  misc
  order
  tactics
.

Local Open Scope order_scope.

Create HintDb cotree.

(* Definition areal  *)
