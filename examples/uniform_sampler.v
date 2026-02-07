(** * Generic uniform sampler extraction. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Streams Basics QArith String Lqa.
Local Open Scope program_scope.
Local Open Scope string_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From cwp Require Import cpGCL debias itree misc uniform.

(** Extracting the sampler. *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.

(* Definition sampler (n : nat) : itree boolE nat := *)
(*   ITree.map (fun s => as_nat (s ϵ)) (to_itree (uniform_tree n)). *)

Definition sampler (n : nat) : itree boolE nat :=
  ITree.map (fun s => as_nat (s ϵ)) (to_itree (uniform_tree n)).

Extraction "extract/uniform/uniform.ml" sampler.
