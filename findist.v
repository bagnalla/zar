(** * Samplers for finite distributions. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Streams Basics QArith String Lia Lqa List.
Local Open Scope program_scope.
Local Open Scope string_scope.
Import ListNotations.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From zar Require Import
  cotree cocwp cpo equidistribution eR itree misc
  order prelude tactics tree uniform.

Fixpoint bin_index (weights : list nat) (i : nat) : nat :=
  match weights with
  | [] => O
  | w :: ws => if Nat.ltb i w then O else S (bin_index ws (i - w))
  end.

Definition findist_btree (weights : list nat) : btree (unit + nat) :=
  reduce_btree' (btree_map (sum_map id (bin_index weights))
                   (uniform_btree' (list_sum weights))).

(* Eval compute in (findist_btree [1%nat; 2%nat]). *)

Definition findist_tree_open (weights : list nat) : tree (unit + nat) :=
  btree_to_tree (findist_btree weights).

Definition findist_tree (weights : list nat) : tree nat :=
  let t := findist_tree_open weights in
  Fix (inl tt) is_inl (fun _ => t) (cotuple (fun _ => Leaf O) (@Leaf _)).

Definition findist_itree (weights : list nat) : itree boolE nat :=
  to_itree (findist_tree weights).

(* TODO: do extraction test first before proving anything. *)

(** Extraction. *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
Extraction "extract/findist/findist.ml" findist_itree.
