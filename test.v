(** * Test programs. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Basics QArith String.
Local Open Scope program_scope.
Local Open Scope string_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From cwp Require Import compile cpGCL cpo cwp eR itree order tactics tree.

Local Open Scope cpGCL_scope.
(* Local Open Scope nat_scope. *)

Definition incr (v : val) : val :=
  match v with
  | vnat n => vnat (S n)
  | _ => v
  end.

Definition plus (v1 v2 : val) : val :=
  match (v1, v2) with
  | (vnat n, vnat m) => vnat (n + m)
  | _ => vnat O
  end.

Definition flip (x : string) (p : Q) : cpGCL :=
  CChoice (const p) (fun b => x <-- b).

(* (* Expected value is 1. *) *)
(* Definition count_heads : cpGCL := *)
(*   let i := O in *)
(*   let x := S O in *)
(*   i <-- O; *)
(*   x <-- true; *)
(*   while (fun s => as_bool (s x)) do *)
(*       CChoice (const (1#2)) *)
(*         (fun b => if b then *)
                 
(*         (i <-- fun s => incr (s i)) *)
(*         (x <-- false) *)
(*   end. *)

From Coq Require Import ExtrOcamlBasic ExtrOcamlString.

(* Extract Inductive bool => "bool" [ "true" "false" ]. *)
(* Extract Inductive list => "list" [ "[]" "(::)" ]. *)

(* Definition sampler : itree boolE nat := *)
(*   ITree.map (fun s => as_nat (s O)) (cpGCL_to_itree count_heads empty). *)
(* Extraction "extract/test/heads.ml" sampler. *)

(* Definition uniform (x : string) (n : nat) : cpGCL := *)
(*   CUniform (const n) (fun i => x <-- const i). *)
(* Definition sampler : itree boolE nat := *)
(*   ITree.map (fun s => as_nat (s EmptyString)) *)
(*     (cpGCL_to_itree (uniform EmptyString 10000) empty). *)
(* Extraction "extract/test/uniform.ml" sampler. *)

Definition gp : cpGCL :=
  flip "f" (1#2);
  CChoice (const (1#2))
    (fun b => if b then 
             "r" <-- (fun s => s "f")
           else
             "r" <-- (fun s => true));
  obs (fun s => s "r").

From Coq Require Import ExtrOcamlBasic ExtrOcamlString.

Definition sampler : itree boolE bool :=
  ITree.map (fun s => as_bool (s "f")) (cpGCL_to_itree gp empty).
Extraction "extract/test/gp.ml" sampler.

Require Import cotree cotcwp.

Definition gp_cotree : cotree bool bool := icotree sampler.

Definition gp_chain (n : nat) : atree bool bool := tprefix n gp_cotree.

Eval compute in (List.map (Qred ∘ btwpQ (fun b : bool => if b then 1%Q else 0%Q)) (misc.prefix gp_chain 30)).

Inductive mytree (A : Type) : Type :=
| mybot : mytree A
| myleaf : A -> mytree A
| mytau : mytree A -> mytree A
| mynode : mytree A -> mytree A -> mytree A.

Fixpoint mytree_of_atree {A} (t : atree bool A) : mytree A :=
  match t with
  | abot => mybot
  | aleaf x => myleaf x
  | atau t => mytau (mytree_of_atree t)
  | anode k => mynode (mytree_of_atree (k true)) (mytree_of_atree (k false))
  end.

Fixpoint string_of_mytree (t : mytree string) : string :=
  match t with
  | mybot => "⊥"
  | myleaf s => "(Leaf " ++ s ++ ")"
  | mytau t => "(Tau " ++ string_of_mytree t ++ ")"
  | mynode l r => "(Node " ++ string_of_mytree l ++ " " ++ string_of_mytree r ++ ")"
  end.

(* Eval compute in (List.map mytree_of_atree (misc.prefix gp_chain 4)). *)

(* Eval compute in (List.map (string_of_mytree ∘ mytree_of_atree ∘ *)
(*                              atree_map (fun b : bool => if b then "true" else "false")) *)
(*                    (misc.prefix gp_chain 10)). *)
