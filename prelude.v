(** cpGCL prelude library. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Basics QArith String.
Local Open Scope program_scope.
Local Open Scope string_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From zar Require Import compile cotree cpGCL cpo cwp eR itree misc order tactics tree.

Local Open Scope cpGCL_scope.

Definition incr (x : string) :=
  x <-- (fun s => S (as_nat (s x))).

Definition incr_z (x : string) :=
  x <-- (fun s => as_int (s x) + 1)%Z.

Definition plus (v1 v2 : val) : val :=
  match (v1, v2) with
  | (vnat n, vnat m) => vnat (n + m)
  | _ => vnat O
  end.

Definition flip (x : string) (p : Q) : cpGCL :=
  CChoice (const p) (fun b => x <-- b).

Fixpoint string_of_atree (t : atree bool string) : string :=
  match t with
  | abot => "⊥"
  | aleaf s => "(Leaf " ++ s ++ ")"
  | atau t => "(Tau " ++ string_of_atree t ++ ")"
  | anode k => "(Node " ++ string_of_atree (k false) ++ " " ++ string_of_atree (k true) ++ ")"
  end.

Definition divisible_by (n m : nat) : bool := Nat.eqb (Nat.modulo n m) O.

Definition is_prime (n : nat) : bool :=
  match n with
  | 0%nat => false
  | 1%nat => false
  | 2%nat => true
  | _ => negb (divisible_by n 2) &&
          List.fold_left (fun acc m => acc && negb (divisible_by n m))
            (drop 3 (range (S (Nat.sqrt n)))) true
  end.

(* Eval compute in (List.map (fun n => (n, is_prime n)) (range 24)). *)
