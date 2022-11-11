(** * The geometric distribution program. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Streams Basics QArith String Lqa.
Local Open Scope program_scope.
Local Open Scope string_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From cwp Require Import
  compile cotree cocwp cpGCL cpo cwp equidistribution eR misc itree order tactics tree.
Local Open Scope cpGCL_scope.

Require Import prelude.

(* Eval compute in (List.filter is_prime (range 100)). *)

(** Negative binomial distribution with r=1. *)
Definition geometric (p : Q) : cpGCL :=
  "h" <-- O;
  flip "x" p;
  while (fun s => as_bool (s "x")) do
    incr "h";
    flip "x" p
  end;
  obs (fun s => is_prime (as_nat (s "h"))).
  (* obs (fun s => Nat.leb (as_nat (s "h")) 2). *)

Lemma wf_geometric (p : Q) :
  (0 <= p <= 1)%Q ->
  wf_cpGCL (geometric p).
Proof. repeat constructor; unfold const; lra. Qed.

Section geometric_equidistribution.
  Context (env : SamplingEnvironment) (P : St -> bool) (samples : nat -> St).
  Context (p : Q) (Hp : (0 <= p <= 1)%Q).
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i)
           (cpGCL_to_itree (geometric p) empty).

  Theorem geometric_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (cwp (geometric p) (fun s => if P s then 1 else 0) empty).
  Proof.
    eapply cpGCL_samples_equidistributed; eauto; apply wf_geometric; auto.
  Qed.
End geometric_equidistribution.

(** Extracting the sampler. *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
Definition sampler : itree boolE nat :=
  ITree.map (fun s => as_nat (s "h")) (cpGCL_to_itree (geometric (2#3)) empty).
Extraction "extract/geometric/geometric.ml" sampler.

(* Eval compute in (cpGCL_to_tree (geometric (1#2)) empty). *)

Definition geometric2 : cpGCL :=
  while (fun s => as_bool (s "b")) do
    incr_z "h";
    flip "b" (1#2)
  end;
  obs (fun s => Z.leb (as_int (s "h")) 3).

Definition sampler2 : itree boolE Z :=
  ITree.map (fun s => as_int (s "h"))
    (cpGCL_to_itree geometric2 (upd "h" 0%Z (upd "b" true empty))).

(* Cheat/hack for now. *)
Definition string_of_nat (n : nat) : string :=
  match n with
  | O => "0"
  | S O => "1"
  | S (S O) => "2"
  | S (S (S O)) => "3"
  | S (S (S (S O))) => "4"
  | S (S (S (S (S O)))) => "5"
  | S (S (S (S (S (S O))))) => "6"
  | S (S (S (S (S (S (S O)))))) => "7"
  | S (S (S (S (S (S (S (S O))))))) => "8"
  | S (S (S (S (S (S (S (S (S O)))))))) => "9"
  | _ => "10"
  end.

(* Cheat/hack for now. *)
Definition string_of_int (z : Z) : string :=
  match z with
  | 0%Z => "0"
  | 1%Z => "1"
  | 2%Z => "2"
  | 3%Z => "3"
  | 4%Z => "4"
  | 5%Z => "5"
  | 6%Z => "6"
  | 7%Z => "7"
  | 8%Z => "8"
  | 9%Z => "9"
  | _ => "10"
  end.

Definition approx : fin_itree string := fin_itree_of_itree 12 (ITree.map string_of_nat sampler).
Eval compute in (string_of_fin_itree approx).

(* Definition approx : fin_itree string := fin_itree_of_itree 50 (ITree.map string_of_int sampler2). *)
(* Eval compute in (string_of_fin_itree approx). *)
