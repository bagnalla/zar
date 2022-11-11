(** * The conditional probabilistic guarded command language (cpGCL) syntax. *)

From Coq Require Import
  Basics
  QArith
  String.

Local Open Scope program_scope.

Declare Scope cpGCL_scope.

From zar Require Import cpo misc order.

(** Values are bools, nats, or ints. *)
Variant val : Type :=
| vbool : bool -> val
| vnat : nat -> val
| vint : Z -> val.

(** A program state is a map from identifiers (nat for now) to values. *)
Definition St : Set := string -> val.
Definition empty : St := fun _ => vbool false.
Definition upd (x : string) (v : val) (st : St) : St :=
  fun y => if String.eqb y x then v else st y.

#[global]
  Instance Inhabited_St : Inhabited St :=
  {| el := empty |}.

(** An expression is a function from program states to values. *)
Definition expr := St -> val.

Definition is_bool (v : val) : bool :=
  match v with
  | vbool _ => true
  | _ => false
  end.

Definition is_nat (v : val) : bool :=
  match v with
  | vnat _ => true
  | _ => false
  end.

Definition is_int (v : val) : bool :=
  match v with
  | vint _ => true
  | _ => false
  end.

Definition as_bool (v : val) : bool :=
  match v with
  | vbool b => b
  | _ => false
  end.

Definition as_nat (v : val) : nat :=
  match v with
  | vnat n => n
  | _ => O
  end.

Definition as_int (v : val) : Z :=
  match v with
  | vint n => n
  | _ => Z0
  end.

Inductive cpGCL : Type :=
| CSkip : cpGCL
| CAbort : cpGCL
| CAssign : string -> expr -> cpGCL
| CSeq : cpGCL -> cpGCL -> cpGCL
| CIte : (St -> bool) -> cpGCL -> cpGCL -> cpGCL
| CChoice : (St -> Q) -> (bool -> cpGCL) -> cpGCL
| CUniform : (St -> nat) -> (nat -> cpGCL) -> cpGCL
| CWhile : (St -> bool) -> cpGCL -> cpGCL
| CObserve : (St -> bool) -> cpGCL.

Definition CScore (e : St -> Q) : cpGCL :=
  CChoice e (fun b => if b then CSkip else CObserve (const false)).

Definition unroll_while (e : St -> bool) (c : cpGCL) : cpGCL :=
  CIte e (CSeq c (CWhile e c)) CSkip.

Definition const_val : val -> expr := const.

Coercion vbool : bool >-> val.
Coercion vnat : nat >-> val.
Coercion vint : Z >-> val.
Coercion const_val : val >-> expr.

Notation "'skip'" :=
  CSkip (at level 0) : cpGCL_scope.
Notation "'abort'" :=
  CAbort (at level 0) : cpGCL_scope.
Notation "x <-- e" :=
  (CAssign x e)
    (at level 0, e at level 85, no associativity) : cpGCL_scope.
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 90, right associativity) : cpGCL_scope.
Notation "'if' e 'then' c1 'else' c2 'end'" :=
  (CIte e c1 c2) (at level 89, e at level 99,
      c1 at level 99, c2 at level 99) : cpGCL_scope.
(* Notation "{ c1 } [ p ] { c2 }" := *)
(*   (CChoice p c1 c2) (at level 89, p at level 99, *)
(*       c1 at level 99, c2 at level 99) : cpGCL_scope. *)
(* Notation "'while' e { c }" := *)
(*   (CWhile e c) (at level 89, e at level 99, c at level 99) : cpGCL_scope. *)
Notation "'while' e 'do' c 'end'" :=
  (CWhile e c) (at level 89, e at level 99, c at level 99) : cpGCL_scope.
Notation "'obs' e" :=
  (CObserve e) (at level 89, e at level 99) : cpGCL_scope.
(* Notation "{ c1 } [ p ] { c2 }" := *)
(*   (CChoice p c1 c2) (at level 89, p at level 99, *)
(*       c1 at level 99, c2 at level 99) : cpGCL_scope. *)

(** A cpGCL command is well-formed when all p values in choice
    commands are valid probabilities in all states. *)
(* Could refine to only being valid probabilities in reachable states. *)
Inductive wf_cpGCL : cpGCL -> Type :=
| wf_skip : wf_cpGCL CSkip
| wf_abort : wf_cpGCL CAbort
| wf_assign : forall x e, wf_cpGCL (CAssign x e)
| wf_seq : forall c1 c2,
    wf_cpGCL c1 -> wf_cpGCL c2 -> wf_cpGCL (CSeq c1 c2)
| wf_ite : forall e c1 c2,
    wf_cpGCL c1 -> wf_cpGCL c2 -> wf_cpGCL (CIte e c1 c2)
| wf_choice : forall (e : St -> Q) f,
    (forall s, (0 <= e s <= 1)%Q) ->
    (forall b, wf_cpGCL (f b)) ->
    wf_cpGCL (CChoice e f)
| wf_uniform : forall (e : St -> nat) f,
    (forall s, (0 < e s)%nat) ->
    (forall n, wf_cpGCL (f n)) ->
    wf_cpGCL (CUniform e f)
| wf_while : forall e body, wf_cpGCL body -> wf_cpGCL (CWhile e body)
| wf_observe : forall e, wf_cpGCL (CObserve e).
