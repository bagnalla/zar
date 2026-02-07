(** * cwp on CF trees. *)

Set Implicit Arguments.

Require Import Basics.

Local Open Scope program_scope.

From zar Require Import
  cpGCL
  cpo
  cwp
  eR
  order
  tree
.

Local Open Scope eR_scope.

Create HintDb twp.

Fixpoint twp_ {A} (fl : bool) (t : tree A) (f : A -> eR) : eR :=
  match t with
  | Leaf x => f x
  | Fail _ => if fl then 1 else 0
  | Choice q k =>
      Q2eR q * twp_ fl (k true) f + (1 - Q2eR q) * twp_ fl (k false) f
  | Fix st G g k =>
      let twp_g := fun f s => twp_ fl (g s) f in
      let twp_k := fun f s => twp_ fl (k s) f in
      iter (loop_F G twp_g (twp_k f)) (const 0) st
  end.

Definition twp {A} : tree A -> (A -> eR) -> eR := twp_ false.
Definition twpfail {A} : tree A -> (A -> eR) -> eR := twp_ true.
Definition tfail {A} (t : tree A) : eR := twpfail t (const 0).

Fixpoint twlp_ {A} (fl : bool) (t : tree A) (f : A -> eR) : eR :=
  match t with
  | Leaf x => f x
  | Fail _ => if fl then 1 else 0
  | Choice q k =>
      Q2eR q * twlp_ fl (k true) f + (1 - Q2eR q) * twlp_ fl (k false) f
  | Fix st G g k =>
      let twlp_g := fun f s => twlp_ fl (g s) f in
      let twlp_k := fun f s => twlp_ fl (k s) f in
      dec_iter (loop_F G twlp_g (twlp_k f)) (const 1) st
  end.

Definition twlp {A} : tree A -> (A -> eR) -> eR := twlp_ false.
Definition twlpfail {A} : tree A -> (A -> eR) -> eR := twlp_ true.
Definition tfail_or_diverge {A} (t : tree A) : eR := twlpfail t (const 0).

Definition tcwp {A} (t : tree A) (f : A -> eR) : eR :=
  twp t f / twlp t (const 1).
