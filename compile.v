(** * Compiling cpGCL commands to CF trees. *)

Set Implicit Arguments.

Require Import Basics.

Local Open Scope program_scope.

From zar Require Import
  cpGCL
  misc
  tree
  uniform
.

Fixpoint compile (c : cpGCL) (st : St) : tree :=
  match c with
  | CSkip => Leaf st
  | CAbort => Fix st (const true) Leaf Leaf
  | CSeq c1 c2 => tree_bind (compile c1 st) (compile c2)
  | CAssign x e => Leaf (upd x (e st) st)
  | CIte e c1 c2 => if e st then compile c1 st else compile c2 st
  | CChoice e k => Choice (e st) (fun b => compile (k b) st)
  | CUniform e k => tree_bind (uniform_tree (as_nat (e st)))
                     (fun s => compile (k (as_nat (s ϵ))) st)
  | CWhile e body => Fix st e (compile body) Leaf
  | CObserve e => if e st then Leaf st else Fail
  end.

(** Well-formed commands compile to well-formed trees. *)
Lemma compile_wf (c : cpGCL) (st : St) :
  wf_cpGCL c ->
  wf_tree (compile c st).
Proof.
  intro Hwf; revert st; induction Hwf; intro st; simpl; try solve[constructor].
  - constructor; intro n; constructor.
  - apply wf_tree_bind; auto.
  - destruct (e st); auto.
  - constructor; auto.
  - constructor; intro s; auto; apply wf_tree_btree_to_tree.
  - constructor; intro n; auto; try constructor.
  - destruct (e st); constructor.
Qed.

Lemma compile_uniform e k (st : St) :
  compile (CUniform e k) st =
    tree_bind (uniform_tree (as_nat (e st)))
      (fun s => compile (k (as_nat (s ϵ))) st).
Proof. reflexivity. Qed.
