(** * Choice-fix (CF) trees. *)

Set Implicit Arguments.

From Coq Require Import
  QArith
  Lqa
.

From zar Require Import
  cpGCL
  tactics
.

Create HintDb tree.


(** CF trees are a notation for describing infinite trees that can be
    interpreted into either itrees (for execution) or cotrees (for
    reasoning). They can also be seen as cpGCL programs specialized to
    initial states. *)

Inductive tree (A : Type) : Type :=
| Leaf : A -> tree A
| Fail : tree A
| Choice : Q -> (bool -> tree A) -> tree A
| Fix : forall I, I -> (I -> bool) -> (I -> tree I) -> (I -> tree A) -> tree A.
(* The following encoding would complicate compilation from cpGCL but
   perhaps simplify everything else. *)
(* | Fix : forall I, I -> (I -> tree (I + A)) -> tree A. *)

Fixpoint tree_bind {A B} (t : tree A) (k : A -> tree B) : tree B :=
  match  t with
  | Leaf x => k x
  | Fail _ => Fail _
  | Choice p f => Choice p (fun b => tree_bind (f b) k)
  | Fix st e g h => Fix st e g (fun s => tree_bind (h s) k)
  end.

Lemma tree_bind_leaf {A}  (t : tree A) :
  tree_bind t (@Leaf A) = t.
Proof. induction t; simpl; auto; f_equal; ext x; auto. Qed.

Lemma tree_bind_assoc {A B C}
  (t : tree A) (f : A -> tree B) (g : B -> tree C) :
  tree_bind (tree_bind t f) g = tree_bind t (fun s => tree_bind (f s) g).
Proof.
  revert f g; induction t; intros f h; simpl; auto; f_equal; ext x; auto.
Qed.

(* "Backward" construction. Easy to relate to loop_approx construction
    used by wp and twp. *)
Fixpoint fix_approx {A} (st : A) (e : A -> bool) (g : A -> tree A) (n : nat) : tree A :=
  match n with
  | O => Leaf st
  | S n' =>
      if e st then
        tree_bind (g st) (fun s => fix_approx s e g n')
      else
        Leaf st
  end.

(* Same as above but with an arbitrary continuation [k] instead of [Leaf]. *)
Fixpoint fix_approx''' {A B} (st : A) (e : A -> bool) (g : A -> tree A) (k : A -> tree B) (n : nat)
  : tree B :=
  match n with
  | O => k st
  | S n' =>
      if e st then
        tree_bind (g st) (fun s => fix_approx''' s e g k n')
      else
        k st
  end.

(* "Forward" construction. *)
Fixpoint fix_chain {I} (st : I) (e : I -> bool) (g : I -> tree I) (n : nat) : tree I :=
  match n with
  | O => Leaf st
  | S n' => tree_bind (fix_chain st e g n') (fun s => if e s then g s else Leaf s)
  end.

Lemma fix_approx_G_false_leaf {A} (st : A) G g i :
  G st = false ->
  fix_approx st G g i = Leaf st.
Proof. destruct i; intros H; simpl; auto; rewrite H; reflexivity. Qed.

(* Uses two levels of induction. *)
Lemma fix_approx_fix_chain {I} (st : I) e g n :
  fix_approx st e g n = fix_chain st e g n.
Proof.
  revert st e g; induction n; intros st e g; simpl; auto.
  rewrite <- IHn.
  destruct (e st) eqn:Hest.
  - clear IHn.
    revert st e g Hest.
    induction n; intros st e g Hest; simpl.
    + rewrite Hest.
      apply tree_bind_leaf.
    + rewrite Hest.
      assert ((fun s : I => if e s then
                           tree_bind (g s) (fun s0 : I => fix_approx s0 e g n)
                         else Leaf s) =
                (fun s : I => if e s then
                             tree_bind (fix_approx s e g n)
                               (fun s : I => if e s then g s else Leaf s)
                           else Leaf s)).
      { ext s; destruct (e s) eqn:Hes; auto. }
      rewrite H.
      rewrite tree_bind_assoc.
      f_equal. ext s. destruct (e s) eqn:Hes; auto.
      rewrite fix_approx_G_false_leaf; auto; simpl; rewrite Hes; auto.
  - rewrite fix_approx_G_false_leaf; auto; simpl; rewrite Hest; auto.
Qed.

Inductive wf_tree {A} : tree A -> Prop :=
| wf_leaf : forall x, wf_tree (Leaf x)
| wf_fail : wf_tree (Fail _)
| wf_choice : forall p f,
    0 <= p <= 1 ->
    (forall b, wf_tree (f b)) ->
    wf_tree (Choice p f)
| wf_fix : forall I (st : I) e g k,
    (forall s : I, wf_tree (g s)) ->
    (forall s : I, wf_tree (k s)) ->
    wf_tree (Fix st e g k).
#[export] Hint Constructors wf_tree : tree.

Inductive wf_tree' {A} : tree A -> Prop :=
| wf_leaf' : forall x, wf_tree' (Leaf x)
| wf_fail' : wf_tree' (Fail _)
| wf_choice' : forall p f,
    0 < p -> p < 1 ->
    Qred p = p ->
    (forall b, wf_tree' (f b)) ->
    wf_tree' (Choice p f)
| wf_fix' : forall I (st : I) e g k,
    (forall s : I, wf_tree' (g s)) ->
    (forall s : I, wf_tree' (k s)) ->
    wf_tree' (Fix st e g k).
#[export] Hint Constructors wf_tree' : tree.

Lemma wf_tree'_wf_tree {A} (t : tree A) :
  wf_tree' t -> wf_tree t.
Proof. induction 1; constructor; auto; lra. Qed.
#[export] Hint Resolve wf_tree'_wf_tree : tree.

Lemma wf_tree_bind {A B} (t : tree A) (k : A -> tree B) :
  wf_tree t ->
  (forall st, wf_tree (k st)) ->
  wf_tree (tree_bind t k).
Proof.
  revert k; induction t; simpl; intros k H2 H1; auto;
    inversion H2; subst; try constructor; existT_inv; auto.
Qed.

Inductive tree_unbiased {A} : tree A -> Prop :=
| tree_unbiased_leaf : forall x, tree_unbiased (Leaf x)
| tree_unbiased_fail : tree_unbiased (Fail _)
| tree_unbiased_choice : forall p f,
    p == (1#2) ->
    (forall b, tree_unbiased (f b)) ->
    tree_unbiased (Choice p f)
| tree_unbiased_fix : forall I (st : I) G g k,
    (forall s : I, tree_unbiased (g s)) ->
    (forall s : I, tree_unbiased (k s)) ->
    tree_unbiased (Fix st G g k).

(* Stronger version that is easier to use but harder to satisfy (not
   only are no fails reachable, but none the functions involved are
   even capable of producing a fail). *)
Inductive no_fail' {A} : tree A -> Prop :=
| no_fail'_leaf : forall s, no_fail' (Leaf s)
| no_fail'_choice : forall q f,
    (forall b, no_fail' (f b)) ->
    no_fail' (Choice q f)
| no_fail'_fix : forall I (st : I) G g k,
    (forall s : I, no_fail' (g s)) ->
    (forall s : I, no_fail' (k s)) ->
    no_fail' (Fix st G g k).

Inductive simple {A} : tree A -> Prop :=
| simple_leaf : forall x, simple (Leaf x)
| simple_choice : forall p f,
    (forall b, simple (f b)) ->
    simple (Choice p f).

Lemma tree_unbiased_wf_tree {A} (t : tree A) :
  tree_unbiased t ->
  wf_tree t.
Proof. induction 1; constructor; auto; lra. Qed.
#[export] Hint Resolve tree_unbiased_wf_tree : tree.

Lemma fix_approx'''_tree_bind_fix_approx {A B}
  (st : A) (e : A -> bool) (g : A -> tree A) (k : A -> tree B) (n : nat) :
  fix_approx''' st e g k n = tree_bind (fix_approx st e g n) k.
Proof.
  revert st e g k; induction n; intros st e g k; simpl; auto.
  destruct (e st) eqn:Hest; simpl; auto.
  rewrite tree_bind_assoc; f_equal; ext s; apply IHn.
Qed.

(* There is at least one reachable state that satisfies the given
   predicate. I.e., it has non-zero probability. Assumes wf_tree'. *)
Inductive tree_some {A} : (A -> Prop) -> tree A -> Prop :=
| tree_some_leaf : forall (P : A -> Prop) s,
    P s -> tree_some P (Leaf s)
| tree_some_choice : forall P q k b,
    tree_some P (k b) ->
    tree_some P (Choice q k)
| tree_some_fix : forall I P (st : I) G (g : I -> tree I) k i s,
    G s = false ->
    tree_some (eq s) (fix_approx st G g i) ->
    tree_some P (k s) ->
    tree_some P (Fix st G g k).

Inductive tree_all {A} (P : A -> Prop) : tree A -> Prop :=
| tree_all_leaf : forall s, P s -> tree_all P (Leaf s)
| tree_all_fail : tree_all P (Fail _)
| tree_all_choice : forall p k,
    (forall b, tree_all P (k b)) ->
    tree_all P (Choice p k)
| tree_all_fix : forall I (st : I) G g k,
    (forall i s, G s = false ->
            tree_some (eq s) (fix_approx st G g i) ->
            tree_all P (k s)) ->
    tree_all P (Fix st G g k).

Lemma tree_all_impl {A} (P Q : A -> Prop) (t : tree A) :
  (forall s, P s -> Q s) ->
  tree_all P t ->
  tree_all Q t.
Proof. intro HPQ; induction 1; constructor; auto. Qed.
