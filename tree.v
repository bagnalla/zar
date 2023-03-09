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

Inductive tree : Type :=
| Leaf : St -> tree
| Fail : tree
| Choice : Q -> (bool -> tree) -> tree
| Fix : St -> (St -> bool) -> (St -> tree) -> (St -> tree) -> tree.

Fixpoint tree_bind (t : tree) (k : St -> tree) : tree :=
  match t with
  | Leaf x => k x
  | Fail => Fail
  | Choice p f => Choice p (fun b => tree_bind (f b) k)
  | Fix st e g h => Fix st e g (fun s => tree_bind (h s) k)
  end.

Lemma tree_bind_leaf (t : tree) :
  tree_bind t Leaf = t.
Proof. induction t; simpl; auto; f_equal; ext x; auto. Qed.

Lemma tree_bind_bind t f g :
  tree_bind (tree_bind t f) g = tree_bind t (fun s => tree_bind (f s) g).
Proof.
  revert f g; induction t; intros f g; simpl; auto; f_equal; ext x; auto.
Qed.

(* "Backward" construction. Easy to relate to loop_approx construction
    used by wp and twp. *)
Fixpoint fix_approx (st : St) (e : St -> bool) (g : St -> tree) (n : nat) : tree :=
  match n with
  | O => Leaf st
  | S n' =>
      if e st then
        tree_bind (g st) (fun s => fix_approx s e g n')
      else
        Leaf st
  end.

(* Same as above but with an arbitrary continuation [k] instead of [Leaf]. *)
Fixpoint fix_approx''' (st : St) (e : St -> bool) (g : St -> tree) (k : St -> tree) (n : nat)
  : tree :=
  match n with
  | O => k st
  | S n' =>
      if e st then
        tree_bind (g st) (fun s => fix_approx''' s e g k n')
      else
        k st
  end.

(* "Forward" construction. *)
Fixpoint fix_chain (st : St) (e : St -> bool) (g : St -> tree) (n : nat) : tree :=
  match n with
  | O => Leaf st
  | S n' => tree_bind (fix_chain st e g n') (fun s => if e s then g s else Leaf s)
  end.

Lemma tree_bind_assoc t g k :
  tree_bind (tree_bind t g) k = tree_bind t (fun s => tree_bind (g s) k).
Proof.
  revert g k; induction t; intros g k; simpl; auto; f_equal; ext s'; auto.
Qed.

Lemma fix_approx_G_false_leaf st G g i :
  G st = false ->
  fix_approx st G g i = Leaf st.
Proof. destruct i; intros H; simpl; auto; rewrite H; reflexivity. Qed.

(* Uses two levels of induction. *)
Lemma fix_approx_fix_chain st e g n :
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
      assert ((fun s : St => if e s then
                               tree_bind (g s) (fun s0 : St => fix_approx s0 e g n)
                             else Leaf s) =
                (fun s : St => if e s then
                                 tree_bind (fix_approx s e g n)
                                   (fun s : St => if e s then g s else Leaf s)
                               else Leaf s)).
      { ext s; destruct (e s) eqn:Hes; auto. }
      rewrite H.
      rewrite tree_bind_assoc.
      f_equal. ext s. destruct (e s) eqn:Hes; auto.
      rewrite fix_approx_G_false_leaf; auto; simpl; rewrite Hes; auto.
  - rewrite fix_approx_G_false_leaf; auto; simpl; rewrite Hest; auto.
Qed.

Inductive wf_tree : tree -> Prop :=
| wf_leaf : forall x, wf_tree (Leaf x)
| wf_fail : wf_tree Fail
| wf_choice : forall p f,
    0 <= p <= 1 ->
    (forall b, wf_tree (f b)) ->
    wf_tree (Choice p f)
| wf_fix : forall st e g k,
    (forall s : St, wf_tree (g s)) ->
    (forall s : St, wf_tree (k s)) ->
    wf_tree (Fix st e g k).
#[global] Hint Constructors wf_tree : tree.

Inductive wf_tree' : tree -> Prop :=
| wf_leaf' : forall x, wf_tree' (Leaf x)
| wf_fail' : wf_tree' Fail
| wf_choice' : forall p f,
    0 < p -> p < 1 ->
    Qred p = p ->
    (forall b, wf_tree' (f b)) ->
    wf_tree' (Choice p f)
| wf_fix' : forall st e g k,
    (forall s : St, wf_tree' (g s)) ->
    (forall s : St, wf_tree' (k s)) ->
    wf_tree' (Fix st e g k).
#[global] Hint Constructors wf_tree' : tree.

Lemma wf_tree'_wf_tree (t : tree) :
  wf_tree' t -> wf_tree t.
Proof. induction 1; constructor; auto; lra. Qed.
#[global] Hint Resolve wf_tree'_wf_tree : tree.

Lemma wf_tree_bind (t : tree) (k : St -> tree) :
  wf_tree t ->
  (forall st, wf_tree (k st)) ->
  wf_tree (tree_bind t k).
Proof.
  revert k; induction t; simpl; intros k H2 H1; auto;
    inversion H2; subst; try constructor; auto.
Qed.

Inductive tree_unbiased : tree -> Prop :=
| tree_unbiased_leaf : forall x, tree_unbiased (Leaf x)
| tree_unbiased_fail : tree_unbiased Fail
| tree_unbiased_choice : forall p f,
    p == (1#2) ->
    (forall b, tree_unbiased (f b)) ->
    tree_unbiased (Choice p f)
| tree_unbiased_fix : forall st G g k,
    (forall s, tree_unbiased (g s)) ->
    (forall s, tree_unbiased (k s)) ->
    tree_unbiased (Fix st G g k).

(* Stronger version that is easier to use but harder to satisfy (not
   only are no fails reachable, but none the functions involved are
   even capable of producing a fail). *)
Inductive no_fail' : tree -> Prop :=
| no_fail'_leaf : forall s, no_fail' (Leaf s)
| no_fail'_choice : forall q f,
    (forall b, no_fail' (f b)) ->
    no_fail' (Choice q f)
| no_fail'_fix : forall st G g k,
    (forall s, no_fail' (g s)) ->
    (forall s, no_fail' (k s)) ->
    no_fail' (Fix st G g k).

Inductive simple : tree -> Prop :=
| simple_leaf : forall x, simple (Leaf x)
| simple_choice : forall p f,
    (forall b, simple (f b)) ->
    simple (Choice p f).

Lemma tree_unbiased_wf_tree (t : tree) :
  tree_unbiased t ->
  wf_tree t.
Proof. induction 1; constructor; auto; lra. Qed.
#[global] Hint Resolve tree_unbiased_wf_tree : tree.

Lemma fix_approx'''_tree_bind_fix_approx
  (st : St) (e : St -> bool) (g : St -> tree) (k : St -> tree) (n : nat) :
  fix_approx''' st e g k n = tree_bind (fix_approx st e g n) k.
Proof.
  revert st e g k; induction n; intros st e g k; simpl; auto.
  destruct (e st) eqn:Hest; simpl; auto.
  rewrite tree_bind_bind; f_equal; ext s; apply IHn.
Qed.

(* (* Roughly approximates fix nodes. *) *)
(* Inductive tree_all (P : St -> Prop) : tree -> Prop := *)
(* | tree_all_leaf : forall s, P s -> tree_all P (Leaf s) *)
(* | tree_all_fail : tree_all P Fail *)
(* | tree_all_choice : forall q k, *)
(*     (forall b, tree_all P (k b)) -> *)
(*     tree_all P (Choice q k) *)
(* | tree_all_fix : forall st e g k, *)
(*     (forall s, tree_all P (k s)) -> *)
(*     tree_all P (Fix st e g k). *)

(* There is at least one reachable state that satisfies the given
   predicate. I.e., it has non-zero probability. Assumes wf_tree'. *)
Inductive tree_some : (St -> Prop) -> tree -> Prop :=
| tree_some_leaf : forall (P : St -> Prop) s,
    P s -> tree_some P (Leaf s)
| tree_some_choice : forall P q k b,
    tree_some P (k b) ->
    tree_some P (Choice q k)
| tree_some_fix : forall P st G g k i s,
    G s = false ->
    tree_some (eq s) (fix_approx st G g i) ->
    tree_some P (k s) ->
    tree_some P (Fix st G g k).

Inductive tree_all (P : St -> Prop) : tree -> Prop :=
| tree_all_leaf : forall s, P s -> tree_all P (Leaf s)
| tree_all_fail : tree_all P Fail
| tree_all_choice : forall p k,
    (forall b, tree_all P (k b)) ->
    tree_all P (Choice p k)
| tree_all_fix : forall st G g k,
    (forall i s, G s = false ->
            tree_some (eq s) (fix_approx st G g i) ->
            tree_all P (k s)) ->
    tree_all P (Fix st G g k).

(* (* Roughly approximates fix nodes. *) *)
(* Inductive tree_all (P : St -> Prop) : tree -> Prop := *)
(* | tree_all_leaf : forall s, P s -> tree_all P (Leaf s) *)
(* | tree_all_fail : tree_all P Fail *)
(* | tree_all_choice : forall q k, *)
(*     (forall b, tree_all P (k b)) -> *)
(*     tree_all P (Choice q k) *)
(* | tree_all_fix : forall st e g k, *)
(*     (forall s, tree_all P (k s)) -> *)
(*     tree_all P (Fix st e g k). *)

Lemma tree_all_impl (P Q : St -> Prop) t :
  (forall s, P s -> Q s) ->
  tree_all P t ->
  tree_all Q t.
Proof. intro HPQ; induction 1; constructor; auto. Qed.
