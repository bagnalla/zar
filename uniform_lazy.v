(** * Uniform and Bernoulli CF trees. *)

Set Implicit Arguments.

From Coq Require Import
  Basics
  ClassicalChoice
  Nat
  PeanoNat
  QArith
  Lia
  Lra
  Eqdep
  Equivalence
  Reals
  String
  List
.

Local Open Scope program_scope.
Import ListNotations.

From cwp Require Import
  cpGCL
  cpo
  cwp
  misc
  order
  pow_2
  Q
  eR
  tcwp
  tcwp_facts
  tcwp_geometric
  tree
  tactics
.

Inductive btree (A : Type) : Type :=
| BLeaf : A -> btree A
| BNode : (bool -> btree A) -> btree A.

(* Fixpoint string_of_btree {A} (show : A -> string) (t : btree A) : string := *)
(*   match t with *)
(*   | BLeaf x => show x *)
(*   | BNode l r => "(BNode " ++ string_of_btree show l ++ *)
(*                   " " ++ string_of_btree show r ++ ")" *)
(*   end. *)

Fixpoint btree_map {A B} (f : A -> B) (t : btree A) : btree B :=
  match t with
  | BLeaf x => BLeaf (f x)
  | BNode k => BNode (btree_map f ∘ k)
  end.

Fixpoint btree_infer {A} (f : A -> eR) (t : btree A) : eR :=
  match t with
  | BLeaf x => f x
  | BNode k => Q2eR (1#2) * btree_infer f (k true) + Q2eR (1#2) * btree_infer f (k false)
  end.

Fixpoint btree_to_tree {A} (f : A -> val) (t : btree A) : tree :=
  match t with
  | BLeaf x => Leaf (upd ϵ (f x) empty)
  | BNode k => Choice (1#2) (btree_to_tree f ∘ k)
  end.

(* Definition nat_btree_to_tree : btree nat -> tree := btree_to_tree vnat. *)
(* Definition bool_btree_to_tree : btree bool -> tree := btree_to_tree vbool. *)

Definition bernoulli_btree_to_tree : btree (unit + bool) -> tree :=
  btree_to_tree (cotuple (const (vint 0)) vbool).

Definition uniform_btree_to_tree : btree (unit + nat) -> tree :=
  btree_to_tree (cotuple (const (vint 0)) vnat).

Lemma twp_bernoulli_btree_to_tree (f : bool -> eR) (t : btree (unit + bool)) :
  twp (bernoulli_btree_to_tree t) (fun s => match s ϵ with
                                         | vbool b => f b
                                         | _ => 0
                                         end) =
    btree_infer (cotuple (const 0) f) t.
Proof.
  unfold twp, bernoulli_btree_to_tree; revert f; induction t; intro f; simpl.
  - destruct a; constructor.
  - rewrite (H true), (H false); f_equal; f_equal.
    rewrite Q2eR_one_half, eRminus_1_2; reflexivity.
Qed.

Lemma twp_bernoulli_btree_to_tree' r (t : btree (unit + bool)) :
  twp (bernoulli_btree_to_tree t) (fun s => match s ϵ with
                                         | vint _ => r
                                         | _ => 0
                                         end) =
    btree_infer (cotuple (const r) (const 0)) t.
Proof.
  unfold twp, bernoulli_btree_to_tree; revert r; induction t; intro r; simpl.
  - destruct a; constructor.
  - rewrite (H true), (H false); f_equal; f_equal.
    rewrite Q2eR_one_half, eRminus_1_2; reflexivity.
Qed.

Lemma twp_uniform_btree_to_tree (f : nat -> eR) (t : btree (unit + nat)) :
  twp (uniform_btree_to_tree t) (fun s => match s ϵ with
                                       | vnat n => f n
                                       | _ => 0
                                       end) =
    btree_infer (cotuple (const 0) f) t.
Proof.
  unfold twp; revert f; induction t; intro f; simpl.
  - destruct a; constructor.
  - rewrite (H true), (H false); f_equal; f_equal.
    rewrite Q2eR_one_half, eRminus_1_2; reflexivity.
Qed.

Lemma twp_uniform_btree_to_tree' r (t : btree (unit + nat)) :
  twp (uniform_btree_to_tree t) (fun s => match s ϵ with
                                       | vint _ => r
                                       | _ => 0
                                       end) =
    btree_infer (cotuple (const r) (const 0)) t.
Proof.
  unfold twp, uniform_btree_to_tree; revert r; induction t; intro r; simpl.
  - destruct a; constructor.
  - rewrite (H true), (H false); f_equal; f_equal.
    rewrite Q2eR_one_half, eRminus_1_2; reflexivity.
Qed.

Lemma twp_uniform_btree_to_tree_bool (f : bool -> eR) (t : btree (unit + nat)) :
  twp (uniform_btree_to_tree t) (fun s => match s ϵ with
                                       | vbool b => f b
                                       | _ => 0
                                       end) = 0.
Proof.
  unfold twp, uniform_btree_to_tree; revert f; induction t; intro f; simpl.
  - destruct a; constructor.
  - rewrite (H true), (H false); eRauto.
Qed.

Lemma tree_unbiased_btree_to_tree {A} (f : A -> val) (t : btree A) :
  tree_unbiased (btree_to_tree f t).
Proof.
  revert f; induction t; intro f; constructor; try reflexivity.
  intros []; eauto.
Qed.

Import Lqa.
Lemma wf_tree_btree_to_tree {A} (f : A -> val) (t : btree A) :
  wf_tree (btree_to_tree f t).
Proof.
  revert f; induction t; intro f; constructor; try lra; intros []; eauto.
Qed.
Lemma wf_tree'_btree_to_tree {A} (f : A -> val) (t : btree A) :
  wf_tree' (btree_to_tree f t).
Proof.
  revert f; induction t; intro f; constructor; simpl; try lra; auto.
  intros []; eauto.
Qed.
Import Lra.
#[global] Hint Resolve wf_tree_btree_to_tree : tree.
#[global] Hint Resolve wf_tree'_btree_to_tree : tree.

(* Instead of divide list, take and drop 2^n' from the list. *)
Fixpoint list_btree_aux {A} (l : list A) (n : nat) : btree (unit + A) :=
  match n with
  | O => match l with
        | x :: _ => BLeaf (inr x)
        | _ => BLeaf (inl tt)
        end
  | S n' => BNode (fun b => if b then list_btree_aux (take (2^n') l) n'
                        else list_btree_aux (drop (2^n') l) n')
  end.

Definition list_btree {A} (l : list A) : btree (unit + A) :=
  list_btree_aux l (log2 (next_pow_2 (length l))).

(* Fixpoint btree_eq {A} `{EqType A} (l r : btree A) : bool := *)
(*   match (l, r) with *)
(*   | (BLeaf x, BLeaf y) => eqb x y *)
(*   | (BNode ll lr, BNode rl rr) => btree_eq ll rl && btree_eq lr rr *)
(*   | _ => false *)
(*   end. *)

(* Lemma btree_eq_spec {A} `{EqType A} (l r : btree A) : *)
(*   reflect (l = r) (btree_eq l r). *)
(* Proof. *)
(*   revert r; induction l; intros r. *)
(*   - destruct r; simpl. *)
(*     + destruct (eqb_spec a a0); subst; constructor; auto; congruence. *)
(*     + constructor; congruence. *)
(*   - destruct r; simpl. *)
(*     + constructor; congruence. *)
(*     + destruct (IHl1 r1); subst; simpl. *)
(*       * destruct (IHl2 r2); subst; simpl; constructor; auto; congruence. *)
(*       * constructor; congruence. *)
(* Qed. *)

(* #[global] *)
(*   Instance EqType_btree {A} `{EqType A} : EqType (btree A) := *)
(*   {| eqb := btree_eq *)
(*    ; eqb_spec := btree_eq_spec |}. *)

(* Fixpoint btree_opt {A} `{EqType A} (t : btree A) : btree A := *)
(*   match t with *)
(*   | BLeaf _ => t *)
(*   | BNode l r => *)
(*       let l' := btree_opt l in *)
(*       let r' := btree_opt r in *)
(*       if btree_eq l' r' then l' else BNode l' r' *)
(*   end. *)

(* Fixpoint btree_opt {A} `{EqType A} (t : btree A) : btree A := *)
(*   match t with *)
(*   | BLeaf _ => t *)
(*   | BNode l r => *)
(*       let l' := btree_opt l in *)
(*       let r' := btree_opt r in *)
(*       match (l', r') with *)
(*       | (BLeaf x, BLeaf y) => if eqb x y then l' else BNode l' r' *)
(*       | _ => BNode l' r' *)
(*       end *)
(*   end. *)

(* Lemma btree_infer_btree_opt {A} `{EqType A} (t : btree A) f : *)
(*   btree_infer f (btree_opt t) = btree_infer f t. *)
(* Proof. *)
(*   revert f; induction t; intro f; simpl; auto. *)
(*   destruct (btree_eq_spec (btree_opt t1) (btree_opt t2)); simpl. *)
(*   - rewrite IHt1, <- IHt2, <- e, IHt1. *)
(*     rewrite <- eRmult_plus_distr_l, <- eRmult_2_plus, <- eRmult_assoc. *)
(*     rewrite Q2eR_one_half; unfold eRdiv; rewrite eRmult_1_l, eRinv_l; eRauto. *)
(*   - rewrite <- 2!eRmult_plus_distr_l; f_equal. *)
(*     rewrite IHt1, IHt2; reflexivity. *)
(* Qed. *)

(* Lemma btree_infer_btree_opt {A} `{EqType A} (t : btree A) f : *)
(*   btree_infer f (btree_opt t) = btree_infer f t. *)
(* Proof. *)
(*   revert f; induction t; intro f; simpl; auto. *)
(*   destruct (btree_eq_spec (btree_opt t1) (btree_opt t2)); simpl. *)
(*   - rewrite e. *)
(*     destruct (btree_opt t2). *)
(*     + rewrite eqb_refl; simpl. *)
(*       simpl in *. *)
(*       rewrite <- IHt2. *)
(*       rewrite <- IHt1. *)
(*       rewrite e. simpl. *)
      
(*     (* rewrite IHt1, <- IHt2, <- e, IHt1. *) *)
(*     rewrite <- eRmult_plus_distr_l, <- eRmult_2_plus, <- eRmult_assoc. *)
(*     rewrite Q2eR_one_half; unfold eRdiv; rewrite eRmult_1_l, eRinv_l; eRauto. *)
(*     + simpl. *)
(*       rewrite <- 4!eRmult_plus_distr_l; f_equal. *)
(*       rewrite <- eRmult_2_plus. *)
(*       rewrite <- eRmult_assoc. *)
(*       rewrite Q2eR_one_half; unfold eRdiv; rewrite eRmult_1_l, eRinv_l; eRauto. *)
(*       rewrite <- IHt1. *)
      
(*   - rewrite <- 2!eRmult_plus_distr_l; f_equal. *)
(*     rewrite IHt1, IHt2; reflexivity. *)
(* Qed. *)

(** Eliminate unnecessary fails. *)
Fixpoint reduce_btree {A} (t : btree (unit + A)) : btree (unit + A) :=
  match t with
  | BNode k => let l := reduce_btree (k true) in
              let r := reduce_btree (k false) in
              match (l, r) with
              | (BLeaf (inl tt), BLeaf (inl tt)) => BLeaf (inl tt)
              | _ => BNode (fun b => if b then l else r)
              end
  | _ => t
  end.

Lemma reduce_btree_infer {A} (f : A -> eR) (t : btree (unit + A)) (c : eR) :
  btree_infer (cotuple (fun _ => c) f) (reduce_btree t) =
    btree_infer (cotuple (fun _ => c) f) t.
Proof.
  revert f; induction t; intro f; simpl; auto.
  destruct (reduce_btree (b true)) eqn:Ht1.
  - destruct s; simpl in *.
    + destruct u, (reduce_btree (b false)) eqn:Ht2; simpl.
      * destruct s; simpl in *.
        { destruct u; rewrite <- 2!H, Ht1, Ht2.
          rewrite Q2eR_one_half, <- eRmult_2_plus.
          rewrite <- eRmult_assoc, <- eRmult_half_div_2; eRauto.
          rewrite eRmult_eRdiv_assoc, eRmult_div_cancel; eRauto. }
        { rewrite <- 2!H, Ht1, Ht2; eRauto. }
      * rewrite <- 2!H, Ht1, Ht2; simpl; eRauto.
    + rewrite <- 2!H, Ht1; simpl; reflexivity.
  - simpl; rewrite <- 2!H, Ht1; simpl; eRauto.
Qed.

Definition uniform_btree (n : nat) : btree (unit + nat) :=
  (* btree_opt (list_btree (rev_range n)). *)
  (* list_btree (rev_range n). *)
  reduce_btree (list_btree (rev_range n)).

(* Eval compute in (uniform_btree 10). *)
(* Eval compute in (reduce_btree (uniform_btree 10)). *)

Inductive congruent {A B} : btree A -> btree B -> Prop :=
| congruent_leaf : forall x y, congruent (BLeaf x) (BLeaf y)
| congruent_node : forall k1 k2,
    congruent t1 t1' ->
    congruent t2 t2' ->
    congruent (BNode t1 t2) (BNode t1' t2').

Inductive perfect {A} : btree A -> Prop :=
| perfect_leaf : forall x, perfect (BLeaf x)
| perfect_choice : forall t1 t2,
    congruent t1 t2 ->
    perfect t1 ->
    perfect t2 ->
    perfect (BNode t1 t2).  

Fixpoint countb {A} (f : A -> bool) (t : btree A) : nat :=
  match t with
  | BLeaf x => if f x then 1 else 0
  | BNode t1 t2 => countb f t1 + countb f t2
  end.

(* Lemma countb_btree_opt {A} f (t : btree A) : *)
(*   countb f (btree_opt t) = countb f  *)

Lemma congruent_list_btree_aux {A} (n : nat) (l1 l2 : list A) :
  congruent (list_btree_aux l1 n) (list_btree_aux l2 n).
Proof.
  revert l1 l2; induction n; intros l1 l2; simpl.
  - destruct l1, l2; constructor.
  - constructor; auto.
Qed.

Lemma perfect_list_btree_aux {A} (n : nat) (l : list A) :
  perfect (list_btree_aux l n).
Proof.
  revert l; induction n; intros l; simpl.
  - destruct l; constructor.
  - constructor; auto; apply congruent_list_btree_aux.
Qed.

Lemma perfect_list_btree {A} (l : list A) :
  perfect (list_btree l).
Proof. apply perfect_list_btree_aux. Qed.

Lemma list_btree_aux_count {A} (n : nat) (l : list A) (f : A -> bool) :
  (length l <= 2 ^ n)%nat ->
  countb (cotuple (const false) f) (list_btree_aux l n) = countb_list f l.
Proof.
  revert l f; induction n; simpl; intros l f H0.
  - destruct l; simpl in *; auto.
    assert (l = nil).
    { apply length_zero_iff_nil; lia. }
    subst; simpl; lia.
  - rewrite Nat.add_0_r in H0.
    rewrite 2!IHn.
    + rewrite <- countb_list_app, take_drop_spec; auto.
    + etransitivity.
      { apply length_drop_le. }
      lia.
    + apply take_length.
Qed.

Lemma list_btree_count {A} (l : list A) (f : A -> bool) :
  countb (cotuple (const false) f) (list_btree l) = countb_list f l.
Proof.
  apply list_btree_aux_count.
  generalize (is_power_of_2_next_pow_2 (length l)); intros [k H0].
  rewrite <- H0, Nat.log2_pow2; try lia.
  rewrite H0; apply next_pow_2_ub.
Qed.

Lemma list_btree_aux_countb {A} (n : nat) (l : list A) :
  (length l <= 2^n)%nat ->
  countb (cotuple (const false) (const true)) (list_btree_aux l n) = length l.
Proof.
  revert l; induction n; simpl; intros l H0.
  - destruct l; simpl in *; auto; lia.
  - rewrite Nat.add_0_r in H0.
    rewrite 2!IHn.
    + rewrite <- app_length, take_drop_spec; reflexivity.
    + etransitivity.
      * apply length_drop_le.
      * lia.
    + apply take_length.
Qed.

Lemma list_btree_aux_countb' {A} (n : nat) (l : list A) :
  (length l <= 2^n)%nat ->
  countb (cotuple (const true) (const false)) (list_btree_aux l n) = (2^n - length l)%nat.
Proof.
  revert l; induction n; simpl; intros l H0.
  - destruct l; simpl in *; auto; lia.
  - rewrite Nat.add_0_r in H0.
    rewrite 2!IHn.
    + 
      rewrite Nat.add_0_r.
      replace (2 ^ n - length (take (2 ^ n) l) + (2 ^ n - length (drop (2 ^ n) l)))%nat with
        (2^n + 2^n - (length (take (2^n) l) + length (drop (2^n) l)))%nat.
      2: { assert (length (take (2^n) l) <= 2^n)%nat.
           { apply take_length. }
           assert (length (drop (2^n) l) <= 2^n)%nat.
           { etransitivity.
             - apply length_drop_le.
             - lia. }
           lia. }
      rewrite <- app_length, take_drop_spec; reflexivity.
    + etransitivity.
      * apply length_drop_le.
      * lia.
    + apply take_length.
Qed.

Lemma list_btree_countb {A} (l : list A) :
  countb (cotuple (const false) (const true)) (list_btree l) = length l.
Proof.
  unfold list_btree.
  apply list_btree_aux_countb.
  generalize (is_power_of_2_next_pow_2 (length l)); intros [k H0].
  rewrite <- H0, Nat.log2_pow2; try lia.
  rewrite H0; apply next_pow_2_ub.
Qed.

Lemma countb_partition {A} (P : A -> bool) (t : btree A) :
  (countb P t + countb (fun s => negb (P s)) t = countb (const true) t)%nat.
Proof.
  revert P; induction t; intro P; simpl; auto.
  - destruct (P a); simpl; auto.
  - replace (countb P t1 + countb P t2 +
               (countb (fun s => negb (P s)) t1 +
                  countb (fun s => negb (P s)) t2))%nat with
      (countb P t1 + countb (fun s => negb (P s)) t1 +
         (countb P t2 + countb (fun s => negb (P s)) t2))%nat by lia.
    rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma perfect_congruent_countb_const_true {A B} (t1 : btree A) (t2 : btree B) :
  perfect t1 ->
  perfect t2 ->
  congruent t1 t2 ->
  countb (const true) t1 = countb (const true) t2.
Proof.
  revert t2.
  induction t1; intros t2 Hp1 Hp2 Hcong;
    inv Hcong; inv Hp1; inv Hp2; simpl; auto.
Qed.

Lemma perfect_countb_nonzero {A} (t : btree A) :
  perfect t ->
  (0 < countb (const true) t)%nat.
Proof. induction 1; simpl; lia. Qed.

Lemma perfect_btree_infer {A} (f : A -> bool) (t : btree A)  :
  perfect t ->
  btree_infer (fun x => if f x then 1 else 0) t =
    INeR (countb f t) / INeR (countb (const true) t).
Proof.
  induction t; intro Hperf; simpl; inv Hperf.
  - destruct (f a); simpl.
    + eRauto; rewrite INeR_1; eRauto.
    + rewrite INeR_0, INeR_1; eRauto.
  - rewrite IHt1, IHt2; auto.
    rewrite 2!plus_INeR.
    apply perfect_congruent_countb_const_true in H1; auto.
    rewrite H1; clear H1.
    replace (Q2eR (1#2)) with (1/2).
    2: { rewrite Q2eR_one_half; reflexivity. }
    assert (H0: INeR (countb (const true) t2) <> 0).
    { apply perfect_countb_nonzero in H3.
      intro HC; replace 0 with (INeR 0) in HC by apply INeR_0.
      apply INeR_eq in HC; lia. }
    rewrite 2!eRmult_fract; auto.
    2: { eRauto. }
    2: { eRauto. }
    rewrite 2!eRmult_1_l.
    rewrite eRplus_combine_fract.
    f_equal; eRauto.
Qed.

Definition bernoulli_btree (n d : nat) : btree (unit + bool) :=
  (* btree_opt (btree_map (sum_map (fun x => x) (fun i => Nat.ltb i n)) *)
  btree_map (sum_map (fun x => x) (fun i => Nat.ltb i n)) (uniform_btree d).

Definition bernoulli_tree_open (n d : nat) : tree :=
  bernoulli_btree_to_tree (bernoulli_btree n d).

Definition bernoulli_tree (p : Q) : tree :=
  Fix (upd ϵ (vint 0) empty) (fun s => is_int (s ϵ))
    (fun _ => bernoulli_tree_open (Z.to_nat (Qnum p)) (Pos.to_nat (Qden p)))
    Leaf.

Definition uniform_tree_open (n : nat) : tree :=
  uniform_btree_to_tree (uniform_btree n).

Definition uniform_tree (n : nat) : tree :=
  Fix (upd ϵ (vint 0) empty) (fun s => negb (is_nat (s ϵ)))
    (fun _ => uniform_tree_open n) Leaf.

Lemma btree_infer_fmap_bool {A} (f : A -> bool) (g : bool -> eR) (t : btree (unit + A)) :
  btree_infer (cotuple (const 0) g) (btree_map (sum_map (fun x => x) f) t) =
    btree_infer (cotuple (const 0) (g ∘ f)) t.
Proof.
  revert f; induction t; intro f; simpl; try lra.
  - destruct a; auto.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma countb_list_or {A} (P Q : A -> bool) (l : list A) :
  (forall x, P x = true -> Q x = false) ->
  countb_list (fun x => P x || Q x) l = (countb_list P l + countb_list Q l)%nat.
Proof.
  induction l; simpl; intro H; auto.
  rewrite IHl; auto.
  destruct (P a) eqn:HP, (Q a) eqn:HQ; auto.
  apply H in HP; congruence.
Qed.

Lemma not_in_countb_list_S n l :
  ~ In n l ->
  countb_list (fun i : nat => i <? S n) l =
    countb_list (fun i : nat => i <? n) l.
Proof.
  intro Hnotin.
  replace (fun i : nat => i <? S n) with
    (fun i => Nat.ltb i n || Nat.eqb n i).
  { rewrite countb_list_or.
    - rewrite not_in_countb_list; auto; lia.
    - intros m H; simpl.
      destruct (Nat.ltb_spec m n); try congruence.
      destruct (Nat.eqb_spec n m); subst; try lia. }
  ext i; simpl.
  destruct (Nat.ltb_spec i n); simpl.
  - destruct (Nat.ltb_spec i (S n)); simpl; auto; lia.
  - destruct (Nat.eqb_spec n i); subst.
    + destruct (Nat.ltb_spec i (S i)); lia.
    + destruct (Nat.ltb_spec i (S n)); lia.
Qed.

Lemma in_rev_range_lt n i :
  In i (rev_range n) ->
  (i < n)%nat.
Proof.
  revert i; induction n; simpl; intros i Hi; try contradiction.
  destruct Hi as [?|Hi]; subst; try lia.
  apply IHn in Hi; lia.
Qed.

Corollary in_rev_range_n n :
  ~ In n (rev_range n).
Proof. intro HC; apply in_rev_range_lt in HC; lia. Qed.

Lemma countb_list_rev_range n d :
  (n < d)%nat ->
  countb_list (Nat.eqb n) (rev_range d) = S O.
Proof.
  revert n; induction d; intros n Hle; simpl; try lia.
  destruct (Nat.eqb_spec n d); subst.
  - rewrite not_in_countb_list; try lia.
    apply in_rev_range_n.
  - apply IHd; lia.
Qed.

Lemma countb_list_rev_range_lt n d :
  (n <= d)%nat ->
  countb_list (fun i : nat => i <? n) (rev_range d) = n.
Proof.
  revert n; induction d; intros n Hle; simpl; try lia.
  destruct (Nat.eqb_spec n (S d)); subst.
  - specialize (IHd d (Nat.le_refl d)).
    rewrite not_in_countb_list_S.
    + rewrite IHd.
      destruct (Nat.ltb_spec d (S d)); lia.
    + rewrite rev_range_spec.
      intro HC.
      apply in_rev in HC.
      apply in_range in HC. lia.
  - destruct (Nat.ltb_spec d n); try lia.
    rewrite IHd; lia.
Qed.

Lemma btree_infer_uniform_btree n i :
  (i < n)%nat ->
  btree_infer (cotuple (fun _ : unit => 0) (fun x : nat => if x =? i then 1 else 0))
    (uniform_btree n) = 1 / INeR (next_pow_2 n).
Proof.
  intro Hlt.
  unfold uniform_btree.
  rewrite reduce_btree_infer.
  replace (cotuple (fun _ => 0) (fun x => if x =? i then 1 else 0)) with
    (fun x : unit + nat => if (match x with
                               | inl _ => false
                               | inr j => j =? i
                               end) then 1 else 0).
  2: { ext lr; destruct lr; auto. }
  (* rewrite btree_infer_btree_opt. *)
  rewrite perfect_btree_infer.
  2: { apply perfect_list_btree. }
  replace (fun x : unit + nat => match x with
                                 | inl _ => false
                                 | inr x => x =? i
                                 end) with
    (cotuple (fun _ : unit => false) (Nat.eqb i)).
  2: { ext x; destruct x; auto; simpl.
       rewrite Nat.eqb_sym; reflexivity. }
  rewrite list_btree_count.
  rewrite <- countb_partition with (P := cotuple (const false) (const true)).
  rewrite list_btree_count.
  rewrite countb_list_const_true.
  replace (fun s : unit + nat => negb (cotuple (const false) (const true) s)) with
    (cotuple (fun _ : unit => true) (fun _ : nat => false)).
  2: { ext x; destruct x; auto. }
  unfold list_btree.
  rewrite list_btree_aux_countb'.
  - rewrite rev_range_spec, rev_length, range_length.
    generalize (is_power_of_2_next_pow_2 n).
    unfold is_power_of_2.
    intros [k H].
    rewrite <- H.
    rewrite Nat.log2_pow2; try lia.
    rewrite Nat.add_comm, Nat.sub_add.
    2: { rewrite H; apply next_pow_2_ub. }
    rewrite <- rev_range_spec.
    rewrite countb_list_rev_range; try lia.
    f_equal; apply INeR_1.
  - rewrite rev_range_spec, rev_length, range_length.
    generalize (is_power_of_2_next_pow_2 n).
    unfold is_power_of_2.
    intros [k H].
    rewrite <- H.
    rewrite Nat.log2_pow2; try lia.
    rewrite H.
    apply next_pow_2_ub.
Qed.

Lemma btree_infer_uniform_btree_lt n d :
  (n <= d)%nat ->
  btree_infer (cotuple (fun _ : unit => 0) (fun x : nat => if x <? n then 1 else 0))
    (uniform_btree d) = INeR n / INeR (next_pow_2 d).
Proof.
  intro Hle.
  unfold uniform_btree.
  rewrite reduce_btree_infer.
  replace (cotuple (fun _ => 0) (fun i => if i <? n then 1 else 0)) with
    (fun x : unit + nat => if (match x with
                               | inl _ => false
                               | inr i => i <? n
                               end) then 1 else 0).
  { (* rewrite btree_infer_btree_opt. *)
    rewrite perfect_btree_infer.
    - replace (fun x : unit + nat => match x with
                                     | inl _ => false
                                     | inr i => i <? n
                                     end) with
        (cotuple (fun _ : unit => false) (fun i => i <? n)).
      2: { ext x; destruct x; auto. }
      rewrite list_btree_count.
      rewrite <- countb_partition with (P := cotuple (const false) (const true)).
      rewrite list_btree_count.
      rewrite countb_list_const_true.
      replace (fun s : unit + nat => negb (cotuple (const false) (const true) s)) with
        (cotuple (fun _ : unit => true) (fun _ : nat => false)).
      2: { ext x; destruct x; auto. }
      unfold list_btree.
      rewrite list_btree_aux_countb'.
      + rewrite rev_range_spec, rev_length, range_length.
        generalize (is_power_of_2_next_pow_2 d).
        unfold is_power_of_2.
        intros [k H].
        rewrite <- H.
        rewrite Nat.log2_pow2; try lia.
        rewrite Nat.add_comm, Nat.sub_add.
        2:{ rewrite H; apply next_pow_2_ub. }
        rewrite <- rev_range_spec.
        rewrite countb_list_rev_range_lt; try lia.
        rewrite H; reflexivity.
      + rewrite rev_range_spec, rev_length, range_length.
        generalize (is_power_of_2_next_pow_2 d).
        unfold is_power_of_2.
        intros [k H].
        rewrite <- H.
        rewrite Nat.log2_pow2; try lia.
        rewrite H.
        apply next_pow_2_ub.
    - apply perfect_list_btree. }
  ext x; destruct x; auto.
Qed.

Lemma btree_infer_list_btree_const_1 {A} (l : list A) :
  btree_infer (cotuple (fun _ => 0) (fun _ => 1)) (list_btree l) =
    INeR (length l) / INeR (next_pow_2 (length l)).
Proof.
  replace (cotuple (fun _ : unit => 0) (fun _ : A => 1)) with
    (fun x : unit + A => if (match x with
                             | inl _ => false
                             | inr _ => true
                             end) then 1 else 0).
  rewrite perfect_btree_infer.
  { f_equal.
    - f_equal.
      replace (fun x : unit + A => match x with
                                   | inl _ => false
                                   | inr _ => true
                                   end) with
        (cotuple (fun _ : unit => false) (fun _ : A =>  true)).
      { apply list_btree_countb. }
      ext x; destruct x; auto.
    - f_equal.
      unfold list_btree.
      rewrite <- countb_partition with (P := cotuple (const false) (const true)).
      assert (length l <= 2 ^ log2 (next_pow_2 (length l)))%nat.
      { generalize (is_power_of_2_next_pow_2 (length l)); intros [k H].
        rewrite <- H.
        rewrite Nat.log2_pow2; try lia.
        rewrite H; apply next_pow_2_ub. }
      rewrite list_btree_aux_countb; auto.
      replace (fun s : unit + A => negb (cotuple (const false) (const true) s)) with
        (cotuple (fun _ : unit => true) (fun _ : A =>  false)).
      2: { ext x; destruct x; auto. }
      rewrite list_btree_aux_countb'; auto.
      generalize (is_power_of_2_next_pow_2 (length l)); intros [k H1].
      rewrite <- H1.
      rewrite Nat.log2_pow2; try lia.
      rewrite Nat.add_comm, Nat.sub_add; auto.
      rewrite H1; apply next_pow_2_ub. }
  { apply perfect_list_btree. }
  ext x; destruct x; auto.
Qed.

Lemma btree_infer_uniform_btree_const_1 n :
  btree_infer (cotuple (fun _ => 0) (fun _ => 1)) (uniform_btree n) =
    INeR n / INeR (next_pow_2 n).
Proof.
  unfold uniform_btree.
  (* rewrite btree_infer_btree_opt. *)
  rewrite reduce_btree_infer.
  rewrite btree_infer_list_btree_const_1.
  rewrite rev_range_spec, rev_length, range_length; reflexivity.
Qed.

Lemma btree_infer_bernoulli_btree_n n d :
  (n <= d)%nat ->
  btree_infer (cotuple (const 0) (fun b : bool => if b then 1 else 0))
    (bernoulli_btree n d) = INeR n / INeR (next_pow_2 d).
Proof.
  unfold bernoulli_btree.
  intro Hnd.
  (* rewrite btree_infer_btree_opt. *)
  rewrite btree_infer_fmap_bool.
  unfold compose, const.
  apply btree_infer_uniform_btree_lt; auto.
Qed.

Lemma btree_infer_uniform_btree_n n i :
  (i < n)%nat ->
  btree_infer (cotuple (const 0) (fun x : nat => if x =? i then 1 else 0))
    (uniform_btree n) = INeR 1 / INeR (next_pow_2 n).
Proof.
  unfold uniform_btree, compose, const; rewrite INeR_1.
  apply btree_infer_uniform_btree.
Qed.

Lemma btree_infer_bernoulli_btree_const_1 n d :
  btree_infer (cotuple (const 0) (const 1)) (bernoulli_btree n d) =
    INeR d / INeR (next_pow_2 d).
Proof.
  unfold bernoulli_btree.
  (* rewrite btree_infer_btree_opt. *)
  rewrite btree_infer_fmap_bool.
  apply btree_infer_uniform_btree_const_1.
Qed.

Lemma INeR_Qnum_Qden_Q2R p :
  Qred p = p ->
  (0 <= p)%Q ->
  INeR (Z.to_nat (Qnum p)) / INeR (Pos.to_nat (Qden p)) = Q2eR p.
Proof.
  intros Hp Hle.
  unfold Q2eR, eRdiv, INeR, eRmult, eRinv. simpl.
  destruct (R.R_eq_dec (INR (Pos.to_nat (Qden p))) 0).
  { exfalso.
    assert (0 < INR (Pos.to_nat (Qden p)))%R.
    { replace 0%R with (INR 0) by reflexivity.
      apply lt_INR, Pos2Nat.is_pos. }
    lra. }
  apply eR_eq; unfold Q2R; f_equal.
  - rewrite INR_IZR_INZ.
    rewrite Z2Nat.id.
    + repeat f_equal.
      unfold Qminmax.Qmax, GenericMinMax.gmax.
      destruct (0 ?= p) eqn:Hp0; auto.
      * apply Qeq_alt in Hp0.
        rewrite <- Hp.
        replace 0%Q with (Qred 0%Q) by reflexivity.
        apply Qred_complete; symmetry; auto.
      * apply Qgt_alt in Hp0.
        exfalso; eapply Qlt_not_le; eauto.
    + apply Qnum_nonnegative; auto.
  - f_equal.
    rewrite INR_IZR_INZ.
    rewrite positive_nat_Z.
    repeat f_equal.
    unfold Qminmax.Qmax, GenericMinMax.gmax.
    destruct (0 ?= p) eqn:Hp0; auto.
    + apply Qeq_alt in Hp0.
      rewrite <- Hp.
      replace 0%Q with (Qred 0%Q) by reflexivity.
      apply Qred_complete; symmetry; auto.
    + apply Qgt_alt in Hp0.
      exfalso; eapply Qlt_not_le; eauto.
Qed.

Lemma simple_btree_to_tree {A} f (t : btree A) :
  simple (btree_to_tree f t).
Proof. induction t; constructor; intros []; auto. Qed.

Lemma btree_infer_sum_1 {A} (f : A -> eR) (t : btree A) :
  bounded f 1 ->
  btree_infer f t + btree_infer (fun a => 1 - f a) t = 1.
Proof.
  revert f; induction t; intros f Hf; simpl.
  { eRauto. }
  rewrite <- eRplus_assoc.
  rewrite eRplus_comm4.
  rewrite eRplus_assoc.
  rewrite <- 2!eRmult_plus_distr_l.
  rewrite IHt1, IHt2; auto.
  rewrite eRmult_1_r, Q2eR_one_half.
  apply eRplus_half_plus_half.
Qed.

Corollary btree_infer_complement' {A} (f : A -> eR) (t : btree A) :
  bounded f 1 ->
  btree_infer f t = 1 - btree_infer (fun a => 1 - f a) t.
Proof.
  intro Hf; apply eRplus_eq_minus.
  { eRauto. }
  rewrite eRplus_comm; apply btree_infer_sum_1; auto.
Qed.

Lemma btree_infer_const_1_bernoulli_btree_positive n d :
  (0 < d)%nat ->
  0 < btree_infer (cotuple (const 0) (const 1)) (bernoulli_btree n d).
Proof.
  intro Hlt.
  unfold bernoulli_btree.
  (* rewrite btree_infer_btree_opt. *)
  rewrite btree_infer_fmap_bool.
  unfold compose.
  unfold const.
  rewrite btree_infer_uniform_btree_const_1.
  apply eRlt_0_eRdiv; eRauto.
  (* replace 0 with (INeR 0) by apply INeR_0. *)
  (* apply lt_INeR; auto. *)
Qed.

Lemma btree_infer_const_1_uniform_btree_positive n :
  (0 < n)%nat ->
  0 < btree_infer (cotuple (const 0) (const 1)) (uniform_btree n).
Proof.
  intro Hlt.
  unfold compose.
  unfold const.
  rewrite btree_infer_uniform_btree_const_1.
  apply eRlt_0_eRdiv; eRauto.
  (* replace 0 with (INeR 0) by apply INeR_0. *)
  (* apply lt_INeR; auto. *)
Qed.

Corollary btree_infer_bernoulli_btree_lt_1 n d :
  (0 < d)%nat ->
  btree_infer (cotuple (const 1) (const 0)) (bernoulli_btree n d) < 1.
Proof.
  intro Hd.
  rewrite btree_infer_complement'.
  2: { intros []; eRauto. }
  apply eRminus_pos_lt; eRauto.
  replace (fun a : unit + bool => 1 - cotuple (const 1) (const 0) a) with
    (cotuple (@const eR unit 0) (@const eR bool 1)).
  2: { ext lr; destruct lr; eRauto. }
  apply btree_infer_const_1_bernoulli_btree_positive; auto.
Qed.

Corollary btree_infer_uniform_btree_lt_1 n :
  (0 < n)%nat ->
  btree_infer (cotuple (const 1) (const 0)) (uniform_btree n) < 1.
Proof.
  intro Hd.
  rewrite btree_infer_complement'.
  2: { intros []; eRauto. }
  apply eRminus_pos_lt; eRauto.
  replace (fun a : unit + nat => 1 - cotuple (const 1) (const 0) a) with
    (cotuple (@const eR unit 0) (@const eR nat 1)).
  2: { ext lr; destruct lr; eRauto. }
  apply btree_infer_const_1_uniform_btree_positive; auto.
Qed.

Lemma no_fail_btree_to_tree {A} (f : A -> val) (b : btree A) :
  no_fail' (btree_to_tree f b).
Proof.
  revert f; induction b; intro f; simpl; constructor; intros []; auto.
Qed.

Lemma bernoulli_tree_twp_p (p : Q) :
  Qred p = p ->
  (0 <= p <= 1)%Q ->
  twp (bernoulli_tree p) (fun s => if as_bool (s ϵ) then 1 else 0) = Q2eR p.
Proof.
  intros Hp [H0p Hp0].
  unfold bernoulli_tree.
  rewrite twp_fix_iid; eauto with tree eR.
  { unfold bernoulli_tree_open.
    replace (fun s : St =>
               if is_int (s ϵ%nat)
               then 0
               else twp (Leaf s) (fun s0 => if as_bool (s0 ϵ%nat) then 1 else 0))
      with (fun s => match s ϵ with
                     | vbool b => if b then 1 else 0
                     | _ => 0
                     end).
    2: { unfold twp; ext s; simpl; destruct (s ϵ); auto. }
    rewrite twp_bernoulli_btree_to_tree.
    replace (fun s : St => if is_int (s ϵ) then 1 else 0) with
      (fun s => match s ϵ with
                | vint _ => 1
                | _ => 0
                end).
    2: { ext s; destruct (s ϵ); reflexivity. }
    rewrite twp_bernoulli_btree_to_tree'.
    rewrite btree_infer_bernoulli_btree_n.
    2: { apply Q_num_le_den; auto. }
    replace (cotuple (const 1) (const 0)) with
      (fun s : unit + bool => 1 - cotuple (const 0) (const 1) s).
    2: { ext lr; destruct lr; eRauto. }
    rewrite <- btree_infer_complement'.
    2: { intros []; eRauto. }
    rewrite btree_infer_bernoulli_btree_const_1.
    rewrite eRdiv_cancel_r.    
    - apply INeR_Qnum_Qden_Q2R; auto.
    - apply not_0_INeR.
      generalize (Pos2Nat.is_pos (Qden p)); lia.
    - apply not_0_INeR.
      generalize (next_pow_2_positive (Pos.to_nat (Qden p))); lia.
    - apply not_infty_INeR. }
  { unfold bernoulli_tree_open.
    replace (fun s : St => if is_int (s ϵ) then 1 else 0) with
      (fun s => match s ϵ with
                | vint _ => 1
                | _ => 0
                end).
    2: { ext s; destr; reflexivity. }
    rewrite twp_bernoulli_btree_to_tree'.
    rewrite btree_infer_complement'.
    2: { intros []; eRauto. }
    apply eRminus_pos_lt; eRauto.
    replace (fun a : unit + bool => 1 - cotuple (const 1) (const 0) a) with
      (cotuple (@const eR unit 0) (@const eR bool 1)).
    2: { ext lr; destruct lr; eRauto. }
    apply btree_infer_const_1_bernoulli_btree_positive.
    apply Pos2Nat.is_pos. }
Qed.

Lemma twp_bernoulli_tree_open_lt_1 n d :
  (0 < d)%nat ->
  twp (bernoulli_tree_open n d)
    (fun s : St => if is_int (s ϵ) then 1 else 0) < 1.
Proof.
  intro Hd.
  replace (fun s : St => if is_int (s ϵ) then 1 else 0) with
    (fun s => match s ϵ with
              | vint _ => 1
              | _ => 0
              end).
  2: { ext s; destr; reflexivity. }
  unfold bernoulli_tree_open.
  rewrite twp_bernoulli_btree_to_tree'.
  apply btree_infer_bernoulli_btree_lt_1; auto.
Qed.

(* Lemma twp_uniform_tree_open_lt_1 n : *)
(*   (0 < n)%nat -> *)
(*   twp (uniform_tree_open n) *)
(*     (fun s : St => if is_int (s 0%nat) then 1 else 0) < 1. *)
(* Proof. *)
(*   intro Hd. *)
(*   replace (fun s : St => if is_int (s 0%nat) then 1 else 0) with *)
(*     (fun s => match s O with *)
(*            | vint _ => 1 *)
(*            | _ => 0 *)
(*            end). *)
(*   2: { ext s; destr; reflexivity. } *)
(*   unfold uniform_tree_open. *)
(*   rewrite twp_uniform_btree_to_tree'. *)
(*   apply btree_infer_uniform_btree_lt_1; auto. *)
(* Qed. *)

Lemma twp_uniform_tree_open_lt_1 n :
  (0 < n)%nat ->
  twp (uniform_tree_open n)
    (fun s : St => if negb (is_nat (s ϵ)) then 1 else 0) < 1.
Proof.
  intro Hd.
  replace (fun s : St => if negb (is_nat (s ϵ)) then 1 else 0) with
    (fun s => (match s ϵ with
               | vint _ => 1
               | _ => 0
               end) + (match s ϵ with
                       | vbool _ => 1
                       | _ => 0
                       end)).
  2: { ext s; destruct (s ϵ); simpl; eRauto. }
  unfold uniform_tree_open.
  rewrite twp_sum.
  rewrite twp_uniform_btree_to_tree_bool.
  rewrite eRplus_0_r.
  rewrite twp_uniform_btree_to_tree'.
  apply btree_infer_uniform_btree_lt_1; auto.
Qed.

Lemma twpfail_uniform_tree_const_1 n :
  (0 < n)%nat ->
  twpfail (uniform_tree n) (const 1) = 1.
Proof.
  intro Hn.
  unfold twpfail.
  rewrite no_fail'_twp.
  2: { constructor; intro s; try constructor; apply no_fail_btree_to_tree. }
  unfold uniform_tree.
  erewrite twp_fix_iid.
  { apply eRdiv_eq_1.
    - intro HC.
      symmetry in HC.
      apply eRminus_eq_plus in HC.
      + rewrite eRplus_0_r in HC; revert HC.
        apply eRlt_neq, twp_uniform_tree_open_lt_1; auto.
      + eRauto.
      + apply twp_bounded.
        * apply wf_tree_btree_to_tree.
        * intro s; destr; eRauto.
    - apply eRle_infty_not_infty with (b:=1); eRauto.
    - rewrite simple_twp_twlp.
      2: { apply simple_btree_to_tree. }
      2: { unfold twp; intro s; destr; eRauto. }
      rewrite <- no_fail'_twp with (fl:=true).
      2: { apply no_fail_btree_to_tree. }
      unfold twlp.
      rewrite twlp_twp_complement.
      2: { apply wf_tree_btree_to_tree. }
      2: { unfold twp; intro s; destr; eRauto. }
      unfold twp; f_equal; f_equal; ext s; destr; eRauto. }
  { apply wf_tree_btree_to_tree. }
  { intro; constructor. }
  { apply twp_uniform_tree_open_lt_1; auto. }
  { reflexivity. }
Qed.

Lemma twpfail_bernoulli_tree_const_1 p :
  twpfail (bernoulli_tree p) (const 1) = 1.
Proof.
  unfold twpfail.
  rewrite no_fail'_twp.
  2: { constructor; intro s; try constructor; apply no_fail_btree_to_tree. }
  unfold bernoulli_tree.
  erewrite twp_fix_iid.
  { apply eRdiv_eq_1.
    - intro HC.
      symmetry in HC.
      apply eRminus_eq_plus in HC.
      + rewrite eRplus_0_r in HC; revert HC.
        apply eRlt_neq, twp_bernoulli_tree_open_lt_1, Pos2Nat.is_pos.
      + eRauto.
      + apply twp_bounded.
        * apply wf_tree_btree_to_tree.
        * intro s; destr; eRauto.
    - apply eRle_infty_not_infty with (b:=1); eRauto.
    - rewrite simple_twp_twlp.
      2: { apply simple_btree_to_tree. }
      2: { unfold twp; intro s; destr; eRauto. }
      rewrite <- no_fail'_twp with (fl:=true).
      2: { apply no_fail_btree_to_tree. }
      unfold twlp.
      rewrite twlp_twp_complement.
      2: { apply wf_tree_btree_to_tree. }
      2: { unfold twp; intro s; destr; eRauto. }
      unfold twp; f_equal; f_equal; ext s; destr; eRauto. }
  { apply wf_tree_btree_to_tree. }
  { intro; constructor. }
  { apply twp_bernoulli_tree_open_lt_1, Pos2Nat.is_pos. }
  { reflexivity. }
Qed.

Lemma uniform_tree_twp_twlp fl n f :
  (0 < n)%nat ->
  bounded f 1 ->
  twp_ fl (uniform_tree n) f = twlp_ fl (uniform_tree n) f.
Proof.
  intros Hn Hf.
  rewrite twlp_twp_complement; auto.
  2: { constructor; intro s; try constructor; apply wf_tree_btree_to_tree. }
  apply eRplus_eq_minus.
  { eRauto. }
  destruct fl.
  - rewrite <- twp__sum.
    etransitivity.
    2: { apply twpfail_uniform_tree_const_1; eauto. }
    unfold twpfail; f_equal.
    ext s; unfold const.
    rewrite <- eRminus_assoc; eRauto.
  - rewrite eRplus_comm.
    rewrite <- twp__sum.
    etransitivity.
    2: { apply twpfail_uniform_tree_const_1, Hn. }
    unfold twpfail; f_equal.
    ext s; unfold const; eRauto.
Qed.

Lemma bernoulli_tree_twp_twlp fl p f :
  bounded f 1 ->
  twp_ fl (bernoulli_tree p) f = twlp_ fl (bernoulli_tree p) f.
Proof.
  intro Hf.
  rewrite twlp_twp_complement; auto.
  2: { constructor; intro s; try constructor; apply wf_tree_btree_to_tree. }
  apply eRplus_eq_minus.
  { eRauto. }
  destruct fl.
  - rewrite <- twp__sum.
    etransitivity.
    2: { apply twpfail_bernoulli_tree_const_1. }
    unfold twpfail; f_equal.
    ext s; unfold const.
    rewrite <- eRminus_assoc; eRauto.
  - rewrite eRplus_comm.
    rewrite <- twp__sum.
    etransitivity.
    2: { apply twpfail_bernoulli_tree_const_1. }
    unfold twpfail; f_equal.
    ext s; unfold const; eRauto.
Qed.

Corollary bernoulli_tree_twp_p_compl (p : Q) :
  Qred p = p ->
  (0 <= p <= 1)%Q ->
  twp (bernoulli_tree p) (fun s => if as_bool (s ϵ) then 0 else 1) = 1 - Q2eR p.
Proof.
  intros Hp Hp'.
  apply eRplus_eq_minus.
  { intro HC; inv HC. }
  unfold twp.
  rewrite <- no_fail'_twp with (fl := true).
  2: { constructor; intro s; try constructor; apply no_fail_btree_to_tree. }
  rewrite bernoulli_tree_twp_twlp.
  2: { intro; destr; eRauto. }
  rewrite twlp_twp_complement.
  2: { constructor; intro.
       - apply wf_tree_btree_to_tree.
       - constructor. }
  2: { intro s; destr; eRauto. }
  rewrite eRplus_minus_assoc.
  2: { eRauto. }
  2: { apply twp__bounded.
       - constructor; intro.
         + apply wf_tree_btree_to_tree.
         + constructor.
       - intro; destr; eRauto. }
  rewrite fold_twp.
  replace (fun s : St => 1 - (if as_bool (s ϵ) then 0 else 1)) with
    (fun s => if as_bool (s ϵ) then 1 else 0).
  2: { ext s; destr; eRauto. }
  rewrite bernoulli_tree_twp_p; auto.
  rewrite <- eRplus_minus_assoc; eRauto.
Qed.

Lemma twp_uniform_tree (n i : nat) :
  (0 < n)%nat ->
  (i < n)%nat ->
  twp (uniform_tree n)
    (fun s => if as_nat (s ϵ) =? i then 1 else 0) = 1 / INeR n.
Proof.
  intros Hn Hi.
  unfold uniform_tree.
  rewrite twp_fix_iid; eauto with tree eR.
  { unfold uniform_tree_open.
    replace (fun s : St =>
               if negb (is_nat (s ϵ))
               then 0
               else twp (Leaf s)
                      (fun s0 => if as_nat (s0 ϵ) =? i then 1 else 0))
      with (fun s => match s ϵ with
                     | vnat m => if m =? i then 1 else 0
                     | _ => 0
                     end).
    2: { unfold twp; ext s; simpl; destruct (s ϵ) eqn:HsO; simpl; auto. }
    rewrite twp_uniform_btree_to_tree.
    replace (fun s : St => if negb (is_nat (s ϵ)) then 1 else 0) with
      (fun s : St => (match s ϵ with
                      | vint _ => 1
                      | _ => 0
                      end) + (match s ϵ with
                              | vbool _ => 1
                              | _ => 0
                              end)).
    2: { ext s; destruct (s ϵ); simpl; eRauto. }
    rewrite twp_sum.
    rewrite twp_uniform_btree_to_tree_bool.
    rewrite eRplus_0_r.
    rewrite twp_uniform_btree_to_tree'.
    rewrite btree_infer_uniform_btree_n; auto.
    replace (cotuple (const 1) (const 0)) with
      (fun s : unit + nat => 1 - cotuple (const 0) (const 1) s).
    2: { ext lr; destruct lr; eRauto. }
    rewrite <- btree_infer_complement'.
    2: { intros []; eRauto. }
    rewrite btree_infer_uniform_btree_const_1.
    rewrite eRdiv_cancel_r.
    - rewrite INeR_1; reflexivity.
    - apply not_0_INeR; lia.
    - apply not_0_INeR; generalize (next_pow_2_positive n); lia.
    - apply not_infty_INeR. }
  { unfold uniform_tree_open.
    replace (fun s : St => if negb (is_nat (s ϵ)) then 1 else 0) with
      (fun s : St => (match s ϵ with
                      | vint _ => 1
                      | _ => 0
                      end) + (match s ϵ with
                              | vbool _ => 1
                              | _ => 0
                              end)).
    2: { ext s; destruct (s ϵ); simpl; eRauto. }
    rewrite twp_sum.
    rewrite twp_uniform_btree_to_tree_bool.
    rewrite eRplus_0_r.
    rewrite twp_uniform_btree_to_tree'.
    rewrite btree_infer_complement'.
    2: { intros []; eRauto. }
    apply eRminus_pos_lt; eRauto.
    replace (fun a : unit + nat => 1 - cotuple (const 1) (const 0) a) with
      (cotuple (@const eR unit 0) (@const eR nat 1)).
    2: { ext lr; destruct lr; eRauto. }
    apply btree_infer_const_1_uniform_btree_positive; auto. }
Qed.

(* Definition disjoint {A} (f g : A -> eR) : Prop := *)
(*   forall x, f x = 0 \/ g x = 0. *)

(* Inductive list_disjoint {A} : list (A -> eR) -> Prop := *)
(* | list_disjoint_nil : list_disjoint nil *)
(* | list_disjoint_cons : forall P l, *)
(*     Forall (disjoint P) l -> *)
(*     list_disjoint l -> *)
(*     list_disjoint (P :: l). *)

Lemma twp_sum (t : tree) (l : list (St -> eR)) :
  twp_ false t (fun s => sum (map (fun f => f s) l)) = sum (map (fun f => twp t f) l).
Proof.
  unfold twp, sum.
  revert t; induction l; intros t; simpl.
  - apply twp_strict.
  - rewrite twp__sum; f_equal; auto.
Qed.

Lemma sum_eq_0 l : 
  Forall (eq 0) l ->
  sum l = 0.
Proof.
  induction 1; simpl; auto.
  rewrite IHForall; subst; eRauto.
Qed.

(* Lemma tree_all_twp_0 f t : *)
(*   simple t -> *)
(*   tree_all (fun s => f s = 0) t -> *)
(*   twp t f = 0. *)
(* Proof. *)
(*   unfold twp. *)
(*   induction 1; simpl; auto. *)
(*   - rewrite 2!H0; eRauto. *)
(*   - unfold loop_F. *)
(*     unfold iter. *)
(*     rewrite sup_apply_eR. *)
(*     apply equ_eR. *)
(*     apply sup_const'. *)
(*     apply equ_arrow; intro i. *)
(*     revert st. *)
(*     apply equ_arrow. *)
(*     apply eq_equ. *)
(*     induction i; ext st; simpl; auto. *)
(*     destruct (e st) eqn:Hest; auto. *)
(*     rewrite IHi, twp_strict; auto. *)
(* Qed. *)

(* Lemma tree_all_twp_0 f t : *)
(*   tree_all (fun s => f s = 0) t -> *)
(*   twp t f = 0. *)
(* Proof. *)
(*   unfold twp. *)
(*   induction 1; simpl; auto. *)
(*   - rewrite 2!H0; eRauto. *)
(*   - unfold loop_F. *)
(*     unfold iter. *)
(*     rewrite sup_apply_eR. *)
(*     apply equ_eR. *)
(*     apply sup_const'. *)
(*     apply equ_arrow; intro i. *)
(*     revert st. *)
(*     apply equ_arrow. *)
(*     apply eq_equ. *)
(*     induction i; ext st; simpl; auto. *)
(*     destruct (e st) eqn:Hest; auto. *)
(*     rewrite IHi, twp_strict; auto. *)
(* Qed. *)

(* Lemma loop_approx_0 e g f n st : *)
(*   g (const 0) = const 0 -> *)
(*   (* (forall s, e s = false -> f s = 0) -> *) *)
(*   (forall i s, tree_some (eq s) (fix_approx e g f i st) -> e s = false -> f s = 0) -> *)
(*   loop_approx e g f n st = 0. *)
(* Proof. *)
(*   revert e g f; induction n; intros e g f Hg Hf; ext s; simpl; auto. *)
(*   destruct (e s) eqn:Hes. *)
(*   - rewrite IHn; auto; rewrite Hg; auto. *)
(*   - rewrite Hf; auto. *)
(* Qed. *)

(* Lemma loop_approx_0 e g f n : *)
(*   g (const 0) = const 0 -> *)
(*   (* (forall s, e s = false -> f s = 0) -> *) *)
(*   (forall i s, tree_some (eq s) loop_approx e g f i s -> e s = false -> f s = 0) -> *)
(*   loop_approx e g f n = const 0. *)
(* Proof. *)
(*   revert e g f; induction n; intros e g f Hg Hf; ext s; simpl; auto. *)
(*   destruct (e s) eqn:Hes. *)
(*   - rewrite IHn; auto; rewrite Hg; auto. *)
(*   - rewrite Hf; auto. *)
(* Qed. *)

Lemma tree_all_twp_0 f t :
  simple t ->
  tree_all (fun s => f s = 0) t ->
  twp t f = 0.
Proof.
  unfold twp.
  revert f; induction t; simpl; intros f Ht Hall; inv Ht; inv Hall; auto.
  rewrite 2!H; eRauto.
Qed.
(* unfold iter. *)
(* rewrite <- loop_approx_iter_n_loop_F. *)
(* rewrite sup_apply_eR. *)
(* (* unfold iter, loop_F. *) *)
(* (* rewrite sup_apply_eR. *) *)
(* apply equ_eR. *)
(* apply sup_const'. *)

(*   apply equ_arrow. *)
(*   intro i. *)
(*   rewrite loop_approx_0. *)
(*   - reflexivity. *)
(*   - ext st; rewrite twp_strict; reflexivity. *)
(*   - intros st Hbst; apply H0. *)
(*     eapply H2; auto. *)

(*   apply equ_arrow; intro i. *)
(*   revert H2. *)
(*   revert s. *)
(*   (* apply equ_arrow. *) *)
(*   (* apply eq_equ. *) *)
(*   (* induction i; ext st; simpl; auto. *) *)


(*   induction i; intros st H2; simpl. *)
(*   { reflexivity. } *)
(*   destruct (b st) eqn:Hbst. *)
(*   - rewrite loop_approx_0. *)
(*     + rewrite twp_strict; reflexivity. *)
(*     + ext s; rewrite twp_strict; reflexivity. *)
(*     + intros s Hbs; apply H0. *)
(*       eapply H2; auto. *)

(*     (* apply equ_eR; unfold const. *) *)
(*     (* replace (iter_n *) *)
(*     (*            (fun (k : St -> eR) (s : St) => *) *)
(*     (*               if b s then twp_ false (t s) k else twp_ false (t0 s) f) *) *)
(*     (*            (fun _ : St => 0) i) with *) *)
(*     (*   (@const eR St 0). *) *)
(*     (* 2: { ext s; apply equ_eR. *) *)
(*     (*      rewrite IHi. *) *)
(*     (*      - reflexivity. *) *)
(*     (*      - intros j s' Hbs' Hsome. *) *)
(*     (*        eapply H2; auto. *) *)




(* Lemma tree_all_twp_0 f t : *)
(*   tree_all (fun s => f s = 0) t -> *)
(*   twp t f = 0. *)
(* Proof. *)
(*   unfold twp. *)
(*   induction 1; simpl; auto. *)
(*   - rewrite 2!H0; eRauto. *)
(*   - unfold loop_F. *)
(*     unfold iter. *)
(*     rewrite sup_apply_eR. *)
(*     apply equ_eR. *)
(*     apply sup_const'. *)
(*     apply equ_arrow; intro i. *)
(*     revert H H0. *)
(*     revert st. *)
(*     (* apply equ_arrow. *) *)
(*     (* apply eq_equ. *) *)
(*     (* induction i; ext st; simpl; auto. *) *)
(*     induction i; intros st H H0; simpl. *)
(*     { reflexivity. } *)
(*     destruct (G st) eqn:HGst. *)
(*     + (* apply IHi in H; auto. *) *)
(*       replace (iter_n *)
(*                  (fun (k0 : St -> eR) (s : St) => *)
(*                     if G s then twp_ false (g s) k0 else *)
(*                       twp_ false (k s) f) (const 0) i) with *)
(*         (@const eR St 0). *)
(*       2: { ext s; apply equ_eR. *)
(*            rewrite IHi; auto. *)
(*            - reflexivity. *)
(*            - intros; eapply H; eauto. *)


(* Qed. *)

Inductive btree_all {A} (P : A -> Prop) : btree A -> Prop :=
| btree_all_leaf : forall x, P x -> btree_all P (BLeaf x)
| btree_all_node : forall l r,
    btree_all P l ->
    btree_all P r ->
    btree_all P (BNode l r).

Inductive btree_some {A} (P : A -> Prop) : btree A -> Prop :=
| btree_some_leaf : forall x, P x -> btree_some P (BLeaf x)
| btree_some_node_l : forall l r,
    btree_some P l ->
    btree_some P (BNode l r)
| btree_some_node_r : forall l r,
    btree_some P r ->
    btree_some P (BNode l r).

Lemma btree_some_impl {A} (P Q : A -> Prop) (t : btree A) :
  (forall x, P x -> Q x) ->
  btree_some P t ->
  btree_some Q t.
Proof. induction t; intros HPQ HP; inv HP; solve [constructor; auto]. Qed.

Lemma Forall_btree_all_list_btree_aux {A} (P : A -> Prop) (l : list A) n :
  Forall P l ->
  btree_all (cotuple (const True) P) (list_btree_aux l n).
Proof.
  simpl.
  revert P l; induction n; intros P l Hl; simpl.
  - destruct l; simpl.
    + constructor; apply I.
    + constructor; inv Hl; auto.
  - constructor; eauto.
    + apply IHn, Forall_take; auto.
    + apply IHn, Forall_drop; auto.
Qed.

Lemma btree_all_tree_all_uniform_btree_to_tree P t :
  btree_all (cotuple (const True) P) t ->
  tree_all (fun s => is_nat (s ϵ) = false \/ P (as_nat (s ϵ)))
    (uniform_btree_to_tree t).
Proof.
  unfold uniform_btree_to_tree.
  induction t; intros Hall; inv Hall; simpl.
  { destruct a as [[]|a]; simpl.
    - constructor; left; reflexivity.
    - constructor; right; auto. }
  constructor; intros [].
  - apply IHt1; auto.
  - apply IHt2; auto.
Qed.

Lemma twp_bernoulli_btree_to_tree_vbool t f :
  twp_ false (uniform_btree_to_tree t)
    (fun s => match s ϵ with
              | vbool b => f b
              | _ => 0
              end) = 0.
Proof.
  revert f; induction t; intros f; simpl.
  { destruct a as [[]|a]; simpl; auto. }
  rewrite IHt1, IHt2; eRauto.
Qed.

Lemma eRmult_lt_compat_l a b c :
  c * a < c * b ->
  a < b.
Proof.
  unfold eRmult.
  intro Hlt.
  destruct c as [c|].
  - destruct a as [a|].
    + destruct b as [b|].
      * inv Hlt; constructor; nra.
      * constructor.
    + destruct b as [b|].
      * destruct (eR_eq_dec (er c r) 0).
        { inv e; inv Hlt; lra. }
        inv Hlt.
      * destruct (eR_eq_dec (er c r) 0); auto.
        inv Hlt; lra.
  - destruct (eR_eq_dec a 0); subst.
    + destruct (eR_eq_dec b 0); subst; eRauto.
    + destruct (eR_eq_dec b 0); inv Hlt.
Qed.

(* Lemma eRmult_lt_compat_l a b c : *)
(*   a < b -> *)
(*   0 < c -> *)
(*   c <> infty -> *)
(*   c * a < c * b. *)
(* Proof. *)
(*   intros Hab Hc Hc'. *)
(*   unfold eRmult. *)
(*   destruct c as [c|]. *)
(*   2: { congruence. } *)
(*   inv Hc. *)
(*   destruct b as [b|]. *)
(*   - inv Hab; constructor; apply Rmult_lt_compat_l; auto. *)
(*   - destruct a as [a|]. *)
(*     + destr. *)
(*       * inv e; lra. *)
(*       * constructor. *)
(*     + inv Hab. *)
(* Qed. *)

Lemma btree_infer_bounded {A} (t : btree A) f ub :
  bounded f ub ->
  btree_infer f t <= ub.
Proof.
  revert f ub; induction t; intros f ub Hf; simpl; auto.
  rewrite Q2eR_one_half.
  replace (1 / 2 * btree_infer f t2) with ((1 - 1 / 2) * btree_infer f t2).
  2: { rewrite eRminus_1_2; reflexivity. }
  apply eRle_convex_sum; auto.
  cut (1 / 2 <= 2 / 2).
  { eRauto. }
  apply eRle_div; constructor; lra.
Qed.

Lemma btree_some_0_btree_infer_lt_1 {A} f (t : btree A) :
  bounded f 1 ->
  btree_some (fun x => f x = 0) t ->
  btree_infer f t < 1.
Proof.
  revert f; induction t; intros f Hf Hsome; inv Hsome; simpl.
  - rewrite H0; eRauto.
  - apply IHt1 in H0; auto.
    rewrite <- eRmult_plus_distr_l.
    apply eRmult_lt_compat_l with (c := 2).
    rewrite <- eRmult_assoc.
    replace (2 * Q2eR (1 # 2)) with 1.
    2: { unfold eRmult; simpl; apply eR_eq; compute; lra. }
    rewrite eRmult_1_l.
    replace (2 * 1) with (1 + 1).
    2: { apply eR_eq; lra. }
    eapply btree_infer_bounded in Hf.
    apply eRplus_lt_compat; eauto with eR.
  - apply IHt2 in H0; auto.
    rewrite <- eRmult_plus_distr_l.
    apply eRmult_lt_compat_l with (c := 2).
    rewrite <- eRmult_assoc.
    replace (2 * Q2eR (1 # 2)) with 1.
    2: { unfold eRmult; simpl; apply eR_eq; compute; lra. }
    rewrite eRmult_1_l.
    replace (2 * 1) with (1 + 1).
    2: { apply eR_eq; lra. }
    eapply btree_infer_bounded in Hf.
    rewrite eRplus_comm.
    apply eRplus_lt_compat; eauto with eR.
Qed.

Lemma btree_infer_list_btree_aux {A} (l : list A) n :
  (O < length l)%nat ->
  btree_infer (cotuple (const 1) (const 0)) (list_btree_aux l n) < 1.
Proof.
  intro Hl; apply btree_some_0_btree_infer_lt_1.
  { intros [[]|a]; eRauto. }
  apply btree_some_impl with (P := cotuple (const False) (const True)).
  { intros [[]|a] []; reflexivity. }
  revert l Hl.
  induction n; intros l Hl; simpl.
  { destruct l; simpl in *; try lia.
    constructor. simpl. apply I. }
  constructor; apply IHn.
  rewrite take_length_min.
  apply Nat.min_case; auto.
  apply pow_positive; lia.
Qed.

Lemma reduce_btree_all {A} (t : btree (unit + A)) P :
  btree_all (cotuple (const True) P) t ->
  btree_all (cotuple (const True) P) (reduce_btree t).
Proof.
  (* unfold const. *)
  revert P; induction t; intros P Ht; inv Ht; simpl.
  { constructor; auto. }
  destruct (reduce_btree t1) eqn:Ht1.
  - destruct s.
    + destruct u.
      destruct (reduce_btree t2) eqn:Ht2.
      * destruct s.
        { destruct u; constructor; apply I. }
        constructor; auto.
      * constructor; auto.
    + constructor; auto.
  - constructor; auto.
Qed.

Lemma twp_uniform_tree_sum (n : nat) (f : nat -> eR) :
  (0 < n)%nat ->
  twp (uniform_tree n) (fun s => f (as_nat (s ϵ))) =
    sum (map (fun i => f i / INeR n) (range n)).
Proof.
  intro Hn.
  replace (fun s : St => f (as_nat (s ϵ))) with
    (fun s => sum (map (fun i => if Nat.eqb (as_nat (s ϵ)) i then
                                   f (as_nat (s ϵ)) else 0) (range n)) +
                if n <=? as_nat (s ϵ) then f (as_nat (s ϵ)) else 0).
  2: { clear Hn; ext s.
       destruct (s ϵ) eqn:HsO; simpl.
       - revert f s b HsO.
         induction n; simpl; intros f s b HsO.
         + eRauto.
         + rewrite eRplus_0_r.
           rewrite map_app.
           unfold sum.
           rewrite fold_right_app.
           simpl.
           unfold sum in IHn.
           rewrite eRplus_0_r.
           destruct n; simpl; auto.
           specialize (IHn f s b HsO).
           simpl in IHn.
           rewrite eRplus_0_r in IHn.
           apply IHn.
       - destruct (Nat.leb_spec0 n n0).
         + rewrite sum_eq_0; eRauto.
           apply Forall_forall.
           intros x Hx.
           apply in_map_iff in Hx.
           destruct Hx as [i [Hx Hin]].
           apply in_range in Hin.
           destruct (Nat.eqb_spec n0 i); subst; try lia; auto.
         + rewrite eRplus_0_r.
           apply not_le in n1.
           apply Nat.le_succ_l in n1.
           induction n; simpl.
           { lia. }
           rewrite map_app, sum_app; simpl; rewrite eRplus_0_r.
           destruct (Nat.eqb_spec n0 n); subst.
           * rewrite sum_eq_0; eRauto.
             apply Forall_forall; intros x Hx.
             apply in_map_iff in Hx; destruct Hx as [i [Hx Hin]].
             apply in_range in Hin.
             destruct (Nat.eqb_spec n i); subst; auto; lia.
           * rewrite eRplus_0_r; apply IHn; lia.
       - revert f s z HsO.
         induction n; simpl; intros f s z HsO.
         + eRauto.
         + rewrite eRplus_0_r.
           rewrite map_app.
           unfold sum.
           rewrite fold_right_app.
           simpl.
           unfold sum in IHn.
           rewrite eRplus_0_r.
           destruct n; simpl; auto.
           specialize (IHn f s z HsO).
           simpl in IHn.
           rewrite eRplus_0_r in IHn.
           apply IHn. }
  unfold twp.
  rewrite twp__sum.
  replace (fun s : St =>
             sum
               (map (fun i : nat => if as_nat (s ϵ) =? i then
                                      f (as_nat (s ϵ)) else 0) (range n))) with
    (fun s => sum (map (fun f => f s)
                     (map (fun i s => if as_nat (s ϵ) =? i then
                                        f (as_nat (s ϵ)) else 0) (range n)))).
  2: { ext s; rewrite map_map; reflexivity. }
  rewrite twp_sum.
  replace (twp_ false (uniform_tree n)
             (fun s : St => if n <=? as_nat (s ϵ) then f (as_nat (s ϵ)) else 0))
    with 0.
  2: { unfold uniform_tree.
       assert (Hlt: twp (uniform_tree_open n)
                      (fun s : St => if negb (is_nat (s ϵ)) then 1 else 0) < 1).
       { unfold uniform_tree_open.
         replace (fun s : St => if negb (is_nat (s ϵ)) then 1 else 0) with
           (fun s => (match s ϵ with
                      | vint _ => 1
                      | _ => 0
                      end) + (match s ϵ with
                              | vbool _ => 1
                              | _ => 0
                              end)).
         2: { ext s; destruct (s ϵ); simpl; eRauto. }
         unfold twp; rewrite twp__sum.
         rewrite twp_uniform_btree_to_tree'.
         rewrite twp_bernoulli_btree_to_tree_vbool; eRauto.
         unfold uniform_btree.
         unfold const.
         rewrite reduce_btree_infer.
         apply btree_infer_list_btree_aux.
         rewrite rev_range_spec, rev_length, range_length; auto. }         
       rewrite twp_fix_iid; auto.
       - replace (fun s : St =>
                    if negb (is_nat (s ϵ))
                    then 0
                    else
                      twp (Leaf s) (fun s0 : St => if n <=? as_nat (s0 ϵ)
                                                then f (as_nat (s0 ϵ)) else 0))
           with (fun s : St =>
                   if negb (is_nat (s ϵ)) then 0
                   else if n <=? as_nat (s ϵ) then f (as_nat (s ϵ)) else 0).
         2: { ext s; unfold twp; simpl; destruct (s ϵ); auto. }
         rewrite tree_all_twp_0; eRauto.
         + apply simple_btree_to_tree.
         + clear Hlt.
           unfold uniform_tree_open. simpl.
           unfold uniform_btree.
           set (P := fun m => (m < n)%nat).
           apply tree_all_impl with
             (P := fun s : St => is_nat (s ϵ) = false \/ P (as_nat (s ϵ))).
           { intros s Hs; destruct (s ϵ) eqn:HsO; simpl; auto.
             destruct Hs as [Hs|Hs].
             { inv Hs. }
             simpl in *; apply leb_correct_conv in Hs; rewrite Hs; reflexivity. }
           apply btree_all_tree_all_uniform_btree_to_tree.
           unfold P.
           apply reduce_btree_all.
           apply Forall_btree_all_list_btree_aux.
           apply Forall_forall; intros x Hx.
           apply in_rev_range_lt in Hx; auto.
       - apply wf_tree_btree_to_tree.
       - intro; constructor. }
  rewrite eRplus_0_r.
  f_equal.
  rewrite map_map.
  apply map_ext_in.
  intros i Hi.
  replace (fun s : string -> val => if as_nat (s ϵ) =? i then f (as_nat (s ϵ)) else 0)
    with (fun s => f i * if as_nat (s ϵ) =? i then 1 else 0).
  2: { ext s; destruct (Nat.eqb_spec (as_nat (s ϵ)) i); eRauto. }
  rewrite twp_scalar.
  rewrite twp_uniform_tree; auto.
  - unfold eRdiv; rewrite eRmult_1_l; reflexivity.
  - apply in_range in Hi; auto.
Qed.
