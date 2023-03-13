(** * Uniform and Bernoulli CF trees (essential for debiasing). *)

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

From zar Require Import
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
| BNode : btree A -> btree A -> btree A.

Fixpoint btree_map {A B} (f : A -> B) (t : btree A) : btree B :=
  match t with
  | BLeaf x => BLeaf (f x)
  | BNode t1 t2 => BNode (btree_map f t1) (btree_map f t2)
  end.

Fixpoint btree_infer {A} (f : A -> eR) (t : btree A) : eR :=
  match t with
  | BLeaf x => f x
  | BNode t1 t2 => Q2eR (1#2) * btree_infer f t1 + Q2eR (1#2) * btree_infer f t2
  end.

Fixpoint btree_to_tree {A} (t : btree A) : tree A :=
  match t with
  | BLeaf x => Leaf x
  | BNode t1 t2 =>
      Choice (1#2) (fun b => if b then btree_to_tree t1 else btree_to_tree t2)
  end.

(* Definition bernoulli_btree_to_tree : btree (unit + bool) -> tree (unit + bool) := *)
(*   btree_to_tree. *)

(* Definition uniform_btree_to_tree : btree (unit + nat) -> tree St := *)
(*   btree_to_tree (cotuple (const (vint 0)) vnat). *)

(* Lemma twp_btree_to_tree {A} (f : A -> eR) (t : btree (unit + A)) : *)
(*   twp (btree_to_tree t) (cotuple (const 0) f) = *)
(*     btree_infer (cotuple (const 0) f) t. *)
(* Proof. *)
(*   unfold twp; revert f; induction t; intro f; simpl. *)
(*   - destruct a; constructor. *)
(*   - rewrite IHt1, IHt2; f_equal; f_equal. *)
(*     rewrite Q2eR_one_half, eRminus_1_2; reflexivity. *)
(* Qed. *)

Lemma twp_btree_to_tree {A} (f : A -> eR) (t : btree A) :
  twp (btree_to_tree t) f = btree_infer f t.
Proof.
  unfold twp; revert f; induction t; intro f; simpl; auto.
  rewrite IHt1, IHt2; f_equal; f_equal.
  rewrite Q2eR_one_half, eRminus_1_2; reflexivity.
Qed.

(* Lemma twp_bernoulli_btree_to_tree' {A} r (t : btree (unit + A)) : *)
(*   twp (btree_to_tree t) (cotuple (const r) (const 0)) = *)
(*     btree_infer (cotuple (const r) (const 0)) t. *)
(* Proof. *)
(*   unfold twp; revert r; induction t; intro r; simpl. *)
(*   - destruct a; constructor. *)
(*   - rewrite IHt1, IHt2; f_equal; f_equal. *)
(*     rewrite Q2eR_one_half, eRminus_1_2; reflexivity. *)
(* Qed. *)

Lemma tree_unbiased_btree_to_tree {A} (t : btree A) :
  tree_unbiased (btree_to_tree t).
Proof. induction t; constructor; try reflexivity; intros []; auto. Qed.

Import Lqa.
Lemma wf_tree_btree_to_tree {A} (t : btree A) :
  wf_tree (btree_to_tree t).
Proof. induction t; constructor; try lra; intros []; auto. Qed.
Lemma wf_tree'_btree_to_tree {A} (t : btree A) :
  wf_tree' (btree_to_tree t).
Proof.
  induction t; constructor; simpl; try lra; auto; intros []; auto.
Qed.
#[global] Hint Resolve wf_tree_btree_to_tree : tree.
#[global] Hint Resolve wf_tree'_btree_to_tree : tree.
Import Lra.

(* Instead of divide list, take and drop 2^n' from the list. *)
Fixpoint list_btree_aux {A} (l : list A) (n : nat) : btree (unit + A) :=
  match n with
  | O => match l with
        | x :: _ => BLeaf (inr x)
        | _ => BLeaf (inl tt)
        end
  | S n' =>
      BNode (list_btree_aux (take (2^n') l) n')
        (list_btree_aux (drop (2^n') l) n')
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

(** Eliminate unnecessary fails. *)
Fixpoint reduce_btree {A} (t : btree (unit + A)) : btree (unit + A) :=
  match t with
  | BNode l r => let l' := reduce_btree l in
                let r' := reduce_btree r in
                match (l', r') with
                | (BLeaf (inl tt), BLeaf (inl tt)) => BLeaf (inl tt)
                | _ => BNode l' r'
                end
  | _ => t
  end.

(** More general -- coalesce leaf nodes. *)
Fixpoint reduce_btree' {A} `{EqType A} (t : btree A) : btree A :=
  match t with
  | BNode l r =>
      let l' := reduce_btree' l in
      let r' := reduce_btree' r in
      match (l', r') with
      | (BLeaf x, BLeaf y) => if eqb x y then BLeaf x else BNode l' r'
      | _ => BNode l' r'
      end
  | _ => t
  end.

Lemma reduce_btree_infer {A} (f : A -> eR) (t : btree (unit + A)) (c : eR) :
  btree_infer (cotuple (fun _ => c) f) (reduce_btree t) =
    btree_infer (cotuple (fun _ => c) f) t.
Proof.
  revert f; induction t; intro f; simpl; auto.
  destruct (reduce_btree t1) eqn:Ht1.
  - destruct s; simpl in *.
    + destruct u, (reduce_btree t2) eqn:Ht2; simpl.
      * destruct s; simpl in *.
        { destruct u; rewrite <- IHt1, <- IHt2.
          rewrite Q2eR_one_half.
          rewrite <- eRmult_2_plus.
          rewrite <- eRmult_assoc.
          rewrite <- eRmult_half_div_2.
          eRauto.
          rewrite eRmult_eRdiv_assoc.
          rewrite eRmult_div_cancel;  eRauto. }
        { rewrite <- IHt1, IHt2; eRauto. }
      * rewrite <- IHt1, <- IHt2; simpl; eRauto.
    + rewrite IHt1, IHt2; reflexivity.
  - simpl; rewrite <- IHt1, IHt2; simpl; eRauto.
Qed.

Lemma reduce_btree'_infer {A} `{EqType A} (f : A -> eR) (t : btree A) :
  btree_infer f (reduce_btree' t) = btree_infer f t.
Proof.
  revert f; induction t; intro f; simpl; auto.
  destruct (reduce_btree' t1) eqn:Ht1.
  - simpl in *.
    + destruct (reduce_btree' t2) eqn:Ht2; simpl.
      * simpl in *.
        { rewrite <- IHt1, <- IHt2.
          rewrite Q2eR_one_half.
          rewrite 2!eRmult_half_div_2.
          rewrite eRplus_combine_fract.
          destruct (eqb_spec a a0); subst; simpl.
          - rewrite <- eRmult_2_plus.
            rewrite eRmult_div_cancel; eRauto.
          - rewrite Q2eR_one_half.
            rewrite 2!eRmult_half_div_2.
            rewrite eRplus_combine_fract; auto. }
      * rewrite <- IHt1, <- IHt2; simpl; eRauto.
  - simpl; rewrite <- IHt1, IHt2; simpl; eRauto.
Qed.

Definition uniform_btree (n : nat) : btree (unit + nat) :=
  reduce_btree (list_btree (rev_range n)).

Definition uniform_btree' (n : nat) : btree (unit + nat) :=
  list_btree (rev_range n).

(* Eval compute in (uniform_btree 10). *)
(* Eval compute in (reduce_btree (uniform_btree 10)). *)

Inductive congruent {A B} : btree A -> btree B -> Prop :=
| congruent_leaf : forall x y, congruent (BLeaf x) (BLeaf y)
| congruent_node : forall t1 t1' t2 t2',
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
  reduce_btree' (btree_map (sum_map (fun x => x) (fun i => Nat.ltb i n)) (uniform_btree d)).

(* Eval compute in (bernoulli_btree 1 3). *)

Definition bernoulli_tree_open (n d : nat) : tree (unit + bool) :=
  btree_to_tree (bernoulli_btree n d).

Definition bernoulli_tree (p : Q) : tree bool :=
  let t := bernoulli_tree_open (Z.to_nat (Qnum p)) (Pos.to_nat (Qden p)) in
  Fix (inl tt) is_inl (fun _ => t) (cotuple (fun _ => Leaf false) (@Leaf _)).

(** TODO: could omit Fix node when n is a power of 2 (to enable more
aggressive optimizations since Fix nodes complicate things). *)
Definition uniform_tree_open (n : nat) : tree (unit + nat) :=
  btree_to_tree (uniform_btree n).

Definition uniform_tree (n : nat) : tree nat :=
  let t := uniform_tree_open n in
  Fix (inl tt) is_inl (fun _ => t) (cotuple (fun _ => Leaf O) (@Leaf _)).

Lemma btree_infer_fmap_bool {A} (f : A -> bool) (g : bool -> eR) (t : btree (unit + A)) :
  btree_infer (cotuple (const 0) g) (btree_map (sum_map (fun x => x) f) t) =
    btree_infer (cotuple (const 0) (g ∘ f)) t.
Proof.
  revert f; induction t; intro f; simpl; try lra.
  - destruct a; auto.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma btree_infer_uniform_btree' n i :
  (i < n)%nat ->
  btree_infer (cotuple (fun _ : unit => 0) (fun x : nat => if x =? i then 1 else 0))
    (uniform_btree' n) = 1 / INeR (next_pow_2 n).
Proof.
  intro Hlt.
  unfold uniform_btree'.
  replace (cotuple (fun _ => 0) (fun x => if x =? i then 1 else 0)) with
    (fun x : unit + nat => if (match x with
                          | inl _ => false
                          | inr j => j =? i
                          end) then 1 else 0).
  2: { ext lr; destruct lr; auto. }
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

Lemma btree_infer_uniform_btree n i :
  (i < n)%nat ->
  btree_infer (cotuple (fun _ : unit => 0) (fun x : nat => if x =? i then 1 else 0))
    (uniform_btree n) = 1 / INeR (next_pow_2 n).
Proof.
  intro Hlt.
  unfold uniform_btree.
  rewrite reduce_btree_infer.
  apply btree_infer_uniform_btree'; auto.
Qed.

Lemma btree_infer_uniform_btree'_lt n d :
  (n <= d)%nat ->
  btree_infer (cotuple (fun _ : unit => 0) (fun x : nat => if x <? n then 1 else 0))
    (uniform_btree' d) = INeR n / INeR (next_pow_2 d).
Proof.
  intro Hle.
  unfold uniform_btree'.
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

Lemma btree_infer_uniform_btree_lt n d :
  (n <= d)%nat ->
  btree_infer (cotuple (fun _ : unit => 0) (fun x : nat => if x <? n then 1 else 0))
    (uniform_btree d) = INeR n / INeR (next_pow_2 d).
Proof.
  intro Hle.
  unfold uniform_btree.
  rewrite reduce_btree_infer.
  apply btree_infer_uniform_btree'_lt; auto.
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

Lemma btree_infer_uniform_btree'_const_1 n :
  btree_infer (cotuple (fun _ => 0) (fun _ => 1)) (uniform_btree' n) =
    INeR n / INeR (next_pow_2 n).
Proof.
  unfold uniform_btree'.
  rewrite btree_infer_list_btree_const_1.
  rewrite rev_range_spec, rev_length, range_length; reflexivity.
Qed.

Lemma btree_infer_uniform_btree_const_1 n :
  btree_infer (cotuple (fun _ => 0) (fun _ => 1)) (uniform_btree n) =
    INeR n / INeR (next_pow_2 n).
Proof.
  unfold uniform_btree.
  rewrite reduce_btree_infer.
  apply btree_infer_uniform_btree'_const_1.
Qed.

Lemma btree_infer_bernoulli_btree_n n d :
  (n <= d)%nat ->
  btree_infer (cotuple (const 0) (fun b : bool => if b then 1 else 0))
    (bernoulli_btree n d) = INeR n / INeR (next_pow_2 d).
Proof.
  unfold bernoulli_btree.
  intro Hnd.
  rewrite reduce_btree'_infer.
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
  rewrite reduce_btree'_infer.
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

Lemma simple_btree_to_tree {A} (t : btree A) :
  simple (btree_to_tree t).
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
  rewrite reduce_btree'_infer.
  rewrite btree_infer_fmap_bool.
  unfold compose.
  unfold const.
  rewrite btree_infer_uniform_btree_const_1.
  apply eRlt_0_eRdiv; eRauto.
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

Lemma no_fail_btree_to_tree {A} (b : btree A) :
  no_fail' (btree_to_tree b).
Proof. induction b; simpl; constructor; intros []; auto. Qed.

Lemma bernoulli_tree_twp_p (p : Q) :
  Qred p = p ->
  (0 <= p <= 1)%Q ->
  twp (bernoulli_tree p) (fun b => if b then 1 else 0) = Q2eR p.
Proof.
  intros Hp [H0p Hp0].
  unfold bernoulli_tree.
  rewrite twp_fix_iid; eauto with tree eR.
  { unfold bernoulli_tree_open.
    replace (fun s : unit + bool =>
               if is_inl s
               then 0
               else
                 twp (cotuple (fun _ : unit => Leaf false) (Leaf (A:=bool)) s)
                   (fun b : bool => if b then 1 else 0)) with
      (cotuple (@const eR unit 0) (fun x => twp (Leaf x)
                                           (fun b : bool => if b then 1 else 0))).
    2: { ext s; destruct s; simpl; auto. }
    rewrite twp_btree_to_tree.
    replace (fun s : unit + bool => if is_inl s then 1 else 0) with
      (@cotuple unit bool eR (const 1) (const 0)).
    2: { ext s; destruct s; auto. }
    rewrite twp_btree_to_tree.
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
  { intros []; constructor. }
  { unfold bernoulli_tree_open.
    replace (fun s : unit + bool => if is_inl s then 1 else 0) with
      (@cotuple unit bool eR (const 1) (const 0)).
    2: { ext s; destruct s; auto. }
    rewrite twp_btree_to_tree.
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
    (fun s : unit + bool => if is_inl s then 1 else 0) < 1.
Proof.
  intro Hd.
  unfold bernoulli_tree_open.
  rewrite twp_btree_to_tree.
  replace (fun s : unit + bool => if is_inl s then 1 else 0) with
    (@cotuple unit bool eR (const 1) (const 0)).
  2: { ext s; destruct s; auto. }
  apply btree_infer_bernoulli_btree_lt_1; auto.
Qed.

Lemma twp_uniform_tree_open_lt_1 n :
  (0 < n)%nat ->
  twp (uniform_tree_open n)
    (fun s : unit + nat => if is_inl s then 1 else 0) < 1.
Proof.
  intro Hd.
  replace (fun s : unit + nat => if is_inl s then 1 else 0) with
    (fun s => @cotuple unit nat eR (const 1) (const 0) s +
             cotuple (const 0) (const 0) s).
  2: { ext s; destruct s; simpl; unfold const; eRauto. }
  unfold uniform_tree_open.
  rewrite twp_plus.
  replace (cotuple (const 0) (const 0)) with (@const eR (unit + nat) 0).
  2: { ext s; destruct s; unfold const; auto. }
  unfold twp.
  rewrite twp_strict; eRauto.
  rewrite fold_twp.
  rewrite twp_btree_to_tree.
  apply btree_infer_uniform_btree_lt_1; auto.
Qed.

Lemma twpfail_uniform_tree_const_1 n :
  (0 < n)%nat ->
  twpfail (uniform_tree n) (const 1) = 1.
Proof.
  intro Hn.
  unfold twpfail.
  rewrite no_fail'_twp.
  2: { constructor; intros []; simpl; try constructor;
       apply no_fail_btree_to_tree. }
  unfold uniform_tree.
  erewrite twp_fix_iid.
  { apply eRdiv_eq_1.
    - intro HC.
      symmetry in HC.
      apply eRminus_eq_plus in HC.
      + rewrite eRplus_0_r in HC; revert HC.
        apply eRlt_neq; apply twp_uniform_tree_open_lt_1; auto.
      + eRauto.
      + apply twp_bounded.
        * apply wf_tree_btree_to_tree.
        * intro s; destr; eRauto.
    - apply eRle_infty_not_infty with (b:=1); eRauto.
    - rewrite simple_twp_twlp.
      2: { apply simple_btree_to_tree. }
      2: { unfold twp; intros []; simpl; eRauto. }
      rewrite <- no_fail'_twp with (fl:=true).
      2: { apply no_fail_btree_to_tree. }
      unfold twlp.
      rewrite twlp_twp_complement.
      2: { apply wf_tree_btree_to_tree. }
      2: { unfold twp; intros []; simpl; eRauto. }
      unfold twp; f_equal; f_equal; ext s; destruct s; simpl; eRauto. }
  { apply wf_tree_btree_to_tree. }
  { intros []; constructor. }
  { apply twp_uniform_tree_open_lt_1; auto. }
  { reflexivity. }
Qed.

Lemma twpfail_bernoulli_tree_const_1 p :
  twpfail (bernoulli_tree p) (const 1) = 1.
Proof.
  unfold twpfail.
  rewrite no_fail'_twp.
  2: { constructor; intros []; try constructor; apply no_fail_btree_to_tree. }
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
      2: { unfold twp; intros []; eRauto. }
      rewrite <- no_fail'_twp with (fl:=true).
      2: { apply no_fail_btree_to_tree. }
      unfold twlp.
      rewrite twlp_twp_complement.
      2: { apply wf_tree_btree_to_tree. }
      2: { unfold twp; intros []; eRauto. }
      unfold twp; f_equal; f_equal; ext s; destruct s; eRauto. }
  { apply wf_tree_btree_to_tree. }
  { intros []; constructor. }
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
  2: { constructor; intros []; try constructor; apply wf_tree_btree_to_tree. }
  apply eRplus_eq_minus.
  { eRauto. }
  destruct fl.
  - rewrite <- twp__plus.
    etransitivity.
    2: { apply twpfail_uniform_tree_const_1; eauto. }
    unfold twpfail; f_equal.
    ext s; unfold const.
    rewrite <- eRminus_assoc; eRauto.
  - rewrite eRplus_comm.
    rewrite <- twp__plus.
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
  2: { constructor; intros []; try constructor; apply wf_tree_btree_to_tree. }
  apply eRplus_eq_minus.
  { eRauto. }
  destruct fl.
  - rewrite <- twp__plus.
    etransitivity.
    2: { apply twpfail_bernoulli_tree_const_1. }
    unfold twpfail; f_equal.
    ext s; unfold const.
    rewrite <- eRminus_assoc; eRauto.
  - rewrite eRplus_comm.
    rewrite <- twp__plus.
    etransitivity.
    2: { apply twpfail_bernoulli_tree_const_1. }
    unfold twpfail; f_equal.
    ext s; unfold const; eRauto.
Qed.

Corollary bernoulli_tree_twp_p_compl (p : Q) :
  Qred p = p ->
  (0 <= p <= 1)%Q ->
  twp (bernoulli_tree p) (fun b => if b then 0 else 1) = 1 - Q2eR p.
Proof.
  intros Hp Hp'.
  apply eRplus_eq_minus.
  { intro HC; inv HC. }
  rewrite <- no_fail'_twp with (fl := true).
  2: { constructor; intros []; try constructor; apply no_fail_btree_to_tree. }
  rewrite bernoulli_tree_twp_twlp.
  2: { intro; destr; eRauto. }
  rewrite twlp_twp_complement.
  2: { constructor; intro.
       - apply wf_tree_btree_to_tree.
       - destruct s; constructor. }
  2: { intro s; destr; eRauto. }
  rewrite eRplus_minus_assoc.
  2: { eRauto. }
  2: { apply twp__bounded.
       - constructor; intro.
         + apply wf_tree_btree_to_tree.
         + destruct s; constructor.
       - intro; destr; eRauto. }
  rewrite fold_twp.
  replace (fun s : bool => 1 - (if s then 0 else 1)) with
    (fun b : bool => if b then 1 else 0).
  2: { ext b; destruct b; eRauto. }
  rewrite bernoulli_tree_twp_p; auto.
  rewrite <- eRplus_minus_assoc; eRauto.
Qed.

Theorem twp_uniform_tree (n i : nat) :
  (0 < n)%nat ->
  (i < n)%nat ->
  twp (uniform_tree n) (fun n => if n =? i then 1 else 0) = 1 / INeR n.
Proof.
  intros Hn Hi.
  unfold uniform_tree.
  rewrite twp_fix_iid; eauto with tree eR.
  { unfold uniform_tree_open.
    replace (fun s : unit + nat =>
     if is_inl s
     then 0
     else
      twp (cotuple (fun _ : unit => Leaf 0%nat) (Leaf (A:=nat)) s)
        (fun n0 : nat => if n0 =? i then 1 else 0)) with
      (cotuple (@const eR unit 0) (fun n => if n =? i then 1 else 0)).
    2: { ext s; destruct s; simpl; auto. }
    rewrite twp_btree_to_tree.
    replace (fun s : unit + nat => if is_inl s then 1 else 0) with
      (@cotuple unit nat eR (const 1) (const 0)).
    2: { ext s; destruct s; auto. }
    rewrite twp_btree_to_tree.
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
  { destruct s; constructor. }
  { unfold uniform_tree_open.
    replace (fun s : unit + nat => if is_inl s then 1 else 0) with
      (@cotuple unit nat eR (const 1) (const 0)).
    2: { ext s; destruct s; auto. }
    rewrite twp_btree_to_tree.
    rewrite btree_infer_complement'.
    2: { intros []; eRauto. }
    apply eRminus_pos_lt; eRauto.
    replace (fun a : unit + nat => 1 - cotuple (const 1) (const 0) a) with
      (cotuple (@const eR unit 0) (@const eR nat 1)).
    2: { ext lr; destruct lr; eRauto. }
    apply btree_infer_const_1_uniform_btree_positive; auto. }
Qed.

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

Lemma btree_all_tree_all_btree_to_tree {A} P (t : btree A) :
  btree_all P t ->
  tree_all P (btree_to_tree t).
Proof.
  induction t; intros Hall; inv Hall; simpl; constructor; auto.
  intros []; auto.
Qed.

(* Lemma twp_bernoulli_btree_to_tree_vbool t f : *)
(*   twp_ false (uniform_btree_to_tree t) *)
(*     (fun s => match s ϵ with *)
(*               | vbool b => f b *)
(*               | _ => 0 *)
(*               end) = 0. *)
(* Proof. *)
(*   revert f; induction t; intros f; simpl. *)
(*   { destruct a as [[]|a]; simpl; auto. } *)
(*   rewrite IHt1, IHt2; eRauto. *)
(* Qed. *)

(* Lemma twp_bernoulli_btree_to_tree_vrat t f : *)
(*   twp_ false (uniform_btree_to_tree t) *)
(*     (fun s => match s ϵ with *)
(*               | vrat b => f b *)
(*               | _ => 0 *)
(*               end) = 0. *)
(* Proof. *)
(*   revert f; induction t; intros f; simpl. *)
(*   { destruct a as [[]|a]; simpl; auto. } *)
(*   rewrite IHt1, IHt2; eRauto. *)
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

(** Don't need wlp version because [uniform_tree_twp_twlp]. *)
Lemma twp_uniform_tree_sum (n : nat) (f : nat -> eR) :
  (0 < n)%nat ->
  twp (uniform_tree n) f = sum (map (fun i => f i / INeR n) (range n)).
Proof.
  intro Hn.  
  replace f with
    (fun k => sum (map (fun i => if Nat.eqb k i then f k else 0) (range n)) +
             if n <=? k then f k else 0).
  2: { clear Hn; ext k.
       destruct (Nat.leb_spec0 n k).
       - rewrite sum_eq_0; eRauto.
         apply Forall_forall.
         intros x Hx.
         apply in_map_iff in Hx.
         destruct Hx as [i [Hx Hin]].
         apply in_range in Hin.
         destruct (Nat.eqb_spec k i); subst; try lia; auto.
       - rewrite eRplus_0_r.
         apply not_le in n0.
         apply Nat.le_succ_l in n0.
         induction n; simpl.
         { lia. }
         rewrite map_app, sum_app; simpl; rewrite eRplus_0_r.
         destruct (Nat.eqb_spec k n); subst.
         * rewrite sum_eq_0; eRauto.
           apply Forall_forall; intros x Hx.
           apply in_map_iff in Hx; destruct Hx as [i [Hx Hin]].
           apply in_range in Hin.
           destruct (Nat.eqb_spec n i); subst; auto; lia.
         * rewrite eRplus_0_r; apply IHn; lia. }
  unfold twp.
  rewrite twp__plus.
  replace (fun s => sum (map (fun i => if s =? i then f s else 0) (range n))) with
    (fun s => sum (map (fun f => f s)
                  (map (fun i s => if s =? i then f s else 0) (range n)))).
  2: { ext s; rewrite map_map; reflexivity. }
  rewrite twp_sum.
  replace (twp_ false (uniform_tree n)
             (fun s => if n <=? s then f s else 0)) with 0.
  2: { unfold uniform_tree.
       rewrite fold_twp.
       rewrite twp_fix_iid; auto.
       -
         replace (fun s : unit + nat =>
                    if is_inl s
                    then 0
                    else
                      twp (cotuple (fun _ : unit => Leaf 0%nat) (Leaf (A:=nat)) s)
                        (fun s0 : nat => if n <=? s0 then f s0 else 0)) with
           (cotuple (@const eR unit 0) (fun s => if n <=? s then f s else 0)).
         2: { ext s; destruct s; auto. }
         rewrite tree_all_twp_0; eRauto.
         + apply simple_btree_to_tree.
         + unfold uniform_tree_open. simpl.
           unfold uniform_btree.
           set (P := fun m => (m < n)%nat).
           apply tree_all_impl with
             (P := fun s : unit + nat => match s with
                                    | inl _ => True
                                    | inr n => P n
                                    end).
           { intros [] Hs; simpl; auto.
             unfold P in Hs.
             apply leb_correct_conv in Hs; rewrite Hs; auto. }
           apply btree_all_tree_all_btree_to_tree.
           unfold P.
           apply reduce_btree_all.
           apply Forall_btree_all_list_btree_aux.
           apply Forall_forall; intros x Hx.
           apply in_rev_range_lt in Hx; auto.
       - apply wf_tree_btree_to_tree.
       - intros []; constructor.
       - apply twp_uniform_tree_open_lt_1; auto. }
  rewrite eRplus_0_r.
  f_equal.
  rewrite map_map.
  apply map_ext_in.
  intros i Hi.
  replace (fun s : nat => if s =? i then f s else 0) with
    (fun s : nat => f i * if s =? i then 1 else 0).
  2: { ext s; destruct (Nat.eqb_spec s i); eRauto. }
    replace (fun i0 : nat => if i =? i0 then f i else 0) with
    (fun s : nat => f i * if i =? s then 1 else 0).
  2: { ext s; destruct (Nat.eqb_spec i s); eRauto. }
  rewrite twp_scalar.
  rewrite twp_uniform_tree; auto.
  - unfold eRdiv.
    rewrite eRmult_1_l.
    f_equal.
    rewrite sum_map_scalar.
    apply in_range in Hi.
    destruct (Nat.leb_spec n i); try lia; eRauto.
    rewrite sum_map_count.
    rewrite countb_list_range_lt; auto.
    rewrite INeR_1; eRauto.
  - apply in_range in Hi; auto.
Qed.
