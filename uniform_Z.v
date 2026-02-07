(** * Uniform and Bernoulli CF trees using Z instead of nat. *)

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
  ZArith
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

Lemma twp_btree_to_tree {A} (f : A -> eR) (t : btree A) :
  twp (btree_to_tree t) f = btree_infer f t.
Proof.
  unfold twp; revert f; induction t; intro f; simpl; auto.
  rewrite IHt1, IHt2; f_equal; f_equal.
  rewrite Q2eR_one_half, eRminus_1_2; reflexivity.
Qed.

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
#[export] Hint Resolve wf_tree_btree_to_tree : tree.
#[export] Hint Resolve wf_tree'_btree_to_tree : tree.
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

Lemma reduce_btree_infer {A} (f : unit + A -> eR) (t : btree (unit + A)) :
  btree_infer f (reduce_btree t) = btree_infer f t.
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
          rewrite eRmult_div_cancel; eRauto. }
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

Fixpoint rev_range_positive (p : positive) : list Z :=
  match p with
  | xH => [Z0]
  | xO p' => List.map (Z.add (Zpos p')) (rev_range_positive p') ++ rev_range_positive p'
  | xI p' => Zpos (2 * p')%positive ::
              List.map (Z.add (Zpos p')) (rev_range_positive p') ++ rev_range_positive p'
  end.

Definition rev_range_Z (n : Z) : list Z :=
  match n with
  | Zpos p => rev_range_positive p
  | _ => []
  end.

Lemma length_rev_range_positive (p : positive) :
  length (rev_range_positive p) = Pos.to_nat p.
Proof.
  induction p; simpl; auto; rewrite length_app, length_map, IHp; lia.
Qed.

Lemma length_rev_range_Z (n : Z) :
  length (rev_range_Z n) = Z.to_nat n.
Proof.
  destruct n; simpl; auto; apply length_rev_range_positive.
Qed.

(* Definition uniform_btree (n : Z) : btree (unit + Z) := *)
(*   btree_map (sum_map id Z.of_nat) *)
(*     (reduce_btree (list_btree (rev_range (Z.to_nat n)))). *)

(** It turns out that Z.of_nat is very slow so the following
    implementation builds much more quickly than the above. *)
Definition uniform_btree (n : Z) : btree (unit + Z) :=
  reduce_btree (list_btree (rev_range_Z n)).

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
    + rewrite <- length_app, take_drop_spec; reflexivity.
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
      rewrite <- length_app, take_drop_spec; reflexivity.
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

Definition bernoulli_btree (n d : Z) : btree (unit + bool) :=
  reduce_btree' (btree_map (sum_map (fun x => x) (fun i => Z.ltb i n))
                   (uniform_btree d)).

(* Eval compute in (bernoulli_btree 1 3). *)

Definition bernoulli_tree_open (n d : Z) : tree (unit + bool) :=
  btree_to_tree (bernoulli_btree n d).

Definition bernoulli_tree (p : Q) : tree bool :=
  let t := bernoulli_tree_open (Qnum p) (Zpos (Qden p)) in
  Fix (inl tt) is_inl (fun _ => t) (cotuple (fun _ => Leaf false) (@Leaf _)).

(** TODO: could omit Fix node when n is a power of 2 (to enable more
    aggressive optimizations since Fix nodes complicate things). *)
Definition uniform_tree_open (n : Z) : tree (unit + Z) :=
  btree_to_tree (uniform_btree n).

Definition uniform_tree (n : Z) : tree Z :=
  let t := uniform_tree_open n in
  Fix (inl tt) is_inl (fun _ => t) (cotuple (fun _ => Leaf Z0) (@Leaf _)).

Lemma btree_infer_fmap_bool {A} (f : A -> bool) (g : bool -> eR) (t : btree (unit + A)) :
  btree_infer (cotuple (const 0) g) (btree_map (sum_map (fun x => x) f) t) =
    btree_infer (cotuple (const 0) (g ∘ f)) t.
Proof.
  revert f; induction t; intro f; simpl; try lra.
  - destruct a; auto.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma congruent_btree_map {A B} (f : A -> B) (t1 t2 : btree A) :
  congruent t1 t2 ->
  congruent (btree_map f t1) (btree_map f t2).
Proof. induction 1; simpl; constructor; auto. Qed.

Lemma perfect_btree_map {A B} (f : A -> B) (t : btree A) :
  perfect t ->
  perfect (btree_map f t).
Proof.
  induction t; intro Ht; simpl; inv Ht; constructor; auto.
  apply congruent_btree_map; auto.
Qed.

Lemma btree_infer_btree_map {A B} (t : btree A) (f : A -> B) (g : B -> eR) :
  btree_infer g (btree_map f t) = btree_infer (g ∘ f) t.
Proof. induction t; simpl; auto; rewrite IHt1, IHt2; auto. Qed.

Lemma countb_list_all_false {A} (P : A -> bool) (l : list A) :
  Forall (is_true ∘ negb ∘ P) l ->
  countb_list P l = O.
Proof.
  induction l; simpl; unfold compose; intro Hall; auto; inv Hall.
  destr; simpl in *; try congruence; auto.
Qed.

Lemma countb_list_all_true {A} (P : A -> bool) (l : list A) :
  Forall (is_true ∘ P) l ->
  countb_list P l = length l.
Proof.
  induction l; simpl; unfold compose; intro Hall; auto; inv Hall.
  destr; simpl in *; try congruence; auto.
Qed.

Lemma forall_lt_rev_range_positive (p : positive) :
  Forall (fun x => Z.lt x (Zpos p)) (rev_range_positive p).
Proof.
  unfold compose; induction p; simpl.
  - constructor; try lia.
    apply Forall_app; split.
    + apply Forall_map; eapply Forall_impl; eauto.
      intros a Ha; simpl in Ha; lia.
    + eapply Forall_impl; eauto.
      intros a Ha; simpl in Ha; lia.
  - apply Forall_app; split.
    + apply Forall_map; eapply Forall_impl; eauto.
      intros a Ha; simpl in Ha; lia.
    + eapply Forall_impl; eauto.
      intros a Ha; simpl in Ha; lia.
  - constructor; try lia; constructor.
Qed.

Lemma Forall_impl' {A} (P Q : A -> Prop) (l : list A) :
  (forall a, In a l -> P a -> Q a) ->
  Forall P l ->
  Forall Q l.
Proof.
  induction l; intros HPQ HP; inv HP; constructor; firstorder.
Qed.

Lemma rev_range_add (n m : nat) :
  rev_range (n + m) = map (Nat.add m) (rev_range n) ++ rev_range m.
Proof.
  revert m; induction n; intro m; simpl; auto.
  rewrite Nat.add_comm; f_equal.
  rewrite <- IHn, Nat.add_comm; auto.
Qed.  

Lemma rev_range_positive_rev_range (p : positive) :
  rev_range_positive p = map Z.of_nat (rev_range (Pos.to_nat p)).
Proof.
  induction p; simpl; auto.
  - rewrite IHp.
    f_equal.
    + rewrite <- positive_nat_Z; auto.
    + rewrite <- IHp.
      rewrite Pmult_nat_mult.
      replace (Pos.to_nat p * 2)%nat with (Pos.to_nat p + Pos.to_nat p)%nat by lia.
      rewrite rev_range_add, map_app, <- IHp.
      f_equal; rewrite IHp, 2!map_map.
      f_equal; ext i; lia.
  - unfold Pos.to_nat; simpl.
    rewrite Pmult_nat_mult.
    replace (Pos.to_nat p * 2)%nat with (Pos.to_nat p + Pos.to_nat p)%nat by lia.
    rewrite rev_range_add, map_app, <- IHp.
    f_equal; rewrite IHp, 2!map_map.
    f_equal; ext i; lia.
Qed.

Lemma rev_range_Z_rev_range (z : Z) :
  rev_range_Z z = map Z.of_nat (rev_range (Z.to_nat z)).
Proof.
  destruct z; simpl; auto; apply rev_range_positive_rev_range.
Qed.

Lemma in_rev_range_positive_nonnegative (n : Z) (p : positive) :
  In n (rev_range_positive p) ->
  (0 <= n)%Z.
Proof.
  revert n; induction p; simpl; intros n Hin.
  - destruct Hin as [Heq | Hin]; subst; try lia.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply in_map_iff in Hin.
      destruct Hin as [x [Heq Hin]]; subst.
      apply IHp in Hin; lia.
    + apply IHp; auto.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply in_map_iff in Hin.
      destruct Hin as [x [Heq Hin]]; subst.
      apply IHp in Hin; lia.
    + apply IHp; auto.
  - lia.
Qed.

Lemma countb_list_rev_range_positive n p :
  (0 <= n < Z.pos p)%Z ->
  countb_list (Z.eqb n) (rev_range_positive p) = 1%nat.
Proof.
  revert n; induction p; intros n Hnp; simpl.
  - rewrite countb_list_app.
    destruct (Z.eqb_spec n (Zpos p~0)); subst; simpl.
    + rewrite 2!countb_list_all_false; try lia.
      * eapply Forall_impl.
        2: { apply forall_lt_rev_range_positive. }
        intros a Ha; simpl in Ha; unfold compose.
        destruct (Z.eqb_spec (Zpos p~0) a); subst; try lia.
        constructor.
      * apply Forall_map.
        eapply Forall_impl.
        2: { apply forall_lt_rev_range_positive. }
        intros a Ha; simpl in Ha; unfold compose.
        destruct (Z.eqb_spec (Zpos p~0) (Z.pos p + a)); subst; try lia.
        constructor.
    + destruct (Z.ltb_spec n (Z.pos p)).
      * rewrite countb_list_all_false; simpl.
        2: { apply Forall_map.
             eapply Forall_impl'.
             2: { apply forall_lt_rev_range_positive. }
             unfold compose.
             intros a Hin lt.
             destruct (Z.eqb_spec n (Z.pos p + a)); subst; simpl; auto.
             apply in_rev_range_positive_nonnegative in Hin; lia. }
        apply IHp; lia.
      * rewrite Nat.add_comm.
        rewrite countb_list_all_false; simpl.
        2: { eapply Forall_impl'.
             2: { apply forall_lt_rev_range_positive. }
             unfold compose.
             intros a Hin lt.
             destruct (Z.eqb_spec n a); subst; simpl; auto; lia. }
        rewrite countb_list_map.
        replace (Z.eqb n ∘ Z.add (Z.pos p)) with (Z.eqb (n - Z.pos p)).
        2: { ext i; unfold compose; lia. }
        apply IHp; lia.
  - rewrite countb_list_app.
    destruct (Z.ltb_spec n (Z.pos p)).
    * rewrite countb_list_all_false; simpl.
      2: { apply Forall_map.
           eapply Forall_impl'.
           2: { apply forall_lt_rev_range_positive. }
           unfold compose.
           intros a Hin lt.
           destruct (Z.eqb_spec n (Z.pos p + a)); subst; simpl; auto.
           apply in_rev_range_positive_nonnegative in Hin; lia. }
      apply IHp; lia.
    * rewrite Nat.add_comm.
      rewrite countb_list_all_false; simpl.
      2: { eapply Forall_impl'.
           2: { apply forall_lt_rev_range_positive. }
           unfold compose.
           intros a Hin lt.
           destruct (Z.eqb_spec n a); subst; simpl; auto; lia. }
      rewrite countb_list_map.
      replace (Z.eqb n ∘ Z.add (Z.pos p)) with (Z.eqb (n - Z.pos p)).
      2: { ext i; unfold compose; lia. }
      apply IHp; lia.
  - destruct (Z.eqb_spec n 0); subst; lia.
Qed.

Lemma countb_list_rev_range_Z n d :
  (0 <= n < d)%Z ->
  countb_list (eqb n) (rev_range_Z d) = S O.
Proof.
  intro Hnd; destruct d; simpl; try lia.
  apply countb_list_rev_range_positive; auto.
Qed.

Lemma ltb_N_nat i n :
  (i <? Z.to_nat n) = (Z.of_nat i <? n)%Z.
Proof. destruct (Nat.ltb_spec i (Z.to_nat n)); lia. Qed.

Lemma countb_list_rev_range_Z_lt n d :
  (n <= d)%Z ->
  countb_list (fun i : Z => Z.ltb i n) (rev_range_Z d) = Z.to_nat n.
Proof.
  intro Hle.
  rewrite rev_range_Z_rev_range.
  rewrite countb_list_map.
  unfold compose.
  replace (fun x : nat => (Z.of_nat x <? n)%Z) with (fun x => x <? Z.to_nat n).
  2: { ext i; apply ltb_N_nat. }
  apply countb_list_rev_range_lt; lia.
Qed.

Lemma btree_infer_uniform_btree n i :
  (0 <= i < n)%Z ->
  btree_infer (cotuple (fun _ : unit => 0) (fun x : Z => if Z.eqb x i then 1 else 0))
    (uniform_btree n) = 1 / INeR (next_pow_2 (Z.to_nat n)).
Proof.
  intro Hlt.
  unfold uniform_btree.
  (* rewrite btree_infer_btree_map. *)
  rewrite reduce_btree_infer.
  replace (cotuple (fun _ => 0) (fun x => if Z.eqb x i then 1 else 0)) with
    (fun x : unit + Z => if (match x with
                          | inl _ => false
                          | inr j => Z.eqb j i
                          end) then 1 else 0).
  2: { ext lr; destruct lr; auto. }
  rewrite perfect_btree_infer.
  2: { apply perfect_list_btree. }
  replace (fun x : unit + Z => match x with
                            | inl _ => false
                            | inr x => Z.eqb x i
                            end) with
    (cotuple (fun _ : unit => false) (Z.eqb i)).
  2: { ext x; destruct x; auto; simpl; rewrite Z.eqb_sym; reflexivity. }
  rewrite list_btree_count.
  rewrite <- countb_partition with (P := cotuple (const false) (const true)).
  rewrite list_btree_count.
  rewrite countb_list_const_true.
  replace (fun s : unit + Z => negb (cotuple (const false) (const true) s)) with
    (cotuple (fun _ : unit => true) (fun _ : Z => false)).
  2: { ext x; destruct x; auto. }
  unfold list_btree.
  rewrite list_btree_aux_countb'.
  - rewrite length_rev_range_Z.
    generalize (is_power_of_2_next_pow_2 (Z.to_nat n)).
    unfold is_power_of_2.
    intros [k H]; rewrite <- H.
    rewrite Nat.log2_pow2; try lia.
    rewrite Nat.add_comm, Nat.sub_add.
    2: { rewrite H; apply next_pow_2_ub. }
    (* rewrite <- rev_range_spec. *)
    (* replace (Z.eqb i ∘ Z.of_nat) with (Nat.eqb (Z.to_nat i)). *)
    (* 2: { ext j; unfold compose. *)
    (*      destruct (Z.eqb_spec i (Z.of_nat j)); subst. *)
    (*      - rewrite Nat2Z.id; apply Nat.eqb_refl. *)
    (*      - destruct (Nat.eqb_spec (Z.to_nat i) j); subst; lia. } *)
    rewrite countb_list_rev_range_Z; try lia.
    f_equal; apply INeR_1.
  - rewrite length_rev_range_Z.
    generalize (is_power_of_2_next_pow_2 (Z.to_nat n)).
    unfold is_power_of_2.
    intros [k H].
    rewrite <- H.
    rewrite Nat.log2_pow2; try lia.
    rewrite H.
    apply next_pow_2_ub.
  Qed.

Lemma INeR_IZeR (n : Z) :
  INeR (Z.to_nat n) = IZeR n.
Proof.
  apply eR_eq.
  destruct n; simpl; auto.
  rewrite Zmax_right; try lia.
  rewrite INR_IZR_INZ; f_equal; lia.
Qed.

Lemma btree_infer_uniform_btree_lt n d :
  (0 <= n <= d)%Z ->
  btree_infer (cotuple (fun _ : unit => 0) (fun x : Z => if Z.ltb x n then 1 else 0))
    (uniform_btree d) = IZeR n / INeR (next_pow_2 (Z.to_nat d)).
Proof.
  intro Hle.
  unfold uniform_btree.
  replace (cotuple (fun _ => 0) (fun i => if Z.ltb i n then 1 else 0)) with
    (fun x : unit + Z => if (match x with
                          | inl _ => false
                          | inr i => Z.ltb i n
                          end) then 1 else 0).
  2: { ext x; destruct x; auto. }
  rewrite reduce_btree_infer.
  rewrite perfect_btree_infer.
  - replace (fun x : unit + Z => match x with
                              | inl _ => false
                              | inr i => Z.ltb i n
                              end) with
      (cotuple (fun _ : unit => false) (fun i => Z.ltb i n)).
    2: { ext x; destruct x; auto. }
    rewrite list_btree_count.
    rewrite <- countb_partition with (P := cotuple (const false) (const true)).
    rewrite list_btree_count.
    rewrite countb_list_const_true.
    replace (fun s : unit + Z => negb (cotuple (const false) (const true) s)) with
      (cotuple (fun _ : unit => true) (fun _ : Z => false)).
    2: { ext x; destruct x; auto. }
    unfold list_btree.
    rewrite list_btree_aux_countb'.
    + rewrite length_rev_range_Z.
      generalize (is_power_of_2_next_pow_2 (Z.to_nat d)).
      unfold is_power_of_2.
      intros [k H].
      rewrite <- H.
      rewrite Nat.log2_pow2; try lia.
      rewrite Nat.add_comm, Nat.sub_add.
      2:{ rewrite H; apply next_pow_2_ub. }
      rewrite countb_list_rev_range_Z_lt; try lia.
      rewrite H, INeR_IZeR; auto.
    + rewrite length_rev_range_Z.
      generalize (is_power_of_2_next_pow_2 (Z.to_nat d)).
      unfold is_power_of_2.
      intros [k H].
      rewrite <- H.
      rewrite Nat.log2_pow2; try lia.
      rewrite H.
      apply next_pow_2_ub.
  - apply perfect_list_btree.
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
    IZeR n / INeR (next_pow_2 (Z.to_nat n)).
Proof.
  unfold uniform_btree.
  rewrite reduce_btree_infer.
  rewrite btree_infer_list_btree_const_1.
  rewrite length_rev_range_Z, INeR_IZeR; reflexivity.
Qed.

Lemma btree_infer_bernoulli_btree_n n d :
  (0 <= n <= d)%Z ->
  btree_infer (cotuple (const 0) (fun b : bool => if b then 1 else 0))
    (bernoulli_btree n d) = IZeR n / INeR (next_pow_2 (Z.to_nat d)).
Proof.
  unfold bernoulli_btree.
  intro Hnd.
  rewrite reduce_btree'_infer.
  rewrite btree_infer_fmap_bool.
  unfold compose, const.
  apply btree_infer_uniform_btree_lt; auto.
Qed.

Lemma btree_infer_uniform_btree_n n i :
  (0 <= i < n)%Z ->
  btree_infer (cotuple (const 0) (fun x : Z => if eqb x i then 1 else 0))
    (uniform_btree n) = INeR 1 / INeR (next_pow_2 (Z.to_nat n)).
Proof.
  unfold uniform_btree, compose, const; rewrite INeR_1.
  apply btree_infer_uniform_btree.
Qed.

Lemma btree_infer_bernoulli_btree_const_1 n d :
  btree_infer (cotuple (const 0) (const 1)) (bernoulli_btree n d) =
    IZeR d / INeR (next_pow_2 (Z.to_nat d)).
Proof.
  unfold bernoulli_btree.
  rewrite reduce_btree'_infer.
  rewrite btree_infer_fmap_bool.
  apply btree_infer_uniform_btree_const_1.
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
  (0 < d)%Z ->
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
  apply IZeR_positive; auto.
Qed.

Lemma btree_infer_const_1_uniform_btree_positive n :
  (0 < n)%Z ->
  0 < btree_infer (cotuple (const 0) (const 1)) (uniform_btree n).
Proof.
  intro Hlt.
  unfold compose.
  unfold const.
  rewrite btree_infer_uniform_btree_const_1.
  apply eRlt_0_eRdiv; eRauto.
  apply IZeR_positive; auto.
Qed.

Corollary btree_infer_bernoulli_btree_lt_1 n d :
  (0 < d)%Z ->
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
  (0 < n)%Z ->
  btree_infer (cotuple (const 1) (const 0)) (uniform_btree n) < 1.
Proof.
  intro Hd.
  rewrite btree_infer_complement'.
  2: { intros []; eRauto. }
  apply eRminus_pos_lt; eRauto.
  replace (fun a : unit + Z => 1 - cotuple (const 1) (const 0) a) with
    (cotuple (@const eR unit 0) (@const eR Z 1)).
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
    2: { split.
         - apply Qnum_nonnegative; auto.
         - generalize (Q_num_le_den Hp0); lia. }
    replace (cotuple (const 1) (const 0)) with
      (fun s : unit + bool => 1 - cotuple (const 0) (const 1) s).
    2: { ext lr; destruct lr; eRauto. }
    rewrite <- btree_infer_complement'.
    2: { intros []; eRauto. }
    rewrite btree_infer_bernoulli_btree_const_1.
    rewrite eRdiv_cancel_r.
    - rewrite <- 2!INeR_IZeR.
      apply INeR_Qnum_Qden_Q2R; auto.
    - rewrite <- INeR_IZeR; apply not_0_INeR.
      generalize (Pos2Nat.is_pos (Qden p)); lia.
    - apply not_0_INeR; rewrite Z2Nat.inj_pos.
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
    lia. }
Qed.

Lemma twp_bernoulli_tree_open_lt_1 n d :
  (0 < d)%Z ->
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
  (0 < n)%Z ->
  twp (uniform_tree_open n)
    (fun s : unit + Z => if is_inl s then 1 else 0) < 1.
Proof.
  intro Hd.
  replace (fun s : unit + Z => if is_inl s then 1 else 0) with
    (fun s => @cotuple unit Z eR (const 1) (const 0) s +
             cotuple (const 0) (const 0) s).
  2: { ext s; destruct s; simpl; unfold const; eRauto. }
  unfold uniform_tree_open.
  rewrite twp_plus.
  replace (cotuple (const 0) (const 0)) with (@const eR (unit + Z) 0).
  2: { ext s; destruct s; unfold const; auto. }
  unfold twp.
  rewrite twp_strict; eRauto.
  rewrite fold_twp.
  rewrite twp_btree_to_tree.
  apply btree_infer_uniform_btree_lt_1; auto.
Qed.

Lemma twpfail_uniform_tree_const_1 n :
  (0 < n)%Z ->
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
        apply eRlt_neq, twp_bernoulli_tree_open_lt_1; lia.
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
  { apply twp_bernoulli_tree_open_lt_1; lia. }
  { reflexivity. }
Qed.

Lemma uniform_tree_twp_twlp fl n f :
  (0 < n)%Z ->
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

Theorem twp_uniform_tree (n i : Z) :
  (0 < n)%Z ->
  (0 <= i < n)%Z ->
  twp (uniform_tree n) (fun n => if eqb n i then 1 else 0) = 1 / IZeR n.
Proof.
  intros Hn Hi.  unfold uniform_tree.
  rewrite twp_fix_iid; eauto with tree eR.
  { unfold uniform_tree_open.
    replace (fun s : unit + Z =>
     if is_inl s
     then 0
     else
      twp (cotuple (fun _ : unit => Leaf 0%Z) (Leaf (A:=Z)) s)
        (fun n0 : Z => if eqb n0 i then 1 else 0)) with
      (cotuple (@const eR unit 0) (fun n => if eqb n i then 1 else 0)).
    2: { ext s; destruct s; simpl; auto. }
    rewrite twp_btree_to_tree.
    replace (fun s : unit + Z => if is_inl s then 1 else 0) with
      (@cotuple unit Z eR (const 1) (const 0)).
    2: { ext s; destruct s; auto. }
    rewrite twp_btree_to_tree.
    rewrite btree_infer_uniform_btree_n; auto.
    replace (cotuple (const 1) (const 0)) with
      (fun s : unit + Z => 1 - cotuple (const 0) (const 1) s).
    2: { ext lr; destruct lr; eRauto. }
    rewrite <- btree_infer_complement'.
    2: { intros []; eRauto. }
    rewrite btree_infer_uniform_btree_const_1.
    rewrite eRdiv_cancel_r.
    - rewrite INeR_1; reflexivity.
    - rewrite <- INeR_IZeR; apply not_0_INeR; lia.
    - apply not_0_INeR; generalize (next_pow_2_positive (Z.to_nat n)); lia.
    - apply not_infty_INeR. }
  { destruct s; constructor. }
  { unfold uniform_tree_open.
    replace (fun s : unit + Z => if is_inl s then 1 else 0) with
      (@cotuple unit Z eR (const 1) (const 0)).
    2: { ext s; destruct s; auto. }
    rewrite twp_btree_to_tree.
    rewrite btree_infer_complement'.
    2: { intros []; eRauto. }
    apply eRminus_pos_lt; eRauto.
    replace (fun a : unit + Z => 1 - cotuple (const 1) (const 0) a) with
      (cotuple (@const eR unit 0) (@const eR Z 1)).
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

Lemma btree_some_reduce_btree' {A} `{EqType A} P (t : btree A) :
  btree_some P t ->
  btree_some P (reduce_btree' t).
Proof.
  induction t; intro Ht; simpl; auto; inv Ht.
  - destruct (reduce_btree' t1) eqn:Ht1.
    + destruct (reduce_btree' t2) eqn:Ht2.
      * destr; auto; constructor; auto.
      * constructor; auto.
    + constructor; auto.
  - destruct (reduce_btree' t1) eqn:Ht1.
    + destruct (reduce_btree' t2) eqn:Ht2.
      * destruct (eqb_spec a a0); subst; auto.
        apply btree_some_node_r; auto.
      * apply btree_some_node_r; auto.
    + apply btree_some_node_r; auto.
Qed.

Lemma btree_some_btree_map {A B} (P : B -> Prop) (f : A -> B) (t : btree A) :
  btree_some (P ∘ f) t ->
  btree_some P (btree_map f t).
Proof.
  induction t; intro Hsome; simpl; inv Hsome; solve [constructor; auto].
Qed.

Lemma btree_some_is_inr_list_btree_aux {A} (l : list A) (n : nat) :
  l <> nil ->
  btree_some (fun x : unit + A => is_true (is_inr x)) (list_btree_aux l n).
Proof.
  revert l; induction n; intros l Hl; simpl; destruct l; try congruence.
  - constructor; auto.
  - constructor.
    apply IHn.
    apply take_not_nil; auto.
    apply pow_positive; lia.
Qed.

Lemma btree_some_is_inr_list_btree {A} (l : list A) :
  l <> nil ->
  btree_some (fun x : unit + A => is_true (is_inr x)) (list_btree l).
Proof. apply btree_some_is_inr_list_btree_aux; auto. Qed.

Lemma countb_btree_map {A B} (f : B -> bool) (g : A -> B) (t : btree A) :
  countb f (btree_map g t) = countb (f ∘ g) t.
Proof. unfold compose; induction t; simpl; auto. Qed.

Lemma countb_true_list_btree_aux_pow_2 {A} (l : list A) (k : nat) :
  countb (const true) (list_btree_aux l k) = (2 ^ k)%nat.
Proof.
  revert l; induction k; intro l; simpl.
  { destruct l; auto. }
  rewrite 2!IHk; lia.
Qed.

Lemma countb_length_list_btree {A} (l : list A) :
  countb (const true) (list_btree l) = next_pow_2 (length l).
Proof.
  unfold list_btree.
  simpl.
  generalize (is_power_of_2_next_pow_2 (length l)).
  intros [k Hk].
  rewrite <- Hk.
  rewrite Nat.log2_pow2; try lia.
  apply countb_true_list_btree_aux_pow_2.
Qed.

Lemma countb_list_btree_aux_le_pow_2 {A} P (l : list A) n :
  (countb P (list_btree_aux l n) <= 2^n)%nat.
Proof.
  revert l; induction n; intro l; simpl.
  - destruct l; simpl; destr; lia.
  - rewrite Nat.add_0_r.
    pose proof (IHn (take (2^n) l)).
    specialize (IHn (drop (2^n) l)); lia.
Qed.

Lemma no_fail_uniform_tree (n : Z) :
  no_fail' (uniform_tree n).
Proof.
  constructor.
  - intros; apply no_fail_btree_to_tree.
  - intros []; constructor.
Qed.

Lemma no_fail_bernoulli_tree (p : Q) :
  no_fail' (bernoulli_tree p).
Proof.
  constructor.
  - intros; apply no_fail_btree_to_tree.
  - intros []; constructor.
Qed.

Lemma wf_tree_uniform_tree (n : Z) :
  wf_tree (uniform_tree n).
Proof.
  constructor.
  - intros; apply wf_tree_btree_to_tree.
  - intros []; constructor.
Qed.

Lemma wf_tree_bernoulli_tree (p : Q) :
  wf_tree (bernoulli_tree p).
Proof.
  constructor.
  - intros; apply wf_tree_btree_to_tree.
  - intros []; constructor.
Qed.

Lemma twlp_const_1_uniform_tree (n : Z) :
  twlp (uniform_tree n) (const 1) = 1.
Proof.
  rewrite twlp_fail.
  { rewrite no_fail_twlp; eRauto.
    apply no_fail_uniform_tree. }
  apply wf_tree_uniform_tree.
Qed.

Lemma twlp_const_1_bernoulli_tree (p : Q) :
  twlp (bernoulli_tree p) (const 1) = 1.
Proof.
  rewrite twlp_fail.
  { rewrite no_fail_twlp; eRauto.
    apply no_fail_bernoulli_tree. }
  apply wf_tree_bernoulli_tree.
Qed.

Lemma tree_unbiased_uniform_tree (n : Z) :
  tree_unbiased (uniform_tree n).
Proof.
  constructor.
  - intros; apply tree_unbiased_btree_to_tree.
  - intros []; constructor.
Qed.

Lemma tree_unbiased_bernoulli_tree (p : Q) :
  tree_unbiased (bernoulli_tree p).
Proof.
  constructor.
  - intros; apply tree_unbiased_btree_to_tree.
  - intros []; constructor.
Qed.
