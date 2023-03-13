(** * Samplers for finite distributions. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Streams Basics QArith String Lia Lqa List Reals.
Local Open Scope program_scope.
Local Open Scope string_scope.
Import ListNotations.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From zar Require Import
  cotree cocwp cpo equidistribution eR itree misc order pow_2 prelude R
  tactics tcwp tcwp_facts tcwp_geometric tree uniform.

Fixpoint bin_index (weights : list nat) (i : nat) : nat :=
  match weights with
  | [] => O
  | w :: ws => if Nat.ltb i w then O else S (bin_index ws (i - w))
  end.

Definition findist_btree (weights : list nat) : btree (unit + nat) :=
  reduce_btree' (btree_map (sum_map id (bin_index weights))
                   (uniform_btree' (list_sum weights))).

(* Eval compute in (findist_btree [1%nat; 2%nat]). *)

Definition findist_tree_open (weights : list nat) : tree (unit + nat) :=
  btree_to_tree (findist_btree weights).

Definition findist_tree (weights : list nat) : tree nat :=
  let t := findist_tree_open weights in
  Fix (inl tt) is_inl (fun _ => t) (cotuple (fun _ => Leaf O) (@Leaf _)).

Lemma wf_tree_findist_tree (weights : list nat) :
  wf_tree (findist_tree weights).
Proof.
  constructor.
  - intros ?; apply wf_tree_btree_to_tree.
  - intros []; constructor.
Qed.

Lemma no_fail_findist_tree (weights : list nat) :
  no_fail' (findist_tree weights).
Proof.
  constructor.
  - intros ?; apply no_fail_btree_to_tree.
  - intros []; constructor.
Qed.

(* Lemma twlp_findist_tree_positive (weights : list nat) : *)
(*   0 < twlp (findist_tree weights) (const 1). *)
(* Proof. *)
(*   rewrite twlp_fail. *)
(*   2: { apply wf_tree_findist_tree. } *)
(*   rewrite no_fail_twlp; eRauto. *)
(*   apply no_fail_findist_tree. *)
(* Qed. *)

Lemma twlp_const_1_findist_tree (weights : list nat) :
  twlp (findist_tree weights) (const 1) = 1.
Proof.
  rewrite twlp_fail.
  { rewrite no_fail_twlp; eRauto.
    apply no_fail_findist_tree. }
  apply wf_tree_findist_tree.
Qed.

Definition findist_itree (weights : list nat) : itree boolE nat :=
  to_itree (findist_tree weights).

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

Lemma is_inr_sum_map {A B C D} (x : A + B) (f : A -> C) (g : B -> D) :
  is_inr x = is_inr (sum_map f g x).
Proof. destruct x; auto. Qed.

Lemma take_not_nil {A} (l : list A) (n : nat) :
  l <> nil ->
  (0 < n)%nat ->
  ~ take n l = [].
Proof.
  revert l; induction n; intros l Hl Hn; simpl; try lia.
  destruct l; congruence.
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

Lemma rev_range_not_nil (n : nat) :
  (0 < n)%nat ->
  rev_range n <> [].
Proof.
  induction n; simpl; intros Hlt HC; auto; try lia; congruence.
Qed.

Lemma exists_pos_list_sum l :
  Exists (fun w : nat => (0 < w)%nat) l ->
  (0 < list_sum l)%nat.
Proof.
  induction l; intro Hex; inv Hex; simpl; try lia.
  apply Nat.lt_lt_add_l; auto.
Qed.

Lemma btree_some_inr_findist_btree (weights : list nat) :
  Exists (fun w : nat => (0 < w)%nat) weights ->
  btree_some (is_true ∘ is_inr) (findist_btree weights).
Proof.
  intro Hex.
  apply btree_some_reduce_btree'.
  apply btree_some_btree_map.
  unfold compose.
  unfold uniform_btree'.
  replace (fun x => is_true (is_inr (sum_map id (bin_index weights) x))) with
    (fun x : unit + nat => is_true (is_inr x)).
  2: { ext x; destruct x; auto. }
  apply btree_some_is_inr_list_btree.
  apply rev_range_not_nil.
  apply exists_pos_list_sum; auto.
Qed.

Definition proj_inr {A B} (x : A + B) (default : B) : B :=
  match x with
  | inl _ => default
  | inr b => b
  end.

Lemma congruence_btree_map {A B} (f : A -> B) (t1 t2 : btree A) :
  congruent t1 t2 ->
  congruent (btree_map f t1) (btree_map f t2).
Proof. induction 1; simpl; constructor; auto. Qed.

Lemma perfect_btree_map {A B} (f : A -> B) (t : btree A) :
  perfect t ->
  perfect (btree_map f t).
Proof.
  induction t; intro Ht; simpl; inv Ht; constructor; auto.
  apply congruence_btree_map; auto.
Qed.

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

Lemma countb_list_rev {A} (f : A -> bool) (l : list A) :
  countb_list f (rev l) = countb_list f l.
Proof.
  induction l; simpl; auto; rewrite countb_list_app; simpl; lia.
Qed.

Lemma minus_INeR (n m : nat) :
  (m <= n)%nat ->
  INeR n - INeR m = INeR (n - m)%nat.
Proof.
  intro Hle; unfold eRminus; simpl; destr.
  - apply eR_eq; rewrite minus_INR; auto.
  - exfalso; apply n0; apply le_INR; auto.
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

Lemma findist_itree_correct (weights : list nat) (n : nat) :
  Exists (fun w => (0 < w)%nat) weights ->
  (n < length weights)%nat ->
  tcwp (findist_tree weights) (fun x : nat => if eqb x n then 1 else 0) =
    INeR (nth n weights O) / INeR (list_sum weights).
Proof.
  intros Hex Hlt.
  unfold tcwp.
  simpl.
  rewrite twlp_const_1_findist_tree; eRauto.
  unfold findist_tree.
  rewrite twp_fix_iid; auto.
  2: { apply wf_tree_btree_to_tree. }
  2: { intros []; constructor. }
  2: { unfold findist_tree_open.
       rewrite twp_btree_to_tree.
       apply btree_some_0_btree_infer_lt_1.
       - intros []; eRauto.
       - apply btree_some_impl with (P := is_true ∘ @is_inr unit nat).
         { intros [] H; inv H; auto. }
         apply btree_some_inr_findist_btree; auto. }
  unfold findist_tree_open.
  rewrite 2!twp_btree_to_tree.
  unfold findist_btree.
  rewrite 2!reduce_btree'_infer.
  replace (fun s : unit + nat =>
             if is_inl s
             then 0
             else
               twp (cotuple (fun _ : unit => Leaf 0%nat) (Leaf (A:=nat)) s)
                 (fun x : nat => if (x =? n)%nat then 1 else 0)) with
    (fun s => if is_inr s && Nat.eqb (@proj_inr unit nat s O) n then 1 else 0).
  2: { ext s; destruct s; simpl; auto. }
  rewrite 2!perfect_btree_infer.
  2: { apply perfect_btree_map, perfect_list_btree. }
  2: { apply perfect_btree_map, perfect_list_btree. }
  rewrite 3!countb_btree_map.
  unfold compose.
  unfold uniform_btree'.
  unfold const.
  replace (fun x : unit + nat =>
             is_inr (sum_map id (bin_index weights) x) &&
               (proj_inr (sum_map id (bin_index weights) x) 0 =? n)%nat) with
    (cotuple (@const bool unit false) (fun x => Nat.eqb (bin_index weights x) n)).
  2: { ext s; destruct s; auto. }
  rewrite list_btree_count.
  rewrite countb_length_list_btree.
  rewrite rev_range_spec, rev_length, range_length.
  set (a := INeR (countb_list (fun x : nat => (bin_index weights x =? n)%nat)
                    (rev (range (list_sum weights))))).
  set (c := INeR (next_pow_2 (list_sum weights))).
  set (b := INeR
              (countb (fun x => is_inl (sum_map id (bin_index weights) x))
                 (list_btree (rev (range (list_sum weights)))))).
  assert (Hcnz: c <> 0).
  { unfold c; apply not_0_INeR.
    generalize (is_power_of_2_next_pow_2 (list_sum weights)); intros [k Hk].
    rewrite <- Hk; apply Nat.pow_nonzero; lia. }
  assert (Hcninfty: c <> infty).
  { unfold c; apply not_infty_INeR. }
  assert (Hcbnz: c - b <> 0).
  { unfold b, c.
    admit. }
  replace 1 with (c / c) by eRauto.
  replace (c / c - b / c) with ((c - b) / c).
  2: { rewrite eRdiv_minus_distr; auto. }
  rewrite eRdiv_cancel_r; auto.
  f_equal.
  - unfold a.
    f_equal.
    rewrite countb_list_rev.
    admit.
  - unfold c, b.
    rewrite minus_INeR.
    2: { unfold list_btree.
         rewrite rev_length, range_length.
         generalize (is_power_of_2_next_pow_2 (list_sum weights)).
         intros [k Hk]; rewrite <- Hk.
         rewrite Nat.log2_pow2 by lia.
         apply countb_list_btree_aux_le_pow_2. }
    f_equal.
    replace (fun x : unit + nat => is_inl (sum_map id (bin_index weights) x)) with
      (@cotuple unit nat _ (const true) (const false)).
    2: { ext s; destruct s; auto. }
    admit.

Admitted.

(* (** Extraction. *) *)
(* From Coq Require Import ExtrOcamlBasic ExtrOcamlString. *)
(* Extraction "extract/findist/findist.ml" findist_itree. *)
