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

Fixpoint flatten_weights_aux (weights : list nat) (acc : nat) : list nat :=
  match weights with
  | [] => []
  | w :: ws => repeat acc w ++ flatten_weights_aux ws (S acc)
  end.

Definition flatten_weights (weights : list nat) : list nat :=
  flatten_weights_aux weights O.

Fixpoint flatten_weights' (weights : list nat) : list nat :=
  match weights with
  | [] => []
  | w :: ws => repeat O w ++ List.map S (flatten_weights' ws)
  end.

Lemma flatten_weights_aux_flatten_weights' (weights : list nat) (n : nat) :
  flatten_weights_aux weights n =
    List.map (Peano.plus n) (flatten_weights' weights).
Proof.
  revert n; induction weights; intro n; simpl; auto.
  rewrite IHweights.
  rewrite map_app.
  f_equal.
  - rewrite map_repeat; auto.
  - rewrite List.map_map; f_equal; ext i; lia.
Qed.

Lemma flatten_weights_flatten_weights' (weights : list nat) :
  flatten_weights weights = flatten_weights' weights.
Proof.
  unfold flatten_weights.
  rewrite flatten_weights_aux_flatten_weights'.
  replace (Init.Nat.add O) with (@id nat) by auto.
  rewrite map_id; auto.
Qed.

Lemma countb_list_flatten_weights' (weights : list nat) (n : nat) :
  countb_list (fun x => Nat.eqb n x) (flatten_weights' weights) = nth n weights O.
Proof.
  revert n; induction weights; intro n; simpl.
  { destruct n; auto. }
  rewrite countb_list_app.
  rewrite countb_list_map.
  unfold compose.
  simpl.
  destruct n; simpl.
  { rewrite countb_list_repeat, countb_list_false; lia. }
  rewrite IHweights.
  rewrite countb_list_repeat; lia.
Qed.

Lemma countb_list_flatten_weights (weights : list nat) (n : nat) :
  countb_list (fun x => Nat.eqb n x) (flatten_weights weights) = nth n weights O.
Proof.
  rewrite flatten_weights_flatten_weights'.
  apply countb_list_flatten_weights'.
Qed.

Definition findist_btree (weights : list nat) : btree (unit + nat) :=
  reduce_btree' (list_btree (flatten_weights weights)).

Definition findist_tree_open (weights : list nat) : tree (unit + nat) :=
  btree_to_tree (findist_btree weights).

(** This generalizes uniform_tree in uniform.v, i.e., we technically
    could implement uniform_tree as a special case of this
    construction. But uniform_tree is already done so there is no
    need. *)
Definition findist_tree (weights : list nat) : tree nat :=
  let t := findist_tree_open weights in
  Fix (inl tt) is_inl (fun _ => t) (cotuple (fun _ => Leaf O) (@Leaf _)).

(* Eval compute in (findist_btree [2%nat; 1%nat]). *)

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

Lemma exists_pos_flatten_weights_aux_neq_nil (l : list nat) (n : nat) :
  Exists (fun w : nat => (0 < w)%nat) l ->
  flatten_weights_aux l n <> [].
Proof.
  revert n; induction l; simpl; intros n Hex HC; inv Hex;
    apply app_eq_nil in HC; destruct HC as [Ha Hl].
  - apply repeat_eq_nil in Ha; lia.
  - eapply IHl; eauto.
Qed.

Lemma btree_some_inr_findist_btree (weights : list nat) :
  Exists (fun w : nat => (0 < w)%nat) weights ->
  btree_some (is_true ∘ is_inr) (findist_btree weights).
Proof.
  intro Hex; apply btree_some_reduce_btree'.
  unfold compose, uniform_btree'.
  apply btree_some_is_inr_list_btree.
  unfold flatten_weights.
  apply exists_pos_flatten_weights_aux_neq_nil; auto.
Qed.

Definition proj_inr {A B} (x : A + B) (default : B) : B :=
  match x with
  | inl _ => default
  | inr b => b
  end.

Lemma length_flatten_weights_aux (l : list nat) (n : nat) :
  length (flatten_weights_aux l n) = list_sum l.
Proof.
  revert n; induction l; intro n; simpl; auto.
  rewrite app_length, repeat_length; auto.
Qed.  

Lemma length_flatten_weights (l : list nat) :
  length (flatten_weights l) = list_sum l.
Proof. apply length_flatten_weights_aux. Qed.

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
  2: { apply perfect_list_btree. }
  2: { apply perfect_list_btree. }
  unfold const.
  replace (fun x : unit + nat => is_inr x && (proj_inr x 0 =? n)%nat) with
    (cotuple (@const bool unit false) (fun x => Nat.eqb x n)).
  2: { ext s; destruct s; auto. }
  rewrite list_btree_count.
  rewrite countb_length_list_btree.
  rewrite length_flatten_weights.
  set (a := INeR (countb_list (fun x : nat => (x =? n)%nat) (flatten_weights weights))).
  set (c := INeR (next_pow_2 (list_sum weights))).
  set (b := INeR (countb is_inl (list_btree (flatten_weights weights)))).
  assert (Hcnz: c <> 0).
  { unfold c; apply not_0_INeR.
    generalize (is_power_of_2_next_pow_2 (list_sum weights)); intros [k Hk].
    rewrite <- Hk; apply Nat.pow_nonzero; lia. }
  assert (Hcninfty: c <> infty).
  { unfold c; apply not_infty_INeR. }
  assert (Hcbnz: c - b <> 0).
  { unfold b, c.
    apply eRlt_neq', eRlt_pos, lt_INeR.
    (* replace (fun x : unit + nat => is_inl (sum_map id (bin_index weights) x)) *)
    (*   with (@cotuple unit nat _ (const true) (const false)). *)
    (* 2: { ext x; destruct x; reflexivity. } *)
    unfold list_btree.
    (* rewrite rev_length, range_length. *)
    rewrite length_flatten_weights.
    generalize (is_power_of_2_next_pow_2 (list_sum weights)).
    intros [k Hk]; rewrite <- Hk.
    rewrite Nat.log2_pow2; try lia.
    replace is_inl with (@cotuple unit nat _ (const true) (const false)).
    2: { ext x; destruct x; reflexivity. }
    rewrite list_btree_aux_countb'.
    { rewrite length_flatten_weights.
      assert (0 < list_sum weights)%nat.
      { apply exists_pos_list_sum; auto. }
      assert (0 < 2^k)%nat.
      { apply pow_positive; lia. }
      lia. }
    rewrite length_flatten_weights, Hk.
    apply next_pow_2_ub. }
  replace 1 with (c / c) by eRauto.
  replace (c / c - b / c) with ((c - b) / c).
  2: { rewrite eRdiv_minus_distr; auto. }
  rewrite eRdiv_cancel_r; auto; f_equal.
  - unfold a; f_equal.
    replace (fun x => Nat.eqb x n) with (fun x => Nat.eqb n x).
    2: { ext i; apply Nat.eqb_sym. }
    apply countb_list_flatten_weights.
  - unfold c, b.
    rewrite minus_INeR.
    2: { unfold list_btree.
         rewrite length_flatten_weights.
         generalize (is_power_of_2_next_pow_2 (list_sum weights)).
         intros [k Hk]; rewrite <- Hk.
         rewrite Nat.log2_pow2 by lia.
         apply countb_list_btree_aux_le_pow_2. }
    f_equal.
    replace is_inl with (@cotuple unit nat _ (const true) (const false)).
    2: { ext s; destruct s; auto. }
    unfold list_btree.
    rewrite length_flatten_weights.
    generalize (is_power_of_2_next_pow_2 (list_sum weights)).
    intros [k Hk]; rewrite <- Hk.
    rewrite Nat.log2_pow2; try lia.
    rewrite list_btree_aux_countb'.
    { rewrite length_flatten_weights.
      apply sub_sub_le; rewrite Hk; apply next_pow_2_ub. }
    rewrite length_flatten_weights.
    rewrite Hk; apply next_pow_2_ub.
Qed.

(* (** Extraction. *) *)
(* From Coq Require Import ExtrOcamlBasic ExtrOcamlString. *)
(* Extraction "extract/findist/findist.ml" findist_itree. *)
