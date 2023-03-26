(** * Samplers for finite distributions. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Streams Basics QArith String Lia Lqa List Reals ZArith.
Local Open Scope program_scope.
Local Open Scope string_scope.
Import ListNotations.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From zar Require Import
  cotree cocwp cpo equidistribution eR itree misc order pow_2 prelude R
  tactics tcwp tcwp_facts tcwp_geometric tree uniform_Z.

(* Inductive N : Set := *)
(*   | N0 : N *)
(*   | Npos : positive -> N. *)

(* Inductive positive : Set := *)
(*   | xI : positive -> positive *)
(*   | xO : positive -> positive *)
(*   | xH : positive. *)

(* Fixpoint repeat_positive {A} (a : A) (p : positive) : list A := *)
(*   match p with *)
(*   | xH => [a] *)
(*   | xO p' => repeat_positive a p' ++ repeat_positive a p' *)
(*   | xI p' => a :: repeat_positive a p' ++ repeat_positive a p' *)
(*   end. *)

(* Definition repeat_N {A} (a : A) (n : N) : list A := *)
(*   match n with *)
(*   | N0 => [] *)
(*   | Npos p => repeat_positive a p *)
(*   end. *)
  
Fixpoint flatten_weights_aux (weights : list Z) (acc : Z) : list Z :=
  match weights with
  | [] => []
  | w :: ws => repeat acc (Z.to_nat w) ++ flatten_weights_aux ws (Z.succ acc)
  end.

Definition flatten_weights (weights : list Z) : list Z :=
  flatten_weights_aux weights Z0.

Fixpoint flatten_weights' (weights : list Z) : list Z :=
  match weights with
  | [] => []
  | w :: ws => repeat Z0 (Z.to_nat w) ++ List.map Z.succ (flatten_weights' ws)
  end.

Lemma map_repeat_N {A B} (f : A -> B) (a : A) (n : nat) :
  List.map f (repeat a n) = repeat (f a) n.
Proof. induction n; auto; simpl; rewrite IHn; auto. Qed.

Lemma flatten_weights_aux_flatten_weights' (weights : list Z) (n : Z) :
  flatten_weights_aux weights n =
    List.map (Z.add n) (flatten_weights' weights).
Proof.
  revert n; induction weights; intro n; simpl; auto.
  rewrite IHweights.
  rewrite map_app.
  f_equal.
  - rewrite map_repeat, Z.add_0_r; auto.
  - rewrite List.map_map; f_equal; ext i; lia.
Qed.

Lemma flatten_weights_flatten_weights' (weights : list Z) :
  flatten_weights weights = flatten_weights' weights.
Proof.
  unfold flatten_weights.
  rewrite flatten_weights_aux_flatten_weights'.
  rewrite map_id; auto.
Qed.

Lemma forall_repeat {A} (a : A) (P : A -> Prop) (n : nat) :
  P a ->
  Forall P (repeat a n).
Proof. induction n; intro Ha; simpl; constructor; auto. Qed.

Lemma flatten_weights_nonnegative weights :
  Forall (fun x => 0 <= x)%Z weights ->
  Forall (fun x => 0 <= x)%Z (flatten_weights' weights).
Proof.
  induction weights; simpl; intro Hall; inv Hall.
  { constructor. }
  apply Forall_app; split.
  - apply forall_repeat; lia.
  - apply Forall_map.
    eapply Forall_impl.
    2: { apply IHweights; auto. }
    simpl; lia.
Qed.

Lemma countb_list_flatten_weights' (weights : list Z) (n : Z) :
  (0 <= n)%Z ->
  Forall (fun x => 0 <= x)%Z weights ->
  countb_list (fun x => eqb n x) (flatten_weights' weights) =
    Z.to_nat (nth (Z.to_nat n) weights Z0).
Proof.
  revert n; induction weights; intros n Hle Hall; simpl.
  { destr; auto. }
  rewrite countb_list_app.
  rewrite countb_list_map.
  unfold compose.
  simpl; destruct (Z.to_nat n) eqn:Hn; simpl.
  {rewrite countb_list_repeat.
   destruct (Z.eqb_spec n 0); subst; try lia.
   rewrite countb_list_all_false; try lia.
   inv Hall.
   eapply Forall_impl; eauto.
   apply flatten_weights_nonnegative in H2.
   eapply Forall_impl.
   2: { eauto. }
   unfold compose; intros z Hz.
   destruct (Z.eqb_spec 0 (Z.succ z)); subst; try lia; constructor. }
  rewrite countb_list_all_false; simpl.
  2: { apply forall_repeat; unfold compose.
       destruct (Z.eqb_spec n 0); subst; try lia; constructor. }
  replace (fun x : Z => (n =? Z.succ x)%Z) with (fun x : Z => (Z.pred n =? x)%Z).
  2: { ext i; destruct (Z.eqb_spec (Z.pred n) i); subst.
       - rewrite Z.succ_pred; lia.
       - destruct (Z.eqb_spec n (Z.succ i)); subst; lia. }
  inv Hall; rewrite IHweights; auto; try lia; f_equal.
  replace n0 with (Z.to_nat (Z.pred n)) by lia; auto.
Qed.

Lemma countb_list_flatten_weights (weights : list Z) (n : Z) :
  (0 <= n)%Z ->
  Forall (fun x : Z => (0 <= x)%Z) weights ->
  countb_list (fun x => eqb n x) (flatten_weights weights) =
    Z.to_nat (nth (Z.to_nat n) weights Z0).
Proof.
  intros Hn Hall; rewrite flatten_weights_flatten_weights'.
  apply countb_list_flatten_weights'; auto.
Qed.

Definition findist_btree (weights : list Z) : btree (unit + Z) :=
  reduce_btree' (list_btree (flatten_weights weights)).

Definition findist_tree_open (weights : list Z) : tree (unit + Z) :=
  btree_to_tree (findist_btree weights).

(** This generalizes uniform_tree in uniform.v, i.e., we technically
    could implement uniform_tree as a special case of this
    construction. But uniform_tree is already done so there is no
    need. *)
Definition findist_tree (weights : list Z) : tree Z :=
  let t := findist_tree_open weights in
  Fix (inl tt) is_inl (fun _ => t) (cotuple (fun _ => Leaf Z0) (@Leaf _)).

(* Eval compute in (findist_btree [2%nat; 1%nat]). *)

Lemma wf_tree_findist_tree (weights : list Z) :
  wf_tree (findist_tree weights).
Proof.
  constructor.
  - intros ?; apply wf_tree_btree_to_tree.
  - intros []; constructor.
Qed.

Lemma no_fail_findist_tree (weights : list Z) :
  no_fail' (findist_tree weights).
Proof.
  constructor.
  - intros ?; apply no_fail_btree_to_tree.
  - intros []; constructor.
Qed.

Lemma twlp_const_1_findist_tree (weights : list Z) :
  twlp (findist_tree weights) (const 1) = 1.
Proof.
  rewrite twlp_fail.
  { rewrite no_fail_twlp; eRauto.
    apply no_fail_findist_tree. }
  apply wf_tree_findist_tree.
Qed.

Definition findist_itree (weights : list Z) : itree boolE Z :=
  to_itree (findist_tree weights).

(* Lemma repeat_positive_neq_nil {A} (a : A) (p : positive) : *)
(*   repeat_positive a p <> []. *)
(* Proof. *)
(*   revert a; induction p; simpl; intros a HC; try congruence. *)
(*   apply app_eq_nil in HC; destruct HC as [HC _]; congruence. *)
(* Qed. *)

(* Lemma repeat_N_eq_nil {A} (a : A) (n : N) : *)
(*   repeat_N a n = [] -> *)
(*   n = N0. *)
(* Proof. *)
(*   destruct n; simpl; auto; intro HC. *)
(*   apply repeat_positive_neq_nil in HC; contradiction. *)
(* Qed. *)

Lemma exists_pos_flatten_weights_aux_neq_nil (l : list Z) (n : Z) :
  Exists (fun w : Z => (0 < w)%Z) l ->
  flatten_weights_aux l n <> [].
Proof.
  revert n; induction l; simpl; intros n Hex HC; inv Hex;
    apply app_eq_nil in HC; destruct HC as [Ha Hl].
  - apply repeat_eq_nil in Ha; lia.
  - eapply IHl; eauto.
Qed.

Lemma btree_some_inr_findist_btree (weights : list Z) :
  Exists (fun w : Z => (0 < w)%Z) weights ->
  btree_some (is_true ∘ is_inr) (findist_btree weights).
Proof.
  intro Hex; apply btree_some_reduce_btree'.
  unfold compose, uniform_btree.
  apply btree_some_is_inr_list_btree.
  unfold flatten_weights.
  apply exists_pos_flatten_weights_aux_neq_nil; auto.
Qed.

Definition proj_inr {A B} (x : A + B) (default : B) : B :=
  match x with
  | inl _ => default
  | inr b => b
  end.

Definition list_sum_Z (l : list Z) := fold_right Z.add Z0 l.

(* Lemma repeat_positive_length {A} (a : A) (p : positive) : *)
(*   length (repeat_positive a p) = Pos.to_nat p. *)
(* Proof. induction p; simpl; auto; rewrite app_length; lia. Qed. *)

(* Lemma repeat_N_length {A} (a : A) (n : N) : *)
(*   length (repeat_N a n) = N.to_nat n. *)
(* Proof. destruct n; simpl; auto; apply repeat_positive_length. Qed. *)

Lemma list_sum_Z_nonnegative l :
  Forall (fun x : Z => (0 <= x)%Z) l ->
  (0 <= list_sum_Z l)%Z.
Proof.
  induction l; intro Hall; inv Hall; simpl; try lia.
  apply IHl in H2; lia.
Qed.

Lemma length_flatten_weights_aux (l : list Z) (n : Z) :
  Forall (fun x => 0 <= x)%Z l ->
  length (flatten_weights_aux l n) = Z.to_nat (list_sum_Z l).
Proof.
  revert n; induction l; intros n Hl; simpl; auto; inv Hl.
  rewrite Z2Nat.inj_add, app_length, repeat_length; auto.
  apply list_sum_Z_nonnegative; auto.
Qed.

Lemma length_flatten_weights (l : list Z) :
  Forall (fun x => 0 <= x)%Z l ->
  length (flatten_weights l) = Z.to_nat (list_sum_Z l).
Proof. intro Hl; apply length_flatten_weights_aux; auto. Qed.

Lemma exists_pos_list_sum_N l :
  Forall (fun x => 0 <= x)%Z l ->
  Exists (fun w : Z => (0 < w)%Z) l ->
  (0 < list_sum_Z l)%Z.
Proof.
  induction l; intros Hall Hex; inv Hall; inv Hex; simpl.
  - apply list_sum_Z_nonnegative in H2; lia.
  - apply IHl in H0; auto; lia.
Qed.

Lemma findist_tree_correct (weights : list Z) (n : Z) :
  (0 <= n)%Z ->
  Forall (fun x => 0 <= x)%Z weights ->
  Exists (fun w => (0 < w)%Z) weights ->
  (Z.to_nat n < length weights)%nat ->
  tcwp (findist_tree weights) (fun x : Z => if eqb n x then 1 else 0) =
    IZeR (nth (Z.to_nat n) weights Z0) / IZeR (list_sum_Z weights).
Proof.
  intros Hn Hall Hex Hlt.
  unfold tcwp; simpl.
  rewrite twlp_const_1_findist_tree; eRauto.
  unfold findist_tree.
  rewrite twp_fix_iid; auto.
  2: { apply wf_tree_btree_to_tree. }
  2: { intros []; constructor. }
  2: { unfold findist_tree_open.
       rewrite twp_btree_to_tree.
       apply btree_some_0_btree_infer_lt_1.
       - intros []; eRauto.
       - apply btree_some_impl with (P := is_true ∘ @is_inr unit Z).
         { intros [] H; inv H; auto. }
         apply btree_some_inr_findist_btree; auto. }
  unfold findist_tree_open.
  rewrite 2!twp_btree_to_tree.
  unfold findist_btree.
  rewrite 2!reduce_btree'_infer.
  replace (fun s : unit + Z =>
             if is_inl s
             then 0
             else
               twp (cotuple (fun _ : unit => Leaf 0%Z) (Leaf (A:=Z)) s)
                 (fun x : Z => if (n =? x)%Z then 1 else 0)) with
    (fun s => if is_inr s && eqb (@proj_inr unit Z s Z0) n then 1 else 0).
  2: { ext s; destruct s; simpl; auto.
       rewrite Z.eqb_sym; auto. }
  rewrite 2!perfect_btree_infer.
  2: { apply perfect_list_btree. }
  2: { apply perfect_list_btree. }
  unfold const.
  replace (fun x : unit + Z => is_inr x && eqb (proj_inr x Z0) n) with
    (cotuple (@const bool unit false) (fun x => eqb x n)).
  2: { ext s; destruct s; auto. }
  rewrite list_btree_count.
  rewrite countb_length_list_btree.
  rewrite length_flatten_weights; auto.
  set (a := INeR (countb_list (fun x : Z => eqb x n) (flatten_weights weights))).
  set (c := INeR (next_pow_2 (Z.to_nat (list_sum_Z weights)))).
  set (b := INeR (countb is_inl (list_btree (flatten_weights weights)))).
  assert (Hcnz: c <> 0).
  { unfold c; apply not_0_INeR.
    generalize (is_power_of_2_next_pow_2 (Z.to_nat (list_sum_Z weights))); intros [k Hk].
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
    rewrite length_flatten_weights; auto.
    generalize (is_power_of_2_next_pow_2 (Z.to_nat (list_sum_Z weights))).
    intros [k Hk]; rewrite <- Hk.
    rewrite Nat.log2_pow2; try lia.
    replace is_inl with (@cotuple unit Z _ (const true) (const false)).
    2: { ext x; destruct x; reflexivity. }
    rewrite list_btree_aux_countb'.
    { rewrite length_flatten_weights; auto.
      assert (0 < list_sum_Z weights)%Z.
      { apply exists_pos_list_sum_N; auto. }
      assert (0 < 2^k)%nat.
      { apply pow_positive; lia. }
      lia. }
    rewrite length_flatten_weights, Hk; auto.
    apply next_pow_2_ub. }
  replace 1 with (c / c) by eRauto.
  replace (c / c - b / c) with ((c - b) / c).
  2: { rewrite eRdiv_minus_distr; auto. }
  rewrite eRdiv_cancel_r; auto; f_equal.
  - unfold a; f_equal.
    replace (fun x => eqb x n) with (fun x => eqb n x).
    2: { ext i; apply Z.eqb_sym. }
    rewrite countb_list_flatten_weights; auto.
    apply INeR_IZeR.
  - unfold c, b.
    rewrite minus_INeR.
    2: { unfold list_btree.
         rewrite length_flatten_weights; auto.
         generalize (is_power_of_2_next_pow_2 (Z.to_nat (list_sum_Z weights))).
         intros [k Hk]; rewrite <- Hk.
         rewrite Nat.log2_pow2 by lia.
         apply countb_list_btree_aux_le_pow_2. }
    f_equal.
    replace is_inl with (@cotuple unit Z _ (const true) (const false)).
    2: { ext s; destruct s; auto. }
    unfold list_btree.
    rewrite length_flatten_weights; auto.
    generalize (is_power_of_2_next_pow_2 (Z.to_nat (list_sum_Z weights))).
    intros [k Hk]; rewrite <- Hk.
    rewrite Nat.log2_pow2; try lia.
    rewrite list_btree_aux_countb'.
    { rewrite length_flatten_weights; auto.
      rewrite sub_sub_le.
      - apply INeR_IZeR.
      - rewrite Hk; apply next_pow_2_ub. }
    rewrite length_flatten_weights; auto.
    rewrite Hk; apply next_pow_2_ub.
Qed.

(* (** Extraction. *) *)
(* From Coq Require Import ExtrOcamlBasic ExtrOcamlString. *)
(* Extraction "extract/findist/findist.ml" findist_itree. *)
