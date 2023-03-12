(** * De-biasing CF trees and other transformations (elim_choices, opt). *)

From Coq Require Import
  Basics
  QArith
  Lqa
.

Local Open Scope program_scope.

From zar Require Import
  cpGCL
  cpo
  cwp
  misc
  order
  eR
  tactics
  tcwp
  tcwp_facts
  tree
  uniform
.

Fixpoint debias {A} (t : tree A) : tree A :=
  match t with
  | Leaf x => Leaf x
  | Fail _ => Fail _
  | Choice p f =>
      if Qeq_bool p (1#2) then Choice p (debias ∘ f) else
        tree_bind (bernoulli_tree p)
          (fun b => if b then debias (f true) else debias (f false))
  | Fix st G g k => Fix st G (debias ∘ g) (debias ∘ k)
  end.

Lemma wf_tree'_debias {A} (t : tree A) :
  wf_tree' t ->
  wf_tree' (debias t).
Proof.
  induction 1; try constructor; eauto with tree.
  simpl.
  destruct (Qeq_bool p (1#2)) eqn:Hp.
  - constructor; auto.
  - constructor; eauto with tree.
    intros [|[]]; simpl; auto.
Qed.
#[global] Hint Resolve wf_tree'_debias : tree.

Lemma debias_choice {A} q (f : bool -> tree A) :
  debias (Choice q f) =
    if Qeq_bool q (1#2) then Choice q (debias ∘ f) else
      tree_bind (bernoulli_tree q)
        (fun b => if b then debias (f true) else debias (f false)).
Proof. reflexivity. Qed.

Lemma twp_debias {A} (t : tree A) f :
  wf_tree' t ->
  twp (debias t) f = twp t f.
Proof.
  revert f; induction t; intros f Hwf; inv Hwf; auto.
  - rewrite debias_choice.
    destruct (Qeq_bool q (1#2)) eqn:Hq.
    + unfold twp. simpl.
      apply Qeq_bool_iff in Hq.
      rewrite Hq.
      unfold compose.
      rewrite 3!fold_twp.
      rewrite 2!H; auto.
    + rewrite twp_tree_bind_cond; eauto with tree.
      2: { constructor.
           - intros _; apply wf_tree_btree_to_tree.
           - intros []; constructor. }
      rewrite bernoulli_tree_twp_p; try lra; auto.
      rewrite bernoulli_tree_twp_p_compl; try lra; auto.
      rewrite 2!H; auto.
  - existT_inv.
    unfold twp; simpl; unfold compose.
    f_equal; unfold loop_F.
    ext k; ext st; destr; eauto.
Qed.

Lemma twlp_debias {A} (t : tree A) f :
  wf_tree' t ->
  bounded f 1 ->
  twlp (debias t) f = twlp t f.
Proof.
  revert f; induction t; intros f Hwf Hf; inv Hwf; auto.
  - rewrite debias_choice.
    destruct (Qeq_bool q (1#2)) eqn:Hq.
    + unfold twlp, compose; simpl; rewrite 2!fold_twlp, 2!H; auto.
    + rewrite twlp_tree_bind_cond; eauto with tree.
      2: { constructor.
           - intros _; apply wf_tree_btree_to_tree.
           - intros []; constructor. }
      rewrite bernoulli_tree_twp_p; try lra; auto.
      rewrite bernoulli_tree_twp_p_compl; try lra; auto.
      rewrite 2!H; auto.
      replace (twlp (bernoulli_tree q) (const 0)) with 0.
      2: { unfold twlp; rewrite <- bernoulli_tree_twp_twlp.
           - symmetry; apply twp_strict.
           - intro; eRauto. }
      eRauto.
  - existT_inv.
    unfold twlp; simpl; unfold compose.
    unfold dec_iter.
    rewrite 2!inf_apply_eR.
    f_equal; ext j.
    apply equ_eR.
    revert i.
    apply equ_arrow.
    apply equ_f_eR.
    induction j; simpl; auto.
    unfold loop_F in *; ext s; destruct (b s); eauto.
    rewrite IHj; apply H; auto.
    intro s'.
    apply leq_eRle.
    revert s'.
    apply leq_arrow.
    apply iter_n_bounded.
    + reflexivity.
    + intros g Hg st; destr; apply twlp_bounded;
        auto; apply wf_tree'_wf_tree; auto.
Qed.

Theorem tcwp_debias {A} (t : tree A) f :
  wf_tree' t ->
  tcwp (debias t) f = tcwp t f.
Proof.
  unfold tcwp; intro Hwf.
  rewrite twp_debias, twlp_debias; auto; intro; eRauto.
Qed.

(** De-biasing produces unbiased trees. *)
Theorem tree_unbiased_debias {A} (t : tree A) :
  tree_unbiased (debias t).
Proof.
  induction t; simpl; try constructor; auto.
  destruct (Qeq_bool q (1#2)) eqn:Hq.
  - constructor; auto.
    apply Qeq_bool_iff in Hq; auto.
  - constructor.
    + intro s; apply tree_unbiased_btree_to_tree.
    + intros [|[]]; simpl; auto.
Qed.

(** Eliminating redundant choices and reducing rationals. *)
Fixpoint elim_choices {A} (t : tree A) : tree A :=
  match t with
  | Leaf x => Leaf x
  | Fail _ => Fail _
  | Choice p k =>
      if Qeq_bool p 0 then
        elim_choices (k false)
      else if Qeq_bool p 1 then
             elim_choices (k true) else
             Choice (Qred p) (elim_choices ∘ k)
  | Fix st G g k => Fix st G (elim_choices ∘ g) (elim_choices ∘ k)
  end.

Theorem wf_tree'_elim_choices {A} (t : tree A) :
  wf_tree t ->
  wf_tree' (elim_choices t).
Proof.
  induction t; intro Hwf; simpl; inv Hwf.
  - constructor.
  - constructor.
  - destruct (Qeq_bool q 0) eqn:Hq0; eauto.
    destruct (Qeq_bool q 1) eqn:Hq1; eauto.
    apply Qeq_bool_neq in Hq0.
    apply Qeq_bool_neq in Hq1.
    constructor; auto.
    + replace 0%Q with (Qred 0)%Q by reflexivity.
      apply Qred_lt; lra.
    + replace 1%Q with (Qred 1)%Q by reflexivity.
      apply Qred_lt; lra.
    + apply Qred_complete, Qred_correct.
    + intros []; unfold compose; auto.
  - existT_inv; constructor; eauto.
Qed.

Lemma twp__elim_choices {A} (fl : bool) (f : A -> eR) (t : tree A) :
  wf_tree t ->
  twp_ fl (elim_choices t) f = twp_ fl t f.
Proof.
  revert fl f; induction t; intros fl f Hwf; inv Hwf; simpl; auto.
  - destruct (Qeq_bool q 0) eqn:Hq0.
    + rewrite H; auto.
      apply Qeq_bool_eq in Hq0.
      replace (Q2eR q) with 0.
      2: { rewrite Hq0, Q2eR_0; reflexivity. }
      eRauto.
    + destruct (Qeq_bool q 1) eqn:Hq1.
      * rewrite H; auto.
        apply Qeq_bool_eq in Hq1.
        replace (Q2eR q) with 1.
        2: { rewrite Hq1, Q2eR_1; reflexivity. }
        eRauto.
      * simpl; unfold compose; rewrite 2!H; auto.
        replace (Q2eR (Qred q)) with (Q2eR q); auto.
        rewrite Qred_correct; reflexivity.
  - existT_inv; f_equal; ext k; ext st; unfold loop_F, compose; destr; auto.
Qed.

Corollary twp_elim_choices {A} (f : A -> eR) (t : tree A) :
  wf_tree t ->
  twp (elim_choices t) f = twp t f.
Proof. apply twp__elim_choices. Qed.

Lemma twlp__elim_choices {A} (fl : bool) (f : A -> eR) (t : tree A) :
  wf_tree t ->
  twlp_ fl (elim_choices t) f = twlp_ fl t f.
Proof.
  revert fl f; induction t; intros fl f Hwf; inv Hwf; simpl; auto.
  - destruct (Qeq_bool q 0) eqn:Hq0.
    + rewrite H; auto.
      apply Qeq_bool_eq in Hq0.
      replace (Q2eR q) with 0.
      2: { rewrite Hq0, Q2eR_0; reflexivity. }
      eRauto.
    + destruct (Qeq_bool q 1) eqn:Hq1.
      * rewrite H; auto.
        apply Qeq_bool_eq in Hq1.
        replace (Q2eR q) with 1.
        2: { rewrite Hq1, Q2eR_1; reflexivity. }
        eRauto.
      * simpl; unfold compose; rewrite 2!H; auto.
        replace (Q2eR (Qred q)) with (Q2eR q); auto.
        rewrite Qred_correct; reflexivity.
  - existT_inv; f_equal; ext k; ext st; unfold loop_F, compose; destr; auto.
Qed.

Corollary twlp_elim_choices {A} (f : A -> eR) (t : tree A) :
  wf_tree t ->
  twlp (elim_choices t) f = twlp t f.
Proof. apply twlp__elim_choices. Qed.

Theorem tcwp_elim_choices {A} (f : A -> eR) (t : tree A) :
  wf_tree t ->
  tcwp (elim_choices t) f = tcwp t f.
Proof.
  intro Ht; unfold tcwp, twp, twlp.
  rewrite twp__elim_choices, twlp__elim_choices; auto.
Qed.

Inductive reduced {A} : tree A -> Prop :=
| reduced_leaf : forall x, reduced (Leaf x)
| reduced_fail : reduced (Fail _)
| reduced_choice : forall q k,
    (0 < q < 1)%Q ->
    Qred q = q ->
    (forall b, reduced (k b)) ->
    reduced (Choice q k)
| reduce_fix : forall I (st : I) e g k,
    (forall s, reduced (g s)) ->
    (forall s, reduced (k s)) ->
    reduced (Fix st e g k).
    
Theorem reduced_elim_choices {A} (t : tree A) :
  wf_tree t ->
  reduced (elim_choices t).
Proof.
  induction t; simpl; intro Hwf; inv Hwf.
  - constructor.
  - constructor.
  - destruct (Qeq_bool q 0) eqn:Hq0; auto.
    destruct (Qeq_bool q 1) eqn:Hq1; auto.
    constructor; auto.
    + apply Qeq_bool_neq in Hq0.
      apply Qeq_bool_neq in Hq1.
      destruct H2; split.
      * replace 0%Q with (Qred 0%Q) by reflexivity.
        apply Qred_lt; lra.
      * replace 1%Q with (Qred 1%Q) by reflexivity.
        apply Qred_lt; lra.
    + apply Qred_complete, Qred_correct.
    + intro b; apply H; auto.
  - existT_inv; constructor; eauto.
Qed.

(** Eliminate fail children of the root. *)
Fixpoint opt {A} (t : tree A) : tree A :=
  match t with
  | Choice p k =>
      let l := k true in
      let r := k false in
      match (l, r) with
      | (Fail _, _) => opt r
      | (_, Fail _) => opt l
      | _ => t
      end
  (* | Fix st e g k => Fix st e (opt ∘ g) k *)
  | _ => t
  end.

Theorem wf_tree_opt {A} (t : tree A) :
  wf_tree t ->
  wf_tree (opt t).
Proof.
  induction t; intro Hwf; simpl; inv Hwf.
  - constructor.
  - constructor.
  - destruct (t true) eqn:Ht; auto.
    + destruct (t false); simpl; constructor; auto.
    + destruct (t false) eqn:Hf; auto.
      * constructor; auto.
      * specialize (H true (H3 true)); rewrite Ht in H; auto.
      * constructor; auto.
      * constructor; auto.
    + destruct (t false).
      * constructor; auto.
      * specialize (H true (H3 true)).
        rewrite Ht in H; simpl in H; inv H.
        existT_inv.
        simpl; constructor; auto.
      * constructor; auto.
      * constructor; auto.
    (* + destruct (t false); constructor; auto. *)
    (*   * specialize (H3 true); rewrite Ht in H3; inv H3; auto. *)
    (*   * specialize (H3 true); rewrite Ht in H3; inv H3; auto. *)
  - existT_inv; constructor; eauto.
Qed.

Theorem wf_tree'_opt {A} (t : tree A) :
  wf_tree' t ->
  wf_tree' (opt t).
Proof.
  induction t; intro Hwf; simpl; inv Hwf.
  - constructor.
  - constructor.
  - destruct (t true) eqn:Ht; auto.
    + destruct (t false); simpl; constructor; auto.
    + destruct (t false) eqn:Hf; auto.
      * constructor; auto.
      * specialize (H true (H5 true)); rewrite Ht in H; auto.
      * constructor; auto.
      * constructor; auto.
    + destruct (t false); constructor; auto.
      * specialize (H5 true); rewrite Ht in H5; inv H5; existT_inv; auto.
      * specialize (H5 true); rewrite Ht in H5; inv H5; existT_inv; auto.
  - existT_inv; constructor; eauto.
Qed.

Lemma twp_twlp_opt {A} (f g : A -> eR) (t : tree A) :
  wf_tree' t ->
  twp (opt t) f / twlp (opt t) g = twp t f / twlp t g.
Proof.
  unfold twp, twlp.
  revert f g; induction t; intros f g Hwf; inv Hwf; simpl; auto.
  - destruct (t true) eqn:Ht.
    + destruct (t false) eqn:Hf; simpl.
      * rewrite Ht, Hf; reflexivity.
      * eRauto; rewrite eRdiv_mult_l; eauto with eR.
        apply Q2eR_nz; auto.
      * rewrite Ht, Hf; reflexivity.
      * rewrite Ht, Hf; reflexivity.
    + rewrite H; simpl; eRauto.
      rewrite eRdiv_mult_l; auto with eR.
      apply one_minus_Q2eR_nz; lra.
    + destruct (t false) eqn:Hf.
      * simpl; rewrite Ht, Hf; reflexivity.
      * specialize (H true f g (H5 true)).
        rewrite Ht in H; rewrite H; simpl.
        eRauto; rewrite eRdiv_mult_l; eauto with eR.
        apply Q2eR_nz; auto.
      * simpl; rewrite Ht, Hf; reflexivity.
      * simpl; rewrite Ht, Hf; reflexivity.
    + destruct (t false) eqn:Hf.
      * simpl; rewrite Ht, Hf; reflexivity.
      * specialize (H true f g (H5 true)).
        rewrite Ht in H; rewrite H; simpl.
        eRauto; rewrite eRdiv_mult_l; eauto with eR.
        apply Q2eR_nz; auto.
      * simpl; rewrite Ht, Hf; reflexivity.
      * simpl; rewrite Ht, Hf; reflexivity.
Qed.

Lemma twlp_opt_pos {A} (t : tree A) f :
  0 < twlp t f ->
  0 < twlp (opt t) f.
Proof.
  revert f; induction t; simpl; intros f Hlt; auto.
  destruct (t true) eqn:Ht.
  - destruct (t false) eqn:Hf; auto.
    unfold twlp in *; simpl in *.
    rewrite Ht, Hf in Hlt; simpl in Hlt.
    rewrite eRmult_0_r, eRplus_0_r in Hlt.
    eapply eRmult_eRlt; eauto; eRauto.
  - apply H.
    unfold twlp in *; simpl in *.
    rewrite Ht in Hlt; simpl in Hlt.
    rewrite eRmult_0_r, eRplus_0_l in Hlt.
    eapply eRmult_eRlt; eauto; eRauto.
  - destruct (t false) eqn:Hf; auto.
    rewrite <- Ht; apply H.
    unfold twlp in *; simpl in *.
    rewrite Hf in Hlt; simpl in Hlt.
    rewrite eRmult_0_r, eRplus_0_r in Hlt.
    eapply eRmult_eRlt; eauto; eRauto.
  - destruct (t false) eqn:Hf; auto.
    simpl; rewrite <- Ht.
    unfold twlp in *; simpl in Hlt.
    rewrite Hf in Hlt.
    rewrite eRmult_0_r, eRplus_0_r in Hlt.
    eapply eRmult_eRlt; eauto; eRauto.
Qed.

Theorem tcwp_opt {A} (f : A -> eR) (t : tree A) :
  wf_tree' t ->
  tcwp (opt t) f = tcwp t f.
Proof.
  intro Ht; unfold tcwp, twp, twlp.
  rewrite 2!fold_twp, 2!fold_twlp.
  rewrite twp_twlp_opt; auto.
Qed.

(* Eval compute in (opt (Choice (1#2) *)
(*                         (fun b => if b then Fail else *)
(*                                  Choice (1#2) (fun b => if b then Leaf empty else Fail)))). *)

Lemma tree_unbiased_opt {A} (t : tree A) :
  tree_unbiased t ->
  tree_unbiased (opt t).
Proof.
  induction t; intro Hub; simpl; auto.
  destruct (t true) eqn:Ht.
  - destruct (t false) eqn:Hf; auto.
    simpl; constructor.
  - apply H; inv Hub; auto.
  - destruct (t false) eqn:Hf; auto.
    rewrite <- Ht; apply H; inv Hub; auto.
  - destruct (t false) eqn:Hf; auto.
    inv Hub.
    specialize (H true (H3 true)).
    rewrite Ht in H; inv H.
    existT_inv; simpl; constructor; auto.
Qed.
