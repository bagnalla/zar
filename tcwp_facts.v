(** * Properties of tcwp. *)

Set Implicit Arguments.

From Coq Require Import
  Basics
  QArith
  Reals
.

Local Open Scope program_scope.

From zar Require Import
  cpGCL
  cpo
  cwp
  eR
  misc
  order
  tactics
  tcwp
  tree
.

Local Open Scope eR_scope.

Lemma fold_twp t f :
  twp_ false t f = twp t f.
Proof. reflexivity. Qed.

Lemma twp__bounded (fl : bool) (t : tree) (f : St -> eR) :
  wf_tree t ->
  bounded f 1 ->
  twp_ fl t f <= 1.
Proof.
  revert f; induction t; simpl; intros f Hwf Hf; inv Hwf; auto.
  - destr; eRauto.
  -apply eRle_convex_sum; try apply H; eRauto.
  - apply leq_eRle.
    unfold iter.
    rewrite sup_apply.
    apply ge_sup.
    intro i.
    revert s; apply leq_arrow.
    eapply iter_n_bounded.
    { intro; eRauto. }
    intros g Hg s; unfold loop_F; simpl.
    destr; auto.
Qed.

Corollary twpfail_bounded (t : tree) (f : St -> eR) :
  wf_tree t ->
  bounded f 1 ->
  twpfail t f <= 1.
Proof. intros Hwf Hf; apply twp__bounded; auto. Qed.

Lemma twp_bounded (t : tree) (f : St -> eR) (ub : eR) :
  wf_tree t ->
  bounded f ub ->
  twp t f <= ub.
Proof.
  unfold twp; revert f; induction t; simpl; intros f Hwf Hf; inv Hwf; auto.
  - eRauto.
  - apply eRle_convex_sum; try apply H; eRauto.
  - apply leq_eRle.
    unfold iter.
    rewrite sup_apply.
    apply ge_sup.
    intro i.
    revert s; apply leq_arrow.
    eapply iter_n_bounded.
    { intro; eRauto. }
    intros g Hg s; unfold loop_F; simpl.
    destr; auto.
Qed.

Lemma monotone_twp fl t : monotone (twp_ fl t).
Proof.
  induction t; intros f f' Hf; simpl.
  - apply Hf.
  - eRauto.
  - apply eRplus_le_compat; apply eRmult_le_compat_l; try apply H; eRauto.
  - unfold iter.
    rewrite 2!sup_apply_eR.
    apply leq_eRle.
    eapply pointwise_le_supremum_le.
    2: { apply sup_spec. }
    2: { apply sup_spec. }
    intro i; revert s; apply leq_arrow.
    apply monotone_iter_n.
    2: { reflexivity. }
    intros g g' Hg.
    apply monotone_loop_F'; auto.
    + intros h h' Hh s; apply H; auto.
    + intro s; apply H0; auto.
Qed.
#[global] Hint Resolve monotone_twp : twp.

Corollary monotone_twp' fl t :
  monotone (fun (f0 : St -> eR) (s0 : St) => twp_ fl (t s0) f0).
Proof. intros f f' Hf s; apply monotone_twp; auto. Qed.
#[global] Hint Resolve monotone_twp' : twp.

Lemma twp_strict t :
  twp_ false t (const 0) = 0.
Proof.
  unfold const; induction t; simpl; try reflexivity.
  - rewrite 2!H; eRauto.
  - unfold iter, loop_F.
    apply equ_eR; rewrite sup_apply.
    apply supremum_sup, const_supremum.
    intro i; apply equ_eR.
    replace 0 with (const 0 s) by reflexivity.
    apply f_eq'. unfold const.
    induction i; simpl; try reflexivity.
    ext st; destruct (b st); auto; rewrite IHi; apply H.
Qed.

Lemma twp__tree_bind fl t k f :
  twp_ fl (tree_bind t k) f = twp_ fl t (fun s => twp_ fl (k s) f).
Proof.
  revert k f; induction t; intros k f; simpl; auto.
  - rewrite 2!H; reflexivity.
  - repeat f_equal; ext s'; auto.
Qed.

Corollary twp_tree_bind t k f :
  twp (tree_bind t k) f = twp t (fun s => twp (k s) f).
Proof. apply twp__tree_bind. Qed.

Lemma twlp__tree_bind fl t k f :
  twlp_ fl (tree_bind t k) f = twlp_ fl t (fun s => twlp_ fl (k s) f).
Proof.
  revert k f; induction t; intros k f; simpl; auto.
  - rewrite 2!H; reflexivity.
  - repeat f_equal; ext s'; auto.
Qed.

Corollary twlp_tree_bind t k f :
  twlp (tree_bind t k) f = twlp t (fun s => twlp (k s) f).
Proof. apply twlp__tree_bind. Qed.

Lemma twp_scalar t f c :
  twp t (fun x => c * f x) = c * twp t f.
Proof.
  unfold twp; revert f c; induction t; intros f c; simpl; eRauto.
  - rewrite 2!H.
    rewrite eRmult_plus_distr_l.
    rewrite <- 4!eRmult_assoc.
    f_equal; rewrite eRmult_comm, <- eRmult_assoc, eRmult_comm, eRmult_assoc;
      f_equal; apply eRmult_comm.
  - unfold iter.
    rewrite 2!sup_apply_eR.
    rewrite sup_scalar.
    f_equal; ext i.
    revert s f c.
    induction i; simpl; intros s f c; unfold const; eRauto.
    unfold loop_F.
    destruct (b s); eRauto.
    rewrite <- H; f_equal; ext st; apply IHi.
Qed.

Lemma monotone_twlp fl t : monotone (twlp_ fl t).
Proof.
  induction t; intros f f' Hf; simpl.
  - apply Hf.
  - eRauto.
  - apply eRplus_le_compat; apply eRmult_le_compat_l; try apply H; eRauto.
  - unfold dec_iter.
    rewrite 2!inf_apply_eR.
    apply leq_eRle.
    eapply pointwise_le_infimum_le.
    2: { apply inf_spec. }
    2: { apply inf_spec. }
    intro i; revert s; apply leq_arrow.
    apply monotone_iter_n.
    2: { reflexivity. }
    intros g g' Hg.
    apply monotone_loop_F'; auto.
    + intros h h' Hh s; apply H; auto.
    + intro s; apply H0; auto.
Qed.
#[global] Hint Resolve monotone_twlp : twp.

Corollary monotone_twlp' fl t :
  monotone (fun (f0 : St -> eR) (s0 : St) => twlp_ fl (t s0) f0).
Proof. intros f f' Hf s; apply monotone_twlp; auto. Qed.
#[global] Hint Resolve monotone_twlp' : twp.

Lemma twlp_bounded (fl : bool) (t : tree) (f : St -> eR) :
  wf_tree t ->
  bounded f 1 ->
  twlp_ fl t f <= 1.
Proof.
  revert fl f; induction t; intros fl f Hwf Hf; inv Hwf; simpl; auto.
  - destruct fl; eRauto.
  - apply eRle_convex_sum; eauto.
    apply Q2eR_le_1; apply H2.
  - unfold dec_iter.
    apply leq_eRle.
    rewrite inf_apply.
    apply ge_dinf with O.
    + apply dec_chain_downward_directed.
      apply dec_chain_iter_n''.
      * intro st; apply H0; auto.
      * intro st; apply H; auto.
        intro; reflexivity.
      * intros g g' Hg st; apply monotone_twlp; auto.
    + revert s; apply leq_arrow.
      apply iter_n_bounded.
      * eRauto.
      * intros g Hg s; unfold loop_F; destruct (b s).
        { apply H; auto. }
        { apply H0; auto. }
Qed.

Lemma twp__sum fl (t : tree) (f g : St -> eR) :
  twp_ fl t (fun s => f s + g s) = twp_ false t f + twp_ fl t g.
Proof.
  unfold twp; revert f g; induction t; intros f g; simpl; auto.
  - eRauto.
  - rewrite 2!H, 2!eRmult_plus_distr_l.
    rewrite <- eRplus_assoc, eRplus_comm4, eRplus_assoc; reflexivity.
  - unfold iter.
    rewrite 3!sup_apply_eR.
    rewrite <- sup_sum.
    2: { apply chain_iter_n''; auto with twp; intro; eRauto. }
    2: { apply chain_iter_n''; auto with twp; intro; eRauto. }
    f_equal; ext i.
    apply equ_eR.
    revert s. apply equ_arrow.
    apply equ_f_eR.
    induction i; simpl.
    { ext s; eRauto. }
    ext s.
    unfold loop_F; simpl.
    destruct (b s) eqn:Hbs.
    + unfold loop_F in IHi; rewrite IHi; apply H.
    + apply H0.
Qed.

Corollary twp_sum (t : tree) (f g : St -> eR) :
  twp t (fun s => f s + g s) = twp t f + twp t g.
Proof. apply twp__sum. Qed.

Corollary twpfail_sum (t : tree) (f g : St -> eR) :
  twpfail t (fun s => f s + g s) = twp t f + twpfail t g.
Proof. apply twp__sum. Qed.

(** [twp_ b c f = 1 - twlp_ (~ b) c (1 - f)] *)
Theorem twp_twlp_sum (fl : bool) (t : tree) (f : St -> eR) :
  wf_tree t ->
  bounded f 1 ->
  twp_ fl t f + twlp_ (negb fl) t (fun s => 1 - f s) = 1.
Proof.
  revert fl f; induction t; intros fl f Hwf Hf; inv Hwf; simpl.
  - eRauto.
  - destr; eRauto.
  - rewrite <- eRplus_assoc, eRplus_comm4.
    rewrite eRplus_assoc, <- 2!eRmult_plus_distr_l.
    rewrite 2!H; eRauto.
  - unfold iter, dec_iter.
    rewrite sup_apply_eR, inf_apply_eR.
    eapply supremum_infimum_sum with (ub:=1%R).
    6: { apply sup_spec. }
    6: { apply inf_spec. }
    { apply chain_iter_n''; auto with twp; intro; eRauto. }
    { apply dec_chain_iter_n''; auto with twp;
        intro st; apply twlp_bounded; auto; intro; eRauto. }
    { intro i; revert s; apply leq_arrow; apply iter_n_bounded.
      - intro; eRauto.
      - intros g Hg s; unfold loop_F; destr; apply twp__bounded; auto. }
    { intro i; revert s; apply leq_arrow; apply iter_n_bounded.
      - intro; eRauto.
      - intros g Hg s; unfold loop_F; destr;
          apply twlp_bounded; auto; intro; eRauto. }
    intro i; simpl.
    revert s.
    induction i; intro s; simpl.
    { eRauto. }
    unfold loop_F in *.
    destr.
    + replace (iter_n
                 (fun (k : St -> eR) (s0 : St) =>
                    if b s0
                    then twlp_ (negb fl) (t s0) k
                    else twlp_ (negb fl) (t0 s0) (fun s1 : St => 1 - f s1))
                 (const 1) i) with
        (fun s => 1 - iter_n (fun (k : St -> eR) (s : St) =>
                             if b s then twp_ fl (t s) k else twp_ fl (t0 s) f)
                     (const 0) i s).
      2: { ext st; symmetry; apply eRplus_eq_minus; try apply IHi; eRauto. }
      apply H; auto.
      intro s'; apply leq_eRle; revert s'.
      apply leq_arrow, iter_n_bounded.
      { intro; eRauto. }
      intros g Hg st; destr; apply twp__bounded; auto.
    + apply H0; auto.
Qed.

(** [twlp b c f = 1 - twp (~ b) c (1 - f)] *)
Corollary twlp_twp_sum (fl : bool) (t : tree) (f : St -> eR) :
  wf_tree t ->
  bounded f 1 ->
  twlp_ fl t f + twp_ (negb fl) t (fun s => 1 - f s) = 1.
Proof.
  intros Hwf Hf.
  rewrite eRplus_comm.
  replace (twlp_ fl t f) with
    (twlp_ (negb (negb fl)) t (fun s => 1 - (fun s' => 1 - f s') s)).
  2: { f_equal.
       - apply negb_involutive.
       - ext s; eRauto. }
  apply twp_twlp_sum; auto.
  intro s; eRauto.
Qed.

Corollary twlp_twp_complement (fl : bool) (t : tree) (f : St -> eR) :
  wf_tree t ->
  bounded f 1 ->
  twlp_ fl t f = 1 - twp_ (negb fl) t (fun s => 1 - f s).
Proof.
  intros Hwf Hf; apply eRplus_eq_minus.
  { eRauto. }
  rewrite eRplus_comm; apply twlp_twp_sum; auto.
Qed.

Corollary twlp_twpfail_complement (t : tree) (f : St -> eR) :
  wf_tree t ->
  bounded f 1 ->
  twlp t f = 1 - twpfail t (fun s => 1 - f s).
Proof. intros Hwf Hf; apply twlp_twp_complement; auto. Qed.

Lemma no_fail'_twp fl t f :
  no_fail' t ->
  twp_ fl t f = twp t f.
Proof.
  unfold twp; revert fl f; induction t; intros fl f Ht; inv Ht; simpl; auto.
  - rewrite H; auto; f_equal; f_equal; apply H; auto.
  - f_equal; unfold loop_F.
    ext k; ext st; destruct (b st) eqn:Hbst; auto.
Qed.

Lemma no_fail'_twlp fl t f :
  no_fail' t ->
  twlp_ fl t f = twlp t f.
Proof.
  unfold twlp; revert fl f; induction t; intros fl f Ht; inv Ht; simpl; auto.
  - rewrite H; auto; f_equal; f_equal; apply H; auto.
  - f_equal; unfold loop_F.
    ext k; ext st; destruct (b st) eqn:Hbst; auto.
Qed.

Lemma twp_tree_bind_cond (t t1 t2 : tree) (e : St -> bool) (f : St -> eR) :
  wf_tree t ->
  wf_tree t1 ->
  wf_tree t2 ->
  twp (tree_bind t (fun s => if e s then t1 else t2)) f =
    twp t (fun s => if e s then 1 else 0) * twp t1 f +
      twp t (fun s => if e s then 0 else 1) * twp t2 f.
Proof.
  intros Ht Ht1 Ht2.
  rewrite twp_tree_bind.
  rewrite eRmult_comm, <- twp_scalar.
  rewrite eRmult_comm, <- twp_scalar.
  rewrite <- twp_sum.
  f_equal; ext s; destr; eRauto.
Qed.

Lemma twp_twlp (t : tree) (f : St -> eR) :
  wf_tree t ->
  bounded f 1 ->
  twlp t f = twp t f + twlp t (const 0).
Proof.
  (** twlp t f = twp t f + twlp t (const 0)
               = twp t f + (1 - twpfail t (const 1))
      1 - twpfail t (1 - f) = twp t f + 1 - twpfail t (const 1)
      1 - twpfail t (1 - f) + twpfail t (const 1) = twp t f + 1
      1 + twpfail t (const 1) = twp t f + 1 + twpfail t (1 - f)
   *)  
  intros Hwf Hf.
  rewrite (@twlp_twpfail_complement t (const 0)); auto.
  2: { intro; eRauto. }
  rewrite eRplus_minus_assoc.
  2: { eRauto. }
  2: { apply twp__bounded; auto; intro s; eRauto. }
  rewrite twlp_twpfail_complement; auto.
  rewrite eRplus_comm.
  apply eRplus_eq_minus.
  { unfold eRplus; simpl.
    destruct (twp t f) eqn:Ht; try congruence.
    eapply twp_bounded in Hf; eauto.
    eapply eRle_infty_not_infty in Hf; try congruence.
    intro HC; inv HC. }
  rewrite eRplus_minus_assoc.
  2: { eRauto. }
  2: { apply twp__bounded; auto.
       intro; eRauto. }
  symmetry.
  apply eRplus_eq_minus.
  { unfold eRplus; simpl.
    destruct (twpfail t (fun s => 1 - const 0 s)) eqn:Ht; try congruence.
    assert (Hb: bounded (fun s => 1 - @const eR St 0 s) 1).
    { intro; eRauto. }
    eapply twpfail_bounded in Hb; eauto.
    eapply eRle_infty_not_infty in Hb; try congruence.
    intro HC; inv HC. }
  rewrite (eRplus_comm 1).
  rewrite <- eRplus_assoc.
  f_equal.
  rewrite eRplus_comm.
  rewrite <- twpfail_sum.
  f_equal.
  ext s; eRauto.
Qed.

Lemma twlp_tree_bind_cond (t t1 t2 : tree) (e : St -> bool) (f : St -> eR) :
  wf_tree t ->
  wf_tree t1 ->
  wf_tree t2 ->
  bounded f 1 ->
  twlp (tree_bind t (fun s => if e s then t1 else t2)) f =
    twp t (fun s => if e s then 1 else 0) * twlp t1 f +
      twp t (fun s => if e s then 0 else 1) * twlp t2 f +
      twlp t (const 0).
Proof.
  intros Ht Ht1 Ht2 Hf.
  rewrite twlp_tree_bind.
  rewrite eRmult_comm, <- twp_scalar.
  rewrite eRmult_comm, <- twp_scalar.
  rewrite <- twp_sum.
  replace (fun s : St => twlp t1 f * (if e s then 1 else 0) +
                        twlp t2 f * (if e s then 0 else 1)) with
    (fun s => if e s then twlp t1 f else twlp t2 f).
  2: { ext s; destr; eRauto. }
  replace (fun s : St => twlp (if e s then t1 else t2) f) with
    (fun s : St => if e s then twlp t1 f else twlp t2 f).
  2: { ext s; destr; reflexivity. }
  apply twp_twlp; auto.
  intro s; destr; apply twlp_bounded; auto.
Qed.

Lemma simple_twp_twlp (f : St -> eR) (t : tree) :
  simple t ->
  bounded f 1 ->
  twp t f = twlp t f.
Proof.
  unfold twp, twlp.
  revert f; induction t; intros f Ht Hf; simpl; auto; inv Ht.
  rewrite 2!H; auto.
Qed.

Lemma twlp_fail t :
  wf_tree t ->
  twlp t (const 1) = 1 - tfail t.
Proof.
  intro Hwf.
  cut (twlp t (const 1) + tfail t = 1).
  { intro H; apply eRplus_eq_minus.
    - eRauto.
    - rewrite eRplus_comm; apply H. }
  unfold twlp, tfail, twpfail.
  replace (twp_ true t (const 0)) with
    (twp_ (negb false) t (fun s => 1 - const 1 s)).
  { apply twlp_twp_sum; auto.
    intro s; eRauto. }
  f_equal; ext s; eRauto.
Qed.
