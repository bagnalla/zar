(** * Geometric series definition and proof of convergence. *)

(** Divergent series are the devil, and it is a shame to base on them
    any demonstration whatsoever. (Niels Henrik Abel, 1826)
    (https://www.math.ucdavis.edu/~hunter/intro_analysis_pdf/ch4.pdf) *)

Set Implicit Arguments.

From Coq Require Import
  Lia
  Lra
  Reals
.

Local Open Scope R_scope.

From zar Require Import
  cpo
  eR
  order
  tactics
.

Fixpoint geometric_series (a r : eR) (n : nat) : eR :=
  match n with
  | O => 0
  | S n' => geometric_series a r n' + a * r ^ n'
  end.

Lemma eRmult_infty_inv a b :
  a * b = infty ->
  a = infty \/ b = infty.
Proof. intro Hab; destruct a, b; inv Hab; auto. Qed.

Lemma eRpow_infty_inv r i :
  r ^ i = infty ->
  r = infty.
Proof.
  revert r; induction i; simpl; intros r Hr.
  - inv Hr.
  - apply eRmult_infty_inv in Hr; destruct Hr; auto.
Qed.

Lemma geometric_series_sum (r : eR) (n : nat) :
  r < 1 ->
  geometric_series 1 r n = (1 - r ^ n) / (1 - r).
Proof.
  revert r; induction n; intros r Hr; simpl.
  { rewrite eRminus_cancel; eRauto. }
  rewrite eRmult_1_l.
  rewrite IHn; auto; clear IHn.
  replace ((1 - r ^ n) / (1 - r) + r ^ n) with
    ((1 - r ^ n) / (1 - r) + ((1 - r) * r ^ n) / (1 - r)).
  2: { rewrite eRmult_div_cancel; eRauto; intro HC.
       symmetry in HC; apply eRminus_eq_plus in HC; eRauto.
       rewrite eRplus_0_r in HC; subst.
       inv Hr; lra. }
  rewrite eRplus_combine_fract; f_equal.
  rewrite eRmult_minus_distr_r.
  2: { intro HC; apply eRpow_infty_inv in HC; subst; inv Hr. }
  rewrite eRmult_1_l.
  rewrite eRplus_minus_assoc.
  2: { intro HC; apply eRpow_infty_inv in HC; subst; inv Hr. }
  2: { eRauto. }
  f_equal.
  rewrite <- eRminus_assoc.
  { eRauto. }
  { apply eRpow_le_1; eRauto. }
  { reflexivity. }
  { intro HC; apply eRpow_infty_inv in HC; subst; inv Hr. }
Qed.

Lemma eRpow_pow a r n r1 r2 :
  er a r ^ n = er r1 r2 ->
  (a ^ n)%R = r1.
Proof.
  revert a r r1 r2; induction n; simpl; intros a r r1 r2 H.
  { inv H; reflexivity. }
  unfold eRmult in H.
  destruct (er a r ^ n) eqn:Har.
  - inv H; erewrite IHn; eauto.
  - apply eRpow_infty_inv in Har; inv Har.
Qed.

Lemma pow_seq_converges (a : eR) :
  a < 1 ->
  converges (eRpow a) 0.
Proof.
  intros Ha eps Heps.
  destruct a as [a|].
  2: { inv Ha. }
  inv Ha.
  destruct (Req_dec a 0); subst.
  - exists (S O); intros n Hn.
    unfold diff. simpl.
    destruct n; simpl; try lia.
    + rewrite eRmult_0_l'; simpl; destr.
      2: { exfalso; lra. }
      destruct eps; constructor; inv Heps; lra.
  - assert (Hr: R.converges_R (R.pow_sequence a) 0%R).
    { apply R.pow_sequence_converges'; lra. }
    unfold R.converges_R in Hr.
    destruct eps as [eps|].
    2: { exists O; intros n Hn.
         unfold diff; simpl.
         destruct (er a r ^ n) eqn:Hrn.
         - destr; constructor.
         - apply eRpow_infty_inv in Hrn; inv Hrn. }
    inv Heps.
    specialize (Hr eps H3).
    destruct Hr as [n0 Hr].
    exists n0; intros n Hn; specialize (Hr n Hn).
    unfold R.pow_sequence in Hr.
    unfold diff.
    rewrite Rabs_minus_sym in Hr.
    rewrite Rminus_0_r in Hr.
    destruct (er a r ^ n) eqn:Hrn; simpl.
    + destr.
      * constructor.
        rewrite Rabs_pos_eq in Hr.
        2: { apply pow_le; lra. }
        rewrite Rminus_0_r.
        eapply Rle_lt_trans.
        2: { apply Hr. }
        apply eRpow_pow in Hrn; lra.
      * constructor; lra.
    + apply eRpow_infty_inv in Hrn; inv Hrn.
Qed.

Lemma infimum_0_minus_supremum (a : eR) (f : nat -> eR) :
  dec_chain f ->
  upper_bound a f ->
  infimum 0 f ->
  supremum a (fun i => a - f i).
Proof.
  intros Hch Ha H0; split.
  - intro; eRauto.
  - intros x Hx; simpl.
    unfold upper_bound in Hx; simpl in Hx.
    destruct H0 as [Hlb Hglb]; simpl in *.
    assert (Haxf: lower_bound (a - x) f).
    { intro i; simpl.
      apply eRplus_le_minus.
      rewrite eRplus_comm.
      apply eRminus_le_plus; auto. }
    apply Hglb in Haxf.
    apply eRminus_le_plus in Haxf; rewrite eRplus_0_l in Haxf; auto.
Qed.

Lemma geometric_series_supremum_1 (r : eR) :
  r < 1 ->
  supremum (1 / (1 - r)) (geometric_series 1 r).
Proof.
  intro Hr.
  replace (geometric_series 1 r) with (fun n => (1 - r ^ n) / (1 - r)).
  2: { ext i; rewrite geometric_series_sum; auto. }
  replace (fun n : nat => (1 - r ^ n) / (1 - r)) with
    (fun n : nat => 1 / (1 - r) - r ^ n / (1 - r)).
  2: { ext i; rewrite eRdiv_minus_distr; eRauto.
       intro HC. symmetry in HC; apply eRminus_eq_plus in HC; eRauto.
       rewrite eRplus_0_r in HC; subst.
       inv Hr; lra. }
  apply infimum_0_minus_supremum.
  { intro i; simpl.
    unfold eRdiv.
    rewrite eRmult_assoc.
    apply eRmult_le_1_le; eRauto. }
  { intro i; simpl.
    apply eRle_div.
    apply eRpow_le_1; eRauto. }
  replace (fun i : nat => r ^ i / (1 - r)) with
    (fun i : nat => / (1 - r) * r ^ i).
  2: { ext i; rewrite eRmult_comm; reflexivity. }
  replace 0 with (/ (1 - r) * 0) by eRauto.
  apply infimum_scalar.
  { unfold eRinv, eRminus; simpl.
    destruct r as [r|]; simpl; inv Hr.
    destruct (Rle_dec r 1); simpl.
    - destr.
      + lra.
      + intro HC; inv HC.
    - lra. }
  { apply converges_infimum.
    - intro i; simpl.
      apply eRmult_le_1_le; eRauto.
    - intro i; intro HC; apply eRpow_infty_inv in HC; subst; inv Hr.
    - apply pow_seq_converges; auto. }
Qed.

Lemma geometric_series_scalar a r  i:
  geometric_series a r i = a * geometric_series 1 r i.
Proof.
  revert a r; induction i; intros a r; simpl.
  { eRauto. }
  rewrite IHi, eRmult_1_l, eRmult_plus_distr_l; reflexivity.
Qed.

Lemma geometric_series_supremum (a r : eR) :
  r < 1 ->
  supremum (a / (1 - r)) (geometric_series a r).
Proof.
  intro Hr.
  replace (geometric_series a r) with (fun i => a * geometric_series 1 r i).
  2: { ext i; rewrite <- geometric_series_scalar; reflexivity. }
  unfold eRdiv.
  apply supremum_scalar.
  replace (/ (1 - r)) with (1 / (1 - r)) by eRauto.
  apply geometric_series_supremum_1; auto.
Qed.

Corollary geometric_series_sup (a r : eR) :
  r < 1 ->
  sup (geometric_series a r) = a / (1 - r).
Proof.
  intro Hr; apply equ_eR, supremum_sup, geometric_series_supremum; auto.
Qed.
