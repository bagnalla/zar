(** * Real number facts and definitions. *)

From Coq Require Import
  RelationClasses
  Lra
  Basics
  Lia
  Reals
  ClassicalChoice
.

Local Open Scope program_scope.
Local Open Scope R_scope.

From zar Require Import
  misc
  order
  tactics
.

Local Open Scope order_scope.

(* Sequence g converges to limit point lim. *)
Definition converges_R (g : nat -> R) (lim : R) :=
  forall eps, 0 < eps -> exists n0, forall n, (n0 <= n)%nat -> Rabs (lim - g n) < eps.

#[global]
  Program Instance OType_R : OType R :=
  { leq := Rle }.
Next Obligation.
  constructor; unfold Reflexive, Transitive; intros; lra.
Qed.

Lemma R_bounded_complete {A} `{Inhabited A} (f : A -> R) :
  bounded_above f ->
  exists s : R, supremum s f.
Proof.
  intros H0.
  generalize (completeness_weak (fun r => exists n, f n = r)).
  destruct H0 as [ub H0]; intro Hcomplete.
  assert (H2: bound (fun r => exists n, f n = r)).
  { exists ub; intros x [n H2]; subst; apply H0. }
  apply Hcomplete in H2.
  { destruct H2 as [m H2]; exists m.
    destruct H2 as [H2 H3]; split.
    - intro i; apply H2; exists i; reflexivity.
    - intros x Hub; simpl; apply H3; intros i [n H4]; subst; apply Hub. }
  destruct H; exists (f el), el; reflexivity.
Qed.

Lemma dec_chain_opp_chain (f : nat -> R) :
  dec_chain f ->
  chain (Ropp ∘ f).
Proof.
  unfold compose, dec_chain, chain.
  intros H0 i.
  unfold leq in *; simpl in *.
  specialize (H0 i); lra.
Qed.

Lemma supremum_opp_infimum {A} (s : R) (f : A -> R) :
  supremum s (Ropp ∘ f) ->
  infimum (- s) f.
Proof.
  unfold supremum, infimum, upper_bound, lower_bound, compose, leq; simpl.
  intros [Hub Hlub]; split.
  - intro i; specialize (Hub i); lra.
  - intros x Hlb.
    specialize (Hlub (- x)).
    cut (s <= - x); try lra.
    apply Hlub; intro i; specialize (Hlb i); lra.
Qed.

Lemma infimum_opp_supremum {A} (s : R) (f : A -> R) :
  infimum s (Ropp ∘ f) ->
  supremum (- s) f.
Proof.
  unfold supremum, infimum, upper_bound, lower_bound, compose, leq; simpl.
  intros [Hlb Hglb]; split.
  - intro i; specialize (Hlb i); lra.
  - intros x Hub.
    specialize (Hglb (- x)).
    cut (- x <= s); try lra.
    apply Hglb; intro i; specialize (Hub i); lra.
Qed.

Lemma R_eq_dec (a b : R) :
  {a = b} + {a <> b}.
Proof.
  destruct (Rlt_le_dec a b).
  - right; lra.
  - destruct (Rlt_le_dec b a).
    + right; lra.
    + left; lra.
Qed.

Lemma Rle_leq (a b : R) :
  a ⊑ b ->
  a <= b.
Proof. auto. Qed.

Definition Req_bool (r1 r2 : R) : bool :=
  if R_eq_dec r1 r2 then true else false.

Lemma Req_bool_spec (r1 r2 : R) : Bool.reflect (r1 = r2) (Req_bool r1 r2).
Proof.
  unfold Req_bool; destruct (R_eq_dec r1 r2); constructor; auto.
Qed.

Lemma Rle_Rdiv a b c:
  0 < a ->
  a * b <= c ->
  b <= c / a.
Proof.
  intros Ha H; apply Rmult_le_reg_r with a; auto.
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l; lra.
Qed.

Lemma supremum_sum_R (f g : nat -> R) (a b : R) :
  chain f ->
  chain g ->
  supremum a f ->
  supremum b g ->
  supremum (a + b) (fun i => f i + g i).
Proof.
  intros Hf Hg [Ha Ha'] [Hb Hb']; split.
  - intro i; simpl in *.
    apply Rplus_le_compat.
    + apply Ha.
    + apply Hb.
  - intros x Hx; simpl in *.
    unfold upper_bound in Hx; simpl in *.
    destruct (Rle_dec (a + b) x); auto.
    assert (x < a + b) by lra; clear n.
    exfalso.
    assert (x - b < a) by lra.
    assert (upper_bound (x - b) f).
    { intro i; simpl.
      cut (b <= x - f i); try lra.
      apply Hb'.
      intro j; simpl.
      cut (f i + g j <= x); try lra.
      destruct (dec_le i j).
      - apply Rle_trans with (f j + g j).
        { apply Rplus_le_compat_r.
          apply Rle_leq, chain_leq; auto. }
        apply Hx.
      - apply Rle_trans with (f i + g i).
        { apply Rplus_le_compat_l.
          apply Rle_leq, chain_leq; auto; lia. }
        apply Hx. }
    apply Ha' in H1; lra.
Qed.

Lemma converges_opp (f : nat -> R) (a : R) :
  converges_R (Ropp ∘ f) (- a) <-> converges_R f a.
Proof.
  unfold converges_R.
  split; intros H eps Heps; specialize (H eps Heps);
    destruct H as [n0 H]; exists n0; intros n Hle; specialize (H n Hle); unfold compose in H.
  - replace (- a - - f n) with (- (a - f n)) in H by lra.
    rewrite Rabs_Ropp in H; auto.
  - unfold compose.
    replace (-a - - f n) with (f n - a) by lra.
    rewrite Rabs_minus_sym; auto.
Qed.

Lemma supremum_converges_R (f : nat -> R) (a : R) :
  chain f ->
  supremum a f ->
  converges_R f a.
Proof.
  intros Hf Ha eps Heps.
  assert (H: exists n, Rabs (a - f n) < eps).
  { destruct (classic (exists n, Rabs (a - f n) < eps)); auto.
    assert (forall n, eps <= Rabs (a - f n)).
    { intro n; apply not_ex_all_not with (n:=n) in H; try lra. }
    clear H.
    exfalso.
    assert (forall n, eps <= a - f n).
    { intro n; specialize (H0 n).
      rewrite Rabs_right in H0; auto.
      cut (f n <= a); try lra; apply Ha. }
    clear H0.
    assert (upper_bound (a - eps) f).
    { intro i; simpl; specialize (H i); lra. }
    apply Ha in H0; simpl in H0; lra. }
  destruct H as [n0 H].
  exists n0; intros n Hle.
  assert (forall n', a - f n' >= 0).
  { intro n'; cut (f n' <= a); try lra; apply Ha. }
  rewrite Rabs_right in H; auto.
  rewrite Rabs_right; auto.
  cut (a < eps + f n); try lra.
  apply Rlt_le_trans with (eps + f n0); try lra.
  apply Rplus_le_compat_l.
  apply Rle_leq.
  apply chain_leq; auto.
Qed.

Lemma infimum_converges_R (f : nat -> R) (a : R) :
  dec_chain f ->
  infimum a f ->
  converges_R f a.
Proof.
  intros Hf Ha eps Heps.
  replace f with (Ropp ∘ (Ropp ∘ f)) in Ha.
  2: { unfold compose; ext s; lra. }
  apply dec_chain_opp_chain in Hf.
  apply infimum_opp_supremum in Ha.
  apply converges_opp; auto.
  apply supremum_converges_R; auto.
Qed.

Lemma converges_const_sum (f g : nat -> R) (a b c : R) :
  (forall i, f i + g i = c) ->
  converges_R f a ->
  converges_R g b ->
  a + b = c.
Proof.
  intros Hc Ha Hb.
  apply cond_eq; intros eps Heps.
  assert (H: 0 < eps / 2) by lra.
  specialize (Ha _ H).
  specialize (Hb _ H).
  destruct Ha as [n Ha].
  destruct Hb as [m Hb].
  destruct (Nat.leb_spec0 n m).
  - specialize (Ha m l).
    specialize (Hb m (le_n m)).
    specialize (Hc m).
    rewrite <- Hc.
    replace (a + b - (f m + g m)) with ((a - f m) + (b - g m)).
    2: { lra. }
    eapply Rle_lt_trans.
    apply Rabs_triang.
    lra.
  - assert (Hle: (m <= n)%nat) by lia.
    specialize (Ha n (le_n n)).
    specialize (Hb n Hle).
    specialize (Hc n).
    rewrite <- Hc.
    replace (a + b - (f n + g n)) with ((a - f n) + (b - g n)).
    2: { lra. }
    eapply Rle_lt_trans.
    apply Rabs_triang.
    lra.
Qed.

Lemma supremum_infimum_sum_R (f g : nat -> R) (a b c : R) :
  chain f ->
  dec_chain g ->
  (forall i, f i + g i = c) ->
  supremum a f ->
  infimum b g ->
  a + b = c.
Proof.
  intros Hf Hg Heq Ha Hb.
  eapply converges_const_sum; eauto.
  - apply supremum_converges_R; auto.
  - apply infimum_converges_R; auto.
Qed.

Lemma upper_bound_Ropp_lower_bound {A} (a : R) (f : A -> R) :
  upper_bound (-a) (Ropp ∘ f) <->
    lower_bound a f.
Proof.
  unfold upper_bound, lower_bound, compose; simpl.
  split; intros Hub y; specialize (Hub y); lra.
Qed.

Lemma converges_increasing_ub (g : nat -> R) (lim : R) :
  (forall i, g i <= g (S i)) ->
  converges_R g lim ->
  upper_bound lim g.
Proof.
  unfold converges_R.
  intros Hle Hc n; simpl.
  destruct (Rlt_le_dec lim (g n)); auto.
  set (eps := g n - lim).
  assert (0 < eps).
  { unfold eps; lra. }
  specialize (Hc eps H); destruct Hc as [n0 Hc].
  specialize (Hc (max n n0) (Nat.le_max_r _ _)).
  rewrite Rabs_minus_sym in Hc.
  assert (H0: forall m, (n <= m)%nat -> g n <= g m).
  { intros m Hle'; induction m.
    - inversion Hle'; lra.
    - destruct (Nat.eqb_spec n (S m)); subst.
      + lra.
      + assert (n <= m)%nat. lia.
        apply IHm in H0; eapply Rle_trans; eauto. }
  assert (H1: g n <= g (max n n0)).
  { apply H0. apply Nat.le_max_l. }
  rewrite Rabs_pos_eq in Hc.
  - unfold eps in Hc; lra.
  - lra.
Qed.

Lemma converges_decreasing_lb (g : nat -> R) (lim : R) :
  (forall i, g i >= g (S i)) ->
  converges_R g lim ->
  lower_bound lim g.
Proof.
  intros H0 H1.
  apply converges_opp in H1.
  apply upper_bound_Ropp_lower_bound.
  apply converges_increasing_ub; auto.
  intro i; unfold compose; specialize (H0 i); lra.
Qed.

Lemma converges_increasing_le_ub (g : nat -> R) (lim : R) :
  converges_R g lim ->
  forall ub, upper_bound ub g -> lim <= ub.
Proof.
  unfold upper_bound; simpl; unfold converges_R.
  intros Hc ub Hub; destruct (Rlt_le_dec ub lim); auto.
  set (eps := lim - ub).
  assert (Heps: 0 < eps).
  { unfold eps; lra. }
  specialize (Hc eps Heps); destruct Hc as [n0 Hc].
  specialize (Hc n0 (Nat.le_refl _)); specialize (Hub n0).
  unfold eps in Hc; rewrite Rabs_pos_eq in Hc; lra.
Qed.

Lemma converges_decreasing_ge_lb (g : nat -> R) (lim : R) :
  converges_R g lim ->
  forall lb, lower_bound lb g -> lb <= lim.
Proof.
  intros Hlim lb Hlb.
  apply upper_bound_Ropp_lower_bound in Hlb.
  apply converges_opp in Hlim.
  eapply converges_increasing_le_ub in Hlb; eauto.
  lra.
Qed.

(* If g is monotonically increasing and converges to lim, then lim is
   the supremum of g. *)
Lemma converges_infimum_R (g : nat -> R) (lim : R) :
  (forall i, g i >= g (S i)) ->
  converges_R g lim ->
  infimum lim g.
Proof.
  unfold converges_R.
  intros Hc. split.
  - apply converges_decreasing_lb; auto.
  - apply converges_decreasing_ge_lb; auto.
Qed.

Lemma supremum_scalar_R {A} `{Inhabited A} (f : A -> R) (a c : R) :
  0 <= c ->
  supremum a f ->
  supremum (c * a) (fun i => c * f i).
Proof.
  destruct (Req_dec c 0); subst.
  { intros _ _.
    replace (fun i => 0 * f i) with (fun _ : A => 0).
    { rewrite Rmult_0_l; apply supremum_const. }
    ext i; lra. }
  intros Hle [Hub Hlub]; split.
  - intro i; simpl.
    cut (f i <= a); try nra.
    apply Hub.
  - intros x Hx; simpl.
    unfold upper_bound in *; simpl in *.
    cut (c * / c * a <= x * /c).
    { intro H1; eapply Rmult_le_reg_r.
      2: { rewrite Rmult_assoc, (@Rmult_comm a _), <- Rmult_assoc; apply H1. }
      apply Rinv_0_lt_compat; lra. }
    rewrite Rinv_r; auto.
    rewrite Rmult_1_l; apply Hlub.
    intro i; specialize (Hx i).
    eapply Rmult_le_reg_l with (r:=c); try lra.
    rewrite <- Rmult_assoc, (@Rmult_comm c x), Rmult_assoc, Rinv_r; lra.
Qed.

Definition pow_sequence (a : R) (n : nat) : R := pow a n.

Lemma archimedean (r : R) :
  exists n, (r < INR n)%R.
Proof.
  destruct (Rlt_le_dec 0 r).
  - assert (Hlt: (0 < / r)%R).
    { apply Rinv_0_lt_compat; auto. }
    generalize (archimed_cor1 (/ r) Hlt).
    intros [n [H Hnz]]; exists n.
    rewrite <- Rinv_inv, <- (Rinv_inv r); try lra.
    apply Rinv_lt_contravar; auto.
    apply Rmult_lt_0_compat; auto.
    apply Rinv_0_lt_compat.
    replace 0%R with (INR 0) by reflexivity.
    apply lt_INR; auto.
  - exists (S O); eapply Rle_lt_trans; eauto.
    replace 0%R with (INR 0) by reflexivity.
    apply lt_INR; lia.
Qed.

Lemma ln_neg (a : R) :
  (0 < a)%R ->
  (a < 1)%R ->
  (ln a < 0)%R.
Proof.
  intro Hlt.
  replace 0%R with (ln 1).
  2: apply ln_1.
  apply ln_increasing; auto.
Qed.

Lemma pow_sequence_converges :
  forall a : R,
    (0 < a)%R -> (a < 1)%R ->
    forall eps : R, (0 < eps)%R -> exists n0, forall n, (n0 <= n)%nat -> (pow a n < eps)%R.
Proof.
  intros a H0 H1 eps Heps.
  generalize (archimedean (/ ln a * ln eps)); intros [n0 H2].
  exists n0; intros n Hle.
  apply ln_lt_inv; auto.
  { apply pow_lt; auto. }
  rewrite ln_pow; auto.
  apply Rmult_lt_reg_l with (r := Ropp (Rinv (ln a))%R).
  { rewrite <- Rinv_opp.
    apply Rinv_0_lt_compat, Ropp_0_gt_lt_contravar, Rlt_gt, ln_neg; auto. }
  rewrite 2!Ropp_mult_distr_l_reverse.
  apply Ropp_lt_contravar.
  replace (INR n * ln a)%R with (ln a * INR n)%R.
  2: { apply Rmult_comm. }
  rewrite <- Rmult_assoc.
  replace (/ ln a * ln a)%R with 1%R.
  2: { field; apply ln_neq_0; lra. }
  rewrite Rmult_1_l.
  apply Rlt_le_trans with (INR n0); auto.
  apply le_INR; auto.
Qed.

Lemma pow_sequence_converges' :
  forall a : R,
    (0 < a)%R -> (a < 1)%R ->
    converges_R (pow_sequence a) 0.
Proof.
  intros a H0 H1 eps Heps.
  generalize (pow_sequence_converges a H0 H1 eps Heps); intros [n0 Hn].
  exists n0; intros n Hle.
  apply Hn in Hle.
  rewrite Rabs_minus_sym.
  rewrite Rminus_0_r.
  unfold pow_sequence.
  rewrite Rabs_pos_eq; auto.
  apply pow_le; lra.
Qed.

Lemma Rmult_le_1_le a b :
  a <= 1 ->
  0 <= b ->
  a * b <= b.
Proof. nra. Qed.

Lemma Rminus_0_le a b :
  b <= a ->
  0 <= a - b.
Proof. lra. Qed.

Lemma Rle_not_eq_Rlt a b :
  a <= b ->
  b <> a ->
  a < b.
Proof. lra. Qed.
