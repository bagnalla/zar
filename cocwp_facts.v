(** * Properties of cocwp (cwp on cotrees). *)

Set Implicit Arguments.

From Coq Require Import
  Basics
  QArith
  Lra
  Equivalence
  Reals
.

Local Open Scope equiv_scope.
Local Open Scope program_scope.

From zar Require Import
  aCPO
  cocwp
  cotree
  cpGCL
  cpo
  cwp
  geometric_series
  misc
  order
  R
  eR
  tactics
  tree
  tcwp
  tcwp_facts
.

Local Open Scope eR_scope.
Local Open Scope order_scope.

Create HintDb cotcwp.

Lemma chain_cotree_loop_approx {A} (x : A) (e : A -> bool)
  (g : A -> cotree bool (unit + A))
  (f : A -> cotree bool (unit + A)) :
  chain (cotree_loop_approx x e g f).
Proof.
  unfold cotree_loop_approx, cotree_loop_F.
  intro i.
  revert x e g f.
  induction i; simpl; intros x e g f.
  - destruct (e x); try reflexivity; constructor.
  - destruct (e x); try reflexivity; apply cotree_le_bind.
    intros [[]|a]; try reflexivity; constructor; apply IHi.
Qed.

(** Example of Proper_co followed by induction on atree. *)
Lemma cotree_bind_map_sum t g :
  cotree_bind (cotree_map inr t)
    (fun lr : St + (unit + St) => match lr with
                               | inl j => cotau (g j)
                               | inr x => coleaf x
                               end) = t.
Proof.
  apply cotree_ext, equ_cotree_eq.
  replace t with (co inj t) by apply co_inj_t.
  unfold cotree_bind, cotree_map.
  rewrite co_co''; eauto with cotree order.
  apply Proper_co'.
  { apply monotone_compose; eauto with cotree order aCPO.
    apply monotone_co; eauto with cotree order. }
  { apply Proper_inj. }
  2: { rewrite co_inj_t; reflexivity. }
  unfold compose.
  apply equ_arrow; intro a.
  unfold atree_cotree_map, atree_cotree_bind, cofold; simpl.
  induction a; unfold compose; simpl.
  - rewrite co_fold_bot; reflexivity.
  - rewrite co_fold_leaf; try reflexivity; constructor.
  - rewrite co_fold_tau; auto with cotree order;
      try solve [intros; constructor].
    apply cotree_eq_equ; constructor; apply equ_cotree_eq, IHa.
  - rewrite co_fold_node; auto with cotree order;
      try solve [intros; constructor].
    apply cotree_eq_equ; constructor; intro b; apply equ_cotree_eq, H.
Qed.

Lemma to_cotree_open_to_cotree'' (t : tree) :
  to_cotree_open t = to_cotree'' t.
Proof.
  induction t; simpl; auto.
  - f_equal; ext b; apply H.
  - unfold cotree_loop, cotree_iter, iter.
    apply cotree_ext, equ_cotree_eq.
    rewrite dsup_apply.
    2: { apply chain_directed, chain_iter_n'.
         - unfold cotree_loop_F; intro st; destruct (b st); constructor.
         - apply monotone_cotree_iter_F. }
    apply eq_equ; f_equal; ext i.
    unfold cotree_loop_approx.
    apply cotree_ext, equ_cotree_eq.
    revert s.
    apply equ_arrow.
    apply iter_n_eq.
    + intros f g Hfg.
      unfold cotree_loop_F, cotree_iter_F.
      apply equ_arrow; intro s; destruct (b s); unfold compose.
      * apply eq_equ; f_equal; auto.
        rewrite cotree_bind_assoc.
        f_equal; auto.
        ext x; destruct x; auto; rewrite cotree_bind_leaf.
        { reflexivity. }
        apply cotree_ext; constructor; apply equ_cotree_eq, equ_arrow; auto.
      * rewrite cotree_bind_map_sum, H0; reflexivity.
    + apply equ_arrow; intro s; destruct (b s); reflexivity.
Qed.

Lemma iid_F_cotree_iter_F {A} (a : cotree bool (unit + A)) (b : cotree bool A) :
  iid_F a b = cotree_iter_F (const a) (const b) tt.
Proof. reflexivity. Qed.

Lemma continuous_iid_F {A} (t : cotree bool (unit + A)) :
  continuous (iid_F t).
Proof.
  intros ch Hch s Hs.
  rewrite iid_F_cotree_iter_F.
  unfold compose.
  replace (fun x => iid_F t (ch x)) with
    (fun x => cotree_iter_F (const t) (const (ch x)) tt).
  2: { ext i; rewrite iid_F_cotree_iter_F; reflexivity. }
  set (ch' := (fun t' => cotree_iter_F (const t) (const t')) ∘ ch).
  replace (fun x : nat => cotree_iter_F (const t) (const (ch x)) tt) with
    (fun i => ch' i tt) by reflexivity.
  apply apply_supremum.
  apply continuous_cotree_iter_F.
  - unfold const.
    intros i j; destruct (Hch i j) as [k [Hk Hk']].
    exists k; split; intros []; auto.
  - unfold const.
    split.
    + intros i []; apply Hs.
    + intros x Hx []; apply Hs; intro i; apply Hx.
Qed.

#[global]
  Instance monotone_btwp {A} (f : A -> eR) : Proper (leq ==> leq) (btwp f).
Proof.
  apply monotone_fold.
  - intros; eRauto.
  - apply monotone_id.
  - intros g g' Hg; simpl.
    apply eRle_div, eRplus_le_compat; apply Hg.
Qed.
#[global] Hint Resolve monotone_btwp : cotcwp.

Lemma fold_avg_bounded {A} (f : A -> eR) (t : atree bool A) :
  bounded f 1 ->
  fold 1 f id (fun k : bool -> eR => (k false + k true) / 2) t ⊑ 1.
Proof.
  revert f; induction t; intros f Hf; simpl; eRauto.
  unfold compose.
  apply eRmult_le_reg_r with (r:=2); eRauto.
  unfold eRdiv.
  rewrite eRmult_assoc.
  rewrite eRinv_l; eRauto.
  etransitivity.
  { apply eRplus_le_compat; apply H; auto. }
  constructor; lra.
Qed.    

Lemma monotone_avg : monotone (fun k : bool -> eR => (k false + k true) / 2).
Proof.
  intros f g Hfg; simpl.
  apply eRle_div, eRplus_le_compat; apply Hfg.
Qed.

#[global]
  Instance antimonotone_btwlp {A} (f : A -> eR) {Hf: bounded f 1}
  : Proper (leq ==> flip leq) (btwlp f).
Proof.
  apply antimonotone_fold.
  - intro a; apply fold_avg_bounded; auto.
  - apply monotone_id.
  - apply monotone_avg.
Qed.
#[global] Hint Resolve antimonotone_btwlp : cotcwp.

Corollary continuous_cotwp {A} (f : A -> eR) : continuous (cotwp f).
Proof. apply continuous_co, monotone_btwp. Qed.
#[global] Hint Resolve continuous_cotwp : cotcwp.

Corollary cocontinuous_cotwlp {A} (f : A -> eR) :
  bounded f 1 ->
  cocontinuous (cotwlp f).
Proof. intro Hf; apply cocontinuous_coop, antimonotone_btwlp; auto. Qed.
#[global] Hint Resolve cocontinuous_cotwlp : cotcwp.

Lemma wcontinuous_avg : wcontinuous (fun k : bool -> eR => (k false + k true) / 2).
Proof.
  intros ch Hch s Hs; unfold compose.
  unfold eRdiv.
  rewrite eRmult_comm.
  replace (fun x : nat => (ch x false + ch x true) * / 2) with
    (fun i => / 2 * (ch i false + ch i true)).
  2: { ext i; apply eRmult_comm. }
  apply supremum_scalar.
  apply supremum_sum.
  { intro i; apply Hch. }
  { intro i; apply Hch. }
  { apply apply_supremum; auto. }
  { apply apply_supremum; auto. }
Qed.

Lemma dec_wcontinuous_avg : dec_wcontinuous (fun k : bool -> eR => (k false + k true) / 2).
Proof.
  intros ch Hch s Hs; unfold compose.
  unfold eRdiv.
  rewrite eRmult_comm.
  replace (fun x : nat => (ch x false + ch x true) * / 2) with
    (fun i => / 2 * (ch i false + ch i true)).
  2: { ext i; apply eRmult_comm. }
  apply infimum_scalar.
  { simpl; destr; try congruence; lra. }
  apply infimum_sum.
  { intro i; apply Hch. }
  { intro i; apply Hch. }
  { apply apply_infimum; auto. }
  { apply apply_infimum; auto. }
Qed.

(** Computation lemmas for cotwp. *)
Lemma cotwp_bot {A} (f : A -> eR) :
  cotwp f cobot = 0.
Proof.
  apply equ_eR.
  unfold cotwp, btwp.
  rewrite co_fold_bot; reflexivity.
Qed.

Lemma cotwp_leaf {A} (f : A -> eR) (x : A) :
  cotwp f (coleaf x) = f x.
Proof.
  apply equ_eR.
  unfold cotwp, btwp.
  rewrite co_fold_leaf; eRauto.
Qed.

Lemma cotwp_tau {A} (f : A -> eR) (t : cotree bool A) :
  cotwp f (cotau t) = cotwp f t.
Proof.
  apply equ_eR.
  unfold cotwp, btwp.
  rewrite co_fold_tau; eRauto.
  { apply continuous_id. }
  { apply monotone_avg. }
Qed.

Lemma cotwp_node {A} (f : A -> eR) (k : bool -> cotree bool A) :
  cotwp f (conode k) = (cotwp f (k false) + cotwp f (k true)) / 2.
Proof.
  apply equ_eR.
  unfold cotwp, btwp.
  rewrite co_fold_node; eRauto.
  { apply monotone_id. }
  { apply wcontinuous_avg. }
Qed.

(** An essential lemma about the co-semantics. Proof by using
    co_compose to turn the LHS into a single comorphism, then
    Proper_co to show equality of LHS and RHS. *)
Lemma cotwp_bind {A B} (f : B -> eR) (t : cotree bool A) (k : A -> cotree bool B) :
  cotwp f (cotree_bind t k) = cotwp (cotwp f ∘ k) t.
Proof.
  unfold cotwp.
  unfold cotree_bind.
  apply equ_eR.
  set (g := btwp f).
  set (h := atree_cotree_bind k).
  assert (Hg: wcontinuous (co g)).
  { apply continuous_wcontinuous, continuous_co, monotone_btwp. }
  assert (Hh: monotone h).
  { apply monotone_atree_cotree_bind. }
  generalize (@co_co (cotree bool A) (atree bool A) (cotree bool B)
                eR _ _ _ _ _ _ _ _ _ _ h (co g) Hh Hg).
  intro H.
  apply equ_arrow with (x:=t) in H.
  unfold compose in H; rewrite H; clear H.
  revert t.
  apply equ_arrow.
  apply Proper_co.
  { replace (fun x : atree bool A => co g (h x)) with (co g ∘ h) by reflexivity.
    apply monotone_compose.
    - apply monotone_atree_cotree_bind.
    - apply monotone_co, monotone_btwp. }
  { apply monotone_btwp. }
  apply equ_arrow.
  intro t.
  apply equ_eR.
  unfold g, h in *; clear g h Hg Hh.
  unfold compose.
  revert f k.
  induction t; intros f k; simpl.
  - apply cotwp_bot.
  - reflexivity.
  - apply equ_eR.
    unfold btwp, atree_cotree_bind, cofold in *; simpl.
    rewrite co_fold_tau; eRauto.
    { rewrite IHt; reflexivity. }
    { apply continuous_id. }
    { apply monotone_avg. }
  - apply equ_eR.
    unfold btwp, atree_cotree_bind, cofold in *; simpl.
    rewrite co_fold_node; eRauto.
    { apply equ_eR; unfold compose; rewrite 2!H; reflexivity. }
    { apply monotone_id. }
    { apply wcontinuous_avg. }
Qed.

(** Computation lemmas for cotwlp. *)
Lemma cotwlp_bot {A} (f : A -> eR) :
  cotwlp f cobot = 1.
Proof.
  apply equ_eR.
  unfold cotwlp, btwlp.
  rewrite coop_fold_bot; reflexivity.
Qed.

Lemma cotwlp_leaf {A} (f : A -> eR) (x : A) :
  bounded f 1 ->
  cotwlp f (coleaf x) = f x.
Proof.
  intro Hf; apply equ_eR.
  unfold cotwlp, btwlp.
  rewrite coop_fold_leaf; eRauto; apply Hf.
Qed.

Lemma cotwlp_tau {A} (f : A -> eR) (t : cotree bool A) :
  bounded f 1 ->
  cotwlp f (cotau t) = cotwlp f t.
Proof.
  intro Hf; apply equ_eR.
  unfold cotwlp, btwlp.
  rewrite coop_fold_tau; eRauto.
  { apply dec_continuous_id. }
  { apply monotone_avg. }
  intros a; apply fold_avg_bounded; auto.
Qed.

Lemma cotwlp_node {A} (f : A -> eR) (k : bool -> cotree bool A) :
  bounded f 1 ->
  cotwlp f (conode k) = (cotwlp f (k false) + cotwlp f (k true)) / 2.
Proof.
  intro Hf; apply equ_eR.
  unfold cotwlp, btwlp.
  rewrite coop_fold_node; eRauto.
  { apply monotone_id. }
  { apply dec_wcontinuous_avg. }
  { intro a; apply fold_avg_bounded; auto. }
  { unfold eRdiv, eRmult; simpl.
    destruct (R_eq_dec 2 0); try lra.
    constructor; lra. }
Qed.

Corollary btwlp_bounded {A} (f : A -> eR) (t : atree bool A) :
  bounded f 1 ->
  btwlp f t ⊑ 1.
Proof. apply fold_avg_bounded. Qed.

(** See above. *)
Lemma cotwlp_bind {A B} (f : B -> eR) (t : cotree bool A) (k : A -> cotree bool B) :
  bounded f 1 ->
  cotwlp f (cotree_bind t k) = cotwlp (cotwlp f ∘ k) t.
Proof.
  intro Hf.
  unfold cotwlp.
  unfold cotree_bind.
  apply equ_eR.
  set (g := btwlp f).
  set (h := atree_cotree_bind k).
  assert (Hg: cocontinuous (coop g)).
  { apply cocontinuous_coop, antimonotone_btwlp; auto. }
  assert (Hh: monotone h).
  { apply monotone_atree_cotree_bind. }
  generalize (@co_coop (cotree bool A) (atree bool A) (cotree bool B)
                eR _ _ _ _ _ _ _ _ _ _ h (coop g) Hh Hg).
  intro H.
  apply equ_arrow with (x:=t) in H.
  unfold compose in H; rewrite H; clear H.
  revert t.
  apply equ_arrow.
  apply Proper_coop.
  { replace (fun x : atree bool A => co g (h x)) with (co g ∘ h) by reflexivity.
    intros a b Hab; unfold flip.
    apply antimonotone_coop; auto.
    apply antimonotone_btwlp; auto. }
  { apply antimonotone_btwlp.
    intro x; unfold compose, coop.
    apply leq_eRle.
    unfold g.
    apply ge_inf with O.
    apply btwlp_bounded; auto. }
  apply equ_arrow.
  intro t.
  apply equ_eR.
  unfold g, h in *; clear g h Hg Hh.
  unfold compose.
  revert Hf.
  revert f k.
  induction t; intros f k Hf; simpl.
  - apply cotwlp_bot.
  - reflexivity.
  - apply equ_eR.
    unfold btwlp, atree_cotree_bind, cofold in *; simpl.
    rewrite coop_fold_tau; eRauto.
    { rewrite IHt; auto; reflexivity. }
    { apply dec_continuous_id. }
    { apply monotone_avg. }
    { intro; apply fold_avg_bounded; auto. }
  - apply equ_eR.
    unfold btwlp, atree_cotree_bind, cofold in *; simpl.
    rewrite coop_fold_node; eRauto.
    { apply equ_eR; unfold compose; rewrite 2!H; auto; reflexivity. }
    { apply monotone_id. }
    { apply dec_wcontinuous_avg. }
    { intro; apply fold_avg_bounded; auto. }
    { unfold eRdiv, eRmult; simpl.
      destruct (R_eq_dec 2 0); try lra.
      constructor; lra. }
Qed.

(** twp_ coincides with cotwp. *)
Theorem twp_cotwp (fl : bool) (t : tree) (f : St -> eR) :
  tree_unbiased t ->
  twp_ fl t f = cotwp (cotuple (const (if fl then 1 else 0)) f) (to_cotree'' t).
Proof.
  revert fl f; induction t; intros fl f Hub; simpl; inv Hub.
  - rewrite cotwp_leaf; reflexivity.
  - rewrite cotwp_leaf; reflexivity.
  - rewrite 2!H; auto.
    replace (Q2eR q) with (1/2).
    2: { rewrite H2, Q2eR_one_half; reflexivity. }
    rewrite cotwp_node, <- eRplus_combine_fract, eRplus_comm; f_equal.
    + rewrite eRminus_1_2; apply eRmult_half_div_2.
    + apply eRmult_half_div_2.
  - unfold iter; rewrite sup_apply_eR; apply equ_eR.
    apply equ_eR; rewrite continuous_sup_eR.
    2: { apply chain_directed, chain_cotree_loop_approx. }
    2: { apply continuous_cotwp. }
    f_equal; ext i.
    unfold compose, cotree_loop_approx, loop_F, cotree_loop_F.
    revert s; induction i; intro s; simpl.
    + unfold const; rewrite cotwp_bot; reflexivity.
    + destruct (b s); auto.
      rewrite cotwp_bind, H; auto.
      f_equal; ext s'; destruct s'.
      * simpl; unfold compose; rewrite cotwp_leaf; reflexivity.
      * unfold compose; simpl.
        rewrite IHi, cotwp_tau; auto.
Qed.

Corollary twp_cowp (t : tree) (f : St -> eR) :
  tree_unbiased t ->
  twp t f = cowp f (to_cotree_open t).
Proof. rewrite to_cotree_open_to_cotree''; apply twp_cotwp. Qed.

(** twlp coincides with cowlp. *)
Theorem twlp_cotwlp (fl : bool) (t : tree) (f : St -> eR) :
  tree_unbiased t ->
  bounded f 1 ->
  twlp_ fl t f = cotwlp (cotuple (const (if fl then 1 else 0)) f) (to_cotree'' t).
Proof.
  revert fl f; induction t; intros fl f Hub Hf; simpl; inv Hub.
  - rewrite cotwlp_leaf; try reflexivity.
    intros []; destruct fl; unfold const; simpl; eRauto.
  - rewrite cotwlp_leaf; try reflexivity.
    intros []; destruct fl; unfold const; simpl; eRauto.
  - rewrite 2!H; auto.
    replace (Q2eR q) with (1/2).
    2: { rewrite H2, Q2eR_one_half; reflexivity. }
    rewrite cotwlp_node, <- eRplus_combine_fract, eRplus_comm; f_equal.
    + rewrite eRminus_1_2; apply eRmult_half_div_2.
    + apply eRmult_half_div_2.
    + intros []; simpl; auto; destruct fl; eRauto.
  - unfold dec_iter; rewrite inf_apply_eR; apply equ_eR.
    apply equ_eR; rewrite cocontinuous_sup_eR.
    2: { apply chain_directed, chain_cotree_loop_approx. }
    2: { apply cocontinuous_cotwlp; intros []; destruct fl; eRauto. }
    f_equal; ext i.
    unfold compose, cotree_loop_approx, loop_F, cotree_loop_F.
    revert s; induction i; intro s; simpl.
    + unfold const; rewrite cotwlp_bot; reflexivity.
    + destruct (b s); auto.
      rewrite cotwlp_bind, H; auto.
      f_equal; ext s'; destruct s'.
      * simpl; unfold compose; rewrite cotwlp_leaf; auto.
        intros []; destruct fl; eRauto.
      * unfold compose; simpl.
        rewrite IHi, cotwlp_tau; auto.
        intros []; destruct fl; eRauto.
      * intro st.
        apply leq_eRle.
        revert st.
        apply leq_arrow.
        apply iter_n_bounded.
        { eRauto. }
        { intros g Hg st; destruct (b st); apply twlp_bounded; auto with tree. }
      * intros []; destruct fl; eRauto.
Qed.

Corollary twlp_cowlp (t : tree) (f : St -> eR) :
  tree_unbiased t ->
  bounded f 1 ->
  twlp t f = cowlp f (to_cotree_open t).
Proof. intros; rewrite to_cotree_open_to_cotree''; apply twlp_cotwlp; auto. Qed.

(** tcwp coincides with cocwp. *)
Theorem tcwp_cotcwp (t : tree) (f : St -> eR) :
  tree_unbiased t ->
  tcwp t f = cocwp f (to_cotree_open t).
Proof.
  intro Ht.
  unfold tcwp, cocwp.
  f_equal.
  - apply twp_cowp; auto.
  - apply twlp_cowlp; auto; intro; eRauto.
Qed.

Lemma cotwp_filter {A} (P : A -> bool) (f : A -> eR) :
  cotwp (fun x => if P x then f x else 0) === cotwp f ∘ cotree_filter P.
Proof.
  unfold cotwp, cotree_filter.
  rewrite co_co; eauto with cotcwp cotree order.
  apply Proper_co; eauto with cotcwp order.
  { apply monotone_compose; eauto with cotree order.
    apply monotone_co; eauto with cotcwp. }
  apply equ_arrow; intro a.
  unfold compose.
  revert P f; induction a; intros P f; simpl.
  - unfold atree_cotree_filter, cofold. simpl.
    unfold btwp; simpl.
    rewrite co_fold_bot.
    reflexivity.
  - unfold btwp; simpl.
    unfold atree_cotree_filter, cofold; simpl.
    destruct (P a).
    + rewrite co_fold_leaf; eRauto.
    + rewrite co_fold_bot; reflexivity.
  - unfold btwp, atree_cotree_filter, cofold in *; simpl.
    unfold id.
    rewrite co_fold_tau; eRauto.
    { apply continuous_id. }
    { apply monotone_avg. }
  - unfold btwp, atree_cotree_filter, cofold in *; simpl.
    unfold id, compose in *.
    rewrite co_fold_node; eRauto.
    { unfold compose; apply equ_eR.
      f_equal; f_equal; apply equ_eR, H. }
    { apply monotone_id. }
    { apply wcontinuous_avg. }
Qed.

Lemma btwp_node {A} (f : A -> eR) (g : bool -> atree bool A) :
  btwp f (anode g) = (btwp f (g false) + btwp f (g true)) / 2.
Proof. reflexivity. Qed.

Lemma btwp_strict {A} (t : atree bool A) :
  btwp (fun _ : A => 0) t = 0.
Proof.
  unfold btwp; induction t; simpl; auto.
  unfold compose; rewrite 2!H; eRauto.
Qed.

Lemma btwlp_costrict {A} (t : atree bool A) :
  btwlp (fun _ : A => 1) t = 1.
Proof.
  unfold btwlp; induction t; simpl; auto.
  unfold compose; rewrite 2!H; eRauto.
  rewrite <- eRplus_combine_fract.
  apply eRplus_half_plus_half.
Qed.

Lemma cotwp_strict {A} :
  cotwp (fun _ : A => 0) = const 0.
Proof.
  symmetry; apply co_unique_ext.
  - apply monotone_btwp.
  - apply continuous_wcontinuous, continuous_const.
  - ext t; rewrite btwp_strict; reflexivity.
Qed.

Lemma cotwlp_costrict {A} :
  cotwlp (fun _ : A => 1) = const 1.
Proof.
  symmetry; apply coop_unique_ext.
  - apply antimonotone_btwlp; intro; reflexivity.
  - apply cocontinuous_const.
  - ext t; rewrite btwlp_costrict; reflexivity.
Qed.

Lemma btwp_cotuple {A B} (t : atree bool (A + B)) (f : A -> eR) (g : B -> eR) :
  btwp (cotuple f g) t = btwp (cotuple f (const 0)) t + btwp (cotuple (const 0) g) t.
Proof.
  revert f g; induction t; intros f g; simpl; eRauto.
  - destruct a; simpl; unfold const; eRauto.
  - rewrite btwp_node.
    rewrite 2!H.
    rewrite 2!btwp_node.
    rewrite <- 5!eRplus_combine_fract.
    set (x := btwp (cotuple f (const 0)) (a false) / 2).
    set (y := btwp (cotuple (const 0) (const 0)) (a false) / 2).
    set (z := btwp (cotuple (const 0) g) (a false) / 2).
    set (w := btwp (cotuple f g) (a true) / 2).
    set (y' := btwp (cotuple f (const 0)) (a true) / 2).
    set (w' := btwp (cotuple (const 0) g) (a true) / 2).
    rewrite <- eRplus_assoc.
    cut (y + w = y' + w').
    { intro Heq; destruct x, y, z, w, y', w';
        compute; auto; inv Heq; apply eR_eq; lra. }
    unfold y, y', w, w'.
    rewrite 2!eRplus_combine_fract.
    replace (cotuple (const 0) (const 0)) with (fun _ : A + B => 0).
    2: { ext ab; destruct ab; reflexivity. }
    rewrite btwp_strict; eRauto.
    rewrite H; reflexivity.
Qed.    

Lemma cotwp_cotuple {A B} (t : cotree bool (A + B)) (f : A -> eR) (g : B -> eR) :
  cotwp (cotuple f g) t = cotwp (cotuple f (const 0)) t + cotwp (cotuple (const 0) g) t.
Proof.
  unfold cotwp, co.
  rewrite <- sup_sum.
  2: { apply monotone_chain.
       - apply monotone_btwp.
       - apply chain_ideal. }
  2: { apply monotone_chain.
       - apply monotone_btwp.
       - apply chain_ideal. }
  f_equal; ext i; unfold compose.
  apply btwp_cotuple.
Qed.

Lemma tie_cotree_iid_tie_cotree {A} :
  @tie_cotree_iid A = @tie_cotree A.
Proof.
  ext ct.
  unfold tie_cotree_iid, tie_cotree, cotree_iter, iter.
  apply cotree_ext, equ_cotree_eq; rewrite dsup_apply.
  2: { apply chain_directed, chain_iter_n';
       eauto with order cotree; constructor. }
  apply eq_equ; f_equal; ext i.
  revert ct; induction i; intros t; simpl; auto.
  unfold iid_F; simpl; unfold cotree_iter_F, const; f_equal.
  ext lr; destruct lr; simpl; auto.
  f_equal; destruct u; apply IHi.
Qed.

Lemma btwp_scalar {A} (c : eR) (f : A -> eR) (t : atree bool A) :
  c * btwp f t = btwp (fun x => c * f x) t.
Proof.
  unfold btwp.
  revert c f; induction t; intros c f; simpl; eRauto.
  unfold compose.
  rewrite <- 2!H.
  rewrite eRmult_eRdiv_assoc, eRmult_plus_distr_l; reflexivity.
Qed.

Lemma cotwp_scalar {A} (c : eR) (f : A -> eR) (t : cotree bool A) :
  c * cotwp f t = cotwp (fun x => c * f x) t.
Proof.
  unfold cotwp, co.
  unfold compose.
  rewrite sup_scalar.
  f_equal; ext i.
  apply btwp_scalar.
Qed.

Lemma btwp_sum {A} (f g : A -> eR) (t : atree bool A) :
  btwp (fun a => f a + g a) t = btwp f t + btwp g t.
Proof.
  unfold btwp.
  revert f; induction t; intros f; simpl; eRauto.
  unfold compose.
  rewrite 2!H,  eRplus_combine_fract.
  rewrite <- 2!eRplus_assoc, eRplus_comm4; reflexivity.
Qed.

Lemma cotwp_sum {A} (f g : A -> eR) (t : cotree bool A) :
  cotwp (fun a => f a + g a) t = cotwp f t + cotwp g t.
Proof.
  symmetry.
  set (h := fun t => cotwp f t + cotwp g t).
  replace (cotwp f t + cotwp g t) with (h t) by reflexivity.
  cut (h = cotwp (fun a => f a + g a)).
  { intros ->; reflexivity. }
  apply co_unique_ext.
  - apply monotone_btwp.
  - unfold h.
    apply wcontinuous_sum;
      apply continuous_wcontinuous, continuous_co, monotone_btwp.
  - clear t.
    ext t.
    rewrite btwp_sum.
    unfold compose, h.
    f_equal; apply co_incl'_ext, monotone_btwp.
Qed.

Lemma cotwp_linear {A} (c : eR) (f g : A -> eR) (t : cotree bool A) :
  cotwp (fun a => c * f a + g a) t = c * cotwp f t + cotwp g t.
Proof. rewrite cotwp_sum, cotwp_scalar; reflexivity. Qed.

Lemma cotree_bind_iid_chain_ {A} t i :
  cotree_bind (iid_chain_ t i)
    (fun x : unit + A => match x with
                      | inl _ => t
                      | inr b => coleaf (inr b)
                      end) =
    cotree_bind t
      (fun x : unit + A => match x with
                        | inl _ => iid_chain_ t i
                        | inr b => coleaf (inr b)
                        end).
Proof.
  revert t; induction i; intro t; simpl.
  { rewrite cotree_bind_leaf.
    replace (fun x : unit + A => match x with
                              | inl _ => coleaf (inl tt)
                              | inr b => coleaf (inr b)
                              end) with
      (@coleaf bool (unit + A)).
    2: { ext lr; destruct lr as [[]|?]; reflexivity. }
    rewrite cotree_bind_id_r; reflexivity. }
  rewrite IHi.
  rewrite cotree_bind_assoc.
  f_equal.
  ext lr; destruct lr as [[]|a]; auto.
  rewrite cotree_bind_leaf; reflexivity.
Qed.

Lemma cotree_bind_iid_chain_snip {A} t i :
  cotree_bind (iid_chain_ t i)
    (fun x : unit + A =>
       match x with
       | inl _ => snip t
       | inr b => coleaf b
       end) =
    cotree_bind t
      (fun x : unit + A =>
         match x with
         | inl _ => snip (iid_chain_ t i)
         | inr b => coleaf b
         end).
Proof.
  replace (fun x : unit + A => match x with
                            | inl _ => snip t
                            | inr b => coleaf b
                            end) with
    (snip ∘ fun x : unit + A => match x with
                             | inl _ => t
                             | inr b => coleaf (inr b)
                             end).
  2: { unfold compose; ext lr; destruct lr; auto; rewrite snip_leaf; auto. }
  rewrite <- snip_bind.
  replace (fun x : unit + A => match x with
                            | inl _ => snip (iid_chain_ t i)
                            | inr b => coleaf b
                            end) with
    (snip ∘ fun x : unit + A => match x with
                             | inl _ => iid_chain_ t i
                             | inr b => coleaf (inr b)
                             end).
  2: { unfold compose; ext lr; destruct lr; auto; rewrite snip_leaf; auto. }
  rewrite <- snip_bind.
  f_equal.
  apply cotree_bind_iid_chain_.
Qed.

Lemma iid_chain_iter_n {A} (t : cotree bool (unit + A)) :
  iid_chain t = iter_n (iid_F' t) cobot.
Proof.
  ext i; revert t; induction i; intro t.
  { unfold iid_chain; simpl; rewrite snip_leaf; reflexivity. }
  unfold iid_chain in *; simpl.
  unfold compose. unfold iid_F' in *.
  unfold snip in *.
  rewrite <- IHi; clear IHi.
  rewrite cotree_bind_assoc.
  etransitivity.
  2: { apply cotree_bind_iid_chain_snip. }
  f_equal.
  ext lr; destruct lr as [[]|a]; simpl; auto.
  rewrite cotree_bind_leaf; reflexivity.
Qed.

Lemma cotwp_cotuple_const_inl {A} a t :
  cotwp (cotuple (fun _ : unit => a) (fun _ : A => 0)) t =
    cotwp (cotuple (const 1) (const 0)) t * a.
Proof.
  rewrite eRmult_comm, cotwp_scalar.
  f_equal; ext lr; destruct lr as [[]|b]; eRauto.
Qed.

Lemma cowp_iid_chain_geometric_series {A}
  (f : A -> eR) (t : cotree bool (unit + A)) (i : nat) :
  cowp f (iid_chain_ t i) = geometric_series (cowp f t) (cofail t) i.
Proof.
  unfold cowp.
  revert f t; induction i; intros f t; simpl.
  { rewrite cotwp_leaf; reflexivity. }
  rewrite <- IHi; clear IHi.
  unfold compose, cotuple, const.
  rewrite cotwp_bind.
  unfold compose.
  replace (fun x : unit + A =>
             cotwp (fun x0 : unit + A => match x0 with
                                      | inl _ => 0
                                      | inr b => f b
                                      end) match x with
               | inl _ => t
               | inr b => coleaf (inr b)
               end) with
    (cotuple (fun _ : unit => cotwp (cotuple (const 0) f) t) f).
  2: { ext lr; destruct lr as [[]|a]; simpl; auto.
       rewrite cotwp_leaf; reflexivity. }
  rewrite cotwp_cotuple.
  rewrite eRplus_comm.
  f_equal.
  replace (fun x : unit + A => match x with
                            | inl _ => 0
                            | inr b => f b
                            end) with
    (cotuple (fun _ : unit => 0) f) by reflexivity.
  revert f t; induction i; intros f t; simpl.
  { eRauto; rewrite cotwp_leaf; reflexivity. }
  rewrite eRmult_comm.
  rewrite eRmult_assoc.
  specialize (IHi f t).
  rewrite eRmult_comm in IHi.
  rewrite <- IHi; clear IHi.
  rewrite cotwp_bind.
  unfold compose.
  rewrite cotwp_scalar.
  f_equal; ext lr; destruct lr as [[]|a]; simpl.
  - apply cotwp_cotuple_const_inl.
  - unfold const; eRauto.
    rewrite cotwp_leaf; reflexivity.
Qed.

Lemma cotwp_iid_chain_geometric_series {A}
  (f : A -> eR) (t : cotree bool (unit + A)) (i : nat) :
  cotwp f (iid_chain t i) = geometric_series (cowp f t) (cofail t) i.
Proof.
  unfold iid_chain.
  unfold snip.
  rewrite cotwp_bind.
  unfold cotuple, const, compose.
  replace (fun x : unit + A => cotwp f match x with
                              | inl _ => cobot
                              | inr b => coleaf b
                              end) with
    (cotuple (fun _ : unit => 0) f).
  2: { ext lr; destruct lr as [[]|a]; simpl; auto.
       - rewrite cotwp_bot; reflexivity.
       - rewrite cotwp_leaf; reflexivity. }
  apply cowp_iid_chain_geometric_series.
Qed.

Lemma cotwp_iter_n_iid_F_iid_F' {A} (f : A -> eR) (t : cotree bool (unit + A)) (i : nat) :
  cotwp f (iter_n (iid_F t) cobot i) = cotwp f (iter_n (iid_F' t) cobot i).
Proof.
  revert f t; induction i; intros f t; simpl; auto.
  unfold iid_F, iid_F' in *.
  rewrite 2!cotwp_bind.
  f_equal.
  ext lr; destruct lr as [[]|a]; simpl; auto.
  unfold compose.
  rewrite cotwp_tau.
  apply IHi.
Qed.

Corollary cotwp_iter_n_geometric_series {A} (f : A -> eR) (t : cotree bool (unit + A)) (i : nat) :
  cotwp f (iter_n (iid_F t) cobot i) = geometric_series (cowp f t) (cofail t) i.
Proof.
  rewrite <- cotwp_iid_chain_geometric_series.
  rewrite cotwp_iter_n_iid_F_iid_F'.
  f_equal; rewrite iid_chain_iter_n; reflexivity.
Qed.

Theorem cotwp_tie_cotree_iid {A} (t : cotree bool (unit + A)) (f : A -> eR) :
  cofail t < 1 -> cotwp f (tie_cotree_iid t) = cowp f t / (1 - cofail t).
Proof.
  intro Hlt.
  unfold tie_cotree_iid.
  unfold cotree_iter.
  unfold iter.
  rewrite continuous_sup_eR; auto with cotcwp.
  2: { apply chain_directed, chain_iter_n'.
       - constructor.
       - apply continuous_monotone, continuous_iid_F. }
  etransitivity.
  2: { apply geometric_series_sup; eRauto. }
  f_equal; ext i.
  unfold compose.
  apply cotwp_iter_n_geometric_series.
Qed.  

Lemma btwp_bounded {A} (f : A -> eR) t ub :
  bounded f ub ->
  btwp f t <= ub.
Proof.
  unfold btwp.
  revert f ub; induction t; intros f ub Hf; simpl; eRauto.
  rewrite <- eRplus_combine_fract.
  replace ub with (ub / 2 + ub / 2) by apply eRplus_half_plus_half.
  apply eRplus_le_compat; apply eRle_div, H; auto.
Qed.

Lemma btwp_btwlp_sum_1 {A} (f : A -> eR) t :
  bounded f 1 ->
  btwp f t + btwlp (fun x : A => 1 - f x) t = 1.
Proof.
  unfold btwp, btwlp.
  revert f; induction t; intros f Hf; simpl.
  - eRauto.
  - eRauto.
  - eRauto.
  - rewrite <- 2!eRplus_combine_fract, <- eRplus_assoc.
    rewrite eRplus_comm4, eRplus_assoc.
    etransitivity.
    2: { apply eRplus_half_plus_half. }
    f_equal; rewrite eRplus_combine_fract; f_equal; apply H; auto.
Qed.

Theorem cotwp_cotwlp_sum_1 {A} (f : A -> eR) (t : cotree bool A) :
  bounded f 1 ->
  cotwp f t + cotwlp (fun x => 1 - f x) t = 1.
Proof.
  intro Hf.
  unfold cotwp, cotwlp.
  unfold co, coop.
  eapply supremum_infimum_sum.
  6: { apply sup_spec. }
  6: { apply inf_spec. }
  { apply chain_f_ideal; eauto with cotcwp order. }
  { apply dec_chain_f_ideal, antimonotone_btwlp; intro; eRauto. }
  { intro i; unfold compose. simpl. unfold flip.
    apply btwp_bounded; eauto. }
  { intro i; unfold compose; simpl; unfold flip.
    apply btwlp_bounded; intro; eRauto. }
  intro i; unfold compose.
  apply btwp_btwlp_sum_1; auto.
Qed.

Corollary cofail_cowlp {A} (t : cotree bool (unit + A)) :
  cofail t = 1 - cowlp (const 1) t.
Proof.
  apply eRplus_eq_minus.
  { eRauto. }
  rewrite eRplus_comm.
  unfold cofail, cowpfail.
  etransitivity.
  2: { eapply cotwp_cotwlp_sum_1 with (f := cotuple (const 1) (const 0)).
       intros []; eRauto. }
  f_equal; unfold cowlp; f_equal.
  ext lr; destruct lr as [[]|s]; eRauto.
Qed.

Lemma cotwlp_bounded {A} (t : cotree bool A) (f : A -> eR) :
  bounded f 1 ->
  cotwlp f t <= 1.
Proof.
  intro Hf; apply leq_eRle, ge_inf with (i:=O), btwlp_bounded; auto.
Qed.

Corollary cowlp_cofail {A} (t : cotree bool (unit + A)) :
  cowlp (const 1) t = 1 - cofail t.
Proof.
  apply eRplus_eq_minus.
  { eRauto. }
  rewrite eRplus_comm.
  apply eRminus_eq_plus.
  { eRauto. }
  - apply cotwlp_bounded; intros [[]|a]; eRauto.
  - apply cofail_cowlp.
Qed.

Lemma cocwp_cotwp_tie_cotree {A} (t : cotree bool (unit + A)) (f : A -> eR) :
  cofail t < 1 ->
  cocwp f t = cotwp f (tie_cotree t).
Proof.
  intro Hlt.
  rewrite <- tie_cotree_iid_tie_cotree.
  rewrite cotwp_tie_cotree_iid; auto.
  unfold cocwp.
  f_equal.
  apply eRplus_eq_minus.
  { eRauto. }
  unfold cofail, cowpfail, cowlp.
  replace (cotuple (const 0) (const 1)) with
    (fun x => 1 - cotuple (fun _ : unit => 1) (fun _ : A => 0) x).
  2: { ext lr; destruct lr; eRauto. }
  apply cotwp_cotwlp_sum_1.
  intros [[]|s]; simpl; eRauto.
Qed.

Theorem cotwp_tie_cotree_to_cotree_open_tcwp (t : tree) (f : St -> eR) :
  tree_unbiased t ->
  twpfail t (const 0) < 1 ->
  cotwp f (tie_cotree (to_cotree_open t)) = tcwp t f.
Proof.
  intros Hub Ht.
  unfold twpfail in Ht.
  rewrite twp_cotwp in Ht; auto.
  rewrite <- to_cotree_open_to_cotree'' in Ht.
  rewrite <- cocwp_cotwp_tie_cotree; auto.
  rewrite tcwp_cotcwp; auto.
Qed.

(** Note: tie_cotree and tie_cotree_iid are the same (see
    tie_cotree_iid_tie_cotree lemma). *)
Corollary cotwp_tie_cotree_iid_wlp {A} (t : cotree bool (unit + A)) (f : A -> eR) :
  0 < cowlp (const 1) t -> cotwp f (tie_cotree_iid t) = cowp f t / cowlp (const 1) t.
Proof.
  intro Hlt; rewrite cowlp_cofail; apply cotwp_tie_cotree_iid.
  rewrite cofail_cowlp.
  apply eRminus_pos_lt; eRauto.
Qed.

Lemma monotone_btwp' {A} (f g : A -> eR) (t : atree bool A) :
  f ⊑ g ->
  btwp f t <= btwp g t.
Proof.
  unfold btwp.
  revert f g; induction t; intros f g Hfg; simpl.
  - reflexivity.
  - apply Hfg.
  - apply IHt; auto.
  - unfold compose.
    rewrite <- 2!eRplus_combine_fract.
    apply eRplus_le_compat; apply eRmult_le_compat_r, H; auto.
Qed.

Lemma monotone_cotwp {A} (f g : A -> eR) (t : cotree bool A) :
  f ⊑ g ->
  cotwp f t <= cotwp g t.
Proof.
  intro Hfg.
  apply leq_eRle.
  unfold cotwp.
  apply ge_dsup.
  { apply monotone_directed.
    - apply monotone_btwp.
    - apply chain_directed, chain_ideal. }
  intro i; unfold compose.
  apply le_dsup with i.
  { apply monotone_directed.
    - apply monotone_btwp.
    - apply chain_directed, chain_ideal. }
  unfold compose.
  apply monotone_btwp'; auto.
Qed.

Theorem markov_inequality {A} (f : A -> eR) (a : eR) (t : cotree bool A) :
  a <> 0 ->
  a <> infty ->
  cotwp (fun x => if eRle_dec a (f x) then 1 else 0) t <= cotwp f t / a.
Proof.
  intros Ha Ha'.
  unfold eRdiv.
  apply eRmult_le_div; auto.
  rewrite cotwp_scalar.
  apply monotone_cotwp.
  intro x.
  destr; eRauto.
Qed.
