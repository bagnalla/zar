(** * Conditional weakest pre-expectation (cwp) semantics for the cpGCL. *)

Set Implicit Arguments.
From Coq Require Import
  Basics
  Nat
  QArith
  Reals
  List
  Lia
  Lra
  Equivalence
.

Local Open Scope program_scope.
Local Open Scope equiv_scope.

From zar Require Import
  cpGCL
  cpo
  misc
  order
  eR
  tactics
.

Local Open Scope order_scope.
Local Open Scope eR_scope.

Create HintDb cwp.

(** [f] is an expectation. *)
Definition expectation {A} : Type := A -> eR.

(** [f] is a bounded expectation (bounded above by constant [b]). *)
Definition bounded {A : Type} (f : A -> eR) (b : eR) := forall x, f x <= b.

Fixpoint loop_approx {A}
  (e : A -> bool) (g : (A -> eR) -> A -> eR) (f : A -> eR) (n : nat) : A -> eR :=
  match n with
  | O => fun st => 0
  | S n' => fun st => if e st then g (loop_approx e g f n') st else f st
  end.

Fixpoint dec_loop_approx {A}
  (e : A -> bool) (g : (A -> eR) -> A -> eR) (f : A -> eR) (n : nat) : A -> eR :=
  match n with
  | O => fun st => 1
  | S n' => fun st => if e st then g (dec_loop_approx e g f n') st else f st
  end.

(* (* The continuous loop automorphism. *) *)
(* Definition loop_F {A} (e : St -> bool) (g : (St -> A) -> St -> A) (f : St -> A) *)
(*   : (St -> A) -> St -> A := *)
(*   fun k s => if e s then g k s else f s. *)

(* The continuous loop automorphism. *)
Definition loop_F {A B} (e : A -> bool) (g : (A -> B) -> A -> B) (f : A -> B)
  : (A -> B) -> A -> B :=
  fun k s => if e s then g k s else f s.

Definition loop_approx' {A}
  (e : A -> bool) (g : (A -> eR) -> A -> eR) (f : A -> eR) (n : nat) : A -> eR :=
  iter_n (loop_F e g f) (const 0) n.

Definition loop_approx'' {A}
  (e : A -> bool) (g : (A -> eR) -> A -> eR) (f : A -> eR) (n : nat) : A -> eR :=
  iter_n (loop_F e g f) (fun s => if e s then 0 else f s) n.

Definition dec_loop_approx'
  (e : St -> bool) (g : (St -> eR) -> St -> eR) (f : St -> eR) (n : nat) : St -> eR :=
  iter_n (loop_F e g f) (const 1) n.

Lemma monotone_loop_F {A} `{OType A}
  (e : St -> bool) (g : (St -> A) -> St -> A) (f : St -> A) :
  monotone g ->
  monotone (loop_F e g f).
Proof.
  unfold loop_F; intros Hg x y Hxy s;
    destruct (e s); try reflexivity; apply Hg; auto.
Qed.
#[export] Hint Resolve monotone_loop_F : cwp.

Lemma monotone_loop_F' {A B} `{OType A} (e : B -> bool) F f f' g g' :
  monotone F ->
  f ⊑ f' ->
  g ⊑ g' ->
  loop_F e F f g ⊑ loop_F e F f' g'.
Proof.
  intros HF Hf Hg s.
  unfold loop_F.
  destruct (e s).
  - apply HF; auto.
  - apply Hf.
Qed.

Lemma loop_approx_loop_approx' {A}
  (e : A -> bool) (g : (A -> eR) -> A -> eR) (f : A -> eR) :
  loop_approx e g f = loop_approx' e g f.
Proof.
  unfold loop_approx', loop_F.
  ext n; revert e g f; induction n; intros e g f; simpl; auto.
  ext s; destruct (e s); auto.
  rewrite IHn; auto.
Qed.

Lemma dec_loop_approx_dec_loop_approx'
  (e : St -> bool) (g : (St -> eR) -> St -> eR) (f : St -> eR) :
  dec_loop_approx e g f = dec_loop_approx' e g f.
Proof.
  unfold dec_loop_approx', loop_F.
  ext n; revert e g f; induction n; intros e g f; simpl; auto.
  ext s; destruct (e s); auto.
  rewrite IHn; auto.
Qed.

Corollary loop_approx_iter_n_loop_F {A}
  (e : A -> bool) (g : (A -> eR) -> A -> eR) (f : A -> eR) :
  loop_approx e g f = iter_n (loop_F e g f) (const 0).
Proof. apply loop_approx_loop_approx'. Qed.

Corollary dec_loop_approx_iteR_n_loop_F
  (e : St -> bool) (g : (St -> eR) -> St -> eR) (f : St -> eR) :
  dec_loop_approx e g f = iter_n (loop_F e g f) (const 1).
Proof. apply dec_loop_approx_dec_loop_approx'. Qed.

(** 4 possible configurations. Can draw square sort of like political
    compass thing. *)

Fixpoint wp_ (fl : bool) (c : cpGCL) (f : St -> eR) (st : St) : eR :=
  match c with
  | CSkip => f st
  | CAbort => 0
  | CAssign x e => f (upd x (e st) st)
  | CSeq c1 c2 => wp_ fl c1 (wp_ fl c2 f) st
  | CIte e c1 c2 => if e st then wp_ fl c1 f st else wp_ fl c2 f st
  | CChoice e k =>
      Q2eR (e st) * wp_ fl (k true) f st + (1 - Q2eR (e st)) * wp_ fl (k false) f st
  | CUniform e k =>
      sum (map (fun i => wp_ fl (k i) f st / INeR (e st)) (range (e st)))
  | CWhile e body => iter (loop_F e (wp_ fl body) f) (const 0) st
  | CObserve e => if e st then f st else if fl then 1 else 0
  end.

Definition wp : cpGCL -> (St -> eR) -> St -> eR := wp_ false.
Definition wpfail : cpGCL -> (St -> eR) -> St -> eR := wp_ true.
Definition fail (c : cpGCL) : St -> eR := wpfail c (const 0).

Fixpoint wlp_ (fl : bool) (c : cpGCL) (f : St -> eR) (st : St) : eR :=
  match c with
  | CSkip => f st
  | CAbort => 1
  | CAssign x e => f (upd x (e st) st)
  | CSeq c1 c2 => wlp_ fl c1 (wlp_ fl c2 f) st
  | CIte e c1 c2 => if e st then wlp_ fl c1 f st else wlp_ fl c2 f st
  | CChoice e k =>
      Q2eR (e st) * wlp_ fl (k true) f st + (1 - Q2eR (e st)) * wlp_ fl (k false) f st
  | CUniform e k =>
      sum (map (fun i => wlp_ fl (k i) f st / INeR (e st)) (range (e st)))
  | CWhile e body => dec_iter (loop_F e (wlp_ fl body) f) (const 1) st
  | CObserve e => if e st then f st else if fl then 1 else 0
  end.

Definition wlp : cpGCL -> (St -> eR) -> St -> eR := wlp_ false.
Definition wlpfail : cpGCL -> (St -> eR) -> St -> eR := wlp_ true.
Definition fail_or_diverge (c : cpGCL) : St -> eR := wlpfail c (const 0).

Definition cwp (c : cpGCL) (f : St -> eR) (st : St) : eR :=
  wp c f st / wlp c (const 1) st.  

(** In unconditional setting, wp and wlp have the following nice properties:
    1) wp is strict on 0,
    2) wlp is strict on 1,
    3) wp + wlp = 1 on bounded expectations.

    In conditional setting, wp is still strict on 0 but the other two
    properties are lost. We present two different ways to restore the
    desired properties and examine their relative merits. There's no
    reason to use one to the exclusion of the other, so we may as well
    introduce both and use whichever is most convenient.

    Wpfail bundles failure with wp in a least fixed point construction,
    and wlpfail bundles failure along with wlp (which itself bundles
    nontermination with wp) in a greatest fixed point construction.

    Both wpfail and wlpfail yield their own versions of the invariant
    sum property:
    [ wpfail + wlp = 1 on bounded expectations ]
    [ wp + wlpfail = 1 on bounded expectations ]

    Which one, if either, is better? Differences:
    1) Wlpfail makes it hard to separate nontermination and observation
       failure. Wpfail makes probability of failure easy: [wpfail (const 0)].
       In contrast, [wlpfail (const 0)] computes the sum of nontermination
       and failure probabilities, which can be used to place an upper bound
       on either one of them but can't be used to determine either one
       exactly (unless the other is known).
    2) Wpfail is not strict on 0. This seems to suggest, along with wlp
       also being not strict on 1, that something may be deeply wrong with
       this option. However, wlpfail *is* strict on 1.
 *)

(* Reveals the geometric (i.i.d.) structure of the condition loop, and
   clearly expresses the fact that the semantics is undefined for
   programs that condition on impossible events (probability of
   observation failure is 1). *)
(* Definition cwp' (c : cpGCL) (f : St -> eR) (st : St) : eR := *)
(*   wp c f st / (1 - fail c st). *)

(** [unroll e c i] is the ith finite unrolling of the loop with guard
    condition [e] and body [c]. *)
Fixpoint unroll (e : St -> bool) (c : cpGCL) (i : nat) : cpGCL :=
  match i with
  | O => CIte e CAbort CSkip
  | S i' => CIte e (CSeq c (unroll e c i')) CSkip
  end.

Lemma chain_iter_n'' {A B} `{OType B} s z (e : A -> bool) g f :
  z ⊑ f ->
  z ⊑ g z ->
  monotone g ->
  chain (fun i => iter_n (fun (k : A -> B) (x : A) =>
                            if e x then g k x else f x) z i s).
Proof.
  intros Hzf Hzg Hg; apply monotone_chain.
  2: { apply chain_id. }
  intros i j Hij; simpl.
  revert s; apply leq_arrow, chain_leq; auto; apply chain_iter_n'.
  + unfold const; simpl; intro s; destr; auto.
  + intros h h' Hh s; destr; try reflexivity; apply Hg; auto.
Qed.

Lemma dec_chain_iter_n'' {A B} `{OType B} s z (e : A -> bool) g f :
  f ⊑ z ->
  g z ⊑ z ->
  monotone g ->
  dec_chain (fun i => iter_n (fun (k : A -> B) (x : A) =>
                                if e x then g k x else f x) z i s).
Proof.
  intros Hzf Hzg Hg.
  replace (fun i : nat => iter_n (fun (k : A -> B) (x : A) =>
                                    if e x then g k x else f x) z i s)
    with ((fun i => iter_n (fun (k : A -> B) (x : A) =>
                              if e x then g k x else f x) z i s) ∘ id)
    by reflexivity.
  apply antimonotone_dec_chain.
  2: { apply chain_id. }
  intros i j Hij; simpl; unfold flip.
  revert s; apply leq_arrow, dec_chain_leq; auto; apply dec_chain_iter_n'.
  + unfold const; simpl; intro s; destr; auto.
  + intros h h' Hh s; destr; try reflexivity; apply Hg; auto.
Qed.

Lemma monotone_wlp (b : bool) (c : cpGCL) : monotone (wlp_ b c).
Proof.
  induction c; intros f f' Hf st; simpl.
  - apply Hf.
  - eRauto.
  - eRauto.
  - apply IHc1, IHc2; auto.
  - destruct (b0 st).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - apply eRplus_le_compat; apply eRmult_le_compat_l; try apply H; eRauto.
  - apply monotone_sum; eRauto.
    apply list_rel_map, Forall_list_rel, Forall_forall.
    intros i Hi; apply eRle_div, H; auto.
  - unfold dec_iter.
    rewrite 2!inf_apply_eR.
    apply leq_eRle.
    eapply pointwise_le_infimum_le.
    2: { apply inf_spec. }
    2: { apply inf_spec. }
    intro i; revert st; apply leq_arrow.
    eapply monotone_iter_n; try reflexivity.
    intros g g' Hg.
    apply monotone_loop_F'; auto.
  - destruct (b0 st); eRauto.
Qed.
#[export] Hint Resolve monotone_wlp : cwp.

Lemma bounded_wlp (b : bool) (c : cpGCL) (f : St -> eR) :
  wf_cpGCL c ->
  bounded f 1 ->
  bounded (wlp_ b c f) 1.
Proof.
  revert f; induction c; intros f Hwf Hf st; simpl; auto;
    inversion Hwf; subst; auto with cwp; auto.
  - reflexivity.
  - apply IHc1; auto.
  - destruct (b0 st).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - pose proof (H false f (H3 false) Hf st) as H'.
    specialize (H true f (H3 true) Hf st).
    pose proof (H3 false) as X'.
    specialize (H3 true); eRauto.
  - replace (fun i : nat => wlp_ b (c i) f st / INeR (n st)) with
      (fun i : nat => / INeR (n st) * wlp_ b (c i) f st).
    2: { ext i; rewrite eRmult_comm; reflexivity. }
    rewrite sum_map_scalar.
    apply eRmult_le_reg_r with (r := INeR (n st)).
    + replace 0 with (INeR 0) by apply INeR_0.
      apply lt_INeR; auto.
    + apply not_infty_INeR.
    + rewrite eRmult_comm.
      rewrite <- eRmult_assoc.
      rewrite eRinv_r.
      2: { apply eRlt_neq'.
           replace 0 with (INeR 0) by apply INeR_0.
           apply lt_INeR; auto. }
      2: { apply not_infty_INeR. }
      rewrite 2!eRmult_1_l.
      replace (INeR (n st)) with (INeR (n st) * 1) by eRauto.
      replace (INeR (n st)) with (INeR (length (range (n st)))).
      2: { rewrite range_length; auto. }
      apply sum_map_ub.
      apply Forall_forall; intros i Hi.
      apply H; auto.
      (* apply in_range in Hi; eapply X; eauto. *)
  - unfold dec_iter, loop_F.
    rewrite inf_apply_eR.
    apply leq_eRle.
    apply ge_inf with O.
    reflexivity.
  - specialize (Hf st); destruct (b0 st); eRauto.
    destruct b; eRauto.
Qed.
#[export] Hint Resolve bounded_wlp : cwp.

Lemma monotone_wp (fl : bool) (c : cpGCL) : monotone (wp_ fl c).
Proof.
  induction c; intros f f' Hf st; simpl.
  - apply Hf.
  - reflexivity.
  - eRauto.
  - apply IHc1, IHc2; auto.
  - destruct (b st).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - apply eRplus_le_compat.
     + apply eRmult_le_compat_l.
       * eRauto.
       * apply H; auto.
     + apply eRmult_le_compat_l.
       * eRauto.
       * apply H; auto.
  - apply sum_le, list_rel_map, Forall_list_rel.
    apply Forall_forall; intros i Hi.
    apply eRle_div, H; auto.
  - unfold iter.
    rewrite 2!sup_apply_eR.
    apply leq_eRle.
    eapply pointwise_le_supremum_le.
    2: { apply sup_spec. }
    2: { apply sup_spec. }
    intro i; revert st; apply leq_arrow.
    eapply monotone_iter_n; try reflexivity.
    intros g g' Hg.
    apply monotone_loop_F'; auto.
  - destruct (b st); eRauto.
Qed.
#[export] Hint Resolve monotone_wp : cwp.

Lemma bounded_wpfail b c f ub :
  wf_cpGCL c ->
  1 <= ub ->
  bounded f ub ->
  bounded (wp_ b c f) ub.
Proof.
  revert f; induction c; intros f Hwf Hub Hf st; simpl;
    inversion Hwf; subst; eauto with cwp.
  - eRauto.
  - apply IHc1; auto.
  - destruct (b0 st).
    + apply IHc1; auto.
    + apply IHc2; auto.
  - apply eRle_convex_sum; try apply H; eRauto.
  - replace (fun i : nat => wp_ b (c i) f st / INeR (n st)) with
      (fun i : nat => / INeR (n st) * wp_ b (c i) f st).
    2: { ext i; rewrite eRmult_comm; reflexivity. }
    rewrite sum_map_scalar.
    apply eRmult_le_reg_r with (r := INeR (n st)).
    + replace 0 with (INeR 0) by apply INeR_0.
      apply lt_INeR; auto.
    + apply not_infty_INeR.
    + rewrite eRmult_comm.
      rewrite <- eRmult_assoc.
      rewrite eRinv_r.
      2: { apply eRlt_neq'.
           replace 0 with (INeR 0) by apply INeR_0.
           apply lt_INeR; auto. }
      2: { apply not_infty_INeR. }
      rewrite eRmult_1_l.
      rewrite eRmult_comm.
      (* replace (INeR (n s)) with (INeR (n s) * 1) by eRauto. *)
      replace (INeR (n st)) with (INeR (length (range (n st)))).
      2: { rewrite range_length; auto. }
      apply sum_map_ub.
      apply Forall_forall; intros i Hi.
      apply H; auto.
      (* apply in_range in Hi; eapply X; eauto. *)
  - unfold iter, loop_F.
    rewrite sup_apply_eR.
    apply leq_eRle.
    apply ge_sup; intro i.
    replace ub with (const ub st) by reflexivity.
    apply leq_arrow.
    apply iter_n_bounded.
    { intro; unfold const; eRauto. }
    intros g Hg s'; unfold const; destr.
    + apply IHc; auto.
    + apply Hf.
  - specialize (Hf st); destruct (b0 st); eRauto.
    destruct b; eRauto.
Qed.
#[export] Hint Resolve bounded_wpfail : cwp.

Lemma wcontinuous_loop_F (e : St -> bool) (g : (St -> eR) -> St -> eR) (f : St -> eR) :
  wcontinuous g ->
  wcontinuous (loop_F e g f).
Proof.
  unfold loop_F.
  intros Hg ch Hch h Hh.
  apply supremum_apply.
  intro st.
  unfold compose.
  apply supremum_cond.
  2: { apply supremum_const. }
  replace (fun i => g (ch i) st) with (fun i => (g ∘ ch) i st) by reflexivity.
  apply apply_supremum, Hg; auto.
Qed.

Lemma dec_wcontinuous_loop_F (e : St -> bool) (g : (St -> eR) -> St -> eR) (f : St -> eR) :
  dec_wcontinuous g ->
  dec_wcontinuous (loop_F e g f).
Proof.
  unfold loop_F.
  intros Hg ch Hch h Hh.
  apply infimum_apply.
  intro st.
  unfold compose.
  apply infimum_cond.
  2: { apply infimum_const. }
  replace (fun i => g (ch i) st) with (fun i => (g ∘ ch) i st) by reflexivity.
  apply apply_infimum, Hg; auto.
Qed.

Lemma loop_approx_monotone {A} (e : A -> bool) g :
  monotone g ->
  monotone (loop_approx e g).
Proof.
  intros Hg f f' Hf i.
  revert e g Hg f f' Hf.
  induction i; intros e g Hg f f' Hf st; simpl.
  - eRauto.
  - destr; eRauto; apply Hg; auto.
Qed.

Lemma dec_loop_approx_monotone {A} (e : A -> bool) g :
  monotone g ->
  monotone (dec_loop_approx e g).
Proof.
  intros Hg f f' Hf i.
  revert e g Hg f f' Hf.
  induction i; intros e g Hg f f' Hf st; simpl.
  - eRauto.
  - destr; eRauto; apply Hg; auto.
Qed.

Lemma loop_approx_continuous {A} (e : A -> bool) g i s ch :
  chain ch ->
  monotone g ->
  (forall ch s, chain ch -> g (sup ch) s = sup (fun i => g (ch i) s)) ->
  loop_approx e g (sup ch) i s = sup (fun j => loop_approx e g (ch j) i s).
Proof.
  unfold loop_approx, loop_F.
  revert e g s ch; induction i; intros e g s ch Hch Hmono Hg; simpl.
  - apply equ_eR; rewrite sup_const; reflexivity.
  - destruct (e s) eqn:Hes.
    + rewrite <- Hg.
      * f_equal.
        ext s'.
        rewrite IHi; auto.
        rewrite sup_apply_eR; auto.
      * intros j s'.
        simpl.
        apply loop_approx_monotone; auto.
    + apply sup_apply_eR.
Qed.

Lemma dec_loop_approx_continuous {A} (e : A -> bool) g i s ch :
  dec_chain ch ->
  monotone g ->
  (forall ch s, dec_chain ch -> g (inf ch) s = inf (fun i => g (ch i) s)) ->
  dec_loop_approx e g (inf ch) i s = inf (fun j => dec_loop_approx e g (ch j) i s).
Proof.
  unfold dec_loop_approx, loop_F.
  revert e g s ch; induction i; intros e g s ch Hch Hmono Hg; simpl.
  - apply equ_eR; rewrite inf_const; reflexivity.
  - destruct (e s) eqn:Hes.
    + rewrite <- Hg.
      * f_equal.
        ext s'.
        rewrite IHi; auto.
        rewrite inf_apply_eR; auto.
      * intros j s'.
        simpl.
        apply dec_loop_approx_monotone; auto.
    + apply inf_apply_eR.
Qed.

Lemma sum_map_sup {A} (l : list A) f :
  Forall (fun a => chain (fun i : nat => f a i)) l ->
  sum (map (fun x => sup (fun i : nat => f x i)) l) =
    sup (fun i : nat => sum (map (fun x => f x i) l)).
Proof.
  revert f; induction l; intros f Hl; simpl.
  { apply equ_eR; rewrite sup_const; reflexivity. }
  inv Hl; rewrite IHl; clear IHl; auto.
  rewrite <- sup_sum; auto.
  intro i; apply monotone_sum; eRauto.
  apply list_rel_map, Forall_list_rel.
  apply Forall_forall; intros j Hj.
  eapply Forall_forall in H2; eauto; apply H2.
Qed.

Lemma sum_map_inf l f :
  Forall (fun a => dec_chain (fun i : nat => f a i)) l ->
  sum (map (fun i : nat => inf (fun j : nat => f i j)) l) =
    inf (fun x : nat => sum (map (fun i0 : nat => f i0 x) l)).
Proof.
  revert f; induction l; intros f Hl; simpl.
  { apply equ_eR; rewrite inf_const; reflexivity. }
  inv Hl; rewrite IHl; clear IHl; auto.
  rewrite <- inf_sum; auto.
  intro i; apply monotone_sum; eRauto.
  apply list_rel_map, Forall_list_rel.
  apply Forall_forall; intros j Hj.
  eapply Forall_forall in H2; eauto; apply H2.
Qed.

(** wp is continuous. *)
Theorem wp_continuous (b : bool) (c : cpGCL) (ch : nat -> St -> eR) :
  wf_cpGCL c ->
  chain ch ->
  wp_ b c (sup ch) = sup (wp_ b c ∘ ch).
Proof.
  revert ch.
  induction c; intros ch Hwf Hch; inv Hwf; unfold compose; simpl; auto.
  - symmetry.
    apply equ_f_eR, supremum_sup.
    apply supremum_const.
  - ext st.
    rename s into x.
    set (f' := fun s => upd x (e s) s).
    assert (upd x (e st) st = f' st).
    { reflexivity. }
    rewrite 2!sup_apply_eR; auto.
  - rewrite IHc2; auto.
    rewrite IHc1; auto.
    apply monotone_chain; auto with cwp.
  - ext st.
    apply equ_eR.
    rewrite sup_apply.
    + apply equ_eR.
      destruct (b0 st) eqn:Hest.
      * erewrite IHc1; eauto; apply equ_eR; rewrite sup_apply; reflexivity.
      * erewrite IHc2; eauto; apply equ_eR; rewrite sup_apply; reflexivity.
  - ext st.
    rewrite sup_apply_eR.
    rewrite 2!H; auto.
    symmetry.
    apply equ_eR.
    apply supremum_sup.
    apply supremum_sum.
    { apply chain_scalar.
      set (g := fun f => wp (c true) f st).
      replace (fun i => wp (c true) (ch i) st) with (g ∘ ch).
      - apply monotone_chain.
        + intros i j Hij; apply monotone_wp; apply chain_leq; auto.
        + apply chain_id.
      - unfold compose, g; reflexivity. }
    { apply chain_scalar.
      set (g := fun f => wp (c false) f st).
      replace (fun i => wp (c false) (ch i) st) with (g ∘ ch).
      - apply monotone_chain.
        + intros i j Hij; apply monotone_wp; apply chain_leq; auto.
        + apply chain_id.
      - unfold compose, g; reflexivity. }
    { rewrite sup_apply_eR, sup_scalar; apply sup_spec. }
    { rewrite sup_apply_eR, sup_scalar; apply sup_spec. }
  - ext s.
    rewrite sup_apply_eR.
    replace (fun i : nat => wp_ b (c i) (@sup _ (@OType_arrow _ _ OType_eR) ch) s / INeR (n s))
      with (fun i : nat => / INeR (n s) * wp_ b (c i) (sup ch) s).
    2: { ext i; apply eRmult_comm. }
    rewrite sum_map_scalar.
    replace (fun i : nat => sum (map (fun i0 : nat => wp_ b (c i0) (ch i) s / INeR (n s))
                              (range (n s)))) with
      (fun i : nat => / INeR (n s) * sum (map (fun i0 : nat => wp_ b (c i0) (ch i) s)
                                       (range (n s)))).
    2: { ext i.
         replace (fun i0 : nat => wp_ b (c i0) (ch i) s / INeR (n s)) with
           (fun i0 : nat => / INeR (n s) * wp_ b (c i0) (ch i) s).
         2: { ext j; apply eRmult_comm. }
         rewrite sum_map_scalar; reflexivity. }
    rewrite <- sup_scalar.
    f_equal.
    replace (fun i : nat => wp_ b (c i) (sup ch) s) with
      (fun i : nat => sup (wp_ b (c i) ∘ ch) s).
    2: { ext i; rewrite H; auto. }
    replace (fun i : nat => sup (wp_ b (c i) ∘ ch) s) with
      (fun i : nat => sup (fun j => wp_ b (c i) (ch j) s)).
    2: { ext i; rewrite sup_apply_eR; reflexivity. }
    apply sum_map_sup.
    apply Forall_forall; intros i Hi.
    intro j; apply monotone_wp; auto.
  - apply equ_f_eR, equ_arrow, equ_arrow, equ_f_eR.
    unfold iter.
    rewrite <- loop_approx_iter_n_loop_F.
    replace (sup (fun (x : nat) (st : St) =>
                    sup (iter_n (loop_F b0 (wp_ b c) (ch x)) (const 0)) st))
      with (sup
              (fun (x : nat) (st : St) =>
                 sup (loop_approx b0 (wp_ b c) (ch x)) st)).
    2: { f_equal; ext i; ext s.
         apply equ_eR.
         rewrite sup_apply.
         rewrite sup_apply.
         apply equ_eR; f_equal; ext j.
         rewrite loop_approx_iter_n_loop_F; reflexivity. }
    apply equ_f_eR.
    symmetry.
    apply supremum_sup.
    split.
    + intros i s; simpl.
      apply leq_eRle.
      rewrite 2!sup_apply.
      apply ge_sup.
      intro j.
      apply le_sup with j.
      apply loop_approx_monotone; auto with cwp.
      apply sup_spec.
    + intros ub Hub s.
      rewrite sup_apply.
      pose proof Hub as H.
      apply sup_spec in H.
      simpl in H.
      specialize (H s).
      etransitivity.
      2: { apply H. }
      simpl.
      rewrite sup_apply.
      apply leq_eRle.
      apply ge_sup.
      intro i. simpl.
      assert (Hsup: supremum (loop_approx b0 (wp_ b c) (sup ch) i s)
                      (fun j => loop_approx b0 (wp_ b c) (ch j) i s)).
      { split.
        - intro j.
          apply loop_approx_monotone; eauto with cwp.
          apply sup_spec.
        - intros x Hx.
          rewrite loop_approx_continuous; eauto with cwp.
          + apply ge_sup; auto.
          + intros ch0 s0 Hch0.
            rewrite IHc; auto.
            apply sup_apply_eR. }
      apply Hsup.
      intro j.
      apply le_sup with j.
      rewrite sup_apply.
      apply le_sup with i; eRauto.
  - ext s.
    destruct (b0 s) eqn:Hes.
    + rewrite 2!sup_apply_eR.
      f_equal; ext i; rewrite Hes; auto.
    + rewrite sup_apply_eR.
      apply equ_eR.
      symmetry.
      apply supremum_sup.
      destruct b; apply supremum_const'; apply equ_arrow;
        intro i; rewrite Hes; reflexivity.
Qed.

(** wlp is continuous. *)
Theorem wlp_continuous (b : bool) (c : cpGCL) (ch : nat -> St -> eR) :
  wf_cpGCL c ->
  dec_chain ch ->
  wlp_ b c (inf ch) = inf (wlp_ b c ∘ ch).
Proof.
  revert ch.
  induction c; intros ch Hwf Hch; inv Hwf; unfold compose; simpl; auto.
  - symmetry.
    apply equ_f_eR, infimum_inf.
    apply infimum_const.
  - ext st.
    rename s into x.
    set (f' := fun s => upd x (e s) s).
    assert (upd x (e st) st = f' st).
    { reflexivity. }
    rewrite 2!inf_apply_eR; auto.
  - rewrite IHc2; auto.
    rewrite IHc1; auto.
    apply monotone_dec_chain; auto with cwp.
  - ext st.
    apply equ_eR.
    rewrite inf_apply.
    + apply equ_eR.
      destruct (b0 st) eqn:Hest.
      * erewrite IHc1; eauto; apply equ_eR; rewrite inf_apply; reflexivity.
      * erewrite IHc2; eauto; apply equ_eR; rewrite inf_apply; reflexivity.
  - ext st.
    rewrite inf_apply_eR.
    rewrite 2!H; auto.
    symmetry.
    apply equ_eR.
    apply infimum_inf.
    apply infimum_sum.
    { apply dec_chain_scalar.
      set (g := fun f => wlp_ b (c true) f st).
      replace (fun i => wlp_ b (c true) (ch i) st) with (g ∘ ch).
      - apply monotone_dec_chain; auto.
        intros i j Hij; apply monotone_wlp; auto.
      - unfold compose, g; reflexivity. }
    { apply dec_chain_scalar.
      set (g := fun f => wlp_ b (c false) f st).
      replace (fun i => wlp_ b (c false) (ch i) st) with (g ∘ ch).
      - apply monotone_dec_chain; auto.
        intros i j Hij; apply monotone_wlp; auto.
      - unfold compose, g; reflexivity. }
    { rewrite inf_apply_eR, inf_scalar; eRauto; apply inf_spec. }
    { rewrite inf_apply_eR, inf_scalar; eRauto; apply inf_spec. }
  - ext s.
    rewrite inf_apply_eR.
    replace (fun i : nat => wlp_ b (c i) (@inf _ (@OType_arrow _ _ OType_eR) ch) s / INeR (n s))
      with (fun i : nat => / INeR (n s) * wlp_ b (c i) (inf ch) s).
    2: { ext i; apply eRmult_comm. }
    rewrite sum_map_scalar.
    replace (fun i : nat => sum (map (fun i0 : nat => wlp_ b (c i0) (ch i) s / INeR (n s))
                              (range (n s)))) with
      (fun i : nat => / INeR (n s) * sum (map (fun i0 : nat => wlp_ b (c i0) (ch i) s)
                                            (range (n s)))).
    2: { ext i.
         replace (fun i0 : nat => wlp_ b (c i0) (ch i) s / INeR (n s)) with
           (fun i0 : nat => / INeR (n s) * wlp_ b (c i0) (ch i) s).
         2: { ext j; apply eRmult_comm. }
         rewrite sum_map_scalar; reflexivity. }
    rewrite <- inf_scalar.
    2: { simpl; destr.
         - assert (0 < INR (n s))%R.
           { replace 0%R with (INR 0) by auto.
             apply lt_INR; auto. }
           lra.
         - intro HC; inv HC. }
    f_equal.
    replace (fun i : nat => wlp_ b (c i) (inf ch) s) with
      (fun i : nat => inf (wlp_ b (c i) ∘ ch) s).
    2: { ext i; rewrite H; auto. }
    replace (fun i : nat => inf (wlp_ b (c i) ∘ ch) s) with
      (fun i : nat => inf (fun j => wlp_ b (c i) (ch j) s)).
    2: { ext i; rewrite inf_apply_eR; reflexivity. }
    apply sum_map_inf.
    apply Forall_forall; intros i Hi.
    intro j; apply monotone_wlp; auto.
  - apply equ_f_eR, equ_arrow, equ_arrow, equ_f_eR.
    unfold dec_iter.
    rewrite <- dec_loop_approx_iteR_n_loop_F.
    replace (inf (fun (x : nat) (st : St) =>
                    inf (iter_n (loop_F b0 (wlp_ b c) (ch x)) (const 1)) st))
      with (inf
              (fun (x : nat) (st : St) =>
                 inf (dec_loop_approx b0 (wlp_ b c) (ch x)) st)).
    2: { f_equal; ext i; ext s.
         apply equ_eR.
         rewrite 2!inf_apply.
         apply equ_eR; f_equal; ext j.
         rewrite dec_loop_approx_iteR_n_loop_F; reflexivity. }
    apply equ_f_eR.
    symmetry.
    apply infimum_inf.
    split.
    + intros i s; simpl.
      apply leq_eRle.
      rewrite 2!inf_apply.
      apply le_inf.
      intro j.
      apply ge_inf with j.
      apply dec_loop_approx_monotone; auto with cwp.
      apply inf_spec.
    + intros ub Hub s.
      rewrite inf_apply.
      pose proof Hub as H.
      apply inf_spec in H.
      simpl in H.
      specialize (H s).
      etransitivity.
      { apply H. }
      simpl.
      rewrite inf_apply.
      apply leq_eRle.
      apply le_inf.
      intro i. simpl.
      assert (Hinf: infimum (dec_loop_approx b0 (wlp_ b c) (inf ch) i s)
                      (fun j => dec_loop_approx b0 (wlp_ b c) (ch j) i s)).
      { split.
        - intro j.
          apply dec_loop_approx_monotone; eauto with cwp.
          apply inf_spec.
        - intros x Hx.
          rewrite dec_loop_approx_continuous; eauto with cwp.
          + apply le_inf; auto.
          + intros ch0 s0 Hch0.
            rewrite IHc; auto.
            apply inf_apply_eR. }
      apply Hinf.
      intro j.
      apply ge_inf with j.
      rewrite inf_apply.
      apply ge_inf with i; eRauto.
  - ext s.
    destruct (b0 s) eqn:Hes.
    + rewrite 2!inf_apply_eR.
      f_equal; ext i; rewrite Hes; auto.
    + rewrite inf_apply_eR.
      apply equ_eR.
      symmetry.
      apply infimum_inf.
      destruct b; apply infimum_const'; apply equ_arrow;
        intro i; rewrite Hes; reflexivity.
Qed.

Lemma loop_F_bounded {A} `{OType A} e F f g (ub : A) (s : St) :
  F f s ⊑ ub ->
  g s ⊑ ub ->
  loop_F e F g f s ⊑ ub.
Proof. intros HF Hg; unfold loop_F; destr; auto. Qed.

Lemma wp_unroll_loop b G c f :
  wf_cpGCL c ->
  wp_ b (CWhile G c) f = wp_ b (CIte G (CSeq c (CWhile G c)) CSkip) f.
Proof.
  intro Hwf.
  apply equ_f_eR; simpl.
  rewrite iter_unfold.
  { reflexivity. }
  { apply wcontinuous_loop_F.
    intros ch Hch s Hs.
    assert (s = sup ch).
    { apply equ_f_eR; symmetry; apply supremum_sup; auto. }
    subst; rewrite wp_continuous; auto; apply sup_spec. }
  { intro; unfold const; eRauto. }
Qed.

Lemma wlp_unroll_loop b G c f :
  wf_cpGCL c ->
  bounded f 1 ->
  wlp_ b (CWhile G c) f = wlp_ b (CIte G (CSeq c (CWhile G c)) CSkip) f.
Proof.
  intros Hwf Hf.
  apply equ_f_eR; simpl.
  rewrite dec_iter_unfold.
  { reflexivity. }
  { apply dec_wcontinuous_loop_F.
    intros ch Hch s Hs.
    assert (s = inf ch).
    { apply equ_f_eR; symmetry; apply infimum_inf; auto. }
    subst; rewrite wlp_continuous; auto; apply inf_spec. }
  intro s.
  { apply loop_F_bounded.
    - apply bounded_wlp; auto; intro; reflexivity.
    - apply Hf. }
Qed.

Theorem cwp_unroll_loop G c f :
  wf_cpGCL c ->
  cwp (CWhile G c) f = cwp (CIte G (CSeq c (CWhile G c)) CSkip) f.
Proof.
  intro Hwf; apply equ_f_eR, equ_arrow; intro st.
  unfold cwp, wp, wlp.
  apply equ_eR; f_equal.
  - rewrite wp_unroll_loop; auto.
  - rewrite wlp_unroll_loop; auto; intro; reflexivity.
Qed.

Lemma wp_strict c :
  wp c (const 0) = const 0.
Proof.
  unfold wp.
  induction c; simpl; auto; ext s.
  - rewrite IHc2, IHc1; reflexivity.
  - destr; try rewrite IHc1; auto; rewrite IHc2; auto.
  - rewrite 2!H; unfold const; eRauto.
  - apply sum_0, Forall_forall; intros x Hx.
    apply in_map_iff in Hx.
    destruct Hx as [i [? Hin]]; subst.
    rewrite H; eRauto.
  - unfold iter, const.
    apply equ_eR; rewrite sup_apply.
    apply sup_const'.
    apply equ_arrow; intro i; unfold const.
    transitivity (const 0 s); try reflexivity.
    revert s; apply equ_arrow, iter_n_const.
    + apply monotone_loop_F, monotone_wp.
    + apply equ_arrow; intro s; unfold loop_F; destr; try reflexivity.
      unfold const in IHc; rewrite IHc; reflexivity.
  - destr; reflexivity.
Qed.

Lemma wlpfail_costrict (c : cpGCL) :
  wf_cpGCL c ->
  wlpfail c (const 1) = const 1.
Proof.
  intro Hwf.
  unfold wlpfail.
  induction c; simpl; auto; ext s; inv Hwf.
  - rewrite IHc2, IHc1; auto; reflexivity.
  - destr; try rewrite IHc1; auto; rewrite IHc2; auto.
  - rewrite 2!H; unfold const; eRauto.
  - replace (fun i : nat => wlp_ true (c i) (const 1) s / INeR (n s)) with
      (fun i : nat => / INeR (n s) * wlp_ true (c i) (const 1) s).
    2: { ext i; apply eRmult_comm. }
    rewrite sum_map_scalar.
    apply eRmult_eq_reg_r with (r := INeR (n s)); auto with eR.
    unfold const.
    rewrite eRmult_1_l, eRmult_comm, <- eRmult_assoc.
    rewrite eRinv_r; auto with eR.
    rewrite eRmult_1_l, sum_map_const with (c:=1).
    { rewrite eRmult_1_r, range_length; reflexivity. }
    apply Forall_forall; intros i Hi.
    rewrite H; auto.
  - unfold dec_iter, const.
    rewrite inf_apply_eR.
    apply equ_eR.
    apply inf_const'.
    apply equ_arrow; intro i; unfold const.
    transitivity (const 1 s); try reflexivity.
    revert s; apply equ_arrow, iter_n_const.
    + apply monotone_loop_F, monotone_wlp.
    + apply equ_arrow; intro s; unfold loop_F; destr; try reflexivity.
      unfold const in IHc; rewrite IHc; auto; reflexivity.
  - destr; reflexivity.
Qed.

(** [wp b c f = 1 - wlp (~ b) c (1 - f)] *)
Lemma wp_wlp_sum (fl : bool) (c : cpGCL) (f : St -> eR) (st : St) :
  wf_cpGCL c ->
  bounded f 1 ->
  wp_ fl c f st + wlp_ (negb fl) c (fun s => 1 - f s) st = 1.
Proof.
  revert fl f st; induction c; intros fl f st Hwf Hf; inv Hwf; simpl.
  - eRauto.
  - eRauto.
  - eRauto.
  - replace (wlp_ (negb fl) c2 (fun s : St => 1 - f s))
      with (fun s => 1 - wp_ fl c2 f s).
    2: { ext s; symmetry; eapply eRplus_eq_minus; eRauto. }
    apply IHc1; auto.
    apply bounded_wpfail; auto; reflexivity.
  - destruct (b st) eqn:Hest.
    + apply IHc1; auto.
    + apply IHc2; auto.
  - rewrite <- eRplus_assoc, eRplus_factor, 2!H; eRauto.
  - rewrite sum_map_plus.
    replace (fun x : nat =>
               wp_ fl (c x) f st / INeR (n st) +
                 wlp_ (negb fl) (c x) (fun s : St => 1 - f s) st / INeR (n st))
      with (fun x : nat => / INeR (n st) *
                        (wp_ fl (c x) f st +
                           wlp_ (negb fl) (c x) (fun s : St => 1 - f s) st)).
    2: { ext i; rewrite eRmult_plus_distr_l.
         rewrite eRmult_comm; f_equal; apply eRmult_comm. }
    rewrite sum_map_scalar.
    apply eRmult_eq_reg_r with (r := INeR (n st)); auto with eR.
    rewrite eRmult_1_l, eRmult_comm, <- eRmult_assoc.
    rewrite eRinv_r; auto with eR.
    rewrite eRmult_1_l, sum_map_const with (c:=1).
    { rewrite eRmult_1_r, range_length; reflexivity. }
    apply Forall_forall; intros i Hi.
    rewrite H; auto.
  - unfold iter, dec_iter.
    rewrite sup_apply_eR, inf_apply_eR.
    eapply supremum_infimum_sum with (ub:=1%R).
    6: { apply sup_spec. }
    6: { apply inf_spec. }
    { apply chain_iter_n''.
      - intro; unfold const; eRauto.
      - intro; unfold const; eRauto.
      - apply monotone_wp. }
    { apply dec_chain_iter_n''.
      - intro; unfold const; eRauto.
      - apply bounded_wlp; auto; intro; reflexivity.
      - apply monotone_wlp. }
    { intro i; revert st; apply leq_arrow, iter_n_bounded.
      - simpl; eRauto.
      - intros g Hle s.
        apply loop_F_bounded.
        + apply bounded_wpfail; auto.
          * eRauto.
          * apply Hle.
        + apply Hf. }
    { intro i; revert st; apply leq_arrow, iter_n_bounded.
      - simpl; eRauto.
      - intros g Hle s.
        apply loop_F_bounded.
        + apply bounded_wlp; auto.
        + eRauto. }
    intro i; simpl.
    revert st; induction i; intro st; simpl.
    + unfold const; eRauto.
    + unfold loop_F; destr.
      2: { eRauto. }
      unfold as_bool. simpl.
      replace (iter_n (fun (k : St -> eR) (s : St) =>
                         if b s then wlp_ (negb fl) c k s else 1 - f s)
                 (const 1) i) with
        (fun s => 1 - (iter_n (fun (k : St -> eR) (s : St) =>
                              if b s then wp_ fl c k s else f s)
                      (const 0) i) s).
      { apply IHc; auto.
        intro s; apply leq_eRle; revert s.
        apply leq_arrow, iter_n_bounded.
        - intro; eRauto.
        - intros g Hg s; destr.
          + apply bounded_wpfail; auto; reflexivity.
          + apply Hf. }
      ext s.
      symmetry; apply eRplus_eq_minus; eRauto.
  - destruct (b st).
    + eRauto.
    + destruct fl; simpl; eRauto.
Qed.

(** [wlp b c f = 1 - wp (~ b) c (1 - f)] *)
Lemma wlp_wp_sum (fl : bool) (c : cpGCL) (f : St -> eR) (st : St) :
  wf_cpGCL c ->
  bounded f 1 ->
  wlp_ fl c f st + wp_ (negb fl) c (fun s => 1 - f s) st = 1.
Proof.
  intros Hwf Hf.
  rewrite eRplus_comm.
  replace (wlp_ fl c f st) with
    (wlp_ (negb (negb fl)) c (fun s => 1 - (fun s' => 1 - f s') s) st).
  2: { f_equal.
       - apply negb_involutive.
       - ext s; eRauto. }
  apply wp_wlp_sum; auto.
  intro; eRauto.
Qed.

Lemma wlp_fail (c : cpGCL) (st : St) :
  wf_cpGCL c ->
  wlp c (const 1) st = 1 - fail c st.
Proof.
  intro Hwf.
  cut (wlp c (const 1) st + fail c st = 1).
  { intro H; apply eRplus_eq_minus.
    - eRauto.
    - rewrite eRplus_comm; apply H. }
  unfold wlp, fail, wpfail.
  replace (wp_ true c (const 0) st) with
    (wp_ (negb false) c (fun s => 1 - const 1 s) st).
  { apply wlp_wp_sum; auto.
    intro s; eRauto. }
  f_equal; ext s; eRauto.
Qed.

Lemma score_wp (e : St -> Q) (f : St -> eR) (st : St) :
  wp (CScore e) f st = Q2eR (e st) * f st.
Proof. unfold wp; simpl; eRauto. Qed.

Lemma score_wlp (e : St -> Q) (f : St -> eR) (st : St) :
  wlp (CScore e) f st = Q2eR (e st) * f st.
Proof. unfold wlp; simpl; eRauto. Qed.

Lemma score_cwp (e : St -> Q) (f : St -> eR) (st : St) :
  (0 < e st)%Q ->
  cwp (CScore e) f st = f st.
Proof.
  intro Hlt; unfold cwp, wlp.
  rewrite score_wp.
  simpl; unfold const; eRauto.
  rewrite eRmult_div_cancel; eRauto; intro HC.
  replace 0 with (Q2eR 0) in HC.
  { apply eq_eR_Qeq in HC.
    - rewrite HC in Hlt; inv Hlt.
    - apply Qlt_le_weak; auto.
    - apply Qle_refl. }
  apply Q2eR_0.
Qed.
