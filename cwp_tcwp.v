(** * tcwp after compilation agrees with cwp. *)

Set Implicit Arguments.

Require Import Basics.

Local Open Scope program_scope.

From zar Require Import
  compile
  cpo
  cpGCL
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

Lemma wp_twp_ (fl : bool) (c : cpGCL) (f : St -> eR) (st : St) :
  wf_cpGCL c ->
  twp_ fl (compile c st) f = wp_ fl c f st.
Proof.
  revert f st; induction c; intros f st Hwf; auto; inv Hwf.
  - simpl; unfold iter, loop_F; simpl.
    apply equ_eR.
    rewrite sup_apply.
    apply sup_const'.
    apply equ_arrow; intro i; unfold const.
    apply iter_n_const'; try reflexivity.
    intros x y Hxy s; auto.
  - simpl; rewrite twp__tree_bind, IHc1; auto; f_equal; ext s; apply IHc2; auto.
  - simpl; destruct (b st); auto.
  - simpl; rewrite 2!H; auto.
  - rewrite compile_uniform, twp__tree_bind, no_fail'_twp; simpl.
    2: { constructor; intro s; try constructor; apply no_fail_btree_to_tree. }
    set (g := fun n => twp_ fl (compile (c n) st) f).
    replace (fun s : St => twp_ fl (compile (c (as_nat (s ϵ))) st) f)
      with (fun s => g (as_nat (s ϵ))).
    2: { ext i; reflexivity. }
    rewrite twp_uniform_tree_sum; auto.
    f_equal; f_equal; ext i; f_equal.
    apply H; auto.
  - simpl; unfold iter, loop_F.
    rewrite 2!sup_apply_eR.
    f_equal; ext i; f_equal; ext k; ext s; destr; auto.
  - simpl; destruct (b st); constructor.
Qed.

Corollary wp_twp (c : cpGCL) (f : St -> eR) (st : St) :
  wf_cpGCL c ->
  twp (compile c st) f = wp c f st.
Proof. apply wp_twp_. Qed.

Corollary fail_tfail (c : cpGCL) (st : St) :
  wf_cpGCL c ->
  tfail (compile c st) = fail c st.
Proof. apply wp_twp_. Qed.

Lemma wlp_twlp_ (fl : bool) (c : cpGCL) (f : St -> eR) (st : St) :
  wf_cpGCL c ->
  bounded f 1 ->
  twlp_ fl (compile c st) f = wlp_ fl c f st.
Proof.
  revert f st; induction c; intros f st Hwf Hf; auto; inv Hwf.
  - simpl; unfold dec_iter, loop_F; simpl.
    apply equ_eR.
    rewrite inf_apply.
    apply inf_const', equ_arrow; intro i; unfold const.
    apply iter_n_const'; try reflexivity.
    intros x y Hxy s; auto.
  - simpl; rewrite twlp__tree_bind, IHc1; auto; f_equal.
    + ext s; apply IHc2; auto.
    + intro s; apply twlp_bounded; auto; apply compile_wf; auto.
  - simpl; destruct (b st); auto.
  - simpl; rewrite 2!H; auto.
  - rewrite compile_uniform.
    rewrite twlp__tree_bind.
    rewrite <- uniform_tree_twp_twlp; eauto.
    + rewrite no_fail'_twp.
      2: { constructor; intro s; try constructor; apply no_fail_btree_to_tree. }
      set (g := fun n => twlp_ fl (compile (c n) st) f).
      replace (fun s : St => twlp_ fl (compile (c (as_nat (s ϵ))) st) f)
        with (fun s => g (as_nat (s ϵ))).
      2: { ext i; reflexivity. }
      rewrite twp_uniform_tree_sum; eauto.
      simpl; f_equal; f_equal.
      ext i; unfold g; f_equal; apply H; auto.
    + intro s; apply twlp_bounded; auto; apply compile_wf; auto.
  - simpl; unfold dec_iter, loop_F.
    rewrite 2!inf_apply_eR.
    f_equal; ext i; apply equ_eR.
    revert st; apply equ_arrow, equ_f_eR.
    induction i; ext st; simpl; auto.
    unfold compose in *.
    destruct (b st) eqn:Hest; auto.
    rewrite IHi; apply IHc; auto.      
    intro s; apply leq_eRle.
    revert s; apply leq_arrow.
    eapply iter_n_bounded.
    + intro s; reflexivity.
    + intros g Hg s; apply eRle_leq.
      destr; auto; apply bounded_wlp; auto.
  - simpl; destruct (b st); constructor.
Qed.

Corollary wlp_twlp (c : cpGCL) (f : St -> eR) (st : St) :
  wf_cpGCL c ->
  bounded f 1 ->
  twlp (compile c st) f = wlp c f st.
Proof. apply wlp_twlp_. Qed.

Theorem cwp_tcwp (c : cpGCL) (f : St -> eR) (st : St):
  wf_cpGCL c ->
  tcwp (compile c st) f = cwp c f st.
Proof.
  intros Hwf; unfold tcwp, cwp.
  f_equal.
  - apply wp_twp; auto.
  - apply wlp_twlp; auto; intro; reflexivity.
Qed.
