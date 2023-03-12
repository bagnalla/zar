(** * Geometric (i.i.d.) tcwp semantics. *)

Set Implicit Arguments.

Require Import Basics.
Local Open Scope program_scope.

From zar Require Import
  cpGCL
  cpo
  cwp
  geometric_series
  misc
  eR
  tactics
  tcwp
  tcwp_facts
  tree
.

Local Open Scope order_scope.

Lemma loop_approx''_twp_fix_approx''' {I A}
  (st : I) (e : I -> bool) (g : I -> tree I) (k : I -> tree A) (n : nat) f :
  loop_approx'' e (fun f0 s => twp_ false (g s) f0)
    (fun s => twp_ false (k s) f) n st =
    twp (fix_approx''' st e g (fun s => if e s then Fail _ else k s) n) f.
Proof.
  unfold twp; revert st e g k f; induction n; intros st e g k f; simpl.
  { unfold loop_approx''; simpl; destr; auto. }
  unfold loop_approx'', loop_F; simpl.
  destruct (e st) eqn:Hest; simpl; auto.
  rewrite twp__tree_bind; f_equal; ext s; apply IHn.
Qed.

Lemma loop_approx''_false {A} e g f n (s : A) :
  e s = false ->
  loop_approx'' e g f n s = f s.
Proof.
  unfold loop_approx''.
  intro Hes; destruct n; simpl.
  - rewrite Hes; reflexivity.
  - unfold loop_F. rewrite Hes; reflexivity.
Qed.

Lemma g_loop_approx'_loop_approx'' {A} (e : A -> bool) g f n s :
  e s = true ->
  g (const 0) = const 0 ->
  g (loop_approx' e g f n) s = loop_approx'' e g f n s.
Proof.
  unfold shift, loop_approx', loop_approx'', const.
  revert e g f s; induction n; intros e g f s Hes Hg; simpl.
  { rewrite Hg, Hes; reflexivity. }
  unfold loop_F; simpl.
  rewrite Hes.
  f_equal.
  ext st.
  destruct (e st) eqn:Hest; simpl.
  - apply IHn; auto.
  - symmetry; apply loop_approx''_false; auto.
Qed.

Lemma shift_loop_approx'_loop_approx'' {A} (e : A -> bool) g f  :
  g (const 0) = const 0 ->
  shift (loop_approx' e g f) = loop_approx'' e g f.
Proof.
  intro Hg.
  unfold shift, loop_approx', loop_approx'', const.
  simpl; unfold loop_F.
  ext i. ext s.
  destruct (e s) eqn:Hes.
  - apply g_loop_approx'_loop_approx''; auto.
  - symmetry; apply loop_approx''_false; auto.
Qed.

Lemma twp_fix_chain_scalar {I} G (st : I) a t i :
  G st = true ->
  twp (fix_chain st G (fun _ => t) i) (fun s => if G s then a else 0) =
    a *  twp t (fun s : I => if G s then 1 else 0) ^ i.
Proof.
  unfold twp; revert G st a t; induction i; intros G st a t HGst; simpl.
  { rewrite HGst; eRauto. }
  rewrite twp__tree_bind.
  replace (fun s : I => twp_ false (if G s then t else Leaf s)
                       (fun s0 : I => if G s0 then a else 0)) with
    (fun s : I => if G s then twp t (fun s0 : I => if G s0 then a else 0)
               else 0).
  2: { ext s; destruct (G s) eqn:HGs; simpl; auto.
       rewrite HGs; reflexivity. }
  rewrite eRmult_comm.
  rewrite eRmult_assoc.
  rewrite (@eRmult_comm _ a).
  erewrite <- IHi; eauto; clear IHi.
  replace (fun s : I => if G s then a else 0) with
    (fun s : I => a * (if G s then 1 else 0)).
  2: { ext s; destr; eRauto. }
  rewrite 3!fold_twp.
  rewrite <- twp_scalar; unfold twp.
  f_equal; ext s; destr.
  - eRauto; rewrite eRmult_comm; apply twp_scalar.
  - eRauto.
Qed.

Lemma twp_fix_chain_geometric_series {I} (st : I) G t i f :
  G st = true ->
  twp_ false (fix_chain st G (fun _ => t) i) (fun s => if G s then 0 else f s) =
    geometric_series (twp t (fun s => if G s then 0 else f s))
      (twp t (fun s : I => if G s then 1 else 0)) i.
Proof.
  unfold twp; revert st G t f; induction i; intros st G t f HGst; simpl.
  { rewrite HGst; reflexivity. }
  rewrite twp__tree_bind.
  erewrite <- IHi; eauto; clear IHi.
  replace (fun s : I => twp_ false (if G s then t else Leaf s)
                       (fun s0 : I => if G s0 then 0 else f s0)) with
    (fun s => if G s then twp t (fun s0 : I => if G s0 then 0 else f s0) else f s).
  2: { ext s; destruct (G s) eqn:HGs; simpl; auto; rewrite HGs; reflexivity. }
  replace (fun s => if G s then twp t (fun s0 => if G s0 then 0 else f s0) else f s)
    with (fun s => (if G s then twp t (fun s0 => if G s0 then 0 else f s0) else 0) +
                  (if G s then 0 else f s)).
  2: { ext s; destr; eRauto. }
  rewrite 4!fold_twp.
  rewrite twp_plus.
  unfold twp.
  rewrite eRplus_comm; f_equal.
  rewrite 3!fold_twp.
  rewrite twp_fix_chain_scalar; auto.
Qed.

Lemma twp_fix_iid {A B} (st : A) (G : A -> bool) (t : tree A) (k : A -> tree B) f :
  wf_tree t ->
  (forall s, wf_tree (k s)) ->
  twp t (fun s => if G s then 1 else 0) < 1 ->
  G st = true ->
  twp (Fix st G (fun _ => t) k) f = twp t (fun s => if G s then 0 else twp (k s) f) /
                                   (1 - twp t (fun s => if G s then 1 else 0)).
Proof.
  intros Ht Hk Hlt HGst.
  unfold twp.
  simpl.
  unfold iter.
  rewrite sup_apply_eR.
  rewrite <- geometric_series_sup; eRauto.
  apply sup_shift_eR.
  { apply chain_iter_n''; eauto with twp order; intro; eRauto. }
  f_equal; ext i.
  rewrite <- loop_approx_iter_n_loop_F.
  rewrite loop_approx_loop_approx'.
  replace (shift
             (fun i0 : nat =>
                loop_approx' G (fun (f0 : A -> eR) (s : A) => twp_ false t f0)
                  (fun s : A => twp_ false (k s) f) i0 st) i) with
    (loop_approx'' G (fun (f0 : A -> eR) (s : A) => twp_ false t f0)
       (fun s : A => twp_ false (k s) f) i st).
  2: { rewrite <- shift_loop_approx'_loop_approx''.
       - reflexivity.
       - ext s; apply twp_strict. }
  rewrite loop_approx''_twp_fix_approx'''.
  rewrite fix_approx'''_tree_bind_fix_approx.
  rewrite twp_tree_bind.
  replace (fun s : A => twp (if G s then Fail _ else k s) f) with
    (fun s => if G s then 0 else twp (k s) f).
  2: { ext s; destr; reflexivity. }
  unfold twp.
  rewrite fix_approx_fix_chain.
  rewrite twp_fix_chain_geometric_series; auto.
Qed.
