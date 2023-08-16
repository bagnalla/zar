(** * Interaction tree definitions and compiler correctness theorem. *)

Set Implicit Arguments.
Set Contextual Implicit.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From Paco Require Import paco.

Require Import Equivalence.
Local Open Scope equiv_scope.

From zar Require Import
  compile
  cocwp
  cocwp_facts
  cotree
  cpGCL
  cpo
  cwp
  cwp_tcwp
  debias
  misc
  mu
  order
  eR
  tactics
  tree
  tcwp
  tcwp_facts
.

Local Open Scope eR_scope.

Create HintDb itree.

Variant boolE : Type -> Type :=
  | GetBool : boolE bool.

Definition itree_sampler (A : Type) : Type := itree boolE A.

Definition itree_ret {A : Type} (x : A)
  : itree_sampler A := Ret x.
Definition itree_tau {A : Type} (t : itree_sampler A)
  : itree_sampler A := Tau t.
Definition itree_vis {A : Type} (k : bool -> itree_sampler A)
  : itree_sampler A := Vis GetBool k.

Lemma _observe_observe {A : Type} {E : Type -> Type} (t : itree E A) :
  _observe t = observe t.
Proof. reflexivity. Qed.

(** itrees to cotrees. *)
CoFixpoint icotree {A} (t : itree boolE A) : cotree bool A :=
  match observe t with
  | RetF x => coleaf x
  | TauF t' => cotau (icotree t')
  | VisF GetBool k => conode (icotree ∘ k)
  end.

(* (** cotrees to itrees. If there are no occurrences of [coitree] in the *) *)
(* (*   construction of an itree, then it will be executable. *) *)
(* CoFixpoint coitree {A} (t : cotree bool A) : itree boolE A := *)
(*   match t with *)
(*   | cobot => Tau (coitree t) *)
(*   | coleaf x => Ret x *)
(*   | cotau t' => Tau (coitree t') *)
(*   | conode k => Vis GetBool (coitree ∘ k) *)
(*   end. *)

(* Lemma coitree_icotree {A} (t : itree boolE A) : *)
(*   coitree (icotree t) ≅ t. *)
(* Proof. *)
(*   revert t; pcofix CH; intros t. *)
(*   pstep; unfold eqit_. *)
(*   rewrite unf_eq; simpl. *)
(*   destruct (observe t) eqn:Ht. *)
(*   - compute; constructor; reflexivity. *)
(*   - compute; constructor; right; apply CH. *)
(*   - destruct e; compute; constructor; intro b; right; apply CH. *)
(* Qed. *)

(* Lemma icotree_coitree {A} (t : cotree bool A) : *)
(*   total t -> *)
(*   cotree_eq (icotree (coitree t)) t. *)
(* Proof. *)
(*   revert t; cofix CH; intros t Hbot. *)
(*   destruct t. *)
(*   - exfalso; eapply not_total_cobot; eauto. *)
(*   - rewrite unf_eq; simpl; compute; constructor. *)
(*   - rewrite unf_eq; simpl; compute; constructor. *)
(*     apply CH, total_cotau; auto. *)
(*   - rewrite unf_eq; simpl; compute; constructor; intro b. *)
(*     apply CH, total_conode; auto. *)
(* Qed. *)

Definition itwp {A} (f : A -> eR) : itree boolE A -> eR :=
  cotwp f ∘ icotree.

Definition itree_preimage {A} (P : A -> bool) : itree boolE A -> cotree bool (list bool) :=
  cotree_preimage P ∘ icotree.

Section itree_cotree_eq.
  Context {A : Type}.

  (** See Eq/Eq.v in the ITree development for explanation of this
      construction (eqitF, eqit_, etc.). *)
  Inductive itree_cotree_eqF (R : itree boolE A -> cotree bool A -> Prop)
    : itree' boolE A -> cotree bool A -> Prop :=
  | itree_cotree_eqF_ret : forall x,
      itree_cotree_eqF R (RetF x) (coleaf x)
  | itree_cotree_eqF_tau : forall it ct,
      R it ct ->
      itree_cotree_eqF R (TauF it) (cotau ct)
  | itree_cotree_eqF_node : forall f g,
      (forall b, R (f b) (g b)) ->
      itree_cotree_eqF R (VisF GetBool f) (conode g).

  Definition itree_cotree_eq_ R : itree boolE A -> cotree bool A -> Prop :=
    fun it ct => itree_cotree_eqF R (observe it) ct.

  Lemma itree_cotree_eqF_mono R R' it ct
    (IN: itree_cotree_eqF R it ct)
    (LE: R <2= R') :
    itree_cotree_eqF R' it ct.
  Proof. intros; induction IN; econstructor; eauto. Qed.

  Lemma itree_cotree_eq__mono : paco2.monotone2 (itree_cotree_eq_).
  Proof. do 2 red. intros. eapply itree_cotree_eqF_mono; eauto. Qed.
  Hint Resolve itree_cotree_eq__mono : paco.

  Definition itree_cotree_eq : itree boolE A -> cotree bool A -> Prop :=
    paco2 itree_cotree_eq_ bot2.

  Lemma itree_cotree_eqF_impl (it : itree' boolE A) (ct : cotree bool A)
    (r1 r2 : itree boolE A -> cotree bool A -> Prop) :
    (forall a b, r1 a b -> r2 a b) ->
    itree_cotree_eqF r1 it ct -> itree_cotree_eqF r2 it ct.
  Proof.
    intros H0 H1.
    destruct it; inversion H1; subst; existT_inv; constructor; auto.
  Qed.

  Lemma itree_cotree_eq_impl
    (it : itree boolE A) (ct : cotree bool A)
    (r1 r2 : itree boolE A -> cotree bool A -> Prop) :
    (forall a b, r1 a b -> r2 a b) ->
    paco2 itree_cotree_eq_ r1 it ct -> paco2 itree_cotree_eq_ r2 it ct.
  Proof.
    revert it ct.
    pcofix CH.
    intros it ct H0 H1.
    punfold H1; pstep.
    eapply itree_cotree_eqF_impl.
    2: { apply H1. }
    intros t' s' [H2 | H2].
    - right; apply CH; auto.
    - right; auto.
  Qed.
End itree_cotree_eq.

#[export]
  Hint Resolve itree_cotree_eq__mono : paco.

(** Translating CF trees to itrees. *)
Fixpoint to_itree_open {A} (t : tree A) : itree boolE (unit + A) :=
  match t with
  | Leaf x => ret (inr x)
  | Fail _ => ret (inl tt)
  | Choice _ k => Vis GetBool (to_itree_open ∘ k)
  | Fix st G g k =>
      ITree.iter (fun s => if G s then
                          y <- to_itree_open (g s) ;;
                          match y with
                          | inl tt => ret (inr (inl tt))
                          | inr s' => ret (inl s')
                          end
                        else
                          ITree.map inr (to_itree_open (k s))) st
  end.

(* (** Should be equivalent to the above. *) *)
(* Fixpoint to_itree_open' (t : tree) : itree boolE (unit + St) := *)
(*   match t with *)
(*   | Leaf x => ret (inr x) *)
(*   | Fail => ret (inl tt) *)
(*   | Choice _ k => Vis GetBool (to_itree_open' ∘ k) *)
(*   | Fix st G g k => *)
(*       x <- ITree.iter (fun s => if G s then *)
(*                               y <- to_itree_open' (g s) ;; *)
(*                               match y with *)
(*                               | inl tt => ret (inr (inl tt)) *)
(*                               | inr s' => ret (inl s') *)
(*                               end *)
(*                             else *)
(*                               ret (inr (inr s))) st ;; *)
(*       match x with *)
(*       | inl _ => ret (inl tt) *)
(*       | inr st' => to_itree_open (k st') *)
(*       end *)
(*   end. *)

Definition tie_itree {A : Type} {E : Type -> Type} (t : itree E (unit + A))
  : itree E A :=
  ITree.iter (const t) tt.

Definition to_itree {A} : tree A -> itree boolE A :=
  tie_itree ∘ to_itree_open.

(* Had to generalize a bit to an arbitrary relation R in order to use
   in the iter lemma below. *)
Lemma itree_cotree_eq_bind {A B} (it : itree boolE A) (ct : cotree bool A)
  (f : A -> itree boolE B) (g : A -> cotree bool B)
  (R : itree boolE B -> cotree bool B -> Prop) :
  itree_cotree_eq it ct ->
  (forall x, paco2 itree_cotree_eq_ R (f x) (g x)) ->
  paco2 itree_cotree_eq_ R (ITree.bind it f) (cotree_bind ct g).
Proof.
  revert it ct f g.
  pcofix CH; intros it ct f g Ht Hfg.
  punfold Ht; pstep; unfold itree_cotree_eq_ in *.
  remember (cotree_bind ct g) as x.
  compute.
  rewrite 2!_observe_observe.
  destruct (observe it) eqn:Hit.
  - inv Ht.
    rewrite cotree_bind_leaf.
    specialize (Hfg r0); punfold Hfg.
    unfold itree_cotree_eq_ in Hfg.
    eapply itree_cotree_eqF_impl.
    2: { eauto. }
    intros a b Hab; dupaco.
    destruct Hab.
    + left; eapply itree_cotree_eq_impl; eauto.
    + right; auto.
  - inv Ht; dupaco.
    rewrite cotree_bind_tau.
    constructor; right; apply CH; auto.
  - inv Ht; existT_inv.
    rewrite cotree_bind_node.
    constructor; intro b; specialize (H3 b); dupaco.
    right; apply CH; auto.
Qed.

Lemma itree_cotree_eq_iter {I A}
  (f : I -> itree boolE (I + A)) (g : I -> cotree bool (I + A)) (z : I) :
  (forall i, itree_cotree_eq (f i) (g i)) ->
  itree_cotree_eq (ITree.iter f z) (cotree_iter g z).
Proof.
  revert f g z; pcofix CH; intros f g z Heq.
  pstep; unfold itree_cotree_eq_.
  remember (cotree_iter g z) as ct.
  assert (cotree_iter g === cotree_iter_F g (cotree_iter g)).
  { apply iter_unfold.
    - apply wcontinuous_cotree_iter_F.
    - constructor. }
  rewrite equ_arrow in H.
  assert (H': forall x, cotree_iter g x = cotree_iter_F g (cotree_iter g) x).
  { intro x; apply cotree_ext, equ_cotree_eq; auto. }
  rewrite Heqct.
  rewrite H'; clear H H'.
  remember (cotree_iter_F g (cotree_iter g) z) as ct'.
  compute.
  rewrite 2!_observe_observe.
  rewrite Heqct'.
  unfold cotree_iter_F.
  pose proof (Heq z) as Hz.
  punfold Hz; unfold itree_cotree_eq_ in Hz.
  destruct (observe (f z)) eqn:Hfz; inv Hz.
  - destruct r0.
    + rewrite cotree_bind_leaf.
      constructor; right; apply CH; auto.
    + rewrite cotree_bind_leaf; constructor.
  - rewrite cotree_bind_tau.
    dupaco; constructor; left.
    apply itree_cotree_eq_bind; auto.
    intros []; pstep; constructor.
    right; apply CH; auto.
  - rewrite cotree_bind_node.
    existT_inv; constructor; intro b; left.
    apply itree_cotree_eq_bind.
    + specialize (H0 b); dupaco; auto.
    + intros []; pstep; constructor.
      right; apply CH; auto.
Qed.

(** Example of comorphism computation lemmas playing nicer with paco
    than with standard coinduction? TODO: check this statement by
    trying with standard coinduction. *)
Lemma itree_cotree_eq_map {A B} (it : itree boolE A) (ct : cotree bool A) (f : A -> B) :
  itree_cotree_eq it ct ->
  itree_cotree_eq (ITree.map f it) (cotree_map f ct).
Proof.
  revert it ct f; pcofix CH; intros it ct f Heq.
  punfold Heq; pstep; unfold itree_cotree_eq_ in *.
  remember (cotree_map f ct) as t.
  compute; rewrite 2!_observe_observe.
  destruct (observe it) eqn:Hit; inv Heq.
  - rewrite cotree_map_leaf; constructor.
  - dupaco; rewrite cotree_map_tau; constructor; right; apply CH; auto.
  - existT_inv; rewrite cotree_map_node.
    constructor; intro b; specialize (H3 b); dupaco; right; apply CH; auto.
Qed.

Lemma to_itree_open_to_cotree_open {A} (t : tree A) :
  itree_cotree_eq (to_itree_open t) (to_cotree_open t).
Proof.
  induction t; simpl.
  - pstep; constructor; auto.
  - pstep; constructor; auto.
  - pstep; constructor; intros []; left; apply H.
  - apply itree_cotree_eq_iter.
    intro st; destruct (b st).
    + apply itree_cotree_eq_bind; eauto.
      intros [[]|s']; pstep; constructor.
    + apply itree_cotree_eq_map; eauto.
Qed.

Theorem to_itree_to_cotree {A} (t : tree A) :
  itree_cotree_eq (to_itree t) (to_cotree t).
Proof.
  unfold to_itree, to_cotree, compose, tie_itree, tie_cotree.
  apply itree_cotree_eq_iter; intros []; apply to_itree_open_to_cotree_open.
Qed.

Lemma itree_cotree_icotree {A} (it : itree boolE A) :
  itree_cotree_eq it (icotree it).
Proof.
  revert it; pcofix CH; intro it.
  pstep; unfold itree_cotree_eq_.
  rewrite unf_eq; simpl.
  destruct (observe it) eqn:Hit.
  - constructor.
  - constructor; right; apply CH.
  - destruct e.
    constructor; intro b; right; apply CH.
Qed.

(* Lemma itree_cotree_coitree {A} (ct : cotree bool A) : *)
(*   total ct -> *)
(*   itree_cotree_eq (coitree ct) ct. *)
(* Proof. *)
(*   revert ct; pcofix CH; intros ct Hbot. *)
(*   pstep; unfold itree_cotree_eq_. *)
(*   destruct ct. *)
(*   - exfalso; eapply not_total_cobot; eauto. *)
(*   - compute; constructor. *)
(*   - apply total_cotau in Hbot. *)
(*     compute; constructor; right; apply CH; auto. *)
(*   - compute; constructor; intro b; right; apply CH; *)
(*       eapply total_conode in Hbot; eauto. *)
(* Qed. *)

Lemma itree_cotree_icotree_eq {A} (it : itree boolE A) (ct : cotree bool A) :
  itree_cotree_eq it ct ->
  icotree it = ct.
Proof.
  intro H; apply cotree_ext; revert H.
  revert it ct; cofix CH; intros it ct Heq.
  punfold Heq; unfold itree_cotree_eq_ in Heq.
  rewrite unf_eq; simpl.
  destruct (observe it) eqn:Hit; inv Heq.
  - constructor.
  - dupaco; constructor; auto.
  - existT_inv; constructor; intro b; specialize (H3 b); dupaco; apply CH; auto.
Qed.

(* Lemma itree_cotree_coitree_eq {A} (it : itree boolE A) (ct : cotree bool A) : *)
(*   itree_cotree_eq it ct -> *)
(*   it ≅ coitree ct. *)
(* Proof. *)
(*   revert it ct; pcofix CH; intros it ct Heq. *)
(*   punfold Heq; pstep. *)
(*   unfold itree_cotree_eq_ in Heq. *)
(*   unfold eqit_. *)
(*   rewrite unf_eq. *)
(*   destruct ct; simpl; inv Heq. *)
(*   - compute; constructor; reflexivity. *)
(*   - dupaco; compute; constructor; right; apply CH; auto. *)
(*   - compute; constructor; intro b; specialize (H1 b); dupaco. *)
(*     right; apply CH; auto. *)
(* Qed. *)

(** Related itrees and cotrees are semantically equivalent. *)
Theorem itwp_cotwp {A} (it : itree boolE A) (ct : cotree bool A) (f : A -> eR) :
  itree_cotree_eq it ct ->
  itwp f it = cotwp f ct.
Proof.
  intro Heq; unfold itwp, compose, cotwp; apply equ_eR.
  erewrite itree_cotree_icotree_eq; eauto; reflexivity.
Qed.

Definition cpGCL_to_tree (c : cpGCL) : St -> tree St :=
  opt ∘ debias ∘ elim_choices ∘ compile c.

Definition cpGCL_to_itree_open (c : cpGCL) : St -> itree boolE (unit + St) :=
  to_itree_open ∘ opt ∘ debias ∘ elim_choices ∘ compile c.

Definition cpGCL_to_itree (c : cpGCL) : St -> itree boolE St :=
  to_itree ∘ opt ∘ debias ∘ elim_choices ∘ compile c.

Lemma cwp_tcwp_cpGCL_to_tree (c : cpGCL) (f : St -> eR) (st : St) :
  wf_cpGCL c ->
  0 < wlp c (const 1) st ->
  cwp c f st = tcwp (cpGCL_to_tree c st) f.
Proof.
  intros Hwf Hlt.
  unfold cpGCL_to_tree, compose.
  rewrite tcwp_opt.
  2: { apply wf_tree'_debias, wf_tree'_elim_choices, compile_wf; auto. }
  rewrite tcwp_debias.
  2: { apply wf_tree'_elim_choices, compile_wf; auto. }
  rewrite tcwp_elim_choices.
  2: { apply compile_wf; auto. }
  rewrite cwp_tcwp; auto.
Qed.

(* Lemma tcwp_itwp {A} (t : tree A) f : *)
(*   wf_tree t -> *)
(*   tree_unbiased t -> *)
(*   tcwp t f = itwp f (to_itree t). *)
(* Proof. *)
(*   intros Hwf Gub. *)
(*   erewrite itwp_cotwp. *)
(*   2: { apply to_itree_to_cotree. } *)
(*   unfold to_cotree, compose. *)
(*   rewrite <- cocwp_cotwp_tie_cotree; auto. *)
(*   apply tcwp_cotcwp. *)
(* Qed. *)

Lemma tcwp_itwp {A} (t : tree A) f :
  wf_tree t ->
  tree_unbiased t ->
  0 < twlp t (const 1) ->
  tcwp t f = itwp f (to_itree t).
Proof.
  intros Hwf Hub Hlt.
  unfold to_itree.
  erewrite itwp_cotwp.
  2: { apply to_itree_to_cotree. }
  unfold to_cotree, compose.
  unfold tcwp.
  rewrite twlp_fail; auto.
  rewrite <- tie_cotree_iid_tie_cotree.
  rewrite cotwp_tie_cotree_iid_wlp.
  2: { rewrite <- twlp_cowlp; auto. intro; eRauto. }
  f_equal.
  - apply twp_cowp; auto.
  - rewrite <- twlp_cowlp; auto.
    2: { intro; eRauto. }
    unfold tfail, twlp, twpfail.
    symmetry; apply eRplus_eq_minus.
    { eRauto. }
    replace false with (negb true) by reflexivity.
    replace (@const eR A 1) with (fun s => 1 - @const eR A 0 s).
    2: { ext s; eRauto. }
    eapply twp_twlp_sum; auto.
    intro; eRauto.
Qed.

(** End-to-end compiler correctness from cpGCL to itree. *)
Theorem cwp_itwp (c : cpGCL) (f : St -> eR) (st : St) :
  wf_cpGCL c ->
  0 < wlp c (const 1) st ->
  cwp c f st = itwp f (cpGCL_to_itree c st).
Proof.
  intros Hwf Hlt.
  rewrite cwp_tcwp_cpGCL_to_tree; auto.
  unfold cpGCL_to_tree, cpGCL_to_itree.
  unfold compose.
  apply tcwp_itwp.
  - apply wf_tree_opt, wf_tree'_wf_tree, wf_tree'_debias.
    apply wf_tree'_elim_choices, compile_wf; auto.
  - apply tree_unbiased_opt, tree_unbiased_debias.
  - apply twlp_opt_pos.
    rewrite twlp_debias.
    2: { apply wf_tree'_elim_choices, compile_wf; auto. }
    2: { intro; eRauto. }
    rewrite twlp_elim_choices.
    2: { apply compile_wf; auto. }
    rewrite wlp_twlp; auto; intro; eRauto.
Qed.

(* Print Assumptions cwp_itwp. *)

Inductive fin_itree (A : Type) : Type :=
| fin_bot : fin_itree A
| fin_leaf : A -> fin_itree A
| fin_node : fin_itree A -> fin_itree A -> fin_itree A.

Require Import String.

Fixpoint string_of_fin_itree (t : fin_itree string) : string :=
  match t with
  | fin_bot => "(⊥)"
  | fin_leaf s => "(" ++ s ++ ")"
  | fin_node l r => "(" ++ string_of_fin_itree l ++ string_of_fin_itree r ++ ")"
  end.

Fixpoint fin_itree_of_itree {A} (n : nat) (t : itree boolE A) : fin_itree A :=
  match n with
  | O => fin_bot
  | S n' => match observe t with
           | RetF x => fin_leaf x
           | TauF t' => fin_itree_of_itree n' t'
           | VisF GetBool k => fin_node (fin_itree_of_itree n' (k true))
                                (fin_itree_of_itree n' (k false))
           end
  end.

Lemma icotree_ret {A} (t : itree boolE A) (x : A) :
  observe t = RetF x ->
  icotree t = coleaf x.
Proof.
  intro Ht.
  rewrite unf_eq; simpl.
  rewrite Ht; auto.
Qed.

Lemma icotree_tau {A} (t t' : itree boolE A) :
  observe t = TauF t' ->
  icotree t = cotau (icotree t').
Proof.
  intro Ht.
  rewrite unf_eq; simpl.
  rewrite Ht; auto.
Qed.

Lemma icotree_vis {A} (t : itree boolE A) k :
  observe t = VisF GetBool k ->
  icotree t = conode (icotree ∘ k).
Proof.
  intro Ht.
  rewrite unf_eq; simpl.
  rewrite Ht; auto.
Qed.  

Lemma icotree_map {A B} (f : A -> B) (t : itree boolE A) :
  icotree (ITree.map f t) = cotree_map f (icotree t).
Proof.
  apply cotree_ext.
  revert t; cofix CH; intro t.
  destruct (observe t) eqn:Ht.
  - rewrite icotree_ret with (x:=r); auto.    
    remember (cotree_map f (coleaf r)) as x.
    rewrite unf_eq; simpl; compute.
    rewrite 2!_observe_observe.
    rewrite Ht; simpl.
    rewrite Heqx.
    rewrite cotree_map_leaf; constructor.
  - rewrite icotree_tau with (t':=t0); auto.
    remember (cotree_map f (cotau (icotree t0))) as x.
    rewrite unf_eq; simpl; compute.
    rewrite 2!_observe_observe.
    rewrite Ht; simpl.
    rewrite Heqx.
    rewrite cotree_map_tau; constructor.
    apply CH.
  - destruct e.
    rewrite icotree_vis with (k:=k); auto.
    remember (cotree_map f (conode (icotree ∘ k))) as x.
    rewrite unf_eq.
    simpl; compute.
    rewrite 2!_observe_observe.
    rewrite Ht; simpl.
    rewrite Heqx.
    rewrite cotree_map_node; constructor.
    intro b; apply CH.
Qed.

Lemma itwp_map {A B} (f : A -> B) (g : B -> eR) (t : itree boolE A) :
  itwp g (ITree.map f t) = itwp (g ∘ f) t.
Proof.
  unfold itwp, compose.
  rewrite icotree_map; apply cotwp_map.
Qed.
