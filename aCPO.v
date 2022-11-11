(** * Algebraic CPOs, comorphisms, and their proof principles. *)

From Coq Require Import
  Basics
  Morphisms
  Equivalence
.

Local Open Scope program_scope.
Local Open Scope equiv_scope.

From zar Require Import
  cpo
  order
.

Local Open Scope order_scope.

Create HintDb aCPO.

(** The reason we don't use sigma types for monotone and continuous
    functions is that you have to use weird syntax for function
    application. Besides that, it would be pretty cool I think.. maybe
    still worth it? *)

(** Just as the continuous functions are the approximable functions,
    the (co)continuous properties are the approximable properties. A
    continuous property is true globally whenever it is true locally
    *somewhere*. A cocontinuous property is true globally whenever it
    is true locally *everywhere*. *)

Definition compact {A} `{OType A} (x : A) : Prop :=
  forall f : nat -> A, directed f -> supremum x f -> exists i, f i = x.

(** A space [A] is compact whenever none of its elements can be
    non-trivially approximated. *)
Class Compact (A : Type) `{OType A} : Prop :=
  { compact_spec : forall x : A, compact x }.

(** [B] is dense in [A] when there is an injective inclusion map and a
    way to map an element [a : A] to a chain of elements of [B] that
    converges to [a] (through the inclusion map). *)
Class Dense (A B : Type) `{OType A} `{OType B} : Type :=
  { incl : B -> A
  ; ideal : A -> nat -> B
  }.

(** A is a dCPO with basis B (B is compact and dense in A). *)
Class aCPO (A B : Type) `{oA : OType A} `{oB : OType B}
  {compact : Compact B} {dense : Dense A B} {cpoA : dCPO A} : Prop :=
  { incl_order : forall x y : B, x ⊑ y <-> incl x ⊑ incl y
  ; chain_ideal : forall a : A, chain (ideal a)
  ; monotone_ideal : monotone (@ideal _ _ _ _ dense)
  ; continuous_ideal : forall n, continuous (flip (@ideal _ _ _ _ dense) n)
  ; supremum_ideal : forall a : A, supremum a (incl ∘ ideal a)
  }.

#[global] Hint Resolve chain_ideal : aCPO.

(** Any monotone function on a compact space is continuous. *)
Lemma continuous_compact {A B} `{Compact A} `{OType B} (f : A -> B) :
  monotone f ->
  continuous f.
Proof.
  intros Hmono ch Hch x Hx; unfold compose.
  destruct H0 as [H0].
  split.
  - intro i; apply Hmono, Hx.
  - intros ub Hub.
    specialize (H0 x ch Hch Hx).
    destruct H0 as [i Hi]; subst.
    apply Hub.
Qed.
#[global] Hint Resolve continuous_compact : aCPO.

(** Any antimonotone function on a compact space is cocontinuous. *)
Lemma cocontinuous_compact {A B} `{Compact A} `{OType B} (f : A -> B) :
  antimonotone f ->
  cocontinuous f.
Proof.
  intros Hmono ch Hch x Hx; unfold compose.
  destruct H0 as [H0].
  split.
  - intro i; apply Hmono, Hx.
  - intros ub Hub.
    specialize (H0 x ch Hch Hx).
    destruct H0 as [i Hi]; subst.
    apply Hub.
Qed.
#[global] Hint Resolve cocontinuous_compact : aCPO.

(** Shorthand for referring to the basis of an aCPO. *)
Definition basis (A : Type) {B : Type} `{aCPO A B} : Type := B.

Section aCPO.
  Context {A B : Type} `{aCPO A B}.

  (** Continuous comorphism. *)
  Definition co {C} `{OType C} (f : basis A -> C) (a : A) : C :=
    sup (f ∘ ideal a).

  (** Co-continuous comorphism. *)
  Definition coop {C} `{OType C} (f : basis A -> C) (a : A) : C :=
    inf (f ∘ ideal a).

  Lemma chain_f_ideal {C} `{OType C} (f : basis A -> C) (a : A) :
    monotone f ->
    chain (fun i => f (ideal a i)).
  Proof. intro Hf; apply monotone_chain; auto; apply chain_ideal. Qed.

  Lemma dec_chain_f_ideal {C} `{OType C} (f : basis A -> C) (a : A) :
    antimonotone f ->
    dec_chain (fun i => f (ideal a i)).
  Proof. intro Hf; apply antimonotone_dec_chain; auto; apply chain_ideal. Qed.

  Lemma directed_f_ideal {C} `{OType C} (f : basis A -> C) (a : A) :
    monotone f ->
    directed (fun i => f (ideal a i)).
  Proof.
    intro Hf.
    apply monotone_directed; auto.
    apply chain_directed, chain_ideal.
  Qed.

  Lemma downward_directed_f_ideal {C} `{OType C} (f : basis A -> C) (a : A) :
    antimonotone f ->
    downward_directed (fun i => f (ideal a i)).
  Proof.
    intro Hf.
    apply antimonotone_downward_directed; auto.
    apply chain_directed, chain_ideal.
  Qed.

  Lemma supremum_ideal_incl (b : basis A) :
    supremum b (ideal (incl b)).
  Proof.
    unfold basis in *.
    destruct H as [Hincl ? ? ? Hsup].
    specialize (Hsup (incl b)); destruct Hsup as [Hub Hlub].
    split.
    - intro i.
      specialize (Hub i); unfold compose in Hub.
      apply Hincl; auto.
    - intros x Hx.
      apply Hincl.
      apply Hlub.
      intro i; unfold compose.
      apply Hincl; auto.
  Qed.

  Lemma ideal_incl_le a i :
    ideal (incl a) i ⊑ a.
  Proof.
    generalize (supremum_ideal_incl a); intros [Hub ?]; apply Hub.
  Qed.
  
  (** [co f] is the unique morphism (continuous function) satisfying
      this equation. [co f] is equal to f on all basis elements for
      which f was originally defined. *)
  Theorem co_incl {C} `{dCPO C} (f : basis A -> C) :
    monotone f ->
    co f ∘ incl === f.
  Proof.
    intro Hmono.
    apply equ_arrow; intro b.
    unfold co, compose.
    apply supremum_sup.
    apply continuous_compact; auto.
    - apply chain_directed, chain_ideal.
    - apply supremum_ideal_incl.
  Qed.

  (** Pointwise variant. *)
  Corollary co_incl' {C} `{dCPO C} (f : basis A -> C) (b : basis A) :
    monotone f ->
    co f (incl b) === f b.
  Proof. intro Hmono; revert b; apply equ_arrow, co_incl; auto. Qed.

  (** [coop f] is the unique morphism (continuous function) satisfying
      this equation. [coop f] is equal to f on all basis elements for
      which f was originally defined. *)
  Theorem coop_incl {C} `{ldCPO C} (f : basis A -> C) :
    antimonotone f ->
    coop f ∘ incl === f.
  Proof.
    intro Hmono.
    apply equ_arrow; intro b.
    unfold coop, compose.
    apply infimum_inf.
    apply cocontinuous_compact; auto.
    - apply chain_directed, chain_ideal.
    - apply supremum_ideal_incl.
  Qed.

  (** Pointwise variant. *)
  Corollary coop_incl' {C} `{ldCPO C} (f : basis A -> C) (b : basis A) :
    antimonotone f ->
    coop f (incl b) === f b.
  Proof. intro Hmono; revert b; apply equ_arrow, coop_incl; auto. Qed.

  (** The co-version of any monotone basis function is monotone. *)
  #[global]
    Instance monotone_co {C} `{dCPO C}
    (f : basis A -> C) {_ : Proper (leq ==> leq) f}
    : Proper (leq ==> leq) (co f).
  Proof.
    intros a b Hab.
    apply ge_dsup.
    { apply directed_f_ideal; auto. }
    intro i.
    apply le_dsup with i.
    { apply directed_f_ideal; auto. }
    apply H2, monotone_ideal; auto.
  Qed.

  (** The coop-version of any antimonotone basis function is antimonotone. *)
  #[global]
    Instance antimonotone_coop {C} `{ldCPO C}
    (f : basis A -> C) {_ : Proper (leq ==> flip leq) f}
    : Proper (leq ==> flip leq) (coop f).
  Proof.
    intros a b Hab.
    unfold flip.
    unfold co.
    eapply monotone_dinf.
    { apply downward_directed_f_ideal; auto. }
    { apply downward_directed_f_ideal; auto. }
    intro i; apply H2, monotone_ideal; auto.
  Qed.
  
  (** The approximate co-version of any monotone basis function is continuous. *)
  Lemma continuous_f_ideal {C} `{OType C} (f : basis A -> C) (n : nat) :
    monotone f ->
    continuous (f ∘ flip ideal n).
  Proof.
    intro Hmono.
    apply continuous_compose.
    - apply continuous_ideal.
    - apply continuous_compact; auto.
  Qed.
  
  (** The approximate co-version of any antimonotone basis function is cocontinuous. *)
  Lemma cocontinuous_f_ideal {C} `{OType C} (f : basis A -> C) (n : nat) :
    antimonotone f ->
    cocontinuous (f ∘ flip ideal n).
  Proof.
    intro Hmono.
    apply continuous_cocontinuous_compose.
    - apply continuous_ideal.
    - apply cocontinuous_compact; auto.
  Qed.

  (** The co-version of any monotone basis function is continuous. *)
  Theorem continuous_co {C} `{dCPO C} (f : basis A -> C) :
    monotone f ->
    continuous (co f).
  Proof.
    intros Hmono ch Hch t Hsup; unfold compose; split.
    - intro i; apply monotone_co; auto; apply Hsup.
    - intros x Hx.
      apply ge_dsup.
      { apply directed_f_ideal; auto. }
      intro i.
      eapply continuous_f_ideal; eauto.
      unfold flip, compose; intro j; specialize (Hx j).
      etransitivity; eauto.
      generalize (dsup_spec (fun x0 : nat => f (ideal (ch j) x0))).
      intro Hwsup.
      assert (Hch': directed (fun x0 : nat => f (ideal (ch j) x0))).
      { apply directed_f_ideal; auto. }
      apply Hwsup in Hch'.
      destruct Hch' as [Hub Hlub].
      apply Hub.
  Qed.

  (** The coop-version of any antimonotone basis function is cocontinuous. *)
  Theorem cocontinuous_coop {C} `{ldCPO C} (f : basis A -> C) :
    antimonotone f ->
    cocontinuous (coop f).
  Proof.
    intros Hmono ch Hch t Hsup; unfold compose; split.
    - intro i; apply antimonotone_coop; auto; apply Hsup.
    - intros x Hx.
      apply le_dinf.
      { apply downward_directed_f_ideal; auto. }
      intro i.
      eapply cocontinuous_f_ideal; eauto.
      unfold flip, compose; intro j; specialize (Hx j).
      etransitivity; eauto.
      generalize (dinf_spec (fun x0 : nat => f (ideal (ch j) x0))).
      intro Hdinf.
      assert (Hch': downward_directed (fun x0 : nat => f (ideal (ch j) x0))).
      { apply downward_directed_f_ideal; auto. }
      apply Hdinf in Hch'.
      destruct Hch' as [Hub Hlub].
      apply Hub.
  Qed.

  Lemma monotone_incl : monotone incl.
  Proof.
    intros i j Hij.
    destruct H as [Hincl _ _ _ _].
    apply Hincl; auto.
  Qed.
  
  (** Uniqueness property. This is the primary proof principle. *)
  Theorem co_unique {C} `{dCPO C} (f : basis A -> C) (g : A -> C) :
    monotone f ->
    continuous g ->
    g ∘ incl === f ->
    g === co f.
  Proof.
    unfold basis, compose in *; intros Hf Hg [Hgf Hfg].
    apply equ_arrow.
    intro a.
    symmetry.
    apply supremum_sup.
    split.
    - intro i; unfold compose.
      simpl in *.
      etransitivity; eauto.
      apply continuous_monotone; auto.
      destruct H as [? ? ? ? Hsup].
      destruct (Hsup a) as [Hub _].
      apply Hub.
    - intros c Hc.
      simpl in *.
      destruct H as [? ? ? ? Hsup].
      pose proof (Hsup a) as Ha.
      apply Hg in Ha.
      2: { apply directed_f_ideal; auto.
           apply monotone_incl. }
      destruct Ha as [Hub Hlub].
      apply Hlub.
      intro i; unfold compose.
      etransitivity; eauto.
  Qed.

  (** The comorphism lemma. *)
  Lemma co_exists_unique {C} `{dCPO C} (f : basis A -> C) :
    monotone f ->
    co f ∘ incl === f /\ forall g, continuous g -> g ∘ incl === f -> g === co f.
  Proof.
    intro Hf; split.
    - apply co_incl; auto.
    - intros; apply co_unique; auto.
  Qed.

  (** Useful variant. *)
  Corollary co_unique' {C} `{dCPO C} (f : basis A -> C) (g : A -> C) (a : A) :
    monotone f ->
    continuous g ->
    (forall b, g (incl b) === f b) ->
    g a === co f a.
  Proof.
    intros Hf Hg Hgf.
    revert a; apply equ_arrow.
    apply co_unique; auto.
    apply equ_arrow; auto.
  Qed.

  Corollary Proper_coop {C} `{ldCPO C} (f g : basis A -> C) :
    antimonotone f ->
    antimonotone g ->
    f === g ->
    coop f === coop g.
  Proof.
    intros Hf Hg Hfg.
    unfold coop; unfold compose.
    apply equ_arrow; intro x.
    apply Proper_inf; eauto with order aCPO.
    apply equ_arrow; intro i.
    split; apply Hfg.
  Qed.

  Corollary Proper_coop' {C} `{ldCPO C} (f g : basis A -> C) (x y : A) :
    antimonotone f ->
    antimonotone g ->
    f === g ->
    x === y ->
    coop f x === coop g y.
  Proof.
    intros Hf Hg Hfg Hxy.
    unfold antimonotone in Hf.
    rewrite Hxy; clear Hxy.
    revert y; apply equ_arrow, Proper_coop; auto.
  Qed.

  Theorem coop_unique {C} `{ldCPO C} (f : basis A -> C) (g : A -> C) :
    antimonotone f ->
    cocontinuous g ->
    g ∘ incl === f ->
    g === coop f.
  Proof.
    intros Hf Hg Hfg.
    etransitivity.
    2: { apply Proper_coop; auto.
         2: { apply Hfg. }
         apply monotone_antimonotone_compose; auto with order aCPO.
         apply monotone_incl. }
    apply equ_arrow.
    intro x.
    unfold coop.
    assert (x === sup (incl ∘ ideal x)).
    { symmetry; apply supremum_sup, supremum_ideal. }
    assert (Hgx: g x === g (sup (incl ∘ ideal x))).
    { apply Proper_antimonotone_equ; auto.
      apply cocontinuous_antimonotone; auto. }
    rewrite Hgx.
    rewrite cocontinuous_sup; auto.
    - reflexivity.
    - apply directed_f_ideal, monotone_incl.
  Qed.

  Corollary coop_unique' {C} `{ldCPO C} (f : basis A -> C) (g : A -> C) (a : A) :
    antimonotone f ->
    cocontinuous g ->
    (forall b, g (incl b) === f b) ->
    g a === coop f a.
  Proof.
    intros Hf Hg Hgf.
    revert a; apply equ_arrow.
    apply coop_unique; auto.
    apply equ_arrow; auto.
  Qed.

  (** The anticomorphism lemma. *)
  Lemma coop_exists_unique {C} `{ldCPO C} (f : basis A -> C) :
    antimonotone f ->
    coop f ∘ incl === f /\ forall g, cocontinuous g -> g ∘ incl === f -> g === coop f.
  Proof.
    intro Hf; split.
    - apply coop_incl; auto.
    - intros; apply coop_unique; auto.
  Qed.

  Lemma monotone_co_f {C} `{dCPO C} (f g : basis A -> C) :
    monotone f ->
    monotone g ->
    f ⊑ g ->
    co f ⊑ co g.
  Proof.
    intros Hf Hg Hfg t.
    apply ge_dsup.
    { apply directed_f_ideal; auto. }
    intro i.
    apply le_dsup with (i:=i).
    { apply directed_f_ideal; auto. }
    apply Hfg.
  Qed.

  Lemma monotone_coop_f {C} `{ldCPO C} (f g : basis A -> C) :
    antimonotone f ->
    antimonotone g ->
    f ⊑ g ->
    coop f ⊑ coop g.
  Proof.
    intros Hf Hg Hfg t.
    apply le_dinf.
    { apply downward_directed_f_ideal; auto. }
    intro i.
    apply ge_dinf with (i:=i).
    { apply downward_directed_f_ideal; auto. }
    apply Hfg.
  Qed.

  (** Two comorphisms are equal whenever their initial morphisms
      are. Alternate version of the uniqueness property that is
      sometimes useful. *)
  Corollary Proper_co {C} `{dCPO C} (f g : basis A -> C) :
    monotone f ->
    monotone g ->
    f === g ->
    co f === co g.
  Proof.
    intros Hf Hg Hfg.
    apply co_unique; auto.
    - apply continuous_co; auto.
    - rewrite <- Hfg.
      apply equ_arrow; intro b.
      apply co_incl'; auto.
  Qed.

  Corollary Proper_co' {C} `{dCPO C} (f g : basis A -> C) (x y : A) :
    monotone f ->
    monotone g ->
    f === g ->
    x === y ->
    co f x === co g y.
  Proof.
    intros Hf Hg Hfg Hxy.
    unfold monotone in Hf.
    rewrite Hxy; clear Hxy.
    revert y; apply equ_arrow, Proper_co; auto.
  Qed.

  Theorem co_intro (P : basis A -> Prop) (a : A) (i : nat) :
    monotone P ->
    P (ideal a i) ->
    co P a.
  Proof.
    intros Hmono HP; unfold co.
    assert (Hch: directed (P ∘ ideal a)).
    { apply directed_f_ideal; auto. }
    generalize (dsup_spec (P ∘ ideal a) Hch).
    intros [Hub Hlub].
    eapply Hub; eauto.
  Qed.

  Theorem coop_intro (P : basis A -> Prop) (a : A) :
    antimonotone P ->
    (forall i, P (ideal a i)) ->
    coop P a.
  Proof.
    intros Hmono HP; unfold coop.
    assert (Hch: downward_directed (P ∘ ideal a)).
    { apply downward_directed_f_ideal; auto. }
    generalize (dinf_spec (P ∘ ideal a) Hch).
    intros [Hub Hlub].
    unfold lower_bound in Hub.
    simpl in *; unfold flip, impl in *.
    eapply Hlub; eauto.
    intro i; simpl; unfold flip, impl.
    intro Hx; apply HP.
  Qed.

  Theorem co_elim (P : basis A -> Prop) (a : A) :
    monotone P ->
    co P a ->
    exists i, P (ideal a i).
  Proof.
    intros Hmono HP; unfold co.
    assert (Hch: directed (P ∘ ideal a)).
    { apply directed_f_ideal; auto. }
    generalize (dsup_spec (P ∘ ideal a) Hch).
    intros [Hub Hlub].
    apply Hlub; auto.
    intros i Hi; exists i; auto.
  Qed.

  Theorem coop_elim (P : basis A -> Prop) (a : A) :
    antimonotone P ->
    coop P a ->
    forall i, P (ideal a i).
  Proof.
    intros Hmono HP; unfold coop.
    assert (Hch: downward_directed (P ∘ ideal a)).
    { apply downward_directed_f_ideal; auto. }
    generalize (dinf_spec (P ∘ ideal a) Hch).
    intros [Hub Hlub] i.
    apply Hub, HP.
  Qed.

  Theorem co_intro2 {C} (R : basis A -> C -> Prop) (a : A) (c : C) (i : nat) :
    monotone R ->
    R (ideal a i) c ->
    co R a c.
  Proof.
    intros Hmono HR; unfold co.
    assert (Hch: directed (R ∘ ideal a)).
    { apply directed_f_ideal; auto. }
    generalize (dsup_spec (R ∘ ideal a) Hch).
    intros [Hub Hlub].
    eapply Hub; eauto.
  Qed.
  
  Theorem coop_intro2 {C} (R : basis A -> C -> Prop) (a : A) (c : C) :
    antimonotone R ->
    (forall i, R (ideal a i) c) ->
    coop R a c.
  Proof.
    intros Hmono HR; unfold coop.
    assert (Hch: downward_directed (R ∘ ideal a)).
    { apply downward_directed_f_ideal; auto. }
    generalize (dinf_spec (R ∘ ideal a) Hch).
    intros [Hub Hlub].
    unfold upper_bound in Hub.
    simpl in *; unfold flip, impl in *.
    eapply Hlub with (x := (fun x => forall i, R (ideal a i) x)).
    { intros i x Hx; apply Hx. }
    auto.
  Qed.

  Theorem co_elim2 {C} (R : basis A -> C -> Prop) (a : A) (c : C) :
    monotone R ->
    co R a c ->
    exists i, R (ideal a i) c.
  Proof.
    intros Hmono HR; unfold co.
    assert (Hch: directed (R ∘ ideal a)).
    { apply directed_f_ideal; auto. }
    generalize (dsup_spec (R ∘ ideal a) Hch).
    intros [Hub Hlub].
    unfold upper_bound in Hub.
    assert (Hx: upper_bound (fun c => exists i, R (ideal a i) c) (R ∘ ideal a)).
    { intro i; exists i; auto. }
    apply Hlub in Hx.
    apply Hx; auto.
  Qed.

  Theorem coop_elim2 {C} (R : basis A -> C -> Prop) (a : A) (c : C) :
    antimonotone R ->
    coop R a c ->
    forall i, R (ideal a i) c.
  Proof.
    intros Hmono HR; unfold coop.
    assert (Hch: downward_directed (R ∘ ideal a)).
    { apply downward_directed_f_ideal; auto. }
    generalize (dinf_spec (R ∘ ideal a) Hch).
    intros [Hub Hlub] i.
    apply Hub, HR.
  Qed.

  Lemma coop_elim2' {C} (R : basis A -> C -> Prop) (a : A) (c : C) :
    antimonotone R ->
    coop R a c ->
    forall i, R (ideal a i) c.
  Proof.
    intros Hmono HR; unfold coop.
    assert (Hch: downward_directed (R ∘ ideal a)).
    { apply downward_directed_f_ideal; auto. }
    generalize (dinf_spec (R ∘ ideal a) Hch).
    intros [Hub Hlub] i.
    apply Hub, HR.
  Qed.

  (** Every continuous function is a comorphism that is fully
      determined by its behavior on basis elements. *)
  Corollary continuous_co_incl {C} `{dCPO C} (g : A -> C) :
    continuous g ->
    g === co (g ∘ incl).
  Proof.
    intro Hg.
    apply equ_arrow; intro a.
    unfold co, compose.
    symmetry; apply supremum_sup.
    apply Hg.
    { apply directed_f_ideal, monotone_incl. }
    apply supremum_ideal.
  Qed.

  Theorem cocontinuous_coop_incl {C} `{ldCPO C} (g : A -> C) :
    cocontinuous g ->
    g === coop (g ∘ incl).
  Proof.
    intro Hg.
    apply equ_arrow; intro a.
    unfold coop, compose.
    symmetry; apply infimum_inf.
    apply Hg.
    { apply directed_f_ideal, monotone_incl. }
    apply supremum_ideal.
  Qed.

  Corollary continuous_ind {C} `{dCPO C} (f : A -> C) (g : A -> C) :
    continuous f ->
    continuous g ->
    f ∘ incl === g ∘ incl ->
    f === g.
  Proof.
    intros Hf Hg Hfg.
    pose proof Hf as Hf'.
    apply continuous_co_incl in Hf'.
    rewrite Hf'.
    rewrite Proper_co.
    { symmetry; apply continuous_co_incl; auto. }
    { apply monotone_compose.
      - apply monotone_incl.
      - apply continuous_monotone; auto. }
    { apply monotone_compose.
      - apply monotone_incl.
      - apply continuous_monotone; auto. }
    auto.
  Qed.

  Corollary cocontinuous_ind {C} `{ldCPO C} (f : A -> C) (g : A -> C) :
    cocontinuous f ->
    cocontinuous g ->
    f ∘ incl === g ∘ incl ->
    f === g.
  Proof.
    intros Hf Hg Hfg.
    pose proof Hf as Hf'.
    apply cocontinuous_coop_incl in Hf'.
    rewrite Hf'.
    rewrite Proper_coop.
    { symmetry; apply cocontinuous_coop_incl; auto. }
    { apply monotone_antimonotone_compose.
      - apply monotone_incl.
      - apply cocontinuous_antimonotone; auto. }
    { apply monotone_antimonotone_compose.
      - apply monotone_incl.
      - apply cocontinuous_antimonotone; auto. }
    auto.
  Qed.
End aCPO.

#[global] Hint Resolve directed_f_ideal : aCPO.
#[global] Hint Resolve monotone_incl : aCPO.
#[global] Hint Resolve monotone_co : aCPO.
#[global] Hint Resolve continuous_co : aCPO.
#[global] Hint Resolve antimonotone_coop : aCPO.
#[global] Hint Resolve cocontinuous_coop : aCPO.

(** Fusion rule for comorphism composition. A comorphism can be
    extended by a continuous function at the front, resulting in a new
    comorphism. I.e., given monotone f and continuous g:

    [ g ∘ co f = co (g ∘ f) ]

    An immediate consequence is that any chain of continuous function
    compositions can be written as a single comorphism as long as the
    rightmost (the one directly receiving the input) function in the
    chain is a comorphism. We only need to maintain an algebraic hold
    over the input space.  *)

Theorem co_co {A aB B C} `{aCPO A aB} `{dCPO B} `{dCPO C}
  (f : basis A -> B) (g : B -> C) :
  monotone f ->
  wcontinuous g ->
  g ∘ co f === co (g ∘ f).
Proof.
  intros Hf Hg.
  unfold co, compose.
  apply equ_arrow; intro t.
  assert (Heq: g (sup (fun x : nat => f (ideal t x))) ===
                 sup (fun i => g (f (ideal t i)))).
  { apply wcontinuous_sup; auto; apply chain_f_ideal; auto. }
  rewrite Heq; clear Heq.
  reflexivity.
Qed.

(** Pointwise variant of the fusion rule. *)
Corollary co_co' {A aB B C} `{aCPO A aB} `{dCPO B} `{dCPO C}
  (f : basis A -> B) (g : B -> C) (x : A) :
  monotone f ->
  wcontinuous g ->
  g (co f x) === co (g ∘ f) x.
Proof.
  intros Hf Hg; revert x; apply equ_arrow, co_co; auto with aCPO.
Qed.

Corollary co_co'' {A aB B bB C} `{aCPO A aB} `{aCPO B bB} `{dCPO C}
  (f : basis A -> B) (g : basis B -> C) (x : A) :
  monotone f ->
  monotone g ->
  co g (co f x) === co (co g ∘ f) x.
Proof.
  intros Hf Hg; revert x; apply equ_arrow, co_co; auto with aCPO order.
Qed.

Theorem coop_coop {A aB B C} `{aCPO A aB} `{ldCPO B} `{ldCPO C}
  (f : basis A -> B) (g : B -> C) :
  antimonotone f ->
  dec_continuous g ->
  g ∘ coop f === coop (g ∘ f).
Proof.
  intros Hf Hg.
  unfold co, coop, compose.
  apply equ_arrow; intro t.
  assert (Heq: g (inf (fun x : nat => f (ideal t x))) ===
                 inf (fun i => g (f (ideal t i)))).
  { apply dec_continuous_inf; auto.
    apply downward_directed_f_ideal; auto. }
  rewrite Heq; clear Heq.
  reflexivity.
Qed.

Theorem co_coop {A aB B C} `{aCPO A aB} `{dCPO B} `{ldCPO C}
  (f : basis A -> B) (g : B -> C) :
  monotone f ->
  cocontinuous g ->
  g ∘ co f === coop (g ∘ f).
Proof.
  intros Hf Hg.
  unfold co, coop, compose.
  apply equ_arrow; intro t.
  assert (Heq: g (sup (fun x : nat => f (ideal t x))) ===
                 inf (fun i => g (f (ideal t i)))).
  { apply cocontinuous_sup; auto.
    apply directed_f_ideal; auto. }
  rewrite Heq; clear Heq.
  reflexivity.
Qed.

(** Pointwise variant. *) 
Corollary co_coop' {A aB B C} `{aCPO A aB} `{dCPO B} `{ldCPO C}
  (f : basis A -> B) (g : B -> C) (a : A) :
  monotone f ->
  cocontinuous g ->
  g (co f a) === coop (g ∘ f) a.
Proof.
  intros Hf Hg; revert a; apply equ_arrow.
  apply co_coop; auto with aCPO.
Qed.

Theorem coop_co {A aB B C} `{aCPO A aB} `{ldCPO B} `{dCPO C}
  (f : basis A -> B) (g : B -> C) :
  antimonotone f ->
  dec_cocontinuous g ->
  g ∘ coop f === co (g ∘ f).
Proof.
  intros Hf Hg.
  unfold co, coop, compose.
  apply equ_arrow; intro t.
  assert (Heq: g (inf (fun x : nat => f (ideal t x))) ===
                 sup (fun i => g (f (ideal t i)))).
  { apply dec_cocontinuous_inf; auto.
    apply downward_directed_f_ideal; auto. }
  rewrite Heq; clear Heq.
  reflexivity.
Qed.

(** Pointwise variant. *) 
Corollary coop_co' {A aB B C} `{aCPO A aB} `{ldCPO B} `{dCPO C}
  (f : basis A -> B) (g : B -> C) (a : A) :
  antimonotone f ->
  dec_cocontinuous g ->
  g (coop f a) === co (g ∘ f) a.
Proof.
  intros Hf Hg; revert a; apply equ_arrow.
  apply coop_co; auto with aCPO.
Qed.

Corollary co_coP {A aB B} `{aCPO A aB} `{dCPO B}
  (f : basis A -> B) (g : B -> Prop) (x : A) :
  monotone f ->
  continuous g ->
  g (co f x) <-> co (g ∘ f) x.
Proof. intros Hf Hg; apply equ_iff, co_co'; auto with order. Qed.

Theorem co_coopP {A aB B C} `{aCPO A aB} `{dCPO B} `{ldCPO C}
  (f : basis A -> B) (g : B -> Prop) (a : A) :
  monotone f ->
  cocontinuous g ->
  g (co f a) <-> coop (g ∘ f) a.
Proof. intros Hf Hg; apply equ_iff, co_coop'; auto. Qed.

Corollary coop_coP {A aB B} `{aCPO A aB} `{ldCPO B}
  (f : basis A -> B) (g : B -> Prop) (x : A) :
  antimonotone f ->
  dec_cocontinuous g ->
  g (coop f x) <-> co (g ∘ f) x.
Proof.
  intros Hf Hg.
  cut (g (coop f x) === co (g ∘ f) x).
  { firstorder. }
  revert x; apply equ_arrow.
  apply coop_co; auto.
Qed.

Lemma co_incl_id {A B} `{aCPO A B} :
  co incl === @id A.
Proof.
  symmetry; apply co_unique.
  - apply monotone_incl.
  - apply continuous_id.
  - reflexivity.
Qed.

Lemma co_incl_id' {A B} `{aCPO A B} (x : A) :
  co incl x === x.
Proof. revert x; apply equ_arrow, co_incl_id. Qed.

Ltac cointro := try eapply co_intro; try eapply coop_intro.
Ltac cointro2 := try eapply co_intro2; try eapply coop_intro2.
Ltac coelim H := try eapply co_elim in H; try eapply coop_elim in H.
Ltac coelim2 := try eapply co_elim2; try eapply coop_elim2.
