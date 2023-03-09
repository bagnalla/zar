(** * Extended non-negative reals. *)

(** The eRauto tactic is handy for reducing/solving goals involving
  extended reals. *)

From Coq Require Import
  Lra
  Lia
  Basics
  QArith
  Qminmax
  Equivalence
  List
.

Local Open Scope program_scope.
Local Open Scope equiv_scope.

From Coq Require Import
  Reals
  ProofIrrelevance
  ClassicalChoice
.

Local Open Scope R_scope.

From zar Require Import
  cpo
  misc
  order
  Q
  R
  tactics
.

Local Open Scope order_scope.

Create HintDb eR.
Declare Scope eR_scope.

Inductive eR :=
| er : forall r : R, 0 <= r -> eR
| infty : eR.

Definition eR0 : eR := er 0 (Rle_refl 0).
Definition eR1 : eR := er 1 Rle_0_1.
Lemma Rle_0_2 : 0 <= 2. lra. Qed.
Definition eR2 : eR := er 2 Rle_0_2.

Notation "0" := eR0 : eR_scope.
Notation "1" := eR1 : eR_scope.
Notation "2" := eR2 : eR_scope.

Inductive eRle : eR -> eR -> Prop :=
| eRle_infty : forall r, eRle r infty
| eRle_R : forall r1 pf1 r2 pf2, r1 <= r2 -> eRle (er r1 pf1) (er r2 pf2).
#[global] Hint Constructors eRle : eR.

Inductive eRlt : eR -> eR -> Prop :=
| eRlt_infty : forall r pf, eRlt (er r pf) infty
| eRlt_R : forall r1 pf1 r2 pf2, r1 < r2 -> eRlt (er r1 pf1) (er r2 pf2).
#[global] Hint Constructors eRlt : eR.

Infix "<=" := eRle : eR_scope.
Infix "<" := eRlt : eR_scope.
Open Scope eR_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : eR_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : eR_scope.
Notation "x < y < z" := (x < y /\ y < z) : eR_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : eR_scope.

Lemma eR_eq r1 pf1 r2 pf2 :
  r1 = r2 ->
  er r1 pf1 = er r2 pf2.
Proof. intros ->; f_equal; apply proof_irrelevance. Qed.

Lemma eRle_antisym (a b : eR) :
  a <= b -> b <= a -> a = b.
Proof.
  intros Hab Hba; inv Hab; auto; inv Hba; auto; apply eR_eq; lra.
Qed.

Lemma eRlt_le_dec : forall (r1 r2 : eR) , {r1 < r2} + {r2 <= r1}.
Proof.
  intros [a|] [b|].
  - destruct (Rlt_le_dec a b).
    + left; constructor; auto.
    + right; constructor; auto.
  - left; constructor.
  - right; constructor.
  - right; constructor.
Qed.

Lemma eRlt_le a b :
  a < b ->
  a <= b.
Proof. intro Hab; inv Hab; constructor; lra. Qed.
#[global] Hint Resolve eRlt_le : eR.

Lemma eRlt_neq a b :
  a < b ->
  a <> b.
Proof. intro Ha; inv Ha; intro HC; inv HC; lra. Qed.
#[global] Hint Resolve eRlt_neq : eR.

Lemma eRlt_neq' a b :
  b < a ->
  a <> b.
Proof. intro Ha; inv Ha; intro HC; inv HC; lra. Qed.
#[global] Hint Resolve eRlt_neq' : eR.

Lemma neq_eRlt_0 a :
  a <> 0 ->
  0 < a.
Proof.
  intro HC; destruct a; constructor.
  apply Rle_not_eq_Rlt; auto.
  intro H; subst; apply HC; apply eR_eq; reflexivity.
Qed.
#[global] Hint Resolve neq_eRlt_0 : eR.

Lemma eR_eq_dec (a b : eR) :
  {a = b} + {a <> b}.
Proof.
  destruct (eRlt_le_dec a b).
  - right; intro HC; subst; inv e; lra.
  - destruct (eRlt_le_dec b a).
    + right; intro HC; subst; inv e0; lra.
    + left; apply eRle_antisym; auto.
Qed.

Ltac eRdec :=
  match goal with
  | [ |- context[eR_eq_dec ?x ?y] ] =>
      destruct (eR_eq_dec x y); subst; try congruence
  end.

Definition eRplus (r1 r2 : eR) : eR :=
  match (r1, r2) with
  | (infty, _) => infty
  | (_, infty) => infty
  | (er a pf1, er b pf2) => er (a + b) (Rplus_le_le_0_compat a b pf1 pf2)
  end.

Definition eRminus (r1 r2 : eR) : eR :=
  match (r1, r2) with
  | (infty, er _ _) => infty
  | (_, infty) => 0
  | (er a _, er b _) => match Rle_dec b a with
                       | left pf => er (a - b) (Rminus_0_le a b pf)
                       | right _ => 0
                       end
  end.

Definition eRmult (r1 r2 : eR) : eR :=
  match (r1, r2) with
  | (infty, _) => if eR_eq_dec r2 0 then 0 else infty
  | (_, infty) => if eR_eq_dec r1 0 then 0 else infty
  | (er a pf1, er b pf2) => er (a * b) (Rmult_le_pos a b pf1 pf2)
  end.

Definition eRinv (r : eR) : eR :=
  match r with
  | infty => 0
  | er a pf => match R_eq_dec a 0 with
              | left _ => infty
              | right pf' => er (Rinv a) (Rlt_le _ _ (Rinv_0_lt_compat _
                                                       (Rle_not_eq_Rlt _ _ pf pf')))
              end
  end.

Fixpoint eRpow (r : eR) (n : nat) : eR :=
  match n with
  | O => 1
  | S n => eRmult r (eRpow r n)
  end.

Infix "+" := eRplus : eR_scope.
Infix "-" := eRminus : eR_scope.
Infix "*" := eRmult : eR_scope.
Infix "^" := eRpow : eR_scope.
Notation "/ x" := (eRinv x) : eR_scope.

Definition eRdiv (r1 r2 : eR) : eR := r1 * / r2.
Infix "/" := eRdiv : eR_scope.

Lemma eRle_refl (a : eR) :
  a <= a.
Proof. destruct a; constructor; lra. Qed.
#[global] Hint Resolve eRle_refl : eR.

#[global]
  Instance Reflexive_eRle : Reflexive eRle.
Proof. intro a; apply eRle_refl. Qed.

#[global]
  Instance Transitive_eRle : Transitive eRle.
Proof.
  intros a b c Hab Hbc; inv Hab; try solve[constructor]; inv Hbc; constructor; lra.
Qed.

#[global]
  Program Instance OType_eR : OType eR :=
  { leq := eRle }.
Next Obligation. constructor; typeclasses eauto. Qed.

Lemma eR0_le a :
  0 <= a.
Proof. destruct a; constructor; auto. Qed.
#[global] Hint Resolve eR0_le : eR.

Definition proj_eR (r : eR) : R :=
  match r with
  | er a _ => a
  | infty => 0
  end.

Lemma proj_eR_nonnegative (r : eR) :
  (0 <= proj_eR r)%R.
Proof. destruct r; simpl; lra. Qed.

(* Three cases:
   1) infty appears in f, so the lub is infty,
   2) infty doesn't appear but there is no upper bound of f, so the
      lub is infty,
   3) f is bounded above by some real b, so the bounded completeness
      property of the reals applies.
 *)
Lemma eR_complete {A} `{Inhabited A} (f : A -> eR) :
  exists s : eR, supremum s f.
Proof.
  destruct (classic (exists i, f i = infty)) as [Hf|Hf].
  { exists infty; split.
    - intro i; constructor.
    - intros x Hx; destruct Hf as [i Hf].
      specialize (Hx i); inv Hx; try constructor; congruence. }    
  destruct (classic (bounded_above (proj_eR ∘ f))) as [H0|H0].
  { destruct H0 as [x Hx].
    assert (Hbounded: bounded_above (proj_eR ∘ f)).
    { exists x; auto. }
    generalize (R_bounded_complete (proj_eR ∘ f) Hbounded); intros [s Hs].
    assert (Hle: (0 <= s)%R).
    { destruct H.
      destruct Hs as [Hs _].
      eapply Rle_trans.
      2: { apply (Hs el). }
      apply proj_eR_nonnegative. }
    exists (er s Hle).
    unfold compose in Hs.
    destruct Hs as [Hub Hlub]; split.
    - intro i; specialize (Hub i); simpl in Hub.        
      destruct (f i) eqn:Hfi.
      + simpl in Hub; constructor; auto.
      + exfalso; apply Hf; exists i; auto.
    - intros y Hy.
      destruct y.
      2: { constructor. }
      constructor.
      apply Hlub.
      intro i; specialize (Hy i); destruct (f i) eqn:Hfi.
      + inv Hy; simpl; auto.
      + exfalso; apply Hf; exists i; auto. }
  exists infty; split.
  - intro i; constructor.
  - intros x Hx; destruct x.
    + exfalso; apply H0; exists r; intro i; unfold compose.
      specialize (Hx i); inv Hx; simpl; auto.
    + constructor.
Qed.

Definition replace_inftys {A} (r : eR) (f : A -> eR) (x : A) : eR :=
  match f x with
  | infty => r
  | _ => f x
  end.

Lemma infimum_remove_infty {A} (a : eR) (f : A -> eR) (x : A) :
  f x <> infty ->
  infimum a (replace_inftys (f x) f) -> 
  infimum a f.
Proof.
  unfold compose, replace_inftys.
  intros Hfx [Hlb Hglb]; split.
  - intro y.
    specialize (Hlb y); simpl in Hlb.
    destruct (f y); auto; constructor.
  - intros r Hr; apply Hglb; intro y.
    specialize (Hlb y); simpl in Hlb.
    pose proof (Hr x) as Hx; simpl in Hx.
    specialize (Hr y); simpl in Hr.
    destruct (f y); auto.
Qed.

Lemma infimum_proj_eR {A} `{Inhabited A} (a : eR) (f : A -> eR) :
  a <> infty ->
  (forall x, f x <> infty) ->
  infimum (proj_eR a) (proj_eR ∘ f) ->
  infimum a f.
Proof.
  destruct H as [el].
  unfold compose.
  intros Ha Hfx [Hlb Hglb].
  destruct a as [a|]; try congruence; clear Ha; split.  
  - intro x.
    specialize (Hlb x). simpl in Hlb.
    destruct (f x); constructor; auto.
  - intros [x|] Hx.
    2: { specialize (Hx el); inv Hx; congruence. }
    constructor.
    apply Hglb.
    intro y; specialize (Hx y).
    specialize (Hfx y).
    destruct (f y); try congruence.
    inv Hx; auto.
Qed.

(* Either all elements of f are infty or not. If so, infty is the
   glb. Otherwise, prove by the following steps:

   1) remove all inftys from f and suffice to show infimum of the
      resulting f' exists.

   2) inject f' into a collection of reals f'' (injective since f'
      contains no inftys) and suffice to show f'' has an infimum in
      the reals.

   3) the negation of f'' has a supremum since it's bounded above by 0
      (since the original f'' is bounded below by 0), which is the
      infimum of f''.
 *)
Lemma eR_complete_inf {A} `{Inhabited A} (f : A -> eR) :
  exists s : eR, infimum s f.
Proof.
  destruct (classic (exists y, f y <> infty)) as [H0|H0].
  { destruct H0 as [x Hx].
    set (f' := proj_eR ∘ replace_inftys (f x) f).
    cut (exists s, supremum s (Ropp ∘ f')).
    { intros [s Hs].
      apply supremum_opp_infimum in Hs.
      assert (Hle: (0 <= - s)%R).
      { apply Hs; intro y; unfold f', compose, replace_inftys.
        destruct (f y); apply proj_eR_nonnegative. }
      exists (er (- s) Hle).
      eapply infimum_remove_infty; eauto.
      apply infimum_proj_eR; try congruence; auto.
      intro y; unfold replace_inftys; destruct (f y); auto; congruence. }
    { apply R_bounded_complete.
      exists 0%R.
      intro y; unfold compose. simpl.
      assert (0 <= f' y)%R.
      { unfold f', compose, replace_inftys; destruct (f y); apply proj_eR_nonnegative. }
      lra. } }
  { exists infty; split.
    - intro x; destruct (f x) eqn:Hfx; try constructor.
      exfalso; apply H0; exists x; congruence.
    - intros x Hx; constructor. }
Qed.

#[global]
  Instance lCPO_eR : lCPO eR.
Proof. constructor; intros f; apply eR_complete_inf. Qed.

#[global]
  Instance CPO_eR : CPO eR.
Proof. constructor; intros f; apply eR_complete. Qed.

Lemma eRplus_assoc (a b c : eR) :
  a + b + c = a + (b + c).
Proof. destruct a, b, c; unfold eRplus; auto; apply eR_eq; lra. Qed.

Lemma eRplus_comm (a b : eR) :
  a + b = b + a.
Proof. destruct a, b; unfold eRplus; auto; apply eR_eq; lra. Qed.

Lemma eRmult_assoc (a b c : eR) :
  a * b * c = a * (b * c).
Proof. 
  unfold eRmult.
  destruct a.
  - destruct b.
    + destruct c.
      * apply eR_eq; lra.
      * destr. inv e.
        { destruct (eR_eq_dec (er r1 r2) 0); simpl.
          - apply eR_eq; lra.
          - destr; try congruence.
            apply Rmult_integral in H0; destruct H0; subst.
            + exfalso; apply n0, eR_eq; reflexivity.
            + exfalso; apply n, eR_eq; reflexivity. }
        { destruct (eR_eq_dec (er r1 r2) 0); simpl.
          - inv e; exfalso; apply n, eR_eq; lra.
          - destr; auto; inv e.
            exfalso; apply n, eR_eq; lra. }
    + destruct (eR_eq_dec (er r r0) 0); simpl.
      * destruct c.
        { destruct (eR_eq_dec (er r1 r2) 0); apply eR_eq; lra. }
        destr; try congruence.
        destruct (eR_eq_dec infty 0); congruence.
      * destr; simpl; auto.
        apply eR_eq; lra.
  - destruct (eR_eq_dec b 0); subst; simpl.
    + destruct c.
      * destr.
        { apply eR_eq; lra. }
        { exfalso; apply n, eR_eq; lra. }
      * destr; reflexivity.
    + destr; subst; simpl.
      * destruct b.
        { destr; auto; exfalso; apply n0, eR_eq; lra. }
        { destr; congruence. }
      * destruct b.
        { destruct c.
          - destr; auto.
            inv e.
            apply Rmult_integral in H0; destruct H0; subst.
            + exfalso; apply n, eR_eq; reflexivity.
            + exfalso; apply n0, eR_eq; reflexivity.
          - destr; congruence. }
        destr; congruence.
Qed.

Lemma eRmult_comm (a b : eR) :
  a * b = b * a.
Proof. destruct a, b; auto; apply eR_eq; lra. Qed.

Lemma eRplus_0_l (a : eR) :
  eR0 + a = a.
Proof. destruct a; simpl; auto; apply eR_eq; lra. Qed.
#[global] Hint Resolve eRplus_0_l : eR.

Lemma eRplus_0_r (a : eR) :
  a + eR0 = a.
Proof. destruct a; simpl; auto; apply eR_eq; lra. Qed.
#[global] Hint Resolve eRplus_0_r : eR.

Lemma eRplus_infty_l (a : eR) :
  infty + a = infty.
Proof. destruct a; simpl; auto; apply eR_eq; lra. Qed.
#[global] Hint Resolve eRplus_infty_l : eR.

Lemma eRplus_infty_r (a : eR) :
  a + infty = infty.
Proof. destruct a; simpl; auto; apply eR_eq; lra. Qed.
#[global] Hint Resolve eRplus_infty_r : eR.

Lemma eRmult_plus_distr_l (a b c : eR) :
  a * (b + c) = a * b + a * c.
Proof.
  unfold eRmult.
  destruct a, b, c; simpl; try (apply eR_eq; lra);
    try (destr; try reflexivity; inv e; apply eR_eq; lra);
    repeat destr; try reflexivity; auto with eR;
    inv e; try inv e0; exfalso; apply n, eR_eq; lra.
Qed.

Lemma eRmult_plus_distr_r (a b c : eR) :
  (a + b) * c = a * c + b * c.
Proof.
  rewrite eRmult_comm, eRmult_plus_distr_l, eRmult_comm; f_equal; apply eRmult_comm.
Qed.

Lemma eRplus_le_compat_l (a b c : eR) :
  b <= c ->
  a + b <= a + c.
Proof.
  intro Hle; inv Hle; unfold eRplus; simpl;
    try constructor; destruct a; constructor; lra.
Qed.

Lemma eRplus_le_compat_r (a b c : eR) :
  a <= b ->
  a + c <= b + c.
Proof.
  intro Hle; inv Hle; unfold eRplus; simpl;
    try constructor; destruct c; constructor; lra.
Qed.

Lemma le_eR0 (a : eR) :
  a <= eR0 ->
  a = eR0.
Proof. intro H; inv H; apply eR_eq; lra. Qed.

Lemma eRmult_le_compat (a b c d : eR) :
  a <= c ->
  b <= d ->
  a * b <= c * d.
Proof.
  intros Hac Hbd.
  unfold eRmult.
  destruct a as [a|].
  - destruct b as [b|].
    + destruct c as [c|].
      * destruct d as [d|].
        { inv Hac; inv Hbd; constructor; nra. }
        inv Hac; destr.
        { inv e; constructor; nra. }
        constructor.
      * destr.
        { inv e; inv Hbd; constructor; nra. }
        constructor.
    + inv Hbd; destruct c as [c|].
      * inv Hac; destr.
        { apply eR0_le. }
        destr.
        { inv e; exfalso; apply n; apply eR_eq; lra. }
        reflexivity.
      * destr.
        { inv e; destr; apply eR0_le. }
        destr.
        { inv e. }
        reflexivity.
  - inv Hac; destr.
    + inv e; destr; apply eR0_le.
    + destr.
      * inv e; destruct b as [b|].
        { inv Hbd; exfalso; apply n; apply eR_eq; lra. }
        inv Hbd.
      * reflexivity.
Qed.

Lemma eRmult_le_compat_l (a b c : eR) :
  eR0 <= a ->
  b <= c ->
  a * b <= a * c.
Proof.
  intros Ha Hbc.
  unfold eRmult.
  destruct a.
  - inv Ha.
    destruct b.
    + destruct c.
      * inv Hbc; constructor; apply Rmult_le_compat_l; auto.
      * destr.
        { inv e; constructor; lra. }
        { constructor. }
    + destr.
      * apply eR0_le.
      * destruct c; try constructor; inv Hbc.
  - repeat destr; auto with eR; subst.
    inv Hbc; exfalso; apply n, eR_eq; lra.
Qed.

Lemma eRmult_le_compat_r (a b c : eR) :
  a <= b ->
  a * c <= b * c.
Proof.
  intros Hab.
  replace (a * c) with (c * a) by apply eRmult_comm.
  replace (b * c) with (c * b) by apply eRmult_comm.
  apply eRmult_le_compat_l; auto; apply eR0_le.
Qed.

Lemma eRplus_le_compat :
  forall r1 r2 r3 r4, r1 <= r2 -> r3 <= r4 -> r1 + r3 <= r2 + r4.
Proof.
  intros; transitivity (r2 + r3).
  - apply eRplus_le_compat_r; auto.
  - apply eRplus_le_compat_l; auto.
Qed.

Lemma eRlt_le_trans a b c :
  a < b ->
  b <= c ->
  a < c.
Proof.
  intros Hab Hbc.
  inv Hab.
  - inv Hbc; constructor.
  - destruct c as [c|].
    + inv Hbc; constructor; lra.
    + constructor.
Qed.

Lemma eRplus_lt_compat_r a b c :
  c <> infty ->
  a < b ->
  a + c < b + c.
Proof.
  intros Hc Hab.
  destruct c as [c|]; try congruence.
  destruct a as [a|].
  - destruct b as [b|].
    + inv Hab; constructor; lra.
    + constructor.
  - inv Hab.
Qed.

Lemma eRplus_lt_compat_l a b c :
  c <> infty ->
  a < b ->
  c + a < c + b.
Proof.
  intros Hc Hab.
  rewrite eRplus_comm.
  replace (c + b) with (b + c) by apply eRplus_comm.
  apply eRplus_lt_compat_r; auto.
Qed.

Lemma eRplus_lt_compat a b c d :
  c <> infty ->
  a < b -> c <= d -> a + c < b + d.
Proof.
  intros Hc Hab Hcd.
  intros; apply eRlt_le_trans with (b + c).
  - apply eRplus_lt_compat_r; auto.
  - apply eRplus_le_compat_l; auto.
Qed.

Lemma eRmult_0_l (a : eR) :
  0 * a = 0.
Proof.
  unfold eRmult; simpl; destruct a.
  - apply eR_eq; lra.
  - destr; congruence.
Qed.
#[global] Hint Resolve eRmult_0_l : eR.

Lemma eRmult_0_l' (a : eR) pf :
  er 0 pf * a = 0.
Proof.
  unfold eRmult; simpl; destruct a.
  - apply eR_eq; lra.
  - destr; auto; exfalso; apply n, eR_eq; reflexivity.
Qed.
#[global] Hint Resolve eRmult_0_l : eR.

Lemma eRmult_0_r (a : eR) :
  a * 0 = 0.
Proof.
  unfold eRmult; simpl; destruct a.
  - apply eR_eq; lra.
  - destr; congruence.
Qed.
#[global] Hint Resolve eRmult_0_r : eR.

Lemma eRmult_1_l (a : eR) :
  eR1 * a = a.
Proof.
  unfold eRmult; simpl.
  destruct a.
  - apply eR_eq; lra.
  - destr; auto; inv e; lra.
Qed.
#[global] Hint Resolve eRmult_1_l : eR.

Lemma eRmult_1_r (a : eR) :
  a * eR1 = a.
Proof. 
  unfold eRmult; simpl.
  destruct a.
  - apply eR_eq; lra.
  - destr; auto; inv e; lra.
Qed.
#[global] Hint Resolve eRmult_1_r : eR.

Lemma eRmult_infty_l (a : eR) :
  a <> 0 ->
  infty * a = infty.
Proof. intro Ha; unfold eRmult; destr; congruence. Qed.
#[global] Hint Resolve eRmult_infty_l : eR.

Lemma eRmult_infty_r (a : eR) :
  a <> 0 ->
  a * infty = infty.
Proof. intro Ha; unfold eRmult; destruct a; destr; congruence. Qed.
#[global] Hint Resolve eRmult_infty_r : eR.

Lemma Q2R_0_le (q : Q) :
  (0 <= q)%Q ->
  (0 <= Q2R q)%R.
Proof. intro Hq; apply Qreals.Qle_Rle in Hq; lra. Qed.

Definition Q2eR (q : Q) : eR := er (Q2R (Qmax 0 q)) (Q2R_0_le _ (Q.le_max_l _ _)).

#[global]
  Instance Proper_Q2eR : Proper (Qeq ==> eq) Q2eR.
Proof.
  intros p q Hpq; unfold Q2eR; apply eR_eq; rewrite Hpq; reflexivity.
Qed.

Lemma Q2eR_div (a b : Q) :
  (0 <= a)%Q ->
  (0 < b)%Q ->
  Q2eR (a / b) = Q2eR a / Q2eR b.
Proof.
  unfold Q2eR, eRdiv, eRmult, eRinv.
  intros Ha Hb.
  destruct (R_eq_dec (Q2R (Qmax 0 b)) 0).
  - destr.
    + inv e0; apply eR_eq.
      rewrite Q.max_r in H0; auto.
      replace 0%R with (Q2R 0%Q) in * by lra.
      apply Qreals.eqR_Qeq in H0.
      apply Qreals.Qeq_eqR.
      apply Q.max_l.
      rewrite H0.
      rewrite Qdiv_0_num.
      apply Qle_refl.
    + Import Lqa.
      rewrite Q.max_r in e; try lra.
      replace 0%R with (Q2R 0%Q) in e by apply RMicromega.Q2R_0.
      apply Qreals.eqR_Qeq in e; lra.
      Import Lra.
  - assert (H: ~ b == 0).
    { intro HC; apply n; rewrite HC; compute; lra. }
    assert (Heq: Qmax 0 (a / b) == a / b).
    { apply Q.max_r.
      Import Lqa.
      apply Qle_shift_div_l; auto; lra.
      Import Lra. }
    apply eR_eq.
    rewrite Heq; clear Heq.
    unfold Qdiv; rewrite Qreals.Q2R_mult.
    f_equal.
    + apply Qreals.Qeq_eqR; rewrite Q.max_r; auto; reflexivity.
    + rewrite Qreals.Q2R_inv; auto.
      rewrite Q.max_r; try reflexivity.
      apply Qlt_le_weak; auto.
Qed.

Corollary Q2eR_one_half :
  Q2eR (1#2) = 1 / 2.
Proof.
  replace (1#2) with (1/2)%Q by reflexivity.
  rewrite Q2eR_div.
  - f_equal; apply eR_eq; compute; lra.
  - apply Q0_le_1.
  - apply Q0_lt_2.
Qed.

Lemma eRminus_Q2eR_not_infty (a : R) pf (q : Q) :
  er a pf - Q2eR q <> infty.
Proof. unfold eRminus; simpl; destr; intro HC; inv HC. Qed.
#[global] Hint Resolve eRminus_Q2eR_not_infty : eR.

Corollary eR1_eRminus_Q2eR_not_infty (q : Q) :
  eR1 - Q2eR q <> infty.
Proof. apply eRminus_Q2eR_not_infty. Qed.
#[global] Hint Resolve eR1_eRminus_Q2eR_not_infty : eR.

Lemma Q2eR_0 :
  Q2eR 0 = 0.
Proof. apply eR_eq; compute; lra. Qed.

Lemma Q2eR_1 :
  Q2eR 1 = 1.
Proof. apply eR_eq; compute; lra. Qed.

Lemma Q2eR_le (a b : Q) :
  (a <= b)%Q ->
  Q2eR a <= Q2eR b.
Proof.
  intros Hab; constructor.
  apply Qreals.Qle_Rle.
  apply Q.max_le_compat_l; auto.
Qed.  
#[global] Hint Resolve Q2eR_le : eR.

Corollary Q2eR_le_1 (a : Q) :
  (a <= 1)%Q ->
  Q2eR a <= 1.
Proof.
  intro Ha.
  replace 1 with (Q2eR 1).
  - apply Q2eR_le; auto.
  - apply eR_eq; compute; lra.
Qed.
#[global] Hint Resolve Q2eR_le_1 : eR.

Corollary Q2eR_le_0_1 (a : Q) :
  (0 <= a <= 1)%Q ->
  Q2eR a <= 1.
Proof. intros [_ Ha]; apply Q2eR_le_1; auto. Qed.
#[global] Hint Resolve Q2eR_le_0_1 : eR.

Lemma equ_eR (a b : eR) :
  a === b <-> a = b.
Proof.
  unfold equ, leq; simpl; split.
  - intros [H0 H1]; inv H0; inv H1; auto; apply eR_eq; lra.
  - intros ->; split; reflexivity.
Qed.

Lemma equ_f_eR {A} (f g : A -> eR) :
  f === g <-> f = g.
Proof.
  split.
  - intros [Hfg Hgf].
    ext s; specialize (Hfg s); specialize (Hgf s).
    unfold leq in *; simpl in *; apply eRle_antisym; auto.
  - intros ->; reflexivity.
Qed.

Lemma eRle_dec : forall r1 r2, {r1 <= r2} + {~ r1 <= r2}.
Proof.
  intros [] [].
  - destruct (Rle_dec r r1).
    + left; constructor; auto.
    + right; intro HC; inv HC; lra.
  - left; constructor.
  - right; intro HC; inv HC.
  - left; reflexivity.
Qed.

Lemma proj_eR_0_le (a : eR) :
  (0 <= proj_eR a)%R.
Proof. destruct a; simpl; lra. Qed.
#[global] Hint Resolve proj_eR_0_le : eR.

Lemma chain_proj_eR f :
  (forall i, f i <> infty) ->
  chain f ->
  chain (fun i => proj_eR (f i)).
Proof.
  intros H Hf i; simpl.
  specialize (Hf i); inv Hf; simpl; try lra.
  exfalso; eapply H; eauto.
Qed.
#[global] Hint Resolve chain_proj_eR : eR.

Lemma dec_chain_proj_eR f :
  (forall i, f i <> infty) ->
  dec_chain f ->
  dec_chain (fun i => proj_eR (f i)).
Proof.
  intros H Hf i; simpl.
  specialize (Hf i); inv Hf; simpl; try lra.
  exfalso; eapply H; eauto.
Qed.
#[global] Hint Resolve dec_chain_proj_eR : eR.

Lemma supremum_er_not_infty {I} (a : R) pf (f : I -> eR) i :
  supremum (er a pf) f ->
  f i <> infty.
Proof.
  intros [Hub Hlub] HC; specialize (Hub i); rewrite HC in Hub; inv Hub.
Qed.
#[global] Hint Resolve supremum_er_not_infty : eR.

Lemma supremum_er_proj_eR {A} `{Inhabited A} (a : R) pf (f : A -> eR) :
  (forall i, f i <> infty) ->
  supremum (er a pf) f ->
  supremum a (fun i => proj_eR (f i)).
Proof.
  intros Hfi [Hub Hlub]; split.
  - intro i; specialize (Hub i); inv Hub; simpl; lra.
  - intros x Hx.
    assert (Hle: (0 <= x)%R).
    { destruct H as [el]; specialize (Hx el).
      simpl in Hx.
      eapply Rle_trans.
      - apply proj_eR_0_le.
      - eauto. }
    assert (Hx': upper_bound (er x Hle) f).
    { intro i; specialize (Hx i); simpl in Hx.
      destruct (f i) eqn:Hfi'; eauto.
      2: { exfalso; apply (Hfi i); auto. }
      constructor; auto. }
    apply Hlub in Hx'; inv Hx'; simpl; lra.
Qed.
#[global] Hint Resolve supremum_er_proj_eR : eR.

Lemma infimum_er_proj_eR {A} `{Inhabited A} (a : R) pf (f : A -> eR) :
  (forall i, f i <> infty) ->
  infimum (er a pf) f ->
  infimum a (fun i => proj_eR (f i)).
Proof.
  intros Hfi [Hlb Hglb]; split.
  - intro i; specialize (Hlb i); inv Hlb; simpl; try congruence; lra.
  - intros x Hx.
    destruct (Rle_dec 0 x).
    { assert (Hx': lower_bound (er x r) f).
      { intro i; specialize (Hx i); simpl in Hx.
        destruct (f i) eqn:Hfi'; eauto.
        2: { exfalso; apply (Hfi i); auto. }
        constructor; auto. }
      apply Hglb in Hx'; inv Hx'; simpl; lra. }
    simpl; lra.
Qed.    
#[global] Hint Resolve infimum_er_proj_eR : eR.

Lemma supremum_proj_eR_er {A} (a : R) pf (f : A -> eR) :
  (forall i, f i <> infty) ->
  supremum a (fun i => proj_eR (f i)) ->
  supremum (er a pf) f.
Proof.
  intros Hfi [Hub Hlub]; split.
  - intro i; specialize (Hub i); simpl in Hub.
    destruct (f i) eqn:Hfi'.
    2: { exfalso; apply (Hfi i); auto. }
    constructor; apply Hub.
  - intros x Hx; destruct x as [x|]; constructor.
    apply Hlub; intro i.
    specialize (Hx i).
    destruct (f i) eqn:Hfi'.
    2: { exfalso; apply (Hfi i); auto. }
    inv Hx; auto.
Qed.
#[global] Hint Resolve supremum_proj_eR_er : eR.

Lemma infimum_proj_eR_er {A} `{Inhabited A} (a : R) pf (f : A -> eR) :
  (forall i, f i <> infty) ->
  infimum a (fun i => proj_eR (f i)) ->
  infimum (er a pf) f.
Proof.
  intros Hfi [Hub Hlub]; split.
  - intro i; specialize (Hub i); simpl in Hub.
    destruct (f i) eqn:Hfi'.
    2: { exfalso; apply (Hfi i); auto. }
    constructor; apply Hub.
  - intros x Hx; destruct x as [x|].
    2: { destruct H as [el]. specialize (Hx el).
         inv Hx; specialize (Hfi el); congruence. }
    constructor.
    apply Hlub; intro i.
    specialize (Hx i).
    destruct (f i) eqn:Hfi'.
    2: { exfalso; apply (Hfi i); auto. }
    inv Hx; auto.
Qed.

Lemma proj_eR_sum a b :
  a <> infty ->
  b <> infty ->
  proj_eR (a + b) = (proj_eR a + proj_eR b)%R.
Proof. intros Ha Hb; destruct a, b; try congruence; auto. Qed.
#[global] Hint Resolve proj_eR_sum : eR.

Lemma sum_not_infty a b :
  a <> infty ->
  b <> infty ->
  a + b <> infty.
Proof. intros Ha Hb HC; destruct a, b; try congruence; inv HC. Qed.
#[global] Hint Resolve sum_not_infty : eR.

Lemma le_er_not_infty a b pf :
  a <= er b pf ->
  a <> infty.
Proof. intros Hle HC; rewrite HC in Hle; inv Hle. Qed.
#[global] Hint Resolve le_er_not_infty : eR.

Definition unbounded {A} (f : A -> eR) : Prop :=
  forall ub, upper_bound ub f -> ub = infty.

Lemma supremum_infty_unbounded {A} (f : A -> eR) :
  supremum infty f -> unbounded f.
Proof.
  intros [Hub Hlub] x Hx; destruct x as [x|]; auto; apply Hlub in Hx; inv Hx.
Qed.
#[global] Hint Resolve supremum_infty_unbounded : eR.

Lemma infimum_infty_inv {A} (f : A -> eR) :
  infimum infty f -> f = const infty.
Proof.
  intros [Hlb Hglb]; ext x; unfold const.
  specialize (Hlb x); inv Hlb; reflexivity.
Qed.

Lemma unbounded_supremum_infty {A} (f : A -> eR) :
  unbounded f -> supremum infty f.
Proof.
  intros H; split.
  - intro i; constructor.
  - intros x Hx; apply H in Hx; subst; reflexivity.
Qed.
#[global] Hint Resolve unbounded_supremum_infty : eR.

Lemma eRplus_le_l (a b c : eR) :
  a + b <= c ->
  a <= c.
Proof. intro H; destruct a, b, c; try constructor; auto; inv H; lra. Qed.
#[global] Hint Resolve eRplus_le_l : eR.  

Lemma eRplus_le_r (a b c : eR) :
  a + b <= c ->
  b <= c.
Proof. intro H; destruct a, b, c; try constructor; auto; inv H; lra. Qed.
#[global] Hint Resolve eRplus_le_r : eR.  

Lemma unbounded_sum_l {I} (f g : I -> eR) :
  unbounded f ->
  unbounded (fun i => f i + g i).
Proof.
  intros H x Hx; apply H; intro i.
  specialize (Hx i); simpl in *; eauto with eR.
Qed.
#[global] Hint Resolve unbounded_sum_l : eR.

Lemma unbounded_sum_r {I} (f g : I -> eR) :
  unbounded g ->
  unbounded (fun i => f i + g i).
Proof.
  intros H x Hx; apply H; intro i.
  specialize (Hx i); simpl in *; eauto with eR.
Qed.
#[global] Hint Resolve unbounded_sum_r : eR.

Lemma supremum_0_inv {A} `{Inhabited A} (f : A -> eR) :
  supremum 0 f ->
  f = const 0.
Proof. intros [Hub _]; ext x; apply le_eR0, Hub. Qed.

Lemma supremum_sum (f g : nat -> eR) (a b : eR) :
  chain f ->
  chain g ->
  supremum a f ->
  supremum b g ->
  supremum (a + b) (fun i => f i + g i).
Proof with eauto with eR.
  destruct a as [a|].
  2: { intros Ha Hb... }
  destruct b as [b|].
  2: { intros Ha Hb... }
  intros Hf Hg Ha Hb.
  assert (supremum (a + b) (fun i => proj_eR (f i) + proj_eR (g i)))%R.
  { apply supremum_sum_R...
    - eapply supremum_er_proj_eR...
    - eapply supremum_er_proj_eR... }
  replace (fun i : nat => (proj_eR (f i) + proj_eR (g i))%R) with
    (fun i : nat => proj_eR (f i + g i)) in H by (ext i; eauto with eR).
  apply supremum_proj_eR_er; eauto with eR.
Qed.

Lemma not_eRle a b :
  ~ a <= b ->
  b < a.
Proof.
  intro H.
  destruct a as [a|], b as [b|].
  - constructor; apply Rnot_le_lt; intro HC; apply H; constructor; auto.
  - exfalso; apply H; constructor.
  - constructor.
  - exfalso; apply H; constructor.
Qed.

Lemma not_eRlt_le a b :
  ~ b < a ->
  a <= b.
Proof.
  intro Hba.
  destruct a as [a|], b as [b|].
  - constructor.
    apply Rnot_lt_le; intro HC; apply Hba; constructor; auto.
  - constructor.
  - exfalso; apply Hba; constructor.
  - constructor.
Qed.

Lemma sup_sum (f g : nat -> eR) :
  chain f ->
  chain g ->
  sup (fun i => f i + g i) = sup f + sup g.
Proof.
  intros Hf Hg.
  apply equ_eR, supremum_sup; auto with eR.
  apply supremum_sum; auto; apply sup_spec; auto with order.
Qed.

Lemma sup_apply_eR {A} (ch : nat -> A -> eR) (x : A) :
  sup ch x = sup (fun i => ch i x).
Proof. apply equ_eR, sup_apply; auto. Qed.

Lemma inf_apply_eR {A} (ch : nat -> A -> eR) (x : A) :
  inf ch x = inf (fun i => ch i x).
Proof. apply equ_eR, inf_apply; auto. Qed.

Lemma sup_apply_f_eR {A B} (ch : nat -> A -> (B -> eR)) (x : A) :
  directed ch ->
  sup ch x = sup (fun i => ch i x).
Proof. intro Hch; apply equ_f_eR, sup_apply; auto. Qed.

Lemma er_mult_infty_inv a pfa b pfb :
  er a pfa = er b pfb * infty ->
  a = 0%R /\ b = 0%R.
Proof.
  intro H.
  unfold eRmult in H.
  destruct (eR_eq_dec (er b pfb) 0).
  - inv e; inv H; auto.
  - inv H.
Qed.

Lemma unbounded_scalar {A} (f : A -> eR) c :
  c <> eR0 ->
  c <> infty ->
  unbounded f ->
  unbounded (fun x => c * f x).
Proof.
  unfold unbounded.
  intros Hc Hc' Hf [ub|] Hub; auto.
  destruct c as [c|]; try congruence.
  assert (upper_bound (er ub r / er c r0) f).
  { intro x; specialize (Hub x); simpl in Hub.
    destruct (f x) eqn:Hfx.
    - unfold eRdiv. simpl.
      destruct (R_eq_dec c 0); subst.
      + exfalso; apply Hc; apply eR_eq; reflexivity.
      + constructor; inv Hub; apply Rle_Rdiv; lra.
    - inv Hub; apply er_mult_infty_inv in H; destruct H; subst.
      exfalso; apply Hc, eR_eq; reflexivity. }
  apply Hf in H; unfold eRdiv in H; simpl in H.
  destruct (R_eq_dec c 0); subst; inv H.
  exfalso; apply Hc, eR_eq; reflexivity.
Qed.

Lemma supremum_infty {A} (f : A -> eR) (x : A) :
  f x = infty ->
  supremum infty f.
Proof.
  intro Hfx; split.
  - constructor.
  - intros ub Hub; specialize (Hub x).
    rewrite Hfx in Hub; inv Hub; constructor.
Qed.

(* Don't delete. *)
Lemma not_eRlt_eRle a b :
  ~ a < b ->
  b <= a.
Proof.
  intro HC; destruct a, b; try constructor.
  - assert (~ r < r1)%R.
    { intro H; apply HC; constructor; auto. }
    lra.
  - exfalso; apply HC; constructor.
Qed.
#[global] Hint Resolve not_eRlt_eRle : eR.

(* Don't delete. *)
Lemma supremum_0_lt_inv {A} (f : A -> eR) (a : eR) :
  supremum a f ->
  0 < a ->
  exists x, 0 < f x.
Proof.
  intros [Hub Hlub] Hlt; apply not_all_not_ex; intro HC.
  assert (H0: upper_bound 0 f).
  { intro x; specialize (HC x); simpl; auto with eR. }
  apply Hlub in H0; simpl in H0.
  inv Hlt; inv H0; lra.
Qed.

Lemma supremum_scalar {A} `{Inhabited A} (f : A -> eR) (a c : eR) :
  supremum a f ->
  supremum (c * a) (fun i => c * f i).
Proof.
  intros Hf.
  destruct (eR_eq_dec c 0); subst.
  { rewrite eRmult_0_l.
    replace (fun i => 0 * f i) with (fun _ : A => 0).
    { apply supremum_const. }
    ext x; rewrite eRmult_0_l; reflexivity. }
  destruct (classic (exists x, f x = infty)) as [Hx|Hx].
  { destruct Hx as [x Hx].
    destruct a.
    - destruct Hf as [Hub _].
      specialize (Hub x); rewrite Hx in Hub; inv Hub.
    - rewrite eRmult_infty_r; auto with eR.
      split.
      + intro y; constructor.
      + intros y Hy; destruct y; try constructor.
        specialize (Hy x); simpl in Hy.
        rewrite Hx, eRmult_infty_r in Hy; inv Hy; auto with eR. }
  destruct c.
  2: { destruct (eR_eq_dec a 0); subst.
       { rewrite eRmult_0_r; apply supremum_0_inv in Hf; subst.
         replace (fun i => infty * const 0 i) with (fun _ : A => 0).
         { apply supremum_const. }
         ext x; unfold const; rewrite eRmult_0_r; reflexivity. }
       rewrite eRmult_infty_l; auto with eR.
       apply supremum_0_lt_inv in Hf; auto with eR.
       destruct Hf as [x Hf].
       eapply supremum_infty with x.
       rewrite eRmult_infty_l; auto with eR. }
  destruct (classic (exists r pf, forall x, f x <= er r pf)) as [H0|H0].
  { destruct H0 as [b [Hle Hb]].
    destruct a.
    2: { destruct Hf as [_ Hlub].
         apply Hlub in Hb; inv Hb. }
    apply supremum_proj_eR_er.
    - intros x HC; destruct (f x) eqn:Hfx.
      + inv HC.
      + apply Hx; exists x; auto.
    - replace (fun i => proj_eR (er r r0 * f i)) with
        (fun i => (r * proj_eR (f i))%R).
      { apply supremum_scalar_R; auto.
        eapply supremum_er_proj_eR; eauto. }
      ext x; specialize (Hb x); destruct (f x).
      + reflexivity.
      + inv Hb. }
  (* a must be infty *)
  destruct a.
  { exfalso; apply H0; exists r1, r2; intro x; apply Hf. }
  rewrite eRmult_infty_r; auto with eR.
  apply unbounded_supremum_infty.
  apply unbounded_scalar; try congruence.
  intros [ub pf|] Hub; auto.
  exfalso; apply H0; exists ub, pf; apply Hub.
Qed.

Lemma er_not_infty a pf :
  er a pf <> infty.
Proof. congruence. Qed.
#[global] Hint Resolve er_not_infty : eR.

Lemma leq_eRle (a b : eR) :
  a ⊑ b ->
  a <= b.
Proof. auto. Qed.
#[global] Hint Resolve leq_eRle : eR.

Lemma eRle_leq (a b : eR) :
  a <= b ->
  a ⊑ b.
Proof. auto. Qed.
#[global] Hint Resolve eRle_leq : eR.

Lemma eRmult_eq_reg_r : forall r r1 r2,
    0 < r ->
    r <> infty ->
    r1 * r = r2 * r ->
    r1 = r2.
Proof.
  intros a b c Hlt Ha Hle.
  destruct a, b, c; try solve [constructor]; try congruence; inv Hle.
  - apply eR_eq; inv Hlt; nra.
  - unfold eRmult in H0; destruct (eR_eq_dec (er r r0) 0);
      try inv H0; inv e; inv Hlt; lra.
  - unfold eRmult in H0; destruct (eR_eq_dec (er r r0) 0);
      try inv H0; inv e; inv Hlt; lra.
Qed.

Lemma eRmult_le_reg_r : forall r r1 r2,
    0 < r ->
    r <> infty ->
    r1 * r <= r2 * r ->
    r1 <= r2.
Proof.
  intros a b c Hlt Ha Hle.
  destruct a, b, c; try solve[constructor]; try congruence; inv Hle.
  inv Hlt; constructor; eapply Rmult_le_reg_r; eauto.
  unfold eRmult in H.
  destruct (eR_eq_dec (er r r0) 0); try congruence; inv e; inv Hlt; lra.
Qed.

Lemma eRinv_l (a : eR) :
  a <> 0 ->
  a <> infty ->
  / a * a = 1.
Proof.
  intros Hnz Hninf.
  destruct a; simpl; try congruence.
  destr; subst.
  - exfalso; apply Hnz, eR_eq; reflexivity.
  - apply eR_eq, Rinv_l; auto.
Qed.
#[global] Hint Resolve eRinv_l : eR.

Lemma eRinv_r (a : eR) :
  a <> 0 ->
  a <> infty ->
  a * / a = 1.
Proof.
  intros Hnz Hninf.
  destruct a; simpl; try congruence.
  destr; subst.
  - exfalso; apply Hnz, eR_eq; reflexivity.
  - apply eR_eq, Rinv_r; auto.
Qed.
#[global] Hint Resolve eRinv_r : eR.

Lemma eRinv_1 (a : eR) :
  a * / 1 = a.
Proof.
  destruct a; simpl; destr; try lra.
  - apply eR_eq; lra.
  - unfold eRmult; destr; try congruence; inv e; lra.
Qed.
#[global] Hint Resolve eRinv_1 : eR.

Lemma eRdiv_1 (a : eR) :
  a / 1 = a.
Proof. apply eRinv_1. Qed.
#[global] Hint Resolve eRdiv_1 : eR.

Lemma eRdiv_r (a : eR) :
  a <> 0 ->
  a <> infty ->
  a / a = 1.
Proof. apply eRinv_r. Qed.
#[global] Hint Resolve eRdiv_r : eR.

Lemma eRmult_comm3 a b c :
  a * b * c = a * c * b.
Proof.
  rewrite eRmult_assoc.
  replace (b * c) with (c * b) by apply eRmult_comm.
  rewrite <- eRmult_assoc; reflexivity.
Qed.
#[global] Hint Resolve eRmult_comm3 : eR.

Lemma eRplus_eRminus a b :
  a <= b ->
  a + (b - a) = b.
Proof.
  intro Hle.
  inv Hle; auto.
  - destruct a; auto.
  - unfold eRminus.
    destr.
    + apply eR_eq; lra.
    + rewrite eRplus_0_r; apply eR_eq; lra.
Qed.
#[global] Hint Resolve eRplus_eRminus : eR.

Definition diff (r1 r2 : eR) : eR :=
  match (r1, r2) with
  | (infty, infty) => eR0
  | (infty, _) => infty
  | (_, infty) => infty
  | (er a pf1, er b pf2) =>
      match Rle_dec b a with
      | left pf => er (a - b) (Rminus_0_le _ _ pf)
      | right pf => er (b - a) (Rminus_0_le _ _ (Rlt_le _ _ (Rnot_le_lt _ _ pf)))
      end
  end.

Lemma eR0_lt_1 :
  0 < 1.
Proof. constructor; lra. Qed.
#[global] Hint Resolve eR0_lt_1 : eR.

Lemma eR0_lt_2 :
  0 < 2.
Proof. constructor; lra. Qed.
#[global] Hint Resolve eR0_lt_2 : eR.

(* Sequence g converges to limit point lim. *)
Definition converges (g : nat -> eR) (lim : eR) :=
  forall eps, eR0 < eps -> exists n0, forall n, (n0 <= n)%nat -> diff (g n) lim < eps.

Lemma converges_proj_eR f a pf :
  converges f (er a pf) ->
  converges_R (fun i => proj_eR (f i)) a.
Proof.
  unfold converges, converges_R.
  intros Hc eps Heps.
  set (eps' := er eps (Rlt_le _ _ Heps)).
  assert (Heps': 0 < eps') by (constructor; auto).
  specialize (Hc eps' Heps').
  destruct Hc as [n0 Hc].
  exists n0; intros n Hle.
  apply Hc in Hle.
  destruct (f n); simpl.
  2: { inv Hle. }
  unfold diff in Hle.
  destruct (Rle_dec a r); inv Hle.
  { destruct (Req_dec a r); subst.
    - rewrite Rminus_eq_0, Rabs_R0; auto.
    - rewrite Rabs_left; lra. }
  { rewrite Rabs_right; lra. }
Qed.

Lemma converges_infty (f : nat -> eR) :
  converges f infty ->
  exists x, f x = infty.
Proof.
  unfold converges.
  intro Hc.
  apply not_all_not_ex.
  intro HC.
  specialize (Hc eR1 eR0_lt_1).
  destruct Hc as [n0 Hc].
  specialize (Hc n0 (Nat.le_refl n0)).
  specialize (HC n0).
  destruct (f n0); try congruence.
  inv Hc.
Qed.

Lemma converges_infimum (g : nat -> eR) (lim : eR) :
  dec_chain g ->
  (forall i, g i <> infty) ->
  converges g lim ->
  infimum lim g.
Proof.
  intros Hchain Hgi Hlim.
  destruct lim.
  - apply infimum_proj_eR_er; auto.
    apply converges_infimum_R.
    + intro i; simpl.
      apply Rle_ge.
      apply dec_chain_proj_eR; auto.
    + eapply converges_proj_eR; eauto.
  - apply converges_infty in Hlim.
    destruct Hlim as [x Hx].
    specialize (Hgi x); congruence.
Qed.

Lemma supremum_infimum_sum (f g : nat -> eR) (a b c : eR) (ub : R) (pf : (0 <= ub)%R):
  chain f ->
  dec_chain g ->
  upper_bound (er ub pf) f ->
  upper_bound (er ub pf) g ->
  (forall i, f i + g i = c) ->
  supremum a f ->
  infimum b g ->
  a + b = c.
Proof.
  intros Hf Hg Hfbound Hgbound Heq Ha Hb.
  destruct a as [a pfa|].
  2: { apply supremum_infty_unbounded in Ha.
       specialize (Ha (er ub pf) Hfbound); congruence. }
  destruct b as [b pfb|].
  2: { apply infimum_infty_inv in Hb.
       rewrite Hb in Hgbound.
       specialize (Hgbound O); inv Hgbound. }
  destruct c as [c pfc|].
  2: { specialize (Heq O).
       specialize (Hfbound O).
       destruct (f O).
       2: { inv Hfbound. }
       specialize (Hgbound O).
       destruct (g O).
       2: { inv Hgbound. }
       inv Heq. }
  assert (Hfi: forall i : nat, f i <> infty).
  { intros i HC; specialize (Hfbound i); rewrite HC in Hfbound; inv Hfbound. }
  assert (Hgi: forall i : nat, g i <> infty).
  { intros i HC; specialize (Hgbound i); rewrite HC in Hgbound; inv Hgbound. }
  apply supremum_er_proj_eR in Ha; auto.
  apply infimum_er_proj_eR in Hb; auto.
  apply eR_eq.
  eapply supremum_infimum_sum_R; eauto with eR.
  simpl; intro i; specialize (Heq i).
  unfold eRplus in Heq.
  destruct (f i); try congruence.
  destruct (g i); try congruence.
  inv Heq; reflexivity.
Qed.

Lemma eRminus_le a b :
  a - b <= a.
Proof.
  unfold eRminus.
  destruct a, b; auto with eR.
  destr; auto with eR; constructor; lra.
Qed.
#[global] Hint Resolve eRminus_le : eR.  

Lemma eRminus_0_r a :
  a - eR0 = a.
Proof.
  unfold eRminus; destruct a; simpl; auto; destr.
  - apply eR_eq; lra.
  - congruence.
Qed.
#[global] Hint Resolve eRminus_0_r : eR.  

Lemma eRminus_eq_plus a b c :
  c <> infty ->
  a <= c ->
  b = c - a ->
  a + b = c.
Proof.
  intros Hc Hac Hbca.
  unfold eRminus; destruct a as [a|], b as [b|], c as [c|]; simpl; inv Hbca; auto.
  - inv Hac.
    apply eR_eq.
    unfold eRminus in H0.
    destruct (Rle_dec a c).
    + inv H0; lra.
    + lra.
  - unfold eRminus in H0.
    destruct (Rle_dec a c); inv H0.
  - inv Hac.
Qed.
#[global] Hint Resolve eRminus_eq_plus : eR.  

Lemma eRplus_eq_minus a b c :
  c <> infty ->
  a + b = c ->
  b = c - a.
Proof.
  intros Hc Habc.
  unfold eRminus; destruct a, b, c; simpl; inv Habc; auto; try congruence.
  destr; apply eR_eq; lra.
Qed.
#[global] Hint Resolve eRplus_eq_minus : eR.  

Lemma eRminus_minus_le a b :
  a <> infty ->
  b <= a ->
  a - (a - b) = b.
Proof.
  intros Ha Hba; destruct a as [a|], b as [b|]; simpl; auto; try congruence; inv Hba.
  unfold eRminus.
  destruct (Rle_dec b a).
  - destruct (Rle_dec (a - b) a); apply eR_eq; lra.
  - simpl; destr; lra.
Qed.
#[global] Hint Resolve eRminus_minus_le : eR.

Lemma eRmult_minus_distr_l a b c :
  a <> infty ->
  a * (b - c) = a * b - a * c.
Proof.
  intro Ha.
  unfold eRminus, eRmult.
  destruct a as [a|].
  - destruct b as [b|].
    + destruct c as [c|]; simpl.
      * destruct (Rle_dec c b); simpl; destr; apply eR_eq; nra.
      * destruct (eR_eq_dec (er a r) 0); simpl.
        { destr; inv e; apply eR_eq; lra. }
        { apply eR_eq; lra. }
    + destruct c as [c|]; simpl.
      * destr; simpl; auto.
        inv e; destr; apply eR_eq; lra.
      * destruct (eR_eq_dec (er a r) 0); simpl.
        { destr; apply eR_eq; lra. }
        apply eR_eq; lra.
  - congruence.
Qed.
#[global] Hint Resolve eRmult_minus_distr_l : eR.

Lemma eRmult_minus_distr_r a b c :
  c <> infty ->
  (a - b) * c = a * c - b * c.
Proof.
  intro Hc.
  rewrite eRmult_comm, eRmult_minus_distr_l; auto.
  rewrite eRmult_comm; f_equal; apply eRmult_comm.
Qed.
#[global] Hint Resolve eRmult_minus_distr_r : eR.

Lemma eRle_infty_not_infty a b :
  a <= b ->
  b <> infty ->
  a <> infty.
Proof. intros Hle Hb; inv Hle; congruence. Qed.
#[global] Hint Resolve eRle_infty_not_infty : eR.

Lemma eRplus_half_plus_half a :
  a/2 + a/2 = a.
Proof.
  unfold eRdiv, eRinv, eRmult; simpl.
  destruct a as [a|].
  - destruct (R_eq_dec 2 0); try lra.
    apply eR_eq; lra.
  - destruct (R_eq_dec 2 0); try lra.
    destr.
    + inv e; lra.
    + reflexivity.
Qed.

Lemma eRminus_1_2 :
  1 - 1/2 = 1/2.
Proof.
  unfold eRdiv, eRinv; simpl.
  rewrite eRmult_1_l.
  destr; try lra.
  unfold eRminus; simpl.
  destr; try lra.
  apply eR_eq; lra.
Qed.

(* Could have other variants. Just can't have one infty and the other zero. *)
Lemma eRinv_distr_mult a b :
  a <> 0 ->
  b <> 0 ->
  / (a * b) = / a * / b.
Proof.
  intros Ha Hb.
  unfold eRinv, eRmult.
  destruct a as [a|], b as [b|]; simpl.
  - destr.
    + apply Rmult_integral in e; destruct e; subst.
      * destruct (R_eq_dec 0 0); try congruence.
        destruct (R_eq_dec b 0); subst.
        { destr; congruence. }
        { destr; try congruence.
          inv e0; apply Rinv_neq_0_compat in n; congruence. }
      * destruct (R_eq_dec a 0).
        { destruct (R_eq_dec 0 0); try congruence.
          destr; auto. }
        destruct (R_eq_dec 0 0); try congruence.
        destr; auto.
        inv e0; apply Rinv_neq_0_compat in n; congruence.
    + destruct (R_eq_dec a 0); subst.
      * exfalso; apply n; lra.
      * destruct (R_eq_dec b 0); subst.
        { exfalso; apply n; lra. }
        { apply eR_eq; field; auto. }
  - destruct (eR_eq_dec (er a r) 0); simpl.
    + congruence.
    + destruct (R_eq_dec a 0); subst.
      * exfalso; apply Ha, eR_eq; reflexivity.
      * apply eR_eq; lra.
  - destruct (eR_eq_dec (er b r) 0); simpl.
    + congruence.
    + destruct (R_eq_dec b 0); subst.
      * destr; auto; congruence.
      * apply eR_eq; lra.
  - destruct (eR_eq_dec infty 0); try congruence.
    apply eR_eq; lra.
Qed.

Lemma eRmult_le_1_le a b :
  a <= 1 ->
  a * b <= b.
Proof.
  intro H; inv H; unfold eRmult.
  destruct b; constructor.
  apply Rmult_le_1_le; auto.
Qed.
#[global] Hint Resolve eRmult_le_1_le : eR.

Lemma eRlt_eRmult a b :
  0 < a ->
  0 < b ->
  0 < a * b.
Proof.
  intros Ha Hb.
  inv Ha; inv Hb.
  - rewrite eRmult_infty_l; try constructor; intro HC; inv HC.
  - rewrite eRmult_infty_l; try constructor; intro HC; inv HC; lra.
  - rewrite eRmult_infty_r; try constructor; intro HC; inv HC; lra.
  - constructor; nra.
Qed.
#[global] Hint Resolve eRlt_eRmult : eR.

Lemma eRpow_0_lt : forall (x:eR) (k:nat), 0 < x -> 0 < x ^ k.
Proof.
  intros a n; revert a; induction n; intros a Hlt; simpl; auto with eR.
Qed.
#[global] Hint Resolve eRpow_0_lt : eR.

Lemma eRpow_le_1 : forall (x:eR) (k:nat), x <= 1 -> x ^ k <= 1.
Proof.
  intros a n; revert a; induction n; intros a Hlt; simpl; eauto with eR.
  etransitivity.
  - apply eRmult_le_1_le; auto.
  - auto.
Qed.
#[global] Hint Resolve eRpow_le_1 : eR.

Corollary eRpow_nz : forall (x:eR) (k:nat), 0 < x -> x ^ k <> 0.
Proof.
  intros a k Ha; apply eRpow_0_lt with (k:=k) in Ha.
  intro HC; rewrite HC in Ha; inv Ha; lra.
Qed.
#[global] Hint Resolve eRpow_nz : eR.

Lemma eRle_convex_sum a b c d :
  a <= 1 ->
  b <= d ->
  c <= d ->
  a * b + (1 - a) * c <= d.
Proof.
  intros Ha Hbd Hcd.
  destruct d.
  2: { constructor. }
  destruct a.
  2: { inv Ha. }
  destruct b.
  2: { inv Hbd. }
  destruct c.
  2: { inv Hcd. }
  unfold eRminus; simpl.
  inv Ha; inv Hbd; inv Hcd; destr.
  2: { congruence. }
  constructor; nra.
Qed.  
#[global] Hint Resolve eRle_convex_sum : eR.

Lemma eRplus_comm4 a b c d :
  a + b + c + d = a + c + b + d.
Proof. destruct a, b, c, d; auto; apply eR_eq; lra. Qed.

Lemma eRplus_factor a b x y z w :
  a * x + b * y + a * z + b * w = a * (x + z) + b * (y + w).
Proof.
  rewrite eRplus_comm4, eRplus_assoc, <- 2!eRmult_plus_distr_l; reflexivity.
Qed.

Lemma eRplus_minus_assoc a b c :
  b <> infty ->
  c <= b ->
  a + (b - c) = a + b - c.
Proof.
  unfold eRminus.
  intros Hb Hle; inv Hle.
  - congruence.
  - destruct a; auto; destr; simpl; destr; apply eR_eq; lra.
Qed.

Lemma eRminus_cancel a :
  a - a = 0.
Proof.
  unfold eRminus.
  destruct a; auto.
  destr; auto.
  apply eR_eq; lra.
Qed.
#[global] Hint Resolve eRminus_cancel : eR.

Ltac eRauto :=
  repeat try match goal with
    | [ |- context[0 + _] ] => rewrite eRplus_0_l
    | [ |- context[_ + 0] ] => rewrite eRplus_0_r
    | [ |- context[_ - 0] ] => rewrite eRminus_0_r
    | [ |- context[?a + (_ - ?a)] ] => try rewrite eRplus_eRminus
    | [ |- context[?a - ?a] ] => rewrite eRminus_cancel
    | [ |- context[1 * _] ] => rewrite eRmult_1_l
    | [ |- context[_ * 1] ] => rewrite eRmult_1_r
    | [ |- context[0 * _] ] => rewrite eRmult_0_l
    | [ |- context[_ * 0] ] => rewrite eRmult_0_r
    | [ |- context[_ / 1] ] => rewrite eRdiv_1
    | [ |- context[?a / ?a] ] => rewrite eRdiv_r
    | [ H: infty <= er _ _ |- _ ] => inversion H
    end; eauto with eR; try reflexivity.

(* Could have another variant where a <> infty. *)
Lemma eRminus_assoc (a b c : eR) :
  b <= a ->
  c <= b ->
  b <> infty ->
  a - (b - c) = a - b + c.
Proof.
  intros Hba Hcb Hb.
  unfold eRminus.
  destruct a as [a|], b as [b|], c as [c|]; simpl; eRauto.
  - inv Hba; inv Hcb.
    destruct (Rle_dec c b); try lra.
    destruct (Rle_dec (b - c) a).
    + destr; try lra.
      apply eR_eq; lra.
    + destr; try lra.
      apply eR_eq; lra.
  - destruct (Rle_dec c b); eRauto.
  - congruence.
Qed.
#[global] Hint Resolve eRminus_assoc : eR.

Lemma sup_scalar (f : nat -> eR) (c : eR) :
  c * sup f = sup (fun x => c * f x).
Proof.
  apply equ_eR.
  eapply supremum_unique.
  2: { apply sup_spec; auto with eR. }
  apply supremum_scalar, sup_spec; auto with eR.
Qed.

Lemma chain_scalar (f : nat -> eR) (a : eR) :
  chain f ->
  chain (fun i => a * f i).
Proof. intros Hf i; apply eRmult_le_compat_l; eRauto. Qed.

Lemma dec_chain_scalar (f : nat -> eR) (c : eR) :
  dec_chain f ->
  dec_chain (fun i => c * f i).
Proof.
  unfold dec_chain; simpl; intros Hch i.
  apply eRmult_le_compat_l; eRauto.
Qed.

Lemma eRminus_le_plus a b c :
  a - b <= c ->
  a <= c + b.
Proof.
  unfold eRminus, eRplus.
  intro Hle.
  destruct a as [a|].
  - destruct b as [b|].
    + destruct c as [c|]; constructor.
      destruct (Rle_dec b a) in Hle; inv Hle; lra.
    + destruct c; constructor.
  - destruct b as [b|].
    + inv Hle; constructor.
    + destruct c; constructor.
Qed.

Lemma eRplus_le_minus a b c :
  a <= c + b ->
  a - b <= c.
Proof.
  unfold eRminus, eRplus.
  intro Hle.
  destruct a as [a|].
  - destruct c as [c|].
    + destruct b as [b|].
      * inv Hle; destr; constructor; lra.
      * constructor; auto.
    + constructor.
  - destruct c as [c|].
    + destruct b as [b|].
      * inv Hle.
      * constructor; auto.
    + constructor.
Qed.

Lemma infimum_sum (f g : nat -> eR) (a b : eR) :
  dec_chain f ->
  dec_chain g ->
  infimum a f ->
  infimum b g ->
  infimum (a + b) (fun i => f i + g i).
Proof with eauto with eR.
  intros Hf Hg Ha Hb.
  destruct a as [a|].
  2: { rewrite eRplus_infty_l.
       apply infimum_infty_inv in Ha.
       replace (fun i => f i + g i) with (fun _ : nat => infty).
       { apply infimum_const. }
       ext i; rewrite Ha; unfold const; rewrite eRplus_infty_l; reflexivity. }
  destruct b as [b|].
  2: { rewrite eRplus_infty_r.
       apply infimum_infty_inv in Hb.
       replace (fun i => f i + g i) with (fun _ : nat => infty).
       { apply infimum_const. }
       ext i; rewrite Hb; unfold const; rewrite eRplus_infty_r; reflexivity. }
  destruct Ha as [Hlba Hglba].
  destruct Hb as [Hlbb Hglbb].
  split.
  - intro i; apply eRplus_le_compat.
    + apply Hlba.
    + apply Hlbb.
  - intros x Hx.
    cut (x - er b r0 <= er a r).
    { intro H; apply eRminus_le_plus; auto. }
    apply Hglba.
    intro i.
    cut (x - f i <= er b r0).
    { intro H; simpl; apply eRplus_le_minus.
      rewrite eRplus_comm; apply eRminus_le_plus; auto. }
    apply Hglbb.
    intro j.
    cut (x <= f i + g j).
    { intro H; apply eRplus_le_minus; rewrite eRplus_comm; auto. }
    destruct (Nat.leb_spec i j).
    + specialize (Hx j); simpl in Hx.
      etransitivity; eauto.
      apply eRplus_le_compat; eRauto.
      apply leq_eRle, dec_chain_leq; auto.
    + specialize (Hx i); simpl in Hx.
      etransitivity; eauto.
      apply eRplus_le_compat; eRauto.
      apply leq_eRle, dec_chain_leq; auto; lia.
Qed.

Corollary eRle_div a b c :
  a <= b ->
  a / c <= b / c.
Proof. intros Hab; apply eRmult_le_compat_r; auto. Qed.

Definition INeR (n : nat) : eR := er _ (pos_INR n).

Lemma INeR_0 : INeR 0 = 0.
Proof. apply eR_eq; reflexivity. Qed.

Lemma INeR_1 : INeR 1 = 1.
Proof. apply eR_eq; reflexivity. Qed.

Lemma plus_INeR : forall n m:nat, INeR (n + m) = INeR n + INeR m.
Proof. intros n m; apply eR_eq, plus_INR. Qed.

Lemma INeR_eq : forall n m:nat, INeR n = INeR m -> n = m.
Proof. intros n m Heq; inv Heq; apply INR_eq; auto. Qed.

Lemma eRmult_eRdiv_assoc a b c :
  a * (b / c) = (a * b) / c.
Proof. unfold eRdiv; rewrite eRmult_assoc; reflexivity. Qed.

Lemma eRdiv_eRmult_assoc a b c :
  b <> 0 ->
  c <> 0 ->
  a / b / c = a / (b * c).
Proof.
  intros Hb Hc; unfold eRdiv.
  rewrite eRinv_distr_mult; auto.
  rewrite eRmult_assoc; reflexivity.
Qed.

Lemma eRmult_fract a b c d :
  b <> 0 ->
  d <> 0 ->
  (a / b) * (c / d) = (a * c) / (b * d).
Proof.
  intros Hb Hd.
  rewrite eRmult_eRdiv_assoc.
  replace (a / b * c) with (a * c / b) by eRauto.
  rewrite eRdiv_eRmult_assoc; auto.
Qed.

Lemma eRplus_combine_fract a b c:
  a / c + b / c = (a + b) / c.
Proof. unfold eRdiv; rewrite eRmult_plus_distr_r; reflexivity. Qed.

Lemma eRmult_2_plus a :
  2 * a = a + a.
Proof.
  unfold eRmult, eRplus; simpl.
  destruct a as [a|].
  - apply eR_eq; lra.
  - destr; auto; inv e; lra.
Qed.
#[global] Hint Resolve eRmult_2_plus : eR.

Lemma eRmult_half_div_2 a :
  1 / 2 * a = a / 2.
Proof. unfold eRdiv; rewrite eRmult_1_l; apply eRmult_comm. Qed.

Lemma continuous_sup_eR {A} `{dCPO A} (f : A -> eR) (ch : nat -> A) :
  directed ch ->
  continuous f ->
  f (sup ch) = sup (f ∘ ch).
Proof. intros Hch Hf; apply equ_eR, continuous_sup; auto. Qed.

Lemma cocontinuous_sup_eR {A} `{dCPO A} (f : A -> eR) (ch : nat -> A) :
  directed ch ->
  cocontinuous f ->
  f (sup ch) = inf (f ∘ ch).
Proof. intros Hch Hf; apply equ_eR, cocontinuous_sup; auto. Qed.

Lemma wcontinuous_sum {A} `{OType A} (f g : A -> eR) :
  wcontinuous f ->
  wcontinuous g ->
  wcontinuous (fun x => f x + g x).
Proof.
  intros Hf Hg ch Hch s Hs; unfold compose.
  apply supremum_sum.
  { apply monotone_chain; auto. apply wcontinuous_monotone; auto. }
  { apply monotone_chain; auto; apply wcontinuous_monotone; auto. }
  { apply Hf; auto. }
  { apply Hg; auto. }
Qed.

#[global]
  Instance ExtType_eR : ExtType eR.
Proof. constructor; intros a b Hab; apply eRle_antisym; apply Hab. Qed.

Lemma eR_total a b :
  a <= b \/ b <= a.
Proof.
  destruct a as [a|], b as [b|].
  - destruct (Rle_or_lt a b).
    + left; constructor; auto.
    + right; constructor; lra.
  - left; constructor.
  - right; constructor.
  - left; constructor.
Qed.

Lemma eRminus_pos_lt a b :
  a <> infty ->
  0 < a ->
  0 < b ->
  a - b < a.
Proof.
  intros Ha Ha' Hb.
  destruct a as [a|].
  inv Ha'.
  - destruct b as [b|].
    + inv Hb.
      unfold eRminus.
      destruct (Rle_dec b a); eRauto.
      constructor; lra.
    + constructor; auto.
  - congruence.
Qed.

Lemma eRmult_lt_0_compat : forall r1 r2, 0 < r1 -> 0 < r2 -> 0 < r1 * r2.
Proof. intros; replace 0 with (0 * r2); eRauto. Qed.

Lemma eRlt_0_eRdiv a b :
  0 < a ->
  b <> infty ->
  0 < a / b.
Proof.
  intros Ha Hb.
  unfold eRdiv.
  apply eRmult_lt_0_compat; eRauto.
  unfold eRinv.
  destruct b as [b|].
  - destr; subst; constructor.
    apply Rinv_0_lt_compat; lra.
  - congruence.
Qed.  

Lemma eRlt_0_plus_l a b :
  0 < a ->
  0 < a + b.
Proof.
  intro Ha.
  destruct a as [a|].
  - inv Ha; destruct b as [b|]; constructor; lra.
  - constructor.
Qed.

Lemma eRlt_0_plus_r a b :
  0 < b ->
  0 < a + b.
Proof.
  intro Hb.
  destruct b as [b|].
  - inv Hb; destruct a as [a|]; constructor; lra.
  - rewrite eRplus_comm; constructor.
Qed.

Lemma lt_INeR n m :
  (n < m)%nat ->
  INeR n < INeR m.
Proof. intro Hlt; constructor; apply lt_INR; auto. Qed.

Corollary sup_shift_eR f g :
  chain f ->
  g = shift f ->
  sup f = sup g.
Proof. intros; subst; symmetry; apply equ_eR, sup_shift; auto. Qed.

Lemma eRdiv_cancel_r a b c:
  b <> 0 ->
  c <> 0 ->
  c <> infty ->
  (a / c) / (b / c) = a / b.
Proof.
  intros Hb Hc Hc'.
  rewrite eRdiv_eRmult_assoc; auto.
  2: { apply eRlt_neq', eRlt_0_eRdiv; eRauto. }
  f_equal.
  rewrite eRmult_eRdiv_assoc.
  rewrite eRmult_comm.
  unfold eRdiv.
  rewrite eRmult_assoc.
  rewrite eRinv_r; eRauto.
Qed.

Lemma not_0_INeR : forall n:nat, n <> 0%nat -> INeR n <> 0.
Proof. intros n Hn HC; inv HC; eapply not_0_INR; eauto. Qed.

Lemma not_infty_INeR n :
  INeR n <> infty.
Proof. intro HC; inv HC. Qed.
#[global] Hint Resolve not_infty_INeR : eR.

Lemma eRdiv_minus_distr a b c :
  c <> 0 ->
  c <> infty ->
  a / c - b / c = (a - b) / c.
Proof.
  intros Hc Hc'.
  unfold eRminus, eRdiv.
  destruct c as [c|]; simpl; try congruence.
  destruct (R_eq_dec c 0); subst; simpl.
  - exfalso; apply Hc, eR_eq; reflexivity.
  - destruct a as [a|]; simpl.
    + destruct b as [b|]; simpl.
      * destruct (Rle_dec b a).
        { destr.
          - apply eR_eq; lra.
          - apply Rnot_le_lt in n0.
            apply Rmult_lt_reg_r in n0.
            + exfalso; lra.
            + apply Rinv_0_lt_compat; lra. }
        { apply Rnot_le_lt in n0.
          rewrite eRmult_0_l.
          destr; auto.
          assert (b <= a)%R.
          { eapply Rmult_le_reg_r; eauto.
            apply Rinv_0_lt_compat; lra. }
          lra. }
      * rewrite eRmult_0_l.
        rewrite eRmult_infty_l; auto.
        intro HC; inv HC; eapply Rinv_neq_0_compat; eauto.
    + rewrite eRmult_infty_l.
      * destruct b as [b|]; simpl.
        { rewrite eRmult_infty_l; auto.
          intro HC; inv HC.
          eapply Rinv_neq_0_compat; eauto. }
        rewrite eRmult_0_l.
        rewrite eRmult_infty_l; auto.
        intro HC; inv HC; eapply Rinv_neq_0_compat; eauto.
      * intro HC; inv HC; eapply Rinv_neq_0_compat; eauto.
Qed.

Lemma infimum_scalar {A} `{Inhabited A} (f : A -> eR) (a c : eR) :
  c <> infty -> (* could maybe allow whenever a <> 0 *)
  infimum a f ->
  infimum (c * a) (fun i => c * f i).
Proof.
  intros Hc Hf.
  destruct (eR_eq_dec c 0); subst.
  { rewrite eRmult_0_l.
    replace (fun i => 0 * f i) with (fun _ : A => 0).
    { apply infimum_const. }
    ext x; rewrite eRmult_0_l; reflexivity. }
  destruct c as [c|]; try congruence.
  split.
  - intro x; simpl.
    apply eRmult_le_compat_l.
    + apply eR0_le.
    + apply Hf.
  - intros x Hx; simpl.
    unfold lower_bound in Hx.
    replace x with (er c r * / er c r * x).
    2: { rewrite eRinv_r; eRauto. }
    rewrite eRmult_assoc.
    apply eRmult_le_compat_l; eRauto.
    destruct Hf as [Hlb Hglb].
    apply Hglb; intro i; specialize (Hx i); simpl in *.
    destr; subst.
    { exfalso; apply n, eR_eq; reflexivity. }
    apply eRmult_le_reg_r with (r := er c r).
    { eRauto. }
    { eRauto. }
    rewrite eRmult_comm, <- eRmult_assoc.
    replace (er c r * er (/ c) (Rlt_le 0 (/ c)
                                  (Rinv_0_lt_compat c
                                     (Rle_not_eq_Rlt 0 c r n0))))
      with 1.
    2: { apply eR_eq; rewrite Rinv_r; auto. }
    rewrite eRmult_1_l, eRmult_comm; auto.
Qed.

Lemma inf_scalar (f : nat -> eR) (c : eR) :
  c <> infty ->
  c * inf f = inf (fun x => c * f x).
Proof.
  intro Hc; apply equ_eR; eapply infimum_unique.
  2: { apply inf_spec; auto with eR. }
  apply infimum_scalar, inf_spec; auto with eR.
Qed.

Lemma eRmult_div_cancel a b :
  a <> 0 ->
  a <> infty ->
  a * b / a = b.
Proof.
  intros Ha Ha'; unfold eRdiv.
  rewrite eRmult_assoc, eRmult_comm, eRmult_assoc, eRinv_l; eRauto.
Qed.

Lemma eRdiv_eq_1 a b :
  b <> 0 ->
  b <> infty ->
  a = b ->
  a / b = 1.
Proof. intros Hb Hb' Hab; subst; apply eRdiv_r; auto. Qed.

Definition sum (l : list eR) : eR :=
  fold_right eRplus 0 l.

Lemma monotone_sum (a b : eR) (l1 l2 : list eR) :
  list_rel eRle l1 l2 ->
  a <= b ->
  fold_right eRplus a l1 <= fold_right eRplus b l2.
Proof.
  revert a b l2.
  induction l1; intros a' b l2 Hle Hab; inv Hle; simpl; auto.
  apply eRplus_le_compat; auto.
Qed.

Lemma INeR_S n :
  INeR (S n) = 1 + INeR n.
Proof. unfold INeR; apply eR_eq; rewrite S_INR; lra. Qed.

Lemma sum_map_scalar {A} (l : list A) a f :
  sum (map (fun x => a * f x) l) = a * sum (map f l).
Proof.
  revert a f; induction l; intros b f; simpl.
  { eRauto. }
  rewrite IHl, eRmult_plus_distr_l; reflexivity.
Qed.

Lemma sum_map_scalar_r {A} (l : list A) a f :
  sum (map (fun x => f x * a) l) = sum (map f l) * a.
Proof.
  revert a f; induction l; intros b f; simpl.
  { eRauto. }
  rewrite IHl, eRmult_plus_distr_r; reflexivity.
Qed.

Lemma sum_app (l1 l2 : list eR) :
  sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
  revert l2; induction l1; intro l2; simpl.
  { eRauto. }
  rewrite IHl1, eRplus_assoc; reflexivity.
Qed.

Lemma sum_map_count {A} (l : list A) (P : A -> bool) :
  sum (List.map (fun x => if P x then 1 else 0) l) = INeR (countb_list P l).
Proof.
  induction l; simpl.
  { rewrite INeR_0; auto. }
  destruct (P a) eqn:HPa.
  - rewrite IHl; simpl.
    rewrite INeR_S; auto.
  - eRauto.
Qed.

Lemma sum_map_ub {A} (l : list A) f ub :
  Forall (fun x => f x <= ub) l ->
  sum (map f l) <= INeR (length l) * ub.
Proof.
  revert f ub; induction l; intros f ub Hl; simpl.
  { eRauto. }
  inv Hl; rewrite INeR_S, eRmult_plus_distr_r, eRmult_1_l.
  apply eRplus_le_compat; auto.
Qed.

Lemma sum_map_const {A} (l : list A) f c :
  Forall (fun x => f x = c) l ->
  sum (map f l) = INeR (length l) * c.
Proof.
  revert f c; induction l; intros f c Hl; simpl.
  { rewrite INeR_0; eRauto. }
  inv Hl; rewrite INeR_S, eRmult_plus_distr_r, eRmult_1_l.
  f_equal; apply IHl; auto.
Qed.

Lemma sum_le l1 l2 :
  list_rel eRle l1 l2 ->
  sum l1 <= sum l2.
Proof.
  induction 1; simpl.
  { reflexivity. }
  apply eRplus_le_compat; auto.
Qed.

Lemma sum_0 l :
  Forall (eq 0) l ->
  sum l = 0.
Proof. induction 1; simpl; auto; subst; rewrite IHForall; eRauto. Qed.

Lemma INeR_positive n:
  (0 < n)%nat ->
  0 < INeR n.
Proof.
  intro Hn; replace 0 with (INeR 0) by apply INeR_0; apply lt_INeR; auto.
Qed.
#[global] Hint Resolve INeR_positive : eR.

Lemma sum_map_plus {A} (l : list A) f g :
  sum (map f l) + sum (map g l) = sum (map (fun x => f x + g x) l).
Proof.
  revert f g; induction l; intros f g; simpl.
  { eRauto. }
  rewrite <- eRplus_assoc, eRplus_comm4, eRplus_assoc, IHl; reflexivity.
Qed.

Lemma inf_sum (f g : nat -> eR) :
  dec_chain f ->
  dec_chain g ->
  inf (fun i => f i + g i) = inf f + inf g.
Proof.
  intros Hf Hg.
  apply equ_eR, infimum_inf; auto with eR.
  apply infimum_sum; auto; apply inf_spec; auto with order.
Qed.

Lemma eq_eR_Qeq a b :
  (0 <= a)%Q ->
  (0 <= b)%Q ->
  Q2eR a = Q2eR b ->
  a == b.
Proof.
  intros Ha Hb Heq.
  unfold Q2eR in Heq; inv Heq.
  rewrite Qminmax.Q.max_r in H0; auto.
  rewrite Qminmax.Q.max_r in H0; auto.
  apply Qreals.eqR_Qeq; auto.
Qed.

Lemma Rmult_eq_reg_r (a b c : R) :
  c <> 0%R ->
  (a * c = b * c)%R ->
  a = b.
Proof. intros Hc H; eapply Rmult_eq_reg_r; eauto. Qed.

Lemma R_eq_0_inv (a b : R) :
  (a * b = 0)%R ->
  (a = 0 \/ b = 0)%R.
Proof. intro H; nra. Qed.

Lemma Rinv_0 (a : R) :
  (/ a = 0)%R ->
  (a = 0)%R.
Proof. apply axioms.contrapositive, Rinv_neq_0_compat. Qed.

Lemma eRdiv_mult_l a b c :
  c <> 0 ->
  c <> infty ->
  (c * a) / (c * b) = a / b.
Proof.
  intros Hnz Hninf.
  unfold eRdiv, eRinv, eRmult.
  destruct c as [c|].
  2: { congruence. }
  assert (Hc: c <> 0%R).
  { intro HC; apply Hnz, eR_eq; auto. }
  destruct a as [a|].
  - destruct b as [b|].
    + destruct (R_eq_dec (c * b) 0).
      * destruct (R_eq_dec b 0).
        { destr.
          - destr; auto.
            exfalso; apply n; inv e1; apply eR_eq; nra.
          - destr; auto.
            exfalso; apply n, eR_eq; inv e1; lra. }
        { exfalso; apply n; nra. }
      * destruct (R_eq_dec b 0).
        { exfalso; apply n; nra. }
        apply eR_eq.
        rewrite Rinv_mult.
        replace (c * a * (/ c * / b))%R with (c * / c * (a * / b))%R.
        { field; auto. }
        lra.
    + destruct (eR_eq_dec (er c r) 0); simpl.
      * inv e; lra.
      * apply eR_eq; lra.
  - destruct (eR_eq_dec (er c r) 0).
    + inv e; lra.
    + destruct b as [b|].
      * destruct (R_eq_dec (c * b) 0).
        { assert (b = 0)%R by nra; subst.
          destr.
          - inv e0.
          - destruct (R_eq_dec 0 0).
            + destr; auto.
            + destr; congruence. }
        { destruct (R_eq_dec b 0); subst.
          - exfalso; apply n0; lra.
          - destruct (eR_eq_dec (er (/ b) (Rlt_le 0 (/ b)
                                             (Rinv_0_lt_compat b
                                                (Rle_not_eq_Rlt 0 b r0 n1)))) 0).
            + inv e; destr; auto.
              exfalso; apply n2, eR_eq.
              rewrite Rinv_mult.
              rewrite H0; lra.
            + destr; auto.
              inv e.
              rewrite Rinv_mult in H0.
              apply R_eq_0_inv in H0; destruct H0 as [H0|H0].
              { apply Rinv_0 in H0; lra. }
              exfalso; apply n2, eR_eq; auto. }
      * destr; auto.
Qed.

Lemma Q2eR_nz (a : Q) :
  (0 < a)%Q ->
  Q2eR a <> 0.
Proof.
  intros Ha HC; inv HC.
  assert (H: Q2R (Qmax 0 a) = Q2R 0) by lra.
  apply Qreals.eqR_Qeq, Q.max_l_iff in H.
  apply Qlt_not_le in Ha; contradiction.
Qed.

Lemma one_minus_Q2eR_nz (a : Q) :
  (0 <= a)%Q -> (* Not strictly necessary but makes it easier. *)
  (a < 1)%Q ->
  1 - Q2eR a <> 0.
Proof.
  intros H0 H1.
  unfold eRminus; simpl.
  destr.
  - intro HC; inv HC.
    rewrite Q.max_r in H2; auto.
    rewrite Q.max_r in r; auto.
    assert (Q2R a = 1)%R by lra.
    replace 1%R with (Q2R 1) in H by lra.
    apply Qreals.eqR_Qeq in H.
    Require Import Lqa.
    lra. (* Ugly but I really don't care right now. *)
    Require Import Lra.
  - intro HC.
    apply n.
    replace 1%R with (Q2R 1) by lra.
    apply Qreals.Qle_Rle.
    apply Q.max_lub; auto.
    + apply Q0_le_1.
    + apply Qlt_le_weak; auto.
Qed.

Lemma eRmult_lt_compat_l a b c :
  c * a < c * b ->
  a < b.
Proof.
  unfold eRmult.
  intro Hlt.
  destruct c as [c|].
  - destruct a as [a|].
    + destruct b as [b|].
      * inv Hlt; constructor; nra.
      * constructor.
    + destruct b as [b|].
      * destruct (eR_eq_dec (er c r) 0).
        { inv e; inv Hlt; lra. }
        inv Hlt.
      * destruct (eR_eq_dec (er c r) 0); auto.
        inv Hlt; lra.
  - destruct (eR_eq_dec a 0); subst.
    + destruct (eR_eq_dec b 0); subst; eRauto.
    + destruct (eR_eq_dec b 0); inv Hlt.
Qed.

Lemma eRmult_eRlt a b :
  a <> infty ->
  0 < a * b ->
  0 < b.
Proof. intros Ha Hab; apply eRmult_lt_compat_l with a; eRauto. Qed.  

Lemma eRmult_le_div (a b c : eR) :
  a <> 0 ->
  a <> infty ->
  a * b <= c ->
  b <= c / a.
Proof.
  intros Ha Ha' Hle.
  apply eRmult_le_reg_r with a; auto.
  - eRauto.
  - unfold eRdiv.
    rewrite eRmult_assoc.
    rewrite eRinv_l; auto.
    rewrite eRmult_comm; eRauto.
Qed.
