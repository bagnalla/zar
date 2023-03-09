(** * Sieve of Eratosthenes without algebraic coinduction. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
  Basics
  Equivalence
  Lia
  Morphisms
  Equality
  List
  Nat
.
Local Open Scope program_scope.
Local Open Scope equiv_scope.
Import ListNotations.

From Coq Require Import
  Reals
  Raxioms
  Rpower
  FunctionalExtensionality
  ClassicalChoice
.

From zar Require Import aCPO axioms misc colist cpo order tactics.

Local Open Scope order_scope.

Fixpoint afilter {A} (f : A -> bool) (l : alist A) : alist A :=
  match l with
  | anil => anil
  | atau l' => atau (afilter f l')
  | acons a l' => if f a then acons a (afilter f l') else atau (afilter f l')
  end.

CoFixpoint cofilter {A} (f : A -> bool) (l : colist A) : colist A :=
  match l with
  | conil => conil
  | cotau l' => cotau (cofilter f l')
  | cocons a l' => if f a then cocons a (cofilter f l') else cotau (cofilter f l')
  end.

CoFixpoint nats (n : nat) : colist nat := cocons n (nats (S n)).

Fixpoint sieve_aux_alist (l : alist nat) : alist nat :=
  match l with
  | anil => anil
  | atau l' => atau (sieve_aux_alist l')
  | acons n l' => acons n (afilter (fun m => negb (m mod n =? O)) (sieve_aux_alist l'))
  end.

CoFixpoint sieve_aux (l : colist nat) : colist nat :=
  match l with
  | conil => conil
  | cotau l' => cotau (sieve_aux l')
  | cocons n l' => cocons n (sieve_aux (cofilter (fun m => negb (m mod n =? O)) l'))
  end.

(* Bad definition. *)
(* CoFixpoint sieve (n : nat) : colist nat := *)
(*   cocons n (cotau (cofilter (fun m => m mod n =? O) (cotau (sieve (S n))))). *)

Definition sieve : colist nat := sieve_aux (nats 2).
Definition sieve_list (n : nat) : alist nat := sieve_aux_alist (prefix n (nats 2)).

Lemma cofilter_comm_leq {A} (P Q : A -> bool) (l : colist A) :
  cofilter P (cofilter Q l) ⊑ cofilter Q (cofilter P l).
Proof.
  simpl.
  revert l P Q.
  cofix CH; intros l P Q.
  destruct l.
  - rewrite unf_eq; constructor.
  - rewrite unf_eq; simpl.
    rewrite (@unf_eq _ (cofilter Q (cofilter P (cotau l)))); simpl.
    constructor; auto.
  - rewrite unf_eq; simpl.
    rewrite (@unf_eq _ (cofilter Q (cofilter P (cocons a l)))); simpl.
    destruct (P a) eqn:HPa, (Q a) eqn:HQa.
    + rewrite HPa; constructor; auto.
    + constructor; auto.
    + rewrite HPa; constructor; auto.
    + constructor; auto.
Qed.

Lemma cofilter_comm {A} (P Q : A -> bool) (l : colist A) :
  cofilter P (cofilter Q l) = cofilter Q (cofilter P l).
Proof. apply ext; split; apply cofilter_comm_leq. Qed.

Lemma cofilter_comm_impl_leq {A} (P Q : A -> bool) (l : colist A) :
  (forall a, P a = true -> Q a = true) ->
  cofilter P (cofilter Q l) ⊑ cofilter P l.
Proof.
  revert l.
  cofix CH; intros l HPQ.
  destruct l; simpl.
  - rewrite unf_eq; constructor.
  - rewrite unf_eq; simpl.
    rewrite (@unf_eq _ (cofilter P (cotau l))); simpl.
    constructor; apply CH; auto.
  - rewrite unf_eq; simpl.
    rewrite (@unf_eq _ (cofilter P (cocons a l))); simpl.
    destruct (Q a) eqn:HQa.
    + destruct (P a); constructor; apply CH; auto.
    + destruct (P a) eqn:HPa.
      * apply HPQ in HPa; congruence.
      * constructor; apply CH; auto.
Qed.

Lemma cofilter_comm_impl_leq' {A} (P Q : A -> bool) (l : colist A) :
  (forall a, P a = true -> Q a = true) ->
  cofilter P l ⊑ cofilter P (cofilter Q l).
Proof.
  revert l.
  cofix CH; intros l HPQ.
  destruct l; simpl.
  - rewrite unf_eq; constructor.
  - rewrite unf_eq; simpl.
    rewrite (@unf_eq _ (cofilter P (cofilter Q (cotau l)))); simpl.
    constructor; apply CH; auto.
  - rewrite unf_eq; simpl.
    rewrite (@unf_eq _ (cofilter P (cofilter Q (cocons a l)))); simpl.
    destruct (P a) eqn:HPa.
    + assert (HQa: Q a = true) by (apply HPQ; auto).
      rewrite HQa, HPa; constructor; apply CH; auto.
    + destruct (Q a) eqn:HQa.
      * rewrite HPa; constructor; apply CH; auto.
      * constructor; apply CH; auto.
Qed.

Lemma cofilter_comm_impl {A} (P Q : A -> bool) (l : colist A) :
  (forall a, P a = true -> Q a = true) ->
  cofilter P (cofilter Q l) = cofilter P l.
Proof.
  intro HPQ.
  apply ext; split.
  - apply cofilter_comm_impl_leq; auto.
  - apply cofilter_comm_impl_leq'; auto.
Qed.

Lemma sieve_aux_prefix n l :
  sieve_aux_alist (prefix n l) = prefix n (sieve_aux l).
Proof.
  revert l; induction n; intro l; simpl; auto.
  destruct l; simpl; auto.
  - rewrite IHn; reflexivity.
  - rewrite IHn; f_equal.
    clear IHn.
    revert n0 l.
    induction n; intros m l; simpl; auto.
    destruct l; simpl; auto.
    + rewrite IHn; auto.
    + destruct (n0 mod m =? O) eqn:Hmod; simpl.
      * rewrite IHn; f_equal; f_equal; f_equal.
        rename n0 into k.
        apply cofilter_comm_impl.
        intros i Hi.
        apply Bool.negb_true_iff in Hi.
        apply Bool.negb_true_iff.
        (* k is a multiple of m. *)
        (* i is not a multiple of m. *)
        (* therefore, i is not a multiple of k. *)
        destruct (Nat.eqb_spec (k mod m) 0); try congruence.
        destruct (Nat.eqb_spec (i mod m) 0); try congruence.
        destruct (Nat.eqb_spec (i mod k) 0); try congruence.
        exfalso; apply n0; clear n0.
        destruct i, m, k; auto.
        { simpl; lia. }
        { inv e. }
        { inv e0. }
        apply Nat.mod_divides in e; try lia.
        apply Nat.mod_divides in e0; try lia.
        apply Nat.mod_divides; try lia.
        destruct e as [a Ha].
        destruct e0 as [b Hb].
        eexists.
        rewrite Hb. rewrite Ha. rewrite Nat.mul_assoc; reflexivity.
      * rewrite IHn, cofilter_comm; auto.
Qed.

(* Eval compute in (sieve_list 100). *)

(** Extracting the sieve. *)
From Coq Require Import ExtrOcamlBasic.
Extraction "extract/sieve/sieve.ml" sieve.

Definition is_prime (n : nat) : Prop :=
  1 < n /\ forall m, 1 < m -> n <> m -> n mod m <> O.

CoInductive colist_forall {A} (P : A -> Prop) : colist A -> Prop :=
| colist_forall_nil : colist_forall P conil
| colist_forall_tau : forall l,
    colist_forall P l ->
    colist_forall P (cotau l)
| colist_forall_cons : forall a l,
    P a ->
    colist_forall P l ->
    colist_forall P (cocons a l).

Inductive alist_forall {A} (P : A -> Prop) : alist A -> Prop :=
| alist_forall_nil : alist_forall P anil
| alist_forall_tau : forall l,
    alist_forall P l ->
    alist_forall P (atau l)
| alist_forall_cons : forall a l,
    P a ->
    alist_forall P l ->
    alist_forall P (acons a l).

Lemma alist_forall_colist_forall {A} (P : A -> Prop) (l : colist A) :
  (forall n, alist_forall P (prefix n l)) -> colist_forall P l.
Proof.
  revert P l; cofix CH; intros P l H.
  destruct l.
  - constructor.
  - constructor; apply CH; intro n.
    specialize (H (S n)); inv H; auto.
  - assert (colist_forall P l).
    { apply CH; intro n; specialize (H (S n)); inv H; auto. }
    specialize (H (S O)); inv H; constructor; auto.
Qed.

Lemma colist_forall_alist_forall {A} (P : A -> Prop) (l : colist A) :
  colist_forall P l -> (forall n, alist_forall P (prefix n l)).
Proof.
  intros H n.
  revert l H; induction n; intros l H; simpl.
  { constructor. }
  inv H; constructor; auto.
Qed.

Inductive colist_exists {A} (P : A -> Prop) : colist A -> Prop :=
| colist_exists_tau : forall l,
    colist_exists P l ->
    colist_exists P (cotau l)
| colist_exists_hd : forall a l,
    P a ->
    colist_exists P (cocons a l)
| colist_exists_tl : forall a l,
    ~ P a ->
    colist_exists P l ->
    colist_exists P (cocons a l).

Inductive alist_exists {A} (P : A -> Prop) : alist A -> Prop :=
| alist_exists_tau : forall l,
    alist_exists P l ->
    alist_exists P (atau l)
| alist_exists_hd : forall a l,
    P a ->
    alist_exists P (acons a l)
| alist_exists_tl : forall a l,
    ~ P a ->
    alist_exists P l ->
    alist_exists P (acons a l).

Lemma alist_exists_colist_exists {A} (P : A -> Prop) (l : colist A) :
  (exists n, alist_exists P (prefix n l)) -> colist_exists P l.
Proof.
  intros [n H].
  revert H. revert l.
  induction n; simpl; intros l H.
  { inv H. }
  destruct l; inv H.
  - constructor; apply IHn; auto.
  - constructor; auto.
  - apply colist_exists_tl; auto.
Qed.

Lemma colist_exists_alist_exists {A} (P : A -> Prop) (l : colist A) :
  colist_exists P l ->  exists n, alist_exists P (prefix n l).
Proof.
  induction 1.
  - destruct IHcolist_exists as [n IH].
    exists (S n).
    simpl; constructor; auto.
  - exists (S O); constructor; auto.
  - destruct IHcolist_exists as [n IH].
    exists (S n); apply alist_exists_tl; auto.
Qed.

Lemma alists_exists_nats n m k :
  m <= n ->
  n < m + k ->
  alist_exists (eq n) (prefix k (nats m)).
Proof.
  revert n m; induction k; intros n m H0 H1.
  { lia. }
  simpl.
  destruct (Nat.eqb_spec n m); subst.
  - constructor; auto.
  - apply alist_exists_tl; auto.
    apply IHk; lia.
Qed.

Lemma nats_exists (n m : nat) :
  m <= n ->
  colist_exists (eq n) (nats m).
Proof.
  intro Hle.
  apply alist_exists_colist_exists.
  exists (n - m + 1).
  apply alists_exists_nats; lia.
Qed.

Lemma alist_exists_afilter {A} (a : A) (l : alist A) (P : A -> bool) :
  P a = true ->
  alist_exists (eq a) l ->
  alist_exists (eq a) (afilter P l).
Proof.
  revert a P; induction l; intros x P HPx Hex; inv Hex; simpl.
  - constructor; auto.
  - rewrite HPx; constructor; auto.
  - destruct (P a) eqn:HPa.
    + apply alist_exists_tl; auto.
    + constructor; auto.
Qed.

Lemma prime_exists_sieve_aux (n : nat) (l : colist nat) :
  is_prime n ->
  colist_forall (fun m => 1 < m) l ->
  colist_exists (eq n) l ->
  colist_exists (eq n) (sieve_aux l).
Proof.
  intros Hn Hlt Hex.
  apply colist_exists_alist_exists in Hex.
  destruct Hex as [k Hex].
  apply alist_exists_colist_exists.
  exists k.
  rewrite <- sieve_aux_prefix.
  apply colist_forall_alist_forall with (n := k) in Hlt; auto.
  revert Hlt Hex.
  generalize (prefix k l) as l'.
  clear l k; intro l.  
  revert Hn; revert n.
  induction l; intros n Hn Hlt Hex; inv Hlt; inv Hex.
  - constructor; auto.
  - constructor; auto.
  - apply alist_exists_tl; auto.
    apply alist_exists_afilter; auto.
    unfold is_prime in Hn.
    destruct Hn as [Hn Hn'].
    apply Hn' in H1; auto.
    destruct (Nat.eqb_spec (n mod a) O); auto.
Qed.

Lemma prime_exists_sieve_aux_nats (n m : nat) :
  1 < m ->
  m <= n ->
  is_prime n ->
  colist_exists (eq n) (sieve_aux (nats m)).
Proof.
  intros Hlt Hle Hn.
  apply prime_exists_sieve_aux; auto.
  - clear Hle Hn n.
    revert Hlt; revert m.
    cofix CH; intros n Hn.
    rewrite unf_eq; constructor; auto.
  - apply nats_exists; auto.
Qed.

Lemma is_prime_2_le n :
  is_prime n ->
  2 <= n.
Proof. intros [H ?]; inv H; auto. Qed.

Theorem prime_exists_sieve (n : nat) :
  is_prime n ->
  colist_exists (eq n) sieve.
Proof.
  intro Hn; apply prime_exists_sieve_aux_nats; auto; apply is_prime_2_le; auto.
Qed.

Lemma prefix_cofilter {A} (P : A -> bool) (l : colist A) n :
  prefix n (cofilter P l) = afilter P (prefix n l).
Proof.
  revert l; induction n; intro l; simpl; auto.
  destruct l; simpl; auto.
  - rewrite IHn; auto.
  - destruct (P a); rewrite IHn; auto.
Qed.

CoInductive alist_increasing_from : nat -> alist nat -> Prop :=
| alist_increasing_from_nil : forall n, alist_increasing_from n anil
| alist_increasing_from_tau : forall n l,
    alist_increasing_from n l ->
    alist_increasing_from n (atau l)
| alist_increasing_from_cons : forall n l,
    alist_increasing_from (S n) l ->
    alist_increasing_from n (acons n l).

CoInductive increasing_from : nat -> colist nat -> Prop :=
| increasing_from_nil : forall n, increasing_from n conil
| increasing_from_tau : forall n l,
    increasing_from n l ->
    increasing_from n (cotau l)
| increasing_from_cons : forall n l,
    increasing_from (S n) l ->
    increasing_from n (cocons n l).

Lemma alist_forall_afilter {A} (P : A -> Prop) (Q : A -> bool) (l : alist A) :
  alist_forall P l ->
  alist_forall (fun x => P x /\ Q x = true) (afilter Q l).
Proof.
  induction l; intro Hl; inv Hl; simpl.
  - constructor.
  - constructor; auto.
  - destruct (Q a) eqn:HQa; constructor; auto.
Qed.

Lemma alist_forall_afilter' {A} (P : A -> Prop) (Q : A -> bool) (l : alist A) :
  alist_forall P l ->
  alist_forall P (afilter Q l).
Proof.
  induction l; intro Hl; inv Hl; simpl.
  - constructor.
  - constructor; auto.
  - destruct (Q a) eqn:HQa; constructor; auto.
Qed.

Lemma alist_forall_impl {A} (P Q : A -> Prop) (l : alist A) :
  (forall x, P x -> Q x) ->
  alist_forall P l ->
  alist_forall Q l.
Proof. induction l; intros HPQ HP; inv HP; constructor; auto. Qed.

Lemma alist_forall_sieve_aux_alist l n :
  1 < n ->
  alist_increasing_from n l ->
  alist_forall (fun n0 : nat => n <= n0 /\ (forall m : nat, n <= m -> n0 <> m -> n0 mod m <> 0))
    (sieve_aux_alist l).
Proof.
  revert n.
  induction l; simpl; intros n Hlt Hl; inv Hl.
  { constructor. }
  { constructor; auto. }
  constructor.
  - split; auto.
    intros n Hle Hneq.
    (* a is strictly less than n so can't be a multiple of n. *)
    intro HC.
    apply Nat.mod_divides in HC; try lia.
    destruct HC as [c HC]; subst.
    destruct c; lia.
  - assert (Hlt': 1 < S a) by lia.
    specialize (IHl _ Hlt' H1).
    eapply alist_forall_impl.
    2: { apply alist_forall_afilter; eauto. }
    intros n [[H0 H2] H3]; split.
    + apply Bool.negb_true_iff in H3.
      apply Nat.eqb_neq in H3.
      (* H3 implies a <> n which together with H0 implies the goal. *)
      lia.
    + intros m Hle Hneq.
      apply Bool.negb_true_iff in H3.
      apply Nat.eqb_neq in H3.
      intro HC.
      eapply H2.
      2: { eauto. }
      2: { auto. }
      destruct (Nat.eqb_spec a m); subst; lia.
Qed.

Lemma alist_increasing_from_nats n k :
  alist_increasing_from k (prefix n (nats k)).
Proof.
  revert k; induction n; intro k; simpl.
  { constructor. }
  constructor; auto.
Qed.

Theorem sieve_forall :
  colist_forall is_prime sieve.
Proof.
  apply alist_forall_colist_forall; intro n.
  unfold is_prime.
  unfold sieve.
  rewrite <- sieve_aux_prefix.
  apply alist_forall_sieve_aux_alist; try lia.
  apply alist_increasing_from_nats.
Qed.

Inductive alist_nodup {A} : alist A -> Prop :=
| alist_nodup_nil : alist_nodup anil
| alist_nodup_tau : forall l,
    alist_nodup l ->
    alist_nodup (atau l)
| alist_nodup_cons : forall a l,
    alist_forall (fun x => x <> a) l ->
    alist_nodup l ->
    alist_nodup (acons a l).

CoInductive colist_nodup {A} : colist A -> Prop :=
| colist_nodup_nil : colist_nodup conil
| colist_nodup_tau : forall l,
    colist_nodup l ->
    colist_nodup (cotau l)
| colist_nodup_cons : forall a l,
    colist_forall (fun x => x <> a) l ->
    colist_nodup l ->
    colist_nodup (cocons a l).

Lemma alist_nodup_colist_nodup {A} (l : colist A) :
  (forall n, alist_nodup (prefix n l)) -> colist_nodup l.
Proof.
  revert l; cofix CH; intros l H.
  destruct l.
  - constructor.
  - constructor; apply CH; intro n.
    specialize (H (S n)); inv H; auto.
  - constructor.
    + apply alist_forall_colist_forall; intro n.
      specialize (H (S n)); inv H; auto.
    + apply CH; intro n; specialize (H (S n)); inv H; auto.
Qed.

Lemma colist_nodup_alist_nodup {A} (l : colist A) :
  colist_nodup l -> (forall n, alist_nodup (prefix n l)).
Proof.
  intros H n; revert H; revert l; induction n; intros l Hl.
  { constructor. }
  inv Hl.
  - constructor.
  - constructor; auto.
  - constructor; auto.
    apply colist_forall_alist_forall; auto.
Qed.

Lemma alist_forall_sieve_aux_alist' P l :
  alist_forall P l ->
  alist_forall P (sieve_aux_alist l).
Proof.
  induction l; intro Hl; inv Hl; constructor; auto.
  apply alist_forall_afilter'; auto.
Qed.

Lemma alist_nodup_afilter {A} (P : A -> bool) (l : alist A) :
  alist_nodup l ->
  alist_nodup (afilter P l).
Proof.
  induction l; intro Hl; inv Hl.
  - constructor.
  - constructor; auto.
  - simpl; destruct (P a); constructor; auto.
    apply alist_forall_afilter'; auto.
Qed.
  
Lemma colist_nodup_sieve_aux l :
  colist_nodup l ->
  colist_nodup (sieve_aux l).
Proof.
  intro H.
  apply alist_nodup_colist_nodup; intro n.
  apply colist_nodup_alist_nodup with (n:=n) in H.
  rewrite <- sieve_aux_prefix.
  revert H.
  generalize (prefix n l).
  clear l; intro l; induction l; intro Hl; inv Hl.
  - constructor.
  - constructor; auto.
  - constructor.
    + apply alist_forall_afilter'.
      apply alist_forall_sieve_aux_alist'; auto.
    + apply alist_nodup_afilter; auto.
Qed.

Lemma colist_forall_neq_nats (n m : nat) :
  n < m ->
  colist_forall (fun x : nat => x <> n) (nats m).
Proof.
  revert n m; cofix CH; intros n m Hnm.
  rewrite unf_eq; constructor; auto; lia.
Qed.

Lemma colist_nodup_nats (n : nat) :
  colist_nodup (nats n).
Proof.
  revert n; cofix CH; intro n.
  rewrite unf_eq; constructor; auto.
  apply colist_forall_neq_nats; lia.
Qed.

Theorem sieve_nodup :
  colist_nodup sieve.
Proof.
  apply colist_nodup_sieve_aux, colist_nodup_nats.
Qed.

Fixpoint remove_taus {A} (l : alist A) : alist A :=
  match l with
  | anil => anil
  | atau l' => remove_taus l'
  | acons a l' => acons a (remove_taus l')
  end.

(* Eval compute in (remove_taus (prefix 100 sieve)). *)
