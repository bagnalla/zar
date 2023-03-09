(** * Computing the next power of 2. *)

(** Apparently there is a Nat.log2_up function that probably obviates
    the need for most of the things in this file. *)

From Coq Require Import
  Nat
  PeanoNat
  Arith
  Lia
.

Definition is_power_of_2 (n : nat) : Prop := exists m, 2^m = n.

Definition is_power_of_2b (n : nat) := n =? 2 ^ log2 n.

Lemma is_power_of_2b_spec (n : nat)
  : Bool.reflect (is_power_of_2 n) (is_power_of_2b n).
Proof.
  destruct (is_power_of_2b n) eqn:H; constructor.
  - unfold is_power_of_2b in H; apply Nat.eqb_eq in H.
    exists (log2 n); auto.
  - apply Nat.eqb_neq in H.
    intro Contra; apply H.
    destruct Contra as [m Contra].
    subst; rewrite Nat.log2_pow2; lia.
Qed.

(** The function *)
Definition next_pow_2 (n : nat) :=
  if n =? 0 then 1 else if is_power_of_2b n then n else 2 ^ S (log2 n).

Lemma not_pow_2_le_lt (n m : nat) : ~ is_power_of_2 n -> n <= 2^m -> n < 2^m.
Proof.
  intros H0 H1; unfold is_power_of_2 in H0.
  assert (forall k, 2 ^ k <> n).
  { intros k HC. apply H0. exists k; auto. }
  specialize (H m);  lia.
Qed.

Lemma pow_2_lt_le (a b : nat) : 2^a < 2^b -> 2*2^a <= 2^b.
Proof.
  intro H.
  assert (H0: 2 * 2^a = 2 ^ (S a)). auto.
  rewrite H0. clear H0.
  assert (a < b).
  { rewrite Nat.pow_lt_mono_r_iff; eauto. }
  unfold lt in H0.
  apply Nat.pow_le_mono_r; auto.
Qed.

Lemma pow_positive (n k : nat) :
  0 < n ->
  0 < pow n k.
Proof.
  revert n; induction k; simpl; intros n Hlt; try lia.
  specialize (IHk n Hlt); lia.
Qed.

(** Specification and proof. *)
Lemma next_pow_2_spec (n : nat) :
  is_power_of_2 (next_pow_2 n) /\
    n <= next_pow_2 n /\
    forall m, n <= 2^m -> next_pow_2 n <= 2^m.
Proof.
  split.
  - unfold next_pow_2. destruct n; simpl.
    + exists 0; auto.
    + destruct (is_power_of_2b_spec (S n)); auto.
      rewrite Nat.add_0_r.
      exists (S (log2 (S n))); simpl; auto.
  - split.
    + unfold next_pow_2.
      destruct n; simpl; auto.
      destruct (is_power_of_2b_spec (S n)); auto.
      generalize (Nat.log2_spec (S n) (Nat.lt_0_succ n)). intros [_ H0].
      simpl in H0; lia.
    + intros m Hm; unfold next_pow_2.
      destruct n; simpl.
      * clear Hm; induction m; auto; simpl; lia.
      * destruct (is_power_of_2b_spec (S n)); auto.
        generalize (Nat.log2_spec (S n) (Nat.lt_0_succ n)). intros [H0 H1].
        rewrite Nat.add_0_r.
        apply not_pow_2_le_lt with (m:=m) in n0; auto.
        assert (H2: 2 ^ log2 (S n) < 2^m). lia.
        apply pow_2_lt_le in H2; lia.
Qed.

(** Immediate corollaries / helpers. *)

Lemma is_power_of_2_next_pow_2 (n : nat) :
  is_power_of_2 (next_pow_2 n).
Proof. apply next_pow_2_spec. Qed.

Lemma next_pow_2_ub (n : nat) :
  n <= next_pow_2 n.
Proof. apply next_pow_2_spec. Qed.

Lemma next_pow_2_positive (n : nat) :
  0 < next_pow_2 n.
Proof.
  generalize (is_power_of_2_next_pow_2 n); intros [k H].
  rewrite <- H.
  apply pow_positive; lia.
Qed.
