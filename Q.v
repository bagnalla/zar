(** * Rational numbers. *)

Set Implicit Arguments.

From Coq Require Import
  QArith
  Lia
  Lqa
.

Definition N2Q (n : nat) : Q := Z.of_nat n # 1.

Lemma Qdiv_0_num (a : Q) : 0 / a == 0.
Proof. destruct a; destruct Qnum; compute; reflexivity. Qed.

Lemma Q0_le_1 : 0 <= 1. Proof. lra. Qed.
Lemma Q0_lt_2 : 0 < 2. Proof. lra. Qed.

Lemma inject_Z_pos_nonzero (p : positive) :
  ~ inject_Z (Z.pos p) == 0.
Proof. compute; congruence. Qed.

Lemma inject_Z_pos_positive (p : positive) :
  0 < inject_Z (Z.pos p).
Proof. reflexivity. Qed.

Lemma pos_num_le_den (n d : positive) :
  Z.pos n # d <= 1 ->
  (n <= d)%positive.
Proof.
  intro H.
  rewrite Qmake_Qdiv in H.
  apply (Qmult_le_compat_r _ _ (inject_Z (Z.pos d))) in H.
  - rewrite Qmult_1_l in H.
    rewrite Qmult_comm in H.
    rewrite Qmult_div_r in H.
    + rewrite <- Zle_Qle in H; apply H.
    + apply inject_Z_pos_nonzero.
  - apply Qlt_le_weak, inject_Z_pos_positive.
Qed.

Lemma Q_num_le_den p :
  p <= 1 ->
  (Z.to_nat (Qnum p) <= Pos.to_nat (Qden p))%nat.
Proof.
  intros Hle.
  destruct p. simpl.
  destruct Qnum, Qden; simpl; try lia;
    apply Pos2Nat.inj_le, pos_num_le_den; auto.
Qed.

Lemma Qnum_nonnegative p :
  0 <= p ->
  (0 <= Qnum p)%Z.
Proof. intro Hle; destruct p; unfold Qle in Hle; simpl in *; lia. Qed.

Lemma Qle_num_1 (p : Z) :
  (0 < p)%Z ->
  1 <= p # 1.
Proof. intro Hp; unfold Qle; simpl; lia. Qed.
