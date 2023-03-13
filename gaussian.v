(** * Discrete Gaussian. *)

From Coq Require Import Basics QArith Lia Lqa String Qabs.
Open Scope string_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From zar Require Import compile cpGCL itree prelude Q tactics tree.

Local Open Scope cpGCL_scope.

Definition succ (v : val) : val :=
  match v with
  | vnat n => vnat (S n)
  | vint n => vint (n + 1)
  | _ => v
  end.

Definition is_even (v : val) : bool :=
  match v with
  | vnat n => Nat.even n
  | vint n => Z.even n
  | _ => false
  end.

(** Sampling from Bernoulli(exp(-γ)), where ∀ s, 0 <= γ s <= 1. *)
(* Assumes 0 <= gamma <= 1. *)
(* Clobbers: k, a *)
(* Slightly modified from version in paper to make it obvious that the
   divisor is always nonzero. *)
Definition bernoulli_exponential_0_1 (out : string) (gamma : St -> Q) : cpGCL :=
  "k" <-- O;
  "a" <-- true;
  while (fun s : St => as_bool (s "a")) do
      CChoice (fun s => gamma s / N2Q (S (as_nat (s "k"))))
              (fun b => if b then "k" <-- fun s => succ (s "k") else "a" <-- false)
  end;
  if (fun s => is_even (s "k")) then out <-- true else out <-- false end.

Lemma wf_bernoulli_exponential_0_1 (out : string) (gamma : St -> Q) :
  (forall s, 0 <= gamma s <= 1) ->
  wf_cpGCL (bernoulli_exponential_0_1 out gamma).
Proof.
  intros Hg; repeat constructor.
  - apply Qle_shift_div_l; try lra.
    unfold N2Q, Qlt; simpl; lia.
    rewrite Qmult_0_l; apply Hg.
  - apply Qle_shift_div_r.
    + unfold N2Q, Qlt; simpl; lia.
    + rewrite Qmult_1_l; eapply Qle_trans; eauto.
      * apply Hg.
      * apply Qle_num_1; lia.
  - intros []; constructor.
Qed.

(** Sampling from Bernoulli(exp(-γ)), where ∀ s, 0 <= γ s. *)
(* Assumes 0 <= gamma. *)
(* Clobbers: k, a, i, b *)
Definition bernoulli_exponential (out : string) (gamma : St -> Q) : cpGCL :=
  CIte (fun s => Qle_bool (gamma s) 1)
    (bernoulli_exponential_0_1 out
       (fun s => if Qle_bool (gamma s) 1 then gamma s else 1))
    ("i" <-- S O;
    "b" <-- true;
    while (fun s => as_bool (s "b") && Qle_bool (N2Q (as_nat (s "i"))) (gamma s)) do
      bernoulli_exponential_0_1 "b" (const 1);
      "i" <-- fun s => succ (s "i")
    end;
    if (fun s => as_bool (s "b")) then
      bernoulli_exponential_0_1 out
        (fun s => gamma s - (Qround.Qfloor (gamma s) # 1))
    else
      out <-- O
     end).

Lemma Qle_minus a b :
  b <= a ->
  0 <= a - b.
Proof. lra. Qed.

Lemma Qle_minus' a b c :
  a <= b + c ->
  a - b <= c.
Proof. lra. Qed.

Lemma lem2 a :
  0 <= a - (Qround.Qfloor a # 1) <= 1.
Proof.
  split.
  - apply Qle_minus, Qround.Qfloor_le.
  - apply Qle_minus'.
    apply Qlt_le_weak.
    replace ((Qround.Qfloor a # 1) + 1) with (Qround.Qfloor a + 1 # 1).
    2: { generalize inject_Z_plus; unfold inject_Z.
         intro H; rewrite H; reflexivity. }
    apply Qround.Qlt_floor.
Qed.

Lemma wf_bernoulli_exponential (out : string) (gamma : St -> Q) :
  (forall s, 0 <= gamma s) ->
  wf_cpGCL (bernoulli_exponential out gamma).
Proof.
  intro Hg.
  constructor.
  { apply wf_bernoulli_exponential_0_1; auto.
    intro s; destruct (Qle_bool (gamma s) 1) eqn:H; try lra.
    apply Qle_bool_iff in H; auto. }
  constructor.
  { constructor. }
  constructor.
  { constructor. }
  constructor.
  { constructor; constructor.
    - apply wf_bernoulli_exponential_0_1; unfold const; intro; lra.
    - constructor. }
  constructor.
  { apply wf_bernoulli_exponential_0_1.
    intro s; apply lem2. }
  constructor.
Qed.

(** Sampling from Laplace_Z(t/s), where 0 < s and 0 < t. *)
(* Clobbers: k, a, i, b, lp, d, v, il, x, y, c *)
Definition laplace (out : string) (s t : nat) : cpGCL :=
  "lp" <-- true;
  while (fun s => as_bool (s "lp")) do
    CUniform (const t)
      (fun u =>
         bernoulli_exponential "d" (fun s => Z.of_nat (min u t) # Pos.of_nat t);
         if (fun s => as_bool (s "d")) then
           "v" <-- (fun s => O);
           bernoulli_exponential "il" (const 1);
           while (fun s => as_bool (s "il")) do
             "v" <-- (fun s => S (as_nat (s "v")));
             bernoulli_exponential "il" (const 1)
           end;
           "x" <-- (fun s => (u + t * as_nat (s "v"))%nat);
           "y" <-- (fun st => (as_nat (st "x") / s)%nat);
           flip "c" (1#2);
           CIte (fun s => as_bool (s "c") && Nat.eqb (as_nat (s "y")) O)
                 skip
                 ("lp" <-- (fun s => vbool false);
                  out <-- (fun s => vint ((1 - 2 * (if as_bool (s "c") then 1 else 0))
                                     * Z.of_nat (as_nat (s "y")))%Z))
         else
           skip
         end)
  end.

Lemma z_le_0_Qle n d :
  (0 <= n)%Z ->
  0 <= n # d.
Proof. intro Hn; compute; destruct n; try congruence; lia. Qed.

Lemma Qle_0_of_nat n p :
  0 <= Z.of_nat n # p.
Proof. apply z_le_0_Qle, Zle_0_nat. Qed.

Lemma Qmake_le_1 n d :
  (n <= Zpos d)%Z ->
  n # d <= 1.
Proof.
  intro Hle.
  apply Qmult_lt_0_le_reg_r with (z := Zpos d # 1).
  { apply inject_Z_pos_positive. }
  rewrite Qmult_1_l.
  unfold Qmult.
  simpl.
  rewrite Pos.mul_comm.
  rewrite Qreduce_r.
  generalize (Zle_Qle n (Z.pos d)).
  intro H.
  rewrite H in Hle.
  apply Hle.
Qed.

Lemma Z_pos_of_nat n :
  (0 < n)%nat ->
  Z.pos (Pos.of_nat n) = Z.of_nat n.
Proof. destruct n; lia. Qed.

Lemma wf_laplace (out : string) (s t : nat) :
  (0 < s)%nat ->
  (0 < t)%nat ->
  wf_cpGCL (laplace out s t).
Proof.
  intros Hs Ht.
  wf. wf. wf.
  intro n; wf.
  { eapply wf_bernoulli_exponential; intro st.
    apply Qle_0_of_nat. }
  wf. wf. wf.
  { apply wf_bernoulli_exponential; intro st; unfold const; lra. }
  wf.
  { wf. wf.
    apply wf_bernoulli_exponential; intro st; unfold const; lra. }
  wf. wf. wf. wf.
  intro st; unfold const; lra.
Qed.

Lemma lem1 b :
  0 <= (let a := b in if Qle_bool 0 a then a else 0).
Proof.
  simpl. destruct (Qle_bool 0 b) eqn:Hb; simpl; try lra.
  apply Qle_bool_imp_le in Hb; auto.
Qed.

(** Sampling from Gaussian_Z(0, σ²), where 0 < σ. *)
(* Assumes 0 < sigma. *)
(* Clobbers: k, a, i, b, lp, d, v, il, x, y, c, ol, z *)
Definition gaussian (out : string) (sigma : Q) : cpGCL :=
  let t := S (Z.to_nat (Qround.Qfloor sigma)) in
  "ol" <-- false;
  while (fun s => negb (as_bool (s "ol"))) do
    laplace "z" 1 t;
    bernoulli_exponential "ol"
      (fun s => let q := Qpower (Qabs (as_int (s "z") # 1) - Qpower sigma 2 / N2Q t) 2 /
                        (2 * Qpower sigma 2) in
             if Qle_bool 0 q then q else 0)
  end;
  out <-- (fun s => s "z").

Lemma wf_gaussian (out : string) (sigma : Q) :
  0 < sigma ->
  wf_cpGCL (gaussian out sigma).
Proof.
  intro Hs.
  wf. wf. wf. wf.
  { apply wf_laplace; lia. }
  apply wf_bernoulli_exponential.
  intro s; apply lem1.
Qed.

Definition gauss (out : string) (mu : Z) (sigma : Q) : cpGCL :=
  gaussian "x123" sigma;
  out <-- (fun s => vint (as_int (s "x123") + mu)%Z).

Lemma wf_gauss (out : string) (mu : Z) (sigma : Q) :
  0 < sigma ->
  wf_cpGCL (gauss out mu sigma).
Proof. intro Hs; wf; apply wf_gaussian; auto. Qed.

From Coq Require Import ExtrOcamlBasic ExtrOcamlString.

(* Definition sampler (mu : Z) (sigma : Q) : itree boolE Z := *)
(*   ITree.map (fun s => as_int (s "")) (cpGCL_to_itree (gauss "" mu sigma) empty). *)
(* Extraction "extract/gaussian/sampler.ml" sampler. *)
