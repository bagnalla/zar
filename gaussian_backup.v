(** * Discrete Gaussian. *)

From Coq Require Import Basics QArith Lia Lqa String Qabs.
Open Scope string_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From cwp Require Import compile cpGCL itree Q tree.

Local Open Scope cpGCL_scope.
(* Local Open Scope nat_scope. *)

Definition incr (v : val) : val :=
  match v with
  | vnat n => vnat (S n)
  | vint n => vint (n + 1)
  | _ => v
  end.

Definition is_even (v : val) : val :=
  match v with
  | vnat n => vbool (Nat.even n)
  | vint n => vbool (Z.even n)
  | _ => vbool false
  end.

(* Assumes 0 <= gamma <= 1. *)
(* Clobbers: k, a *)
(* Slightly modified from version in paper to make it obvious that the
   divisor is always nonzero. *)
Definition bernoulli_exponential_0_1 (out : string) (gamma : St -> Q) : cpGCL :=
  "k" <-- O;
  "a" <-- true;
  while (fun s : St => s "a") do
      CChoice (fun s => gamma s / N2Q (S (as_nat (s "k"))))
              (fun b => if b then "k" <-- fun s => incr (s "k") else "a" <-- false)
  end;
  if (fun s => is_even (s "k")) then out <-- true else out <-- false end.

(* Set Printing All. *)
(* Print bernoulli_exponential_0_1. *)

(* Lemma wf_bernoulli_exponential_0_1 (out : string) (gamma : Q) : *)
(*   0 <= gamma <= 1 -> *)
(*   wf_cpGCL (bernoulli_exponential_0_1 out gamma). *)
(* Proof. *)
(*   intros [H0 H1]; repeat constructor. *)
(*   - apply Qle_shift_div_l; try lra. *)
(*     unfold N2Q, Qlt; simpl; lia. *)
(*   - apply Qle_shift_div_r. *)
(*     + unfold N2Q, Qlt; simpl; lia. *)
(*     + rewrite Qmult_1_l; eapply Qle_trans; eauto. *)
(*       apply Qle_num_1; lia. *)
(*   - intros []; constructor. *)
(* Qed. *)

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

(* (* Assumes 0 <= gamma. *) *)
(* Definition bernoulli_exponential (out : nat) (gamma : Q) : cpGCL := *)
(*   let k := 2%nat in *)
(*   let b := 3%nat in *)
(*   if Qle_bool gamma 1 then *)
(*     bernoulli_exponential_0_1 out gamma *)
(*   else *)
(*     k <-- S O; *)
(*     b <-- true; *)
(*     while (fun s => as_bool (s b) && Qle_bool (N2Q (as_nat (s k))) gamma) do *)
(*       bernoulli_exponential_0_1 b 1; *)
(*       k <-- fun s => incr (s k) *)
(*     end; *)
(*     if (fun s => s b) then *)
(*       bernoulli_exponential_0_1 out (gamma - (Qround.Qfloor gamma # 1)) *)
(*     else *)
(*       out <-- O *)
(*     end. *)

(* Assumes 0 <= gamma. *)
(* Clobbers: k, a, i, b *)
Definition bernoulli_exponential (out : string) (gamma : St -> Q) : cpGCL :=
  (* if Qle_bool gamma 1 then *)
  (* if (fun s => Qle_bool (gamma s) 1) then *)
  CIte (fun s => Qle_bool (gamma s) 1)
    (bernoulli_exponential_0_1 out gamma)
  (* else *)
    ("i" <-- S O;
    "b" <-- true;
    while (fun s => as_bool (s "b") && Qle_bool (N2Q (as_nat (s "i"))) (gamma s)) do
      bernoulli_exponential_0_1 "b" (const 1);
      "i" <-- fun s => incr (s "i")
    end;
    if (fun s => s "b") then
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
  (forall s, 0 <= gamma s <= 1) ->
  wf_cpGCL (bernoulli_exponential out gamma).
Proof.
  intro Hg.
  constructor.
  { apply wf_bernoulli_exponential_0_1; auto. }
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

Definition flip (x : string) (p : Q) : cpGCL :=
  CChoice (const p) (fun b => x <-- b).

(* Clobbers: k, a, i, b, lp, d, v, il, x, y, c *)
Definition laplace (out : string) (s t : nat) : cpGCL :=
  "lp" <-- true;
  while (fun s => s "lp") do
    CUniform (const t)
      (fun u =>
         bernoulli_exponential "d" (fun s => Z.of_nat (min u t) # Pos.of_nat t);
         if (fun s => s "d") then
           "v" <-- (fun s => O);
           bernoulli_exponential "il" (const 1);
           while (fun s => s "il") do
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

Ltac wf :=
  constructor; try solve [repeat constructor]; auto.

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
    split.
    - apply Qle_0_of_nat.
    - destruct (Nat.leb_spec0 n t).
      + rewrite min_l; auto.
        apply Qmake_le_1.
        rewrite Z_pos_of_nat; auto.
        apply inj_le; auto.
      + rewrite min_r; try lia.
        apply Qmake_le_1.
        rewrite Z_pos_of_nat; auto.
        apply inj_le; auto. }
  wf. wf. wf.
  { apply wf_bernoulli_exponential; intro st; unfold const; lra. }
  wf.
  { wf. wf.
    apply wf_bernoulli_exponential; intro st; unfold const; lra. }
  wf. wf. wf. wf.
  intro st; unfold const; lra.
Qed.

Lemma lem1 b :
  0 <= (let a := b in if Qle_bool 0 a && Qle_bool a 1 then a else 0) <= 1.
Proof.
  split; simpl.
  - destruct (Qle_bool 0 b) eqn:Hb; simpl; try lra.
    apply Qle_bool_imp_le in Hb.
    destruct (Qle_bool b 1); auto; lra.
  - destruct (Qle_bool 0 b) eqn:Hb; simpl; try lra.
    destruct (Qle_bool b 1) eqn:Hb1; try lra.
    apply Qle_bool_imp_le in Hb1; auto.
Qed.

(* Assumes 0 < sigma. *)
(* Clobbers: k, a, i, b, lp, d, v, il, x, y, c, t, ol, z *)
Definition gaussian (out : string) (sigma : Q) : cpGCL :=
  let t := S (Z.to_nat (Qround.Qfloor sigma)) in
  "ol" <-- false;
  while (fun s => negb (as_bool (s "ol"))) do
    laplace "z" 1 t;
    bernoulli_exponential "ol"
      (fun s => let q := Qpower (Qabs (as_int (s "z") # 1) - Qpower sigma 2 / N2Q t) 2 /
                        (2 * Qpower sigma 2) in
             if Qle_bool 0 q && Qle_bool q 1 then q else 1)
  end;
  out <-- (fun s => s "z").

(* Lemma wf_gaussian (out : string) (sigma : Q) : *)
(*   0 < sigma -> *)
(*   wf_cpGCL (gaussian out sigma). *)
(* Proof. *)
(*   intro Hs. *)
(*   wf. wf. wf. wf. *)
(*   { apply wf_laplace; lia. } *)
(*   apply wf_bernoulli_exponential. *)
(*   intro s. *)
(*   apply lem1. *)
(* Qed. *)

(* Definition t : tree := compile (bernoulli_exponential_0_1 O (1#2)) empty. *)

(* Eval simpl in compile (bernoulli_exponential_0_1 O (1#2)) empty. *)

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

(* Definition sampler : itree boolE bool := *)
(*   ITree.map (fun s => as_bool (s "")) (cpGCL_to_itree (bernoulli_exponential "" (9#10)) empty). *)
(* Extraction "extract/exponential/exponential.ml" sampler. *)

(* Definition sampler (s t : nat) : itree boolE Z := *)
(*   ITree.map (fun s => as_int (s "")) (cpGCL_to_itree (laplace "" s t) empty). *)
(* Extraction "extract/laplace/laplace.ml" sampler. *)

Definition sampler (sigma : Q) : itree boolE Z :=
  ITree.map (fun s => as_int (s "")) (cpGCL_to_itree (gaussian "" sigma) empty).
Extraction "extract/gaussian/gaussian.ml" sampler.
