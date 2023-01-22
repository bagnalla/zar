(** * cwp on cotrees. *)

Set Implicit Arguments.

From Coq Require Import
  Basics
  QArith
.

Local Open Scope program_scope.

From zar Require Import
  aCPO
  cotree
  cpGCL
  cpo
  misc
  order
  eR
  tree
.

Create HintDb cotwp.

Definition cotree_loop_F {A} (e : A -> bool) (g : A -> cotree bool (unit + A))
  (f : A -> cotree bool (unit + A))
  : (A -> cotree bool (unit + A)) -> A -> cotree bool (unit + A) :=
  fun k x => if e x then
            cotree_bind (g x) (fun y => match y with
                                     | inl _ => coleaf (inl tt)
                                     | inr z => cotau (k z)
                                     end)
          else
            f x.

(** Used for building cotrees corresponding to fix nodes in CF trees. *)
Definition cotree_loop_approx {A} (x : A) (e : A -> bool)
  (g : A -> cotree bool (unit + A))
  (f : A -> cotree bool (unit + A)) (n : nat)
  : cotree bool (unit + A) :=
  iter_n (cotree_loop_F e g f) (const cobot) n x.

(* Designed to match the itree construction. *)
Definition cotree_loop {A} (e : A -> bool) (g : A -> cotree bool (unit + A))
  (f : A -> cotree bool (unit + A)) (x : A) : cotree bool (unit + A) :=
  cotree_iter (fun y => if e y then
                       cotree_bind (g y) (fun lr => match lr with
                                                 | inl _ => coleaf (inr (inl tt))
                                                 | inr z => coleaf (inl z)
                                                 end)
                     else cotree_map inr (f y)) x.

(** Old version (most proofs below are wrt this one). *)
Fixpoint to_cotree'' (t : tree) : cotree bool (unit + St) :=
  match t with
  | Leaf s => coleaf (inr s)
  | Fail => coleaf (inl tt)
  | Choice _ k => conode (to_cotree'' ∘ k)
  | Fix st G g k => sup (cotree_loop_approx st G (to_cotree'' ∘ g) (to_cotree'' ∘ k))
  end.

(** cotree_iter version (matches itree construction exactly. Would
    prefer to only use this version but the above one was defined
    first. Could probably remove it and fix the proofs fairly easily. *)
Fixpoint to_cotree_open (t : tree) : cotree bool (unit + St) :=
  match t with
  | Leaf s => coleaf (inr s)
  | Fail => coleaf (inl tt)
  | Choice _ k => conode (to_cotree_open ∘ k)
  | Fix st G g k => cotree_loop G (to_cotree_open ∘ g) (to_cotree_open ∘ k) st
  end.

Definition tie_cotree (t : cotree bool (unit + St)) : cotree bool St :=
  cotree_iter (const t) tt.

(** This can be used instead *)
Definition iid_F {A} (a : cotree bool (unit + A)) : cotree bool A -> cotree bool A :=
  fun b => cotree_bind a (fun y => match y with
                             | inl _ => cotau b
                             | inr z => coleaf z
                             end).

(** Doesn't include tau nodes. Easier to reason about when doing the
    geometric series proof, and is obviously equivalent under cotwp to
    the version (iid_F) with tau nodes.*)
Definition iid_F' {A} (a : cotree bool (unit + A)) : cotree bool A -> cotree bool A :=
  fun b => cotree_bind a (cotuple (const b) (@coleaf bool A)).

(** iter iid_F'
    a0 = cobot
    a1 = F a0 = F cobot = bind t (cotuple (const cobot) coleaf) = snip t
    a2 = F a1 = F (bind t (cotuple (const cobot) coleaf)) = F (snip t)
       = bind t (cotuple (const (snip t)) coleaf)
    a3 = F a2 = F (bind t (cotuple (const (snip t)) coleaf))
       = bind t (cotuple (bind t (cotuple (const (snip t)) coleaf)) coleaf)
 *)

Definition tie_cotree_iid (t : cotree bool (unit + St)) : cotree bool St :=
  iter (iid_F t) cobot.

Definition to_cotree : tree -> cotree bool St := tie_cotree ∘ to_cotree_open.

(** iid_chain_
    a0 = coleaf (inl tt)
    a1 = bind a0 (cotuple (const t) (coleaf ∘ inr)) = t
    a2 = bind a1 (cotuple (const t) (coleaf ∘ inr))
       = bind t (cotuple (const t) (coleaf ∘ inr))
    a3 = bind a2 (cotuple (const t) (coleaf ∘ inr))
       = bind (bind t (cotuple (const t) (coleaf ∘ inr)))
              (cotuple (const t) (coleaf ∘ inr))
 *)
Fixpoint iid_chain_ {A} (t : cotree bool (unit + A)) (n : nat) : cotree bool (unit + A) :=
  match n with
  | O => coleaf (inl tt)
  | S n' => cotree_bind (iid_chain_ t n')
             (cotuple (const t) (@coleaf bool (unit + A) ∘ inr))
  end.

(** iid_chain
    b0 = snip a0 = cobot
    b1 = snip a1 = snip t
    b2 = snip a2 = snip (bind t (cotuple (const t) (coleaf ∘ inr)))
                 = bind t (snip ∘ (cotuple (const t) (coleaf ∘ inr)))
    b3 = snip a3 = snip (bind (bind t (cotuple (const t) (coleaf ∘ inr)))
                              (cotuple (const t) (coleaf ∘ inr)))
                 = bind (bind t (cotuple (const t) (coleaf ∘ inr)))
                        (snip ∘ cotuple (const t) (coleaf ∘ inr))
                 = bind t (fun x => bind (cotuple (const t) (coleaf ∘ inr) x)
                                         (snip ∘ cotuple (const t) (coleaf ∘ inr)))

  cotree_bind' (cotree_bind' t f) g = cotree_bind' t (fun x => cotree_bind' (f x) g).
 *)

Definition iid_chain {A} (t : cotree bool (unit + A)) (n : nat) : cotree bool A :=
  snip (iid_chain_ t n).

(** wp_ on finite trees. *)
Definition btwp {A} (f : A -> eR) : atree bool A -> eR :=
  fold 0 f id (fun k => (k false + k true) / 2).

Definition btwpQ {A} (f : A -> Q) : atree bool A -> Q :=
  fold 0%Q f id (fun k => (k false + k true) / 2)%Q.

(** wp_ on cotrees. *)
Definition cotwp {A} (f : A -> eR) : cotree bool A -> eR := co (btwp f).

(** wp on cotrees. *)
Definition cowp {A} (f : A -> eR) : cotree bool (unit + A) -> eR :=
  cotwp (cotuple (const 0) f).

(** wpfail on cotrees. *)
Definition cowpfail {A} (f : A -> eR) : cotree bool (unit + A) -> eR :=
  cotwp (cotuple (const 1) f).

(** fail on cotrees. *)
Definition cofail {A} : cotree bool (unit + A) -> eR := cowpfail (const 0).

(** wlp_ on finite trees. *)
Definition btwlp {A} (f : A -> eR) : atree bool A -> eR :=
  fold 1 f id (fun k => (k false + k true) / 2).

(** wlp_ on cotrees. *)
Definition cotwlp {A} (f : A -> eR) : cotree bool A -> eR := coop (btwlp f).

(** wlp on cotrees. *)
Definition cowlp {A} (f : A -> eR) : cotree bool (unit + A) -> eR :=
  cotwlp (cotuple (const 0) f).

(** wlpfail on cotrees. *)
Definition cowlpfail {A} (f : A -> eR) : cotree bool (unit + A) -> eR :=
  cotwlp (cotuple (const 1) f).

(** fail_or_diverge on cotrees. *)
Definition cofail_or_diverge {A} : cotree bool (unit + A) -> eR := cowlpfail (const 0).

(** cwp on cotrees. *)
Definition cocwp {A} (f : A -> eR) (t : cotree bool (unit + A)) : eR :=
  cowp f t / cowlp (const 1) t.
