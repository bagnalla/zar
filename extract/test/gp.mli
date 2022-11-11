
type __ = Obj.t

val negb : bool -> bool

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> nat

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val pred : nat -> nat

val add : nat -> nat -> nat

val log2_iter : nat -> nat -> nat -> nat -> nat

val log2 : nat -> nat

val compose : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3

val const : 'a1 -> 'a2 -> 'a1

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat :
 sig
  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val pow : nat -> nat -> nat
 end

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val size_nat : positive -> nat

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val ggcdn : nat -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat
 end

module Z :
 sig
  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val sgn : z -> z

  val abs : z -> z

  val to_nat : z -> nat

  val to_pos : z -> positive

  val ggcd : z -> z -> z * (z * z)
 end

val zeq_bool : z -> z -> bool

type q = { qnum : z; qden : positive }

val qeq_bool : q -> q -> bool

val qred : q -> q

val eqb0 : char list -> char list -> bool

type 'm monad = { ret : (__ -> __ -> 'm); bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

val ret : 'a1 monad -> 'a2 -> 'a1

type ('e, 'r, 'itree) itreeF =
| RetF of 'r
| TauF of 'itree
| VisF of 'e * (__ -> 'itree)

type ('e, 'r) itree = ('e, 'r) __itree Lazy.t
and ('e, 'r) __itree =
| Go of ('e, 'r, ('e, 'r) itree) itreeF

val _observe : ('a1, 'a2) itree -> ('a1, 'a2, ('a1, 'a2) itree) itreeF

val observe : ('a1, 'a2) itree -> ('a1, 'a2, ('a1, 'a2) itree) itreeF

module ITree :
 sig
  val subst : ('a2 -> ('a1, 'a3) itree) -> ('a1, 'a2) itree -> ('a1, 'a3) itree

  val bind : ('a1, 'a2) itree -> ('a2 -> ('a1, 'a3) itree) -> ('a1, 'a3) itree

  val iter : ('a3 -> ('a1, ('a3, 'a2) sum) itree) -> 'a3 -> ('a1, 'a2) itree

  val map : ('a2 -> 'a3) -> ('a1, 'a2) itree -> ('a1, 'a3) itree
 end

val monad_itree : ('a1, __) itree monad

val _UU03f5_ : char list

val cotuple : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3

val sum_map : ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a2) sum -> ('a3, 'a4) sum

val rev_range : nat -> nat list

val drop : nat -> 'a1 list -> 'a1 list

val take : nat -> 'a1 list -> 'a1 list

type val0 =
| Vbool of bool
| Vnat of nat
| Vint of z

type st = char list -> val0

val empty : st

val upd : char list -> val0 -> st -> st

type expr = st -> val0

val is_nat : val0 -> bool

val is_int : val0 -> bool

val as_bool : val0 -> bool

val as_nat : val0 -> nat

type cpGCL =
| CSkip
| CAbort
| CAssign of char list * expr
| CSeq of cpGCL * cpGCL
| CIte of expr * cpGCL * cpGCL
| CChoice of (st -> q) * (bool -> cpGCL)
| CUniform of (st -> nat) * (nat -> cpGCL)
| CWhile of expr * cpGCL
| CObserve of expr

val const_val : val0 -> expr

type tree =
| Leaf of st
| Fail
| Choice of q * (bool -> tree)
| Fix of st * (st -> bool) * (st -> tree) * (st -> tree)

val tree_bind : tree -> (st -> tree) -> tree

val is_power_of_2b : nat -> bool

val next_pow_2 : nat -> nat

type 'a btree =
| BLeaf of 'a
| BNode of 'a btree * 'a btree

val btree_map : ('a1 -> 'a2) -> 'a1 btree -> 'a2 btree

val btree_to_tree : ('a1 -> val0) -> 'a1 btree -> tree

val bernoulli_btree_to_tree : (unit, bool) sum btree -> tree

val uniform_btree_to_tree : (unit, nat) sum btree -> tree

val list_btree_aux : 'a1 list -> nat -> (unit, 'a1) sum btree

val list_btree : 'a1 list -> (unit, 'a1) sum btree

val uniform_btree : nat -> (unit, nat) sum btree

val bernoulli_btree : nat -> nat -> (unit, bool) sum btree

val bernoulli_tree_open : nat -> nat -> tree

val bernoulli_tree : q -> tree

val uniform_tree_open : nat -> tree

val uniform_tree : nat -> tree

val compile : cpGCL -> st -> tree

val debias : tree -> tree

val elim_choices : tree -> tree

val to_itree_ : tree -> (__, (unit, st) sum) itree

val tie_itree : ('a2, (unit, 'a1) sum) itree -> ('a2, 'a1) itree

val to_itree : tree -> (__, st) itree

val cpGCL_to_itree : cpGCL -> st -> (__, st) itree

val flip : char list -> q -> cpGCL

val gp : cpGCL

val sampler : (__, bool) itree
