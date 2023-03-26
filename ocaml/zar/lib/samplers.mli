
type __ = Obj.t

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

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

val eqb : bool -> bool -> bool

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

val eqb_spec : bool -> bool -> reflect

module Nat :
 sig
  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val eqb : nat -> nat -> bool

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

  val eqb : positive -> positive -> bool

  val ggcdn : nat -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val succ : z -> z

  val compare : z -> z -> comparison

  val sgn : z -> z

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val abs : z -> z

  val to_nat : z -> nat

  val to_pos : z -> positive

  val ggcd : z -> z -> z * (z * z)

  val eqb_spec : z -> z -> reflect
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val repeat : 'a1 -> nat -> 'a1 list

type q = { qnum : z; qden : positive }

val qred : q -> q

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

val cotuple : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3

val sum_map : ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a2) sum -> ('a3, 'a4) sum

val drop : nat -> 'a1 list -> 'a1 list

val take : nat -> 'a1 list -> 'a1 list

type 'a eqType = { eqb0 : ('a -> 'a -> bool); eqb_spec0 : ('a -> 'a -> reflect) }

val unit_eqb_spec : unit -> unit -> reflect

val eqType_unit : unit eqType

val eqType_bool : bool eqType

val eqType_Z : z eqType

val eqType_sum_obligation_3 :
  'a1 eqType -> 'a2 eqType -> ('a1, 'a2) sum -> ('a1, 'a2) sum -> reflect

val eqType_sum : 'a1 eqType -> 'a2 eqType -> ('a1, 'a2) sum eqType

val is_inl : ('a1, 'a2) sum -> bool

type 'a tree =
| Leaf of 'a
| Fail
| Choice of q * (bool -> 'a tree)
| Fix of __ * (__ -> bool) * (__ -> __ tree) * (__ -> 'a tree)

val is_power_of_2b : nat -> bool

val next_pow_2 : nat -> nat

val to_itree_open : 'a1 tree -> (__, (unit, 'a1) sum) itree

val tie_itree : ('a2, (unit, 'a1) sum) itree -> ('a2, 'a1) itree

val to_itree : 'a1 tree -> (__, 'a1) itree

type 'a btree =
| BLeaf of 'a
| BNode of 'a btree * 'a btree

val btree_map : ('a1 -> 'a2) -> 'a1 btree -> 'a2 btree

val btree_to_tree : 'a1 btree -> 'a1 tree

val list_btree_aux : 'a1 list -> nat -> (unit, 'a1) sum btree

val list_btree : 'a1 list -> (unit, 'a1) sum btree

val reduce_btree : (unit, 'a1) sum btree -> (unit, 'a1) sum btree

val reduce_btree' : 'a1 eqType -> 'a1 btree -> 'a1 btree

val rev_range_positive : positive -> z list

val rev_range_Z : z -> z list

val uniform_btree : z -> (unit, z) sum btree

val bernoulli_btree : z -> z -> (unit, bool) sum btree

val bernoulli_tree_open : z -> z -> (unit, bool) sum tree

val bernoulli_tree : q -> bool tree

val uniform_tree_open : z -> (unit, z) sum tree

val uniform_tree : z -> z tree

val flatten_weights_aux : z list -> z -> z list

val flatten_weights : z list -> z list

val findist_btree : z list -> (unit, z) sum btree

val findist_tree_open : z list -> (unit, z) sum tree

val findist_tree : z list -> z tree

val findist_itree : z list -> (__, z) itree

type samplers = { coin_sampler : (q -> (__, bool) itree); die_sampler : (z -> (__, z) itree);
                  findist_sampler : (z list -> (__, z) itree) }

val coin_itree : q -> (__, bool) itree

val die_itree : z -> (__, z) itree

val coin_die_samplers : samplers
