
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

(** val pred : nat -> nat **)

let pred n = match n with
| O -> n
| S u -> u

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val log2_iter : nat -> nat -> nat -> nat -> nat **)

let rec log2_iter k p q0 r =
  match k with
  | O -> p
  | S k' -> (match r with
             | O -> log2_iter k' (S p) (S q0) q0
             | S r' -> log2_iter k' p (S q0) r')

(** val log2 : nat -> nat **)

let log2 n =
  log2_iter (pred n) O (S O) O

(** val compose : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3 **)

let compose g f x =
  g (f x)

(** val const : 'a1 -> 'a2 -> 'a1 **)

let const a _ =
  a

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

(** val eqb_spec : bool -> bool -> reflect **)

let eqb_spec b b' =
  if b then if b' then ReflectT else ReflectF else if b' then ReflectF else ReflectT

module Nat =
 struct
  (** val add : nat -> nat -> nat **)

  let rec add n m =
    match n with
    | O -> m
    | S p -> S (add p m)

  (** val mul : nat -> nat -> nat **)

  let rec mul n m =
    match n with
    | O -> O
    | S p -> add m (mul p m)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n' -> (match m with
               | O -> false
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> true
    | S n' -> (match m with
               | O -> false
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m

  (** val pow : nat -> nat -> nat **)

  let rec pow n = function
  | O -> S O
  | S m0 -> mul n (pow n m0)

  (** val eqb_spec : nat -> nat -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)
 end

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p -> (match y with
               | XI q0 -> XI (add p q0)
               | XO q0 -> XO (add p q0)
               | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH -> (match y with
             | XI q0 -> XI (succ q0)
             | XO q0 -> XO (succ q0)
             | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val ggcdn : nat -> positive -> positive -> positive * (positive * positive) **)

  let rec ggcdn n a b =
    match n with
    | O -> (XH, (a, b))
    | S n0 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> (a, (XH, XH))
             | Lt ->
               let (g, p) = ggcdn n0 (sub b' a') a in
               let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
             | Gt ->
               let (g, p) = ggcdn n0 (sub a' b') b in
               let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
          | XO b0 -> let (g, p) = ggcdn n0 a b0 in let (aa, bb) = p in (g, (aa, (XO bb)))
          | XH -> (XH, (a, XH)))
       | XO a0 ->
         (match b with
          | XI _ -> let (g, p) = ggcdn n0 a0 b in let (aa, bb) = p in (g, ((XO aa), bb))
          | XO b0 -> let (g, p) = ggcdn n0 a0 b0 in ((XO g), p)
          | XH -> (XH, (a, XH)))
       | XH -> (XH, (XH, b)))

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)
 end

module Z =
 struct
  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' -> (match y with
                  | Zneg y' -> compOpp (Coq_Pos.compare x' y')
                  | _ -> Lt)

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> O

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val ggcd : z -> z -> z * (z * z) **)

  let ggcd a b =
    match a with
    | Z0 -> ((abs b), (Z0, (sgn b)))
    | Zpos a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zneg bb))))
 end

(** val zeq_bool : z -> z -> bool **)

let zeq_bool x y =
  match Z.compare x y with
  | Eq -> true
  | _ -> false

(** val repeat : 'a1 -> nat -> 'a1 list **)

let rec repeat x = function
| O -> []
| S k -> x :: (repeat x k)

type q = { qnum : z; qden : positive }

(** val qeq_bool : q -> q -> bool **)

let qeq_bool x y =
  zeq_bool (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qred : q -> q **)

let qred q0 =
  let { qnum = q1; qden = q2 } = q0 in
  let (r1, r2) = snd (Z.ggcd q1 (Zpos q2)) in { qnum = r1; qden = (Z.to_pos r2) }

(** val eqb0 : char list -> char list -> bool **)

let rec eqb0 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' -> (match s2 with
                | [] -> false
                | c2::s2' -> if (=) c1 c2 then eqb0 s1' s2' else false)

type 'm monad = { ret : (__ -> __ -> 'm); bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

(** val ret : 'a1 monad -> 'a2 -> 'a1 **)

let ret monad0 x =
  Obj.magic monad0.ret __ x

type ('e, 'r, 'itree) itreeF =
| RetF of 'r
| TauF of 'itree
| VisF of 'e * (__ -> 'itree)

type ('e, 'r) itree = ('e, 'r) __itree Lazy.t
and ('e, 'r) __itree =
| Go of ('e, 'r, ('e, 'r) itree) itreeF

(** val _observe : ('a1, 'a2) itree -> ('a1, 'a2, ('a1, 'a2) itree) itreeF **)

let _observe i =
  let Go _observe0 = Lazy.force i in _observe0

(** val observe : ('a1, 'a2) itree -> ('a1, 'a2, ('a1, 'a2) itree) itreeF **)

let observe =
  _observe

module ITree =
 struct
  (** val subst : ('a2 -> ('a1, 'a3) itree) -> ('a1, 'a2) itree -> ('a1, 'a3) itree **)

  let rec subst k u =
    match observe u with
    | RetF r -> k r
    | TauF t -> lazy (Go (TauF (subst k t)))
    | VisF (e, h) -> lazy (Go (VisF (e, (fun x -> subst k (h x)))))

  (** val bind : ('a1, 'a2) itree -> ('a2 -> ('a1, 'a3) itree) -> ('a1, 'a3) itree **)

  let bind u k =
    subst k u

  (** val iter : ('a3 -> ('a1, ('a3, 'a2) sum) itree) -> 'a3 -> ('a1, 'a2) itree **)

  let rec iter step i =
    bind (step i) (fun lr ->
      match lr with
      | Inl l -> lazy (Go (TauF (iter step l)))
      | Inr r -> lazy (Go (RetF r)))

  (** val map : ('a2 -> 'a3) -> ('a1, 'a2) itree -> ('a1, 'a3) itree **)

  let map f t =
    bind t (fun x -> lazy (Go (RetF (f x))))
 end

(** val monad_itree : ('a1, __) itree monad **)

let monad_itree =
  { ret = (fun _ x -> lazy (Go (RetF x))); bind = (fun _ _ -> ITree.bind) }

(** val cotuple : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3 **)

let cotuple f g = function
| Inl a -> f a
| Inr b -> g b

(** val sum_map : ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a2) sum -> ('a3, 'a4) sum **)

let sum_map f g = function
| Inl a -> Inl (f a)
| Inr b -> Inr (g b)

(** val rev_range : nat -> nat list **)

let rec rev_range = function
| O -> []
| S n' -> n' :: (rev_range n')

(** val drop : nat -> 'a1 list -> 'a1 list **)

let rec drop n l =
  match n with
  | O -> (match l with
          | [] -> []
          | _ :: _ -> l)
  | S n' -> (match l with
             | [] -> []
             | _ :: l' -> drop n' l')

(** val take : nat -> 'a1 list -> 'a1 list **)

let rec take n l =
  match n with
  | O -> []
  | S n' -> (match l with
             | [] -> []
             | x :: l' -> x :: (take n' l'))

type 'a eqType = { eqb1 : ('a -> 'a -> bool); eqb_spec0 : ('a -> 'a -> reflect) }

(** val unit_eqb_spec : unit -> unit -> reflect **)

let unit_eqb_spec _ _ =
  ReflectT

(** val eqType_unit : unit eqType **)

let eqType_unit =
  { eqb1 = (fun _ _ -> true); eqb_spec0 = unit_eqb_spec }

(** val eqType_bool : bool eqType **)

let eqType_bool =
  { eqb1 = eqb; eqb_spec0 = eqb_spec }

(** val eqType_nat : nat eqType **)

let eqType_nat =
  { eqb1 = Nat.eqb; eqb_spec0 = Nat.eqb_spec }

(** val eqType_sum_obligation_3 :
    'a1 eqType -> 'a2 eqType -> ('a1, 'a2) sum -> ('a1, 'a2) sum -> reflect **)

let eqType_sum_obligation_3 h h0 x y =
  match x with
  | Inl a -> (match y with
              | Inl a0 -> h.eqb_spec0 a a0
              | Inr _ -> ReflectF)
  | Inr b -> (match y with
              | Inl _ -> ReflectF
              | Inr b0 -> h0.eqb_spec0 b b0)

(** val eqType_sum : 'a1 eqType -> 'a2 eqType -> ('a1, 'a2) sum eqType **)

let eqType_sum h h0 =
  { eqb1 = (fun a b ->
    let filtered_var = (a, b) in
    let (s, s0) = filtered_var in
    (match s with
     | Inl x -> (match s0 with
                 | Inl y -> h.eqb1 x y
                 | Inr _ -> false)
     | Inr x -> (match s0 with
                 | Inl _ -> false
                 | Inr y -> h0.eqb1 x y))); eqb_spec0 = (fun x y ->
    eqType_sum_obligation_3 h h0 x y) }

(** val is_inl : ('a1, 'a2) sum -> bool **)

let is_inl = function
| Inl _ -> true
| Inr _ -> false

type val0 =
| Vbool of bool
| Vnat of nat
| Vint of z
| Vrat of q

type st = char list -> val0

(** val empty : st **)

let empty _ =
  Vbool false

(** val upd : char list -> val0 -> st -> st **)

let upd x v st0 y =
  if eqb0 y x then v else st0 y

type expr = st -> val0

(** val as_bool : val0 -> bool **)

let as_bool = function
| Vbool b -> b
| _ -> false

(** val as_nat : val0 -> nat **)

let as_nat = function
| Vnat n -> n
| _ -> O

type cpGCL =
| CSkip
| CAbort
| CAssign of char list * expr
| CSeq of cpGCL * cpGCL
| CIte of (st -> bool) * cpGCL * cpGCL
| CChoice of (st -> q) * (bool -> cpGCL)
| CUniform of (st -> nat) * (nat -> cpGCL)
| CWhile of (st -> bool) * cpGCL
| CObserve of (st -> bool)

(** val const_val : val0 -> expr **)

let const_val =
  const

type 'a tree =
| Leaf of 'a
| Fail
| Choice of q * (bool -> 'a tree)
| Fix of __ * (__ -> bool) * (__ -> __ tree) * (__ -> 'a tree)

(** val tree_bind : 'a1 tree -> ('a1 -> 'a2 tree) -> 'a2 tree **)

let rec tree_bind t k =
  match t with
  | Leaf x -> k x
  | Fail -> Fail
  | Choice (p, f) -> Choice (p, (fun b -> tree_bind (f b) k))
  | Fix (st0, e, g, h) -> Fix (st0, e, g, (fun s -> tree_bind (h s) k))

(** val is_power_of_2b : nat -> bool **)

let is_power_of_2b n =
  Nat.eqb n (Nat.pow (S (S O)) (log2 n))

(** val next_pow_2 : nat -> nat **)

let next_pow_2 n =
  if Nat.eqb n O then S O else if is_power_of_2b n then n else Nat.pow (S (S O)) (S (log2 n))

type 'a btree =
| BLeaf of 'a
| BNode of 'a btree * 'a btree

(** val btree_map : ('a1 -> 'a2) -> 'a1 btree -> 'a2 btree **)

let rec btree_map f = function
| BLeaf x -> BLeaf (f x)
| BNode (t1, t2) -> BNode ((btree_map f t1), (btree_map f t2))

(** val btree_to_tree : 'a1 btree -> 'a1 tree **)

let rec btree_to_tree = function
| BLeaf x -> Leaf x
| BNode (t1, t2) ->
  Choice ({ qnum = (Zpos XH); qden = (XO XH) }, (fun b ->
    if b then btree_to_tree t1 else btree_to_tree t2))

(** val list_btree_aux : 'a1 list -> nat -> (unit, 'a1) sum btree **)

let rec list_btree_aux l = function
| O -> (match l with
        | [] -> BLeaf (Inl ())
        | x :: _ -> BLeaf (Inr x))
| S n' ->
  BNode ((list_btree_aux (take (Nat.pow (S (S O)) n') l) n'),
    (list_btree_aux (drop (Nat.pow (S (S O)) n') l) n'))

(** val list_btree : 'a1 list -> (unit, 'a1) sum btree **)

let list_btree l =
  list_btree_aux l (log2 (next_pow_2 (length l)))

(** val reduce_btree : (unit, 'a1) sum btree -> (unit, 'a1) sum btree **)

let rec reduce_btree t = match t with
| BLeaf _ -> t
| BNode (l, r) ->
  let l' = reduce_btree l in
  let r' = reduce_btree r in
  (match l' with
   | BLeaf s ->
     (match s with
      | Inl _ ->
        (match r' with
         | BLeaf s0 -> (match s0 with
                        | Inl _ -> BLeaf (Inl ())
                        | Inr _ -> BNode (l', r'))
         | BNode (_, _) -> BNode (l', r'))
      | Inr _ -> BNode (l', r'))
   | BNode (_, _) -> BNode (l', r'))

(** val reduce_btree' : 'a1 eqType -> 'a1 btree -> 'a1 btree **)

let rec reduce_btree' h t = match t with
| BLeaf _ -> t
| BNode (l, r) ->
  let l' = reduce_btree' h l in
  let r' = reduce_btree' h r in
  (match l' with
   | BLeaf x ->
     (match r' with
      | BLeaf y -> if h.eqb1 x y then BLeaf x else BNode (l', r')
      | BNode (_, _) -> BNode (l', r'))
   | BNode (_, _) -> BNode (l', r'))

(** val uniform_btree : nat -> (unit, nat) sum btree **)

let uniform_btree n =
  reduce_btree (list_btree (rev_range n))

(** val bernoulli_btree : nat -> nat -> (unit, bool) sum btree **)

let bernoulli_btree n d =
  reduce_btree' (eqType_sum eqType_unit eqType_bool)
    (btree_map (sum_map (fun x -> x) (fun i -> Nat.ltb i n)) (uniform_btree d))

(** val bernoulli_tree_open : nat -> nat -> (unit, bool) sum tree **)

let bernoulli_tree_open n d =
  btree_to_tree (bernoulli_btree n d)

(** val bernoulli_tree : q -> bool tree **)

let bernoulli_tree p =
  let t = bernoulli_tree_open (Z.to_nat p.qnum) (Coq_Pos.to_nat p.qden) in
  Fix ((Obj.magic (Inl ())), (Obj.magic is_inl), (fun _ -> Obj.magic t),
  (Obj.magic cotuple (fun _ -> Leaf false) (fun x -> Leaf x)))

(** val uniform_tree_open : nat -> (unit, nat) sum tree **)

let uniform_tree_open n =
  btree_to_tree (uniform_btree n)

(** val uniform_tree : nat -> nat tree **)

let uniform_tree n =
  let t = uniform_tree_open n in
  Fix ((Obj.magic (Inl ())), (Obj.magic is_inl), (fun _ -> Obj.magic t),
  (Obj.magic cotuple (fun _ -> Leaf O) (fun x -> Leaf x)))

(** val compile : cpGCL -> st -> st tree **)

let rec compile c st0 =
  match c with
  | CSkip -> Leaf st0
  | CAbort ->
    Fix ((Obj.magic st0), (const true), (fun x -> Leaf x), (Obj.magic (fun x -> Leaf x)))
  | CAssign (x, e) -> Leaf (upd x (e st0) st0)
  | CSeq (c1, c2) -> tree_bind (compile c1 st0) (compile c2)
  | CIte (e, c1, c2) -> if e st0 then compile c1 st0 else compile c2 st0
  | CChoice (e, k) -> Choice ((e st0), (fun b -> compile (k b) st0))
  | CUniform (e, k) ->
    tree_bind (uniform_tree (as_nat (Vnat (e st0)))) (fun n -> compile (k n) st0)
  | CWhile (e, body) ->
    Fix ((Obj.magic st0), (Obj.magic e), (Obj.magic compile body), (Obj.magic (fun x -> Leaf x)))
  | CObserve e -> if e st0 then Leaf st0 else Fail

(** val debias : 'a1 tree -> 'a1 tree **)

let rec debias = function
| Choice (p, f) ->
  if qeq_bool p { qnum = (Zpos XH); qden = (XO XH) }
  then Choice (p, (compose debias f))
  else tree_bind (bernoulli_tree p) (fun b -> debias (f b))
| Fix (st0, g, g0, k) -> Fix (st0, g, (compose (Obj.magic debias) g0), (compose debias k))
| x -> x

(** val elim_choices : 'a1 tree -> 'a1 tree **)

let rec elim_choices = function
| Choice (p, k) ->
  if qeq_bool p { qnum = Z0; qden = XH }
  then elim_choices (k false)
  else if qeq_bool p { qnum = (Zpos XH); qden = XH }
       then elim_choices (k true)
       else Choice ((qred p), (compose elim_choices k))
| Fix (st0, g, g0, k) ->
  Fix (st0, g, (compose (Obj.magic elim_choices) g0), (compose elim_choices k))
| x -> x

(** val opt : 'a1 tree -> 'a1 tree **)

let rec opt t = match t with
| Choice (_, k) ->
  let l = k true in
  let r = k false in (match l with
                      | Fail -> opt r
                      | _ -> (match r with
                              | Fail -> opt l
                              | _ -> t))
| _ -> t

(** val to_itree_open : 'a1 tree -> (__, (unit, 'a1) sum) itree **)

let rec to_itree_open = function
| Leaf x -> ret (Obj.magic monad_itree) (Inr x)
| Fail -> ret (Obj.magic monad_itree) (Inl ())
| Choice (_, k) -> lazy (Go (VisF (__, (compose to_itree_open (Obj.magic k)))))
| Fix (st0, g, g0, k) ->
  ITree.iter (fun s ->
    if g s
    then ITree.bind (to_itree_open (Obj.magic g0 s)) (fun y ->
           match y with
           | Inl _ -> ret (Obj.magic monad_itree) (Inr (Inl ()))
           | Inr s' -> ret (Obj.magic monad_itree) (Inl s'))
    else ITree.map (fun x -> Inr x) (to_itree_open (k s))) st0

(** val tie_itree : ('a2, (unit, 'a1) sum) itree -> ('a2, 'a1) itree **)

let tie_itree t =
  ITree.iter (const t) ()

(** val to_itree : 'a1 tree -> (__, 'a1) itree **)

let to_itree x =
  compose tie_itree to_itree_open x

(** val cpGCL_to_itree : cpGCL -> st -> (__, st) itree **)

let cpGCL_to_itree c =
  compose (compose (compose (compose to_itree opt) debias) elim_choices) (compile c)

(** val flatten_weights_aux : nat list -> nat -> nat list **)

let rec flatten_weights_aux weights acc =
  match weights with
  | [] -> []
  | w :: ws -> app (repeat acc w) (flatten_weights_aux ws (S acc))

(** val flatten_weights : nat list -> nat list **)

let flatten_weights weights =
  flatten_weights_aux weights O

(** val findist_btree : nat list -> (unit, nat) sum btree **)

let findist_btree weights =
  reduce_btree' (eqType_sum eqType_unit eqType_nat) (list_btree (flatten_weights weights))

(** val findist_tree_open : nat list -> (unit, nat) sum tree **)

let findist_tree_open weights =
  btree_to_tree (findist_btree weights)

(** val findist_tree : nat list -> nat tree **)

let findist_tree weights =
  let t = findist_tree_open weights in
  Fix ((Obj.magic (Inl ())), (Obj.magic is_inl), (fun _ -> Obj.magic t),
  (Obj.magic cotuple (fun _ -> Leaf O) (fun x -> Leaf x)))

(** val findist_itree : nat list -> (__, nat) itree **)

let findist_itree weights =
  to_itree (findist_tree weights)

type samplers = { coin_sampler : (q -> (__, bool) itree); die_sampler : (nat -> (__, nat) itree);
                  findist_sampler : (nat list -> (__, nat) itree) }

(** val coin : char list -> q -> cpGCL **)

let coin out p =
  CChoice ((const p), (fun b -> CAssign (out, (const_val (Vbool b)))))

(** val die : char list -> nat -> cpGCL **)

let die out n =
  CUniform ((const n), (fun m -> CAssign (out, (const_val (Vnat m)))))

(** val coin_die_samplers : samplers **)

let coin_die_samplers =
  { coin_sampler = (fun p ->
    ITree.map (fun s -> as_bool (s ('b'::[]))) (cpGCL_to_itree (coin ('b'::[]) p) empty));
    die_sampler = (fun n ->
    ITree.map (fun s -> as_nat (s ('n'::[]))) (cpGCL_to_itree (die ('n'::[]) n) empty));
    findist_sampler = findist_itree }
