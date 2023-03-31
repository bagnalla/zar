
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
 (** val add : nat -> nat -> nat **)
 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val log2_iter : nat -> nat -> nat -> nat -> nat **)

let rec log2_iter k p q0 r =
  match k with
  | O -> p
  | S k' ->
    (match r with
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
  if b
  then if b' then ReflectT else ReflectF
  else if b' then ReflectF else ReflectT

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

  (** val pow : nat -> nat -> nat **)

  let rec pow n = function
  | O -> S O
  | S m0 -> mul n (pow n m0)
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
    | XO p ->
      (match y with
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
    | XH ->
      (match y with
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

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q0 =
    match p with
    | XI p0 -> (match q0 with
                | XI q1 -> eqb p0 q1
                | _ -> false)
    | XO p0 -> (match q0 with
                | XO q1 -> eqb p0 q1
                | _ -> false)
    | XH -> (match q0 with
             | XH -> true
             | _ -> false)

  (** val ggcdn :
      nat -> positive -> positive -> positive * (positive * positive) **)

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
          | XO b0 ->
            let (g, p) = ggcdn n0 a b0 in
            let (aa, bb) = p in (g, (aa, (XO bb)))
          | XH -> (XH, (a, XH)))
       | XO a0 ->
         (match b with
          | XI _ ->
            let (g, p) = ggcdn n0 a0 b in
            let (aa, bb) = p in (g, ((XO aa), bb))
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
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Coq_Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val succ : z -> z **)

  let succ x =
    add x (Zpos XH)

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
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q0 -> Coq_Pos.eqb p q0
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q0 -> Coq_Pos.eqb p q0
                 | _ -> false)

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
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zneg bb))))

  (** val eqb_spec : z -> z -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val repeat : 'a1 -> nat -> 'a1 list **)

let rec repeat x = function
| O -> []
| S k -> x :: (repeat x k)

type q = { qnum : z; qden : positive }

(** val qred : q -> q **)

let qred q0 =
  let { qnum = q1; qden = q2 } = q0 in
  let (r1, r2) = snd (Z.ggcd q1 (Zpos q2)) in
  { qnum = r1; qden = (Z.to_pos r2) }

type 'm monad = { ret : (__ -> __ -> 'm);
                  bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

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
  (** val subst :
      ('a2 -> ('a1, 'a3) itree) -> ('a1, 'a2) itree -> ('a1, 'a3) itree **)

  let rec subst k u =
    match observe u with
    | RetF r -> k r
    | TauF t -> lazy (Go (TauF (subst k t)))
    | VisF (e, h) -> lazy (Go (VisF (e, (fun x -> subst k (h x)))))

  (** val bind :
      ('a1, 'a2) itree -> ('a2 -> ('a1, 'a3) itree) -> ('a1, 'a3) itree **)

  let bind u k =
    subst k u

  (** val iter :
      ('a3 -> ('a1, ('a3, 'a2) sum) itree) -> 'a3 -> ('a1, 'a2) itree **)

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

(** val sum_map :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a2) sum -> ('a3, 'a4) sum **)

let sum_map f g = function
| Inl a -> Inl (f a)
| Inr b -> Inr (g b)

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

type 'a eqType = { eqb0 : ('a -> 'a -> bool);
                   eqb_spec0 : ('a -> 'a -> reflect) }

(** val unit_eqb_spec : unit -> unit -> reflect **)

let unit_eqb_spec _ _ =
  ReflectT

(** val eqType_unit : unit eqType **)

let eqType_unit =
  { eqb0 = (fun _ _ -> true); eqb_spec0 = unit_eqb_spec }

(** val eqType_bool : bool eqType **)

let eqType_bool =
  { eqb0 = eqb; eqb_spec0 = eqb_spec }

(** val eqType_Z : z eqType **)

let eqType_Z =
  { eqb0 = Z.eqb; eqb_spec0 = Z.eqb_spec }

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
  { eqb0 = (fun a b ->
    let filtered_var = (a, b) in
    let (s, s0) = filtered_var in
    (match s with
     | Inl x -> (match s0 with
                 | Inl y -> h.eqb0 x y
                 | Inr _ -> false)
     | Inr x -> (match s0 with
                 | Inl _ -> false
                 | Inr y -> h0.eqb0 x y))); eqb_spec0 = (fun x y ->
    eqType_sum_obligation_3 h h0 x y) }

(** val is_inl : ('a1, 'a2) sum -> bool **)

let is_inl = function
| Inl _ -> true
| Inr _ -> false

type 'a tree =
| Leaf of 'a
| Fail
| Choice of q * (bool -> 'a tree)
| Fix of __ * (__ -> bool) * (__ -> __ tree) * (__ -> 'a tree)

(** val is_power_of_2b : nat -> bool **)

let is_power_of_2b n =
  Nat.eqb n (Nat.pow (S (S O)) (log2 n))

(** val next_pow_2 : nat -> nat **)

let next_pow_2 n =
  if Nat.eqb n O
  then S O
  else if is_power_of_2b n then n else Nat.pow (S (S O)) (S (log2 n))

(** val to_itree_open : 'a1 tree -> (__, (unit, 'a1) sum) itree **)

let rec to_itree_open = function
| Leaf x -> ret (Obj.magic monad_itree) (Inr x)
| Fail -> ret (Obj.magic monad_itree) (Inl ())
| Choice (_, k) ->
  lazy (Go (VisF (__, (compose to_itree_open (Obj.magic k)))))
| Fix (st, g, g0, k) ->
  ITree.iter (fun s ->
    if g s
    then ITree.bind (to_itree_open (Obj.magic g0 s)) (fun y ->
           match y with
           | Inl _ -> ret (Obj.magic monad_itree) (Inr (Inl ()))
           | Inr s' -> ret (Obj.magic monad_itree) (Inl s'))
    else ITree.map (fun x -> Inr x) (to_itree_open (k s))) st

(** val tie_itree : ('a2, (unit, 'a1) sum) itree -> ('a2, 'a1) itree **)

let tie_itree t =
  ITree.iter (const t) ()

(** val to_itree : 'a1 tree -> (__, 'a1) itree **)

let to_itree x =
  compose tie_itree to_itree_open x

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
         | BLeaf s0 ->
           (match s0 with
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
      | BLeaf y -> if h.eqb0 x y then BLeaf x else BNode (l', r')
      | BNode (_, _) -> BNode (l', r'))
   | BNode (_, _) -> BNode (l', r'))

(** val rev_range_positive : positive -> z list **)

let rec rev_range_positive = function
| XI p' ->
  (Zpos
    (Coq_Pos.mul (XO XH) p')) :: (app
                                   (map (Z.add (Zpos p'))
                                     (rev_range_positive p'))
                                   (rev_range_positive p'))
| XO p' ->
  app (map (Z.add (Zpos p')) (rev_range_positive p')) (rev_range_positive p')
| XH -> Z0 :: []

(** val rev_range_Z : z -> z list **)

let rev_range_Z = function
| Zpos p -> rev_range_positive p
| _ -> []

(** val uniform_btree : z -> (unit, z) sum btree **)

let uniform_btree n =
  reduce_btree (list_btree (rev_range_Z n))

(** val bernoulli_btree : z -> z -> (unit, bool) sum btree **)

let bernoulli_btree n d =
  reduce_btree' (eqType_sum eqType_unit eqType_bool)
    (btree_map (sum_map (fun x -> x) (fun i -> Z.ltb i n)) (uniform_btree d))

(** val bernoulli_tree_open : z -> z -> (unit, bool) sum tree **)

let bernoulli_tree_open n d =
  btree_to_tree (bernoulli_btree n d)

(** val bernoulli_tree : q -> bool tree **)

let bernoulli_tree p =
  let t = bernoulli_tree_open p.qnum (Zpos p.qden) in
  Fix ((Obj.magic (Inl ())), (Obj.magic is_inl), (fun _ -> Obj.magic t),
  (Obj.magic cotuple (fun _ -> Leaf false) (fun x -> Leaf x)))

(** val uniform_tree_open : z -> (unit, z) sum tree **)

let uniform_tree_open n =
  btree_to_tree (uniform_btree n)

(** val uniform_tree : z -> z tree **)

let uniform_tree n =
  let t = uniform_tree_open n in
  Fix ((Obj.magic (Inl ())), (Obj.magic is_inl), (fun _ -> Obj.magic t),
  (Obj.magic cotuple (fun _ -> Leaf Z0) (fun x -> Leaf x)))

(** val flatten_weights_aux : z list -> z -> z list **)

let rec flatten_weights_aux weights acc =
  match weights with
  | [] -> []
  | w :: ws ->
    app (repeat acc (Z.to_nat w)) (flatten_weights_aux ws (Z.succ acc))

(** val flatten_weights : z list -> z list **)

let flatten_weights weights =
  flatten_weights_aux weights Z0

(** val findist_btree : z list -> (unit, z) sum btree **)

let findist_btree weights =
  reduce_btree' (eqType_sum eqType_unit eqType_Z)
    (list_btree (flatten_weights weights))

(** val findist_tree_open : z list -> (unit, z) sum tree **)

let findist_tree_open weights =
  btree_to_tree (findist_btree weights)

(** val findist_tree : z list -> z tree **)

let findist_tree weights =
  let t = findist_tree_open weights in
  Fix ((Obj.magic (Inl ())), (Obj.magic is_inl), (fun _ -> Obj.magic t),
  (Obj.magic cotuple (fun _ -> Leaf Z0) (fun x -> Leaf x)))

(** val findist_itree : z list -> (__, z) itree **)

let findist_itree weights =
  to_itree (findist_tree weights)

type samplerPackage = { coin_sampler : (q -> (__, bool) itree);
                        die_sampler : (z -> (__, z) itree);
                        findist_sampler : (z list -> (__, z) itree) }

(** val coin_itree : q -> (__, bool) itree **)

let coin_itree p =
  to_itree (bernoulli_tree (qred p))

(** val die_itree : z -> (__, z) itree **)

let die_itree n =
  to_itree (uniform_tree n)

(** val samplers : samplerPackage **)

let samplers =
  { coin_sampler = coin_itree; die_sampler = die_itree; findist_sampler =
    findist_itree }
