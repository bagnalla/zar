
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

(** val pred : nat -> nat **)

let pred n = match n with
| O -> n
| S u -> u

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

type q = { qnum : z; qden : positive }

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

(** val _UU03f5_ : char list **)

let _UU03f5_ =
  []

(** val cotuple : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3 **)

let cotuple f g = function
| Inl a -> f a
| Inr b -> g b

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

type val0 =
| Vbool of bool
| Vnat of nat
| Vint of z

type st = char list -> val0

(** val empty : st **)

let empty _ =
  Vbool false

(** val upd : char list -> val0 -> st -> st **)

let upd x v st0 y =
  if eqb0 y x then v else st0 y

(** val is_nat : val0 -> bool **)

let is_nat = function
| Vnat _ -> true
| _ -> false

(** val as_nat : val0 -> nat **)

let as_nat = function
| Vnat n -> n
| _ -> O

type tree =
| Leaf of st
| Fail
| Choice of q * (bool -> tree)
| Fix of st * (st -> bool) * (st -> tree) * (st -> tree)

(** val is_power_of_2b : nat -> bool **)

let is_power_of_2b n =
  Nat.eqb n (Nat.pow (S (S O)) (log2 n))

(** val next_pow_2 : nat -> nat **)

let next_pow_2 n =
  if Nat.eqb n O then S O else if is_power_of_2b n then n else Nat.pow (S (S O)) (S (log2 n))

type 'a btree =
| BLeaf of 'a
| BNode of 'a btree * 'a btree

(** val btree_to_tree : ('a1 -> val0) -> 'a1 btree -> tree **)

let rec btree_to_tree f = function
| BLeaf x -> Leaf (upd _UU03f5_ (f x) empty)
| BNode (t1, t2) ->
  Choice ({ qnum = (Zpos XH); qden = (XO XH) }, (fun b ->
    if b then btree_to_tree f t1 else btree_to_tree f t2))

(** val uniform_btree_to_tree : (unit, nat) sum btree -> tree **)

let uniform_btree_to_tree =
  btree_to_tree (cotuple (const (Vint Z0)) (fun x -> Vnat x))

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

(** val uniform_btree : nat -> (unit, nat) sum btree **)

let uniform_btree n =
  reduce_btree (list_btree (rev_range n))

(** val uniform_tree_open : nat -> tree **)

let uniform_tree_open n =
  uniform_btree_to_tree (uniform_btree n)

(** val uniform_tree : nat -> tree **)

let uniform_tree n =
  let t = uniform_tree_open n in
  Fix ((upd _UU03f5_ (Vint Z0) empty), (fun s -> negb (is_nat (s _UU03f5_))), (fun _ -> t),
  (fun x -> Leaf x))

(** val to_itree_open : tree -> (__, (unit, st) sum) itree **)

let rec to_itree_open = function
| Leaf x -> ret (Obj.magic monad_itree) (Inr x)
| Fail -> ret (Obj.magic monad_itree) (Inl ())
| Choice (_, k) -> lazy (Go (VisF (__, (compose to_itree_open (Obj.magic k)))))
| Fix (st0, g, g0, k) ->
  ITree.iter (fun s ->
    if g s
    then ITree.bind (to_itree_open (g0 s)) (fun y ->
           match y with
           | Inl _ -> ret (Obj.magic monad_itree) (Inr (Inl ()))
           | Inr s' -> ret (Obj.magic monad_itree) (Inl s'))
    else ITree.map (fun x -> Inr x) (to_itree_open (k s))) st0

(** val tie_itree : ('a2, (unit, 'a1) sum) itree -> ('a2, 'a1) itree **)

let tie_itree t =
  ITree.iter (const t) ()

(** val to_itree : tree -> (__, st) itree **)

let to_itree =
  compose tie_itree to_itree_open

(** val sampler : nat -> (__, nat) itree **)

let sampler n =
  ITree.map (fun s -> as_nat (s _UU03f5_)) (to_itree (uniform_tree n))
