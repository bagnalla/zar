
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

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

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

  (** val even : nat -> bool **)

  let rec even = function
  | O -> true
  | S n0 -> (match n0 with
             | O -> false
             | S n' -> even n')

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

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
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

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

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

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> O

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Coq_Pos.of_succ_nat n0)

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q0), r')
      else ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q0), r')
      else ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let (q0, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q0), Z0)
          | _ -> ((opp (add q0 (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ ->
         let (q0, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q0), Z0)
          | _ -> ((opp (add q0 (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q0, r) = pos_div_eucl a' (Zpos b') in (q0, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let (q0, _) = div_eucl a b in q0

  (** val even : z -> bool **)

  let even = function
  | Z0 -> true
  | Zpos p -> (match p with
               | XO _ -> true
               | _ -> false)
  | Zneg p -> (match p with
               | XO _ -> true
               | _ -> false)

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

type q = { qnum : z; qden : positive }

(** val qeq_bool : q -> q -> bool **)

let qeq_bool x y =
  zeq_bool (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qle_bool : q -> q -> bool **)

let qle_bool x y =
  Z.leb (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))); qden =
    (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qinv : q -> q **)

let qinv x =
  match x.qnum with
  | Z0 -> { qnum = Z0; qden = XH }
  | Zpos p -> { qnum = (Zpos x.qden); qden = p }
  | Zneg p -> { qnum = (Zneg x.qden); qden = p }

(** val qdiv : q -> q -> q **)

let qdiv x y =
  qmult x (qinv y)

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

(** val qfloor : q -> z **)

let qfloor x =
  let { qnum = n; qden = d } = x in Z.div n (Zpos d)

(** val _UU03f5_ : char list **)

let _UU03f5_ =
  []

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

type expr = st -> val0

(** val is_nat : val0 -> bool **)

let is_nat = function
| Vnat _ -> true
| _ -> false

(** val is_int : val0 -> bool **)

let is_int = function
| Vint _ -> true
| _ -> false

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

type tree =
| Leaf of st
| Fail
| Choice of q * (bool -> tree)
| Fix of st * (st -> bool) * (st -> tree) * (st -> tree)

(** val tree_bind : tree -> (st -> tree) -> tree **)

let rec tree_bind t k =
  match t with
  | Leaf x -> k x
  | Fail -> Fail
  | Choice (p, f) -> Choice (p, (fun b -> tree_bind (f b) k))
  | Fix (st0, e, g, h) -> Fix (st0, e, g, (fun s -> tree_bind (h s) k))

(** val n2Q : nat -> q **)

let n2Q n =
  { qnum = (Z.of_nat n); qden = XH }

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

(** val btree_to_tree : ('a1 -> val0) -> 'a1 btree -> tree **)

let rec btree_to_tree f = function
| BLeaf x -> Leaf (upd _UU03f5_ (f x) empty)
| BNode (t1, t2) ->
  Choice ({ qnum = (Zpos XH); qden = (XO XH) }, (fun b ->
    if b then btree_to_tree f t1 else btree_to_tree f t2))

(** val bernoulli_btree_to_tree : (unit, bool) sum btree -> tree **)

let bernoulli_btree_to_tree =
  btree_to_tree (cotuple (const (Vint Z0)) (fun x -> Vbool x))

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

(** val bernoulli_btree : nat -> nat -> (unit, bool) sum btree **)

let bernoulli_btree n d =
  btree_map (sum_map (fun x -> x) (fun i -> Nat.ltb i n)) (uniform_btree d)

(** val bernoulli_tree_open : nat -> nat -> tree **)

let bernoulli_tree_open n d =
  bernoulli_btree_to_tree (bernoulli_btree n d)

(** val bernoulli_tree : q -> tree **)

let bernoulli_tree p =
  Fix ((upd _UU03f5_ (Vint Z0) empty), (fun s -> is_int (s _UU03f5_)), (fun _ ->
    bernoulli_tree_open (Z.to_nat p.qnum) (Coq_Pos.to_nat p.qden)), (fun x -> Leaf x))

(** val uniform_tree_open : nat -> tree **)

let uniform_tree_open n =
  uniform_btree_to_tree (uniform_btree n)

(** val uniform_tree : nat -> tree **)

let uniform_tree n =
  let t = uniform_tree_open n in
  Fix ((upd _UU03f5_ (Vint Z0) empty), (fun s -> negb (is_nat (s _UU03f5_))), (fun _ -> t),
  (fun x -> Leaf x))

(** val compile : cpGCL -> st -> tree **)

let rec compile c st0 =
  match c with
  | CSkip -> Leaf st0
  | CAbort -> Fix (st0, (const true), (fun x -> Leaf x), (fun x -> Leaf x))
  | CAssign (x, e) -> Leaf (upd x (e st0) st0)
  | CSeq (c1, c2) -> tree_bind (compile c1 st0) (compile c2)
  | CIte (e, c1, c2) -> if e st0 then compile c1 st0 else compile c2 st0
  | CChoice (e, k) -> Choice ((e st0), (fun b -> compile (k b) st0))
  | CUniform (e, k) ->
    tree_bind (uniform_tree (as_nat (Vnat (e st0)))) (fun s ->
      compile (k (as_nat (s _UU03f5_))) st0)
  | CWhile (e, body) -> Fix (st0, e, (compile body), (fun x -> Leaf x))
  | CObserve e -> if e st0 then Leaf st0 else Fail

(** val debias : tree -> tree **)

let rec debias = function
| Choice (p, f) -> tree_bind (bernoulli_tree p) (fun s -> debias (f (as_bool (s _UU03f5_))))
| Fix (st0, g, g0, k) -> Fix (st0, g, (compose debias g0), (compose debias k))
| x -> x

(** val elim_choices : tree -> tree **)

let rec elim_choices = function
| Choice (p, k) ->
  if qeq_bool p { qnum = Z0; qden = XH }
  then elim_choices (k false)
  else if qeq_bool p { qnum = (Zpos XH); qden = XH }
       then elim_choices (k true)
       else Choice ((qred p), (compose elim_choices k))
| Fix (st0, g, g0, k) -> Fix (st0, g, (compose elim_choices g0), (compose elim_choices k))
| x -> x

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

(** val cpGCL_to_itree : cpGCL -> st -> (__, st) itree **)

let cpGCL_to_itree c =
  compose (compose (compose to_itree debias) elim_choices) (compile c)

(** val succ0 : val0 -> val0 **)

let succ0 v = match v with
| Vbool _ -> v
| Vnat n -> Vnat (S n)
| Vint n -> Vint (Z.add n (Zpos XH))

(** val is_even : val0 -> bool **)

let is_even = function
| Vbool _ -> false
| Vnat n -> Nat.even n
| Vint n -> Z.even n

(** val bernoulli_exponential_0_1 : char list -> (st -> q) -> cpGCL **)

let bernoulli_exponential_0_1 out gamma =
  CSeq ((CAssign (('k'::[]), (const_val (Vnat O)))), (CSeq ((CAssign (('a'::[]),
    (const_val (Vbool true)))), (CSeq ((CWhile ((fun s -> as_bool (s ('a'::[]))), (CChoice
    ((fun s -> qdiv (gamma s) (n2Q (S (as_nat (s ('k'::[])))))), (fun b ->
    if b
    then CAssign (('k'::[]), (fun s -> succ0 (s ('k'::[]))))
    else CAssign (('a'::[]), (const_val (Vbool false)))))))), (CIte ((fun s ->
    is_even (s ('k'::[]))), (CAssign (out, (const_val (Vbool true)))), (CAssign (out,
    (const_val (Vbool false)))))))))))

(** val bernoulli_exponential : char list -> (st -> q) -> cpGCL **)

let bernoulli_exponential out gamma =
  CIte ((fun s -> qle_bool (gamma s) { qnum = (Zpos XH); qden = XH }),
    (bernoulli_exponential_0_1 out (fun s ->
      if qle_bool (gamma s) { qnum = (Zpos XH); qden = XH }
      then gamma s
      else { qnum = (Zpos XH); qden = XH })), (CSeq ((CAssign (('i'::[]),
    (const_val (Vnat (S O))))), (CSeq ((CAssign (('b'::[]), (const_val (Vbool true)))), (CSeq
    ((CWhile ((fun s ->
    (&&) (as_bool (s ('b'::[]))) (qle_bool (n2Q (as_nat (s ('i'::[])))) (gamma s))), (CSeq
    ((bernoulli_exponential_0_1 ('b'::[]) (const { qnum = (Zpos XH); qden = XH })), (CAssign
    (('i'::[]), (fun s -> succ0 (s ('i'::[]))))))))), (CIte ((fun s -> as_bool (s ('b'::[]))),
    (bernoulli_exponential_0_1 out (fun s ->
      qminus (gamma s) { qnum = (qfloor (gamma s)); qden = XH })), (CAssign (out,
    (const_val (Vnat O)))))))))))))

(** val sampler : q -> (__, bool) itree **)

let sampler gamma =
  ITree.map (fun s -> as_bool (s []))
    (cpGCL_to_itree (bernoulli_exponential [] (const gamma)) empty)
