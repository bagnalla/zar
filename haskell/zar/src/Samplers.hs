{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Samplers where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
#if __GLASGOW_HASKELL__ >= 900
unsafeCoerce = GHC.Exts.unsafeCoerce#
#else
unsafeCoerce = GHC.Base.unsafeCoerce#
#endif
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec =
  and_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

data Nat =
   O
 | S Nat

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

length :: (([]) a1) -> Nat
length l =
  case l of {
   ([]) -> O;
   (:) _ l' -> S (length l')}

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

pred :: Nat -> Nat
pred n =
  case n of {
   O -> n;
   S u -> u}

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

log2_iter :: Nat -> Nat -> Nat -> Nat -> Nat
log2_iter k p q r =
  case k of {
   O -> p;
   S k' ->
    case r of {
     O -> log2_iter k' (S p) (S q) q;
     S r' -> log2_iter k' p (S q) r'}}

log2 :: Nat -> Nat
log2 n =
  log2_iter (pred n) O (S O) O

compose :: (a2 -> a3) -> (a1 -> a2) -> a1 -> a3
compose g f x =
  g (f x)

const :: a1 -> a2 -> a1
const a _ =
  a

data Positive =
   XI Positive
 | XO Positive
 | XH

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

eqb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
eqb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False ->
    case b2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

data Reflect =
   ReflectT
 | ReflectF

iff_reflect :: Prelude.Bool -> Reflect
iff_reflect b =
  case b of {
   Prelude.True -> and_rec (\_ _ -> ReflectT);
   Prelude.False -> and_rec (\_ _ -> ReflectF)}

eqb_spec :: Prelude.Bool -> Prelude.Bool -> Reflect
eqb_spec b b' =
  case b of {
   Prelude.True ->
    case b' of {
     Prelude.True -> ReflectT;
     Prelude.False -> ReflectF};
   Prelude.False ->
    case b' of {
     Prelude.True -> ReflectF;
     Prelude.False -> ReflectT}}

add0 :: Nat -> Nat -> Nat
add0 n m =
  case n of {
   O -> m;
   S p -> S (add0 p m)}

mul :: Nat -> Nat -> Nat
mul n m =
  case n of {
   O -> O;
   S p -> add0 m (mul p m)}

eqb0 :: Nat -> Nat -> Prelude.Bool
eqb0 n m =
  case n of {
   O -> case m of {
         O -> Prelude.True;
         S _ -> Prelude.False};
   S n' -> case m of {
            O -> Prelude.False;
            S m' -> eqb0 n' m'}}

pow :: Nat -> Nat -> Nat
pow n m =
  case m of {
   O -> S O;
   S m0 -> mul n (pow n m0)}

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add1 :: Positive -> Positive -> Positive
add1 x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add1 p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add1 p q);
     XO q -> XO (add1 p q);
     XH -> XI p};
   XH -> case y of {
          XI q -> XO (succ q);
          XO q -> XI q;
          XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add1 p q);
     XH -> XO (succ p)};
   XH -> case y of {
          XI q -> XI (succ q);
          XO q -> XO (succ q);
          XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

data Mask =
   IsNul
 | IsPos Positive
 | IsNeg

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos XH;
   IsPos p -> IsPos (XI p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos (XO p);
   x0 -> x0}

double_pred_mask :: Positive -> Mask
double_pred_mask x =
  case x of {
   XI p -> IsPos (XO (XO p));
   XO p -> IsPos (XO (pred_double p));
   XH -> IsNul}

sub_mask :: Positive -> Positive -> Mask
sub_mask x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double_mask (sub_mask p q);
     XO q -> succ_double_mask (sub_mask p q);
     XH -> IsPos (XO p)};
   XO p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XH -> case y of {
          XH -> IsNul;
          _ -> IsNeg}}

sub_mask_carry :: Positive -> Positive -> Mask
sub_mask_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XO p ->
    case y of {
     XI q -> double_mask (sub_mask_carry p q);
     XO q -> succ_double_mask (sub_mask_carry p q);
     XH -> double_pred_mask p};
   XH -> IsNeg}

sub :: Positive -> Positive -> Positive
sub x y =
  case sub_mask x y of {
   IsPos z -> z;
   _ -> XH}

mul0 :: Positive -> Positive -> Positive
mul0 x y =
  case x of {
   XI p -> add1 y (XO (mul0 p y));
   XO p -> XO (mul0 p y);
   XH -> y}

size_nat :: Positive -> Nat
size_nat p =
  case p of {
   XI p0 -> S (size_nat p0);
   XO p0 -> S (size_nat p0);
   XH -> S O}

compare_cont :: Comparison -> Positive -> Positive -> Comparison
compare_cont r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont r p q;
     XO q -> compare_cont Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont Lt p q;
     XO q -> compare_cont r p q;
     XH -> Gt};
   XH -> case y of {
          XH -> r;
          _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare =
  compare_cont Eq

eqb1 :: Positive -> Positive -> Prelude.Bool
eqb1 p q =
  case p of {
   XI p0 -> case q of {
             XI q0 -> eqb1 p0 q0;
             _ -> Prelude.False};
   XO p0 -> case q of {
             XO q0 -> eqb1 p0 q0;
             _ -> Prelude.False};
   XH -> case q of {
          XH -> Prelude.True;
          _ -> Prelude.False}}

ggcdn :: Nat -> Positive -> Positive -> (,) Positive ((,) Positive Positive)
ggcdn n a b =
  case n of {
   O -> (,) XH ((,) a b);
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> (,) a ((,) XH XH);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           (,) g p ->
            case p of {
             (,) ba aa -> (,) g ((,) aa (add1 aa (XO ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           (,) g p ->
            case p of {
             (,) ab bb -> (,) g ((,) (add1 bb (XO ab)) bb)}}};
       XO b0 ->
        case ggcdn n0 a b0 of {
         (,) g p -> case p of {
                     (,) aa bb -> (,) g ((,) aa (XO bb))}};
       XH -> (,) XH ((,) a XH)};
     XO a0 ->
      case b of {
       XI _ ->
        case ggcdn n0 a0 b of {
         (,) g p -> case p of {
                     (,) aa bb -> (,) g ((,) (XO aa) bb)}};
       XO b0 -> case ggcdn n0 a0 b0 of {
                 (,) g p -> (,) (XO g) p};
       XH -> (,) XH ((,) a XH)};
     XH -> (,) XH ((,) XH b)}}

ggcd :: Positive -> Positive -> (,) Positive ((,) Positive Positive)
ggcd a b =
  ggcdn (add (size_nat a) (size_nat b)) a b

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op p a =
  case p of {
   XI p0 -> op a (iter_op op p0 (op a a));
   XO p0 -> iter_op op p0 (op a a);
   XH -> a}

to_nat :: Positive -> Nat
to_nat x =
  iter_op add x (S O)

double :: Z -> Z
double x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double :: Z -> Z
succ_double x =
  case x of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x =
  case x of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double (pos_sub p q);
     XO q -> succ_double (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add2 :: Z -> Z -> Z
add2 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add1 x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add1 x' y')}}

succ0 :: Z -> Z
succ0 x =
  add2 x (Zpos XH)

compare0 :: Z -> Z -> Comparison
compare0 x y =
  case x of {
   Z0 -> case y of {
          Z0 -> Eq;
          Zpos _ -> Lt;
          Zneg _ -> Gt};
   Zpos x' -> case y of {
               Zpos y' -> compare x' y';
               _ -> Gt};
   Zneg x' -> case y of {
               Zneg y' -> compOpp (compare x' y');
               _ -> Lt}}

sgn :: Z -> Z
sgn z =
  case z of {
   Z0 -> Z0;
   Zpos _ -> Zpos XH;
   Zneg _ -> Zneg XH}

ltb :: Z -> Z -> Prelude.Bool
ltb x y =
  case compare0 x y of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

eqb2 :: Z -> Z -> Prelude.Bool
eqb2 x y =
  case x of {
   Z0 -> case y of {
          Z0 -> Prelude.True;
          _ -> Prelude.False};
   Zpos p -> case y of {
              Zpos q -> eqb1 p q;
              _ -> Prelude.False};
   Zneg p -> case y of {
              Zneg q -> eqb1 p q;
              _ -> Prelude.False}}

abs :: Z -> Z
abs z =
  case z of {
   Zneg p -> Zpos p;
   x -> x}

to_nat0 :: Z -> Nat
to_nat0 z =
  case z of {
   Zpos p -> to_nat p;
   _ -> O}

to_pos :: Z -> Positive
to_pos z =
  case z of {
   Zpos p -> p;
   _ -> XH}

ggcd0 :: Z -> Z -> (,) Z ((,) Z Z)
ggcd0 a b =
  case a of {
   Z0 -> (,) (abs b) ((,) Z0 (sgn b));
   Zpos a0 ->
    case b of {
     Z0 -> (,) (abs a) ((,) (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) (Zpos g) ((,) (Zpos aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) (Zpos g) ((,) (Zpos aa) (Zneg bb))}}};
   Zneg a0 ->
    case b of {
     Z0 -> (,) (abs a) ((,) (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) (Zpos g) ((,) (Zneg aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) (Zpos g) ((,) (Zneg aa) (Zneg bb))}}}}

eqb_spec0 :: Z -> Z -> Reflect
eqb_spec0 x y =
  iff_reflect (eqb2 x y)

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

repeat :: a1 -> Nat -> ([]) a1
repeat x n =
  case n of {
   O -> ([]);
   S k -> (:) x (repeat x k)}

data Q =
   Qmake Z Positive

qnum :: Q -> Z
qnum q =
  case q of {
   Qmake qnum0 _ -> qnum0}

qden :: Q -> Positive
qden q =
  case q of {
   Qmake _ qden0 -> qden0}

qred :: Q -> Q
qred q =
  case q of {
   Qmake q1 q2 ->
    case snd (ggcd0 q1 (Zpos q2)) of {
     (,) r1 r2 -> Qmake r1 (to_pos r2)}}

data Monad m =
   Build_Monad (() -> Any -> m) (() -> () -> m -> (Any -> m) -> m)

ret :: (Monad a1) -> a2 -> a1
ret monad x =
  case monad of {
   Build_Monad ret0 _ -> unsafeCoerce ret0 __ x}

data ItreeF e r itree =
   RetF r
 | TauF itree
 | VisF e (Any -> itree)

data Itree e r =
   Go (ItreeF e r (Itree e r))

_observe :: (Itree a1 a2) -> ItreeF a1 a2 (Itree a1 a2)
_observe i =
  case i of {
   Go _observe0 -> _observe0}

observe :: (Itree a1 a2) -> ItreeF a1 a2 (Itree a1 a2)
observe =
  _observe

subst :: (a2 -> Itree a1 a3) -> (Itree a1 a2) -> Itree a1 a3
subst k u =
  case observe u of {
   RetF r -> k r;
   TauF t -> Go (TauF (subst k t));
   VisF e h -> Go (VisF e (\x -> subst k (h x)))}

bind :: (Itree a1 a2) -> (a2 -> Itree a1 a3) -> Itree a1 a3
bind u k =
  subst k u

iter :: (a3 -> Itree a1 (Prelude.Either a3 a2)) -> a3 -> Itree a1 a2
iter step i =
  bind (step i) (\lr ->
    case lr of {
     Prelude.Left l -> Go (TauF (iter step l));
     Prelude.Right r -> Go (RetF r)})

map0 :: (a2 -> a3) -> (Itree a1 a2) -> Itree a1 a3
map0 f t =
  bind t (\x -> Go (RetF (f x)))

monad_itree :: Monad (Itree a1 Any)
monad_itree =
  Build_Monad (\_ x -> Go (RetF x)) (\_ _ -> bind)

cotuple :: (a1 -> a3) -> (a2 -> a3) -> (Prelude.Either a1 a2) -> a3
cotuple f g x =
  case x of {
   Prelude.Left a -> f a;
   Prelude.Right b -> g b}

sum_map :: (a1 -> a3) -> (a2 -> a4) -> (Prelude.Either a1 a2) ->
           Prelude.Either a3 a4
sum_map f g x =
  case x of {
   Prelude.Left a -> Prelude.Left (f a);
   Prelude.Right b -> Prelude.Right (g b)}

drop :: Nat -> (([]) a1) -> ([]) a1
drop n l =
  case n of {
   O -> case l of {
         ([]) -> ([]);
         (:) _ _ -> l};
   S n' -> case l of {
            ([]) -> ([]);
            (:) _ l' -> drop n' l'}}

take :: Nat -> (([]) a1) -> ([]) a1
take n l =
  case n of {
   O -> ([]);
   S n' -> case l of {
            ([]) -> ([]);
            (:) x l' -> (:) x (take n' l')}}

data EqType a =
   Build_EqType (a -> a -> Prelude.Bool) (a -> a -> Reflect)

eqb3 :: (EqType a1) -> a1 -> a1 -> Prelude.Bool
eqb3 eqType =
  case eqType of {
   Build_EqType eqb4 _ -> eqb4}

eqb_spec1 :: (EqType a1) -> a1 -> a1 -> Reflect
eqb_spec1 eqType =
  case eqType of {
   Build_EqType _ eqb_spec2 -> eqb_spec2}

unit_eqb_spec :: () -> () -> Reflect
unit_eqb_spec _ _ =
  ReflectT

eqType_unit :: EqType ()
eqType_unit =
  Build_EqType (\_ _ -> Prelude.True) unit_eqb_spec

eqType_bool :: EqType Prelude.Bool
eqType_bool =
  Build_EqType eqb eqb_spec

eqType_Z :: EqType Z
eqType_Z =
  Build_EqType eqb2 eqb_spec0

eqType_sum_obligation_3 :: (EqType a1) -> (EqType a2) -> (Prelude.Either 
                           a1 a2) -> (Prelude.Either a1 a2) -> Reflect
eqType_sum_obligation_3 h h0 x y =
  case x of {
   Prelude.Left a ->
    case y of {
     Prelude.Left a0 ->
      let {r = eqb_spec1 h a a0} in
      case r of {
       ReflectT -> eq_rec_r a0 ReflectT a;
       ReflectF -> ReflectF};
     Prelude.Right _ -> ReflectF};
   Prelude.Right b ->
    case y of {
     Prelude.Left _ -> ReflectF;
     Prelude.Right b0 ->
      let {r = eqb_spec1 h0 b b0} in
      case r of {
       ReflectT -> eq_rec_r b0 ReflectT b;
       ReflectF -> ReflectF}}}

eqType_sum :: (EqType a1) -> (EqType a2) -> EqType (Prelude.Either a1 a2)
eqType_sum h h0 =
  Build_EqType (\a b ->
    let {filtered_var = (,) a b} in
    case filtered_var of {
     (,) s s0 ->
      case s of {
       Prelude.Left x ->
        case s0 of {
         Prelude.Left y -> eqb3 h x y;
         Prelude.Right _ -> Prelude.False};
       Prelude.Right x ->
        case s0 of {
         Prelude.Left _ -> Prelude.False;
         Prelude.Right y -> eqb3 h0 x y}}}) (\x y ->
    eqType_sum_obligation_3 h h0 x y)

is_inl :: (Prelude.Either a1 a2) -> Prelude.Bool
is_inl x =
  case x of {
   Prelude.Left _ -> Prelude.True;
   Prelude.Right _ -> Prelude.False}

data Tree a =
   Leaf a
 | Fail
 | Choice Q (Prelude.Bool -> Tree a)
 | Fix Any (Any -> Prelude.Bool) (Any -> Tree Any) (Any -> Tree a)

is_power_of_2b :: Nat -> Prelude.Bool
is_power_of_2b n =
  eqb0 n (pow (S (S O)) (log2 n))

next_pow_2 :: Nat -> Nat
next_pow_2 n =
  case eqb0 n O of {
   Prelude.True -> S O;
   Prelude.False ->
    case is_power_of_2b n of {
     Prelude.True -> n;
     Prelude.False -> pow (S (S O)) (S (log2 n))}}

to_itree_open :: (Tree a1) -> Itree () (Prelude.Either () a1)
to_itree_open t =
  case t of {
   Leaf x -> ret (unsafeCoerce monad_itree) (Prelude.Right x);
   Fail -> ret (unsafeCoerce monad_itree) (Prelude.Left ());
   Choice _ k -> Go (VisF __ (compose to_itree_open (unsafeCoerce k)));
   Fix st g g0 k ->
    iter (\s ->
      case g s of {
       Prelude.True ->
        bind (to_itree_open (g0 s)) (\y ->
          case y of {
           Prelude.Left _ ->
            ret (unsafeCoerce monad_itree) (Prelude.Right (Prelude.Left ()));
           Prelude.Right s' ->
            ret (unsafeCoerce monad_itree) (Prelude.Left s')});
       Prelude.False -> map0 (\x -> Prelude.Right x) (to_itree_open (k s))})
      st}

tie_itree :: (Itree a2 (Prelude.Either () a1)) -> Itree a2 a1
tie_itree t =
  iter (const t) ()

to_itree :: (Tree a1) -> Itree () a1
to_itree =
  compose tie_itree to_itree_open

data Btree a =
   BLeaf a
 | BNode (Btree a) (Btree a)

btree_map :: (a1 -> a2) -> (Btree a1) -> Btree a2
btree_map f t =
  case t of {
   BLeaf x -> BLeaf (f x);
   BNode t1 t2 -> BNode (btree_map f t1) (btree_map f t2)}

btree_to_tree :: (Btree a1) -> Tree a1
btree_to_tree t =
  case t of {
   BLeaf x -> Leaf x;
   BNode t1 t2 -> Choice (Qmake (Zpos XH) (XO XH)) (\b ->
    case b of {
     Prelude.True -> btree_to_tree t1;
     Prelude.False -> btree_to_tree t2})}

list_btree_aux :: (([]) a1) -> Nat -> Btree (Prelude.Either () a1)
list_btree_aux l n =
  case n of {
   O ->
    case l of {
     ([]) -> BLeaf (Prelude.Left ());
     (:) x _ -> BLeaf (Prelude.Right x)};
   S n' -> BNode (list_btree_aux (take (pow (S (S O)) n') l) n')
    (list_btree_aux (drop (pow (S (S O)) n') l) n')}

list_btree :: (([]) a1) -> Btree (Prelude.Either () a1)
list_btree l =
  list_btree_aux l (log2 (next_pow_2 (length l)))

reduce_btree :: (Btree (Prelude.Either () a1)) -> Btree
                (Prelude.Either () a1)
reduce_btree t =
  case t of {
   BLeaf _ -> t;
   BNode l r ->
    let {l' = reduce_btree l} in
    let {r' = reduce_btree r} in
    case l' of {
     BLeaf s ->
      case s of {
       Prelude.Left _ ->
        case r' of {
         BLeaf s0 ->
          case s0 of {
           Prelude.Left _ -> BLeaf (Prelude.Left ());
           Prelude.Right _ -> BNode l' r'};
         BNode _ _ -> BNode l' r'};
       Prelude.Right _ -> BNode l' r'};
     BNode _ _ -> BNode l' r'}}

reduce_btree' :: (EqType a1) -> (Btree a1) -> Btree a1
reduce_btree' h t =
  case t of {
   BLeaf _ -> t;
   BNode l r ->
    let {l' = reduce_btree' h l} in
    let {r' = reduce_btree' h r} in
    case l' of {
     BLeaf x ->
      case r' of {
       BLeaf y ->
        case eqb3 h x y of {
         Prelude.True -> BLeaf x;
         Prelude.False -> BNode l' r'};
       BNode _ _ -> BNode l' r'};
     BNode _ _ -> BNode l' r'}}

rev_range_positive :: Positive -> ([]) Z
rev_range_positive p =
  case p of {
   XI p' -> (:) (Zpos (mul0 (XO XH) p'))
    (app (map (add2 (Zpos p')) (rev_range_positive p'))
      (rev_range_positive p'));
   XO p' ->
    app (map (add2 (Zpos p')) (rev_range_positive p'))
      (rev_range_positive p');
   XH -> (:) Z0 ([])}

rev_range_Z :: Z -> ([]) Z
rev_range_Z n =
  case n of {
   Zpos p -> rev_range_positive p;
   _ -> ([])}

uniform_btree :: Z -> Btree (Prelude.Either () Z)
uniform_btree n =
  reduce_btree (list_btree (rev_range_Z n))

bernoulli_btree :: Z -> Z -> Btree (Prelude.Either () Prelude.Bool)
bernoulli_btree n d =
  reduce_btree' (eqType_sum eqType_unit eqType_bool)
    (btree_map (sum_map (\x -> x) (\i -> ltb i n)) (uniform_btree d))

bernoulli_tree_open :: Z -> Z -> Tree (Prelude.Either () Prelude.Bool)
bernoulli_tree_open n d =
  btree_to_tree (bernoulli_btree n d)

bernoulli_tree :: Q -> Tree Prelude.Bool
bernoulli_tree p =
  let {t = bernoulli_tree_open (qnum p) (Zpos (qden p))} in
  Fix (unsafeCoerce (Prelude.Left ())) (unsafeCoerce is_inl) (\_ ->
  unsafeCoerce t)
  (unsafeCoerce cotuple (\_ -> Leaf Prelude.False) (\x -> Leaf x))

uniform_tree_open :: Z -> Tree (Prelude.Either () Z)
uniform_tree_open n =
  btree_to_tree (uniform_btree n)

uniform_tree :: Z -> Tree Z
uniform_tree n =
  let {t = uniform_tree_open n} in
  Fix (unsafeCoerce (Prelude.Left ())) (unsafeCoerce is_inl) (\_ ->
  unsafeCoerce t) (unsafeCoerce cotuple (\_ -> Leaf Z0) (\x -> Leaf x))

flatten_weights_aux :: (([]) Z) -> Z -> ([]) Z
flatten_weights_aux weights acc =
  case weights of {
   ([]) -> ([]);
   (:) w ws ->
    app (repeat acc (to_nat0 w)) (flatten_weights_aux ws (succ0 acc))}

flatten_weights :: (([]) Z) -> ([]) Z
flatten_weights weights =
  flatten_weights_aux weights Z0

findist_btree :: (([]) Z) -> Btree (Prelude.Either () Z)
findist_btree weights =
  reduce_btree' (eqType_sum eqType_unit eqType_Z)
    (list_btree (flatten_weights weights))

findist_tree_open :: (([]) Z) -> Tree (Prelude.Either () Z)
findist_tree_open weights =
  btree_to_tree (findist_btree weights)

findist_tree :: (([]) Z) -> Tree Z
findist_tree weights =
  let {t = findist_tree_open weights} in
  Fix (unsafeCoerce (Prelude.Left ())) (unsafeCoerce is_inl) (\_ ->
  unsafeCoerce t) (unsafeCoerce cotuple (\_ -> Leaf Z0) (\x -> Leaf x))

findist_itree :: (([]) Z) -> Itree () Z
findist_itree weights =
  to_itree (findist_tree weights)

data SamplerPackage =
   MkSamplers (Q -> Itree () Prelude.Bool) (Z -> Itree () Z) ((([]) Z) ->
                                                             Itree () 
                                                             Z)

coin_itree :: Q -> Itree () Prelude.Bool
coin_itree p =
  to_itree (bernoulli_tree (qred p))

die_itree :: Z -> Itree () Z
die_itree n =
  to_itree (uniform_tree n)

samplers :: SamplerPackage
samplers =
  MkSamplers coin_itree die_itree findist_itree

