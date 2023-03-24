open Samplers

exception ZarError of string

let nat_of_int (i : int) : nat =
  if i < 0 then
    raise (ZarError ("nat_of_int: int must be nonnegative, got "
                     ^ string_of_int i))
  else
    let rec go (j : int) (acc : nat) : nat =
      if j <= 0 then acc else (go [@tailcall]) (j-1) (S acc)
    in go i O

let int_of_nat (n : nat) =
  let rec go (acc : int) = function
    | O -> acc
    | S n' -> (go [@tailcall]) (acc + 1) n'
  in go 0 n

let positive_of_int (i : int) : positive =
  if i < 1 then
    raise (ZarError ("positive_of_int: int must be positive, got "
                     ^ string_of_int i))
  else
    let rec go (j : int) : positive =
      if j == 1 then
        XH
      else if j mod 2 == 0 then
        XO (go @@ j / 2)
      else
        XI (go @@ j / 2)
    in go i

let rec int_of_positive = function
  | XH -> 1
  | XO p' -> 2 * int_of_positive p'
  | XI p' -> 2 * int_of_positive p' + 1

let z_of_int (i : int) : z =
  if i == 0 then
    Z0
  else if i > 0 then
    Zpos (positive_of_int i)
  else
    Zneg (positive_of_int (-i))

let int_of_z = function
  | Z0 -> 0
  | Zpos p -> int_of_positive p
  | Zneg p -> - int_of_positive p

let qmake n d = { qnum = z_of_int n; qden = positive_of_int d }

let seed () = Random.self_init ()

(** Run an itree sampler. *) 
let rec run t =
  match observe t with
  | RetF x -> x
  | TauF t' -> run t'
  | VisF (_, k) -> run (k (Obj.magic (Random.bool ())))
