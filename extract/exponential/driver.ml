open Random
open Exponential

let handle_choice k = k (Obj.magic (Random.bool ()))

(* let handle_choice k = k (Random.bool ()) *)

let rec run t =
  match observe t with
  | RetF x -> x
  | TauF t' -> run t'
  | VisF (_, k) -> run (handle_choice k)

(* let rec gen_samples (n : int) : bool list =
 *   if n <= 0 then [] else run sampler_itree :: gen_samples (n-1)
 * 
 * let rec count (f : 'a -> bool) = function
 *   | [] -> 0
 *   | x :: xs -> (if f x then 1 else 0) + count f xs
 * 
 * let rel_freq (bs : bool list) : float =
 *   Float.of_int (count Fun.id bs) /. Float.of_int (count (Fun.const true) bs) *)

let eval : int -> int =
  let rec eval_aux acc n =
    if n <= 0 then acc else
      eval_aux (acc + if run sampler then 1 else 0) (n-1) in
  eval_aux 0

let () =
  let _ = Random.self_init () in
  let d = 100000 in
  eval d
  |> fun n -> Float.of_int n /. Float.of_int d
  |> Float.to_string
  |> print_endline

  (* print_endline (Bool.to_string (run sampler)) *)
