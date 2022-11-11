open Random
(* open Sampler *)
open List

let handle_choice k = k (Obj.magic (Random.bool ()))

(* let handle_choice k = k (Random.bool ()) *)

(* let rec run t = *)
(*   match observe t with *)
(*   | RetF x -> x *)
(*   | TauF t' -> run t' *)
(*   | VisF (_, k) -> *)
(*      (\* let _ = print_endline "choice" in *\) *)
(*      run (handle_choice k) *)

(* type positive =
 *   | XI of positive
 *   | XO of positive
 *   | XH *)

(* type z =
 *   | Z0
 *   | Zpos of positive
 *   | Zneg of positive *)

(* let rec pos_to_int = function *)
(*   | XI p -> 2 * pos_to_int p + 1 *)
(*   | XO p -> 2 * pos_to_int p *)
(*   | XH -> 1 *)

(* let z_to_int = function *)
(*   | Z0 -> 0 *)
(*   | Zpos p -> pos_to_int p *)
(*   | Zneg p -> - pos_to_int p *)

(* let z_to_string (z : z) = *)
(*   string_of_int (z_to_int z) *)

(* let rec positive_eq (a : positive) (b : positive) = *)
(*   match (a, b) with *)
(*   | (XI p, XI q) -> positive_eq p q *)
(*   | (XO p, XO q) -> positive_eq p q *)
(*   | (XH, XH) -> true *)
(*   | _ -> false *)

(* let z_eq (a : z) (b : z) = *)
(*   match (a, b) with *)
(*   | (Z0, Z0) -> true *)
(*   | (Zpos p, Zpos q) -> positive_eq p q *)
(*   | (Zneg p, Zneg q) -> positive_eq p q *)
(*   | _ -> false *)

(* let eval (mu : z) (sigma : q) (pred : z -> bool) : int -> int = *)
(*   let rec eval_aux acc n = *)
(*     if n <= 0 then acc else *)
(*       let sample = run (sampler mu sigma) in *)
(*       (if n mod 1000 == 0 then print_endline (string_of_int n) else ()); *)
(*       (\* print_endline (z_to_string sample); *\) *)
(*       (eval_aux [@tailcall]) (acc + if pred sample then 1 else 0) (n-1) in *)
(*   eval_aux 0 *)

let rec range (i : int) : int list =
  if i <= 0 then [] else range (i - 1) @ [i-1]

let rec sum : float list -> float = function
  | [] -> 0.0
  | x :: xs -> x +. sum xs

let range' (start : int) (len : int) : int list =
  map (fun i -> i + start) (range len)

let pmf_e (sigma : float) (x : int) : float =
  exp ((-. (float_of_int x ** 2.0)) /. (2.0 *. (sigma ** 2.0)))

(* let rec string_of_list (f : 'a -> string) : 'a list -> string = function
 *   | [] -> ""
 *   | x :: xs -> f x ^ " " ^ string_of_list f xs *)
  
(* let string_of_list (f : 'a -> string) (l : 'a list) : string =
 *   String.concat ", " (map f l) *)
  
(* let string_of_list (f : 'a -> string) (l : 'a list) : string =
 *   map f l |> String.concat ", " *)
  
(* Discrete gaussian centered at 0 with std deviation sigma. Computes P[X = z]. *)
let pmf (sigma : float) (z : int) : float =
  (* (pmf_e sigma z) /. (sum (map (fun i -> pmf_e sigma i) (range' (-10) 20))) *)
  let n = pmf_e sigma z in
  let d = sum (map (pmf_e sigma) (range' (-500) 1000)) in
  (* print_endline ("ints:" ^ string_of_list string_of_int (range' (-5) 10));
   * print_endline ("n:" ^ string_of_float n);
   * print_endline ("d:" ^ string_of_float d); *)
  n /. d

(* let rec nat_of_int (i : int) : nat = *)
(*   if i <= 0 then O else S (nat_of_int (i - 1)) *)

(* type positive =
 *   | XI of positive
 *   | XO of positive
 *   | XH *)

(* type z =
 *   | Z0
 *   | Zpos of positive
 *   | Zneg of positive *)

(* let rec positive_of_int (i : int) : positive = *)
(*   if i <= 1 then *)
(*     XH *)
(*   else if i mod 2 == 0 then *)
(*     XO (positive_of_int (i / 2)) *)
(*   else *)
(*     XI (positive_of_int (i / 2)) *)
(*  (\*   Coq_Pos.of_succ_nat (nat_of_int (i - 1)) *\) *)

(* let rec int_of_positive : positive -> int = function *)
(*   | XI p -> 2 * int_of_positive p + 1 *)
(*   | XO p -> 2 * int_of_positive p *)
(*   | XH -> 1 *)

(* let int_of_z : z -> int = function *)
(*   | Z0 -> 0 *)
(*   | Zpos p -> int_of_positive p *)
(*   | Zneg p -> - int_of_positive p *)

(* let float_of_q (q : q) : float = *)
(*   float_of_int (int_of_z q.qnum) /. float_of_int (int_of_positive q.qden) *)

(* let rec z_of_int (i : int) : z = *)
(*   if i == 0 then *)
(*     Z0 *)
(*   else if i > 0 then *)
(*     Zpos (positive_of_int i) *)
(*   else *)
(*     Zneg (positive_of_int (-i)) *)
(*   (\* if 0 <= i then *)
(*    *   Z.of_nat (nat_of_int i) *)
(*    * else *)
(*    *   Z.opp (z_of_int (-i)) *\) *)

let () =
  (* Printexc.record_backtrace true; *)
  let _ = Random.self_init () in

  print_endline (string_of_float (pmf 1.0 0))

  (* let mu = 1 in *)
  (* let sigma = { qnum = z_of_int 5; qden = positive_of_int 4 } in *)
  (* let z = 1 in *)

  (* print_endline ("sigma.qnum: " ^ string_of_int (int_of_z sigma.qnum)); *)
  (* print_endline ("sigma.qden: " ^ string_of_int (int_of_positive sigma.qden)); *)
  (* print_endline ("sigma: " ^ string_of_float (float_of_q sigma)); *)
  (* print_endline ("expected: " ^ Float.to_string (pmf (float_of_q sigma) z)); *)
  
  (* let d = 1000 in *)
  (* eval (z_of_int mu) sigma (fun x -> z_eq x (z_of_int z)) d *)
  (* |> fun n -> Float.of_int n /. Float.of_int d *)
  (* |> Float.to_string *)
  (* |> print_endline *)

  (* (\* print_endline (Bool.to_string (run sampler)) *\) *)
