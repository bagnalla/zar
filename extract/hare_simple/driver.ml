open Random
open Hare

let bits : bool list ref = ref []

let handle_choice k =
  let b = Random.bool () in
  bits := b :: !bits;
  let x = k (Obj.magic b) in
  x

(** Run an itree sampler. *) 
let rec run t =
  match observe t with
  | RetF x -> x
  | TauF t' -> run t'
  | VisF (_, k) -> run (handle_choice k)

type 'a sample_record =
  { sample : 'a      (* the sample *)
  ; bits : bool list (* bits used to generate sample *)
  ; time : float }   (* time to generate sample (in seconds) *)

let string_of_bool (b : bool) : string =
  if b then "1" else "0"

let rec bitstring : bool list -> string = function
  | [] -> ""
  | b :: bs -> string_of_bool b ^ bitstring bs

let show_record (show : 'a -> string)
    : 'a sample_record -> string = function
  | { sample = s; bits = b; time = t } ->
     show s ^ " " ^ bitstring b ^ " " ^ string_of_float t

let records : (nat sample_record) list ref = ref []

let gen (n : int) : unit =
  for i = 1 to n do
    let t0 = Sys.time() in
    let sample = run sampler in
    let t1 = Sys.time() in
    records := { sample = sample
               ; bits = List.rev !bits
               ; time = t1 -. t0 } :: !records;
    bits := []
  done

let rec string_of_nat = function
  | O -> "O"
  | S n -> "S " ^ string_of_nat n

let rec int_of_nat = function
  | O -> 0
  | S n -> 1 + int_of_nat n

let rec int_of_positive = function
  | XH -> 1
  | XO p -> 2 * int_of_positive p
  | XI p -> 2 * int_of_positive p + 1

let int_of_z = function
  | Z0 -> 0
  | Zpos p -> int_of_positive p
  | Zneg p -> - int_of_positive p

let string_of_z (x : z) : string = string_of_int (int_of_z x)

let string_of_positive (x : positive) : string =
  string_of_int (int_of_positive x)

let rec string_of_q (x : q) : string =
  string_of_z (x.qnum) ^ "/" ^ string_of_positive (x.qden)

let rec string_of_tree (show : st -> string) = function
  | Leaf s -> "(Leaf " ^ show s ^ ")"
  | Fail -> "Fail"
  | Choice (p, k) ->
     "(Choice " ^ string_of_q p ^ " " ^ string_of_tree show (k true)
     ^ " " ^ string_of_tree show (k false) ^ ")"
  | Fix (s, e, g, k) -> "(Fix " ^ show s ^ " " ^ ")"

(* type tree = *)
(* | Leaf of st *)
(* | Fail *)
(* | Choice of q * (bool -> tree) *)
(* | Fix of st * (st -> bool) * (st -> tree) * (st -> tree) *)

let () =
  let _ = Random.self_init () in

  gen 10000;

  print_endline (string_of_int @@ List.length !records);

  let oc = open_out "samples.dat" in
  List.iter (fun o -> Printf.fprintf oc "%s\n"
                        (show_record (fun n -> string_of_int (int_of_nat n)) o))
    !records;
  close_out oc
