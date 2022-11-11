open Random
open Gp

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

let records : (bool sample_record) list ref = ref []

let gen (n : int) : unit =
  for i = 1 to n do
    let t0 = Sys.time() in
    let sample = run sampler in
    let t1 = Sys.time() in
    records := { sample = sample
               ; bits = !bits
               ; time = t1 -. t0 } :: !records;
    bits := []
  done

(* let rec nat_to_string = function *)
(*   | O -> "O" *)
(*   | S n -> "S " ^ nat_to_string n *)

(* let rec nat_to_float = function
 *   | O -> 0.0
 *   | S n -> nat_to_float n +. 1.0 *)

(* let rec nat_to_int = function *)
(*   | O -> 0 *)
(*   | S n -> nat_to_int n + 1 *)

let () =
  let _ = Random.self_init () in

  gen 100000;

  print_endline (string_of_int @@ List.length !records);

  let oc = open_out "samples.dat" in
  List.iter (fun o -> Printf.fprintf oc "%s\n" (show_record string_of_bool o)) !records;
    (* Printf.fprintf oc "%s\n" (show_record string_of_bool (List.nth !records i)) *)
    (* print_endline (show_record string_of_bool (List.nth !records i)) *)
  (* done; *)
  close_out oc

  (* let n = 1000000 in *)
  (* let t0 = Sys.time() in *)
  (* let count = eval n in *)
  (* print_endline (Float.to_string (float_of_int count /. float_of_int n)); *)
  (* let t1 = Sys.time() in *)

  (* print_endline (string_of_int n ^ " samples generated"); *)
  (* print_endline ("# true: " ^ string_of_int count); *)
  (* print_endline (string_of_float (t1 -. t0) ^ "s elapsed"); *)
  (* print_endline ("avg time per sample: " ^ string_of_float ((t1 -. t0) /. float_of_int n)); *)
  (* print_endline ("# of random bits used: " ^ string_of_int !num_bits); *)
  (* print_endline ("avg bits per sample: " ^ string_of_float (float_of_int !num_bits /. float_of_int n)) *)

  (* print_endline (nat_to_string (run sampler)) *)
