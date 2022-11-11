open Random
open Dueling_coins

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

  (* let oc = open_out "samples.dat" in *)
  (* List.iter (fun o -> Printf.fprintf oc "%s\n" (show_record string_of_bool o)) !records; *)
  (* close_out oc; *)

  (* gen 100; *)
  (* print_endline (string_of_int @@ List.length !records); *)

  (* let oc = open_out "samples1k.dat" in *)
  (* List.iter (fun o -> Printf.fprintf oc "%s\n" (show_record string_of_bool o)) !records; *)
  (* close_out oc; *)

  (* gen 900; *)
  (* print_endline (string_of_int @@ List.length !records); *)

  (* let oc = open_out "samples10k.dat" in *)
  (* List.iter (fun o -> Printf.fprintf oc "%s\n" (show_record string_of_bool o)) !records; *)
  (* close_out oc; *)

  (* gen 9000; *)
  (* print_endline (string_of_int @@ List.length !records); *)

  gen 100000;
  print_endline (string_of_int @@ List.length !records);

  let oc = open_out "samples100k.dat" in
  List.iter (fun o -> Printf.fprintf oc "%s\n" (show_record string_of_bool o)) !records;
  close_out oc
