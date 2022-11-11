(** For comparison with FLDR and OPTAS. *)

open Random
open Uniform
open Unix

let num_bits : int ref = ref 0

let handle_choice k =
  num_bits := !num_bits + 1;
  k (Obj.magic (Random.bool ()))

(** Run an itree sampler. *) 
let rec run t =
  match observe t with
  | RetF x -> x
  | TauF t' -> run t'
  | VisF (_, k) -> run (handle_choice k)

type 'a sample_record =
  { sample : 'a    (* the sample *)
  ; num_bits : int (* # bits used to generate sample *) }

let string_of_bool (b : bool) : string =
  if b then "1" else "0"

let show_record (show : 'a -> string)
    : 'a sample_record -> string = function
  | { sample = s; num_bits = n } ->
     show s ^ " " ^ string_of_int n

let rec string_of_nat = function
  | O -> "O"
  | S n -> "S " ^ string_of_nat n

let rec int_of_nat = function
  | O -> 0
  | S n -> 1 + int_of_nat n

let rec nat_of_int = function
  | n when n <= 0 -> O
  | n -> S (nat_of_int (n - 1))

let records : (nat sample_record) list ref = ref []

let gen sampler (n : int) : unit =
  for i = 1 to n do
    let sample = run sampler in
    records := { sample = sample
               ; num_bits = !num_bits } :: !records;
    num_bits := 0
  done

let () =
  let t0 = Unix.gettimeofday () in
  let _ = Random.self_init () in
  let sampler = sampler (nat_of_int 200) in
  let t1 = Unix.gettimeofday () in
  print_endline ("setup time: " ^ string_of_float (t1 -. t0));

  (* let t0 = Sys.time() in *)
  let t0 = Unix.gettimeofday () in
  gen sampler 100000;
  let t1 = Unix.gettimeofday () in
  print_endline ("sample time: " ^ string_of_float (t1 -. t0));
  print_endline (string_of_int @@ List.length !records);

  let oc = open_out "zar_samples.dat" in
  List.iter (fun o -> Printf.fprintf oc "%s\n"
                        (show_record (fun n -> string_of_int (int_of_nat n)) o))
    !records;
  close_out oc

  (* gen sampler 1000; *)

  (* print_endline (string_of_int @@ List.length !records); *)

  (* let oc = open_out "samples.dat" in *)
  (* List.iter (fun o -> Printf.fprintf oc "%s\n" *)
  (*                       (show_record (fun n -> string_of_int (int_of_nat n)) o)) *)
  (*   !records; *)
  (* close_out oc *)
