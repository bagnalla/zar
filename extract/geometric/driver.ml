open Geometric

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

let () =
  let _ = Random.self_init () in

  (* gen 1000; *)
  (* print_endline (string_of_int @@ List.length !records); *)

  (* let oc = open_out "samples1k.dat" in *)
  (* List.iter (fun o -> Printf.fprintf oc "%s\n" *)
  (*                       (show_record (fun n -> string_of_int (int_of_nat n)) o)) *)
  (*   !records; *)
  (* close_out oc; *)

  (* gen 9000; *)
  (* print_endline (string_of_int @@ List.length !records); *)

  (* let oc = open_out "samples10k.dat" in *)
  (* List.iter (fun o -> Printf.fprintf oc "%s\n" *)
  (*                       (show_record (fun n -> string_of_int (int_of_nat n)) o)) *)
  (*   !records; *)
  (* close_out oc; *)

  gen 100000;
  print_endline (string_of_int @@ List.length !records);

  let oc = open_out "samples100k.dat" in
  List.iter (fun o -> Printf.fprintf oc "%s\n"
                        (show_record (fun n -> string_of_int (int_of_nat n)) o))
    !records;
  close_out oc
