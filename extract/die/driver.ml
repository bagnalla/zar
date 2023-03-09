open Random
open Die

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
    let t0 = Sys.time() in
    let sample = run sampler in
    let t1 = Sys.time() in
    (* print_endline (string_of_int (int_of_nat sample)); *)
    records := { sample = sample
               ; bits = List.rev !bits
               ; time = t1 -. t0 } :: !records;
    bits := []
  done

let () =
  let _ = Random.self_init () in

  (* let t0 = Sys.time() in *)
  let sampler = sampler (nat_of_int 200) in
  (* let t1 = Sys.time() in *)
  (* print_endline (string_of_float (t1 -. t0)); *)

  (* gen sampler 1000; *)
  (* print_endline (string_of_int @@ List.length !records); *)

  (* let oc = open_out "samples1k.dat" in *)
  (* List.iter (fun o -> Printf.fprintf oc "%s\n" *)
  (*                       (show_record (fun n -> string_of_int (int_of_nat n)) o)) *)
  (*   !records; *)
  (* close_out oc; *)

  (* gen sampler 9000; *)
  (* print_endline (string_of_int @@ List.length !records); *)

  (* let oc = open_out "samples10k.dat" in *)
  (* List.iter (fun o -> Printf.fprintf oc "%s\n" *)
  (*                       (show_record (fun n -> string_of_int (int_of_nat n)) o)) *)
  (*   !records; *)
  (* close_out oc; *)

  gen sampler 100000;
  print_endline (string_of_int @@ List.length !records);

  let oc = open_out "samples100k.dat" in
  List.iter (fun o -> Printf.fprintf oc "%s\n"
                        (show_record (fun n -> string_of_int (int_of_nat n)) o))
    !records;
  close_out oc

  (* gen sampler 900000; *)
  (* print_endline (string_of_int @@ List.length !records); *)

  (* let oc = open_out "samples1m.dat" in *)
  (* List.iter (fun o -> Printf.fprintf oc "%s\n" *)
  (*                       (show_record (fun n -> string_of_int (int_of_nat n)) o)) *)
  (*   !records; *)
  (* close_out oc *)
