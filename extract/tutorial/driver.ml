open Prog

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
  ; bits : bool list (* bits used to generate sample *) }

let string_of_bool (b : bool) : string =
  if b then "1" else "0"

let rec bitstring : bool list -> string = function
  | [] -> ""
  | b :: bs -> string_of_bool b ^ bitstring bs

let show_record (show : 'a -> string)
    : 'a sample_record -> string = function
  | { sample = s; bits = b } -> show s ^ " " ^ bitstring b

let records : (z sample_record) list ref = ref []

let gen sampler (n : int) : unit =
  for i = 1 to n do
    let sample = run sampler in
    records := { sample = sample
               ; bits = List.rev !bits } :: !records;
    bits := []
  done

let rec string_of_nat = function
  | O -> "O"
  | S n -> "S " ^ string_of_nat n

let rec int_of_nat = function
  | O -> 0
  | S n -> 1 + int_of_nat n

let rec nat_of_int = function
  | n when n <= 0 -> O
  | n -> S (nat_of_int (n - 1))

let rec int_of_positive : positive -> int = function
  | XI p -> 2 * int_of_positive p + 1
  | XO p -> 2 * int_of_positive p
  | XH -> 1

let int_of_z : z -> int = function
  | Z0 -> 0
  | Zpos p -> int_of_positive p
  | Zneg p -> - int_of_positive p

let rec positive_of_int (i : int) : positive =
  if i <= 1 then
    XH
  else if i mod 2 == 0 then
    XO (positive_of_int (i / 2))
  else
    XI (positive_of_int (i / 2))

let rec z_of_int (i : int) : z =
  if i == 0 then
    Z0
  else if i > 0 then
    Zpos (positive_of_int i)
  else
    Zneg (positive_of_int (-i))

let qmake n d = { qnum = z_of_int n; qden = positive_of_int d }

let () =
  (** Initialize PRNG. *)
  let _ = Random.self_init () in

  (** Generate 100k samples. *)
  let t0 = Sys.time () in
  gen sampler 100000;
  print_endline @@ "time elapsed: " ^ string_of_float (Sys.time () -. t0) ^ "s";
  print_endline @@ "# samples: " ^ string_of_int @@ List.length !records;

  (** Dump samples to disk. *)
  let oc = open_out "samples100k.dat" in
  List.iter (fun o -> Printf.fprintf oc "%s\n"
                        (show_record (fun n -> string_of_int (int_of_z n)) o))
    !records;
  close_out oc
