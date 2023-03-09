open Random
open Coin

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

let gen (n : int) : unit =
  for i = 1 to n do
    let t0 = Sys.time() in
    let sample = run (sampler (qmake 2 3)) in
    let t1 = Sys.time() in
    records := { sample = sample
               ; bits = !bits
               ; time = t1 -. t0 } :: !records;
    bits := []
  done

let () =
  let _ = Random.self_init () in

  gen 100000;
  print_endline (string_of_int @@ List.length !records);

  let oc = open_out "samples100k.dat" in
  List.iter (fun o -> Printf.fprintf oc "%s\n" (show_record string_of_bool o)) !records;
  close_out oc
