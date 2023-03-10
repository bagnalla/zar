open Python_lib
open Python_lib.Let_syntax
open Samplers

exception ZarError of string

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

let seed = Let_syntax.return (Random.self_init (); fun () -> Py.none)

(** Biased coin. *)

let rec positive_of_int (i : int) : positive =
  if i <= 1 then
    XH
  else if i mod 2 == 0 then
    XO (positive_of_int (i / 2))
  else
    XI (positive_of_int (i / 2))

let z_of_int (i : int) : z =
  if i == 0 then
    Z0
  else if i > 0 then
    Zpos (positive_of_int i)
  else
    Zneg (positive_of_int (-i))

let qmake n d =
  if d < 1 then
    raise (ZarError "qmake: denominator of rational must be positive")
  else 
    { qnum = z_of_int n; qden = positive_of_int d }

let cached_coin : ((__, bool) itree) ref = ref (coin_die_samplers.coin_sampler (qmake 0 1))

let flip_coin () : bool =
  run !cached_coin

let n_flips (n : int) : bool list =
  List.init n (fun _ -> 0) |> List.map @@ fun _ -> run !cached_coin

let build_coin =
  let%map_open (n, d) =
    positional "nd" (pair int int)
      ~docstring:"numerator and denominator of coin bias parameter" in
  if n < 0 then
    raise (ZarError "build_coin: numerator must be nonnegative")
  else
    (cached_coin := coin_die_samplers.coin_sampler (qmake n d);
     fun () -> Py.none)

let flip =
  let%map_open _ = keyword_opt "x" int ~docstring:"no argument" in
  fun () -> python_of_bool @@ flip_coin ()

let flip_n =
  let%map_open n = positional "n" int ~docstring:"number of flips" in
  fun () -> python_of_list python_of_bool @@ n_flips n

(** N-sided die. *)

let rec nat_of_int (i : int) : nat =
  if i <= 0 then O else S (nat_of_int (i - 1))

let rec int_of_nat = function
  | O -> 0
  | S n' -> 1 + int_of_nat n'

let cached_die : ((__, nat) itree) ref = ref (coin_die_samplers.die_sampler O)

let roll_die () : int =
  int_of_nat @@ run !cached_die

let n_rolls (n : int) : int list =
  List.init n (fun _ -> 0) |> List.map @@ fun _ -> int_of_nat (run !cached_die)

(* let n_rolls_entropy (n : int) : (int list) list = *)
(*   List.init n (fun _ -> 0) |> List.map @@ fun _ -> *)
(*                                           let sample = run !cached_die in *)
(*                                           let n = !num_bits in *)
(*                                           num_bits := 0; *)
(*                                           [int_of_nat (sample); n] *)

let build_die =
  let%map_open m = positional "m" int ~docstring:"number of possible values" in
  cached_die := coin_die_samplers.die_sampler (nat_of_int m);
  fun () -> Py.none

let roll =
  let%map_open _ = keyword_opt "x" int ~docstring:"no argument" in
  fun () -> python_of_int @@ roll_die ()

let roll_n =
  let%map_open n = positional "n" int ~docstring:"number of rolls" in
  fun () -> python_of_list python_of_int @@ n_rolls n

(* let roll_n_entropy = *)
(*   let%map_open n = positional "n" int ~docstring:"" in *)
(*   fun () -> python_of_list (python_of_list python_of_int) @@ n_rolls_entropy n *)

let () =
  if not (Py.is_initialized ()) then Py.initialize ();
  let mod_ = Py_module.create "zarpy" in
  Py_module.set mod_ "seed"
    ~docstring:"Seed PRNG." seed;
  Py_module.set mod_ "build_coin"
    ~docstring:"Build and cache coin sampler." build_coin;
  Py_module.set mod_ "flip"
    ~docstring:"Flip the cached coin." flip;
  Py_module.set mod_ "flip_n"
    ~docstring:"Flip the cached coin n times." flip_n;
  Py_module.set mod_ "build_die"
    ~docstring:"Build and cache die sampler." build_die;
  Py_module.set mod_ "roll"
    ~docstring:"Roll the cached die." roll;
  Py_module.set mod_ "roll_n"
    ~docstring:"Roll the cached die n times." roll_n;
  (* Py_module.set mod_ "many_entropy" *)
  (*   ~docstring:"Generate multiple samples with entropy information." roll_n_entropy; *)
