open Python_lib
open Python_lib.Let_syntax
open Sampler

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

let rec nat_of_int (i : int) : nat =
  if i <= 0 then O else S (nat_of_int (i - 1))

let rec int_of_nat = function
  | O -> 0
  | S n' -> 1 + int_of_nat n'

let cached_sampler : ((__, nat) itree) ref = ref (sampler O)

let single_sample () : int =
  int_of_nat @@ run !cached_sampler

let n_samples (n : int) : int list =
  List.init n (fun _ -> 0) |> List.map @@ fun _ -> int_of_nat (run !cached_sampler)

let n_samples_entropy (n : int) : (int list) list =
  List.init n (fun _ -> 0) |> List.map @@ fun _ ->
                                          let sample = run !cached_sampler in
                                          let n = !num_bits in
                                          num_bits := 0;
                                          [int_of_nat (sample); n]

let seed = Let_syntax.return (Random.self_init (); fun () -> Py.none)

let build =
  let%map_open m = positional "m" int ~docstring:"" in
  cached_sampler := sampler (nat_of_int m);
  fun () -> Py.none

let single =
  let%map_open _ = keyword_opt "x" int ~docstring:"" in
  fun () -> python_of_int @@ single_sample ()

let many =
  let%map_open n = positional "n" int ~docstring:"" in
  fun () -> python_of_list python_of_int @@ n_samples n

let many_entropy =
  let%map_open n = positional "n" int ~docstring:"" in
  fun () -> python_of_list (python_of_list python_of_int) @@ n_samples_entropy n

let () =
  if not (Py.is_initialized ()) then Py.initialize ();
  let mod_ = Py_module.create "zarpy" in
  Py_module.set mod_ "seed"
    ~docstring:"Seed PRNG." seed;
  Py_module.set mod_ "build"
    ~docstring:"Build and cache sampler." build;
  Py_module.set mod_ "single"
    ~docstring:"Generate a single sample." single;
  Py_module.set mod_ "many"
    ~docstring:"Generate multiple samples." many;
  Py_module.set mod_ "many_entropy"
    ~docstring:"Generate multiple samples with entropy information." many_entropy;
