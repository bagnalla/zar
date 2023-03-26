open Core
open Samplers

let cached_die : ((__, z) itree) ref =
  ref (coin_die_samplers.die_sampler Z0)

let build n =
  if n <= 0 then
    raise (ZarError "Die.build: n must be positive")
  else
    cached_die := coin_die_samplers.die_sampler (z_of_int n)

let roll () = int_of_z @@ run !cached_die

let rolls n =
  List.init n (fun _ -> int_of_z @@ run !cached_die)
