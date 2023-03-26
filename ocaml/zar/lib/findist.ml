open Core
open Samplers

let cached_sampler : ((__, z) itree) ref =
  ref (coin_die_samplers.findist_sampler [z_of_int 1])

let build weights =
  if List.exists (fun w -> w < 0) weights then
    raise (ZarError "Findist.weights: all weights must be nonnegative")
  else if List.for_all (fun w -> w <= 0) weights then
    raise (ZarError "Findist.weights: at least one weight must be positive")
  else
    cached_sampler :=
      coin_die_samplers.findist_sampler @@ List.map z_of_int weights

let sample () = int_of_z @@ run !cached_sampler

let samples n =
  List.init n (fun _ -> int_of_z @@ run !cached_sampler)
