open Core
open Samplers

let cached_coin : ((__, bool) itree) ref =
  ref (samplers.coin_sampler (qmake 0 1))

let build n d =
  if n < 0 then
    raise (ZarError "Coin.build: numerator must be nonnegative")
  else if n > d then
    raise (ZarError "Coin.build: numerator must be <= denominator")
  else
    cached_coin := samplers.coin_sampler (qmake n d)

let flip () = run !cached_coin

let flips n =
  List.init n (fun _ -> run !cached_coin)
