open Random
open Gp

let rec entropy n t =
  if n <= 0 then 0.0 else
    match observe t with
    | RetF x -> 0.0
    | TauF t' -> entropy n t'
    | VisF (_, k) -> 1.0 +. (entropy (n - 1) (k (Obj.magic false)) +.
                               entropy (n - 1) (k (Obj.magic true))) /. 2.0

let () =
  for i = 0 to 100 do
    print_endline @@ string_of_int i ^ ": " ^ string_of_float (entropy i sampler)
  done
