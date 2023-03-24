open Samplers

exception ZarError of string

val nat_of_int : int -> nat

val int_of_nat : nat -> int

val positive_of_int : int -> positive

val int_of_positive : positive -> int

val z_of_int : int -> z

val int_of_z : z -> int

val qmake : int -> int -> q

val seed : unit -> unit

(** Run an itree sampler. *) 
val run : (__, 'a) itree -> 'a
