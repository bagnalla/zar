(** Biased coin. *)

(** Build and cache coin. *)
val build : int -> int -> unit

(** Flip the coin. *)
val flip : unit -> bool

(** Flip the coin n times. *)
val flips : int -> bool list
