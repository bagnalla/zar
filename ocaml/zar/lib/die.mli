
(** Build and cache die. *)
val build : int -> unit

(** Roll the die. *)
val roll : unit -> int

(** Flip the die n times. *)
val rolls : int -> int list
