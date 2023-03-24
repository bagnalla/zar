
(** Build and cache sampler from list of weights. *)
val build : int list -> unit

(** Draw a single sample. *)
val sample : unit -> int

(** Flip the die n times. *)
val samples : int -> int list
