(** Finite distribution. *)

(** Build and cache sampler from list of weights. *)
val build : int list -> unit

(** Draw a single sample. *)
val sample : unit -> int

(** Draw n samples. *)
val samples : int -> int list
