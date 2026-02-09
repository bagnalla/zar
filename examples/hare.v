(** * Hare and tortoise. *)

From Coq Require Import Basics QArith Lia Lqa String Qabs.
Open Scope string_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From zar Require Import compile cpGCL cpGCLNotations gaussian itree Q tree.

Local Open Scope cpGCL_scope.

(* Definition hare_tortoise : cpGCL := *)
(*   "t" <-- 5%nat; *)
(*   "h" <-- 0%nat; *)
(*   "time" <-- 0%nat; *)
(*   while (fun s => Nat.ltb (as_nat (s "h")) (as_nat (s "t"))) do *)
(*     "t" <-- (fun s => incr (s "t")); *)
(*     CChoice (const (1#4)) *)
(*       (fun b => if b then *)
(*                gaussian "g" 2; *)
(*                "h" <-- (fun s => (as_nat (s "h") + as_nat (s "g") + 5)%nat) *)
(*              else *)
(*                skip); *)
(*     "time" <-- (fun s => incr (s "time")) *)
(*   end. *)

Definition gauss (x : string) (mu : Z) (sigma : Q) : cpGCL :=
  gaussian x sigma;
  x <-- (fun s => (as_int (s x) + mu)%Z).

Definition gauss' (x : string) (mu : St -> Z) (sigma : Q) : cpGCL :=
  gaussian x sigma;
  x <-- (fun s => (as_int (s x) + mu s)%Z).

(* Definition hare_tortoise : cpGCL := *)
(*   gauss "T0" 5 2; *)
(*   "T" <-- (fun s => s "T0"); *)
(*   "h" <-- 0%Z; *)
(*   "t" <-- 0%Z; *)
(*   while (fun s => Z.ltb (as_int (s "h")) (as_int (s "T"))) do *)
(*     "T" <-- (fun s => (as_int (s "T") + 1)%Z); *)
(*     CChoice (const (1#4)) *)
(*       (fun b => if b then *)
(*                gaussian "g" 2; *)
(*                "h" <-- (fun s => (as_int (s "h") + as_int (s "g") + 5)%Z) *)
(*              else *)
(*                skip); *)
(*     "t" <-- (fun s => (as_int (s "t") + 1)%Z) *)
(*   end; *)
(* (* obs (fun s => Z.leb 20 (as_int (s "T")) && Z.leb (as_int (s "T")) 40) *) *)
(* obs (fun s => Z.leb 200 (as_int (s "T"))) *)
(*   (* obs (fun s => true) *) *)
(* . *)

(* Definition hare_tortoise : cpGCL := *)
(*   gauss "mu" 0 5; *)
(*   gauss' "t0" (fun s => as_int (s "mu")) 2; *)
(*   "T" <-- 0%Z; *)
(*   "h" <-- 0%Z; *)
(*   "t" <-- (fun s => s "t0"); *)
(*   while (fun s => Z.ltb (as_int (s "h")) (as_int (s "T"))) do *)
(*     "T" <-- (fun s => (as_int (s "T") + 1)%Z); *)
(*     CChoice (const (1#4)) *)
(*       (fun b => if b then *)
(*                gaussian "g" 2; *)
(*                "h" <-- (fun s => (as_int (s "h") + as_int (s "g") + 5)%Z) *)
(*              else *)
(*                skip); *)
(*     "t" <-- (fun s => (as_int (s "t") + 1)%Z) *)
(*   end; *)
(* (* obs (fun s => Z.leb 20 (as_int (s "T")) && Z.leb (as_int (s "T")) 40) *) *)
(*   obs (fun s => Z.leb 40 (as_int (s "T"))) *)
(*   (* obs (fun s => true) *) *)
(* . *)

Definition unif (x : string) (e : St -> nat) : cpGCL :=
  CUniform e (fun n => x <-- Z.of_nat n).

Definition hare_tortoise : cpGCL :=
  unif "t0" (const 10%nat);
  "t" <-- (fun s => s "t0");
  "h" <-- 0%Z;
  "time" <-- 0%Z;
  while (fun s => Z.ltb (as_int (s "h")) (as_int (s "t"))) do
    "t" <-- (fun s => (as_int (s "t") + 1)%Z);
    CChoice (const (2#5))
      (fun b => if b then
               gauss' "g" (const 4%Z) 2;
               "h" <-- (fun s => (as_int (s "h") + as_int (s "g"))%Z)
             else
               skip);
    "time" <-- (fun s => (as_int (s "time") + 1)%Z)
  end;
  obs (fun s => true).
  (* obs (fun s => Z.leb 20 (as_int (s "time"))). *)
  (* obs (fun s => Z.leb (as_int (s "time")) 10). *)

From Coq Require Import ExtrOcamlBasic ExtrOcamlString.

Definition sampler : itree boolE Z :=
  ITree.map (fun s => as_int (s "t0"))
    (cpGCL_to_itree hare_tortoise empty).
Extraction "extract/hare/sampler.ml" sampler.
