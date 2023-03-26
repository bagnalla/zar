open Alcotest
open QCheck_alcotest
open Zar.Core
open Zar.Samplers

let tests = ref []
let add_test nm t = tests := !tests @ [Alcotest.test_case nm `Quick t]
let add_qcheck t = tests := !tests @ [to_alcotest t]

(* (\** Test nats. *\) *)

(* let rec string_of_nat : nat -> string = function *)
(*   | O -> "O" *)
(*   | S n' -> "S " ^ string_of_nat n' *)
(* let nat : nat testable = *)
(*   let pp_nat ppf x = Fmt.pf ppf "%s" (string_of_nat x) in *)
(*   testable pp_nat ( = ) *)
(* let nat_gen = QCheck.Gen.(map nat_of_int (int_bound 1000)) *)
(* let arbitrary_nat = *)
(*   let open QCheck.Iter in *)
(*   let shrink_nat = function *)
(*     | O -> empty *)
(*     | S n -> return n *)
(*   in *)
(*   QCheck.make nat_gen ~print:string_of_nat ~shrink:shrink_nat *)

(* (\** A few nats for testing. *\) *)
(* let one = S O *)
(* let two = S one *)
(* let three = S two *)
(* let four = S three *)
(* let five = S four *)

(* let () = add_test "int_of_nat" @@ *)
(*            fun _ -> *)
(*            (check int) "" 1 (int_of_nat one); *)
(*            (check int) "" 2 (int_of_nat two); *)
(*            (check int) "" 3 (int_of_nat three); *)
(*            (check int) "" 4 (int_of_nat four); *)
(*            (check int) "" 5 (int_of_nat five); *)
(*            (check int) "" 20 (int_of_nat @@ Nat.mul five four) *)

(* let () = add_test "nat_of_int" @@ *)
(*            fun _ -> *)
(*            (check nat) "" one (nat_of_int 1); *)
(*            (check nat) "" two (nat_of_int 2); *)
(*            (check nat) "" three (nat_of_int 3); *)
(*            (check nat) "" four (nat_of_int 4); *)
(*            (check nat) "" five (nat_of_int 5); *)
(*            (check nat) "" (Nat.mul five five) (nat_of_int 25) *)

(* (\** nat_of_int ∘ int_of_nat = id *\) *)
(* let () = add_qcheck @@ *)
(*            QCheck.Test.make ~name:"nat_of_int_int_of_nat" ~count:1000 *)
(*              arbitrary_nat (fun n -> nat_of_int (int_of_nat n) = n) *)

(* (\** int_of_nat ∘ nat_of_int = id *\) *)
(* let () = add_qcheck @@ *)
(*            QCheck.(Test.make ~name:"int_of_nat_nat_of_int" ~count:1000 *)
(*                      (int_bound 1000) *)
(*                      (fun n -> int_of_nat (nat_of_int n) = n)) *)

(* (\** ∀ n m, nat_of_int n + nat_of_int m = nat_of_int (n + m) *\) *)
(* let () = add_qcheck @@ *)
(*            QCheck.(Test.make ~name:"nat_of_int_plus" ~count:1000 *)
(*                      (pair (int_bound 1000) (int_bound 1000)) *)
(*                      (fun (n, m) -> add (nat_of_int n) (nat_of_int m) *)
(*                                     = nat_of_int (n + m))) *)

(* (\** ∀ n m, int_of_nat n + int_of_nat m = int_of_nat (n + m) *\) *)
(* let () = add_qcheck @@ *)
(*            QCheck.(Test.make ~name:"int_of_nat_plus" ~count:1000 *)
(*                      (pair arbitrary_nat arbitrary_nat) *)
(*                      (fun (n, m) -> int_of_nat n + int_of_nat m *)
(*                                     = int_of_nat (add n m))) *)

(* (\** Test positives. *\) *)

(* let rec string_of_positive : positive -> string = function *)
(*   | XH -> "XH" *)
(*   | XO p -> "XO " ^ string_of_positive p *)
(*   | XI p -> "XI " ^ string_of_positive p *)
(* let positive : positive testable = *)
(*   let pp_positive ppf x = Fmt.pf ppf "%s" (string_of_positive x) in *)
(*   testable pp_positive ( = ) *)
(* let positive_gen = QCheck.Gen.(map positive_of_int (int_range 1 1000)) *)
(* let shrink_positive = function *)
(*   | XH -> QCheck.Iter.empty *)
(*   | XO p -> QCheck.Iter.return p *)
(*   | XI p -> QCheck.Iter.return p *)
(* let arbitrary_positive = *)
(*   QCheck.make positive_gen ~print:string_of_positive ~shrink:shrink_positive *)

(* (\** A few positives for testing. *\) *)
(* let one = XH *)
(* let two = XO one *)
(* let three = XI one *)
(* let four = XO two *)
(* let five = XI two *)

(* let () = add_test "int_of_positive" @@ *)
(*            fun _ -> *)
(*            (check int) "" 1 (int_of_positive one); *)
(*            (check int) "" 2 (int_of_positive two); *)
(*            (check int) "" 3 (int_of_positive three); *)
(*            (check int) "" 4 (int_of_positive four); *)
(*            (check int) "" 5 (int_of_positive five); *)
(*            (check int) "" 9 (int_of_positive @@ Pos.add five four) *)

(* let () = add_test "positive_of_int" @@ *)
(*            fun _ -> *)
(*            (check positive) "" one (positive_of_int 1); *)
(*            (check positive) "" two (positive_of_int 2); *)
(*            (check positive) "" three (positive_of_int 3); *)
(*            (check positive) "" four (positive_of_int 4); *)
(*            (check positive) "" five (positive_of_int 5); *)
(*            (check positive) "" (Pos.add four five) (positive_of_int 9) *)

(* (\** ∀ p, 0 < int_of_positive p *\) *)
(* let () = add_qcheck @@ *)
(*            QCheck.Test.make ~name:"0_lt_int_of_positive" ~count:1000 *)
(*              arbitrary_positive (fun n -> 0 < int_of_positive n) *)

(* (\** positive_of_int ∘ int_of_positive = id *\) *)
(* let () = add_qcheck @@ *)
(*            QCheck.Test.make ~name:"positive_of_int_int_of_positive" ~count:1000 *)
(*              arbitrary_positive *)
(*              (fun n -> positive_of_int (int_of_positive n) = n) *)

(* (\** int_of_positive ∘ positive_of_int = id *\) *)
(* let () = add_qcheck @@ *)
(*            QCheck.(Test.make ~name:"int_of_positive_positive_of_int" ~count:1000 *)
(*                      (int_range 1 1000) *)
(*                      (fun n -> int_of_positive (positive_of_int n) = n)) *)

(* (\** ∀ n m, positive_of_int n + positive_of_int m = positive_of_int (n + m) *\) *)
(* let () = add_qcheck @@ *)
(*            QCheck.(Test.make ~name:"positive_of_int_plus" ~count:1000 *)
(*                      (pair (int_range 1 1000) (int_range 1 1000)) *)
(*                      (fun (n, m) -> Pos.add (positive_of_int n) (positive_of_int m) *)
(*                                     = positive_of_int (n + m))) *)

(* (\** ∀ n m, int_of_positive n + int_of_positive m = int_of_positive (n + m) *\) *)
(* let () = add_qcheck @@ *)
(*            QCheck.(Test.make ~name:"int_of_positive_plus" ~count:1000 *)
(*                      (pair arbitrary_positive arbitrary_positive) *)
(*                      (fun (n, m) -> int_of_positive n + int_of_positive m *)
(*                                     = int_of_positive (Pos.add n m))) *)

(** Test integers. *)

let rec string_of_positive : positive -> string = function
  | XH -> "XH"
  | XO p -> "XO " ^ string_of_positive p
  | XI p -> "XI " ^ string_of_positive p
let string_of_z : z -> string = function
  | Z0 -> "Z0"
  | Zpos p -> "Zpos " ^ string_of_positive p
  | Zneg p -> "Zneg " ^ string_of_positive p
let z : z testable =
  let pp_z ppf x = Fmt.pf ppf "%s" (string_of_z x) in
  testable pp_z ( = )
let z_gen = QCheck.Gen.(map z_of_int (int_range (-1000) 1000))
let arbitrary_z =
  let open QCheck.Iter in
  let shrink_positive = function
  | XH -> QCheck.Iter.empty
  | XO p -> QCheck.Iter.return p
  | XI p -> QCheck.Iter.return p
  in
  let shrink_z = function
    | Z0 -> empty
    | Zpos p -> let* x = shrink_positive p in return (Zpos x)
    | Zneg p -> let* x = shrink_positive p in return (Zneg x)
  in
  QCheck.make z_gen ~print:string_of_z ~shrink:shrink_z

(** A few positives for testing. *)
let one = XH
let two = XO one
let three = XI one
let four = XO two
let five = XI two

let () = add_test "int_of_z" @@
           fun _ ->
           (check int) "" 0 (int_of_z Z0);
           (check int) "" 1 (int_of_z (Zpos one));
           (check int) "" 2 (int_of_z (Zpos two));
           (check int) "" 3 (int_of_z (Zpos three));
           (check int) "" 4 (int_of_z (Zpos four));
           (check int) "" 5 (int_of_z (Zpos five));
           (check int) "" (-1) (int_of_z (Zneg one));
           (check int) "" (-2) (int_of_z (Zneg two));
           (check int) "" (-3) (int_of_z (Zneg three));
           (check int) "" (-4) (int_of_z (Zneg four));
           (check int) "" (-5) (int_of_z (Zneg five))

let () = add_test "z_of_int" @@
           fun _ ->
           (check z) "" Z0 (z_of_int 0);
           (check z) "" (Zpos one) (z_of_int 1);
           (check z) "" (Zpos two) (z_of_int 2);
           (check z) "" (Zpos three) (z_of_int 3);
           (check z) "" (Zpos four) (z_of_int 4);
           (check z) "" (Zpos five) (z_of_int 5);
           (check z) "" (Zneg one) (z_of_int (-1));
           (check z) "" (Zneg two) (z_of_int (-2));
           (check z) "" (Zneg three) (z_of_int (-3));
           (check z) "" (Zneg four) (z_of_int (-4));
           (check z) "" (Zneg five) (z_of_int (-5))

(** z_of_int ∘ int_of_z = id *)
let () = add_qcheck @@
           QCheck.Test.make ~name:"z_of_int_int_of_z" ~count:1000
             arbitrary_z
             (fun n -> z_of_int (int_of_z n) = n)

(** int_of_z ∘ z_of_int = id *)
let () = add_qcheck @@
           QCheck.(Test.make ~name:"int_of_z_z_of_int" ~count:1000
                     (int_range (-1000) 1000)
                     (fun n -> int_of_z (z_of_int n) = n))

(** ∀ n m, z_of_int n + z_of_int m = z_of_int (n + m) *)
let () = add_qcheck @@
           QCheck.(Test.make ~name:"z_of_int_plus" ~count:1000
                     (pair (int_range (-1000) 1000) (int_range (-1000) 1000))
                     (fun (n, m) -> Z.add (z_of_int n) (z_of_int m)
                                    = z_of_int (n + m)))

(** ∀ n m, int_of_z n + int_of_z m = int_of_z (n + m) *)
let () = add_qcheck @@
           QCheck.(Test.make ~name:"int_of_z_plus" ~count:1000
                     (pair arbitrary_z arbitrary_z)
                     (fun (n, m) -> int_of_z n + int_of_z m
                                    = int_of_z (Z.add n m)))

let () = add_test "int_of_z" @@
           fun _ ->
           (check int) "" 0 (int_of_z Z0);
           (check int) "" 1 (int_of_z (Zpos one));
           (check int) "" 2 (int_of_z (Zpos two));
           (check int) "" 3 (int_of_z (Zpos three));
           (check int) "" 4 (int_of_z (Zpos four));
           (check int) "" 5 (int_of_z (Zpos five));
           (check int) "" (-1) (int_of_z (Zneg one));
           (check int) "" (-2) (int_of_z (Zneg two));
           (check int) "" (-3) (int_of_z (Zneg three));
           (check int) "" (-4) (int_of_z (Zneg four));
           (check int) "" (-5) (int_of_z (Zneg five))


(** Run unit tests. *)
let () = Alcotest.run "zar" [ "zar", !tests ]

(** Test samplers. *)
let () =
  Zar.Core.seed ();
  
  (* Coin. *)
  Zar.Coin.build 2 3;
  print_endline @@ string_of_bool @@ Zar.Coin.flip ();

  (* Die. *)
  Zar.Die.build 100;
  print_endline @@ string_of_int @@ Zar.Die.roll ();

  (* Findist. *)
  Zar.Findist.build [1; 2; 3; 4; 5];
  print_endline @@ string_of_int @@ Zar.Findist.sample ()
