(** Here we test the conversion functions z_of_int and int_of_z and
    check that samplers can build and run successfully. *)

open Alcotest
open QCheck_alcotest
open Zar.Core
open Zar.Samplers

(** Number of samples per QCheck test. *)
let gen_count = 10000

(** Lower and upper bounds on randomly generated ints. Divide by two
    to prevent overflow in 'double_z_of_int' and 'z_of_int_plus'
    tests. *)
let bound = Int.max_int / 2

let tests = ref []
let add_test nm t = tests := !tests @ [Alcotest.test_case nm `Quick t]
let add_qcheck t = tests := !tests @ [to_alcotest t]

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
let pos_gen =
  let open QCheck.Gen in
  sized_size (int_bound 61) @@ fix (fun self n ->
               match n with
               | 0 -> return XH
               | _ -> frequency [1, return XH;
                                 10, map (fun x -> XO x) (self (n - 1));
                                 10, map (fun x -> XI x) (self (n - 1))])
let z_gen =
  let open QCheck.Gen in
  oneof [return Z0; map (fun x -> Zpos x) pos_gen;
         map (fun x -> Zneg x) pos_gen]
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
           QCheck.Test.make ~name:"z_of_int_int_of_z" ~count:gen_count
             arbitrary_z
             (fun n -> z_of_int (int_of_z n) = n)

(** int_of_z ∘ z_of_int = id *)
let () = add_qcheck @@
           QCheck.(Test.make ~name:"int_of_z_z_of_int" ~count:gen_count
                     (int_range (-bound) bound)
                     (fun n -> int_of_z (z_of_int n) = n))

(** ∀ n m, z_of_int n + z_of_int m = z_of_int (n + m) *)
let () = add_qcheck @@
           QCheck.(Test.make ~name:"z_of_int_plus" ~count:gen_count
                     (pair (int_range (-bound) bound) (int_range (-bound) bound))
                     (fun (n, m) -> Z.add (z_of_int n) (z_of_int m)
                                    = z_of_int (n + m)))

(** ∀ n m, int_of_z n + int_of_z m = int_of_z (n + m) *)
let () = add_qcheck @@
           QCheck.(Test.make ~name:"int_of_z_plus" ~count:gen_count
                     (pair arbitrary_z arbitrary_z)
                     (fun (n, m) -> int_of_z n + int_of_z m
                                    = int_of_z (Z.add n m)))

let () = add_qcheck @@
           QCheck.(Test.make ~name:"int_of_z_double" ~count:gen_count
                     arbitrary_z
                     (fun n -> int_of_z (Z.double n) = 2 * int_of_z n))

let () = add_qcheck @@
           QCheck.(Test.make ~name:"double_z_of_int" ~count:gen_count
                     (int_range (-bound) bound)
                     (fun n -> Z.double (z_of_int n) = z_of_int (2 * n)))

let () = add_qcheck @@
           QCheck.(Test.make ~name:"lt_int_of_z" ~count:gen_count
                     (pair arbitrary_z arbitrary_z)
                     (fun (n, m) -> Z.ltb n m == (int_of_z n < int_of_z m)))

let () = add_qcheck @@
           QCheck.(Test.make ~name:"z_of_int_lt" ~count:gen_count
                     (pair (int_range (-bound) (bound))
                        (int_range (-bound) (bound)))
                     (fun (n, m) -> n < m == Z.ltb (z_of_int n) (z_of_int m)))

(** Run unit tests. *)
let () = Alcotest.run "zar" [ "zar", !tests ]

(** Check that samplers can build and run. *)
let () =
  Zar.Core.seed ();
  
  (* Coin. *)
  Zar.Coin.build 2 3;
  print_endline @@ string_of_bool @@ Zar.Coin.flip ();
  print_endline @@ string_of_int @@ List.length @@
    List.filter (fun b -> b) @@ Zar.Coin.flips 1000;

  (* Die. *)
  Zar.Die.build 100;
  print_endline @@ string_of_int @@ Zar.Die.roll ();
  print_endline @@ string_of_int @@ List.fold_right (+) (Zar.Die.rolls 1000) 0;

  (* Findist. *)
  Zar.Findist.build [1; 2; 3; 4; 5];
  print_endline @@ string_of_int @@ Zar.Findist.sample ();
  print_endline @@ string_of_int @@ List.fold_right (+) (Zar.Findist.samples 1000) 0
