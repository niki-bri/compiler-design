open Assert
open Hellocaml

(* These tests are provided by you -- they will NOT be graded *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let provided_tests : suite = [
  Test ("Student-Provided Tests For Problem 1-3", [
    ("case1", assert_eqf (fun () -> prob3_ans) 42 );
    ("case2", assert_eqf (fun () ->(prob3_case2 17)) 25 );
    ("case3", assert_eqf (fun () -> prob3_case3) 64);
  ]);
  
] 
