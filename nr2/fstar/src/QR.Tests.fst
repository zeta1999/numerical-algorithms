module QR.Tests

open FStar.Seq
open FStar.Mul
open QR.Matrix
open QR.Decompose

(** Helper: create a 2x2 matrix from values. *)
let mat2x2 (a b c d : int) : matrix 2 =
  let r0 = append (create 1 a) (create 1 b) in
  let r1 = append (create 1 c) (create 1 d) in
  append (create 1 r0) (create 1 r1)

(** Helper: create a 3x3 matrix from values. *)
let mat3x3 (a b c d e f g h i : int) : matrix 3 =
  let r0 = append (append (create 1 a) (create 1 b)) (create 1 c) in
  let r1 = append (append (create 1 d) (create 1 e)) (create 1 f) in
  let r2 = append (append (create 1 g) (create 1 h)) (create 1 i) in
  append (append (create 1 r0) (create 1 r1)) (create 1 r2)

(** Helper: create a 2-vector. *)
let vec2 (a b : int) : vector 2 =
  append (create 1 a) (create 1 b)

(** Helper: create a 3-vector. *)
let vec3 (a b c : int) : vector 3 =
  append (append (create 1 a) (create 1 b)) (create 1 c)

(* ================================================================
   DECOMPOSITION TESTS
   ================================================================ *)

(** Test: identity matrix decomposition should not be singular. *)
let test_identity_2x2 () : bool =
  let a = identity_mat 2 in
  let r = qr_decompose a in
  not r.singular

(** Test: simple 2x2 matrix should not be singular. *)
let test_simple_2x2 () : bool =
  let a = mat2x2 2 1 4 3 in
  let r = qr_decompose a in
  not r.singular

(** Test: singular matrix should be detected. *)
let test_singular_2x2 () : bool =
  let a = mat2x2 1 2 2 4 in
  let r = qr_decompose a in
  r.singular

(** Test: 3x3 non-singular matrix. *)
let test_3x3 () : bool =
  let a = mat3x3 1 2 3 4 5 6 7 8 10 in
  let r = qr_decompose a in
  not r.singular

(** Test: R should be upper triangular for 2x2. *)
let test_upper_tri_2x2 () : bool =
  let a = mat2x2 2 1 4 3 in
  let r = qr_decompose a in
  if r.singular then false
  else mat_get r.r 1 0 = 0

(** Test: R should be upper triangular for 3x3. *)
let test_upper_tri_3x3 () : bool =
  let a = mat3x3 1 2 3 4 5 6 7 8 10 in
  let r = qr_decompose a in
  if r.singular then false
  else
    mat_get r.r 1 0 = 0 &&
    mat_get r.r 2 0 = 0 &&
    mat_get r.r 2 1 = 0

(* ================================================================
   END-TO-END SOLVE TESTS
   ================================================================ *)

(** Test: solve 2x2 system A*x = b.
    A = [[2,1],[4,3]], b = [5,11] => x = [2,1].
    Using verify_solution to check A*x_scaled = b*scale. *)
let test_solve_2x2 () : bool =
  let a = mat2x2 2 1 4 3 in
  let b = vec2 5 11 in
  match solve a b with
  | None -> false
  | Some sr -> verify_solution a b sr

(** Test: solve 3x3 system A*x = b.
    A = [[1,2,3],[4,5,6],[7,8,10]], b = [6,15,25] => x = [1,1,1]. *)
let test_solve_3x3 () : bool =
  let a = mat3x3 1 2 3 4 5 6 7 8 10 in
  let b = vec3 6 15 25 in
  match solve a b with
  | None -> false
  | Some sr -> verify_solution a b sr

(** Test: solve identity system I*x = b => x = b. *)
let test_solve_identity () : bool =
  let a = identity_mat 2 in
  let b = vec2 7 3 in
  match solve a b with
  | None -> false
  | Some sr -> verify_solution a b sr

(** Test: solve with negative entries.
    A = [[3,-1],[-2,4]], b = [5,6] *)
let test_solve_negative () : bool =
  let a = mat2x2 3 (-1) (-2) 4 in
  let b = vec2 5 6 in
  match solve a b with
  | None -> false
  | Some sr -> verify_solution a b sr

(** Test: solve should return None for singular matrix. *)
let test_solve_singular () : bool =
  let a = mat2x2 1 2 2 4 in
  let b = vec2 3 6 in
  match solve a b with
  | None -> true
  | Some _ -> false

(** Test: solve 3x3 with larger values.
    A = [[10,2,1],[1,5,1],[2,3,10]], b = [13,7,15] => x = [1,1,1] *)
let test_solve_3x3_large () : bool =
  let a = mat3x3 10 2 1 1 5 1 2 3 10 in
  let b = vec3 13 7 15 in
  match solve a b with
  | None -> false
  | Some sr -> verify_solution a b sr

(* ================================================================
   TEST RUNNER
   ================================================================ *)

(** Run all tests and return number of passes. *)
let run_tests () : nat =
  let results = [
    (* Decomposition tests *)
    test_identity_2x2 ();
    test_simple_2x2 ();
    test_singular_2x2 ();
    test_3x3 ();
    test_upper_tri_2x2 ();
    test_upper_tri_3x3 ();
    (* Solve tests *)
    test_solve_2x2 ();
    test_solve_3x3 ();
    test_solve_identity ();
    test_solve_negative ();
    test_solve_singular ();
    test_solve_3x3_large ()
  ] in
  List.Tot.length (List.Tot.filter (fun b -> b) results)

(** Total number of tests. *)
let total_tests : nat = 12
