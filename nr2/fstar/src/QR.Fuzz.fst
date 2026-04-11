module QR.Fuzz

open FStar.Seq
open FStar.Mul
open QR.Matrix
open QR.Decompose

(* ================================================================
   PSEUDO-RANDOM NUMBER GENERATOR
   Simple linear congruential generator for reproducible fuzzing.
   Uses integer arithmetic throughout.
   ================================================================ *)

(** PRNG state — a single integer seed. *)
type prng_state = nat

(** Advance the PRNG (LCG with modulus 2^31 - 1). *)
val prng_next : prng_state -> prng_state & int
let prng_next s =
  let a = 1103515245 in
  let c = 12345 in
  let m = 2147483647 in
  let s' = (a * s + c) % m in
  (s', s')

(** Generate a random integer in [lo, hi). *)
val rand_int : prng_state -> lo:int -> hi:int{hi > lo} -> prng_state & int
let rand_int s lo hi =
  let (s', v) = prng_next s in
  let range = hi - lo in
  let v_abs = if v < 0 then -v else v in
  let r = lo + (v_abs % range) in
  (s', r)

(* ================================================================
   MATRIX GENERATORS
   ================================================================ *)

(** Generate a random n x n matrix with entries in [lo, hi). *)
val rand_matrix : n:pos -> prng_state -> lo:int -> hi:int{hi > lo} -> prng_state & matrix n
let rand_matrix n s lo hi =
  let rec fill_rows (i:nat) (s_acc:prng_state) (m:matrix n)
    : Tot (prng_state & matrix n) (decreases (n - i)) =
    if i >= n then (s_acc, m)
    else
      let rec fill_cols (j:nat) (s_inner:prng_state) (m_inner:matrix n)
        : Tot (prng_state & matrix n) (decreases (n - j)) =
        if j >= n then (s_inner, m_inner)
        else
          let (s', v) = rand_int s_inner lo hi in
          fill_cols (j + 1) s' (mat_set m_inner i j v)
      in
      let (s', m') = fill_cols 0 s_acc m in
      fill_rows (i + 1) s' m'
  in
  fill_rows 0 s (zero_mat n)

(** Generate a diagonally dominant n x n matrix (guaranteed non-singular). *)
val rand_diag_dominant : n:pos -> prng_state -> prng_state & matrix n
let rand_diag_dominant n s =
  let (s1, m) = rand_matrix n s (-10) 11 in
  let rec fix_diag (i:nat) (m_acc:matrix n) : Tot (matrix n) (decreases (n - i)) =
    if i >= n then m_acc
    else
      let rec row_abs_sum (j:nat) (acc:int) : Tot int (decreases (n - j)) =
        if j >= n then acc
        else if j = i then row_abs_sum (j + 1) acc
        else row_abs_sum (j + 1) (acc + iabs (mat_get m_acc i j))
      in
      let diag_val = row_abs_sum 0 0 + 1 in
      fix_diag (i + 1) (mat_set m_acc i i diag_val)
  in
  (s1, fix_diag 0 m)

(** Generate a random vector with entries in [lo, hi). *)
val rand_vector : n:pos -> prng_state -> lo:int -> hi:int{hi > lo} -> prng_state & vector n
let rand_vector n s lo hi =
  let rec aux (i:nat) (s_acc:prng_state) (v:vector n)
    : Tot (prng_state & vector n) (decreases (n - i)) =
    if i >= n then (s_acc, v)
    else
      let (s', val_) = rand_int s_acc lo hi in
      aux (i + 1) s' (vec_set v i val_)
  in
  aux 0 s (zero_vec n)

(* ================================================================
   FUZZ TEST PREDICATES
   ================================================================ *)

(** Check that R is upper triangular. *)
val check_upper_tri : #n:pos -> matrix n -> bool
let check_upper_tri #n r =
  let rec aux (i:nat) : Tot bool (decreases (n - i)) =
    if i >= n then true
    else
      let rec check_row (j:nat) : Tot bool (decreases (i - j)) =
        if j >= i then true
        else if mat_get r i j <> 0 then false
        else check_row (j + 1)
      in
      if check_row 0 then aux (i + 1)
      else false
  in
  aux 0

(** Check that Q columns are orthogonal: dot(q_i, q_j) = 0 for i != j. *)
val check_orthogonal : #n:pos -> matrix n -> bool
let check_orthogonal #n q =
  let rec aux_i (i:nat) : Tot bool (decreases (n - i)) =
    if i >= n then true
    else
      let rec aux_j (j:nat) : Tot bool (decreases (n - j)) =
        if j >= n then true
        else if j = i then aux_j (j + 1)
        else
          let col_i = get_col q i in
          let col_j = get_col q j in
          if dot_product col_i col_j <> 0 then false
          else aux_j (j + 1)
      in
      if aux_j 0 then aux_i (i + 1)
      else false
  in
  aux_i 0

(** Check that a decomposition is valid: not singular, R upper triangular, Q orthogonal. *)
val check_decompose : #n:pos -> matrix n -> bool
let check_decompose #n a =
  let r = qr_decompose a in
  if r.singular then false
  else check_upper_tri r.r && check_orthogonal r.q

(** Fuzz test: decompose random diagonally dominant matrices. *)
val fuzz_decompose : n:pos -> num_trials:nat -> prng_state -> nat & nat & prng_state
let fuzz_decompose n num_trials s =
  let rec aux (t:nat) (passes:nat) (s_acc:prng_state)
    : Tot (nat & nat & prng_state) (decreases (num_trials - t)) =
    if t >= num_trials then (passes, num_trials, s_acc)
    else
      let (s', m) = rand_diag_dominant n s_acc in
      let ok = check_decompose m in
      aux (t + 1) (if ok then passes + 1 else passes) s'
  in
  aux 0 0 s

(** Fuzz test: solve random systems A*x = b and verify. *)
val fuzz_solve : n:pos -> num_trials:nat -> prng_state -> nat & nat & prng_state
let fuzz_solve n num_trials s =
  let rec aux (t:nat) (passes:nat) (s_acc:prng_state)
    : Tot (nat & nat & prng_state) (decreases (num_trials - t)) =
    if t >= num_trials then (passes, num_trials, s_acc)
    else
      let (s1, m) = rand_diag_dominant n s_acc in
      let (s2, b) = rand_vector n s1 (-10) 11 in
      let ok = match solve m b with
        | None -> false
        | Some sr -> verify_solution m b sr
      in
      aux (t + 1) (if ok then passes + 1 else passes) s2
  in
  aux 0 0 s

(** Run all fuzz tests across matrix sizes. *)
val run_fuzz : unit -> nat & nat
let run_fuzz () =
  let seed : prng_state = 42 in
  let sizes : list pos = [2; 3; 4; 5] in
  let trials_per_size = 50 in
  let rec run_sizes (ss:list pos) (total_pass:nat) (total_tests:nat) (s:prng_state)
    : Tot (nat & nat) (decreases ss) =
    match ss with
    | [] -> (total_pass, total_tests)
    | n :: rest ->
      let (dp, dt, s1) = fuzz_decompose n trials_per_size s in
      let (sp, st, s2) = fuzz_solve n trials_per_size s1 in
      run_sizes rest (total_pass + dp + sp) (total_tests + dt + st) s2
  in
  run_sizes sizes 0 0 seed
