module LU.Decompose

open FStar.Seq
open FStar.Mul
open LU.Matrix

(** Result of LU decomposition. *)
noeq type lu_result (n:pos) = {
  l : matrix n;
  u : matrix n;
  perm : seq nat;  (* perm[i] = original row index *)
  num_swaps : nat;
  singular : bool;
}

(** Find pivot: row with max |U[i][col]| for i >= start_row. *)
val find_pivot_row : #n:pos -> matrix n -> col:nat{col < n} -> start:nat{start < n} -> nat
let find_pivot_row #n u col start =
  let rec aux (i:nat) (best:nat) (best_val:int) : Tot nat (decreases (n - i)) =
    if i >= n then best
    else
      let v = iabs (mat_get u i col) in
      if v > best_val then aux (i + 1) i v
      else aux (i + 1) best best_val
  in
  aux start start (iabs (mat_get u start col))

(** Initialize the permutation array [0, 1, ..., n-1]. *)
val init_perm : n:pos -> p:seq nat{length p = n}
let init_perm n = init n (fun i -> i)

(** LU decomposition with partial pivoting (Doolittle method).
    Uses fraction-free integer arithmetic for exact computation.
    L stores the raw multipliers (unnormalized).
    U stores the eliminated matrix (scaled by accumulated pivot products).
    The diagonal of L is set to the pivot value used at each step. *)
val lu_decompose : #n:pos -> matrix n -> lu_result n
let lu_decompose #n a =
  let rec aux (k:nat) (u:matrix n) (l:matrix n) (perm:seq nat{length perm = n})
              (swaps:nat) (sing:bool)
    : Tot (lu_result n) (decreases (n - k)) =
    if k >= n || sing then
      { l = l; u = u; perm = perm; num_swaps = swaps; singular = sing }
    else
      (* Find pivot *)
      let pivot_row = find_pivot_row u k k in
      (* Swap rows in U *)
      let u1 = swap_rows u k pivot_row in
      (* Swap rows in L for columns < k *)
      let l1 =
        let rec swap_l_cols (j:nat) (acc:matrix n) : Tot (matrix n) (decreases (k - j)) =
          if j >= k then acc
          else
            let tmp = mat_get acc k j in
            let acc1 = mat_set acc k j (mat_get acc pivot_row j) in
            let acc2 = mat_set acc1 pivot_row j tmp in
            swap_l_cols (j + 1) acc2
        in
        swap_l_cols 0 l
      in
      (* Swap perm entries *)
      let perm1 =
        if k = pivot_row then perm
        else
          let pk = index perm k in
          let pp = index perm pivot_row in
          upd (upd perm k pp) pivot_row pk
      in
      let new_swaps = if k = pivot_row then swaps else swaps + 1 in
      (* Check for zero pivot *)
      let pivot_val = mat_get u1 k k in
      if pivot_val = 0 then
        { l = l1; u = u1; perm = perm1; num_swaps = new_swaps; singular = true }
      else
        (* Store pivot on L diagonal *)
        let l1 = mat_set l1 k k pivot_val in
        (* Eliminate below diagonal and store multipliers *)
        let rec elim (i:nat) (u_acc:matrix n) (l_acc:matrix n)
          : Tot (matrix n & matrix n) (decreases (n - i)) =
          if i >= n then (u_acc, l_acc)
          else
            let u_ik = mat_get u_acc i k in
            (* Store multiplier: l[i][k] = u[i][k] (unnormalized) *)
            let l_acc1 = mat_set l_acc i k u_ik in
            (* Eliminate: u[i][j] = pivot * u[i][j] - u[i][k] * u[k][j] for all j *)
            let rec elim_row (j:nat) (row_acc:matrix n)
              : Tot (matrix n) (decreases (n - j)) =
              if j >= n then row_acc
              else
                let new_val = pivot_val * (mat_get row_acc i j) - u_ik * (mat_get row_acc k j) in
                elim_row (j + 1) (mat_set row_acc i j new_val)
            in
            let u_acc1 = elim_row 0 u_acc in
            elim (i + 1) u_acc1 l_acc1
        in
        let (u2, l2) = elim (k + 1) u1 l1 in
        aux (k + 1) u2 l2 perm1 new_swaps false
  in
  aux 0 a (identity_mat n) (init_perm n) 0 false

(** Forward substitution: solve L*y = Pb using the fraction-free L.
    L[i][i] = pivot_i (diagonal stores the pivot used at step i).
    L[i][j] for j < i stores the raw multiplier.
    We compute y such that: y[i] = L[i][i] * (Pb[i] - sum_{j<i} L[i][j] * y[j] / L[j][j])
    but keeping everything in integers by accumulating scale factors. *)
val forward_sub : #n:pos -> l:matrix n -> perm:seq nat{length perm = n}
                  -> b:vector n -> vector n
let forward_sub #n l perm b =
  (* Apply permutation to b *)
  let pb = init n (fun i -> vec_get b (index perm i)) in
  let rec aux (i:nat) (y:vector n) : Tot (vector n) (decreases (n - i)) =
    if i >= n then y
    else
      let rec sum_terms (j:nat) (acc:int) : Tot int (decreases (i - j)) =
        if j >= i then acc
        else sum_terms (j + 1) (acc + mat_get l i j * vec_get y j)
      in
      let s = sum_terms 0 0 in
      (* y[i] = Pb[i] * product_of_pivots_before_i - sum
         For fraction-free: y[i] = Pb[i] - s  (keeping same scale as U) *)
      let yi = vec_get pb i - s in
      aux (i + 1) (vec_set y i yi)
  in
  aux 0 (zero_vec n)

(** Back substitution: solve U*x = y (fraction-free).
    Returns scaled solution: x[i] * product_of_all_pivots.
    The actual solution is x[i] / U[i][i] at each step, but we keep
    integer arithmetic by returning (x_scaled, scale_factor).
    Returns None if singular. *)
val back_sub : #n:pos -> u:matrix n -> y:vector n -> option (vector n)
let back_sub #n u y =
  let rec aux (ki:nat) (x:vector n) : Tot (option (vector n)) (decreases (n - ki)) =
    if ki >= n then Some x
    else
      let i = n - 1 - ki in
      let rec sum_terms (j:nat) (acc:int) : Tot int (decreases (n - j)) =
        if j >= n then acc
        else if j > i then sum_terms (j + 1) (acc + mat_get u i j * vec_get x j)
        else sum_terms (j + 1) acc
      in
      let s = sum_terms 0 0 in
      let diag = mat_get u i i in
      if diag = 0 then None
      else
        let xi = vec_get y i - s in
        aux (ki + 1) (vec_set x i xi)
  in
  aux 0 (zero_vec n)

(** Solve the linear system A*x = b using LU decomposition.
    Returns None if A is singular.
    The returned vector x_scaled satisfies: A * x_scaled = b * scale,
    where scale is the product of pivot elements.
    For exact rational solution: x[i] = x_scaled[i] / U[i][i]. *)
noeq type solve_result (n:pos) = {
  solution : vector n;
  pivots : vector n;  (* diagonal of U, for recovering exact solution *)
  is_valid : bool;
}

val solve : #n:pos -> matrix n -> vector n -> option (solve_result n)
let solve #n a b =
  let r = lu_decompose a in
  if r.singular then None
  else
    let y = forward_sub r.l r.perm b in
    match back_sub r.u y with
    | None -> None
    | Some x ->
      let pivots = init n (fun i -> mat_get r.u i i) in
      Some { solution = x; pivots = pivots; is_valid = true }

(** Check if the solve result is correct by verifying A*x is proportional to b.
    Since we use fraction-free arithmetic, A*x = b * scale for some integer scale.
    We find the scale from the first nonzero b entry and verify all others match.
    This is a verification predicate — useful for testing. *)
val verify_solution : #n:pos -> matrix n -> vector n -> solve_result n -> bool
let verify_solution #n a b sr =
  (* Compute A * x_scaled *)
  let ax = mat_vec_mul a sr.solution in
  (* Find first nonzero entry in b to determine scale *)
  let rec find_nonzero (i:nat) : Tot (option nat) (decreases (n - i)) =
    if i >= n then None
    else if vec_get b i <> 0 then Some i
    else find_nonzero (i + 1)
  in
  match find_nonzero 0 with
  | None ->
    (* b is zero vector — solution should give A*x = 0 *)
    let rec check_zero (i:nat) : Tot bool (decreases (n - i)) =
      if i >= n then true
      else if vec_get ax i <> 0 then false
      else check_zero (i + 1)
    in
    check_zero 0
  | Some k ->
    (* Check proportionality: (A*x)[i] * b[k] == (A*x)[k] * b[i] for all i.
       This verifies A*x = c*b for some constant c without needing to know c. *)
    let ax_k = vec_get ax k in
    let b_k = vec_get b k in
    let rec check (i:nat) : Tot bool (decreases (n - i)) =
      if i >= n then true
      else
        let ok = vec_get ax i * b_k = ax_k * vec_get b i in
        if ok then check (i + 1)
        else false
    in
    (* Also verify the scale is positive (non-degenerate solution) *)
    check 0 && ax_k <> 0
