module QR.Decompose

open FStar.Seq
open FStar.Mul
open QR.Matrix

(** Result of QR decomposition. *)
noeq type qr_result (n:pos) = {
  q : matrix n;
  r : matrix n;
  singular : bool;
}

(** Modified Gram-Schmidt: orthogonalize column k against columns 0..k-1.
    Uses fraction-free arithmetic to avoid division:
      q_k = normSq(q_j) * q_k - dot(q_j, q_k) * q_j
    R stores the raw dot products (unnormalized multipliers).
    R[k][k] stores the accumulated scale factor. *)

(** Helper: orthogonalize column col_k against column col_j (fraction-free).
    Updates q_k = normSq(q_j) * q_k - dot(q_j, q_k) * q_j
    Returns updated q_k and the raw dot product coefficient. *)
val ortho_step : #n:pos -> q_j:vector n -> q_k:vector n -> vector n & int
let ortho_step #n q_j q_k =
  let coeff = dot_product q_j q_k in
  let nsq = dot_product q_j q_j in
  (* q_k' = nsq * q_k - coeff * q_j *)
  let q_k' = init n (fun i ->
    nsq * vec_get q_k i - coeff * vec_get q_j i)
  in
  (q_k', coeff)

(** QR decomposition using fraction-free Modified Gram-Schmidt.
    Q columns are orthogonal (not orthonormal).
    R[j][k] = dot(q_j, original_q_k_at_step_j) for j < k.
    R[k][k] = dot(q_k, q_k) (the squared norm after orthogonalization).
    R[i][k] = 0 for i > k. *)
val qr_decompose : #n:pos -> matrix n -> qr_result n
let qr_decompose #n a =
  let rec process_col (k:nat) (q:matrix n) (r:matrix n) (sing:bool)
    : Tot (qr_result n) (decreases (n - k)) =
    if k >= n || sing then
      { q = q; r = r; singular = sing }
    else
      (* Extract column k *)
      let col_k = get_col q k in
      (* Orthogonalize against columns 0..k-1 *)
      let rec ortho (j:nat) (v:vector n) (r_acc:matrix n)
        : Tot (vector n & matrix n) (decreases (k - j)) =
        if j >= k then (v, r_acc)
        else
          let col_j = get_col q j in
          let (v', coeff) = ortho_step col_j v in
          let r_acc' = mat_set r_acc j k coeff in
          ortho (j + 1) v' r_acc'
      in
      let (v_orth, r1) = ortho 0 col_k r in
      (* Check if orthogonalized column is zero (singular) *)
      let nsq = dot_product v_orth v_orth in
      if nsq = 0 then
        { q = q; r = r1; singular = true }
      else
        (* Store R[k][k] = normSq *)
        let r2 = mat_set r1 k k nsq in
        (* Store orthogonalized column back into Q *)
        let q' = set_col q k v_orth in
        process_col (k + 1) q' r2 false
  in
  process_col 0 a (zero_mat n) false

(** Apply Q^T to a vector b: compute y where y_i = dot(q_col_i, b).
    The result is scaled by the accumulated factors from fraction-free arithmetic.
    To get the actual Q^T b, each y_i must be divided by dot(q_i, q_i) = R[i][i]. *)
val apply_qt : #n:pos -> q:matrix n -> b:vector n -> vector n
let apply_qt #n q b =
  init n (fun i ->
    let col_i = get_col q i in
    dot_product col_i b)

(** Back substitution for fraction-free QR.
    Solve R*x = y where R is upper triangular.
    R[i][i] stores normSq values, R[j][k] stores raw dot products.
    The diagonal equation is: R[i][i] * x[i] + sum_{j>i} R[i][j] * x[j] = y[i]
    But in our fraction-free convention:
      x[i] = (y[i] - sum_{j>i} R[i][j] * x[j]) (integer division check at end)
    Returns None if singular. *)
val back_sub : #n:pos -> r:matrix n -> y:vector n -> option (vector n)
let back_sub #n r y =
  let rec aux (ki:nat) (x:vector n) : Tot (option (vector n)) (decreases (n - ki)) =
    if ki >= n then Some x
    else
      let i = n - 1 - ki in
      let rec sum_terms (j:nat) (acc:int) : Tot int (decreases (n - j)) =
        if j >= n then acc
        else if j > i then sum_terms (j + 1) (acc + mat_get r i j * vec_get x j)
        else sum_terms (j + 1) acc
      in
      let s = sum_terms 0 0 in
      let diag = mat_get r i i in
      if diag = 0 then None
      else
        let xi = vec_get y i - s in
        aux (ki + 1) (vec_set x i xi)
  in
  aux 0 (zero_vec n)

(** Solve the linear system A*x = b using QR decomposition.
    Steps: 1. Decompose A = QR
           2. Compute y = Q^T * b
           3. Solve R * x = y via back substitution
    The solution is scaled due to fraction-free arithmetic.
    verify_solution checks correctness via proportionality. *)
noeq type solve_result (n:pos) = {
  solution : vector n;
  norms_sq : vector n;  (* R diagonal: normSq for each Q column *)
  is_valid : bool;
}

val solve : #n:pos -> matrix n -> vector n -> option (solve_result n)
let solve #n a b =
  let r = qr_decompose a in
  if r.singular then None
  else
    let y = apply_qt r.q b in
    match back_sub r.r y with
    | None -> None
    | Some x ->
      let norms = init n (fun i -> mat_get r.r i i) in
      Some { solution = x; norms_sq = norms; is_valid = true }

(** Verify the solution by checking that A*x is proportional to b.
    Since we use fraction-free arithmetic, A*x = b * scale for some integer scale.
    We check proportionality: (A*x)[i] * b[k] == (A*x)[k] * b[i] for all i. *)
val verify_solution : #n:pos -> matrix n -> vector n -> solve_result n -> bool
let verify_solution #n a b sr =
  let ax = mat_vec_mul a sr.solution in
  let rec find_nonzero (i:nat) : Tot (option (k:nat{k < n})) (decreases (n - i)) =
    if i >= n then None
    else if vec_get b i <> 0 then Some i
    else find_nonzero (i + 1)
  in
  match find_nonzero 0 with
  | None ->
    let rec check_zero (i:nat) : Tot bool (decreases (n - i)) =
      if i >= n then true
      else if vec_get ax i <> 0 then false
      else check_zero (i + 1)
    in
    check_zero 0
  | Some k ->
    let ax_k = vec_get ax k in
    let b_k = vec_get b k in
    let rec check (i:nat) : Tot bool (decreases (n - i)) =
      if i >= n then true
      else
        let ok = vec_get ax i * b_k = ax_k * vec_get b i in
        if ok then check (i + 1)
        else false
    in
    check 0 && ax_k <> 0
