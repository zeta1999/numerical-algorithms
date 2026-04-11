module QR.Matrix

open FStar.Seq
open FStar.Mul

(** A matrix is a sequence of rows, each a sequence of integers.
    We use integers with explicit scaling for exact arithmetic. *)

type matrix (n:pos) = s:seq (seq int){
  length s = n /\
  (forall (i:nat). i < n ==> length (index s i) = n)
}

type vector (n:pos) = v:seq int{length v = n}

(** Get element at (i, j). *)
val mat_get : #n:pos -> matrix n -> i:nat{i < n} -> j:nat{j < n} -> int
let mat_get #n m i j = index (index m i) j

(** Set element at (i, j). *)
val mat_set : #n:pos -> matrix n -> i:nat{i < n} -> j:nat{j < n} -> int -> matrix n
let mat_set #n m i j v =
  let row = index m i in
  let row' = upd row j v in
  upd m i row'

(** Get vector element. *)
val vec_get : #n:pos -> vector n -> i:nat{i < n} -> int
let vec_get #n v i = index v i

(** Set vector element. *)
val vec_set : #n:pos -> vector n -> i:nat{i < n} -> int -> vector n
let vec_set #n v i x = upd v i x

(** Create a zero vector. *)
val zero_vec : n:pos -> vector n
let zero_vec n = create n 0

(** Create a zero matrix. *)
val zero_mat : n:pos -> matrix n
let zero_mat n =
  let row = create n 0 in
  create n row

(** Create an identity matrix. *)
val identity_mat : n:pos -> matrix n
let identity_mat n =
  init n (fun i ->
    init n (fun j ->
      if i = j then 1 else 0))

(** Swap rows i and j in a matrix. *)
val swap_rows : #n:pos -> matrix n -> i:nat{i < n} -> j:nat{j < n} -> matrix n
let swap_rows #n m i j =
  if i = j then m
  else
    let ri = index m i in
    let rj = index m j in
    upd (upd m i rj) j ri

(** Absolute value for integers. *)
val iabs : int -> int
let iabs x = if x < 0 then -x else x

(** Matrix-vector multiplication. *)
val mat_vec_mul : #n:pos -> matrix n -> vector n -> vector n
let mat_vec_mul #n m v =
  init n (fun i ->
    let row = index m i in
    let rec dot (k:nat) (acc:int) : Tot int (decreases (n - k)) =
      if k >= n then acc
      else dot (k + 1) (acc + index row k * index v k)
    in
    dot 0 0)

(** Dot product of two vectors. *)
val dot_product : #n:pos -> vector n -> vector n -> int
let dot_product #n u v =
  let rec aux (k:nat) (acc:int) : Tot int (decreases (n - k)) =
    if k >= n then acc
    else aux (k + 1) (acc + vec_get u k * vec_get v k)
  in
  aux 0 0

(** Vector subtraction. *)
val vec_sub : #n:pos -> vector n -> vector n -> vector n
let vec_sub #n u v =
  init n (fun i -> vec_get u i - vec_get v i)

(** Scalar-vector multiplication. *)
val vec_scale : #n:pos -> int -> vector n -> vector n
let vec_scale #n c v =
  init n (fun i -> c * vec_get v i)

(** Extract column j from a matrix as a vector. *)
val get_col : #n:pos -> matrix n -> j:nat{j < n} -> vector n
let get_col #n m j =
  init n (fun i -> mat_get m i j)

(** Set column j of a matrix from a vector. *)
val set_col : #n:pos -> matrix n -> j:nat{j < n} -> vector n -> matrix n
let set_col #n m j v =
  let rec aux (i:nat) (acc:matrix n) : Tot (matrix n) (decreases (n - i)) =
    if i >= n then acc
    else aux (i + 1) (mat_set acc i j (vec_get v i))
  in
  aux 0 m
