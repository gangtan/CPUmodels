(** val positive_rect :
    (Big.big_int -> 'a1 -> 'a1) -> (Big.big_int -> 'a1 -> 'a1) -> 'a1 ->
    Big.big_int -> 'a1 **)

let rec positive_rect f f0 f1 p =
  Big.positive_case
    (fun p0 ->
    f p0 (positive_rect f f0 f1 p0))
    (fun p0 ->
    f0 p0 (positive_rect f f0 f1 p0))
    (fun _ ->
    f1)
    p

(** val positive_rec :
    (Big.big_int -> 'a1 -> 'a1) -> (Big.big_int -> 'a1 -> 'a1) -> 'a1 ->
    Big.big_int -> 'a1 **)

let rec positive_rec f f0 f1 p =
  Big.positive_case
    (fun p0 ->
    f p0 (positive_rec f f0 f1 p0))
    (fun p0 ->
    f0 p0 (positive_rec f f0 f1 p0))
    (fun _ ->
    f1)
    p

(** val coq_N_rect : 'a1 -> (Big.big_int -> 'a1) -> Big.big_int -> 'a1 **)

let coq_N_rect f f0 n =
  Big.n_case
    (fun _ ->
    f)
    (fun x ->
    f0 x)
    n

(** val coq_N_rec : 'a1 -> (Big.big_int -> 'a1) -> Big.big_int -> 'a1 **)

let coq_N_rec f f0 n =
  Big.n_case
    (fun _ ->
    f)
    (fun x ->
    f0 x)
    n

(** val coq_Z_rect :
    'a1 -> (Big.big_int -> 'a1) -> (Big.big_int -> 'a1) -> Big.big_int -> 'a1 **)

let coq_Z_rect f f0 f1 z =
  Big.z_case
    (fun _ ->
    f)
    (fun x ->
    f0 x)
    (fun x ->
    f1 x)
    z

(** val coq_Z_rec :
    'a1 -> (Big.big_int -> 'a1) -> (Big.big_int -> 'a1) -> Big.big_int -> 'a1 **)

let coq_Z_rec f f0 f1 z =
  Big.z_case
    (fun _ ->
    f)
    (fun x ->
    f0 x)
    (fun x ->
    f1 x)
    z

