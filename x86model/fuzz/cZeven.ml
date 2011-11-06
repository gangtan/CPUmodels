open BinInt
open BinPos
open Datatypes

(** val coq_Zeven_bool : Big.big_int -> bool **)

let coq_Zeven_bool z =
  Big.z_case
    (fun _ -> true)
    (fun p ->
    Big.positive_case
      (fun p0 -> false)
      (fun p0 -> true)
      (fun _ -> false)
      p)
    (fun p ->
    Big.positive_case
      (fun p0 -> false)
      (fun p0 -> true)
      (fun _ -> false)
      p)
    z

(** val coq_Zodd_bool : Big.big_int -> bool **)

let coq_Zodd_bool z =
  Big.z_case
    (fun _ -> false)
    (fun p ->
    Big.positive_case
      (fun p0 -> true)
      (fun p0 -> false)
      (fun _ -> true)
      p)
    (fun p ->
    Big.positive_case
      (fun p0 -> true)
      (fun p0 -> false)
      (fun _ -> true)
      p)
    z

(** val coq_Zeven_odd_dec : Big.big_int -> bool **)

let coq_Zeven_odd_dec z =
  Big.z_case
    (fun _ -> true)
    (fun p ->
    Big.positive_case
      (fun p0 -> false)
      (fun p0 -> true)
      (fun _ -> false)
      p)
    (fun p ->
    Big.positive_case
      (fun p0 -> false)
      (fun p0 -> true)
      (fun _ -> false)
      p)
    z

(** val coq_Zeven_dec : Big.big_int -> bool **)

let coq_Zeven_dec z =
  Big.z_case
    (fun _ -> true)
    (fun p ->
    Big.positive_case
      (fun p0 -> false)
      (fun p0 -> true)
      (fun _ -> false)
      p)
    (fun p ->
    Big.positive_case
      (fun p0 -> false)
      (fun p0 -> true)
      (fun _ -> false)
      p)
    z

(** val coq_Zodd_dec : Big.big_int -> bool **)

let coq_Zodd_dec z =
  Big.z_case
    (fun _ -> false)
    (fun p ->
    Big.positive_case
      (fun p0 -> true)
      (fun p0 -> false)
      (fun _ -> true)
      p)
    (fun p ->
    Big.positive_case
      (fun p0 -> true)
      (fun p0 -> false)
      (fun _ -> true)
      p)
    z

(** val coq_Zdiv2 : Big.big_int -> Big.big_int **)

let coq_Zdiv2 z =
  Big.z_case
    (fun _ -> Big.zero)
    (fun p ->
    Big.positive_case
      (fun p0 -> (coq_Pdiv2 p))
      (fun p0 -> (coq_Pdiv2 p))
      (fun _ -> Big.zero)
      p)
    (fun p ->
    Big.positive_case
      (fun p0 -> Big.opp (coq_Pdiv2 p))
      (fun p0 -> Big.opp (coq_Pdiv2 p))
      (fun _ -> Big.zero)
      p)
    z

(** val coq_Z_modulo_2 : Big.big_int -> (Big.big_int, Big.big_int) sum **)

let coq_Z_modulo_2 x =
  if coq_Zeven_odd_dec x
  then Coq_inl (coq_Zdiv2 x)
  else Coq_inr
         (Big.z_case
           (fun _ -> assert false (* absurd case *))
           (fun p -> coq_Zdiv2 p)
           (fun p -> coq_Zdiv2 (coq_Zpred (Big.opp p)))
           x)

(** val coq_Zsplit2 : Big.big_int -> (Big.big_int * Big.big_int) **)

let coq_Zsplit2 x =
  match coq_Z_modulo_2 x with
    | Coq_inl x0 -> (x0, x0)
    | Coq_inr x0 -> (x0, (coq_Zplus x0 Big.one))

