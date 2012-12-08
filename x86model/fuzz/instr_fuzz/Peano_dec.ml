(** val coq_O_or_S : Big.big_int -> Big.big_int option **)

let coq_O_or_S n =
  Big.nat_case
    (fun _ ->
    None)
    (fun n0 -> Some
    n0)
    n

(** val eq_nat_dec : Big.big_int -> Big.big_int -> bool **)

let rec eq_nat_dec = Big.eq

