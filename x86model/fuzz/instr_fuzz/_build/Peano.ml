(** val pred : Big.big_int -> Big.big_int **)

let pred = fun n -> Big.max Big.zero (Big.pred n)

(** val plus : Big.big_int -> Big.big_int -> Big.big_int **)

let rec plus = Big.add

(** val mult : Big.big_int -> Big.big_int -> Big.big_int **)

let rec mult = Big.mult

(** val minus : Big.big_int -> Big.big_int -> Big.big_int **)

let rec minus = fun n m -> Big.max Big.zero (Big.sub n m)

(** val max : Big.big_int -> Big.big_int -> Big.big_int **)

let rec max = Big.max

(** val min : Big.big_int -> Big.big_int -> Big.big_int **)

let rec min = Big.min

(** val nat_iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n f x =
  Big.nat_case
    (fun _ ->
    x)
    (fun n' ->
    f (nat_iter n' f x))
    n

