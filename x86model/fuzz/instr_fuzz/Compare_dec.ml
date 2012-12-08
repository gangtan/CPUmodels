open Datatypes

(** val zerop : Big.big_int -> bool **)

let zerop n =
  Big.nat_case
    (fun _ ->
    true)
    (fun n0 ->
    false)
    n

(** val lt_eq_lt_dec : Big.big_int -> Big.big_int -> bool option **)

let rec lt_eq_lt_dec = Big.compare_case (Some false) (Some true) None

(** val gt_eq_gt_dec : Big.big_int -> Big.big_int -> bool option **)

let gt_eq_gt_dec n m =
  lt_eq_lt_dec n m

(** val le_lt_dec : Big.big_int -> Big.big_int -> bool **)

let rec le_lt_dec = Big.le

(** val le_le_S_dec : Big.big_int -> Big.big_int -> bool **)

let le_le_S_dec n m =
  le_lt_dec n m

(** val le_ge_dec : Big.big_int -> Big.big_int -> bool **)

let le_ge_dec n m =
  le_lt_dec n m

(** val le_gt_dec : Big.big_int -> Big.big_int -> bool **)

let le_gt_dec n m =
  le_lt_dec n m

(** val le_lt_eq_dec : Big.big_int -> Big.big_int -> bool **)

let le_lt_eq_dec n m =
  let s = lt_eq_lt_dec n m in
  (match s with
   | Some s0 -> s0
   | None -> assert false (* absurd case *))

(** val le_dec : Big.big_int -> Big.big_int -> bool **)

let le_dec n m =
  le_gt_dec n m

(** val lt_dec : Big.big_int -> Big.big_int -> bool **)

let lt_dec n m =
  le_dec (Big.succ n) m

(** val gt_dec : Big.big_int -> Big.big_int -> bool **)

let gt_dec n m =
  lt_dec m n

(** val ge_dec : Big.big_int -> Big.big_int -> bool **)

let ge_dec n m =
  le_dec m n

(** val nat_compare : Big.big_int -> Big.big_int -> comparison **)

let rec nat_compare = Big.compare_case Eq Lt Gt

(** val nat_compare_alt : Big.big_int -> Big.big_int -> comparison **)

let nat_compare_alt n m =
  match lt_eq_lt_dec n m with
  | Some s -> if s then Lt else Eq
  | None -> Gt

(** val leb : Big.big_int -> Big.big_int -> bool **)

let rec leb = Big.le

