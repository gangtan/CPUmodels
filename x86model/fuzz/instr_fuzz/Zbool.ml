open BinInt
open Datatypes
open Sumbool
open ZArith_dec
open Zeven

(** val coq_Z_lt_ge_bool : Big.big_int -> Big.big_int -> bool **)

let coq_Z_lt_ge_bool x y =
  bool_of_sumbool (coq_Z_lt_ge_dec x y)

(** val coq_Z_ge_lt_bool : Big.big_int -> Big.big_int -> bool **)

let coq_Z_ge_lt_bool x y =
  bool_of_sumbool (coq_Z_ge_lt_dec x y)

(** val coq_Z_le_gt_bool : Big.big_int -> Big.big_int -> bool **)

let coq_Z_le_gt_bool x y =
  bool_of_sumbool (coq_Z_le_gt_dec x y)

(** val coq_Z_gt_le_bool : Big.big_int -> Big.big_int -> bool **)

let coq_Z_gt_le_bool x y =
  bool_of_sumbool (coq_Z_gt_le_dec x y)

(** val coq_Z_eq_bool : Big.big_int -> Big.big_int -> bool **)

let coq_Z_eq_bool x y =
  bool_of_sumbool (Z.eq_dec x y)

(** val coq_Z_noteq_bool : Big.big_int -> Big.big_int -> bool **)

let coq_Z_noteq_bool x y =
  (*bool_of_sumbool (coq_Z_noteq_dec x y) *) true

(** val coq_Zeven_odd_bool : Big.big_int -> bool **)

let coq_Zeven_odd_bool x =
  bool_of_sumbool (coq_Zeven_odd_dec x)

(** val coq_Zeq_bool : Big.big_int -> Big.big_int -> bool **)

let coq_Zeq_bool x y =
  match Z.compare x y with
  | Eq -> true
  | _ -> false

(** val coq_Zneq_bool : Big.big_int -> Big.big_int -> bool **)

let coq_Zneq_bool x y =
  match Z.compare x y with
  | Eq -> false
  | _ -> true

(** val coq_Zle_bool_total : Big.big_int -> Big.big_int -> bool **)

let coq_Zle_bool_total x y =
  if Z.leb x y then true else false

