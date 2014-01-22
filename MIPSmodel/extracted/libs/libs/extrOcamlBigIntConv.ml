open BinInt
open BinNat
open BinPos
open Datatypes

(** val bigint_of_nat : nat -> Big.big_int **)

let bigint_of_nat x =
  let rec loop acc = function
    | O -> acc
    | S n0 -> loop (Big.succ acc) n0
  in loop Big.zero x

(** val bigint_of_pos : positive -> Big.big_int **)

let rec bigint_of_pos = function
  | Coq_xI p0 -> Big.succ (Big.double (bigint_of_pos p0))
  | Coq_xO p0 -> Big.double (bigint_of_pos p0)
  | Coq_xH -> Big.succ Big.zero

(** val bigint_of_z : coq_Z -> Big.big_int **)

let rec bigint_of_z = function
  | Z0 -> Big.zero
  | Zpos p -> bigint_of_pos p
  | Zneg p -> Big.opp (bigint_of_pos p)

(** val bigint_of_n : coq_N -> Big.big_int **)

let rec bigint_of_n = function
  | N0 -> Big.zero
  | Npos p -> bigint_of_pos p

(** val bigint_natlike_rec : 'a1 -> ('a1 -> 'a1) -> Big.big_int -> 'a1 **)

let bigint_natlike_rec = Big.nat_rec

(** val nat_of_bigint : Big.big_int -> nat **)

let nat_of_bigint x =
  bigint_natlike_rec O (fun x0 -> S x0) x

(** val bigint_poslike_rec :
    ('a1 -> 'a1) -> ('a1 -> 'a1) -> 'a1 -> Big.big_int -> 'a1 **)

let bigint_poslike_rec = Big.positive_rec

(** val pos_of_bigint : Big.big_int -> positive **)

let pos_of_bigint x =
  bigint_poslike_rec (fun x0 -> Coq_xI x0) (fun x0 -> Coq_xO x0) Coq_xH x

(** val bigint_zlike_case :
    'a1 -> (Big.big_int -> 'a1) -> (Big.big_int -> 'a1) -> Big.big_int -> 'a1 **)

let bigint_zlike_case = Big.z_rec

(** val z_of_bigint : Big.big_int -> coq_Z **)

let z_of_bigint x =
  bigint_zlike_case Z0 (fun i -> Zpos (pos_of_bigint i)) (fun i -> Zneg
    (pos_of_bigint i)) x

(** val n_of_bigint : Big.big_int -> coq_N **)

let n_of_bigint x =
  bigint_zlike_case N0 (fun i -> Npos (pos_of_bigint i)) (fun x0 -> N0) x

