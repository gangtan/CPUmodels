open BinInt
open BinNat
open BinPos
open Datatypes

val bigint_of_nat : nat -> Big.big_int

val bigint_of_pos : positive -> Big.big_int

val bigint_of_z : coq_Z -> Big.big_int

val bigint_of_n : coq_N -> Big.big_int

val bigint_natlike_rec : 'a1 -> ('a1 -> 'a1) -> Big.big_int -> 'a1

val nat_of_bigint : Big.big_int -> nat

val bigint_poslike_rec :
  ('a1 -> 'a1) -> ('a1 -> 'a1) -> 'a1 -> Big.big_int -> 'a1

val pos_of_bigint : Big.big_int -> positive

val bigint_zlike_case :
  'a1 -> (Big.big_int -> 'a1) -> (Big.big_int -> 'a1) -> Big.big_int -> 'a1

val z_of_bigint : Big.big_int -> coq_Z

val n_of_bigint : Big.big_int -> coq_N

