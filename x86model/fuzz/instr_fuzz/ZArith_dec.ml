open BinInt
open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_Dcompare_inf : comparison -> bool option **)

let coq_Dcompare_inf = function
| Eq -> Some true
| Lt -> Some false
| Gt -> None

(** val coq_Zcompare_rect :
    Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
    -> 'a1 **)

let coq_Zcompare_rect n m h1 h2 h3 =
  let c = Z.compare n m in
  (match c with
   | Eq -> h1 __
   | Lt -> h2 __
   | Gt -> h3 __)

(** val coq_Zcompare_rec :
    Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
    -> 'a1 **)

let coq_Zcompare_rec n m =
  coq_Zcompare_rect n m

(** val coq_Z_lt_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_lt_dec x y =
  match Z.compare x y with
  | Lt -> true
  | _ -> false

(** val coq_Z_le_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_le_dec x y =
  match Z.compare x y with
  | Gt -> false
  | _ -> true

(** val coq_Z_gt_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_gt_dec x y =
  match Z.compare x y with
  | Gt -> true
  | _ -> false

(** val coq_Z_ge_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_ge_dec x y =
  match Z.compare x y with
  | Lt -> false
  | _ -> true

(** val coq_Z_lt_ge_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_lt_ge_dec x y =
  coq_Z_lt_dec x y

(** val coq_Z_lt_le_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_lt_le_dec x y =
  coq_Z_lt_ge_dec x y

(** val coq_Z_le_gt_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_le_gt_dec x y =
  coq_Z_le_dec x y

(** val coq_Z_gt_le_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_gt_le_dec x y =
  coq_Z_gt_dec x y

(** val coq_Z_ge_lt_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_ge_lt_dec x y =
  coq_Z_ge_dec x y

(** val coq_Z_le_lt_eq_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_le_lt_eq_dec x y =
  coq_Zcompare_rec x y (fun _ -> false) (fun _ -> true) (fun _ ->
    assert false (* absurd case *))

(** val coq_Zlt_cotrans :
    Big.big_int -> Big.big_int -> Big.big_int -> bool **)

let coq_Zlt_cotrans x y z =
  coq_Z_lt_ge_dec x z

(** val coq_Zlt_cotrans_pos : Big.big_int -> Big.big_int -> bool **)

let coq_Zlt_cotrans_pos x y =
  coq_Zlt_cotrans Big.zero (Z.add x y) x

(** val coq_Zlt_cotrans_neg : Big.big_int -> Big.big_int -> bool **)

let coq_Zlt_cotrans_neg x y =
  if coq_Zlt_cotrans (Z.add x y) Big.zero x then false else true

(** val not_Zeq_inf : Big.big_int -> Big.big_int -> bool **)

let not_Zeq_inf x y =
  if coq_Z_lt_ge_dec x y
  then true
  else if coq_Z_le_lt_eq_dec y x
       then false
       else assert false (* absurd case *)

(** val coq_Z_dec : Big.big_int -> Big.big_int -> bool option **)

let coq_Z_dec x y =
  if coq_Z_lt_ge_dec x y
  then Some true
  else if coq_Z_le_lt_eq_dec y x then Some false else None

(** val coq_Z_dec' : Big.big_int -> Big.big_int -> bool option **)

let coq_Z_dec' x y =
  if Z.eq_dec x y then None else Some (not_Zeq_inf x y)

(** val coq_Z_zerop : Big.big_int -> bool **)

let coq_Z_zerop x =
  Z.eq_dec x Big.zero

(** val coq_Z_notzerop : Big.big_int -> bool **)

let coq_Z_notzerop =
(*  failwith "AXIOM TO BE REALIZED" *)
fun _ -> false

(** val coq_Z_noteq_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_noteq_dec =
(*  failwith "AXIOM TO BE REALIZED" *)
fun _ _ -> false

