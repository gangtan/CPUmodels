open BinInt
open BinPos
open Datatypes
open List0
open ZArith_dec

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val peq : Big.big_int -> Big.big_int -> bool **)

let peq =
  fun _ _ -> false

(** val plt : Big.big_int -> Big.big_int -> bool **)

let plt =
  fun _ _ -> false

(** val positive_rec :
    'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1 **)

let positive_rec v1 f =
  let iter = fun x p ->
     f (Pos.pred x) (p (Pos.pred x) __)
  in
  (fun x ->
  let rec fix_F x0 =
    iter x0 (fun y _ -> fix_F y)
  in fix_F x)

(** val zeq : Big.big_int -> Big.big_int -> bool **)

let zeq =
  Z.eq_dec

(** val zlt : Big.big_int -> Big.big_int -> bool **)

let zlt =
  coq_Z_lt_ge_dec

(** val zle : Big.big_int -> Big.big_int -> bool **)

let zle =
  coq_Z_le_gt_dec

(** val coq_Zdivide_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Zdivide_dec =
  fun _ _ -> false

(** val align : Big.big_int -> Big.big_int -> Big.big_int **)

let align n amount =
  Z.mul (Z.div (Z.sub (Z.add n amount) Big.one) amount) amount

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some y -> Some (f y)
| None -> None

(** val sum_left_map : ('a1 -> 'a2) -> ('a1, 'a3) sum -> ('a2, 'a3) sum **)

let sum_left_map f = function
| Coq_inl y -> Coq_inl (f y)
| Coq_inr z -> Coq_inr z

(** val list_disjoint_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_disjoint_dec eqA_dec l1 l2 =
  match l1 with
  | [] -> true
  | y :: l ->
    if in_dec eqA_dec y l2 then false else list_disjoint_dec eqA_dec l l2

(** val list_norepet_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool **)

let rec list_norepet_dec eqA_dec = function
| [] -> true
| y :: l0 ->
  if list_norepet_dec eqA_dec l0
  then if in_dec eqA_dec y l0 then false else true
  else false

(** val list_drop1 : 'a1 list -> 'a1 list **)

let list_drop1 = function
| [] -> []
| hd :: tl -> tl

(** val list_drop2 : 'a1 list -> 'a1 list **)

let list_drop2 = function
| [] -> []
| hd1 :: l ->
  (match l with
   | [] -> []
   | hd2 :: tl -> tl)

(** val proj_sumbool : bool -> bool **)

let proj_sumbool = function
| true -> true
| false -> false

(** val list_flatten : 'a1 list list -> 'a1 list **)

let list_flatten xs =
  fold_right app [] xs

