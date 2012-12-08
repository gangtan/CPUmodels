open BinInt
open BinPos
open Peano

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_Zpower_nat : Big.big_int -> Big.big_int -> Big.big_int **)

let coq_Zpower_nat z n =
  nat_iter n (Z.mul z) Big.one

(** val shift_nat : Big.big_int -> Big.big_int -> Big.big_int **)

let shift_nat n z =
  nat_iter n (fun x -> Big.double x) z

(** val shift_pos : Big.big_int -> Big.big_int -> Big.big_int **)

let shift_pos n z =
  Pos.iter n (fun x -> Big.double x) z

(** val shift : Big.big_int -> Big.big_int -> Big.big_int **)

let shift n z =
  Big.z_case
    (fun _ ->
    z)
    (fun p ->
    Pos.iter p (fun x -> Big.double x) z)
    (fun p ->
    z)
    n

(** val two_power_nat : Big.big_int -> Big.big_int **)

let two_power_nat n =
  (shift_nat n Big.one)

(** val two_power_pos : Big.big_int -> Big.big_int **)

let two_power_pos x =
  (shift_pos x Big.one)

(** val two_p : Big.big_int -> Big.big_int **)

let two_p x =
  Big.z_case
    (fun _ ->
    Big.one)
    (fun y ->
    two_power_pos y)
    (fun y ->
    Big.zero)
    x

(** val coq_Zdiv_rest_aux :
    ((Big.big_int * Big.big_int) * Big.big_int) ->
    (Big.big_int * Big.big_int) * Big.big_int **)

let coq_Zdiv_rest_aux = function
| (p, d) ->
  let (q, r) = p in
  ((Big.z_case
      (fun _ -> (Big.zero,
      r))
      (fun p0 ->
      Big.positive_case
        (fun n -> (n,
        (Z.add d r)))
        (fun n -> (n,
        r))
        (fun _ -> (Big.zero,
        (Z.add d r)))
        p0)
      (fun p0 ->
      Big.positive_case
        (fun n -> ((Z.sub (Big.opp n) Big.one),
        (Z.add d r)))
        (fun n -> ((Big.opp n),
        r))
        (fun _ -> ((Big.opp Big.one),
        (Z.add d r)))
        p0)
      q), (Z.mul (Big.double Big.one) d))

(** val coq_Zdiv_rest :
    Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)

let coq_Zdiv_rest x p =
  let (qr, d) = Pos.iter p coq_Zdiv_rest_aux ((x, Big.zero), Big.one) in qr

type coq_Zdiv_rest_proofs =
| Zdiv_rest_proof of Big.big_int * Big.big_int

(** val coq_Zdiv_rest_proofs_rect :
    Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> __ ->
    __ -> 'a1) -> coq_Zdiv_rest_proofs -> 'a1 **)

let coq_Zdiv_rest_proofs_rect x p f = function
| Zdiv_rest_proof (x0, x1) -> f x0 x1 __ __ __

(** val coq_Zdiv_rest_proofs_rec :
    Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ -> __ ->
    __ -> 'a1) -> coq_Zdiv_rest_proofs -> 'a1 **)

let coq_Zdiv_rest_proofs_rec x p f = function
| Zdiv_rest_proof (x0, x1) -> f x0 x1 __ __ __

(** val coq_Zdiv_rest_correct :
    Big.big_int -> Big.big_int -> coq_Zdiv_rest_proofs **)

(*let coq_Zdiv_rest_correct =
  failwith "AXIOM TO BE REALIZED"
*)
