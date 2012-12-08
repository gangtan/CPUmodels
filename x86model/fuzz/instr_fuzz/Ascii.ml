open BinNat

(** val ascii_rect :
    (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
    char -> 'a1 **)

let ascii_rect f a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun x x0 x1 x2 x3 x4 x5 x6 ->
    f x x0 x1 x2 x3 x4 x5 x6)
    a

(** val ascii_rec :
    (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
    char -> 'a1 **)

let ascii_rec f a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun x x0 x1 x2 x3 x4 x5 x6 ->
    f x x0 x1 x2 x3 x4 x5 x6)
    a

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : Big.big_int -> char **)

let ascii_of_pos =
  let rec loop n p =
    Big.nat_case
      (fun _ ->
      zero)
      (fun n' ->
      Big.positive_case
        (fun p' ->
        shift true (loop n' p'))
        (fun p' ->
        shift false (loop n' p'))
        (fun _ ->
        one)
        p)
      n
  in loop (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
       (Big.succ (Big.succ Big.zero))))))))

(** val ascii_of_N : Big.big_int -> char **)

let ascii_of_N n =
  Big.n_case
    (fun _ ->
    zero)
    (fun p ->
    ascii_of_pos p)
    n

(** val ascii_of_nat : Big.big_int -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val coq_N_of_digits : bool list -> Big.big_int **)

let rec coq_N_of_digits = function
| [] -> Big.zero
| b :: l' ->
  N.add (if b then Big.one else Big.zero)
    (N.mul (Big.double Big.one) (coq_N_of_digits l'))

(** val coq_N_of_ascii : char -> Big.big_int **)

let coq_N_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    coq_N_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> Big.big_int **)

let nat_of_ascii a =
  N.to_nat (coq_N_of_ascii a)

(** val coq_Space : char **)

let coq_Space =
  ' '

(** val coq_DoubleQuote : char **)

let coq_DoubleQuote =
  '"'

(** val coq_Beep : char **)

let coq_Beep =
  '\007'

