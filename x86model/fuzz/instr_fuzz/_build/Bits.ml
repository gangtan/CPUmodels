open BinInt
open Coqlib
open Datatypes
open List0
open Zpower

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Word = 
 struct 
  (** val wordsize : Big.big_int -> Big.big_int **)
  
  let wordsize wordsize_minus_one =
    Big.succ wordsize_minus_one
  
  (** val modulus : Big.big_int -> Big.big_int **)
  
  let modulus wordsize_minus_one =
    two_power_nat (wordsize wordsize_minus_one)
  
  (** val half_modulus : Big.big_int -> Big.big_int **)
  
  let half_modulus wordsize_minus_one =
    Z.div (modulus wordsize_minus_one) (Big.double Big.one)
  
  type comparison =
  | Ceq
  | Cne
  | Clt
  | Cle
  | Cgt
  | Cge
  
  (** val comparison_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1 **)
  
  let comparison_rect f f0 f1 f2 f3 f4 = function
  | Ceq -> f
  | Cne -> f0
  | Clt -> f1
  | Cle -> f2
  | Cgt -> f3
  | Cge -> f4
  
  (** val comparison_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1 **)
  
  let comparison_rec f f0 f1 f2 f3 f4 = function
  | Ceq -> f
  | Cne -> f0
  | Clt -> f1
  | Cle -> f2
  | Cgt -> f3
  | Cge -> f4
  
  (** val negate_comparison : comparison -> comparison **)
  
  let negate_comparison = function
  | Ceq -> Cne
  | Cne -> Ceq
  | Clt -> Cge
  | Cle -> Cgt
  | Cgt -> Cle
  | Cge -> Clt
  
  (** val swap_comparison : comparison -> comparison **)
  
  let swap_comparison = function
  | Clt -> Cgt
  | Cle -> Cge
  | Cgt -> Clt
  | Cge -> Cle
  | x -> x
  
  type int =
    Big.big_int
    (* singleton inductive, whose constructor was mkint *)
  
  (** val int_rect :
      Big.big_int -> (Big.big_int -> __ -> 'a1) -> int -> 'a1 **)
  
  let int_rect wordsize_minus_one f i =
    f i __
  
  (** val int_rec :
      Big.big_int -> (Big.big_int -> __ -> 'a1) -> int -> 'a1 **)
  
  let int_rec wordsize_minus_one f i =
    f i __
  
  (** val intval : Big.big_int -> int -> Big.big_int **)
  
  let intval wordsize_minus_one i =
    i
  
  (** val max_unsigned : Big.big_int -> Big.big_int **)
  
  let max_unsigned wordsize_minus_one =
    Z.sub (modulus wordsize_minus_one) Big.one
  
  (** val max_signed : Big.big_int -> Big.big_int **)
  
  let max_signed wordsize_minus_one =
    Z.sub (half_modulus wordsize_minus_one) Big.one
  
  (** val min_signed : Big.big_int -> Big.big_int **)
  
  let min_signed wordsize_minus_one =
    Z.opp (half_modulus wordsize_minus_one)
  
  (** val unsigned : Big.big_int -> int -> Big.big_int **)
  
  let unsigned wordsize_minus_one n =
    intval wordsize_minus_one n
  
  (** val signed : Big.big_int -> int -> Big.big_int **)
  
  let signed wordsize_minus_one n =
    if zlt (unsigned wordsize_minus_one n) (half_modulus wordsize_minus_one)
    then unsigned wordsize_minus_one n
    else Z.sub (unsigned wordsize_minus_one n) (modulus wordsize_minus_one)
  
  (** val repr : Big.big_int -> Big.big_int -> int **)
  
  let repr wordsize_minus_one x =
    Z.modulo x (modulus wordsize_minus_one)
  
  (** val zero : Big.big_int -> int **)
  
  let zero wordsize_minus_one =
    repr wordsize_minus_one Big.zero
  
  (** val one : Big.big_int -> int **)
  
  let one wordsize_minus_one =
    repr wordsize_minus_one Big.one
  
  (** val mone : Big.big_int -> int **)
  
  let mone wordsize_minus_one =
    repr wordsize_minus_one (Big.opp Big.one)
  
  (** val eq_dec : Big.big_int -> int -> int -> bool **)
  
  let eq_dec =
    fun _ _ _ -> false
  
  (** val eq : Big.big_int -> int -> int -> bool **)
  
  let eq wordsize_minus_one x y =
    if zeq (unsigned wordsize_minus_one x) (unsigned wordsize_minus_one y)
    then true
    else false
  
  (** val lt : Big.big_int -> int -> int -> bool **)
  
  let lt wordsize_minus_one x y =
    if zlt (signed wordsize_minus_one x) (signed wordsize_minus_one y)
    then true
    else false
  
  (** val ltu : Big.big_int -> int -> int -> bool **)
  
  let ltu wordsize_minus_one x y =
    if zlt (unsigned wordsize_minus_one x) (unsigned wordsize_minus_one y)
    then true
    else false
  
  (** val lequ : Big.big_int -> int -> int -> bool **)
  
  let lequ wordsize_minus_one x y =
    (||) (ltu wordsize_minus_one x y) (eq wordsize_minus_one x y)
  
  (** val neg : Big.big_int -> int -> int **)
  
  let neg wordsize_minus_one x =
    repr wordsize_minus_one (Z.opp (unsigned wordsize_minus_one x))
  
  (** val zero_ext : Big.big_int -> Big.big_int -> int -> int **)
  
  let zero_ext wordsize_minus_one n x =
    repr wordsize_minus_one
      (Z.modulo (unsigned wordsize_minus_one x) (two_p n))
  
  (** val sign_ext : Big.big_int -> Big.big_int -> int -> int **)
  
  let sign_ext wordsize_minus_one n x =
    repr wordsize_minus_one
      (let p = two_p n in
       let y = Z.modulo (unsigned wordsize_minus_one x) p in
       if zlt y (two_p (Z.sub n Big.one)) then y else Z.sub y p)
  
  (** val add : Big.big_int -> int -> int -> int **)
  
  let add wordsize_minus_one x y =
    repr wordsize_minus_one
      (Z.add (unsigned wordsize_minus_one x) (unsigned wordsize_minus_one y))
  
  (** val sub : Big.big_int -> int -> int -> int **)
  
  let sub wordsize_minus_one x y =
    repr wordsize_minus_one
      (Z.sub (unsigned wordsize_minus_one x) (unsigned wordsize_minus_one y))
  
  (** val mul : Big.big_int -> int -> int -> int **)
  
  let mul wordsize_minus_one x y =
    repr wordsize_minus_one
      (Z.mul (unsigned wordsize_minus_one x) (unsigned wordsize_minus_one y))
  
  (** val coq_Zdiv_round : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_Zdiv_round x y =
    if zlt x Big.zero
    then if zlt y Big.zero
         then Z.div (Z.opp x) (Z.opp y)
         else Z.opp (Z.div (Z.opp x) y)
    else if zlt y Big.zero then Z.opp (Z.div x (Z.opp y)) else Z.div x y
  
  (** val coq_Zmod_round : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_Zmod_round x y =
    Z.sub x (Z.mul (coq_Zdiv_round x y) y)
  
  (** val divs : Big.big_int -> int -> int -> int **)
  
  let divs wordsize_minus_one x y =
    repr wordsize_minus_one
      (coq_Zdiv_round (signed wordsize_minus_one x)
        (signed wordsize_minus_one y))
  
  (** val mods : Big.big_int -> int -> int -> int **)
  
  let mods wordsize_minus_one x y =
    repr wordsize_minus_one
      (coq_Zmod_round (signed wordsize_minus_one x)
        (signed wordsize_minus_one y))
  
  (** val divu : Big.big_int -> int -> int -> int **)
  
  let divu wordsize_minus_one x y =
    repr wordsize_minus_one
      (Z.div (unsigned wordsize_minus_one x) (unsigned wordsize_minus_one y))
  
  (** val modu : Big.big_int -> int -> int -> int **)
  
  let modu wordsize_minus_one x y =
    repr wordsize_minus_one
      (Z.modulo (unsigned wordsize_minus_one x)
        (unsigned wordsize_minus_one y))
  
  (** val bool_to_int : Big.big_int -> bool -> int **)
  
  let bool_to_int wordsize_minus_one = function
  | true -> one wordsize_minus_one
  | false -> zero wordsize_minus_one
  
  (** val unsigned_overflow :
      Big.big_int -> Big.big_int -> Big.big_int -> bool **)
  
  let unsigned_overflow wordsize_minus_one o1 o2 =
    let res = Z.add o1 o2 in
    if zlt res (modulus wordsize_minus_one) then false else true
  
  (** val unsigned_overflow_with_carry :
      Big.big_int -> Big.big_int -> Big.big_int -> bool -> bool **)
  
  let unsigned_overflow_with_carry wordsize_minus_one o1 o2 carry =
    let c = bool_to_int wordsize_minus_one carry in
    let res = Z.add (Z.add o1 o2) (unsigned wordsize_minus_one c) in
    if zle res (max_unsigned wordsize_minus_one) then false else true
  
  (** val signed_overflow :
      Big.big_int -> Big.big_int -> Big.big_int -> bool **)
  
  let signed_overflow wordsize_minus_one o1 o2 =
    let res = Z.add o1 o2 in
    if (&&) (proj_sumbool (zle res (max_signed wordsize_minus_one)))
         (proj_sumbool (zle (min_signed wordsize_minus_one) res))
    then false
    else true
  
  (** val signed_overflow_with_carry :
      Big.big_int -> Big.big_int -> Big.big_int -> bool -> bool **)
  
  let signed_overflow_with_carry wordsize_minus_one o1 o2 carry =
    let c = bool_to_int wordsize_minus_one carry in
    let res = Z.add (Z.add o1 o2) (signed wordsize_minus_one c) in
    if (&&) (proj_sumbool (zle res (max_signed wordsize_minus_one)))
         (proj_sumbool (zle (min_signed wordsize_minus_one) res))
    then false
    else true
  
  (** val signed_overflow_with_borrow :
      Big.big_int -> Big.big_int -> Big.big_int -> bool -> bool **)
  
  let signed_overflow_with_borrow wordsize_minus_one o1 o2 borrow =
    let b = bool_to_int wordsize_minus_one borrow in
    let res = Z.sub (Z.add o1 o2) (signed wordsize_minus_one b) in
    if (&&) (proj_sumbool (zle res (max_signed wordsize_minus_one)))
         (proj_sumbool (zle (min_signed wordsize_minus_one) res))
    then false
    else true
  
  (** val is_zero : Big.big_int -> int -> bool **)
  
  let is_zero wordsize_minus_one i =
    eq wordsize_minus_one i (zero wordsize_minus_one)
  
  (** val is_signed : Big.big_int -> int -> bool **)
  
  let is_signed wordsize_minus_one i =
    lt wordsize_minus_one i (zero wordsize_minus_one)
  
  (** val coq_Z_shift_add : bool -> Big.big_int -> Big.big_int **)
  
  let coq_Z_shift_add b x =
    if b
    then Z.add (Z.mul (Big.double Big.one) x) Big.one
    else Z.mul (Big.double Big.one) x
  
  (** val coq_Z_bin_decomp : Big.big_int -> bool * Big.big_int **)
  
  let coq_Z_bin_decomp x =
    Big.z_case
      (fun _ -> (false,
      Big.zero))
      (fun p ->
      Big.positive_case
        (fun q -> (true,
        q))
        (fun q -> (false,
        q))
        (fun _ -> (true,
        Big.zero))
        p)
      (fun p ->
      Big.positive_case
        (fun q -> (true,
        (Z.sub (Big.opp q) Big.one)))
        (fun q -> (false, (Big.opp
        q)))
        (fun _ -> (true, (Big.opp
        Big.one)))
        p)
      x
  
  (** val bits_of_Z : Big.big_int -> Big.big_int -> Big.big_int -> bool **)
  
  let rec bits_of_Z n x =
    Big.nat_case
      (fun _ i ->
      false)
      (fun m ->
      let (b, y) = coq_Z_bin_decomp x in
      let f = bits_of_Z m y in
      (fun i -> if zeq i Big.zero then b else f (Z.sub i Big.one)))
      n
  
  (** val coq_Z_of_bits :
      Big.big_int -> (Big.big_int -> bool) -> Big.big_int **)
  
  let rec coq_Z_of_bits n f =
    Big.nat_case
      (fun _ ->
      Big.zero)
      (fun m ->
      coq_Z_shift_add (f Big.zero)
        (coq_Z_of_bits m (fun i -> f (Z.add i Big.one))))
      n
  
  (** val bitwise_binop :
      Big.big_int -> (bool -> bool -> bool) -> int -> int -> int **)
  
  let bitwise_binop wordsize_minus_one f x y =
    let fx =
      bits_of_Z (wordsize wordsize_minus_one) (unsigned wordsize_minus_one x)
    in
    let fy =
      bits_of_Z (wordsize wordsize_minus_one) (unsigned wordsize_minus_one y)
    in
    repr wordsize_minus_one
      (coq_Z_of_bits (wordsize wordsize_minus_one) (fun i ->
        f (fx i) (fy i)))
  
  (** val coq_and : Big.big_int -> int -> int -> int **)
  
  let coq_and wordsize_minus_one x y =
    bitwise_binop wordsize_minus_one (&&) x y
  
  (** val coq_or : Big.big_int -> int -> int -> int **)
  
  let coq_or wordsize_minus_one x y =
    bitwise_binop wordsize_minus_one (||) x y
  
  (** val xor : Big.big_int -> int -> int -> int **)
  
  let xor wordsize_minus_one x y =
    bitwise_binop wordsize_minus_one xorb x y
  
  (** val not : Big.big_int -> int -> int **)
  
  let not wordsize_minus_one x =
    xor wordsize_minus_one x (mone wordsize_minus_one)
  
  (** val shl : Big.big_int -> int -> int -> int **)
  
  let shl wordsize_minus_one x y =
    let fx =
      bits_of_Z (wordsize wordsize_minus_one) (unsigned wordsize_minus_one x)
    in
    let vy = unsigned wordsize_minus_one y in
    repr wordsize_minus_one
      (coq_Z_of_bits (wordsize wordsize_minus_one) (fun i ->
        fx (Z.sub i vy)))
  
  (** val shru : Big.big_int -> int -> int -> int **)
  
  let shru wordsize_minus_one x y =
    let fx =
      bits_of_Z (wordsize wordsize_minus_one) (unsigned wordsize_minus_one x)
    in
    let vy = unsigned wordsize_minus_one y in
    repr wordsize_minus_one
      (coq_Z_of_bits (wordsize wordsize_minus_one) (fun i ->
        fx (Z.add i vy)))
  
  (** val shr : Big.big_int -> int -> int -> int **)
  
  let shr wordsize_minus_one x y =
    repr wordsize_minus_one
      (Z.div (signed wordsize_minus_one x)
        (two_p (unsigned wordsize_minus_one y)))
  
  (** val shrx : Big.big_int -> int -> int -> int **)
  
  let shrx wordsize_minus_one x y =
    divs wordsize_minus_one x
      (shl wordsize_minus_one (one wordsize_minus_one) y)
  
  (** val shr_carry : Big.big_int -> int -> int -> int **)
  
  let shr_carry wordsize_minus_one x y =
    sub wordsize_minus_one (shrx wordsize_minus_one x y)
      (shr wordsize_minus_one x y)
  
  (** val rol : Big.big_int -> int -> int -> int **)
  
  let rol wordsize_minus_one x y =
    let fx =
      bits_of_Z (wordsize wordsize_minus_one) (unsigned wordsize_minus_one x)
    in
    let vy = unsigned wordsize_minus_one y in
    repr wordsize_minus_one
      (coq_Z_of_bits (wordsize wordsize_minus_one) (fun i ->
        fx (Z.modulo (Z.sub i vy) (Z.of_nat (wordsize wordsize_minus_one)))))
  
  (** val ror : Big.big_int -> int -> int -> int **)
  
  let ror wordsize_minus_one x y =
    let fx =
      bits_of_Z (wordsize wordsize_minus_one) (unsigned wordsize_minus_one x)
    in
    let vy = unsigned wordsize_minus_one y in
    repr wordsize_minus_one
      (coq_Z_of_bits (wordsize wordsize_minus_one) (fun i ->
        fx (Z.modulo (Z.add i vy) (Z.of_nat (wordsize wordsize_minus_one)))))
  
  (** val rolm : Big.big_int -> int -> int -> int -> int **)
  
  let rolm wordsize_minus_one x a m =
    coq_and wordsize_minus_one (rol wordsize_minus_one x a) m
  
  (** val coq_Z_one_bits :
      Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int list **)
  
  let rec coq_Z_one_bits n x i =
    Big.nat_case
      (fun _ ->
      [])
      (fun m ->
      let (b, y) = coq_Z_bin_decomp x in
      if b
      then i :: (coq_Z_one_bits m y (Z.add i Big.one))
      else coq_Z_one_bits m y (Z.add i Big.one))
      n
  
  (** val one_bits : Big.big_int -> int -> int list **)
  
  let one_bits wordsize_minus_one x =
    map (repr wordsize_minus_one)
      (coq_Z_one_bits (wordsize wordsize_minus_one)
        (unsigned wordsize_minus_one x) Big.zero)
  
  (** val is_power2 : Big.big_int -> int -> int option **)
  
  let is_power2 wordsize_minus_one x =
    match coq_Z_one_bits (wordsize wordsize_minus_one)
            (unsigned wordsize_minus_one x) Big.zero with
    | [] -> None
    | i :: l ->
      (match l with
       | [] -> Some (repr wordsize_minus_one i)
       | z :: l0 -> None)
  
  type rlw_state =
  | RLW_S0
  | RLW_S1
  | RLW_S2
  | RLW_S3
  | RLW_S4
  | RLW_S5
  | RLW_S6
  | RLW_Sbad
  
  (** val rlw_state_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> rlw_state ->
      'a1 **)
  
  let rlw_state_rect f f0 f1 f2 f3 f4 f5 f6 = function
  | RLW_S0 -> f
  | RLW_S1 -> f0
  | RLW_S2 -> f1
  | RLW_S3 -> f2
  | RLW_S4 -> f3
  | RLW_S5 -> f4
  | RLW_S6 -> f5
  | RLW_Sbad -> f6
  
  (** val rlw_state_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> rlw_state ->
      'a1 **)
  
  let rlw_state_rec f f0 f1 f2 f3 f4 f5 f6 = function
  | RLW_S0 -> f
  | RLW_S1 -> f0
  | RLW_S2 -> f1
  | RLW_S3 -> f2
  | RLW_S4 -> f3
  | RLW_S5 -> f4
  | RLW_S6 -> f5
  | RLW_Sbad -> f6
  
  (** val rlw_transition : rlw_state -> bool -> rlw_state **)
  
  let rlw_transition s b =
    match s with
    | RLW_S0 -> if b then RLW_S4 else RLW_S1
    | RLW_S1 -> if b then RLW_S2 else RLW_S1
    | RLW_S2 -> if b then RLW_S2 else RLW_S3
    | RLW_S3 -> if b then RLW_Sbad else RLW_S3
    | RLW_S4 -> if b then RLW_S4 else RLW_S5
    | RLW_S5 -> if b then RLW_S6 else RLW_S5
    | RLW_S6 -> if b then RLW_S6 else RLW_Sbad
    | RLW_Sbad -> RLW_Sbad
  
  (** val rlw_accepting : rlw_state -> bool **)
  
  let rlw_accepting = function
  | RLW_S0 -> false
  | RLW_S1 -> false
  | RLW_Sbad -> false
  | _ -> true
  
  (** val is_rlw_mask_rec :
      Big.big_int -> rlw_state -> Big.big_int -> bool **)
  
  let rec is_rlw_mask_rec n s x =
    Big.nat_case
      (fun _ ->
      rlw_accepting s)
      (fun m ->
      let (b, y) = coq_Z_bin_decomp x in
      is_rlw_mask_rec m (rlw_transition s b) y)
      n
  
  (** val is_rlw_mask : Big.big_int -> int -> bool **)
  
  let is_rlw_mask wordsize_minus_one x =
    is_rlw_mask_rec (wordsize wordsize_minus_one) RLW_S0
      (unsigned wordsize_minus_one x)
  
  (** val cmp : Big.big_int -> comparison -> int -> int -> bool **)
  
  let cmp wordsize_minus_one c x y =
    match c with
    | Ceq -> eq wordsize_minus_one x y
    | Cne -> negb (eq wordsize_minus_one x y)
    | Clt -> lt wordsize_minus_one x y
    | Cle -> negb (lt wordsize_minus_one y x)
    | Cgt -> lt wordsize_minus_one y x
    | Cge -> negb (lt wordsize_minus_one x y)
  
  (** val cmpu : Big.big_int -> comparison -> int -> int -> bool **)
  
  let cmpu wordsize_minus_one c x y =
    match c with
    | Ceq -> eq wordsize_minus_one x y
    | Cne -> negb (eq wordsize_minus_one x y)
    | Clt -> ltu wordsize_minus_one x y
    | Cle -> negb (ltu wordsize_minus_one y x)
    | Cgt -> ltu wordsize_minus_one y x
    | Cge -> negb (ltu wordsize_minus_one x y)
  
  (** val notbool : Big.big_int -> int -> int **)
  
  let notbool wordsize_minus_one x =
    if eq wordsize_minus_one x (zero wordsize_minus_one)
    then one wordsize_minus_one
    else zero wordsize_minus_one
  
  (** val check_equal_on_range :
      Big.big_int -> (int -> int) -> (int -> int) -> Big.big_int -> bool **)
  
  let rec check_equal_on_range wordsize_minus_one f g n =
    Big.nat_case
      (fun _ ->
      true)
      (fun n0 ->
      if eq wordsize_minus_one (f (repr wordsize_minus_one (Z.of_nat n0)))
           (g (repr wordsize_minus_one (Z.of_nat n0)))
      then check_equal_on_range wordsize_minus_one f g n0
      else false)
      n
  
  (** val powerserie : Big.big_int list -> Big.big_int **)
  
  let rec powerserie = function
  | [] -> Big.zero
  | x :: xs -> Z.add (two_p x) (powerserie xs)
  
  (** val int_of_one_bits : Big.big_int -> int list -> int **)
  
  let rec int_of_one_bits wordsize_minus_one = function
  | [] -> zero wordsize_minus_one
  | a :: b ->
    add wordsize_minus_one
      (shl wordsize_minus_one (one wordsize_minus_one) a)
      (int_of_one_bits wordsize_minus_one b)
  
  (** val string_to_Z_bool : char list -> Big.big_int -> bool **)
  
  let rec string_to_Z_bool = function
  | [] -> (fun i -> false)
  | a::s0 ->
    let b = if (=) a '0' then false else true in
    (fun i ->
    if zeq i Big.zero then b else string_to_Z_bool s0 (Z.sub i Big.one))
  
  (** val string_to_int : Big.big_int -> char list -> int **)
  
  let string_to_int n s =
    let zb = string_to_Z_bool s in repr n (coq_Z_of_bits n zb)
 end

type int1 = Word.int

type int2 = Word.int

type int3 = Word.int

type int4 = Word.int

type int8 = Word.int

type int11 = Word.int

type int16 = Word.int

type int32 = Word.int

type int64 = Word.int

type int80 = Word.int

module Int32_OT = 
 struct 
  type t = Word.int
  
  (** val compare : t -> t -> t OrderedType.coq_Compare **)
  
 (* let compare =
    failwith "AXIOM TO BE REALIZED"
  *)
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec x y =
    if Word.eq (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
         (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
         (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
         (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
         (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
         (Big.succ Big.zero))))))))))))))))))))))))))))))) x y
    then true
    else false
 end

