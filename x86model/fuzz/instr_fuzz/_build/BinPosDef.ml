open Datatypes
open Peano

module Pos = 
 struct 
  type t = Big.big_int
  
  (** val succ : Big.big_int -> Big.big_int **)
  
  let rec succ x =
    Big.positive_case
      (fun p -> Big.double
      (succ p))
      (fun p -> Big.doubleplusone
      p)
      (fun _ -> Big.double
      Big.one)
      x
  
  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec add x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q -> Big.double
        (add_carry p q))
        (fun q -> Big.doubleplusone
        (add p q))
        (fun _ -> Big.double
        (succ p))
        y)
      (fun p ->
      Big.positive_case
        (fun q -> Big.doubleplusone
        (add p q))
        (fun q -> Big.double
        (add p q))
        (fun _ -> Big.doubleplusone
        p)
        y)
      (fun _ ->
      Big.positive_case
        (fun q -> Big.double
        (succ q))
        (fun q -> Big.doubleplusone
        q)
        (fun _ -> Big.double
        Big.one)
        y)
      x
  
  (** val add_carry : Big.big_int -> Big.big_int -> Big.big_int **)
  
  and add_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q -> Big.doubleplusone
        (add_carry p q))
        (fun q -> Big.double
        (add_carry p q))
        (fun _ -> Big.doubleplusone
        (succ p))
        y)
      (fun p ->
      Big.positive_case
        (fun q -> Big.double
        (add_carry p q))
        (fun q -> Big.doubleplusone
        (add p q))
        (fun _ -> Big.double
        (succ p))
        y)
      (fun _ ->
      Big.positive_case
        (fun q -> Big.doubleplusone
        (succ q))
        (fun q -> Big.double
        (succ q))
        (fun _ -> Big.doubleplusone
        Big.one)
        y)
      x
  
  (** val pred_double : Big.big_int -> Big.big_int **)
  
  let rec pred_double x =
    Big.positive_case
      (fun p -> Big.doubleplusone (Big.double
      p))
      (fun p -> Big.doubleplusone
      (pred_double p))
      (fun _ ->
      Big.one)
      x
  
  (** val pred : Big.big_int -> Big.big_int **)
  
  let pred x =
    Big.positive_case
      (fun p -> Big.double
      p)
      (fun p ->
      pred_double p)
      (fun _ ->
      Big.one)
      x
  
  (** val pred_N : Big.big_int -> Big.big_int **)
  
  let pred_N x =
    Big.positive_case
      (fun p -> (Big.double
      p))
      (fun p ->
      (pred_double p))
      (fun _ ->
      Big.zero)
      x
  
  type mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg
  
  (** val mask_rect : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (Big.big_int -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos Big.one
  | IsPos p -> IsPos (Big.doubleplusone p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (Big.double p)
  | x0 -> x0
  
  (** val double_pred_mask : Big.big_int -> mask **)
  
  let double_pred_mask x =
    Big.positive_case
      (fun p -> IsPos (Big.double (Big.double
      p)))
      (fun p -> IsPos (Big.double
      (pred_double p)))
      (fun _ ->
      IsNul)
      x
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (Big.positive_case
       (fun p0 -> IsPos
       (pred q))
       (fun p0 -> IsPos
       (pred q))
       (fun _ ->
       IsNul)
       q)
  | _ -> IsNeg
  
  (** val sub_mask : Big.big_int -> Big.big_int -> mask **)
  
  let rec sub_mask x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q ->
        double_mask (sub_mask p q))
        (fun q ->
        succ_double_mask (sub_mask p q))
        (fun _ -> IsPos (Big.double
        p))
        y)
      (fun p ->
      Big.positive_case
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun q ->
        double_mask (sub_mask p q))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun _ ->
      Big.positive_case
        (fun p ->
        IsNeg)
        (fun p ->
        IsNeg)
        (fun _ ->
        IsNul)
        y)
      x
  
  (** val sub_mask_carry : Big.big_int -> Big.big_int -> mask **)
  
  and sub_mask_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun q ->
        double_mask (sub_mask p q))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun p ->
      Big.positive_case
        (fun q ->
        double_mask (sub_mask_carry p q))
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun _ ->
        double_pred_mask p)
        y)
      (fun _ ->
      IsNeg)
      x
  
  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z -> z
    | _ -> Big.one
  
  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec mul x y =
    Big.positive_case
      (fun p ->
      add y (Big.double (mul p y)))
      (fun p -> Big.double
      (mul p y))
      (fun _ ->
      y)
      x
  
  (** val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n f x =
    Big.positive_case
      (fun n' ->
      f (iter n' f (iter n' f x)))
      (fun n' ->
      iter n' f (iter n' f x))
      (fun _ ->
      f x)
      n
  
  (** val pow : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let pow x y =
    iter y (mul x) Big.one
  
  (** val square : Big.big_int -> Big.big_int **)
  
  let rec square p =
    Big.positive_case
      (fun p0 -> Big.doubleplusone (Big.double
      (add (square p0) p0)))
      (fun p0 -> Big.double (Big.double
      (square p0)))
      (fun _ ->
      Big.one)
      p
  
  (** val div2 : Big.big_int -> Big.big_int **)
  
  let div2 p =
    Big.positive_case
      (fun p0 ->
      p0)
      (fun p0 ->
      p0)
      (fun _ ->
      Big.one)
      p
  
  (** val div2_up : Big.big_int -> Big.big_int **)
  
  let div2_up p =
    Big.positive_case
      (fun p0 ->
      succ p0)
      (fun p0 ->
      p0)
      (fun _ ->
      Big.one)
      p
  
  (** val size_nat : Big.big_int -> Big.big_int **)
  
  let rec size_nat p =
    Big.positive_case
      (fun p0 -> Big.succ
      (size_nat p0))
      (fun p0 -> Big.succ
      (size_nat p0))
      (fun _ -> Big.succ
      Big.zero)
      p
  
  (** val size : Big.big_int -> Big.big_int **)
  
  let rec size p =
    Big.positive_case
      (fun p0 ->
      succ (size p0))
      (fun p0 ->
      succ (size p0))
      (fun _ ->
      Big.one)
      p
  
  (** val compare_cont :
      Big.big_int -> Big.big_int -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q ->
        compare_cont p q r)
        (fun q ->
        compare_cont p q Gt)
        (fun _ ->
        Gt)
        y)
      (fun p ->
      Big.positive_case
        (fun q ->
        compare_cont p q Lt)
        (fun q ->
        compare_cont p q r)
        (fun _ ->
        Gt)
        y)
      (fun _ ->
      Big.positive_case
        (fun q ->
        Lt)
        (fun q ->
        Lt)
        (fun _ ->
        r)
        y)
      x
  
  (** val compare : Big.big_int -> Big.big_int -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : Big.big_int -> Big.big_int -> bool **)
  
  let rec eqb p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        eqb p0 q0)
        (fun p1 ->
        false)
        (fun _ ->
        false)
        q)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        false)
        (fun q0 ->
        eqb p0 q0)
        (fun _ ->
        false)
        q)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        q)
      p
  
  (** val leb : Big.big_int -> Big.big_int -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : Big.big_int -> Big.big_int -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (Big.big_int -> Big.big_int) -> (Big.big_int -> Big.big_int) ->
      (Big.big_int * mask) -> Big.big_int * mask **)
  
  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = Big.doubleplusone (Big.double s) in
       let r' = g (f r) in
       if leb s' r'
       then ((Big.doubleplusone s), (sub_mask r' s'))
       else ((Big.double s), (IsPos r'))
     | _ ->
       ((Big.double s),
         (sub_mask (g (f Big.one)) (Big.double (Big.double Big.one)))))
  
  (** val sqrtrem : Big.big_int -> Big.big_int * mask **)
  
  let rec sqrtrem p =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        sqrtrem_step (fun x -> Big.doubleplusone x) (fun x ->
          Big.doubleplusone x) (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> Big.double x) (fun x -> Big.doubleplusone x)
          (sqrtrem p1))
        (fun _ -> (Big.one, (IsPos (Big.double
        Big.one))))
        p0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        sqrtrem_step (fun x -> Big.doubleplusone x) (fun x -> Big.double x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> Big.double x) (fun x -> Big.double x)
          (sqrtrem p1))
        (fun _ -> (Big.one, (IsPos
        Big.one)))
        p0)
      (fun _ -> (Big.one,
      IsNul))
      p
  
  (** val sqrt : Big.big_int -> Big.big_int **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec gcdn n a b =
    Big.nat_case
      (fun _ ->
      Big.one)
      (fun n0 ->
      Big.positive_case
        (fun a' ->
        Big.positive_case
          (fun b' ->
          match compare a' b' with
          | Eq -> a
          | Lt -> gcdn n0 (sub b' a') a
          | Gt -> gcdn n0 (sub a' b') b)
          (fun b0 ->
          gcdn n0 a b0)
          (fun _ ->
          Big.one)
          b)
        (fun a0 ->
        Big.positive_case
          (fun p ->
          gcdn n0 a0 b)
          (fun b0 -> Big.double
          (gcdn n0 a0 b0))
          (fun _ ->
          Big.one)
          b)
        (fun _ ->
        Big.one)
        a)
      n
  
  (** val gcd : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      Big.big_int -> Big.big_int -> Big.big_int ->
      Big.big_int * (Big.big_int * Big.big_int) **)
  
  let rec ggcdn n a b =
    Big.nat_case
      (fun _ -> (Big.one, (a,
      b)))
      (fun n0 ->
      Big.positive_case
        (fun a' ->
        Big.positive_case
          (fun b' ->
          match compare a' b' with
          | Eq -> (a, (Big.one, Big.one))
          | Lt ->
            let (g, p) = ggcdn n0 (sub b' a') a in
            let (ba, aa) = p in (g, (aa, (add aa (Big.double ba))))
          | Gt ->
            let (g, p) = ggcdn n0 (sub a' b') b in
            let (ab, bb) = p in (g, ((add bb (Big.double ab)), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a b0 in
          let (aa, bb) = p in (g, (aa, (Big.double bb))))
          (fun _ -> (Big.one, (a,
          Big.one)))
          b)
        (fun a0 ->
        Big.positive_case
          (fun p ->
          let (g, p0) = ggcdn n0 a0 b in
          let (aa, bb) = p0 in (g, ((Big.double aa), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a0 b0 in ((Big.double g), p))
          (fun _ -> (Big.one, (a,
          Big.one)))
          b)
        (fun _ -> (Big.one, (Big.one,
        b)))
        a)
      n
  
  (** val ggcd :
      Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : Big.big_int -> Big.big_int **)
  
  let coq_Nsucc_double x =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p -> (Big.doubleplusone
      p))
      x
  
  (** val coq_Ndouble : Big.big_int -> Big.big_int **)
  
  let coq_Ndouble n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p -> (Big.double
      p))
      n
  
  (** val coq_lor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_lor p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone
        (coq_lor p0 q0))
        (fun q0 -> Big.doubleplusone
        (coq_lor p0 q0))
        (fun _ ->
        p)
        q)
      (fun p0 ->
      Big.positive_case
        (fun q0 -> Big.doubleplusone
        (coq_lor p0 q0))
        (fun q0 -> Big.double
        (coq_lor p0 q0))
        (fun _ -> Big.doubleplusone
        p0)
        q)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        q)
        (fun q0 -> Big.doubleplusone
        q0)
        (fun _ ->
        q)
        q)
      p
  
  (** val coq_land : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_land p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Nsucc_double (coq_land p0 q0))
        (fun q0 ->
        coq_Ndouble (coq_land p0 q0))
        (fun _ ->
        Big.one)
        q)
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Ndouble (coq_land p0 q0))
        (fun q0 ->
        coq_Ndouble (coq_land p0 q0))
        (fun _ ->
        Big.zero)
        q)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        Big.one)
        (fun q0 ->
        Big.zero)
        (fun _ ->
        Big.one)
        q)
      p
  
  (** val ldiff : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec ldiff p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Ndouble (ldiff p0 q0))
        (fun q0 ->
        coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> (Big.double
        p0))
        q)
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Ndouble (ldiff p0 q0))
        (fun q0 ->
        coq_Ndouble (ldiff p0 q0))
        (fun _ ->
        p)
        q)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        Big.zero)
        (fun q0 ->
        Big.one)
        (fun _ ->
        Big.zero)
        q)
      p
  
  (** val coq_lxor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec coq_lxor p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Ndouble (coq_lxor p0 q0))
        (fun q0 ->
        coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> (Big.double
        p0))
        q)
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 ->
        coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> (Big.doubleplusone
        p0))
        q)
      (fun _ ->
      Big.positive_case
        (fun q0 -> (Big.double
        q0))
        (fun q0 -> (Big.doubleplusone
        q0))
        (fun _ ->
        Big.zero)
        q)
      p
  
  (** val shiftl_nat : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl_nat p n =
    nat_iter n (fun x -> Big.double x) p
  
  (** val shiftr_nat : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr_nat p n =
    nat_iter n div2 p
  
  (** val shiftl : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl p n =
    Big.n_case
      (fun _ ->
      p)
      (fun n0 ->
      iter n0 (fun x -> Big.double x) p)
      n
  
  (** val shiftr : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr p n =
    Big.n_case
      (fun _ ->
      p)
      (fun n0 ->
      iter n0 div2 p)
      n
  
  (** val testbit_nat : Big.big_int -> Big.big_int -> bool **)
  
  let rec testbit_nat p n =
    Big.positive_case
      (fun p0 ->
      Big.nat_case
        (fun _ ->
        true)
        (fun n' ->
        testbit_nat p0 n')
        n)
      (fun p0 ->
      Big.nat_case
        (fun _ ->
        false)
        (fun n' ->
        testbit_nat p0 n')
        n)
      (fun _ ->
      Big.nat_case
        (fun _ ->
        true)
        (fun n0 ->
        false)
        n)
      p
  
  (** val testbit : Big.big_int -> Big.big_int -> bool **)
  
  let rec testbit p n =
    Big.positive_case
      (fun p0 ->
      Big.n_case
        (fun _ ->
        true)
        (fun n0 ->
        testbit p0 (pred_N n0))
        n)
      (fun p0 ->
      Big.n_case
        (fun _ ->
        false)
        (fun n0 ->
        testbit p0 (pred_N n0))
        n)
      (fun _ ->
      Big.n_case
        (fun _ ->
        true)
        (fun p0 ->
        false)
        n)
      p
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    Big.positive_case
      (fun p0 ->
      op a (iter_op op p0 (op a a)))
      (fun p0 ->
      iter_op op p0 (op a a))
      (fun _ ->
      a)
      p
  
  (** val to_nat : Big.big_int -> Big.big_int **)
  
  let to_nat x =
    iter_op plus x (Big.succ Big.zero)
  
  (** val of_nat : Big.big_int -> Big.big_int **)
  
  let rec of_nat n =
    Big.nat_case
      (fun _ ->
      Big.one)
      (fun x ->
      Big.nat_case
        (fun _ ->
        Big.one)
        (fun n0 ->
        succ (of_nat x))
        x)
      n
  
  (** val of_succ_nat : Big.big_int -> Big.big_int **)
  
  let rec of_succ_nat n =
    Big.nat_case
      (fun _ ->
      Big.one)
      (fun x ->
      succ (of_succ_nat x))
      n
 end

