open BinPos
open Bool
open Datatypes
open OrdersTac
open Peano

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module N = 
 struct 
  type t = Big.big_int
  
  (** val zero : Big.big_int **)
  
  let zero =
    Big.zero
  
  (** val one : Big.big_int **)
  
  let one =
    Big.one
  
  (** val two : Big.big_int **)
  
  let two =
    (Big.double Big.one)
  
  (** val succ_double : Big.big_int -> Big.big_int **)
  
  let succ_double x =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p -> (Big.doubleplusone
      p))
      x
  
  (** val double : Big.big_int -> Big.big_int **)
  
  let double n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p -> (Big.double
      p))
      n
  
  (** val succ : Big.big_int -> Big.big_int **)
  
  let succ = Big.succ
  
  (** val pred : Big.big_int -> Big.big_int **)
  
  let pred = fun n -> Big.max Big.zero (Big.pred n)
  
  (** val succ_pos : Big.big_int -> Big.big_int **)
  
  let succ_pos n =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p ->
      Pos.succ p)
      n
  
  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let add = Big.add
  
  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let sub = fun n m -> Big.max Big.zero (Big.sub n m)
  
  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let mul = Big.mult
  
  (** val compare : Big.big_int -> Big.big_int -> comparison **)
  
  let compare = Big.compare_case Eq Lt Gt
  
  (** val eqb : Big.big_int -> Big.big_int -> bool **)
  
  let rec eqb n m =
    Big.n_case
      (fun _ ->
      Big.n_case
        (fun _ ->
        true)
        (fun p ->
        false)
        m)
      (fun p ->
      Big.n_case
        (fun _ ->
        false)
        (fun q ->
        Pos.eqb p q)
        m)
      n
  
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
  
  (** val min : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let min = Big.min
  
  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let max = Big.max
  
  (** val div2 : Big.big_int -> Big.big_int **)
  
  let div2 n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p0 ->
      Big.positive_case
        (fun p ->
        p)
        (fun p ->
        p)
        (fun _ ->
        Big.zero)
        p0)
      n
  
  (** val even : Big.big_int -> bool **)
  
  let even n =
    Big.n_case
      (fun _ ->
      true)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        true)
        (fun _ ->
        false)
        p)
      n
  
  (** val odd : Big.big_int -> bool **)
  
  let odd n =
    negb (even n)
  
  (** val pow : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let pow n p =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p0 ->
      Big.n_case
        (fun _ ->
        Big.zero)
        (fun q ->
        (Pos.pow q p0))
        n)
      p
  
  (** val square : Big.big_int -> Big.big_int **)
  
  let square n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Pos.square p))
      n
  
  (** val log2 : Big.big_int -> Big.big_int **)
  
  let log2 n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p0 ->
      Big.positive_case
        (fun p ->
        (Pos.size p))
        (fun p ->
        (Pos.size p))
        (fun _ ->
        Big.zero)
        p0)
      n
  
  (** val size : Big.big_int -> Big.big_int **)
  
  let size n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Pos.size p))
      n
  
  (** val size_nat : Big.big_int -> Big.big_int **)
  
  let size_nat n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Pos.size_nat p)
      n
  
  (** val pos_div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)
  
  let rec pos_div_eucl a b =
    Big.positive_case
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun _ ->
      Big.n_case
        (fun _ -> (Big.zero,
        Big.one))
        (fun p ->
        Big.positive_case
          (fun p0 -> (Big.zero,
          Big.one))
          (fun p0 -> (Big.zero,
          Big.one))
          (fun _ -> (Big.one,
          Big.zero))
          p)
        b)
      a
  
  (** val div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)
  
  let div_eucl a b =
    Big.n_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun na ->
      Big.n_case
        (fun _ -> (Big.zero,
        a))
        (fun p ->
        pos_div_eucl na b)
        b)
      a
  
  (** val div : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let div = fun a b -> if Big.eq b Big.zero then Big.zero else Big.div a b
  
  (** val modulo : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let modulo = fun a b -> if Big.eq b Big.zero then Big.zero else Big.modulo a b
  
  (** val gcd : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let gcd a b =
    Big.n_case
      (fun _ ->
      b)
      (fun p ->
      Big.n_case
        (fun _ ->
        a)
        (fun q ->
        (Pos.gcd p q))
        b)
      a
  
  (** val ggcd :
      Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int) **)
  
  let ggcd a b =
    Big.n_case
      (fun _ -> (b, (Big.zero,
      Big.one)))
      (fun p ->
      Big.n_case
        (fun _ -> (a, (Big.one,
        Big.zero)))
        (fun q ->
        let (g, p0) = Pos.ggcd p q in let (aa, bb) = p0 in (g, (aa, bb)))
        b)
      a
  
  (** val sqrtrem : Big.big_int -> Big.big_int * Big.big_int **)
  
  let sqrtrem n =
    Big.n_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun p ->
      let (s, m) = Pos.sqrtrem p in
      (match m with
       | Pos.IsPos r -> (s, r)
       | _ -> (s, Big.zero)))
      n
  
  (** val sqrt : Big.big_int -> Big.big_int **)
  
  let sqrt n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Pos.sqrt p))
      n
  
  (** val coq_lor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_lor n m =
    Big.n_case
      (fun _ ->
      m)
      (fun p ->
      Big.n_case
        (fun _ ->
        n)
        (fun q ->
        (Pos.coq_lor p q))
        m)
      n
  
  (** val coq_land : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_land n m =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.n_case
        (fun _ ->
        Big.zero)
        (fun q ->
        Pos.coq_land p q)
        m)
      n
  
  (** val ldiff : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec ldiff n m =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.n_case
        (fun _ ->
        n)
        (fun q ->
        Pos.ldiff p q)
        m)
      n
  
  (** val coq_lxor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_lxor n m =
    Big.n_case
      (fun _ ->
      m)
      (fun p ->
      Big.n_case
        (fun _ ->
        n)
        (fun q ->
        Pos.coq_lxor p q)
        m)
      n
  
  (** val shiftl_nat : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl_nat a n =
    nat_iter n double a
  
  (** val shiftr_nat : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr_nat a n =
    nat_iter n div2 a
  
  (** val shiftl : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl a n =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun a0 ->
      (Pos.shiftl a0 n))
      a
  
  (** val shiftr : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr a n =
    Big.n_case
      (fun _ ->
      a)
      (fun p ->
      Pos.iter p div2 a)
      n
  
  (** val testbit_nat : Big.big_int -> Big.big_int -> bool **)
  
  let testbit_nat a =
    Big.n_case
      (fun _ x ->
      false)
      (fun p ->
      Pos.testbit_nat p)
      a
  
  (** val testbit : Big.big_int -> Big.big_int -> bool **)
  
  let testbit a n =
    Big.n_case
      (fun _ ->
      false)
      (fun p ->
      Pos.testbit p n)
      a
  
  (** val to_nat : Big.big_int -> Big.big_int **)
  
  let to_nat a =
    Big.n_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Pos.to_nat p)
      a
  
  (** val of_nat : Big.big_int -> Big.big_int **)
  
  let of_nat n =
    Big.nat_case
      (fun _ ->
      Big.zero)
      (fun n' ->
      (Pos.of_succ_nat n'))
      n
  
  (** val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n f x =
    Big.n_case
      (fun _ ->
      x)
      (fun p ->
      Pos.iter p f x)
      n
  
  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)
  
  let eq_dec n m =
    Big.n_case
      (fun _ ->
      Big.n_case
        (fun _ ->
        true)
        (fun p ->
        false)
        m)
      (fun x ->
      Big.n_case
        (fun _ ->
        false)
        (fun p0 ->
        Pos.eq_dec x p0)
        m)
      n
  
  (** val discr : Big.big_int -> Big.big_int option **)
  
  let discr n =
    Big.n_case
      (fun _ ->
      None)
      (fun p -> Some
      p)
      n
  
  (** val binary_rect :
      'a1 -> (Big.big_int -> 'a1 -> 'a1) -> (Big.big_int -> 'a1 -> 'a1) ->
      Big.big_int -> 'a1 **)
  
  let binary_rect f0 f2 fS2 n =
    let f2' = fun p -> f2 p in
    let fS2' = fun p -> fS2 p in
    (Big.n_case
       (fun _ ->
       f0)
       (fun p ->
       let rec f p0 =
         Big.positive_case
           (fun p1 ->
           fS2' p1 (f p1))
           (fun p1 ->
           f2' p1 (f p1))
           (fun _ ->
           fS2 Big.zero f0)
           p0
       in f p)
       n)
  
  (** val binary_rec :
      'a1 -> (Big.big_int -> 'a1 -> 'a1) -> (Big.big_int -> 'a1 -> 'a1) ->
      Big.big_int -> 'a1 **)
  
  let binary_rec =
    binary_rect
  
  (** val peano_rect :
      'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1 **)
  
  let peano_rect f0 f n =
    let f' = fun p -> f p in
    (Big.n_case
       (fun _ ->
       f0)
       (fun p ->
       Pos.peano_rect (f Big.zero f0) f' p)
       n)
  
  (** val peano_rec :
      'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  (** val leb_spec0 : Big.big_int -> Big.big_int -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : Big.big_int -> Big.big_int -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val recursion :
      'a1 -> (Big.big_int -> 'a1 -> 'a1) -> Big.big_int -> 'a1 **)
  
  let recursion x =
    peano_rect x
  
  module Private_OrderTac = 
   struct 
    module Elts = 
     struct 
      type t = Big.big_int
     end
    
    module Tac = MakeOrderTac(Elts)
   end
  
  module Private_NZPow = 
   struct 
    
   end
  
  module Private_NZSqrt = 
   struct 
    
   end
  
  (** val sqrt_up : Big.big_int -> Big.big_int **)
  
  let sqrt_up a =
    match compare Big.zero a with
    | Lt -> succ (sqrt (pred a))
    | _ -> Big.zero
  
  (** val log2_up : Big.big_int -> Big.big_int **)
  
  let log2_up a =
    match compare Big.one a with
    | Lt -> succ (log2 (pred a))
    | _ -> Big.zero
  
  module Private_NZDiv = 
   struct 
    
   end
  
  (** val lcm : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let lcm a b =
    mul a (div b (gcd a b))
  
  (** val eqb_spec : Big.big_int -> Big.big_int -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2n : bool -> Big.big_int **)
  
  let b2n = function
  | true -> Big.one
  | false -> Big.zero
  
  (** val setbit : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let setbit a n =
    coq_lor a (shiftl Big.one n)
  
  (** val clearbit : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let clearbit a n =
    ldiff a (shiftl Big.one n)
  
  (** val ones : Big.big_int -> Big.big_int **)
  
  let ones n =
    pred (shiftl Big.one n)
  
  (** val lnot : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let lnot a n =
    coq_lxor a (ones n)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Rev = 
   struct 
    module ORev = 
     struct 
      type t = Big.big_int
     end
    
    module MRev = 
     struct 
      (** val max : Big.big_int -> Big.big_int -> Big.big_int **)
      
      let max x y =
        min y x
     end
    
    module MPRev = GenericMinMax.MaxLogicalProperties(ORev)(MRev)
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let max_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))
    
    (** val max_case :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : Big.big_int -> Big.big_int -> bool **)
    
    let max_dec n m =
      max_case n m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let min_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))
    
    (** val min_case :
        Big.big_int -> Big.big_int -> (Big.big_int -> Big.big_int -> __ ->
        'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : Big.big_int -> Big.big_int -> bool **)
    
    let min_dec n m =
      min_case n m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong :
      Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : Big.big_int -> Big.big_int -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      Big.big_int -> Big.big_int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : Big.big_int -> Big.big_int -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : Big.big_int -> Big.big_int -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

(** val coq_N_rec_double :
    Big.big_int -> 'a1 -> (Big.big_int -> 'a1 -> 'a1) -> (Big.big_int -> 'a1
    -> 'a1) -> 'a1 **)

let coq_N_rec_double a f0 f2 fS2 =
  N.binary_rec f0 f2 fS2 a

