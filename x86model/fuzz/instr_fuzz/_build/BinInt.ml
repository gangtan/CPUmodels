open BinNat
open BinPos
open Bool
open Datatypes
open OrdersTac

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Z = 
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
  
  (** val double : Big.big_int -> Big.big_int **)
  
  let double x =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p -> (Big.double
      p))
      (fun p -> Big.opp (Big.double
      p))
      x
  
  (** val succ_double : Big.big_int -> Big.big_int **)
  
  let succ_double x =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p -> (Big.doubleplusone
      p))
      (fun p -> Big.opp
      (Pos.pred_double p))
      x
  
  (** val pred_double : Big.big_int -> Big.big_int **)
  
  let pred_double x =
    Big.z_case
      (fun _ -> Big.opp
      Big.one)
      (fun p ->
      (Pos.pred_double p))
      (fun p -> Big.opp (Big.doubleplusone
      p))
      x
  
  (** val pos_sub : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec pos_sub x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q ->
        double (pos_sub p q))
        (fun q ->
        succ_double (pos_sub p q))
        (fun _ -> (Big.double
        p))
        y)
      (fun p ->
      Big.positive_case
        (fun q ->
        pred_double (pos_sub p q))
        (fun q ->
        double (pos_sub p q))
        (fun _ ->
        (Pos.pred_double p))
        y)
      (fun _ ->
      Big.positive_case
        (fun q -> Big.opp (Big.double
        q))
        (fun q -> Big.opp
        (Pos.pred_double q))
        (fun _ ->
        Big.zero)
        y)
      x
  
  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let add = Big.add
  
  (** val opp : Big.big_int -> Big.big_int **)
  
  let opp = Big.opp
  
  (** val succ : Big.big_int -> Big.big_int **)
  
  let succ = Big.succ
  
  (** val pred : Big.big_int -> Big.big_int **)
  
  let pred = Big.pred
  
  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let sub = Big.sub
  
  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let mul = Big.mult
  
  (** val pow_pos : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let pow_pos z n =
    Pos.iter n (mul z) Big.one
  
  (** val pow : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let pow x y =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p ->
      pow_pos x p)
      (fun p ->
      Big.zero)
      y
  
  (** val square : Big.big_int -> Big.big_int **)
  
  let square x =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Pos.square p))
      (fun p ->
      (Pos.square p))
      x
  
  (** val compare : Big.big_int -> Big.big_int -> comparison **)
  
  let compare = Big.compare_case Eq Lt Gt
  
  (** val sgn : Big.big_int -> Big.big_int **)
  
  let sgn z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.one)
      (fun p -> Big.opp
      Big.one)
      z
  
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
  
  (** val geb : Big.big_int -> Big.big_int -> bool **)
  
  let geb x y =
    match compare x y with
    | Lt -> false
    | _ -> true
  
  (** val gtb : Big.big_int -> Big.big_int -> bool **)
  
  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false
  
  (** val eqb : Big.big_int -> Big.big_int -> bool **)
  
  let rec eqb x y =
    Big.z_case
      (fun _ ->
      Big.z_case
        (fun _ ->
        true)
        (fun p ->
        false)
        (fun p ->
        false)
        y)
      (fun p ->
      Big.z_case
        (fun _ ->
        false)
        (fun q ->
        Pos.eqb p q)
        (fun p0 ->
        false)
        y)
      (fun p ->
      Big.z_case
        (fun _ ->
        false)
        (fun p0 ->
        false)
        (fun q ->
        Pos.eqb p q)
        y)
      x
  
  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let max = Big.max
  
  (** val min : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let min = Big.min
  
  (** val abs : Big.big_int -> Big.big_int **)
  
  let abs = Big.abs
  
  (** val abs_nat : Big.big_int -> Big.big_int **)
  
  let abs_nat z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Pos.to_nat p)
      (fun p ->
      Pos.to_nat p)
      z
  
  (** val abs_N : Big.big_int -> Big.big_int **)
  
  let abs_N = Big.abs
  
  (** val to_nat : Big.big_int -> Big.big_int **)
  
  let to_nat z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Pos.to_nat p)
      (fun p ->
      Big.zero)
      z
  
  (** val to_N : Big.big_int -> Big.big_int **)
  
  let to_N z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      p)
      (fun p ->
      Big.zero)
      z
  
  (** val of_nat : Big.big_int -> Big.big_int **)
  
  let of_nat n =
    Big.nat_case
      (fun _ ->
      Big.zero)
      (fun n0 ->
      (Pos.of_succ_nat n0))
      n
  
  (** val of_N : Big.big_int -> Big.big_int **)
  
  let of_N = fun p -> p
  
  (** val to_pos : Big.big_int -> Big.big_int **)
  
  let to_pos z =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p ->
      p)
      (fun p ->
      Big.one)
      z
  
  (** val iter : Big.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n f x =
    Big.z_case
      (fun _ ->
      x)
      (fun p ->
      Pos.iter p f x)
      (fun p ->
      x)
      n
  
  (** val pos_div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)
  
  let rec pos_div_eucl a b =
    Big.positive_case
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Big.double Big.one) r) Big.one in
      if ltb r' b
      then ((mul (Big.double Big.one) q), r')
      else ((add (mul (Big.double Big.one) q) Big.one), (sub r' b)))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Big.double Big.one) r in
      if ltb r' b
      then ((mul (Big.double Big.one) q), r')
      else ((add (mul (Big.double Big.one) q) Big.one), (sub r' b)))
      (fun _ ->
      if leb (Big.double Big.one) b
      then (Big.zero, Big.one)
      else (Big.one, Big.zero))
      a
  
  (** val div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)
  
  let div_eucl a b =
    Big.z_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun a' ->
      Big.z_case
        (fun _ -> (Big.zero,
        Big.zero))
        (fun p ->
        pos_div_eucl a' b)
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in
        (Big.z_case
           (fun _ -> ((opp q),
           Big.zero))
           (fun p -> ((opp (add q Big.one)),
           (add b r)))
           (fun p -> ((opp (add q Big.one)),
           (add b r)))
           r))
        b)
      (fun a' ->
      Big.z_case
        (fun _ -> (Big.zero,
        Big.zero))
        (fun p ->
        let (q, r) = pos_div_eucl a' b in
        (Big.z_case
           (fun _ -> ((opp q),
           Big.zero))
           (fun p0 -> ((opp (add q Big.one)),
           (sub b r)))
           (fun p0 -> ((opp (add q Big.one)),
           (sub b r)))
           r))
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in (q, (opp r)))
        b)
      a
  
  (** val div : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let div a b =
    let (q, x) = div_eucl a b in q
  
  (** val modulo : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let modulo a b =
    let (x, r) = div_eucl a b in r
  
  (** val quotrem :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)
  
  let quotrem a b =
    Big.z_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun a0 ->
      Big.z_case
        (fun _ -> (Big.zero,
        a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (of_N r)))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (of_N r)))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ -> (Big.zero,
        a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (opp (of_N r))))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (opp (of_N r))))
        b)
      a
  
  (** val quot : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let quot a b =
    fst (quotrem a b)
  
  (** val rem : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rem a b =
    snd (quotrem a b)
  
  (** val even : Big.big_int -> bool **)
  
  let even z =
    Big.z_case
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
      (fun p ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        true)
        (fun _ ->
        false)
        p)
      z
  
  (** val odd : Big.big_int -> bool **)
  
  let odd z =
    Big.z_case
      (fun _ ->
      false)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        true)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        p)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        true)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        p)
      z
  
  (** val div2 : Big.big_int -> Big.big_int **)
  
  let div2 z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        (Pos.div2 p))
        (fun p0 ->
        (Pos.div2 p))
        (fun _ ->
        Big.zero)
        p)
      (fun p -> Big.opp
      (Pos.div2_up p))
      z
  
  (** val quot2 : Big.big_int -> Big.big_int **)
  
  let quot2 z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.positive_case
        (fun p0 ->
        (Pos.div2 p))
        (fun p0 ->
        (Pos.div2 p))
        (fun _ ->
        Big.zero)
        p)
      (fun p ->
      Big.positive_case
        (fun p0 -> Big.opp
        (Pos.div2 p))
        (fun p0 -> Big.opp
        (Pos.div2 p))
        (fun _ ->
        Big.zero)
        p)
      z
  
  (** val log2 : Big.big_int -> Big.big_int **)
  
  let log2 z =
    Big.z_case
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
      (fun p ->
      Big.zero)
      z
  
  (** val sqrtrem : Big.big_int -> Big.big_int * Big.big_int **)
  
  let sqrtrem n =
    Big.z_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun p ->
      let (s, m) = Pos.sqrtrem p in
      (match m with
       | Pos.IsPos r -> (s, r)
       | _ -> (s, Big.zero)))
      (fun p -> (Big.zero,
      Big.zero))
      n
  
  (** val sqrt : Big.big_int -> Big.big_int **)
  
  let sqrt n =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      (Pos.sqrt p))
      (fun p ->
      Big.zero)
      n
  
  (** val gcd : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let gcd a b =
    Big.z_case
      (fun _ ->
      abs b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        abs a)
        (fun b0 ->
        (Pos.gcd a0 b0))
        (fun b0 ->
        (Pos.gcd a0 b0))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        abs a)
        (fun b0 ->
        (Pos.gcd a0 b0))
        (fun b0 ->
        (Pos.gcd a0 b0))
        b)
      a
  
  (** val ggcd :
      Big.big_int -> Big.big_int -> Big.big_int * (Big.big_int * Big.big_int) **)
  
  let ggcd a b =
    Big.z_case
      (fun _ -> ((abs b), (Big.zero,
      (sgn b))))
      (fun a0 ->
      Big.z_case
        (fun _ -> ((abs a), ((sgn a),
        Big.zero)))
        (fun b0 ->
        let (g, p) = Pos.ggcd a0 b0 in let (aa, bb) = p in (g, (aa, bb)))
        (fun b0 ->
        let (g, p) = Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (aa, (Big.opp bb))))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ -> ((abs a), ((sgn a),
        Big.zero)))
        (fun b0 ->
        let (g, p) = Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, ((Big.opp aa), bb)))
        (fun b0 ->
        let (g, p) = Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, ((Big.opp aa), (Big.opp bb))))
        b)
      a
  
  (** val testbit : Big.big_int -> Big.big_int -> bool **)
  
  let testbit a n =
    Big.z_case
      (fun _ ->
      odd a)
      (fun p ->
      Big.z_case
        (fun _ ->
        false)
        (fun a0 ->
        Pos.testbit a0 p)
        (fun a0 ->
        negb (N.testbit (Pos.pred_N a0) p))
        a)
      (fun p ->
      false)
      n
  
  (** val shiftl : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftl a n =
    Big.z_case
      (fun _ ->
      a)
      (fun p ->
      Pos.iter p (mul (Big.double Big.one)) a)
      (fun p ->
      Pos.iter p div2 a)
      n
  
  (** val shiftr : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let shiftr a n =
    shiftl a (opp n)
  
  (** val coq_lor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_lor a b =
    Big.z_case
      (fun _ ->
      b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 ->
        (Pos.coq_lor a0 b0))
        (fun b0 -> Big.opp
        (N.succ_pos (N.ldiff (Pos.pred_N b0) a0)))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 -> Big.opp
        (N.succ_pos (N.ldiff (Pos.pred_N a0) b0)))
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_land (Pos.pred_N a0) (Pos.pred_N b0))))
        b)
      a
  
  (** val coq_land : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_land a b =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        Big.zero)
        (fun b0 ->
        of_N (Pos.coq_land a0 b0))
        (fun b0 ->
        of_N (N.ldiff a0 (Pos.pred_N b0)))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        Big.zero)
        (fun b0 ->
        of_N (N.ldiff b0 (Pos.pred_N a0)))
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_lor (Pos.pred_N a0) (Pos.pred_N b0))))
        b)
      a
  
  (** val ldiff : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let ldiff a b =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 ->
        of_N (Pos.ldiff a0 b0))
        (fun b0 ->
        of_N (N.coq_land a0 (Pos.pred_N b0)))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_lor (Pos.pred_N a0) b0)))
        (fun b0 ->
        of_N (N.ldiff (Pos.pred_N b0) (Pos.pred_N a0)))
        b)
      a
  
  (** val coq_lxor : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let coq_lxor a b =
    Big.z_case
      (fun _ ->
      b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 ->
        of_N (Pos.coq_lxor a0 b0))
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_lxor a0 (Pos.pred_N b0))))
        b)
      (fun a0 ->
      Big.z_case
        (fun _ ->
        a)
        (fun b0 -> Big.opp
        (N.succ_pos (N.coq_lxor (Pos.pred_N a0) b0)))
        (fun b0 ->
        of_N (N.coq_lxor (Pos.pred_N a0) (Pos.pred_N b0)))
        b)
      a
  
  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)
  
  let eq_dec x y =
    Big.z_case
      (fun _ ->
      Big.z_case
        (fun _ ->
        true)
        (fun p ->
        false)
        (fun p ->
        false)
        y)
      (fun x0 ->
      Big.z_case
        (fun _ ->
        false)
        (fun p0 ->
        Pos.eq_dec x0 p0)
        (fun p0 ->
        false)
        y)
      (fun x0 ->
      Big.z_case
        (fun _ ->
        false)
        (fun p0 ->
        false)
        (fun p0 ->
        Pos.eq_dec x0 p0)
        y)
      x
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val leb_spec0 : Big.big_int -> Big.big_int -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : Big.big_int -> Big.big_int -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_OrderTac = 
   struct 
    module Elts = 
     struct 
      type t = Big.big_int
     end
    
    module Tac = MakeOrderTac(Elts)
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
  
  module Private_Div = 
   struct 
    module Quot2Div = 
     struct 
      (** val div : Big.big_int -> Big.big_int -> Big.big_int **)
      
      let div =
        quot
      
      (** val modulo : Big.big_int -> Big.big_int -> Big.big_int **)
      
      let modulo =
        rem
     end
    
    module NZQuot = 
     struct 
      
     end
   end
  
  (** val lcm : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let lcm a b =
    abs (mul a (div b (gcd a b)))
  
  (** val eqb_spec : Big.big_int -> Big.big_int -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2z : bool -> Big.big_int **)
  
  let b2z = function
  | true -> Big.one
  | false -> Big.zero
  
  (** val setbit : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let setbit a n =
    coq_lor a (shiftl Big.one n)
  
  (** val clearbit : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let clearbit a n =
    ldiff a (shiftl Big.one n)
  
  (** val lnot : Big.big_int -> Big.big_int **)
  
  let lnot a =
    pred (opp a)
  
  (** val ones : Big.big_int -> Big.big_int **)
  
  let ones n =
    pred (shiftl Big.one n)
  
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

module Pos2Z = 
 struct 
  
 end

module Z2Pos = 
 struct 
  
 end

