open Big


let xorb b1 b2 =
  if b1 then if b2 then false else true else b2


let rec length = function
  | [] -> Big.zero
  | y :: l' -> Big.succ (length l')


let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)


type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT


let rec nat_iter n f x =
  Big.nat_case
    (fun _ ->
    x)
    (fun n' ->
    f (nat_iter n' f x))
    n


module Pos =
  struct
  let rec succ x =
    Big.positive_case
      (fun p -> Big.double
      (succ p))
      (fun p -> Big.doubleplusone
      p)
      (fun _ -> Big.double
      Big.one)
      x

end

type big_int = Big_int.big_int

module type INDEXED_TYPE =
 sig
  type t
  val index : t -> big_int
  val eq : t -> t -> bool
 end



module PTree =
 struct
  type elt = big_int

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree


  let rec eq eqA a b =
    match a with
    | Leaf ->
      (match b with
       | Leaf -> true
       | Node (t0, o, t1) -> false)
    | Node (t0, o, t1) ->
      (match b with
       | Leaf -> false
       | Node (t2, o0, t3) ->
         if eq eqA t0 t2
         then if match o with
                 | Some x ->
                   (match o0 with
                    | Some a1 -> eqA x a1
                    | None -> false)
                 | None ->
                   (match o0 with
                    | Some a0 -> false
                    | None -> true)
              then eq eqA t1 t3
              else false
         else false)


  let rec set i v = function
  | Leaf ->
    (Big.positive_case
       (fun ii -> Node (Leaf, None,
       (set ii v Leaf)))
       (fun ii -> Node ((set ii v Leaf), None,
       Leaf))
       (fun _ -> Node (Leaf, (Some v),
       Leaf))
       i)
  | Node (l, o, r2) ->
    (Big.positive_case
       (fun ii -> Node (l, o,
       (set ii v r2)))
       (fun ii -> Node ((set ii v l), o,
       r2))
       (fun _ -> Node (l, (Some v),
       r2))
       i)

end




module type MACHINE_SIG =
 sig
  type location

  val size_addr :
  big_int

end

module Coq_Pos =
 struct

  let rec eq_dec p y0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
      (fun p1 ->
        eq_dec
          p0
          p1)
        (fun p1 ->
        false)
        (fun _ ->
        false)
        y0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        false)
        (fun p1 ->
        eq_dec
          p0
          p1)
        (fun _ ->
        false)
        y0)
      (fun _ ->
      Big.positive_case
        (fun p0 ->
        false)
        (fun p0 ->
        false)
        (fun _ ->
        true)
        y0)
      p

end

module Z =
 struct

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
        Coq_Pos.eq_dec x0 p0)
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
        Coq_Pos.eq_dec x0 p0)
        y)
      x

end

let zeq =
  Z.eq_dec

module Word =
 struct

  type int  = big_int


  let intval wordsize_minus_one i =
    i

  let unsigned wordsize_minus_one n =
    intval wordsize_minus_one n

    let eq_dec wordsize_minus_one x y =
    zeq x y
end



type int0
  =
  Word.int

module PMap =
 struct
  type elt = big_int

  let eq x a b =
    let x0 = PTree.eq x in
    let (x1, x2) = a in
    let (a1, t0) = b in if x x1 a1 then x0 x2 t0 else false

  let set i x m =
    ((fst m), (PTree.set i x (snd m)))


  type oracle = { oracle_bits : (big_int
                                ->
                                big_int
                                ->
                                int0);
                  oracle_offsets : big_int }


end



module IMap =
 functor (X:INDEXED_TYPE) ->
 struct

  let eq x a b =
    PMap.eq
      x
      a
      b

  let set i v m =
    PMap.set
      (X.index
        i)
      v
      m

  type oracle = { oracle_bits : (big_int
				 ->
                                big_int
                                ->
                                int0);                                                                                                                                                                             
                  oracle_offsets : big_int }

end

module ZIndexed =
 struct

  let index z =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p ->
      Big.double
      p)
      (fun p ->
      Big.doubleplusone
      p)
      z

end

module RTL =
 functor (M:MACHINE_SIG) ->
 struct
 module AddrIndexed =
   struct
    type t
      =
      int0

    (** val index :
        int0
        ->
        big_int **)

    let index i =
      ZIndexed.index
        (Word.unsigned
          M.size_addr
          i)

    (** val eq :
        Word.int
        ->
        Word.int
        ->
        bool **)

    let eq =
      Word.eq_dec
        M.size_addr
 end

 module AddrMap = IMap(AddrIndexed)



end