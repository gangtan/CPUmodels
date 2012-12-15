open Coqlib
open Datatypes
open List0

module type TREE = 
 sig 
  type elt 
  
  val elt_eq : elt -> elt -> bool
  
  type 'x t 
  
  val eq : 'a -> 'b -> 'c -> 'd -> 'e -> bool
  
  val empty : 'a1 t
  
  val get : elt -> 'a1 t -> 'a1 option
  
  val set : elt -> 'a1 -> 'a1 t -> 'a1 t
  
  val remove : elt -> 'a1 t -> 'a1 t
  
  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val map : (elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val combine :
    ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t -> 'a1 t
  
  val elements : 'a1 t -> (elt * 'a1) list
  
  val fold : ('a2 -> elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
 end

module type MAP = 
 sig 
  type elt 
  
  val elt_eq : elt -> elt -> bool
  
  type 'x t 
  
  val init : 'a1 -> 'a1 t
  
  val get : elt -> 'a1 t -> 'a1
  
  val set : elt -> 'a1 -> 'a1 t -> 'a1 t
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module PTree = 
 struct 
  type elt = Big.big_int
  
  (** val elt_eq : Big.big_int -> Big.big_int -> bool **)
  
  let elt_eq =
    peq
  
  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree
  
  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> 'a1 option -> 'a1 tree -> 'a2 -> 'a2) -> 'a1
      tree -> 'a2 **)
  
  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t1, o, t2) -> f0 t1 (tree_rect f f0 t1) o t2 (tree_rect f f0 t2)
  
  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> 'a1 option -> 'a1 tree -> 'a2 -> 'a2) -> 'a1
      tree -> 'a2 **)
  
  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t1, o, t2) -> f0 t1 (tree_rec f f0 t1) o t2 (tree_rec f f0 t2)
  
  type 'a t = 'a tree
  
  (** val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let eq =
(*    failwith "AXIOM TO BE REALIZED" *)
  fun _ _ _ _ _ -> false
  
  (** val empty : 'a1 t **)
  
  let empty =
    Leaf
  
  (** val get : Big.big_int -> 'a1 t -> 'a1 option **)
  
  let rec get i = function
  | Leaf -> None
  | Node (l, o, r) ->
    (Big.positive_case
       (fun ii ->
       get ii r)
       (fun ii ->
       get ii l)
       (fun _ ->
       o)
       i)
  
  (** val set : Big.big_int -> 'a1 -> 'a1 t -> 'a1 t **)
  
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
  | Node (l, o, r) ->
    (Big.positive_case
       (fun ii -> Node (l, o,
       (set ii v r)))
       (fun ii -> Node ((set ii v l), o,
       r))
       (fun _ -> Node (l, (Some v),
       r))
       i)
  
  (** val remove : Big.big_int -> 'a1 t -> 'a1 t **)
  
  let rec remove i m =
    Big.positive_case
      (fun ii ->
      match m with
      | Leaf -> Leaf
      | Node (l, o, r) ->
        (match l with
         | Leaf ->
           (match o with
            | Some a -> Node (l, o, (remove ii r))
            | None ->
              (match remove ii r with
               | Leaf -> Leaf
               | Node (t0, o0, t1) -> Node (Leaf, None, (Node (t0, o0, t1)))))
         | Node (t0, o0, t1) -> Node (l, o, (remove ii r))))
      (fun ii ->
      match m with
      | Leaf -> Leaf
      | Node (l, o, r) ->
        (match o with
         | Some a -> Node ((remove ii l), o, r)
         | None ->
           (match r with
            | Leaf ->
              (match remove ii l with
               | Leaf -> Leaf
               | Node (t0, o0, t1) -> Node ((Node (t0, o0, t1)), None, Leaf))
            | Node (t0, o0, t1) -> Node ((remove ii l), o, r))))
      (fun _ ->
      match m with
      | Leaf -> Leaf
      | Node (l, o, r) ->
        (match l with
         | Leaf ->
           (match r with
            | Leaf -> Leaf
            | Node (t0, o0, t1) -> Node (l, None, r))
         | Node (t0, o0, t1) -> Node (l, None, r)))
      i
  
  (** val bempty : 'a1 t -> bool **)
  
  let rec bempty = function
  | Leaf -> true
  | Node (l, o, r) ->
    (match o with
     | Some a -> false
     | None -> (&&) (bempty l) (bempty r))
  
  (** val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let rec beq beqA m1 m2 =
    match m1 with
    | Leaf -> bempty m2
    | Node (l1, o1, r1) ->
      (match m2 with
       | Leaf -> bempty m1
       | Node (l2, o2, r2) ->
         (&&)
           ((&&)
             (match o1 with
              | Some y1 ->
                (match o2 with
                 | Some y2 -> beqA y1 y2
                 | None -> false)
              | None ->
                (match o2 with
                 | Some a -> false
                 | None -> true)) (beq beqA l1 l2)) (beq beqA r1 r2))
  
  (** val append : Big.big_int -> Big.big_int -> Big.big_int **)
  
  let rec append i j =
    Big.positive_case
      (fun ii -> Big.doubleplusone
      (append ii j))
      (fun ii -> Big.double
      (append ii j))
      (fun _ ->
      j)
      i
  
  (** val xmap :
      (Big.big_int -> 'a1 -> 'a2) -> 'a1 t -> Big.big_int -> 'a2 t **)
  
  let rec xmap f m i =
    match m with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      Node ((xmap f l (append i (Big.double Big.one))),
        (Coqlib.option_map (f i) o),
        (xmap f r (append i (Big.doubleplusone Big.one))))
  
  (** val map : (Big.big_int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let map f m =
    xmap f m Big.one
  
  (** val coq_Node' : 'a1 t -> 'a1 option -> 'a1 t -> 'a1 t **)
  
  let coq_Node' l x r =
    match l with
    | Leaf ->
      (match x with
       | Some a -> Node (l, x, r)
       | None ->
         (match r with
          | Leaf -> Leaf
          | Node (t0, o, t1) -> Node (l, x, r)))
    | Node (t0, o, t1) -> Node (l, x, r)
  
  (** val xcombine_l :
      ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t **)
  
  let rec xcombine_l f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> coq_Node' (xcombine_l f l) (f o None) (xcombine_l f r)
  
  (** val xcombine_r :
      ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t **)
  
  let rec xcombine_r f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> coq_Node' (xcombine_r f l) (f None o) (xcombine_r f r)
  
  (** val combine :
      ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t -> 'a1 t **)
  
  let rec combine f m1 m2 =
    match m1 with
    | Leaf -> xcombine_r f m2
    | Node (l1, o1, r1) ->
      (match m2 with
       | Leaf -> xcombine_l f m1
       | Node (l2, o2, r2) ->
         coq_Node' (combine f l1 l2) (f o1 o2) (combine f r1 r2))
  
  (** val xelements : 'a1 t -> Big.big_int -> (Big.big_int * 'a1) list **)
  
  let rec xelements m i =
    match m with
    | Leaf -> []
    | Node (l, o, r) ->
      (match o with
       | Some x ->
         app (xelements l (append i (Big.double Big.one))) ((i,
           x) :: (xelements r (append i (Big.doubleplusone Big.one))))
       | None ->
         app (xelements l (append i (Big.double Big.one)))
           (xelements r (append i (Big.doubleplusone Big.one))))
  
  (** val elements : 'a1 t -> (Big.big_int * 'a1) list **)
  
  let elements m =
    xelements m Big.one
  
  (** val xget : Big.big_int -> Big.big_int -> 'a1 t -> 'a1 option **)
  
  let rec xget i j m =
    Big.positive_case
      (fun ii ->
      Big.positive_case
        (fun jj ->
        xget ii jj m)
        (fun p ->
        None)
        (fun _ ->
        get i m)
        j)
      (fun ii ->
      Big.positive_case
        (fun p ->
        None)
        (fun jj ->
        xget ii jj m)
        (fun _ ->
        get i m)
        j)
      (fun _ ->
      Big.positive_case
        (fun p ->
        None)
        (fun p ->
        None)
        (fun _ ->
        get i m)
        j)
      i
  
  (** val xkeys : 'a1 t -> Big.big_int -> Big.big_int list **)
  
  let xkeys m i =
    List0.map fst (xelements m i)
  
  (** val xfold :
      ('a2 -> Big.big_int -> 'a1 -> 'a2) -> Big.big_int -> 'a1 t -> 'a2 ->
      'a2 **)
  
  let rec xfold f i m v =
    match m with
    | Leaf -> v
    | Node (l, o, r) ->
      (match o with
       | Some x ->
         let v1 = xfold f (append i (Big.double Big.one)) l v in
         let v2 = f v1 i x in
         xfold f (append i (Big.doubleplusone Big.one)) r v2
       | None ->
         let v1 = xfold f (append i (Big.double Big.one)) l v in
         xfold f (append i (Big.doubleplusone Big.one)) r v1)
  
  (** val fold :
      ('a2 -> Big.big_int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)
  
  let fold f m v =
    xfold f Big.one m v
 end

module PMap = 
 struct 
  type elt = Big.big_int
  
  (** val elt_eq : Big.big_int -> Big.big_int -> bool **)
  
  let elt_eq =
    peq
  
  type 'a t = 'a * 'a PTree.t
  
  (** val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let eq =
   (* failwith "AXIOM TO BE REALIZED"*)
   fun _ _  false  _ _ -> false 
  
  (** val init : 'a1 -> 'a1 * 'a1 PTree.t **)
  
  let init x =
    (x, PTree.empty)
  
  (** val get : Big.big_int -> 'a1 t -> 'a1 **)
  
  let get i m =
    match PTree.get i (snd m) with
    | Some x -> x
    | None -> fst m
  
  (** val set : Big.big_int -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.t **)
  
  let set i x m =
    ((fst m), (PTree.set i x (snd m)))
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let map f m =
    ((f (fst m)), (PTree.map (fun x -> f) (snd m)))
 end

module type INDEXED_TYPE = 
 sig 
  type t 
  
  val index : t -> Big.big_int
  
  val eq : t -> t -> bool
 end

module IMap = 
 functor (X:INDEXED_TYPE) ->
 struct 
  type elt = X.t
  
  (** val elt_eq : X.t -> X.t -> bool **)
  
  let elt_eq =
    X.eq
  
  type 'x t = 'x PMap.t
  
  (** val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let eq x a b =
   (* PMap.eq x a b *) true
  
  (** val init : 'a1 -> 'a1 * 'a1 PTree.t **)
  
  let init x =
    PMap.init x
  
  (** val get : X.t -> 'a1 t -> 'a1 **)
  
  let get i m =
    PMap.get (X.index i) m
  
  (** val set : X.t -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.t **)
  
  let set i v m =
    PMap.set (X.index i) v m
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let map f m =
    PMap.map f m
 end

module ZIndexed = 
 struct 
  type t = Big.big_int
  
  (** val index : Big.big_int -> Big.big_int **)
  
  let index z =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p -> Big.double
      p)
      (fun p -> Big.doubleplusone
      p)
      z
  
  (** val eq : Big.big_int -> Big.big_int -> bool **)
  
  let eq =
    zeq
 end

module ZMap = IMap(ZIndexed)

module NIndexed = 
 struct 
  type t = Big.big_int
  
  (** val index : Big.big_int -> Big.big_int **)
  
  let index n =
    Big.n_case
      (fun _ ->
      Big.one)
      (fun p -> Big.double
      p)
      n
  
  (** val eq : Big.big_int -> Big.big_int -> bool **)
  
  let eq =
   fun _ _ -> false
   (* failwith "AXIOM TO BE REALIZED" *)
 end

module NMap = IMap(NIndexed)

module type EQUALITY_TYPE = 
 sig 
  type t 
  
  val eq : t -> t -> bool
 end

module EMap = 
 functor (X:EQUALITY_TYPE) ->
 struct 
  type elt = X.t
  
  (** val elt_eq : X.t -> X.t -> bool **)
  
  let elt_eq =
    X.eq
  
  type 'a t = X.t -> 'a
  
  (** val init : 'a1 -> X.t -> 'a1 **)
  
  let init v x =
    v
  
  (** val get : X.t -> 'a1 t -> 'a1 **)
  
  let get x m =
    m x
  
  (** val set : X.t -> 'a1 -> 'a1 t -> X.t -> 'a1 **)
  
  let set x v m y =
    if X.eq y x then v else m y
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> X.t -> 'a2 **)
  
  let map f m x =
    f (m x)
 end

module Tree_Properties = 
 functor (T:TREE) ->
 struct 
  (** val f' :
      ('a2 -> T.elt -> 'a1 -> 'a2) -> 'a2 -> (T.elt * 'a1) -> 'a2 **)
  
  let f' f a p =
    f a (fst p) (snd p)
 end

module PTree_Properties = Tree_Properties(PTree)

