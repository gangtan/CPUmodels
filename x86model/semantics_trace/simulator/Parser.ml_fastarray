open Compare_dec
open Datatypes
open List0
open Peano
open Peano_dec

type __ = Obj.t

module type PARSER_ARG = 
 sig 
  type char_p 
  
  val char_eq : char_p -> char_p -> bool
  
  type tipe 
  
  val tipe_eq : tipe -> tipe -> bool
  
  type tipe_m 
 end

module Parser = 
 functor (PA:PARSER_ARG) ->
 struct 
  type result =
  | Coq_unit_t
  | Coq_char_t
  | Coq_pair_t of result * result
  | Coq_list_t of result
  | Coq_sum_t of result * result
  | Coq_tipe_t of PA.tipe
  
  (** val result_rect :
      'a1 -> 'a1 -> (result -> 'a1 -> result -> 'a1 -> 'a1) -> (result -> 'a1
      -> 'a1) -> (result -> 'a1 -> result -> 'a1 -> 'a1) -> (PA.tipe -> 'a1)
      -> result -> 'a1 **)
  
  let rec result_rect f f0 f1 f2 f3 f4 = function
  | Coq_unit_t -> f
  | Coq_char_t -> f0
  | Coq_pair_t (r0, r1) ->
    f1 r0 (result_rect f f0 f1 f2 f3 f4 r0) r1
      (result_rect f f0 f1 f2 f3 f4 r1)
  | Coq_list_t r0 -> f2 r0 (result_rect f f0 f1 f2 f3 f4 r0)
  | Coq_sum_t (r0, r1) ->
    f3 r0 (result_rect f f0 f1 f2 f3 f4 r0) r1
      (result_rect f f0 f1 f2 f3 f4 r1)
  | Coq_tipe_t t -> f4 t
  
  (** val result_rec :
      'a1 -> 'a1 -> (result -> 'a1 -> result -> 'a1 -> 'a1) -> (result -> 'a1
      -> 'a1) -> (result -> 'a1 -> result -> 'a1 -> 'a1) -> (PA.tipe -> 'a1)
      -> result -> 'a1 **)
  
  let rec result_rec f f0 f1 f2 f3 f4 = function
  | Coq_unit_t -> f
  | Coq_char_t -> f0
  | Coq_pair_t (r0, r1) ->
    f1 r0 (result_rec f f0 f1 f2 f3 f4 r0) r1
      (result_rec f f0 f1 f2 f3 f4 r1)
  | Coq_list_t r0 -> f2 r0 (result_rec f f0 f1 f2 f3 f4 r0)
  | Coq_sum_t (r0, r1) ->
    f3 r0 (result_rec f f0 f1 f2 f3 f4 r0) r1
      (result_rec f f0 f1 f2 f3 f4 r1)
  | Coq_tipe_t t -> f4 t
  
  (** val result_eq : result -> result -> bool **)
  
  let rec result_eq r r0 =
    match r with
    | Coq_unit_t ->
      (match r0 with
       | Coq_unit_t -> true
       | _ -> false)
    | Coq_char_t ->
      (match r0 with
       | Coq_char_t -> true
       | _ -> false)
    | Coq_pair_t (r1, r2) ->
      (match r0 with
       | Coq_pair_t (r3, r4) ->
         if result_eq r1 r3 then result_eq r2 r4 else false
       | _ -> false)
    | Coq_list_t r1 ->
      (match r0 with
       | Coq_list_t r2 -> result_eq r1 r2
       | _ -> false)
    | Coq_sum_t (r1, r2) ->
      (match r0 with
       | Coq_sum_t (r3, r4) ->
         if result_eq r1 r3 then result_eq r2 r4 else false
       | _ -> false)
    | Coq_tipe_t t ->
      (match r0 with
       | Coq_tipe_t t0 -> PA.tipe_eq t t0
       | _ -> false)
  
  type result_m = __
  
  type coq_parser =
  | Any_p
  | Char_p of PA.char_p
  | Eps_p
  | Cat_p of result * result * coq_parser * coq_parser
  | Zero_p of result
  | Alt_p of result * coq_parser * coq_parser
  | Star_p of result * coq_parser
  | Map_p of result * result * (result_m -> result_m) * coq_parser
  
  (** val parser_rect :
      'a1 -> (PA.char_p -> 'a1) -> 'a1 -> (result -> result -> coq_parser ->
      'a1 -> coq_parser -> 'a1 -> 'a1) -> (result -> 'a1) -> (result ->
      coq_parser -> 'a1 -> coq_parser -> 'a1 -> 'a1) -> (result -> coq_parser
      -> 'a1 -> 'a1) -> (result -> result -> (result_m -> result_m) ->
      coq_parser -> 'a1 -> 'a1) -> result -> coq_parser -> 'a1 **)
  
  let rec parser_rect f f0 f1 f2 f3 f4 f5 f6 r = function
  | Any_p -> f
  | Char_p c -> f0 c
  | Eps_p -> f1
  | Cat_p (t1, t2, r1, r2) ->
    f2 t1 t2 r1 (parser_rect f f0 f1 f2 f3 f4 f5 f6 t1 r1) r2
      (parser_rect f f0 f1 f2 f3 f4 f5 f6 t2 r2)
  | Zero_p t -> f3 t
  | Alt_p (t, r1, r2) ->
    f4 t r1 (parser_rect f f0 f1 f2 f3 f4 f5 f6 t r1) r2
      (parser_rect f f0 f1 f2 f3 f4 f5 f6 t r2)
  | Star_p (t, p0) -> f5 t p0 (parser_rect f f0 f1 f2 f3 f4 f5 f6 t p0)
  | Map_p (t1, t2, r0, p0) ->
    f6 t1 t2 r0 p0 (parser_rect f f0 f1 f2 f3 f4 f5 f6 t1 p0)
  
  (** val parser_rec :
      'a1 -> (PA.char_p -> 'a1) -> 'a1 -> (result -> result -> coq_parser ->
      'a1 -> coq_parser -> 'a1 -> 'a1) -> (result -> 'a1) -> (result ->
      coq_parser -> 'a1 -> coq_parser -> 'a1 -> 'a1) -> (result -> coq_parser
      -> 'a1 -> 'a1) -> (result -> result -> (result_m -> result_m) ->
      coq_parser -> 'a1 -> 'a1) -> result -> coq_parser -> 'a1 **)
  
  let rec parser_rec f f0 f1 f2 f3 f4 f5 f6 r = function
  | Any_p -> f
  | Char_p c -> f0 c
  | Eps_p -> f1
  | Cat_p (t1, t2, r1, r2) ->
    f2 t1 t2 r1 (parser_rec f f0 f1 f2 f3 f4 f5 f6 t1 r1) r2
      (parser_rec f f0 f1 f2 f3 f4 f5 f6 t2 r2)
  | Zero_p t -> f3 t
  | Alt_p (t, r1, r2) ->
    f4 t r1 (parser_rec f f0 f1 f2 f3 f4 f5 f6 t r1) r2
      (parser_rec f f0 f1 f2 f3 f4 f5 f6 t r2)
  | Star_p (t, p0) -> f5 t p0 (parser_rec f f0 f1 f2 f3 f4 f5 f6 t p0)
  | Map_p (t1, t2, r0, p0) ->
    f6 t1 t2 r0 p0 (parser_rec f f0 f1 f2 f3 f4 f5 f6 t1 p0)
  
  type fn_name = Big.big_int
  
  (** val fn_name_eq : Big.big_int -> Big.big_int -> bool **)
  
  let fn_name_eq =
    eq_nat_dec
  
  type fn =
  | Fn_name of fn_name * result * result
  | Fn_const_char of PA.char_p
  | Fn_empty_list of result
  | Fn_cons of result
  | Fn_unit_left of result
  | Fn_unit_right of result
  | Fn_unit of result
  
  (** val fn_rect :
      (fn_name -> result -> result -> 'a1) -> (PA.char_p -> 'a1) -> (result
      -> 'a1) -> (result -> 'a1) -> (result -> 'a1) -> (result -> 'a1) ->
      (result -> 'a1) -> result -> result -> fn -> 'a1 **)
  
  let fn_rect f f0 f1 f2 f3 f4 f5 r r0 = function
  | Fn_name (x, x0, x1) -> f x x0 x1
  | Fn_const_char x -> f0 x
  | Fn_empty_list x -> f1 x
  | Fn_cons x -> f2 x
  | Fn_unit_left x -> f3 x
  | Fn_unit_right x -> f4 x
  | Fn_unit x -> f5 x
  
  (** val fn_rec :
      (fn_name -> result -> result -> 'a1) -> (PA.char_p -> 'a1) -> (result
      -> 'a1) -> (result -> 'a1) -> (result -> 'a1) -> (result -> 'a1) ->
      (result -> 'a1) -> result -> result -> fn -> 'a1 **)
  
  let fn_rec f f0 f1 f2 f3 f4 f5 r r0 = function
  | Fn_name (x, x0, x1) -> f x x0 x1
  | Fn_const_char x -> f0 x
  | Fn_empty_list x -> f1 x
  | Fn_cons x -> f2 x
  | Fn_unit_left x -> f3 x
  | Fn_unit_right x -> f4 x
  | Fn_unit x -> f5 x
  
  type regexp =
  | Any
  | Char of PA.char_p
  | Eps
  | Cat of result * result * regexp * regexp
  | Alt of result * regexp * regexp
  | Zero of result
  | Star of result * regexp
  | Map of result * result * fn * regexp
  
  (** val regexp_rect :
      'a1 -> (PA.char_p -> 'a1) -> 'a1 -> (result -> result -> regexp -> 'a1
      -> regexp -> 'a1 -> 'a1) -> (result -> regexp -> 'a1 -> regexp -> 'a1
      -> 'a1) -> (result -> 'a1) -> (result -> regexp -> 'a1 -> 'a1) ->
      (result -> result -> fn -> regexp -> 'a1 -> 'a1) -> result -> regexp ->
      'a1 **)
  
  let rec regexp_rect f f0 f1 f2 f3 f4 f5 f6 r = function
  | Any -> f
  | Char c -> f0 c
  | Eps -> f1
  | Cat (t1, t2, r1, r2) ->
    f2 t1 t2 r1 (regexp_rect f f0 f1 f2 f3 f4 f5 f6 t1 r1) r2
      (regexp_rect f f0 f1 f2 f3 f4 f5 f6 t2 r2)
  | Alt (t, r1, r2) ->
    f3 t r1 (regexp_rect f f0 f1 f2 f3 f4 f5 f6 t r1) r2
      (regexp_rect f f0 f1 f2 f3 f4 f5 f6 t r2)
  | Zero t -> f4 t
  | Star (t, r1) -> f5 t r1 (regexp_rect f f0 f1 f2 f3 f4 f5 f6 t r1)
  | Map (t, u, f7, r1) ->
    f6 t u f7 r1 (regexp_rect f f0 f1 f2 f3 f4 f5 f6 t r1)
  
  (** val regexp_rec :
      'a1 -> (PA.char_p -> 'a1) -> 'a1 -> (result -> result -> regexp -> 'a1
      -> regexp -> 'a1 -> 'a1) -> (result -> regexp -> 'a1 -> regexp -> 'a1
      -> 'a1) -> (result -> 'a1) -> (result -> regexp -> 'a1 -> 'a1) ->
      (result -> result -> fn -> regexp -> 'a1 -> 'a1) -> result -> regexp ->
      'a1 **)
  
  let rec regexp_rec f f0 f1 f2 f3 f4 f5 f6 r = function
  | Any -> f
  | Char c -> f0 c
  | Eps -> f1
  | Cat (t1, t2, r1, r2) ->
    f2 t1 t2 r1 (regexp_rec f f0 f1 f2 f3 f4 f5 f6 t1 r1) r2
      (regexp_rec f f0 f1 f2 f3 f4 f5 f6 t2 r2)
  | Alt (t, r1, r2) ->
    f3 t r1 (regexp_rec f f0 f1 f2 f3 f4 f5 f6 t r1) r2
      (regexp_rec f f0 f1 f2 f3 f4 f5 f6 t r2)
  | Zero t -> f4 t
  | Star (t, r1) -> f5 t r1 (regexp_rec f f0 f1 f2 f3 f4 f5 f6 t r1)
  | Map (t, u, f7, r1) ->
    f6 t u f7 r1 (regexp_rec f f0 f1 f2 f3 f4 f5 f6 t r1)
  
  (** val s2b : bool -> bool **)
  
  let s2b = function
  | true -> true
  | false -> false
  
  (** val fn_eq :
      result -> result -> fn -> result -> result -> fn -> bool **)
  
  let fn_eq t1 u1 f1 t2 u2 f2 =
    match f1 with
    | Fn_name (f3, t3, u3) ->
      (match f2 with
       | Fn_name (f4, t4, u4) ->
         (&&) ((&&) (s2b (fn_name_eq f3 f4)) (s2b (result_eq t3 t4)))
           (s2b (result_eq u3 u4))
       | _ -> false)
    | Fn_const_char c1 ->
      (match f2 with
       | Fn_const_char c2 -> if PA.char_eq c1 c2 then true else false
       | _ -> false)
    | Fn_empty_list t3 ->
      (match f2 with
       | Fn_empty_list t4 -> s2b (result_eq t3 t4)
       | _ -> false)
    | Fn_cons t3 ->
      (match f2 with
       | Fn_cons t4 -> s2b (result_eq t3 t4)
       | _ -> false)
    | Fn_unit_left t3 ->
      (match f2 with
       | Fn_unit_left t4 -> s2b (result_eq t3 t4)
       | _ -> false)
    | Fn_unit_right t3 ->
      (match f2 with
       | Fn_unit_right t4 -> s2b (result_eq t3 t4)
       | _ -> false)
    | Fn_unit t3 ->
      (match f2 with
       | Fn_unit t4 -> s2b (result_eq t3 t4)
       | _ -> false)
  
  (** val regexp_eq' : result -> regexp -> result -> regexp -> bool **)
  
  let rec regexp_eq' t1 r1 t2 r2 =
    match r1 with
    | Any ->
      (match r2 with
       | Any -> true
       | _ -> false)
    | Char c1 ->
      (match r2 with
       | Char c2 -> if PA.char_eq c1 c2 then true else false
       | _ -> false)
    | Eps ->
      (match r2 with
       | Eps -> true
       | _ -> false)
    | Cat (t1a, t1b, r1a, r1b) ->
      (match r2 with
       | Cat (t2a, t2b, r2a, r2b) ->
         (&&) (regexp_eq' t1a r1a t2a r2a) (regexp_eq' t1b r1b t2b r2b)
       | _ -> false)
    | Alt (t3, r1a, r1b) ->
      (match r2 with
       | Alt (t4, r2a, r2b) ->
         (&&) (regexp_eq' t3 r1a t4 r2a) (regexp_eq' t3 r1b t4 r2b)
       | _ -> false)
    | Zero t3 ->
      (match r2 with
       | Zero t4 -> s2b (result_eq t3 t4)
       | _ -> false)
    | Star (t3, r1a) ->
      (match r2 with
       | Star (t4, r2a) -> regexp_eq' t3 r1a t4 r2a
       | _ -> false)
    | Map (t3, u1, f1, r1a) ->
      (match r2 with
       | Map (t4, u2, f2, r2a) ->
         (&&) (fn_eq t3 u1 f1 t4 u2 f2) (regexp_eq' t3 r1a t4 r2a)
       | _ -> false)
  
  (** val regexp_eq : result -> regexp -> regexp -> bool **)
  
  let regexp_eq t r1 r2 =
    if regexp_eq' t r1 t r2 then true else false
  
  type fn_result_m = result_m -> result_m
  
  type ctxt_t = ((result * result)*fn_result_m) list
  
  (** val fn_result' : ctxt_t -> fn_name -> (result * result) option **)
  
  let fn_result' g n =
    match nth_error g n with
    | Some s -> let p,f = s in Some p
    | None -> None
  
  type void = unit (* empty inductive *)
  
  (** val void_rect : void -> 'a1 **)
  
  let void_rect v =
    assert false (* absurd case *)
  
  (** val void_rec : void -> 'a1 **)
  
  let void_rec v =
    assert false (* absurd case *)
  
  type fn_result_m_opt = __
  
  (** val lookup_fn' : fn_name -> ctxt_t -> fn_result_m_opt **)
  
  let rec lookup_fn' n g =
    Big.nat_case
      (fun _ ->
      match g with
      | [] -> assert false (* absurd case *)
      | s :: l -> let p,f = s in Obj.magic f)
      (fun m ->
      match g with
      | [] -> assert false (* absurd case *)
      | s :: g' -> lookup_fn' m g')
      n
  
  (** val fn_result : ctxt_t -> fn_name -> (result * result) option **)
  
  let fn_result fn_ctxt =
    fn_result' fn_ctxt
  
  (** val lookup_fn : ctxt_t -> fn_name -> fn_result_m_opt **)
  
  let lookup_fn fn_ctxt n =
    lookup_fn' n fn_ctxt
  
  (** val apply_fn :
      ctxt_t -> result -> result -> fn -> result_m -> result_m **)
  
  let apply_fn fn_ctxt t1 t2 f x =
    match f with
    | Fn_name (f0, t0, t3) ->
      let h = fun h1 -> h1 in Obj.magic h (lookup_fn fn_ctxt f0) x
    | Fn_const_char c -> Obj.magic c
    | Fn_empty_list t -> Obj.magic []
    | Fn_cons t -> Obj.magic ((fst (Obj.magic x)) :: (snd (Obj.magic x)))
    | Fn_unit_left t -> Obj.magic ((), x)
    | Fn_unit_right t -> Obj.magic (x, ())
    | Fn_unit t -> Obj.magic ()
  
  (** val coq_OptCat_r : result -> result -> regexp -> regexp -> regexp **)
  
  let coq_OptCat_r t1 t2 r2 r1 =
    match r2 with
    | Eps -> Map (t1, (Coq_pair_t (t1, Coq_unit_t)), (Fn_unit_right t1), r1)
    | Cat (t3, t4, r, r0) ->
      let r3 = Cat (t3, t4, r, r0) in Cat (t1, (Coq_pair_t (t3, t4)), r1, r3)
    | Alt (t, r, r0) -> let r3 = Alt (t, r, r0) in Cat (t1, t, r1, r3)
    | Zero t -> Zero (Coq_pair_t (t1, t))
    | Star (t, r) -> let r3 = Star (t, r) in Cat (t1, (Coq_list_t t), r1, r3)
    | Map (t, u, f, r) -> let r3 = Map (t, u, f, r) in Cat (t1, u, r1, r3)
    | x -> let r3 = x in Cat (t1, Coq_char_t, r1, r3)
  
  (** val coq_OptCat : result -> result -> regexp -> regexp -> regexp **)
  
  let coq_OptCat t1 t2 r1 r2 =
    match r1 with
    | Eps -> Map (t2, (Coq_pair_t (Coq_unit_t, t2)), (Fn_unit_left t2), r2)
    | Cat (t3, t4, r, r0) ->
      let r3 = Cat (t3, t4, r, r0) in
      coq_OptCat_r (Coq_pair_t (t3, t4)) t2 r2 r3
    | Alt (t, r, r0) -> let r3 = Alt (t, r, r0) in coq_OptCat_r t t2 r2 r3
    | Zero t -> Zero (Coq_pair_t (t, t2))
    | Star (t, r) ->
      let r3 = Star (t, r) in coq_OptCat_r (Coq_list_t t) t2 r2 r3
    | Map (t, u, f, r) ->
      let r3 = Map (t, u, f, r) in coq_OptCat_r u t2 r2 r3
    | x -> let r3 = x in coq_OptCat_r Coq_char_t t2 r2 r3
  
  (** val coq_OptAlt_r : result -> regexp -> regexp -> regexp **)
  
  let coq_OptAlt_r t = function
  | Eps ->
    let r = Eps in
    (fun r1 ->
    if regexp_eq Coq_unit_t r r1 then r else Alt (Coq_unit_t, r1, r))
  | Cat (t1, t2, r0, r1) ->
    let r = Cat (t1, t2, r0, r1) in
    (fun r3 ->
    if regexp_eq (Coq_pair_t (t1, t2)) r r3
    then r
    else Alt ((Coq_pair_t (t1, t2)), r3, r))
  | Alt (t0, r0, r1) ->
    let r = Alt (t0, r0, r1) in
    (fun r3 -> if regexp_eq t0 r r3 then r else Alt (t0, r3, r))
  | Zero t0 -> (fun r -> r)
  | Star (t0, r0) ->
    let r = Star (t0, r0) in
    (fun r1 ->
    if regexp_eq (Coq_list_t t0) r r1
    then r
    else Alt ((Coq_list_t t0), r1, r))
  | Map (t0, u, f, r0) ->
    let r = Map (t0, u, f, r0) in
    (fun r1 -> if regexp_eq u r r1 then r else Alt (u, r1, r))
  | x ->
    let r = x in
    (fun r1 ->
    if regexp_eq Coq_char_t r r1 then r else Alt (Coq_char_t, r1, r))
  
  (** val coq_OptAlt : result -> regexp -> regexp -> regexp **)
  
  let coq_OptAlt t = function
  | Eps -> let r = Eps in (fun r2 -> coq_OptAlt_r Coq_unit_t r2 r)
  | Cat (t1, t2, r0, r2) ->
    let r = Cat (t1, t2, r0, r2) in
    (fun r3 -> coq_OptAlt_r (Coq_pair_t (t1, t2)) r3 r)
  | Alt (t0, r0, r2) ->
    let r = Alt (t0, r0, r2) in (fun r3 -> coq_OptAlt_r t0 r3 r)
  | Zero t0 -> (fun r -> r)
  | Star (t0, r0) ->
    let r = Star (t0, r0) in (fun r2 -> coq_OptAlt_r (Coq_list_t t0) r2 r)
  | Map (t0, u, f, r0) ->
    let r = Map (t0, u, f, r0) in (fun r2 -> coq_OptAlt_r u r2 r)
  | x -> let r = x in (fun r2 -> coq_OptAlt_r Coq_char_t r2 r)
  
  (** val coq_MapUnit : result -> regexp -> regexp **)
  
  let rec coq_MapUnit t = function
  | Eps -> Eps
  | Cat (t1, t2, p1, p2) ->
    (match coq_OptCat Coq_unit_t Coq_unit_t (coq_MapUnit t1 p1)
             (coq_MapUnit t2 p2) with
     | Eps ->
       let r0 = Eps in Map (Coq_unit_t, Coq_unit_t, (Fn_unit Coq_unit_t), r0)
     | Cat (t3, t4, r0, r1) ->
       let r2 = Cat (t3, t4, r0, r1) in
       Map ((Coq_pair_t (t3, t4)), Coq_unit_t, (Fn_unit (Coq_pair_t (t3,
       t4))), r2)
     | Alt (t0, r0, r1) ->
       let r2 = Alt (t0, r0, r1) in Map (t0, Coq_unit_t, (Fn_unit t0), r2)
     | Zero t0 -> let r0 = Zero t0 in Map (t0, Coq_unit_t, (Fn_unit t0), r0)
     | Star (t0, r0) ->
       let r1 = Star (t0, r0) in
       Map ((Coq_list_t t0), Coq_unit_t, (Fn_unit (Coq_list_t t0)), r1)
     | Map (t0, u, f, r0) -> Map (t0, Coq_unit_t, (Fn_unit t0), r0)
     | x ->
       let r0 = x in Map (Coq_char_t, Coq_unit_t, (Fn_unit Coq_char_t), r0))
  | Alt (t0, p1, p2) ->
    coq_OptAlt Coq_unit_t (coq_MapUnit t0 p1) (coq_MapUnit t0 p2)
  | Zero t0 -> Zero Coq_unit_t
  | Star (t0, p1) ->
    Map ((Coq_list_t Coq_unit_t), Coq_unit_t, (Fn_unit (Coq_list_t
      Coq_unit_t)), (Star (Coq_unit_t, (coq_MapUnit t0 p1))))
  | Map (t1, t2, f, p) -> coq_MapUnit t1 p
  | x -> Map (Coq_char_t, Coq_unit_t, (Fn_unit Coq_char_t), x)
  
  (** val coq_OptMap' : result -> result -> fn -> regexp -> regexp **)
  
  let coq_OptMap' t u = function
  | Fn_name (f0, t1, t2) ->
    let f1 = Fn_name (f0, t1, t2) in (fun r -> Map (t1, t2, f1, r))
  | Fn_const_char c ->
    let f1 = Fn_const_char c in
    (fun r -> Map (Coq_unit_t, Coq_char_t, f1, r))
  | Fn_empty_list t0 ->
    let f1 = Fn_empty_list t0 in
    (fun r -> Map (Coq_unit_t, (Coq_list_t t0), f1, r))
  | Fn_cons t0 ->
    let f1 = Fn_cons t0 in
    (fun r -> Map ((Coq_pair_t (t0, (Coq_list_t t0))), (Coq_list_t t0), f1,
    r))
  | Fn_unit_left t0 ->
    let f1 = Fn_unit_left t0 in
    (fun r -> Map (t0, (Coq_pair_t (Coq_unit_t, t0)), f1, r))
  | Fn_unit_right t0 ->
    let f1 = Fn_unit_right t0 in
    (fun r -> Map (t0, (Coq_pair_t (t0, Coq_unit_t)), f1, r))
  | Fn_unit t' -> coq_MapUnit t'
  
  (** val coq_OptMap : result -> result -> fn -> regexp -> regexp **)
  
  let coq_OptMap t u f = function
  | Eps -> let r2 = Eps in Map (Coq_unit_t, u, f, r2)
  | Cat (t1, t2, r, r0) ->
    let r2 = Cat (t1, t2, r, r0) in Map ((Coq_pair_t (t1, t2)), u, f, r2)
  | Alt (t0, r, r0) -> let r2 = Alt (t0, r, r0) in Map (t0, u, f, r2)
  | Zero t0 -> Zero u
  | Star (t0, r) -> let r2 = Star (t0, r) in Map ((Coq_list_t t0), u, f, r2)
  | Map (t0, u0, f0, r) -> let r2 = Map (t0, u0, f0, r) in Map (u0, u, f, r2)
  | x -> let r2 = x in Map (Coq_char_t, u, f, r2)
  
  (** val coerce_reg : result -> result -> regexp -> regexp **)
  
  let coerce_reg t1 t2 r =
    r
  
  (** val coerce_val : result -> result -> result_m -> result_m **)
  
  let coerce_val t1 t2 v =
    v
  
  (** val eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2 **)
  
  let eq_rew_r_dep x y hC =
    hC
  
  (** val null : result -> regexp -> regexp **)
  
  let rec null t = function
  | Any -> Zero Coq_char_t
  | Char c -> Zero Coq_char_t
  | Cat (t1, t2, r1, r2) -> coq_OptCat t1 t2 (null t1 r1) (null t2 r2)
  | Alt (t0, r1, r2) -> coq_OptAlt t0 (null t0 r1) (null t0 r2)
  | Star (t0, r0) ->
    coq_OptMap Coq_unit_t (Coq_list_t t0) (Fn_empty_list t0) Eps
  | Map (t0, u, f, r1) -> coq_OptMap t0 u f (null t0 r1)
  | x -> x
  
  (** val coq_OptCatDelayed :
      result -> result -> regexp -> (PA.char_p -> regexp) -> PA.char_p ->
      regexp **)
  
  let coq_OptCatDelayed t1 t2 r1 d c =
    match r1 with
    | Eps -> let r2 = Eps in coq_OptCat Coq_unit_t t2 r2 (d c)
    | Cat (t3, t4, r, r0) ->
      let r2 = Cat (t3, t4, r, r0) in
      coq_OptCat (Coq_pair_t (t3, t4)) t2 r2 (d c)
    | Alt (t, r, r0) -> let r2 = Alt (t, r, r0) in coq_OptCat t t2 r2 (d c)
    | Zero t -> Zero (Coq_pair_t (t, t2))
    | Star (t, r) ->
      let r2 = Star (t, r) in coq_OptCat (Coq_list_t t) t2 r2 (d c)
    | Map (t, u, f, r) ->
      let r2 = Map (t, u, f, r) in coq_OptCat u t2 r2 (d c)
    | x -> let r2 = x in coq_OptCat Coq_char_t t2 r2 (d c)
  
  (** val deriv : result -> regexp -> PA.char_p -> regexp **)
  
  let rec deriv t r c =
    match r with
    | Any -> coq_OptMap Coq_unit_t Coq_char_t (Fn_const_char c) Eps
    | Char c' ->
      if PA.char_eq c c'
      then coq_OptMap Coq_unit_t Coq_char_t (Fn_const_char c) Eps
      else Zero Coq_char_t
    | Eps -> Zero Coq_unit_t
    | Cat (t1, t2, r1, r2) ->
      coq_OptAlt (Coq_pair_t (t1, t2)) (coq_OptCat t1 t2 (deriv t1 r1 c) r2)
        (coq_OptCatDelayed t1 t2 (null t1 r1) (deriv t2 r2) c)
    | Alt (t0, r1, r2) -> coq_OptAlt t0 (deriv t0 r1 c) (deriv t0 r2 c)
    | Zero t0 -> Zero t0
    | Star (t0, r0) ->
      let r' = Star (t0, r0) in
      coq_OptMap (Coq_pair_t (t0, (Coq_list_t t0))) (Coq_list_t t0) (Fn_cons
        t0) (coq_OptCat t0 (Coq_list_t t0) (deriv t0 r0 c) r')
    | Map (t0, u, f, r1) -> coq_OptMap t0 u f (deriv t0 r1 c)
  
  (** val accepts_null : result -> regexp -> bool **)
  
  let rec accepts_null t = function
  | Eps -> true
  | Cat (t1, t2, r1, r2) -> (&&) (accepts_null t1 r1) (accepts_null t2 r2)
  | Alt (t0, r1, r2) -> (||) (accepts_null t0 r1) (accepts_null t0 r2)
  | Star (t0, r0) -> true
  | Map (t0, u, f, r1) -> accepts_null t0 r1
  | _ -> false
  
  (** val unit_deriv : result -> regexp -> PA.char_p -> regexp **)
  
  let rec unit_deriv t r c =
    match r with
    | Any -> Eps
    | Char c' -> if PA.char_eq c c' then Eps else Zero Coq_unit_t
    | Cat (t1, t2, r1, r2) ->
      (match unit_deriv t1 r1 c with
       | Eps ->
         let r1' = Eps in
         if accepts_null t1 r1
         then coq_OptAlt Coq_unit_t
                (coq_MapUnit (Coq_pair_t (Coq_unit_t, t2))
                  (coq_OptCat Coq_unit_t t2 r1' r2)) (unit_deriv t2 r2 c)
         else coq_MapUnit (Coq_pair_t (Coq_unit_t, t2))
                (coq_OptCat Coq_unit_t t2 r1' r2)
       | Cat (t3, t4, r0, r3) ->
         let r1' = Cat (t3, t4, r0, r3) in
         if accepts_null t1 r1
         then coq_OptAlt Coq_unit_t
                (coq_MapUnit (Coq_pair_t ((Coq_pair_t (t3, t4)), t2))
                  (coq_OptCat (Coq_pair_t (t3, t4)) t2 r1' r2))
                (unit_deriv t2 r2 c)
         else coq_MapUnit (Coq_pair_t ((Coq_pair_t (t3, t4)), t2))
                (coq_OptCat (Coq_pair_t (t3, t4)) t2 r1' r2)
       | Alt (t0, r0, r3) ->
         let r1' = Alt (t0, r0, r3) in
         if accepts_null t1 r1
         then coq_OptAlt Coq_unit_t
                (coq_MapUnit (Coq_pair_t (t0, t2)) (coq_OptCat t0 t2 r1' r2))
                (unit_deriv t2 r2 c)
         else coq_MapUnit (Coq_pair_t (t0, t2)) (coq_OptCat t0 t2 r1' r2)
       | Zero t0 ->
         if accepts_null t1 r1 then unit_deriv t2 r2 c else Zero Coq_unit_t
       | Star (t0, r0) ->
         let r1' = Star (t0, r0) in
         if accepts_null t1 r1
         then coq_OptAlt Coq_unit_t
                (coq_MapUnit (Coq_pair_t ((Coq_list_t t0), t2))
                  (coq_OptCat (Coq_list_t t0) t2 r1' r2))
                (unit_deriv t2 r2 c)
         else coq_MapUnit (Coq_pair_t ((Coq_list_t t0), t2))
                (coq_OptCat (Coq_list_t t0) t2 r1' r2)
       | Map (t0, u, f, r0) ->
         let r1' = Map (t0, u, f, r0) in
         if accepts_null t1 r1
         then coq_OptAlt Coq_unit_t
                (coq_MapUnit (Coq_pair_t (u, t2)) (coq_OptCat u t2 r1' r2))
                (unit_deriv t2 r2 c)
         else coq_MapUnit (Coq_pair_t (u, t2)) (coq_OptCat u t2 r1' r2)
       | x ->
         let r1' = x in
         if accepts_null t1 r1
         then coq_OptAlt Coq_unit_t
                (coq_MapUnit (Coq_pair_t (Coq_char_t, t2))
                  (coq_OptCat Coq_char_t t2 r1' r2)) (unit_deriv t2 r2 c)
         else coq_MapUnit (Coq_pair_t (Coq_char_t, t2))
                (coq_OptCat Coq_char_t t2 r1' r2))
    | Alt (t0, r1, r2) ->
      coq_OptAlt Coq_unit_t (unit_deriv t0 r1 c) (unit_deriv t0 r2 c)
    | Star (t0, r0) ->
      let r' = Star (t0, r0) in
      (match unit_deriv t0 r0 c with
       | Eps ->
         let r1' = Eps in
         coq_MapUnit (Coq_pair_t (Coq_unit_t, (Coq_list_t t0)))
           (coq_OptCat Coq_unit_t (Coq_list_t t0) r1' r')
       | Cat (t1, t2, r1, r2) ->
         let r1' = Cat (t1, t2, r1, r2) in
         coq_MapUnit (Coq_pair_t ((Coq_pair_t (t1, t2)), (Coq_list_t t0)))
           (coq_OptCat (Coq_pair_t (t1, t2)) (Coq_list_t t0) r1' r')
       | Alt (t1, r1, r2) ->
         let r1' = Alt (t1, r1, r2) in
         coq_MapUnit (Coq_pair_t (t1, (Coq_list_t t0)))
           (coq_OptCat t1 (Coq_list_t t0) r1' r')
       | Zero t1 -> Zero Coq_unit_t
       | Star (t1, r1) ->
         let r1' = Star (t1, r1) in
         coq_MapUnit (Coq_pair_t ((Coq_list_t t1), (Coq_list_t t0)))
           (coq_OptCat (Coq_list_t t1) (Coq_list_t t0) r1' r')
       | Map (t1, u, f, r1) ->
         let r1' = Map (t1, u, f, r1) in
         coq_MapUnit (Coq_pair_t (u, (Coq_list_t t0)))
           (coq_OptCat u (Coq_list_t t0) r1' r')
       | x ->
         let r1' = x in
         coq_MapUnit (Coq_pair_t (Coq_char_t, (Coq_list_t t0)))
           (coq_OptCat Coq_char_t (Coq_list_t t0) r1' r'))
    | Map (t0, u, f, r1) -> unit_deriv t0 r1 c
    | _ -> Zero Coq_unit_t
  
  (** val unit_derivs : regexp -> PA.char_p list -> regexp **)
  
  let rec unit_derivs r = function
  | [] -> r
  | c :: cs' -> unit_derivs (unit_deriv Coq_unit_t r c) cs'
  
  (** val apply_null : ctxt_t -> result -> regexp -> result_m list **)
  
  let rec apply_null fn_ctxt t = function
  | Eps -> (Obj.magic ()) :: []
  | Cat (t1, t2, r1, r2) ->
    let res1 = apply_null fn_ctxt t1 r1 in
    let res2 = apply_null fn_ctxt t2 r2 in
    fold_right (fun v1 a -> app (map (fun v2 -> Obj.magic (v1, v2)) res2) a)
      [] res1
  | Alt (t0, r1, r2) ->
    app (apply_null fn_ctxt t0 r1) (apply_null fn_ctxt t0 r2)
  | Star (t0, r0) -> (Obj.magic []) :: []
  | Map (t0, u, f, r1) ->
    map (apply_fn fn_ctxt t0 u f) (apply_null fn_ctxt t0 r1)
  | _ -> []
  
  (** val deriv_parse' : result -> regexp -> PA.char_p list -> regexp **)
  
  let rec deriv_parse' t r = function
  | [] -> r
  | c :: cs' -> deriv_parse' t (deriv t r c) cs'
  
  (** val deriv_parse :
      ctxt_t -> result -> regexp -> PA.char_p list -> result_m list **)
  
  let deriv_parse fn_ctxt t r cs =
    apply_null fn_ctxt t (deriv_parse' t r cs)
  
  type coq_DFA = { dfa_num_states : Big.big_int; dfa_states : regexp list;
                   dfa_transition : Big.big_int list list;
                   dfa_accepts : bool list; dfa_rejects : bool list }
  
  (** val coq_DFA_rect :
      (Big.big_int -> regexp list -> Big.big_int list list -> bool list ->
      bool list -> 'a1) -> coq_DFA -> 'a1 **)
  
  let coq_DFA_rect f d =
    let { dfa_num_states = x; dfa_states = x0; dfa_transition = x1;
      dfa_accepts = x2; dfa_rejects = x3 } = d
    in
    f x x0 x1 x2 x3
  
  (** val coq_DFA_rec :
      (Big.big_int -> regexp list -> Big.big_int list list -> bool list ->
      bool list -> 'a1) -> coq_DFA -> 'a1 **)
  
  let coq_DFA_rec f d =
    let { dfa_num_states = x; dfa_states = x0; dfa_transition = x1;
      dfa_accepts = x2; dfa_rejects = x3 } = d
    in
    f x x0 x1 x2 x3
  
  (** val dfa_num_states : coq_DFA -> Big.big_int **)
  
  let dfa_num_states d =
    d.dfa_num_states
  
  (** val dfa_states : coq_DFA -> regexp list **)
  
  let dfa_states d =
    d.dfa_states
  
  (** val dfa_transition : coq_DFA -> Big.big_int list list **)
  
  let dfa_transition d =
    d.dfa_transition
  
  (** val dfa_accepts : coq_DFA -> bool list **)
  
  let dfa_accepts d =
    d.dfa_accepts
  
  (** val dfa_rejects : coq_DFA -> bool list **)
  
  let dfa_rejects d =
    d.dfa_rejects
  
  type token_id = Big.big_int
  
  type states = regexp list
  
  (** val find_index' :
      regexp -> Big.big_int -> states -> Big.big_int option **)
  
  let rec find_index' r n = function
  | [] -> None
  | h :: tl ->
    if regexp_eq Coq_unit_t r h
    then Some n
    else find_index' r (plus (Big.succ Big.zero) n) tl
  
  (** val find_index : regexp -> states -> Big.big_int option **)
  
  let find_index r s =
    find_index' r Big.zero s
  
  (** val find_or_add : regexp -> states -> states * Big.big_int **)
  
  let find_or_add r s =
    match find_index r s with
    | Some i -> (s, i)
    | None -> ((app s (r :: [])), (length s))
  
  (** val gen_row' :
      (token_id -> PA.char_p list) -> Big.big_int -> regexp -> states ->
      token_id -> states * Big.big_int list **)
  
  let rec gen_row' token_id_to_chars n r s token_id0 =
    Big.nat_case
      (fun _ -> (s,
      []))
      (fun n' ->
      let (s1, d) =
        find_or_add (unit_derivs r (token_id_to_chars token_id0)) s
      in
      let (s2, row) =
        gen_row' token_id_to_chars n' r s1
          (plus (Big.succ Big.zero) token_id0)
      in
      (s2, (d :: row)))
      n
  
  (** val gen_row :
      Big.big_int -> (token_id -> PA.char_p list) -> regexp -> states ->
      states * Big.big_int list **)
  
  let gen_row num_tokens token_id_to_chars r s =
    gen_row' token_id_to_chars num_tokens r s Big.zero
  
  (** val build_table' :
      Big.big_int -> (token_id -> PA.char_p list) -> Big.big_int -> states ->
      Big.big_int list list -> Big.big_int -> (states * Big.big_int list
      list) option **)
  
  let rec build_table' num_tokens token_id_to_chars n s rows next_state =
    Big.nat_case
      (fun _ ->
      None)
      (fun n' ->
      match nth_error s next_state with
      | Some r ->
        let (s1, row) = gen_row num_tokens token_id_to_chars r s in
        build_table' num_tokens token_id_to_chars n' s1
          (app rows (row :: [])) (plus (Big.succ Big.zero) next_state)
      | None -> Some (s, rows))
      n
  
  (** val build_transition_table :
      Big.big_int -> (token_id -> PA.char_p list) -> Big.big_int -> regexp ->
      (states * Big.big_int list list) option **)
  
  let build_transition_table num_tokens token_id_to_chars n r =
    build_table' num_tokens token_id_to_chars n (r :: []) [] Big.zero
  
  (** val build_accept_table : states -> bool list **)
  
  let build_accept_table s =
    map (accepts_null Coq_unit_t) s
  
  (** val always_rejects : result -> regexp -> bool **)
  
  let rec always_rejects t = function
  | Cat (t1, t2, r1, r2) ->
    (||) (always_rejects t1 r1) (always_rejects t2 r2)
  | Alt (t0, r1, r2) -> (&&) (always_rejects t0 r1) (always_rejects t0 r2)
  | Zero t0 -> true
  | Map (t0, u, f, r0) -> always_rejects t0 r0
  | _ -> false
  
  (** val build_rejects : states -> bool list **)
  
  let build_rejects s =
    map (always_rejects Coq_unit_t) s
  
  (** val build_dfa :
      Big.big_int -> (token_id -> PA.char_p list) -> Big.big_int -> regexp ->
      coq_DFA option **)
  
  let build_dfa num_tokens token_id_to_chars n r =
    match build_transition_table num_tokens token_id_to_chars n r with
    | Some p ->
      let (states0, table) = p in
      Some { dfa_num_states = (length states0); dfa_states = states0;
      dfa_transition = table; dfa_accepts = (build_accept_table states0);
      dfa_rejects = (build_rejects states0) }
    | None -> None
  
  (** val dfa_loop :
      Big.big_int -> coq_DFA -> Big.big_int -> Big.big_int -> token_id list
      -> (Big.big_int * token_id list) option **)
  
  let rec dfa_loop num_tokens d state count ts =
    if nth state (dfa_accepts d) false
    then Some (count, ts)
    else (match ts with
          | [] -> None
          | t :: ts' ->
            let row = nth state (dfa_transition d) [] in
            let new_state = nth t row num_tokens in
            dfa_loop num_tokens d new_state (Big.succ count) ts')
  
  (** val dfa_recognize :
      Big.big_int -> coq_DFA -> token_id list -> (Big.big_int * token_id
      list) option **)
  
  let dfa_recognize num_tokens d ts =
    dfa_loop num_tokens d Big.zero Big.zero ts
  
  (** val par2rec : result -> coq_parser -> regexp **)
  
  let rec par2rec t = function
  | Any_p -> Map (Coq_char_t, Coq_unit_t, (Fn_unit Coq_char_t), Any)
  | Char_p b -> Map (Coq_char_t, Coq_unit_t, (Fn_unit Coq_char_t), (Char b))
  | Eps_p -> Eps
  | Cat_p (t1, t2, p1, p2) ->
    Map ((Coq_pair_t (Coq_unit_t, Coq_unit_t)), Coq_unit_t, (Fn_unit
      (Coq_pair_t (Coq_unit_t, Coq_unit_t))),
      (coq_OptCat Coq_unit_t Coq_unit_t (par2rec t1 p1) (par2rec t2 p2)))
  | Zero_p t0 -> Zero Coq_unit_t
  | Alt_p (t0, p1, p2) ->
    coq_OptAlt Coq_unit_t (par2rec t0 p1) (par2rec t0 p2)
  | Star_p (t0, p1) ->
    Map ((Coq_list_t Coq_unit_t), Coq_unit_t, (Fn_unit (Coq_list_t
      Coq_unit_t)), (Star (Coq_unit_t, (par2rec t0 p1))))
  | Map_p (t1, t2, f, p0) -> par2rec t1 p0
  
  (** val recognize :
      ctxt_t -> result -> coq_parser -> PA.char_p list -> bool **)
  
  let recognize fn_ctxt t p cs =
    let l = deriv_parse fn_ctxt Coq_unit_t (par2rec t p) cs in
    (match l with
     | [] -> false
     | r :: l0 -> true)
  
  (** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)
  
  let flat_map f xs =
    fold_right (fun v a -> app (f v) a) [] xs
  
  (** val run_dfa :
      Big.big_int -> coq_DFA -> Big.big_int -> token_id list -> bool **)
  
  let rec run_dfa num_tokens d state = function
  | [] -> nth state (dfa_accepts d) false
  | t :: ts' ->
    run_dfa num_tokens d (nth t (nth state (dfa_transition d) []) num_tokens)
      ts'
  
  (** val accepts_at_most_one_null : ctxt_t -> result -> regexp -> bool **)
  
  let accepts_at_most_one_null fn_ctxt t r =
    if le_gt_dec (length (apply_null fn_ctxt t r)) (Big.succ Big.zero)
    then true
    else false
  
  (** val enum_tokens : (token_id -> bool) -> Big.big_int -> bool **)
  
  let rec enum_tokens f n =
    Big.nat_case
      (fun _ ->
      true)
      (fun m ->
      (&&) (f m) (enum_tokens f m))
      n
  
  (** val forall_tokens : Big.big_int -> (token_id -> bool) -> bool **)
  
  let forall_tokens num_tokens f =
    enum_tokens f num_tokens
  
  (** val extend_state :
      ctxt_t -> result -> result -> fn_result_m -> fn_name * ctxt_t **)

  (* ************************************************************************ *)
  (* Beginning of changes to the parser: using a fast array for the context , 
     instead of a list *)
  (* 
  let extend_state s t1 t2 f =
    ((length s), (app s (((t1, t2),f) :: []))) *)
  
  open Array

  let max_array_len = 100000

  let initial_array = (0, make max_array_len ((Coq_unit_t, Coq_unit_t), (fun _ -> Obj.magic 1)))

  exception Insufficient_Array_Len

  let extend_state (last,arr) t1 t2 f =
    if (last < max_array_len) then
      let _ = set arr last ((t1,t2), f) in (last+1, arr)
    else raise Insufficient_Array_Len

  let rec par2reg' t p s =
    match p with
    | Any_p -> (Any, s)
    | Char_p b -> ((Char b), s)
    | Eps_p -> (Eps, s)
    | Cat_p (t1, t2, p1, p2) ->
      let (r1, s1) = par2reg' t1 p1 s in
      let (r2, s2) = par2reg' t2 p2 s1 in ((Cat (t1, t2, r1, r2)), s2)
    | Zero_p t0 -> ((Zero t0), s)
    | Alt_p (t0, p1, p2) ->
      let (r1, s1) = par2reg' t0 p1 s in
      let (r2, s2) = par2reg' t0 p2 s1 in ((Alt (t0, r1, r2)), s2)
    | Star_p (t0, p1) ->
      let (r1, s1) = par2reg' t0 p1 s in ((Star (t0, r1)), s1)
    | Map_p (t1, t2, f, p0) ->
      let (r, s1) = par2reg' t1 p0 s in
      let s2 = extend_state s1 t1 t2 f in
      let (len,arr) = s2 in
      ((Map (t1, t2, (Fn_name (Big.of_int(len-1), t1, t2)), r)), s2)
  
  (** val par2reg : result -> coq_parser -> ctxt_t -> regexp * ctxt_t **)
  
  let rec par2reg t p lst = 
    let build_array lst s =
      match lst with
      | [] -> s
      | ((t1,t2),f)::tl -> extend_state s t1 t2 f
    in
    let (re, s) = par2reg' t p (build_array lst initial_array) in
      (re, to_list (sub (snd s) 0 (fst s)))
  
  (* ************************************************************************ *)
  
  (** val initial_ctxt : ctxt_t **)

  let initial_ctxt = []

  (** val parser2regexp : result -> coq_parser -> regexp * ctxt_t **)
  
  let parser2regexp t p =
    let (r, ctx) = par2reg t p initial_ctxt in
      (r, ctx)
  
  (** val parse : result -> coq_parser -> PA.char_p list -> result_m list **)
  
  let parse t p =
    deriv_parse (snd (parser2regexp t p)) t (fst (parser2regexp t p))
 end

