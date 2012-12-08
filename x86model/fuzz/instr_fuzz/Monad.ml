open Coqlib
open List0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'm coq_Monad = { coq_Return : (__ -> __ -> 'm);
                      coq_Bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

(** val coq_Monad_rect :
    ((__ -> __ -> 'a1) -> (__ -> __ -> 'a1 -> (__ -> 'a1) -> 'a1) -> __ -> __
    -> __ -> 'a2) -> 'a1 coq_Monad -> 'a2 **)

let coq_Monad_rect f m =
  let { coq_Return = x; coq_Bind = x0 } = m in f x x0 __ __ __

(** val coq_Monad_rec :
    ((__ -> __ -> 'a1) -> (__ -> __ -> 'a1 -> (__ -> 'a1) -> 'a1) -> __ -> __
    -> __ -> 'a2) -> 'a1 coq_Monad -> 'a2 **)

let coq_Monad_rec f m =
  let { coq_Return = x; coq_Bind = x0 } = m in f x x0 __ __ __

(** val coq_Return : 'a1 coq_Monad -> 'a2 -> 'a1 **)

let coq_Return monad x =
  let { coq_Return = return; coq_Bind = bind } = monad in
  Obj.magic return __ x

(** val coq_Bind : 'a1 coq_Monad -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let coq_Bind monad x x0 =
  let { coq_Return = return; coq_Bind = bind } = monad in
  Obj.magic bind __ __ x x0

(** val coq_OptionMonad : __ option coq_Monad **)

let coq_OptionMonad =
  { coq_Return = (fun _ x -> Some x); coq_Bind = (fun _ _ c f ->
    match c with
    | Some v -> f v
    | None -> None) }

type ('s, 'a) coq_ST = 's -> 's * 'a

(** val coq_StateMonad : ('a1, __) coq_ST coq_Monad **)

let coq_StateMonad =
  { coq_Return = (fun _ x s -> (s, x)); coq_Bind = (fun _ _ c f s ->
    let (s', x) = c s in f x s') }

(** val coq_ListMonad : __ list coq_Monad **)

let coq_ListMonad =
  { coq_Return = (fun _ x -> x :: []); coq_Bind = (fun _ _ c f ->
    list_flatten (map f c)) }

