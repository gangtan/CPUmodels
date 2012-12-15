type __ = Obj.t

(** val coq_Fix_F_sub : ('a1 -> ('a1 -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let rec coq_Fix_F_sub f_sub x =
  f_sub x (fun y -> coq_Fix_F_sub f_sub y)

(** val coq_Fix_sub : ('a1 -> ('a1 -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let rec coq_Fix_sub f_sub x =
  f_sub x (fun y -> coq_Fix_sub f_sub y)

(** val coq_Fix_F_sub_rect :
    ('a1 -> ('a1 -> 'a2) -> 'a2) -> ('a1 -> ('a1 -> __ -> __ -> 'a3) -> __ ->
    'a3) -> 'a1 -> 'a3 **)
(*
let coq_Fix_F_sub_rect =
  failwith "AXIOM TO BE REALIZED"
*)
(** val coq_Fix_sub_rect :
    ('a1 -> ('a1 -> 'a2) -> 'a2) -> ('a1 -> ('a1 -> __ -> 'a3) -> __ -> 'a3)
    -> 'a1 -> 'a3 **)
(*
let coq_Fix_sub_rect =
  failwith "AXIOM TO BE REALIZED"
*)
module WfExtensionality = 
 struct 
  
 end

