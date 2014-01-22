open Big
open Big_int

type big_int = Big_int.big_int

module type INDEXED_TYPE =
 sig
  type t

  val index : t -> big_int

  val eq : t -> t -> bool
 end


module IMap =
  functor (X:INDEXED_TYPE) -> 
  struct
   type elt = X.t 

  let eq x b =
  if x > b then true else false

end