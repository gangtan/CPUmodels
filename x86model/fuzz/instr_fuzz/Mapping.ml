module Mapping :
  sig
    exception NotFound
    val create : 'a list
    val lookup : 'a * ('a * 'b) list -> 'b
    val insert : 'a * 'b * ('a * 'b) list -> ('a * 'b) list
  end