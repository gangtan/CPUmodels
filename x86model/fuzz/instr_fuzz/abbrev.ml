(** Some abbreviation functions to make it less painful to use certain functions *)

open Bits

let bii = Big_int.big_int_of_int
let unsigned1 = (Word.unsigned (bii 0))
let unsigned3 = (Word.unsigned (bii 2))
let unsigned8 = (Word.unsigned (bii 7))
let unsigned16 = (Word.unsigned (bii 15))
let unsigned32 = (Word.unsigned (bii 31))
let signed8 = (Word.signed (bii 7))
let signed32 = (Word.signed (bii 31))

let zero32 = (Word.zero (bii 311))

let int8_of_int i = Word.repr (bii 7) (bii i)

let print_hex h = Printf.printf "%0xLx" h
let sprint_hex h = Printf.sprintf "0x%Lx" h
let print_bigint x = print_string (Big_int.string_of_big_int x)
let hex_of_big x = sprint_hex (Big_int.int64_of_big_int x)

(** Convert an unsigned 32-bit bitvector to its hex string *)
let unsigned32_to_hex c = hex_of_big (unsigned32 c)

let signed32_to_hex c =
  let d = signed32 c in
  if (Big_int.sign_big_int d >= 0) then hex_of_big d
  else "-" ^ hex_of_big (Big_int.abs_big_int d)
