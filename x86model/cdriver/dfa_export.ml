(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)


let print_bits max l s stab = 
  Printf.printf "uint8_t %s_%s[%n] = {\n" stab s max;
  for i = 0 to (max - 1) do
    if i mod 10 = 0 then Printf.printf "\n";
    Printf.printf "[%3n]=%n" i (if (List.nth l i) then 1 else 0);
    if (i <> (max - 1)) then Printf.printf " , ";
  done;
  Printf.printf "};\n"

(* let print_line num l last =  *)
(*   for i = 0 to 254 do *)
(*     if i mod 10 = 0 then Printf.printf "\n"; *)
(*     Printf.printf "[%3n][%3n]=%3n" num i (List.nth l i); *)
(*     if (i <> 254) || (not last) then Printf.printf " , " *)
(*   done; *)
(*   Printf.printf "\n" *)
(* ;; *)
  
(* let print_transition max l s = *)
(*   Printf.printf "uint8_t table_%s[%3n][255] = {\n" s max;  *)
(*   for i = 0 to (max - 1) do *)
(*     let b = if i = (max-1) then true else false in *)
(*     print_line i (List.nth l i) b *)
(*   done; *)
(*   Printf.printf "};\n" *)
(* ;; *)

let print_line num l s = 
  Printf.printf "uint8_t line_%s_%n[256] = { " s num;
  for i = 0 to 255 do
    if i mod 10 = 0 then Printf.printf "\n";
    Printf.printf "%3n" (List.nth l i);
    if (i <> 255) then Printf.printf " , "
  done;
  Printf.printf "}; \n";
;;
  
let print_transition max l s =
  for i = 0 to (max - 1) do
    print_line i (List.nth l i) s
  done;
  Printf.printf "uint8_t *table_%s[%3n] = {\n" s max; 
  for i = 0 to (max - 1) do
    Printf.printf "line_%s_%n" s i;
    if (i <> max) then Printf.printf " , "
  done;
  Printf.printf "};\n"
;;

let print_dfa dfa s =
  match dfa with 
    | None ->failwith "No DFA...\n"
    | Some dfa ->
      let max = X86_PARSER.X86_BASE_PARSER.dfa_num_states dfa in
      print_transition max (X86_PARSER.X86_BASE_PARSER.dfa_transition dfa) s;
      print_bits max (X86_PARSER.X86_BASE_PARSER.dfa_accepts dfa) s "accepts";
      print_bits max (X86_PARSER.X86_BASE_PARSER.dfa_rejects dfa) s "rejects";
;;

print_dfa (fst (fst dfas)) "ncflow";;
print_dfa (snd (fst dfas)) "dbranch";;
print_dfa (snd dfas) "ibranch";;

Printf.printf "
typedef struct automaton {\n
uint8_t **table;\n
uint8_t *accepts;\n
uint8_t *rejects;\n
uint8_t start;\n
} DFA;\n
";;  

let init_DFA s = 
  Printf.printf "DFA %s = { .table = table_%s , .accepts = accepts_%s , .rejects = rejects_%s , .start = 0 };\n" s s s s
;;

init_DFA "ncflow";;
init_DFA "dbranch";;
init_DFA "ibranch";;

