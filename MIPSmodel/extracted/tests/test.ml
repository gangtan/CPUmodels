exception Fail;;
exception FailSafe;;
exception EndReg;;

open Unix
open Peano
open Char
open BinInt
open BinPos
open Coqlib
open Specif
open Zdiv
open Zpower
open Big_int
open Bits
open Datatypes
open Parser
open Decode
open Monad
open Maps
open ZArith_dec
open String
open List0
open Zdiv
open MIPSSyntax
open RTL
open MIPSSemantics
open MIPS_RTL
open MIPS_MACHINE
open MIPS_PARSER
open IPrinter

let bii = big_int_of_int
let bzero = Word.zero (bii 31)
let bfalse = Word.zero (bii 0)
let unsigned1 = (Word.unsigned (bii 0))
let unsigned8 = (Word.unsigned (bii 7))
let unsigned32 = (Word.unsigned (bii 31))
let signed32 = (Word.signed (bii 31))
let print_hex h = Printf.printf "%LX" h
let sprint_hex h = Printf.sprintf "%LX" h
let print_bigint x = print_string (string_of_big_int x)
let hex_of_big x = sprint_hex (int64_of_big_int x)

let get_instr () = Scanf.scanf "%LX\n" (fun h -> h);;
let s_instr (i:instr) = (instr_to_str i);;
let p_instrn (i:instr) = print_string ((instr_to_str i)^"\n");;


let empty_mem =
  (Word.zero (bii 7), PTree.empty);;
let empty_oracle =
  { oracle_bits = (fun a b -> zero_big_int); oracle_offset = zero_big_int };;
let empty_regs = (fun (reg:register) -> bzero);;
let init_machine : mach=
  { gp_regs = empty_regs;
    hi_reg = bzero;
    lo_reg = bzero;
    pc_reg = bzero;
    bdelay_active_f = bfalse;
    bdelay_pc_reg = bzero
  };;
let init_rtl_state : rtl_state=
  { rtl_oracle = empty_oracle;
    rtl_env = empty_env;
    rtl_mach_state = init_machine;
    rtl_memory = empty_mem};;



let rec loop icnt rs= 
  try(
  let (new_instr:Int64.t) = get_instr() in
  let (il:instr list) = parse_word (Word.repr (bii 31) 
  (((*print_hex new_instr;*)big_int_of_int64 new_instr))) in
  match il with
  | [] -> print_string "Parse FAIL\n"
  | i::tl ->(
    let (rtl_ans,rstate_n) = (step_ins i) rs in
    print_endline ("Step "^(string_of_int icnt));
    print_endline (s_instr i);
    match rtl_ans with
    | Fail_ans -> (
      print_endline "Failed\n")
    | SafeFail_ans -> print_endline "Safe Failed\n"
    | Okay_ans _ ->
      print_endline (mach_to_str (rtl_mach_state rstate_n));
      loop (icnt+1) (rstate_n)
  )
  )
  with
  | End_of_file|Scanf.Scan_failure _ -> print_string "EOF\n"
;;

let _ = loop 0 init_rtl_state;;
