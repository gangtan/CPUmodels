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
open Monad
open ZArith_dec
open String
open List0
open Zdiv
open Fuzz
open Random
open X86Syntax
open X86_PARSER_ARG
open X86_PARSER
open X86_BASE_PARSER
open Decode

let out_code = open_out "fuzz.ascii"
let out_data = open_out "data.ascii"
  
 
let rec myalts l =
  match l with
    | x :: y :: [] -> alt instruction_t x y
    | x :: [] -> x
    | x :: l' -> alt instruction_t x (myalts l')
  
 
(*let parser_to_fuzz = myalts [coq_ADC_p false; coq_ADD_p false; coq_AND_p false; coq_CMP_p false; 
	                     coq_OR_p false; coq_SBB_p false; coq_SUB_p false; coq_XOR_p false]*)
(* Skip over div/idiv because of exceptions in the fuzzed code *)
(*
let parser_to_fuzz1 = Cat_p (Obj.magic(), Obj.magic(), coq_SAHF_p, 
	myalts [ coq_AND_p false; coq_OR_p false; coq_XOR_p false; coq_TEST_p false;
	coq_NOT_p; coq_INC_p; coq_ADD_p false; coq_ADC_p false; coq_CMP_p false; coq_SUB_p false;
	coq_SBB_p false; coq_NEG_p; coq_HLT_p; coq_IMUL_p false ; coq_MUL_p;
	coq_SHL_p; coq_SHR_p; coq_SHRD_p; coq_SAR_p; coq_BSR_p; coq_BSF_p; coq_BT_p; coq_BTC_p;
	coq_BTS_p; coq_BTR_p; coq_BSWAP_p; coq_CWDE_p; coq_CDQ_p; coq_MOV_p false; coq_CMOVcc_p;
	coq_MOVZX_p; coq_MOVSX_p; coq_CWDE_p; coq_CDQ_p; coq_MOV_p false;
	coq_CMOVcc_p; coq_MOVZX_p; coq_MOVSX_p; coq_XCHG_p; coq_CLC_p; coq_CLD_p; coq_STD_p; coq_STC_p;
	coq_MOVS_p; coq_CMPXCHG_p; coq_CMPS_p; coq_STOS_p; coq_LEA_p; coq_SETcc_p; coq_POP_p; coq_PUSH_p;
	coq_ROL_p; coq_ROR_p; coq_RCL_p; coq_RCR_p; coq_LAHF_p; coq_CMC_p])
 *)
let parser_to_fuzz1 = Cat_p (Obj.magic(), Obj.magic(), coq_SAHF_p, 
	myalts [ coq_AND_p false; coq_OR_p false; coq_XOR_p false; coq_TEST_p false;
	coq_NOT_p; coq_DEC_p; coq_INC_p; coq_ADD_p false; coq_ADC_p false; coq_CMP_p false; coq_SUB_p false;
	coq_SBB_p false; coq_NEG_p; coq_HLT_p; coq_IMUL_p false ; coq_MUL_p;
	coq_AAA_p; coq_AAS_p; coq_AAD_p; coq_AAM_p; (* coq_DAA_p; coq_DAS_p; *)
	coq_SHL_p; coq_SHR_p; coq_SHLD_p; coq_SHRD_p; coq_SAR_p; (*coq_BSR_p; coq_BSF_p;*) coq_BT_p; coq_BTC_p;
	coq_BTS_p; coq_BTR_p; coq_BSWAP_p; coq_CWDE_p; coq_CDQ_p; coq_MOV_p false; coq_CMOVcc_p;
	coq_CMOVcc_p; coq_MOVZX_p; coq_MOVSX_p; coq_XCHG_p; coq_CLC_p; coq_CLD_p; coq_STD_p; coq_STC_p;
	coq_MOVS_p; coq_CMPXCHG_p; coq_CMPS_p; coq_STOS_p; coq_LEA_p; coq_SETcc_p; coq_POP_p; coq_PUSH_p;
	coq_PUSHF_p;  coq_ROL_p; coq_ROR_p; coq_RCL_p; coq_RCR_p; coq_LAHF_p; coq_CMC_p; 
        (*coq_LOOP_p; coq_LOOPZ_p; coq_LOOPNZ_p*)]) 


let instr_parsers_opsize_pre_nodiv =
    (coq_ADC_p
      true) :: ((coq_ADD_p
                  true) :: ((coq_AND_p
                              true) :: ((coq_CMP_p
                                          true) :: ((coq_OR_p
                                                      true) :: ((coq_SBB_p
                                                                  true) :: (
      (coq_SUB_p
        true) :: (coq_SHL_p :: (coq_SHR_p :: (coq_SAR_p :: (
      (coq_XOR_p
        true) :: ((coq_IMUL_p
                    true) :: ((coq_MOV_p
                                true) :: (coq_MOVSX_p :: (coq_MOVZX_p :: (coq_NEG_p :: (coq_NOT_p :: (
      (coq_TEST_p
        true) :: (coq_CDQ_p :: (coq_CWDE_p :: (coq_MUL_p :: (coq_XCHG_p :: [])))))))))))))))))))))
  

let parser_to_fuzz2 = Cat_p (Obj.magic(), Obj.magic(), coq_SAHF_p, Cat_p (Obj.magic(), Obj.magic(), op_override_p, myalts instr_parsers_opsize_pre_nodiv))

let parser_to_fuzz = parser_to_fuzz1

let () = Random.self_init ()

let mytestempty_oracle : oracle  = {oracle_num = (fun x -> big_int_of_int (Random.int 2000)); oracle_offset = Big.zero};;

let print_bool b =
 match b with
    | false -> "0"
    | true -> "1"

let rec conv_byte_aux bs res count =
  match count with
  | 0 -> (bs, res)
  | count2 ->
        (match bs with 
        | h :: tl -> (match h with
                  | true -> conv_byte_aux tl (2*res +1) (count2 -1)
                  | false -> conv_byte_aux tl (2*res) (count2 - 1))
        | [] -> conv_byte_aux [] (2*res) (count2 - 1));;

let rec conv_total bs =
  match bs with
    | [] -> []
    | h :: tl' -> let (rem, res) = (conv_byte_aux bs 0 4) in
                     res :: (conv_total rem)

let rec print_list l =
  match l with
    | [] -> print_string ""
    | h :: tl -> print_string (print_bool h); print_string "";  print_list tl

let rec print_hex_list l =
  match l with
    | [] -> print_string ""
    | h :: h' :: tl -> Printf.fprintf out_code "%x%x\n" h h';
	               Printf.fprintf out_data "01\n"; 
	               print_hex_list tl

(* This takes in a parser (that's p) and an int (i) 
 * and generates that many instances of instructions in
 * the language of p *)
(*
let rec generate p i =
        match i with
          | 0 -> ()
          | x -> print_hex_list (conv_total (snd (fuzz_p (Obj.magic()) p
          mytestempty_oracle))); generate p (x - 1);;

let rec generate_withnop p i =
        match i with
          | 0 -> ()
          | x -> print_hex_list (conv_total (snd (fuzz_p (Obj.magic()) p
          mytestempty_oracle))); print_string "\n"; generate coq_NOP 16;
	  generate_withnop p (x - 1);;
*)

let rec print_nops i =
	match i with
	  | 0 -> ()
	  | x -> Printf.fprintf out_code "90\n";
	         Printf.fprintf out_data "00\n";
	         print_nops (x -1);;

let rec generate p i =
        match i with
          | 0 -> ()
          | x -> print_hex_list (conv_total (snd (fuzz_p (Obj.magic()) p
                   mytestempty_oracle))); 
	         print_nops 16;   	 
	         generate p (x - 1);;

let () = generate (coq_MOV_ESP_to_EBX) 1;;
let () = generate (parser_to_fuzz) 100;;
