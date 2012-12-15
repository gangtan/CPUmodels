(* Testing the encode-decode loop *)

(*open Batteries_uni *)
open Bigarray
open Big
open X86Syntax
open Printf

(*
module F=Format
module E=Errormsg
open Formatutil

open Config
open Instr

open Disassembler
*)
let pp_big_int fmt bi = 
  F.printf "%02x" (Big_int.to_int bi)

(* A global array for holding intermediate results of encoding in
   the encoder-decoder loop *)
let bytes = Array1.create int8_unsigned c_layout 15

(* Testing the encode-decode loop on an instruction *)
let test_encode_decode_instr 
    (pre:X86Syntax.prefix) (ins:X86Syntax.instr)(* (loc:mword)*) = 
  match (Encode.enc_pre_instr_bytes pre ins) with
  | None -> 
    Printf.printf "Instruction cannot be encoded!\n"
      pp_prefix_instr (pre,ins)(* pp_mword_flex loc*)
  | Some lz ->
    Array1.modifyi 
      (fun idx _ -> 
	if (idx < List.length lz) then Big_int.to_int (List.nth lz idx)
	else 0) bytes;
    try
      let (pre',ins', _) = decode_instr bytes 0 in
      if (not (pre_instr_eq_dec (pre,ins) (pre',ins'))) then
	(Printf.printf "Encoding-decoding loop fails with instruction: \n"
	   pp_prefix_instr (pre,ins) (*pp_mword_flex loc; *)
	 Printf.printf " after encoding: @[  %a@]\n after decoding: %a\n"
	   (pp_list ~sep:"," pp_big_int) lz
	   pp_prefix_instr (pre',ins'))
    with DF_IllegalInstr l ->
      F.printf "Decoding failure after encoding %a at address 0x%a\n"
	pp_prefix_instr (pre,ins) pp_mword loc;
      F.printf " after encoding: @[  %a@]\n"
	(pp_list ~sep:"," pp_big_int) lz


