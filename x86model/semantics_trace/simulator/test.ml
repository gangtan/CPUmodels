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
open X86Syntax
open RTL
open X86Semantics
open X86_RTL
open X86_MACHINE

let mem_file = open_in Sys.argv.(1)
let reg_file = open_in Sys.argv.(2)

(* This is just to make it less painful to use the Big_int module
 * and the extracted Word module  *)

let bii = big_int_of_int
let unsigned1 = (Word.unsigned (bii 0))
let unsigned8 = (Word.unsigned (bii 7))
let unsigned32 = (Word.unsigned (bii 31))
let signed32 = (Word.signed (bii 31))
let print_hex h = Printf.printf "%Lx" h
let sprint_hex h = Printf.sprintf "%Lx" h
let print_bigint x = print_string (string_of_big_int x)
let hex_of_big x = sprint_hex (int64_of_big_int x)

(**************************************************)
(* Code for printing out info about machine state *)
(**************************************************)

let reg_to_str r = match r with 
  | EAX -> "EAX"
  | ECX -> "ECX"
  | EDX -> "EDX"
  | EBX -> "EBX"
  | ESP -> "ESP"
  | EBP -> "EBP"
  | ESI -> "ESI"
  | EDI -> "EDI";;

let str_to_reg s = match s with
  | "EAX" -> Some EAX
  | "ECX" -> Some ECX
  | "EDX" -> Some EDX
  | "EBX" -> Some EBX
  | "ESP" -> Some ESP
  | "EBP" -> Some EBP
  | "ESI" -> Some ESI
  | "EDI" -> Some EDI
  | _ -> None

let flag_to_str f = match f with
  | CF -> "CF"
  | ZF -> "ZF"
  | SF -> "SF"
  | OF -> "OF"
  | AF -> "AF"
  | PF -> "PF"
  | _ -> "???";;

let str_to_flag s = match s with
  | "CF" -> Some CF
  | "ZF" -> Some ZF
  | "SF" -> Some SF
  | "OF" -> Some OF
  | "AF" -> Some AF
  | "PF" -> Some PF
  | _ -> None;;

let print_flags m =
  let pr x = print_string (flag_to_str x ^ " ");
    print_string (hex_of_big (unsigned1 (get_location (bii 1) (Coq_flag_loc x) m))); 
    print_string "\n" in
  pr OF; pr SF; pr ZF; pr CF; pr AF; pr PF; 
  print_string "\n\n";;

let print_regs m =
  let pr x = print_string (reg_to_str x ^ " ");   
    print_string (hex_of_big (unsigned32 (get_location (bii 31) (Coq_reg_loc x) m))); 
    print_string "\n" in
  pr EAX; pr ECX; pr EDX; pr EBX; pr ESP; pr EBP; pr ESI; pr EDI;
  print_string "EIP "; 
  print_string (hex_of_big (unsigned32 (get_location (bii 31) (Coq_pc_loc) m)));
  print_string "\n\n";;

(*********************************************)
(* Code to update/compare machine states     *) 
(*********************************************)

(*
let update_mem m x y =
     (AddrMap.set (Word.repr (bii 31) (big_int_of_int64 x)) 
       (Word.repr (bii 7) (big_int_of_int64 y)) m)
*)

let update_mem m x y = (AddrMap.set x y m)

let update eq f x0 y x =
  match eq x0 x with
    | true -> y
    | false -> f x

let set_regpc (regs,pc,segs) s x = 
  let v = Word.repr (bii 31) (big_int_of_int64 x) in
  let set_reg r y = (update X86Syntax.register_eq_dec regs r y) in
  let set_seg r y = (update X86Syntax.segment_register_eq_dec segs r y) in
  match str_to_reg s with
    | Some r -> (set_reg r v, pc, segs)
    | None -> match s with
                | "GS" -> (regs, pc, set_seg GS v) 
                | "FS" -> (regs, pc, set_seg FS v) 
                | "EIP" -> (regs, v, segs) 
                | "END" -> raise EndReg
                | _ -> (regs, pc, segs)

(* Given a memory and a channel, assigns the memory addresses/values
   indicated by the input from the channel, and then returns the updated
   memory value. It keeps updating like this until it reaches the end
   of the channel or a line in the channel does not match the formatting
   string.
  
   Also returns a list of addresses that were modified in this manner.
   
 *)

let rec load_memory m addrs channel =
  let cast x y = (Word.repr (bii 31) (big_int_of_int64 x),
                  Word.repr (bii 7) (big_int_of_int64 y)) in
  try (let (x, y) = Scanf.bscanf (Scanf.Scanning.from_string (input_line
                      channel)) "%Lx %Lx" cast in
           load_memory (update_mem m x y) (x::addrs) channel) with
    | End_of_file -> (m, addrs)
    | Scanf.Scan_failure str -> (m, addrs);;

(* You'll notice this is very similar to the load_memory function.
   Previously there was a more general function that handled both cases
   but people found it hard to read *)

let rec load_regpc curr channel =
  try (Scanf.bscanf (Scanf.Scanning.from_string (input_line channel)) "%s %Lx" 
        (fun x y -> load_regpc (set_regpc curr x y) channel)) with
    | End_of_file -> curr
    | Scanf.Scan_failure str -> curr;;
  

let mismatch_string r v1 v2 = 
   let (v1, v2) = (hex_of_big (unsigned32 v1), hex_of_big (unsigned32 v2)) in
  "Mismatched on " ^ reg_to_str r ^ ". Simulated: " ^ v1 ^ "\tReal: " ^ v2 ^ ".\n"

let compare_reg r1 r2 =
   let comp_reg r = if (Word.eq (bii 31) (r1 r) (r2 r)) then ""
                      else mismatch_string r (r1 r) (r2 r) in
   comp_reg EAX ^ comp_reg ECX ^ comp_reg EDX ^ comp_reg EBX ^
   comp_reg ESP ^ comp_reg EBP ^ comp_reg ESI ^ comp_reg EDI 

let compare_pc pc1 pc2 = 
  if (Word.eq (bii 31) pc1 pc2) then "" else
    let (v1, v2) = (hex_of_big (unsigned32 pc1), hex_of_big (unsigned32 pc2)) in
    "Mismatched on PC. Simulated: " ^ v1 ^ "\tReal: " ^ v2 ^ "\n"

let rec compare_mem m1 m2 addrs : unit =
   match addrs with
   | [] -> print_string ""
   | a :: tl -> if (Word.eq (bii 7) (AddrMap.get a m1) (AddrMap.get a m2)) then
                  compare_mem m1 m2 tl
                else
                  let (a, v1, v2) = (hex_of_big (unsigned32 a),
                                    hex_of_big (unsigned8 (AddrMap.get a m1)),
                                    hex_of_big (unsigned8 (AddrMap.get a m2)))
                   in (print_string ("Mem Discrepancy at " ^ a ^ " Simulated: " ^ v1 ^
                        " Real " ^ v2 ^ "\n")); compare_mem m1 m2 tl

(********************************************)
(*     Initializing the machine monad       *)
(********************************************)

let empty_mem = (Word.zero (bii 7), PTree.empty);;
let empty_reg = (fun reg -> Word.zero (bii 31));;
let empty_seg = (fun seg -> Word.zero (bii 31));;
let empty_regpcseg = (empty_reg, Word.zero (bii 31), empty_seg);;

let empty_oracle =
  { oracle_bits = (fun a b -> zero_big_int); oracle_offset = zero_big_int }

let (loaded_mem, _) = load_memory empty_mem [] mem_file;;
let (loaded_reg, pc, loaded_seg) = load_regpc empty_regpcseg reg_file;;

let init_machine =     
  { gp_regs = loaded_reg;
    seg_regs_starts =  loaded_seg;
    seg_regs_limits = (fun seg_reg->(Word.repr (bii 31) (Word.max_unsigned
                                                           (bii 31))));
    flags_reg = (fun f -> Word.zero (bii 0));
    control_regs = (fun c -> Word.zero (bii 31));
    debug_regs =  (fun d -> Word.zero (bii 31));
    pc_reg = pc};;

let init_rtl_state =
  { rtl_oracle = empty_oracle;
    rtl_env = empty_env;
    rtl_mach_state = init_machine;
    rtl_memory = loaded_mem };;


(* Wrapper for the step function that is extracted from Coq. *)

let mstep m = match step m with
  | (Okay_ans tt, m) -> m
  | (SafeFail_ans, _)  -> raise FailSafe;
  | (Fail_ans, _) -> raise Fail;;

(* Recursive function that steps the simulated machine repeatedly.
   Checks at each step whether we
     (1) There's a mismatch between our simulated registers/pc and the
         real registers/pc.
     (2) We reach the Fail or SafeFail state
     (3) We reach the end of the register trace file
*)

let rec step_total m = 
  try (let (realregs, realpc, _ ) = load_regpc empty_regpcseg reg_file  in
        let mnew = mstep m in
         print_regs (rtl_mach_state mnew);
         print_flags (rtl_mach_state mnew);
         let simregs = fun r -> (get_location (bii 31) (Coq_reg_loc r) (rtl_mach_state mnew)) in
         let simpc = get_location (bii 31) (Coq_pc_loc) (rtl_mach_state mnew) in
           match (compare_reg simregs realregs, compare_pc simpc realpc) with
             | ("", "") -> step_total mnew 
             | (s1, s2) -> print_string s1; print_string s2)
  with 
    | EndReg -> print_string "Ok matched all register states\n";
                try(let endmem_file = open_in Sys.argv.(3) in
                  let (endmem, addrs) = load_memory empty_mem [] endmem_file in
                       compare_mem (rtl_memory m) endmem addrs) with
                    | Sys_error _ | Invalid_argument _ -> 
                         print_string "No extra memory file." 
    | Fail -> print_string "Machined reached the Fail state"
    | FailSafe -> print_string "Machined reached the SafeFail state"
;;

print_regs init_machine;;
print_string "\nStarting to step through machine states...";;

step_total init_rtl_state;; 
print_string "\n\n";;
