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
open X86Semantics2
open X86Syntax

let mem_file = open_in Sys.argv.(1)
let reg_file = open_in Sys.argv.(2)
let bii = big_int_of_int
let unsigned8 = (Word.unsigned (bii 7))
let unsigned32 = (Word.unsigned (bii 31))
let signed32 = (Word.signed (bii 31))
let print_hex h = Printf.printf "%Lx" h
let sprint_hex h = Printf.sprintf "%Lx" h
let print_bigint x = print_string (string_of_big_int x)
let hex_of_big x = sprint_hex (int64_of_big_int x)


let reg_to_str r = match r with 
		       | EAX -> "EAX"
		       | ECX -> "ECX"
		       | EDX -> "EDX"
		       | EBX -> "EBX"
		       | ESP -> "ESP"
		       | EBP -> "EBP"
		       | ESI -> "ESI"
                       | EDI -> "EDI";;

let addr_to_string a =
        (hex_of_big (signed32 (addrDisp a))) ^ "(" ^
         (match addrBase a with
                | Some reg -> reg_to_str reg
                | None -> "None") ^ ")" ^
         (match addrIndex a with
                | None -> ""
                | Some (s, r2) -> (hex_of_big (unsigned32 (scale_to_int32 s)))
         ^ ":" ^ reg_to_str (r2));;
                 


let oper_to_str op = match op with
        | Reg_op r -> reg_to_str r
        | Imm_op n -> string_of_big_int(unsigned32 n)
        | Address_op a -> addr_to_string a
        |_ -> "???";;


let reg_or_imm_to_str op = match op with
        (* Actually you can't access ESP,EBP,ESI,EDI  at all... need to fix *)
        | Reg_ri r -> reg_to_str r
        | Imm_ri n -> string_of_big_int(unsigned8 n);;

let instr_to_str instr =
        let p3 (w, a, b) = string_of_bool w ^ " " ^  oper_to_str a ^ " " ^
                oper_to_str b in
        let p_bool_op (w, a) = string_of_bool w ^ " " ^ oper_to_str a in
        let p_op_pair (a,b) = oper_to_str a ^ " " ^ oper_to_str b in
        match instr with 
        | AAA -> "AAA"
        | AAD -> "AAD"
        | AAM -> "AAM"
        | AAS -> "AAS"
        | ADC (w, a, b) -> "ADC " ^ p3 (w,a,b)
        | ADD (w, a, b) -> "ADD " ^ p3 (w,a,b)
        | AND (w, a, b) -> "AND " ^ p3 (w,a,b)
        | CMP (w, a, b) -> "CMP " ^ p3 (w,a,b)
        | MOV (w, a, b) -> "MOV " ^ p3 (w,a,b)
        | OR  (w, a, b) -> "OR "  ^ p3 (w,a,b)
        | SBB (w, a, b) -> "SBB " ^ p3 (w,a,b)
        | SUB (w, a, b) -> "SUB " ^ p3 (w,a,b)
        | BSF (a,b) -> "BSF " ^ p_op_pair (a,b) 
        | BSR (a,b) -> "BSR " ^ p_op_pair (a,b) 
        | BSWAP r -> "BSWAP " ^ (reg_to_str r) 
        | DEC (w, a) -> "DEC " ^ p_bool_op (w, a) 
        | INC (w, a) -> "INC " ^ p_bool_op (w, a)
        | NEG (w, a) -> "NEG " ^ p_bool_op (w, a)
        | NOT (w, a) -> "NOT " ^ p_bool_op (w, a)
        | PUSH (w,a) -> "PUSH " ^  p_bool_op (w, a)
        | CALL (n, a, op1, sel) -> "CALL " ^ string_of_bool (n) ^ " " ^ p_bool_op
                (a, op1)
        | _ -> "???"

let empty_mem =
  (Word.zero (bii 7), PTree.empty)

let rec conv_total s m f chan = 
        try (let newm = (Scanf.bscanf (Scanf.Scanning.from_string (input_line chan))
                s (f m)) in
                conv_total s newm f chan) with
                | End_of_file -> m
                | Scanf.Scan_failure str -> m;;

(* This is stupid but I don't want to fight with ocaml's numeric types.
 * We'll use int64s to read in the addresses (even though they're 32 bits)
 * Why? Because although you can read scanf in int32s interpreting it as an
 * unsigned int, when you go to convert to bigint, it will treat it as signed.
 * *)

let update_mem m x y = 
       (*print_string (string_of_big_int ( big_int_of_int64 x));*)
        (Word32Map.set (Word.repr (bii 31) (big_int_of_int64 x)) 
        (Word.repr (bii 7) (big_int_of_int64 y)) m)
        

let loaded_mem = conv_total "%Lx %Lx" empty_mem update_mem mem_file;;

print_string "Memory loaded.";;

let update eq f x0 y x =
       match eq x0 x with
       | true -> y
       | false -> f x

let set_regpc (regs,pc) s x = let v = Word.repr (bii 31) (big_int_of_int64 x) in
        let set_reg r y = (update X86Syntax.register_eq_dec regs r y) in
        match s with
          | "EAX" -> (set_reg EAX v, pc)
          | "ECX" -> (set_reg ECX v, pc)
          | "EDX" -> (set_reg EDX v, pc)
          | "EBX" -> (set_reg EBX v, pc)
          | "ESP" -> (set_reg ESP v, pc)
          | "EBP" -> (set_reg EBP v, pc)
          | "ESI" -> (set_reg ESI v, pc)
          | "EDI" -> (set_reg EDI v, pc)
          | "EIP" -> (regs, v) 
          | _ -> (regs, pc)


let compare_regpc m mismatches s x = let v = Word.repr (bii 31) (big_int_of_int64 x) in
        let comp_reg r v = match Word.eq (bii 31) ((gp_regs m) r) v with
                | true -> mismatches
                | false -> ("Mismatched on " ^ reg_to_str r ^ " (Simulated: " ^
                        hex_of_big (unsigned32 ((gp_regs m) r)) ^ " Real: " ^
                        hex_of_big (unsigned32 v) ^ ")\n") :: mismatches in
        match s with
          | "EAX" -> comp_reg EAX v
          | "ECX" -> comp_reg ECX v
          | "EDX" -> comp_reg EDX v
          | "EBX" -> comp_reg EBX v
          | "ESP" -> comp_reg ESP v
          | "EBP" -> comp_reg EBP v
          | "ESI" -> comp_reg ESI v
          | "EDI" -> comp_reg EDI v
          | "EIP" -> (match Word.eq (bii 31) (pc_reg m) v with
                | true -> mismatches
                | false -> "Mismatched on EIP\n" :: mismatches)
          | "END" -> raise EndReg 
          | _ -> mismatches

let empty_reg = (fun reg -> Word.zero (bii 31));;

let (loaded_reg, pc) = conv_total "%s %Lx" (empty_reg, (Word.zero (bii 31)))
        set_regpc reg_file;;

let empty_oracle =
  { oracle_bits = (fun c -> false); oracle_offset = zero_big_int }
  
let init_machine =
        { gp_regs = loaded_reg; 
    seg_regs = (fun seg_reg -> Word.zero (bii 31));
    seg_regs_starts = (fun seg_reg-> Word.zero (bii 31));
    seg_regs_limits = (fun seg_reg->(Word.repr (bii 31) (Word.max_unsigned (bii
    31))));
    ps_regs = (fun a b -> Word.zero (bii 31));
    flags_reg = (fun f -> false); control_regs =
    (fun c -> Word.zero (bii 31)); debug_regs = (fun d -> Word.zero (bii 31));
    mem = loaded_mem; pc_reg = pc;  mach_oracle = empty_oracle };;


let mstep m = match step m with
        | Succ (m,u) -> m
        | SafelyFailed  -> raise FailSafe;
        | _-> raise Fail;;


let print_regs m =
        let pr x = print_string (reg_to_str x ^ " ");   
                print_string (hex_of_big (unsigned32 (gp_regs m x))); print_string
                "\n" in
        pr EAX; pr ECX; pr EDX; pr EBX; pr ESP; pr EBP; pr ESI; pr EDI;
        print_string "EIP "; print_string (hex_of_big (unsigned32 (pc_reg m)));
        print_string "\n\n";;

let step_instrumented =
  coq_Bind (Obj.magic coq_Mach_monad) (Obj.magic get_pc) (fun pc ->
    coq_Bind (Obj.magic coq_Mach_monad) (Obj.magic (in_seg_bounds CS pc))
      (fun pc_in_bounds ->
      if pc_in_bounds
      then coq_Bind (Obj.magic coq_Mach_monad)
             (Obj.magic (fetch_instruction pc)) (fun v ->
             let (pi, length0) = v in
             let (pre, instr0) = pi in
             let default_new_pc =
               Word.add (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ Big.zero)))))))))))))))))))))))))))))))
                 pc
                 (Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ Big.zero))))))))))))))))))))))))))))))) length0)
             in print_string (instr_to_str instr0);
             coq_Bind (Obj.magic coq_Mach_monad) (set_pc default_new_pc)
               (fun x ->
               coq_Bind (Obj.magic coq_Mach_monad) flush_ps_regs (fun x0 ->
                 m_step_list (CONVERT.instr_to_m_instr_list pre instr0))))
      else coq_SafeFail))

let rec step_total m = 
        try (let mnew = mstep m in
                print_regs mnew;
                (match conv_total "%s %Lx" [] (compare_regpc mnew) reg_file with
                        | [] -> step_total mnew
                        | l -> print_string (List.fold_left (^) "" l) ;
                        step_instrumented m;  m
                 )) with
                | EndReg -> print_string "OK matched all register states."; m
                | Fail -> 
                         print_string "The X86Semantics reached the \"Failed\"
                         state.\n"; step_instrumented m; m
                | FailSafe -> print_string "Did a FailSafe."; step_instrumented m; m ;;
                
print_regs init_machine;;

print_string "Starting to step through machine states...";;

let res = step_total init_machine;;

print_string "\n\n";;
