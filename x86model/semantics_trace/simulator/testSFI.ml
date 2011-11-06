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
open X86SemanticsSFI
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

let string_of_eint e =
        match e with
                | Coq_aligned -> "Aligned"
                | Coq_unaligned -> "Unaligned"
                | Coq_val w -> "Val " ^ hex_of_big (unsigned32 w)

let reg_to_str r = match r with 
		       | EAX -> "EAX"
		       | ECX -> "ECX"
		       | EDX -> "EDX"
		       | EBX -> "EBX"
		       | ESP -> "ESP"
		       | EBP -> "EBP"
		       | ESI -> "ESI"
                       | EDI -> "EDI";;
(*
let addr_to_string a =
        (string_of_z (signed32 (addrDisp a))) ^ "(" ^
         (match addrBase a with
                | Some reg -> reg_to_str reg
                | None -> "None") ^ ")" ^
         (match addrIndex a with
                | None -> ""
                | Some Datatypes.Coq_pair (s, r2) -> (string_of_z (unsigned32 (scale_to_int32 s)))
         ^ ":" ^ reg_to_str (r2));;
                 
*)
let oper_to_str op = match op with
        | Reg_op r -> reg_to_str r
        | Imm_op n -> string_of_big_int(unsigned32 n)
        | Address_op a -> "Address_op ???"
        |_ -> "???";;


let reg_or_imm_to_str op = match op with
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

(* At first one might think "None" should be the default value for the memory 
 * the problem is that fetch_instruction requires all 15 bytes around the EIP
 * to be defined, or else it auto-fails. I didn't ensure that this would be true
 * when I initially wrote the tracer, so now I have to use this trick. *)

let empty_mem =
  (Some (Word.zero (bii 7)), PTree.empty)
 
let empty_memstate =
  (true, PTree.empty)

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

let rec set_memstate_range m b a n =
   match n with
       | 0 -> m
       | n' -> set_memstate_range (Word32Map.set a b m) b 
        (Word.add (bii 31) a (Word.one (bii 31))) (n'-1)
      
let update_mem (m,ms) x y = 
       (*print_string (string_of_big_int ( big_int_of_int64 x));*)
        ((Word32Map.set (Word.repr (bii 31) (big_int_of_int64 x)) (Some
        (Word.repr (bii 7) (big_int_of_int64 y))) m),
         set_memstate_range ms false (Word.repr (bii 31) (big_int_of_int64 x))
           20)
        

let (loaded_mem, loaded_memstate) = conv_total "%Lx %Lx" (empty_mem, empty_memstate) update_mem mem_file;;

print_string "Memory loaded.";;

let update eq f x0 y x =
       match eq x0 x with
       | true -> y
       | false -> f x

let set_regpc (regs,pc) s x = let v = Word.repr (bii 31) (big_int_of_int64 x) in
        let set_reg r y = (update X86Syntax.register_eq_dec regs r (Coq_val y)) in
        match s with
          | "EAX" -> (set_reg EAX v, pc)
          | "ECX" -> (set_reg ECX v, pc)
          | "EDX" -> (set_reg EDX v, pc)
          | "EBX" -> (set_reg EBX v, pc)
          | "ESP" -> (set_reg ESP v, pc)
          | "EBP" -> (set_reg EBP v, pc)
          | "ESI" -> (set_reg ESI v, pc)
          | "EDI" -> (set_reg EDI v, pc)
          | "EIP" -> (regs, Coq_val v) 
          | _ -> (regs, pc)

let reset_pc m v =
  { gp_regs = m.gp_regs; seg_regs_starts =
    m.seg_regs_starts; seg_regs_limits = m.seg_regs_limits;
    memstate = m.memstate; mem = m.mem; pc_reg = v;
    mach_oracle = m.mach_oracle} 

let compare_regpc ((m1, mismatch1), (m2, mismatch2)) s x = let v = Word.repr
        (bii 31) (big_int_of_int64 x) in
        let comp_reg_ind m r v mismatches = 
              match compare_eint_int ((gp_regs m) r) v with
                | true -> (m, mismatches)
                | false -> (m, (("Mismatched on " ^ reg_to_str r ^ " (Simulated: " ^
                        string_of_eint ((gp_regs m) r) ^ " Real: " ^
                        hex_of_big (unsigned32 v) ^ ")\n") :: mismatches)) in
        let comp_reg r v =
               (comp_reg_ind m1 r v mismatch1, comp_reg_ind m2 r v mismatch2) in
        let comp_pc_ind m v mismatches =
               match compare_eint_int (pc_reg m) v with
                | true -> (reset_pc m (Coq_val v), mismatches)
                | false -> (m, (("Mismatched on EIP (Simulated: " ^ (string_of_eint
                             (pc_reg m)) ^ " Real: " ^ (hex_of_big
                             (unsigned32 v)) ^ "\n") :: mismatches)) in
        let comp_pc v =
                (comp_pc_ind m1 v mismatch1, comp_pc_ind m2 v mismatch2) in
        match s with
          | "EAX" -> comp_reg EAX v
          | "ECX" -> comp_reg ECX v
          | "EDX" -> comp_reg EDX v
          | "EBX" -> comp_reg EBX v
          | "ESP" -> comp_reg ESP v
          | "EBP" -> comp_reg EBP v
          | "ESI" -> comp_reg ESI v
          | "EDI" -> comp_reg EDI v
          | "EIP" -> comp_pc v 
          | "END" -> raise EndReg 
          | _ -> ((m1, mismatch1), (m2, mismatch2))

let empty_reg = (fun reg -> Coq_unaligned);;

let (loaded_reg, pc) = conv_total "%s %Lx" (empty_reg, Coq_unaligned)
        set_regpc reg_file;;

let empty_oracle =
  { oracle_bits = (fun c -> false); oracle_offset = zero_big_int }
 
let init_machine =
        { gp_regs = loaded_reg; 
    seg_regs_starts = (fun seg_reg -> Word.zero (bii 31));
    seg_regs_limits = (fun seg_reg -> (Word.repr (bii 31) (Word.max_unsigned
        (bii 31))));
    memstate = loaded_memstate;
    mem = loaded_mem; pc_reg = pc;  mach_oracle = empty_oracle };;

let set_oracle m b =
  { gp_regs = m.gp_regs; seg_regs_starts =
    m.seg_regs_starts; seg_regs_limits = m.seg_regs_limits;
    memstate = m.memstate; mem = m.mem; pc_reg = m.pc_reg;
    mach_oracle = { oracle_bits = (fun c -> b); oracle_offset = zero_big_int}}

let mstep m =
      let m0 = (set_oracle m false) in
      let m1 = (set_oracle m true) in
      match (step m0, step m1) with
        | (Succ (n0,u), Succ (n1, t))  -> (n0, n1)
        | (Succ (n0,u), _)  -> (n0, n0)
        | (_, Succ (n1, u)) -> (n1, n1) 
        | (SafelyFailed, _) -> raise FailSafe
        | (_, SafelyFailed) -> raise FailSafe 
        | _-> raise Fail;;



let print_regs m =
        let pr x = print_string (reg_to_str x ^ " ");  print_string
             (string_of_eint (gp_regs m x)); print_string "\n" in
        pr EAX; pr ECX; pr EDX; pr EBX; pr ESP; pr EBP; pr ESI; pr EDI;
        print_string "EIP "; print_string (string_of_eint (pc_reg m));
        print_string "\n\n";;

let rec step_total m = 
        try (let (m0, m1) = mstep m in
                  (match conv_total "%s %Lx" ((m0, []),(m1, [])) (compare_regpc) reg_file with
                        | ((mnew0,[]),_) -> print_regs mnew0; step_total mnew0
                        | (_,(mnew1, [])) -> print_regs mnew1; step_total mnew1
                        | ((mnew0,l),_) -> print_string (List.fold_left (^) ""
                        l) ; print_regs mnew0; mnew0
                 )) with
                 | EndReg -> print_string "OK matched all register states."; m
                | Fail -> 
                         print_string "The X86Semantics reached the \"Failed\"
                         state."; m
                | FailSafe -> print_string "Did a FailSafe."; m;;
print_regs init_machine;;

print_string "Starting to step through machine states...";;

let res = step_total init_machine;;
print_string "\n\n";; 
