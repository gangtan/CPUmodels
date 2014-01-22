exception Fail;;                                                                                                                                                                                                  
exception FailSafe;;                                                                                                                                                                                              exception EndReg;;


open X86Semantics
open Big_int


let bii = big_int_of_int
let bzero = Word.zero (bii 31)
let bfalse = Word.zero (bii 0)
let print_hex h = Printf.printf "%Lx" h
let sprint_hex h = Printf.sprintf "%Lx" h
let print_bigint x = print_string (string_of_big_int x)

let hex_of_big x = sprint_hex (int64_of_big_int x)

let mem_file = open_in Sys.argv.(1)
let reg_file = open_in Sys.argv.(2)

  
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
  | X86_MACHINE.CF -> "CF"
  | X86_MACHINE.ZF -> "ZF"
  | X86_MACHINE.SF -> "SF"
  | X86_MACHINE.OF -> "OF"
  | X86_MACHINE.AF -> "AF"
  | X86_MACHINE.PF -> "PF"
  | _ -> "???";;



let str_to_flag s = match s with
  | "CF" -> Some X86_MACHINE.CF
  | "ZF" -> Some X86_MACHINE.ZF
  | "SF" -> Some X86_MACHINE.SF
  | "OF" -> Some X86_MACHINE.OF
  | "AF" -> Some X86_MACHINE.AF
  | "PF" -> Some X86_MACHINE.PF
  | _ -> None;;


let print_flags m =
  let pr x = print_string (flag_to_str x ^ " ");
(*    print_string (hex_of_big (unsigned1 (X86_RTL.get_location (bii 1) (Coq_flag_loc x) m))); *)
    print_string "\n" in
  pr X86_MACHINE.OF; pr X86_MACHINE.SF; pr X86_MACHINE.ZF; pr X86_MACHINE.CF; pr X86_MACHINE.AF; pr X86_MACHINE.PF;
  print_string "\n\n";;

let print_regs m =
  let pr x = print_string (reg_to_str x ^ " ");
(*    print_string (hex_of_big (unsigned32 (get_location (bii 31) (X86_MACHINE.Coq_reg_loc x) m))); *)
    print_string "\n" in
  pr EAX; pr ECX; pr EDX; pr EBX; pr ESP; pr EBP; pr ESI; pr EDI;
  print_string "EIP ";
(*  print_string (hex_of_big (unsigned32 (get_location (bii 31) (X86_MACHINE.Coq_pc_loc) m))); *)
  print_string "\n\n";;




let empty_mem = (Word.zero (bii 7), PTree.empty);;                                                                                                                                                                let empty_reg = (fun reg -> Word.zero (bii 31));;                                                                                                                                                                 let empty_seg = (fun seg -> Word.zero (bii 31));; 
let empty_regpcseg = (empty_reg, Word.zero (bii 31), empty_seg);; 


let rec load_memory m addrs channel =
  let cast x y = (Word.repr (bii 31) (big_int_of_int64 x),
                  Word.repr (bii 7) (big_int_of_int64 y)) in
  try (let (x, y) = Scanf.bscanf (Scanf.Scanning.from_string (input_line
                      channel)) "%Lx %Lx" cast in
           load_memory m (x::addrs) channel) with
    | End_of_file -> (m, addrs)
    | Scanf.Scan_failure str -> (m, addrs);;                                                                                                                                                                       

(* You'll notice this is very similar to the load_memory function.
   Previously there was a more general function that handled both cases
   but people found it hard to read *)

let rec load_regpc curr channel =
  try (Scanf.bscanf (Scanf.Scanning.from_string (input_line channel)) "%s %Lx"
		    (fun x y -> load_regpc curr channel)) with
    | End_of_file -> curr
    | Scanf.Scan_failure str -> curr;;




let empty_oracle =
  { X86_RTL.oracle_bits = (fun a b -> zero_big_int); X86_RTL.oracle_offset = zero_big_int } 


let (loaded_mem, _) = load_memory empty_mem [] mem_file;;                                                                                                                                                         let (loaded_reg, pc, loaded_seg) = load_regpc empty_regpcseg reg_file;;



let init_machine =
  { X86_MACHINE.gp_regs = loaded_reg;                                                                                                                                                                                         
    seg_regs_starts =  loaded_seg;                                                                                                                                                                                
    seg_regs_limits = (fun seg_reg->(Word.repr (bii 31) (Word.max_unsigned
                                                           (bii 31))));                                                                                                                                          
    flags_reg = (fun f -> Word.zero (bii 0));                                                                                                                                                                         control_regs = (fun c -> Word.zero (bii 31));                                                                                                                                                                 
    debug_regs =  (fun d -> Word.zero (bii 31));                                                                                                                                                                      pc_reg = pc;                                                                                                                                                                                                    };;


let empty_fpu_machine =
{
  X86_MACHINE.fpu_data_regs = (fun fpr -> (Word.repr(bii 2) (Word.zero(bii 79))));                                                                                                                                  fpu_status = Word.zero(bii 15);                                                                                                                                                                                 
  fpu_control = Word.zero(bii 15);                                                                                                                                                                                
  fpu_tags = (fun t -> (Word.repr(bii 2) (Word.zero(bii 1))));                                                                                                                                                       fpu_lastInstrPtr = Word.zero(bii 47);                                                                                                                                                                             fpu_lastDataPtr = Word.zero(bii 47);                                                                                                                                                                              fpu_lastOpcode = Word.zero(bii 2);                                                                                                                                      
};;


let init_full_machine =
  {  X86_MACHINE.core = init_machine;                                                                                                                                                                                  fpu = empty_fpu_machine; 
  }


let init_rtl_state =
  { X86_RTL.rtl_oracle = empty_oracle;                                                                                                                                                                                rtl_mach_state = init_full_machine;                                                                                                                                                                               rtl_memory = loaded_mem
  };; 


let mstep m = match step m with
  | (X86_RTL.Okay_ans tt, m) -> m
  | _ -> raise Fail;; 

let rec loop icnt m =
  try (let (realregs, realpc, _ ) = load_regpc empty_regpcseg reg_file  in
        let mnew = mstep m in
        print_regs (X86_RTL.rtl_mach_state mnew);                                                                                                                                                              
        print_flags (X86_RTL.rtl_mach_state mnew);                                                                                                                                                             
        loop (icnt + 1) mnew
(*
         let simregs = fun r -> (get_location (bii 31) (X86_MACHINE.Coq_reg_loc r) (X86_RTL.rtl_mach_state mnew)) in
         let simpc = get_location (bii 31) (X86_MACHINE.Coq_pc_loc) (X86_RTL.rtl_mach_state mnew) in
           match (compare_reg simregs realregs, compare_pc simpc realpc) with
             | ("", "") -> loop (icnt + 1) mnew
             | (s1, s2) -> print_string s1; print_string s2                                                                                                                                                        
*)
)
  with
    | EndReg -> print_string "Ok matched all register states\n";
    | Fail -> print_string "Machined reached the Fail state"
    | FailSafe -> print_string "Machined reached the SafeFail state"
;;


let _ = loop 0 init_rtl_state;;
