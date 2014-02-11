exception Fail;;
exception FailSafe;;
exception EndReg;;

open X86Semantics
open Big_int


let bii = big_int_of_int
let signed32 = (Word.signed (bii 31))
let signed1 = (Word.signed (bii 0))
let unsigned32 = (Word.unsigned (bii 31))  

let empty_mem = (Word.zero (bii 7), PTree.empty);;
let empty_reg = (fun reg -> Word.zero (bii 31));;
let empty_seg = (fun seg -> Word.zero (bii 31));; 
let empty_regpcseg = (empty_reg, Word.zero (bii 31), empty_seg);; 

let get_instr () = Scanf.scanf "%LX\n" (fun h -> h);;

let reg_file = open_in "regs.txt" (* Sys.argv.(1) *)
let mem_file = open_in "mem.txt" (* Sys.argv.(2) *)

(***Update Machine State *****)


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




let update eq f x0 y x =
  match eq x0 x with
    | true -> y
    | false -> f x


let register_eq_dec x y =
  match x with
  | EAX ->
    (match y with
     | EAX -> true
     | _ -> false)
  | ECX ->
    (match y with
     | ECX -> true
     | _ -> false)
  | EDX ->
    (match y with
     | EDX -> true
     | _ -> false)
  | EBX ->
    (match y with
     | EBX -> true
     | _ -> false)
  | ESP ->
    (match y with
     | ESP -> true
     | _ -> false)
  | EBP ->
    (match y with
     | EBP -> true
     | _ -> false)
  | ESI ->
    (match y with
     | ESI -> true
     | _ -> false)
  | EDI ->
    (match y with
     | EDI -> true
     | _ -> false)


let segment_register_eq_dec x y =
  match x with
  | ES ->
    (match y with
     | ES -> true
     | _ -> false)
  | CS ->
    (match y with
     | CS -> true
     | _ -> false)
  | SS ->
    (match y with
     | SS -> true
     | _ -> false)
  | DS ->
    (match y with
     | DS -> true
     | _ -> false)
  | FS ->
    (match y with
     | FS -> true
     | _ -> false)
  | GS ->
    (match y with
     | GS -> true
     | _ -> false)


let set_regpc (regs,pc,segs) s x =
  let v = Word.repr (bii 31) (big_int_of_int64 x) in
  let set_reg r y = (update register_eq_dec regs r y) in
  let set_seg r y = (update segment_register_eq_dec segs r y) in
  match str_to_reg s with
    | Some r -> (set_reg r v, pc, segs)
    | None -> match s with
                | "GS" -> (regs, pc, set_seg GS v)
                | "FS" -> (regs, pc, set_seg FS v)
                | "EIP" -> (regs, v, segs)
                | "END" -> raise EndReg
                | _ -> (regs, pc, segs)


let rec load_regpc curr channel =
  try (Scanf.bscanf (Scanf.Scanning.from_string (input_line channel)) "%s %Lx"
        (fun x y -> load_regpc (set_regpc curr x y) channel)) with
    | End_of_file -> print_string("\nEnd of file\n");curr
    | Scanf.Scan_failure str -> print_string("\Scan failure\n");curr;; 



let rec load_memory m addrs channel =
  let cast x y = (Word.repr (bii 31) (big_int_of_int64 x),
                  Word.repr (bii 7) (big_int_of_int64 y)) in
  try (let (x, y) = Scanf.bscanf (Scanf.Scanning.from_string (input_line
                      channel)) "%Lx %Lx" cast in
           load_memory m (*(update_mem m x y)*) (x::addrs) channel) with
    | End_of_file -> (m, addrs)
    | Scanf.Scan_failure str -> (m, addrs);; 


(***Update Machine State *****)


let empty_oracle =
  { X86_RTL.oracle_bits = (fun a b -> zero_big_int); X86_RTL.oracle_offset = zero_big_int } 

 let (loaded_mem, _) = load_memory empty_mem [] mem_file;;
let (loaded_reg, pc, loaded_seg) = load_regpc empty_regpcseg reg_file ;;

let init_machine =
  { X86_MACHINE.gp_regs = loaded_reg;
    seg_regs_starts =  loaded_seg;
    seg_regs_limits = (fun seg_reg->(Word.repr (bii 31) (Word.max_unsigned (bii 31))));
    flags_reg = (fun f -> Word.zero (bii 0));
    control_regs = (fun c -> Word.zero (bii 31));
    debug_regs =  (fun d -> Word.zero (bii 31));
    pc_reg = pc; };;

let empty_fpu_machine =
{
  X86_MACHINE.fpu_data_regs = (fun fpr -> (Word.repr(bii 2) (Word.zero(bii 79)))); 
  fpu_status = Word.zero(bii 15);
  fpu_control = Word.zero(bii 15);
  fpu_tags = (fun t -> (Word.repr(bii 2) (Word.zero(bii 1))));
  fpu_lastInstrPtr = Word.zero(bii 47);
  fpu_lastDataPtr = Word.zero(bii 47);
  fpu_lastOpcode = Word.zero(bii 2); };;


let init_full_machine =
  { X86_MACHINE.core = init_machine;
    fpu = empty_fpu_machine;
  }


let init_rtl_state =
  { X86_RTL.rtl_oracle = empty_oracle;
    X86_RTL.rtl_mach_state = init_full_machine;
    rtl_memory = loaded_mem
  };; 



(**************** Begin Print **************************)

let sprint_hex h = Printf.sprintf "%Lx" h
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


let flag_to_str f = match f with
  | X86_MACHINE.CF -> "CF"
  | X86_MACHINE.ZF -> "ZF"
  | X86_MACHINE.SF -> "SF"
  | X86_MACHINE.OF -> "OF"
  | X86_MACHINE.AF -> "AF"
  | X86_MACHINE.PF -> "PF"
  | _ -> "???";; 


let print_flags m =
  let pr x = print_string (flag_to_str x ^ " ");
    print_string (hex_of_big (signed1 (X86_MACHINE.get_location (bii 1) 
                                                                (X86_MACHINE.Coq_flag_loc x) m)));
    print_string "\n" in
  pr X86_MACHINE.OF; pr X86_MACHINE.SF; pr X86_MACHINE.ZF; pr X86_MACHINE.CF; pr X86_MACHINE.AF; 
  pr X86_MACHINE.PF;
  print_string "\n\n";;


let print_regs m =
  let pr x = print_string (reg_to_str x ^ " ");
    print_string (hex_of_big (signed32 (X86_MACHINE.get_location (bii 31) 
								 (X86_MACHINE.Coq_reg_loc x) m)));
    print_string "\n" in
  pr EAX; pr ECX; pr EDX; pr EBX; pr ESP; pr EBP; pr ESI; pr EDI;
  print_string "EIP ";
  print_string (hex_of_big (signed32 (X86_MACHINE.get_location (bii 31) 
							       (X86_MACHINE.Coq_pc_loc) m)));
  print_string "\n\n";;


(**************** End Print **************************)

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




 let rec loop icnt rs = 
   try(
    let (real_regs, real_pc, real_segs) = load_regpc empty_regpcseg reg_file in
    let (rtl_ans, rstate_n) = step rs in
    print_endline ("\nStep "^(string_of_int icnt));  

    match rtl_ans with
    | X86_RTL.Fail_ans -> ( print_endline "Failed\n" )
    | X86_RTL.Trap_ans -> ( print_endline "Safe Failed\n")
    | X86_RTL.Okay_ans _ ->
         print_regs (X86_RTL.rtl_mach_state rstate_n);
         let simregs = fun r -> (X86_MACHINE.get_location (bii 31) (X86_MACHINE.Coq_reg_loc r) (X86_RTL.rtl_mach_state rstate_n)) in
         let simpc = X86_MACHINE.get_location (bii 31) (X86_MACHINE.Coq_pc_loc) (X86_RTL.rtl_mach_state rstate_n) in
           match (compare_reg simregs real_regs, compare_pc simpc real_pc) with
             | ("", "") -> loop (icnt + 1) rstate_n
             | (s1, s2) -> print_string s1; print_string s2
      
   ) 
   with
   | End_of_file -> print_string "EOF\n"
   | Scanf.Scan_failure _-> print_string "scan failure\n"

;;   

let _ = 
loop 0 init_rtl_state;;
