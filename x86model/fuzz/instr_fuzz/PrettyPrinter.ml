(*open Batteries_uni *)

module F=Format
module P=Printf
(*module E=Errormsg *)
open X86Syntax
open Big
open Abbrev

type op_size = OpSize8 | OpSize16 | OpSize32

(* Only supports 32-bit mode for now *)
let addrSize = OpSize32

(** Util functions *)

let mkPrefix l so oo ao =
  {lock_rep = l; seg_override = so; op_override = oo; addr_override = ao}

let emptyPrefix = mkPrefix None None false false

let mkAddress disp base index = 
  {addrDisp=disp; addrBase=base; addrIndex=index}


(** A pretty printer for machine instructions, following the intel syntax *)

let str_of_reg (sz:op_size) r = match sz,r with
  | OpSize8, EAX -> "al"
  | OpSize8, ECX -> "cl"
  | OpSize8, EDX -> "dl"
  | OpSize8, EBX -> "bl"
  | OpSize8, ESP -> "ah"
  | OpSize8, EBP -> "ch"
  | OpSize8, ESI -> "dh"
  | OpSize8, EDI -> "bh"
  | _,_ -> 
    let pre = match sz with
      | OpSize16 -> ""
      | OpSize32 -> "e"
      | OpSize8 -> "Impossible"
    in
    let rs = match r with
      | EAX -> "ax"
      | ECX -> "cx"
      | EDX -> "dx"
      | EBX -> "bx"
      | ESP -> "sp"
      | EBP -> "bp"
      | ESI -> "si"
      | EDI -> "di"
    in pre ^ rs

let str_of_segreg seg = match seg with
  | ES -> "es"
  | CS -> "cs"
  | SS -> "ss"
  | DS -> "ds"
  | FS -> "fs"
  | GS -> "gs";;

let str_of_controlreg cr = match cr with 
  | CR0 -> "CR0"
  | CR2 -> "CR2"
  | CR3 -> "CR3"
  | CR4 -> "CR4";;

let str_of_debugreg db = match db with 
  | DR0 -> "DR0"
  | DR1 -> "DR1"
  | DR2 -> "DR2"
  | DR3 -> "DR3"
  | DR6 -> "DR6"
  | DR7 -> "DR7";;

(*
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
*)

let str_of_cond_ty ct = match ct with
  | O_ct -> "o"
  | NO_ct -> "no"
  | B_ct -> "b"
  | NB_ct -> "nb"
  | E_ct -> "e"
  | NE_ct -> "ne"
  | BE_ct -> "be"
  | NBE_ct -> "nbe"
  | S_ct -> "s"
  | NS_ct -> "ns"
  | P_ct -> "p"
  | NP_ct -> "np"
  | L_ct -> "l"
  | NL_ct -> "nl"
  | LE_ct -> "le"
  | NLE_ct -> "nle"

let str_of_fp_cond_ty fct = match fct with
  | B_fct -> "b"
  | E_fct -> "e"
  | BE_fct -> "be"
  | U_fct -> "u"
  | NB_fct -> "nb"
  | NE_fct -> "ne"
  | NBE_fct -> "nbe"
  | NU_fct -> "nu"

let str_of_addr (a:address) = 
  let l1 = match a.addrIndex with
    | Some (Scale1, idx) -> [str_of_reg addrSize idx ^ "*1"]
    | Some (Scale2, idx) -> [str_of_reg addrSize idx ^ "*2"]
    | Some (Scale4, idx) -> [str_of_reg addrSize idx ^ "*4"]
    | Some (Scale8, idx) -> [str_of_reg addrSize idx ^ "*8"]
    | None -> []
  in
  let l2 = match a.addrBase with
    | Some r -> (str_of_reg addrSize r) :: l1
    | None -> l1
  in
  let sdisp = signed32_to_hex a.addrDisp in
  if (Big_int.sign_big_int (signed32 a.addrDisp) = 0) then 
    Printf.sprintf "[%s]" (String.concat "+" l2)
  else if (Big_int.sign_big_int (signed32 a.addrDisp) > 0) then
    if (List.length l2 = 0) then Printf.sprintf "[%s]" sdisp
    else Printf.sprintf "[%s+%s]" (String.concat "+" l2) sdisp
  else Printf.sprintf "[%s%s]" (String.concat "+" l2) sdisp

let str_of_size_dir (sz:op_size) = match sz with
    | OpSize8 -> "BYTE PTR "
    | OpSize16 -> "WORD PTR "
    | OpSize32 -> "DWORD PTR "

let str_of_reg_or_imm (sz:op_size) op = match op with
  | Reg_ri r -> str_of_reg sz r
  | Imm_ri n -> "0x" ^ hex_of_big (unsigned8 n)


let str_of_operand (sz, op) = 
  match op with
    | Reg_op r -> str_of_reg sz r
    | Imm_op n -> unsigned32_to_hex n
    | Address_op a -> Printf.sprintf "%s %s" (str_of_size_dir sz) (str_of_addr a)
    | Offset_op w -> Printf.sprintf "[%s]" (unsigned32_to_hex w)


let str_of_lock_rep pre ins = match pre.lock_rep with
    | Some Coq_lock -> "lock"
    | Some Coq_rep -> 
      (match ins with 
	| CMPS _ | SCAS _ -> "repz"
	| _ -> "rep")
    | Some Coq_repn -> "repnz"
    | None -> ""

let str_of_prefix (pre,ins) = 
  let so_s = match pre.seg_override with
    | Some seg -> "seg_override(" ^ str_of_segreg seg ^ ")"
    | None -> ""
  in 
  let op_s = if pre.op_override then "op_override" else "" in
  let addr_s = if pre.addr_override then "addr_override" else "" in
  Printf.sprintf "%s %s %s %s" (str_of_lock_rep pre ins) so_s op_s addr_s


let get_size prefix w = match prefix.op_override, w with
  | true, true -> OpSize16
  | true, false -> OpSize8
  | false, true -> OpSize32
  | false, false -> OpSize8;;

let selector_to_str (sel: selector option) = 
  match sel with
    | Some n -> hex_of_big (unsigned16 n)
    | None -> ""

let str_of_fpu_register fr = 
  match fr with
  | ST0 -> "st0"
  | ST1 -> "st1"
  | ST2 -> "st2"
  | ST3 -> "st3"
  | ST4 -> "st4"
  | ST5 -> "st5"
  | ST6 -> "st6"
  | ST7 -> "st7"

let str_of_fp_operand fop = 
  match fop with
    | FPS_op offset ->
      Printf.sprintf "st%s" 
	(if (Big_int.eq_big_int (unsigned3 offset) Big_int.zero_big_int) then ""
	 else "(" ^ (Big_int.string_of_big_int (unsigned3 offset)) ^ ")")
    | FPM16_op a -> Printf.sprintf "WORD PTR %s" (str_of_addr a)
    | FPM32_op a -> Printf.sprintf "DWORD PTR %s" (str_of_addr a)
    | FPM64_op a -> Printf.sprintf "QWORD PTR %s" (str_of_addr a)
    | FPM80_op a -> Printf.sprintf "TBYTE PTR %s" (str_of_addr a)

let str_of_sse_register ssr = 
  match ssr with
  | XMM0 -> "xmm0"
  | XMM1 -> "xmm1"
  | XMM2 -> "xmm2"
  | XMM3 -> "xmm3"
  | XMM4 -> "xmm4"
  | XMM5 -> "xmm5"
  | XMM6 -> "xmm6"
  | XMM7 -> "xmm7"

let str_of_sse_operand sop = 
  match sop with
  | SSE_XMM_Reg_op ssr -> Printf.sprintf "%s" (str_of_sse_register ssr)
  | SSE_MM_Reg_op mmr -> Printf.sprintf "%s" (str_of_fpu_register mmr)
  | SSE_Addr_op a -> Printf.sprintf "%s" (str_of_addr a)
  | SSE_GP_Reg_op r -> Printf.sprintf "%s" (str_of_reg OpSize32 r)
  | SSE_Imm_op n -> Printf.sprintf "%s" (unsigned32_to_hex n)


(** Pretty printing an instruction *)
let str_of_instr (prefix, ins) = 
  let pp_one_op (w, op) = 
    let sz = get_size prefix w in
    Printf.sprintf "%s" (str_of_operand (sz,op))
  in
  let pp_two_ops (w, op1, op2) = 
    let sz = get_size prefix w in
    F.sprintf "%s, %s" (str_of_operand (sz,op1)) (str_of_operand (sz,op2)) in
  let pp_two_ops_sz (sz1, op1, sz2, op2) = 
    F.sprintf "%s, %s" (str_of_operand (sz1,op1)) (str_of_operand (sz2,op2)) in
  (* the sizes function for movsx and movzx *)
  let movx_sizes prefix w = 
    match prefix.op_override, w with
      | true, true -> (OpSize16, OpSize16)
      | true, false -> (OpSize8, OpSize16)
      | false, true -> (OpSize16, OpSize32)
      | false, false -> (OpSize8, OpSize32)
  in
  match ins with 
    | AAA -> "aaa"
    | AAD -> "aad"
    | AAM -> "aam"
    | AAS -> "aas"
    | ADC (w,a,b) -> P.sprintf "adc %s" (pp_two_ops (w,a,b))
    | ADD (w,a,b) -> P.sprintf "add %s" (pp_two_ops (w,a,b))
    | AND (w,a,b) -> P.sprintf "and %s" (pp_two_ops (w,a,b))
    | ARPL (a, b) -> P.sprintf "arpl %s" (pp_two_ops (true, a, b))
    | BOUND (a, b) -> P.sprintf "bound %s" (pp_two_ops (true, a, b))
    | BSF (a,b) -> P.sprintf "bsf %s" (pp_two_ops (true,a,b))
    | BSR (a,b) -> P.sprintf "bsr %s" (pp_two_ops (true,a,b))
    | BSWAP r -> P.sprintf "bswap %s" (str_of_reg OpSize32 r)
    | BT (a,b) -> P.sprintf "bt %s" (pp_two_ops (true,a,b))
    | BTC (a, b) -> P.sprintf "btc %s" (pp_two_ops (true,a,b))
    | BTR (a, b) -> P.sprintf "btr %s" (pp_two_ops (true,a,b))
    | BTS (a, b) -> P.sprintf "bts %s" (pp_two_ops (true,a,b))
    | CALL (true, absolute, op, None) ->
      (* using the comment PC-REL to indicate the pc-relative jump;
    	 disassemblers always seem to print out the absolute address
    	 (i.e., adding the pc following the instr with the offset);
    	 I'll tolerate this for now *)
       let sa = if absolute then "" else "PC-REL" in
	 P.sprintf "call %s %s" sa (pp_one_op (true,op))

    (* far calls *)
    | CALL (false, _, op, sel) ->
      P.sprintf "call far %s:%s" (selector_to_str sel) (pp_one_op (true,op))

    | CDQ -> "cdq"
    | CLC -> "clc"
    | CLD -> "cld"
    | CLI -> "cli"
    | CLTS -> "clts"
    | CMC -> "cmc"
    | CMOVcc (ct,a,b) -> 
      P.sprintf "cmov%s %s" (str_of_cond_ty ct) (pp_two_ops (true,a,b))
    | CMP (w,a,b) -> P.sprintf "cmp %s" (pp_two_ops (w,a,b))
    | CMPS w -> 
      P.sprintf "cmps %s" 
	(pp_two_ops (w, Address_op (mkAddress zero (Some ESI) None), 
		    Address_op (mkAddress zero (Some EDI) None)))

    | CMPXCHG (w,a,b) -> P.sprintf "cmpxchg %s" (pp_two_ops (w,a,b))

    | CPUID -> "cpuid"
    | CWDE -> "cwde"
    | DAA -> "daa"
    | DAS -> "das"
    | DEC (w,a) -> P.sprintf "dec %s" (pp_one_op (w,a))
    | DIV (w,op) -> P.sprintf "div %s" (pp_one_op (w,op))

    | F2XM1 -> "f2xm1 st0"
    | FABS -> "fabs st0"
    | FADD (true,fop) -> P.sprintf "fadd st, %s" (str_of_fp_operand fop)
    | FADD (false,fop) -> P.sprintf "fadd %s, st" (str_of_fp_operand fop)
    | FADDP fop -> P.sprintf "faddp %s, st" (str_of_fp_operand fop)
    | FBLD fop -> P.sprintf "fbld %s, st" (str_of_fp_operand fop) 
    | FBSTP fop -> P.sprintf "fbstp %s, st" (str_of_fp_operand fop) 
    | FCHS -> "fchs st0"
    | FCLEX -> "fclex"
    | FCOM (None) -> P.sprintf "fcom st0, st1"
    | FCOM(Some fop) -> P.sprintf "fcom st0, %s" (str_of_fp_operand fop)
    | FCOMP (None) -> P.sprintf "fcomp st0, st1"
    | FCOMP (Some fop) -> P.sprintf "fcomp st0, %s" (str_of_fp_operand fop)
    | FCOMIP fop -> P.sprintf "fcomip %s" (str_of_fp_operand fop)
    | FCOS -> "fcos st0"
    | FCMOVcc (fct,fop) ->  
      P.sprintf "fcmov%s st, %s" (str_of_fp_cond_ty fct) (str_of_fp_operand fop)
    | FDECSTP -> "fdecstp"
    | FDIV (fop1,fop2) -> 
      P.sprintf "fdiv %s, %s" (str_of_fp_operand fop1) (str_of_fp_operand fop2)
    | FDIVP fop -> P.sprintf "fdivp %s, st" ((str_of_fp_operand fop))
    | FDIVR (fop1,fop2) -> 
      P.sprintf "fdivr %s, %s" (str_of_fp_operand fop1) (str_of_fp_operand fop2)
    | FDIVRP fop -> P.sprintf "fdivrp %s, st" (str_of_fp_operand fop)
    | FFREE fop -> P.sprintf "ffree %s" (str_of_fp_operand fop)
    | FIADD fop -> P.sprintf "fiadd %s" (str_of_fp_operand fop)
    | FICOMP fop -> P.sprintf "ficomp %s" (str_of_fp_operand fop)
    | FIDIV fop -> P.sprintf "fidiv %s" (str_of_fp_operand fop)
    | FIDIVR fop -> P.sprintf "fidivr %s" (str_of_fp_operand fop)
    | FILD fop -> P.sprintf "fild %s" (str_of_fp_operand fop)
    | FIMUL fop -> P.sprintf "fimul %s" (str_of_fp_operand fop)
    | FINCSTP -> "fincstp"
    | FINIT -> "finit"
    | FIST fop -> P.sprintf "fist %s" (str_of_fp_operand fop)
    | FISUB fop -> P.sprintf "fisub %s" (str_of_fp_operand fop)
    | FISUBR fop -> P.sprintf "fisubr %s" (str_of_fp_operand fop)
    | FISTP fop -> P.sprintf "fistp %s" (str_of_fp_operand fop)
    | FLD fop -> P.sprintf "fld %s" (str_of_fp_operand fop)
    | FLD1 -> P.sprintf "fld1"
    | FLDCW fop -> P.sprintf "fldcw %s" (str_of_fp_operand fop)
    | FLDENV fop -> P.sprintf "fldenv %s" (str_of_fp_operand fop)
    | FLDL2E -> "fldl2e"
    | FLDL2T -> "fldl2t"
    | FLDLG2 -> "fldlg2"
    | FLDPI -> "fldpi"
    | FLDZ -> P.sprintf "fldz"
    | FMUL (true,fop) -> P.sprintf "fmul st, %s" (str_of_fp_operand fop)
    | FMUL (false,fop) -> P.sprintf "fmul %s, st" (str_of_fp_operand fop)
    | FMULP fop -> P.sprintf "fmulp %s, st" (str_of_fp_operand fop)
    | FNOP -> "fnop"
    | FNSAVE fop -> P.sprintf "fnsave %s" (str_of_fp_operand fop)
    | FNSTCW fop -> P.sprintf "fnstcw %s" (str_of_fp_operand fop)
    | FNSTSW opt -> 
      (match opt with
      | None -> P.sprintf "fnstsw ax"
      | Some fop -> P.sprintf "fnstsw %s" (str_of_fp_operand fop))
    | FPATAN -> "fpatan"
    | FPREM -> P.sprintf "fprem"
    | FPREM1 -> "fprem1"
    | FPTAN -> "fptan"
    | FRNDINT -> P.sprintf "frndint"
    | FRSTOR fop -> P.sprintf "frstor %s" (str_of_fp_operand fop)
    | FSCALE -> "fscale" 
    | FSIN -> "fsin"
    | FSINCOS -> "fsincos"
    | FSQRT -> P.sprintf "fsqrt"
    | FST fop -> P.sprintf "fst %s" (str_of_fp_operand fop)
    | FSTENV fop -> P.sprintf "fstenv %s" (str_of_fp_operand fop)
    | FSTP fop -> P.sprintf "fstp %s" (str_of_fp_operand fop)
    | FSUB (fop1,fop2) -> 
      P.sprintf "fsub %s, %s" (str_of_fp_operand fop1) (str_of_fp_operand fop2)
    | FSUBR (fop1,fop2) -> 
      P.sprintf "fsubr %s, %s" (str_of_fp_operand fop1) (str_of_fp_operand fop2)
    | FSUBRP fop -> P.sprintf "fsubrp %s, st" (str_of_fp_operand fop)
    | FSUBP fop -> P.sprintf "fsubp %s, st" (str_of_fp_operand fop)
    | FTST -> "ftst"
    | FUCOM fop -> P.sprintf "fucom st, %s" (str_of_fp_operand fop)
    | FUCOMI fop -> P.sprintf "fucomi st, %s" (str_of_fp_operand fop)
    | FUCOMIP fop -> P.sprintf "fucomip st, %s" (str_of_fp_operand fop)
    | FUCOMP fop -> P.sprintf "fucomp %s" (str_of_fp_operand fop)
    | FUCOMPP -> P.sprintf "fucompp"
    | FXAM -> P.sprintf "fxam"
    | FXCH fop -> P.sprintf "fxch %s" (str_of_fp_operand fop)
    | FXTRACT -> "fxctract"
    | FYL2X -> "fyl2x"
    | FYL2XP1 -> "fyl2xp1"
    | FWAIT -> "fwait"

    | HLT -> P.sprintf "hlt"
    | IDIV (w,op) -> P.sprintf "idiv %s" (pp_one_op (w,op))

    | IMUL (w,op1,op2,op3) ->
      let s1 = P.sprintf "imul %s" (pp_one_op (w,op1)) in
      let s2 = 
	match op2 with
	  | Some op -> P.sprintf ", %s" (pp_one_op (w,op))
	  | None -> ""
      in
      let s3 =
	match op3 with
	  | Some n -> P.sprintf "%s" (unsigned32_to_hex n)
	  | None -> ""
      in s1 ^ s2 ^ s3

    | IN (w, Some p) -> P.sprintf "in %s%s" (if w then "true" else "false") (unsigned32_to_hex p)
    | IN (w, None) -> P.sprintf "in %s" (if w then "true" else "false")
    | INC (w,a) -> P.sprintf "inc %s" (pp_one_op (w,a))
    | INS (w) -> P.sprintf "ins %s" (if w then "true" else "false")
    | INTn (n) -> P.sprintf "intn %s" (unsigned32_to_hex n)
    | INT -> "int"
    | INTO -> "into"
    | INVD -> "invd"
    | INVLPG (op) -> P.sprintf "invlpg %s" (pp_one_op (true, op))
    | IRET -> "iret"
    | JCXZ (n) -> P.sprintf "jcxz %s" (unsigned32_to_hex n)
    | LAHF -> "lahf"
    | Jcc (ct,disp)-> 
      P.sprintf "j%s PC-REL %s" (str_of_cond_ty ct)
	(unsigned32_to_hex disp)

    | JMP (true, absolute, op, None) ->
       let sa = if absolute then "" else "PC-REL" in
	 P.sprintf "jmp %s %s" sa (pp_one_op (true,op))

    (* far jumps *)
    | JMP (false, _, op, sel) ->
      P.sprintf "jmp far %s:%s" (selector_to_str sel) (pp_one_op (true,op))

    | LDS (a,b) -> P.sprintf "lds %s" (pp_two_ops (true,a,b))
    | LEA (a,b) -> P.sprintf "lea %s" (pp_two_ops (true,a,b))
    | LEAVE -> P.sprintf "leave"
    | LES (a,b) -> P.sprintf "les %s" (pp_two_ops (true,a,b))
    | LFS (a,b) -> P.sprintf "lfs %s" (pp_two_ops (true,a,b))
    | LGDT (a) -> P.sprintf "lgdt %s" (pp_one_op (true, a))
    | LGS (a,b) -> P.sprintf "lgs %s" (pp_two_ops (true,a,b))
    | LIDT (op) -> P.sprintf "lidt %s" (pp_one_op (true, op))
    | LLDT (op) -> P.sprintf "lldt %s" (pp_one_op (true, op))
    | LMSW (op) -> P.sprintf "lmsw %s" (pp_one_op (true, op)) 
    | LODS (w) -> P.sprintf "lods %s" (if w then "true" else "false")
    | LOOP (disp) -> P.sprintf "loop %s" (unsigned32_to_hex disp)
    | LOOPZ (disp) -> P.sprintf "loopz %s" (unsigned32_to_hex disp)
    | LOOPNZ (disp) -> P.sprintf "loopnz %s" (unsigned32_to_hex disp)
    | LSL (a,b) -> P.sprintf "lsl %s" (pp_two_ops (true,a,b))
    | LSS (a,b) -> P.sprintf "lss %s" (pp_two_ops (true,a,b))
    | LTR (op) -> P.sprintf "ltr %s" (pp_one_op (true, op))    

    | MOV (w,a,b) -> P.sprintf "mov %s" (pp_two_ops (true,a,b))
    | MOVCR (d, cr, reg) ->
      if d then 
	P.sprintf "movcr %s, %s" (str_of_reg OpSize32 reg) (str_of_controlreg cr)
      else P.sprintf "movcr %s, %s" (str_of_controlreg cr) (str_of_reg OpSize32 reg)
    | MOVDR (d, dr, reg) ->
      if d then 
	P.sprintf "movdr %s, %s" (str_of_reg OpSize32 reg) (str_of_debugreg dr)
      else P.sprintf "movdr %s, %s" (str_of_debugreg dr) (str_of_reg OpSize32 reg)
    | MOVSR (d,seg,op) -> 
      if d then 
	P.sprintf "mov %s, %s" (pp_one_op (true,op)) (str_of_segreg seg)
      else P.sprintf "mov %s, %s" (str_of_segreg seg) (pp_one_op (true,op))
    | MOVBE (op1, op2) -> P.sprintf "movbe %s" (pp_two_ops (true, op1, op2))    

    | MOVS w -> 
      P.sprintf "movs %s" 
	(pp_two_ops (w, Address_op (mkAddress zero (Some EDI) None), 
		    Address_op (mkAddress zero (Some ESI) None)))

    | MOVSX (w,a,b) -> 
      let sz_from, sz_to = movx_sizes prefix w in
      P.sprintf "movsx %s" (pp_two_ops_sz (sz_to,a,sz_from,b))
    | MOVZX (w,a,b) -> 
      let sz_from, sz_to = movx_sizes prefix w in
      P.sprintf "movzx %s" (pp_two_ops_sz (sz_to,a,sz_from,b))

    | MUL (w,op) -> P.sprintf "mul %s" (pp_one_op (w,op))
    | NEG (w,a) -> P.sprintf "neg %s" (pp_one_op (w,a))
    | NOP  (op) -> P.sprintf "nop %s" (pp_one_op (true,op))
    | NOT (w,a) -> P.sprintf "not %s" (pp_one_op (w,a))
    | OR  (w,a,b) -> P.sprintf "or %s"  (pp_two_ops (w,a,b))
    | OUT (w, Some n) -> P.sprintf "out %s %s" 
			 (if w then "true" else "false") (to_string n)
    | OUT (w, None) -> P.sprintf "out %s"
	 		 (if w then "true" else "false")
   
    | OUTS (w) -> P.sprintf "outs %s"
	 		 (if w then "true" else "false")
    | POP op -> P.sprintf "pop %s" (pp_one_op (true,op))
    | POPA -> P.sprintf "popa"
    | POPF -> P.sprintf "popf"
    | PUSH (w,a) -> P.sprintf "push %s" (pp_one_op (w,a))
    | PUSHA -> P.sprintf "pusha"
    | PUSHF -> P.sprintf "pushf"
    | PUSHSR seg -> P.sprintf "pushsr %s" (str_of_segreg seg)
    | POPSR seg -> P.sprintf "pop %s" (str_of_segreg seg)

    | RCL (w,op,ri) -> 
      P.sprintf "rcl %s, %s" (pp_one_op (w,op)) (str_of_reg_or_imm OpSize32 ri)
    | RCR (w,op,ri) -> 
      P.sprintf "rcr %s, %s" (pp_one_op (w,op)) (str_of_reg_or_imm OpSize32 ri)
    | RDMSR -> P.sprintf "rdmsr"
    | RDPMC -> P.sprintf "rdpmc"
    | RDTSC -> P.sprintf "rdtsc"
    | RDTSCP -> P.sprintf "rdtscp"
    | RET (sameseg, disp) -> 
      let disp_s = match disp with
	| Some n -> hex_of_big (unsigned16 n)
	| None -> ""
      in 
      let ss_s = if sameseg then "ret" else "ret far"
      in P.sprintf "%s %s" ss_s disp_s

    | ROL (w,op,ri) ->
      P.sprintf "rol %s, %s" (pp_one_op (w,op))
	(str_of_reg_or_imm OpSize32 ri)
    | ROR (w,op,ri) ->
      P.sprintf "ror %s, %s" (pp_one_op (w,op))
	(str_of_reg_or_imm OpSize32 ri)
    
    | RSM -> P.sprintf "rsm"
    | SAHF -> P.sprintf "sahf"

    | SAR (w,op,ri) -> 
      P.sprintf "sar %s, %s" (pp_one_op (w,op)) (str_of_reg_or_imm OpSize32 ri)
    | SBB (w, a, b) -> P.sprintf "sbb %s" (pp_two_ops (w, a, b))
    | SCAS w ->
      P.sprintf "scas %s"
	(pp_two_ops (w, Reg_op EAX, Address_op (mkAddress zero (Some EDI) None)))
    | SETcc (ct,op) ->
      P.sprintf "set%s %s" (str_of_cond_ty ct) (pp_one_op (false,op))
    | SGDT (a) -> P.sprintf "sgdt %s" (pp_one_op (true, a))
    | SHL (w,op,ri) -> 
      P.sprintf "shl %s, %s" (pp_one_op (w,op))
	(str_of_reg_or_imm OpSize32 ri)
    | SHLD (op,r,ri) ->
      P.sprintf "shld %s, %s, %s"
	(pp_one_op (true,op)) (str_of_reg OpSize32 r)
	(str_of_reg_or_imm OpSize32 ri)
    | SHR (w,op,ri) ->
      P.sprintf "shr %s, %s" (pp_one_op (w,op))
	(str_of_reg_or_imm OpSize32 ri)
    | SHRD (op,r,ri) ->
      P.sprintf "shrd %s, %s, %s"
	(pp_one_op (true,op)) (str_of_reg OpSize32 r)
	(str_of_reg_or_imm  OpSize32 ri)
    | SIDT (a) -> P.sprintf "sidt %s" (pp_one_op (true, a))
    | SLDT (a) -> P.sprintf "sldt %s" (pp_one_op (true, a))
    | SMSW (a) -> P.sprintf "smsw %s" (pp_one_op (true, a))
    | STC -> P.sprintf "stc"
    | STD -> P.sprintf "std"
    | STI -> P.sprintf "sti"
    | STR (a) -> P.sprintf "str %s" (pp_one_op (true, a))

    | SUB (w,a,b) -> P.sprintf "sub %s" (pp_two_ops (w,a,b))

    | STMXCSR sop -> P.sprintf "stmxcsr %s" (str_of_sse_operand sop)

    | STOS w -> 
      P.sprintf "stos %s" 
	(pp_two_ops (w, Address_op (mkAddress zero (Some EDI) None), 
		    Reg_op EAX))

    | TEST (w,a,b) -> P.sprintf "test %s" (pp_two_ops (w,a,b))
 
    | UD2 -> P.sprintf "ud2"
    | VERR (a) -> P.sprintf "verr %s" (pp_one_op (true, a))
    | VERW (a) -> P.sprintf "verw %s" (pp_one_op (true, a))
    | WBINVD -> P.sprintf "wbinvd"
    | WRMSR -> P.sprintf "wrmsr"

    | XADD (w,a,b) -> P.sprintf "xadd %s" (pp_two_ops (w,a,b))
    | XCHG (w,a,b) -> P.sprintf "xchg %s" (pp_two_ops (w,a,b))
    | XLAT -> P.sprintf "xlat"
    | XOR (w,a,b) -> P.sprintf "xor %s" (pp_two_ops (w,a,b))
    | _ -> P.sprintf "???"


let pp_prefix_instr fmt (pre,ins) = 
  Format.fprintf fmt "%s %s" (str_of_prefix (pre,ins)) (str_of_instr (pre,ins))

(** An instruction equivalence checker *)
(*
let address_eq_dec (a1:address) (a2 : address) : bool = 
  (Big_int.(=) a1.addrDisp a2.addrDisp) && 
  a1.addrBase = a2.addrBase &&
  a1.addrIndex = a2.addrIndex

let operand_eq_dec op1 op2 : bool = 
  match op1, op2 with
  | Imm_op i1, Imm_op i2 -> Big_int.(=) i1 i2
  | Reg_op r1, Reg_op r2 -> r1 = r2
  | Address_op a1, Address_op a2 -> address_eq_dec a1 a2
  | Offset_op i1, Offset_op i2 -> Big_int.(=) i1 i2
  | _ -> false

let reg_or_immed_eq_dec ri1 ri2 : bool = 
  match ri1, ri2 with
  | Reg_ri r1, Reg_ri r2 -> r1 = r2
  | Imm_ri i1, Imm_ri i2 -> Big_int.(=) i1 i2
  | _ -> false

let option_eq_dec cmp opt1 opt2 =
  match opt1, opt2 with
  | None, None -> true
  | Some o1, Some o2 -> cmp o1 o2
  | _, _ -> false

let fp_operand_eq_dec op1 op2 = 
  match op1, op2 with
  | FPS_op i1, FPS_op i2 -> Big_int.(=) i1 i2
  | FPM16_op a1, FPM16_op a2 
  | FPM32_op a1, FPM32_op a2 
  | FPM64_op a1, FPM64_op a2 
  | FPM80_op a1, FPM80_op a2 
    -> address_eq_dec a1 a2
  | _, _ -> false

let sse_operand_eq_dec sop1 sop2 : bool = 
  match sop1, sop2 with
  | SSE_XMM_Reg_op sr1, SSE_XMM_Reg_op sr2 -> sr1 = sr2
  | SSE_MM_Reg_op mr1, SSE_MM_Reg_op mr2 -> mr1 = mr2
  | SSE_Addr_op a1, SSE_Addr_op a2 -> address_eq_dec a1 a2
  | SSE_GP_Reg_op r1, SSE_GP_Reg_op r2 -> r1 = r2
  | SSE_Imm_op i1, SSE_Imm_op i2 -> Big_int.(=) i1 i2
  | _,_ -> false

(* todo: make it complete for all instructions *)
let instr_eq_dec (ins1:instr) (ins2:instr) : bool =
  match ins1, ins2 with
  | ADC (w1,op11,op12), ADC (w2,op21,op22)
  | ADD (w1,op11,op12), ADD (w2,op21,op22)
  | AND (w1,op11,op12), AND (w2,op21,op22)
  | CMP (w1,op11,op12), CMP (w2,op21,op22)
  | CMPXCHG (w1,op11,op12), CMPXCHG (w2,op21,op22)
  | MOV (w1,op11,op12), MOV (w2,op21,op22)
  | MOVSX (w1,op11,op12), MOVSX (w2,op21,op22)
  | MOVZX (w1,op11,op12), MOVZX (w2,op21,op22)
  | OR (w1,op11,op12), OR (w2,op21,op22) 
  | SBB (w1,op11,op12), SBB (w2,op21,op22) 
  | SUB (w1,op11,op12), SUB (w2,op21,op22) 
  | TEST (w1,op11,op12), TEST (w2,op21,op22) 
  | XADD (w1,op11,op12), XADD (w2,op21,op22)
  | XCHG (w1,op11,op12), XCHG (w2,op21,op22)
  | XOR (w1,op11,op12), XOR (w2,op21,op22)
    -> w1=w2 && operand_eq_dec op11 op21 && operand_eq_dec op12 op22

  | BSWAP r1, BSWAP r2 -> r1 = r2

  | BT (op11,op12), BT (op21, op22)
  | BSR (op11,op12), BSR (op21,op22)
  | LEA (op11,op12), LEA (op21,op22)
    -> operand_eq_dec op11 op21 && operand_eq_dec op12 op22

  | CALL (near1,abs1,op1,sel1), CALL (near2,abs2,op2,sel2)
  | JMP (near1,abs1,op1,sel1), JMP (near2,abs2,op2,sel2) ->
    near1 = near2 && abs2 = abs2 && operand_eq_dec op1 op2
	  && option_eq_dec (Big_int.(=)) sel1 sel2

  | CDQ, CDQ
  | CLD, CLD
  | CWDE, CWDE
  | FABS, FABS
  | FCHS, FCHS
  | FLDZ, FLDZ
  | FLD1, FLD1
  | FPREM, FPREM
  | FRNDINT, FRNDINT
  | FSQRT, FSQRT
  | FUCOMPP, FUCOMPP
  | FXAM, FXAM
  | HLT, HLT
  | LEAVE, LEAVE
  | SAHF, SAHF
    -> true

  | CMOVcc (ct1, op11, op12), CMOVcc (ct2, op21, op22) ->
    ct1 = ct2 && operand_eq_dec op11 op21 && operand_eq_dec op12 op22

  | CMPS w1, CMPS w2 
  | MOVS w1, MOVS w2 
  | SCAS w1, SCAS w2 
  | STOS w1, STOS w2 -> w1 = w2

  | DIV (w1,op1), DIV (w2, op2)
  | DEC (w1,op1), DEC (w2, op2)
  | INC (w1,op1), INC (w2, op2)
  | IDIV (w1,op1), IDIV (w2, op2)
  | MUL (w1,op1), MUL (w2, op2)
  | NEG (w1,op1), NEG (w2, op2)
  | NOT (w1,op1), NOT (w2, op2)
  | PUSH (w1,op1), PUSH (w2,op2) -> w1=w2 && operand_eq_dec op1 op2

  | FADD (d1,op1), FADD (d2,op2)
  | FMUL (d1,op1), FMUL (d2,op2) ->
    d1 = d2 && fp_operand_eq_dec op1 op2

  | FADDP op1, FADDP op2
  | FDIVP op1, FDIVP op2
  | FDIVRP op1, FDIVRP op2
  | FILD op1, FILD op2 
  | FISUB op1, FISUB op2 
  | FISUBR op1, FISUBR op2 
  | FIST op1, FIST op2 
  | FISTP op1, FISTP op2 
  | FLD op1, FLD op2 
  | FLDCW op1, FLDCW op2 
  | FMULP op1, FMULP op2 
  | FNSTCW op1, FNSTCW op2 
  | FSUBRP op1, FSUBRP op2 
  | FSUBP op1, FSUBP op2 
  | FST op1, FST op2 
  | FSTP op1, FSTP op2 
  | FUCOM op1, FUCOM op2 
  | FUCOMI op1, FUCOMI op2 
  | FUCOMIP op1, FUCOMIP op2 
  | FUCOMP op1, FUCOMP op2 
  | FXCH op1, FXCH op2 
    -> fp_operand_eq_dec op1 op2

  | FCMOVcc (fct1,op1), FCMOVcc (fct2,op2) ->
    fct1 = fct2 && fp_operand_eq_dec op1 op2

  | FDIV (op11,op12), FDIV (op21, op22)
  | FDIVR (op11,op12), FDIVR (op21, op22)
  | FSUB (op11,op12), FSUB (op21, op22)
  | FSUBR (op11,op12), FSUBR (op21, op22) -> 
    fp_operand_eq_dec op11 op21 && fp_operand_eq_dec op12 op22

  | FNSTSW opt1, FNSTSW opt2 
    -> option_eq_dec fp_operand_eq_dec opt1 opt2

  | IMUL (w1,op1,opopt1,iopt1), IMUL (w2,op2,opopt2,iopt2) ->
    w1 = w2 && operand_eq_dec op1 op2 
    && option_eq_dec operand_eq_dec opopt1 opopt2
    && option_eq_dec (Big_int.(=)) iopt1 iopt2

  | Jcc (ct1,disp1), Jcc (ct2,disp2) ->
    ct1 = ct2 && (Big_int.(=) disp1 disp2)

  | NOP op1, NOP op2 
  | POP op1, POP op2 -> operand_eq_dec op1 op2

  | RET (ss1,dopt1), RET (ss2,dopt2) -> 
    ss1 = ss2 && option_eq_dec (Big_int.(=)) dopt1 dopt2

  | ROL (w1,op1,ri1), ROL (w2,op2,ri2)
  | ROR (w1,op1,ri1), ROR (w2,op2,ri2)
  | SAR (w1,op1,ri1), SAR (w2,op2,ri2)
  | SHL (w1,op1,ri1), SHL (w2,op2,ri2)
  | SHR (w1,op1,ri1), SHR (w2,op2,ri2) -> 
    w1 = w2 && operand_eq_dec op1 op2 && reg_or_immed_eq_dec ri1 ri2

  | SETcc (ct1, op1), SETcc (ct2, op2) ->
    ct1 = ct2 && operand_eq_dec op1 op2

  | SHLD (op1,r1,ri1), SHLD(op2, r2, ri2)
  | SHRD (op1,r1,ri1), SHRD(op2, r2, ri2) ->
    operand_eq_dec op1 op2 && r1=r2 && reg_or_immed_eq_dec ri1 ri2

  | STMXCSR sop1, STMXCSR sop2 -> 
    sse_operand_eq_dec sop1 sop2

  | _ -> false

let prefix_eq_dec pre1 pre2 = 
  pre1 = pre2

let pre_instr_eq_dec (pre1,ins1) (pre2,ins2) = 
  prefix_eq_dec pre1 pre2 && instr_eq_dec ins1 ins2


(** An instruction validator *)

let assert_reg_op op = match op with
    | Reg_op _ -> true
    | _ -> false

let assert_address_op op = match op with
    | Address_op _ -> true
    | _ -> false

(** Validate the syntax of instructions. Our abstract syntax
    is loose and does not encode many dependencies in real syntax *)
let validate_instr prefix ins = match ins with
  (* In near calls, selector must be none *)
  | CALL (true, absolute, op, sel) -> sel = None
  (* far calls must be absolute calls; 
     is this right??? or our decoder.v is wrong about the patterns for call_p *)
  | CALL (false, absolute, op, sel) -> absolute

  (* the source op must be an address and the destination must be a register *)
  | LDS (op1,op2)
  | LES (op1,op2)
  | LFS (op1,op2)
  | LGS (op1,op2)
  | LSS (op1,op2) -> (assert_reg_op op1) && (assert_address_op op2)

  | _ -> true

  *)
