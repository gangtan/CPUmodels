(*open Batteries_uni *)

module F=Format
(*module E=Errormsg *)
open X86Syntax
open Big
(*open Abbrev*)

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

let cond_ty_to_str ct = match ct with
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

let fp_cond_ty_to_str fct = match fct with
  | B_fct -> "b"
  | E_fct -> "e"
  | BE_fct -> "be"
  | U_fct -> "u"
  | NB_fct -> "nb"
  | NE_fct -> "ne"
  | NBE_fct -> "nbe"
  | NU_fct -> "nu"

let pp_addr (a:address) = 
  let l1 = match a.addrIndex with
    | Some (Scale1, idx) -> str_of_reg addrSize idx ^ "*1"
    | Some (Scale2, idx) -> str_of_reg addrSize idx ^ "*2"
    | Some (Scale4, idx) -> str_of_reg addrSize idx ^ "*4"
    | Some (Scale8, idx) -> str_of_reg addrSize idx ^ "*8"
    | None -> ""
  in
  let l2 = match a.addrBase with
    | Some r -> (str_of_reg addrSize r) ^ " " ^ l1
    | None -> l1
  in
  (*let sdisp = signed32_to_hex a.addrDisp in
  if (Big_int.sign_big_int (signed32 a.addrDisp) = 0) then 
    Printf.printf "[%s]" (String.concat "+" l2)
  else if (Big_int.sign_big_int (signed32 a.addrDisp) > 0) then
    if (List.is_empty l2) then Printf.printf "[%s]" sdisp
    else Printf.printf "[%s+%s]" (String.concat "+" l2) sdisp
  else Printf.printf "[%s%s]" (String.concat "+" l2) sdisp *)
  
  let sdisp = to_string a.addrDisp in
    "+" ^ l2 ^ sdisp

let p_size_dir (sz:op_size) = match sz with
    | OpSize8 -> "BYTE PTR "
    | OpSize16 -> "WORD PTR "
    | OpSize32 -> "DWORD PTR "

let reg_or_imm_to_str (sz:op_size) op = match op with
  | Reg_ri r -> str_of_reg sz r
  | Imm_ri n -> "0x" ^ (to_string n)

let pp_operand (sz, op) = 
  match op with
    | Reg_op r -> (str_of_reg sz r)
    | Imm_op n -> (to_string n)
    | Address_op a -> (p_size_dir sz) ^ (pp_addr a)
    | Offset_op w -> to_string w

let lock_rep_to_str pre ins = match pre.lock_rep with
    | Some Coq_lock -> "lock"
    | Some Coq_rep -> 
      (match ins with 
	| CMPS _ | SCAS _ -> "repz"
	| _ -> "rep")
    | Some Coq_repn -> "repnz"
    | None -> ""

let pp_prefix  (pre,ins) = 
  let so_s = match pre.seg_override with
    | Some seg -> "seg_override(" ^ str_of_segreg seg ^ ")"
    | None -> ""
  in 
  let op_s = if pre.op_override then "op_override" else "" in
  let addr_s = if pre.addr_override then "addr_override" else "" in
  (lock_rep_to_str pre ins) ^ so_s ^ op_s ^ addr_s ^ " "

let get_size prefix w = match prefix.op_override, w with
  | true, true -> OpSize16
  | true, false -> OpSize8
  | false, true -> OpSize32
  | false, false -> OpSize8;;

let selector_to_str (sel: selector option) = 
  match sel with
    | Some n -> to_string n
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

let pp_fp_operand fop = 
  match fop with
    | FPS_op offset ->
      "st" ^ 
	(if (eq offset zero) then ""
	 else "(" ^ to_string offset ^ ")")
    | FPM16_op a -> "WORD PTR " ^ (pp_addr a)
    | FPM32_op a -> "DWORD PTR " ^ (pp_addr a)
    | FPM64_op a -> "QWORD PTR " ^ (pp_addr a)
    | FPM80_op a -> "TBYTE PTR " ^ (pp_addr a)

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

let pp_sse_operand  sop = 
  match sop with
  | SSE_XMM_Reg_op ssr -> (str_of_sse_register ssr)
  | SSE_MM_Reg_op mmr -> (str_of_fpu_register mmr)
  | SSE_Addr_op a ->  (pp_addr a)
  | SSE_GP_Reg_op r -> (str_of_reg OpSize32 r)
  | SSE_Imm_op n -> (to_string n)


(** Pretty printing an instruction *)
let pp_instr (prefix, ins) = 
  let pp_one_op (w, op) = 
    let sz = get_size prefix w in
    pp_operand (sz,op)
  in
  let pp_two_ops (w, op1, op2) = 
    let sz = get_size prefix w in
    (pp_operand (sz,op1)) ^ ", " ^ (pp_operand (sz,op2)) in

  let pp_two_ops_sz  (sz1, op1, sz2, op2) = 
    (pp_operand (sz1,op1)) ^ ", " ^ (pp_operand (sz2,op2)) in

  (* the sizes function for movsx and movzx *)
  let movx_sizes prefix w = 
    match prefix.op_override, w with
      | true, true -> (OpSize16, OpSize16)
      | true, false -> (OpSize8, OpSize16)
      | false, false -> (OpSize8, OpSize32)
      | _ -> (OpSize32, OpSize32)
  in
  match ins with 
    | AAA -> Printf.printf "aaa"
    | AAD -> Printf.printf "aad"
    | AAM -> Printf.printf "aam"
    | AAS -> Printf.printf "aas"
    | ADC (w,a,b) -> Printf.printf "adc %s" (pp_two_ops (w,a,b))
    | ADD (w,a,b) -> Printf.printf "add %s" (pp_two_ops (w,a,b))
    | AND (w,a,b) -> Printf.printf "and %s" (pp_two_ops (w,a,b))
    | ARPL (a, b) -> Printf.printf "arpl %s" (pp_two_ops (true, a, b))
    | BOUND (a, b) -> Printf.printf "bound %s" (pp_two_ops (true, a, b))
    | BSF (a,b) -> Printf.printf "bsf %s" (pp_two_ops (true,a,b))
    | BSR (a,b) -> Printf.printf "bsr %s" (pp_two_ops (true,a,b))
    | BSWAP r -> Printf.printf "bswap %s" (str_of_reg OpSize32 r)
    | BT (a,b) -> Printf.printf "bt %s" (pp_two_ops (true,a,b))
    | BTC (a, b) -> Printf.printf "btc %s" (pp_two_ops (true,a,b))
    | BTR (a, b) -> Printf.printf "btr %s" (pp_two_ops (true,a,b))
    | BTS (a, b) -> Printf.printf "bts %s" (pp_two_ops (true,a,b))
    | CALL (true, absolute, op, None) ->
      (* using the comment PC-REL to indicate the pc-relative jump;
    	 disassemblers always seem to print out the absolute address
    	 (i.e., adding the pc following the instr with the offset);
    	 I'll tolerate this for now *)
       let sa = if absolute then "" else "PC-REL" in
	 Printf.printf "call %s %s" sa (pp_one_op (true,op))

    (* far calls *)
    | CALL (false, _, op, sel) ->
      Printf.printf "call far %s:%s" (selector_to_str sel) (pp_one_op (true,op))

    | CDQ -> Printf.printf "cdq"
    | CLC -> Printf.printf "clc"
    | CLD -> Printf.printf "cld"
    | CLI -> Printf.printf "cli"
    | CLTS -> Printf.printf "clts"
    | CMC -> Printf.printf "cmc"
    | CMOVcc (ct,a,b) -> 
      Printf.printf "cmov%s %s" (cond_ty_to_str ct) (pp_two_ops (true,a,b))
    | CMP (w,a,b) -> Printf.printf "cmp %s" (pp_two_ops (w,a,b))
    | CMPS w -> 
      Printf.printf "cmps %s" 
	(pp_two_ops (w, Address_op (mkAddress zero (Some ESI) None), 
		    Address_op (mkAddress zero (Some EDI) None)))

    | CMPXCHG (w,a,b) -> Printf.printf "cmpxchg %s" (pp_two_ops (w,a,b))

    | CPUID -> Printf.printf "cpuid"
    | CWDE -> Printf.printf "cwde"
    | DAA -> Printf.printf "daa"
    | DAS -> Printf.printf "das"
    | DEC (w,a) -> Printf.printf "dec %s" (pp_one_op (w,a))
    | DIV (w,op) -> Printf.printf "div %s" (pp_one_op (w,op))

    | FABS -> Printf.printf "fabs"
    | FADD (true,fop) -> Printf.printf "fadd st, %s" ((pp_fp_operand fop))
    | FADD (false,fop) -> Printf.printf "fadd %s, st" ((pp_fp_operand fop))
    | FADDP fop -> Printf.printf "faddp %s, st" ((pp_fp_operand fop))
    | FCHS -> Printf.printf "fchs"
    | FCMOVcc (fct,fop) -> 
      Printf.printf "fcmov%s st, %s" (fp_cond_ty_to_str fct) ((pp_fp_operand fop))
    | FDIV (fop1,fop2) -> 
      Printf.printf "fdiv %s, %s" (pp_fp_operand fop1) (pp_fp_operand fop2)
    | FDIVP fop -> Printf.printf "fdivp %s, st" ((pp_fp_operand fop))
    | FDIVR (fop1,fop2) -> 
      Printf.printf "fdivr %s, %s" (pp_fp_operand fop1) (pp_fp_operand fop2)
    | FDIVRP fop -> Printf.printf "fdivrp %s, st" (pp_fp_operand fop)
    | FILD fop -> Printf.printf "fild %s" (pp_fp_operand fop)
    | FIST fop -> Printf.printf "fist %s" (pp_fp_operand fop)
    | FISUB fop -> Printf.printf "fisub %s" (pp_fp_operand fop)
    | FISUBR fop -> Printf.printf "fisubr %s" (pp_fp_operand fop)
    | FISTP fop -> Printf.printf "fistp %s" (pp_fp_operand fop)
    | FLD fop -> Printf.printf "fld %s" (pp_fp_operand fop)
    | FLD1 -> Printf.printf "fld1"
    | FLDCW fop -> Printf.printf "fldcw %s" (pp_fp_operand fop)
    | FLDZ -> Printf.printf "fldz"
    | FMUL (true,fop) -> Printf.printf "fmul st, %s" (pp_fp_operand fop)
    | FMUL (false,fop) -> Printf.printf "fmul %s, st" (pp_fp_operand fop)
    | FMULP fop -> Printf.printf "fmulp %s, st" (pp_fp_operand fop)
    | FNSTCW fop -> Printf.printf "fnstcw %s" (pp_fp_operand fop)
    | FNSTSW opt -> 
      (match opt with
      | None -> Printf.printf "fnstsw ax"
      | Some fop -> Printf.printf "fnstsw %s" (pp_fp_operand fop))
    | FPREM -> Printf.printf "fprem"
    | FRNDINT -> Printf.printf "frndint"
    | FSQRT -> Printf.printf "fsqrt"
    | FST fop -> Printf.printf "fst %s" (pp_fp_operand fop)
    | FSTP fop -> Printf.printf "fstp %s" (pp_fp_operand fop)
    | FSUB (fop1,fop2) -> 
      Printf.printf "fsub %s, %s" (pp_fp_operand fop1) (pp_fp_operand fop2)
    | FSUBR (fop1,fop2) -> 
      Printf.printf "fsubr %s, %s" (pp_fp_operand fop1) (pp_fp_operand fop2)
    | FSUBRP fop -> Printf.printf "fsubrp %s, st" (pp_fp_operand fop)
    | FSUBP fop -> Printf.printf "fsubp %s, st" (pp_fp_operand fop)
    | FUCOM fop -> Printf.printf "fucom st, %s" (pp_fp_operand fop)
    | FUCOMI fop -> Printf.printf "fucomi st, %s" (pp_fp_operand fop)
    | FUCOMIP fop -> Printf.printf "fucomip st, %s" (pp_fp_operand fop)
    | FUCOMP fop -> Printf.printf "fucomp %s" (pp_fp_operand fop)
    | FUCOMPP -> Printf.printf "fucompp"
    | FXAM -> Printf.printf "fxam"
    | FXCH fop -> Printf.printf "fxch %s" (pp_fp_operand fop)

    | HLT -> Printf.printf "hlt"
    | IDIV (w,op) -> Printf.printf "idiv %s" (pp_one_op (w,op));
    | IMUL (w,op1,op2,op3) ->
      Printf.printf "imul %s" (pp_one_op (w,op1));
      (match op2 with
	| Some op -> Printf.printf ", %s" (pp_one_op (w,op))
	| None -> ());
      (match op3 with
	| Some n -> Printf.printf "%s" (to_string n)
	| None -> ())
    | IN (w, Some p) -> Printf.printf "in %s%s" (if w then "true" else "false") (to_string p)
    | INC (w,a) -> Printf.printf "inc %s" (pp_one_op (w,a))
    | INS (w) -> Printf.printf "ins %s" (if w then "true" else "false")
    | INTn (n) -> Printf.printf "intn %s" (to_string n)
    | INT -> Printf.printf "int"
    | INTO -> Printf.printf "into"
    | INVD -> Printf.printf "invd"
    | INVLPG (op) -> Printf.printf "invlpg %s" (pp_one_op (true, op))
    | IRET -> Printf.printf "iret"
    | JCXZ (n) -> Printf.printf "jcxz %s" (to_string n)
    | LAHF -> Printf.printf "lahf"
    | Jcc (ct,disp)-> 
      Printf.printf "j%s PC-REL %s" (cond_ty_to_str ct)
	(to_string disp)

    | JMP (true, absolute, op, None) ->
       let sa = if absolute then "" else "PC-REL" in
	 Printf.printf "jmp %s %s" sa (pp_one_op (true,op))

    (* far jumps *)
    | JMP (false, _, op, sel) ->
      Printf.printf "jmp far %s:%s" (selector_to_str sel) (pp_one_op (true,op))

    | LDS (a,b) -> Printf.printf "lds %s" (pp_two_ops (true,a,b))
    | LEA (a,b) -> Printf.printf "lea %s" (pp_two_ops (true,a,b))
    | LEAVE -> Printf.printf "leave"
    | LES (a,b) -> Printf.printf "les %s" (pp_two_ops (true,a,b))
    | LFS (a,b) -> Printf.printf "lfs %s" (pp_two_ops (true,a,b))
    | LGS (a,b) -> Printf.printf "lgs %s" (pp_two_ops (true,a,b))
    | LSS (a,b) -> Printf.printf "lss %s" (pp_two_ops (true,a,b))

    | MOV (w,a,b) -> Printf.printf "mov %s" (pp_two_ops (true,a,b))
    | MOVSR (d,seg,op) -> 
      if d then 
	Printf.printf "mov %s, %s" (pp_one_op (true,op)) (str_of_segreg seg)
      else Printf.printf "mov %s, %s" (str_of_segreg seg) (pp_one_op (true,op))
    | MOVS w -> 
      Printf.printf "movs %s" 
	(pp_two_ops (w, Address_op (mkAddress zero (Some EDI) None), 
		    Address_op (mkAddress zero (Some ESI) None)))

    | MOVSX (w,a,b) -> 
      let sz_from, sz_to = movx_sizes prefix w in
      Printf.printf "movsx %s" (pp_two_ops_sz (sz_to,a,sz_from,b))
    | MOVZX (w,a,b) -> 
      let sz_from, sz_to = movx_sizes prefix w in
      Printf.printf "movzx %s" (pp_two_ops_sz (sz_to,a,sz_from,b))

    | MUL (w,op) -> Printf.printf "mul %s" (pp_one_op (w,op))
    | NEG (w,a) -> Printf.printf "neg %s" (pp_one_op (w,a))
    | NOP (Some op) -> Printf.printf "nop %s" (pp_one_op (true,op))
    | NOT (w,a) -> Printf.printf "not %s" (pp_one_op (w,a))
    | OR  (w,a,b) -> Printf.printf "or %s"  (pp_two_ops (w,a,b))

    | POP op -> Printf.printf "pop %s" (pp_one_op (true,op))
    | POPF -> Printf.printf "popf"
    | PUSH (w,a) -> Printf.printf "push %s" (pp_one_op (w,a))
    | PUSHF -> Printf.printf "pushf"
    | POPSR seg -> Printf.printf "pop %s" (str_of_segreg seg)
    | RET (sameseg, disp) -> 
      let disp_s = match disp with
	| Some n -> to_string n
	| None -> ""
      in 
      let ss_s = if sameseg then "ret" else "ret far"
      in Printf.printf "%s %s" ss_s disp_s

    | ROL (w,op,ri) ->
      Printf.printf "rol %s, %s" (pp_one_op (w,op))
	(reg_or_imm_to_str OpSize32 ri)
    | ROR (w,op,ri) ->
      Printf.printf "ror %s, %s" (pp_one_op (w,op))
	(reg_or_imm_to_str OpSize32 ri)

    | SAHF -> Printf.printf "sahf"

    | SAR (w,op,ri) -> 
      Printf.printf "sar %s, %s" (pp_one_op (w,op)) (reg_or_imm_to_str OpSize32 ri)
    | SCAS w ->
      Printf.printf "scas %s"
	(pp_two_ops (w, Reg_op EAX, Address_op (mkAddress zero (Some EDI) None)))
    | SETcc (ct,op) ->
      Printf.printf "set%s %s" (cond_ty_to_str ct) (pp_one_op (false,op))

    | SHL (w,op,ri) -> 
      Printf.printf "shl %s, %s" (pp_one_op (w,op))
	(reg_or_imm_to_str OpSize32 ri)
    | SHLD (op,r,ri) ->
      Printf.printf "shld %s, %s, %s"
	(pp_one_op (true,op)) (str_of_reg OpSize32 r)
	(reg_or_imm_to_str OpSize32 ri)
    | SHR (w,op,ri) ->
      Printf.printf "shr %s, %s" (pp_one_op (w,op))
	(reg_or_imm_to_str OpSize32 ri)
    | SHRD (op,r,ri) ->
      Printf.printf "shrd %s, %s, %s"
	(pp_one_op (true,op)) (str_of_reg OpSize32 r)
	(reg_or_imm_to_str OpSize32 ri)

    | SBB (w,a,b) -> Printf.printf "sbb %s" (pp_two_ops (w,a,b))
    | SUB (w,a,b) -> Printf.printf "sub %s" (pp_two_ops (w,a,b))

    | STMXCSR sop -> Printf.printf "stmxcsr %s" (pp_sse_operand sop)

    | STOS w -> 
      Printf.printf "stos %s" 
	(pp_two_ops (w, Address_op (mkAddress zero (Some EDI) None), 
		    Reg_op EAX))

    | TEST (w,a,b) -> Printf.printf "test %s" (pp_two_ops (w,a,b))

    | XADD (w,a,b) -> Printf.printf "xadd %s" (pp_two_ops (w,a,b))
    | XCHG (w,a,b) -> Printf.printf "xchg %s" (pp_two_ops (w,a,b))
    | XOR (w,a,b) -> Printf.printf "xor %s" (pp_two_ops (w,a,b))
    | _ -> Printf.printf "???"

let pp_prefix_instr  (pre,ins) = 
  Printf.printf "%s" (pp_prefix (pre,ins)); 
  (pp_instr (pre,ins))

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
