(* Testing the encode-decode loop *)

(*open Batteries_uni *)
(* open Bigarray *)
open Big
open X86Syntax
open Printf

open Decode
open Abbrev
open PrettyPrinter

(*
module E=Errormsg
open Formatutil

open Config
open Instr

open Disassembler
*)

let pp_big_int fmt bi =
  F.printf "%02x" (Big_int.int_of_big_int bi)

let pp_tab fmt = Format.pp_print_tab fmt ()

(** Pretty print a list *)
let rec pp_list ?(sep="") pp_element fmt = function
  | [h] -> Format.fprintf fmt "%a" pp_element h
  | h::t ->
      Format.fprintf fmt "%a%s@,%a"
      pp_element h sep (pp_list ~sep pp_element) t
  | [] -> ()


(* (\** The type used to store bytes in a code section *\) *)
type codeBytes = int list
(* type codeBytes = (int, int8_unsigned_elt, c_layout) Array1.t *)

(* (\* A global array for holding intermediate results of encoding in *)
(*    the encoder-decoder loop *\) *)
(* let bytes:codeBytes = Array1.create int8_unsigned c_layout 15 *)

(** illegal instruction at some loc *)
exception DF_IllegalInstr

(** The maximum number of bytes used by an instructions *)
let maxDecodingLen = 15

let rec decode_instr' (prog:codeBytes) (loc:int)
    (ps:X86_PARSER.instParserState) =
  if (loc >= maxDecodingLen or loc >= List.length prog)
  then raise DF_IllegalInstr 
  else match X86_PARSER.parse_byte ps (int8_of_int (List.nth prog loc)) with 
    | (ps', []) -> decode_instr' prog (loc+1) ps'
    | (_, v::_) -> v

(** decode one instruction. Use 15 as the upper bound of number of bytes 
    to decode. Return the instruction and its length. If the decode fails,
    raise an exception *)
let decode_instr (prog:codeBytes) = 
  decode_instr' prog 0 X86_PARSER.initial_parser_state


(******************************************************)
(** An instruction equivalence checker *)

let address_eq_dec (a1:address) (a2 : address) : bool = 
  (Big_int.eq_big_int a1.addrDisp a2.addrDisp) && 
  a1.addrBase = a2.addrBase &&
  a1.addrIndex = a2.addrIndex

let operand_eq_dec op1 op2 : bool = 
  match op1, op2 with
  | Imm_op i1, Imm_op i2 -> Big_int.eq_big_int i1 i2
  | Reg_op r1, Reg_op r2 -> r1 = r2
  | Address_op a1, Address_op a2 -> address_eq_dec a1 a2
  | Offset_op i1, Offset_op i2 -> Big_int.eq_big_int i1 i2
  | _ -> false

let reg_or_immed_eq_dec ri1 ri2 : bool = 
  match ri1, ri2 with
  | Reg_ri r1, Reg_ri r2 -> r1 = r2
  | Imm_ri i1, Imm_ri i2 -> Big_int.eq_big_int i1 i2
  | _ -> false

let option_eq_dec cmp opt1 opt2 =
  match opt1, opt2 with
  | None, None -> true
  | Some o1, Some o2 -> cmp o1 o2
  | _, _ -> false

let fp_operand_eq_dec op1 op2 = 
  match op1, op2 with
  | FPS_op i1, FPS_op i2 -> Big_int.eq_big_int i1 i2
  | FPM16_op a1, FPM16_op a2 
  | FPM32_op a1, FPM32_op a2 
  | FPM64_op a1, FPM64_op a2 
  | FPM80_op a1, FPM80_op a2 
    -> address_eq_dec a1 a2
  | _, _ -> false

let mmx_operand_eq_dec mop1 mop2 = 
  match mop1, mop2 with
  | GP_Reg_op r1, GP_Reg_op r2 -> r1 = r2
  | MMX_Addr_op a1, MMX_Addr_op a2 -> address_eq_dec a1 a2
  | MMX_Reg_op m1, MMX_Reg_op m2 -> m1 = m2
  | MMX_Imm_op i1, MMX_Imm_op i2 -> Big_int.eq_big_int i1 i2
  | _, _ -> false

let sse_operand_eq_dec sop1 sop2 = 
  match sop1, sop2 with
  | SSE_XMM_Reg_op sr1, SSE_XMM_Reg_op sr2 -> sr1 = sr2
  | SSE_MM_Reg_op mr1, SSE_MM_Reg_op mr2 -> mr1 = mr2
  | SSE_Addr_op a1, SSE_Addr_op a2 -> address_eq_dec a1 a2
  | SSE_GP_Reg_op r1, SSE_GP_Reg_op r2 -> r1 = r2
  | SSE_Imm_op i1, SSE_Imm_op i2 -> Big_int.eq_big_int i1 i2
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

  | ARPL(op11, op12), ARPL (op21, op22)
  | BOUND(op11, op12), BOUND(op21, op22)
  | BSF(op11, op12), BSF(op21, op22)
  | BSR(op11, op12), BSR(op21, op22)
  | BT (op11,op12), BT (op21, op22)
  | BTC(op11, op12), BTC (op21, op22)
  | BTR(op11, op12), BTR (op21, op22)
  | BTS(op11, op12), BTS (op21, op22)
  | LAR (op11, op12), LAR (op21, op22)
  | LDS (op11, op12), LDS (op21, op22)
  | LEA (op11,op12), LEA (op21,op22)
  | LES (op11, op12), LES (op21, op22)
  | LFS (op11, op12), LFS (op21, op22)
  | LGS (op11, op12), LGS (op21, op22)
  | LSL (op11, op12), LSL (op21, op22)
  | LSS (op11, op12), LSS (op21, op22)   
  | MOVBE (op11, op12), MOVBE (op21, op22)
     -> operand_eq_dec op11 op21 && operand_eq_dec op12 op22
  
  | CALL (near1,abs1,op1,sel1), CALL (near2,abs2,op2,sel2)
  | JMP (near1,abs1,op1,sel1), JMP (near2,abs2,op2,sel2) ->
    near1 = near2 && abs2 = abs2 && operand_eq_dec op1 op2
	  && option_eq_dec (Big_int.eq_big_int) sel1 sel2

  | AAA, AAA
  | AAD, AAD
  | AAM, AAM
  | AAS, AAS
  | CDQ, CDQ
  | CLC, CLC
  | CLD, CLD
  | CLI, CLI
  | CLTS, CLTS
  | CMC, CMC
  | CPUID, CPUID
  | CWDE, CWDE
  | DAA, DAA
  | DAS, DAS

  | EMMS, EMMS

  | F2XM1, F2XM1
  | FABS, FABS
  | FCHS, FCHS
  | FNCLEX, FNCLEX
  | FCOMPP, FCOMPP
  | FCOS, FCOS
  | FDECSTP, FDECSTP
  | FINCSTP, FINCSTP
  | FNINIT, FNINIT
  | FLDL2E, FLDL2E
  | FLDL2T, FLDL2T
  | FLDLG2, FLDLG2
  | FLDLN2, FLDLN2
  | FLDPI, FLDPI
  | FLDZ, FLDZ
  | FLD1, FLD1
  | FNOP, FNOP
  | FPATAN, FPATAN
  | FPREM, FPREM
  | FPREM1, FPREM1
  | FPTAN, FPTAN
  | FRNDINT, FRNDINT
  | FSCALE, FSCALE
  | FSIN, FSIN
  | FSINCOS, FSINCOS
  | FSQRT, FSQRT
  | FTST, FTST
  | FUCOMPP, FUCOMPP
  | FXAM, FXAM
  | FXTRACT, FXTRACT
  | FYL2X, FYL2X
  | FYL2XP1, FYL2XP1
  | FWAIT, FWAIT
  
  | HLT, HLT
  | INT, INT
  | INTO, INTO
  | INVD, INVD
  | IRET, IRET
  | LAHF, LAHF
  | LEAVE, LEAVE
  | POPA, POPA
  | POPF, POPF
  | PUSHA, PUSHA
  | PUSHF, PUSHF
  | RDMSR, RDMSR
  | RDPMC, RDPMC
  | RDTSC, RDTSC
  | RDTSCP, RDTSCP
  | RSM, RSM
  | SAHF, SAHF
  | STC, STC
  | STD, STD
  | STI, STI
  | UD2, UD2
  | WBINVD, WBINVD
  | WRMSR, WRMSR
  | XLAT, XLAT

  | SFENCE, SFENCE
    -> true

  | MOVCR (d1, cr1, r1), MOVCR (d2, cr2, r2) 
    -> d1 = d2 && cr1 = cr2 && r1 = r2
 
  | MOVDR (d1, dr1, r1), MOVDR (d2, dr2, r2)
    -> d1 = d2 && dr1 = dr2 && r1 = r2
  | MOVSR (d1, sr1, op1), MOVSR (d2, sr2, op2)
    -> d1 = d2 && sr1 = sr2 && operand_eq_dec op1 op2

  | CMOVcc (ct1, op11, op12), CMOVcc (ct2, op21, op22) ->
    ct1 = ct2 && operand_eq_dec op11 op21 && operand_eq_dec op12 op22

  | CMPS w1, CMPS w2 
  | INS w1, INS w2
  | LODS w1, LODS w2
  | MOVS w1, MOVS w2 
  | OUTS w1, OUTS w2
  | SCAS w1, SCAS w2 
  | STOS w1, STOS w2 -> w1 = w2

  | IN(w1, port_no1), IN(w2, port_no2) 
  | OUT (w1, port_no1), OUT(w2, port_no2) 
    -> w1 = w2 && option_eq_dec (Big_int.eq_big_int) port_no1 port_no2 

  | INTn it1, INTn it2 -> Big_int.eq_big_int it1 it2
 
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
  | FBLD op1, FBLD op2
  | FCOMIP op1, FCOMIP op2
  | FBSTP op1, FBSTP op2
  | FDIVP op1, FDIVP op2
  | FDIVRP op1, FDIVRP op2
  | FFREE op1, FFREE op2
  | FIADD op1, FIADD op2
  | FICOM op1, FICOM op2
  | FICOMP op1, FICOMP op2
  | FIDIV op1, FIDIV op2
  | FIDIVR op1, FIDIVR op2
  | FILD op1, FILD op2 
  | FIMUL op1, FIMUL op2
  | FISUB op1, FISUB op2 
  | FISUBR op1, FISUBR op2 
  | FIST op1, FIST op2 
  | FISTP op1, FISTP op2 
  | FLD op1, FLD op2 
  | FLDCW op1, FLDCW op2 
  | FLDENV op1, FLDENV op2
  | FMULP op1, FMULP op2 
  | FNSAVE op1, FNSAVE op2 
  | FNSTCW op1, FNSTCW op2 
(*  | FNSTSW op1, FNSTSW op2 *)
  | FRSTOR op1, FRSTOR op2
  | FSUBRP op1, FSUBRP op2 
  | FSUBP op1, FSUBP op2   
  | FST op1, FST op2 
  | FSTENV op1, FSTENV op2
  | FSTP op1, FSTP op2 
  | FUCOM op1, FUCOM op2 
  | FUCOMI op1, FUCOMI op2 
  | FUCOMIP op1, FUCOMIP op2 
  | FUCOMP op1, FUCOMP op2 
  | FXCH op1, FXCH op2 
    -> fp_operand_eq_dec op1 op2 

  | FCMOVcc (fct1,op1), FCMOVcc (fct2,op2) ->
    fct1 = fct2 && fp_operand_eq_dec op1 op2

  | FDIV (d1,op12), FDIV (d2, op22)
  | FDIVR (d1,op12), FDIVR (d2, op22)
  | FSUB (d1,op12), FSUB (d2, op22)
  | FSUBR (d1,op12), FSUBR (d2, op22) -> 
    d1 = d2 && fp_operand_eq_dec op12 op22

  | FCOM (opt1), FCOM (opt2)
  | FCOMP (opt1), FCOMP (opt2)
 (* | FNSTSW opt1, FNSTSW opt2  *)
    -> (*option_eq_dec*) fp_operand_eq_dec opt1 opt2

  | IMUL (w1,op1,opopt1,iopt1), IMUL (w2,op2,opopt2,iopt2) ->
    w1 = w2 && operand_eq_dec op1 op2 
    && option_eq_dec operand_eq_dec opopt1 opopt2
    && option_eq_dec (Big_int.eq_big_int) iopt1 iopt2

  | Jcc (ct1,disp1), Jcc (ct2,disp2) ->
    ct1 = ct2 && (Big_int.eq_big_int disp1 disp2)


  | JCXZ b1, JCXZ b2
  | LOOP b1, LOOP b2
  | LOOPZ b1, LOOPZ b2
  | LOOPNZ b1, LOOPNZ b2 -> (Big_int.eq_big_int b1 b2)

  | INVLPG op1, INVLPG op2
  | LGDT op1, LGDT op2
  | LIDT op1, LIDT op2
  | LLDT op1, LLDT op2
  | LMSW op1, LMSW op2
  | LTR op1, LTR op2
  | NOP op1, NOP op2 
  | POP op1, POP op2 
  | SGDT op1, SGDT op2
  | SIDT op1, SIDT op2
  | SLDT op1, SLDT op2
  | SMSW op1, SMSW op2
  | STR op1, STR op2
  | VERR op1, VERR op2
  | VERW op1, VERW op2
    -> operand_eq_dec op1 op2

  | POPSR s1, POPSR s2 
  | PUSHSR s1, PUSHSR s2 -> s1 = s2

  | RET (ss1,dopt1), RET (ss2,dopt2) -> 
    ss1 = ss2 && option_eq_dec (Big_int.eq_big_int) dopt1 dopt2

  | ROL (w1,op1,ri1), ROL (w2,op2,ri2)
  | ROR (w1,op1,ri1), ROR (w2,op2,ri2)
  | RCL (w1,op1,ri1), RCL (w2,op2,ri2)
  | RCR (w1,op1,ri1), RCR (w2,op2,ri2)
  | SAR (w1,op1,ri1), SAR (w2,op2,ri2)
  | SHL (w1,op1,ri1), SHL (w2,op2,ri2)
  | SHR (w1,op1,ri1), SHR (w2,op2,ri2) -> 
    w1 = w2 && operand_eq_dec op1 op2 && reg_or_immed_eq_dec ri1 ri2

  | SETcc (ct1, op1), SETcc (ct2, op2) ->
    ct1 = ct2 && operand_eq_dec op1 op2

  | SHLD (op1,r1,ri1), SHLD(op2, r2, ri2)
  | SHRD (op1,r1,ri1), SHRD(op2, r2, ri2) ->
    operand_eq_dec op1 op2 && r1=r2 && reg_or_immed_eq_dec ri1 ri2

  | MOVD (op11, op12), MOVD (op21, op22) 
  | MOVQ (op11, op12), MOVQ (op21, op22) 
  | PACKSSDW (op11, op12), PACKSSDW (op21, op22) 
  | PACKSSWB (op11, op12), PACKSSWB (op21, op22) 
  | PACKUSWB (op11, op12), PACKUSWB (op21, op22) 
  | PAND (op11, op12), PAND (op21, op22) 
  | PANDN (op11, op12), PANDN (op21, op22) 
  | PMADDWD (op11, op12), PMADDWD (op21, op22) 
  | PMULHUW (op11, op12), PMULHUW (op21, op22) 
  | PMULHW (op11, op12), PMULHW (op21, op22) 
  | PMULLW (op11, op12), PMULLW (op21, op22) 
  | POR (op11, op12), POR (op21, op22) 
  | PXOR (op11, op12), PXOR (op21, op22) ->
    mmx_operand_eq_dec op11 op21 && mmx_operand_eq_dec op12 op22

  | PADD (g1, op11, op12), PADD (g2, op21, op22)
  | PADDS (g1, op11, op12), PADDS (g2, op21, op22)
  | PADDUS (g1, op11, op12), PADDUS (g2, op21, op22)
  | PCMPEQ (g1, op11, op12), PCMPEQ (g2, op21, op22)
  | PCMPGT (g1, op11, op12), PCMPGT (g2, op21, op22)
  | PSLL (g1, op11, op12), PSLL (g2, op21, op22)
  | PSRA (g1, op11, op12), PSRA (g2, op21, op22)
  | PSRL (g1, op11, op12), PSRL (g2, op21, op22)
  | PSUB (g1, op11, op12), PSUB (g2, op21, op22)
  | PSUBS (g1, op11, op12), PSUBS (g2, op21, op22)
  | PSUBUS (g1, op11, op12), PSUBUS (g2, op21, op22)
  | PUNPCKH (g1, op11, op12), PUNPCKH (g2, op21, op22)
  | PUNPCKL (g1, op11, op12), PUNPCKL (g2, op21, op22) ->
    g1 = g2 && mmx_operand_eq_dec op11 op21 && mmx_operand_eq_dec op12 op22

  | LDMXCSR sop1, LDMXCSR sop2
  | STMXCSR sop1, STMXCSR sop2 
  | PREFETCHT0 sop1, PREFETCHT0 sop2 
  | PREFETCHT1 sop1, PREFETCHT1 sop2 
  | PREFETCHT2 sop1, PREFETCHT2 sop2 
  | PREFETCHNTA sop1, PREFETCHNTA sop2 
  -> sse_operand_eq_dec sop1 sop2

  | ADDPS (op11, op12), ADDPS (op21, op22)
  | ADDSS (op11, op12), ADDSS (op21, op22)
  | ANDNPS (op11, op12), ANDNPS (op21, op22)
  | ANDPS (op11, op12), ANDPS (op21, op22)
  | COMISS (op11, op12), COMISS (op21, op22)
  | CVTPI2PS (op11, op12), CVTPI2PS (op21, op22)
  | CVTPS2PI (op11, op12), CVTPS2PI (op21, op22)
  | CVTSI2SS (op11, op12), CVTSI2SS (op21, op22)
  | CVTSS2SI (op11, op12), CVTSS2SI (op21, op22)
  | CVTTPS2PI (op11, op12), CVTTPS2PI (op21, op22)
  | CVTTSS2SI (op11, op12), CVTTSS2SI (op21, op22)
  | DIVPS (op11, op12), DIVPS (op21, op22)
  | DIVSS (op11, op12), DIVSS (op21, op22)
  | MAXPS (op11, op12), MAXPS (op21, op22)
  | MAXSS (op11, op12), MAXSS (op21, op22)
  | MINPS (op11, op12), MINPS (op21, op22)
  | MINSS (op11, op12), MINSS (op21, op22)
  | MOVAPS (op11, op12), MOVAPS (op21, op22)
  | MOVHLPS (op11, op12), MOVHLPS (op21, op22)
  | MOVHPS (op11, op12), MOVHPS (op21, op22)
  | MOVLHPS (op11, op12), MOVLHPS (op21, op22)
  | MOVLPS (op11, op12), MOVLPS (op21, op22)
  | MOVMSKPS (op11, op12), MOVMSKPS (op21, op22)
  | MOVSS (op11, op12), MOVSS (op21, op22)
  | MOVUPS (op11, op12), MOVUPS (op21, op22)
  | MULPS (op11, op12), MULPS (op21, op22)
  | MULSS (op11, op12), MULSS (op21, op22)
  | ORPS (op11, op12), ORPS (op21, op22)
  | RCPPS (op11, op12), RCPPS (op21, op22)
  | RCPSS (op11, op12), RCPSS (op21, op22)
  | RSQRTPS (op11, op12), RSQRTPS (op21, op22)
  | RSQRTSS (op11, op12), RSQRTSS (op21, op22)
  | SQRTPS (op11, op12), SQRTPS (op21, op22)
  | SQRTSS (op11, op12), SQRTSS (op21, op22)
  | SUBPS (op11, op12), SUBPS (op21, op22)
  | SUBSS (op11, op12), SUBSS (op21, op22)
  | UCOMISS (op11, op12), UCOMISS (op21, op22)
  | UNPCKHPS (op11, op12), UNPCKHPS (op21, op22)
  | UNPCKLPS (op11, op12), UNPCKLPS (op21, op22)
  | XORPS (op11, op12), XORPS (op21, op22)
  | PAVGB (op11, op12), PAVGB (op21, op22)
  | PMAXSW (op11, op12), PMAXSW (op21, op22)
  | PMAXUB (op11, op12), PMAXUB (op21, op22)
  | PMINSW (op11, op12), PMINSW (op21, op22)
  | PMINUB (op11, op12), PMINUB (op21, op22)
  | PMOVMSKB (op11, op12), PMOVMSKB (op21, op22)
  | PSADBW (op11, op12), PSADBW (op21, op22)
  | MASKMOVQ (op11, op12), MASKMOVQ (op21, op22)
  | MOVNTPS (op11, op12), MOVNTPS (op21, op22)
  | MOVNTQ (op11, op12), MOVNTQ (op21, op22)
    -> sse_operand_eq_dec op11 op21 && sse_operand_eq_dec op12 op22

  | CMPPS (op11, op12, imm1), CMPPS (op21, op22, imm2)
  | CMPSS (op11, op12, imm1), CMPSS (op21, op22, imm2)
  | SHUFPS (op11, op12, imm1), SHUFPS (op21, op22, imm2)
  | PEXTRW (op11, op12, imm1), PEXTRW (op21, op22, imm2)
  | PINSRW (op11, op12, imm1), PINSRW (op21, op22, imm2)
  | PSHUFW (op11, op12, imm1), PSHUFW (op21, op22, imm2)
    -> sse_operand_eq_dec op11 op21 && sse_operand_eq_dec op12 op22 
                                       && sse_operand_eq_dec imm1 imm2

  | _ -> false

let prefix_eq_dec pre1 pre2 = 
pre1 = pre2 

let pre_instr_eq_dec (pre1,ins1) (pre2,ins2) = 
  prefix_eq_dec pre1 pre2 && instr_eq_dec ins1 ins2 

let succ_count = ref 0
let dec_fails_count = ref 0
let enc_dec_fails_count = ref 0
let enc_fails_count = ref 0

(*let oc() = open_out ".error_log.txt"; *)

let write_enc_dec_to_file pre ins pre' ins' lz = 
	let file = "./error_log.txt" in
	let oc = open_out_gen [Open_append] 0o644 file in 
  let instr = str_of_instr(pre, ins) in
  let new_instr = str_of_instr(pre', ins') in
  
	   Printf.fprintf oc "Encoding-decoding loop fails with instr %s\n" instr;
	   Printf.fprintf oc "after decoding: %s\n\n"

  (*   output_string ".error_log.txt" *)
	  (* (str_of_list ~sep:"," str_of_big_int) lz *)
	   new_instr;
	
	close_out oc;;

let write_dec_fails_to_file pre ins = 
  let file = "./error_log.txt" in
  let oc = open_out_gen [Open_append] 0o644 file in 
  let instr = str_of_instr(pre, ins) in

  Printf.fprintf oc "Decoding step fails after encoding %s\n\n" instr;

  close_out oc;; 


(****************************************************)
(* Testing the encode-decode loop on an instruction *)
let test_encode_decode_instr
    (pre:X86Syntax.prefix) (ins:X86Syntax.instr) =

  match (Encode.enc_pre_instr_bytes pre ins) with
  | None ->
    incr enc_fails_count;
    F.printf "  Instruction %a cannot be encoded!\n"
      pp_prefix_instr (pre,ins)
  | Some lz ->
    let prog = List.map Big_int.int_of_big_int lz in
    try
      let (pre',ins') = decode_instr prog in
      if (not (pre_instr_eq_dec (pre,ins) (pre',ins'))) then
	     (F.printf "  Encoding-decoding loop fails with instr %a\n"
	       pp_prefix_instr (pre,ins);
         write_enc_dec_to_file pre ins pre' ins' lz; 

         incr enc_dec_fails_count;
	       F.printf "    after encoding: @[  %a@]\n after decoding: %a\n"
	      (pp_list ~sep:"," pp_big_int) lz
	       pp_prefix_instr (pre',ins')
		   )
      else
	  (incr succ_count;
	   F.printf "  Encoding-decoding loop succeeds with instr %a\n"
	   pp_prefix_instr (pre,ins) )
    with DF_IllegalInstr ->
       (incr dec_fails_count;
        write_dec_fails_to_file pre ins;
        F.printf "  Decoding step fails after encoding %a\n"
	pp_prefix_instr (pre,ins);
        F.printf "    after encoding: @[  %a@]\n"
	(pp_list ~sep:"," pp_big_int) lz)

