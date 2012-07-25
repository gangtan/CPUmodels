(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)


(* This file provides abstract syntax definitions for the IA32 (x86) 32-bit
 * instruction set architecture. *)
Require Import List.
Require Import Bits.
Require Import ZArith.
Set Implicit Arguments.
Local Open Scope Z_scope.

(********************************************)
(* Type definitions for x86 abstract syntax *)
(********************************************)
Definition zero_extend8_32(w:int8) : int32 := Word.repr (Word.unsigned w).
Definition sign_extend8_32(w:int8) : int32 := Word.repr (Word.signed w).
Definition zero_extend16_32(w:int16) : int32 := Word.repr (Word.unsigned w).
Definition sign_extend16_32(w:int16) : int32 := Word.repr (Word.signed w).
Definition port_number := int8.
Definition interrupt_type := int8.  
Definition selector := int16.  

Inductive register : Set := EAX | ECX | EDX | EBX | ESP | EBP | ESI | EDI.
Definition register_eq_dec : forall (x y:register), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

Definition Z_to_register(n:Z) := 
  match n with 
    | 0 => EAX 
    | 1 => ECX
    | 2 => EDX
    | 3 => EBX 
    | 4 => ESP 
    | 5 => EBP 
    | 6 => ESI
    | _ => EDI
  end.

Inductive scale : Set := Scale1 | Scale2 | Scale4 | Scale8.
Definition scale_eq_dec : forall (x y:scale), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

Definition Z_to_scale n := match n with 
                            | 0 => Scale1
                            | 1 => Scale2
                            | 2 => Scale4
                            | _ => Scale8
                          end.

Inductive segment_register : Set := ES | CS | SS | DS | FS | GS.
Definition segment_register_eq_dec : 
  forall (x y:segment_register), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

Inductive control_register : Set := CR0 | CR2 | CR3 | CR4.
Definition control_register_eq_dec : 
  forall (x y:control_register), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

Inductive debug_register   : Set := DR0 | DR1 | DR2 | DR3 | DR6 | DR7.
Definition debug_register_eq_dec : 
  forall (x y:debug_register), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

(*Based on the floating-point instruction paper, page 25.
http://www-wjp.cs.uni-saarland.de/publikationen/Ba08.pdf *)
Inductive fp_debug_register : Set := eMF | eDB | eBP | eUD | eNM | eDF | eSS | eGP | ePF | eAC | eMC.
Definition fp_debug_register_eq_dec : 
  forall (x y: fp_debug_register), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

Record address : Set := mkAddress {
  addrDisp : int32 ; 
  addrBase : option register ; 
  addrIndex : option (scale * register)
}.

(*
Based on Section 4.2 of text 
"Floating-Point operands may be x87 registers (fp stack elements), or data residing in
memory." 
*)

Inductive fpu_register : Set := Rseven | Rsix | Rfive | Rfour | Rthree | Rtwo | Rone | Rzero.
Definition fpu_register_eq_dec : 
  forall (x y:fpu_register), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

(*
Definition Z_to_fpu_registeRzero(n:Z) :=
  match n with
    | 0 => Rzero
    | 1 => Rone
    | 2 => Rtwo
    | 3 => Rthree
    | 4 => Rfour
    | 5 => Rfive
    | 6 => Rsix
    | _ => Rseven
  end.

Definition Z_to_fpu_registeRone(n:Z) :=
  match n with
    | 0 => Rone
    | 1 => Rtwo
    | 2 => Rthree
    | 3 => Rfour
    | 4 => Rfive
    | 5 => Rsix
    | 6 => Rseven
    | _ => Rzero
  end.

Definition Z_to_fpu_registeRtwo(n:Z) :=
  match n with
    | 0 => Rtwo
    | 1 => Rthree
    | 2 => Rfour
    | 3 => Rfive
    | 4 => Rsix
    | 5 => Rseven
    | 6 => Rzero
    | _ => Rone
  end.

Definition Z_to_fpu_registeRthree(n:Z) :=
  match n with
    | 0 => Rthree
    | 1 => Rfour
    | 2 => Rfive
    | 3 => Rsix
    | 4 => Rseven
    | 5 => Rzero
    | 6 => Rone
    | _ => Rtwo
  end.

Definition Z_to_fpu_registeRfour(n:Z) :=
  match n with
    | 0 => Rfour
    | 1 => Rfive
    | 2 => Rsix
    | 3 => Rseven
    | 4 => Rzero
    | 5 => Rone
    | 6 => Rtwo
    | _ => Rthree
  end.

Definition Z_to_fpu_registeRfive(n:Z) :=
  match n with
    | 0 => Rfive
    | 1 => Rsix
    | 2 => Rseven
    | 3 => Rzero
    | 4 => Rone
    | 5 => Rtwo
    | 6 => Rthree
    | _ => Rfour
  end.

Definition Z_to_fpu_registeRsix(n:Z) :=
  match n with
    | 0 => Rsix
    | 1 => Rseven
    | 2 => Rzero
    | 3 => Rone
    | 4 => Rtwo
    | 5 => Rthree
    | 6 => Rfour
    | _ => Rfive
  end.

Definition Z_to_fpu_registeRseven(n:Z) :=
  match n with
    | 0 => Rseven
    | 1 => Rzero
    | 2 => Rone
    | 3 => Rtwo
    | 4 => Rthree
    | 5 => Rfour
    | 6 => Rfive
    | _ => Rsix
  end.

Definition stack_i (top index : Z) :=
  match top with
    | 0 => Z_to_fpu_registeRzero index
    | 1 => Z_to_fpu_registeRone index
    | 2 => Z_to_fpu_registeRtwo index
    | 3 => Z_to_fpu_registeRthree index
    | 4 => Z_to_fpu_registeRfour index
    | 5 => Z_to_fpu_registeRfive index
    | 6 => Z_to_fpu_registeRsix index
    | _ => Z_to_fpu_registeRseven index
  end.
(*
Record fp_address : Set := mkFpAddress {
  intAddr : address ;
  fp_addrDisp : int64 ;
  fp_addrBase : option fpu_register ;
  fp_addrIndex : option (scale * fpu_register)
}.
*)

*)
Definition fp_address := address.

Inductive fp_status_register : Set := Busy | C3 | Top | C2 | C1 | C0 |
                                      Es | Sf | Pe | Ue | Oe | Ze | De | Ie.

Definition fp_status_register_eq_dec : 
  forall (x y:fp_status_register), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

Inductive fp_control_register : Set := Res15 | Res14 | Res13 | Res7 | Res6 | IC | RC | PC 
									| Pm | Um | Om | Zm | Dm | Im.
Definition fp_control_register_eq_dec : 
  forall (x y:fp_control_register), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

Inductive fp_tagWord_register : Set := valid | zero | special | empty.
Definition fp_tagWord_register_eq_dec : 
  forall (x y:fp_tagWord_register), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

Definition Z_to_fp_tagWord_register (n:Z) :=
  match n with
  | 0 => valid
  | 1 => zero
  | 2 => special
  | _ => empty
  end.

Inductive fpu_tagWords : Set := Tag0 | Tag1 | Tag2 | Tag3 | Tag4 | Tag5 | Tag6 | Tag7.

Definition fp_tagWords_eq_dec : 
  forall (x y:fpu_tagWords), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

Inductive fp_lastOperandPtr_register : Set := 
| Valid
| Undefined.

Definition fp_lastOperandPtr_register_eq_dec : 
  forall (x y:fp_lastOperandPtr_register), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

(*This includes operands for all types of instructions (int, floating-point, etc). *)
Inductive operand : Set := 
| Imm_op : int32 -> operand
| Reg_op : register -> operand
| Address_op : address -> operand
| Offset_op : int32 -> operand
| FPS_op : int3 -> operand 	    (*an index from 0 to 7 relative to stack top *)
| FPM_op : fp_address -> operand.   (*Same as address *)

Inductive reg_or_immed : Set := 
| Reg_ri : register -> reg_or_immed
| Imm_ri : int8 -> reg_or_immed.

Inductive condition_type : Set :=
| O_ct (* overflow *)
| NO_ct (* not overflow *)
| B_ct (* below, not above or equal *)
| NB_ct (* not below, above or equal *)
| E_ct (* equal, zero *)
| NE_ct (* not equal, not zero *)
| BE_ct (* below or equal, not above *)
| NBE_ct (* not below or equal, above *)
| S_ct (* sign *)
| NS_ct (* not sign *)
| P_ct (* parity, parity even *)
| NP_ct (* not parity, parity odd *)
| L_ct  (* less than, not greater than or equal to *)
| NL_ct (* not less than, greater than or equal to *)
| LE_ct (* less than or equal to, not greater than *)
| NLE_ct (* not less than or equal to, greater than *).

Definition condition_type_eq_dec : 
  forall (x y:condition_type), {x=y} + {x<>y}.
  intros ; decide equality.
Defined.

Definition Z_to_condition_type(n:Z) : condition_type := 
  match n with 
    | 0 => O_ct
    | 1 => NO_ct
    | 2 => B_ct
    | 3 => NB_ct
    | 4 => E_ct
    | 5 => NE_ct
    | 6 => BE_ct
    | 7 => NBE_ct 
    | 8 => S_ct 
    | 9 => NS_ct 
    | 10 => P_ct
    | 11 => NP_ct 
    | 12 => L_ct 
    | 13 => NL_ct
    | 14 => LE_ct 
    | _ => NLE_ct
  end.

Inductive instr : Set :=
(* two parts:  1-byte opcode instructions, followed by 2-byte in alphabetical order,
   following Table B-13 and Table ??? *) 
| AAA 
| AAD 
| AAM 
| AAS 
| ADC   : forall (w:bool)(op1 op2:operand), instr
| ADD   : forall (w:bool)(op1 op2:operand), instr
| AND   : forall (w:bool)(op1 op2:operand), instr
| ARPL  : forall (op1 op2:operand), instr
| BOUND : forall (op1 op2:operand), instr
| BSF   : forall (op1 op2:operand), instr
| BSR   : forall (op1 op2:operand), instr
| BSWAP : forall (r:register), instr
| BT    : forall (op1 op2:operand), instr
| BTC   : forall (op1 op2:operand), instr
| BTR   : forall (op1 op2:operand), instr
| BTS   : forall (op1 op2:operand), instr
| CALL  : forall (near:bool)(absolute: bool)(op1:operand)(sel:option selector), instr
| CDQ 
| CLC 
| CLD 
| CLI 
| CLTS 
| CMC
| CMOVcc : forall (ct:condition_type)(op1 op2: operand), instr
| CMP    : forall (w:bool)(op1 op2:operand), instr
| CMPS   : forall (w:bool), instr
| CMPXCHG: forall (w:bool)(op1 op2:operand), instr
| CPUID 
| CWDE 
| DAA 
| DAS
| DEC   : forall (w:bool)(op1:operand), instr
| DIV   : forall (w:bool)(op1:operand), instr

(*Floating-point syntax defined starting here. Table B-38 explains how to read instructions and B-39 has the
actual instruction details. Instructions can be found here: 
http://download.intel.com/products/processor/manual/325383.pdf*)
| F2XM1 : instr
| FABS : instr
| FADD : forall (d: bool)(op1: operand), instr
| FADDP : forall (op1: option operand), instr
| FBLD : forall (op1: operand), instr
| FBSTP : forall (op1: operand), instr
| FCHS : instr
| FCLEX : instr
| FCOM : forall (op1: option operand), instr
| FCOMP : forall (op1: option operand), instr
| FCOMPP : instr
| FCOMIP : forall (op1: operand), instr
| FCOS : instr
| FDECSTP : instr
(*In the stack case, this kind of instruction has a 2-bit R parameter, 
which I have broken up into Rone and Rtwo. Details are shown in table B-38 of the manual *)
| FDIV : forall (d: bool) (Rone: option bool) (Rtwo: option bool) (op1: operand), instr
| FDIVP : forall (op1: option operand), instr
| FDIVR : forall (d: bool) (Rone: option bool) (Rtwo: option bool) (op1: operand), instr
| FDIVRP : forall (op1: operand), instr
| FFREE : forall (op1: operand), instr
| FIADD : forall (op1: operand), instr
| FICOM : forall (op1: operand), instr
| FICOMP : forall (op1: operand), instr
| FIDIV : forall (op1: operand), instr
| FIDIVR : forall (op1: operand), instr
| FILD : forall (op1: operand), instr
| FIMUL : forall (op1: operand), instr
| FINCSTP : instr
| FINIT : instr
| FIST : forall (op1: operand), instr
| FISTP : forall (op1: operand), instr
| FISUB : forall (op1: operand), instr
| FISUBR : forall (op1: operand), instr
| FLD : forall (op1: operand), instr
| FLD1 : instr
| FLDCW : forall (op1: operand), instr
| FLDENV : forall (op1: operand), instr
| FLDL2E : instr
| FLDL2T : instr
| FLDLG2 : instr
| FLDLN2 : instr
| FLDPI : instr
| FLDZ : instr
| FMUL : forall (d: bool) (op1: operand), instr
| FMULP : forall (op1: option operand), instr
| FNOP : instr
| FPATAN : instr
| FPREM : instr
| FPREM1 : instr
| FPTAN : instr
| FRNDINT : instr
| FRSTOR : forall (op1: operand), instr
| FSAVE : forall (op1: operand), instr
| FSCALE : instr
| FSIN : instr
| FSINCOS : instr
| FSQRT : instr
| FST : forall (op1: operand), instr
| FSTCW : forall (op1: operand), instr
| FSTENV : forall (op1: operand), instr
| FSTP : forall (op1: operand), instr
| FSTSW : forall(op1: option operand), instr
| FSUB : forall (d: bool) (Rone: option bool) (Rtwo: option bool) (op1: operand), instr
| FSUBP : forall (op1: option operand), instr
| FSUBR : forall (d: bool) (Rone: option bool) (Rtwo: option bool) (op1: operand), instr
| FSUBRP : forall (op1: operand), instr
| FTST : instr
| FUCOM : forall (op1: operand), instr
| FUCOMP : forall (op1: operand), instr
| FUCOMPP : instr
| FUCOMI : forall (op1: operand), instr
| FUCOMIP : forall (op1: operand), instr
| FXAM : instr
| FXCH : forall (op1: operand), instr
| FXTRACT : instr
| FYL2X : instr
| FYL2XP1 : instr
| FWAIT : instr
(*Floating-Point syntax ends here for now*)

| HLT  
| IDIV  : forall (w:bool)(op1:operand), instr
(* This one is kind of funny -- there are three cases:
   one operand, two operand, and three operand. The one operand
   form is precise and implicitly uses EAX; the other two variants
   can potentially lose some data due to overflow. *)
| IMUL  : forall (w:bool)(op1:operand) (opopt: option operand) (iopt:option int32), instr
| IN    : forall (w:bool)(p: option port_number), instr
| INC   : forall (w:bool)(op1:operand), instr
| INS   : forall (w:bool), instr
| INTn  : forall (it:interrupt_type),instr
| INT   : instr
| INTO  : instr
| INVD  : instr
| INVLPG : forall (op1:operand), instr
| IRET   : instr
| Jcc   : forall (ct:condition_type)(disp:int32), instr
| JCXZ  : forall (b:int8), instr
| JMP   : forall (near:bool)(absolute:bool)(op1: operand)(sel:option selector), instr
| LAHF
| LAR   : forall (op1 op2:operand), instr
| LDS   : forall (op1 op2:operand), instr
| LEA   : forall (op1 op2:operand), instr
| LEAVE
| LES   : forall (op1 op2:operand), instr
| LFS   : forall (op1 op2:operand), instr
| LGDT  : forall (op1:operand), instr
| LGS   : forall (op1 op2:operand), instr
| LIDT  : forall (op1:operand), instr
| LLDT  : forall (op1:operand), instr
| LMSW  : forall (op1:operand), instr
| LODS  : forall (w:bool), instr
| LOOP  : forall (disp:int8), instr
| LOOPZ : forall (disp:int8), instr
| LOOPNZ: forall (disp:int8), instr
| LSL   : forall (op1 op2:operand), instr
| LSS   : forall (op1 op2:operand), instr
| LTR   : forall (op1:operand), instr
| MOV   : forall (w:bool)(op1 op2:operand), instr
(* Note:  when direction is true, we move the first operand to the second.  
 * When the direction is false, we move the second operand to the first. *)
| MOVCR : forall (direction:bool)(cr:control_register)(r:register), instr
| MOVDR : forall (direction:bool)(dr:debug_register)(r:register), instr
| MOVSR : forall (direction:bool)(sr:segment_register)(op1:operand), instr
| MOVBE : forall (op1 op2:operand), instr
| MOVS  : forall (w:bool), instr
| MOVSX : forall (w:bool)(op1 op2:operand), instr
| MOVZX : forall (w:bool)(op1 op2:operand), instr
| MUL   : forall (w:bool)(op1:operand), instr
| NEG   : forall (w:bool)(op:operand), instr
| NOP   : forall (op_opt: option operand), instr
| NOT   : forall (w:bool)(op:operand), instr
| OR    : forall (w:bool)(op1 op2:operand), instr
| OUT   : forall (w:bool)(p:option port_number), instr
| OUTS  : forall (w:bool), instr
| POP   : forall (op1:operand), instr
| POPSR : forall (sr:segment_register), instr
| POPA 
| POPF
| PUSH  : forall (w:bool)(op1:operand), instr
| PUSHSR: forall (sr:segment_register), instr
| PUSHA
| PUSHF
| RCL   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| RCR   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| RDMSR     : instr
| RDPMC     : instr
| RDTSC     : instr
| RDTSCP    : instr
| RET   : forall (same_segment:bool)(disp:option int16), instr
| ROL   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| ROR   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| RSM
| SAHF
| SAR   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| SBB   : forall (w:bool)(op1 op2:operand), instr
| SCAS  : forall (w:bool), instr
| SETcc : forall (ct:condition_type)(op1:operand), instr
| SGDT  : forall (op1:operand), instr
| SHL   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| SHLD  : forall (op1:operand)(r:register)(ri:reg_or_immed), instr
| SHR   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| SHRD  : forall (op1:operand)(r:register)(ri:reg_or_immed), instr
| SIDT  : forall (op1:operand), instr
| SLDT  : forall (op1:operand), instr
| SMSW  : forall (op1:operand), instr
| STC
| STD
| STI
| STOS  : forall (w:bool), instr
| STR   : forall (op1:operand), instr
| SUB   : forall (w:bool)(op1 op2:operand), instr
| TEST  : forall (w:bool)(op1 op2:operand), instr
| UD2
| VERR  : forall (op1:operand), instr
| VERW  : forall (op1:operand), instr
| WAIT
| WBINVD
| WRMSR
| XADD  : forall (w:bool)(op1 op2:operand), instr
| XCHG  : forall (w:bool)(op1 op2:operand), instr
| XLAT 
| XOR   : forall (w:bool)(op1 op2:operand), instr.



Definition fp_lastInstrPtr_register := instr.

Definition fp_opcode_register := instr.

Inductive lock_or_rep : Set := lock | rep | repn.

Record prefix : Set := mkPrefix {
   lock_rep : option lock_or_rep;
   seg_override : option segment_register;
   op_override : bool;
   addr_override : bool
}.


(* To add:

B.3.  MMX instructions
B.4.  Streaming SIMD instructions
B.5.  Floating point instructions

*)
