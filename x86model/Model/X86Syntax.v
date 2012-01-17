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

Record address : Set := mkAddress {
  addrDisp : int32 ; 
  addrBase : option register ; 
  addrIndex : option (scale * register)
}.

Inductive operand : Set := 
| Imm_op : int32 -> operand
| Reg_op : register -> operand
| Address_op : address -> operand
| Offset_op : int32 -> operand.

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
