(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

   
(* This file provides abstract syntax definitions for the MIPS32
 * instruction set architecture. *)
Require Import List.
Require Import ZArith.
Set Implicit Arguments.
Local Open Scope Z_scope.

Require Import Shared.Bits.

(********************************************)
(* Type definitions for MIPS abstract syntax *)
(********************************************)
Definition zero_extend8_32(w:int8) : int32 := Word.repr (Word.unsigned w).
Definition sign_extend8_32(w:int8) : int32 := Word.repr (Word.signed w).
Definition zero_extend16_32(w:int16) : int32 := Word.repr (Word.unsigned w).
Definition sign_extend16_32(w:int16) : int32 := Word.repr (Word.signed w).

Inductive register : Set := 
| Reg : int5 -> register.

Definition register_eq_dec : forall (x y:register), {x=y} + {x<>y}.
  intros.
  decide equality.
  apply Word.eq_dec.
Defined.

Inductive ioperand : Set := 
| Iop : register -> register -> int16 -> ioperand
.
Inductive joperand : Set :=
| Jop : int26 -> joperand
.
Inductive roperand : Set :=
| Rop : register -> register -> register -> int5 -> roperand
.

(* three-register operands *)
Inductive reg3_operand : Set := 
| Reg3_op: register -> register -> register -> reg3_operand.

(* Operands for bgez, bgezal, ...; they compare a register with zero
   and conditionally make a pc-relative jump based on an offset
   operand *)
Inductive bz_operand : Set :=
| BZ_op : register -> int16 -> bz_operand.

Inductive instr : Set :=
| ADD : reg3_operand -> instr
| ADDI : ioperand -> instr
| ADDIU : ioperand -> instr
| ADDU : reg3_operand -> instr
| AND : reg3_operand -> instr
| ANDI : ioperand -> instr
| BEQ : ioperand -> instr
| BGEZ : bz_operand -> instr
| BGEZAL : bz_operand -> instr
| BGTZ : bz_operand -> instr
| BLEZ : bz_operand -> instr
| BLTZ : bz_operand -> instr
| BLTZAL : bz_operand -> instr
| BNE : ioperand -> instr
| DIV : roperand -> instr
| DIVU : roperand -> instr
| J : joperand -> instr
| JAL : joperand -> instr
| JALR : roperand -> instr
| JR : roperand -> instr
| LB : ioperand -> instr
| LBU : ioperand -> instr
| LH : ioperand -> instr
| LHU : ioperand -> instr
| LUI : ioperand -> instr
| LW : ioperand -> instr
| MFHI : roperand -> instr
| MFLO : roperand -> instr
| MUL : reg3_operand -> instr
| MULT : roperand -> instr
| MULTU : roperand -> instr
| NOR : reg3_operand -> instr
| OR : reg3_operand -> instr
| ORI : ioperand -> instr
| SB : ioperand -> instr
| SEB : roperand -> instr
| SEH : roperand -> instr
| SH : ioperand -> instr
| SLL : roperand -> instr
| SLLV : reg3_operand -> instr
| SLT : reg3_operand -> instr
| SLTI : ioperand -> instr
| SLTIU : ioperand -> instr
| SLTU : reg3_operand -> instr
| SRA : roperand -> instr
| SRAV : reg3_operand -> instr
| SRL : roperand -> instr
| SRLV : reg3_operand -> instr
| SUB : reg3_operand -> instr
| SUBU : reg3_operand -> instr
| SW : ioperand -> instr
| XOR : reg3_operand -> instr
| XORI : ioperand -> instr.
