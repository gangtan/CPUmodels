(* MIPSSyntax.v, Copyright 2010 Greg Morrisett, all rights reserved. *)

(* This file provides abstract syntax definitions for the MIPS32
 * instruction set architecture. *)
Require Import List.
Require Import Bits.
Require Import ZArith.
Set Implicit Arguments.
Local Open Scope Z_scope.

(********************************************)
(* Type definitions for MIPS abstract syntax *)
(********************************************)
Definition zero_extend8_32(w:int8) : int32 := Word.repr (Word.unsigned w).
Definition sign_extend8_32(w:int8) : int32 := Word.repr (Word.signed w).
Definition zero_extend16_32(w:int16) : int32 := Word.repr (Word.unsigned w).
Definition sign_extend16_32(w:int16) : int32 := Word.repr (Word.signed w).

Definition int26 := Word.int 25.
Definition int5 := Word.int 4.

Inductive register : Set := 
| Reg : nat -> register
.
Definition register_eq_dec : forall (x y:register), {x=y} + {x<>y}.
  intros.
  decide equality.
  apply eq_nat_dec.
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

Inductive instr : Set :=
| ADD : roperand -> instr
| ADDI : ioperand -> instr
| ADDIU : ioperand -> instr
| ADDU : roperand -> instr
| AND : roperand -> instr
| ANDI : ioperand -> instr
| BEQ : ioperand -> instr
| BGEZ : ioperand -> instr
| BGEZAL : ioperand -> instr
| BGTZ : ioperand -> instr
| BLEZ : ioperand -> instr
| BLTZ : ioperand -> instr
| BLTZAL : ioperand -> instr
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
| MUL : roperand -> instr
| MULT : roperand -> instr
| MULTU : roperand -> instr
| NOR : roperand -> instr
| OR : roperand -> instr
| ORI : ioperand -> instr
| SB : ioperand -> instr
| SEB : roperand -> instr
| SEH : roperand -> instr
| SH : ioperand -> instr
| SLL : roperand -> instr
| SLLV : roperand -> instr
| SLT : roperand -> instr
| SLTI : ioperand -> instr
| SLTIU : ioperand -> instr
| SLTU : roperand -> instr
| SRA : roperand -> instr
| SRAV : roperand -> instr
| SRL : roperand -> instr
| SRLV : roperand -> instr
| SUB : roperand -> instr
| SUBU : roperand -> instr
| SW : ioperand -> instr
| XOR : roperand -> instr
| XORI : ioperand -> instr
.
