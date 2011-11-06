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
open MIPSSyntax
open MIPSSemantics
open MIPS_RTL
open MIPS_MACHINE
open MIPS_PARSER

let bii = big_int_of_int
;;
let reg_to_str (r:register) = "R"^string_of_big_int r
;;

let rop_to_str (r:roperand) =
  match r with
  | Rop (r1,r2,r3,i) -> "("^(reg_to_str r1)^","^(reg_to_str r2)^","^
    (reg_to_str r3)^","^(string_of_big_int i)^")"
;;

let iop_to_str (i:ioperand) =
  match i with
  | Iop (r1,r2,i) -> "("^(reg_to_str r1)^","^(reg_to_str r2)^","^
    (string_of_big_int i)^")"
;;

let jop_to_str (j:joperand) = "("^(string_of_big_int j)^")"
;;

let instr_to_str (i:instr) =
  match i with
| ADD roperand -> "ADD"^(rop_to_str roperand)
| ADDI ioperand -> "ADDI"^(iop_to_str ioperand)
| ADDIU ioperand -> "ADDIU"^(iop_to_str ioperand)
| ADDU roperand -> "ADDU"^(rop_to_str roperand)
| AND roperand -> "AND"^(rop_to_str roperand)
| ANDI ioperand -> "ANDI"^(iop_to_str ioperand)
| BEQ ioperand -> "BEQ"^(iop_to_str ioperand)
| BGEZ ioperand -> "BGEZ"^(iop_to_str ioperand)
| BGEZAL ioperand -> "BGEZAL"^(iop_to_str ioperand)
| BGTZ ioperand -> "BGTZ"^(iop_to_str ioperand)
| BLEZ ioperand -> "BLEZ"^(iop_to_str ioperand)
| BLTZ ioperand -> "BLTZ"^(iop_to_str ioperand)
| BLTZAL ioperand -> "BLTZAL"^(iop_to_str ioperand)
| BNE ioperand -> "BNE"^(iop_to_str ioperand)
| DIV roperand -> "DIV"^(rop_to_str roperand)
| DIVU roperand -> "DIVU"^(rop_to_str roperand)
| J joperand -> "J"^(jop_to_str joperand)
| JAL joperand -> "JAL"^(jop_to_str joperand)
| JALR roperand -> "JALR"^(rop_to_str roperand)
| JR roperand -> "JR"^(rop_to_str roperand)
| LB ioperand -> "LB"^(iop_to_str ioperand)
| LBU ioperand -> "LBU"^(iop_to_str ioperand)
| LH ioperand -> "LH"^(iop_to_str ioperand)
| LHU ioperand -> "LHU"^(iop_to_str ioperand)
| LUI ioperand -> "LUI"^(iop_to_str ioperand)
| LW ioperand -> "LW"^(iop_to_str ioperand)
| MFHI roperand -> "MFHI"^(rop_to_str roperand)
| MFLO roperand -> "MFLO"^(rop_to_str roperand)
| MUL roperand -> "MUL"^(rop_to_str roperand)
| MULT roperand -> "MULT"^(rop_to_str roperand)
| MULTU roperand -> "MULTU"^(rop_to_str roperand)
| NOR roperand -> "NOR"^(rop_to_str roperand)
| OR roperand -> "OR"^(rop_to_str roperand)
| ORI ioperand -> "ORI"^(iop_to_str ioperand)
| SB ioperand -> "SB"^(iop_to_str ioperand)
| SEB roperand -> "SEB"^(rop_to_str roperand)
| SEH roperand -> "SEH"^(rop_to_str roperand)
| SH ioperand -> "SH"^(iop_to_str ioperand)
| SLL roperand -> "SLL"^(rop_to_str roperand)
| SLLV roperand -> "SLLV"^(rop_to_str roperand)
| SLT roperand -> "SLT"^(rop_to_str roperand)
| SLTI ioperand -> "SLTI"^(iop_to_str ioperand)
| SLTIU ioperand -> "SLTIU"^(iop_to_str ioperand)
| SLTU roperand -> "SLTU"^(rop_to_str roperand)
| SRA roperand -> "SRA"^(rop_to_str roperand)
| SRAV roperand -> "SRAV"^(rop_to_str roperand)
| SRL roperand -> "SRL"^(rop_to_str roperand)
| SRLV roperand -> "SRLV"^(rop_to_str roperand)
| SUB roperand -> "SUB"^(rop_to_str roperand)
| SUBU roperand -> "SUBU"^(rop_to_str roperand)
| SW ioperand -> "SW"^(iop_to_str ioperand)
| XOR roperand -> "XOR"^ (rop_to_str roperand)
| XORI ioperand -> "XORI"^ (iop_to_str ioperand)

let rec rmap_to_stri rm (i:int) =
  if(i>31) then "" else(
  "R"^(string_of_int i)^":"^(string_of_big_int(rm (bii i)))^
  (if (i mod 10 = 0) then "\n" else ", ")^
  (rmap_to_stri rm (i + 1)))
;;
let rmap_to_str (rm: (register,int32) fmap) =
  rmap_to_stri rm 1;;

let mach_to_str (m:mach) =
  "PC: "^(string_of_big_int (pc_reg m))^"\n"^
  "REGS:\n"^(rmap_to_str (gp_regs m))^"\n"^
  "HIREG: "^(string_of_big_int (hi_reg m))^", "^
  "LOREG: "^(string_of_big_int (lo_reg m))^", "^
  "BDF: "^(string_of_big_int (bdelay_active_f m))^", "^
  "BDPC: "^(string_of_big_int (bdelay_pc_reg m))^"\n"

