(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

(* This file provides simple bit-level parsing combinators for disassembling
 * MIPS 32-bit binaries. *)
Require Import Coq.Init.Logic.
Require Import Bool.
Require Import List.
Require Import String.
Require Import Ascii.
Require Import ZArith.
Require Import Eqdep.

Require Import Shared.Coqlib.
Require Import Shared.Maps.

Unset Automatic Introduction.
Set Implicit Arguments.
Local Open Scope Z_scope.


(* Module MIPS_PARSER. *)
(*   Module MIPS_BASE_PARSER := Parser.Parser(MIPS_PARSER_ARG). *)
  (* Import MIPS_BASE_PARSER. *)

  Require Import MIPSSyntax.
  Require Import Shared.Bits.

  Require Import MIPSModel.ParserArg.
  Require Import MIPSModel.Parser.
  Import MIPS_PARSER_ARG.

  Definition int_t := User_t Int_t.
  Definition register_t := User_t Register_t.
  Definition instruction_t := User_t Instruction_t.
  Definition shamt5_t := User_t Shamt5_t.
  Definition imm16_t := User_t Imm16_t.
  Definition target26_t := User_t Target26_t.

  (* combinators for building parsers *)
  Definition bit(x:bool) : grammar Char_t := Char x.
  Definition never t : grammar t := Zero t.
  Definition always t (x:interp t) : grammar t := @Map Unit_t t (fun (_:unit) => x) Eps.
  Definition alt t (p1 p2:grammar t) : grammar t := 
    Map _ (fun (x:interp (Sum_t t t)) => match x with inl a => a | inr b => b end) 
        (Alt p1 p2).

  Fixpoint alts0 t (ps:list (grammar t)) : grammar t := 
    match ps with 
      | nil => @never t
      | p::nil => p
      | p::rest => alt p (alts0 rest)
    end.

  Fixpoint half A (xs ys zs: list A) : (list A) * (list A) := 
    match xs with 
      | nil => (ys,zs) 
      | h::t => half t zs (h::ys)
    end.

  Fixpoint alts' n t (ps:list (grammar t)) : grammar t := 
    match n, ps with 
      | 0%nat, _ => alts0 ps
      | S n, nil => @never t
      | S n, p::nil => p
      | S n, ps => 
        let (ps1,ps2) := half ps nil nil in 
          let g1 := alts' n ps1 in 
            let g2 := alts' n ps2 in 
              alt g1 g2
    end.

  Definition alts t (ps:list (grammar t)) : grammar t := alts' 20 ps.
  Definition map t1 t2 (p:grammar t1) (f:interp t1 -> interp t2) : grammar t2 := 
    @Map t1 t2 f p.
  Implicit Arguments map [t1 t2].
  Definition seq t1 t2 (p1:grammar t1) (p2:grammar t2) : grammar (Pair_t t1 t2) := Cat p1 p2.
  Definition cons t (pair : interp (Pair_t t (List_t t))) : interp (List_t t) := 
    (fst pair)::(snd pair).
  Definition seqs t (ps:list (grammar t)) : grammar (List_t t) := 
    List.fold_right (fun p1 p2 => map (seq p1 p2) (@cons t)) 
      (@always (List_t t) (@nil (interp t))) ps.

  (*Useful bit and string manipulators*)
  Fixpoint string_to_bool_list (s:string) : list bool := 
    match s with
      | EmptyString => nil
      | String a s => 
        (if ascii_dec a "0"%char then false else true)::(string_to_bool_list s)
    end.

  Fixpoint bits_n (n:nat) : type := 
    match n with 
      | 0%nat => Unit_t
      | S n => Pair_t Char_t (bits_n n)
    end.
  Fixpoint field'(n:nat) : grammar (bits_n n) := 
    match n with 
      | 0%nat => Eps
      | S n => Cat Any (field' n)
    end.
  Fixpoint bits2Z(n:nat)(a:Z) : interp (bits_n n) -> interp int_t := 
    match n with 
      | 0%nat => fun _ => a
      | S n => fun p => bits2Z n (2*a + (if (fst p) then 1 else 0)) (snd p)
    end.
  Definition bits2int(n:nat)(bs:interp (bits_n n)) : interp int_t := bits2Z n 0 bs.
  Fixpoint bits (x:string) : grammar (bits_n (String.length x)) := 
    match x with 
      | EmptyString => Eps
      | String c s => 
        (Cat (Char (if ascii_dec c "0"%char then false else true)) (bits s))
    end.
  Fixpoint string2int' (s:string) (a:Z) : Z :=
    match s with
      | EmptyString => a
      | String c s' => string2int' s' (2*a+ (if (ascii_dec c "0"%char) then 0 else 1))
    end
    .
  Definition string2int (s:string) : Z :=
    string2int' s 0.

  (* notation for building parsers *)
  Infix "|+|" := alt (right associativity, at level 80).
  Infix "$" := seq (right associativity, at level 70).
  Infix "@" := map (right associativity, at level 75).
  Notation "e %% t" := (e : interp t) (at level 80).
  Definition bitsleft t (s:string)(p:grammar t) : grammar t := 
    bits s $ p @ (@snd _ _).
  Infix "$$" := bitsleft (right associativity, at level 70).

  Definition anybit : grammar Char_t := Any.
  Definition field(n:nat) := (field' n) @ (bits2int n).
  Definition reg := (field 5) @ ((fun z => Reg (Word.repr z)) : _ -> interp register_t).
  Definition imm_p := (field 16) @ (@Word.repr 15 : _ -> interp imm16_t).
  Definition target_p := (field 26) @ (@Word.repr 25 : _ -> interp target26_t).
  Definition shamt_p := (field 5) @ (@Word.repr 4 : _ -> interp shamt5_t).

  Definition bitsmatch (s:string): grammar Unit_t := 
    (bits s) @ (fun _ => tt: interp Unit_t ).
  Notation "! s" := (bitsmatch s) (at level 60).
 
  Definition creg_p (s:string) : grammar register_t :=
    ((bits s)@(fun _ => Reg (Word.repr (string2int s)) %% register_t)).
  Definition reg0_p : grammar register_t :=
    creg_p "00000".
  Definition cshamt_p (s:string) : grammar shamt5_t :=
    let sfval := @Word.repr 4 (string2int s) in
    ((bits s)@(fun _ => sfval %% shamt5_t)).
  Definition shamt0_p : grammar shamt5_t :=
    cshamt_p "00000".
  Definition cfcode_p (s:string) : grammar Unit_t :=
    ((bits s)@(fun _ => tt %%Unit_t)).

  (*Generic Instruction Format Parsers*)
  Definition i_p_gen (opcode: string) (rs_p : grammar register_t) (rt_p : grammar register_t) 
    (immf_p : grammar imm16_t) (InstCon : ioperand -> instr):=
    opcode $$ rs_p $ rt_p $ immf_p @
    (fun p =>
      match p with
        | (r1,(r2,immval)) => InstCon (Iop r1 r2 immval)
      end %% instruction_t).
  Definition i_p (opcode: string) (InstCon : ioperand -> instr) : grammar instruction_t :=
    i_p_gen opcode reg reg imm_p InstCon.
  Definition j_p_gen (opcode: string) (targetf_p : grammar target26_t) (InstCon : joperand -> instr) 
    : grammar instruction_t :=
    opcode $$ targetf_p @
    (fun tval => InstCon (Jop tval) %% instruction_t).
  Definition j_p (opcode: string) (InstCon: joperand -> instr) : grammar instruction_t :=
    j_p_gen opcode target_p InstCon.
  Definition r_p_gen (opcode: string) (rs_p: grammar register_t) (rt_p: grammar register_t)
    (rd_p: grammar register_t) (shamtf_p: grammar shamt5_t) (fcode_p: grammar Unit_t) (InstCon: roperand ->instr):=
    opcode $$ rs_p $ rt_p $ rd_p $ shamtf_p $ fcode_p @
    (fun p =>
      match p with
        | (r1,(r2,(r3,(shval,_)))) => InstCon (Rop r1 r2 r3 shval) %% instruction_t
      end).
  Definition r_p (opcode: string) (fcode: string) (InstCon: roperand -> instr) : grammar instruction_t :=
    r_p_gen opcode reg reg reg shamt_p ((bits fcode)@(fun _ => tt %%Unit_t)) InstCon. 
  Definition shift_p (fcode: string) (InstCon: roperand -> instr) : grammar instruction_t :=
    r_p_gen "000000" reg0_p reg reg shamt_p (cfcode_p fcode) InstCon.

  (* a generic parser for parsing instructions that accept three register *)
  Definition reg3_p (opcode: string) (fcode: string) (InstCon: reg3_operand -> instr)
    : grammar instruction_t :=
    opcode $$ reg $ reg $ reg $ "00000" $$ bits fcode @
    (fun p =>
      match p with
        | (r1,(r2,(r3,_))) => InstCon (Reg3_op r1 r2 r3) %% instruction_t
      end).

  (* Definition r_p_zsf (opcode: string) (fcode: string) (InstCon: roperand -> instr) *)
  (*   : grammar instruction_t := *)
  (*   r_p_gen opcode reg reg reg shamt0_p (cfcode_p fcode) InstCon. *)


  (*Specific Instruction Parsers*)
  Definition ADD_p := reg3_p "000000" "100000" ADD.
  Definition ADDI_p := i_p "001000" ADDI.
  Definition ADDIU_p := i_p "001001" ADDIU.
  Definition ADDU_p := reg3_p "000000" "100001" ADDU.
  Definition AND_p := reg3_p "000000" "100100" AND.
  Definition ANDI_p := i_p "001100" ANDI.
  Definition BEQ_p := i_p "000100" BEQ.

  Definition bz_p_gen (opcode1: string) (rs_p: grammar register_t) (opcode2: string)
    (immf_p : grammar imm16_t) (InstCon : bz_operand -> instr):=
    opcode1 $$ rs_p $ opcode2 $$ immf_p @
    (fun p =>
      match p with
        | (r1,immval) => InstCon (BZ_op r1 immval)
      end %% instruction_t).

  Definition BGEZ_p := bz_p_gen "000001" reg "00001" imm_p BGEZ.
  Definition BGEZAL_p := bz_p_gen "000001" reg "10001" imm_p BGEZAL.
  Definition BGTZ_p := bz_p_gen "000111" reg "00000" imm_p BGTZ.
  Definition BLEZ_p := bz_p_gen "000110" reg "00000" imm_p BLEZ.
  Definition BLTZ_p := bz_p_gen "000001" reg "00000" imm_p BLTZ.
  Definition BLTZAL_p := bz_p_gen "000001" reg "10000" imm_p BLTZAL.

  Definition BNE_p := i_p "000101" BNE.
  Definition DIV_p := r_p_gen "000000" reg reg reg0_p shamt0_p (cfcode_p "011010") DIV.
  Definition DIVU_p := r_p_gen "000000" reg reg reg0_p shamt0_p (cfcode_p "011011") DIVU.
  Definition J_p := j_p "000010" J.
  Definition JAL_p := j_p "000011" JAL.
  Definition JALR_p := r_p_gen "000000" reg reg0_p reg shamt_p (cfcode_p "001001") JALR.
  Definition JR_p := r_p_gen "000000" reg reg0_p reg0_p shamt_p (cfcode_p "001000") JR.
  Definition LB_p := i_p "100000" LB.
  Definition LBU_p := i_p "100100" LBU.
  Definition LH_p := i_p "100001" LH.
  Definition LHU_p := i_p "100101" LHU.
  Definition LUI_p := i_p "001111" LUI.
  Definition LW_p := i_p "100101" LHU.
  Definition MFHI_p := r_p_gen "000000" reg0_p reg0_p reg shamt0_p (cfcode_p "010000") MFHI.
  Definition MFLO_p := r_p_gen "000000" reg0_p reg0_p reg shamt0_p (cfcode_p "010010") MFLO.
  Definition MUL_p := reg3_p "000000" "000010" MUL.
  Definition MULT_p := r_p_gen "000000" reg reg reg0_p shamt0_p (cfcode_p "011000") MULT.
  Definition MULTU_p := r_p_gen "000000" reg reg reg0_p shamt0_p (cfcode_p "011001") MULTU.
  Definition NOR_p := reg3_p "000000" "100111" NOR.
  Definition OR_p := reg3_p "000000" "100101" OR.
  Definition ORI_p := i_p "001101" ORI.
  Definition SB_p := i_p "101000" SB.
  Definition SEB_p := r_p_gen "011111" reg0_p reg reg (cshamt_p "10000") (cfcode_p "100000") SEB.
  Definition SEH_p := r_p_gen "011111" reg0_p reg reg (cshamt_p "11000") (cfcode_p "100000") SEH.
  Definition SH_p := i_p "101001" SH.
  Definition SLL_p := shift_p "000000" SLL.
  Definition SLLV_p := reg3_p "000000" "000100" SLLV.
  Definition SLT_p := reg3_p "000000" "101010" SLT.
  Definition SLTI_p := i_p "001010" SLTI.
  Definition SLTU_p := reg3_p "000000" "101011" SLTU.
  Definition SLTIU_p := i_p "001011" SLTIU.
  Definition SRA_p := shift_p "000011" SRA.
  Definition SRAV_p := reg3_p "000000" "000111" SRAV.
  Definition SRL_p := shift_p "000010" SRL.
  Definition SRLV_p := reg3_p "000000" "000110" SRLV.
  Definition SUB_p := reg3_p "000000" "100010" SUB.
  Definition SUBU_p := reg3_p "000000" "100011" SUBU.
  Definition SW_p := i_p "101011" SW.
  Definition XOR_p := reg3_p "000000" "100110" XOR.
  Definition XORI_p := i_p "001110" XORI.

  
  (*Large grammar list*)
  Definition instr_grammar_list : list (grammar instruction_t) := 
    ADD_p :: ADDI_p :: ADDIU_p :: ADDU_p ::
    AND_p :: ANDI_p :: BEQ_p :: BGEZ_p :: BGEZAL_p ::
    BGTZ_p :: BLEZ_p :: BLTZ_p :: BLTZAL_p ::
    BNE_p :: DIV_p :: DIVU_p :: J_p :: JAL_p :: JALR_p :: JR_p :: LB_p ::
    LBU_p :: LH_p :: LHU_p :: LUI_p :: LW_p :: MFHI_p :: MFLO_p ::
    MUL_p :: MULT_p :: MULTU_p :: NOR_p :: OR_p ::
    ORI_p :: SB_p :: SEB_p :: SEH_p :: SH_p :: SLL_p :: 
    SLLV_p :: SLT_p :: SLTI_p :: SLTU_p :: SLTIU_p :: SRA_p ::
    SRL_p :: SRLV_p :: SUB_p :: SUBU_p :: SW_p :: XOR_p :: XORI_p ::
    nil.

  Definition instr_grammar : grammar instruction_t :=
    alts instr_grammar_list.
  Definition instr_regexp := projT1 (split_grammar instr_grammar).

  Definition parse_string (s: string) : list instr :=
    let cs := string_to_bool_list s in
    naive_parse instr_grammar cs.

  Definition test1 := 
    match (parse_string "00001000000000000000000000000000") with
      | (J jop)::tl => 1
      | _ => 0
    end.
  (* Eval compute in test1. *)

  Definition word_explode (b:int32) : list bool :=
  let bs := Word.bits_of_Z 32 (Word.unsigned b) in
    (fix f (n:nat) : list bool := 
      match n with
      | S n' => (bs (Z_of_nat n'))::(f n')
      | O => nil
      end
    ) 32%nat.

  Definition parse_word (w:int32) : list instr :=
    let cs := word_explode w in
    naive_parse instr_grammar cs.
  
(* End MIPS_PARSER. *)
