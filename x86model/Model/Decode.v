(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

(* This file provides simple bit-level parsing combinators for disassembling
 * Intel IA32 (x86) 32-bit binaries. *)
Require Coqlib.
Require Import Coq.Init.Logic.
Require Import Bool.
Require Import List.
Require Import String.
Require Import Maps.
Require Import Ascii.
Require Import ZArith.
Require Import Eqdep.
Require Import Parser.
Unset Automatic Introduction.
Set Implicit Arguments.
Local Open Scope Z_scope.


Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.


(* a module for generating the parser for x86 instructions *)
Module X86_PARSER_ARG.
  Require Import X86Syntax.
  Require Import Bits.
  
  Definition char_p : Set := bool.
  Definition char_eq : forall (c1 c2:char_p), {c1=c2}+{c1<>c2} := bool_dec.
  Inductive type : Set := 
  | Int_t : type
  | Register_t : type
  | Byte_t : type
  | Half_t : type
  | Word_t : type
  | Scale_t : type
  | Condition_t : type
  | Operand_t : type
  | Instruction_t : type
  | Control_Register_t : type
  | Debug_Register_t : type
  | Segment_Register_t : type
  | Lock_or_Rep_t : type
  | Bool_t : type
  | Prefix_t : type
  | Option_t (t: type) : type
  (* Need pairs at this level if I want to have options of pairs*)
  | Pair_t (t1 t2: type) : type. 

  Definition tipe := type.
  Definition tipe_eq : forall (t1 t2:tipe), {t1=t2} + {t1<>t2}.
    intros ; decide equality.
  Defined.

  Fixpoint tipe_m (t:tipe) := 
    match t with 
      | Int_t => Z
      | Register_t => register
      | Byte_t => int8
      | Half_t => int16
      | Word_t => int32
      | Scale_t => scale
      | Condition_t => condition_type
      | Operand_t => operand
      | Instruction_t => instr
      | Control_Register_t => control_register
      | Debug_Register_t => debug_register
      | Segment_Register_t => segment_register
      | Lock_or_Rep_t => lock_or_rep
      | Bool_t => bool
      | Prefix_t => prefix
      | Option_t t => option (tipe_m t)
      | Pair_t t1 t2 => ((tipe_m t1) * (tipe_m t2))%type
    end.
End X86_PARSER_ARG.

Module X86_PARSER.
  Module X86_BASE_PARSER := Parser.Parser(X86_PARSER_ARG).
  Require Import X86Syntax.
  Require Import Bits.
  Import X86_PARSER_ARG.
  Import X86_BASE_PARSER.

  Definition option_t x := tipe_t (Option_t x).
  Definition int_t := tipe_t Int_t.
  Definition register_t := tipe_t Register_t.
  Definition byte_t := tipe_t Byte_t.
  Definition half_t := tipe_t Half_t.
  Definition word_t := tipe_t Word_t.
  Definition scale_t := tipe_t Scale_t.
  Definition condition_t := tipe_t Condition_t.
  Definition operand_t := tipe_t Operand_t.
  Definition instruction_t := tipe_t Instruction_t.
  Definition control_register_t := tipe_t Control_Register_t.
  Definition debug_register_t := tipe_t Debug_Register_t.
  Definition segment_register_t := tipe_t Segment_Register_t.
  Definition lock_or_rep_t := tipe_t Lock_or_Rep_t.
  Definition bool_t := tipe_t Bool_t.
  Definition prefix_t := tipe_t Prefix_t.
  (* combinators for building parsers *)
  Definition bit(x:bool) : parser char_t := Char_p x.
  Definition never t : parser t := Zero_p t.
  Definition always t (x:result_m t) : parser t := @Map_p unit_t t (fun (_:unit) => x) Eps_p.
  Definition alt t (p1 p2:parser t) : parser t := Alt_p p1 p2.
  Definition alts t (ps: list (parser t)) : parser t := List.fold_right (@alt t) (@never t) ps.
  Definition map t1 t2 (p:parser t1) (f:result_m t1 -> result_m t2) : parser t2 := 
    @Map_p t1 t2 f p.
  Implicit Arguments map [t1 t2].
  Definition seq t1 t2 (p1:parser t1) (p2:parser t2) : parser (pair_t t1 t2) := Cat_p p1 p2.
  Definition cons t (pair : result_m (pair_t t (list_t t))) : result_m (list_t t) := 
    (fst pair)::(snd pair).
  Definition seqs t (ps:list (parser t)) : parser (list_t t) := 
    List.fold_right (fun p1 p2 => map (seq p1 p2) (@cons t)) 
      (@always (list_t t) (@nil (result_m t))) ps.
  Fixpoint string_to_bool_list (s:string) : list bool := 
    match s with
      | EmptyString => nil
      | String a s => 
        (if ascii_dec a "0"%char then false else true)::(string_to_bool_list s)
    end.

  Fixpoint bits_n (n:nat) : result := 
    match n with 
      | 0%nat => unit_t
      | S n => pair_t char_t (bits_n n)
    end.
  Fixpoint field'(n:nat) : parser (bits_n n) := 
    match n with 
      | 0%nat => Eps_p
      | S n => Cat_p Any_p (field' n)
    end.
  Fixpoint bits2Z(n:nat)(a:Z) : result_m (bits_n n) -> result_m int_t := 
    match n with 
      | 0%nat => fun _ => a
      | S n => fun p => bits2Z n (2*a + (if (fst p) then 1 else 0)) (snd p)
    end.
  Definition bits2int(n:nat)(bs:result_m (bits_n n)) : result_m int_t := bits2Z n 0 bs.
  Fixpoint bits (x:string) : parser (bits_n (String.length x)) := 
    match x with 
      | EmptyString => Eps_p
      | String c s => 
        (Cat_p (Char_p (if ascii_dec c "0"%char then false else true)) (bits s))
    end.

  (* notation for building parsers *)
  Infix "|+|" := alt (right associativity, at level 80).
  Infix "$" := seq (right associativity, at level 70).
  Infix "@" := map (right associativity, at level 75).
  Notation "e %% t" := (e : result_m t) (at level 80).
  Definition bitsleft t (s:string)(p:parser t) : parser t := 
    bits s $ p @ (@snd _ _).
  Infix "$$" := bitsleft (right associativity, at level 70).

  Definition anybit : parser char_t := Any_p.
  Definition field(n:nat) := (field' n) @ (bits2int n).
  Definition reg := (field 3) @ (Z_to_register : _ -> result_m register_t).
  Definition byte := (field 8) @ (@Word.repr 7 : _ -> result_m byte_t).
 (* Definition halfword := (field 16) @ (@Word.repr 15 : _ -> result_m half_t).
  Definition word := (field 32) @ (@Word.repr 31 : _ -> result_m word_t). *)
  Definition halfword := (byte $ byte) @ ((fun p =>
      let b0 := Word.repr (Word.unsigned (fst p)) in
      let b1 := Word.repr (Word.unsigned (snd p)) in
        Word.or (Word.shl b1 (Word.repr 8)) b0): _ -> result_m half_t).
  Definition word := (byte $ byte $ byte $ byte) @
    ((fun p => 
        let b0 := zero_extend8_32 (fst p) in
        let b1 := zero_extend8_32 (fst (snd p)) in
        let b2 := zero_extend8_32 (fst (snd (snd p))) in
        let b3 := zero_extend8_32 (snd (snd (snd p))) in
         let w1 := Word.shl b1 (Word.repr 8) in
         let w2 := Word.shl b2 (Word.repr 16) in
         let w3 := Word.shl b3 (Word.repr 24) in
          Word.or w3 (Word.or w2 (Word.or w1 b0)))
    : _ -> result_m word_t).

  Definition scale_p := (field 2) @ (Z_to_scale : _ -> result_m scale_t).
  Definition tttn := (field 4) @ (Z_to_condition_type : _ -> result_m condition_t).

  (* This is used in a strange edge-case for modrm parsing. See the
     footnotes on p37 of the manual in the repo This is a case where I
     think intersections/complements would be nice operators *)

  (* JGM: we can handle this in the semantic action instead of the parser, 
     so I replaced si, which used this and another pattern for [bits "100"]
     to the simpler case below -- helps to avoid some explosions in the 
     definitions. *)
  Definition reg_no_esp : parser register_t :=
     (bits "000" |+| bits "001" |+| bits "010" |+|
     bits "011" |+| (* bits "100" <- this is esp *)  bits "101" |+|
     bits "110" |+| bits "111") @ 
       ((fun bs => Z_to_register (bits2int 3 bs)) : _ -> result_m register_t).

  Definition reg_no_ebp : parser register_t :=
     (bits "000" |+| bits "001" |+| bits "010" |+|
     bits "011" |+|  bits "100"  (* |+| bits "101" <- this is ebp *) |+|
     bits "110" |+| bits "111") @ 
       ((fun bs => Z_to_register (bits2int 3 bs)) : _ -> result_m register_t).

  Definition si := 
    (scale_p $ reg) @ (fun p => match snd p with 
                                  | ESP => None
                                  | _ => Some p
                                end %% option_t (Pair_t Scale_t Register_t)).

  Definition sib := si $ reg.
      
  (* These next 4 parsers are used in the definition of the mod/rm parser *)
  Definition rm00 : parser operand_t := 
    (     bits "000" 
      |+| bits "001" 
      |+| bits "010" 
      |+| bits "011" 
      |+| bits "110"
      |+| bits "111" ) @ 
          (fun bs => Address_op (mkAddress (Word.repr 0) 
            (Some (Z_to_register(bits2int 3 bs))) None) %% operand_t)
      |+| bits "100" $ si $ reg_no_ebp @ 
          (fun p => match p with
                      | (_,(si,base)) => 
                        Address_op (mkAddress (Word.repr 0) 
                          (Some base) si)
                    end : result_m operand_t)     
      |+| bits "100" $ si $ bits "101" $ word @
          (fun p => match p with
                      | (_,(si,(_, disp))) => 
                        Address_op (mkAddress disp
                          (None) si)
                    end : result_m operand_t)
      |+| bits "101" $ word @
          (fun p => match p with 
                      | (_, disp) => 
                        Address_op (mkAddress disp None None)
                    end %% operand_t).  

  Definition rm01 : parser operand_t := 
    ((    bits "000" 
      |+| bits "001" 
      |+| bits "010" 
      |+| bits "011"
      |+| bits "101" 
      |+| bits "110"
      |+| bits "111") $ byte) @ 
          (fun p => 
            match p with 
              | (bs, disp) =>
                Address_op (mkAddress (sign_extend8_32 disp) 
                  (Some (Z_to_register(bits2int 3 bs))) None)
            end %% operand_t)
      |+| bits "100" $ sib $ byte @ 
          (fun p => 
            match p with
              | (_,((si,base),disp)) => 
                Address_op (mkAddress (sign_extend8_32 disp) (Some base)
                  (si))
            end %% operand_t).

  Definition rm10 : parser operand_t := 
    ((    bits "000" 
      |+| bits "001" 
      |+| bits "010" 
      |+| bits "011"
      |+| bits "101" 
      |+| bits "110"
      |+| bits "111") $ word) @ 
          (fun p => 
            match p with 
              | (bs, disp) =>
                Address_op (mkAddress disp (Some (Z_to_register(bits2int 3 bs))) None)
            end %% operand_t)
      |+|  bits "100" $ sib $ word @ 
          (fun p => 
            match p with
              | (_,((si,base),disp)) => 
                Address_op (mkAddress disp (Some base) si)
            end %% operand_t).
  
  Definition rm11 : parser operand_t := reg @ (fun x => Reg_op x : result_m operand_t).

  Definition modrm : parser (pair_t operand_t operand_t) := 
    (     (bits "00" $ reg $ rm00)
      |+| (bits "01" $ reg $ rm01)
      |+| (bits "10" $ reg $ rm10)
      |+| (bits "11" $ reg $ rm11) ) @ 
          (fun p => match p with 
                      | (_, (r, op)) => (Reg_op r, op)
                    end %% (pair_t operand_t operand_t)).

  (* same as modrm but disallows the register case *)
  Definition modrm_noreg :=
  (     ("00" $$ reg $ rm00)
    |+| ("01" $$ reg $ rm01)
    |+| ("10" $$ reg $ rm10)).

  (* Similar to mod/rm parser except that the register field is fixed to a
   * particular bit-pattern, and the pattern starting with "11" is excluded. *)
  Definition ext_op_modrm(bs:string) : parser operand_t := 
    (      (bits "00" $ bits bs $ rm00)
     |+|   (bits "01" $ bits bs $ rm01)
     |+|   (bits "10" $ bits bs $ rm10) ) @
           (fun p => match p with 
                       | (_,(_,op)) => op
                     end %% operand_t).

  Definition ext_op_modrm2(bs:string) : parser operand_t :=
    (      (bits "00" $ bits bs $ rm00)
     |+|   (bits "01" $ bits bs $ rm01)
     |+|   (bits "10" $ bits bs $ rm10)
     |+|   (bits "11" $ bits bs $ rm11) ) @
           (fun p => match p with 
                       | (_,(_,op)) => op
                     end %% operand_t).

  (* Parsers for the individual instructions *)
  Definition AAA_p := bits "00110111" @ (fun _ => AAA %% instruction_t).
  Definition AAD_p := bits "1101010100001010" @ (fun _ => AAD %% instruction_t).
  Definition AAM_p := bits "1101010000001010" @ (fun _ => AAM %% instruction_t).
  Definition AAS_p := bits "00111111" @ (fun _ => AAS %% instruction_t).

  (* The parsing for ADC, ADD, AND, CMP, OR, SBB, SUB, and XOR can be shared *)

  Definition imm_op (opsize_override: bool) : parser operand_t :=
    match opsize_override with
      | false => word @ (fun w => Imm_op w %% operand_t)
      | true => halfword @ (fun w => Imm_op (sign_extend16_32 w) %% operand_t)
    end.
      
  Definition logic_or_arith_p (opsize_override: bool)
    (op1 : string) (* first 5 bits for most cases *)
    (op2 : string) (* when first 5 bits are 10000, the next byte has 3 bits
                      that determine the opcode *)
    (InstCon : bool->operand->operand->instr) (* instruction constructor *)
    : parser instruction_t
    :=
  (* register/memory to register and vice versa -- the d bit specifies
   * the direction. *)
  op1 $$ "0" $$ anybit $ anybit $ modrm @
    (fun p => match p with 
                | (d, (w, (op1, op2))) => 
                  if d then InstCon w op1 op2 else InstCon w op2 op1
              end %% instruction_t)
  |+|
  (* sign extend immediate byte to register *)
  "1000" $$ "0011" $$ "11" $$ op2 $$ reg $ byte @ 
    (fun p => 
      let (r,imm) := p in InstCon true (Reg_op r) (Imm_op (sign_extend8_32 imm)) %%
    instruction_t)
  |+|
  (* zero-extend immediate byte to register *)
  "1000" $$ "0000" $$ "11" $$ op2 $$ reg $ byte @ 
    (fun p => 
      let (r,imm) := p in InstCon false (Reg_op r) (Imm_op (zero_extend8_32 imm)) %%
    instruction_t)
  |+|
  (* immediate word to register *)
  "1000" $$ "0001" $$ "11" $$ op2 $$ reg $ imm_op opsize_override @ 
    (fun p => let (r,imm) := p in InstCon true (Reg_op r) imm %% instruction_t)
  |+|
  (* zero-extend immediate byte to EAX *)
  op1 $$ "100" $$ byte @
    (fun imm => InstCon false (Reg_op EAX) (Imm_op (zero_extend8_32 imm)) %% instruction_t)
  |+|
  (* word to EAX *)
  op1 $$ "101" $$ imm_op opsize_override @
    (fun imm => InstCon true (Reg_op EAX)  imm %% instruction_t)
  |+|
  (* zero-extend immediate byte to memory *)
  "1000" $$ "0000" $$ ext_op_modrm op2 $ byte @ 
    (fun p => let (op,imm) := p in InstCon false op (Imm_op (zero_extend8_32 imm)) %% 
    instruction_t)
  |+|
  (* sign-extend immediate byte to memory *)
  "1000" $$ "0011" $$ ext_op_modrm op2 $ byte @ 
    (fun p => let (op,imm) := p in InstCon true op (Imm_op (sign_extend8_32 imm)) %%
    instruction_t)
  |+|
  (* immediate word to memory *)
  "1000" $$ "0001" $$ ext_op_modrm op2 $ imm_op opsize_override @ 
    (fun p => let (op,imm) := p in InstCon true op imm %% instruction_t).

  Definition ADC_p s := logic_or_arith_p s "00010" "010" ADC.
  Definition ADD_p s := logic_or_arith_p s "00000" "000" ADD.
  Definition AND_p s := logic_or_arith_p s "00100" "100" AND.
  Definition CMP_p s := logic_or_arith_p s "00111" "111" CMP.
  Definition OR_p  s := logic_or_arith_p s "00001" "001" OR.
  Definition SBB_p s := logic_or_arith_p s "00011" "011" SBB.
  Definition SUB_p s := logic_or_arith_p s "00101" "101" SUB.
  Definition XOR_p s := logic_or_arith_p s "00110" "110" XOR.

  Definition ARPL_p := 
  "0110" $$ "0011" $$ modrm @ 
    (fun p => let (op1,op2) := p in ARPL op1 op2 %% instruction_t).

  Definition BOUND_p := 
  "0110" $$ "0010" $$ modrm @ 
    (fun p => let (op1,op2) := p in BOUND op1 op2 %% instruction_t).

  Definition BSF_p := 
  "0000" $$ "1111" $$ "1011" $$ "1100" $$ modrm @ 
    (fun p => let (op1,op2) := p in BSF op1 op2 %% instruction_t).

  Definition BSR_p := 
  "0000" $$ "1111" $$ "1011" $$ "1101" $$ modrm @ 
    (fun p => let (op1,op2) := p in BSR op1 op2 %% instruction_t).

  Definition BSWAP_p := 
  "0000" $$ "1111" $$ "1100" $$ "1" $$ reg @ (fun x => BSWAP x %% instruction_t).

  (* The various bit-testing operations can also share a parser *)
  Definition bit_test_p (opcode1:string) (opcode2:string)
    (Instr : operand -> operand -> instr) := 
    "0000" $$ "1111" $$ "1011" $$ "1010" $$ "11" $$ opcode1 $$ reg $ byte @ 
    (fun p => 
      let (r,imm) := p in Instr (Reg_op r) (Imm_op (zero_extend8_32 imm)) %% instruction_t)
  |+| 
    "0000" $$ "1111" $$ "1011" $$ "1010" $$ ext_op_modrm opcode1 $ byte @
    (fun p => 
      let (op1,imm) := p in Instr op1 (Imm_op (zero_extend8_32 imm)) %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "101" $$ opcode2 $$ "011" $$ modrm @
    (fun p => let (op2,op1) := p in Instr op1 op2 %% instruction_t).

  Definition BT_p := bit_test_p "100" "00" BT.
  Definition BTC_p := bit_test_p "111" "11" BTC.
  Definition BTR_p := bit_test_p "110" "10" BTR.
  Definition BTS_p := bit_test_p "101" "01" BTS.

  Definition CALL_p := 
    "1110" $$ "1000" $$ word  @ 
    (fun w => CALL true false (Imm_op w) None %% instruction_t)
  |+|
    "1111" $$ "1111" $$ ext_op_modrm2 "010" @ 
    (fun op => CALL true true op None %% instruction_t)
  |+| 
    "1001" $$ "1010" $$ halfword $ word @ 
    (fun p => CALL false false (Imm_op (snd p)) (Some (fst p)) %% instruction_t)
  |+|
    "1111" $$ "1111" $$ ext_op_modrm2 "011" @ 
    (fun op => CALL false true op None %% instruction_t).

  Definition CDQ_p := "1001" $$ bits "1001" @ (fun _ => CDQ %% instruction_t).
  Definition CLC_p := "1111" $$ bits "1000" @ (fun _ => CLC %% instruction_t).
  Definition CLD_p := "1111" $$ bits "1100" @ (fun _ => CLD %% instruction_t).
  Definition CLI_p := "1111" $$ bits "1010" @ (fun _ => CLI %% instruction_t).
  Definition CLTS_p := "0000" $$ "1111" $$ "0000" $$ bits "0110" @ 
    (fun _ => CLTS %% instruction_t).
  Definition CMC_p := "1111" $$ bits "0101" @ (fun _ => CMC %% instruction_t).
  Definition CMPS_p := "1010" $$ "011" $$ anybit @ (fun x => CMPS x %% instruction_t).
  Definition CMPXCHG_p := 
   "0000" $$ "1111" $$ "1011" $$ "000" $$ anybit $ modrm @ 
    (fun p => match p with 
                | (w,(op1,op2)) => CMPXCHG w op2 op1
              end %% instruction_t).

  Definition CPUID_p := "0000" $$ "1111" $$ "1010" $$ bits "0010" @ 
    (fun _ => CPUID %% instruction_t).
  Definition CWDE_p := "1001" $$ bits "1000" @ (fun _ => CWDE %% instruction_t).
  Definition DAA_p := "0010" $$ bits "0111" @ (fun _ => DAA %% instruction_t).
  Definition DAS_p := "0010" $$ bits "1111" @ (fun _ => DAS %% instruction_t).

  Definition DEC_p := 
    "1111" $$ "111" $$ anybit $ "11001" $$ reg @ 
      (fun p => let (w,r) := p in DEC w (Reg_op r) %% instruction_t)
  |+|
    "0100" $$ "1" $$ reg @ 
      (fun r => DEC true (Reg_op r) %% instruction_t)
  |+| 
    "1111" $$ "111" $$ anybit $ ext_op_modrm "001" @
      (fun p => let (w,op1) := p in DEC w op1 %% instruction_t).

  Definition DIV_p := 
    "1111" $$ "011" $$ anybit $ "11110" $$ reg @ 
      (fun p => let (w,r) := p in DIV w (Reg_op r) %% instruction_t)
  |+| 
    "1111" $$ "011" $$ anybit $ ext_op_modrm "110" @ 
      (fun p => let (w,op1) := p in DIV w op1 %% instruction_t).

  Definition HLT_p := "1111" $$ bits "0100" @ (fun _ => HLT %% instruction_t).

  Definition IDIV_p := 
    "1111" $$ "011" $$ anybit $ "11111" $$ reg @ 
    (fun p => let (w,r) := p in IDIV w (Reg_op r) %% instruction_t)
  |+|
    "1111" $$ "011" $$ anybit $ ext_op_modrm "111" @ 
     (fun p => let (w,op1) := p in IDIV w op1 %% instruction_t).

  Definition IMUL_p opsize_override := 
    "1111" $$ "011" $$ anybit $ ext_op_modrm2 "101" @
    (fun p => let (w,op1) := p in IMUL w op1 None None %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "1010" $$ "1111" $$ modrm @
    (fun p => let (op1,op2) := p in IMUL true op1 (Some op2) None %% instruction_t)
  |+|
    "0110" $$ "1011" $$ modrm $ byte @
    (fun p => match p with 
                | ((op1,op2),imm) => 
                  IMUL true op1 (Some op2) (Some (sign_extend8_32 imm))
              end %% instruction_t)
  |+|
    match opsize_override with
      | false =>
          "0110" $$ "1001" $$ modrm $ word @
           (fun p => match p with 
                | ((op1,op2),imm) => 
                  IMUL true op1 (Some op2) (Some imm)
              end  %% instruction_t)
      | true => 
          "0110" $$ "1001" $$ modrm $ halfword @
           (fun p => match p with 
                | ((op1,op2),imm) => 
                  IMUL true op1 (Some op2) (Some (sign_extend16_32 imm))
              end  %% instruction_t)
    end.

  Definition IN_p := 
    "1110" $$ "010" $$ anybit $ byte @ 
    (fun p => let (w,pt) := p in IN w (Some pt) %% instruction_t)
  |+|
    "1110" $$ "110" $$ anybit @ (fun w => IN w None %% instruction_t).

  Definition INC_p := 
    "1111" $$ "111" $$ anybit  $ "11000" $$ reg @ 
      (fun p => let (w,r) := p in INC w (Reg_op r) %% instruction_t)
  |+|
    "0100" $$ "0" $$ reg @ (fun r => INC true (Reg_op r) %% instruction_t)
  |+|
    "1111" $$ "111" $$ anybit $ ext_op_modrm "000" @ 
       (fun p => let (w,op1) := p in INC w op1 %% instruction_t).

  Definition INS_p := "0110" $$ "110" $$ anybit @ (fun x => INS x %% instruction_t).

  Definition INTn_p := "1100" $$ "1101" $$ byte @ (fun x => INTn x %% instruction_t).
  Definition INT_p := "1100" $$ bits "1100" @ (fun _ => INT %% instruction_t).

  Definition INTO_p := "1100" $$ bits "1110" @ (fun _ => INTO %% instruction_t).
  Definition INVD_p := "0000" $$ "1111" $$ "0000" $$ bits "1000" @ 
    (fun _ => INVD %% instruction_t).

  Definition INVLPG_p := 
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm "111" @ 
    (fun x => INVLPG x %% instruction_t).

  Definition IRET_p := "1100" $$ bits "1111" @ (fun _ => IRET %% instruction_t).

  Definition Jcc_p := 
    "0111" $$ tttn $ byte @ 
    (fun p => let (ct,imm) := p in Jcc ct (sign_extend8_32 imm) %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "1000" $$ tttn $ word @ 
    (fun p => let (ct,imm) := p in Jcc ct imm %% instruction_t).

  Definition JCXZ_p := "1110" $$ "0011" $$ byte @ (fun x => JCXZ x %% instruction_t).

  Definition JMP_p := 
    "1110" $$ "1011" $$ byte @
    (fun b => JMP true false (Imm_op (sign_extend8_32 b)) None %% instruction_t)
  |+|
    "1110" $$ "1001" $$ word @ 
    (fun w => JMP true false (Imm_op w) None %% instruction_t)
  |+|
    "1111" $$ "1111" $$ ext_op_modrm2 "100" @ 
    (fun op => JMP true true op None %% instruction_t)
  |+|
    "1110" $$ "1010" $$ halfword $ word @ 
      (fun p => JMP false true (Imm_op (snd p)) (Some (fst p)) %% instruction_t)
  |+|
    "1111" $$ "1111" $$ ext_op_modrm2 "101" @ 
    (fun op => JMP false true op None %% instruction_t).

  Definition LAHF_p := "1001" $$ bits "1111" @ (fun _ => LAHF %% instruction_t).

  Definition LAR_p := 
    "0000" $$ "1111" $$ "0000" $$ "0010" $$ modrm @ 
      (fun p => LAR (fst p) (snd p) %% instruction_t).

  Definition LDS_p := "1100" $$ "0101" $$ modrm @ 
    (fun p => LDS (fst p) (snd p) %% instruction_t).
  Definition LEA_p := "1000" $$ "1101" $$ modrm_noreg @ 
    (fun p => LEA (Reg_op (fst p)) (snd p) %% instruction_t).
  Definition LEAVE_p := "1100" $$ bits "1001" @ 
    (fun _ => LEAVE %% instruction_t).
  Definition LES_p := "1100" $$ "0100" $$ modrm @ 
    (fun p => LES (fst p) (snd p) %% instruction_t).
  Definition LFS_p := "0000" $$ "1111" $$ "1011" $$ "0100" $$ modrm @ 
    (fun p => LFS (fst p) (snd p) %% instruction_t).
  Definition LGDT_p := "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm "010" @ 
    (fun x => LGDT x %% instruction_t).
  Definition LGS_p := "0000" $$ "1111" $$ "1011" $$ "0101" $$ modrm @ 
    (fun p => LGS (fst p) (snd p) %% instruction_t).
  Definition LIDT_p := "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm "011" @ 
    (fun x => LIDT x %% instruction_t).
  Definition LLDT_p := 
    "0000" $$ "1111" $$ "0000" $$ "0000" $$ "11" $$ "010" $$ reg @ 
    (fun r => LLDT (Reg_op r) %% instruction_t)
  |+| 
    "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "010" @ 
    (fun x => LLDT x %% instruction_t).

  Definition LMSW_p := 
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ "11" $$ "110" $$ reg @ 
      (fun r => LMSW (Reg_op r) %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ "11" $$ ext_op_modrm "110" @ 
      (fun x => LMSW x %% instruction_t).

  (* JGM: note, this isn't really an instruction, but rather a prefix.  So it
     shouldn't be included in the list of instruction parsers. *)
(*  Definition LOCK_p := "1111" $$ bits "0000" @ (fun _ => LOCK %% instruction_t). *)
  Definition LODS_p := "1010" $$ "110" $$ anybit @ (fun x => LODS x %% instruction_t).
  Definition LOOP_p := "1110" $$ "0010" $$ byte @ (fun x => LOOP x %% instruction_t).
  Definition LOOPZ_p := "1110" $$ "0001" $$ byte @ (fun x => LOOPZ x %% instruction_t).
  Definition LOOPNZ_p := "1110" $$ "0000" $$ byte @ (fun x => LOOPNZ x %% instruction_t).
  Definition LSL_p := "0000" $$ "1111" $$ "0000" $$ "0011" $$ modrm @ 
    (fun p => LSL (fst p) (snd p) %% instruction_t).
  Definition LSS_p := "0000" $$ "1111" $$ "1011" $$ "0010" $$ modrm @ 
    (fun p => LSS (fst p) (snd p) %% instruction_t).
  Definition LTR_p := "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "011" @ 
    (fun x => LTR x %% instruction_t).

  (* This is may not be right. Need to test this thoroughly. 
     There is no 8bit mode for CMOVcc *)

  Definition CMOVcc_p :=
    "0000" $$ "1111" $$ "0100" $$ tttn $ modrm @
    (fun p => match p with | (tttn, (op1, op2))=>CMOVcc tttn op1 op2 end %% instruction_t).

  Definition MOV_p opsize_override := 
    "1000" $$ "101" $$ anybit $ modrm @ 
      (fun p => match p with | (w,(op1,op2)) => MOV w op1 op2 end %% instruction_t)
  |+|
    "1000" $$ "100" $$ anybit $ modrm @ 
      (fun p => match p with | (w,(op1,op2)) => MOV w op2 op1 end %% instruction_t)
  |+|
   "1100" $$ "0111" $$ "11" $$ "000" $$ reg $ imm_op opsize_override @
     (fun p => match p with | (r,w) => MOV true  (Reg_op r) w end %% instruction_t)
  |+|
   "1100" $$ "0110" $$ "11" $$ "000" $$ reg $ byte @
     (fun p => match p with
                 | (r,b) => MOV false (Reg_op r) (Imm_op (zero_extend8_32 b)) 
               end %% instruction_t)
  |+|
    "1011" $$ "1" $$ reg $ imm_op opsize_override @ 
      (fun p => match p with | (r,w) => MOV true (Reg_op r)  w
                end %% instruction_t)
  |+| 
    "1011" $$ "0" $$ reg $ byte @ 
      (fun p => match p with 
                  | (r,b) => MOV false (Reg_op r) (Imm_op (zero_extend8_32 b))
                end %% instruction_t)
  |+|
    "1100" $$ "0111" $$ ext_op_modrm "000" $ imm_op opsize_override @ 
      (fun p => match p with | (op,w) => MOV true op w end %% instruction_t)
  |+|
    "1100" $$ "0110" $$ ext_op_modrm "000" $ byte @ 
    (fun p => match p with | (op,b) => MOV false op (Imm_op (zero_extend8_32 b)) end %% instruction_t)
  |+|
    "1010" $$ "0001" $$ word @ (fun w => MOV true  (Reg_op EAX) (Offset_op w) %% instruction_t)
  |+|
    "1010" $$ "0000" $$ word @ (fun w => MOV false (Reg_op EAX) (Offset_op w)  %% instruction_t)
  |+|
    "1010" $$ "0011" $$ word @ (fun w => MOV true (Offset_op w) (Reg_op EAX) %% instruction_t)
  |+|
    "1010" $$ "0010" $$ word @ (fun w => MOV false (Offset_op w) (Reg_op EAX) %% instruction_t).
  

  Definition control_reg_p := 
      bits "000" @ (fun _ => CR0 %% control_register_t) 
  |+| bits "010" @ (fun _ => CR2 %% control_register_t) 
  |+| bits "011" @ (fun _ => CR3 %% control_register_t) 
  |+| bits "100" @ (fun _ => CR4 %% control_register_t).
  
  Definition MOVCR_p := 
    "0000" $$ "1111" $$ "0010" $$ "0010" $$ "11" $$ control_reg_p $ reg @ 
    (fun p => MOVCR false (fst p) (snd p) %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "0010" $$ "0000" $$ "11" $$ control_reg_p $ reg @ 
    (fun p => MOVCR true (fst p) (snd p) %% instruction_t).

  (* Note:  apparently, the bit patterns corresponding to DR4 and DR5 either
   * (a) get mapped to DR6 and DR7 respectively or else (b) cause a fault,
   * depending upon the value of some control register.  My guess is that it's
   * okay for us to just consider this a fault. Something similar seems to
   * happen with the CR registers above -- e.g., we don't have a CR1. *)
  Definition debug_reg_p := 
      bits "000" @ (fun _ => DR0 %% debug_register_t) 
  |+| bits "001" @ (fun _ => DR1 %% debug_register_t) 
  |+| bits "010" @ (fun _ => DR2 %% debug_register_t) 
  |+| bits "011" @ (fun _ => DR3 %% debug_register_t) 
  |+| bits "110" @ (fun _ => DR6 %% debug_register_t) 
  |+| bits "111" @ (fun _ => DR7 %% debug_register_t).

  Definition MOVDR_p := 
    "0000" $$ "1111" $$ "0010" $$ "0011" $$ "11" $$ debug_reg_p $ reg @
    (fun p => MOVDR false (fst p) (snd p) %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "0010" $$ "0001" $$ "11" $$ debug_reg_p $ reg @
    (fun p => MOVDR true (fst p) (snd p) %% instruction_t).

  Definition segment_reg_p := 
      bits "000" @ (fun _ => ES %% segment_register_t) 
  |+| bits "001" @ (fun _ => CS %% segment_register_t) 
  |+| bits "010" @ (fun _ => SS %% segment_register_t) 
  |+| bits "011" @ (fun _ => DS %% segment_register_t) 
  |+| bits "100" @ (fun _ => FS %% segment_register_t) 
  |+| bits "101" @ (fun _ => GS %% segment_register_t).

  Definition seg_modrm : parser (pair_t segment_register_t operand_t) := 
        ("00" $$ segment_reg_p $ rm00)
    |+| ("01" $$ segment_reg_p $ rm01)
    |+| ("10" $$ segment_reg_p $ rm10)
    |+| ("11" $$ segment_reg_p $ rm11).

  Definition MOVSR_p := 
    "1000" $$ "1110" $$ seg_modrm @ 
      (fun p => MOVSR false (fst p) (snd p) %% instruction_t)
  |+|
    "1000" $$ "1100" $$ seg_modrm @ 
     (fun p => MOVSR true (fst p) (snd p) %% instruction_t).

  Definition MOVBE_p := 
    "0000" $$ "1111" $$ "0011" $$ "1000" $$ "1111" $$ "0000" $$ modrm @
    (fun p => MOVBE (snd p) (fst p) %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "0011" $$ "1000" $$ "1111" $$ "0001" $$ modrm @ 
    (fun p => MOVBE (fst p) (snd p) %% instruction_t).

  Definition MOVS_p := "1010" $$ "010" $$ anybit @ (fun x => MOVS x %% instruction_t).

  Definition MOVSX_p := "0000" $$ "1111" $$ "1011" $$ "111" $$ anybit $ modrm @
    (fun p => match p with | (w,(op1,op2)) => MOVSX w op1 op2 end %% instruction_t).

  Definition MOVZX_p := "0000" $$ "1111" $$ "1011" $$ "011" $$ anybit $ modrm @
    (fun p => match p with | (w,(op1,op2)) => MOVZX w op1 op2 end %% instruction_t).

  Definition MUL_p := 
  "1111" $$ "011" $$ anybit $ ext_op_modrm2 "100" @ 
    (fun p => MUL (fst p) (snd p) %% instruction_t).

  Definition NEG_p := 
  "1111" $$ "011" $$ anybit $ ext_op_modrm2 "011" @ 
    (fun p => NEG (fst p) (snd p) %% instruction_t).

  (*
  Definition NOP_p := 
    "1001" $$ bits "0000" @ (fun _ => NOP None %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "0001" $$ "1111" $$ ext_op_modrm "000" @ 
    (fun op => NOP (Some op) %% instruction_t).
  *)

  Definition NOT_p := 
    "1111" $$ "011" $$ anybit $ ext_op_modrm2 "010" @ 
    (fun p => NOT (fst p) (snd p) %% instruction_t).

  Definition OUT_p := 
    "1110" $$ "011" $$ anybit $ byte @ 
      (fun p => OUT (fst p) (Some (snd p)) %% instruction_t)
  |+|
    "1110" $$ "111" $$ anybit @ (fun w => OUT w None %% instruction_t).

  Definition OUTS_p := "0110" $$ "111" $$ anybit @ (fun x => OUTS x %% instruction_t).

  Definition POP_p := 
  "1000" $$ "1111" $$ ext_op_modrm "000" @ (fun x => POP x %% instruction_t)
  |+|
    "0101" $$ "1" $$ reg @ (fun r => POP (Reg_op r) %% instruction_t).

  Definition POPSR_p := 
    "000" $$ "00" $$ bits "111" @ (fun _ => POPSR ES %% instruction_t)
  |+|
    "000" $$ "10" $$ bits "111" @ (fun _ => POPSR SS %% instruction_t)
  |+|
    "000" $$ "11" $$ bits "111" @ (fun _ => POPSR DS %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "10" $$ "100" $$ bits "001" @ 
      (fun _ => POPSR FS %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "10" $$ "101" $$ bits "001" @ 
      (fun _ => POPSR GS %% instruction_t).

  Definition POPA_p := "0110" $$ bits "0001" @ (fun _ => POPA %% instruction_t).
  Definition POPF_p := "1001" $$ bits "1101" @ (fun _ => POPF %% instruction_t).
  
  Definition PUSH_p := 
    "1111" $$ "1111" $$ ext_op_modrm "110" @ (fun x => PUSH true x %% instruction_t)
  |+|
    "0101" $$ "0" $$ reg @ (fun r => PUSH true (Reg_op r) %% instruction_t)
  |+|
    "0110" $$ "1010" $$ byte @ 
    (fun b => PUSH false (Imm_op (sign_extend8_32 b)) %% instruction_t)
  |+|
    "0110" $$ "1000" $$ word @ (fun w => PUSH true (Imm_op w) %% instruction_t).

  Definition segment_reg2_p := 
        bits "00" @ (fun _ => ES %% segment_register_t) 
    |+| bits "01" @ (fun _ => CS %% segment_register_t) 
    |+| bits "10" @ (fun _ => SS %% segment_register_t) 
    |+| bits "11" @ (fun _ => DS %% segment_register_t).

  Definition PUSHSR_p := 
    "000" $$ segment_reg2_p $ bits "110" @ 
    (fun p => PUSHSR (fst p) %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "10" $$ "100" $$ bits "000" @ 
    (fun _ => PUSHSR FS %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "10" $$ "101" $$ bits "000" @ 
    (fun _ => PUSHSR GS %% instruction_t).

  Definition PUSHA_p := "0110" $$ bits "0000" @ (fun _ => PUSHA %% instruction_t).
  Definition PUSHF_p := "1001" $$ bits "1100" @ (fun _ => PUSHF %% instruction_t).

  Definition rotate_p extop (inst : bool -> operand -> reg_or_immed -> instr) := 
    "1101" $$ "000" $$ anybit $ ext_op_modrm2 extop @ 
    (fun p => inst (fst p) (snd p) (Imm_ri (Word.repr 1)) %% instruction_t)
  |+|
    "1101" $$ "001" $$ anybit $ ext_op_modrm2 extop @
    (fun p => inst (fst p) (snd p) (Reg_ri ECX) %% instruction_t)
  |+|
    "1100" $$ "000" $$ anybit $ ext_op_modrm2 extop $ byte @
    (fun p => match p with | (w, (op,b)) => inst w op (Imm_ri b) end %% instruction_t).

  Definition RCL_p := rotate_p "010" RCL.
  Definition RCR_p := rotate_p "011" RCR.

  Definition RDMSR_p := "0000" $$ "1111" $$ "0011" $$ bits "0010" @ 
    (fun _ => RDMSR %% instruction_t).
  Definition RDPMC_p := "0000" $$ "1111" $$ "0011" $$ bits "0011" @ 
    (fun _ => RDPMC %% instruction_t).
  Definition RDTSC_p := "0000" $$ "1111" $$ "0011" $$ bits "0001" @ 
    (fun _ => RDTSC %% instruction_t).
  Definition RDTSCP_p := "0000" $$ "1111" $$ "0000" $$ "0001" $$ "1111" $$ bits "1001" @
    (fun _ => RDTSCP %% instruction_t).

  (*
  Definition REPINS_p := "1111" $$ "0011" $$ "0110" $$ "110" $$ anybit @ 
    (fun x => REPINS x %% instruction_t).
  Definition REPLODS_p := "1111" $$ "0011" $$ "1010" $$ "110" $$ anybit @ 
    (fun x => REPLODS x %% instruction_t).
  Definition REPMOVS_p := "1111" $$ "0011" $$ "1010" $$ "010" $$ anybit @ 
    (fun x => REPMOVS x %% instruction_t).
  Definition REPOUTS_p := "1111" $$ "0011" $$ "0110" $$ "111" $$ anybit @ 
    (fun x => REPOUTS x %% instruction_t).
  Definition REPSTOS_p := "1111" $$ "0011" $$ "1010" $$ "101" $$ anybit @ 
    (fun x => REPSTOS x %% instruction_t).
  Definition REPECMPS_p := "1111" $$ "0011" $$ "1010" $$ "011" $$ anybit @ 
    (fun x => REPECMPS x %% instruction_t).
  Definition REPESCAS_p := "1111" $$ "0011" $$ "1010" $$ "111" $$ anybit @ 
    (fun x => REPESCAS x %% instruction_t).
  Definition REPNECMPS_p := "1111" $$ "0010" $$ "1010" $$ "011" $$ anybit @ 
    (fun x => REPNECMPS x %% instruction_t).
  Definition REPNESCAS_p := "1111" $$ "0010" $$ "1010" $$ "111" $$ anybit @ 
    (fun x => REPNESCAS x %% instruction_t).
  *)

  Definition RET_p := 
    "1100" $$ bits "0011" @ (fun _ => RET true None %% instruction_t)
  |+|
    "1100" $$ "0010" $$ halfword @ (fun h => RET true (Some h) %% instruction_t)
  |+|
    "1100" $$ bits "1011" @ (fun _ => RET false None %% instruction_t)
  |+|
    "1100" $$ "1010" $$ halfword @ (fun h => RET false (Some h) %% instruction_t).

  Definition ROL_p := rotate_p "000" ROL.
  Definition ROR_p := rotate_p "001" ROR.
  Definition RSM_p := "0000" $$ "1111" $$ "1010" $$ bits "1010" @ 
    (fun _ => RSM %% instruction_t).
  Definition SAHF_p := "1001" $$ bits "1110" @ 
    (fun _ => SAHF %% instruction_t).
  Definition SAR_p := rotate_p "111" SAR.
  Definition SCAS_p := "1010" $$ "111" $$ anybit @ (fun x => SCAS x %% instruction_t).
  Definition SETcc_p := 
  "0000" $$ "1111" $$ "1001" $$ tttn $ modrm @ 
    (fun p => SETcc (fst p) (snd (snd p)) %% instruction_t).
  Definition SGDT_p := "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm "000" @ 
    (fun x => SGDT x %% instruction_t).
  Definition SHL_p := rotate_p "100" SHL.

  Definition shiftdouble_p opcode inst :=
    ("0000" $$ "1111" $$ "1010" $$ opcode $$ "00" $$ "11" $$ reg $ reg $ byte) @
    (fun p => match p with | (r2,(r1,b)) => inst (Reg_op r1) r2 (Imm_ri b) end %% instruction_t)
  |+|
    ("0000" $$ "1111" $$ "1010" $$ opcode $$ "00" $$ modrm_noreg $ byte) @
    (fun p => match p with | ((r,op), b) => inst op r (Imm_ri b) end %% instruction_t)
  |+|
    ("0000" $$ "1111" $$ "1010" $$ opcode $$ "01" $$ "11" $$ reg $ reg) @
    (fun p => match p with | (r2,r1) => inst (Reg_op r1) r2 (Reg_ri ECX) end %% instruction_t)
  |+|
    ("0000" $$ "1111" $$ "1010" $$ opcode $$ "01" $$ modrm_noreg) @
    (fun p => match p with | (r,op) => inst op r (Reg_ri ECX) end %% instruction_t).
 
  Definition SHLD_p := shiftdouble_p "01" SHLD.
  Definition SHR_p := rotate_p "101" SHR.
  Definition SHRD_p := shiftdouble_p "11" SHRD.
  Definition SIDT_p := "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm "001" @ 
    (fun x => SIDT x %% instruction_t).
  Definition SLDT_p := "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "000" @ 
    (fun x => SLDT x %% instruction_t).
  Definition SMSW_p := "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm "100" @ 
    (fun x => SMSW x %% instruction_t).
  Definition STC_p := "1111" $$ bits "1001" @ (fun _ => STC %% instruction_t).
  Definition STD_p := "1111" $$ bits "1101" @ (fun _ => STD %% instruction_t).
  Definition STI_p := "1111" $$ bits "1011" @ (fun _ => STI %% instruction_t).
  Definition STOS_p := "1010" $$ "101" $$ anybit @ 
    (fun x => STOS x %% instruction_t).
  Definition STR_p := "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "001" @ 
    (fun x => STR x  %% instruction_t).
 
  Definition TEST_p (opsize_override: bool) := 
    "1111" $$ "0111" $$ ext_op_modrm2 "000" $ imm_op opsize_override @ 
    (fun p => TEST true (fst p) (snd p) %% instruction_t)
  |+| 
    "1111" $$ "0110" $$ ext_op_modrm2 "000" $ byte @ 
    (fun p => TEST false (fst p) (Imm_op (zero_extend8_32 (snd p))) %% instruction_t)
  |+|
    "1000" $$ "010" $$ anybit $ modrm @
    (fun p => match p with | (w,(op1,op2)) => TEST w op1 op2 end %% instruction_t)
  |+|
    "1010" $$ "1001" $$ imm_op opsize_override @ (fun w => TEST true w (Reg_op EAX) %% instruction_t)
  |+|
    "1010" $$ "1000" $$ byte @ 
    (fun b => TEST true (Imm_op (zero_extend8_32 b)) (Reg_op EAX) %% instruction_t).
  
  Definition UD2_p := "0000" $$ "1111" $$ "0000" $$ bits "1011" @ 
    (fun _ => UD2 %% instruction_t).

  Definition VERR_p := "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "100" @ 
    (fun x => VERR x %% instruction_t).
  Definition VERW_p := "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "101" @ 
    (fun x => VERW x %% instruction_t).
  Definition WAIT_p := "1001" $$ bits "1011 " @ (fun _ => WAIT %% instruction_t).
  Definition WBINVD_p := "0000" $$ "1111" $$ "0000" $$ bits "1001" @ 
    (fun _ => WBINVD %% instruction_t).
  Definition WRMSR_p := "0000" $$ "1111" $$ "0011" $$ bits "0000" @ 
    (fun _ => WRMSR %% instruction_t).
  Definition XADD_p := 
    "0000" $$ "1111" $$ "1100" $$ "000" $$ anybit $ modrm @ 
    (fun p => match p with | (w,(op1,op2)) => XADD w op2 op1 end %% instruction_t).
  Definition XCHG_p := 
    "1000" $$ "011" $$ anybit $ modrm @ 
    (fun p => match p with | (w,(op1,op2)) => XCHG w op1 op2 end %% instruction_t)
  |+|
    "1001" $$ "0" $$ reg @ (fun r => XCHG true (Reg_op EAX) (Reg_op r) %% instruction_t).

  Definition XLAT_p := "1101" $$ bits "0111" @ (fun _ => XLAT %% instruction_t).

  (* Now glue all of the individual instruction parsers together into 
     one big parser. *)
  
  Definition instr_parsers_opsize_pre : list (parser instruction_t) :=
    ADC_p true :: ADD_p true :: AND_p true :: CMP_p true :: OR_p true :: SBB_p true :: SUB_p true :: SHL_p :: SHLD_p :: SHR_p :: SAR_p :: SHRD_p :: XOR_p true ::IMUL_p true :: MOV_p true :: MOVSX_p :: MOVZX_p :: NEG_p :: NOT_p :: DIV_p :: IDIV_p :: TEST_p true :: CDQ_p :: CWDE_p :: MUL_p :: XCHG_p :: nil.

  Definition instr_parsers_nosize_pre : list (parser instruction_t) := 
    AAA_p :: AAD_p :: AAM_p :: AAS_p :: ADC_p false :: ADD_p false :: AND_p false :: CMP_p false :: OR_p false :: SBB_p false :: SUB_p false :: XOR_p false :: ARPL_p :: BOUND_p :: BSF_p :: BSR_p :: BSWAP_p :: BT_p :: BTC_p :: BTR_p :: BTS_p :: CALL_p :: CDQ_p :: CLC_p :: CLD_p :: CLI_p :: CMOVcc_p :: CMC_p :: CMPS_p :: CMPXCHG_p :: CPUID_p :: CWDE_p :: DAA_p :: DAS_p :: DEC_p :: DIV_p :: HLT_p :: IDIV_p :: IMUL_p false :: IN_p :: INC_p :: INS_p :: INTn_p :: INT_p :: INTO_p :: INVD_p :: INVLPG_p :: IRET_p :: Jcc_p :: JCXZ_p :: JMP_p :: LAHF_p :: LAR_p :: LDS_p :: LEA_p :: LEAVE_p :: LES_p :: LFS_p :: LGDT_p :: LGS_p :: LIDT_p :: LLDT_p :: LMSW_p :: (* LOCK_p :: -- see note above about LOCK_p *) LODS_p :: LOOP_p :: LOOPZ_p :: LOOPNZ_p :: LSL_p :: LSS_p :: LTR_p :: MOV_p false :: MOVCR_p :: MOVDR_p :: MOVSR_p :: MOVBE_p :: MOVS_p :: MOVSX_p :: MOVZX_p :: MUL_p :: NEG_p :: (* NOP_p :: *) NOT_p :: OUT_p :: OUTS_p :: POP_p :: POPSR_p :: POPA_p :: POPF_p :: PUSH_p :: PUSHSR_p :: PUSHA_p :: PUSHF_p :: RCL_p :: RCR_p :: RDMSR_p :: RDPMC_p :: RDTSC_p :: RDTSCP_p :: (* REPINS_p :: REPLODS_p :: REPMOVS_p :: REPOUTS_p :: REPSTOS_p :: REPECMPS_p :: REPESCAS_p :: REPNECMPS_p :: REPNESCAS_p :: *) RET_p :: ROL_p :: ROR_p :: RSM_p :: SAHF_p :: SAR_p :: SCAS_p :: SETcc_p :: SGDT_p :: SHL_p :: SHLD_p :: SHR_p :: SHRD_p :: SIDT_p :: SLDT_p :: SMSW_p :: STC_p :: STD_p :: STI_p :: STOS_p :: STR_p :: TEST_p false :: UD2_p :: VERR_p :: VERW_p :: WAIT_p :: WBINVD_p :: WRMSR_p :: XADD_p :: XCHG_p :: XLAT_p :: nil.

  Fixpoint list2pair_t (l: list result) :=
    match l with
      | nil => unit_t
      | r::r'::nil => pair_t r r'
      | r::l' => pair_t r (list2pair_t l')
    end.
 

  Definition lock_or_rep_p : parser lock_or_rep_t :=
    ("1111" $$ ( bits "0000" @ (fun _ => lock %% lock_or_rep_t)
                 |+| bits "0010" @ (fun _ => repn %% lock_or_rep_t)
                 |+| bits "0011" @ (fun _ => rep  %% lock_or_rep_t))).

  Definition segment_override_p : parser segment_register_t :=
  ("0010" $$ bits "1110" @ (fun _ => CS %% segment_register_t)
    |+| "0011" $$ bits "0110" @ (fun _ => SS %% segment_register_t)
    |+| "0011" $$ bits "1110" @ (fun _ => DS %% segment_register_t)
    |+| "0010" $$ bits "0110" @ (fun _ => ES %% segment_register_t)
    |+| "0110" $$ bits "0100" @ (fun _ => FS %% segment_register_t)
    |+| "0110" $$ bits "0101" @ (fun _ => GS %% segment_register_t)).

  Definition op_override_p : parser bool_t :=
    "0110" $$ bits "0110" @ (fun _ => true %% bool_t).
  Definition addr_override_p : parser bool_t :=
    "0110" $$ bits "0111" @ (fun _ => true %% bool_t).

  (* Ok, now I want all permutations of the above four parsers. 
     I make a little perm2 combinator that takes two parsers and gives you
     p1 $ p2 |+| p2 $ p1, making sure to swap the results in the second case *)
  
  Definition perm2 t1 t2 (p1: parser t1) (p2: parser t2) : parser (pair_t t1 t2) :=
      p1 $ p2 |+|
      p2 $ p1 @ (fun p => match p with (a, b) => (b, a) %% pair_t t1 t2 end).

  (* Then I build that up into a perm3 and perm4. One could make a recursive
     function to do this, but I didn't want to bother with the necessary
     proofs and type-system juggling.*) 

  Definition perm3 t1 t2 t3 (p1: parser t1) (p2: parser t2) (p3: parser t3)
    : parser (pair_t t1 (pair_t t2 t3)) :=
    let r_t := pair_t t1 (pair_t t2 t3) in
       p1 $ (perm2 p2 p3)
   |+| p2 $ (perm2 p1 p3) @ (fun p => match p with (b, (a, c)) => (a, (b, c)) %% r_t end)
   |+| p3 $ (perm2 p1 p2) @ (fun p => match p with (c, (a, b)) => (a, (b, c)) %% r_t end).

  Definition perm4 t1 t2 t3 t4 (p1: parser t1) (p2: parser t2) (p3: parser t3)
    (p4: parser t4) : parser (pair_t t1 (pair_t t2 (pair_t t3 t4))) :=
    let r_t := pair_t t1 (pair_t t2 (pair_t t3 t4)) in
       p1 $ (perm3 p2 p3 p4)
   |+| p2 $ (perm3 p1 p3 p4) @ 
         (fun p => match p with (b, (a, (c, d))) => (a, (b, (c, d))) %% r_t end)
   |+| p3 $ (perm3 p1 p2 p4) @ 
         (fun p => match p with (c, (a, (b, d))) => (a, (b, (c, d))) %% r_t end)
   |+| p4 $ (perm3 p1 p2 p3) @ 
         (fun p => match p with (d, (a, (b, c))) => (a, (b, (c, d))) %% r_t end). 

  (* In this case, prefixes are optional. Before, each of the above
     parsing rules for the prefixes accepted Eps, and this was how we
     handled this.  However, if the parsers you join with perm can
     each accept Eps, then the result is a _highly_ ambiguous parser.

     Instead we have a different combinator, called option_perm, that 
     handles this without introducing extra ambiguity *)

  (* This signature is slightly awkward - because there's no result
     type corresponding to option (and I'm hesitant to add it to
     Parser at the moment) we can't just have a signature like parser
     t1 -> parser t2 -> parser (option_t t1) (option_t t2)) *)
    
  Definition option_perm2 t1 t2 (p1: parser (tipe_t t1)) (p2: parser (tipe_t t2)) 
     : parser (pair_t (option_t t1) (option_t t2)) :=
     let r_t := pair_t (option_t t1) (option_t t2) in 
         Eps_p @ (fun p => (None, None) %% r_t)  
     |+| p1 @ (fun p => (Some p, None) %% r_t ) 
     |+| p2 @ (fun p => (None, Some p) %% r_t) 
     |+| perm2 p1 p2 @ (fun p => match p with (a, b) => (Some a, Some b) %%r_t end). 

  Definition option_perm3 t1 t2 t3 (p1:parser(tipe_t t1)) (p2:parser(tipe_t t2))
    (p3:parser(tipe_t t3)): parser(pair_t(option_t t1)(pair_t(option_t t2) (option_t t3)))
    :=
    let r_t := pair_t(option_t t1)(pair_t(option_t t2) (option_t t3))  in
        Eps_p @ (fun p => (None, (None, None)) %% r_t)
    |+| p1 @ (fun p => (Some p, (None, None)) %% r_t)
    |+| p2 @ (fun p => (None, (Some p, None)) %% r_t)
    |+| p3 @ (fun p => (None, (None, Some p)) %% r_t)
    |+| perm2 p1 p2 @(fun p => match p with (a, b) => (Some a, (Some b, None)) %%r_t end)
    |+| perm2 p1 p3 @(fun p => match p with (a, c) => (Some a, (None, Some c)) %%r_t end)
    |+| perm2 p2 p3 @(fun p => match p with (b, c) => (None, (Some b, Some c)) %%r_t end)
    |+| perm3 p1 p2 p3 @ (fun p => match p with (a, (b, c))
                                    => (Some a, (Some b, Some c)) %%r_t end).

  (* This is beginning to get quite nasty. Someone should write a form for arbitrary
     n and prove it's correct :) *)
  Definition option_perm4 t1 t2 t3 t4 (p1:parser(tipe_t t1)) (p2: parser(tipe_t t2))
    (p3: parser(tipe_t t3)) (p4: parser(tipe_t t4)) :
      parser(pair_t(option_t t1) (pair_t(option_t t2) (pair_t(option_t t3) (option_t t4))))
      := 
    let r_t := pair_t(option_t t1) (pair_t(option_t t2)
      (pair_t(option_t t3)(option_t t4))) in
        Eps_p @ (fun p => (None, (None, (None, None))) %% r_t)
    |+| p1 @ (fun p => (Some p, (None, (None, None))) %% r_t)
    |+| p2 @ (fun p => (None, (Some p, (None, None))) %% r_t)
    |+| p3 @ (fun p => (None, (None, (Some p, None))) %% r_t)
    |+| p4 @ (fun p => (None, (None, (None, Some p))) %% r_t)
    |+| perm2 p1 p2 @ (fun p => match p with (a, b)
                                  => (Some a, (Some b, (None, None))) %% r_t end)
    |+| perm2 p1 p3 @ (fun p => match p with (a, c)
                                  => (Some a, (None, (Some c, None))) %% r_t end)
    |+| perm2 p1 p4 @ (fun p => match p with (a, d)
                                  => (Some a, (None, (None, Some d))) %% r_t end)
    |+| perm2 p2 p3 @ (fun p => match p with (b, c)
                                  => (None, (Some b, (Some c, None))) %% r_t end)
    |+| perm2 p2 p4 @ (fun p => match p with (b, d)
                                  => (None, (Some b, (None, Some d))) %% r_t end)
    |+| perm2 p3 p4 @ (fun p => match p with (c, d)
                                  => (None, (None, (Some c, Some d))) %% r_t end)
    |+| perm3 p1 p2 p3 @ (fun p => match p with (a, (b, c))
                                    => (Some a, (Some b, (Some c, None))) %%r_t end)
    |+| perm3 p1 p3 p4 @ (fun p => match p with (a, (c, d))
                                    => (Some a, (None, (Some c, Some d))) %%r_t end)
    |+| perm3 p1 p2 p4 @ (fun p => match p with (a, (b, d))
                                    => (Some a, (Some b, (None, Some d))) %%r_t end)
    |+| perm3 p2 p3 p4 @ (fun p => match p with (b, (c, d))
                                    => (None, (Some b, (Some c, Some d))) %%r_t end)
    |+| perm4 p1 p2 p3 p4 @ (fun p => match p with (a, (b, (c, d)))
                                        => (Some a, (Some b, (Some c, Some d))) %% r_t end).
                                      
  Definition opt2b (a: option bool) (default: bool) :=
    match a with
      | Some b => b
      | None => default
    end.
  
  Definition prefix_parser_nooverride := 
   option_perm2 lock_or_rep_p segment_override_p @ 
     (fun p => match p with (l, s) => 
                 mkPrefix l s false false %% prefix_t end).
  Definition prefix_parser_opsize :=
    op_override_p @ (fun p =>  mkPrefix None None p false %% prefix_t)
    |+| op_override_p $ lock_or_rep_p @ 
        (fun p => match p with (b, l) => (mkPrefix (Some l) None b false %% prefix_t) end)

    |+| op_override_p $ segment_override_p @
        (fun p => match p with (b, s) => (mkPrefix None (Some s) b false %% prefix_t) end)

    |+| op_override_p $ lock_or_rep_p $ segment_override_p @
        (fun p => match p with (b, (l, s)) => 
                    (mkPrefix (Some l) (Some s) b false %% prefix_t) end)

    |+| op_override_p $ segment_override_p $ lock_or_rep_p @
        (fun p => match p with (b, (s, l)) =>
                    (mkPrefix (Some l) (Some s) b false %% prefix_t) end)

    |+| segment_override_p $ op_override_p @
        (fun p => match p with (s, b) =>
                    (mkPrefix None (Some s) b false %% prefix_t) end)

    |+| segment_override_p $ op_override_p $ lock_or_rep_p @
        (fun p => match p with (s, (b, l)) =>
                    (mkPrefix (Some l) (Some s) b false %% prefix_t) end)

    |+| segment_override_p $ lock_or_rep_p $ op_override_p  @
        (fun p => match p with (s, (l, b)) =>
                    (mkPrefix (Some l) (Some s) b false %% prefix_t) end)

    |+| lock_or_rep_p $ op_override_p @
        (fun p => match p with (l, b) =>
                    (mkPrefix (Some l) None b false %% prefix_t) end)

    |+| lock_or_rep_p $ op_override_p $ segment_override_p @
        (fun p => match p with (l, (b, s)) =>
                    (mkPrefix (Some l) (Some s) b false %% prefix_t) end)

    |+| lock_or_rep_p $ segment_override_p $ op_override_p @
        (fun p => match p with (l, (s, b)) =>
                    (mkPrefix (Some l) (Some s) b false %% prefix_t) end).

  Definition instruction_parser_list := 
    (List.map (fun (p:parser instruction_t) => prefix_parser_nooverride $ p)
      instr_parsers_nosize_pre) ++
    (List.map (fun (p:parser instruction_t) => prefix_parser_opsize $ p) 
      instr_parsers_opsize_pre).

  Definition instruction_parser := alts instruction_parser_list.

  Definition instruction_regexp_pair := parser2regexp instruction_parser.
  Record instParserState := mkPS { 
    inst_ctxt : ctxt_t ; 
    inst_regexp : regexp (pair_t prefix_t instruction_t) ; 
    inst_regexp_wf : wf_regexp inst_ctxt inst_regexp 
  }.

  Definition initial_parser_state : instParserState := 
    mkPS (snd instruction_regexp_pair) (fst instruction_regexp_pair) 
    (p2r_wf instruction_parser _).

  Definition byte_explode (b:int8) : list bool := 
  let bs := Word.bits_of_Z 8 (Word.unsigned b) in
    (bs 7)::(bs 6)::(bs 5)::(bs 4)::(bs 3)::(bs 2)::(bs 1)::(bs 0)::nil.

  Definition parse_byte (ps:instParserState) (b:int8) : 
    instParserState * list (prefix * instr) := 
    let cs := byte_explode b in
    let r' := deriv_parse' (inst_regexp ps) cs in
    let wf' := wf_derivs (inst_ctxt ps) cs (inst_regexp ps) (inst_regexp_wf ps) in
      (mkPS (inst_ctxt ps) r' wf', apply_null (inst_ctxt ps) r' wf').

End X86_PARSER.

