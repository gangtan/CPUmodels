(* Copyright (c) 2010-2011.
   Greg Morrisett, Gang Tan, Joseph Tassarotti, Jean-Baptiste Tristan, Edward Gan.
   All rights reserved. *)

(** VerifierDFA.v:  
    This file contains definitions of the parsers used to build the DFAs
    used in FastVerifier.
*)
Require Import Coqlib.
Require Import Parser.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import Bits.
Require Import Decode.
Require Import Eqdep.
Require Import Int32.
Unset Automatic Introduction.
Set Implicit Arguments.
Open Scope char_scope.
Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.
Require ExtrOcamlNatInt.
Import X86_PARSER_ARG.
Import X86_PARSER.
Import X86_BASE_PARSER.
Require Import X86Syntax.

(* In NaCl, ChunkSize is either 16 or 32 *)
Definition logChunkSize := 5%nat.
Definition chunkSize := two_power_nat logChunkSize.
Notation int8_of_nat n := (@repr 7 (Z_of_nat n)).
Definition safeMask := shl (Word.mone 7) (int8_of_nat logChunkSize).

Fixpoint int2bools_aux (bs : Z -> bool) (n: nat) : list bool :=
  match n with
    | O => bs 0 :: nil
    | S n' => bs (Z_of_nat n) :: int2bools_aux bs n'
  end.

Definition int_to_bools {s} (x: Word.int s) : list bool :=
  int2bools_aux (Word.bits_of_Z (s+1) (Word.unsigned x)) s.

Definition nat2bools(n:nat) : list bool := 
  let bs := Word.bits_of_Z 8 (Z_of_nat n) in
    (bs 7)::(bs 6)::(bs 5)::(bs 4)::(bs 3)::(bs 2)::(bs 1)::(bs 0)::nil.

Definition make_dfa t (p:parser t) := build_dfa 256 nat2bools 400 (par2rec p).
Implicit Arguments make_dfa [t].


(** Subset of the parsers that don't do control-flow, but allow the
    operand size override prefix -- this is actually the same as 
    instr_parsers_opsize_pre. *)
Definition non_cflow_instrs_opsize_pre : list (parser instruction_t) := 
  instr_parsers_opsize_pre.

(** Subset of the parsers that don't do control-flow, and do not allow the
    operand size override prefix. *)
Definition non_cflow_instrs_nosize_pre : list (parser instruction_t) := 
  AAA_p :: AAD_p :: AAM_p :: AAS_p :: ADC_p false :: ADD_p false :: AND_p false :: 
  CMP_p false :: OR_p false :: SBB_p false :: SUB_p false :: XOR_p false :: 
  BSF_p :: BSR_p :: BSWAP_p :: BT_p :: BTC_p :: BTR_p :: BTS_p :: 
  CDQ_p :: CLC_p :: 
  (* FIX:  why does NACL accept CLD? *)
  CLD_p :: 
  CMOVcc_p :: CMC_p ::CMPXCHG_p :: 
  CWDE_p :: DAA_p :: DAS_p :: DEC_p :: DIV_p :: 
  (* FIX:  why does NACL accept HLT? *)
  HLT_p ::
  IDIV_p :: 
  IMUL_p false :: INC_p :: LAHF_p :: LEA_p :: LEAVE_p :: MOV_p false 
  :: MOVSX_p :: MOVZX_p :: 
  MUL_p :: NEG_p :: NOT_p :: POP_p :: POPA_p :: PUSH_p :: PUSHA_p :: 
  RCL_p :: RCR_p :: ROL_p :: ROR_p :: SAHF_p :: SAR_p :: SETcc_p :: 
  SHL_p :: SHLD_p :: SHR_p :: SHRD_p :: STC_p :: STD_p :: TEST_p false :: XADD_p :: XCHG_p :: 
  nil.

(** Subset of the parsers that don't do control-flow and which allow
   the rep prefix - some of these are allowed to have 16 bit mode
   in NaCl, but to be safe we'll not add those in unless we get a
   failing test case. *)
Definition non_cflow_instrs_rep_pre : list (parser instruction_t) :=
  CMPS_p :: MOVS_p :: STOS_p :: nil.

(** Prefixes allowed for non-control-flow operations that support an
    operand size override.  We could possibly add in the lock and 
    repeat prefixes, but I'm keeping things simple for now.  We cannot
    allow the segment override prefix for NaCL. *)
Definition valid_prefix_parser_opsize := 
  op_override_p @ (fun p => mkPrefix None None p false %% prefix_t).

(** Prefixes allowed for non-control-flow operations that do not support
    an operand size override.  We could possibly add in the lock and
    repeat prefixes, but I'm keeping things simple for now. We cannot
    allows the segment override prefix for NaCL, except for GS *)
Definition valid_prefix_parser_nooverride := 
  Eps_p @ (fun p => (mkPrefix None None false false) %% prefix_t) |+|
  ("0110" $$ bits "0101" @ (fun p => (mkPrefix None (Some GS) false false) %% prefix_t)).

(** We're only allowing rep for now - no lock - these are just the string ops. *)
Definition valid_prefix_parser_rep :=
  Eps_p @ (fun p => (mkPrefix None None false false) %% prefix_t) |+|
  ("1111" $$ bits "0011" @ (fun _ => (mkPrefix (Some rep) None false false) %% prefix_t)).


(** The list of valid prefix and instruction parsers for non-control-flow
    operations. *)
Definition non_cflow_parser_list := 
  (List.map (fun (p:parser instruction_t) => valid_prefix_parser_nooverride $ p) 
    non_cflow_instrs_nosize_pre) ++
  (List.map (fun (p:parser instruction_t) => valid_prefix_parser_opsize $ p)
    non_cflow_instrs_opsize_pre) ++
  (List.map (fun (p:parser instruction_t) => valid_prefix_parser_rep $ p)
    non_cflow_instrs_rep_pre).

Definition non_cflow_parser := alts non_cflow_parser_list.

(* Direct jumps. Destinations will be checked to see if 
   they are known, valid starts of instructions. *)

(* We only want to allow "near" jumps to direct, relative offsets *)
Definition dir_near_JMP_p : parser instruction_t := 
    "1110" $$ "1011" $$ byte @
    (fun b => JMP true false (Imm_op (sign_extend8_32 b)) None %% instruction_t)
  |+|
    "1110" $$ "1001" $$ word @ 
    (fun w => JMP true false (Imm_op w) None %% instruction_t).

Definition dir_near_Jcc_p : parser instruction_t :=
    "0111" $$ tttn $ byte @ 
    (fun p => let (ct,imm) := p in Jcc ct (sign_extend8_32 imm) %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "1000" $$ tttn $ word @ 
    (fun p => let (ct,imm) := p in Jcc ct imm %% instruction_t).

Definition dir_near_CALL_p : parser instruction_t := 
   "1110" $$ "1000" $$ word  @ 
    (fun w => CALL true false (Imm_op w) None %% instruction_t).

Definition dir_cflow : list (parser instruction_t) :=
  dir_near_JMP_p :: dir_near_Jcc_p :: dir_near_CALL_p :: nil.

Definition register_to_Z (r: register) :=
  match r with
    | EAX => 0
    | ECX => 1
    | EDX => 2
    | EBX => 3
    | ESP => 4
    | EBP => 5
    | ESI => 6
    | EDI => 7
  end.

Lemma register_to_Z_identity1: forall r, Z_to_register (register_to_Z r) = r.
Proof. destruct r; auto.
Qed. 

Definition register_to_bools (r: register) := 
  let bs := Word.bits_of_Z 3 (register_to_Z r) in
    (bs 2) :: (bs 1) :: (bs 0) :: nil.

Fixpoint bitslist (bs: list bool) : parser unit_t :=
  match bs with
    | nil => Eps_p
    | b::bs' => Cat_p (Char_p b) (bitslist bs') @ (fun _ => tt %% unit_t)
  end.

Definition nacl_MASK_p (r: register) : parser instruction_t :=
      "1000" $$ "0011" $$ "11" $$ bits "100"    (* AND opcode for Imm to register*)
    $ bitslist (register_to_bools r)             (* Register *)
    $ bitslist (int_to_bools safeMask)
    @ (fun _ => AND true (Reg_op r) (Imm_op (sign_extend8_32 safeMask))
      %% instruction_t).

(* This should give a parser corresponding to (JMP true true (Reg_op
   reg) None. Note that ESP cannot be passed as a register here since
   the bit pattern for ESP is used as a special mode for the rm00 *)

Definition nacl_JMP_p  (r: register) : parser instruction_t :=
      "1111" $$ "1111" $$ "11" $$ bits "100"
    $ bitslist (register_to_bools r)  @ 
    (fun _ =>  JMP true true (Reg_op r) None %% instruction_t).

Definition nacl_CALL_p (r: register) : parser instruction_t :=
      "1111" $$ "1111" $$ "11" $$ bits "010"
    $ bitslist (register_to_bools r)  @ 
    (fun _ => CALL true true (Reg_op r) None %% instruction_t).

Definition nacljmp_p (r: register) : parser (pair_t instruction_t instruction_t) :=
  nacl_MASK_p r $ (nacl_JMP_p r |+| nacl_CALL_p r).

Definition b8 := true::false::false::false::nil.
Definition b3 := false::false::true::true::nil.
Definition be := true::true::true::false::nil.
Definition b0 := false::false::false::false::nil.
Definition bf := true::true::true::true::nil.

Definition mybits := b8 ++ b3 ++ be ++ b0 ++ be ++ b0 ++ bf ++ bf ++ be ++ b0.


(* These are akin to the NaCl "pseudo-instruction" nacljmp. We will
   check if the jump destination is appropriately masked by the
   preceding AND *)
Definition nacljmp_mask : list (parser (pair_t instruction_t instruction_t)) := 
  nacljmp_p EAX :: nacljmp_p ECX :: nacljmp_p EDX :: nacljmp_p EBX ::
  nacljmp_p EBP :: nacljmp_p ESI :: nacljmp_p EDI :: nil.

  Fixpoint parseloop ps bytes := 
    match bytes with 
      | nil => None
      | b::bs => match Decode.X86_PARSER.parse_byte ps b with 
                   | (ps', nil) => parseloop ps' bs
                     (* JGM: FIX!  What to do with prefix? *)
                   | (ps', (pfx,JMP true false (Imm_op disp) sel)::_) => 
                     match bs with 
                       | nil => Some disp
                       | _ => None
                     end
                   | (ps', _) => None
                 end
    end.

(** Next, we define a boolean-valued test that tells whether an instruction
    is a valid non-control-flow instruction.  We should have the property
    that the [non_cflow_parser] only builds instructions that satisfy this
    predicate (as shown below.)  Furthermore, we should be able to argue
    that for each of these instructions, the NaCL SFI invariants are preserved. 
*)
Definition no_imm_op(op1:operand) : bool := 
  match op1 with 
    | Imm_op _ => false
    | _ => true
  end.

Definition only_op_override (p : prefix) : bool := 
  match lock_rep p, seg_override p, addr_override p with 
    | None, None, false => true
    | _, _, _ => false
  end.

Definition no_prefix (p : prefix) : bool := 
  match lock_rep p, seg_override p, op_override p, addr_override p with
    | None, None, false, false => true
    | _, _, _, _ => false
  end.

Definition only_gs_seg_override (p:prefix) : bool := 
  match lock_rep p, seg_override p, op_override p, addr_override p with
    | None, None, false, false => true
    | None, (Some GS), false, false => true
    | _, _, _, _ => false
  end.

Definition only_lock_or_rep (p: prefix) : bool :=
  match lock_rep p, seg_override p, op_override p, addr_override p with
    | Some rep, None, false, false => true
    | None, None, false, false => true
    | _,_,_,_ => false
  end.

Definition either_prefix (p:prefix) := 
  only_op_override p || only_gs_seg_override p.

Definition non_cflow_instr (pfx:prefix) (ins:instr) : bool := 
  match ins with 
    | AAA => only_gs_seg_override pfx
    | AAD => only_gs_seg_override pfx
    | AAM => only_gs_seg_override pfx
    | AAS => only_gs_seg_override pfx
    | ADC w op1 op2 => either_prefix pfx && no_imm_op op1
    | ADD w op1 op2 => either_prefix pfx && no_imm_op op1
    | AND w op1 op2 => either_prefix pfx && no_imm_op op1
    | CMP w op1 op2 => either_prefix pfx
    | OR w op1 op2 => either_prefix pfx && no_imm_op op1
    | SBB w op1 op2 => either_prefix pfx && no_imm_op op1
    | SUB w op1 op2 => either_prefix pfx && no_imm_op op1
    | XOR w op1 op2 => either_prefix pfx && no_imm_op op1
    | BSF op1 op2 => only_gs_seg_override pfx && no_imm_op op1
    | BSR op1 op2 => only_gs_seg_override pfx && no_imm_op op1 
    | BSWAP r => only_gs_seg_override pfx
    | BT op1 op2 => only_gs_seg_override pfx && no_imm_op op1
    | BTC op1 op2 => only_gs_seg_override pfx  && no_imm_op op1
    | BTR op1 op2 => only_gs_seg_override pfx && no_imm_op op1
    | BTS op1 op2 => only_gs_seg_override pfx  && no_imm_op op1
    | CDQ => either_prefix pfx
    | CLC => only_gs_seg_override pfx 
    | CLD => only_gs_seg_override pfx
    | CMOVcc ct op1 op2 => only_gs_seg_override pfx && no_imm_op op1
    | CMC => only_gs_seg_override pfx 
    | CMPXCHG w op1 op2 => only_gs_seg_override pfx && no_imm_op op1
    | CWDE => either_prefix pfx
    | DAA => only_gs_seg_override pfx
    | DAS => only_gs_seg_override pfx
    | DEC w op1 => only_gs_seg_override pfx && no_imm_op op1
    | DIV w op1 => either_prefix pfx && no_imm_op op1
    | HLT => only_gs_seg_override pfx
    | IDIV w op1 => either_prefix pfx && no_imm_op op1
    | IMUL w op1 opopt2 iopt3 => either_prefix pfx && no_imm_op op1
    | INC w op1 => only_gs_seg_override pfx && no_imm_op op1
    | LAHF => only_gs_seg_override pfx
    | LEA op1 (Address_op a) => only_gs_seg_override pfx && no_imm_op op1
    | LEAVE => only_gs_seg_override pfx
    | MOV w op1 op2 => either_prefix pfx && no_imm_op op1
    | MOVSX w op1 op2 => either_prefix pfx && no_imm_op op1
    | MOVZX w op1 op2 => either_prefix pfx && no_imm_op op1
    | MUL w op1 => either_prefix pfx && no_imm_op op1
    | NEG w op1 => either_prefix pfx && no_imm_op op1
    | NOT w op1 => either_prefix pfx && no_imm_op op1
    | POP op1 => only_gs_seg_override pfx && no_imm_op op1
    | POPA => only_gs_seg_override pfx  
    | PUSH w op1 => only_gs_seg_override pfx
    | PUSHA => only_gs_seg_override pfx 
    | RCL w op1 ri => only_gs_seg_override pfx && no_imm_op op1
    | RCR w op1 ri => only_gs_seg_override pfx && no_imm_op op1
    | ROL w op1 ri => only_gs_seg_override pfx && no_imm_op op1
    | ROR w op1 ri => only_gs_seg_override pfx && no_imm_op op1
    | SAHF => only_gs_seg_override pfx
    | SAR w op1 ri => either_prefix pfx && no_imm_op op1
    | SETcc ct op1 => only_gs_seg_override pfx && no_imm_op op1
    | SHL w op1 ri => either_prefix pfx && no_imm_op op1
    | SHLD op1 r ri => either_prefix pfx && no_imm_op op1
    | SHR w op1 ri => either_prefix pfx && no_imm_op op1
    | SHRD op1 r ri => either_prefix pfx && no_imm_op op1
    | STC => only_gs_seg_override pfx 
    | STD => only_gs_seg_override pfx 
    | TEST w op1 op2 => either_prefix pfx
    | XADD w op1 op2 => only_gs_seg_override pfx && no_imm_op op1 && no_imm_op op2
    | XCHG w op1 op2 => either_prefix pfx && no_imm_op op1 && no_imm_op op2
    | CMPS w => only_lock_or_rep pfx
    | MOVS w => only_lock_or_rep pfx
    | STOS w => only_lock_or_rep pfx
    | _ => false
  end.


(** We rule out JMPs and CALLs that are far (i.e., not near), that
    are absolute instead of relative, that don't have an immediate
    operand, or that have a selector. *)
Definition dir_cflow_instr (pre:prefix) (ins: instr) : bool :=
  match ins with
    | JMP true false (Imm_op _) None => no_prefix pre
    | Jcc ct disp => no_prefix pre
    | CALL true false (Imm_op _) None => no_prefix pre
    | _ => false
  end.

(** This predicate is defined on a pair of prefixes and instructions and
    captures the legal masked indirect jumps. *)
Definition nacljmp_mask_instr (pfx1:prefix) (ins1:instr) (pfx2:prefix) (ins2:instr) :=
  no_prefix pfx1 && no_prefix pfx2 && 
  match ins1 with
    | AND true (Reg_op r1) (Imm_op wd) => 
      zeq (Word.signed wd) (Word.signed safeMask) &&
      (if register_eq_dec r1 ESP then false else true) &&
      match ins2 with 
        | JMP true true (Reg_op r2) None => 
          if register_eq_dec r1 r2 then true else false
        | CALL true true (Reg_op r2) None => 
          if register_eq_dec r1 r2 then true else false
        | _ => false
      end
    | _ => false
  end.



Definition dfas := (make_dfa non_cflow_parser, make_dfa (alts dir_cflow), make_dfa (alts nacljmp_mask)).
(* Extraction "tables.ml" dfas.*)


