(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)


(** VerifierDFA.v:  
    This file contains definitions of the parsers used to build the DFAs
    used in FastVerifier.
*)
Require Import Coqlib.
Require Import Parser.
Require Import Recognizer.
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
Import ParserArg.X86_PARSER_ARG.
(* Import X86_PARSER. *)
(* Import X86_BASE_PARSER. *)
Require Import X86Syntax.

Definition byte2token (b: int8) : token_id := Zabs_nat (Word.unsigned b).
Definition token2byte (t: token_id) : int8 := Word.repr (Z_of_nat t).

(* In NaCl, ChunkSize is either 16 or 32 *)
Definition logChunkSize := 5%nat.
Definition chunkSize := two_power_nat logChunkSize.
Notation int8_of_nat n := (@repr 7 (Z_of_nat n)).
Definition safeMask := shl (Word.mone 7) (int8_of_nat logChunkSize).
Local Open Scope Z_scope.

Fixpoint int2bools_aux (bs : Z -> bool) (n: nat) : list bool :=
  match n with
    | O => bs 0%Z :: nil
    | S n' => bs (Z_of_nat n) :: int2bools_aux bs n'
  end.

Definition int_to_bools {s} (x: Word.int s) : list bool :=
  int2bools_aux (Word.bits_of_Z (s+1) (Word.unsigned x)) s.

Definition nat2bools(n:nat) : list bool :=
  let bs := Word.bits_of_Z 8 (Z_of_nat n) in
    ((bs 7)::(bs 6)::(bs 5)::(bs 4)::(bs 3)::(bs 2)::(bs 1)::(bs 0)::nil)%Z.

Definition make_dfa t (p:grammar t) := build_dfa (par2rec p).
Implicit Arguments make_dfa [t].

(** We mirror the definitions in Decode but only for valid, non-control-flow
    instructions below.  Instructions that are commented out are presumed *not* 
    valid.  I've been a little conservative and ruled out many systems level
    instructions, such as INS, OUTS, LODS, etc.  Still, we really ought to 
    audit this list carefully.
*)

(* this set of instructions can take prefixes in prefix_grammar_rep;
     that is, in lock_or_rep, only rep can be used;
     we put RET in this category because it turns out many binaries use
     the "rep ret" sequence to avoid branch prediction panelty in AMD processors;
     intel processor seems to just ignore the rep prefix *)
Definition valid_instr_grammars_rep :=
    (*INS_p :: OUTS_p :: *) MOVS_p :: (* LODS_p ::*) STOS_p :: (*RET_p ::*) nil.

(* this set of instructions can take prefixes in prefix_grammar_repn;
      that is, in lock_or_rep, only repn can be used *)
Definition valid_instr_grammars_rep_or_repn := 
  instr_grammars_rep_or_repn.

(* this set of instructions can take prefixes in 
     prefix_grammar_lock_with_op_override;
     that is, in lock_or_rep, only lock can be used;
     and op_override prefix *must* be used *)
Definition valid_instr_grammars_lock_with_op_override := 
  instr_grammars_lock_with_op_override.

(* this set of instructions can take prefixes in 
     prefix_grammar_lock_no_op_override;
     that is, in lock_or_rep, only lock can be used;
     and op_override prefix *must not* be used *)
Definition valid_instr_grammars_lock_no_op_override := 
  instr_grammars_lock_no_op_override.

(* this set of instructions can take prefixes in 
     prefix_grammar_seg_op_override;
     that is, it cannot take a lock_or_rep prefix, but can
     optionally take segment or op override prefix *)
Definition valid_instr_grammars_seg_op_override := 
  instr_grammars_seg_op_override.

(* this set of instructions can take only the seg_override prefix *)
Definition valid_instr_grammars_seg_override := 
    AAA_p :: AAD_p :: AAM_p :: AAS_p :: CMP_p false ::
    (* ARPL_p :: *) BOUND_p :: BSF_p :: BSR_p :: BSWAP_p :: BT_p :: 
    (* CALL_p :: *) CLC_p :: CLD_p :: CLI_p :: CLTS_p :: CMC_p :: CPUID_p :: DAA_p :: DAS_p ::
    HLT_p :: IMUL_p false :: (* IN_p :: INTn_p :: INT_p :: INTO_p :: INVD_p :: INVLPG_p :: IRET_p :: Jcc_p :: JCXZ_p :: JMP_p :: *)
    LAHF_p :: LAR_p :: (* LDS_p :: *) LEA_p :: LEAVE_p :: (* LES_p :: LFS_p :: LGDT_p ::*) LGS_p :: (* LIDT_p :: LLDT_p :: LMSW_p :: 
    LOOP_p :: LOOPZ_p :: LOOPNZ_p :: LSL_p :: LSS_p :: LTR_p :: *) MOV_p false :: MOVCR_p :: MOVDR_p :: 
    MOVSR_p :: MOVBE_p ::  (* OUT_p :: *) POP_p :: (* POPSR_p :: *) POPA_p :: POPF_p ::
    PUSH_p :: PUSHSR_p :: PUSHA_p :: PUSHF_p :: RCL_p :: RCR_p :: (* RDMSR_p :: *) RDPMC_p :: RDTSC_p :: RDTSCP_p :: 
    (* RSM_p :: *) SAHF_p :: SETcc_p :: (* SGDT_p :: SIDT_p :: *) SLDT_p :: SMSW_p :: STC_p :: STD_p :: (* STI_p :: *)
    STR_p :: TEST_p false :: (* UD2_p :: VERR_p :: VERW_p :: *) WBINVD_p :: (* WRMSR_p :: XLAT_p :: *) F2XM1_p ::
    FABS_p :: FADD_p :: FADDP_p :: FBLD_p :: FBSTP_p :: FCHS_p :: FCMOVcc_p :: FCOM_p :: FCOMP_p :: FCOMPP_p :: FCOMIP_p :: FCOS_p :: FDECSTP_p ::
    FDIV_p :: FDIVP_p :: FDIVR_p :: FDIVRP_p :: FFREE_p :: FIADD_p :: FICOM_p :: FICOMP_p :: FIDIV_p :: FIDIVR_p :: FILD_p :: FIMUL_p :: FINCSTP_p
    :: FIST_p :: FISTP_p :: FISUB_p :: FISUBR_p :: FLD_p :: FLD1_p :: FLDCW_p :: FLDENV_p :: FLDL2E_p :: FLDL2T_p :: FLDLG2_p :: FLDLN2_p
    :: FLDPI_p :: FLDZ_p :: FMUL_p :: FMULP_p :: FNCLEX_p :: FNINIT_p :: FNOP_p :: FNSAVE_p :: FNSTCW_p :: FNSTSW_p :: FPATAN_p :: FPREM_p :: FPREM1_p :: FPTAN_p :: FRNDINT_p :: FRSTOR_p :: (* FSAVE_p :: *) 
    FSCALE_p :: 
    FSIN_p :: FSINCOS_p :: FSQRT_p :: FST_p :: (* FSTCW_p :: *) FSTENV_p :: FSTP_p :: FSUB_p :: FSUBP_p :: FSUBR_p :: FSUBRP_p ::FTST_p ::
    FUCOM_p :: FUCOMP_p :: FUCOMPP_p :: FUCOMI_p :: FUCOMIP_p :: FXAM_p :: FXCH_p :: FXTRACT_p :: FYL2X_p :: FYL2XP1_p :: FWAIT_p :: 
    EMMS_p :: MOVD_p :: MOVQ_p :: PACKSSDW_p :: PACKSSWB_p :: PACKUSWB_p :: PADD_p :: PADDS_p :: PADDUS_p :: PAND_p :: PANDN_p :: PCMPEQ_p :: PCMPGT_p :: 
    PMADDWD_p :: PMULHUW_p :: PMULHW_p :: PMULLW_p :: POR_p :: PSLL_p :: PSRA_p :: PSRL_p :: PSUB_p :: PSUBS_p :: PSUBUS_p :: PUNPCKH_p :: PUNPCKL_p :: PXOR_p :: 
    ADDPS_p :: ADDSS_p :: ANDNPS_p :: ANDPS_p :: CMPPS_p :: CMPSS_p :: COMISS_p :: CVTPI2PS_p :: CVTPS2PI_p :: CVTSI2SS_p :: CVTSS2SI_p :: CVTTPS2PI_p :: CVTTSS2SI_p ::
    DIVPS_p :: DIVSS_p :: LDMXCSR_p :: MAXPS_p :: MAXSS_p :: MINPS_p :: MINSS_p :: MOVAPS_p :: MOVHLPS_p :: MOVLPS_p :: MOVMSKPS_p :: MOVSS_p :: MOVUPS_p :: MULPS_p ::
    MULSS_p :: ORPS_p :: RCPPS_p :: RCPSS_p :: RSQRTPS_p :: RSQRTSS_p :: SHUFPS_p :: SQRTPS_p :: SQRTSS_p :: STMXCSR_p :: SUBPS_p :: SUBSS_p :: UCOMISS_p :: UNPCKHPS_p ::
    UNPCKLPS_p :: XORPS_p :: PAVGB_p :: PEXTRW_p :: PINSRW_p :: PMAXSW_p :: PMAXUB_p :: PMINSW_p :: PMINUB_p :: PMOVMSKB_p :: PSADBW_p :: PSHUFW_p :: MASKMOVQ_p ::
    MOVNTPS_p :: MOVNTQ_p :: PREFETCHT0_p :: PREFETCHT1_p :: PREFETCHT2_p :: PREFETCHNTA_p :: SFENCE_p :: nil.

Definition gs_segment_override_p : grammar segment_register_t := 
"0110" $$ bits "0101" @ (fun _ => GS %% segment_register_t).

Definition valid_prefix_grammar_rep := 
  option_perm3 rep_p gs_segment_override_p op_override_p @ 
               (fun p => match p with (l, (s, op)) => 
                                      mkPrefix l s (opt2b op false) false %% prefix_t
                         end).

Definition valid_prefix_grammar_rep_or_repn :=
    option_perm3 rep_or_repn_p gs_segment_override_p op_override_p @
      (fun p => match p with (l, (s, op)) =>
                  mkPrefix l s (opt2b op false) false %% prefix_t end).

Definition valid_prefix_grammar_lock_with_op_override :=
    option_perm3_variation lock_p gs_segment_override_p op_override_p @
     (fun p => match p with (l, (s, op)) =>
                 mkPrefix l s op false %% prefix_t end).

Definition valid_prefix_grammar_lock_no_op_override :=
    option_perm2 lock_p gs_segment_override_p @
     (fun p => match p with (l, s) =>
                 mkPrefix l s false false %% prefix_t end).

Definition valid_prefix_grammar_seg_with_op_override := 
    option_perm2_variation gs_segment_override_p op_override_p @
     (fun p => match p with (s, op) =>
                 mkPrefix None s op false %% prefix_t end).

Definition valid_instr_grammars_seg_with_op_override := 
  instr_grammars_seg_with_op_override.

Definition valid_prefix_grammar_seg_op_override :=
    option_perm2 gs_segment_override_p op_override_p @
     (fun p => match p with (s, op) =>
                 mkPrefix None s (opt2b op false) false %% prefix_t end).

Definition valid_prefix_grammar_seg_override :=
    option_perm gs_segment_override_p @
     (fun s => mkPrefix None s false false %% prefix_t).

(** The list of valid prefix and instruction grammars for non-control-flow
    operations. *)
Definition non_cflow_grammar_list := 
  (List.map (fun (p:grammar instruction_t) => valid_prefix_grammar_rep $ p) 
            valid_instr_grammars_rep) ++
  (List.map (fun (p:grammar instruction_t) => valid_prefix_grammar_rep_or_repn $ p)
            valid_instr_grammars_rep_or_repn) ++
  (List.map (fun (p:grammar instruction_t) => 
               valid_prefix_grammar_lock_with_op_override $ p)
            valid_instr_grammars_lock_with_op_override) ++
  (List.map (fun (p:grammar instruction_t) => 
               valid_prefix_grammar_lock_no_op_override $ p)
            valid_instr_grammars_lock_no_op_override) ++
  (List.map (fun (p:grammar instruction_t) => 
               valid_prefix_grammar_seg_with_op_override $ p)
      valid_instr_grammars_seg_with_op_override) ++
  (List.map (fun (p:grammar instruction_t) => 
               valid_prefix_grammar_seg_op_override $ p)
      valid_instr_grammars_seg_op_override) ++
  (List.map (fun (p:grammar instruction_t) =>
               valid_prefix_grammar_seg_override $ p)
      valid_instr_grammars_seg_override).

Definition non_cflow_grammar := alts non_cflow_grammar_list.

(* Direct jumps. Destinations will be checked to see if 
   they are known, valid starts of instructions. *)

(* We only want to allow "near" jumps to direct, relative offsets *)
Definition dir_near_JMP_p : grammar instruction_t := 
    "1110" $$ "1011" $$ byte @
    (fun b => JMP true false (Imm_op (sign_extend8_32 b)) None %% instruction_t)
  |+|
    "1110" $$ "1001" $$ word @ 
    (fun w => JMP true false (Imm_op w) None %% instruction_t).

Definition dir_near_Jcc_p : grammar instruction_t :=
    "0111" $$ tttn $ byte @ 
    (fun p => let (ct,imm) := p in Jcc ct (sign_extend8_32 imm) %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "1000" $$ tttn $ word @ 
    (fun p => let (ct,imm) := p in Jcc ct imm %% instruction_t).

Definition dir_near_CALL_p : grammar instruction_t := 
   "1110" $$ "1000" $$ word  @ 
    (fun w => CALL true false (Imm_op w) None %% instruction_t).

Definition dir_cflow : list (grammar instruction_t) :=
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
  end%nat.

(* Lemma register_to_Z_identity1: forall r:register, Z_to_register (register_to_Z r) = r. *)
(* Proof. destruct r; auto. *)
(* Qed.  *)

Definition register_to_bools (r: register) :=
  let bs := Word.bits_of_Z 3 (Z_of_nat (register_to_Z r)) in
    ((bs 2) :: (bs 1) :: (bs 0) :: nil)%Z.

Fixpoint bitslist (bs: list bool) : grammar Unit_t :=
  match bs with
    | nil => Eps
    | b::bs' => Cat (Char b) (bitslist bs') @ (fun _ => tt %% Unit_t)
  end.

Definition nacl_MASK_p (r: register) : grammar instruction_t :=
      "1000" $$ "0011" $$ "11" $$ bits "100"    (* AND opcode for Imm to register*)
    $ bitslist (register_to_bools r)             (* Register *)
    $ bitslist (int_to_bools safeMask)
    @ (fun _ => AND true (Reg_op r) (Imm_op (sign_extend8_32 safeMask))
      %% instruction_t).

(* This should give a grammar corresponding to (JMP true true (Reg_op
   reg) None. Note that ESP cannot be passed as a register here since
   the bit pattern for ESP is used as a special mode for the rm00 *)

Definition nacl_JMP_p  (r: register) : grammar instruction_t :=
      "1111" $$ "1111" $$ "11" $$ bits "100"
    $ bitslist (register_to_bools r)  @ 
    (fun _ =>  JMP true true (Reg_op r) None %% instruction_t).

Definition nacl_CALL_p (r: register) : grammar instruction_t :=
      "1111" $$ "1111" $$ "11" $$ bits "010"
    $ bitslist (register_to_bools r)  @ 
    (fun _ => CALL true true (Reg_op r) None %% instruction_t).

Definition nacljmp_p (r: register) : grammar (Pair_t instruction_t instruction_t) :=
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
Definition nacljmp_mask : list (grammar (Pair_t instruction_t instruction_t)) := 
  nacljmp_p EAX :: nacljmp_p ECX :: nacljmp_p EDX :: nacljmp_p EBX ::
  nacljmp_p EBP :: nacljmp_p ESI :: nacljmp_p EDI :: nil.

Fixpoint parseloop ps bytes := 
  match bytes with 
    | nil => None
    | b::bs => match parse_byte ps b with 
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
    that the [non_cflow_grammar] only builds instructions that satisfy this
    predicate (as shown below.)  Furthermore, we should be able to argue
    that for each of these instructions, the NaCL SFI invariants are preserved. 
*)
Definition no_imm_op(op1:operand) : bool := 
  match op1 with 
    | Imm_op _ => false
    | _ => true
  end.

Definition no_mmx_imm_op(op1:mmx_operand) : bool := 
  match op1 with 
    | MMX_Imm_op _ => false
    | _ => true
  end.

Definition no_sse_imm_op(op1:sse_operand) : bool := 
  match op1 with 
    | SSE_Imm_op _ => false
    | _ => true
  end.

Definition filter_prefix
   (lr_ft: option lock_or_rep -> bool) (* filter on lock-or-rep prefix *) 
   (seg_ft: option segment_register -> bool) (* filter on segment_override prefix *) 
   (op_ft: bool -> bool) (* filter on op_override prefix *)
   (addr_ft: bool -> bool) (* filter on addr_override prefix *)
   (p: prefix) :=
  lr_ft (lock_rep p) && seg_ft (seg_override p) && 
  op_ft (op_override p) && addr_ft (addr_override p).

Definition ft_no_lock_or_rep (lro: option lock_or_rep) := 
  match lro with
    | None => true
    | _ => false
  end.

Definition ft_only_lock (lro: option lock_or_rep) := 
  match lro with
    | Some lock => true
    | None => true
    | _ => false
  end.

Definition ft_only_rep (lro: option lock_or_rep) := 
  match lro with
    | Some rep => true
    | None => true
    | _ => false
  end.

Definition ft_rep_or_repn (lro: option lock_or_rep) := 
  match lro with
    | Some rep | Some repn | None => true
    | _ => false
  end.

Definition ft_lock_or_rep_wildcard (lro: option lock_or_rep) := true.

Definition ft_no_seg (so: option segment_register) :=
  match so with
    | None => true
    | _ => false
  end.

Definition ft_only_gs_seg (so: option segment_register) :=
  match so with
    | Some GS => true
    | None => true
    | _ => false
  end.

Definition ft_bool_yes (b:bool) := b.
Definition ft_bool_no (b:bool) := negb b.
Definition ft_bool_wildcard (b:bool) := true.


Definition no_prefix : prefix -> bool := 
  filter_prefix ft_no_lock_or_rep ft_no_seg ft_bool_no ft_bool_no.

Definition only_op_override: prefix -> bool := 
  filter_prefix ft_no_lock_or_rep ft_no_seg ft_bool_wildcard ft_bool_no.

Definition only_seg_or_op: prefix -> bool := 
  filter_prefix ft_no_lock_or_rep ft_only_gs_seg ft_bool_wildcard ft_bool_no.

Definition only_gs_seg_override: prefix -> bool := 
  filter_prefix ft_no_lock_or_rep ft_only_gs_seg ft_bool_no ft_bool_no.

Definition rep_or_gs_or_op_prefix: prefix -> bool := 
  filter_prefix ft_only_rep ft_only_gs_seg ft_bool_wildcard ft_bool_no.

Definition rep_or_repn_or_gs_or_op_prefix: prefix -> bool :=
  filter_prefix ft_rep_or_repn ft_only_gs_seg ft_bool_wildcard ft_bool_no.
  
Definition lock_or_gs_without_op: prefix -> bool := 
  filter_prefix ft_only_lock ft_only_gs_seg ft_bool_no ft_bool_no.

Definition lock_or_gs_or_op: prefix -> bool := 
  filter_prefix ft_only_lock ft_only_gs_seg ft_bool_wildcard ft_bool_no.


Definition non_cflow_instr (pfx:prefix) (ins:instr) : bool := 
  match ins with 
    (* valid_instr_grammars_rep *)
    | MOVS w => rep_or_gs_or_op_prefix pfx
    | STOS w => rep_or_gs_or_op_prefix pfx
    (* valid_instr_grammars_rep_or_repn *)
    | CMPS w => rep_or_repn_or_gs_or_op_prefix pfx

    (* G.T.: the machine raises error (not trap) when there is no semantics for
       instructions such as SCAS; same for BOUND, CLI, CLTS, CPUID, LAR, LGS,
       MOVCR, MOVDR, MOVSR, MOVBE, POPF, PUSHSR, PUSHF, RDMSR, RDPMC, RDTSC, 
       RDTSCP, RSM, SGDT, SIDT, SLDT, SMSW, STI, STR, WBINVD *)
    (* | SCAS w => rep_or_repn_or_gs_or_op_prefix pfx *)

    (* valid_instr_grammars_lock_with_op_override *)
    | ADD w op1 op2 => 
      no_imm_op op1 && lock_or_gs_or_op pfx
    | ADC w op1 op2 => 
      no_imm_op op1 && lock_or_gs_or_op pfx
    | AND w op1 op2 => 
      no_imm_op op1 && lock_or_gs_or_op pfx
    | NEG w op1 => 
      no_imm_op op1 && lock_or_gs_or_op pfx
    | NOT w op1 => 
      no_imm_op op1 && lock_or_gs_or_op pfx
    | OR w op1 op2 => 
      no_imm_op op1 && lock_or_gs_or_op pfx
    | SBB w op1 op2 => 
      no_imm_op op1 && lock_or_gs_or_op pfx
    | SUB w op1 op2 => 
      no_imm_op op1 && lock_or_gs_or_op pfx
    | XOR w op1 op2 => 
      no_imm_op op1 && lock_or_gs_or_op pfx
    | XCHG w op1 op2 => 
      no_imm_op op1 && no_imm_op op2 && lock_or_gs_or_op pfx
    (* valid_instr_grammars_lock_no_op_override *)
    (* covered by above: 
    | ADD false op1 op2 => lock_or_gs_without_op pfx && no_imm_op op1
    | ADC false op1 op2 => lock_or_gs_without_op pfx && no_imm_op op1
    | AND false op1 op2 => lock_or_gs_without_op pfx && no_imm_op op1
    *)
    | BTC op1 op2 => lock_or_gs_without_op pfx && no_imm_op op1
    | BTR op1 op2 => lock_or_gs_without_op pfx && no_imm_op op1
    | BTS op1 op2 => lock_or_gs_without_op pfx && no_imm_op op1
    | CMPXCHG w op1 op2 => lock_or_gs_without_op pfx && no_imm_op op1
    | DEC w op1 => lock_or_gs_without_op pfx && no_imm_op op1
    | INC w op1 => lock_or_gs_without_op pfx && no_imm_op op1
    (* covered by above:                                         
    | OR false op1 op2 => lock_or_gs_without_op pfx && no_imm_op op1
    | SBB false op1 op2 => lock_or_gs_without_op pfx && no_imm_op op1
    | SUB false op1 op2 => lock_or_gs_without_op pfx && no_imm_op op1
    | XOR false op1 op2 => lock_or_gs_without_op pfx && no_imm_op op1
    *)
    | XADD w op1 op2 => lock_or_gs_without_op pfx && no_imm_op op1 && no_imm_op op2
    (* valid_instr_grammars_only_seg_or_op_override *)
    (* Similar issue with ADD above for CMP, IMUL, MOV, and TEST. *)
    | CMP w op1 op2 => only_seg_or_op pfx 
    | IMUL w op1 opopt iopt => only_seg_or_op pfx  && no_imm_op op1
    | MOV w op1 op2 => only_seg_or_op pfx && no_imm_op op1
    | TEST w op1 op2 => only_seg_or_op pfx
    (* valid_instr_grammars_seg_op_override *) 
    | CDQ => only_seg_or_op pfx 
    | CMOVcc ct op1 op2 =>  only_seg_or_op pfx && no_imm_op op1
    | CWDE => only_seg_or_op pfx
    | DIV w op1 => only_seg_or_op pfx && no_imm_op op1
    | IDIV w op1 => only_seg_or_op pfx && no_imm_op op1
    | MOVSX w op1 op2 => only_seg_or_op pfx && no_imm_op op1
    | MOVZX w op1 op2 => only_seg_or_op pfx && no_imm_op op1
    | MUL w op1 => only_seg_or_op pfx && no_imm_op op1
    | NOP op1 => only_seg_or_op pfx && no_imm_op op1
    | ROL w op1 ri => only_seg_or_op pfx && no_imm_op op1
    | ROR w op1 ri => only_seg_or_op pfx && no_imm_op op1
    | SAR w op1 ri => only_seg_or_op pfx && no_imm_op op1
    | SHL w op1 ri => only_seg_or_op pfx && no_imm_op op1
    | SHLD op1 r ri => only_seg_or_op pfx && no_imm_op op1
    | SHR w op1 ri => only_seg_or_op pfx && no_imm_op op1
    | SHRD op1 op2 ri => only_seg_or_op pfx && no_imm_op op1
    (* valid_instr_grammars_seg_override -- just gs segment override *)
    | AAA => only_gs_seg_override pfx
    | AAD => only_gs_seg_override pfx
    | AAM => only_gs_seg_override pfx
    | AAS => only_gs_seg_override pfx
    (* | BOUND op1 op2 => only_gs_seg_override pfx && no_imm_op op1 *)
    | BSF op1 op2 => only_gs_seg_override pfx && no_imm_op op1
    | BSR op1 op2 => only_gs_seg_override pfx && no_imm_op op1
    | BSWAP r => only_gs_seg_override pfx
    | BT op1 op2 => only_gs_seg_override pfx && no_imm_op op1
    | CLC => only_gs_seg_override pfx
    | CLD => only_gs_seg_override pfx
    (* | CLI => only_gs_seg_override pfx *)
    (* | CLTS => only_gs_seg_override pfx *)
    | CMC => only_gs_seg_override pfx
    (* | CPUID => only_gs_seg_override pfx *)
    | DAA => only_gs_seg_override pfx
    | DAS => only_gs_seg_override pfx
    | HLT => only_gs_seg_override pfx
    (* | IMUL false op1 opopt iopt => only_gs_seg_override pfx (* FIX? *) *)
    | LAHF => only_gs_seg_override pfx
    (* | LAR op1 op2 => only_gs_seg_override pfx && no_imm_op op1 *)
    (* G.T.:  The decoder allows only Address_op in the second operand *)
    | LEA op1 (Address_op a) => only_gs_seg_override pfx && no_imm_op op1
    | LEAVE => only_gs_seg_override pfx
    (* | LGS op1 op2 => only_gs_seg_override pfx && no_imm_op op1 *)
    (* | MOV false op1 op2 => only_seg_or_op pfx && no_imm_op op1 *)
    (* | MOVCR direction cr r => only_gs_seg_override pfx *)
    (* | MOVDR direction dr r => only_gs_seg_override pfx *)
    (* | MOVSR direction sr r => only_gs_seg_override pfx *)
    (* | MOVBE op1 op2 => only_gs_seg_override pfx && no_imm_op op1 *)
    | POP op1 => only_gs_seg_override pfx && no_imm_op op1
    | POPA => only_gs_seg_override pfx  
    (* | POPF => only_gs_seg_override pfx   *)
    | PUSH w op1 => only_gs_seg_override pfx
    | PUSHA => only_gs_seg_override pfx 
    (* | PUSHSR sr => only_gs_seg_override pfx   *)
    (* | PUSHF => only_gs_seg_override pfx   *)
    | RCL w op1 ri => only_gs_seg_override pfx && no_imm_op op1
    | RCR w op1 ri => only_gs_seg_override pfx && no_imm_op op1

    (* | RDMSR => only_gs_seg_override pfx   *)
    (* | RDPMC => only_gs_seg_override pfx   *)
    (* | RDTSC => only_gs_seg_override pfx   *)
    (* | RDTSCP => only_gs_seg_override pfx   *)
    (* | RSM => only_gs_seg_override pfx   *)

    | SAHF => only_gs_seg_override pfx
    | SETcc ct op1 => only_gs_seg_override pfx && no_imm_op op1

    (* | SGDT op1 => only_gs_seg_override pfx  *)
    (* | SIDT op1 => only_gs_seg_override pfx  *)
    (* | SLDT op1 => only_gs_seg_override pfx  *)
    (* | SMSW op1 => only_gs_seg_override pfx  *)

    | STC => only_gs_seg_override pfx 
    | STD => only_gs_seg_override pfx 

    (* | STI => only_gs_seg_override pfx  *)
    (* | STR op1 => only_gs_seg_override pfx  *)
    (* | TEST false op1 op2 => only_gs_seg_override pfx *)
    (* | WBINVD => only_gs_seg_override pfx  *)

    (* G.T.: the model raises errors when FPU/MMX instructions are encourntered;
       to show the execution of a binary doesn't raise errors, we have to comment
       these cases out from the checker *)
    (* | F2XM1 => only_gs_seg_override pfx  *)
    (* | FABS => only_gs_seg_override pfx  *)
    (* | FADD zerod op1 => only_gs_seg_override pfx  *)
    (* | FADDP op1 => only_gs_seg_override pfx  *)
    (* | FBLD op1 => only_gs_seg_override pfx  *)
    (* | FBSTP op1 => only_gs_seg_override pfx  *)
    (* | FCHS => only_gs_seg_override pfx  *)
    (* | FCMOVcc ct op1 => only_gs_seg_override pfx  *)
    (* | FCOM op1 => only_gs_seg_override pfx  *)
    (* | FCOMP op1 => only_gs_seg_override pfx  *)
    (* | FCOMPP => only_gs_seg_override pfx  *)
    (* | FCOMIP op1 => only_gs_seg_override pfx  *)
    (* | FCOS => only_gs_seg_override pfx  *)
    (* | FDECSTP => only_gs_seg_override pfx  *)
    (* | FDIV zerod op1 => only_gs_seg_override pfx  *)
    (* | FDIVP op1 => only_gs_seg_override pfx  *)
    (* | FDIVR zerod op1 => only_gs_seg_override pfx  *)
    (* | FDIVRP op1 => only_gs_seg_override pfx  *)
    (* | FFREE op1 => only_gs_seg_override pfx  *)
    (* | FIADD op1 => only_gs_seg_override pfx  *)
    (* | FICOM op1 => only_gs_seg_override pfx  *)
    (* | FICOMP op1 => only_gs_seg_override pfx  *)
    (* | FIDIV op1 => only_gs_seg_override pfx  *)
    (* | FIDIVR op1 => only_gs_seg_override pfx  *)
    (* | FILD op1 => only_gs_seg_override pfx  *)
    (* | FIMUL op1 => only_gs_seg_override pfx  *)
    (* | FINCSTP => only_gs_seg_override pfx  *)
    (* | FIST op1 => only_gs_seg_override pfx  *)
    (* | FISTP op1 => only_gs_seg_override pfx  *)
    (* | FISUB op1 => only_gs_seg_override pfx  *)
    (* | FISUBR op1 => only_gs_seg_override pfx  *)
    (* | FLD op1 => only_gs_seg_override pfx  *)
    (* | FLD1 => only_gs_seg_override pfx  *)
    (* | FLDCW op1 => only_gs_seg_override pfx  *)
    (* | FLDENV op1 => only_gs_seg_override pfx  *)
    (* | FLDL2E => only_gs_seg_override pfx  *)
    (* | FLDL2T => only_gs_seg_override pfx  *)
    (* | FLDLG2 => only_gs_seg_override pfx  *)
    (* | FLDLN2 => only_gs_seg_override pfx  *)
    (* | FLDPI => only_gs_seg_override pfx  *)
    (* | FLDZ => only_gs_seg_override pfx  *)
    (* | FMUL zerod op1 => only_gs_seg_override pfx  *)
    (* | FMULP op1 => only_gs_seg_override pfx *)
    (* | FNCLEX => only_gs_seg_override pfx  *)
    (* | FNINIT => only_gs_seg_override pfx  *)
    (* | FNOP => only_gs_seg_override pfx  *)
    (* | FNSAVE op1 => only_gs_seg_override pfx  *)
    (* | FNSTCW op1 => only_gs_seg_override pfx  *)
    (* | FNSTSW op1 => only_gs_seg_override pfx  *)
    (* | FPATAN => only_gs_seg_override pfx  *)
    (* | FPREM => only_gs_seg_override pfx  *)
    (* | FPREM1 => only_gs_seg_override pfx  *)
    (* | FPTAN => only_gs_seg_override pfx *)
    (* | FRNDINT => only_gs_seg_override pfx  *)
    (* | FRSTOR op1 => only_gs_seg_override pfx  *)
    (* | FSCALE => only_gs_seg_override pfx  *)
    (* | FSIN => only_gs_seg_override pfx  *)
    (* | FSINCOS => only_gs_seg_override pfx  *)
    (* | FSQRT => only_gs_seg_override pfx  *)
    (* | FST op1 => only_gs_seg_override pfx  *)
    (* | FSTENV op1 => only_gs_seg_override pfx  *)
    (* | FSTP op1 => only_gs_seg_override pfx  *)
    (* | FSUB zerod op1 => only_gs_seg_override pfx  *)
    (* | FSUBP op1 => only_gs_seg_override pfx  *)
    (* | FSUBR zerod op1 => only_gs_seg_override pfx  *)
    (* | FSUBRP op1 => only_gs_seg_override pfx  *)
    (* | FTST => only_gs_seg_override pfx  *)
    (* | FUCOM op1 => only_gs_seg_override pfx  *)
    (* | FUCOMP op1 => only_gs_seg_override pfx  *)
    (* | FUCOMPP => only_gs_seg_override pfx  *)
    (* | FUCOMI op1 => only_gs_seg_override pfx  *)
    (* | FUCOMIP op1 => only_gs_seg_override pfx  *)
    (* | FXAM => only_gs_seg_override pfx  *)
    (* | FXCH op1 => only_gs_seg_override pfx  *)
    (* | FXTRACT => only_gs_seg_override pfx  *)
    (* | FYL2X => only_gs_seg_override pfx  *)
    (* | FYL2XP1 => only_gs_seg_override pfx  *)
    (* | FWAIT => only_gs_seg_override pfx  *)
    (* | EMMS => only_gs_seg_override pfx  *)
    (* | MOVD op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | MOVQ op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PACKSSDW op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PACKSSWB op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PACKUSWB op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PADD gg op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PADDS gg op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PADDUS gg op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PAND op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PANDN op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PCMPEQ gg op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PCMPGT gg op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PMADDWD op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PMULHUW op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PMULHW op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PMULLW op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | POR op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PSLL gg op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PSRA gg op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PSRL gg op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PSUB gg op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PSUBS gg op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PSUBUS gg op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PUNPCKH gg op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PUNPCKL gg op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | PXOR op1 op2 => only_gs_seg_override pfx && no_mmx_imm_op op1 *)
    (* | ADDPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | ADDSS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | ANDNPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | ANDPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | CMPPS op1 op2 imm => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | CMPSS op1 op2 imm => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | COMISS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | CVTPI2PS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | CVTPS2PI op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | CVTSI2SS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | CVTSS2SI op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | CVTTPS2PI op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | CVTTSS2SI op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | DIVPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | DIVSS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | LDMXCSR op1 => only_gs_seg_override pfx  *)
    (* | MAXPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MAXSS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MINPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MINSS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MOVAPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MOVHLPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MOVLPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MOVMSKPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MOVSS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MOVUPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MULPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MULSS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | ORPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | RCPPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | RCPSS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | RSQRTPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | RSQRTSS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | SHUFPS op1 op2 imm => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | SQRTPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | SQRTSS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | STMXCSR op1 => only_gs_seg_override pfx *)
    (* | SUBPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | SUBSS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | UCOMISS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | UNPCKHPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | UNPCKLPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | XORPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | PAVGB op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | PEXTRW op1 op2 imm => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | PINSRW op1 op2 imm => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | PMAXSW op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | PMAXUB op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | PMINSW op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | PMINUB op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | PMOVMSKB op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | PSADBW op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | PSHUFW op1 op2 imm => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MASKMOVQ op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MOVNTPS op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | MOVNTQ op1 op2 => only_gs_seg_override pfx && no_sse_imm_op op1 *)
    (* | PREFETCHT0 op1 => only_gs_seg_override pfx  *)
    (* | PREFETCHT1 op1 => only_gs_seg_override pfx  *)
    (* | PREFETCHT2 op1 => only_gs_seg_override pfx  *)
    (* | PREFETCHNTA op1 => only_gs_seg_override pfx  *)
    (* | SFENCE => only_gs_seg_override pfx  *)

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

Definition make_recognizer t (g:grammar t) := 
  Recognizer.build_dfa (par2rec g).

Definition dfas := (make_recognizer non_cflow_grammar, make_recognizer (alts dir_cflow), make_recognizer (alts nacljmp_mask)).
(* Extraction "tables.ml" dfas.*)


