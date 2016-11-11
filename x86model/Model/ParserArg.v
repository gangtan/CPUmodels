Require Export Coq.Bool.Bool.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List.

Require Import Coq.Strings.String.
Require Import Coq.Structures.OrdersAlt.

Module Type PARSER_ARG.
  (* the type of characters used in the grammar specifications *)
  Parameter char_p : Set.
  (* equality on characters -- should change this to a boolean function,
     paired with a proof that it's an equality so that
     we get faster symbolic computation. *)
  Parameter char_dec : forall (c1 c2:char_p), {c1=c2} + {c1<>c2}.
  
  (* compare two chars *)
  Parameter char_cmp : char_p -> char_p -> comparison.
  Parameter char_eq_leibniz :
    forall c1 c2, char_cmp c1 c2 = Eq -> c1 = c2.

  (* a name for user types embedded within our AST grammar types. *)
  Parameter user_type : Set.
  (* equality on user type names. *)
  Parameter user_type_dec : forall (t1 t2:user_type), {t1=t2} + {t1<>t2}.
  (* a semantic interpretation function for user type names. *)
  Parameter user_type_denote : user_type -> Set.

  (* when we parse, instead of working in terms of individual characters,
     we work in terms of tokens.   For instance, the x86 grammar is specified
     with characters as bits, and tokens as bytes (8-bits). *)
  Definition token_id := nat.
  (* this is the total number of tokens that we can have -- e.g., for the
     x86 parser it is 256 because they have 8 bits. *)
  Variable num_tokens : nat.
  (* this converts tokens to a list of characters -- it's used only during
     the table construction for the parser. *)
  Variable token_id_to_chars : token_id -> list char_p.

  (* converts a char to a string *)
  Parameter show_char: char_p -> string.

End PARSER_ARG.


(* a module for generating the parser for x86 instructions *)
Module X86_PARSER_ARG.
  Require Import X86Syntax.
  Require Import Bits.
  Local Open Scope Z_scope.

  Definition char_p : Set := bool.

  Definition char_dec : forall (c1 c2:char_p), {c1=c2}+{c1<>c2} := bool_dec.

  Definition char_cmp (c1 c2:char_p) : comparison :=
    match c1, c2 with
      | false, true => Lt
      | true, false => Gt
      | _, _ => Eq
    end.

  Lemma char_eq_leibniz :
    forall c1 c2, char_cmp c1 c2 = Eq -> c1 = c2.
  Proof.
    destruct c1 ; destruct c2 ; intros  ; auto ; discriminate.
  Qed.

  (** Hierarchical instruction syntax. The problem with a parser mapping
      directly to instr is that the current instr syntax is flat with more
      than 350 cases. A bidirectional grammar for instr would need to
      construct an AST with many cases and Coq runs out of mem during the
      proof search (even with the help of the abstract tactical).
   
      So we introduce an hierarhical instruction syntax as an intermiary for
      coping with the scability issue.
   *)

  (** This set of integer instructions
     - take no parameters
     - take only the seg_override prefix *)
  Inductive i_instr1 : Set :=
  | I_AAA
  | I_AAD 
  | I_AAM 
  | I_AAS 
  | I_CLC 
  | I_CLD 
  | I_CLI 
  | I_CLTS 
  | I_CMC
  | I_CPUID 
  | I_DAA 
  | I_DAS
  | I_HLT  
  | I_INT
  | I_INTO
  | I_INVD
  | I_IRET
  | I_LAHF
  | I_LEAVE
  | I_POPA 
  | I_POPF
  | I_PUSHA
  | I_PUSHF
  | I_RDMSR
  | I_RDPMC
  | I_RDTSC
  | I_RDTSCP
  | I_RSM
  | I_SAHF
  | I_STC
  | I_STD
  | I_STI
  | I_UD2
  | I_WBINVD
  | I_WRMSR
  | I_XLAT.

  (** This set of integer instructions
     - take some parameters
     - take only the seg_override prefix
     - first letter of name in A-L *)
  Inductive i_instr2 : Set :=
  | I_ARPL (op1 op2:operand)
  | I_BOUND (op1 op2:operand)
  | I_BSF (op1 op2:operand)
  | I_BSR (op1 op2:operand)
  | I_BSWAP (r:register)
  | I_BT (op1 op2:operand)
  | I_CALL (near:bool)(absolute: bool)(op1:operand)(sel:option selector)
  | I_IN (w:bool)(p: option port_number)
  | I_INTn (it:interrupt_type)
  | I_INVLPG (op1:operand)
  | I_Jcc (ct:condition_type)(disp:int32)
  | I_JCXZ (b:int8)
  | I_JMP (near:bool)(absolute:bool)(op1: operand)(sel:option selector)
  | I_LAR (op1 op2:operand)
  | I_LDS (op1 op2:operand)
  | I_LEA (op1 op2:operand)
  | I_LES (op1 op2:operand)
  | I_LFS (op1 op2:operand)
  | I_LGDT (op1:operand)
  | I_LGS (op1 op2:operand)
  | I_LIDT (op1:operand)
  | I_LLDT (op1:operand)
  | I_LMSW (op1:operand)
  | I_LOOP (disp:int8)
  | I_LOOPZ (disp:int8)
  | I_LOOPNZ (disp:int8)
  | I_LSL  (op1 op2:operand)
  | I_LSS (op1 op2:operand)
  | I_LTR (op1:operand).

  (** This set of integer instructions
     - take some parameters
     - take only the seg_override prefix
     - first letter of name in M-Z *)
  Inductive i_instr3 : Set :=
  | I_MOVCR (direction:bool)(cr:control_register)(r:register)
  | I_MOVDR (direction:bool)(dr:debug_register)(r:register)
  | I_MOVSR (direction:bool)(sr:segment_register)(op1:operand)
  | I_MOVBE (op1 op2:operand)
  | I_OUT (w:bool)(p:option port_number)
  | I_POP (op1:operand)
  | I_POPSR (sr:segment_register)
  | I_PUSH (w:bool)(op1:operand)
  | I_PUSHSR (sr:segment_register)
  | I_RCL (w:bool)(op1:operand)(ri:reg_or_immed)
  | I_RCR (w:bool)(op1:operand)(ri:reg_or_immed)
  | I_SETcc (ct:condition_type)(op1:operand)
  | I_SGDT (op1:operand)
  | I_SIDT (op1:operand)
  | I_SLDT (op1:operand)
  | I_SMSW (op1:operand)
  | I_STR (op1:operand)
  | I_VERR (op1:operand)
  | I_VERW (op1:operand).

  (** These integer instructions can take prefixes in prefix_grammar_rep, 
      or prefix_grammar_repn. *)
  Inductive i_instr4 : Set :=
  (* the following can take prefixes in prefix_grammar_rep *)
  | I_INS (w:bool)
  | I_OUTS (w:bool)
  | I_MOVS (w:bool)
  | I_LODS (w:bool)
  | I_STOS (w:bool)
  | I_RET (same_segment:bool)(disp:option int16)
  (* the following can take prefixes in prefix_grammar_repn *)
  | I_CMPS (w:bool)
  | I_SCAS (w:bool).

  (** This set of instructions can take prefixes in 
      prefix_grammar_seg_with_op_override, prefix_grammar_lock_no_op_override,
      or prefix_grammar_lock_with_op_override *)
  Inductive i_instr5 : Set := 
  | I_ADC (w:bool)(op1 op2:operand)
  | I_ADD (w:bool)(op1 op2:operand)
  | I_AND (w:bool)(op1 op2:operand)
  | I_BTC (op1 op2:operand)
  | I_BTR (op1 op2:operand)
  | I_BTS (op1 op2:operand)
  | I_CMP (w:bool)(op1 op2:operand)
  | I_CMPXCHG (w:bool)(op1 op2:operand)
  | I_DEC (w:bool)(op1:operand)
  | I_IMUL (w:bool)(op1:operand) (opopt: option operand) (iopt:option int32)
  | I_INC (w:bool)(op1:operand)
  | I_MOV (w:bool)(op1 op2:operand)
  | I_NEG (w:bool)(op:operand)
  | I_NOT (w:bool)(op:operand)
  | I_OR (w:bool)(op1 op2:operand)
  | I_SBB (w:bool)(op1 op2:operand)
  | I_SUB (w:bool)(op1 op2:operand)
  | I_TEST (w:bool)(op1 op2:operand)
  | I_XADD (w:bool)(op1 op2:operand)
  | I_XCHG (w:bool)(op1 op2:operand)
  | I_XOR (w:bool)(op1 op2:operand).

  (** this set of instructions can take prefixes in prefix_grammar_seg_op_override *)
  Inductive i_instr6 : Set := 
  | I_CDQ
  | I_CMOVcc (ct:condition_type)(op1 op2: operand)
  | I_CWDE 
  | I_DIV (w:bool)(op1:operand)
  | I_IDIV (w:bool)(op1:operand)
  | I_MOVSX (w:bool)(op1 op2:operand)
  | I_MOVZX (w:bool)(op1 op2:operand)
  | I_MUL (w:bool)(op1:operand)
  | I_NOP (op:operand)
  | I_ROL (w:bool)(op1:operand)(ri:reg_or_immed)
  | I_ROR (w:bool)(op1:operand)(ri:reg_or_immed)
  | I_SAR (w:bool)(op1:operand)(ri:reg_or_immed)
  | I_SHL (w:bool)(op1:operand)(ri:reg_or_immed)
  | I_SHLD (op1:operand)(r:register)(ri:reg_or_immed)
  | I_SHR (w:bool)(op1:operand)(ri:reg_or_immed)
  | I_SHRD (op1:operand)(r:register)(ri:reg_or_immed).

  (** the first set of floating-point instrs *)
  Inductive f_instr1 : Set :=
  | F_F2XM1
  | F_FABS
  | F_FADD (zerod: bool) (op1: fp_operand)
  | F_FADDP (op1: fp_operand)
  | F_FBLD (op1: fp_operand)
  | F_FBSTP (op1: fp_operand)
  | F_FCHS
  | F_FCMOVcc (ct:fp_condition_type)(op1: fp_operand)
  | F_FCOM (op1: fp_operand)
  | F_FCOMP (op1: fp_operand)
  | F_FCOMPP
  | F_FCOMIP (op1: fp_operand)
  | F_FCOS
  | F_FDECSTP
  | F_FDIV (zerod: bool) (op: fp_operand)
  | F_FDIVP (op1: fp_operand)
  | F_FDIVR (zerod: bool) (op: fp_operand)
  | F_FDIVRP (op1: fp_operand)
  | F_FFREE (op1: fp_operand)
  | F_FIADD (op1: fp_operand)
  | F_FICOM (op1: fp_operand)
  | F_FICOMP (op1: fp_operand)
  | F_FIDIV (op1: fp_operand)
  | F_FIDIVR (op1: fp_operand)
  | F_FILD (op1: fp_operand)
  | F_FIMUL (op1: fp_operand)
  | F_FINCSTP
  | F_FIST (op1: fp_operand)
  | F_FISTP (op1: fp_operand)
  | F_FISUB (op1: fp_operand)
  | F_FISUBR (op1: fp_operand)
  | F_FLD (op1: fp_operand)
  | F_FLD1
  | F_FLDCW (op1: fp_operand)
  | F_FLDENV (op1: fp_operand)
  | F_FLDL2E
  | F_FLDL2T
  | F_FLDLG2
  | F_FLDLN2
  | F_FLDPI
  | F_FLDZ
  | F_FMUL (zerod: bool) (op1: fp_operand)
  | F_FMULP (op1: fp_operand).

  Inductive f_instr2 : Set :=
  | F_FNCLEX
  | F_FNINIT
  | F_FNOP
  | F_FNSAVE (op1: fp_operand)
  | F_FNSTCW (op1 : fp_operand)
  | F_FNSTSW (op1 : option fp_operand)
  | F_FPATAN
  | F_FPREM
  | F_FPREM1
  | F_FPTAN
  | F_FRNDINT
  | F_FRSTOR (op1: fp_operand)
  | F_FSCALE
  | F_FSIN
  | F_FSINCOS
  | F_FSQRT
  | F_FST (op1: fp_operand)
  | F_FSTENV (op1: fp_operand)
  | F_FSTP (op1: fp_operand)
  | F_FSUB (zerod: bool) (op: fp_operand)
  | F_FSUBP (op1: fp_operand)
  | F_FSUBR (zerod: bool) (op: fp_operand)
  | F_FSUBRP (op1: fp_operand)
  | F_FTST
  | F_FUCOM (op1: fp_operand)
  | F_FUCOMP (op1: fp_operand)
  | F_FUCOMPP
  | F_FUCOMI (op1: fp_operand)
  | F_FUCOMIP (op1: fp_operand)
  | F_FXAM
  | F_FXCH (op1: fp_operand)
  | F_FXTRACT
  | F_FYL2X
  | F_FYL2XP1
  | F_FWAIT.

  (** mmx instructions *)
  Inductive m_instr : Set :=
  | M_EMMS
  | M_MOVD (op1 op2: mmx_operand)
  | M_MOVQ (op1 op2: mmx_operand)
  | M_PACKSSDW (op1 op2: mmx_operand)
  | M_PACKSSWB (op1 op2: mmx_operand)
  | M_PACKUSWB (op1 op2: mmx_operand)
  | M_PADD (gg:mmx_granularity) (op1 op2: mmx_operand)
  | M_PADDS (gg:mmx_granularity) (op1 op2: mmx_operand)
  | M_PADDUS (gg:mmx_granularity) (op1 op2: mmx_operand)
  | M_PAND (op1 op2 : mmx_operand)
  | M_PANDN (op1 op2 : mmx_operand)
  | M_PCMPEQ (gg:mmx_granularity) (op1 op2 : mmx_operand)
  | M_PCMPGT (gg:mmx_granularity) (op1 op2 : mmx_operand)
  | M_PMADDWD (op1 op2 : mmx_operand)
  | M_PMULHUW (op1 op2 : mmx_operand)
  | M_PMULHW (op1 op2 : mmx_operand)
  | M_PMULLW (op1 op2 : mmx_operand)
  | M_POR (op1 op2 : mmx_operand)
  | M_PSLL (gg:mmx_granularity) (op1 op2: mmx_operand)
  | M_PSRA (gg:mmx_granularity) (op1 op2: mmx_operand)
  | M_PSRL (gg:mmx_granularity) (op1 op2: mmx_operand)
  | M_PSUB (gg:mmx_granularity) (op1 op2: mmx_operand)
  | M_PSUBS (gg:mmx_granularity) (op1 op2: mmx_operand)
  | M_PSUBUS (gg:mmx_granularity) (op1 op2: mmx_operand)
  | M_PUNPCKH (gg:mmx_granularity) (op1 op2: mmx_operand)
  | M_PUNPCKL (gg:mmx_granularity) (op1 op2: mmx_operand)
  | M_PXOR (op1 op2 : mmx_operand).

  (** sse instructions *)
  Inductive s_instr1 : Set :=
  | S_ADDPS (op1 op2: sse_operand)
  | S_ADDSS (op1 op2: sse_operand)
  | S_ANDNPS (op1 op2: sse_operand)
  | S_ANDPS (op1 op2: sse_operand)
  | S_CMPPS (op1 op2:sse_operand) (imm:int8)
  | S_CMPSS (op1 op2: sse_operand) (imm:int8)
  | S_COMISS (op1 op2: sse_operand)
  | S_CVTPI2PS (op1 op2: sse_operand)
  | S_CVTPS2PI (op1 op2: sse_operand)
  | S_CVTSI2SS (op1 op2: sse_operand)
  | S_CVTSS2SI (op1 op2: sse_operand)
  | S_CVTTPS2PI (op1 op2: sse_operand)
  | S_CVTTSS2SI (op1 op2: sse_operand)
  | S_DIVPS (op1 op2: sse_operand)
  | S_DIVSS (op1 op2: sse_operand)
  | S_LDMXCSR (op1: sse_operand)
  | S_MAXPS (op1 op2: sse_operand)
  | S_MAXSS (op1 op2: sse_operand)
  | S_MINPS (op1 op2: sse_operand)
  | S_MINSS (op1 op2: sse_operand)
  | S_MOVAPS (op1 op2: sse_operand)
  | S_MOVHLPS (op1 op2: sse_operand)
  | S_MOVHPS (op1 op2: sse_operand)
  | S_MOVLHPS (op1 op2: sse_operand)
  | S_MOVLPS (op1 op2: sse_operand)
  | S_MOVMSKPS (op1 op2: sse_operand)
  | S_MOVSS (op1 op2: sse_operand)
  | S_MOVUPS (op1 op2: sse_operand)
  | S_MULPS (op1 op2: sse_operand)
  | S_MULSS (op1 op2: sse_operand)
  | S_ORPS (op1 op2: sse_operand)
  | S_RCPPS (op1 op2: sse_operand)
  | S_RCPSS (op1 op2: sse_operand)
  | S_RSQRTPS (op1 op2: sse_operand)
  | S_RSQRTSS (op1 op2: sse_operand).

  Inductive s_instr2 : Set :=
  | S_SHUFPS (op1 op2: sse_operand) (imm:int8)
  | S_SQRTPS (op1 op2: sse_operand)
  | S_SQRTSS (op1 op2: sse_operand)
  | S_STMXCSR (op1 : sse_operand)
  | S_SUBPS (op1 op2: sse_operand)
  | S_SUBSS (op1 op2: sse_operand)
  | S_UCOMISS (op1 op2: sse_operand)
  | S_UNPCKHPS (op1 op2: sse_operand)
  | S_UNPCKLPS (op1 op2: sse_operand)
  | S_XORPS (op1 op2: sse_operand)
  | S_PAVGB (op1 op2: sse_operand)
  | S_PEXTRW (op1 op2: sse_operand) (imm:int8)
  | S_PINSRW (op1 op2: sse_operand) (imm:int8)
  | S_PMAXSW (op1 op2: sse_operand)
  | S_PMAXUB (op1 op2: sse_operand)
  | S_PMINSW (op1 op2: sse_operand)
  | S_PMINUB (op1 op2: sse_operand)
  | S_PMOVMSKB (op1 op2: sse_operand)
  | S_PSADBW (op1 op2: sse_operand)
  | S_PSHUFW (op1 op2: sse_operand) (imm:int8)
  | S_MASKMOVQ (op1 op2: sse_operand)
  | S_MOVNTPS (op1 op2: sse_operand)
  | S_MOVNTQ (op1 op2: sse_operand)
  | S_PREFETCHT0 (op1: sse_operand)
  | S_PREFETCHT1 (op1: sse_operand)
  | S_PREFETCHT2 (op1: sse_operand)
  | S_PREFETCHNTA (op1: sse_operand)
  | S_SFENCE.
  
  Inductive tipe : Set := 
  | Int_t
  | Register_t
  | BitVector_t : nat -> tipe (* a bit vector of a certain width *)
  | Scale_t
  | Condition_t
  | Address_t
  | Operand_t
  | Reg_or_Immed_t
  | Fp_Debug_Register_t
  | Fp_Operand_t
  | Fp_Condition_t
  | MMX_Granularity_t
  | MMX_Operand_t
  | SSE_Operand_t
  | I_Instr1_t
  | I_Instr2_t
  | I_Instr3_t
  | I_Instr4_t
  | I_Instr5_t
  | I_Instr6_t
  | F_Instr1_t
  | F_Instr2_t
  | M_Instr_t
  | S_Instr1_t
  | S_Instr2_t
  | Instruction_t
  | Control_Register_t
  | Debug_Register_t
  | Segment_Register_t
  | Lock_or_Rep_t
  | Bool_t
  | Prefix_t
  (* G.T.: added option_t as a stardard decoder type *)
  (* | Option_t (t: type) : type *)
  (* Need pairs at this level if I want to have options of pairs*)
  | UPair_t: tipe -> tipe -> tipe.

  Definition Byte_t := BitVector_t 7.
  Definition Half_t := BitVector_t 15.
  Definition Word_t := BitVector_t 31.
  Definition Double_Word_t := BitVector_t 63.
  Definition Ten_Byte_t := BitVector_t 79.
  Definition Fpu_Register_t := BitVector_t 2.
  Definition MMX_Register_t := BitVector_t 2.
  Definition SSE_Register_t := BitVector_t 2.

  Definition tipe_eq : forall (t1 t2:tipe), {t1=t2} + {t1<>t2}.
    intros ; decide equality.
    apply eq_nat_dec.
  Defined.

  Fixpoint tipe_m (t:tipe) := 
    match t with 
      | Int_t => Z
      | Register_t => register
      | BitVector_t n => Word.int n
      | Scale_t => scale
      | Condition_t => condition_type
      | Address_t => address
      | Operand_t => operand
      | Reg_or_Immed_t => reg_or_immed
      | Fp_Debug_Register_t => fp_debug_register
      | Fp_Operand_t => fp_operand  
      | Fp_Condition_t => fp_condition_type
      | MMX_Granularity_t => mmx_granularity
      | MMX_Operand_t => mmx_operand
      | SSE_Operand_t => sse_operand
      | Instruction_t => instr
      | I_Instr1_t => i_instr1
      | I_Instr2_t => i_instr2
      | I_Instr3_t => i_instr3
      | I_Instr4_t => i_instr4
      | I_Instr5_t => i_instr5
      | I_Instr6_t => i_instr6
      | F_Instr1_t => f_instr1
      | F_Instr2_t => f_instr2
      | M_Instr_t => m_instr
      | S_Instr1_t => s_instr1
      | S_Instr2_t => s_instr2
      | Control_Register_t => control_register
      | Debug_Register_t => debug_register
      | Segment_Register_t => segment_register
      | Lock_or_Rep_t => lock_or_rep
      | Bool_t => bool
      | Prefix_t => prefix
      (* | Option_t t => option (tipe_m t) *)
      | UPair_t t1 t2 => ((tipe_m t1) * (tipe_m t2))%type
    end.

  Definition user_type := tipe.
  Definition user_type_dec : forall (t1 t2:user_type), {t1=t2} + {t1<>t2} := 
    tipe_eq.
  Definition user_type_denote := tipe_m.

  Definition byte_explode (b:int8) : list bool := 
  let bs := Word.bits_of_Z 8 (Word.unsigned b) in
    (bs 7)::(bs 6)::(bs 5)::(bs 4)::(bs 3)::(bs 2)::(bs 1)::(bs 0)::nil.

  Definition nat_explode (n:nat) : list bool := 
    byte_explode (Word.repr (Z_of_nat n)).

  Definition token_id := nat.
  Definition num_tokens : token_id := 256%nat.
  Definition token_id_to_chars : token_id -> list char_p := nat_explode.

  Open Scope string_scope.
  Definition show_char (c:char_p) : string :=
    match c with
      | true => "1"
      | false => "0"
    end.

End X86_PARSER_ARG.

Require Import Coq.Structures.OrdersAlt.
Module CharOrderedTypeAlt <: OrderedTypeAlt.
  Definition t : Type := X86_PARSER_ARG.char_p.
  Definition compare : t -> t -> comparison := X86_PARSER_ARG.char_cmp.

  Lemma compare_sym : forall (c1 c2 : t), compare c2 c1 = CompOpp (compare c1 c2).
  Proof.
    destruct c1 ; destruct c2 ; auto.
  Qed.

  Lemma compare_trans :
    forall cmp c1 c2 c3, compare c1 c2 = cmp  -> compare c2 c3 = cmp -> compare c1 c3 = cmp.
  Proof.
    destruct c1 ; destruct c2 ; destruct c3 ; simpl ; intros ; subst ; auto ; discriminate.
  Qed.
End CharOrderedTypeAlt.

Module CharOrderedType := OT_from_Alt CharOrderedTypeAlt.



(******************************************************************************)
(* I would like to put this in a module but alas, the Extraction Implicit     *)
(* stuff breaks then.  So I've had to break this out to top-level.            *)
(******************************************************************************)
(* Module X86_BASE_PARSER(NewParser(PA : NEW_PARSER_ARG). *)
