(** Gang Tan: Bi-directional grammars for both parsing and pretty-printing *)

(* This file glues all individual x86 instruction bigrammars in
   Decode_ins.v into one big bigrammar. *)

Require Import Coqlib.
Require Import Coq.Init.Logic.
Require Import Bool.
Require Import String.
Require Import List.
Require Import Maps.
Require Import Ascii.
Require Import ZArith.
Require Import Eqdep.
Require Import CommonTacs.
Require Import Program.
Require Import Coq.Classes.Morphisms.

Unset Automatic Introduction.
Set Implicit Arguments.

Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.

  Require Import X86Syntax.
  Require Import Bits.
  Require ParserArg.
  Import ParserArg.X86_PARSER_ARG.
  Require Import BiGrammar.
  Require Import DecodeBi_ins.


  Definition lock_p : wf_bigrammar lock_or_rep_t. 
    refine("1111" $$ ! "0000"
             @ (fun v => lock %% lock_or_rep_t)
             & (fun lr => 
                  match lr with
                    | lock => Some ()
                    | _ => None
                  end)
             & _); ins_invertible_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition rep_or_repn_p : wf_bigrammar lock_or_rep_t. 
    refine ((("1111" $$ ! "0010") |+| ("1111" $$ ! "0011"))
              @ (fun v => 
                   match v with
                     | inl () => repn
                     | inr () => rep
                   end %% lock_or_rep_t)
              & (fun u => 
                   match u with
                     | repn => Some (inl ())
                     | rep => Some (inr ())
                     | _ => None
                   end)
              & _); ins_invertible_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition rep_p : wf_bigrammar lock_or_rep_t. 
    refine ("1111" $$ ! "0011"
              @ (fun v => rep  %% lock_or_rep_t)
              & (fun u => 
                   match u with
                     | rep => Some ()
                     | _ => None
                   end)
              & _); ins_invertible_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition lock_or_rep_p : wf_bigrammar lock_or_rep_t.
    refine (("1111" $$ ( ! "0000" |+| ! "0010" |+| ! "0011"))
              @ (fun v => 
                   match v with
                     | inl () => lock
                     | inr (inl ()) => repn
                     | inr (inr ()) => rep
                   end %% lock_or_rep_t)
              & (fun lr => 
                   match lr with
                     | lock => Some (inl ())
                     | repn => Some (inr (inl ()))
                     | rep => Some (inr (inr ()))
                   end)
              & _); ins_invertible_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition segment_override_env : AST_Env segment_register_t :=
    {0, "0010" $$ ! "1110", (fun v => CS %% segment_register_t)} :::
    {1, "0011" $$ ! "0110", (fun v => SS %% segment_register_t)} :::
    {2, "0011" $$ ! "1110", (fun v => DS %% segment_register_t)} :::
    {3, "0010" $$ ! "0110", (fun v => ES %% segment_register_t)} :::
    {4, "0110" $$ ! "0100", (fun v => FS %% segment_register_t)} :::
    {5, "0110" $$ ! "0101", (fun v => GS %% segment_register_t)} :::
    ast_env_nil.
  Hint Unfold segment_override_env : env_unfold_db.

  Definition segment_override_p : wf_bigrammar segment_register_t.
    gen_ast_defs segment_override_env.
    refine (gr @ (mp: _ -> [|segment_register_t|])
               & (fun u => 
                    match u with 
                      | CS => case0 ()
                      | SS => case1 ()
                      | DS => case2 ()
                      | ES => case3 ()
                      | FS => case4 ()
                      | GS => case5 ()
                    end)
               & _); clear_ast_defs; ins_invertible_tac.
  Defined.

  Definition op_override_p : wf_bigrammar bool_t.
    refine ("0110" $$ ! "0110"
              @ (fun v => true %% bool_t)
              & (fun u =>
                   match u with
                     | true => Some ()
                     | false => None
                   end)
              & _); ins_invertible_tac.
  Defined.

  Definition addr_override_p : wf_bigrammar bool_t.
    refine ("0110" $$ ! "0111"
              @ (fun v => true %% bool_t)
              & (fun u =>
                   match u with
                     | true => Some ()
                     | false => None
                   end)
              & _); ins_invertible_tac.
  Defined.

  Lemma op_override_p_rng_inv op :
    in_bigrammar_rng (` op_override_p) op -> op = true.
  Proof. unfold op_override_p; intros; ins_ibr_sim. Qed.

  Definition opt2b (a: option bool) (default: bool) :=
    match a with
      | Some b => b
      | None => default
    end.

  (** In lock_or_rep, only rep can be used; 
      segment_override and op_override are allowed. *)
  Definition prefix_grammar_rep : wf_bigrammar prefix_t.
    refine ((option_perm3 rep_p segment_override_p op_override_p)
              @ (fun v => match v with (l, (s, op)) =>
                   mkPrefix l s (opt2b op false) false %% prefix_t end)
              & (fun u => 
                   match op_override u, addr_override u with
                     | true,false => Some (lock_rep u, (seg_override u, Some true))
                     | false,false => Some (lock_rep u, (seg_override u, None))
                     | _,_ => None
                   end)
              & _); compute [op_override addr_override lock_rep seg_override];
    ins_invertible_tac.
    - destruct v as [l [s op]]. 
      destruct op as [op | ]; [destruct op | ]; compute [opt2b].
      + ins_printable_tac.
      + printable_tac.
        apply option_perm3_rng; sim; auto with ibr_rng_db.
        clear H.
         (* don't understand why auto doesn't work even though
            option_perm_rng2 is in the database *)
        apply option_perm_rng2.
      + ins_printable_tac.
    - destruct w as [l s op addr];
      destruct op; destruct addr; parsable_tac.
  Defined.

  (** In lock_or_rep, either rep or repn can be used, but lock is disallowed;
      segment_override and op_override also allowed.*)
  Definition prefix_grammar_rep_or_repn : wf_bigrammar prefix_t.
    refine ((option_perm3 rep_or_repn_p segment_override_p op_override_p)
              @ (fun v => match v with (l, (s, op)) =>
                   mkPrefix l s (opt2b op false) false %% prefix_t end)
              & (fun u => 
                   match op_override u, addr_override u with
                     | true,false => Some (lock_rep u, (seg_override u, Some true))
                     | false,false => Some (lock_rep u, (seg_override u, None))
                     | _,_ => None
                   end)
              & _); compute [op_override addr_override lock_rep seg_override];
    ins_invertible_tac.
    - destruct v as [l [s op]]. 
      destruct op as [op | ]; [destruct op | ]; compute [opt2b].
      + ins_printable_tac.
      + printable_tac.
        apply option_perm3_rng; sim; auto with ibr_rng_db.
        apply option_perm_rng2.
      + ins_printable_tac.
    - destruct w as [l s op addr];
      destruct op; destruct addr; parsable_tac.
  Defined.

  (** In lock_or_rep, only lock can be used; 
      segment override is optional; op_override prefix *must* be used *)
  Definition prefix_grammar_lock_with_op_override : wf_bigrammar prefix_t.
    refine ((option_perm3_variation lock_p segment_override_p op_override_p)
              @ (fun v => match v with (l, (s, op)) =>
                   mkPrefix l s op false %% prefix_t end)
              & (fun u => 
                   match addr_override u with
                     | false => Some (lock_rep u,
                                      (seg_override u, op_override u))
                     | _ => None
                   end)
              & _); compute [op_override addr_override lock_rep seg_override];
    ins_invertible_tac.
    - destruct w as [l s op addr]; destruct addr; parsable_tac.
  Defined.

  (** In lock_or_rep, only lock can be used; segment override is optional;
      and op_override *must not* be used. *)
  Definition prefix_grammar_lock_no_op_override : wf_bigrammar prefix_t.
    refine ((option_perm2 lock_p segment_override_p)
              @ (fun v => match v with (l, s) =>
                   mkPrefix l s false false %% prefix_t end)
              & (fun u => 
                   match op_override u, addr_override u with
                     | false,false => Some (lock_rep u, seg_override u)
                     | _,_ => None
                   end)
              & _); compute [op_override addr_override lock_rep seg_override];
    ins_invertible_tac.
    - destruct w as [l s op addr]; destruct op; destruct addr; parsable_tac.
  Defined.

  (** It cannot take a lock_or_rep prefix, must take op_override prefix,
      can optionally take segment-override prefix. *)
  Definition prefix_grammar_seg_with_op_override: wf_bigrammar prefix_t. 
    refine ((option_perm2_variation segment_override_p op_override_p)
              @ (fun v => match v with (s, op) =>
                   mkPrefix None s op false %% prefix_t end)
              & (fun u =>
                   match addr_override u, lock_rep u with
                     | false,None => Some (seg_override u, op_override u)
                     | _,_ => None
                   end)
              & _); compute [op_override addr_override lock_rep seg_override];
      ins_invertible_tac.
    - destruct w as [l s op addr]; destruct l; destruct addr; parsable_tac.
  Defined.

  (** Cannot take a lock_or_rep prefix, but can optionally take segment or
      op override prefix. *)
  Definition prefix_grammar_seg_op_override: wf_bigrammar prefix_t. 
    refine ((option_perm2 segment_override_p op_override_p)
              @ (fun v => match v with (s, op) =>
                   mkPrefix None s (opt2b op false) false %% prefix_t end)
              & (fun u =>
                   match op_override u, addr_override u, lock_rep u with
                     | true, false, None => Some (seg_override u, Some true)
                     | false, false, None => Some (seg_override u, None)
                     | _,_,_ => None
                   end)
              & _); compute [op_override addr_override lock_rep seg_override];
    ins_invertible_tac.
    - destruct v as [s op]. 
      destruct op as [op | ]; [destruct op | ]; compute [opt2b].
      + ins_printable_tac.
      + printable_tac.
        apply option_perm2_rng; sim; auto with ibr_rng_db.
        apply option_perm_rng2.
      + ins_printable_tac.
    - destruct w as [l s op addr];
      destruct op; destruct addr; destruct l; parsable_tac.
  Defined.

  (** Only allows seg override prefix. *)
  Definition prefix_grammar_only_seg_override : wf_bigrammar prefix_t.
    refine ((option_perm segment_override_p)
              @ (fun s => mkPrefix None s false false %% prefix_t)
              & (fun u => 
                   match op_override u, addr_override u, lock_rep u with
                     | false, false, None => Some (seg_override u)
                     | _,_,_ => None
                   end)
              & _); compute [op_override addr_override lock_rep seg_override];
    ins_invertible_tac.
    - destruct w as [l s op addr];
      destruct op; destruct addr; destruct l; parsable_tac.
  Defined.

  Lemma lock_with_op_override_rng_inv pre: 
    in_bigrammar_rng (` prefix_grammar_lock_with_op_override) pre ->
    op_override pre = true.
  Proof. unfold prefix_grammar_lock_with_op_override; intros.
    ibr_prover.
    match goal with
      | [H:in_bigrammar_rng (` (option_perm3_variation _ _ _)) (_,(_,_)) |- _] =>
        rewrite <- option_perm3_variation_rng in H; destruct H as [_ [_ H]];
        apply op_override_p_rng_inv in H
    end.
    subst pre; trivial.
  Qed.

  Lemma lock_no_op_override_rng_inv pre:
    in_bigrammar_rng (` prefix_grammar_lock_no_op_override) pre ->
    op_override pre = false.
  Proof. unfold prefix_grammar_lock_no_op_override; intros.
    ibr_prover. subst pre; trivial. 
  Qed.


  Lemma seg_with_op_override_rng_inv pre: 
    in_bigrammar_rng (` prefix_grammar_seg_with_op_override) pre ->
    op_override pre = true.
  Proof. unfold prefix_grammar_seg_with_op_override; intros.
    ibr_prover.
    match goal with
      | [H:in_bigrammar_rng (` (option_perm2_variation _ _)) (_,_) |- _] =>
        rewrite <- option_perm2_variation_rng in H; destruct H as [_ H];
        apply op_override_p_rng_inv in H
    end.
    subst pre; trivial.
  Qed.

  Lemma only_seg_override_rng_inv pre: 
    in_bigrammar_rng (` prefix_grammar_only_seg_override) pre ->
    op_override pre = false.
  Proof. unfold prefix_grammar_only_seg_override; intros.
    ibr_prover.
    subst pre; trivial.
  Qed.


  (* Specialized printable and parsable tactics used when combining
     instruction grammars *)

  Local Ltac ins_com_printable := 
    repeat match goal with
             | [v: [| Sum_t _ _ |] |- _ ] => case v as [v | v]
             | [v: [| unit_t |] |- _] => destruct v
             | [v:[|pair_t _ _|] |- _] => destruct v
           end;
    try (match goal with
           | [ |- exists v', ?c = Some v' /\ _] => 
             match c with
               | Some ?v =>
                 exists v; split; trivial
               | if op_override _ then Some ?v1 else Some ?v2 =>
                 ibr_prover;
                 match goal with
                   | [ H: in_bigrammar_rng
                            (` prefix_grammar_lock_with_op_override) ?pre |- _] =>
                     assert (H2: op_override pre = true) by
                         (apply lock_with_op_override_rng_inv; trivial);
                     rewrite H2;
                     exists v1; split; ibr_prover
                   | [ H: in_bigrammar_rng
                            (` prefix_grammar_lock_no_op_override) ?pre |- _] =>
                     assert (H2: op_override pre = false) by
                         (apply lock_no_op_override_rng_inv; trivial);
                     rewrite H2;
                     exists v2; split; ibr_prover
                   | [ H: in_bigrammar_rng
                            (` prefix_grammar_seg_with_op_override) ?pre |- _] =>
                     assert (H2: op_override pre = true) by
                         (apply seg_with_op_override_rng_inv; trivial);
                     rewrite H2;
                     exists v1; split; ibr_prover
                   | [ H: in_bigrammar_rng
                            (` prefix_grammar_only_seg_override) ?pre |- _] =>
                     assert (H2: op_override pre = false) by
                         (apply only_seg_override_rng_inv; trivial);
                     rewrite H2;
                     exists v2; split; ibr_prover
                 end
             end
        end).

  Local Ltac ins_com_parsable := 
    match goal with
      | [H: ?c = Some _ |- _] => 
        match c with
          | None => discriminate H
          | Some _ => inversion H; clear H; subst; trivial
          | if op_override ?p then Some _ else Some _ => 
            destruct (op_override p);
              inversion H; clear H; subst; trivial
        end
    end.

  Definition i_instr1_env : AST_Env i_instr1_t := 
    {0, AAA_p, (fun v => I_AAA %% i_instr1_t)} :::
    {1, AAD_p, (fun v => I_AAD %% i_instr1_t)} :::
    {2, AAM_p, (fun v => I_AAM %% i_instr1_t)} :::
    {3, AAS_p, (fun v => I_AAS %% i_instr1_t)} :::
    {4, CLC_p, (fun v => I_CLC %% i_instr1_t)} :::
    {5, CLD_p, (fun v => I_CLD %% i_instr1_t)} :::
    {6, CLI_p, (fun v => I_CLI %% i_instr1_t)} :::
    {7, CLTS_p, (fun v => I_CLTS %% i_instr1_t)} :::
    {8, CMC_p, (fun v => I_CMC %% i_instr1_t)} :::
    {9, CPUID_p, (fun v => I_CPUID %% i_instr1_t)} :::
    {10, DAA_p, (fun v => I_DAA %% i_instr1_t)} :::
    {11, DAS_p, (fun v => I_DAS %% i_instr1_t)} :::
    {12, HLT_p, (fun v => I_HLT %% i_instr1_t)} :::
    {13, INT_p, (fun v => I_INT %% i_instr1_t)} :::
    {14, INTO_p, (fun v => I_INTO %% i_instr1_t)} :::
    {15, INVD_p, (fun v => I_INVD %% i_instr1_t)} :::
    {16, IRET_p, (fun v => I_IRET %% i_instr1_t)} :::
    {17, LAHF_p, (fun v => I_LAHF %% i_instr1_t)} :::
    {18, LEAVE_p, (fun v => I_LEAVE %% i_instr1_t)} :::
    {19, POPA_p, (fun v => I_POPA %% i_instr1_t)} :::
    {20, POPF_p, (fun v => I_POPF %% i_instr1_t)} :::
    {21, PUSHA_p, (fun v => I_PUSHA %% i_instr1_t)} :::
    {22, PUSHF_p, (fun v => I_PUSHF %% i_instr1_t)} :::
    {23, RDMSR_p, (fun v => I_RDMSR %% i_instr1_t)} :::
    {24, RDPMC_p, (fun v => I_RDPMC %% i_instr1_t)} :::
    {25, RDTSC_p, (fun v => I_RDTSC %% i_instr1_t)} :::
    {26, RDTSCP_p, (fun v => I_RDTSCP %% i_instr1_t)} :::
    {27, RSM_p, (fun v => I_RSM %% i_instr1_t)} :::
    {28, SAHF_p, (fun v => I_SAHF %% i_instr1_t)} :::
    {29, STC_p, (fun v => I_STC %% i_instr1_t)} :::
    {30, STD_p, (fun v => I_STD %% i_instr1_t)} :::
    {31, STI_p, (fun v => I_STI %% i_instr1_t)} :::
    {32, UD2_p, (fun v => I_UD2 %% i_instr1_t)} :::
    {33, WBINVD_p, (fun v => I_WBINVD %% i_instr1_t)} :::
    {34, WRMSR_p, (fun v => I_WRMSR %% i_instr1_t)} :::
    {35, XLAT_p, (fun v => I_XLAT %% i_instr1_t)} :::
    ast_env_nil.
  Hint Unfold i_instr1_env: env_unfold_db.

  Definition i_instr1_p : wf_bigrammar i_instr1_t.
    gen_ast_defs i_instr1_env.
    refine (gr @ (mp: _ -> [|i_instr1_t|])
               & (fun u =>
                    match u with
                      | I_AAA => case0 ()
                      | I_AAD => case1 ()
                      | I_AAM => case2 ()
                      | I_AAS => case3 ()
                      | I_CLC => case4 ()
                      | I_CLD => case5 ()
                      | I_CLI => case6 ()
                      | I_CLTS => case7 ()
                      | I_CMC => case8 ()
                      | I_CPUID => case9 ()
                      | I_DAA => case10 ()
                      | I_DAS => case11 ()
                      | I_HLT => case12 ()
                      | I_INT => case13 ()
                      | I_INTO => case14 ()
                      | I_INVD => case15 ()
                      | I_IRET => case16 ()
                      | I_LAHF => case17 ()
                      | I_LEAVE => case18 ()
                      | I_POPA => case19 ()
                      | I_POPF => case20 ()
                      | I_PUSHA => case21 ()
                      | I_PUSHF => case22 ()
                      | I_RDMSR => case23 ()
                      | I_RDPMC => case24 ()
                      | I_RDTSC => case25 ()
                      | I_RDTSCP => case26 ()
                      | I_RSM => case27 ()
                      | I_SAHF => case28 ()
                      | I_STC => case29 ()
                      | I_STD => case30 ()
                      | I_STI => case31 ()
                      | I_UD2 => case32 ()
                      | I_WBINVD => case33 ()
                      | I_WRMSR => case34 ()
                      | I_XLAT => case35 ()
                    end)
               & _). clear_ast_defs. invertible_tac.
     - abstract (destruct w; parsable_tac).
  Defined.

  Definition i_instr2_env : AST_Env i_instr2_t := 
    {0, ARPL_p, (fun v => match v with (op1,op2) => I_ARPL op1 op2
                          end %% i_instr2_t)} :::
    {1, BOUND_p, (fun v => match v with (op1,op2) => I_BOUND op1 op2
                          end %% i_instr2_t)} :::
    {2, BSF_p, (fun v => match v with (op1,op2) => I_BSF op1 op2
                          end %% i_instr2_t)} :::
    {3, BSR_p, (fun v => match v with (op1,op2) => I_BSR op1 op2
                          end %% i_instr2_t)} :::
    {4, BSWAP_p, (fun r => I_BSWAP r %% i_instr2_t)} :::
    {5, BT_p, (fun v => match v with (op1,op2) => I_BT op1 op2
                          end %% i_instr2_t)} :::
    {6, CALL_p, (fun v => match v with
                              (near,(abs,(op1,sel))) => I_CALL near abs op1 sel
                          end %% i_instr2_t)} :::
    {7, IN_p, (fun v => match v with (w,p) => I_IN w p
                          end %% i_instr2_t)} :::
    {8, INTn_p, (fun it => I_INTn it %% i_instr2_t)} :::
    {9, INVLPG_p, (fun op => I_INVLPG op %% i_instr2_t)} :::
    {10, Jcc_p, (fun v => match v with (ct,disp) => I_Jcc ct disp
                          end %% i_instr2_t)} :::
    {11, JCXZ_p, (fun b => I_JCXZ b %% i_instr2_t)} :::
    {12, JMP_p, (fun v => match v with
                              (near,(abs,(op1,sel))) => I_JMP near abs op1 sel
                          end %% i_instr2_t)} :::
    {13, LAR_p, (fun v => match v with (op1,op2) => I_LAR op1 op2
                          end %% i_instr2_t)} :::
    {14, LDS_p, (fun v => match v with (op1,op2) => I_LDS op1 op2
                          end %% i_instr2_t)} :::
    {15, LEA_p, (fun v => match v with (op1,op2) => I_LEA op1 op2
                          end %% i_instr2_t)} :::
    {16, LES_p, (fun v => match v with (op1,op2) => I_LES op1 op2
                          end %% i_instr2_t)} :::
    {17, LFS_p, (fun v => match v with (op1,op2) => I_LFS op1 op2
                          end %% i_instr2_t)} :::
    {18, LGDT_p, (fun op => I_LGDT op %% i_instr2_t)} :::
    {19, LGS_p, (fun v => match v with (op1,op2) => I_LGS op1 op2
                          end %% i_instr2_t)} :::
    {20, LIDT_p, (fun op => I_LIDT op %% i_instr2_t)} :::
    {21, LLDT_p, (fun op => I_LLDT op %% i_instr2_t)} :::
    {22, LMSW_p, (fun op => I_LMSW op %% i_instr2_t)} :::
    {23, LOOP_p, (fun di => I_LOOP di %% i_instr2_t)} :::
    {24, LOOPZ_p, (fun di => I_LOOPZ di %% i_instr2_t)} :::
    {25, LOOPNZ_p, (fun di => I_LOOPNZ di %% i_instr2_t)} :::
    {26, LSL_p, (fun v => match v with (op1,op2) => I_LSL op1 op2
                          end %% i_instr2_t)} :::
    {27, LSS_p, (fun v => match v with (op1,op2) => I_LSS op1 op2
                          end %% i_instr2_t)} :::
    {28, LTR_p, (fun op => I_LTR op %% i_instr2_t)} :::
    ast_env_nil.
  Hint Unfold i_instr2_env: env_unfold_db.

  Definition i_instr2_p : wf_bigrammar i_instr2_t.
    gen_ast_defs i_instr2_env.
    refine (gr @ (mp: _ -> [|i_instr2_t|])
               & (fun u =>
                    match u with
                      | I_ARPL op1 op2 => case0 (op1,op2)
                      | I_BOUND op1 op2 => case1 (op1,op2)
                      | I_BSF op1 op2 => case2 (op1,op2)
                      | I_BSR op1 op2 => case3 (op1,op2)
                      | I_BSWAP r => case4 r
                      | I_BT op1 op2 => case5 (op1,op2)
                      | I_CALL near abs op1 sel => case6 (near,(abs,(op1,sel)))
                      | I_IN w p => case7 (w,p)
                      | I_INTn it => case8 it
                      | I_INVLPG op => case9 op
                      | I_Jcc ct disp => case10 (ct,disp)
                      | I_JCXZ b => case11 b
                      | I_JMP near abs op1 sel => case12 (near,(abs,(op1,sel)))
                      | I_LAR op1 op2 => case13 (op1,op2)
                      | I_LDS op1 op2 => case14 (op1,op2)
                      | I_LEA op1 op2 => case15 (op1,op2)
                      | I_LES op1 op2 => case16 (op1,op2)
                      | I_LFS op1 op2 => case17 (op1,op2)
                      | I_LGDT op1 => case18 op1
                      | I_LGS op1 op2 => case19 (op1,op2)
                      | I_LIDT op1 => case20 op1
                      | I_LLDT op1 => case21 op1
                      | I_LMSW op1 => case22 op1
                      | I_LOOP disp => case23 disp
                      | I_LOOPZ disp => case24 disp
                      | I_LOOPNZ disp => case25 disp
                      | I_LSL op1 op2 => case26 (op1,op2)
                      | I_LSS op1 op2 => case27 (op1,op2)
                      | I_LTR op1 => case28 op1
                    end)
               & _); clear_ast_defs;
    unfold invertible; split; [unfold printable | unfold parsable]; 
    compute [snd fst]; intros.
    - repeat match goal with
               | [v: [| Sum_t _ _ |] |- _ ] => case v as [v | v]
               | [v: [| unit_t |] |- _] => destruct v
               | [v:[|pair_t _ _|] |- _] => destruct v
             end; abstract printable_tac.
    - abstract (destruct w; parsable_tac).
  Defined.

  Definition i_instr3_env : AST_Env i_instr3_t := 
    {0, MOVCR_p, (fun v => match v with (d,(cr,r)) => I_MOVCR d cr r
                          end %% i_instr3_t)} :::
    {1, MOVDR_p, (fun v => match v with (d,(cr,r)) => I_MOVDR d cr r
                          end %% i_instr3_t)} :::
    {2, MOVSR_p, (fun v => match v with (d,(cr,r)) => I_MOVSR d cr r
                          end %% i_instr3_t)} :::
    {3, MOVBE_p, (fun v => match v with (op1,op2) => I_MOVBE op1 op2
                          end %% i_instr3_t)} :::
    {4, OUT_p, (fun v => match v with (w,p) => I_OUT w p
                          end %% i_instr3_t)} :::
    {5, POP_p, (fun op => I_POP op %% i_instr3_t)} :::
    {6, POPSR_p, (fun sr => I_POPSR sr %% i_instr3_t)} :::
    {7, PUSH_p, (fun v => match v with (w,op1) => I_PUSH w op1
                          end %% i_instr3_t)} :::
    {8, PUSHSR_p, (fun sr => I_PUSHSR sr %% i_instr3_t)} :::
    {9, RCL_p, (fun v => match v with (w,(op1,ri)) => I_RCL w op1 ri
                          end %% i_instr3_t)} :::
    {10, RCR_p, (fun v => match v with (w,(op1,ri)) => I_RCR w op1 ri
                          end %% i_instr3_t)} :::
    {11, SETcc_p, (fun v => match v with (ct,op1) => I_SETcc ct op1
                          end %% i_instr3_t)} :::
    {12, SGDT_p, (fun op => I_SGDT op %% i_instr3_t)} :::
    {13, SIDT_p, (fun op => I_SIDT op %% i_instr3_t)} :::
    {14, SLDT_p, (fun op => I_SLDT op %% i_instr3_t)} :::
    {15, SMSW_p, (fun op => I_SMSW op %% i_instr3_t)} :::
    {16, STR_p, (fun op => I_STR op %% i_instr3_t)} :::
    {17, VERR_p, (fun op => I_VERR op %% i_instr3_t)} :::
    {18, VERW_p, (fun op => I_VERW op %% i_instr3_t)} :::
    ast_env_nil.
  Hint Unfold i_instr3_env: env_unfold_db.

  Definition i_instr3_p : wf_bigrammar i_instr3_t.
    gen_ast_defs i_instr3_env.
    refine (gr @ (mp: _ -> [|i_instr3_t|])
               & (fun u =>
                    match u with
                      | I_MOVCR d cr r => case0 (d,(cr,r))
                      | I_MOVDR d cr r => case1 (d,(cr,r))
                      | I_MOVSR d cr r => case2 (d,(cr,r))
                      | I_MOVBE op1 op2 => case3 (op1,op2)
                      | I_OUT w p => case4 (w,p)
                      | I_POP op => case5 op
                      | I_POPSR sr => case6 sr
                      | I_PUSH w op1 => case7 (w,op1)
                      | I_PUSHSR sr => case8 sr
                      | I_RCL w op1 ri => case9 (w,(op1,ri))
                      | I_RCR w op1 ri => case10 (w,(op1,ri))
                      | I_SETcc ct op1 => case11 (ct,op1)
                      | I_SGDT op => case12 op
                      | I_SIDT op => case13 op
                      | I_SLDT op => case14 op
                      | I_SMSW op => case15 op
                      | I_STR op => case16 op
                      | I_VERR op => case17 op 
                      | I_VERW op => case18 op 
                    end)
               & _); clear_ast_defs;
    unfold invertible; split; [unfold printable | unfold parsable]; 
    compute [snd fst]; intros.
    - repeat match goal with
               | [v: [| Sum_t _ _ |] |- _ ] => case v as [v | v]
               | [v: [| unit_t |] |- _] => destruct v
               | [v:[|pair_t _ _|] |- _] => destruct v
             end; abstract printable_tac.
    - abstract (destruct w; parsable_tac).
  Defined.

  (** This set of instructions can take prefixes in prefix_grammar_rep we
      put RET in this category because it turns out many binaries use "rep
      ret" to avoid the branch prediction panelty in AMD processors; intel
      processor seems to just ignore the rep prefix in "rep ret". *)
  Definition prefix_grammar_rep_env : AST_Env i_instr4_t := 
    {0, INS_p, (fun v => I_INS v %% i_instr4_t)} :::
    {1, OUTS_p, (fun v => I_OUTS v %% i_instr4_t)} :::
    {2, MOVS_p, (fun v => I_MOVS v %% i_instr4_t)} :::
    {3, LODS_p, (fun v => I_LODS v %% i_instr4_t)} :::
    {4, STOS_p, (fun v => I_STOS v %% i_instr4_t)} :::
    {5, RET_p, (fun v => I_RET (fst v) (snd v) %% i_instr4_t)} :::
    ast_env_nil.
     
  (** this set of instructions can take prefixes in prefix_grammar_repn *)
  Definition prefix_grammar_rep_or_repn_env : AST_Env i_instr4_t :=
    {10, CMPS_p, (fun v => I_CMPS v %% i_instr4_t)} :::
    {11, SCAS_p, (fun v => I_SCAS v %% i_instr4_t)} :::
    ast_env_nil.

  Hint Unfold prefix_grammar_rep_env 
       prefix_grammar_rep_or_repn_env: env_unfold_db.

  Definition i_instr4_grammar_env' := 
    (ast_env_cat prefix_grammar_rep prefix_grammar_rep_env)
      +++
    (ast_env_cat prefix_grammar_rep_or_repn 
       prefix_grammar_rep_or_repn_env).

  Definition i_instr4_grammar_env : AST_Env (pair_t prefix_t i_instr4_t).
    let ige := eval cbv beta
                    delta [i_instr4_grammar_env' prefix_grammar_rep_env
                           prefix_grammar_rep_or_repn_env
                           ast_env_app ast_env_cat]
                    iota zeta 
               in i_instr4_grammar_env' in
    exact(ige).
  Defined.

  Definition i_instr4_grammar_type : type.
    let ige := eval unfold i_instr4_grammar_env in i_instr4_grammar_env in
    let t:=gen_ast_type ige in exact(t).
  Defined.

  Local Ltac gen4 lbl u arg :=
      let ige := eval unfold i_instr4_grammar_env
                 in i_instr4_grammar_env in
      let t := eval unfold i_instr4_grammar_type
                 in i_instr4_grammar_type in
      let f:=gen_rev_case_lbl lbl ige t in
      let f1 := eval simpl in f in
      exact (Some (f1 (fst u, arg))).

  Definition from_instr4 (u:prefix * i_instr4) : option [|i_instr4_grammar_type|].
    intro.
    refine (match snd u with
              | I_INS a1 => _
              | I_OUTS a1 => _
              | I_MOVS a1 => _
              | I_LODS a1 => _ 
              | I_STOS a1 => _ 
              | I_RET a1 a2 => _
              | I_CMPS a1 => _
              | I_SCAS a1 => _ 
            end).
    * (* I_INS *) gen4 0 u a1.
    * (* I_OUTS *) gen4 1 u a1.
    * (* I_MOVS *) gen4 2 u a1.
    * (* I_LODS *) gen4 3 u a1.
    * (* I_STOS *) gen4 4 u a1.
    * (* I_RET *) gen4 5 u (a1,a2).
    * (* I_CMPS *) gen4 10 u a1.
    * (* I_SCAS *) gen4 11 u a1.
  Defined.

  Definition i_instr4_grammar : wf_bigrammar (pair_t prefix_t i_instr4_t).
    let ige := eval unfold i_instr4_grammar_env in i_instr4_grammar_env in
    let g := gen_ast_grammar ige in pose (gr:=g);
    let m := gen_ast_map ige in pose (mp:=m).
    refine (gr @ (mp: _ -> [|pair_t prefix_t i_instr4_t|])
                 & from_instr4
                 & _); clear_ast_defs; unfold from_instr4;
    unfold invertible; split; [unfold printable | unfold parsable];
    compute [snd fst]; intros.
    - abstract ins_com_printable.
    - abstract (destruct w as [p ins]; destruct ins; ins_com_parsable).
  Defined.

  (** Instructions that can take prefixes in
      prefix_grammar_lock_with_op_override.  NEG, NOT, and XCHG appear in
      both instr_grammars_lock_with_op_override_env and
      instr_grammars_lock_no_op_override_env since they allow op_override
      prefix to be optional. *)
  Definition prefix_lock_with_op_override_env : AST_Env i_instr5_t :=
    {0, ADC_p true, (fun v => match v with (b,(op1,op2)) => I_ADC b op1 op2 end
                          %% i_instr5_t)} :::
    {1, ADD_p true, (fun v => match v with (b,(op1,op2)) => I_ADD b op1 op2 end
                          %% i_instr5_t)} :::
    {2, AND_p true, (fun v => match v with (b,(op1,op2)) => I_AND b op1 op2 end
                          %% i_instr5_t)} :::
    {3, NEG_p, (fun v => match v with (b,op) => I_NEG b op end
                          %% i_instr5_t)} :::
    {4, NOT_p, (fun v => match v with (b,op) => I_NOT b op end
                          %% i_instr5_t)} :::
    {5, OR_p true, (fun v => match v with (b,(op1,op2)) => I_OR b op1 op2 end
                          %% i_instr5_t)} :::
    {6, SBB_p true, (fun v => match v with (b,(op1,op2)) => I_SBB b op1 op2 end
                          %% i_instr5_t)} :::
    {7, SUB_p true, (fun v => match v with (b,(op1,op2)) => I_SUB b op1 op2 end
                          %% i_instr5_t)} :::
    {8, XCHG_p, (fun v => match v with (b,(op1,op2)) => I_XCHG b op1 op2 end
                          %% i_instr5_t)} :::
    {9, XOR_p true, (fun v => match v with (b,(op1,op2)) => I_XOR b op1 op2 end
                          %% i_instr5_t)} :::
    ast_env_nil.

  (** Instructions that can take prefixes in
      prefix_grammar_lock_no_op_override *)
  Definition prefix_lock_no_op_override_env : AST_Env i_instr5_t :=
    {20, ADC_p false, (fun v => match v with (b,(op1,op2)) => I_ADC b op1 op2 end
                          %% i_instr5_t)} :::
    {21, ADD_p false, (fun v => match v with (b,(op1,op2)) => I_ADD b op1 op2 end
                          %% i_instr5_t)} :::
    {22, AND_p false, (fun v => match v with (b,(op1,op2)) => I_AND b op1 op2 end
                          %% i_instr5_t)} :::
    {23, BTC_p, (fun v => match v with (op1,op2) => I_BTC op1 op2 end
                          %% i_instr5_t)} :::
    {24, BTR_p, (fun v => match v with (op1,op2) => I_BTR op1 op2 end
                          %% i_instr5_t)} :::
    {25, BTS_p, (fun v => match v with (op1,op2) => I_BTS op1 op2 end
                          %% i_instr5_t)} :::
    {26, CMPXCHG_p, (fun v => match v with (b,(op1,op2)) => I_CMPXCHG b op1 op2 end
                          %% i_instr5_t)} :::
    {27, DEC_p, (fun v => match v with (b,op) => I_DEC b op end
                          %% i_instr5_t)} :::
    {28, INC_p, (fun v => match v with (b,op) => I_INC b op end
                          %% i_instr5_t)} :::
    {29, NEG_p, (fun v => match v with (b,op) => I_NEG b op end
                          %% i_instr5_t)} :::
    {30, NOT_p, (fun v => match v with (b,op) => I_NOT b op end
                          %% i_instr5_t)} :::
    {31, OR_p false, (fun v => match v with (b,(op1,op2)) => I_OR b op1 op2 end
                          %% i_instr5_t)} :::
    {32, SBB_p false, (fun v => match v with (b,(op1,op2)) => I_SBB b op1 op2 end
                          %% i_instr5_t)} :::
    {33, SUB_p false, (fun v => match v with (b,(op1,op2)) => I_SUB b op1 op2 end
                          %% i_instr5_t)} :::
    {34, XADD_p, (fun v => match v with (b,(op1,op2)) => I_XADD b op1 op2 end
                          %% i_instr5_t)} :::
    {35, XCHG_p, (fun v => match v with (b,(op1,op2)) => I_XCHG b op1 op2 end
                          %% i_instr5_t)} :::
    {36, XOR_p false, (fun v => match v with (b,(op1,op2)) => I_XOR b op1 op2 end
                          %% i_instr5_t)} :::
    ast_env_nil.

  (** This set of instructions can take prefixes in 
      prefix_grammar_seg_with_op_override. *)
  Definition prefix_seg_with_op_override_env : AST_Env i_instr5_t :=
    {40, CMP_p true, (fun v => match v with (b,(op1,op2)) => I_CMP b op1 op2 end
                          %% i_instr5_t)} :::
    {41, IMUL_p true, (fun v => match v with (b,(op1,(opopt,iopt))) =>
                                   I_IMUL b op1 opopt iopt end
                          %% i_instr5_t)} :::
    {42, MOV_p true, (fun v => match v with (b,(op1,op2)) => I_MOV b op1 op2 end
                          %% i_instr5_t)} :::
    {43, TEST_p true, (fun v => match v with (b,(op1,op2)) => I_TEST b op1 op2 end
                          %% i_instr5_t)} :::
    ast_env_nil.


  (** This set of instructions can take prefixes in
      prefix_grammar_seg_with_op_override; there are more instructions in
      this category. *)
  Definition prefix_only_seg_override_env : AST_Env i_instr5_t :=
    {50, CMP_p false, (fun v => match v with (b,(op1,op2)) => I_CMP b op1 op2 end
                          %% i_instr5_t)} :::
    {51, IMUL_p false, (fun v => match v with (b,(op1,(opopt,iopt))) =>
                                   I_IMUL b op1 opopt iopt end
                          %% i_instr5_t)} :::
    {52, MOV_p false, (fun v => match v with (b,(op1,op2)) => I_MOV b op1 op2 end
                          %% i_instr5_t)} :::
    {53, TEST_p false, (fun v => match v with (b,(op1,op2)) => I_TEST b op1 op2 end
                          %% i_instr5_t)} :::
    ast_env_nil.


  Hint Unfold prefix_lock_with_op_override_env prefix_lock_no_op_override_env
       prefix_seg_with_op_override_env prefix_only_seg_override_env : env_unfold_db.

  Definition i_instr5_grammar_env' := 
    (ast_env_cat prefix_grammar_lock_with_op_override
       prefix_lock_with_op_override_env)
      +++
    (ast_env_cat prefix_grammar_lock_no_op_override
       prefix_lock_no_op_override_env)
      +++
    (ast_env_cat prefix_grammar_seg_with_op_override
       prefix_seg_with_op_override_env)
      +++
    (ast_env_cat prefix_grammar_only_seg_override
       prefix_only_seg_override_env).

  Definition i_instr5_grammar_env : AST_Env (pair_t prefix_t i_instr5_t).
    let ige := eval cbv beta
                    delta [i_instr5_grammar_env'
                           prefix_lock_with_op_override_env
                           prefix_lock_no_op_override_env
                           prefix_seg_with_op_override_env
                           prefix_only_seg_override_env
                           ast_env_app ast_env_cat]
                    iota zeta 
               in i_instr5_grammar_env' in
    exact(ige).
  Defined.

  Definition i_instr5_grammar_type : type.
    let ige := eval unfold i_instr5_grammar_env in i_instr5_grammar_env in
    let t:=gen_ast_type ige in exact(t).
  Defined.

  Local Ltac gen5 lbl u arg :=
      let ige := eval unfold i_instr5_grammar_env
                 in i_instr5_grammar_env in
      let t := eval unfold i_instr5_grammar_type
                 in i_instr5_grammar_type in
      let f:=gen_rev_case_lbl lbl ige t in
      let f1 := eval simpl in f in
      exact (Some (f1 (fst u, arg))).

  Local Ltac gen_op_override lbl1 lbl2 u arg := 
      refine (if (op_override (fst u)) then _ else _);
      [gen5 lbl1 u arg | gen5 lbl2 u arg].

  Definition from_instr5 (u:prefix * i_instr5) : option [|i_instr5_grammar_type|].
    intro.
    refine (match snd u with
              | I_ADC a1 a2 a3 => _
              | I_ADD a1 a2 a3 => _
              | I_AND a1 a2 a3 => _
              | I_BTC a1 a2 => _
              | I_BTR a1 a2 => _
              | I_BTS a1 a2 => _
              | I_CMP a1 a2 a3 => _
              | I_CMPXCHG a1 a2 a3 => _
              | I_DEC a1 a2 => _
              | I_IMUL a1 a2 a3 a4 => _
              | I_INC a1 a2 => _
              | I_MOV a1 a2 a3 => _
              | I_NEG a1 a2 => _
              | I_NOT a1 a2 => _
              | I_OR a1 a2 a3 => _
              | I_SBB a1 a2 a3 => _
              | I_SUB a1 a2 a3 => _
              | I_TEST a1 a2 a3 => _
              | I_XADD a1 a2 a3 => _
              | I_XCHG a1 a2 a3 => _
              | I_XOR a1 a2 a3 => _
            end).
    * (* ADC *) gen_op_override 0 20 u (a1,(a2,a3)).
    * (* ADD *)  gen_op_override 1 21 u (a1,(a2,a3)).
    * (* AND *)  gen_op_override 2 22 u (a1,(a2,a3)).
    * (* BTC *) gen5 23 u (a1,a2).
    * (* BTR *) gen5 24 u (a1,a2).
    * (* BTS *) gen5 25 u (a1,a2).
    * (* CMP *)  gen_op_override 40 50 u (a1,(a2,a3)).
    * (* CMPXCHG *) gen5 26 u (a1,(a2,a3)).
    * (* DEC *) gen5 27 u (a1,a2).
    * (* IMUL *)  gen_op_override 41 51 u (a1,(a2,(a3,a4))).
    * (* INC *) gen5 28 u (a1,a2).
    * (* MOV *)  gen_op_override 42 52 u (a1,(a2,a3)).
    * (* NEG *) gen_op_override 3 29 u (a1,a2).
    * (* NOT *) gen_op_override 4 30 u (a1,a2).
    * (* OR *)  gen_op_override 5 31 u (a1,(a2,a3)).
    * (* SBB *)  gen_op_override 6 32 u (a1,(a2,a3)).
    * (* SUB *)  gen_op_override 7 33 u (a1,(a2,a3)).
    * (* TEST *)  gen_op_override 43 53 u (a1,(a2,a3)).
    * (* XADD *) gen5 34 u (a1,(a2,a3)).
    * (* XCHG *) gen_op_override 8 35 u (a1,(a2,a3)).
    * (* XOR *)  gen_op_override 9 36 u (a1,(a2,a3)).
  Defined.
    
  Definition i_instr5_grammar : wf_bigrammar (pair_t prefix_t i_instr5_t).
    let ige := eval unfold i_instr5_grammar_env in i_instr5_grammar_env in
    let g := gen_ast_grammar ige in pose (gr:=g);
    let m := gen_ast_map ige in pose (mp:=m).
    refine (gr @ (mp: _ -> [|pair_t prefix_t i_instr5_t|])
               & from_instr5
               & _); clear_ast_defs; unfold from_instr5;
    unfold invertible; split; [unfold printable | unfold parsable];
    compute [snd fst]; intros.
    - ins_com_printable.
    - destruct w as [p ins]; destruct ins; ins_com_parsable.
  Defined.

  (** This set of instructions can take prefixes in
      prefix_grammar_seg_op_override. *)
  Definition i_instr6_env : AST_Env i_instr6_t := 
    {0, CDQ_p, (fun v => I_CDQ %% i_instr6_t)} :::
    {1, CMOVcc_p, (fun v => match v with (ct,(op1,op2)) => I_CMOVcc ct op1 op2
                          end %% i_instr6_t)} :::
    {2, CWDE_p, (fun v => I_CWDE %% i_instr6_t)} :::
    {3, DIV_p, (fun v => match v with (w,op1) => I_DIV w op1
                          end %% i_instr6_t)} :::
    {4, IDIV_p, (fun v => match v with (w,op1) => I_IDIV w op1
                          end %% i_instr6_t)} :::
    {5, MOVSX_p, (fun v => match v with (w,(op1,op2)) => I_MOVSX w op1 op2
                          end %% i_instr6_t)} :::
    {6, MOVZX_p, (fun v => match v with (w,(op1,op2)) => I_MOVZX w op1 op2
                          end %% i_instr6_t)} :::
    {7, MUL_p, (fun v => match v with (w,op1) => I_MUL w op1
                          end %% i_instr6_t)} :::
    {8, NOP_p, (fun op => I_NOP op %% i_instr6_t)} :::
    {9, ROL_p, (fun v => match v with (w,(op1,ri)) => I_ROL w op1 ri
                          end %% i_instr6_t)} :::
    {10, ROR_p, (fun v => match v with (w,(op1,ri)) => I_ROR w op1 ri
                          end %% i_instr6_t)} :::
    {11, SAR_p, (fun v => match v with (w,(op1,ri)) => I_SAR w op1 ri
                          end %% i_instr6_t)} :::
    {12, SHL_p, (fun v => match v with (w,(op1,ri)) => I_SHL w op1 ri
                          end %% i_instr6_t)} :::
    {13, SHLD_p, (fun v => match v with (op1,(r,ri)) => I_SHLD op1 r ri
                          end %% i_instr6_t)} :::
    {14, SHR_p, (fun v => match v with (w,(op1,ri)) => I_SHR w op1 ri
                          end %% i_instr6_t)} :::
    {15, SHRD_p, (fun v => match v with (op1,(r,ri)) => I_SHRD op1 r ri
                          end %% i_instr6_t)} :::
    ast_env_nil.
  Hint Unfold i_instr6_env: env_unfold_db.

  Definition i_instr6_p : wf_bigrammar i_instr6_t.
    gen_ast_defs i_instr6_env.
    refine (gr @ (mp: _ -> [|i_instr6_t|])
               & (fun u =>
                    match u with
                      | I_CDQ => case0 tt
                      | I_CMOVcc ct op1 op2 => case1 (ct,(op1,op2))
                      | I_CWDE => case2 tt
                      | I_DIV w op1 => case3 (w,op1)
                      | I_IDIV w op1 => case4 (w,op1)
                      | I_MOVSX w op1 op2 => case5 (w,(op1,op2))
                      | I_MOVZX w op1 op2 => case6 (w,(op1,op2))
                      | I_MUL w op1 => case7 (w,op1)
                      | I_NOP op => case8 op
                      | I_ROL w op1 ri => case9 (w,(op1,ri))
                      | I_ROR w op1 ri => case10 (w,(op1,ri))
                      | I_SAR w op1 ri => case11 (w,(op1,ri))
                      | I_SHL w op1 ri => case12 (w,(op1,ri))
                      | I_SHLD op1 r ri => case13 (op1,(r,ri))
                      | I_SHR w op1 ri => case14 (w,(op1,ri))
                      | I_SHRD op1 r ri => case15 (op1,(r,ri))
                    end)
               & _); clear_ast_defs;
    unfold invertible; split; [unfold printable | unfold parsable]; 
    compute [snd fst]; intros.
    - repeat match goal with
               | [v: [| Sum_t _ _ |] |- _ ] => case v as [v | v]
               | [v: [| unit_t |] |- _] => destruct v
               | [v:[|pair_t _ _|] |- _] => destruct v
             end; abstract printable_tac.
    - abstract (destruct w; parsable_tac).
  Defined.

  Definition f_instr1_env : AST_Env f_instr1_t := 
    {0, F2XM1_p, (fun v => F_F2XM1 %% f_instr1_t)} :::
    {1, FABS_p, (fun v => F_FABS %% f_instr1_t)} :::
    {2, FADD_p, (fun v => match v with (z,op1) => F_FADD z op1
                          end %% f_instr1_t)} :::
    {3, FADDP_p, (fun op => F_FADDP op %% f_instr1_t)} :::
    {4, FBLD_p, (fun op => F_FBLD op %% f_instr1_t)} :::
    {5, FBSTP_p, (fun op => F_FBSTP op %% f_instr1_t)} :::
    {6, FCHS_p, (fun v => F_FCHS %% f_instr1_t)} :::
    {7, FCMOVcc_p, (fun v => match v with (ct,op1) => F_FCMOVcc ct op1
                          end %% f_instr1_t)} :::
    {8, FCOM_p, (fun op => F_FCOM op %% f_instr1_t)} :::
    {9, FCOMP_p, (fun op => F_FCOMP op %% f_instr1_t)} :::
    {10, FCOMPP_p, (fun v => F_FCOMPP %% f_instr1_t)} :::
    {11, FCOMIP_p, (fun op => F_FCOMIP op %% f_instr1_t)} :::
    {12, FCOS_p, (fun v => F_FCOS %% f_instr1_t)} :::
    {13, FDECSTP_p, (fun v => F_FDECSTP %% f_instr1_t)} :::
    {14, FDIV_p, (fun v => match v with (z,op1) => F_FDIV z op1
                          end %% f_instr1_t)} :::
    {15, FDIVP_p, (fun op => F_FDIVP op %% f_instr1_t)} :::
    {16, FDIVR_p, (fun v => match v with (z,op1) => F_FDIVR z op1
                          end %% f_instr1_t)} :::
    {17, FDIVRP_p, (fun op => F_FDIVRP op %% f_instr1_t)} :::
    {18, FFREE_p, (fun op => F_FFREE op %% f_instr1_t)} :::
    {19, FIADD_p, (fun op => F_FIADD op %% f_instr1_t)} :::
    {20, FICOM_p, (fun op => F_FICOM op %% f_instr1_t)} :::
    {21, FICOMP_p, (fun op => F_FICOMP op %% f_instr1_t)} :::
    {22, FIDIV_p, (fun op => F_FIDIV op %% f_instr1_t)} :::
    {23, FIDIVR_p, (fun op => F_FIDIVR op %% f_instr1_t)} :::
    {24, FILD_p, (fun op => F_FILD op %% f_instr1_t)} :::
    {25, FIMUL_p, (fun op => F_FIMUL op %% f_instr1_t)} :::
    {26, FINCSTP_p, (fun v => F_FINCSTP %% f_instr1_t)} :::
    {27, FIST_p, (fun op => F_FIST op %% f_instr1_t)} :::
    {28, FISTP_p, (fun op => F_FISTP op %% f_instr1_t)} :::
    {29, FISUB_p, (fun op => F_FISUB op %% f_instr1_t)} :::
    {30, FISUBR_p, (fun op => F_FISUBR op %% f_instr1_t)} :::
    {31, FLD_p, (fun op => F_FLD op %% f_instr1_t)} :::
    {32, FLD1_p, (fun v => F_FLD1 %% f_instr1_t)} :::
    {33, FLDCW_p, (fun op => F_FLDCW op %% f_instr1_t)} :::
    {34, FLDENV_p, (fun op => F_FLDENV op %% f_instr1_t)} :::
    {35, FLDL2E_p, (fun v => F_FLDL2E %% f_instr1_t)} :::
    {36, FLDL2T_p, (fun v => F_FLDL2T %% f_instr1_t)} :::
    {37, FLDLG2_p, (fun v => F_FLDLG2 %% f_instr1_t)} :::
    {38, FLDLN2_p, (fun v => F_FLDLN2 %% f_instr1_t)} :::
    {39, FLDPI_p, (fun v => F_FLDPI %% f_instr1_t)} :::
    {40, FLDZ_p, (fun v => F_FLDZ %% f_instr1_t)} :::
    {41, FMUL_p, (fun v => match v with (z,op1) => F_FMUL z op1
                          end %% f_instr1_t)} :::
    {42, FMULP_p, (fun op => F_FMULP op %% f_instr1_t)} :::
    ast_env_nil.
  Hint Unfold f_instr1_env: env_unfold_db.

  Definition f_instr1_p : wf_bigrammar f_instr1_t.
    gen_ast_defs f_instr1_env.
    refine (gr @ (mp: _ -> [|f_instr1_t|])
               & (fun u =>
                    match u with
                      | F_F2XM1 => case0 tt
                      | F_FABS => case1 tt
                      | F_FADD z op1 => case2 (z,op1)
                      | F_FADDP op => case3 op
                      | F_FBLD op => case4 op
                      | F_FBSTP op => case5 op
                      | F_FCHS => case6 tt
                      | F_FCMOVcc ct op => case7 (ct,op)
                      | F_FCOM op => case8 op
                      | F_FCOMP op => case9 op
                      | F_FCOMPP => case10 tt
                      | F_FCOMIP op => case11 op
                      | F_FCOS => case12 tt
                      | F_FDECSTP => case13 tt
                      | F_FDIV z op => case14 (z,op)
                      | F_FDIVP op => case15 op
                      | F_FDIVR z op => case16 (z,op)
                      | F_FDIVRP op => case17 op
                      | F_FFREE op => case18 op
                      | F_FIADD op => case19 op
                      | F_FICOM op => case20 op
                      | F_FICOMP op => case21 op
                      | F_FIDIV op => case22 op
                      | F_FIDIVR op => case23 op
                      | F_FILD op => case24 op
                      | F_FIMUL op => case25 op
                      | F_FINCSTP => case26 tt
                      | F_FIST op => case27 op
                      | F_FISTP op => case28 op
                      | F_FISUB op => case29 op
                      | F_FISUBR op => case30 op
                      | F_FLD op => case31 op
                      | F_FLD1 => case32 tt
                      | F_FLDCW op => case33 op
                      | F_FLDENV op => case34 op
                      | F_FLDL2E => case35 tt
                      | F_FLDL2T => case36 tt
                      | F_FLDLG2 => case37 tt
                      | F_FLDLN2 => case38 tt
                      | F_FLDPI => case39 tt
                      | F_FLDZ => case40 tt
                      | F_FMUL z op => case41 (z,op)
                      | F_FMULP op => case42 op
                    end)
               & _); clear_ast_defs;
    unfold invertible; split; [unfold printable | unfold parsable]; 
    compute [snd fst]; intros.
    - repeat match goal with
               | [v: [| Sum_t _ _ |] |- _ ] => case v as [v | v]
               | [v: [| unit_t |] |- _] => destruct v
               | [v:[|pair_t _ _|] |- _] => destruct v
             end; abstract printable_tac.
    - abstract (destruct w; parsable_tac).
  Defined.

  Definition f_instr2_env : AST_Env f_instr2_t := 
    {0, FNCLEX_p, (fun v => F_FNCLEX %% f_instr2_t)} :::
    {1, FNINIT_p, (fun v => F_FNINIT %% f_instr2_t)} :::
    {2, FNOP_p, (fun v => F_FNOP %% f_instr2_t)} :::
    {3, FNSAVE_p, (fun op => F_FNSAVE op %% f_instr2_t)} :::
    {4, FNSTCW_p, (fun op => F_FNSTCW op %% f_instr2_t)} :::
    {5, FNSTSW_p, (fun op => F_FNSTSW op %% f_instr2_t)} :::
    {6, FPATAN_p, (fun v => F_FPATAN %% f_instr2_t)} :::
    {7, FPREM_p, (fun v => F_FPREM %% f_instr2_t)} :::
    {8, FPREM1_p, (fun v => F_FPREM1 %% f_instr2_t)} :::
    {9, FPTAN_p, (fun v => F_FPTAN %% f_instr2_t)} :::
    {10, FRNDINT_p, (fun v => F_FRNDINT %% f_instr2_t)} :::
    {11, FRSTOR_p, (fun op => F_FRSTOR op %% f_instr2_t)} :::
    {12, FSCALE_p, (fun v => F_FSCALE %% f_instr2_t)} :::
    {13, FSIN_p, (fun v => F_FSIN %% f_instr2_t)} :::
    {14, FSINCOS_p, (fun v => F_FSINCOS %% f_instr2_t)} :::
    {15, FSQRT_p, (fun v => F_FSQRT %% f_instr2_t)} :::
    {16, FST_p, (fun op => F_FST op %% f_instr2_t)} :::
    {17, FSTENV_p, (fun op => F_FSTENV op %% f_instr2_t)} :::
    {18, FSTP_p, (fun op => F_FSTP op %% f_instr2_t)} :::
    {19, FSUB_p, (fun v => match v with (z,op) => F_FSUB z op 
                           end %% f_instr2_t)} :::
    {20, FSUBP_p, (fun op => F_FSUBP op %% f_instr2_t)} :::
    {21, FSUBR_p, (fun v => match v with (z,op) => F_FSUBR z op 
                           end %% f_instr2_t)} :::
    {22, FSUBRP_p, (fun op => F_FSUBRP op %% f_instr2_t)} :::
    {23, FTST_p, (fun v => F_FTST %% f_instr2_t)} :::
    {24, FUCOM_p, (fun op => F_FUCOM op %% f_instr2_t)} :::
    {25, FUCOMP_p, (fun op => F_FUCOMP op %% f_instr2_t)} :::
    {26, FUCOMPP_p, (fun v => F_FUCOMPP %% f_instr2_t)} :::
    {27, FUCOMI_p, (fun op => F_FUCOMI op %% f_instr2_t)} :::
    {28, FUCOMIP_p, (fun op => F_FUCOMIP op %% f_instr2_t)} :::
    {29, FXAM_p, (fun v => F_FXAM %% f_instr2_t)} :::
    {30, FXCH_p, (fun op => F_FXCH op %% f_instr2_t)} :::
    {31, FXTRACT_p, (fun v => F_FXTRACT %% f_instr2_t)} :::
    {32, FYL2X_p, (fun v => F_FYL2X %% f_instr2_t)} :::
    {33, FYL2XP1_p, (fun v => F_FYL2XP1 %% f_instr2_t)} :::
    {34, FWAIT_p, (fun v => F_FWAIT %% f_instr2_t)} :::
    ast_env_nil.
  Hint Unfold f_instr2_env: env_unfold_db.

  Definition f_instr2_p : wf_bigrammar f_instr2_t.
    gen_ast_defs f_instr2_env.
    refine (gr @ (mp: _ -> [|f_instr2_t|])
               & (fun u =>
                    match u with
                      | F_FNCLEX => case0 tt
                      | F_FNINIT => case1 tt
                      | F_FNOP => case2 tt
                      | F_FNSAVE op => case3 op
                      | F_FNSTCW op => case4 op
                      | F_FNSTSW op => case5 op
                      | F_FPATAN => case6 tt
                      | F_FPREM => case7 tt
                      | F_FPREM1 => case8 tt
                      | F_FPTAN => case9 tt
                      | F_FRNDINT => case10 tt
                      | F_FRSTOR op => case11 op
                      | F_FSCALE => case12 tt
                      | F_FSIN => case13 tt
                      | F_FSINCOS => case14 tt
                      | F_FSQRT => case15 tt
                      | F_FST op => case16 op
                      | F_FSTENV op => case17 op
                      | F_FSTP op => case18 op
                      | F_FSUB z op => case19 (z,op)
                      | F_FSUBP op => case20 op
                      | F_FSUBR z op => case21 (z,op)
                      | F_FSUBRP op => case22 op
                      | F_FTST => case23 tt
                      | F_FUCOM op => case24 op
                      | F_FUCOMP op => case25 op
                      | F_FUCOMPP => case26 tt
                      | F_FUCOMI op => case27 op
                      | F_FUCOMIP op => case28 op
                      | F_FXAM => case29 tt
                      | F_FXCH op => case30 op
                      | F_FXTRACT => case31 tt
                      | F_FYL2X => case32 tt
                      | F_FYL2XP1 => case33 tt
                      | F_FWAIT => case34 tt
                    end)
               & _); clear_ast_defs;
    unfold invertible; split; [unfold printable | unfold parsable]; 
    compute [snd fst]; intros.
    - repeat match goal with
               | [v: [| Sum_t _ _ |] |- _ ] => case v as [v | v]
               | [v: [| unit_t |] |- _] => destruct v
               | [v:[|pair_t _ _|] |- _] => destruct v
             end; abstract printable_tac.
    - Time abstract (destruct w; parsable_tac).
  Defined.

  Definition m_instr_env : AST_Env m_instr_t := 
    {0, EMMS_p, (fun v => M_EMMS %% m_instr_t)} :::
    {1, MOVD_p, (fun v => match v with (op1,op2) => M_MOVD op1 op2
                          end %% m_instr_t)} :::
    {2, MOVQ_p, (fun v => match v with (op1,op2) => M_MOVQ op1 op2
                          end %% m_instr_t)} :::
    {3, PACKSSDW_p, (fun v => match v with (op1,op2) => M_PACKSSDW op1 op2
                          end %% m_instr_t)} :::
    {4, PACKSSWB_p, (fun v => match v with (op1,op2) => M_PACKSSWB op1 op2
                          end %% m_instr_t)} :::
    {5, PACKUSWB_p, (fun v => match v with (op1,op2) => M_PACKUSWB op1 op2
                          end %% m_instr_t)} :::
    {6, PADD_p, (fun v => match v with (gg,(op1,op2)) => M_PADD gg op1 op2
                          end %% m_instr_t)} :::
    {7, PADDS_p, (fun v => match v with (gg,(op1,op2)) => M_PADDS gg op1 op2
                          end %% m_instr_t)} :::
    {8, PADDUS_p, (fun v => match v with (gg,(op1,op2)) => M_PADDUS gg op1 op2
                          end %% m_instr_t)} :::
    {9, PAND_p, (fun v => match v with (op1,op2) => M_PAND op1 op2
                          end %% m_instr_t)} :::
    {10, PANDN_p, (fun v => match v with (op1,op2) => M_PANDN op1 op2
                          end %% m_instr_t)} :::
    {11, PCMPEQ_p, (fun v => match v with (gg,(op1,op2)) => M_PCMPEQ gg op1 op2
                          end %% m_instr_t)} :::
    {12, PCMPGT_p, (fun v => match v with (gg,(op1,op2)) => M_PCMPGT gg op1 op2
                          end %% m_instr_t)} :::
    {13, PMADDWD_p, (fun v => match v with (op1,op2) => M_PMADDWD op1 op2
                          end %% m_instr_t)} :::
    {14, PMULHUW_p, (fun v => match v with (op1,op2) => M_PMULHUW op1 op2
                          end %% m_instr_t)} :::
    {15, PMULHW_p, (fun v => match v with (op1,op2) => M_PMULHW op1 op2
                          end %% m_instr_t)} :::
    {16, PMULLW_p, (fun v => match v with (op1,op2) => M_PMULLW op1 op2
                          end %% m_instr_t)} :::
    {17, POR_p, (fun v => match v with (op1,op2) => M_POR op1 op2
                          end %% m_instr_t)} :::
    {18, PSLL_p, (fun v => match v with (gg,(op1,op2)) => M_PSLL gg op1 op2
                          end %% m_instr_t)} :::
    {19, PSRA_p, (fun v => match v with (gg,(op1,op2)) => M_PSRA gg op1 op2
                          end %% m_instr_t)} :::
    {20, PSRL_p, (fun v => match v with (gg,(op1,op2)) => M_PSRL gg op1 op2
                          end %% m_instr_t)} :::
    {20, PSUB_p, (fun v => match v with (gg,(op1,op2)) => M_PSUB gg op1 op2
                          end %% m_instr_t)} :::
    {22, PSUBS_p, (fun v => match v with (gg,(op1,op2)) => M_PSUBS gg op1 op2
                          end %% m_instr_t)} :::
    {23, PSUBUS_p, (fun v => match v with (gg,(op1,op2)) => M_PSUBUS gg op1 op2
                          end %% m_instr_t)} :::
    {24, PUNPCKH_p, (fun v => match v with (gg,(op1,op2)) => M_PUNPCKH gg op1 op2
                          end %% m_instr_t)} :::
    {25, PUNPCKL_p, (fun v => match v with (gg,(op1,op2)) => M_PUNPCKL gg op1 op2
                          end %% m_instr_t)} :::
    {26, PXOR_p, (fun v => match v with (op1,op2) => M_PXOR op1 op2
                          end %% m_instr_t)} :::
    ast_env_nil.
  Hint Unfold m_instr_env: env_unfold_db.

  Definition m_instr_p : wf_bigrammar m_instr_t.
    gen_ast_defs m_instr_env.
    refine (gr @ (mp: _ -> [|m_instr_t|])
               & (fun u =>
                    match u with
                      | M_EMMS => case0 tt
                      | M_MOVD op1 op2 => case1 (op1,op2)
                      | M_MOVQ op1 op2 => case2 (op1,op2)
                      | M_PACKSSDW op1 op2 => case3 (op1,op2)
                      | M_PACKSSWB op1 op2 => case4 (op1,op2)
                      | M_PACKUSWB op1 op2 => case5 (op1,op2)
                      | M_PADD gg op1 op2 => case6 (gg,(op1,op2))
                      | M_PADDS gg op1 op2 => case7 (gg,(op1,op2))
                      | M_PADDUS gg op1 op2 => case8 (gg,(op1,op2))
                      | M_PAND op1 op2 => case9 (op1,op2)
                      | M_PANDN op1 op2 => case10 (op1,op2)
                      | M_PCMPEQ gg op1 op2 => case11 (gg,(op1,op2))
                      | M_PCMPGT gg op1 op2 => case12 (gg,(op1,op2))
                      | M_PMADDWD op1 op2 => case13 (op1,op2)
                      | M_PMULHUW op1 op2 => case14 (op1,op2)
                      | M_PMULHW op1 op2 => case15 (op1,op2)
                      | M_PMULLW op1 op2 => case16 (op1,op2)
                      | M_POR op1 op2 => case17 (op1,op2)
                      | M_PSLL gg op1 op2 => case18 (gg,(op1,op2))
                      | M_PSRA gg op1 op2 => case19 (gg,(op1,op2))
                      | M_PSRL gg op1 op2 => case20 (gg,(op1,op2))
                      | M_PSUB gg op1 op2 => case21 (gg,(op1,op2))
                      | M_PSUBS gg op1 op2 => case22 (gg,(op1,op2))
                      | M_PSUBUS gg op1 op2 => case23 (gg,(op1,op2))
                      | M_PUNPCKH gg op1 op2 => case24 (gg,(op1,op2))
                      | M_PUNPCKL gg op1 op2 => case25 (gg,(op1,op2))
                      | M_PXOR op1 op2 => case26 (op1,op2)
                    end)
               & _); clear_ast_defs;
    unfold invertible; split; [unfold printable | unfold parsable]; 
    compute [snd fst]; intros.
    - repeat match goal with
               | [v: [| Sum_t _ _ |] |- _ ] => case v as [v | v]
               | [v: [| unit_t |] |- _] => destruct v
               | [v:[|pair_t _ _|] |- _] => destruct v
             end; abstract printable_tac.
    - Time abstract (destruct w; parsable_tac).
  Defined.

  Definition s_instr1_env : AST_Env s_instr1_t := 
    {0, ADDPS_p, (fun v => match v with (op1,op2) => S_ADDPS op1 op2
                          end %% s_instr1_t)} :::
    {1, ADDSS_p, (fun v => match v with (op1,op2) => S_ADDSS op1 op2
                          end %% s_instr1_t)} :::
    {2, ANDNPS_p, (fun v => match v with (op1,op2) => S_ANDNPS op1 op2
                          end %% s_instr1_t)} :::
    {3, ANDPS_p, (fun v => match v with (op1,op2) => S_ANDPS op1 op2
                          end %% s_instr1_t)} :::
    {4, CMPPS_p, (fun v => match v with (op1,(op2,imm)) => S_CMPPS op1 op2 imm
                          end %% s_instr1_t)} :::
    {5, CMPSS_p, (fun v => match v with (op1,(op2,imm)) => S_CMPSS op1 op2 imm
                          end %% s_instr1_t)} :::
    {6, COMISS_p, (fun v => match v with (op1,op2) => S_COMISS op1 op2
                          end %% s_instr1_t)} :::
    {7, CVTPI2PS_p, (fun v => match v with (op1,op2) => S_CVTPI2PS op1 op2
                          end %% s_instr1_t)} :::
    {8, CVTPS2PI_p, (fun v => match v with (op1,op2) => S_CVTPS2PI op1 op2
                          end %% s_instr1_t)} :::
    {9, CVTSI2SS_p, (fun v => match v with (op1,op2) => S_CVTSI2SS op1 op2
                          end %% s_instr1_t)} :::
    {10, CVTSS2SI_p, (fun v => match v with (op1,op2) => S_CVTSS2SI op1 op2
                          end %% s_instr1_t)} :::
    {11, CVTTPS2PI_p, (fun v => match v with (op1,op2) => S_CVTTPS2PI op1 op2
                          end %% s_instr1_t)} :::
    {12, CVTTSS2SI_p, (fun v => match v with (op1,op2) => S_CVTTSS2SI op1 op2
                          end %% s_instr1_t)} :::
    {13, DIVPS_p, (fun v => match v with (op1,op2) => S_DIVPS op1 op2
                          end %% s_instr1_t)} :::
    {14, DIVSS_p, (fun v => match v with (op1,op2) => S_DIVSS op1 op2
                          end %% s_instr1_t)} :::
    {15, LDMXCSR_p, (fun op => S_LDMXCSR op %% s_instr1_t)} :::
    {16, MAXPS_p, (fun v => match v with (op1,op2) => S_MAXPS op1 op2
                          end %% s_instr1_t)} :::
    {17, MAXSS_p, (fun v => match v with (op1,op2) => S_MAXSS op1 op2
                          end %% s_instr1_t)} :::
    {18, MINPS_p, (fun v => match v with (op1,op2) => S_MINPS op1 op2
                          end %% s_instr1_t)} :::
    {19, MINSS_p, (fun v => match v with (op1,op2) => S_MINSS op1 op2
                          end %% s_instr1_t)} :::
    {20, MOVAPS_p, (fun v => match v with (op1,op2) => S_MOVAPS op1 op2
                          end %% s_instr1_t)} :::
    {21, MOVHLPS_p, (fun v => match v with (op1,op2) => S_MOVHLPS op1 op2
                          end %% s_instr1_t)} :::
    {22, MOVHPS_p, (fun v => match v with (op1,op2) => S_MOVHPS op1 op2
                          end %% s_instr1_t)} :::
    {23, MOVLHPS_p, (fun v => match v with (op1,op2) => S_MOVLHPS op1 op2
                          end %% s_instr1_t)} :::
    {24, MOVLPS_p, (fun v => match v with (op1,op2) => S_MOVLPS op1 op2
                          end %% s_instr1_t)} :::
    {25, MOVMSKPS_p, (fun v => match v with (op1,op2) => S_MOVMSKPS op1 op2
                          end %% s_instr1_t)} :::
    {26, MOVSS_p, (fun v => match v with (op1,op2) => S_MOVSS op1 op2
                          end %% s_instr1_t)} :::
    {27, MOVUPS_p, (fun v => match v with (op1,op2) => S_MOVUPS op1 op2
                          end %% s_instr1_t)} :::
    {28, MULPS_p, (fun v => match v with (op1,op2) => S_MULPS op1 op2
                          end %% s_instr1_t)} :::
    {29, MULSS_p, (fun v => match v with (op1,op2) => S_MULSS op1 op2
                          end %% s_instr1_t)} :::
    {30, ORPS_p, (fun v => match v with (op1,op2) => S_ORPS op1 op2
                          end %% s_instr1_t)} :::
    {31, RCPPS_p, (fun v => match v with (op1,op2) => S_RCPPS op1 op2
                          end %% s_instr1_t)} :::
    {32, RCPSS_p, (fun v => match v with (op1,op2) => S_RCPSS op1 op2
                          end %% s_instr1_t)} :::
    {33, RSQRTPS_p, (fun v => match v with (op1,op2) => S_RSQRTPS op1 op2
                          end %% s_instr1_t)} :::
    {34, RSQRTSS_p, (fun v => match v with (op1,op2) => S_RSQRTSS op1 op2
                          end %% s_instr1_t)} :::
    ast_env_nil.
  Hint Unfold s_instr1_env: env_unfold_db.

  Definition s_instr1_p : wf_bigrammar s_instr1_t.
    gen_ast_defs s_instr1_env.
    refine (gr @ (mp: _ -> [|s_instr1_t|])
               & (fun u =>
                    match u with
                      | S_ADDPS op1 op2 => case0 (op1,op2)
                      | S_ADDSS op1 op2 => case1 (op1,op2)
                      | S_ANDNPS op1 op2 => case2 (op1,op2)
                      | S_ANDPS op1 op2 => case3 (op1,op2)
                      | S_CMPPS op1 op2 imm => case4 (op1,(op2,imm))
                      | S_CMPSS op1 op2 imm => case5 (op1,(op2,imm))
                      | S_COMISS op1 op2 => case6 (op1,op2)
                      | S_CVTPI2PS op1 op2 => case7 (op1,op2)
                      | S_CVTPS2PI op1 op2 => case8 (op1,op2)
                      | S_CVTSI2SS op1 op2 => case9 (op1,op2)
                      | S_CVTSS2SI op1 op2 => case10 (op1,op2)
                      | S_CVTTPS2PI op1 op2 => case11 (op1,op2)
                      | S_CVTTSS2SI op1 op2 => case12 (op1,op2)
                      | S_DIVPS op1 op2 => case13 (op1,op2)
                      | S_DIVSS op1 op2 => case14 (op1,op2)
                      | S_LDMXCSR op => case15 op
                      | S_MAXPS op1 op2 => case16 (op1,op2)
                      | S_MAXSS op1 op2 => case17 (op1,op2)
                      | S_MINPS op1 op2 => case18 (op1,op2)
                      | S_MINSS op1 op2 => case19 (op1,op2)
                      | S_MOVAPS op1 op2 => case20 (op1,op2)
                      | S_MOVHLPS op1 op2 => case21 (op1,op2)
                      | S_MOVHPS op1 op2 => case22 (op1,op2)
                      | S_MOVLHPS op1 op2 => case23 (op1,op2)
                      | S_MOVLPS op1 op2 => case24 (op1,op2)
                      | S_MOVMSKPS op1 op2 => case25 (op1,op2)
                      | S_MOVSS op1 op2 => case26 (op1,op2)
                      | S_MOVUPS op1 op2 => case27 (op1,op2)
                      | S_MULPS op1 op2 => case28 (op1,op2)
                      | S_MULSS op1 op2 => case29 (op1,op2)
                      | S_ORPS op1 op2 => case30 (op1,op2)
                      | S_RCPPS op1 op2 => case31 (op1,op2)
                      | S_RCPSS op1 op2 => case32 (op1,op2)
                      | S_RSQRTPS op1 op2 => case33 (op1,op2)
                      | S_RSQRTSS op1 op2 => case34 (op1,op2)
                    end)
               & _); clear_ast_defs;
    unfold invertible; split; [unfold printable | unfold parsable]; 
    compute [snd fst]; intros.
    - repeat match goal with
               | [v: [| Sum_t _ _ |] |- _ ] => case v as [v | v]
               | [v: [| unit_t |] |- _] => destruct v
               | [v:[|pair_t _ _|] |- _] => destruct v
             end; abstract printable_tac.
    - Time abstract (destruct w; parsable_tac).
  Defined.

  Definition s_instr2_env : AST_Env s_instr2_t := 
    {0, SHUFPS_p, (fun v => match v with (op1,(op2,imm)) => S_SHUFPS op1 op2 imm
                          end %% s_instr2_t)} :::
    {1, SQRTPS_p, (fun v => match v with (op1,op2) => S_SQRTPS op1 op2
                          end %% s_instr2_t)} :::
    {2, SQRTSS_p, (fun v => match v with (op1,op2) => S_SQRTSS op1 op2
                          end %% s_instr2_t)} :::
    {3, STMXCSR_p, (fun op => S_STMXCSR op %% s_instr2_t)} :::
    {4, SUBPS_p, (fun v => match v with (op1,op2) => S_SUBPS op1 op2
                          end %% s_instr2_t)} :::
    {5, SUBSS_p, (fun v => match v with (op1,op2) => S_SUBSS op1 op2
                          end %% s_instr2_t)} :::
    {6, UCOMISS_p, (fun v => match v with (op1,op2) => S_UCOMISS op1 op2
                          end %% s_instr2_t)} :::
    {7, UNPCKHPS_p, (fun v => match v with (op1,op2) => S_UNPCKHPS op1 op2
                          end %% s_instr2_t)} :::
    {8, UNPCKLPS_p, (fun v => match v with (op1,op2) => S_UNPCKLPS op1 op2
                          end %% s_instr2_t)} :::
    {9, XORPS_p, (fun v => match v with (op1,op2) => S_XORPS op1 op2
                          end %% s_instr2_t)} :::
    {10, PAVGB_p, (fun v => match v with (op1,op2) => S_PAVGB op1 op2
                          end %% s_instr2_t)} :::
    {11, PEXTRW_p, (fun v => match v with (op1,(op2,imm)) => S_PEXTRW op1 op2 imm
                          end %% s_instr2_t)} :::
    {12, PINSRW_p, (fun v => match v with (op1,(op2,imm)) => S_PINSRW op1 op2 imm
                          end %% s_instr2_t)} :::
    {13, PMAXSW_p, (fun v => match v with (op1,op2) => S_PMAXSW op1 op2
                          end %% s_instr2_t)} :::
    {14, PMAXUB_p, (fun v => match v with (op1,op2) => S_PMAXUB op1 op2
                          end %% s_instr2_t)} :::
    {15, PMINSW_p, (fun v => match v with (op1,op2) => S_PMINSW op1 op2
                          end %% s_instr2_t)} :::
    {16, PMINUB_p, (fun v => match v with (op1,op2) => S_PMINUB op1 op2
                          end %% s_instr2_t)} :::
    {17, PMOVMSKB_p, (fun v => match v with (op1,op2) => S_PMOVMSKB op1 op2
                          end %% s_instr2_t)} :::
    {18, PSADBW_p, (fun v => match v with (op1,op2) => S_PSADBW op1 op2
                          end %% s_instr2_t)} :::
    {19, PSHUFW_p, (fun v => match v with (op1,(op2,imm)) => S_PSHUFW op1 op2 imm
                          end %% s_instr2_t)} :::
    {20, MASKMOVQ_p, (fun v => match v with (op1,op2) => S_MASKMOVQ op1 op2
                          end %% s_instr2_t)} :::
    {21, MOVNTPS_p, (fun v => match v with (op1,op2) => S_MOVNTPS op1 op2
                          end %% s_instr2_t)} :::
    {22, MOVNTQ_p, (fun v => match v with (op1,op2) => S_MOVNTQ op1 op2
                          end %% s_instr2_t)} :::
    {23, PREFETCHT0_p, (fun op => S_PREFETCHT0 op %% s_instr2_t)} :::
    {24, PREFETCHT1_p, (fun op => S_PREFETCHT1 op %% s_instr2_t)} :::
    {25, PREFETCHT2_p, (fun op => S_PREFETCHT2 op %% s_instr2_t)} :::
    {26, PREFETCHNTA_p, (fun op => S_PREFETCHNTA op %% s_instr2_t)} :::
    {27, SFENCE_p, (fun v => S_SFENCE %% s_instr2_t)} :::
    ast_env_nil.
  Hint Unfold s_instr2_env: env_unfold_db.

  Definition s_instr2_p : wf_bigrammar s_instr2_t.
    gen_ast_defs s_instr2_env.
    refine (gr @ (mp: _ -> [|s_instr2_t|])
               & (fun u =>
                    match u with
                      | S_SHUFPS op1 op2 imm => case0 (op1,(op2,imm))
                      | S_SQRTPS op1 op2 => case1 (op1,op2)
                      | S_SQRTSS op1 op2 => case2 (op1,op2)
                      | S_STMXCSR op => case3 op
                      | S_SUBPS op1 op2 => case4 (op1,op2)
                      | S_SUBSS op1 op2 => case5 (op1,op2)
                      | S_UCOMISS op1 op2 => case6 (op1,op2)
                      | S_UNPCKHPS op1 op2 => case7 (op1,op2)
                      | S_UNPCKLPS op1 op2 => case8 (op1,op2)
                      | S_XORPS op1 op2 => case9 (op1,op2)
                      | S_PAVGB op1 op2 => case10 (op1,op2)
                      | S_PEXTRW op1 op2 imm => case11 (op1,(op2,imm))
                      | S_PINSRW op1 op2 imm => case12 (op1,(op2,imm))
                      | S_PMAXSW op1 op2 => case13 (op1,op2)
                      | S_PMAXUB op1 op2 => case14 (op1,op2)
                      | S_PMINSW op1 op2 => case15 (op1,op2)
                      | S_PMINUB op1 op2 => case16 (op1,op2)
                      | S_PMOVMSKB op1 op2 => case17 (op1,op2)
                      | S_PSADBW op1 op2 => case18 (op1,op2)
                      | S_PSHUFW op1 op2 imm => case19 (op1,(op2,imm))
                      | S_MASKMOVQ op1 op2 => case20 (op1,op2)
                      | S_MOVNTPS op1 op2 => case21 (op1,op2)
                      | S_MOVNTQ op1 op2 => case22 (op1,op2)
                      | S_PREFETCHT0 op => case23 op
                      | S_PREFETCHT1 op => case24 op
                      | S_PREFETCHT2 op => case25 op
                      | S_PREFETCHNTA op => case26 op
                      | S_SFENCE => case27 tt
                    end)
               & _); clear_ast_defs;
    unfold invertible; split; [unfold printable | unfold parsable]; 
    compute [snd fst]; intros.
    - repeat match goal with
               | [v: [| Sum_t _ _ |] |- _ ] => case v as [v | v]
               | [v: [| unit_t |] |- _] => destruct v
               | [v:[|pair_t _ _|] |- _] => destruct v
             end; abstract printable_tac.
    - Time abstract (destruct w; parsable_tac).
  Defined.

  Definition instr_grammar_env : AST_Env (pair_t prefix_t instruction_t) :=
    {0, prefix_grammar_only_seg_override $ i_instr1_p,
        (fun v => 
           let (pre,hi):=v in
           let i := match hi with
                      | I_AAA => AAA
                      | I_AAD => AAD
                      | I_AAM => AAM
                      | I_AAS => AAS
                      | I_CLC => CLC
                      | I_CLD => CLD
                      | I_CLI => CLI
                      | I_CLTS => CLTS
                      | I_CMC => CMC
                      | I_CPUID => CPUID
                      | I_DAA => DAA
                      | I_DAS => DAS
                      | I_HLT => HLT
                      | I_INT => INT
                      | I_INTO => INTO
                      | I_INVD => INVD
                      | I_IRET => IRET
                      | I_LAHF => LAHF
                      | I_LEAVE => LEAVE
                      | I_POPA => POPA
                      | I_POPF => POPF
                      | I_PUSHA => PUSHA
                      | I_PUSHF => PUSHF
                      | I_RDMSR => RDMSR
                      | I_RDPMC => RDPMC
                      | I_RDTSC => RDTSC
                      | I_RDTSCP => RDTSCP
                      | I_RSM => RSM
                      | I_SAHF => SAHF
                      | I_STC => STC
                      | I_STD => STD
                      | I_STI => STI
                      | I_UD2 => UD2
                      | I_WBINVD => WBINVD
                      | I_WRMSR => WRMSR
                      | I_XLAT => XLAT
                    end
               in (pre,i) %% pair_t prefix_t instruction_t)} :::
    {1, prefix_grammar_only_seg_override $ i_instr2_p,
        (fun v => 
           let (pre,hi):=v in
           let i := match hi with
                      | I_ARPL op1 op2 => ARPL op1 op2
                      | I_BOUND op1 op2 => BOUND op1 op2
                      | I_BSF op1 op2 => BSF op1 op2
                      | I_BSR op1 op2 => BSR op1 op2
                      | I_BSWAP r => BSWAP r
                      | I_BT op1 op2 => BT op1 op2
                      | I_CALL near abs op sel => CALL near abs op sel
                      | I_IN w p => IN w p
                      | I_INTn it => INTn it
                      | I_INVLPG op => INVLPG op
                      | I_Jcc ct disp => Jcc ct disp
                      | I_JCXZ b => JCXZ b
                      | I_JMP near abs op sel => JMP near abs op sel
                      | I_LAR op1 op2 => LAR op1 op2
                      | I_LDS op1 op2 => LDS op1 op2
                      | I_LEA op1 op2 => LEA op1 op2
                      | I_LES op1 op2 => LES op1 op2
                      | I_LFS op1 op2 => LFS op1 op2
                      | I_LGDT op => LGDT op
                      | I_LGS op1 op2 => LGS op1 op2
                      | I_LIDT op => LIDT op
                      | I_LLDT op => LLDT op
                      | I_LMSW op => LMSW op
                      | I_LOOP disp => LOOP disp
                      | I_LOOPZ disp => LOOPZ disp
                      | I_LOOPNZ disp => LOOPNZ disp
                      | I_LSL op1 op2 => LSL op1 op2
                      | I_LSS op1 op2 => LSS op1 op2
                      | I_LTR op => LTR op
                    end
               in (pre,i) %% pair_t prefix_t instruction_t)} :::
    {2, prefix_grammar_only_seg_override $ i_instr3_p,
        (fun v => 
           let (pre,hi):=v in
           let i := match hi with
                      | I_MOVCR d cr r => MOVCR d cr r
                      | I_MOVDR d cr r => MOVDR d cr r
                      | I_MOVSR d cr r => MOVSR d cr r
                      | I_MOVBE op1 op2 => MOVBE op1 op2
                      | I_OUT w p => OUT w p
                      | I_POP op => POP op
                      | I_POPSR sr => POPSR sr
                      | I_PUSH w op => PUSH w op
                      | I_PUSHSR sr => PUSHSR sr
                      | I_RCL w op1 ri => RCL w op1 ri
                      | I_RCR w op1 ri => RCR w op1 ri
                      | I_SETcc ct op => SETcc ct op
                      | I_SGDT op => SGDT op
                      | I_SIDT op => SIDT op
                      | I_SLDT op => SLDT op
                      | I_SMSW op => SMSW op
                      | I_STR op => STR op
                      | I_VERR op => VERR op
                      | I_VERW op => VERW op
                    end
               in (pre,i) %% pair_t prefix_t instruction_t)} :::
    {3, i_instr4_grammar,
        (fun v => 
           let (pre,hi):=v in
           let i := match hi with
                      | I_INS b => INS b
                      | I_OUTS b => OUTS b
                      | I_MOVS b => MOVS b
                      | I_LODS b => LODS b
                      | I_STOS b => STOS b
                      | I_RET ss disp => RET ss disp
                      | I_CMPS b => CMPS b
                      | I_SCAS b => SCAS b
                    end
               in (pre,i) %% pair_t prefix_t instruction_t)} :::
    {4, i_instr5_grammar,
        (fun v => 
           let (pre,hi):=v in
           let i := match hi with
                      | I_ADC w op1 op2 => ADC w op1 op2
                      | I_ADD w op1 op2 => ADD w op1 op2
                      | I_AND w op1 op2 => AND w op1 op2
                      | I_BTC op1 op2 => BTC op1 op2
                      | I_BTR op1 op2 => BTR op1 op2
                      | I_BTS op1 op2 => BTS op1 op2
                      | I_CMP w op1 op2 => CMP w op1 op2
                      | I_CMPXCHG w op1 op2 => CMPXCHG w op1 op2
                      | I_DEC w op1 => DEC w op1
                      | I_IMUL w op1 opopt iopt  => IMUL w op1 opopt iopt
                      | I_INC w op1 => INC w op1
                      | I_MOV w op1 op2 => MOV w op1 op2
                      | I_NEG w op => NEG w op
                      | I_NOT w op => NOT w op
                      | I_OR w op1 op2 => OR w op1 op2
                      | I_SBB w op1 op2 => SBB w op1 op2
                      | I_SUB w op1 op2 => SUB w op1 op2
                      | I_TEST w op1 op2 => TEST w op1 op2
                      | I_XADD w op1 op2 => XADD w op1 op2
                      | I_XCHG w op1 op2 => XCHG w op1 op2
                      | I_XOR w op1 op2 => XOR w op1 op2
                    end
               in (pre,i) %% pair_t prefix_t instruction_t)} :::
    {5, prefix_grammar_seg_op_override $ i_instr6_p,
        (fun v => 
           let (pre,hi):=v in
           let i := match hi with
                      | I_CDQ => CDQ
                      | I_CMOVcc ct op1 op2 => CMOVcc ct op1 op2
                      | I_CWDE => CWDE
                      | I_DIV w op1 => DIV w op1
                      | I_IDIV w op1 => IDIV w op1
                      | I_MOVSX w op1 op2 => MOVSX w op1 op2
                      | I_MOVZX w op1 op2 => MOVZX w op1 op2
                      | I_MUL w op1 => MUL w op1
                      | I_NOP op => NOP op
                      | I_ROL w op1 ri => ROL w op1 ri
                      | I_ROR w op1 ri => ROR w op1 ri
                      | I_SAR w op1 ri => SAR w op1 ri
                      | I_SHL w op1 ri => SHL w op1 ri
                      | I_SHLD op1 r ri => SHLD op1 r ri
                      | I_SHR w op1 ri => SHR w op1 ri
                      | I_SHRD op1 r ri => SHRD op1 r ri
                    end
               in (pre,i) %% pair_t prefix_t instruction_t)} :::
    {6, prefix_grammar_only_seg_override $ f_instr1_p,
        (fun v => 
           let (pre,hi):=v in
           let i := match hi with
                      | F_F2XM1 => F2XM1
                      | F_FABS => FABS
                      | F_FADD z op1 => FADD z op1
                      | F_FADDP op => FADDP op
                      | F_FBLD op => FBLD op
                      | F_FBSTP op => FBSTP op
                      | F_FCHS => FCHS
                      | F_FCMOVcc ct op => FCMOVcc ct op
                      | F_FCOM op => FCOM op
                      | F_FCOMP op => FCOMP op
                      | F_FCOMPP => FCOMPP
                      | F_FCOMIP op => FCOMIP op
                      | F_FCOS => FCOS
                      | F_FDECSTP => FDECSTP
                      | F_FDIV z op => FDIV z op
                      | F_FDIVP op => FDIVP op
                      | F_FDIVR z op => FDIVR z op
                      | F_FDIVRP op => FDIVRP op
                      | F_FFREE op => FFREE op
                      | F_FIADD op => FIADD op
                      | F_FICOM op => FICOM op
                      | F_FICOMP op => FICOMP op
                      | F_FIDIV op => FIDIV op
                      | F_FIDIVR op => FIDIVR op
                      | F_FILD op => FILD op
                      | F_FIMUL op => FIMUL op
                      | F_FINCSTP => FINCSTP
                      | F_FIST op => FIST op
                      | F_FISTP op => FISTP op
                      | F_FISUB op => FISUB op
                      | F_FISUBR op => FISUBR op
                      | F_FLD op => FLD op
                      | F_FLD1 => FLD1
                      | F_FLDCW op => FLDCW op
                      | F_FLDENV op => FLDENV op
                      | F_FLDL2E => FLDL2E
                      | F_FLDL2T => FLDL2T
                      | F_FLDLG2 => FLDLG2
                      | F_FLDLN2 => FLDLN2
                      | F_FLDPI => FLDPI
                      | F_FLDZ => FLDZ
                      | F_FMUL z op => FMUL z op
                      | F_FMULP op => FMULP op
                    end
               in (pre,i) %% pair_t prefix_t instruction_t)} :::
    {7, prefix_grammar_only_seg_override $ f_instr2_p,
        (fun v => 
           let (pre,hi):=v in
           let i := match hi with
                      | F_FNCLEX => FNCLEX
                      | F_FNINIT => FNINIT
                      | F_FNOP => FNOP
                      | F_FNSAVE op => FNSAVE op
                      | F_FNSTCW op => FNSTCW op
                      | F_FNSTSW op => FNSTSW op
                      | F_FPATAN => FPATAN
                      | F_FPREM => FPREM
                      | F_FPREM1 => FPREM1
                      | F_FPTAN => FPTAN
                      | F_FRNDINT => FRNDINT
                      | F_FRSTOR op => FRSTOR op
                      | F_FSCALE => FSCALE
                      | F_FSIN => FSIN
                      | F_FSINCOS => FSINCOS
                      | F_FSQRT => FSQRT
                      | F_FST op => FST op
                      | F_FSTENV op => FSTENV op
                      | F_FSTP op => FSTP op
                      | F_FSUB z op => FSUB z op
                      | F_FSUBP op => FSUBP op
                      | F_FSUBR z op => FSUBR z op
                      | F_FSUBRP op => FSUBRP op
                      | F_FTST => FTST
                      | F_FUCOM op => FUCOM op
                      | F_FUCOMP op => FUCOMP op
                      | F_FUCOMPP => FUCOMPP
                      | F_FUCOMI op => FUCOMI op
                      | F_FUCOMIP op => FUCOMIP op
                      | F_FXAM => FXAM
                      | F_FXCH op => FXCH op
                      | F_FXTRACT => FXTRACT
                      | F_FYL2X => FYL2X
                      | F_FYL2XP1 => FYL2XP1
                      | F_FWAIT => FWAIT
                    end
               in (pre,i) %% pair_t prefix_t instruction_t)} :::
    {8, prefix_grammar_only_seg_override $ m_instr_p,
        (fun v => 
           let (pre,hi):=v in
           let i := match hi with
                      | M_EMMS => EMMS
                      | M_MOVD op1 op2 => MOVD op1 op2
                      | M_MOVQ op1 op2 => MOVQ op1 op2
                      | M_PACKSSDW op1 op2 => PACKSSDW op1 op2
                      | M_PACKSSWB op1 op2 => PACKSSWB op1 op2
                      | M_PACKUSWB op1 op2 => PACKUSWB op1 op2
                      | M_PADD gg op1 op2 => PADD gg op1 op2
                      | M_PADDS gg op1 op2 => PADDS gg op1 op2
                      | M_PADDUS gg op1 op2 => PADDUS gg op1 op2
                      | M_PAND op1 op2 => PAND op1 op2
                      | M_PANDN op1 op2 => PANDN op1 op2
                      | M_PCMPEQ gg op1 op2 => PCMPEQ gg op1 op2
                      | M_PCMPGT gg op1 op2 => PCMPGT gg op1 op2
                      | M_PMADDWD op1 op2 => PMADDWD op1 op2
                      | M_PMULHUW op1 op2 => PMULHUW op1 op2
                      | M_PMULHW op1 op2 => PMULHW op1 op2
                      | M_PMULLW op1 op2 => PMULLW op1 op2
                      | M_POR op1 op2 => POR op1 op2
                      | M_PSLL gg op1 op2 => PSLL gg op1 op2
                      | M_PSRA gg op1 op2 => PSRA gg op1 op2
                      | M_PSRL gg op1 op2 => PSRL gg op1 op2
                      | M_PSUB gg op1 op2 => PSUB gg op1 op2
                      | M_PSUBS gg op1 op2 => PSUBS gg op1 op2
                      | M_PSUBUS gg op1 op2 => PSUBUS gg op1 op2
                      | M_PUNPCKH gg op1 op2 => PUNPCKH gg op1 op2
                      | M_PUNPCKL gg op1 op2 => PUNPCKL gg op1 op2
                      | M_PXOR op1 op2 => PXOR op1 op2
                    end
               in (pre,i) %% pair_t prefix_t instruction_t)} :::
    {9, prefix_grammar_only_seg_override $ s_instr1_p,
        (fun v => 
           let (pre,hi):=v in
           let i := match hi with
                      | S_ADDPS op1 op2 => ADDPS op1 op2
                      | S_ADDSS op1 op2 => ADDSS op1 op2
                      | S_ANDNPS op1 op2 => ANDNPS op1 op2
                      | S_ANDPS op1 op2 => ANDPS op1 op2
                      | S_CMPPS op1 op2 imm => CMPPS op1 op2 imm
                      | S_CMPSS op1 op2 imm => CMPSS op1 op2 imm
                      | S_COMISS op1 op2 => COMISS op1 op2
                      | S_CVTPI2PS op1 op2 => CVTPI2PS op1 op2
                      | S_CVTPS2PI op1 op2 => CVTPS2PI op1 op2
                      | S_CVTSI2SS op1 op2 => CVTSI2SS op1 op2
                      | S_CVTSS2SI op1 op2 => CVTSS2SI op1 op2
                      | S_CVTTPS2PI op1 op2 => CVTTPS2PI op1 op2
                      | S_CVTTSS2SI op1 op2 => CVTTSS2SI op1 op2
                      | S_DIVPS op1 op2 => DIVPS op1 op2
                      | S_DIVSS op1 op2 => DIVSS op1 op2
                      | S_LDMXCSR op => LDMXCSR op
                      | S_MAXPS op1 op2 => MAXPS op1 op2
                      | S_MAXSS op1 op2 => MAXSS op1 op2
                      | S_MINPS op1 op2 => MINPS op1 op2
                      | S_MINSS op1 op2 => MINSS op1 op2
                      | S_MOVAPS op1 op2 => MOVAPS op1 op2
                      | S_MOVHLPS op1 op2 => MOVHLPS op1 op2
                      | S_MOVHPS op1 op2 => MOVHPS op1 op2
                      | S_MOVLHPS op1 op2 => MOVLHPS op1 op2
                      | S_MOVLPS op1 op2 => MOVLPS op1 op2
                      | S_MOVMSKPS op1 op2 => MOVMSKPS op1 op2
                      | S_MOVSS op1 op2 => MOVSS op1 op2
                      | S_MOVUPS op1 op2 => MOVUPS op1 op2
                      | S_MULPS op1 op2 => MULPS op1 op2
                      | S_MULSS op1 op2 => MULSS op1 op2
                      | S_ORPS op1 op2 => ORPS op1 op2
                      | S_RCPPS op1 op2 => RCPPS op1 op2
                      | S_RCPSS op1 op2 => RCPSS op1 op2
                      | S_RSQRTPS op1 op2 => RSQRTPS op1 op2
                      | S_RSQRTSS op1 op2 => RSQRTSS op1 op2
                    end
               in (pre,i) %% pair_t prefix_t instruction_t)} :::
    {10, prefix_grammar_only_seg_override $ s_instr2_p,
        (fun v => 
           let (pre,hi):=v in
           let i := match hi with
                      | S_SHUFPS op1 op2 imm => SHUFPS op1 op2 imm
                      | S_SQRTPS op1 op2 => SQRTPS op1 op2
                      | S_SQRTSS op1 op2 => SQRTSS op1 op2
                      | S_STMXCSR op => STMXCSR op
                      | S_SUBPS op1 op2 => SUBPS op1 op2
                      | S_SUBSS op1 op2 => SUBSS op1 op2
                      | S_UCOMISS op1 op2 => UCOMISS op1 op2
                      | S_UNPCKHPS op1 op2 => UNPCKHPS op1 op2
                      | S_UNPCKLPS op1 op2 => UNPCKLPS op1 op2
                      | S_XORPS op1 op2 => XORPS op1 op2
                      | S_PAVGB op1 op2 => PAVGB op1 op2
                      | S_PEXTRW op1 op2 imm => PEXTRW op1 op2 imm
                      | S_PINSRW op1 op2 imm => PINSRW op1 op2 imm
                      | S_PMAXSW op1 op2 => PMAXSW op1 op2
                      | S_PMAXUB op1 op2 => PMAXUB op1 op2
                      | S_PMINSW op1 op2 => PMINSW op1 op2
                      | S_PMINUB op1 op2 => PMINUB op1 op2
                      | S_PMOVMSKB op1 op2 => PMOVMSKB op1 op2
                      | S_PSADBW op1 op2 => PSADBW op1 op2
                      | S_PSHUFW op1 op2 imm => PSHUFW op1 op2 imm
                      | S_MASKMOVQ op1 op2 => MASKMOVQ op1 op2
                      | S_MOVNTPS op1 op2 => MOVNTPS op1 op2
                      | S_MOVNTQ op1 op2 => MOVNTQ op1 op2
                      | S_PREFETCHT0 op => PREFETCHT0 op
                      | S_PREFETCHT1 op => PREFETCHT1 op
                      | S_PREFETCHT2 op => PREFETCHT2 op
                      | S_PREFETCHNTA op => PREFETCHNTA op
                      | S_SFENCE => SFENCE
                    end
               in (pre,i) %% pair_t prefix_t instruction_t)} :::
    ast_env_nil.
  Hint Unfold instr_grammar_env: env_unfold_db.

  Definition instruction_grammar : wf_bigrammar (pair_t prefix_t instruction_t).
    gen_ast_defs instr_grammar_env.
    refine (gr @ (mp: _ -> [|pair_t prefix_t instruction_t|])
               & (fun u:[|pair_t prefix_t instruction_t|] =>
                   let (pre,i):=u in
                   match i with
                     | AAA => case0 (pre,I_AAA)
                     | AAD => case0 (pre,I_AAD)
                     | AAM => case0 (pre,I_AAM)
                     | AAS => case0 (pre,I_AAS)
                     | CLC => case0 (pre,I_CLC)
                     | CLD => case0 (pre,I_CLD)
                     | CLI => case0 (pre,I_CLI)
                     | CLTS => case0 (pre,I_CLTS)
                     | CMC => case0 (pre,I_CMC)
                     | CPUID => case0 (pre,I_CPUID)
                     | DAA => case0 (pre,I_DAA)
                     | DAS => case0 (pre,I_DAS)
                     | HLT => case0 (pre,I_HLT)
                     | INT => case0 (pre,I_INT)
                     | INTO => case0 (pre,I_INTO)
                     | INVD => case0 (pre,I_INVD)
                     | IRET => case0 (pre,I_IRET)
                     | LAHF => case0 (pre,I_LAHF)
                     | LEAVE => case0 (pre,I_LEAVE)
                     | POPA => case0 (pre,I_POPA)
                     | POPF => case0 (pre,I_POPF)
                     | PUSHA => case0 (pre,I_PUSHA)
                     | PUSHF => case0 (pre,I_PUSHF)
                     | RDMSR => case0 (pre,I_RDMSR)
                     | RDPMC => case0 (pre,I_RDPMC)
                     | RDTSC => case0 (pre,I_RDTSC)
                     | RDTSCP => case0 (pre,I_RDTSCP)
                     | RSM => case0 (pre,I_RSM)
                     | SAHF => case0 (pre,I_SAHF)
                     | STC => case0 (pre,I_STC)
                     | STD => case0 (pre,I_STD)
                     | STI => case0 (pre,I_STI)
                     | UD2 => case0 (pre,I_UD2)
                     | WBINVD => case0 (pre,I_WBINVD)
                     | WRMSR => case0 (pre,I_WRMSR)
                     | XLAT => case0 (pre,I_XLAT)

                     | ARPL op1 op2 => case1 (pre,I_ARPL op1 op2)
                     | BOUND op1 op2 => case1 (pre,I_BOUND op1 op2)
                     | BSF op1 op2 => case1 (pre,I_BSF op1 op2)
                     | BSR op1 op2 => case1 (pre,I_BSR op1 op2)
                     | BSWAP r => case1 (pre,I_BSWAP r)
                     | BT op1 op2 => case1 (pre,I_BT op1 op2)
                     | CALL near abs op sel => case1 (pre,I_CALL near abs op sel)
                     | IN w p => case1 (pre,I_IN w p)
                     | INTn it => case1 (pre,I_INTn it)
                     | INVLPG op => case1 (pre,I_INVLPG op)
                     | Jcc ct disp => case1 (pre,I_Jcc ct disp)
                     | JCXZ b => case1 (pre,I_JCXZ b)
                     | JMP near abs op sel => case1 (pre,I_JMP near abs op sel)
                     | LAR op1 op2 => case1 (pre,I_LAR op1 op2)
                     | LDS op1 op2 => case1 (pre,I_LDS op1 op2)
                     | LEA op1 op2 => case1 (pre,I_LEA op1 op2)
                     | LES op1 op2 => case1 (pre,I_LES op1 op2)
                     | LFS op1 op2 => case1 (pre,I_LFS op1 op2)
                     | LGDT op => case1 (pre,I_LGDT op)
                     | LGS op1 op2 => case1 (pre,I_LGS op1 op2)
                     | LIDT op => case1 (pre,I_LIDT op)
                     | LLDT op => case1 (pre,I_LLDT op)
                     | LMSW op => case1 (pre,I_LMSW op)
                     | LOOP disp => case1 (pre,I_LOOP disp)
                     | LOOPZ disp => case1 (pre,I_LOOPZ disp)
                     | LOOPNZ disp => case1 (pre,I_LOOPNZ disp)
                     | LSL op1 op2 => case1 (pre,I_LSL op1 op2)
                     | LSS op1 op2 => case1 (pre,I_LSS op1 op2)
                     | LTR op => case1 (pre,I_LTR op)

                     | MOVCR d cr r => case2 (pre,I_MOVCR d cr r)
                     | MOVDR d cr r => case2 (pre,I_MOVDR d cr r)
                     | MOVSR d cr r => case2 (pre,I_MOVSR d cr r)
                     | MOVBE op1 op2 => case2 (pre,I_MOVBE op1 op2)
                     | OUT w p => case2 (pre,I_OUT w p)
                     | POP op => case2 (pre,I_POP op)
                     | POPSR sr => case2 (pre,I_POPSR sr)
                     | PUSH w op => case2 (pre,I_PUSH w op)
                     | PUSHSR sr => case2 (pre,I_PUSHSR sr)
                     | RCL w op1 ri => case2 (pre,I_RCL w op1 ri)
                     | RCR w op1 ri => case2 (pre,I_RCR w op1 ri)
                     | SETcc ct op => case2 (pre,I_SETcc ct op)
                     | SGDT op => case2 (pre,I_SGDT op)
                     | SIDT op => case2 (pre,I_SIDT op)
                     | SLDT op => case2 (pre,I_SLDT op)
                     | SMSW op => case2 (pre,I_SMSW op)
                     | STR op => case2 (pre,I_STR op)
                     | VERR op => case2 (pre,I_VERR op)
                     | VERW op => case2 (pre,I_VERW op)
                                          
                     | INS b => case3 (pre,I_INS b)
                     | OUTS b => case3 (pre,I_OUTS b)
                     | MOVS b => case3 (pre,I_MOVS b)
                     | LODS b => case3 (pre,I_LODS b)
                     | STOS b => case3 (pre,I_STOS b)
                     | RET ss disp => case3 (pre,I_RET ss disp)
                     | CMPS b => case3 (pre,I_CMPS b)
                     | SCAS b => case3 (pre,I_SCAS b)

                     | ADC w op1 op2 => case4 (pre, I_ADC w op1 op2)
                     | ADD w op1 op2 => case4 (pre, I_ADD w op1 op2)
                     | AND w op1 op2 => case4 (pre, I_AND w op1 op2)
                     | BTC op1 op2 => case4 (pre, I_BTC op1 op2)
                     | BTR op1 op2 => case4 (pre, I_BTR op1 op2)
                     | BTS op1 op2 => case4 (pre, I_BTS op1 op2)
                     | CMP w op1 op2 => case4 (pre, I_CMP w op1 op2)
                     | CMPXCHG w op1 op2 => case4 (pre, I_CMPXCHG w op1 op2)
                     | DEC w op1 => case4 (pre, I_DEC w op1)
                     | IMUL w op1 opopt iopt  => case4 (pre, I_IMUL w op1 opopt iopt)
                     | INC w op1 => case4 (pre, I_INC w op1)
                     | MOV w op1 op2 => case4 (pre, I_MOV w op1 op2)
                     | NEG w op => case4 (pre, I_NEG w op)
                     | NOT w op => case4 (pre, I_NOT w op)
                     | OR w op1 op2 => case4 (pre, I_OR w op1 op2)
                     | SBB w op1 op2 => case4 (pre, I_SBB w op1 op2)
                     | SUB w op1 op2 => case4 (pre, I_SUB w op1 op2)
                     | TEST w op1 op2 => case4 (pre, I_TEST w op1 op2)
                     | XADD w op1 op2 => case4 (pre, I_XADD w op1 op2)
                     | XCHG w op1 op2 => case4 (pre, I_XCHG w op1 op2)
                     | XOR w op1 op2 => case4 (pre, I_XOR w op1 op2)

                     | CDQ => case5 (pre, I_CDQ)
                     | CMOVcc ct op1 op2 => case5 (pre, I_CMOVcc ct op1 op2)
                     | CWDE => case5 (pre, I_CWDE)
                     | DIV w op1 => case5 (pre, I_DIV w op1)
                     | IDIV w op1 => case5 (pre, I_IDIV w op1)
                     | MOVSX w op1 op2 => case5 (pre, I_MOVSX w op1 op2)
                     | MOVZX w op1 op2 => case5 (pre, I_MOVZX w op1 op2)
                     | MUL w op1 => case5 (pre, I_MUL w op1)
                     | NOP op => case5 (pre, I_NOP op)
                     | ROL w op1 ri => case5 (pre, I_ROL w op1 ri)
                     | ROR w op1 ri => case5 (pre, I_ROR w op1 ri)
                     | SAR w op1 ri => case5 (pre, I_SAR w op1 ri)
                     | SHL w op1 ri => case5 (pre, I_SHL w op1 ri)
                     | SHLD op1 r ri => case5 (pre, I_SHLD op1 r ri)
                     | SHR w op1 ri => case5 (pre, I_SHR w op1 ri)
                     | SHRD op1 r ri => case5 (pre, I_SHRD op1 r ri)

                     | F2XM1 => case6 (pre, F_F2XM1)
                     | FABS => case6 (pre, F_FABS)
                     | FADD z op1 => case6 (pre, F_FADD z op1)
                     | FADDP op => case6 (pre, F_FADDP op)
                     | FBLD op => case6 (pre, F_FBLD op)
                     | FBSTP op => case6 (pre, F_FBSTP op)
                     | FCHS => case6 (pre, F_FCHS)
                     | FCMOVcc ct op => case6 (pre, F_FCMOVcc ct op)
                     | FCOM op => case6 (pre, F_FCOM op)
                     | FCOMP op => case6 (pre, F_FCOMP op)
                     | FCOMPP => case6 (pre, F_FCOMPP)
                     | FCOMIP op => case6 (pre, F_FCOMIP op)
                     | FCOS => case6 (pre, F_FCOS)
                     | FDECSTP => case6 (pre, F_FDECSTP)
                     | FDIV z op => case6 (pre, F_FDIV z op)
                     | FDIVP op => case6 (pre, F_FDIVP op)
                     | FDIVR z op => case6 (pre, F_FDIVR z op)
                     | FDIVRP op => case6 (pre, F_FDIVRP op)
                     | FFREE op => case6 (pre, F_FFREE op)
                     | FIADD op => case6 (pre, F_FIADD op)
                     | FICOM op => case6 (pre, F_FICOM op)
                     | FICOMP op => case6 (pre, F_FICOMP op)
                     | FIDIV op => case6 (pre, F_FIDIV op)
                     | FIDIVR op => case6 (pre, F_FIDIVR op)
                     | FILD op => case6 (pre, F_FILD op)
                     | FIMUL op => case6 (pre, F_FIMUL op)
                     | FINCSTP => case6 (pre, F_FINCSTP)
                     | FIST op => case6 (pre, F_FIST op)
                     | FISTP op => case6 (pre, F_FISTP op)
                     | FISUB op => case6 (pre, F_FISUB op)
                     | FISUBR op => case6 (pre, F_FISUBR op)
                     | FLD op => case6 (pre, F_FLD op)
                     | FLD1 => case6 (pre, F_FLD1)
                     | FLDCW op => case6 (pre, F_FLDCW op)
                     | FLDENV op => case6 (pre, F_FLDENV op)
                     | FLDL2E => case6 (pre, F_FLDL2E)
                     | FLDL2T => case6 (pre, F_FLDL2T)
                     | FLDLG2 => case6 (pre, F_FLDLG2)
                     | FLDLN2 => case6 (pre, F_FLDLN2)
                     | FLDPI => case6 (pre, F_FLDPI)
                     | FLDZ => case6 (pre, F_FLDZ)
                     | FMUL z op => case6 (pre, F_FMUL z op)
                     | FMULP op => case6 (pre, F_FMULP op)

                     | FNCLEX => case7 (pre, F_FNCLEX)
                     | FNINIT => case7 (pre, F_FNINIT)
                     | FNOP => case7 (pre, F_FNOP)
                     | FNSAVE op => case7 (pre, F_FNSAVE op)
                     | FNSTCW op => case7 (pre, F_FNSTCW op)
                     | FNSTSW op => case7 (pre, F_FNSTSW op)
                     | FPATAN => case7 (pre, F_FPATAN)
                     | FPREM => case7 (pre, F_FPREM)
                     | FPREM1 => case7 (pre, F_FPREM1)
                     | FPTAN => case7 (pre, F_FPTAN)
                     | FRNDINT => case7 (pre, F_FRNDINT)
                     | FRSTOR op => case7 (pre, F_FRSTOR op)
                     | FSCALE => case7 (pre, F_FSCALE)
                     | FSIN => case7 (pre, F_FSIN)
                     | FSINCOS => case7 (pre, F_FSINCOS)
                     | FSQRT => case7 (pre, F_FSQRT)
                     | FST op => case7 (pre, F_FST op)
                     | FSTENV op => case7 (pre, F_FSTENV op)
                     | FSTP op => case7 (pre, F_FSTP op)
                     | FSUB z op => case7 (pre, F_FSUB z op)
                     | FSUBP op => case7 (pre, F_FSUBP op)
                     | FSUBR z op => case7 (pre, F_FSUBR z op)
                     | FSUBRP op => case7 (pre, F_FSUBRP op)
                     | FTST => case7 (pre, F_FTST)
                     | FUCOM op => case7 (pre, F_FUCOM op)
                     | FUCOMP op => case7 (pre, F_FUCOMP op)
                     | FUCOMPP => case7 (pre, F_FUCOMPP)
                     | FUCOMI op => case7 (pre, F_FUCOMI op)
                     | FUCOMIP op => case7 (pre, F_FUCOMIP op)
                     | FXAM => case7 (pre, F_FXAM)
                     | FXCH op => case7 (pre, F_FXCH op)
                     | FXTRACT => case7 (pre, F_FXTRACT)
                     | FYL2X => case7 (pre, F_FYL2X)
                     | FYL2XP1 => case7 (pre, F_FYL2XP1)
                     | FWAIT => case7 (pre, F_FWAIT)

                     | EMMS => case8 (pre, M_EMMS)
                     | MOVD op1 op2 => case8 (pre, M_MOVD op1 op2)
                     | MOVQ op1 op2 => case8 (pre, M_MOVQ op1 op2)
                     | PACKSSDW op1 op2 => case8 (pre, M_PACKSSDW op1 op2)
                     | PACKSSWB op1 op2 => case8 (pre, M_PACKSSWB op1 op2)
                     | PACKUSWB op1 op2 => case8 (pre, M_PACKUSWB op1 op2)
                     | PADD gg op1 op2 => case8 (pre, M_PADD gg op1 op2)
                     | PADDS gg op1 op2 => case8 (pre, M_PADDS gg op1 op2)
                     | PADDUS gg op1 op2 => case8 (pre, M_PADDUS gg op1 op2)
                     | PAND op1 op2 => case8 (pre, M_PAND op1 op2)
                     | PANDN op1 op2 => case8 (pre, M_PANDN op1 op2)
                     | PCMPEQ gg op1 op2 => case8 (pre, M_PCMPEQ gg op1 op2)
                     | PCMPGT gg op1 op2 => case8 (pre, M_PCMPGT gg op1 op2)
                     | PMADDWD op1 op2 => case8 (pre, M_PMADDWD op1 op2)
                     | PMULHUW op1 op2 => case8 (pre, M_PMULHUW op1 op2)
                     | PMULHW op1 op2 => case8 (pre, M_PMULHW op1 op2)
                     | PMULLW op1 op2 => case8 (pre, M_PMULLW op1 op2)
                     | POR op1 op2 => case8 (pre, M_POR op1 op2)
                     | PSLL gg op1 op2 => case8 (pre, M_PSLL gg op1 op2)
                     | PSRA gg op1 op2 => case8 (pre, M_PSRA gg op1 op2)
                     | PSRL gg op1 op2 => case8 (pre, M_PSRL gg op1 op2)
                     | PSUB gg op1 op2 => case8 (pre, M_PSUB gg op1 op2)
                     | PSUBS gg op1 op2 => case8 (pre, M_PSUBS gg op1 op2)
                     | PSUBUS gg op1 op2 => case8 (pre, M_PSUBUS gg op1 op2)
                     | PUNPCKH gg op1 op2 => case8 (pre, M_PUNPCKH gg op1 op2)
                     | PUNPCKL gg op1 op2 => case8 (pre, M_PUNPCKL gg op1 op2)
                     | PXOR op1 op2 => case8 (pre, M_PXOR op1 op2)

                     | ADDPS op1 op2 => case9 (pre, S_ADDPS op1 op2)
                     | ADDSS op1 op2 => case9 (pre, S_ADDSS op1 op2)
                     | ANDNPS op1 op2 => case9 (pre, S_ANDNPS op1 op2)
                     | ANDPS op1 op2 => case9 (pre, S_ANDPS op1 op2)
                     | CMPPS op1 op2 imm => case9 (pre, S_CMPPS op1 op2 imm)
                     | CMPSS op1 op2 imm => case9 (pre, S_CMPSS op1 op2 imm)
                     | COMISS op1 op2 => case9 (pre, S_COMISS op1 op2)
                     | CVTPI2PS op1 op2 => case9 (pre, S_CVTPI2PS op1 op2)
                     | CVTPS2PI op1 op2 => case9 (pre, S_CVTPS2PI op1 op2)
                     | CVTSI2SS op1 op2 => case9 (pre, S_CVTSI2SS op1 op2)
                     | CVTSS2SI op1 op2 => case9 (pre, S_CVTSS2SI op1 op2)
                     | CVTTPS2PI op1 op2 => case9 (pre, S_CVTTPS2PI op1 op2)
                     | CVTTSS2SI op1 op2 => case9 (pre, S_CVTTSS2SI op1 op2)
                     | DIVPS op1 op2 => case9 (pre, S_DIVPS op1 op2)
                     | DIVSS op1 op2 => case9 (pre, S_DIVSS op1 op2)
                     | LDMXCSR op => case9 (pre, S_LDMXCSR op)
                     | MAXPS op1 op2 => case9 (pre, S_MAXPS op1 op2)
                     | MAXSS op1 op2 => case9 (pre, S_MAXSS op1 op2)
                     | MINPS op1 op2 => case9 (pre, S_MINPS op1 op2)
                     | MINSS op1 op2 => case9 (pre, S_MINSS op1 op2)
                     | MOVAPS op1 op2 => case9 (pre, S_MOVAPS op1 op2)
                     | MOVHLPS op1 op2 => case9 (pre, S_MOVHLPS op1 op2)
                     | MOVHPS op1 op2 => case9 (pre, S_MOVHPS op1 op2)
                     | MOVLHPS op1 op2 => case9 (pre, S_MOVLHPS op1 op2)
                     | MOVLPS op1 op2 => case9 (pre, S_MOVLPS op1 op2)
                     | MOVMSKPS op1 op2 => case9 (pre, S_MOVMSKPS op1 op2)
                     | MOVSS op1 op2 => case9 (pre, S_MOVSS op1 op2)
                     | MOVUPS op1 op2 => case9 (pre, S_MOVUPS op1 op2)
                     | MULPS op1 op2 => case9 (pre, S_MULPS op1 op2)
                     | MULSS op1 op2 => case9 (pre, S_MULSS op1 op2)
                     | ORPS op1 op2 => case9 (pre, S_ORPS op1 op2)
                     | RCPPS op1 op2 => case9 (pre, S_RCPPS op1 op2)
                     | RCPSS op1 op2 => case9 (pre, S_RCPSS op1 op2)
                     | RSQRTPS op1 op2 => case9 (pre, S_RSQRTPS op1 op2)
                     | RSQRTSS op1 op2 => case9 (pre, S_RSQRTSS op1 op2)

                     | SHUFPS op1 op2 imm => case10 (pre, S_SHUFPS op1 op2 imm)
                     | SQRTPS op1 op2 => case10 (pre, S_SQRTPS op1 op2)
                     | SQRTSS op1 op2 => case10 (pre, S_SQRTSS op1 op2)
                     | STMXCSR op => case10 (pre, S_STMXCSR op)
                     | SUBPS op1 op2 => case10 (pre, S_SUBPS op1 op2)
                     | SUBSS op1 op2 => case10 (pre, S_SUBSS op1 op2)
                     | UCOMISS op1 op2 => case10 (pre, S_UCOMISS op1 op2)
                     | UNPCKHPS op1 op2 => case10 (pre, S_UNPCKHPS op1 op2)
                     | UNPCKLPS op1 op2 => case10 (pre, S_UNPCKLPS op1 op2)
                     | XORPS op1 op2 => case10 (pre, S_XORPS op1 op2)
                     | PAVGB op1 op2 => case10 (pre, S_PAVGB op1 op2)
                     | PEXTRW op1 op2 imm => case10 (pre, S_PEXTRW op1 op2 imm)
                     | PINSRW op1 op2 imm => case10 (pre, S_PINSRW op1 op2 imm)
                     | PMAXSW op1 op2 => case10 (pre, S_PMAXSW op1 op2)
                     | PMAXUB op1 op2 => case10 (pre, S_PMAXUB op1 op2)
                     | PMINSW op1 op2 => case10 (pre, S_PMINSW op1 op2)
                     | PMINUB op1 op2 => case10 (pre, S_PMINUB op1 op2)
                     | PMOVMSKB op1 op2 => case10 (pre, S_PMOVMSKB op1 op2)
                     | PSADBW op1 op2 => case10 (pre, S_PSADBW op1 op2)
                     | PSHUFW op1 op2 imm => case10 (pre, S_PSHUFW op1 op2 imm)
                     | MASKMOVQ op1 op2 => case10 (pre, S_MASKMOVQ op1 op2)
                     | MOVNTPS op1 op2 => case10 (pre, S_MOVNTPS op1 op2)
                     | MOVNTQ op1 op2 => case10 (pre, S_MOVNTQ op1 op2)
                     | PREFETCHT0 op => case10 (pre, S_PREFETCHT0 op)
                     | PREFETCHT1 op => case10 (pre, S_PREFETCHT1 op)
                     | PREFETCHT2 op => case10 (pre, S_PREFETCHT2 op)
                     | PREFETCHNTA op => case10 (pre, S_PREFETCHNTA op)
                     | SFENCE => case10 (pre, S_SFENCE)

                     (* | _ => None *)
                   end)
               & _); clear_ast_defs;
    unfold invertible; split; [unfold printable | unfold parsable]; 
    compute [snd fst]; intros.
    - destruct_union; destruct v as [pre hi];
        abstract (destruct hi; printable_tac).
    - Time abstract (destruct w as [pre i]; destruct i; parsable_tac).
  Defined.

  (** Starting constructing the x86 parser *)
  Require Import Parser.

  Definition instruction_regexp :=
    projT1 (split_grammar (bigrammar_to_grammar (proj1_sig instruction_grammar))).

  Definition ini_decoder_state :=
    initial_parser_state (bigrammar_to_grammar (proj1_sig instruction_grammar)).

  (* Preventing Coq from expanding the def of ini_decoder_state *)
  Module Type ABSTRACT_INI_DECODER_STATE_SIG.
    Parameter abs_ini_decoder_state :
      instParserState
        (Pair_t prefix_t instruction_t)
        instruction_regexp.
    Parameter ini_decoder_state_eq :
        abs_ini_decoder_state = ini_decoder_state.
  End ABSTRACT_INI_DECODER_STATE_SIG.

  Module ABSTRACT_INI_DECODER_STATE : ABSTRACT_INI_DECODER_STATE_SIG.
    Definition abs_ini_decoder_state := ini_decoder_state.
    Definition ini_decoder_state_eq := eq_refl ini_decoder_state.
  End ABSTRACT_INI_DECODER_STATE.

  Lemma byte_less_than_num_tokens (b:int8) :
    (Z.to_nat (Word.intval _ b) < num_tokens)%nat.
  Proof.
    destruct b. destruct intrange. simpl. assert (256 = (Z.to_nat 256%Z))%nat. auto.
    unfold num_tokens, ParserArg.X86_PARSER_ARG.num_tokens.
    rewrite H. apply Z2Nat.inj_lt ; auto. omega.
  Qed.

  Definition ParseState_t := instParserState (Pair_t prefix_t instruction_t)
                                             instruction_regexp.

  Definition parse_byte (ps: ParseState_t) (byte:int8) :
    ParseState_t * list (prefix * instr) :=
    parse_token ps (byte_less_than_num_tokens byte).

(* End X86_PARSER. *)

