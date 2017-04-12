(** Gang Tan: Bi-directional grammars for x86 parsing and pretty-printing *)

(* This file glues all individual x86 instruction bigrammars in
   Decode_ins.v into one big bigrammar. *)

Require Import Coq.Init.Logic.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Program.Program.

Require Import Coqlib.
Require Import CommonTacs.
Require Import Shared.Maps.

Unset Automatic Introduction.
Set Implicit Arguments.

  Require Import X86Syntax.
  Require X86Model.ParserArg.
  Import ParserArg.X86_PARSER_ARG.
  Require Import X86Model.BiGrammar.
  Require Import X86BG_ins.

  Definition lock_b : wf_bigrammar lock_or_rep_t. 
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

  Definition rep_or_repn_b : wf_bigrammar lock_or_rep_t. 
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

  Definition rep_b : wf_bigrammar lock_or_rep_t. 
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

  Definition lock_or_rep_b : wf_bigrammar lock_or_rep_t.
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
    {{0, "0010" $$ ! "1110", (fun v => CS %% segment_register_t)}} :::
    {{1, "0011" $$ ! "0110", (fun v => SS %% segment_register_t)}} :::
    {{2, "0011" $$ ! "1110", (fun v => DS %% segment_register_t)}} :::
    {{3, "0010" $$ ! "0110", (fun v => ES %% segment_register_t)}} :::
    {{4, "0110" $$ ! "0100", (fun v => FS %% segment_register_t)}} :::
    {{5, "0110" $$ ! "0101", (fun v => GS %% segment_register_t)}} :::
    ast_env_nil.
  Hint Unfold segment_override_env : env_unfold_db.

  Definition segment_override_b : wf_bigrammar segment_register_t.
    gen_ast_defs segment_override_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u => 
                    match u with 
                      | CS => inv_case_some case0 ()
                      | SS => inv_case_some case1 ()
                      | DS => inv_case_some case2 ()
                      | ES => inv_case_some case3 ()
                      | FS => inv_case_some case4 ()
                      | GS => inv_case_some case5 ()
                    end)
               & _); ins_invertible_tac.
  Defined.

  Definition op_s := "01100110".

  Lemma op_s_nonempty: non_empty (` (! op_s)).
  Proof. apply bitsmatch_nonempty. unfold op_s. crush. Qed.

  Definition op_override_b: wf_bigrammar bool_t.
    refine((op_s $$ star (! op_s) op_s_nonempty)
             @ (fun _ => true %% bool_t)
             & (fun b:bool => if b then Some nil else None)
             & _); ins_invertible_tac.
  Defined.

  (* Definition op_override_env : AST_Env bool_t := *)
  (*   {{0, ! op_s, (fun _ => true %% bool_t)}} ::: *)
  (*   {{1, ! (op_s ++ op_s), (fun _ => true %% bool_t)}} ::: *)
  (*   {{2, ! (op_s ++ op_s ++ op_s), (fun _ => true %% bool_t)}} ::: *)
  (*   {{3, ! (op_s ++ op_s ++ op_s ++ op_s), (fun _ => true %% bool_t)}} ::: *)
  (*   {{4, ! (op_s ++ op_s ++ op_s ++ op_s ++ op_s),  *)
  (*       (fun _ => true %% bool_t)}} ::: *)
  (*   {{5, ! (op_s ++ op_s ++ op_s ++ op_s ++ op_s ++ op_s), *)
  (*       (fun _ => true %% bool_t)}} ::: *)
  (*   {{6, ! (op_s ++ op_s ++ op_s ++ op_s ++ op_s ++ op_s ++ op_s), *)
  (*       (fun _ => true %% bool_t)}} ::: *)
  (*   {{7, ! (op_s ++ op_s ++ op_s ++ op_s ++ op_s ++ op_s ++ op_s ++ op_s), *)
  (*      (fun _ => true %% bool_t)}} ::: *)
  (*   ast_env_nil. *)
  (* Hint Unfold op_override_env : env_unfold_db. *)

  (* Definition op_override_b : wf_bigrammar bool_t. *)
  (*   gen_ast_defs op_override_env. *)
  (*   refine ((comb_bigrammar gt) @ (comb_map gt) *)
  (*              & (fun b:bool => if b then inv_case_some case0 () else None) *)
  (*              & _); ins_invertible_tac. *)
  (* Defined. *)

  (* Definition op_override_b : wf_bigrammar bool_t. *)
  (*   refine ("0110" $$ ! "0110" *)
  (*             @ (fun v => true %% bool_t) *)
  (*             & (fun u => *)
  (*                  match u with *)
  (*                    | true => Some () *)
  (*                    | false => None *)
  (*                  end) *)
  (*             & _); ins_invertible_tac. *)
  (* Defined. *)

  Definition addr_override_b : wf_bigrammar bool_t.
    refine ("0110" $$ ! "0111"
              @ (fun v => true %% bool_t)
              & (fun u =>
                   match u with
                     | true => Some ()
                     | false => None
                   end)
              & _); ins_invertible_tac.
  Defined.

  Lemma op_override_b_rng_inv op :
    in_bigrammar_rng (` op_override_b) op -> op = true.
  Proof. unfold op_override_b; intros; ins_ibr_sim. Qed.

  (* Lemma op_override_b_rng_inv op : *)
  (*   in_bigrammar_rng (` op_override_b) op -> op = true. *)
  (* Proof. unfold op_override_b; intros; ins_ibr_sim.  *)
  (*   compute [interp_ttype comb_bigrammar] in *. *)
  (*   destruct_all; trivial. *)
  (* Qed. *)

  (* Lemma op_override_b_rng_inv op : *)
  (*   in_bigrammar_rng (` op_override_b) op -> op = true. *)
  (* Proof. unfold op_override_b; intros; ins_ibr_sim. Qed. *)

  Definition opt2b (a: option bool) (default: bool) :=
    match a with
      | Some b => b
      | None => default
    end.

  (** In lock_or_rep, only rep can be used; 
      segment_override and op_override are allowed. *)
  Definition prefix_grammar_rep : wf_bigrammar prefix_t.
    refine ((option_perm3 rep_b segment_override_b op_override_b)
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
    refine ((option_perm3 rep_or_repn_b segment_override_b op_override_b)
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
    refine ((option_perm3_variation lock_b segment_override_b op_override_b)
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
    refine ((option_perm2 lock_b segment_override_b)
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
    refine ((option_perm2_variation segment_override_b op_override_b)
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
    refine ((option_perm2 segment_override_b op_override_b)
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
    refine ((option_perm segment_override_b)
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
        apply op_override_b_rng_inv in H
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
        apply op_override_b_rng_inv in H
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

  (* Specialized tactic for invertibility proofs when combining instructions *)
  Local Ltac ci_invertible_tac :=
    apply strong_inv_imp_inv; unfold strong_invertible;
    try clear_gt; split; [unfold printable | unfold parsable];
    compute [snd fst]; compute [comb_bigrammar comb_map inv_case_some];
    [(clear_ast_defs; compute [interp_ttype inv_case]) | idtac]; intros;
    [try (abstract (destruct_all; trivial); fail) |
     try (abstract (
            match goal with
            | [ |- _ = ?w] => destruct w; inversion H; trivial
            end); fail)].

  Definition i_instr1_env : AST_Env i_instr1_t := 
    {{0, AAA_b, (fun v => I_AAA %% i_instr1_t)}} :::
    {{1, AAD_b, (fun v => I_AAD %% i_instr1_t)}} :::
    {{2, AAM_b, (fun v => I_AAM %% i_instr1_t)}} :::
    {{3, AAS_b, (fun v => I_AAS %% i_instr1_t)}} :::
    {{4, CLC_b, (fun v => I_CLC %% i_instr1_t)}} :::
    {{5, CLD_b, (fun v => I_CLD %% i_instr1_t)}} :::
    {{6, CLI_b, (fun v => I_CLI %% i_instr1_t)}} :::
    {{7, CLTS_b, (fun v => I_CLTS %% i_instr1_t)}} :::
    {{8, CMC_b, (fun v => I_CMC %% i_instr1_t)}} :::
    {{9, CPUID_b, (fun v => I_CPUID %% i_instr1_t)}} :::
    {{10, DAA_b, (fun v => I_DAA %% i_instr1_t)}} :::
    {{11, DAS_b, (fun v => I_DAS %% i_instr1_t)}} :::
    {{12, HLT_b, (fun v => I_HLT %% i_instr1_t)}} :::
    {{13, INT_b, (fun v => I_INT %% i_instr1_t)}} :::
    {{14, INTO_b, (fun v => I_INTO %% i_instr1_t)}} :::
    {{15, INVD_b, (fun v => I_INVD %% i_instr1_t)}} :::
    {{16, IRET_b, (fun v => I_IRET %% i_instr1_t)}} :::
    {{17, LAHF_b, (fun v => I_LAHF %% i_instr1_t)}} :::
    {{18, LEAVE_b, (fun v => I_LEAVE %% i_instr1_t)}} :::
    {{19, POPA_b, (fun v => I_POPA %% i_instr1_t)}} :::
    {{20, POPF_b, (fun v => I_POPF %% i_instr1_t)}} :::
    {{21, PUSHA_b, (fun v => I_PUSHA %% i_instr1_t)}} :::
    {{22, PUSHF_b, (fun v => I_PUSHF %% i_instr1_t)}} :::
    {{23, RDMSR_b, (fun v => I_RDMSR %% i_instr1_t)}} :::
    {{24, RDPMC_b, (fun v => I_RDPMC %% i_instr1_t)}} :::
    {{25, RDTSC_b, (fun v => I_RDTSC %% i_instr1_t)}} :::
    {{26, RDTSCP_b, (fun v => I_RDTSCP %% i_instr1_t)}} :::
    {{27, RSM_b, (fun v => I_RSM %% i_instr1_t)}} :::
    {{28, SAHF_b, (fun v => I_SAHF %% i_instr1_t)}} :::
    {{29, STC_b, (fun v => I_STC %% i_instr1_t)}} :::
    {{30, STD_b, (fun v => I_STD %% i_instr1_t)}} :::
    {{31, STI_b, (fun v => I_STI %% i_instr1_t)}} :::
    {{32, UD2_b, (fun v => I_UD2 %% i_instr1_t)}} :::
    {{33, WBINVD_b, (fun v => I_WBINVD %% i_instr1_t)}} :::
    {{34, WRMSR_b, (fun v => I_WRMSR %% i_instr1_t)}} :::
    {{35, XLAT_b, (fun v => I_XLAT %% i_instr1_t)}} :::
    ast_env_nil.
  Hint Unfold i_instr1_env: env_unfold_db.

  Definition i_instr1_b : wf_bigrammar i_instr1_t.
    Time gen_ast_defs i_instr1_env.
    Time refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u =>
                    match u with
                      | I_AAA => inv_case_some case0 ()
                      | I_AAD => inv_case_some case1 ()
                      | I_AAM => inv_case_some case2 ()
                      | I_AAS => inv_case_some case3 ()
                      | I_CLC => inv_case_some case4 ()
                      | I_CLD => inv_case_some case5 ()
                      | I_CLI => inv_case_some case6 ()
                      | I_CLTS => inv_case_some case7 ()
                      | I_CMC => inv_case_some case8 ()
                      | I_CPUID => inv_case_some case9 ()
                      | I_DAA => inv_case_some case10 ()
                      | I_DAS => inv_case_some case11 ()
                      | I_HLT => inv_case_some case12 ()
                      | I_INT => inv_case_some case13 ()
                      | I_INTO => inv_case_some case14 ()
                      | I_INVD => inv_case_some case15 ()
                      | I_IRET => inv_case_some case16 ()
                      | I_LAHF => inv_case_some case17 ()
                      | I_LEAVE => inv_case_some case18 ()
                      | I_POPA => inv_case_some case19 ()
                      | I_POPF => inv_case_some case20 ()
                      | I_PUSHA => inv_case_some case21 ()
                      | I_PUSHF => inv_case_some case22 ()
                      | I_RDMSR => inv_case_some case23 ()
                      | I_RDPMC => inv_case_some case24 ()
                      | I_RDTSC => inv_case_some case25 ()
                      | I_RDTSCP => inv_case_some case26 ()
                      | I_RSM => inv_case_some case27 ()
                      | I_SAHF => inv_case_some case28 ()
                      | I_STC => inv_case_some case29 ()
                      | I_STD => inv_case_some case30 ()
                      | I_STI => inv_case_some case31 ()
                      | I_UD2 => inv_case_some case32 ()
                      | I_WBINVD => inv_case_some case33 ()
                      | I_WRMSR => inv_case_some case34 ()
                      | I_XLAT => inv_case_some case35 ()
                    end)
               & _). Time ci_invertible_tac.
  Time Defined.

  Definition i_instr2_env : AST_Env i_instr2_t := 
    {{0, ARPL_b, (fun v => match v with (op1,op2) => I_ARPL op1 op2
                          end %% i_instr2_t)}} :::
    {{1, BOUND_b, (fun v => match v with (op1,op2) => I_BOUND op1 op2
                          end %% i_instr2_t)}} :::
    {{2, BSF_b, (fun v => match v with (op1,op2) => I_BSF op1 op2
                          end %% i_instr2_t)}} :::
    {{3, BSR_b, (fun v => match v with (op1,op2) => I_BSR op1 op2
                          end %% i_instr2_t)}} :::
    {{4, BSWAP_b, (fun r => I_BSWAP r %% i_instr2_t)}} :::
    {{5, BT_b, (fun v => match v with (op1,op2) => I_BT op1 op2
                          end %% i_instr2_t)}} :::
    {{6, CALL_b, (fun v => match v with
                              (near,(abs,(op1,sel))) => I_CALL near abs op1 sel
                          end %% i_instr2_t)}} :::
    {{7, IN_b, (fun v => match v with (w,p) => I_IN w p
                          end %% i_instr2_t)}} :::
    {{8, INTn_b, (fun it => I_INTn it %% i_instr2_t)}} :::
    {{9, INVLPG_b, (fun op => I_INVLPG op %% i_instr2_t)}} :::
    {{10, Jcc_b, (fun v => match v with (ct,disp) => I_Jcc ct disp
                          end %% i_instr2_t)}} :::
    {{11, JCXZ_b, (fun b => I_JCXZ b %% i_instr2_t)}} :::
    {{12, JMP_b, (fun v => match v with
                              (near,(abs,(op1,sel))) => I_JMP near abs op1 sel
                          end %% i_instr2_t)}} :::
    {{13, LAR_b, (fun v => match v with (op1,op2) => I_LAR op1 op2
                          end %% i_instr2_t)}} :::
    {{14, LDS_b, (fun v => match v with (op1,op2) => I_LDS op1 op2
                          end %% i_instr2_t)}} :::
    {{15, LEA_b, (fun v => match v with (op1,op2) => I_LEA op1 op2
                          end %% i_instr2_t)}} :::
    {{16, LES_b, (fun v => match v with (op1,op2) => I_LES op1 op2
                          end %% i_instr2_t)}} :::
    {{17, LFS_b, (fun v => match v with (op1,op2) => I_LFS op1 op2
                          end %% i_instr2_t)}} :::
    {{18, LGDT_b, (fun op => I_LGDT op %% i_instr2_t)}} :::
    {{19, LGS_b, (fun v => match v with (op1,op2) => I_LGS op1 op2
                          end %% i_instr2_t)}} :::
    {{20, LIDT_b, (fun op => I_LIDT op %% i_instr2_t)}} :::
    {{21, LLDT_b, (fun op => I_LLDT op %% i_instr2_t)}} :::
    {{22, LMSW_b, (fun op => I_LMSW op %% i_instr2_t)}} :::
    {{23, LOOP_b, (fun di => I_LOOP di %% i_instr2_t)}} :::
    {{24, LOOPZ_b, (fun di => I_LOOPZ di %% i_instr2_t)}} :::
    {{25, LOOPNZ_b, (fun di => I_LOOPNZ di %% i_instr2_t)}} :::
    {{26, LSL_b, (fun v => match v with (op1,op2) => I_LSL op1 op2
                          end %% i_instr2_t)}} :::
    {{27, LSS_b, (fun v => match v with (op1,op2) => I_LSS op1 op2
                          end %% i_instr2_t)}} :::
    {{28, LTR_b, (fun op => I_LTR op %% i_instr2_t)}} :::
    ast_env_nil.
  Hint Unfold i_instr2_env: env_unfold_db.

  Definition i_instr2_b : wf_bigrammar i_instr2_t.
    gen_ast_defs i_instr2_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u =>
                    match u with
                      | I_ARPL op1 op2 => inv_case_some case0 (op1,op2)
                      | I_BOUND op1 op2 => inv_case_some case1 (op1,op2)
                      | I_BSF op1 op2 => inv_case_some case2 (op1,op2)
                      | I_BSR op1 op2 => inv_case_some case3 (op1,op2)
                      | I_BSWAP r => inv_case_some case4 r
                      | I_BT op1 op2 => inv_case_some case5 (op1,op2)
                      | I_CALL near abs op1 sel => inv_case_some case6 (near,(abs,(op1,sel)))
                      | I_IN w p => inv_case_some case7 (w,p)
                      | I_INTn it => inv_case_some case8 it
                      | I_INVLPG op => inv_case_some case9 op
                      | I_Jcc ct disp => inv_case_some case10 (ct,disp)
                      | I_JCXZ b => inv_case_some case11 b
                      | I_JMP near abs op1 sel => inv_case_some case12 (near,(abs,(op1,sel)))
                      | I_LAR op1 op2 => inv_case_some case13 (op1,op2)
                      | I_LDS op1 op2 => inv_case_some case14 (op1,op2)
                      | I_LEA op1 op2 => inv_case_some case15 (op1,op2)
                      | I_LES op1 op2 => inv_case_some case16 (op1,op2)
                      | I_LFS op1 op2 => inv_case_some case17 (op1,op2)
                      | I_LGDT op1 => inv_case_some case18 op1
                      | I_LGS op1 op2 => inv_case_some case19 (op1,op2)
                      | I_LIDT op1 => inv_case_some case20 op1
                      | I_LLDT op1 => inv_case_some case21 op1
                      | I_LMSW op1 => inv_case_some case22 op1
                      | I_LOOP disp => inv_case_some case23 disp
                      | I_LOOPZ disp => inv_case_some case24 disp
                      | I_LOOPNZ disp => inv_case_some case25 disp
                      | I_LSL op1 op2 => inv_case_some case26 (op1,op2)
                      | I_LSS op1 op2 => inv_case_some case27 (op1,op2)
                      | I_LTR op1 => inv_case_some case28 op1
                    end)
               & _). Time ci_invertible_tac.
  Time Defined.

  Definition i_instr3_env : AST_Env i_instr3_t := 
    {{0, MOVCR_b, (fun v => match v with (d,(cr,r)) => I_MOVCR d cr r
                          end %% i_instr3_t)}} :::
    {{1, MOVDR_b, (fun v => match v with (d,(cr,r)) => I_MOVDR d cr r
                          end %% i_instr3_t)}} :::
    {{2, MOVSR_b, (fun v => match v with (d,(cr,r)) => I_MOVSR d cr r
                          end %% i_instr3_t)}} :::
    {{3, MOVBE_b, (fun v => match v with (op1,op2) => I_MOVBE op1 op2
                          end %% i_instr3_t)}} :::
    {{4, OUT_b, (fun v => match v with (w,p) => I_OUT w p
                          end %% i_instr3_t)}} :::
    {{5, POP_b, (fun op => I_POP op %% i_instr3_t)}} :::
    {{6, POPSR_b, (fun sr => I_POPSR sr %% i_instr3_t)}} :::
    {{7, PUSH_b, (fun v => match v with (w,op1) => I_PUSH w op1
                          end %% i_instr3_t)}} :::
    {{8, PUSHSR_b, (fun sr => I_PUSHSR sr %% i_instr3_t)}} :::
    {{9, RCL_b, (fun v => match v with (w,(op1,ri)) => I_RCL w op1 ri
                          end %% i_instr3_t)}} :::
    {{10, RCR_b, (fun v => match v with (w,(op1,ri)) => I_RCR w op1 ri
                          end %% i_instr3_t)}} :::
    {{11, SETcc_b, (fun v => match v with (ct,op1) => I_SETcc ct op1
                          end %% i_instr3_t)}} :::
    {{12, SGDT_b, (fun op => I_SGDT op %% i_instr3_t)}} :::
    {{13, SIDT_b, (fun op => I_SIDT op %% i_instr3_t)}} :::
    {{14, SLDT_b, (fun op => I_SLDT op %% i_instr3_t)}} :::
    {{15, SMSW_b, (fun op => I_SMSW op %% i_instr3_t)}} :::
    {{16, STR_b, (fun op => I_STR op %% i_instr3_t)}} :::
    {{17, VERR_b, (fun op => I_VERR op %% i_instr3_t)}} :::
    {{18, VERW_b, (fun op => I_VERW op %% i_instr3_t)}} :::
    ast_env_nil.
  Hint Unfold i_instr3_env: env_unfold_db.

  Definition i_instr3_b : wf_bigrammar i_instr3_t.
    gen_ast_defs i_instr3_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u =>
                    match u with
                      | I_MOVCR d cr r => inv_case_some case0 (d,(cr,r))
                      | I_MOVDR d cr r => inv_case_some case1 (d,(cr,r))
                      | I_MOVSR d cr r => inv_case_some case2 (d,(cr,r))
                      | I_MOVBE op1 op2 => inv_case_some case3 (op1,op2)
                      | I_OUT w p => inv_case_some case4 (w,p)
                      | I_POP op => inv_case_some case5 op
                      | I_POPSR sr => inv_case_some case6 sr
                      | I_PUSH w op1 => inv_case_some case7 (w,op1)
                      | I_PUSHSR sr => inv_case_some case8 sr
                      | I_RCL w op1 ri => inv_case_some case9 (w,(op1,ri))
                      | I_RCR w op1 ri => inv_case_some case10 (w,(op1,ri))
                      | I_SETcc ct op1 => inv_case_some case11 (ct,op1)
                      | I_SGDT op => inv_case_some case12 op
                      | I_SIDT op => inv_case_some case13 op
                      | I_SLDT op => inv_case_some case14 op
                      | I_SMSW op => inv_case_some case15 op
                      | I_STR op => inv_case_some case16 op
                      | I_VERR op => inv_case_some case17 op 
                      | I_VERW op => inv_case_some case18 op 
                    end)
               & _). Time ci_invertible_tac.
  Defined.

  (** This set of instructions can take prefixes in prefix_grammar_rep we
      put RET in this category because it turns out many binaries use "rep
      ret" to avoid the branch prediction panelty in AMD processors; intel
      processor seems to just ignore the rep prefix in "rep ret". *)
  Definition prefix_grammar_rep_env : AST_Env i_instr4_t := 
    {{0, INS_b, (fun v => I_INS v %% i_instr4_t)}} :::
    {{1, OUTS_b, (fun v => I_OUTS v %% i_instr4_t)}} :::
    {{2, MOVS_b, (fun v => I_MOVS v %% i_instr4_t)}} :::
    {{3, LODS_b, (fun v => I_LODS v %% i_instr4_t)}} :::
    {{4, STOS_b, (fun v => I_STOS v %% i_instr4_t)}} :::
    {{5, RET_b, (fun v => I_RET (fst v) (snd v) %% i_instr4_t)}} :::
    ast_env_nil.
     
  (** this set of instructions can take prefixes in prefix_grammar_repn *)
  Definition prefix_grammar_rep_or_repn_env : AST_Env i_instr4_t :=
    {{10, CMPS_b, (fun v => I_CMPS v %% i_instr4_t)}} :::
    {{11, SCAS_b, (fun v => I_SCAS v %% i_instr4_t)}} :::
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
  Hint Unfold i_instr4_grammar_env: env_unfold_db.

  Definition i_instr4_grammar_type : typetree.
    let ige := eval unfold i_instr4_grammar_env in i_instr4_grammar_env in
    let tt:=gen_ttype ige in exact(tt).
  Defined.

  Definition i_instr4_b : wf_bigrammar (pair_t prefix_t i_instr4_t).
    gen_ast_defs i_instr4_grammar_env.
    let gt := eval unfold gt in gt in
    let tm10:= get_tm_by_idx (N.of_nat 10) gt in
    let tm11:= get_tm_by_idx (N.of_nat 11) gt in
    pose (case10:=tm10);
    pose (case11:=tm11).
    refine ((comb_bigrammar gt) @ (comb_map gt)
              & (fun u =>
                   match snd u with
                   | I_INS a1 => 
                     inv_case_some case0 (fst u, a1)
                   | I_OUTS a1 => 
                     inv_case_some case1 (fst u, a1)
                   | I_MOVS a1 =>
                     inv_case_some case2 (fst u, a1)
                   | I_LODS a1 => 
                     inv_case_some case3 (fst u, a1)
                   | I_STOS a1 =>
                     inv_case_some case4 (fst u, a1)
                   | I_RET a1 a2 =>
                     inv_case_some case5 (fst u, (a1,a2))
                   | I_CMPS a1 =>
                     inv_case_some case10 (fst u, a1)
                   | I_SCAS a1 =>
                     inv_case_some case11 (fst u, a1)
                   end)
              & _). ci_invertible_tac.
    - abstract (destruct w as [p ins]; destruct ins; inversion H; trivial).
  Defined.

  (** Instructions that can take prefixes in
      prefix_grammar_lock_with_op_override.  NEG, NOT, and XCHG appear in
      both instr_grammars_lock_with_op_override_env and
      instr_grammars_lock_no_op_override_env since they allow op_override
      prefix to be optional. *)
  Definition prefix_lock_with_op_override_env : AST_Env i_instr5_t :=
    {{0, ADC_b true, (fun v => match v with (b,(op1,op2)) => I_ADC b op1 op2 end
                          %% i_instr5_t)}} :::
    {{1, ADD_b true, (fun v => match v with (b,(op1,op2)) => I_ADD b op1 op2 end
                          %% i_instr5_t)}} :::
    {{2, AND_b true, (fun v => match v with (b,(op1,op2)) => I_AND b op1 op2 end
                          %% i_instr5_t)}} :::
    {{3, DEC_b, (fun v => match v with (b,op) => I_DEC b op end
                          %% i_instr5_t)}} :::
    {{4, INC_b, (fun v => match v with (b,op) => I_INC b op end
                          %% i_instr5_t)}} :::
    {{5, NEG_b, (fun v => match v with (b,op) => I_NEG b op end
                          %% i_instr5_t)}} :::
    {{6, NOT_b, (fun v => match v with (b,op) => I_NOT b op end
                          %% i_instr5_t)}} :::
    {{7, OR_b true, (fun v => match v with (b,(op1,op2)) => I_OR b op1 op2 end
                          %% i_instr5_t)}} :::
    {{8, SBB_b true, (fun v => match v with (b,(op1,op2)) => I_SBB b op1 op2 end
                          %% i_instr5_t)}} :::
    {{9, SUB_b true, (fun v => match v with (b,(op1,op2)) => I_SUB b op1 op2 end
                          %% i_instr5_t)}} :::
    {{10, XCHG_b, (fun v => match v with (b,(op1,op2)) => I_XCHG b op1 op2 end
                          %% i_instr5_t)}} :::
    {{11, XOR_b true, (fun v => match v with (b,(op1,op2)) => I_XOR b op1 op2 end
                          %% i_instr5_t)}} :::
    ast_env_nil.

  (** Instructions that can take prefixes in
      prefix_grammar_lock_no_op_override *)
  Definition prefix_lock_no_op_override_env : AST_Env i_instr5_t :=
    {{20, ADC_b false, (fun v => match v with (b,(op1,op2)) => I_ADC b op1 op2 end
                          %% i_instr5_t)}} :::
    {{21, ADD_b false, (fun v => match v with (b,(op1,op2)) => I_ADD b op1 op2 end
                          %% i_instr5_t)}} :::
    {{22, AND_b false, (fun v => match v with (b,(op1,op2)) => I_AND b op1 op2 end
                          %% i_instr5_t)}} :::
    {{23, BTC_b, (fun v => match v with (op1,op2) => I_BTC op1 op2 end
                          %% i_instr5_t)}} :::
    {{24, BTR_b, (fun v => match v with (op1,op2) => I_BTR op1 op2 end
                          %% i_instr5_t)}} :::
    {{25, BTS_b, (fun v => match v with (op1,op2) => I_BTS op1 op2 end
                          %% i_instr5_t)}} :::
    {{26, CMPXCHG_b, (fun v => match v with (b,(op1,op2)) => I_CMPXCHG b op1 op2 end
                          %% i_instr5_t)}} :::
    {{27, DEC_b, (fun v => match v with (b,op) => I_DEC b op end
                          %% i_instr5_t)}} :::
    {{28, INC_b, (fun v => match v with (b,op) => I_INC b op end
                          %% i_instr5_t)}} :::
    {{29, NEG_b, (fun v => match v with (b,op) => I_NEG b op end
                          %% i_instr5_t)}} :::
    {{30, NOT_b, (fun v => match v with (b,op) => I_NOT b op end
                          %% i_instr5_t)}} :::
    {{31, OR_b false, (fun v => match v with (b,(op1,op2)) => I_OR b op1 op2 end
                          %% i_instr5_t)}} :::
    {{32, SBB_b false, (fun v => match v with (b,(op1,op2)) => I_SBB b op1 op2 end
                          %% i_instr5_t)}} :::
    {{33, SUB_b false, (fun v => match v with (b,(op1,op2)) => I_SUB b op1 op2 end
                          %% i_instr5_t)}} :::
    {{34, XADD_b, (fun v => match v with (b,(op1,op2)) => I_XADD b op1 op2 end
                          %% i_instr5_t)}} :::
    {{35, XCHG_b, (fun v => match v with (b,(op1,op2)) => I_XCHG b op1 op2 end
                          %% i_instr5_t)}} :::
    {{36, XOR_b false, (fun v => match v with (b,(op1,op2)) => I_XOR b op1 op2 end
                          %% i_instr5_t)}} :::
    ast_env_nil.

  (** This set of instructions can take prefixes in 
      prefix_grammar_seg_with_op_override. *)
  Definition prefix_seg_with_op_override_env : AST_Env i_instr5_t :=
    {{40, CMP_b true, (fun v => match v with (b,(op1,op2)) => I_CMP b op1 op2 end
                          %% i_instr5_t)}} :::
    {{41, IMUL_b true, (fun v => match v with (b,(op1,(opopt,iopt))) =>
                                   I_IMUL b op1 opopt iopt end
                          %% i_instr5_t)}} :::
    {{42, MOV_b true, (fun v => match v with (b,(op1,op2)) => I_MOV b op1 op2 end
                          %% i_instr5_t)}} :::
    {{43, TEST_b true, (fun v => match v with (b,(op1,op2)) => I_TEST b op1 op2 end
                          %% i_instr5_t)}} :::
    ast_env_nil.


  (** This set of instructions can take prefixes in
      prefix_grammar_seg_with_op_override; there are more instructions in
      this category. *)
  Definition prefix_only_seg_override_env : AST_Env i_instr5_t :=
    {{50, CMP_b false, (fun v => match v with (b,(op1,op2)) => I_CMP b op1 op2 end
                          %% i_instr5_t)}} :::
    {{51, IMUL_b false, (fun v => match v with (b,(op1,(opopt,iopt))) =>
                                   I_IMUL b op1 opopt iopt end
                          %% i_instr5_t)}} :::
    {{52, MOV_b false, (fun v => match v with (b,(op1,op2)) => I_MOV b op1 op2 end
                          %% i_instr5_t)}} :::
    {{53, TEST_b false, (fun v => match v with (b,(op1,op2)) => I_TEST b op1 op2 end
                          %% i_instr5_t)}} :::
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
    let tt:=gen_ttype ige in exact(interp_ttype tt).
  Defined.

  Definition from_instr5 (u:prefix * i_instr5) : option [|i_instr5_grammar_type|].
    let ige := eval unfold i_instr5_grammar_env in i_instr5_grammar_env in
      gen_bgr_tree ige.
    let gt' := eval cbv delta [gt] in gt in
        gen_tm_cases gt' 54%nat.
    intro.
    refine (match snd u with
              | I_ADC a1 a2 a3 => 
                if (op_override (fst u)) then
                  inv_case_some case0 (fst u, (a1,(a2,a3)))
                else inv_case_some case20 (fst u, (a1,(a2,a3)))
              (* | _ => inv_case_some case23 (fst u, (Imm_op Word.zero, Imm_op Word.zero)) *)
              | I_ADD a1 a2 a3 =>
                if (op_override (fst u)) then
                  inv_case_some case1 (fst u, (a1,(a2,a3)))
                else inv_case_some case21 (fst u, (a1,(a2,a3)))
              | I_AND a1 a2 a3 =>
                if (op_override (fst u)) then
                  inv_case_some case2 (fst u, (a1,(a2,a3)))
                else inv_case_some case22 (fst u, (a1,(a2,a3)))
              | I_BTC a1 a2 =>
                inv_case_some case23 (fst u, (a1,a2))
              | I_BTR a1 a2 =>
                inv_case_some case24 (fst u, (a1,a2))
              | I_BTS a1 a2 =>
                inv_case_some case25 (fst u, (a1,a2))
              | I_CMP a1 a2 a3 =>
                if (op_override (fst u)) then
                  inv_case_some case40 (fst u, (a1,(a2,a3)))
                else inv_case_some case50 (fst u, (a1,(a2,a3)))
              | I_CMPXCHG a1 a2 a3 =>
                inv_case_some case26 (fst u, (a1,(a2,a3)))
              | I_DEC a1 a2 =>
                if (op_override (fst u)) then
                  inv_case_some case3 (fst u, (a1,a2))
                else inv_case_some case27 (fst u, (a1,a2))
              | I_IMUL a1 a2 a3 a4 =>
                if (op_override (fst u)) then
                  inv_case_some case41 (fst u, (a1,(a2,(a3,a4))))
                else inv_case_some case51 (fst u, (a1,(a2,(a3,a4))))
              | I_INC a1 a2 =>
                if (op_override (fst u)) then
                  inv_case_some case4 (fst u, (a1,a2))
                else inv_case_some case28 (fst u, (a1,a2))
              | I_MOV a1 a2 a3 =>
                if (op_override (fst u)) then
                  inv_case_some case42 (fst u, (a1,(a2,a3)))
                else inv_case_some case52 (fst u, (a1,(a2,a3)))
              | I_NEG a1 a2 =>
                if (op_override (fst u)) then
                  inv_case_some case5 (fst u, (a1,a2))
                else inv_case_some case29 (fst u, (a1,a2))
              | I_NOT a1 a2 =>
                if (op_override (fst u)) then
                  inv_case_some case6 (fst u, (a1,a2))
                else inv_case_some case30 (fst u, (a1,a2))
              | I_OR a1 a2 a3 =>
                if (op_override (fst u)) then
                  inv_case_some case7 (fst u, (a1,(a2,a3)))
                else inv_case_some case31 (fst u, (a1,(a2,a3)))
              | I_SBB a1 a2 a3 =>
                if (op_override (fst u)) then
                  inv_case_some case8 (fst u, (a1,(a2,a3)))
                else inv_case_some case32 (fst u, (a1,(a2,a3)))
              | I_SUB a1 a2 a3 =>
                if (op_override (fst u)) then
                  inv_case_some case9 (fst u, (a1,(a2,a3)))
                else inv_case_some case33 (fst u, (a1,(a2,a3)))
              | I_TEST a1 a2 a3 =>
                if (op_override (fst u)) then
                  inv_case_some case43 (fst u, (a1,(a2,a3)))
                else inv_case_some case53 (fst u, (a1,(a2,a3)))
              | I_XADD a1 a2 a3 =>
                inv_case_some case34 (fst u, (a1,(a2,a3)))
              | I_XCHG a1 a2 a3 =>
                if (op_override (fst u)) then
                  inv_case_some case10 (fst u, (a1,(a2,a3)))
                else inv_case_some case35 (fst u, (a1,(a2,a3)))
              | I_XOR a1 a2 a3 =>
                if (op_override (fst u)) then
                  inv_case_some case11 (fst u, (a1,(a2,a3)))
                else inv_case_some case36 (fst u, (a1,(a2,a3)))
            end).
  Defined.

  Definition from_instr5' : 
     prefix * i_instr5 -> option [|i_instr5_grammar_type|].
    let fi := eval cbv beta
               delta [from_instr5 inv_case_some
                      inv_case projT2 N.of_nat N.leb N.compare
                      Pos.of_succ_nat Pos.compare Pos.compare_cont Pos.succ]
               iota zeta
               in from_instr5 in
       exact(fi).
  Defined.

  Definition i_instr5_b : wf_bigrammar (pair_t prefix_t i_instr5_t).
    let ige := eval unfold i_instr5_grammar_env in i_instr5_grammar_env in
        gen_bgr_tree ige.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & from_instr5'
               & _). unfold from_instr5'; unfold_invertible_ast.
    - Time abstract (
      destruct_all;
      try (match goal with
           | [ |- exists v', ?c = Some v' /\ _] => 
             match c with
               | Some ?v =>
                 exists v; split; trivial
               | if op_override _ then Some ?v1 else Some ?v2 =>
                 ibr_sim;
                 match goal with
                   | [ H: in_bigrammar_rng
                            (` prefix_grammar_lock_with_op_override) ?pre |- _] =>
                     assert (H2: op_override pre = true) by
                         (apply lock_with_op_override_rng_inv; trivial);
                     rewrite H2;
                     exists v1; split; ibr_sim
                   | [ H: in_bigrammar_rng
                            (` prefix_grammar_lock_no_op_override) ?pre |- _] =>
                     assert (H2: op_override pre = false) by
                         (apply lock_no_op_override_rng_inv; trivial);
                     rewrite H2;
                     exists v2; split; ibr_sim
                   | [ H: in_bigrammar_rng
                            (` prefix_grammar_seg_with_op_override) ?pre |- _] =>
                     assert (H2: op_override pre = true) by
                         (apply seg_with_op_override_rng_inv; trivial);
                     rewrite H2;
                     exists v1; split; ibr_sim
                   | [ H: in_bigrammar_rng
                            (` prefix_grammar_only_seg_override) ?pre |- _] =>
                     assert (H2: op_override pre = false) by
                         (apply only_seg_override_rng_inv; trivial);
                     rewrite H2;
                     exists v2; split; ibr_sim
                 end
             end
          end)).
    - Time (abstract (destruct w as [p ins]; destruct ins; 
                          match goal with
                          | [H: ?c = Some _ |- _] => 
                            match c with
                            | None => discriminate H
                            | Some _ => inversion H; clear H; subst; trivial
                            | if op_override ?p then Some _ else Some _ => 
                              destruct (op_override p);
                                inversion H; clear H; subst; trivial
                            end
                          end)).
  Time Defined.

  (** This set of instructions can take prefixes in
      prefix_grammar_seg_op_override. *)
  Definition i_instr6_env : AST_Env i_instr6_t := 
    {{0, CDQ_b, (fun v => I_CDQ %% i_instr6_t)}} :::
    {{1, CMOVcc_b, (fun v => match v with (ct,(op1,op2)) => I_CMOVcc ct op1 op2
                          end %% i_instr6_t)}} :::
    {{2, CWDE_b, (fun v => I_CWDE %% i_instr6_t)}} :::
    {{3, DIV_b, (fun v => match v with (w,op1) => I_DIV w op1
                          end %% i_instr6_t)}} :::
    {{4, IDIV_b, (fun v => match v with (w,op1) => I_IDIV w op1
                          end %% i_instr6_t)}} :::
    {{5, MOVSX_b, (fun v => match v with (w,(op1,op2)) => I_MOVSX w op1 op2
                          end %% i_instr6_t)}} :::
    {{6, MOVZX_b, (fun v => match v with (w,(op1,op2)) => I_MOVZX w op1 op2
                          end %% i_instr6_t)}} :::
    {{7, MUL_b, (fun v => match v with (w,op1) => I_MUL w op1
                          end %% i_instr6_t)}} :::
    {{8, NOP_b, (fun op => I_NOP op %% i_instr6_t)}} :::
    {{9, ROL_b, (fun v => match v with (w,(op1,ri)) => I_ROL w op1 ri
                          end %% i_instr6_t)}} :::
    {{10, ROR_b, (fun v => match v with (w,(op1,ri)) => I_ROR w op1 ri
                          end %% i_instr6_t)}} :::
    {{11, SAR_b, (fun v => match v with (w,(op1,ri)) => I_SAR w op1 ri
                          end %% i_instr6_t)}} :::
    {{12, SHL_b, (fun v => match v with (w,(op1,ri)) => I_SHL w op1 ri
                          end %% i_instr6_t)}} :::
    {{13, SHLD_b, (fun v => match v with (op1,(r,ri)) => I_SHLD op1 r ri
                          end %% i_instr6_t)}} :::
    {{14, SHR_b, (fun v => match v with (w,(op1,ri)) => I_SHR w op1 ri
                          end %% i_instr6_t)}} :::
    {{15, SHRD_b, (fun v => match v with (op1,(r,ri)) => I_SHRD op1 r ri
                          end %% i_instr6_t)}} :::
    ast_env_nil.
  Hint Unfold i_instr6_env: env_unfold_db.

  Definition i_instr6_b : wf_bigrammar i_instr6_t.
    gen_ast_defs i_instr6_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u =>
                    match u with
                      | I_CDQ => inv_case_some case0 ()
                      | I_CMOVcc ct op1 op2 => inv_case_some case1 (ct,(op1,op2))
                      | I_CWDE => inv_case_some case2 ()
                      | I_DIV w op1 => inv_case_some case3 (w,op1)
                      | I_IDIV w op1 => inv_case_some case4 (w,op1)
                      | I_MOVSX w op1 op2 => inv_case_some case5 (w,(op1,op2))
                      | I_MOVZX w op1 op2 => inv_case_some case6 (w,(op1,op2))
                      | I_MUL w op1 => inv_case_some case7 (w,op1)
                      | I_NOP op => inv_case_some case8 op
                      | I_ROL w op1 ri => inv_case_some case9 (w,(op1,ri))
                      | I_ROR w op1 ri => inv_case_some case10 (w,(op1,ri))
                      | I_SAR w op1 ri => inv_case_some case11 (w,(op1,ri))
                      | I_SHL w op1 ri => inv_case_some case12 (w,(op1,ri))
                      | I_SHLD op1 r ri => inv_case_some case13 (op1,(r,ri))
                      | I_SHR w op1 ri => inv_case_some case14 (w,(op1,ri))
                      | I_SHRD op1 r ri => inv_case_some case15 (op1,(r,ri))
                    end)
               & _). ci_invertible_tac. 
  Defined.

  Definition f_instr1_env : AST_Env f_instr1_t := 
    {{0, F2XM1_b, (fun v => F_F2XM1 %% f_instr1_t)}} :::
    {{1, FABS_b, (fun v => F_FABS %% f_instr1_t)}} :::
    {{2, FADD_b, (fun v => match v with (z,op1) => F_FADD z op1
                          end %% f_instr1_t)}} :::
    {{3, FADDP_b, (fun op => F_FADDP op %% f_instr1_t)}} :::
    {{4, FBLD_b, (fun op => F_FBLD op %% f_instr1_t)}} :::
    {{5, FBSTP_b, (fun op => F_FBSTP op %% f_instr1_t)}} :::
    {{6, FCHS_b, (fun v => F_FCHS %% f_instr1_t)}} :::
    {{7, FCMOVcc_b, (fun v => match v with (ct,op1) => F_FCMOVcc ct op1
                          end %% f_instr1_t)}} :::
    {{8, FCOM_b, (fun op => F_FCOM op %% f_instr1_t)}} :::
    {{9, FCOMP_b, (fun op => F_FCOMP op %% f_instr1_t)}} :::
    {{10, FCOMPP_b, (fun v => F_FCOMPP %% f_instr1_t)}} :::
    {{11, FCOMIP_b, (fun op => F_FCOMIP op %% f_instr1_t)}} :::
    {{12, FCOS_b, (fun v => F_FCOS %% f_instr1_t)}} :::
    {{13, FDECSTP_b, (fun v => F_FDECSTP %% f_instr1_t)}} :::
    {{14, FDIV_b, (fun v => match v with (z,op1) => F_FDIV z op1
                          end %% f_instr1_t)}} :::
    {{15, FDIVP_b, (fun op => F_FDIVP op %% f_instr1_t)}} :::
    {{16, FDIVR_b, (fun v => match v with (z,op1) => F_FDIVR z op1
                          end %% f_instr1_t)}} :::
    {{17, FDIVRP_b, (fun op => F_FDIVRP op %% f_instr1_t)}} :::
    {{18, FFREE_b, (fun op => F_FFREE op %% f_instr1_t)}} :::
    {{19, FIADD_b, (fun op => F_FIADD op %% f_instr1_t)}} :::
    {{20, FICOM_b, (fun op => F_FICOM op %% f_instr1_t)}} :::
    {{21, FICOMP_b, (fun op => F_FICOMP op %% f_instr1_t)}} :::
    {{22, FIDIV_b, (fun op => F_FIDIV op %% f_instr1_t)}} :::
    {{23, FIDIVR_b, (fun op => F_FIDIVR op %% f_instr1_t)}} :::
    {{24, FILD_b, (fun op => F_FILD op %% f_instr1_t)}} :::
    {{25, FIMUL_b, (fun op => F_FIMUL op %% f_instr1_t)}} :::
    {{26, FINCSTP_b, (fun v => F_FINCSTP %% f_instr1_t)}} :::
    {{27, FIST_b, (fun op => F_FIST op %% f_instr1_t)}} :::
    {{28, FISTP_b, (fun op => F_FISTP op %% f_instr1_t)}} :::
    {{29, FISUB_b, (fun op => F_FISUB op %% f_instr1_t)}} :::
    {{30, FISUBR_b, (fun op => F_FISUBR op %% f_instr1_t)}} :::
    {{31, FLD_b, (fun op => F_FLD op %% f_instr1_t)}} :::
    {{32, FLD1_b, (fun v => F_FLD1 %% f_instr1_t)}} :::
    {{33, FLDCW_b, (fun op => F_FLDCW op %% f_instr1_t)}} :::
    {{34, FLDENV_b, (fun op => F_FLDENV op %% f_instr1_t)}} :::
    {{35, FLDL2E_b, (fun v => F_FLDL2E %% f_instr1_t)}} :::
    {{36, FLDL2T_b, (fun v => F_FLDL2T %% f_instr1_t)}} :::
    {{37, FLDLG2_b, (fun v => F_FLDLG2 %% f_instr1_t)}} :::
    {{38, FLDLN2_b, (fun v => F_FLDLN2 %% f_instr1_t)}} :::
    {{39, FLDPI_b, (fun v => F_FLDPI %% f_instr1_t)}} :::
    {{40, FLDZ_b, (fun v => F_FLDZ %% f_instr1_t)}} :::
    {{41, FMUL_b, (fun v => match v with (z,op1) => F_FMUL z op1
                          end %% f_instr1_t)}} :::
    {{42, FMULP_b, (fun op => F_FMULP op %% f_instr1_t)}} :::
    ast_env_nil.
  Hint Unfold f_instr1_env: env_unfold_db.

  Definition f_instr1_b : wf_bigrammar f_instr1_t.
    gen_ast_defs f_instr1_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u =>
                    match u with
                      | F_F2XM1 => inv_case_some case0 ()
                      | F_FABS => inv_case_some case1 ()
                      | F_FADD z op1 => inv_case_some case2 (z,op1)
                      | F_FADDP op => inv_case_some case3 op
                      | F_FBLD op => inv_case_some case4 op
                      | F_FBSTP op => inv_case_some case5 op
                      | F_FCHS => inv_case_some case6 ()
                      | F_FCMOVcc ct op => inv_case_some case7 (ct,op)
                      | F_FCOM op => inv_case_some case8 op
                      | F_FCOMP op => inv_case_some case9 op
                      | F_FCOMPP => inv_case_some case10 ()
                      | F_FCOMIP op => inv_case_some case11 op
                      | F_FCOS => inv_case_some case12 ()
                      | F_FDECSTP => inv_case_some case13 ()
                      | F_FDIV z op => inv_case_some case14 (z,op)
                      | F_FDIVP op => inv_case_some case15 op
                      | F_FDIVR z op => inv_case_some case16 (z,op)
                      | F_FDIVRP op => inv_case_some case17 op
                      | F_FFREE op => inv_case_some case18 op
                      | F_FIADD op => inv_case_some case19 op
                      | F_FICOM op => inv_case_some case20 op
                      | F_FICOMP op => inv_case_some case21 op
                      | F_FIDIV op => inv_case_some case22 op
                      | F_FIDIVR op => inv_case_some case23 op
                      | F_FILD op => inv_case_some case24 op
                      | F_FIMUL op => inv_case_some case25 op
                      | F_FINCSTP => inv_case_some case26 ()
                      | F_FIST op => inv_case_some case27 op
                      | F_FISTP op => inv_case_some case28 op
                      | F_FISUB op => inv_case_some case29 op
                      | F_FISUBR op => inv_case_some case30 op
                      | F_FLD op => inv_case_some case31 op
                      | F_FLD1 => inv_case_some case32 ()
                      | F_FLDCW op => inv_case_some case33 op
                      | F_FLDENV op => inv_case_some case34 op
                      | F_FLDL2E => inv_case_some case35 ()
                      | F_FLDL2T => inv_case_some case36 ()
                      | F_FLDLG2 => inv_case_some case37 ()
                      | F_FLDLN2 => inv_case_some case38 ()
                      | F_FLDPI => inv_case_some case39 ()
                      | F_FLDZ => inv_case_some case40 ()
                      | F_FMUL z op => inv_case_some case41 (z,op)
                      | F_FMULP op => inv_case_some case42 op
                    end)
               & _). ci_invertible_tac.
  Defined.

  Definition f_instr2_env : AST_Env f_instr2_t := 
    {{0, FNCLEX_b, (fun v => F_FNCLEX %% f_instr2_t)}} :::
    {{1, FNINIT_b, (fun v => F_FNINIT %% f_instr2_t)}} :::
    {{2, FNOP_b, (fun v => F_FNOP %% f_instr2_t)}} :::
    {{3, FNSAVE_b, (fun op => F_FNSAVE op %% f_instr2_t)}} :::
    {{4, FNSTCW_b, (fun op => F_FNSTCW op %% f_instr2_t)}} :::
    {{5, FNSTSW_b, (fun op => F_FNSTSW op %% f_instr2_t)}} :::
    {{6, FPATAN_b, (fun v => F_FPATAN %% f_instr2_t)}} :::
    {{7, FPREM_b, (fun v => F_FPREM %% f_instr2_t)}} :::
    {{8, FPREM1_b, (fun v => F_FPREM1 %% f_instr2_t)}} :::
    {{9, FPTAN_b, (fun v => F_FPTAN %% f_instr2_t)}} :::
    {{10, FRNDINT_b, (fun v => F_FRNDINT %% f_instr2_t)}} :::
    {{11, FRSTOR_b, (fun op => F_FRSTOR op %% f_instr2_t)}} :::
    {{12, FSCALE_b, (fun v => F_FSCALE %% f_instr2_t)}} :::
    {{13, FSIN_b, (fun v => F_FSIN %% f_instr2_t)}} :::
    {{14, FSINCOS_b, (fun v => F_FSINCOS %% f_instr2_t)}} :::
    {{15, FSQRT_b, (fun v => F_FSQRT %% f_instr2_t)}} :::
    {{16, FST_b, (fun op => F_FST op %% f_instr2_t)}} :::
    {{17, FSTENV_b, (fun op => F_FSTENV op %% f_instr2_t)}} :::
    {{18, FSTP_b, (fun op => F_FSTP op %% f_instr2_t)}} :::
    {{19, FSUB_b, (fun v => match v with (z,op) => F_FSUB z op 
                           end %% f_instr2_t)}} :::
    {{20, FSUBP_b, (fun op => F_FSUBP op %% f_instr2_t)}} :::
    {{21, FSUBR_b, (fun v => match v with (z,op) => F_FSUBR z op 
                           end %% f_instr2_t)}} :::
    {{22, FSUBRP_b, (fun op => F_FSUBRP op %% f_instr2_t)}} :::
    {{23, FTST_b, (fun v => F_FTST %% f_instr2_t)}} :::
    {{24, FUCOM_b, (fun op => F_FUCOM op %% f_instr2_t)}} :::
    {{25, FUCOMP_b, (fun op => F_FUCOMP op %% f_instr2_t)}} :::
    {{26, FUCOMPP_b, (fun v => F_FUCOMPP %% f_instr2_t)}} :::
    {{27, FUCOMI_b, (fun op => F_FUCOMI op %% f_instr2_t)}} :::
    {{28, FUCOMIP_b, (fun op => F_FUCOMIP op %% f_instr2_t)}} :::
    {{29, FXAM_b, (fun v => F_FXAM %% f_instr2_t)}} :::
    {{30, FXCH_b, (fun op => F_FXCH op %% f_instr2_t)}} :::
    {{31, FXTRACT_b, (fun v => F_FXTRACT %% f_instr2_t)}} :::
    {{32, FYL2X_b, (fun v => F_FYL2X %% f_instr2_t)}} :::
    {{33, FYL2XP1_b, (fun v => F_FYL2XP1 %% f_instr2_t)}} :::
    {{34, FWAIT_b, (fun v => F_FWAIT %% f_instr2_t)}} :::
    ast_env_nil.
  Hint Unfold f_instr2_env: env_unfold_db.

  Definition f_instr2_b : wf_bigrammar f_instr2_t.
    gen_ast_defs f_instr2_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u =>
                    match u with
                      | F_FNCLEX => inv_case_some case0 ()
                      | F_FNINIT => inv_case_some case1 ()
                      | F_FNOP => inv_case_some case2 ()
                      | F_FNSAVE op => inv_case_some case3 op
                      | F_FNSTCW op => inv_case_some case4 op
                      | F_FNSTSW op => inv_case_some case5 op
                      | F_FPATAN => inv_case_some case6 ()
                      | F_FPREM => inv_case_some case7 ()
                      | F_FPREM1 => inv_case_some case8 ()
                      | F_FPTAN => inv_case_some case9 ()
                      | F_FRNDINT => inv_case_some case10 ()
                      | F_FRSTOR op => inv_case_some case11 op
                      | F_FSCALE => inv_case_some case12 ()
                      | F_FSIN => inv_case_some case13 ()
                      | F_FSINCOS => inv_case_some case14 ()
                      | F_FSQRT => inv_case_some case15 ()
                      | F_FST op => inv_case_some case16 op
                      | F_FSTENV op => inv_case_some case17 op
                      | F_FSTP op => inv_case_some case18 op
                      | F_FSUB z op => inv_case_some case19 (z,op)
                      | F_FSUBP op => inv_case_some case20 op
                      | F_FSUBR z op => inv_case_some case21 (z,op)
                      | F_FSUBRP op => inv_case_some case22 op
                      | F_FTST => inv_case_some case23 ()
                      | F_FUCOM op => inv_case_some case24 op
                      | F_FUCOMP op => inv_case_some case25 op
                      | F_FUCOMPP => inv_case_some case26 ()
                      | F_FUCOMI op => inv_case_some case27 op
                      | F_FUCOMIP op => inv_case_some case28 op
                      | F_FXAM => inv_case_some case29 ()
                      | F_FXCH op => inv_case_some case30 op
                      | F_FXTRACT => inv_case_some case31 ()
                      | F_FYL2X => inv_case_some case32 ()
                      | F_FYL2XP1 => inv_case_some case33 ()
                      | F_FWAIT => inv_case_some case34 ()
                    end)
               & _). ci_invertible_tac.
  Defined.

  Definition m_instr_env : AST_Env m_instr_t := 
    {{0, EMMS_b, (fun v => M_EMMS %% m_instr_t)}} :::
    {{1, MOVD_b, (fun v => match v with (op1,op2) => M_MOVD op1 op2
                          end %% m_instr_t)}} :::
    {{2, MOVQ_b, (fun v => match v with (op1,op2) => M_MOVQ op1 op2
                          end %% m_instr_t)}} :::
    {{3, PACKSSDW_b, (fun v => match v with (op1,op2) => M_PACKSSDW op1 op2
                          end %% m_instr_t)}} :::
    {{4, PACKSSWB_b, (fun v => match v with (op1,op2) => M_PACKSSWB op1 op2
                          end %% m_instr_t)}} :::
    {{5, PACKUSWB_b, (fun v => match v with (op1,op2) => M_PACKUSWB op1 op2
                          end %% m_instr_t)}} :::
    {{6, PADD_b, (fun v => match v with (gg,(op1,op2)) => M_PADD gg op1 op2
                          end %% m_instr_t)}} :::
    {{7, PADDS_b, (fun v => match v with (gg,(op1,op2)) => M_PADDS gg op1 op2
                          end %% m_instr_t)}} :::
    {{8, PADDUS_b, (fun v => match v with (gg,(op1,op2)) => M_PADDUS gg op1 op2
                          end %% m_instr_t)}} :::
    {{9, PAND_b, (fun v => match v with (op1,op2) => M_PAND op1 op2
                          end %% m_instr_t)}} :::
    {{10, PANDN_b, (fun v => match v with (op1,op2) => M_PANDN op1 op2
                          end %% m_instr_t)}} :::
    {{11, PCMPEQ_b, (fun v => match v with (gg,(op1,op2)) => M_PCMPEQ gg op1 op2
                          end %% m_instr_t)}} :::
    {{12, PCMPGT_b, (fun v => match v with (gg,(op1,op2)) => M_PCMPGT gg op1 op2
                          end %% m_instr_t)}} :::
    {{13, PMADDWD_b, (fun v => match v with (op1,op2) => M_PMADDWD op1 op2
                          end %% m_instr_t)}} :::
    {{14, PMULHUW_b, (fun v => match v with (op1,op2) => M_PMULHUW op1 op2
                          end %% m_instr_t)}} :::
    {{15, PMULHW_b, (fun v => match v with (op1,op2) => M_PMULHW op1 op2
                          end %% m_instr_t)}} :::
    {{16, PMULLW_b, (fun v => match v with (op1,op2) => M_PMULLW op1 op2
                          end %% m_instr_t)}} :::
    {{17, POR_b, (fun v => match v with (op1,op2) => M_POR op1 op2
                          end %% m_instr_t)}} :::
    {{18, PSLL_b, (fun v => match v with (gg,(op1,op2)) => M_PSLL gg op1 op2
                          end %% m_instr_t)}} :::
    {{19, PSRA_b, (fun v => match v with (gg,(op1,op2)) => M_PSRA gg op1 op2
                          end %% m_instr_t)}} :::
    {{20, PSRL_b, (fun v => match v with (gg,(op1,op2)) => M_PSRL gg op1 op2
                          end %% m_instr_t)}} :::
    {{21, PSUB_b, (fun v => match v with (gg,(op1,op2)) => M_PSUB gg op1 op2
                          end %% m_instr_t)}} :::
    {{22, PSUBS_b, (fun v => match v with (gg,(op1,op2)) => M_PSUBS gg op1 op2
                          end %% m_instr_t)}} :::
    {{23, PSUBUS_b, (fun v => match v with (gg,(op1,op2)) => M_PSUBUS gg op1 op2
                          end %% m_instr_t)}} :::
    {{24, PUNPCKH_b, (fun v => match v with (gg,(op1,op2)) => M_PUNPCKH gg op1 op2
                          end %% m_instr_t)}} :::
    {{25, PUNPCKL_b, (fun v => match v with (gg,(op1,op2)) => M_PUNPCKL gg op1 op2
                          end %% m_instr_t)}} :::
    {{26, PXOR_b, (fun v => match v with (op1,op2) => M_PXOR op1 op2
                          end %% m_instr_t)}} :::
    ast_env_nil.
  Hint Unfold m_instr_env: env_unfold_db.

  Definition m_instr_b : wf_bigrammar m_instr_t.
    gen_ast_defs m_instr_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u =>
                    match u with
                      | M_EMMS => inv_case_some case0 ()
                      | M_MOVD op1 op2 => inv_case_some case1 (op1,op2)
                      | M_MOVQ op1 op2 => inv_case_some case2 (op1,op2)
                      | M_PACKSSDW op1 op2 => inv_case_some case3 (op1,op2)
                      | M_PACKSSWB op1 op2 => inv_case_some case4 (op1,op2)
                      | M_PACKUSWB op1 op2 => inv_case_some case5 (op1,op2)
                      | M_PADD gg op1 op2 => inv_case_some case6 (gg,(op1,op2))
                      | M_PADDS gg op1 op2 => inv_case_some case7 (gg,(op1,op2))
                      | M_PADDUS gg op1 op2 => inv_case_some case8 (gg,(op1,op2))
                      | M_PAND op1 op2 => inv_case_some case9 (op1,op2)
                      | M_PANDN op1 op2 => inv_case_some case10 (op1,op2)
                      | M_PCMPEQ gg op1 op2 => inv_case_some case11 (gg,(op1,op2))
                      | M_PCMPGT gg op1 op2 => inv_case_some case12 (gg,(op1,op2))
                      | M_PMADDWD op1 op2 => inv_case_some case13 (op1,op2)
                      | M_PMULHUW op1 op2 => inv_case_some case14 (op1,op2)
                      | M_PMULHW op1 op2 => inv_case_some case15 (op1,op2)
                      | M_PMULLW op1 op2 => inv_case_some case16 (op1,op2)
                      | M_POR op1 op2 => inv_case_some case17 (op1,op2)
                      | M_PSLL gg op1 op2 => inv_case_some case18 (gg,(op1,op2))
                      | M_PSRA gg op1 op2 => inv_case_some case19 (gg,(op1,op2))
                      | M_PSRL gg op1 op2 => inv_case_some case20 (gg,(op1,op2))
                      | M_PSUB gg op1 op2 => inv_case_some case21 (gg,(op1,op2))
                      | M_PSUBS gg op1 op2 => inv_case_some case22 (gg,(op1,op2))
                      | M_PSUBUS gg op1 op2 => inv_case_some case23 (gg,(op1,op2))
                      | M_PUNPCKH gg op1 op2 => inv_case_some case24 (gg,(op1,op2))
                      | M_PUNPCKL gg op1 op2 => inv_case_some case25 (gg,(op1,op2))
                      | M_PXOR op1 op2 => inv_case_some case26 (op1,op2)
                    end)
               & _). ci_invertible_tac.
  Defined.

  Definition s_instr1_env : AST_Env s_instr1_t := 
    {{0, ADDPS_b, (fun v => match v with (op1,op2) => S_ADDPS op1 op2
                          end %% s_instr1_t)}} :::
    {{1, ADDSS_b, (fun v => match v with (op1,op2) => S_ADDSS op1 op2
                          end %% s_instr1_t)}} :::
    {{2, ANDNPS_b, (fun v => match v with (op1,op2) => S_ANDNPS op1 op2
                          end %% s_instr1_t)}} :::
    {{3, ANDPS_b, (fun v => match v with (op1,op2) => S_ANDPS op1 op2
                          end %% s_instr1_t)}} :::
    {{4, CMPPS_b, (fun v => match v with (op1,(op2,imm)) => S_CMPPS op1 op2 imm
                          end %% s_instr1_t)}} :::
    {{5, CMPSS_b, (fun v => match v with (op1,(op2,imm)) => S_CMPSS op1 op2 imm
                          end %% s_instr1_t)}} :::
    {{6, COMISS_b, (fun v => match v with (op1,op2) => S_COMISS op1 op2
                          end %% s_instr1_t)}} :::
    {{7, CVTPI2PS_b, (fun v => match v with (op1,op2) => S_CVTPI2PS op1 op2
                          end %% s_instr1_t)}} :::
    {{8, CVTPS2PI_b, (fun v => match v with (op1,op2) => S_CVTPS2PI op1 op2
                          end %% s_instr1_t)}} :::
    {{9, CVTSI2SS_b, (fun v => match v with (op1,op2) => S_CVTSI2SS op1 op2
                          end %% s_instr1_t)}} :::
    {{10, CVTSS2SI_b, (fun v => match v with (op1,op2) => S_CVTSS2SI op1 op2
                          end %% s_instr1_t)}} :::
    {{11, CVTTPS2PI_b, (fun v => match v with (op1,op2) => S_CVTTPS2PI op1 op2
                          end %% s_instr1_t)}} :::
    {{12, CVTTSS2SI_b, (fun v => match v with (op1,op2) => S_CVTTSS2SI op1 op2
                          end %% s_instr1_t)}} :::
    {{13, DIVPS_b, (fun v => match v with (op1,op2) => S_DIVPS op1 op2
                          end %% s_instr1_t)}} :::
    {{14, DIVSS_b, (fun v => match v with (op1,op2) => S_DIVSS op1 op2
                          end %% s_instr1_t)}} :::
    {{15, LDMXCSR_b, (fun op => S_LDMXCSR op %% s_instr1_t)}} :::
    {{16, MAXPS_b, (fun v => match v with (op1,op2) => S_MAXPS op1 op2
                          end %% s_instr1_t)}} :::
    {{17, MAXSS_b, (fun v => match v with (op1,op2) => S_MAXSS op1 op2
                          end %% s_instr1_t)}} :::
    {{18, MINPS_b, (fun v => match v with (op1,op2) => S_MINPS op1 op2
                          end %% s_instr1_t)}} :::
    {{19, MINSS_b, (fun v => match v with (op1,op2) => S_MINSS op1 op2
                          end %% s_instr1_t)}} :::
    {{20, MOVAPS_b, (fun v => match v with (op1,op2) => S_MOVAPS op1 op2
                          end %% s_instr1_t)}} :::
    {{21, MOVHLPS_b, (fun v => match v with (op1,op2) => S_MOVHLPS op1 op2
                          end %% s_instr1_t)}} :::
    {{22, MOVHPS_b, (fun v => match v with (op1,op2) => S_MOVHPS op1 op2
                          end %% s_instr1_t)}} :::
    {{23, MOVLHPS_b, (fun v => match v with (op1,op2) => S_MOVLHPS op1 op2
                          end %% s_instr1_t)}} :::
    {{24, MOVLPS_b, (fun v => match v with (op1,op2) => S_MOVLPS op1 op2
                          end %% s_instr1_t)}} :::
    {{25, MOVMSKPS_b, (fun v => match v with (op1,op2) => S_MOVMSKPS op1 op2
                          end %% s_instr1_t)}} :::
    {{26, MOVSS_b, (fun v => match v with (op1,op2) => S_MOVSS op1 op2
                          end %% s_instr1_t)}} :::
    {{27, MOVUPS_b, (fun v => match v with (op1,op2) => S_MOVUPS op1 op2
                          end %% s_instr1_t)}} :::
    {{28, MULPS_b, (fun v => match v with (op1,op2) => S_MULPS op1 op2
                          end %% s_instr1_t)}} :::
    {{29, MULSS_b, (fun v => match v with (op1,op2) => S_MULSS op1 op2
                          end %% s_instr1_t)}} :::
    {{30, ORPS_b, (fun v => match v with (op1,op2) => S_ORPS op1 op2
                          end %% s_instr1_t)}} :::
    {{31, RCPPS_b, (fun v => match v with (op1,op2) => S_RCPPS op1 op2
                          end %% s_instr1_t)}} :::
    {{32, RCPSS_b, (fun v => match v with (op1,op2) => S_RCPSS op1 op2
                          end %% s_instr1_t)}} :::
    {{33, RSQRTPS_b, (fun v => match v with (op1,op2) => S_RSQRTPS op1 op2
                          end %% s_instr1_t)}} :::
    {{34, RSQRTSS_b, (fun v => match v with (op1,op2) => S_RSQRTSS op1 op2
                          end %% s_instr1_t)}} :::
    ast_env_nil.
  Hint Unfold s_instr1_env: env_unfold_db.

  Definition s_instr1_b : wf_bigrammar s_instr1_t.
    gen_ast_defs s_instr1_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u =>
                    match u with
                      | S_ADDPS op1 op2 => inv_case_some case0 (op1,op2)
                      | S_ADDSS op1 op2 => inv_case_some case1 (op1,op2)
                      | S_ANDNPS op1 op2 => inv_case_some case2 (op1,op2)
                      | S_ANDPS op1 op2 => inv_case_some case3 (op1,op2)
                      | S_CMPPS op1 op2 imm => inv_case_some case4 (op1,(op2,imm))
                      | S_CMPSS op1 op2 imm => inv_case_some case5 (op1,(op2,imm))
                      | S_COMISS op1 op2 => inv_case_some case6 (op1,op2)
                      | S_CVTPI2PS op1 op2 => inv_case_some case7 (op1,op2)
                      | S_CVTPS2PI op1 op2 => inv_case_some case8 (op1,op2)
                      | S_CVTSI2SS op1 op2 => inv_case_some case9 (op1,op2)
                      | S_CVTSS2SI op1 op2 => inv_case_some case10 (op1,op2)
                      | S_CVTTPS2PI op1 op2 => inv_case_some case11 (op1,op2)
                      | S_CVTTSS2SI op1 op2 => inv_case_some case12 (op1,op2)
                      | S_DIVPS op1 op2 => inv_case_some case13 (op1,op2)
                      | S_DIVSS op1 op2 => inv_case_some case14 (op1,op2)
                      | S_LDMXCSR op => inv_case_some case15 op
                      | S_MAXPS op1 op2 => inv_case_some case16 (op1,op2)
                      | S_MAXSS op1 op2 => inv_case_some case17 (op1,op2)
                      | S_MINPS op1 op2 => inv_case_some case18 (op1,op2)
                      | S_MINSS op1 op2 => inv_case_some case19 (op1,op2)
                      | S_MOVAPS op1 op2 => inv_case_some case20 (op1,op2)
                      | S_MOVHLPS op1 op2 => inv_case_some case21 (op1,op2)
                      | S_MOVHPS op1 op2 => inv_case_some case22 (op1,op2)
                      | S_MOVLHPS op1 op2 => inv_case_some case23 (op1,op2)
                      | S_MOVLPS op1 op2 => inv_case_some case24 (op1,op2)
                      | S_MOVMSKPS op1 op2 => inv_case_some case25 (op1,op2)
                      | S_MOVSS op1 op2 => inv_case_some case26 (op1,op2)
                      | S_MOVUPS op1 op2 => inv_case_some case27 (op1,op2)
                      | S_MULPS op1 op2 => inv_case_some case28 (op1,op2)
                      | S_MULSS op1 op2 => inv_case_some case29 (op1,op2)
                      | S_ORPS op1 op2 => inv_case_some case30 (op1,op2)
                      | S_RCPPS op1 op2 => inv_case_some case31 (op1,op2)
                      | S_RCPSS op1 op2 => inv_case_some case32 (op1,op2)
                      | S_RSQRTPS op1 op2 => inv_case_some case33 (op1,op2)
                      | S_RSQRTSS op1 op2 => inv_case_some case34 (op1,op2)
                    end)
               & _). ci_invertible_tac.
  Defined.

  Definition s_instr2_env : AST_Env s_instr2_t := 
    {{0, SHUFPS_b, (fun v => match v with (op1,(op2,imm)) => S_SHUFPS op1 op2 imm
                          end %% s_instr2_t)}} :::
    {{1, SQRTPS_b, (fun v => match v with (op1,op2) => S_SQRTPS op1 op2
                          end %% s_instr2_t)}} :::
    {{2, SQRTSS_b, (fun v => match v with (op1,op2) => S_SQRTSS op1 op2
                          end %% s_instr2_t)}} :::
    {{3, STMXCSR_b, (fun op => S_STMXCSR op %% s_instr2_t)}} :::
    {{4, SUBPS_b, (fun v => match v with (op1,op2) => S_SUBPS op1 op2
                          end %% s_instr2_t)}} :::
    {{5, SUBSS_b, (fun v => match v with (op1,op2) => S_SUBSS op1 op2
                          end %% s_instr2_t)}} :::
    {{6, UCOMISS_b, (fun v => match v with (op1,op2) => S_UCOMISS op1 op2
                          end %% s_instr2_t)}} :::
    {{7, UNPCKHPS_b, (fun v => match v with (op1,op2) => S_UNPCKHPS op1 op2
                          end %% s_instr2_t)}} :::
    {{8, UNPCKLPS_b, (fun v => match v with (op1,op2) => S_UNPCKLPS op1 op2
                          end %% s_instr2_t)}} :::
    {{9, XORPS_b, (fun v => match v with (op1,op2) => S_XORPS op1 op2
                          end %% s_instr2_t)}} :::
    {{10, PAVGB_b, (fun v => match v with (op1,op2) => S_PAVGB op1 op2
                          end %% s_instr2_t)}} :::
    {{11, PEXTRW_b, (fun v => match v with (op1,(op2,imm)) => S_PEXTRW op1 op2 imm
                          end %% s_instr2_t)}} :::
    {{12, PINSRW_b, (fun v => match v with (op1,(op2,imm)) => S_PINSRW op1 op2 imm
                          end %% s_instr2_t)}} :::
    {{13, PMAXSW_b, (fun v => match v with (op1,op2) => S_PMAXSW op1 op2
                          end %% s_instr2_t)}} :::
    {{14, PMAXUB_b, (fun v => match v with (op1,op2) => S_PMAXUB op1 op2
                          end %% s_instr2_t)}} :::
    {{15, PMINSW_b, (fun v => match v with (op1,op2) => S_PMINSW op1 op2
                          end %% s_instr2_t)}} :::
    {{16, PMINUB_b, (fun v => match v with (op1,op2) => S_PMINUB op1 op2
                          end %% s_instr2_t)}} :::
    {{17, PMOVMSKB_b, (fun v => match v with (op1,op2) => S_PMOVMSKB op1 op2
                          end %% s_instr2_t)}} :::
    {{18, PSADBW_b, (fun v => match v with (op1,op2) => S_PSADBW op1 op2
                          end %% s_instr2_t)}} :::
    {{19, PSHUFW_b, (fun v => match v with (op1,(op2,imm)) => S_PSHUFW op1 op2 imm
                          end %% s_instr2_t)}} :::
    {{20, MASKMOVQ_b, (fun v => match v with (op1,op2) => S_MASKMOVQ op1 op2
                          end %% s_instr2_t)}} :::
    {{21, MOVNTPS_b, (fun v => match v with (op1,op2) => S_MOVNTPS op1 op2
                          end %% s_instr2_t)}} :::
    {{22, MOVNTQ_b, (fun v => match v with (op1,op2) => S_MOVNTQ op1 op2
                          end %% s_instr2_t)}} :::
    {{23, PREFETCHT0_b, (fun op => S_PREFETCHT0 op %% s_instr2_t)}} :::
    {{24, PREFETCHT1_b, (fun op => S_PREFETCHT1 op %% s_instr2_t)}} :::
    {{25, PREFETCHT2_b, (fun op => S_PREFETCHT2 op %% s_instr2_t)}} :::
    {{26, PREFETCHNTA_b, (fun op => S_PREFETCHNTA op %% s_instr2_t)}} :::
    {{27, SFENCE_b, (fun v => S_SFENCE %% s_instr2_t)}} :::
    ast_env_nil.
  Hint Unfold s_instr2_env: env_unfold_db.

  Definition s_instr2_b : wf_bigrammar s_instr2_t.
    gen_ast_defs s_instr2_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u =>
                    match u with
                      | S_SHUFPS op1 op2 imm => inv_case_some case0 (op1,(op2,imm))
                      | S_SQRTPS op1 op2 => inv_case_some case1 (op1,op2)
                      | S_SQRTSS op1 op2 => inv_case_some case2 (op1,op2)
                      | S_STMXCSR op => inv_case_some case3 op
                      | S_SUBPS op1 op2 => inv_case_some case4 (op1,op2)
                      | S_SUBSS op1 op2 => inv_case_some case5 (op1,op2)
                      | S_UCOMISS op1 op2 => inv_case_some case6 (op1,op2)
                      | S_UNPCKHPS op1 op2 => inv_case_some case7 (op1,op2)
                      | S_UNPCKLPS op1 op2 => inv_case_some case8 (op1,op2)
                      | S_XORPS op1 op2 => inv_case_some case9 (op1,op2)
                      | S_PAVGB op1 op2 => inv_case_some case10 (op1,op2)
                      | S_PEXTRW op1 op2 imm => inv_case_some case11 (op1,(op2,imm))
                      | S_PINSRW op1 op2 imm => inv_case_some case12 (op1,(op2,imm))
                      | S_PMAXSW op1 op2 => inv_case_some case13 (op1,op2)
                      | S_PMAXUB op1 op2 => inv_case_some case14 (op1,op2)
                      | S_PMINSW op1 op2 => inv_case_some case15 (op1,op2)
                      | S_PMINUB op1 op2 => inv_case_some case16 (op1,op2)
                      | S_PMOVMSKB op1 op2 => inv_case_some case17 (op1,op2)
                      | S_PSADBW op1 op2 => inv_case_some case18 (op1,op2)
                      | S_PSHUFW op1 op2 imm => inv_case_some case19 (op1,(op2,imm))
                      | S_MASKMOVQ op1 op2 => inv_case_some case20 (op1,op2)
                      | S_MOVNTPS op1 op2 => inv_case_some case21 (op1,op2)
                      | S_MOVNTQ op1 op2 => inv_case_some case22 (op1,op2)
                      | S_PREFETCHT0 op => inv_case_some case23 op
                      | S_PREFETCHT1 op => inv_case_some case24 op
                      | S_PREFETCHT2 op => inv_case_some case25 op
                      | S_PREFETCHNTA op => inv_case_some case26 op
                      | S_SFENCE => inv_case_some case27 tt
                    end)
               & _). ci_invertible_tac.
  Defined.

  Definition instr_bigrammar_env : AST_Env (pair_t prefix_t instruction_t) :=
    {{0, prefix_grammar_only_seg_override $ i_instr1_b,
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
               in (pre,i) %% pair_t prefix_t instruction_t)}} :::
    {{1, prefix_grammar_only_seg_override $ i_instr2_b,
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
               in (pre,i) %% pair_t prefix_t instruction_t)}} :::
    {{2, prefix_grammar_only_seg_override $ i_instr3_b,
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
               in (pre,i) %% pair_t prefix_t instruction_t)}} :::
    {{3, i_instr4_b,
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
               in (pre,i) %% pair_t prefix_t instruction_t)}} :::
    {{4, i_instr5_b,
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
               in (pre,i) %% pair_t prefix_t instruction_t)}} :::
    {{5, prefix_grammar_seg_op_override $ i_instr6_b,
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
               in (pre,i) %% pair_t prefix_t instruction_t)}} :::
    {{6, prefix_grammar_only_seg_override $ f_instr1_b,
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
               in (pre,i) %% pair_t prefix_t instruction_t)}} :::
    {{7, prefix_grammar_only_seg_override $ f_instr2_b,
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
               in (pre,i) %% pair_t prefix_t instruction_t)}} :::
    {{8, prefix_grammar_only_seg_override $ m_instr_b,
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
               in (pre,i) %% pair_t prefix_t instruction_t)}} :::
    {{9, prefix_grammar_only_seg_override $ s_instr1_b,
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
               in (pre,i) %% pair_t prefix_t instruction_t)}} :::
    {{10, prefix_grammar_only_seg_override $ s_instr2_b,
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
               in (pre,i) %% pair_t prefix_t instruction_t)}} :::
    ast_env_nil.
  Hint Unfold instr_bigrammar_env: env_unfold_db.

  Definition instr_bigrammar : wf_bigrammar (pair_t prefix_t instruction_t).
    gen_ast_defs instr_bigrammar_env.
    refine ((comb_bigrammar gt) @ (comb_map gt)
               & (fun u:[|pair_t prefix_t instruction_t|] =>
                   let (pre,i):=u in
                   match i with
                     | AAA => inv_case_some case0 (pre,I_AAA)
                     | AAD => inv_case_some case0 (pre,I_AAD)
                     | AAM => inv_case_some case0 (pre,I_AAM)
                     | AAS => inv_case_some case0 (pre,I_AAS)
                     | CLC => inv_case_some case0 (pre,I_CLC)
                     | CLD => inv_case_some case0 (pre,I_CLD)
                     | CLI => inv_case_some case0 (pre,I_CLI)
                     | CLTS => inv_case_some case0 (pre,I_CLTS)
                     | CMC => inv_case_some case0 (pre,I_CMC)
                     | CPUID => inv_case_some case0 (pre,I_CPUID)
                     | DAA => inv_case_some case0 (pre,I_DAA)
                     | DAS => inv_case_some case0 (pre,I_DAS)
                     | HLT => inv_case_some case0 (pre,I_HLT)
                     | INT => inv_case_some case0 (pre,I_INT)
                     | INTO => inv_case_some case0 (pre,I_INTO)
                     | INVD => inv_case_some case0 (pre,I_INVD)
                     | IRET => inv_case_some case0 (pre,I_IRET)
                     | LAHF => inv_case_some case0 (pre,I_LAHF)
                     | LEAVE => inv_case_some case0 (pre,I_LEAVE)
                     | POPA => inv_case_some case0 (pre,I_POPA)
                     | POPF => inv_case_some case0 (pre,I_POPF)
                     | PUSHA => inv_case_some case0 (pre,I_PUSHA)
                     | PUSHF => inv_case_some case0 (pre,I_PUSHF)
                     | RDMSR => inv_case_some case0 (pre,I_RDMSR)
                     | RDPMC => inv_case_some case0 (pre,I_RDPMC)
                     | RDTSC => inv_case_some case0 (pre,I_RDTSC)
                     | RDTSCP => inv_case_some case0 (pre,I_RDTSCP)
                     | RSM => inv_case_some case0 (pre,I_RSM)
                     | SAHF => inv_case_some case0 (pre,I_SAHF)
                     | STC => inv_case_some case0 (pre,I_STC)
                     | STD => inv_case_some case0 (pre,I_STD)
                     | STI => inv_case_some case0 (pre,I_STI)
                     | UD2 => inv_case_some case0 (pre,I_UD2)
                     | WBINVD => inv_case_some case0 (pre,I_WBINVD)
                     | WRMSR => inv_case_some case0 (pre,I_WRMSR)
                     | XLAT => inv_case_some case0 (pre,I_XLAT)

                     | ARPL op1 op2 => inv_case_some case1 (pre,I_ARPL op1 op2)
                     | BOUND op1 op2 => inv_case_some case1 (pre,I_BOUND op1 op2)
                     | BSF op1 op2 => inv_case_some case1 (pre,I_BSF op1 op2)
                     | BSR op1 op2 => inv_case_some case1 (pre,I_BSR op1 op2)
                     | BSWAP r => inv_case_some case1 (pre,I_BSWAP r)
                     | BT op1 op2 => inv_case_some case1 (pre,I_BT op1 op2)
                     | CALL near abs op sel => inv_case_some case1 (pre,I_CALL near abs op sel)
                     | IN w p => inv_case_some case1 (pre,I_IN w p)
                     | INTn it => inv_case_some case1 (pre,I_INTn it)
                     | INVLPG op => inv_case_some case1 (pre,I_INVLPG op)
                     | Jcc ct disp => inv_case_some case1 (pre,I_Jcc ct disp)
                     | JCXZ b => inv_case_some case1 (pre,I_JCXZ b)
                     | JMP near abs op sel => inv_case_some case1 (pre,I_JMP near abs op sel)
                     | LAR op1 op2 => inv_case_some case1 (pre,I_LAR op1 op2)
                     | LDS op1 op2 => inv_case_some case1 (pre,I_LDS op1 op2)
                     | LEA op1 op2 => inv_case_some case1 (pre,I_LEA op1 op2)
                     | LES op1 op2 => inv_case_some case1 (pre,I_LES op1 op2)
                     | LFS op1 op2 => inv_case_some case1 (pre,I_LFS op1 op2)
                     | LGDT op => inv_case_some case1 (pre,I_LGDT op)
                     | LGS op1 op2 => inv_case_some case1 (pre,I_LGS op1 op2)
                     | LIDT op => inv_case_some case1 (pre,I_LIDT op)
                     | LLDT op => inv_case_some case1 (pre,I_LLDT op)
                     | LMSW op => inv_case_some case1 (pre,I_LMSW op)
                     | LOOP disp => inv_case_some case1 (pre,I_LOOP disp)
                     | LOOPZ disp => inv_case_some case1 (pre,I_LOOPZ disp)
                     | LOOPNZ disp => inv_case_some case1 (pre,I_LOOPNZ disp)
                     | LSL op1 op2 => inv_case_some case1 (pre,I_LSL op1 op2)
                     | LSS op1 op2 => inv_case_some case1 (pre,I_LSS op1 op2)
                     | LTR op => inv_case_some case1 (pre,I_LTR op)

                     | MOVCR d cr r => inv_case_some case2 (pre,I_MOVCR d cr r)
                     | MOVDR d cr r => inv_case_some case2 (pre,I_MOVDR d cr r)
                     | MOVSR d cr r => inv_case_some case2 (pre,I_MOVSR d cr r)
                     | MOVBE op1 op2 => inv_case_some case2 (pre,I_MOVBE op1 op2)
                     | OUT w p => inv_case_some case2 (pre,I_OUT w p)
                     | POP op => inv_case_some case2 (pre,I_POP op)
                     | POPSR sr => inv_case_some case2 (pre,I_POPSR sr)
                     | PUSH w op => inv_case_some case2 (pre,I_PUSH w op)
                     | PUSHSR sr => inv_case_some case2 (pre,I_PUSHSR sr)
                     | RCL w op1 ri => inv_case_some case2 (pre,I_RCL w op1 ri)
                     | RCR w op1 ri => inv_case_some case2 (pre,I_RCR w op1 ri)
                     | SETcc ct op => inv_case_some case2 (pre,I_SETcc ct op)
                     | SGDT op => inv_case_some case2 (pre,I_SGDT op)
                     | SIDT op => inv_case_some case2 (pre,I_SIDT op)
                     | SLDT op => inv_case_some case2 (pre,I_SLDT op)
                     | SMSW op => inv_case_some case2 (pre,I_SMSW op)
                     | STR op => inv_case_some case2 (pre,I_STR op)
                     | VERR op => inv_case_some case2 (pre,I_VERR op)
                     | VERW op => inv_case_some case2 (pre,I_VERW op)
                                          
                     | INS b => inv_case_some case3 (pre,I_INS b)
                     | OUTS b => inv_case_some case3 (pre,I_OUTS b)
                     | MOVS b => inv_case_some case3 (pre,I_MOVS b)
                     | LODS b => inv_case_some case3 (pre,I_LODS b)
                     | STOS b => inv_case_some case3 (pre,I_STOS b)
                     | RET ss disp => inv_case_some case3 (pre,I_RET ss disp)
                     | CMPS b => inv_case_some case3 (pre,I_CMPS b)
                     | SCAS b => inv_case_some case3 (pre,I_SCAS b)

                     | ADC w op1 op2 => inv_case_some case4 (pre, I_ADC w op1 op2)
                     | ADD w op1 op2 => inv_case_some case4 (pre, I_ADD w op1 op2)
                     | AND w op1 op2 => inv_case_some case4 (pre, I_AND w op1 op2)
                     | BTC op1 op2 => inv_case_some case4 (pre, I_BTC op1 op2)
                     | BTR op1 op2 => inv_case_some case4 (pre, I_BTR op1 op2)
                     | BTS op1 op2 => inv_case_some case4 (pre, I_BTS op1 op2)
                     | CMP w op1 op2 => inv_case_some case4 (pre, I_CMP w op1 op2)
                     | CMPXCHG w op1 op2 => inv_case_some case4 (pre, I_CMPXCHG w op1 op2)
                     | DEC w op1 => inv_case_some case4 (pre, I_DEC w op1)
                     | IMUL w op1 opopt iopt  => inv_case_some case4 (pre, I_IMUL w op1 opopt iopt)
                     | INC w op1 => inv_case_some case4 (pre, I_INC w op1)
                     | MOV w op1 op2 => inv_case_some case4 (pre, I_MOV w op1 op2)
                     | NEG w op => inv_case_some case4 (pre, I_NEG w op)
                     | NOT w op => inv_case_some case4 (pre, I_NOT w op)
                     | OR w op1 op2 => inv_case_some case4 (pre, I_OR w op1 op2)
                     | SBB w op1 op2 => inv_case_some case4 (pre, I_SBB w op1 op2)
                     | SUB w op1 op2 => inv_case_some case4 (pre, I_SUB w op1 op2)
                     | TEST w op1 op2 => inv_case_some case4 (pre, I_TEST w op1 op2)
                     | XADD w op1 op2 => inv_case_some case4 (pre, I_XADD w op1 op2)
                     | XCHG w op1 op2 => inv_case_some case4 (pre, I_XCHG w op1 op2)
                     | XOR w op1 op2 => inv_case_some case4 (pre, I_XOR w op1 op2)

                     | CDQ => inv_case_some case5 (pre, I_CDQ)
                     | CMOVcc ct op1 op2 => inv_case_some case5 (pre, I_CMOVcc ct op1 op2)
                     | CWDE => inv_case_some case5 (pre, I_CWDE)
                     | DIV w op1 => inv_case_some case5 (pre, I_DIV w op1)
                     | IDIV w op1 => inv_case_some case5 (pre, I_IDIV w op1)
                     | MOVSX w op1 op2 => inv_case_some case5 (pre, I_MOVSX w op1 op2)
                     | MOVZX w op1 op2 => inv_case_some case5 (pre, I_MOVZX w op1 op2)
                     | MUL w op1 => inv_case_some case5 (pre, I_MUL w op1)
                     | NOP op => inv_case_some case5 (pre, I_NOP op)
                     | ROL w op1 ri => inv_case_some case5 (pre, I_ROL w op1 ri)
                     | ROR w op1 ri => inv_case_some case5 (pre, I_ROR w op1 ri)
                     | SAR w op1 ri => inv_case_some case5 (pre, I_SAR w op1 ri)
                     | SHL w op1 ri => inv_case_some case5 (pre, I_SHL w op1 ri)
                     | SHLD op1 r ri => inv_case_some case5 (pre, I_SHLD op1 r ri)
                     | SHR w op1 ri => inv_case_some case5 (pre, I_SHR w op1 ri)
                     | SHRD op1 r ri => inv_case_some case5 (pre, I_SHRD op1 r ri)

                     | F2XM1 => inv_case_some case6 (pre, F_F2XM1)
                     | FABS => inv_case_some case6 (pre, F_FABS)
                     | FADD z op1 => inv_case_some case6 (pre, F_FADD z op1)
                     | FADDP op => inv_case_some case6 (pre, F_FADDP op)
                     | FBLD op => inv_case_some case6 (pre, F_FBLD op)
                     | FBSTP op => inv_case_some case6 (pre, F_FBSTP op)
                     | FCHS => inv_case_some case6 (pre, F_FCHS)
                     | FCMOVcc ct op => inv_case_some case6 (pre, F_FCMOVcc ct op)
                     | FCOM op => inv_case_some case6 (pre, F_FCOM op)
                     | FCOMP op => inv_case_some case6 (pre, F_FCOMP op)
                     | FCOMPP => inv_case_some case6 (pre, F_FCOMPP)
                     | FCOMIP op => inv_case_some case6 (pre, F_FCOMIP op)
                     | FCOS => inv_case_some case6 (pre, F_FCOS)
                     | FDECSTP => inv_case_some case6 (pre, F_FDECSTP)
                     | FDIV z op => inv_case_some case6 (pre, F_FDIV z op)
                     | FDIVP op => inv_case_some case6 (pre, F_FDIVP op)
                     | FDIVR z op => inv_case_some case6 (pre, F_FDIVR z op)
                     | FDIVRP op => inv_case_some case6 (pre, F_FDIVRP op)
                     | FFREE op => inv_case_some case6 (pre, F_FFREE op)
                     | FIADD op => inv_case_some case6 (pre, F_FIADD op)
                     | FICOM op => inv_case_some case6 (pre, F_FICOM op)
                     | FICOMP op => inv_case_some case6 (pre, F_FICOMP op)
                     | FIDIV op => inv_case_some case6 (pre, F_FIDIV op)
                     | FIDIVR op => inv_case_some case6 (pre, F_FIDIVR op)
                     | FILD op => inv_case_some case6 (pre, F_FILD op)
                     | FIMUL op => inv_case_some case6 (pre, F_FIMUL op)
                     | FINCSTP => inv_case_some case6 (pre, F_FINCSTP)
                     | FIST op => inv_case_some case6 (pre, F_FIST op)
                     | FISTP op => inv_case_some case6 (pre, F_FISTP op)
                     | FISUB op => inv_case_some case6 (pre, F_FISUB op)
                     | FISUBR op => inv_case_some case6 (pre, F_FISUBR op)
                     | FLD op => inv_case_some case6 (pre, F_FLD op)
                     | FLD1 => inv_case_some case6 (pre, F_FLD1)
                     | FLDCW op => inv_case_some case6 (pre, F_FLDCW op)
                     | FLDENV op => inv_case_some case6 (pre, F_FLDENV op)
                     | FLDL2E => inv_case_some case6 (pre, F_FLDL2E)
                     | FLDL2T => inv_case_some case6 (pre, F_FLDL2T)
                     | FLDLG2 => inv_case_some case6 (pre, F_FLDLG2)
                     | FLDLN2 => inv_case_some case6 (pre, F_FLDLN2)
                     | FLDPI => inv_case_some case6 (pre, F_FLDPI)
                     | FLDZ => inv_case_some case6 (pre, F_FLDZ)
                     | FMUL z op => inv_case_some case6 (pre, F_FMUL z op)
                     | FMULP op => inv_case_some case6 (pre, F_FMULP op)

                     | FNCLEX => inv_case_some case7 (pre, F_FNCLEX)
                     | FNINIT => inv_case_some case7 (pre, F_FNINIT)
                     | FNOP => inv_case_some case7 (pre, F_FNOP)
                     | FNSAVE op => inv_case_some case7 (pre, F_FNSAVE op)
                     | FNSTCW op => inv_case_some case7 (pre, F_FNSTCW op)
                     | FNSTSW op => inv_case_some case7 (pre, F_FNSTSW op)
                     | FPATAN => inv_case_some case7 (pre, F_FPATAN)
                     | FPREM => inv_case_some case7 (pre, F_FPREM)
                     | FPREM1 => inv_case_some case7 (pre, F_FPREM1)
                     | FPTAN => inv_case_some case7 (pre, F_FPTAN)
                     | FRNDINT => inv_case_some case7 (pre, F_FRNDINT)
                     | FRSTOR op => inv_case_some case7 (pre, F_FRSTOR op)
                     | FSCALE => inv_case_some case7 (pre, F_FSCALE)
                     | FSIN => inv_case_some case7 (pre, F_FSIN)
                     | FSINCOS => inv_case_some case7 (pre, F_FSINCOS)
                     | FSQRT => inv_case_some case7 (pre, F_FSQRT)
                     | FST op => inv_case_some case7 (pre, F_FST op)
                     | FSTENV op => inv_case_some case7 (pre, F_FSTENV op)
                     | FSTP op => inv_case_some case7 (pre, F_FSTP op)
                     | FSUB z op => inv_case_some case7 (pre, F_FSUB z op)
                     | FSUBP op => inv_case_some case7 (pre, F_FSUBP op)
                     | FSUBR z op => inv_case_some case7 (pre, F_FSUBR z op)
                     | FSUBRP op => inv_case_some case7 (pre, F_FSUBRP op)
                     | FTST => inv_case_some case7 (pre, F_FTST)
                     | FUCOM op => inv_case_some case7 (pre, F_FUCOM op)
                     | FUCOMP op => inv_case_some case7 (pre, F_FUCOMP op)
                     | FUCOMPP => inv_case_some case7 (pre, F_FUCOMPP)
                     | FUCOMI op => inv_case_some case7 (pre, F_FUCOMI op)
                     | FUCOMIP op => inv_case_some case7 (pre, F_FUCOMIP op)
                     | FXAM => inv_case_some case7 (pre, F_FXAM)
                     | FXCH op => inv_case_some case7 (pre, F_FXCH op)
                     | FXTRACT => inv_case_some case7 (pre, F_FXTRACT)
                     | FYL2X => inv_case_some case7 (pre, F_FYL2X)
                     | FYL2XP1 => inv_case_some case7 (pre, F_FYL2XP1)
                     | FWAIT => inv_case_some case7 (pre, F_FWAIT)

                     | EMMS => inv_case_some case8 (pre, M_EMMS)
                     | MOVD op1 op2 => inv_case_some case8 (pre, M_MOVD op1 op2)
                     | MOVQ op1 op2 => inv_case_some case8 (pre, M_MOVQ op1 op2)
                     | PACKSSDW op1 op2 => inv_case_some case8 (pre, M_PACKSSDW op1 op2)
                     | PACKSSWB op1 op2 => inv_case_some case8 (pre, M_PACKSSWB op1 op2)
                     | PACKUSWB op1 op2 => inv_case_some case8 (pre, M_PACKUSWB op1 op2)
                     | PADD gg op1 op2 => inv_case_some case8 (pre, M_PADD gg op1 op2)
                     | PADDS gg op1 op2 => inv_case_some case8 (pre, M_PADDS gg op1 op2)
                     | PADDUS gg op1 op2 => inv_case_some case8 (pre, M_PADDUS gg op1 op2)
                     | PAND op1 op2 => inv_case_some case8 (pre, M_PAND op1 op2)
                     | PANDN op1 op2 => inv_case_some case8 (pre, M_PANDN op1 op2)
                     | PCMPEQ gg op1 op2 => inv_case_some case8 (pre, M_PCMPEQ gg op1 op2)
                     | PCMPGT gg op1 op2 => inv_case_some case8 (pre, M_PCMPGT gg op1 op2)
                     | PMADDWD op1 op2 => inv_case_some case8 (pre, M_PMADDWD op1 op2)
                     | PMULHUW op1 op2 => inv_case_some case8 (pre, M_PMULHUW op1 op2)
                     | PMULHW op1 op2 => inv_case_some case8 (pre, M_PMULHW op1 op2)
                     | PMULLW op1 op2 => inv_case_some case8 (pre, M_PMULLW op1 op2)
                     | POR op1 op2 => inv_case_some case8 (pre, M_POR op1 op2)
                     | PSLL gg op1 op2 => inv_case_some case8 (pre, M_PSLL gg op1 op2)
                     | PSRA gg op1 op2 => inv_case_some case8 (pre, M_PSRA gg op1 op2)
                     | PSRL gg op1 op2 => inv_case_some case8 (pre, M_PSRL gg op1 op2)
                     | PSUB gg op1 op2 => inv_case_some case8 (pre, M_PSUB gg op1 op2)
                     | PSUBS gg op1 op2 => inv_case_some case8 (pre, M_PSUBS gg op1 op2)
                     | PSUBUS gg op1 op2 => inv_case_some case8 (pre, M_PSUBUS gg op1 op2)
                     | PUNPCKH gg op1 op2 => inv_case_some case8 (pre, M_PUNPCKH gg op1 op2)
                     | PUNPCKL gg op1 op2 => inv_case_some case8 (pre, M_PUNPCKL gg op1 op2)
                     | PXOR op1 op2 => inv_case_some case8 (pre, M_PXOR op1 op2)

                     | ADDPS op1 op2 => inv_case_some case9 (pre, S_ADDPS op1 op2)
                     | ADDSS op1 op2 => inv_case_some case9 (pre, S_ADDSS op1 op2)
                     | ANDNPS op1 op2 => inv_case_some case9 (pre, S_ANDNPS op1 op2)
                     | ANDPS op1 op2 => inv_case_some case9 (pre, S_ANDPS op1 op2)
                     | CMPPS op1 op2 imm => inv_case_some case9 (pre, S_CMPPS op1 op2 imm)
                     | CMPSS op1 op2 imm => inv_case_some case9 (pre, S_CMPSS op1 op2 imm)
                     | COMISS op1 op2 => inv_case_some case9 (pre, S_COMISS op1 op2)
                     | CVTPI2PS op1 op2 => inv_case_some case9 (pre, S_CVTPI2PS op1 op2)
                     | CVTPS2PI op1 op2 => inv_case_some case9 (pre, S_CVTPS2PI op1 op2)
                     | CVTSI2SS op1 op2 => inv_case_some case9 (pre, S_CVTSI2SS op1 op2)
                     | CVTSS2SI op1 op2 => inv_case_some case9 (pre, S_CVTSS2SI op1 op2)
                     | CVTTPS2PI op1 op2 => inv_case_some case9 (pre, S_CVTTPS2PI op1 op2)
                     | CVTTSS2SI op1 op2 => inv_case_some case9 (pre, S_CVTTSS2SI op1 op2)
                     | DIVPS op1 op2 => inv_case_some case9 (pre, S_DIVPS op1 op2)
                     | DIVSS op1 op2 => inv_case_some case9 (pre, S_DIVSS op1 op2)
                     | LDMXCSR op => inv_case_some case9 (pre, S_LDMXCSR op)
                     | MAXPS op1 op2 => inv_case_some case9 (pre, S_MAXPS op1 op2)
                     | MAXSS op1 op2 => inv_case_some case9 (pre, S_MAXSS op1 op2)
                     | MINPS op1 op2 => inv_case_some case9 (pre, S_MINPS op1 op2)
                     | MINSS op1 op2 => inv_case_some case9 (pre, S_MINSS op1 op2)
                     | MOVAPS op1 op2 => inv_case_some case9 (pre, S_MOVAPS op1 op2)
                     | MOVHLPS op1 op2 => inv_case_some case9 (pre, S_MOVHLPS op1 op2)
                     | MOVHPS op1 op2 => inv_case_some case9 (pre, S_MOVHPS op1 op2)
                     | MOVLHPS op1 op2 => inv_case_some case9 (pre, S_MOVLHPS op1 op2)
                     | MOVLPS op1 op2 => inv_case_some case9 (pre, S_MOVLPS op1 op2)
                     | MOVMSKPS op1 op2 => inv_case_some case9 (pre, S_MOVMSKPS op1 op2)
                     | MOVSS op1 op2 => inv_case_some case9 (pre, S_MOVSS op1 op2)
                     | MOVUPS op1 op2 => inv_case_some case9 (pre, S_MOVUPS op1 op2)
                     | MULPS op1 op2 => inv_case_some case9 (pre, S_MULPS op1 op2)
                     | MULSS op1 op2 => inv_case_some case9 (pre, S_MULSS op1 op2)
                     | ORPS op1 op2 => inv_case_some case9 (pre, S_ORPS op1 op2)
                     | RCPPS op1 op2 => inv_case_some case9 (pre, S_RCPPS op1 op2)
                     | RCPSS op1 op2 => inv_case_some case9 (pre, S_RCPSS op1 op2)
                     | RSQRTPS op1 op2 => inv_case_some case9 (pre, S_RSQRTPS op1 op2)
                     | RSQRTSS op1 op2 => inv_case_some case9 (pre, S_RSQRTSS op1 op2)

                     | SHUFPS op1 op2 imm => inv_case_some case10 (pre, S_SHUFPS op1 op2 imm)
                     | SQRTPS op1 op2 => inv_case_some case10 (pre, S_SQRTPS op1 op2)
                     | SQRTSS op1 op2 => inv_case_some case10 (pre, S_SQRTSS op1 op2)
                     | STMXCSR op => inv_case_some case10 (pre, S_STMXCSR op)
                     | SUBPS op1 op2 => inv_case_some case10 (pre, S_SUBPS op1 op2)
                     | SUBSS op1 op2 => inv_case_some case10 (pre, S_SUBSS op1 op2)
                     | UCOMISS op1 op2 => inv_case_some case10 (pre, S_UCOMISS op1 op2)
                     | UNPCKHPS op1 op2 => inv_case_some case10 (pre, S_UNPCKHPS op1 op2)
                     | UNPCKLPS op1 op2 => inv_case_some case10 (pre, S_UNPCKLPS op1 op2)
                     | XORPS op1 op2 => inv_case_some case10 (pre, S_XORPS op1 op2)
                     | PAVGB op1 op2 => inv_case_some case10 (pre, S_PAVGB op1 op2)
                     | PEXTRW op1 op2 imm => inv_case_some case10 (pre, S_PEXTRW op1 op2 imm)
                     | PINSRW op1 op2 imm => inv_case_some case10 (pre, S_PINSRW op1 op2 imm)
                     | PMAXSW op1 op2 => inv_case_some case10 (pre, S_PMAXSW op1 op2)
                     | PMAXUB op1 op2 => inv_case_some case10 (pre, S_PMAXUB op1 op2)
                     | PMINSW op1 op2 => inv_case_some case10 (pre, S_PMINSW op1 op2)
                     | PMINUB op1 op2 => inv_case_some case10 (pre, S_PMINUB op1 op2)
                     | PMOVMSKB op1 op2 => inv_case_some case10 (pre, S_PMOVMSKB op1 op2)
                     | PSADBW op1 op2 => inv_case_some case10 (pre, S_PSADBW op1 op2)
                     | PSHUFW op1 op2 imm => inv_case_some case10 (pre, S_PSHUFW op1 op2 imm)
                     | MASKMOVQ op1 op2 => inv_case_some case10 (pre, S_MASKMOVQ op1 op2)
                     | MOVNTPS op1 op2 => inv_case_some case10 (pre, S_MOVNTPS op1 op2)
                     | MOVNTQ op1 op2 => inv_case_some case10 (pre, S_MOVNTQ op1 op2)
                     | PREFETCHT0 op => inv_case_some case10 (pre, S_PREFETCHT0 op)
                     | PREFETCHT1 op => inv_case_some case10 (pre, S_PREFETCHT1 op)
                     | PREFETCHT2 op => inv_case_some case10 (pre, S_PREFETCHT2 op)
                     | PREFETCHNTA op => inv_case_some case10 (pre, S_PREFETCHNTA op)
                     | SFENCE => inv_case_some case10 (pre, S_SFENCE)

                     (* | _ => None *)
                   end)
               & _). ci_invertible_tac.
  - abstract (
        destruct_sum;
        destruct v as [pre hi]; destruct hi; trivial).
  - Time abstract (destruct w as [pre i]; destruct i; inversion H; trivial).
  Time Defined.

  (** Starting constructing the x86 parser *)
  Require Import Parser.
  Require Import Grammar.

  Definition instr_regexp :=
    projT1 (split_grammar (bigrammar_to_grammar (proj1_sig instr_bigrammar))).

  Definition ini_decoder_state :=
    initial_parser_state (bigrammar_to_grammar (proj1_sig instr_bigrammar)).

  (* Preventing Coq from expanding the def of ini_decoder_state *)
  Module Type ABSTRACT_INI_DECODER_STATE_SIG.
    Parameter abs_ini_decoder_state :
      instParserState
        (Pair_t prefix_t instruction_t)
        instr_regexp.
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
                                             instr_regexp.

  Definition parse_byte (ps: ParseState_t) (byte:int8) :
    ParseState_t * list (prefix * instr) :=
    parse_token ps (byte_less_than_num_tokens byte).

(* End X86_PARSER. *)
