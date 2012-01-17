(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

(** Properties about the DFAs that we build for the FastVerifier.
*)
Require Import Coqlib.
Require Import Parser.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import Bits.
Require Import Decode.
Require Import VerifierDFA.
Require Import Eqdep.
Unset Automatic Introduction.
Set Implicit Arguments.
Open Scope char_scope.
Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.
Require ExtrOcamlNatInt.
Import X86_PARSER_ARG.
Import X86_PARSER.
Import X86_BASE_PARSER.
Import X86Syntax.
Hint Constructors in_parser.

Ltac t := repeat
  match goal with 
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : exists _, _ |- _ ] => destruct H
    | [ |- forall _, _ ] => intros
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => 
      generalize (inj_pairT2 _ _ _ _ _ H) ; clear H ; intros ; subst
  end.

(** Inversion lemmas for parsers -- needed because of the dependencies
    (i.e., inversion will fail as a tactic on most of these because it
    can't solve a unification problem.)  These really belong in the 
    Parser library. *)
Lemma inv_any_pi : forall cs v, in_parser Any_p cs v -> cs = v::nil.
  intros. inversion H. t. subst.  auto.
Qed.

Lemma inv_char_pi : forall c cs v, in_parser (Char_p c) cs v -> v = c /\ cs = c::nil.
  intros. inversion H. t. subst. auto.
Qed.

Lemma inv_eps_pi : forall cs v, in_parser Eps_p cs v -> cs = nil /\ v = tt.
  intros. inversion H. t. subst. auto.
Qed.

Lemma inv_zero_pi : forall t cs v, in_parser (Zero_p t) cs v -> False.
  intros. inversion H.
Qed.

Lemma inv_alt_pi : forall t (p1 p2:parser t) cs v, in_parser (Alt_p p1 p2) cs v -> 
  in_parser p1 cs v \/ in_parser p2 cs v.
  intros. inversion H ; t ; auto.
Qed.

Lemma inv_cat_pi : forall t1 t2 (p1:parser t1) (p2:parser t2) cs v, 
  in_parser (Cat_p p1 p2) cs v -> 
  exists cs1, exists cs2, exists v1 : result_m t1, exists v2 : result_m t2,
    cs = cs1 ++ cs2 /\ v = (v1,v2) /\ in_parser p1 cs1 v1 /\ in_parser p2 cs2 v2.
Proof.
  intros. inversion H ; t. exists cs1. exists cs2. exists v1. exists v2. auto.
Qed.

Lemma inv_map_pi : forall t1 t2 (p:parser t1) (f:result_m t1 -> result_m t2) cs v,
  in_parser (Map_p _ f p) cs v -> exists v1 : result_m t1, 
    v = f v1 /\ in_parser p cs v1.
Proof.
  intros. inversion H. t. exists v1. auto.
Qed.

(** A tactic to apply the inversion principles for the parser denotational semantis. *)
Ltac pinv := 
  match goal with
    | [ H : in_parser Any_p _ _ |- _ ] => generalize (inv_any_pi H) ; clear H 
    | [ H : in_parser (Char_p _) _ _ |- _ ] => generalize (inv_char_pi H) ; clear H 
    | [ H : in_parser Eps_p _ _ |- _ ] => generalize (inv_eps_pi H) ; clear H
    | [ H : in_parser (Cat_p _ _) _ _ |- _ ] => generalize (inv_cat_pi H) ; clear H
    | [ H : in_parser (_ $ _) _ _ |- _ ] => generalize (inv_cat_pi H) ; clear H
    | [ H : in_parser (_ |+| _) _ _ |- _ ] => generalize (inv_alt_pi H) ; clear H
    | [ H : in_parser (Zero_p _) _ _ |- _ ] => contradiction (inv_zero_pi H)
    | [ H : in_parser (_ @ _) _ _ |- _ ] => generalize (inv_map_pi H) ; clear H    
    | [ H : in_parser (Map_p _ _ _) _ _ |- _ ] => generalize (inv_map_pi H) ; clear H    
    | [ H : _::_ = _::_ |- _] => injection H ; clear H
    | [ H : true = true |- _ ] => clear H
    | [ H : true = _ |- _ ] => generalize (eq_sym H) ; clear H ; intro H
    | [ H : ?e1 && ?e2 = true |- _ ] => 
      let x1 := fresh "x" in let x2 := fresh "y" in 
        remember e1 as x1 ; remember e2 as x2 ; 
          destruct x1 ; destruct x2 ; simpl in H ; try congruence
    | [ H : ?x = ?x -> _ |- _ ] => specialize (H (eq_refl x))
    | [ H : _ \/ _ |- _ ] => destruct H
    | [ IH : forall _ _ _ _, in_parser ?p1 _ _ -> in_parser ?p2 _ _ -> _, 
      H1 : in_parser ?p1 _ _, H2 : in_parser ?p2 _ _ |- _ ] => 
    specialize (IH _ _ _ _ H1 H2)
  end ; t ; subst.

Lemma in_alts_app : forall t (ps qs:list (parser t)) s v,
  in_parser (alts ps) s v \/ in_parser (alts qs) s v ->
  in_parser (alts (ps ++ qs)) s v.
Proof.
  induction ps ; simpl ; intros ; unfold never in * ; repeat pinv ; auto.
  econstructor. auto. eapply Alt_right_pi. eauto. 
  eapply Alt_right_pi. eauto.
Qed.

Lemma app_cons_nil A (x:A) (ys:list A) (y:A) (zs:list A) : 
  x::nil = ys ++ y :: zs -> ys = nil.
Proof.
  destruct ys. auto. induction ys. simpl. intros. discriminate H.
  simpl in *. intros. specialize (IHys y zs). discriminate H.
Qed.

(** These next few lemmas are used to invert parsers so that we can
    figure out what kinds of values they build. *)
Lemma in_app_alts : forall t (ps1 ps2:list (parser t)) s v,
  in_parser (alts (ps1 ++ ps2)) s v -> 
  in_parser (alts ps1) s v \/ in_parser (alts ps2) s v.
Proof.
  induction ps1 ; simpl ; intros. right. auto. repeat pinv. left. econstructor ; eauto.
  specialize (IHps1 _ _ _ H). pinv. left. eapply Alt_right_pi. auto. right. auto.
Qed.

Lemma in_alts_map : forall t1 t2 (p1:parser t1) (ps:list (parser t2)) s v,
  in_parser (alts (List.map (fun p2 => Cat_p p1 p2) ps)) s v -> 
  in_parser (Cat_p p1 (alts ps)) s v.
Proof.
  induction ps ; simpl ; unfold never ; intros ; repeat pinv. 
  econstructor. eauto. econstructor. eauto. auto. auto.
  specialize (IHps _ _ H). pinv. econstructor. eauto. eapply Alt_right_pi.
  eauto. auto. auto.
Qed.

Lemma inv_bitsleft bs t (p:parser t) s v : 
  in_parser (bs $$ p) s v -> 
  exists s1, exists s2, s = s1 ++ s2 /\ in_parser p s2 v.
Proof.
  unfold bitsleft. induction bs ; simpl ; intros ; repeat pinv ; simpl.
  exists nil. exists x1. auto.
  exists ((if ascii_dec a "0" then false else true)::x4).
  exists x1. split ; auto. 
Qed.

Lemma inv_modrm : forall s p,
  in_parser modrm s p -> 
  match p with | (_, Imm_op _) => False | (Reg_op r, op) => True | _ => False end.
Proof.
  unfold modrm. intros. repeat pinv ; auto. unfold rm00 in *. repeat pinv ; auto.
  unfold rm01 in *. repeat pinv ; auto. destruct x9 ; auto. unfold rm10 in * ; 
  repeat pinv ; auto. destruct x9 ; auto. unfold rm11 in * ; repeat pinv ; auto.
Qed.

Lemma inv_ext_modrm : forall bs s v,
  in_parser (ext_op_modrm bs) s v -> match v with | Imm_op _ => False | _ => True end.
Proof.
  unfold ext_op_modrm. intros. repeat pinv. unfold rm00 in *. repeat pinv ; auto.
  unfold rm01 in *. repeat pinv ; auto. destruct x9. auto. 
  unfold rm10 in *. repeat pinv ; auto. destruct x9. auto.
Qed.

Lemma inv_ext_modrm2 : forall bs s v,
  in_parser (ext_op_modrm2 bs) s v -> match v with | Imm_op _ => False | _ => True end.
Proof.
  unfold ext_op_modrm2. intros. repeat pinv. unfold rm00 in *. repeat pinv ; auto.
  unfold rm01 in *. repeat pinv ; auto. destruct x9 ; auto.
  unfold rm10 in *. repeat pinv ; auto. destruct x9 ; auto.
  unfold rm11 in *. repeat pinv ; auto.
Qed.

(** A tactic for applying these inversion properties on parsers to simplify
    them down to the cases we want to consider. *)
Ltac psimp := 
  simpl in * ;
  match goal with 
    | [ H : prod _ _ |- _ ] => destruct H
    | [ H : (_,_) = (_,_) |- _ ] => injection H ; clear H ; intros ; subst
    | [ H : in_parser (_ $$ _) _ _ |- _ ] => 
      generalize (inv_bitsleft H) ; clear H ; t ; subst
    | [ H : in_parser modrm _ _ |- _ ] => generalize (inv_modrm H) ; clear H ; t
    | [ H : in_parser (ext_op_modrm ?bs) _ _ |- _ ] => 
      generalize (@inv_ext_modrm bs _ _ H) ; clear H ; t
    | [ H : in_parser (ext_op_modrm2 ?bs) _ _ |- _ ] => 
      generalize (@inv_ext_modrm2 bs _ _ H) ; clear H ; t
  end.

(** Main connecton between non_cflow_dfa and semantics -- this is hopefully
    close enough to the actual parser used in the semantics that proving
    a relationship is easy to do.  We will see... *)
Fixpoint simple_parse' (ps:X86_PARSER.instParserState) (bytes:list int8) : 
  option ((prefix * instr) * list int8) := 
  match bytes with 
    | nil => None
    | b::bs => match X86_PARSER.parse_byte ps b with 
                 | (ps',nil) => simple_parse' ps' bs
                 | (_, v::_) => Some (v,bs)
               end
  end.

Definition simple_parse (bytes:list int8) : option ((prefix * instr) * list int8) := 
  simple_parse' X86_PARSER.initial_parser_state bytes.

Definition byte2token (b: int8) : token_id := Zabs_nat (Word.unsigned b).

(** The [valid_prefix_parser_nooveride] parser only builds a [prefix] that satisfies
   [only_gs_seg_override]. *)
Lemma pfx_nooverride : forall s v, 
  in_parser valid_prefix_parser_nooverride s v -> only_gs_seg_override v = true.
Proof.
  unfold only_gs_seg_override, valid_prefix_parser_nooverride. intros. repeat pinv ;
  simpl ; auto. 
Qed.

(** The [only_op_override] satisfies [either_prefix]. *)
Lemma pfx_nooverride_imp_either : forall pfx,
  only_op_override pfx = true -> either_prefix pfx = true.
Proof.
  destruct pfx ; unfold only_op_override, either_prefix ; simpl ; intros ; 
  unfold only_op_override, only_gs_seg_override ; simpl. 
  destruct lock_rep ; try congruence. destruct seg_override ; try congruence.
  rewrite H. auto.
Qed.

(** [only_gs_segoverride] implies [either_prefix] *)
Lemma pfx_gs_seg_imp_either : forall pfx,
  only_gs_seg_override pfx = true -> either_prefix pfx = true.
Proof.
  destruct pfx ; unfold only_gs_seg_override, either_prefix ; simpl ; intros ; 
  unfold only_op_override, only_gs_seg_override ; simpl. 
  destruct lock_rep ; try congruence. destruct seg_override ; try congruence.
  rewrite H. auto. rewrite H. destruct addr_override ; auto.
Qed.

(** The [valid_prefix_parser_rep] only builds a [prefix] that satisfies
    [only_lock_or_rep]. *)
Lemma pfx_rep : forall s v,
  in_parser valid_prefix_parser_rep s v -> only_lock_or_rep v = true.
Proof.
  unfold valid_prefix_parser_rep, only_lock_or_rep ; intros ; repeat pinv ; auto.
Qed.

(** This lemma shows that any instruction returned by the [non_cflow_parser]
    satisfies the boolean predicate [non_cflow_instr].  We should probably
    break this up into a lot of little lemmas to make it a little easier
    to adapt. *)
Lemma non_cflow_instr_inv (pre:prefix) (ins:instr) (s:list char_p) :
  in_parser VerifierDFA.non_cflow_parser s (pre,ins) -> 
  non_cflow_instr pre ins = true.
Proof.
  unfold VerifierDFA.non_cflow_parser, VerifierDFA.non_cflow_parser_list, 
    VerifierDFA.non_cflow_instrs_rep_pre.
  intros. generalize (in_app_alts _ _ H). clear H. intros.
  destruct H ;
    [idtac | generalize (in_app_alts _ _ H) ; clear H ; intro H ; destruct H] ;
  generalize (in_alts_map _ _ H) ; clear H ; intros ; pinv ;
    injection H0 ; intros ; clear H0 ; subst.
  generalize (pfx_nooverride H1). clear H1. intros.
  generalize (pfx_gs_seg_imp_either _ H). intros.

  unfold non_cflow_instrs_nosize_pre in *. simpl in *. repeat pinv.
  (* simple instructions *)
  Ltac punf c := unfold c in *; simpl in * ; pinv ; auto.
  (* logic or arithmetic instructions *)
  (* bit-test instructions *)
  Lemma bit_test : forall pfx I x1 x2 s i,
    only_gs_seg_override pfx = true -> 
    in_parser (bit_test_p x1 x2 I) s i -> 
    (forall op1 op2, no_imm_op op1 = true -> non_cflow_instr pfx (I op1 op2) = true) -> 
    non_cflow_instr pfx i = true.
  Proof.
    unfold bit_test_p. intros. repeat pinv ; repeat psimp ; repeat pinv ; 
    repeat psimp. eauto. destruct x8 ; try contradiction . eauto. eauto.
    eauto. destruct o. destruct o0 ; auto. destruct o0 ; auto. destruct o0 ; auto.
    destruct o0 ; auto.
  Qed.
  Ltac btest c := unfold c in * ; eapply bit_test ; simpl ; eauto ; intros ; auto.
  (* unary operations and a bunch of others *)
  Ltac unop c := 
    punf c ; repeat pinv ; repeat psimp ; auto ; repeat pinv ; repeat psimp ; 
      match goal with 
        | [ H : match ?x with | Imm_op _ => _ | Reg_op _ => _ | Address_op _ => _ | Offset_op _ => _ end |- _ ] => destruct x ; try contradiction ; auto
      end.
  (* rotate and shift instructions *)
  Lemma rotate : forall pfx x I s i, in_parser (rotate_p x I) s i -> 
    only_gs_seg_override pfx = true ->
    (forall b op ri, no_imm_op op = true -> non_cflow_instr pfx (I b op ri) = true) -> 
    non_cflow_instr pfx i = true.
  Proof.
    unfold rotate_p. intros. repeat pinv ; repeat psimp ; repeat pinv ; 
    repeat psimp ; eauto ; try (destruct x6 ; try contradiction ; eauto).
    destruct x8 ; try contradiction ; eauto.
  Qed.
  Ltac rot c := unfold c in * ; eapply rotate ; eauto ; simpl ; intros ; auto.
  Lemma shiftdouble : forall pfx x I s i, 
    only_gs_seg_override pfx = true ->
    in_parser (shiftdouble_p x I) s i -> 
    (forall op r ri, no_imm_op op = true -> non_cflow_instr pfx (I op r ri) = true) -> 
    non_cflow_instr pfx i = true.
  Proof.
    unfold shiftdouble_p, modrm_noreg. intros ; repeat pinv ; repeat psimp ; 
    repeat pinv ; repeat psimp ; eauto ; repeat pinv ; repeat psimp ; 
    unfold rm01, rm00, rm10 in * ; repeat pinv ; auto ; 
    try (destruct x16 ; auto) ; try (destruct x14 ; auto).
  Qed.
  Ltac shdouble c := unfold c in * ; eapply shiftdouble ; eauto ; intros ; simpl ; auto.
  Lemma logic_or_arith : forall pfx I b x1 x2 s i, 
    either_prefix pfx = true ->
    in_parser (logic_or_arith_p b x1 x2 I) s i -> 
    (forall b op1 op2, no_imm_op op1 = true -> 
        non_cflow_instr pfx (I b op1 op2) = true) ->
    non_cflow_instr pfx i = true.
  Proof.
    intros. unfold logic_or_arith_p in * ; repeat pinv ; repeat psimp ; 
    repeat pinv ; repeat psimp ;try (destruct o1 ; destruct o2 ; try 
      contradiction ; eauto ; destruct x6 ; eauto) ; eauto ;
    destruct x6 ; try contradiction ; eauto.
  Qed.
  Lemma simple_andb : forall x y, x = true -> y = true -> x && y = true.
    intros. subst. auto.
  Qed.
  Hint Resolve simple_andb.
  Ltac log_or_arith c := 
    unfold c in *; eapply logic_or_arith ; eauto ; intros ; simpl ; eauto.
  (* AAA_p *)
  punf AAA_p.
  (* AAD_p *)
  punf AAD_p.
  (* AAM_p *)
  punf AAM_p.
  (* AAS_p *)
  punf AAS_p.
  (* ADC_p *)
  log_or_arith ADC_p.
  (* ADD_p *)
  log_or_arith ADD_p.
  (* AND_p *)
  log_or_arith AND_p.
  (* CMP_p *)
  log_or_arith CMP_p.
  (* OR_p *)
  log_or_arith OR_p.
  (* SBB_p *)
  log_or_arith SBB_p.
  (* SUB_p *)
  log_or_arith SUB_p.
  (* XOR_p *)
  log_or_arith XOR_p.
  (* BSF_p *)
  unfold BSF_p in *. repeat pinv ; repeat psimp. 
  rewrite H. destruct o ; try contradiction ; auto. 
  destruct o0 ; contradiction. 
  (* BSR_p *)
  unfold BSR_p in *. repeat pinv ; repeat psimp. 
  rewrite H.
  destruct o ; try contradiction ; auto.
  destruct o0 ; contradiction.
  (* BSWAP_p *)
  punf BSWAP_p.
  (* BT_p *)
  btest BT_p. simpl. auto.
  (* BTC_p *)
  btest BTC_p. simpl. auto.
  (* BTR_p *)
  btest BTR_p. simpl. eauto.
  (* BTS_p *)
  btest BTS_p. simpl. auto.
  (* CDQ_p *)
  punf CDQ_p. 
  (* CLC_p *)
  punf CLC_p.
  (* CLD_p *)
  (* FIX:  why does NACL accept CLD? *)
  punf CLD_p.
  (* CMOVcc_p *)
  punf CMOVcc_p ; repeat psimp ; repeat pinv ; repeat psimp ; destruct o1 ; 
    try contradiction ; auto ; destruct o2 ; try contradiction ; eauto.
  (* CMC_p *)
  punf CMC_p.
  (* CMPXCHG_p *)
  punf CMPXCHG_p ; repeat psimp ; repeat pinv ; repeat psimp ; destruct o1 ; 
    try contradiction ; auto ; destruct o2 ; auto.
  (* CWDE_p *)
  punf CWDE_p.
  (* DAA_p *)
  punf DAA_p.
  (* DAS_p *)
  punf DAS_p.
  (* DEC_p *)
  unop DEC_p.
  (* DIV_p *)
  unop DIV_p.
  (* FIX: why does NACL accept HLT? *)
  (* HLT_p *)
  punf HLT_p.
  (* IDIV_p *)
  unop IDIV_p.
  (* IMUL_p *)
  unop IMUL_p ; try (destruct o0 ; contradiction) ; try (destruct o2 ; contradiction).
  (* INC_p *)
  unop INC_p.
  (* LAHF_p *)
  punf LAHF_p.
  (* LEA_p *)
  punf LEA_p. repeat psimp. unfold modrm_noreg, rm00, rm01, rm10 in *. 
  repeat pinv ; repeat psimp ; repeat pinv ; repeat psimp ; auto.
  (* LEAVE_p *)
  punf LEAVE_p.
  (* MOV_p *)
  unop MOV_p ; destruct o2 ; auto.
  (* MOVSX_p *)
  unop MOVSX_p ; destruct o2 ; auto. 
  (* MOVZX_p *)
  unop MOVZX_p ; destruct o2 ; auto.
  (* MUL_p *)
  unop MUL_p.
  (* NEG_p *)
  unop NEG_p.
  (* NOT_p *)
  unop NOT_p.
  (* POP_p *)
  unop POP_p.
  (* POPA_p *)
  punf POPA_p.
  (* PUSH_p *)
  unop PUSH_p.
  (* PUSHA_p *)
  unop PUSHA_p.
  (* RCL_p *)
  rot RCL_p.
  (* RCR_p *)
  rot RCR_p.
  (* ROL_p *)
  rot ROL_p.
  (* ROR_p *)
  rot ROR_p.
  (* SAHF_p *)
  punf SAHF_p.
  (* SAR_p *)
  rot SAR_p.
  (* SETcc_p *)
  unop SETcc_p ; destruct o2 ; auto.
  (* SHL_p *)
  rot SHL_p.
  (* SHLD_p *)
  shdouble SHLD_p.
  (* SHR_p *)
  rot SHR_p.
  (* SHRD_p *)
  shdouble SHRD_p.
  (* STC_p *)
  punf STC_p.
  (* STD_p *)
  punf STD_p. 
  (* TEST_p *)
  unop TEST_p.
  (* XADD_p *)
  unop XADD_p ; destruct o2 ; auto.
  (* XCHG_p *)
  unop XCHG_p ; destruct o2 ; auto. 
  (* never *)
  unfold never in * ; pinv.
  (****************************************************************)
  (* now to do the opsize_pre *)
  Lemma opsize_prefix : forall s v,
    in_parser valid_prefix_parser_opsize s v -> only_op_override v = true /\ 
    either_prefix v = true.
  Proof.
    intros. 
    unfold valid_prefix_parser_opsize, only_op_override, op_override_p in *.
    repeat pinv. simpl. unfold either_prefix. simpl. auto.
  Qed.
  generalize (opsize_prefix H1) ; clear H1 ; intros. destruct H.
  unfold non_cflow_instrs_opsize_pre in *. simpl in *. repeat pinv.
  (* ADC_p *)
  log_or_arith ADC_p.
  (* ADD_p *)
  log_or_arith ADD_p.
  (* AND_p *)
  log_or_arith AND_p.
  (* CMP_p *)
  log_or_arith CMP_p.
  (* OR_p *)
  log_or_arith OR_p.
  (* SBB_p *)
  log_or_arith SBB_p.
  (* SUB_p *)
  log_or_arith SUB_p.
  (* SHL_p *)
  Lemma rotate2 : forall pfx x I s i, in_parser (rotate_p x I) s i -> 
    only_op_override pfx = true ->
    (forall b op ri, no_imm_op op = true -> non_cflow_instr pfx (I b op ri) = true) -> 
    non_cflow_instr pfx i = true.
  Proof.
    unfold rotate_p. intros. repeat pinv ; repeat psimp ; repeat pinv ; 
    repeat psimp ; eauto ; try (destruct x6 ; try contradiction ; eauto).
    destruct x8 ; try contradiction ; eauto.
  Qed.
  Ltac rot2 c := unfold c in * ; eapply rotate2 ; eauto ; simpl ; intros ; auto.
  rot2 SHL_p.
  (* SHLD_p *)
  Lemma shiftdouble2 : forall pfx x I s i, 
    only_op_override pfx = true ->
    in_parser (shiftdouble_p x I) s i -> 
    (forall op r ri, no_imm_op op = true -> non_cflow_instr pfx (I op r ri) = true) -> 
    non_cflow_instr pfx i = true.
  Proof.
    unfold shiftdouble_p, modrm_noreg. intros ; repeat pinv ; repeat psimp ; 
    repeat pinv ; repeat psimp ; eauto ; repeat pinv ; repeat psimp ; 
    unfold rm01, rm00, rm10 in * ; repeat pinv ; auto ; 
    try (destruct x16 ; auto) ; try (destruct x14 ; auto).
  Qed.
  Ltac shdouble2 c := unfold c in * ; eapply shiftdouble2 ; eauto ; intros ; simpl ; auto.
  shdouble2 SHLD_p.
  (* SHR_p *)
  rot2 SHR_p.
  (* SAR_p *)
  rot2 SAR_p.
  (* SHRD_p *)
  shdouble2 SHRD_p.
  (* XOR_p *)
  log_or_arith XOR_p.
  (* IMUL_p *)
  unop IMUL_p. destruct o0 ; auto. destruct o2 ; auto. destruct o2 ; auto.
  (* MOV_p *)
  unop MOV_p ; destruct o2 ; auto.
  (* MOVSX_p *)
  unop MOVSX_p ; destruct o2 ; auto.
  (* MOVZX_p *)
  unop MOVZX_p ; destruct o2 ; auto.
  (* NEG_p *)
  unop NEG_p.
  (* NOT_p *)
  unop NOT_p. 
  (* DIV_p *)
  unop DIV_p.
  (* IDIV_p *)
  unop IDIV_p.
  (* TEST_p *)
  unop TEST_p.
  (* CDQ_p *)
  punf CDQ_p.
  (* CWDE_p *)
  punf CWDE_p.
  (* MUL_p *)
  unop MUL_p.
  (* XCHG_p *)
  unop XCHG_p ; destruct o2 ; auto.
  (* never *)
  unfold never in * ; pinv.
  (* other stuff *)
  generalize (pfx_rep H1). clear H1.
  simpl in H2. repeat pinv.
  (* CMPS_p *)
  punf CMPS_p.
  (* MOVS_p *)
  punf MOVS_p.
  (* STOS_p *)
  punf STOS_p.
  unfold never in *. pinv.
Qed.

Lemma byteLt256 : forall b:int8, (byte2token b < 256)%nat.
Proof.
  intro. destruct b. unfold byte2token.
  unfold Word.modulus, Word.wordsize, two_power_nat, shift_nat in *. simpl in *.
  destruct intrange. assert ((Zabs_nat intval < Zabs_nat 256)%nat).
  apply Zabs_nat_lt. auto. simpl in *. unfold nat_of_P in *. simpl in *. 
  auto.
Qed.

Lemma bytesLt256 : forall (bs:list int8), 
  list_all (fun t => (t < 256)%nat) (List.map byte2token bs).
Proof.
  induction bs ; auto ; simpl ; auto ; split ; auto. apply byteLt256. 
Qed.

Lemma in_map_alts t1 t2 (p1:parser t1) (ps:list (parser t2)) s v : 
  in_parser (p1 $ (alts ps)) s v ->
  in_parser (alts (List.map (fun p2 => p1 $ p2) ps)) s v .
Proof.
  induction ps ; simpl ; intros ; repeat pinv. unfold never in *. pinv.
  eapply Alt_left_pi. econstructor ; eauto. eapply Alt_right_pi. 
  eapply IHps. econstructor ; eauto.
Qed.

(** The [valid_prefix_parser_nooverride] parser used in the DFA is a subset of the 
    [prefix_parser_nooverride] parser used in the semantics. *)
Lemma prefix_subset : 
  forall s v, in_parser valid_prefix_parser_nooverride s v -> 
    in_parser prefix_parser_nooverride s v.
Proof.
  unfold valid_prefix_parser_nooverride, prefix_parser_nooverride. intros.
  repeat pinv. unfold option_perm2. econstructor. econstructor. 
  econstructor. eauto. eauto. simpl. auto.
  unfold option_perm2. econstructor.
  eapply Alt_right_pi. eapply Alt_right_pi. econstructor. 
  unfold segment_override_p. econstructor. repeat (eapply Alt_right_pi).
  econstructor. eapply H0. eauto. eauto. simpl. auto.
Qed.

Lemma mem_parser_subset : 
  forall t (p:parser t) (ps:list (parser t)),
    In p ps -> 
    forall s v, in_parser p s v -> in_parser (alts ps) s v.
Proof.
  induction ps ; simpl. intros. contradiction. intros.
  destruct H ; subst. eapply Alt_left_pi ; auto. eapply Alt_right_pi ; auto.
Qed.

Lemma alts_subset : 
  forall t (ps qs:list (parser t)), 
    (forall p, In p ps -> In p qs) -> 
    forall s v, in_parser (alts ps) s v -> in_parser (alts qs) s v.
Proof.
  induction ps. simpl. intros. unfold never in *. pinv. intros.
  simpl in *. pinv. destruct H0. eapply mem_parser_subset. eapply (H a). auto. auto.
  apply IHps. intros. eapply H. right. auto. auto.
Qed.

(** All parsers in [non_cflow_instrs_nosize_pre] are also in 
    [instr_parsers_nosize_pre]. *)
Lemma ncflow_is_subset : 
  forall p, In p non_cflow_instrs_nosize_pre -> 
    In p instr_parsers_nosize_pre.
Proof.
  Ltac pv H := repeat (try (left ; auto ; fail) ; right).
  unfold non_cflow_instrs_nosize_pre, instr_parsers_nosize_pre. intros ; simpl in * ; 
  repeat (destruct H ; [pv H | idtac]). contradiction.
Qed.

(** This shows that if a string matches the [non_cflow_parser], then it 
    will also match the [instruction_parser].  It's half of what we need
    to establish the correctness of the [non_cflow] DFA. *)
Lemma non_cflow_parser_subset : 
  forall s v, in_parser non_cflow_parser s v -> 
    in_parser instruction_parser s v.
Proof.
  unfold non_cflow_parser, instruction_parser.
  unfold non_cflow_parser_list, instruction_parser_list.
  intros. generalize (in_app_alts _ _ H). clear H. intro. 
  destruct H ; [idtac | generalize (in_app_alts _ _ H) ; clear H ; intro H ; destruct H];
  generalize (in_alts_map _ _ H) ; clear H ; intro ; apply in_alts_app.
  left. pinv. eapply in_map_alts. 
  eapply (fun H1 H2 => @Cat_pi _ _ _ _ (x ++ x0) (x1,x2) x x0 x1 x2 H1 H2 (eq_refl _)
    (eq_refl _)). apply prefix_subset. auto. eapply alts_subset. eapply ncflow_is_subset.
  auto.
  right. pinv. eapply in_map_alts.
  eapply (fun H1 H2 => @Cat_pi _ _ _ _ (x ++ x0) (x1,x2) x x0 x1 x2 H1 H2 (eq_refl _)
    (eq_refl _)) ; auto. clear H2. unfold valid_prefix_parser_opsize in *.
  pinv. unfold prefix_parser_opsize. econstructor. econstructor. eauto. auto.
  pinv. left. eapply in_map_alts.
  eapply (fun H1 H2 => @Cat_pi _ _ _ _ (x ++ x0) (x1,x2) x x0 x1 x2 H1 H2 (eq_refl _)
    (eq_refl _)). clear H2. unfold valid_prefix_parser_rep, prefix_parser_nooverride
  in * ; repeat pinv ; unfold option_perm2. repeat econstructor.
  econstructor. eapply Alt_right_pi. econstructor. unfold lock_or_rep_p.
  unfold bitsleft in *. econstructor. pinv. pinv. econstructor. econstructor.
  eauto. repeat eapply Alt_right_pi. econstructor. eauto. eauto. auto. eauto.
  simpl. eauto. eauto. simpl. auto. apply (alts_subset non_cflow_instrs_rep_pre) ; 
  auto. clear H1 H2 x1 x0 x x2. unfold non_cflow_instrs_rep_pre in *. 
  unfold instr_parsers_nosize_pre. simpl. intros. 
  repeat (destruct H ; [ repeat (try (left ; auto ; fail) ; right) | idtac ]).
  contradiction.
Qed.
  
Definition nat_to_byte(n:nat) : int8 := Word.repr (Z_of_nat n).

Lemma byte_nat_rev : forall (b:int8), nat_to_byte(byte2token b) = b.
Proof.
  unfold nat_to_byte, byte2token. intros. destruct b. simpl.
  unfold Word.repr. assert (Z_of_nat (Zabs_nat intval) mod Word.modulus 7 = intval).
  unfold Word.modulus, two_power_nat, Word.wordsize, shift_nat in *.
  simpl in *. rewrite inj_Zabs_nat. rewrite Zabs_eq ; auto. 
  rewrite Zmod_small ; auto. destruct intrange ; auto. 
  generalize (Word.mod_in_range 7 (Z_of_nat (Zabs_nat intval))) as H1.
  rewrite H. intros. assert (H1 = intrange). apply Coqlib.proof_irrelevance.
  rewrite H0. auto.
Qed.

Lemma n2bs xs : List.map nat_to_byte (List.map byte2token xs) = xs.
Proof.
  induction xs. auto. simpl. rewrite IHxs. rewrite byte_nat_rev. auto.
Qed.

Lemma explode_bits xs : 
  list_all (fun n => (n < 256)%nat) xs -> 
  flat_map byte_explode (List.map nat_to_byte xs) = flat_map nat2bools xs.
Proof.
  induction xs. auto. intros. simpl in H. destruct H.
  replace (flat_map byte_explode (List.map nat_to_byte (a::xs))) with 
    (byte_explode (nat_to_byte a) ++ 
      (flat_map byte_explode (List.map nat_to_byte xs))) ; auto.
  replace (flat_map nat2bools (a::xs)) with (nat2bools a ++ (flat_map nat2bools xs)) ; 
    auto. rewrite IHxs ; auto.
  replace (byte_explode (nat_to_byte a)) with (nat2bools a) ; auto. clear IHxs H0 xs.
  unfold nat2bools. unfold byte_explode.
  replace (Z_of_nat a) with (Word.unsigned (nat_to_byte a)). auto.
  unfold nat_to_byte. simpl. rewrite Zmod_small ; auto. 
  assert (Z_of_nat a < Z_of_nat 256). apply inj_lt ; auto.
  split.
  apply Zle_0_nat. auto.
Qed.

(** These abstraction shananigans are necessary to keep Coq from
    trying to actually build the DFA from within Coq. *)
Module Type ABSTRACT_MAKE_DFA_SIG.
  Parameter abstract_build_dfa : 
    nat -> (token_id -> list char_p) -> nat -> regexp unit_t -> option DFA.
  Parameter build_dfa_eq : abstract_build_dfa = build_dfa.
End ABSTRACT_MAKE_DFA_SIG.

Module ABSTRACT_MAKE_DFA : ABSTRACT_MAKE_DFA_SIG.
  Definition abstract_build_dfa := build_dfa.
  Definition build_dfa_eq := eq_refl build_dfa.
End ABSTRACT_MAKE_DFA.

Import ABSTRACT_MAKE_DFA.

(** This lemma tells that that the DFA build from the [non_cflow_parser],
    when run on an input string of bytes [bytes] and produces [Some(n,nats2)],
    implies that there exists some prefix of bytes, [bytes1] (of length [n]) 
    such that both the [non_cflow_parser] and the [instruction_parser], accept
    [bytes1] and produce the same value.  Furthermore, there is no smaller
    prefix of [bytes] that the [non_cflow_parser] will accept. Also,
*)
Lemma non_cflow_dfa_corr1 :
  forall (d:DFA), 
    abstract_build_dfa 256 nat2bools 400 (par2rec non_cflow_parser) = Some d -> 
    forall (bytes:list int8) (n:nat) (nats2:list nat),
      dfa_recognize 256 d (List.map byte2token bytes) = Some (n, nats2) -> 
      exists bytes1, exists pfx:prefix, exists ins:instr, 
        in_parser non_cflow_parser (flat_map byte_explode bytes1) (pfx,ins) /\ 
        in_parser instruction_parser (flat_map byte_explode bytes1) (pfx,ins) /\ 
        n = length bytes1 /\ 
        bytes = bytes1 ++ (List.map nat_to_byte nats2) /\ 
        non_cflow_instr pfx ins = true /\
        (forall ts3 ts4,
          (length ts3 < length bytes1)%nat -> 
          bytes = ts3 ++ ts4 -> 
          forall v0, ~ in_parser non_cflow_parser (flat_map byte_explode ts3) v0).
Proof.
  intros. subst. rewrite build_dfa_eq in H.
  generalize (dfa_recognize_corr _ _ _ _ H (List.map byte2token bytes) 
  (bytesLt256 _)). clear H. rewrite H0. clear H0. mysimp. destruct x0. 
  exists (List.map nat_to_byte x). exists p. exists i. 
  assert (List.map nat_to_byte (x ++ nats2) = bytes).
  rewrite <- H. apply n2bs. rewrite map_app in H3. rewrite <- H3.
  rewrite map_length. generalize (non_cflow_instr_inv H1). 
  assert (list_all (fun n => n < 256)%nat (x ++ nats2)).
  rewrite <- H. apply (bytesLt256 bytes). generalize (list_all_app _ _ _ H4).
  intros. destruct H5. 
  assert (flat_map byte_explode (List.map nat_to_byte x) = flat_map nat2bools x).
  apply explode_bits. auto. rewrite H8. mysimp.
  apply non_cflow_parser_subset. auto. intros.
  specialize (H2 (List.map byte2token ts3) (List.map byte2token ts4)).
  repeat rewrite map_length in H2. specialize (H2 H9).
  rewrite <- map_app in H10. rewrite <- H in H10.
  rewrite <- map_app in H2. rewrite <- H10 in H2. rewrite n2bs in H2. 
  specialize (H2 (eq_refl _)). intro. specialize (H2 v0). apply H2.
  assert (flat_map nat2bools (List.map byte2token ts3) = flat_map byte_explode ts3).
  rewrite <- explode_bits. rewrite n2bs. auto. apply (bytesLt256 ts3).
  rewrite <- H12 in H11.  auto.
Qed.

(** In what follows, we need to prove that if the instruction parser
    accepts a string [s] and produces a value [v], then [v] is the 
    only value associated with [s].  That is, the instruction parser
    denotes a partial function from strings to values (i.e., is deterministic.)
    To prove this, we already have that each of the parsers is disjoint
    (i.e., accept different subsets of strings.)  Now all we need to 
    do is establish that all of the parsers are deterministic. 

    A brute force approach (exploding the parsers into a disjunctive
    normal form, and checking all of the paths) does not scale well
    enough.  So we instead prove that the individual parsers, without
    the prefixes on them, are deterministic, and then show that if
    you add the prefixes on, they remain deterministic.  
*)

(** Simple determ holds when a parser doesn't contain [Star_p] nor any 
    [Alt_p].  We can show that these parsers produce at most one value
    (i.e., are deterministic.)  *)
Fixpoint simple_determ t (p:parser t) : bool := 
  match p with 
    | Any_p => true
    | Char_p _ => true
    | Eps_p => true
    | Zero_p _ => true
    | Cat_p t1 t2 p1 p2 => simple_determ p1 && simple_determ p2
    | Map_p t1 t2 f p => simple_determ p
    | _ => false
  end.

(** [simple_determ] implies a parser only accepts strings of the same size. *)
Lemma simple_determ_same_size : forall t (p:parser t), simple_determ p = true ->
  forall s1 v1 s2 v2, 
    in_parser p s1 v1 -> 
    in_parser p s2 v2 -> length s1 = length s2.
Proof.
  induction p ; simpl ; intros ; try congruence ; repeat pinv ; auto.
  repeat rewrite app_length. congruence. apply (IHp H _ _ _ _ H1 H2).
Qed. 

Lemma app_inj_length : forall A (x1 x2 y1 y2:list A), 
  length x1 = length y1 -> 
  length x2 = length y2 -> 
  x1 ++ x2 = y1 ++ y2 -> 
  x1 = y1 /\ x2 = y2.
Proof.
  induction x1 ; simpl ; destruct y1 ; simpl ; auto ; intros ; try discriminate.
  pinv. assert (length x1 = length y1). omega. specialize (IHx1 _ _ _ H2 H0 H1).
  destruct IHx1. subst. auto.
Qed.
  
(** [simple_determ] implies a parser is deterministic. *)
Lemma simple_determ_corr : forall t (p:parser t), 
  simple_determ p = true -> 
  forall s v1 v2,
    in_parser p s v1 -> in_parser p s v2 -> v1 = v2.
Proof.
  induction p ; simpl ; intros ; try congruence ; repeat pinv ; auto.
  generalize (simple_determ_same_size Heqx7 H3 H2).
  generalize (simple_determ_same_size Heqy H4 H5). intros.
  generalize (app_inj_length _ _ _ _ H1 H H0). intros. destruct H6 ; subst.
  specialize (IHp1 _ _ _ H2 H3). specialize (IHp2 _ _ _ H5 H4). subst. auto.
  specialize (IHp H _ _ _ H2 H1). subst. auto.
Qed.

(** We are going to calculate the DNF for the prefixes.  But we can only
    do this for parsers that don't contain [Star_p]. *)
Fixpoint star_free t (p:parser t) : bool := 
  match p with 
    | Star_p _ _ => false
    | Cat_p t1 t2 p1 p2 => star_free p1 && star_free p2
    | Alt_p t p1 p2 => star_free p1 && star_free p2
    | Map_p t1 t2 f p' => star_free p'
    | _ => true
  end.

(** Disjunctive normal-form for parsers.  This is not well-defined when 
    the parser includes [Star_p]. *)
Fixpoint dnf t (p:parser t) : list (parser t) := 
  match p with 
    | Alt_p t p1 p2 => (dnf p1) ++ (dnf p2)
    | Cat_p t1 t2 p1 p2 => 
      flat_map (fun d1 => List.map (fun d2 => Cat_p d1 d2) (dnf p2)) (dnf p1)
    | Map_p t1 t2 f p => List.map (fun d => @Map_p t1 t2 f d) (dnf p)
    | p => p::nil
  end.

Require Import CheckDeterministic.

(** Check that a parser is determinsistic -- blow it up into its disjunctive
    normal form, and use [check_all_p] to ensure that there is no string in
    common. *)
Definition check_determ t (p:parser t) : bool := 
  star_free p && check_all_p' 3 (dnf p).

(** Check that a list of parsers is determinsitic. *)
Fixpoint check_determ_ps t (ps:list (parser t)) : bool := 
  match ps with 
    | nil => true
    | p::ps' => check_determ p && check_determ_ps ps'
  end.

(** converting a parser to DNF is equivalent to the original parser *)
Lemma dnf_corr1 t (p:parser t) s v : 
  in_parser p s v -> 
  in_parser (alts (dnf p)) s v.
Proof.
  induction 1 ; simpl ; intros ; subst ; try (econstructor ; eauto ; fail) ; 
    repeat
    match goal with 
      | [ H : _ && _ = true |- _ ] => generalize (andb_prop _ _ H) ; clear H ; t
      | [ H : ?x = true -> _, H1 : ?x = true |- _ ] => specialize (H H1)
      | [ |- in_parser (alts (_ ++ _)) _ _ ] => eapply in_alts_app
      | _ => auto
    end. 
  generalize (dnf p1) (dnf p2) IHin_parser1 IHin_parser2. 
  induction l ; simpl ; unfold never ; intros ; repeat pinv.  
  eapply in_alts_app. left. induction l0 ; simpl in *; unfold never in *; intros ; 
  repeat pinv. eapply Alt_left_pi. eauto. eapply Alt_right_pi. eauto.
  eapply in_alts_app. right. auto.
  generalize (dnf p) IHin_parser. induction l ; simpl ; unfold never ; intros ; 
  repeat pinv. eapply Alt_left_pi ; eauto. eapply Alt_right_pi ; eauto.
Qed.

Lemma dnf_corr2 t (p:parser t) s v :
  in_parser (alts (dnf p)) s v -> 
  star_free p = true -> 
  in_parser p s v.
Proof.
  induction p ; simpl ; unfold never ; intros ; repeat pinv ; eauto.
  generalize (dnf p1) (dnf p2) IHp1 IHp2 H ; clear IHp1 IHp2 H Heqx Heqy.
  induction l ; simpl ; unfold never in * ; intros ; repeat pinv.
  generalize (in_app_alts _ _ H). clear H ; intros. destruct H.
  clear IHl. induction l0 ; simpl in * ; unfold never in * ; pinv.
  destruct H. pinv. econstructor. eapply IHp1 ; eauto. eapply Alt_left_pi. eauto.
  eapply IHp2 ; eauto. eapply Alt_left_pi. eauto. auto. auto.
  eapply IHl0. intros. eapply IHp2. eapply Alt_right_pi. eauto. auto. auto.
  eapply IHl. intros. eapply IHp1. eapply Alt_right_pi ; eauto. auto. 
  eapply IHp2. auto. generalize (in_app_alts _ _ H). intros. pinv ; eauto.
  generalize (dnf p) IHp H ; clear IHp H. induction l ; simpl ; unfold never ; 
  intros ; repeat pinv. econstructor. eapply IHp. eapply Alt_left_pi. eauto.
  auto. auto. eapply IHl. intros. eapply IHp. eapply Alt_right_pi ; eauto. 
  auto. auto.
Qed.

(** All of the parsers in [ps] are [simple_determ]. *)
Fixpoint simple_determ_list t (ps:list (parser t)) : bool := 
  match ps with 
    | nil => true
    | p::ps' => simple_determ p && simple_determ_list ps'
  end.

Lemma simple_determ_app t (ps1 ps2:list (parser t)) : 
  simple_determ_list (ps1 ++ ps2) = 
  simple_determ_list ps1 && simple_determ_list ps2.
Proof.
  induction ps1 ; simpl ; auto. intros. destruct (simple_determ a) ; simpl ; auto.
Qed.

(** All of the parsers in [dnf p] are [simple_determ] *)
Lemma dnf_determ t (p:parser t) : 
  star_free p = true -> simple_determ_list (dnf p) = true.
Proof.
  induction p ; simpl ; intros ; subst ; simpl ; repeat pinv ; auto.
  generalize (dnf p1) (dnf p2) IHp1 IHp2 ; clear IHp1 IHp2.
  induction l ; simpl ; intros ; try contradiction ; repeat pinv ; auto.
  rewrite simple_determ_app. rewrite IHl ; auto. apply simple_andb ; auto.
  clear IHl. induction l0 ; simpl ; auto. rewrite Heqx0. simpl in *.
  generalize (andb_prop _ _ IHp2). t. rewrite H. rewrite IHl0 ; auto.
  rewrite simple_determ_app. rewrite IHp1. auto.
  specialize (IHp H). clear H. generalize (dnf p) IHp ; clear IHp.
  induction l ; simpl ; auto ; t. generalize (andb_prop _ _ IHp). t.
  rewrite H. rewrite IHl ; auto.
Qed.

(** This ensures that if [p] is deterministic and [s] and [v] are in the 
   denotation of [p], then there is no prefix of [s] in the domain of the 
   denotation of [p], and that there is at most one value associated with 
   [s] in the denotation of [p]. *)
Lemma check_determ_corr' t (p:parser t) : 
  check_determ p = true -> 
  forall s v,
    in_parser p s v -> 
    (forall s1 s2 v', 
        s = s1 ++ s2 -> 
        in_parser p s1 v' -> s2 = nil /\ v' = v).
Proof.
  unfold check_determ. intros. generalize (andb_prop _ _ H) ; clear H ; t.
  generalize (dnf_corr1 H0). intros. subst. 
  generalize (dnf_corr1 H2). intros. clear H2 H0.
  generalize (check_all_p'_corr _ _ H3 H4).
  generalize (check_all_p'_corr _ _ H3 H1). t.
  generalize (dnf_determ p H). 
  generalize (dnf p) x2 x3 x4 x x0 x1 H0 H2 H7 H5 H8 H6.
  clear x2 x3 x4 x x0 x1 H0 H2 H7 H5 H8 H6 H H3 H4 H1.
  induction l ; intros ; destruct x2 ; simpl in H0 ; try congruence ;
  destruct x ; simpl in H2 ; try congruence ; intros. injection H0 ; clear H0 ; 
  injection H2 ; clear H2 ; intros ; subst.
  generalize (andb_prop _ _ H) ; clear H ; t. clear H0. subst.
  generalize (simple_determ_same_size H H7 H5). intros.
  rewrite app_length in H0. destruct s2. rewrite <- app_nil_end in H5.
  rewrite (simple_determ_corr H H7 H5). auto. simpl in H0. assert False. omega.
  contradiction. 
  injection H0 ; injection H2 ; clear H0 H2 ; intros ; subst. subst. clear IHl.
  simpl in *. assert False. apply H8. exists s2. exists v.
  apply in_alts_comm'. eapply Alt_left_pi. auto. contradiction.
  injection H0 ; injection H2 ; clear H0 H2 ; intros ; subst. clear IHl. subst.
  simpl in *. assert False. apply H8. exists s2. exists v. eapply Alt_left_pi. auto.
  contradiction.
  injection H0 ; injection H2 ; clear H0 H2 ; intros ; subst.
  specialize (IHl x2 x3 x4 x x0 x1 H2 (eq_refl _) H7 H5). apply IHl ; clear IHl.
  intro. apply H8. t. exists x5. exists x6. simpl. eapply Alt_right_pi. auto.
  intro ; t. apply H6. exists x5. exists x6. simpl. eapply Alt_right_pi. auto.
  simpl in H. generalize (andb_prop _ _ H). t ; auto.
Qed.

(** Check that all of the instruction parsers (without the prefixes) are 
    deterministic.  This runs fast enough that we can afford to do this. *)
Lemma all_parsers_determ : 
  check_determ_ps (instr_parsers_opsize_pre ++ instr_parsers_nosize_pre) = true.
Proof.
  vm_compute. auto.
Qed.

(** This checks that when we add a prefix to a parser, that the parser 
    remains deterministic.  We do so by calculating the DNF of the 
    prefix, and pre-pending each DNF term to the parser. *)
Definition check_pfx t1 t2 (p1:parser t1) (p2:parser t2) := 
  check_all_p' 3 (List.map (fun d1 => Cat_p d1 p2) (dnf p1)).

Fixpoint check_all_pfx t1 t2 (p1:parser t1) (p2s:list (parser t2)) := 
  match p2s with 
    | nil => true
    | p2::p2s' => check_pfx p1 p2 && check_all_pfx p1 p2s'
  end.

(** Check that adding all of the prefixes to the parsers keeps them
    deterministic. *)
Lemma check_all_prefixed_instructions : 
  (check_all_pfx prefix_parser_nooverride instr_parsers_nosize_pre) && 
  (check_all_pfx prefix_parser_opsize instr_parsers_opsize_pre) = true.
Proof.
  vm_compute. auto.
Qed.

Lemma inj_app_length A (x1 x2 y1 y2:list A) : 
  length x1 = length y1 -> 
  x1 ++ x2 = y1 ++ y2 -> 
  x1 = y1 /\ x2 = y2.
Proof.
  induction x1 ; simpl ; destruct y1 ; simpl ; auto ; intros ; try discriminate.
  injection H0. intros ; subst. assert (length x1 = length y1). omega.
  specialize (IHx1 _ _ _ H2 H1). t. subst. auto.
Qed.

(** This shows that if a we add a [simple_determ] prefix to a deterministic
    parser, then at most one value is associated with a string [s] in the
    denotation of the compound parser, and furthermore, there is no prefix
    of [s] that is in the denotation. This basically handles one of the
    alternatives of the DNF of a prefix. *)
Lemma simple_pfx_determ' t1 t2 (p1:parser t1) (p2:parser t2) : 
  simple_determ p1 = true -> 
  check_determ p2 = true -> 
  forall s v1,
    in_parser (Cat_p p1 p2) s v1 -> 
    forall s1 s2 v2,
      s = s1 ++ s2 ->
      in_parser (Cat_p p1 p2) s1 v2 -> 
      s2 = nil /\ v1 = v2.
Proof.
  intros. generalize (simple_determ_same_size H). intros. repeat pinv.
  rewrite app_ass in H1.
  generalize (inj_app_length _ _ _ _ H4 H1). t. subst.
  generalize (simple_determ_corr H). intros. rewrite (H2 _ _ _ H3 H6).
  generalize (check_determ_corr' H0). intros. 
  specialize (H8 _ _ H5 x0 s2 _ (eq_refl _) H7). t ; subst. auto.
Qed.

Lemma in_dnf_cat t1 t2 (p1:parser t1) (p2:parser t2) s v: 
  in_parser (Cat_p p1 p2) s v -> 
  in_parser (alts (List.map (fun d1 => Cat_p d1 p2) (dnf p1))) s v.
Proof.
  intros. pinv. generalize (dnf_corr1 H1). generalize (dnf p1). induction l ; 
  simpl ; unfold never ; intros ; repeat pinv. econstructor. econstructor ; eauto.
  eapply Alt_right_pi. eauto.
Qed.

Lemma list_map_eq_app : forall t1 t2 (f:t1->t2) (x:list t1) (a c:list t2) (b:t2),
  List.map f x = a ++ b :: c -> 
  exists a':list t1, exists b':t1, exists c':list t1, 
    (x = a' ++ b' :: c') /\ a = List.map f a' /\ b = f b' /\ c = List.map f c'.
Proof.
  induction x ; simpl ; intros. 
  generalize (nil_is_nil_app_nil _ _ H). t ; subst. congruence.
  destruct a0. exists nil. simpl in *. exists a. exists x. injection H ; intros ;
  subst. auto. simpl in *. injection H ; intros ; subst ; clear H. 
  specialize (IHx _ _ _ H0). t. subst. exists (a::x0). exists x1. exists x2. auto.
Qed.

(** Now show that if [p1] is a star-free prefix, and [p2] is a deterministic
    parser, then adding [p1] to [p2] yields a parser that is deterministic,
    and furthermore, if [s] is in the domain of [p1 $ p2], then there is no
    prefix of [s] that is in the domain of [p1 $ p2]. *)
Lemma check_pfx_determ' t1 t2 (p1:parser t1) (p2:parser t2) : 
  star_free p1 = true ->
  check_determ p2 = true -> 
  check_pfx p1 p2 = true -> 
  forall s v1,
    in_parser (Cat_p p1 p2) s v1 -> 
    forall s1 s2 v2,
      s = s1 ++ s2 -> 
      in_parser (Cat_p p1 p2) s1 v2 -> s2 = nil /\ v1 = v2.
Proof.
  intros. generalize (in_dnf_cat H2). intros. generalize (in_dnf_cat H4). intros.
  clear H2 H4. 
  generalize (check_all_p'_corr _ _ H1 H5). generalize (check_all_p'_corr _ _ H1 H6). t. 
  rewrite H2 in H5.  rewrite H4 in H6.
  generalize (in_alts_comm _ _ _ H5).
  generalize (in_alts_comm _ _ _ H6). intros. clear H5 H6. 
  generalize (list_map_eq_app _ (dnf p1) x2 x4 x3 H2). t.  subst.
  generalize (dnf_determ _ H). intros. rewrite H5 in *. 
  rewrite (simple_determ_app) in H3. generalize (andb_prop _ _ H3) ; clear H3 ; t.
  simpl in H6. generalize (andb_prop _ _ H6). clear H6 ; t. 
  generalize (inv_alt_pi H12). generalize (inv_alt_pi H11). clear H11 H12. intros. 
  destruct H11 ; destruct H12 ; 
    try (eapply simple_pfx_determ' ; eauto) ;
      contradiction H10 ; exists s2 ; exists v1 ; auto.
Qed.

(** Show that the prefixes used in the semantics are star-free. *)
Lemma star_free_prefix_parser_nooverride : 
  star_free prefix_parser_nooverride = true.
Proof.
  vm_compute. auto.
Qed.

Lemma star_free_prefix_parser_opsize : 
  star_free prefix_parser_opsize = true.
Proof.
  vm_compute. auto.
Qed.

Lemma and_parse2rexp t (p1:parser t) (ps:list (parser t)) s v1 v2: 
  in_parser p1 s v1 -> in_parser (alts ps) s v2 -> 
  in_rexp (OptAnd_r (parser2rexp p1) (alts_r (List.map (@parser2rexp _) ps))) s.
Proof.
  intros. apply opt_and_r_corr. econstructor. eapply parse2rexp_corr1 ; eauto.
  generalize ps H0. induction ps0. simpl. unfold never. intros. pinv.
  simpl. intros. pv_opt. pinv. destruct H1. econstructor. eapply parse2rexp_corr1.
  eauto. eapply Alt_right_ri. auto.
Qed.

(** An intermediate lemma that tells us that when all of the parsers
    in [p::ps] have been shown to be disjoint, then there is no 
    string in the domain of both [p] and [ps]. *)
Lemma check_all_p'_tail t n (p:parser t) (ps:list (parser t)) : 
  check_all_p' n (p::ps) = true -> 
  check_all_p' n ps = true /\ 
  (forall s v1, in_parser p s v1 -> 
    forall s1 s2 v2, s = s1++s2 -> ~ in_parser (alts ps) s1 v2) /\
  (forall s v1, in_parser (alts ps) s v1 -> 
    forall s1 s2 v2, s = s1++s2 -> ~ in_parser p s1 v2).
Proof.
  intros. generalize (andb_prop _ _ H). t. split. auto. clear H0.
  replace ((fix map (l:list(parser t)) : list rexp := 
            match l with | nil => nil | a::t => parser2rexp a :: map t end) ps) with
  (List.map (@parser2rexp t) ps) in H1 ; auto. clear H.
  generalize (ckzeros_corr _ _ H1). intros. split ; intros ; intro ; subst.
  contradiction H. exists (s1 ++ s2). eapply opt_and_r_corr. econstructor.
  eapply opt_cat_r_corr. econstructor. eapply in_alts.  eauto.
  eapply star_any_all. eauto. eapply opt_cat_r_corr. econstructor.
  eapply parse2rexp_corr1. eauto. eapply (star_any_all nil). 
  rewrite <- app_nil_end. auto.
  contradiction H. exists (s1 ++ s2). eapply opt_and_r_corr. econstructor.
  eapply opt_cat_r_corr. econstructor. eapply in_alts. eauto.
  eapply (star_any_all nil). rewrite <- app_nil_end. eauto. 
  eapply opt_cat_r_corr. econstructor. eapply parse2rexp_corr1. eauto. 
  eapply (star_any_all s2). auto.
Qed.

Lemma in_alts_map2 t1 t2 (ps:list (parser t1)) (p2:parser t2) s v :
  in_parser (alts (List.map (fun p1 => Cat_p p1 p2) ps)) s v -> 
  in_parser (Cat_p (alts ps) p2) s v.
Proof.
  induction ps ; simpl ; unfold never ; intros ; repeat pinv.
  econstructor. econstructor. eauto. eauto. auto. auto.
  specialize (IHps _ _ _ H). repeat pinv. econstructor. eapply Alt_right_pi. 
  eauto. eauto. eauto. auto.
Qed.

(** More abstraction stuff to keep Coq from unwininding the definition 
    of [check_all_p]. *)
Module Type ABSTRACT_CHECK_ALL_P_SIG.
  Parameter abstract_check_all_p : nat -> forall t : result, list (parser t) -> bool.
  Parameter abstract_check_all_p_eq : 
    abstract_check_all_p = check_all_p'.
End ABSTRACT_CHECK_ALL_P_SIG.

Module ABSTRACT_CHECK_ALL_P : ABSTRACT_CHECK_ALL_P_SIG.
  Definition abstract_check_all_p := check_all_p'.
  Definition abstract_check_all_p_eq := eq_refl check_all_p'.
End ABSTRACT_CHECK_ALL_P.

Import ABSTRACT_CHECK_ALL_P.

(** Make the [check_all_p] for the instructions used in the parser abstract. *)
Lemma abstract_check_all_p_instructions : 
  abstract_check_all_p 3 
  (List.map (fun p : parser instruction_t => prefix_parser_nooverride $ p)
    instr_parsers_nosize_pre ++
    List.map (fun p : parser instruction_t => prefix_parser_opsize $ p)
    instr_parsers_opsize_pre) = true.
Proof.
  generalize all_instructions_check.
  unfold instruction_parser_list.
  rewrite <- abstract_check_all_p_eq.
  auto.
Qed.

(** This lemma tells us that if we build a parser from two prefixes
    and two lists of parsers, such that the prefixes are star-free,
    and the parsers have been checked to be deterministic, and the
    concatenation of the prefixes on the parsers don't have any strings
    in common in their domain, then the resulting mongo parser 
    is deterministic and furthermore, when [s] and [v] are in its
    denotation, then there is no prefix of [s] in the denotation. *)
Lemma parser_determ' t1 t2 m (pfx1 pfx2:parser t1) (ps1 ps2 :list (parser t2)) : 
  star_free pfx1 = true -> 
  star_free pfx2 = true -> 
  check_determ_ps ps1 = true -> 
  check_determ_ps ps2 = true -> 
  abstract_check_all_p m ((List.map (fun p => pfx1 $ p) ps1) ++ 
                 (List.map (fun p => pfx2 $ p) ps2)) = true -> 
  check_all_pfx pfx1 ps1 = true -> 
  check_all_pfx pfx2 ps2 = true -> 
  forall s s1 s2 v1 v2,
    in_parser (alts ((List.map (fun p => pfx1 $ p) ps1) ++ 
      (List.map (fun p => pfx2 $ p) ps2))) s v1 -> 
    s = s1 ++ s2 ->
    in_parser (alts ((List.map (fun p => pfx1 $ p) ps1) ++ 
      (List.map (fun p => pfx2 $ p) ps2))) s1 v2 -> s2 = nil /\ v1 = v2.
Proof.
  intros. rewrite abstract_check_all_p_eq in H3.
  generalize (check_all_p'_corr _ _ H3 H6) (check_all_p'_corr _ _ H3 H8). t. 

  assert (x = x2 /\ x3 = x0 /\ x4 = x1).
  remember ((List.map (fun p => pfx1 $ p) ps1) ++ (List.map (fun p => pfx2 $ p)) ps2) as
  ps. 
  generalize H9 H10 ; clear H9 H10. generalize H13 H11 ; clear H13 H11.
  generalize H14 H12 ; clear H14 H12. rewrite H7 in *. clear H7 s.
  generalize ps x2 x3 x4 x x0 x1. clear Heqps. induction ps0. intros.
  generalize (nil_is_nil_app_nil _ _ H9). t. subst. congruence.
  intros. 
  destruct x5 ; destruct x8 ; simpl in *; 
    injection H9 ; clear H9 ; injection H10 ; clear H10 ;
  intros ; subst. subst. auto. assert False. clear IHps0. subst.
  contradiction H12. exists s2. exists v1. eapply Alt_left_pi ; auto. 
  contradiction. assert False ; clear IHps0 ; subst. contradiction H12.
  exists s2. exists v1. eapply in_alts_comm'.  apply Alt_left_pi. auto.
  contradiction. subst. assert (x8 = x5 /\ x6 = x9 /\ x7 = x10).
  eapply IHps0 ; clear IHps0 ; auto. intro. contradiction H14. t.
  exists x11. exists x12. eapply Alt_right_pi ; auto.
  intro ; t. eapply H12. exists x11 ; exists x12 ; eapply Alt_right_pi ; auto.
  t. subst. auto.

  t. subst. clear H3 H6 H9 H8. 
  assert (exists p, 
    (x0 = (pfx1 $ p) /\ check_pfx pfx1 p = true /\ check_determ p = true) \/ 
    (x0 = (pfx2 $ p) /\ check_pfx pfx2 p = true /\ check_determ p = true)).
  generalize ps1 H1 H4 ps2 H2 H5 x2 x0 x1 H10.
  clear ps1 H1 H4 ps2 H2 H5 x2 x0 x1 H10 H11 H12 H14 H13.
  induction ps1 ; simpl. intros _ _. induction ps2 ; simpl ; t.
  contradiction (app_cons_not_nil _ _ _ H10). generalize (andb_prop _ _ H2) ; 
  generalize (andb_prop _ _ H5) ; clear H2 H5 ; t. 
  specialize (IHps2 H3 H4) ; clear H4 H3. destruct x2 ; simpl in * ; 
  injection H10 ; clear H10 ; intros. subst. eauto. subst.
  eapply IHps2. eauto. t. generalize (andb_prop _ _ H1) ; generalize (andb_prop _ _ H4);
  clear H1 H4 ; t. specialize (IHps1 H4 H6 _ H2 H5). clear H4 H6 H2 H5.
  destruct x2 ; simpl in * ; injection H10 ; clear H10 ; t ; subst. eauto.
  eapply IHps1. eauto.

  t. destruct H3 ; t ; subst. 
  eapply check_pfx_determ'. eapply H. eapply H7. eauto. eauto. eauto. eauto.
  eapply check_pfx_determ'. eapply H0. eapply H7. eauto. eauto. eauto. eauto.
Qed.

Lemma check_determ_ps_app : forall t (ps1 ps2:list (parser t)), 
  check_determ_ps (ps1 ++ ps2) = true -> 
  check_determ_ps ps1 = true /\ check_determ_ps ps2 = true.
Proof.
  induction ps1. simpl. auto. simpl. intros. 
  generalize (andb_prop _ _ H). t. generalize (IHps1 _ H1). t. auto.
Qed.

(** A key lemma:  This tells us that the [instruction_parser] is deterministic --
    i.e., associates at most one value with a given string.  Furthermore, it tells
    us that if the [instruction_parser] accepts a string [s], then there is no
    prefix of [s] that is accepted.  This is crucial for showing that a shortest-
    match strategy (used by both the DFA and the derivative-based parserin the
    semantics) is complete. *)
Lemma parser_determ : 
  forall s v1, 
    in_parser instruction_parser s v1 -> 
    forall s1 s2 v2, 
      s = s1 ++ s2 -> in_parser instruction_parser s1 v2 -> 
      s2 = nil /\ v1 = v2.
Proof.
  unfold instruction_parser. unfold instruction_parser_list.
  generalize (check_determ_ps_app _ _ all_parsers_determ). t.
  generalize (andb_prop _ _ check_all_prefixed_instructions). t.
  intros. subst.
  eapply (@parser_determ' prefix_t instruction_t 3 prefix_parser_nooverride 
          prefix_parser_opsize _ _
          star_free_prefix_parser_nooverride
          star_free_prefix_parser_opsize
          H3 H abstract_check_all_p_instructions H4 H5). 
  eauto. eauto. eauto.
Qed.

(** Now I want to relate the [simple_parser] to the results above.
    Note that both the DFA and the simpler parser assume that at
    least one byte is consumed.  So we have to establish that indeed,
    the parsers require at least one byte on all paths.  While I'm
    at it, I calculate the maximum number of bits on any path (but
    haven't bothered to prove it correct.) *)
Require Import Arith.Compare_dec.

Definition max(n1 n2:nat) : nat := if le_lt_dec n1 n2 then n2 else n1.
Definition min(n1 n2:nat) : nat := if le_lt_dec n1 n2 then n1 else n2.

(** Maximum number of bits consumed by a parser.  Undefined if the
    parser includes [Star_p]. *)
Fixpoint max_bit_count t (p:parser t) : option nat := 
  match p with 
    | Eps_p => Some 0
    | Zero_p _ => Some 0
    | Char_p _ => Some 1
    | Any_p => Some 1
    | Cat_p _ _ p1 p2 => 
      match max_bit_count p1, max_bit_count p2 with
        | Some n1, Some n2 => Some (n1 + n2)
        | _,_ => None
      end
    | Map_p _ _ _ p => max_bit_count p
    | Alt_p _ p1 p2 => 
      match max_bit_count p1, max_bit_count p2 with
        | Some n1, Some n2 => Some (max n1 n2)
        | _,_ => None
      end
    | Star_p _ _ => None
  end%nat.

Lemma max_count_corr : forall t (p: parser t) s v,
  in_parser p s v -> 
  match max_bit_count p with 
    | None => True
    | Some n => length s <= n
  end%nat.
Proof.
  Local Open Scope nat_scope.
  induction 1 ; simpl ; intros ; repeat pinv ; subst ; simpl ; try omega ; unfold max ;
    repeat 
      match goal with 
        | [ |- context[max_bit_count ?p] ] => destruct (max_bit_count p)
        | [ |- context[le_lt_dec ?n1 ?n2] ] => destruct (le_lt_dec n1 n2)
      end ; try omega; auto; try (rewrite app_length; omega).
Qed.

Eval vm_compute in (max_bit_count instruction_parser).

Lemma max_instruction_bits: 
  max_bit_count instruction_parser = Some 104.
Proof.
  vm_compute; auto.
Qed.

(** Minimum number of bits consumed by the parser.  This is undefined
    when the parser is [Zero_p].  Or rather, we use [None] to represent
    "minimum infinity" to get this to work out properly. *)
Fixpoint min_bit_count t (p:parser t) : option nat := 
  match p with 
    | Eps_p => Some 0
    | Zero_p _ => None
    | Char_p _ => Some 1
    | Any_p => Some 1
    | Cat_p _ _ p1 p2 => 
      match min_bit_count p1, min_bit_count p2 with
        | Some n1, Some n2 => Some (n1 + n2)
        | _,_ => None
      end
    | Map_p _ _ _ p => min_bit_count p
    | Alt_p _ p1 p2 => 
      match min_bit_count p1, min_bit_count p2 with
        | Some n1, Some n2 => Some (min n1 n2)
        | Some n1, None => Some n1
        | None, Some n1 => Some n1
        | _, _ => None
      end
    | Star_p _ _ => Some 0
  end%nat.

(** If [s] is in the domain of [p], then [length s] is at least [min_bit_count p]. *)
Lemma min_count_corr : forall t (p:parser t) s v,
  in_parser p s v -> 
  match min_bit_count p with 
    | None => False
    | Some n => length s >= n
  end%nat.
Proof.
  Local Open Scope nat_scope.
  induction 1 ; simpl ; intros ; repeat pinv ; subst ; simpl ; try omega ; unfold min ;
    repeat 
      match goal with 
        | [ |- context[min_bit_count ?p] ] => destruct (min_bit_count p)
        | [ |- context[le_lt_dec ?n1 ?n2] ] => destruct (le_lt_dec n1 n2)
      end ; try omega.
  rewrite app_length. omega.
Qed.

(** The [instruction_parser] always consumes at least 8 bits.  *)
Lemma min_instruction_bits : 
  min_bit_count instruction_parser = Some 8.
Proof.
  vm_compute ; auto.
Qed.

(** Probably goes in the Parser file.  In fact, this whole file would be
    much simpler if I could just calculate derivatives directly on parsers,
    instead of having to convert them to regexps.  *)
Lemma in_derivs_app t (x1 x2:list char_p) (c:ctxt_t) (r:regexp t) (v:result_m t): 
  wf_regexp c r -> 
  in_regexp c (deriv_parse' (deriv_parse' r x1) x2) nil v -> 
  in_regexp c r (x1 ++ x2) v.
Proof.
  induction x1. simpl. intros. eapply Deriv'1. auto. auto.
  intros. simpl. eapply Deriv2. auto. eapply IHx1. eapply wf_deriv. eauto.
  eauto.
Qed.  

(** If [apply_null] on [derivs p cs] is [nil], then there's no value associated
   with [cs] in the denotation of [p]. *)
Lemma apply_null_nil : 
  forall (c:ctxt_t) t (p:parser t) (r:regexp t) cs,
    c = snd (parser2regexp p) ->
    r = deriv_parse' (fst (parser2regexp p)) cs ->
    forall (H:wf_regexp c r),
    apply_null c r H = nil -> 
    forall v, ~ in_parser p cs v.
Proof.
  intros c t p r cs H1 H2. rewrite H1. rewrite H2. intros. intro.
  assert (in_regexp (snd (parser2regexp p)) (fst (parser2regexp p)) cs v).
  apply p2r_ok. auto.
  assert (in_regexp (snd (parser2regexp p)) (deriv_parse' (fst (parser2regexp p)) cs) nil
    v).
  eapply Deriv'2. eapply p2r_wf. auto. generalize (ApplyNull1 H H5 (eq_refl _)).
  rewrite H0. auto.
Qed.

(** Goes in Parser.v *)
Lemma deriv_parse'_app : 
  forall t (cs1 cs2:list char_p) (r:regexp t) ,
    deriv_parse' r (cs1 ++ cs2) = deriv_parse' (deriv_parse' r cs1) cs2.
Proof.
  induction cs1 ; simpl ; auto. 
Qed.

(** Awkwardness reasoning with dependent types.  Again, this would be
    much simpler if we didn't have to factor things through the translation
    of regexps (as then we wouldn't need the well-formedness proofs around.) *)
Lemma apply_null_app cs1 cs2 t (r:regexp t) (c:ctxt_t) (H:wf_regexp c r) :
  apply_null c (deriv_parse' r (cs1 ++ cs2)) (wf_derivs c (cs1 ++ cs2) 
    r H) = 
  apply_null c (deriv_parse' (deriv_parse' r cs1) cs2)
    (wf_derivs c cs2 (deriv_parse' r cs1) (wf_derivs c cs1 r H)).
Proof.
  induction cs1. simpl. intros. assert (wf_derivs c cs2 r H = 
  wf_derivs c cs2 r (wf_derivs c nil r H)). apply Coqlib.proof_irrelevance.
  rewrite H0. auto. simpl. intros. 
  specialize (IHcs1 cs2 t (deriv r a) c (wf_deriv c r a H)).
  assert (wf_derivs c (a :: cs1 ++ cs2) r H = 
    wf_derivs c (cs1 ++ cs2) (deriv r a) (wf_deriv c r a H)).
  apply Coqlib.proof_irrelevance. rewrite H0.
  assert (wf_derivs c (a::cs1) r H = wf_derivs c cs1 (deriv r a) (wf_deriv c r a H)).
  apply Coqlib.proof_irrelevance. rewrite H1. auto.
Qed.

(** A surprisingly tricky little lemma used below. *)
Lemma foo_app A (x s1 s2 s3:list A) (v:A) : 
  x ++ v ::nil = s1 ++ s2 -> 
  s2 = s3 ++ v::nil -> 
  x = s1 ++ s3.
Proof.
  induction x ; simpl. destruct s1. simpl. intros. subst.
  destruct s3. auto. simpl in H0. injection H0 ; t.
  generalize (nil_is_nil_app_nil _ _ H) ; t ; subst. congruence.
  simpl; intros ; injection H. intros. clear H. subst.
  destruct s1 ; destruct s3 ; simpl in *; try congruence.
  intros. subst. destruct s1. simpl in *. destruct s3 ; 
  simpl in *. injection H. intros ; subst. clear H.
  destruct x ; simpl in * ; try congruence. injection H ; 
  intros ; subst. clear H. specialize (IHx _ _ nil _ H0 (eq_refl _)).
  subst. rewrite <- app_nil_end. auto. simpl. simpl in H.
  injection H ; intros ; subst ; clear H. generalize (IHx _ _ s3 _ H0 (eq_refl _)).
  intros. subst. auto.
Qed.

(** This lemma establishes a relationship between a parser [p] and the
    execution of the [simple_parse'] loop.  In particular, if we are
    in the loop processing [derivs p bytes1] and trying to process [bytes2],
    and we've already shown that there is no string [s1] that is a prefix of
    [bytes1] such that [apply_null] succeeds on [derivs p s1], then if we
    run [simple_parse'] on bytes2, then:
    (a) if it returns [None], then there is no prefix of [bytes1 ++ bytes2]
    accepted by [p].
    (b) if it returns [Some(n,bytes3)], then there is some prefix of [bytes2],
    say [bytes4], such that [apply_null] returns a value when we calculate
    [derivs p (bytes1 ++ bytes4)].  Furthermore, there is no smaller string
    than [bytes4] that has this property. 

    This proof is really, really ugly and the whole thing needs to be
    re-thought and refactored to make this at all maintainable.  But hey,
    it works.  
*)
Lemma simple_parse'_corr2 : 
  forall p bytes2 ps bytes1,
  inst_ctxt ps = (snd (parser2regexp p)) -> 
  inst_regexp ps = 
    deriv_parse' (fst (parser2regexp p)) (flat_map byte_explode bytes1) -> 
  (forall s1 s2, 
    bytes1 = s1 ++ s2 -> 
    apply_null (snd (parser2regexp p))
      (deriv_parse' (fst (parser2regexp p)) (flat_map byte_explode s1))
      (wf_derivs (snd (parser2regexp p)) (flat_map byte_explode s1) 
        (fst (parser2regexp p)) (p2r_wf p initial_ctxt)) = nil) ->
  match simple_parse' ps bytes2 with 
  | None => 
    forall s1 s2 v, 
      s1 ++ s2 = bytes1 ++ bytes2 -> 
      ~ in_parser p (flat_map byte_explode s1) v
  | Some (v,bytes3) => 
    exists bytes4,
      bytes2 = bytes4 ++ bytes3 /\ 
      in_parser p (flat_map byte_explode (bytes1 ++ bytes4)) v /\
      (forall bytes5 bytes6,
        bytes2 = bytes5 ++ bytes6 -> 
        length bytes5 < length bytes4 -> 
        forall v, ~ in_parser p (flat_map byte_explode (bytes1 ++ bytes5)) v)
  end.
Proof.
  Opaque byte_explode.
  induction bytes2 ; intros. simpl. intros. rewrite <- app_nil_end in H2.
  specialize (H1 _ _ (eq_sym H2)). destruct ps ; simpl in * ; subst. 
  clear inst_regexp_wf0. intro. 
  assert (in_regexp (snd (parser2regexp p)) 
           (deriv_parse' (fst (parser2regexp p))(flat_map byte_explode s1)) nil v).
  eapply Deriv'2.  eapply p2r_wf. eapply p2r_ok. auto.
  generalize
  (@ApplyNull1 (snd (parser2regexp p)) 
    (pair_t prefix_t instruction_t) (deriv_parse' (fst (parser2regexp p)) (flat_map byte_explode s1)) nil v
    (wf_derivs (snd (parser2regexp p)) (flat_map byte_explode s1) (fst (parser2regexp p))
      (p2r_wf p initial_ctxt)) H0 (eq_refl _)). rewrite H1. simpl. auto.

  simpl.
  remember (apply_null (inst_ctxt ps)
    (deriv_parse' (inst_regexp ps) (byte_explode a))
    (wf_derivs (inst_ctxt ps) (byte_explode a) (inst_regexp ps) (inst_regexp_wf ps))).
  destruct l.
  specialize (IHbytes2 (mkPS (inst_ctxt ps) (deriv_parse' (inst_regexp ps) 
    (byte_explode a)) (wf_derivs (inst_ctxt ps) (byte_explode a) 
      (inst_regexp ps) (inst_regexp_wf ps)))). simpl in IHbytes2.
  specialize (IHbytes2 (bytes1 ++ a::nil) H).
  assert (deriv_parse' (inst_regexp ps) (byte_explode a) =
             deriv_parse' (fst (parser2regexp p))
               (flat_map byte_explode (bytes1 ++ a :: nil))).
  rewrite H0. rewrite flat_map_app. simpl.
  generalize (flat_map byte_explode bytes1) (fst (parser2regexp p)).
  induction l ; simpl ; auto. specialize (IHbytes2 H2) ; clear H2.

  assert (forall s1 s2,
    bytes1 ++ a :: nil = s1 ++ s2 -> 
     apply_null (snd (parser2regexp p))
                (deriv_parse' (fst (parser2regexp p))
                   (flat_map byte_explode s1))
                (wf_derivs (snd (parser2regexp p)) 
                   (flat_map byte_explode s1) (fst (parser2regexp p))
                   (p2r_wf p initial_ctxt)) = nil). clear IHbytes2.
  destruct ps ; simpl in *. subst.  
  assert (inst_regexp_wf0 =  
           wf_derivs (snd (parser2regexp p)) (flat_map byte_explode bytes1)
            (fst (parser2regexp p)) (p2r_wf p initial_ctxt)).
  apply Coqlib.proof_irrelevance. subst. clear bytes2. 
  intros.
  assert ((s1 = bytes1 ++ (a::nil) /\ s2 = nil) \/ 
          (exists b1, exists b2, s1 = b1 /\ s2 = b2 ++ a::nil)).
  clear H1 Heql. generalize s2 bytes1 H ; clear s2 bytes1 H. 
  induction s1 ; simpl. intros. right. exists nil. eauto.
  intros. destruct bytes1 ; simpl in * ; injection H ; clear H ; t ; subst.
  generalize (nil_is_nil_app_nil _ _ H). t ; subst. left ; auto.
  specialize (IHs1 _ _ H). destruct IHs1. t. subst. left ; auto. t. 
  rewrite H0. rewrite H1. right. exists (a0 :: x). exists x0. auto.
  destruct H0 ; t. subst. rewrite flat_map_app. simpl in *. 
  rewrite <- app_nil_end. rewrite apply_null_app. auto. 
  specialize (H1 x x0). rewrite <- H0 in H1.
  specialize (H1 (foo_app bytes1 s1 x0 a H H2)). auto.

  specialize (IHbytes2 H2).  
  match goal with [ H : match ?e with | Some _ => _ | None => _ end |- _ ] => 
    destruct e end. destruct p0. t. subst. exists (a::x). split. auto.
  rewrite <- app_assoc in H4. simpl in H4. split. auto.
  intros. destruct bytes5. simpl in *. rewrite <- app_nil_end.
  eapply (apply_null_nil H H0 (inst_regexp_wf ps)). 
  specialize (H1 bytes1 nil). rewrite <- app_nil_end in H1. 
  specialize (H1 (eq_refl _)). destruct ps. simpl in *. subst.
  assert (inst_regexp_wf0 = wf_derivs (snd (parser2regexp p)) (flat_map byte_explode
    bytes1) (fst (parser2regexp p)) (p2r_wf p initial_ctxt)).
  apply Coqlib.proof_irrelevance. rewrite H. apply H1.

  simpl in H3. injection H3 ; intros ; subst. clear H3. simpl in H6.
  specialize (H5 bytes5 bytes6 H7). rewrite <- app_assoc in H5. simpl in H5.
  eapply H5. omega. rewrite <- app_assoc in IHbytes2. simpl in
  IHbytes2. eauto.
  exists (a::nil). simpl. split. auto. split.
  assert (In r (apply_null (inst_ctxt ps)  
           (deriv_parse' (inst_regexp ps) (byte_explode a))
           (wf_derivs (inst_ctxt ps) (byte_explode a) 
              (inst_regexp ps) (inst_regexp_wf ps)))). rewrite <- Heql. left ; auto.
  generalize (ApplyNull2 _ _ _ _ H2). clear H2 Heql.
  rewrite H. rewrite H0. intros. eapply (r2p_ok _ initial_ctxt). unfold
  parser2regexp in H2. rewrite flat_map_app. simpl. rewrite <- app_nil_end.
  eapply in_derivs_app. eapply p2r_wf. auto. intros.
  assert (bytes5 = nil). destruct bytes5 ; auto ; simpl in *; assert False. omega.
  contradiction. rewrite H4. rewrite <- app_nil_end. 
  eapply (apply_null_nil H H0 (inst_regexp_wf ps)). destruct ps ; simpl in * ; 
  subst. clear IHbytes2. specialize (H1 bytes1 nil). rewrite <- app_nil_end in H1.
  specialize (H1 (eq_refl _)). 
  assert (wf_derivs (snd (parser2regexp p)) (flat_map byte_explode bytes1)
            (fst (parser2regexp p)) (p2r_wf p initial_ctxt) = inst_regexp_wf0).
  apply Coqlib.proof_irrelevance. rewrite <- H. auto.
Qed.

(** If the [min_bit_count] of [p] is greater than 0, then there's no 
    way that [apply_null] will succeed. *)
Lemma min_count_not_null : 
  forall n t (p:parser t),
    min_bit_count p = Some (S n) -> 
    apply_null (snd (parser2regexp p)) (fst (parser2regexp p)) 
    (p2r_wf p initial_ctxt) = nil.
Proof.
  intros.
  generalize (@ApplyNull2  (snd (parser2regexp p)) _ (fst (parser2regexp p))
  (p2r_wf _ _)). destruct (apply_null (snd (parser2regexp p)) (fst (parser2regexp p))
  (p2r_wf p initial_ctxt)). auto. intros. specialize (H0 r). assert (In r (r::l)).
  left ; auto. specialize (H0 H1). assert (in_parser p nil r). eapply r2p_ok. eauto. 
  generalize (min_count_corr H2).  rewrite H. simpl. intros. assert False. omega.
  contradiction.
Qed.

(** Finally, the connection that directly ties execution of the DFA for
    the [non_cflow] parser to the [simple_parse] above.  This says that
    if we build the DFA, and run [dfa_recognize] on [bytes] and it 
    returns [Some (n,nats2)], then if we run [simple_parse] on [bytes],
    we'll consume the same number of bytes and get a prefix and instruction
    that satisfy [non_cflow_instr]. *)
Lemma non_cflow_dfa_corr : 
  forall (d:DFA), 
    (* I want to use [make_dfa] here but alas, Coq tries to evaluate it at the Qed,
       even when I immediately rewrite it to use abstract_build_dfa. *)
    abstract_build_dfa 256 nat2bools 400 (par2rec non_cflow_parser) = Some d -> 
    forall (bytes:list int8) (n:nat) (nats2:list nat),
      dfa_recognize 256 d (List.map byte2token bytes) = Some (n, nats2) -> 
      exists bytes1, exists pfx:prefix, exists ins:instr, 
        simple_parse bytes = Some ((pfx,ins), List.map nat_to_byte nats2) /\
        non_cflow_instr pfx ins = true /\
        n = length bytes1 /\ 
        bytes = bytes1 ++ (List.map nat_to_byte nats2).
Proof.
  intros d H bytes n nats2 H1. 
  generalize (@non_cflow_dfa_corr1 d H bytes n nats2 H1). intros ; t.
  exists x. exists x0. exists x1. repeat split ; auto.
  unfold simple_parse. unfold initial_parser_state. unfold instruction_regexp_pair.
  rewrite H4.
  remember {|inst_ctxt := snd (parser2regexp instruction_parser) ; 
             inst_regexp := fst (parser2regexp instruction_parser);
             inst_regexp_wf := p2r_wf instruction_parser initial_ctxt |} as ps.
  generalize (@simple_parse'_corr2 instruction_parser (x ++ List.map nat_to_byte nats2) ps nil).
  rewrite Heqps.
  Opaque instruction_parser.
  simpl. intros. specialize (H7 (eq_refl _) (eq_refl _)).
  assert (forall s1 s2, nil = s1 ++ s2 -> 
    apply_null (snd (parser2regexp instruction_parser))
          (deriv_parse' (fst (parser2regexp instruction_parser))
             (flat_map byte_explode s1))
          (wf_derivs (snd (parser2regexp instruction_parser))
             (flat_map byte_explode s1)
             (fst (parser2regexp instruction_parser))
             (p2r_wf instruction_parser initial_ctxt)) = nil).
  intros. clear H7. 
  generalize (nil_is_nil_app_nil _ _ H8) ; t. subst.
  generalize (min_count_not_null _ min_instruction_bits). 
  generalize instruction_parser. clear H0 H1 H2 H5 H6 H H8. simpl. 
  intro. generalize (apply_null (snd (parser2regexp p)) (fst (parser2regexp p))).
  assert (wf_derivs (snd (parser2regexp p)) nil (fst (parser2regexp p))
    (p2r_wf p initial_ctxt) = p2r_wf p initial_ctxt). 
  apply Coqlib.proof_irrelevance. 
  generalize H. clear H. unfold parser2regexp.
  generalize (p2r_wf p initial_ctxt). intros. rewrite <- H in H0. auto.
  specialize (H7 H8). clear H8. rewrite <- Heqps in *. 
  destruct (simple_parse' ps (x ++ List.map nat_to_byte nats2)). 
  destruct p. 
  t. destruct p. 
  assert (length x >= length x2).
  assert (length x < length x2 -> False). intro.
  eapply (H9 x (List.map nat_to_byte nats2) (eq_refl _) H10). eauto. omega.
  clear Heqps ps. remember (List.map nat_to_byte nats2). clear Heql0.

  assert (exists s2, x = x2 ++ s2). generalize x x2 H10 H7.
  induction x3 ; intro x4 ; destruct x4 ; simpl. intros. exists nil. auto.
  intro. assert False. omega. contradiction. intros. subst.
  eauto. intros. injection H12 ; clear H12 ; t ; subst. 
  assert (length x3 >= length x4). omega. specialize (IHx3 _ H3 H12).
  t. subst. eauto. t. subst. rewrite app_ass in H7.
  generalize (app_inv_head _ _ _ H7). intros. subst.
  rewrite flat_map_app in H2.
  generalize (parser_determ H2). intros. 
  specialize (H3 _ _ (p,i) (eq_refl _) H8). destruct H3.
  injection H4. intros. assert (x3 = nil). generalize x3 H3.
  induction x4. auto. simpl. intros. 
  generalize (nil_is_nil_app_nil _ _ (eq_sym H13)). t. 
  Transparent byte_explode.
  unfold byte_explode in H14. congruence. subst. auto.
  Opaque byte_explode.
  subst. assert False ; try contradiction. 
  specialize (H7 x (List.map nat_to_byte nats2) (x0,x1) (eq_refl _)). apply H7.
  auto.
Qed.

Lemma byte_explode_len: forall x, length (byte_explode x) = 8.
  Transparent byte_explode. auto. Opaque byte_explode.
Qed.

Lemma byte_explode_mult_len: forall l, length (flat_map byte_explode l) = length l * 8.
Proof.
  induction l.
  simpl. auto.
  simpl. rewrite app_length. rewrite byte_explode_len. omega.
Qed.


Lemma non_cflow_dfa_length : 
  forall (d:DFA), 
    (* Need to use abstract_build_dfa for the same reason as above I believe *)
    abstract_build_dfa 256 nat2bools 400 (par2rec non_cflow_parser) = Some d -> 
    forall (bytes:list int8) (n:nat) (nats2:list nat),
      dfa_recognize 256 d (List.map byte2token bytes) = Some (n, nats2) -> 
        (n <= 15). 
Proof.
  intros. apply non_cflow_dfa_corr in H0; auto.
  destruct H0; destruct H0; destruct H0; destruct H0.
  unfold simple_parse in *.
  specialize (simple_parse'_corr2) with (p := instruction_parser) (ps := initial_parser_state) 
      (bytes2 := bytes)
      (bytes1 := @nil int8); intros.
  rewrite H0 in H2.
  unfold initial_parser_state in *. unfold instruction_regexp_pair in *.
  remember {|inst_ctxt := snd (parser2regexp instruction_parser) ; 
             inst_regexp := fst (parser2regexp instruction_parser);
             inst_regexp_wf := p2r_wf instruction_parser initial_ctxt |} as ps.
  Opaque instruction_parser.
  destruct H2.
  rewrite Heqps; simpl. apply eq_refl. 
  rewrite Heqps; simpl. apply eq_refl.
  intros.  
  generalize (nil_is_nil_app_nil _ _ H2) ; t. subst.
  generalize (min_count_not_null _ min_instruction_bits). 
  generalize instruction_parser. (* clear H0 H1 H2 H5 H6 H H8. *) simpl. 
  intro. generalize (apply_null (snd (parser2regexp p)) (fst (parser2regexp p))).
  assert (wf_derivs (snd (parser2regexp p)) nil (fst (parser2regexp p))
    (p2r_wf p initial_ctxt) = p2r_wf p initial_ctxt). 
  apply Coqlib.proof_irrelevance. 
  generalize H3.  unfold parser2regexp.
  generalize (p2r_wf p initial_ctxt). intros. rewrite <-H4 in H5. auto.
  destruct H1. destruct H3. destruct H2.
  assert (x = x2). rewrite H4 in H2. apply app_inv_tail in H2.
    auto.
    inv H6.
  destruct H5.
  simpl in H2.
  specialize max_instruction_bits; intros.
  apply max_count_corr in H2.
  rewrite H5 in H2.
  rewrite byte_explode_mult_len in H2.
  omega.
Qed.


(*********************************************************)
(** Now to do correctness of the direct control flow DFA *)
(*********************************************************)

(** Show that the instruction we get out of the [dir_cflow] parsers satisfies
    the [dir_cflow_instr] predicate. *)
Lemma dir_cflow_instr_inv (ins:instr) (s:list char_p) : 
  in_parser (alts dir_cflow) s ins -> 
  dir_cflow_instr (mkPrefix None None false false) ins = true.
Proof.
  unfold dir_cflow. simpl ; 
  unfold dir_near_JMP_p, dir_near_Jcc_p, dir_near_CALL_p, never.
  intros. (repeat pinv) ; simpl ; unfold no_prefix ; simpl ; auto ; destruct x ; auto.
Qed.

(** Show that the [dir_cflow] parsers are sub-parsers of the [instruction_parser]. *)
Lemma dir_cflow_parser_subset : 
  forall s v, in_parser (alts dir_cflow) s v -> 
    in_parser instruction_parser s (mkPrefix None None false false, v).
Proof.
  intros. replace s with (nil ++ s) ; auto. 
  remember (mkPrefix None None false false) as p.
  assert (in_parser prefix_parser_nooverride nil p). 
  unfold prefix_parser_nooverride. unfold option_perm2. subst.
  repeat econstructor. clear Heqp. unfold dir_cflow in H. simpl in H.
  Transparent instruction_parser.
  unfold instruction_parser. unfold instruction_parser_list. 
  Opaque instruction_parser. eapply in_alts_app. left. eapply in_map_alts.
  econstructor ; eauto. clear H0. repeat pinv ; unfold instr_parsers_nosize_pre ; simpl.
  repeat 
  match goal with 
    | [ |- in_parser (JMP_p |+| _) _ _ ] => eapply Alt_left_pi
    | [ |- in_parser (_ |+| _) _ _ ] => eapply Alt_right_pi
  end.
  unfold dir_near_JMP_p, JMP_p in *. pinv. destruct H.
  eapply Alt_left_pi. auto. eapply Alt_right_pi. eapply Alt_left_pi. auto.
  repeat 
  match goal with 
    | [ |- in_parser (Jcc_p |+| _) _ _ ] => eapply Alt_left_pi
    | [ |- in_parser (_ |+| _) _ _ ] => eapply Alt_right_pi
  end.
  unfold dir_near_Jcc_p, Jcc_p in *. auto.
  repeat 
  match goal with 
    | [ |- in_parser (CALL_p |+| _) _ _ ] => eapply Alt_left_pi
    | [ |- in_parser (_ |+| _) _ _ ] => eapply Alt_right_pi
  end.
  unfold dir_near_CALL_p, CALL_p in *. eapply Alt_left_pi. auto.
  unfold never in *. pinv.
Qed.

(* FIX:  this is exactly the same proof as for [non_cflow_dfa_corr1] 
   except that we use [alts dir_cflow] instead of the non-control-flow
   parser, we use [dir_cflow_instr] instead of the non-control-flow
   predicate, and we use [dir_cflow_parser_subset] instead of the
   non-control-flow one. *)
Lemma dir_cflow_dfa_corr1 : 
  forall (d:DFA),
    abstract_build_dfa 256 nat2bools 400 (par2rec (alts dir_cflow)) = Some d -> 
    forall (bytes:list int8) (n:nat) (nats2:list nat),
      dfa_recognize 256 d (List.map byte2token bytes) = Some (n,nats2) -> 
      exists bytes1, exists pfx:prefix, exists ins:instr, 
        in_parser (alts dir_cflow) (flat_map byte_explode bytes1) ins /\ 
        in_parser instruction_parser (flat_map byte_explode bytes1) (pfx,ins) /\ 
        n = length bytes1 /\ 
        bytes = bytes1 ++ (List.map nat_to_byte nats2) /\ 
        dir_cflow_instr pfx ins = true /\
        (forall ts3 ts4,
          (length ts3 < length bytes1)%nat -> 
          bytes = ts3 ++ ts4 -> 
          forall v0, ~ in_parser (alts dir_cflow) (flat_map byte_explode ts3) v0).
Proof.
  intros. subst. rewrite build_dfa_eq in H.
  generalize (dfa_recognize_corr _ _ _ _ H (List.map byte2token bytes)
    (bytesLt256 _)). clear H. rewrite H0. clear H0. mysimp. 
  exists (List.map nat_to_byte x). exists (mkPrefix None None false false).
  rename x0 into i. exists i. assert (List.map nat_to_byte (x ++ nats2) = bytes).
  rewrite <- H. apply n2bs. rewrite map_app in H3. rewrite <- H3.
  rewrite map_length. generalize (dir_cflow_instr_inv H1).
  assert (list_all (fun n => n < 256)%nat (x ++ nats2)).
  rewrite <- H. apply (bytesLt256 bytes). generalize (list_all_app _ _ _ H4).
  intros. destruct H5.
  assert (flat_map byte_explode (List.map nat_to_byte x) = flat_map nat2bools x).
  apply explode_bits ; auto. rewrite H8. mysimp.
  apply dir_cflow_parser_subset. auto. intros.
  specialize (H2 (List.map byte2token ts3) (List.map byte2token ts4)).
  repeat rewrite map_length in H2. specialize (H2 H9).
  rewrite <- map_app in H10. rewrite <- H in H10.
  rewrite <- map_app in H2. rewrite <- H10 in H2. rewrite n2bs in H2. 
  specialize (H2 (eq_refl _)). intro. specialize (H2 v0). apply H2.
  assert (flat_map nat2bools (List.map byte2token ts3) = flat_map byte_explode ts3).
  rewrite <- explode_bits. rewrite n2bs. auto. apply (bytesLt256 ts3).
  rewrite <- H12 in H11.  auto.
Qed.

(* FIX: this is exactly the same proof as for the non-control-flow DFA
   except that well, we use [alts dir_cflow] and [dir_cflow_dfa_corr1].
   So we should be able to abstract over these but I'm too lazy to do
   this right now. *)
Lemma dir_cflow_dfa_corr : 
  forall (d:DFA),
    abstract_build_dfa 256 nat2bools 400 (par2rec (alts dir_cflow)) = Some d -> 
    forall (bytes:list int8) (n:nat) (nats2:list nat),
      dfa_recognize 256 d (List.map byte2token bytes) = Some (n, nats2) -> 
      exists bytes1, exists pfx:prefix, exists ins:instr,
        simple_parse bytes = Some ((pfx,ins), List.map nat_to_byte nats2) /\
        dir_cflow_instr pfx ins = true /\
        n = length bytes1 /\ 
        bytes = bytes1 ++ (List.map nat_to_byte nats2).
Proof.
  intros d H bytes n nats2 H1.
  generalize (@dir_cflow_dfa_corr1 d H bytes n nats2 H1). intros ; t.
  exists x. exists x0. exists x1. repeat split ; auto.
  unfold simple_parse. unfold initial_parser_state. unfold instruction_regexp_pair.
  rewrite H4.
  remember {|inst_ctxt := snd (parser2regexp instruction_parser) ; 
             inst_regexp := fst (parser2regexp instruction_parser);
             inst_regexp_wf := p2r_wf instruction_parser initial_ctxt |} as ps.
  generalize (@simple_parse'_corr2 instruction_parser (x ++ List.map nat_to_byte nats2) ps nil).
  rewrite Heqps.
  Opaque instruction_parser.
  simpl. intros. specialize (H7 (eq_refl _) (eq_refl _)).
  assert (forall s1 s2, nil = s1 ++ s2 -> 
    apply_null (snd (parser2regexp instruction_parser))
          (deriv_parse' (fst (parser2regexp instruction_parser))
             (flat_map byte_explode s1))
          (wf_derivs (snd (parser2regexp instruction_parser))
             (flat_map byte_explode s1)
             (fst (parser2regexp instruction_parser))
             (p2r_wf instruction_parser initial_ctxt)) = nil).
  intros. clear H7. 
  generalize (nil_is_nil_app_nil _ _ H8) ; t. subst.
  generalize (min_count_not_null _ min_instruction_bits). 
  generalize instruction_parser. clear H0 H1 H2 H5 H6 H H8. simpl. 
  intro. generalize (apply_null (snd (parser2regexp p)) (fst (parser2regexp p))).
  assert (wf_derivs (snd (parser2regexp p)) nil (fst (parser2regexp p))
    (p2r_wf p initial_ctxt) = p2r_wf p initial_ctxt). 
  apply Coqlib.proof_irrelevance. 
  generalize H. clear H. unfold parser2regexp.
  generalize (p2r_wf p initial_ctxt). intros. rewrite <- H in H0. auto.
  specialize (H7 H8). clear H8. rewrite <- Heqps in *. 
  destruct (simple_parse' ps (x ++ List.map nat_to_byte nats2)). 
  destruct p. 
  t. destruct p. 
  assert (length x >= length x2).
  assert (length x < length x2 -> False). intro.
  eapply (H9 x (List.map nat_to_byte nats2) (eq_refl _) H10). eauto. omega.
  clear Heqps ps. remember (List.map nat_to_byte nats2). clear Heql0.

  assert (exists s2, x = x2 ++ s2). generalize x x2 H10 H7.
  induction x3 ; intro x4 ; destruct x4 ; simpl. intros. exists nil. auto.
  intro. assert False. omega. contradiction. intros. subst.
  eauto. intros. injection H12 ; clear H12 ; t ; subst. 
  assert (length x3 >= length x4). omega. specialize (IHx3 _ H3 H12).
  t. subst. eauto. t. subst. rewrite app_ass in H7.
  generalize (app_inv_head _ _ _ H7). intros. subst.
  rewrite flat_map_app in H2.
  generalize (parser_determ H2). intros. 
  specialize (H3 _ _ (p,i) (eq_refl _) H8). destruct H3.
  injection H4. intros. assert (x3 = nil). generalize x3 H3.
  induction x4. auto. simpl. intros. 
  generalize (nil_is_nil_app_nil _ _ (eq_sym H13)). t. 
  Transparent byte_explode.
  unfold byte_explode in H14. congruence. subst. auto.
  Opaque byte_explode.
  subst. assert False ; try contradiction. 
  specialize (H7 x (List.map nat_to_byte nats2) (x0,x1) (eq_refl _)). apply H7.
  auto.
Qed.

(* This is really the same as the above proof about non_cflow_dfa... but 
   since a bunch of the other proof here need to be refactored at some point,
   I'm not terribly worried. *)

Lemma dir_cflow_dfa_length : 
  forall (d:DFA), 
    (* Need to use abstract_build_dfa for the same reason as above I believe *)
    abstract_build_dfa 256 nat2bools 400 (par2rec (alts dir_cflow)) = Some d -> 
    forall (bytes:list int8) (n:nat) (nats2:list nat),
      dfa_recognize 256 d (List.map byte2token bytes) = Some (n, nats2) -> 
        (n <= 15). 
Proof.
  intros. apply dir_cflow_dfa_corr in H0; auto.
  destruct H0; destruct H0; destruct H0; destruct H0.
  unfold simple_parse in *.
  specialize (simple_parse'_corr2) with (p := instruction_parser) (ps := initial_parser_state) 
      (bytes2 := bytes)
      (bytes1 := @nil int8); intros.
  rewrite H0 in H2.
  unfold initial_parser_state in *. unfold instruction_regexp_pair in *.
  remember {|inst_ctxt := snd (parser2regexp instruction_parser) ; 
             inst_regexp := fst (parser2regexp instruction_parser);
             inst_regexp_wf := p2r_wf instruction_parser initial_ctxt |} as ps.
  Opaque instruction_parser.
  destruct H2.
  rewrite Heqps; simpl. apply eq_refl. 
  rewrite Heqps; simpl. apply eq_refl.
  intros.  
  generalize (nil_is_nil_app_nil _ _ H2) ; t. subst.
  generalize (min_count_not_null _ min_instruction_bits). 
  generalize instruction_parser. (* clear H0 H1 H2 H5 H6 H H8. *) simpl. 
  intro. generalize (apply_null (snd (parser2regexp p)) (fst (parser2regexp p))).
  assert (wf_derivs (snd (parser2regexp p)) nil (fst (parser2regexp p))
    (p2r_wf p initial_ctxt) = p2r_wf p initial_ctxt). 
  apply Coqlib.proof_irrelevance. 
  generalize H3.  unfold parser2regexp.
  generalize (p2r_wf p initial_ctxt). intros. rewrite <-H4 in H5. auto.
  destruct H1. destruct H3. destruct H2.
  assert (x = x2). rewrite H4 in H2. apply app_inv_tail in H2.
    auto.
    inv H6.
  destruct H5.
  simpl in H2.
  specialize max_instruction_bits; intros.
  apply max_count_corr in H2.
  rewrite H5 in H2.
  rewrite byte_explode_mult_len in H2.
  omega.
Qed.
