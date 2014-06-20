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
Import ParserArg.X86_PARSER_ARG.
Import X86_PARSER.
(* Import X86_BASE_PARSER. *)
Import X86Syntax.
Hint Constructors in_grammar.

Ltac t := repeat
  match goal with 
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : exists _, _ |- _ ] => destruct H
    | [ |- forall _, _ ] => intros
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => 
      generalize (inj_pairT2 _ _ _ _ _ H) ; clear H ; intros ; subst
  end.

(** Generic simplification tactic. *)
Ltac mysimp := 
  simpl in * ; intros ; 
    repeat 
      match goal with 
        | [ |- context[char_dec ?x ?y] ] => destruct (char_dec x y) ; auto 
        | [ |- _ /\ _ ] => split
        | [ H : context[type_dec ?e1 ?e2] |- _ ] => 
          destruct (type_dec e1 e2) ; simpl in * ; try discriminate
        | [ H : existT ?f ?t ?x = existT ?f ?t ?y |- _ ] => 
          generalize (inj_pairT2 _ f t x y H) ; clear H ; intro H ; subst
        | [ H : _ /\ _ |- _ ] => destruct H
        | [ |- context[ _ ++ nil ] ] => rewrite <- app_nil_end
        | [ H : exists x, _ |- _ ] => destruct H
        | [ H : _ \/ _ |- _] => destruct H
        | [ H : _ <-> _ |- _] => destruct H
        | [ |- _ <-> _ ] => split
        | [ H : _::_ = _::_ |- _] => injection H ; clear H
        | _ => idtac
      end ; auto.

Lemma inv_alt : forall t (p1 p2:grammar t) cs v, in_grammar (alt p1 p2) cs v -> 
  in_grammar p1 cs v \/ in_grammar p2 cs v.                                                
Proof.
  unfold alt. intros. generalize (inv_Map H). intro. destruct H0 as [v' [H0 H1]].
  generalize (inv_Alt H0). intros. destruct H2. destruct H2 as [v1 [H2 H3]]. 
  left. rewrite H1. rewrite H3. auto. destruct H2 as [v1 [H2 H3]]. right.
  rewrite H1. rewrite H3. auto.
Qed.

Lemma inv_never : forall t cs v, in_grammar (never t) cs v -> False.
Proof.
  unfold never. intros. apply (inv_Zero H).
Qed.

Lemma in_alt_r : forall t (p1 p2:grammar t) cs v, in_grammar p2 cs v -> 
                        in_grammar (alt p1 p2) cs v.
Proof.
  intros. econstructor ; eauto.
Qed.
Hint Resolve in_alt_r.

Lemma in_alt_l : forall t (p1 p2:grammar t) cs v, in_grammar p1 cs v -> 
                                                  in_grammar (alt p1 p2) cs v.
Proof.
  intros ; econstructor ; eauto.
Qed.
Hint Resolve in_alt_l.
   
(** A tactic to apply the inversion principles for the parser denotational semantis. *)
Ltac pinv := 
  match goal with
    | [ H : in_grammar (alt _ _) _ _ |- _ ] => generalize (inv_alt H) ; clear H
    | [ H : in_grammar Eps _ _ |- _ ] => generalize (inv_Eps H) ; clear H
    | [ H : in_grammar Any _ _ |- _ ] => generalize (inv_Any H) ; clear H
    | [ H : in_grammar (Char _) _ _ |- _ ] => generalize (inv_Char H) ; clear H
    | [ H : in_grammar (Alt _ _) _ _ |- _ ] => generalize (inv_Alt H) ; clear H
    | [ H : in_grammar (seq _ _) _ _ |- _ ] => generalize (inv_Cat H) ; clear H
    | [ H : in_grammar (Cat _ _) _ _ |- _ ] => generalize (inv_Cat H) ; clear H
    | [ H : in_grammar (never _) _ _ |- _ ] => contradiction (inv_never H)
    | [ H : in_grammar (Zero _) _ _ |- _ ] => contradiction (inv_Zero H)
    | [ H : in_grammar (_ @ _) _ _ |- _ ] => generalize (inv_Map H) ; clear H
    | [ H : in_grammar (Map _ _ _) _ _ |- _ ] => generalize (inv_Map H) ; clear H
    (* | [ H : in_grammar (Xform _ _) _ _ |- _ ] => generalize (XformInv H) ; clear H *)
    | [ H : _::_ = _::_ |- _] => injection H ; clear H
    | [ H : true = true |- _ ] => clear H
    | [ H : true = _ |- _ ] => generalize (eq_sym H) ; clear H ; intro H
    | [ H : ?e1 && ?e2 = true |- _ ] => 
      let x1 := fresh "x" in let x2 := fresh "y" in 
        remember e1 as x1 ; remember e2 as x2 ; 
          destruct x1 ; destruct x2 ; simpl in H ; try congruence
    | [ H : ?x = ?x -> _ |- _ ] => specialize (H (eq_refl x))
    | [ H : _ \/ _ |- _ ] => destruct H
    | [ IH : forall _ _ _ _, in_grammar ?p1 _ _ -> in_grammar ?p2 _ _ -> _, 
      H1 : in_grammar ?p1 _ _, H2 : in_grammar ?p2 _ _ |- _ ] => 
    specialize (IH _ _ _ _ H1 H2)
  end ; t ; subst.

Lemma in_alts0_simp : 
  forall t (ps: list (grammar t)) s v, 
    in_grammar (alts0 ps) s v <-> in_grammar (List.fold_right (@alt t) (@never t) ps) s v.
Proof. 
  induction ps ; simpl ; intros. tauto. destruct ps. simpl.
  split. intro. econstructor. econstructor. eauto. eauto. auto.
  intro ; repeat pinv ; auto. 
  split ; intro. pinv. pinv. eauto. eapply in_alt_r. eapply IHps. auto.
  pinv. pinv. eauto. eapply in_alt_r. eapply IHps. auto.
Qed.

Lemma half_app : forall A (xs ys zs a b: list A), 
  half xs ys zs = (a,b) -> 
  (forall x, (In x xs \/ In x ys \/ In x zs) <-> (In x a) \/ (In x b)).
Proof.
  induction xs. simpl. intros. injection H. intros ; subst. tauto.
  simpl. intros. specialize (IHxs _ _ _ _ H x). simpl in *. tauto.
Qed. 

Lemma in_simp_alts t (ps:list (grammar t)) cs v : 
  in_grammar (List.fold_right (@alt t) (@never t) ps) cs v <-> 
  exists p, In p ps /\ in_grammar p cs v.
Proof.
  induction ps. simpl. intros ; split ; intro. pinv. destruct H as [_ [H _]]. contradiction.
  simpl. intros. split. intro ; repeat pinv. exists a. auto.
  specialize (IHps cs v). destruct IHps. specialize (H0 H). clear H1 H. 
  destruct H0 as [p [H0 H]]. eauto. intro. mysimp ; subst. eauto.
  eapply in_alt_r. specialize (IHps cs v). destruct IHps. eauto.
Qed.

Lemma in_alts' n t (ps:list (grammar t)) cs v : 
  in_grammar (alts' n ps) cs v <-> 
  in_grammar (List.fold_right (@alt t) (@never t) ps) cs v.
Proof.
  induction n. apply in_alts0_simp.
  destruct ps. simpl. tauto. destruct ps. simpl.
  intros. split ; eauto. intros ; repeat pinv ; auto. intros.
  simpl. remember (half ps (g::nil) (g0::nil)) as p. destruct p as [ps1 ps2].
  generalize (IHn _ ps1 cs v) (IHn _ ps2 cs v). intros.
  generalize (half_app _ _ _ (eq_sym Heqp)). intros.
  split. intro. repeat pinv. destruct H as [H _]. specialize (H H2). clear H0 H2.
  assert (exists p, In p ps1 /\ in_grammar p cs v). apply in_simp_alts ; auto.
  destruct H0 as [p [H0 H2]]. specialize (H1 p). destruct H1 as [_ H1].
  specialize (H1 (or_introl H0)). 
  repeat pinv. eapply in_alt_r. eapply in_alt_r. eapply in_simp_alts. eauto.
  simpl in *. repeat pinv ; try contradiction ; eauto.
  simpl in * ; repeat pinv ; try contradiction ; eauto.
  destruct H0 as [H0 _]. specialize (H0 H2). clear H H2.
  assert (exists p, In p ps2 /\ in_grammar p cs v). apply in_simp_alts. auto.
  destruct H as [p [H H2]]. specialize (H1 p). destruct H1 as [_ H1].
  specialize (H1 (or_intror H)). 
  repeat pinv. eapply in_alt_r. eapply in_alt_r. eapply in_simp_alts ; eauto.
  simpl in *. repeat pinv ; try contradiction ; eauto.
  simpl in * ; repeat pinv ; try contradiction ; eauto.
  intro. repeat pinv. assert (In g ps1 \/ In g ps2). apply H1. 
  right. left ; auto. simpl. auto. clear H1. destruct H3.
  apply in_alt_l. apply H. apply in_simp_alts. exists g. auto.
  apply in_alt_r. apply H0. apply in_simp_alts. exists g ; auto.
  assert (In g0 ps1 \/ In g0 ps2). apply H1. right. right ; simpl ; auto.
  clear H1. destruct H3. apply in_alt_l. apply H. apply in_simp_alts. eauto.
  apply in_alt_r. apply H0. apply in_simp_alts. eauto.
  generalize (in_simp_alts ps cs v). intros. destruct H3 as [H3 _].
  specialize (H3 H2). destruct H3. destruct H3. assert (In x ps1 \/ In x ps2).
  apply H1. auto. destruct H5. eapply in_alt_l. apply H. apply in_simp_alts ; eauto.
  eapply in_alt_r. apply H0. eapply in_simp_alts ; eauto.
Qed.

Lemma in_alts t (ps:list (grammar t)) cs v : 
  in_grammar (alts ps) cs v <-> in_grammar (List.fold_right (@alt t) (@never t) ps) cs v.
Proof.
  intros. apply in_alts'.
Qed.

Lemma in_alts_app : forall t (ps qs:list (grammar t)) s v,
  in_grammar (alts ps) s v \/ in_grammar (alts qs) s v ->
  in_grammar (alts (ps ++ qs)) s v.
Proof.
  intros. rewrite in_alts in *. rewrite in_alts in H.
  induction ps ; simpl in *; repeat pinv ; auto.
Qed.

Lemma app_cons_nil A (x:A) (ys:list A) (y:A) (zs:list A) : 
  x::nil = ys ++ y :: zs -> ys = nil.
Proof.
  destruct ys. auto. induction ys. simpl. intros. discriminate H.
  simpl in *. intros. specialize (IHys y zs). discriminate H.
Qed.

(** These next few lemmas are used to invert grammars so that we can
    figure out what kinds of values they build. *)
Lemma in_app_alts : forall t (ps1 ps2:list (grammar t)) s v,
  in_grammar (alts (ps1 ++ ps2)) s v -> 
  in_grammar (alts ps1) s v \/ in_grammar (alts ps2) s v.
Proof.
  intros. rewrite in_alts in *. rewrite in_alts. generalize ps2 s v H ; clear ps2 s v H.
  induction ps1 ; simpl ; intros. right. auto. repeat pinv. left. econstructor ; eauto.
  specialize (IHps1 _ _ _ H). pinv. left. eauto. right. eauto.
Qed.

Lemma in_alts_map : forall t1 t2 (p1:grammar t1) (ps:list (grammar t2)) s v,
  in_grammar (alts (List.map (fun p2 => Cat p1 p2) ps)) s v -> 
  in_grammar (Cat p1 (alts ps)) s v.
Proof.
  induction ps ; simpl ; intros ; rewrite in_alts in * ; simpl in * ; repeat pinv.
  econstructor. eauto. rewrite in_alts. simpl. econstructor. eauto. auto. auto. auto.
  specialize (IHps s v). rewrite in_alts in IHps. specialize (IHps H).
  pinv. econstructor. eauto. rewrite in_alts ; simpl. eapply in_alt_r.
  rewrite in_alts in H1. eauto. eauto. auto. 
Qed.

Lemma inv_bitsleft bs t (p:grammar t) s v : 
  in_grammar (bs $$ p) s v -> 
  exists s1, exists s2, s = s1 ++ s2 /\ in_grammar p s2 v.
Proof.
  unfold bitsleft. induction bs ; simpl ; intros ; repeat pinv ; simpl.
  exists nil. exists x1. auto.
  exists ((if ascii_dec a "0" then false else true)::x4).
  exists x1. split ; auto. 
Qed.

Lemma inv_modrm : forall s p,
  in_grammar modrm s p -> 
  match p with | (_, Imm_op _) => False | (Reg_op r, op) => True | _ => False end.
Proof.
  unfold modrm. unfold modrm_gen. simpl. intros.
  repeat pinv ; auto. unfold rm00, bitsleft, reg_op, reg in * ;
  repeat pinv ; auto ; simpl ; auto. 
  unfold rm01, bitsleft, reg_op, reg in *. repeat pinv ; simpl ; auto. 
  unfold rm10, bitsleft, reg_op, reg in *. repeat pinv ; simpl ; auto.
  unfold reg_op, bitsleft, reg in *. repeat pinv ; simpl ; auto.
Qed.

Lemma inv_ext_modrm : forall bs s v,
  in_grammar (ext_op_modrm bs) s v -> match v with | Imm_op _ => False | _ => True end.
Proof.
  unfold ext_op_modrm. unfold ext_op_modrm_gen. simpl. 
  intros. repeat pinv ; auto. 
Qed.

Lemma inv_ext_modrm2 : forall bs s v,
  in_grammar (ext_op_modrm2 bs) s v -> match v with | Imm_op _ => False | _ => True end.
Proof.
  unfold ext_op_modrm2. unfold ext_op_modrm2_gen ; simpl. intros. 
  repeat pinv ; auto. unfold bitsleft, reg_op in *. repeat pinv ; simpl ; auto.
Qed.

(** A tactic for applying these inversion properties on grammars to simplify
    them down to the cases we want to consider. *)
Ltac psimp := 
  simpl in * ;
  match goal with 
    | [ H : prod _ _ |- _ ] => destruct H
    | [ H : (_,_) = (_,_) |- _ ] => injection H ; clear H ; intros ; subst
    | [ H : in_grammar (_ $$ _) _ _ |- _ ] => 
      generalize (inv_bitsleft H) ; clear H ; t ; subst
    | [ H : in_grammar modrm _ _ |- _ ] => generalize (inv_modrm H) ; clear H ; t
    | [ H : in_grammar (ext_op_modrm ?bs) _ _ |- _ ] => 
      generalize (@inv_ext_modrm bs _ _ H) ; clear H ; t
    | [ H : in_grammar (ext_op_modrm2 ?bs) _ _ |- _ ] => 
      generalize (@inv_ext_modrm2 bs _ _ H) ; clear H ; t
  end.

(** Main connecton between non_cflow_dfa and semantics -- this is hopefully
    close enough to the actual grammar used in the semantics that proving
    a relationship is easy to do.  We will see... *)
Fixpoint simple_parse' (ps:ParseState_t) (bytes:list int8) : 
  option ((prefix * instr) * list int8) := 
  match bytes with 
    | nil => None
    | b::bs => match X86_PARSER.parse_byte ps b with 
                 | (ps',nil) => simple_parse' ps' bs
                 | (_, v::_) => Some (v,bs)
               end
  end.

Import X86_PARSER.ABSTRACT_INI_DECODER_STATE.
Definition simple_parse (bytes:list int8) : option ((prefix * instr) * list int8) := 
  simple_parse' abs_ini_decoder_state bytes.

(** This lemma shows that any instruction returned by the [non_cflow_grammar]
    satisfies the boolean predicate [non_cflow_instr].  We should probably
    break this up into a lot of little lemmas to make it a little easier
    to adapt. *)

Lemma valid_prefix_grammar_rep_non_cflow pre s : 
  in_grammar valid_prefix_grammar_rep s pre -> 
  rep_or_gs_or_op_prefix pre = true.
Proof.
  intros pre s. unfold valid_prefix_grammar_rep, option_perm3, rep_or_gs_or_op_prefix.
  intro. repeat pinv ; simpl ; auto. unfold rep_p, bitsleft in *. repeat pinv. auto.
  unfold gs_segment_override_p, bitsleft in H. repeat pinv. auto.
  unfold perm2, rep_p, gs_segment_override_p, bitsleft in H. repeat pinv ; auto.
  unfold perm2, rep_p, op_override_p, bitsleft in H. repeat pinv ; auto.
  unfold perm2, gs_segment_override_p, op_override_p, bitsleft in H. repeat pinv ; auto.
  unfold perm3, rep_p, gs_segment_override_p, op_override_p, bitsleft in H.
  repeat pinv ; auto. unfold perm2 in * ; repeat pinv ; auto.
  unfold perm2 in * ; repeat pinv ; auto. unfold perm2 in * ; repeat pinv ; auto.
Qed.                                  

Lemma valid_instr_grammars_rep_non_cflow pre ins s : 
  in_grammar (alts (List.map (fun p => valid_prefix_grammar_rep $ p)
                             valid_instr_grammars_rep)) s (pre, ins) -> 
  non_cflow_instr pre ins = true.
Proof.
  unfold valid_instr_grammars_rep. simpl. intros pre ins s.
  rewrite in_alts. simpl. intros. 
  repeat pinv ; injection H2 ; clear H2 ; intros ; subst ; 
  unfold MOVS_p, STOS_p in * ; unfold bitsleft in * ; repeat pinv ; simpl in * ; 
  eapply valid_prefix_grammar_rep_non_cflow ; eauto.
Qed.

Lemma valid_prefix_grammar_rep_or_repn_non_cflow pre s : 
  in_grammar valid_prefix_grammar_rep_or_repn s pre -> 
  rep_or_repn_or_gs_or_op_prefix pre = true.
Proof.
  unfold valid_prefix_grammar_rep_or_repn, rep_or_repn_or_gs_or_op_prefix, 
  option_perm3, rep_or_repn_p, gs_segment_override_p, op_override_p, bitsleft.
  intros. repeat pinv ; auto ; unfold perm3 in * ; repeat pinv ; auto ; 
          unfold perm2 in * ; repeat pinv ; auto.
Qed.

Lemma valid_instr_grammars_rep_or_repn_non_cflow pre ins s : 
  in_grammar (alts (List.map (fun p => valid_prefix_grammar_rep_or_repn $ p)
                             valid_instr_grammars_rep_or_repn)) s (pre, ins) -> 
  non_cflow_instr pre ins = true.
Proof.
  unfold valid_instr_grammars_rep_or_repn. unfold instr_grammars_rep_or_repn.
  simpl ; intros pre ins s. rewrite in_alts. simpl ; intros.
  unfold CMPS_p, SCAS_p, bitsleft in *. 
  repeat pinv ; injection H2 ; clear H2 ; intros ; subst ; simpl ; 
  eapply valid_prefix_grammar_rep_or_repn_non_cflow ; eauto.
Qed.

Lemma valid_prefix_grammar_lock_with_op_override_non_cflow pre s : 
  in_grammar valid_prefix_grammar_lock_with_op_override s pre -> 
  lock_or_gs_with_op pre = true.
Proof.
  unfold valid_prefix_grammar_lock_with_op_override.
  unfold option_perm3_variation, lock_p, gs_segment_override_p, op_override_p, 
  perm3, perm2. intros. repeat (repeat pinv ; repeat psimp) ; auto.
Qed.

Lemma valid_prefix_grammar_lock_no_op_override_non_cflow pre s : 
  in_grammar valid_prefix_grammar_lock_no_op_override s pre -> 
  lock_or_gs_without_op pre = true.
Proof.
  unfold valid_prefix_grammar_lock_no_op_override.
  unfold option_perm3_variation, option_perm2, 
  lock_p, gs_segment_override_p, op_override_p, 
  perm3, perm2. 
  intros. repeat (repeat pinv ; repeat psimp) ; unfold lock_or_gs_without_op ; auto.
Qed.

Lemma valid_instr_grammars_lock_with_op_override_non_cflow pre ins s : 
  in_grammar (alts (List.map (fun p => valid_prefix_grammar_lock_with_op_override $ p)
                             valid_instr_grammars_lock_with_op_override)) s (pre,ins) ->
  non_cflow_instr pre ins = true.
Proof.
  unfold valid_instr_grammars_lock_with_op_override.
  unfold instr_grammars_lock_with_op_override.
  simpl. intros pre ins s. rewrite in_alts. simpl ; intros.
  Ltac unf1 := 
  unfold ADD_p, ADC_p, AND_p, NEG_p, NOT_p, OR_p, SBB_p, SUB_p, XOR_p, XCHG_p,
    logic_or_arith_p in *.
  repeat pinv ; injection H2 ; clear H2 ; intros ; subst ; simpl ;
  unf1 ; repeat (repeat pinv ; repeat psimp) ; 
  repeat 
    (simpl ; 
     match goal with 
       | [ H : match ?x with | Imm_op _ => _ | Reg_op _ => _ | Address_op _ => _ | Offset_op _ => _ end |- _ ] => destruct x ; try contradiction
       | [ |- context[if ?x then _ else _]] => destruct x
       | [ H : in_grammar valid_prefix_grammar_lock_with_op_override _ _ |- _ ] => 
         rewrite (valid_prefix_grammar_lock_with_op_override_non_cflow H) ; auto
       | _ => idtac
  end).
Qed.

Lemma valid_instr_grammars_lock_no_op_override_non_cflow pre ins s : 
  in_grammar (alts (List.map (fun (p:grammar instruction_t) => 
                                valid_prefix_grammar_lock_no_op_override $ p)
                             valid_instr_grammars_lock_no_op_override)) s (pre,ins) ->
  non_cflow_instr pre ins = true.
Proof.
  unfold valid_instr_grammars_lock_no_op_override.
  unfold instr_grammars_lock_no_op_override.
  simpl ; intros pre ins s ; rewrite in_alts ; simpl ; intros.
  repeat pinv ; injection H2 ; clear H2 ; intros ; subst ; simpl ; 
  unfold ADD_p, ADC_p, AND_p, BTC_p, BTR_p, BTS_p, CMPXCHG_p, DEC_p, INC_p, NEG_p, 
  NOT_p, OR_p, SBB_p, SUB_p, XOR_p, XADD_p, XCHG_p, logic_or_arith_p, bit_test_p in * ; 
  repeat (repeat pinv ; repeat psimp) ; 
  repeat 
    (simpl ; 
     match goal with 
       | [ H : match ?x with | Imm_op _ => _ | Reg_op _ => _ | Address_op _ => _ | Offset_op _ => _ end |- _ ] => destruct x ; try contradiction
       | [ |- context[if ?x then _ else _]] => destruct x
       | [ H : in_grammar valid_prefix_grammar_lock_no_op_override _ _ |- _ ] => 
         rewrite (valid_prefix_grammar_lock_no_op_override_non_cflow H) ; auto
       | [ |- _ || true = true ] => apply orb_true_r 
       | _ => idtac
  end).
Qed.

Lemma valid_prefix_grammar_seg_with_op_override_non_cflow pre s : 
  in_grammar valid_prefix_grammar_seg_with_op_override s pre -> 
  only_seg_or_op pre = true.
Proof.
  unfold valid_prefix_grammar_seg_with_op_override.
  unfold option_perm2_variation, gs_segment_override_p, op_override_p, perm2.
  intros. repeat pinv ; repeat psimp ; unfold only_seg_or_op ; auto.
Qed.

Lemma valid_instr_grammars_seg_with_op_override_non_cflow pre ins s : 
  in_grammar (alts (List.map (fun (p:grammar instruction_t) => 
                                valid_prefix_grammar_seg_with_op_override $ p)
                             valid_instr_grammars_seg_with_op_override)) s (pre,ins) ->
  non_cflow_instr pre ins = true.
Proof.
  unfold valid_instr_grammars_seg_with_op_override.
  unfold instr_grammars_seg_with_op_override.
  simpl ; intros pre ins s ; rewrite in_alts ; simpl ; intros.
  repeat pinv ; injection H2 ; clear H2 ; intros ; subst ; simpl ; 
  unfold CMP_p, IMUL_p, MOV_p, TEST_p, logic_or_arith_p in * ; 
  repeat (repeat pinv ; repeat psimp) ;
  repeat 
    (simpl ; 
     match goal with 
       | [ H : match ?x with | Imm_op _ => _ | Reg_op _ => _ | Address_op _ => _ | Offset_op _ => _ end |- _ ] => destruct x ; try contradiction
       | [ |- context[if ?x then _ else _]] => destruct x
       | [ H : in_grammar  valid_prefix_grammar_seg_with_op_override _ _ |- _ ] => 
         rewrite (valid_prefix_grammar_seg_with_op_override_non_cflow H) ; auto
       | [ |- _ || true = true ] => apply orb_true_r 
       | _ => idtac
  end).
Qed.

Lemma valid_prefix_grammar_seg_op_override_non_cflow pre s : 
  in_grammar valid_prefix_grammar_seg_op_override s pre -> 
  only_seg_or_op pre = true.
Proof.
  unfold valid_prefix_grammar_seg_op_override, only_seg_or_op, option_perm2,
  perm2, gs_segment_override_p, op_override_p ; intros ;
  repeat (repeat pinv ; repeat psimp) ; auto.
Qed.

Lemma valid_instr_grammars_seg_op_override_non_cflow pre ins s : 
  in_grammar (alts (List.map
                      (fun p => valid_prefix_grammar_seg_op_override $ p)
                      valid_instr_grammars_seg_op_override)) s (pre, ins) ->
   non_cflow_instr pre ins = true.
Proof.
  unfold valid_instr_grammars_seg_op_override.
  unfold instr_grammars_seg_op_override.
  simpl ; intros pre ins s ; rewrite in_alts ; simpl ; intros.
  repeat pinv ; injection H2 ; clear H2 ; intros ; subst ; simpl ; 
  unfold CDQ_p, CMOVcc_p, CWDE_p, DIV_p, IDIV_p, MOVSX_p, MOVZX_p, MUL_p, 
  NOP_p, ROL_p, ROR_p, SAR_p, SHL_p, SHLD_p, SHR_p, SHRD_p, rotate_p, 
  shiftdouble_p, modrm_noreg, modrm_gen_noreg in * ; 
  repeat (repeat pinv ; repeat psimp) ;
  repeat match goal with 
    | [ H : match ?x with | Imm_op _ => _ | Reg_op _ => _ | Address_op _ => _ | Offset_op _ => _ end |- _ ] => destruct x ; try contradiction
    | [ |- context[if ?x then _ else _]] => destruct x
    | [ H : in_grammar _ _ _ |- _ ] => 
      rewrite (valid_prefix_grammar_seg_op_override_non_cflow H) ; auto
    | _ => idtac
  end.
Qed.

Lemma valid_prefix_grammar_seg_override_non_cflow pre s : 
  in_grammar valid_prefix_grammar_seg_override s pre -> 
  only_gs_seg_override pre = true.
Proof.
  unfold valid_prefix_grammar_seg_override. 
  unfold option_perm, gs_segment_override_p.
  intros. repeat pinv ; auto.
Qed.

Lemma only_gs_seg_override_imp_only_seg_or_op pre : 
  only_gs_seg_override pre = true -> 
  only_seg_or_op pre = true.
Proof.
  unfold only_gs_seg_override, only_seg_or_op. destruct pre.
  simpl. destruct lock_rep ; auto. destruct seg_override ; auto.
  destruct s ; auto. destruct op_override ; auto ; intros.
  discriminate H. destruct op_override ; auto. intros ; discriminate H.
Qed.

Lemma modrm_mx_inv_left x y z : 
  in_grammar modrm_mmx x (y,z) -> no_mmx_imm_op y = true.
Proof.
  unfold modrm_mmx. unfold modrm_gen, mmx_reg_op. intros. 
  repeat (repeat pinv ; repeat psimp ; auto).
Qed.

Lemma modrm_mx_inv_right x y z : 
  in_grammar modrm_mmx x (y,z) -> no_mmx_imm_op z = true.
Proof.
  unfold modrm_mmx. unfold modrm_gen, mmx_reg_op. intros. 
  repeat (repeat pinv ; repeat psimp ; auto).
Qed.

Lemma modrm_xmm_inv_left x y z : 
  in_grammar modrm_xmm x (y,z) -> no_sse_imm_op y = true.
Proof.
  unfold modrm_xmm. unfold modrm_gen, sse_reg_op. intros.
  repeat (repeat pinv ; repeat psimp ; auto).
Qed.

Lemma modrm_xmm_inv_right x y z : 
  in_grammar modrm_xmm x (y,z) -> no_sse_imm_op z = true.
Proof.
  unfold modrm_xmm. unfold modrm_gen, sse_reg_op. intros.
  repeat (repeat pinv ; repeat psimp ; auto).
Qed.

Lemma modrm_xmm_noreg_inv_left x s s0 : 
  in_grammar modrm_xmm_noreg x (s,s0) -> no_sse_imm_op s = true.
Proof.
  unfold modrm_xmm_noreg. unfold modrm_gen_noreg, sse_reg_op. intros.
  repeat (repeat pinv ; repeat psimp) ; auto.
Qed.

Lemma modrm_xmm_noreg_inv_right x s s0 : 
  in_grammar modrm_xmm_noreg x (s,s0) -> no_sse_imm_op s0 = true.
Proof.
  unfold modrm_xmm_noreg. unfold modrm_gen_noreg, sse_reg_op. intros.
  repeat (repeat pinv ; repeat psimp) ; auto.
Qed.

Lemma modrm_xmm_gp_noreg_inv x s s0 : 
  in_grammar modrm_xmm_gp_noreg x (s,s0) -> no_sse_imm_op s = true.
Proof.
  unfold modrm_xmm_gp_noreg. unfold modrm_gen_noreg. intros.
  repeat (repeat pinv ; repeat psimp) ; auto.
Qed.

Lemma modrm_mm_inv_left x s s0 : 
  in_grammar modrm_mm x (s,s0) -> no_sse_imm_op s = true.
Proof.
  unfold modrm_mm. unfold modrm_gen. intros.
  repeat (repeat pinv ; repeat psimp) ; auto.
Qed.

Lemma modrm_mm_inv_right x s s0 : 
  in_grammar modrm_mm x (s,s0) -> no_sse_imm_op s0 = true.
Proof.
  unfold modrm_mm. unfold modrm_gen. intros.
  repeat (repeat pinv ; repeat psimp) ; auto.
Qed.

Lemma modrm_mm_noreg_inv_left x s1 s2 : 
  in_grammar modrm_mm_noreg x (s1,s2) -> no_sse_imm_op s1 = true.
Proof.
  unfold modrm_mm_noreg. unfold modrm_gen_noreg. intros.
  repeat (repeat pinv ; repeat psimp) ; auto.
Qed.

Lemma modrm_mm_noreg_inv_right x s1 s2 : 
  in_grammar modrm_mm_noreg x (s1,s2) -> no_sse_imm_op s2 = true.
Proof.
  unfold modrm_mm_noreg. unfold modrm_gen_noreg. intros.
  repeat (repeat pinv ; repeat psimp) ; auto.
Qed.

Lemma valid_instr_grammars_seg_override_non_cflow pre ins s : 
  in_grammar (alts (List.map
                      (fun p => valid_prefix_grammar_seg_override $ p)
                      valid_instr_grammars_seg_override)) s (pre, ins) -> 
  non_cflow_instr pre ins = true.
Proof.
  unfold valid_instr_grammars_seg_override.
  simpl ; intros pre ins s ; rewrite in_alts ; simpl ; intros.
  Ltac unf2 := unfold AAA_p, AAD_p, AAM_p, AAS_p, CMP_p, BOUND_p, BSF_p, 
               BSR_p, BSWAP_p, BT_p, CLC_p, CLD_p, CLI_p, CLTS_p, CMC_p, 
               CPUID_p, DAA_p, DAS_p, HLT_p, IMUL_p, LAHF_p, LAR_p, LEA_p,
               LEAVE_p, LGS_p, MOV_p, MOVCR_p, MOVDR_p, MOVSR_p, MOVBE_p,
               POP_p, POPA_p, POPF_p, PUSH_p, PUSHSR_p, PUSHA_p, PUSHF_p,
               RCL_p, RCR_p, RDPMC_p, RDTSC_p, RDTSCP_p, SAHF_p, SETcc_p,
               SLDT_p, SMSW_p, STC_p, STD_p, STR_p, TEST_p, WBINVD_p, F2XM1_p,
               FABS_p, FADD_p, FADDP_p, FBLD_p, FBSTP_p, FCHS_p, FCMOVcc_p, 
               FCOM_p, FCOMP_p, FCOMPP_p, FCOMIP_p, FCOS_p, FDECSTP_p,
               FDIV_p, FDIVP_p, FDIVR_p, FDIVRP_p, FFREE_p, FIADD_p, FICOM_p, 
               FICOMP_p, FIDIV_p, FIDIVR_p, FILD_p, FIMUL_p, FINCSTP_p, 
               FIST_p, FISTP_p, FISUB_p, FISUBR_p, FLD_p, FLD1_p, FLDCW_p, 
               FLDENV_p, FLDL2E_p, FLDL2T_p, FLDLG2_p, FLDLN2_p, FLDPI_p, 
               FLDZ_p, FMUL_p, FMULP_p, FNCLEX_p, FNINIT_p, FNOP_p, FNSAVE_p, 
               FNSTCW_p, FNSTSW_p, FPATAN_p, FPREM_p, FPREM1_p, FPTAN_p, 
               FRNDINT_p, FRSTOR_p, FSCALE_p, FSIN_p, FSINCOS_p, FSQRT_p, 
               FST_p, FSTENV_p, FSTP_p, FSUB_p, FSUBP_p, FSUBR_p, FSUBRP_p,
               FTST_p, FUCOM_p, FUCOMP_p, FUCOMPP_p, FUCOMI_p, FUCOMIP_p, 
               FXAM_p, FXCH_p, FXTRACT_p, FYL2X_p, FYL2XP1_p, FWAIT_p, 
               EMMS_p, MOVD_p, MOVQ_p, PACKSSDW_p, PACKSSWB_p, PACKUSWB_p, 
               PADD_p, PADDS_p, PADDUS_p, PAND_p, PANDN_p, PCMPEQ_p, PCMPGT_p, 
               PMADDWD_p, PMULHUW_p, PMULHW_p, PMULLW_p, POR_p, PSLL_p, PSRA_p, 
               PSRL_p, PSUB_p, PSUBS_p, PSUBUS_p, PUNPCKH_p, PUNPCKL_p, PXOR_p, 
               ADDPS_p, ADDSS_p, ANDNPS_p, ANDPS_p, CMPPS_p, CMPSS_p, COMISS_p, 
               CVTPI2PS_p, CVTPS2PI_p, CVTSI2SS_p, CVTSS2SI_p, CVTTPS2PI_p, CVTTSS2SI_p,
               DIVPS_p, DIVSS_p, LDMXCSR_p, MAXPS_p, MAXSS_p, MINPS_p, MINSS_p, 
               MOVAPS_p, MOVHLPS_p, MOVLPS_p, MOVMSKPS_p, MOVSS_p, MOVUPS_p, MULPS_p,
               MULSS_p, ORPS_p, RCPPS_p, RCPSS_p, RSQRTPS_p, RSQRTSS_p, SHUFPS_p, 
               SQRTPS_p, SQRTSS_p, STMXCSR_p, SUBPS_p, SUBSS_p, UCOMISS_p, UNPCKHPS_p,
               UNPCKLPS_p, XORPS_p, PAVGB_p, PEXTRW_p, PINSRW_p, PMAXSW_p, PMAXUB_p, 
               PMINSW_p, PMINUB_p, PMOVMSKB_p, PSADBW_p, PSHUFW_p, MASKMOVQ_p,
               MOVNTPS_p, MOVNTQ_p, PREFETCHT0_p, PREFETCHT1_p, PREFETCHT2_p, 
               PREFETCHNTA_p, SFENCE_p,
               logic_or_arith_p, bit_test_p, rotate_p in *.
  Ltac m3 := 
  try (repeat (simpl ; repeat psimp ; repeat pinv ; 
    match goal with 
    | [ H : match ?x with | Imm_op _ => _ | Reg_op _ => _ | Address_op _ => _ | Offset_op _ => _ end |- _ ] => destruct x ; try contradiction
    | [ |- context[if ?x then _ else _]] => destruct x
    | [ |- context[only_seg_or_op _]] => 
      rewrite only_gs_seg_override_imp_only_seg_or_op ; auto
    | [ H : in_grammar _ _ _ |- _ ] => 
      rewrite (valid_prefix_grammar_seg_override_non_cflow H) ; auto
    | [ H : in_grammar modrm_mmx _ _ |- context[no_mmx_imm_op _]] => 
      rewrite (modrm_mx_inv_left H)
    | [ H : in_grammar modrm_mmx _ _ |- context[no_mmx_imm_op _]] => 
      rewrite (modrm_mx_inv_right H)
    | [ H : in_grammar modrm_xmm _ _ |- _ ] => 
      rewrite (modrm_xmm_inv_left H)
    | [ H : in_grammar modrm_xmm _ _ |- _ ] => 
      rewrite (modrm_xmm_inv_right H)
    | [ H : in_grammar modrm_xmm_noreg _ _ |- _ ] => 
      rewrite (modrm_xmm_noreg_inv_left H)
    | [ H : in_grammar modrm_xmm_noreg _ _ |- _ ] => 
      rewrite (modrm_xmm_noreg_inv_right H)
    | [ H : in_grammar modrm_xmm_gp_noreg _ _ |- _ ] => 
      rewrite (modrm_xmm_gp_noreg_inv H)
    | [ H : in_grammar modrm_mm _ _ |- _ ] => 
      rewrite (modrm_mm_inv_left H)
    | [ H : in_grammar modrm_mm _ _ |- _ ] => 
      rewrite (modrm_mm_inv_right H)
    | [ H : in_grammar modrm_mm_noreg _ _ |- _ ] => 
      rewrite (modrm_mm_noreg_inv_left H)
    | [ H : in_grammar modrm_mm_noreg _ _ |- _ ] => 
      rewrite (modrm_mm_noreg_inv_right H)
    | _ => idtac ; auto
  end)).
  Ltac m2 := 
    pinv ; pinv ; [ unf2 ; repeat pinv ; 
                    match goal with 
                      | [ H : (_,_) = (_,_) |- _ ] => 
                        injection H ; clear H ; intros ; subst
                    end ; m3 | idtac ].
  repeat m2.
  unfold modrm_gen_noreg, mmx_reg_op, mmx_reg in H1.  
  repeat (repeat pinv ; repeat psimp) ; auto.
  unfold modrm_gen_noreg, mmx_reg_op, mmx_reg in H1.
  repeat (repeat pinv ; repeat psimp) ; auto. 
  pinv.
Qed.

Lemma non_cflow_instr_inv (pre:prefix) (ins:instr) (s:list char_p) :
  in_grammar non_cflow_grammar s (pre,ins) -> 
  non_cflow_instr pre ins = true.
Proof.
    unfold non_cflow_grammar.  unfold non_cflow_grammar_list.
    intros. 
    Ltac iaa := 
      match goal with
        | [ H : in_grammar (alts (?A ++ ?B)) _ _ |- _ ] => 
          generalize (in_app_alts _ _ H) ; clear H ; 
          intro H ; destruct H ; [ idtac | iaa ]
        | _ => idtac
      end.
    iaa.
    eapply valid_instr_grammars_rep_non_cflow ; eauto.
    eapply valid_instr_grammars_rep_or_repn_non_cflow ; eauto.
    eapply valid_instr_grammars_lock_with_op_override_non_cflow ; eauto.
    eapply valid_instr_grammars_lock_no_op_override_non_cflow ; eauto.
    eapply valid_instr_grammars_seg_with_op_override_non_cflow ; eauto.
    eapply valid_instr_grammars_seg_op_override_non_cflow ; eauto.
    eapply valid_instr_grammars_seg_override_non_cflow ; eauto.
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
  Parser.list_all (fun t => (t < 256)%nat) (List.map byte2token bs).
Proof.
  induction bs ; auto ; simpl ; auto ; split ; auto. apply byteLt256. 
Qed.

Lemma in_map_alts t1 t2 (p1:grammar t1) (ps:list (grammar t2)) s v : 
  in_grammar (p1 $ (alts ps)) s v <->
  in_grammar (alts (List.map (fun p2 => p1 $ p2) ps)) s v .
Proof.
  intros. rewrite in_alts in *. split. intros. pinv. rewrite in_alts in H0.
  generalize x x0 x1 x2 H H0 ; clear x x0 x1 x2 H H0. 
  induction ps ; simpl in *; intros ; repeat pinv ; eauto. 
  induction ps ; simpl ; intros ; repeat pinv. econstructor ; eauto.
  rewrite in_alts. simpl. eauto. specialize (IHps H). pinv.
  econstructor ; eauto. rewrite in_alts in *. simpl. eauto.
Qed.

Lemma mem_parser_subset : 
  forall t (p:grammar t) (ps:list (grammar t)),
    In p ps -> 
    forall s v, in_grammar p s v -> in_grammar (alts ps) s v.
Proof.
  induction ps ; simpl. intros. contradiction. intros. 
  destruct H ; subst. rewrite in_alts. simpl ; eauto. 
  rewrite in_alts. simpl. eapply in_alt_r. rewrite <- in_alts. eauto.
Qed.

Lemma alts_subset : 
  forall t (ps qs:list (grammar t)), 
    (forall p, In p ps -> In p qs) -> 
    forall s v, in_grammar (alts ps) s v -> in_grammar (alts qs) s v.
Proof.
  induction ps. simpl. intros. rewrite in_alts in *. unfold never in *. simpl in *. 
  pinv. intros. rewrite in_alts in H0. 
  simpl in *. pinv. destruct H0. eapply mem_parser_subset. eapply (H a). auto. auto.
  apply IHps. intros. eapply H. right. auto. auto. rewrite in_alts ; auto.
Qed.

Lemma in_alts_exists t1 t2 (pre : grammar t1) s v (ps:list (grammar t2)) :
  in_grammar (alts (List.map (fun p => pre $ p ) ps)) s v -> 
  exists p, In p ps /\ in_grammar (pre $ p) s v.
Proof.
  intros. rewrite in_alts in H. generalize H ; clear H. 
  induction ps ; simpl ; intros ; repeat pinv. exists a. eauto.
  specialize (IHps H). destruct IHps as [p [H1 H2]].  eauto.
Qed.

Lemma alts_prefix_subset t1 t2 (pre1 pre2 : grammar t1) 
      (ps qs:list (grammar t2)) :
  (forall s v, in_grammar pre1 s v -> in_grammar pre2 s v) -> 
  (forall p, In p ps -> In p qs) -> 
  forall s v, in_grammar (alts (List.map (fun p => pre1 $ p) ps)) s v -> 
              in_grammar (alts ((List.map (fun p => pre2 $ p) qs))) s v.
Proof.
  intros.  eapply in_map_alts. generalize (in_alts_exists _ _ H1). intros.
  destruct H2 as [p [H2 H3]]. clear H1. assert (in_grammar (alts ((pre2 $ p)::nil)) s v).
  pinv. rewrite in_alts. simpl. eauto. clear H3. eapply in_map_alts.
  eapply alts_subset. Focus 2. eauto. simpl. intros. destruct H3 ; try contradiction.
  subst. specialize (H0 _ H2). clear H2. generalize qs H0 ; clear qs H0 H s v H1.
  induction qs ; simpl ; intros ; try contradiction. destruct H0. subst ; auto.
  specialize (IHqs H). auto.
Qed.

Lemma in_perm2_1 t1 t2 (p1 p1' : grammar t1) (p2 : grammar t2) s v : 
  (forall s v, in_grammar p1 s v -> in_grammar p1' s v) ->
  in_grammar (perm2 p1 p2) s v -> in_grammar (perm2 p1' p2) s v.
Proof.
  unfold perm2. intros. repeat pinv. eauto. eapply in_alt_r. 
  econstructor ; eauto.
Qed.

Lemma in_perm2_2 t1 t2 (p1: grammar t1) (p2 p2' : grammar t2) s v : 
  (forall s v, in_grammar p2 s v -> in_grammar p2' s v) ->
  in_grammar (perm2 p1 p2) s v -> in_grammar (perm2 p1 p2') s v.
Proof.
  unfold perm2. intros ; repeat pinv ; eauto. eapply in_alt_r.
  econstructor ; eauto.
Qed.

Lemma in_perm3_1 t1 t2 t3 (p1 p1':grammar t1) (p2:grammar t2) (p3 : grammar t3) s v : 
  (forall s v, in_grammar p1 s v -> in_grammar p1' s v) ->
  in_grammar (perm3 p1 p2 p3) s v -> in_grammar (perm3 p1' p2 p3) s v.
Proof.
  unfold perm3. intros ; repeat pinv ; eauto. eapply in_alt_r.
  eapply in_alt_l. econstructor ; eauto. econstructor ; eauto.
  eapply in_perm2_1 ; eauto. eauto. eapply in_alt_r. eapply in_alt_r.
  econstructor ; eauto. econstructor ; eauto. eapply in_perm2_1 ; eauto. eauto.
Qed.

Lemma in_perm3_2 t1 t2 t3 (p1:grammar t1) (p2 p2':grammar t2) (p3 : grammar t3) s v : 
 (forall s v, in_grammar p2 s v -> in_grammar p2' s v) ->
  in_grammar (perm3 p1 p2 p3) s v -> in_grammar (perm3 p1 p2' p3) s v.
Proof.
  unfold perm3. intros ; repeat pinv ; eauto. eapply in_alt_l. econstructor ; eauto.
  eapply in_perm2_1 ; eauto. eapply in_alt_r.
  eapply in_alt_l. econstructor ; eauto. 
  eapply in_alt_r. eapply in_alt_r.
  econstructor ; eauto. econstructor ; eauto. eapply in_perm2_2 ; eauto. eauto.
Qed.

Lemma in_perm3_3 t1 t2 t3 (p1:grammar t1) (p2:grammar t2) (p3 p3' : grammar t3) s v : 
 (forall s v, in_grammar p3 s v -> in_grammar p3' s v) ->
  in_grammar (perm3 p1 p2 p3) s v -> in_grammar (perm3 p1 p2 p3') s v.
Proof.
  unfold perm3. intros ; repeat pinv ; eauto. eapply in_alt_l. econstructor ; eauto.
  eapply in_perm2_2 ; eauto. eapply in_alt_r.
  eapply in_alt_l. econstructor ; eauto. econstructor ; eauto. eapply in_perm2_2 ; 
  eauto. eauto. eapply in_alt_r. eapply in_alt_r.
  econstructor ; eauto. 
Qed.

Lemma in_option_perm3_1 t1 t2 t3 (p1 p1':grammar (User_t t1)) (p2:grammar (User_t t2)) (p3 : grammar (User_t t3)) s v: 
  (forall s v, in_grammar p1 s v -> in_grammar p1' s v) -> 
  in_grammar (option_perm3 p1 p2 p3) s v -> 
  in_grammar (option_perm3 p1' p2 p3) s v.
Proof.
  unfold option_perm3. intros. repeat 
  match goal with 
    | [ H : in_grammar (_ |+| _) _ _ |- in_grammar (_ |+| _) _ _ ] => 
      pinv ; pinv ; [ eapply in_alt_l | eapply in_alt_r ]
    | _ => idtac
  end ; repeat pinv ; econstructor ; eauto. eapply in_perm2_1 ; eauto.
  eapply in_perm2_1 ; eauto. eapply in_perm3_1 ; eauto.
Qed.

Lemma in_option_perm3_2 t1 t2 t3 (p1:grammar (User_t t1)) (p2 p2':grammar (User_t t2)) (p3 : grammar (User_t t3)) s v: 
  (forall s v, in_grammar p2 s v -> in_grammar p2' s v) -> 
  in_grammar (option_perm3 p1 p2 p3) s v -> 
  in_grammar (option_perm3 p1 p2' p3) s v.
Proof.
  unfold option_perm3. intros. repeat 
  match goal with 
    | [ H : in_grammar (_ |+| _) _ _ |- in_grammar (_ |+| _) _ _ ] => 
      pinv ; pinv ; [ eapply in_alt_l | eapply in_alt_r ]
    | _ => idtac
  end ; repeat pinv ; econstructor ; eauto. eapply in_perm2_2 ; eauto.
  eapply in_perm2_1 ; eauto. eapply in_perm3_2 ; eauto.
Qed.

Lemma in_option_perm3_3 t1 t2 t3 (p1:grammar (User_t t1)) (p2:grammar (User_t t2)) (p3 p3': grammar (User_t t3)) s v: 
  (forall s v, in_grammar p3 s v -> in_grammar p3' s v) -> 
  in_grammar (option_perm3 p1 p2 p3) s v -> 
  in_grammar (option_perm3 p1 p2 p3') s v.
Proof.
  unfold option_perm3. intros. repeat 
  match goal with 
    | [ H : in_grammar (_ |+| _) _ _ |- in_grammar (_ |+| _) _ _ ] => 
      pinv ; pinv ; [ eapply in_alt_l | eapply in_alt_r ]
    | _ => idtac
  end ; repeat pinv ; econstructor ; eauto. eapply in_perm2_2 ; eauto.
  eapply in_perm2_2 ; eauto. eapply in_perm3_3 ; eauto.
Qed.

Lemma in_option_perm3_variation_2 t1 t2 t3 (p1:grammar (User_t t1)) (p2 p2':grammar (User_t t2)) (p3 : grammar (User_t t3)) s v : 
  (forall s v, in_grammar p2 s v -> in_grammar p2' s v) -> 
  in_grammar (option_perm3_variation p1 p2 p3) s v -> 
  in_grammar (option_perm3_variation p1 p2' p3) s v.
Proof.
  unfold option_perm3_variation. intros. 
  repeat match goal with 
    | [ H : in_grammar (_ |+| _) _ _ |- in_grammar (_ |+| _) _ _ ] => 
      pinv ; pinv ; [ eapply in_alt_l | eapply in_alt_r ]
    | _ => idtac
  end ; repeat pinv ; econstructor ; eauto. eapply in_perm2_1 ; eauto.
  eapply in_perm3_2 ; eauto.
Qed.                                           

Lemma gs_seg_imp_seg s v : in_grammar gs_segment_override_p s v -> 
                           in_grammar segment_override_p s v.
Proof.
  unfold gs_segment_override_p, segment_override_p. intros.
  pinv. simpl in x. unfold bitsleft in H. pinv. pinv.
  unfold bits in H. unfold bits in H0. simpl in *. 
  repeat pinv. simpl. repeat apply in_alt_r. unfold bitsleft, bits.
  simpl. repeat econstructor ; eauto.
Qed.

Lemma valid_prefix_grammar_rep_imp s v : 
  in_grammar valid_prefix_grammar_rep s v -> in_grammar prefix_grammar_rep s v.
Proof.
  unfold valid_prefix_grammar_rep, prefix_grammar_rep. intros. pinv.
  econstructor ; eauto. eapply in_option_perm3_2. Focus 2. eauto.
  apply gs_seg_imp_seg.
Qed.

Lemma valid_instr_grammars_imp p :
  In p valid_instr_grammars_rep -> In p instr_grammars_rep.
Proof.
  unfold valid_instr_grammars_rep, instr_grammars_rep. simpl.
  intros. tauto.
Qed.

Lemma valid_prefix_grammar_rep_or_repn_imp s v : 
  in_grammar valid_prefix_grammar_rep_or_repn s v -> 
  in_grammar prefix_grammar_rep_or_repn s v.
Proof.
  unfold valid_prefix_grammar_rep_or_repn, prefix_grammar_rep_or_repn. 
  intros. pinv. econstructor ; eauto. eapply in_option_perm3_2. Focus 2. eauto.
  apply gs_seg_imp_seg.
Qed.

Lemma valid_prefix_grammar_lock_with_op_override_imp s v : 
  in_grammar valid_prefix_grammar_lock_with_op_override s v -> 
  in_grammar prefix_grammar_lock_with_op_override s v.
Proof.
  unfold valid_prefix_grammar_lock_with_op_override, 
  prefix_grammar_lock_with_op_override.
  intros. pinv. econstructor ; eauto. 
  eapply in_option_perm3_variation_2. Focus 2. eauto.
  apply gs_seg_imp_seg.
Qed.

Lemma valid_prefix_grammar_lock_no_op_override_imp s v : 
  in_grammar valid_prefix_grammar_lock_no_op_override s v ->
  in_grammar prefix_grammar_lock_no_op_override s v.
Proof.
  unfold valid_prefix_grammar_lock_no_op_override, 
  prefix_grammar_lock_no_op_override. intros. pinv. econstructor ; eauto.
  unfold option_perm2 in *. 
  repeat match goal with 
    | [ H : in_grammar (_ |+| _) _ _ |- in_grammar (_ |+| _) _ _ ] => 
      pinv ; pinv ; [ eapply in_alt_l | eapply in_alt_r ]
    | _ => idtac
  end ; repeat pinv ; econstructor ; eauto. apply gs_seg_imp_seg ; auto.
  eapply in_perm2_2. Focus 2. eauto. apply gs_seg_imp_seg ; auto.
Qed.

Lemma valid_prefix_grammar_seg_with_op_override_imp s v : 
  in_grammar valid_prefix_grammar_seg_with_op_override s v ->
  in_grammar prefix_grammar_seg_with_op_override s v.
Proof.
  unfold valid_prefix_grammar_seg_with_op_override, 
  prefix_grammar_seg_with_op_override. intros ; pinv. 
  econstructor ; eauto. unfold option_perm2_variation in *.
  repeat match goal with 
    | [ H : in_grammar (_ |+| _) _ _ |- in_grammar (_ |+| _) _ _ ] => 
      pinv ; pinv ; [ eapply in_alt_l | eapply in_alt_r ]
    | _ => idtac
  end ; repeat pinv ; econstructor ; eauto. eapply in_perm2_1.
  Focus 2. eauto. apply gs_seg_imp_seg ; auto.
Qed.

Lemma valid_prefix_grammar_seg_override_imp s v : 
  in_grammar valid_prefix_grammar_seg_override s v -> 
  in_grammar prefix_grammar_seg_override s v.
Proof.
  unfold valid_prefix_grammar_seg_override, 
  prefix_grammar_seg_override. intros ; pinv ; econstructor ; eauto.
  unfold option_perm in *. pinv ; pinv ; [apply in_alt_l | apply in_alt_r].
  auto. pinv. econstructor ; eauto. apply gs_seg_imp_seg ; auto.
Qed.

Lemma valid_prefix_grammar_seg_op_override_imp s v : 
  in_grammar valid_prefix_grammar_seg_op_override s v -> 
  in_grammar prefix_grammar_seg_op_override s v.
Proof.
  unfold valid_prefix_grammar_seg_op_override, 
  prefix_grammar_seg_op_override. intros ; pinv ; econstructor ; eauto.
  unfold option_perm2 in *.
  repeat match goal with 
    | [ H : in_grammar (_ |+| _) _ _ |- in_grammar (_ |+| _) _ _ ] => 
      pinv ; pinv ; [ eapply in_alt_l | eapply in_alt_r ]
    | _ => idtac
  end ; repeat pinv ; econstructor ; eauto. apply gs_seg_imp_seg ; auto.
  eapply in_perm2_1. Focus 2. eauto. apply gs_seg_imp_seg ; auto.
Qed.

Lemma in_valid_instr_grammars_seg_override p : 
  In p valid_instr_grammars_seg_override -> 
  In p instr_grammars_seg_override.
Proof.
  unfold valid_instr_grammars_seg_override, instr_grammars_seg_override.
  intros.
  simpl in H. 
  Ltac m42 := 
  match goal with 
    | [ H : ?x = ?p  \/ ?Q |- In ?p (?x :: _) ] => 
      destruct H ; [left ; auto | right ; m42]
    | [ H : _ = _ \/ _ |- _ ] => right ; m42
    | [ H : False |- _ ] => contradiction 
  end.
  m42. 
Qed.

Lemma non_cflow_grammar_list_subset s v : 
  in_grammar (alts non_cflow_grammar_list) s v -> 
  in_grammar (alts instruction_grammar_list) s v.
Proof.
  unfold non_cflow_grammar_list. unfold instruction_grammar_list. intros.
  repeat
  match goal with 
    | [ H : in_grammar (alts (_ ++ _)) _ _ |- _] => 
      generalize (in_app_alts _ _ H) ; clear H ; intro H ; eapply in_alts_app ; 
      destruct H ; [ left | right ]
    | _ => idtac
  end ; 
  match goal with 
    | [ H : in_grammar (alts (List.map (fun _ => ?pre1 $ _) ?ps1)) _ _
        |- in_grammar (alts (List.map (fun _ => ?pre2 $ _) ?ps2)) _ _ ] => 
      apply (@alts_prefix_subset _ _ pre1 pre2 ps1 ps2) ; intros ; auto
  end.
  apply valid_prefix_grammar_rep_imp ; auto.
  apply valid_instr_grammars_imp ; auto.
  apply valid_prefix_grammar_rep_or_repn_imp ; auto.
  apply valid_prefix_grammar_lock_with_op_override_imp ; auto.
  apply valid_prefix_grammar_lock_no_op_override_imp ; auto.
  apply valid_prefix_grammar_seg_with_op_override_imp ; auto.
  apply valid_prefix_grammar_seg_op_override_imp ; auto.
  apply valid_prefix_grammar_seg_override_imp ; auto.
  apply in_valid_instr_grammars_seg_override ; auto.
Qed.

(** This shows that if a string matches the [non_cflow_parser], then it 
    will also match the [instruction_parser].  It's half of what we need
    to establish the correctness of the [non_cflow] DFA. *)
Lemma non_cflow_parser_subset : 
  forall s v, in_grammar non_cflow_grammar s v -> 
    in_grammar instruction_grammar s v.
Proof.
  apply non_cflow_grammar_list_subset.
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
  Parser.list_all (fun n => (n < 256)%nat) xs -> 
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
  assert (Z_of_nat a < Z_of_nat 256)%Z. apply inj_lt ; auto.
  split.
  apply Zle_0_nat. auto.
Qed.

Require Import Recognizer.

(** These abstraction shananigans are necessary to keep Coq from
    trying to actually build the recognizer from within Coq. *)
Module Type ABSTRACT_MAKE_RECOGNIZER_SIG.
  Parameter abstract_make_recognizer : 
    forall t, grammar t -> option Recognizer.DFA.
  Parameter make_recognizer_eq : abstract_make_recognizer = make_recognizer.
End ABSTRACT_MAKE_RECOGNIZER_SIG.

Module ABSTRACT_MAKE_RECOGNIZER : ABSTRACT_MAKE_RECOGNIZER_SIG.
  Definition abstract_make_recognizer := make_recognizer.
  Definition make_recognizer_eq := eq_refl make_recognizer.
End ABSTRACT_MAKE_RECOGNIZER.

Import ABSTRACT_MAKE_RECOGNIZER.

Lemma list_all_eq A (xs:list A) (P : A -> Prop) : 
  list_all P xs <-> Parser.list_all P xs.
Proof.
  induction xs ; simpl ; mysimp ; intros ; mysimp ; apply IHxs ; auto.
Qed.

(** This lemma tells that that the DFA build from the [non_cflow_parser],
    when run on an input string of bytes [bytes] and produces [Some(n,nats2)],
    implies that there exists some prefix of bytes, [bytes1] (of length [n]) 
    such that both the [non_cflow_parser] and the [instruction_parser], accept
    [bytes1] and produce the same value.  Furthermore, there is no smaller
    prefix of [bytes] that the [non_cflow_parser] will accept. Also,
*)
Opaque non_cflow_grammar.
Lemma non_cflow_dfa_corr1 :
  forall (d:DFA), 
    abstract_make_recognizer non_cflow_grammar = Some d -> 
    forall (bytes:list int8) (n:nat) (nats2:list nat),
      dfa_recognize d (List.map byte2token bytes) = Some (n, nats2) -> 
      exists bytes1, exists pfx:prefix, exists ins:instr, 
        in_grammar non_cflow_grammar (flat_map byte_explode bytes1) (pfx,ins) /\ 
        in_grammar instruction_grammar (flat_map byte_explode bytes1) (pfx,ins) /\ 
        n = length bytes1 /\ 
        bytes = bytes1 ++ (List.map nat_to_byte nats2) /\ 
        non_cflow_instr pfx ins = true /\
        (forall ts3 ts4,
          (length ts3 < length bytes1)%nat -> 
          bytes = ts3 ++ ts4 -> 
          forall v0, ~ in_grammar non_cflow_grammar (flat_map byte_explode ts3) v0).
Proof.
  intros. subst. rewrite make_recognizer_eq in H. unfold make_recognizer in H.
  assert (TLT:list_all (fun t => t < num_tokens) (List.map byte2token bytes)).
  rewrite list_all_eq. apply bytesLt256.
  generalize 
    (@dfa_recognize_corr _ non_cflow_grammar 400 d H (List.map byte2token bytes) TLT).
  clear H. rewrite H0. clear H0. mysimp. destruct x0. 
  exists (List.map nat_to_byte x). exists p. exists i. 
  assert (List.map nat_to_byte (x ++ nats2) = bytes).
  rewrite <- H. apply n2bs. rewrite map_app in H3. rewrite <- H3.
  rewrite map_length. generalize (non_cflow_instr_inv H1). 
  assert (list_all (fun n => n < 256)%nat (x ++ nats2)).
  rewrite <- H. rewrite list_all_eq.
  apply (bytesLt256 bytes). 
  generalize (list_all_app _ _ _ H4).
  intros. destruct H5. 
  assert (flat_map byte_explode (List.map nat_to_byte x) = flat_map nat2bools x).
  apply explode_bits. rewrite <- list_all_eq. auto. rewrite H8.
  assert (flat_map nat2bools x = flat_map token_id_to_chars x).
  generalize x H5. induction x0. simpl. auto. intros.
  replace (flat_map nat2bools (a::x0)) with ((nat2bools a) ++ (flat_map nat2bools x0)) ; 
    auto. replace (flat_map token_id_to_chars (a :: x0)) with 
          ((token_id_to_chars a) ++ (flat_map token_id_to_chars x0)) ; auto. 
  destruct H9. rewrite (IHx0 H10). 
  replace (nat2bools a) with (token_id_to_chars a) ; auto.
  unfold token_id_to_chars. unfold nat2bools. unfold nat_explode. unfold byte_explode. 
  assert (Word.unsigned (int8_of_nat a) = Z.of_nat a).
  rewrite Word.unsigned_repr. auto. 
  split. apply Zle_0_nat. unfold Word.max_unsigned. simpl. 
  omega. rewrite H11. auto. rewrite H9. split. auto. split.
  apply non_cflow_parser_subset. auto. split. auto. split. auto. split. auto. intros.
  specialize (H2 (List.map byte2token ts3) (List.map byte2token ts4)).
  repeat rewrite map_length in H2. specialize (H2 H10).
  rewrite <- map_app in H11. rewrite <- H in H11.
  rewrite <- map_app in H2. rewrite <- H11 in H2. rewrite n2bs in H2. 
  specialize (H2 (eq_refl _)). intro. specialize (H2 v0). apply H2.
  assert (flat_map nat2bools (List.map byte2token ts3) = flat_map byte_explode ts3).
  rewrite <- explode_bits. rewrite n2bs. auto. apply (bytesLt256 ts3).
  rewrite <- H13 in H12. 
  assert (forall x, flat_map token_id_to_chars (List.map byte2token x) = 
                    flat_map nat2bools (List.map byte2token x)).
  induction x0. auto. replace (flat_map token_id_to_chars (List.map byte2token (a::x0)))
  with ((token_id_to_chars (byte2token a)) ++ (flat_map token_id_to_chars (List.map byte2token x0))) ; auto.
  replace (flat_map nat2bools (List.map byte2token (a::x0))) with
  ((nat2bools (byte2token a)) ++ (flat_map nat2bools (List.map byte2token x0))) ; auto.
  rewrite IHx0. replace (token_id_to_chars (byte2token a)) with (nat2bools (byte2token a)); auto.
  unfold nat2bools, token_id_to_chars. unfold nat_explode. unfold byte_explode.
  assert (Z.of_nat (byte2token a) = Word.unsigned (int8_of_nat (byte2token a))).
  unfold byte2token. rewrite Zabs2Nat.id_abs.
  rewrite Word.unsigned_repr. auto. unfold Word.unsigned. destruct a. simpl.
  split. destruct intrange. unfold Z.abs. destruct intval ; auto. 
  assert False. unfold Z.le in H14. unfold Z.compare in H14.
  apply H14 ; auto. contradiction. unfold Word.max_unsigned. simpl.
  assert ((Word.modulus 7 = 256)%Z). auto. rewrite H14 in intrange.
  destruct intrange. destruct intval ; simpl ; auto. omega. omega. 
  assert False. unfold Z.le in H15. unfold Z.compare in H15. apply H15. auto.
  contradiction. rewrite <- H14. auto.
  rewrite H14. auto.
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
Fixpoint simple_determ t (p:grammar t) : bool := 
  match p with 
    | Any => true
    | Char _ => true
    | Eps => true
    | Zero _ => true
    | Cat t1 t2 p1 p2 => simple_determ p1 && simple_determ p2
    | Map t1 t2 f p => simple_determ p
    | Xform t1 t2 f p => simple_determ p
    | _ => false
  end.

(** [simple_determ] implies a grammar only accepts strings of the same size. *)
Lemma simple_determ_same_size : forall t (p:grammar t), simple_determ p = true ->
  forall s1 v1 s2 v2, 
    in_grammar p s1 v1 -> 
    in_grammar p s2 v2 -> length s1 = length s2.
Proof.
  induction p ; simpl ; intros ; try congruence ; repeat pinv ; auto.
  repeat rewrite app_length. congruence. 
  apply (IHp H s1 x0 s2 x H0 H1).   apply (IHp H s1 x1 s2 x0 H0 H1).
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
  
(** [simple_determ] implies a grammar is deterministic. *)
Lemma simple_determ_corr : forall t (p:grammar t), 
  simple_determ p = true -> 
  forall s v1 v2,
    in_grammar p s v1 -> in_grammar p s v2 -> v1 = v2.
Proof.
  induction p ; simpl ; intros ; try congruence ; repeat pinv ; auto.
  generalize (simple_determ_same_size Heqx7 H0 H1).
  generalize (simple_determ_same_size Heqy H3 H2). intros.
  generalize (app_inj_length _ _ _ _ H5 H (eq_sym H4)). intros. destruct H6 ; subst.
  rewrite (IHp1 _ _ _ H1 H0). rewrite (IHp2 _ _ _ H2 H3). auto.
  rewrite (IHp H _ _ _ H1 H0). auto. rewrite (IHp H _ _ _ H1 H0) ; auto.
Qed.

(** We are going to calculate the DNF for the prefixes.  But we can only
    do this for grammars that don't contain [Star_p]. *)
Fixpoint star_free t (p:grammar t) : bool := 
  match p with 
    | Star _ _ => false
    | Cat t1 t2 p1 p2 => star_free p1 && star_free p2
    | Alt t1 t2 p1 p2 => star_free p1 && star_free p2
    | Map t1 t2 f p' => star_free p'
    | Xform t1 t2 f p' => star_free p'
    | _ => true
  end.

(** Disjunctive normal-form for grammars.  This is not well-defined when 
    the grammar includes [Star_p]. *)
Fixpoint dnf t (p:grammar t) : list (grammar t) := 
  match p in grammar t return list (grammar t) with 
    | Alt t1 t2 p1 p2 => 
      (List.map (fun p => @Map t1 (Sum_t t1 t2) (fun x => inl x) p) (dnf p1)) ++ 
      (List.map (fun p => @Map t2 (Sum_t t1 t2) (fun x => inr x) p) (dnf p2))
    | Cat t1 t2 p1 p2 => 
      flat_map (fun d1 => List.map (fun d2 => Cat d1 d2) (dnf p2)) (dnf p1)
    | Map t1 t2 f p => List.map (fun d => @Map t1 t2 f d) (dnf p)
    | Xform t1 t2 f p => List.map (fun d => @Xform t1 t2 f d) (dnf p)
    | p' => p'::nil
  end.

Definition in_alts_g := in_alts.
Require Import CheckDeterministic.

(** Check that a grammar is determinsistic -- blow it up into its disjunctive
    normal form, and use [check_all_p] to ensure that there is no string in
    common. *)
Definition check_determ t (p:grammar t) : bool := 
  star_free p && check_all_p' 3 (dnf p).

(** Check that a list of grammars is determinsitic. *)
Fixpoint check_determ_ps t (ps:list (grammar t)) : bool := 
  match ps with 
    | nil => true
    | p::ps' => check_determ p && check_determ_ps ps'
  end.

(** converting a grammar to DNF is equivalent to the original grammar *)
Lemma dnf_corr1 t (p:grammar t) s v : 
  in_grammar p s v -> 
  in_grammar (alts (dnf p)) s v.
Proof.
  induction 1 ; simpl ; intros ; subst ; try (econstructor ; eauto ; fail) ; 
    repeat
    match goal with 
      | [ H : _ && _ = true |- _ ] => generalize (andb_prop _ _ H) ; clear H ; t
      | [ H : ?x = true -> _, H1 : ?x = true |- _ ] => specialize (H H1)
      | [ |- in_grammar (alts (_ ++ _)) _ _ ] => eapply in_alts_app
      | _ => auto
    end. 
  generalize (dnf g1) (dnf g2) IHin_grammar1 IHin_grammar2. 
  induction l ; simpl ; intros. rewrite in_alts_g in IHin_grammar0. simpl in *.
  pinv. eapply in_alts_app. rewrite in_alts_g in IHin_grammar0. 
  simpl in IHin_grammar0. pinv. destruct H1. left. 
  apply in_map_alts. econstructor ; eauto. right. eapply IHl ; eauto.
  rewrite in_alts_g. auto. left. generalize (dnf g1) IHin_grammar. 
  induction l ; rewrite in_alts_g ; simpl ; intros.  pinv.
  pinv. rewrite in_alts_g. simpl. destruct H0. eapply in_alt_l.
  econstructor ; eauto. eapply in_alt_r. rewrite in_alts_g in IHl.
  specialize (IHl H0). rewrite in_alts_g in IHl. auto.
  right. generalize (dnf g2) IHin_grammar. induction l ; rewrite in_alts_g ; simpl ; 
  intros ; pinv. rewrite in_alts_g ; simpl. destruct H0. eapply in_alt_l.
  econstructor ; eauto. eapply in_alt_r. repeat rewrite in_alts_g in IHl.
  apply (IHl H0). rewrite in_alts_g. simpl. eapply in_alt_l. eapply InStar_cons ; eauto. 
  generalize (dnf g) IHin_grammar. induction l ; repeat rewrite in_alts_g. simpl.
  intros ; pinv. simpl. intros ; pinv. destruct H0. apply in_alt_l. econstructor ; eauto.
  eapply in_alt_r. repeat rewrite in_alts_g in IHl. eauto.
  generalize (dnf g) IHin_grammar. induction l ; repeat rewrite in_alts_g. simpl.
  intros ; pinv. simpl. intros ; pinv. destruct H0. apply in_alt_l. econstructor ; eauto.
  eapply in_alt_r. repeat rewrite in_alts_g in IHl. eauto.
Qed.

Lemma dnf_corr2 t (p:grammar t) s v :
  in_grammar (alts (dnf p)) s v -> 
  star_free p = true -> 
  in_grammar p s v.
Proof.
  intros t p s v. rewrite in_alts_g. generalize s v ; clear s v.
  induction p ; simpl ; unfold never ; intros ; repeat pinv ; eauto.
  generalize (dnf p1) (dnf p2) IHp1 IHp2 H ; clear IHp1 IHp2 H Heqx Heqy.
  induction l ; simpl ; unfold never in * ; intros ; simpl in * ; repeat pinv. 
  rewrite <- in_alts_g in H. 
  generalize (in_app_alts _ _ H). repeat rewrite in_alts_g. clear H ; intros. destruct H.
  clear IHl. induction l0 ; simpl in * ; unfold never in * ; pinv.
  destruct H. pinv. econstructor ; eauto. rewrite <- in_alts_g in *.
  rewrite <- in_map_alts in H. pinv. econstructor ; eauto. eapply IHp2 ; auto.
  eapply in_alt_r. apply in_alts_g ; auto. eapply IHl. intros. eapply IHp1 ; eauto.
  eapply IHp2 ; eauto. auto. rewrite <- in_alts_g in H. generalize (in_app_alts _ _ H).
  clear H ; intros. destruct H. 
  assert (in_grammar (Map (Sum_t t1 t2) (fun x => inl x) (alts (dnf p1))) s v).
  generalize (dnf p1) H. induction l ; simpl ; repeat rewrite in_alts_g ; simpl ; 
  intros ; pinv. destruct H0. pinv. econstructor ; eauto. rewrite in_alts_g. simpl.
  eapply in_alt_l. eauto. rewrite in_alts_g in IHl. specialize (IHl H0).
  pinv. econstructor ; eauto. rewrite in_alts_g. simpl. eapply in_alt_r. 
  rewrite in_alts_g in H1. auto. pinv. rewrite in_alts_g in H0.
  specialize (IHp1 _ _ H0 (eq_refl _)). eauto.
  assert (in_grammar (Map (Sum_t t1 t2) (fun x => inr x) (alts (dnf p2))) s v).
  generalize (dnf p2) H ; induction l ; simpl ; repeat rewrite in_alts_g ; simpl ; 
  intros ; pinv. destruct H0. pinv. econstructor ; eauto. rewrite in_alts_g ; simpl.
  eapply in_alt_l ; eauto. rewrite in_alts_g in IHl. specialize (IHl H0).
  pinv. econstructor ; eauto. rewrite in_alts_g. simpl. eapply in_alt_r ; eauto.
  apply in_alts_g. auto. pinv. eapply InAlt_r ; eauto. eapply IHp2 ; auto.
  eapply in_alts_g. eauto.
  assert (in_grammar (Map t2 i (alts (dnf p))) s v). 
  generalize (dnf p) H. induction l ; simpl ; intros ; pinv. destruct H1.
  pinv. econstructor ; eauto. rewrite in_alts_g. eapply in_alt_l. eauto.
  specialize (IHl H1). pinv. econstructor ; eauto. rewrite in_alts_g.
  eapply in_alt_r. eapply in_alts_g. eauto. clear H. pinv.
  rewrite in_alts_g in H. specialize (IHp _ _ H H0). econstructor ; eauto.
  assert (in_grammar (Xform x (alts (dnf p))) s v).
  generalize (dnf p) H. induction l ; simpl ; intros ; pinv. 
  destruct H1. pinv. econstructor ; eauto. rewrite in_alts_g. eapply in_alt_l ; eauto.
  specialize (IHl H1). clear H1. pinv. econstructor ; eauto. rewrite in_alts_g ; eapply
  in_alt_r. apply in_alts_g. eauto. pinv. rewrite in_alts_g in H1.
  specialize (IHp _ _ H1 H0). econstructor ; eauto.
Qed.

(** All of the grammars in [ps] are [simple_determ]. *)
Fixpoint simple_determ_list t (ps:list (grammar t)) : bool := 
  match ps with 
    | nil => true
    | p::ps' => simple_determ p && simple_determ_list ps'
  end.

Lemma simple_determ_app t (ps1 ps2:list (grammar t)) : 
  simple_determ_list (ps1 ++ ps2) = 
  simple_determ_list ps1 && simple_determ_list ps2.
Proof.
  induction ps1 ; simpl ; auto. intros. destruct (simple_determ a) ; simpl ; auto.
Qed.

(** All of the grammars in [dnf p] are [simple_determ] *)
Lemma dnf_determ t (p:grammar t) : 
  star_free p = true -> simple_determ_list (dnf p) = true.
Proof.
  induction p ; simpl ; intros ; subst ; simpl ; repeat pinv ; auto.
  generalize (dnf p1) (dnf p2) IHp1 IHp2 ; clear IHp1 IHp2.
  induction l ; simpl ; intros ; try contradiction ; repeat pinv ; auto.
  rewrite simple_determ_app. rewrite IHl ; auto. 
  SearchAbout (_ && _). rewrite andb_true_r.
  clear IHl. induction l0 ; simpl ; auto. rewrite Heqx0. simpl in *.
  generalize (andb_prop _ _ IHp2). t. rewrite H. rewrite IHl0 ; auto.
  rewrite simple_determ_app. generalize (dnf p1) (dnf p2) IHp1 IHp2.
  induction l ; simpl ; intros. induction l ; simpl in * ; auto.
  generalize (andb_prop _ _ IHp3). t. rewrite H. simpl. rewrite IHl ; auto.
  generalize (andb_prop _ _ IHp0) ; t. rewrite H. simpl. rewrite IHl ; auto.
  specialize (IHp H). clear H. generalize (dnf p) IHp ; clear IHp.
  induction l ; simpl ; auto ; t. generalize (andb_prop _ _ IHp). t.
  rewrite H. rewrite IHl ; auto.
  specialize (IHp H). clear H. generalize (dnf p) IHp ; clear IHp.
  induction l ; simpl ; auto ; t. generalize (andb_prop _ _ IHp). t.
  rewrite H. rewrite IHl ; auto.
Qed.

(** This ensures that if [p] is deterministic and [s] and [v] are in the 
   denotation of [p], then there is no prefix of [s] in the domain of the 
   denotation of [p], and that there is at most one value associated with 
   [s] in the denotation of [p]. *)
Lemma check_determ_corr' t (p:grammar t) : 
  check_determ p = true -> 
  forall s v,
    in_grammar p s v -> 
    (forall s1 s2 v', 
        s = s1 ++ s2 -> 
        in_grammar p s1 v' -> s2 = nil /\ v' = v).
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
  apply in_alts_comm'. rewrite in_alts_g. apply in_alt_l. auto. contradiction.
  injection H0 ; injection H2 ; clear H0 H2 ; intros ; subst. clear IHl. subst.
  simpl in *. assert False. apply H8. exists s2. exists v. rewrite in_alts_g. 
  eapply in_alt_l. auto.
  contradiction.
  injection H0 ; injection H2 ; clear H0 H2 ; intros ; subst.
  specialize (IHl x2 x3 x4 x x0 x1 H2 (eq_refl _) H7 H5). apply IHl ; clear IHl.
  intro. apply H8. t. exists x5. exists x6. simpl. 
  rewrite in_alts_g. eapply in_alt_r. rewrite <- in_alts_g. auto.
  intro ; t. apply H6. exists x5. exists x6. simpl. rewrite in_alts_g. 
  eapply in_alt_r. rewrite <- in_alts_g. auto.
  simpl in H. generalize (andb_prop _ _ H). t ; auto.
Qed.

(** Check that all of the instruction grammars (without the prefixes) are 
    deterministic.  This runs fast enough that we can afford to do this. *)
Lemma all_grammars_determ : 
  check_determ_ps (
      instr_grammars_rep ++
      instr_grammars_rep_or_repn ++
      instr_grammars_lock_with_op_override ++
      instr_grammars_lock_no_op_override ++
      instr_grammars_seg_with_op_override ++
      instr_grammars_seg_op_override ++ 
      instr_grammars_seg_override 
  ) = true.
Proof.
  vm_compute. auto.
Qed.

(** This checks that when we add a prefix to a grammar, that the grammar 
    remains deterministic.  We do so by calculating the DNF of the 
    prefix, and pre-pending each DNF term to the grammar. *)
Definition check_pfx t1 t2 (p1:grammar t1) (p2:grammar t2) := 
  check_all_p' 3 (List.map (fun d1 => Cat d1 p2) (dnf p1)).

Fixpoint check_all_pfx t1 t2 (p1:grammar t1) (p2s:list (grammar t2)) := 
  match p2s with 
    | nil => true
    | p2::p2s' => check_pfx p1 p2 && check_all_pfx p1 p2s'
  end.

(** Check that adding all of the prefixes to the grammars keeps them
    deterministic. *)
Lemma check_all_prefixed_instructions : 
  (check_all_pfx prefix_grammar_rep instr_grammars_rep) && 
  (check_all_pfx prefix_grammar_rep_or_repn instr_grammars_rep_or_repn) &&
  (check_all_pfx prefix_grammar_lock_with_op_override 
                 instr_grammars_lock_with_op_override) &&
  (check_all_pfx prefix_grammar_lock_no_op_override instr_grammars_lock_no_op_override) &&
  (check_all_pfx prefix_grammar_seg_with_op_override 
                 instr_grammars_seg_with_op_override) &&
  (check_all_pfx prefix_grammar_seg_op_override instr_grammars_seg_op_override) &&
  (check_all_pfx prefix_grammar_seg_override instr_grammars_seg_override) = true.
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
    grammar, then at most one value is associated with a string [s] in the
    denotation of the compound grammar, and furthermore, there is no prefix
    of [s] that is in the denotation. This basically handles one of the
    alternatives of the DNF of a prefix. *)
Lemma simple_pfx_determ' t1 t2 (p1:grammar t1) (p2:grammar t2) : 
  simple_determ p1 = true -> 
  check_determ p2 = true -> 
  forall s v1,
    in_grammar (Cat p1 p2) s v1 -> 
    forall s1 s2 v2,
      s = s1 ++ s2 ->
      in_grammar (Cat p1 p2) s1 v2 -> 
      s2 = nil /\ v1 = v2.
Proof.
  intros. generalize (simple_determ_same_size H). intros. repeat pinv.
  rewrite app_ass in H6.
  generalize (inj_app_length _ _ _ _ H4 H6). t. subst.
  generalize (simple_determ_corr H). intros. rewrite (H7 _ _ _ H3 H1).
  generalize (check_determ_corr' H0). intros. 
  specialize (H8 _ _ H2 x0 s2 _ (eq_refl _) H5). t ; subst. auto.
Qed.

Lemma in_dnf_cat t1 t2 (p1:grammar t1) (p2:grammar t2) s v: 
  in_grammar (Cat p1 p2) s v -> 
  in_grammar (alts (List.map (fun d1 => Cat d1 p2) (dnf p1))) s v.
Proof.
  intros. pinv. generalize (dnf_corr1 H). generalize (dnf p1). intro l.
  rewrite in_alts_g. rewrite in_alts_g. induction l ; 
  simpl ; intros ; repeat pinv. apply in_alt_l. econstructor ; eauto.
  apply in_alt_r. eauto.
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
    grammar, then adding [p1] to [p2] yields a grammar that is deterministic,
    and furthermore, if [s] is in the domain of [p1 $ p2], then there is no
    prefix of [s] that is in the domain of [p1 $ p2]. *)
Lemma check_pfx_determ' t1 t2 (p1:grammar t1) (p2:grammar t2) : 
  star_free p1 = true ->
  check_determ p2 = true -> 
  check_pfx p1 p2 = true -> 
  forall s v1,
    in_grammar (Cat p1 p2) s v1 -> 
    forall s1 s2 v2,
      s = s1 ++ s2 -> 
      in_grammar (Cat p1 p2) s1 v2 -> s2 = nil /\ v1 = v2.
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
  generalize (inv_alt H12). generalize (inv_alt H11). clear H11 H12. intros. 
  destruct H11 ; destruct H12 ; 
    try (eapply simple_pfx_determ' ; eauto) ;
      contradiction H10 ; exists s2 ; exists v1 ; auto.
Qed.

(** Show that the prefixes used in the semantics are star-free. *)
Lemma star_free_prefix_grammar_rep : 
  star_free prefix_grammar_rep = true.
Proof.
  vm_compute ; auto.
Qed.

Lemma star_free_prefix_grammar_rep_or_repn : 
  star_free prefix_grammar_rep_or_repn = true.
Proof.
  vm_compute ; auto.
Qed.

Lemma star_free_prefix_grammar_lock_with_op_override : 
  star_free prefix_grammar_lock_with_op_override = true.
Proof.
  vm_compute ; auto.
Qed.

Lemma star_free_prefix_grammar_lock_no_op_override : 
  star_free prefix_grammar_lock_no_op_override = true.
Proof.
  vm_compute ; auto.
Qed.

Lemma star_free_prefix_grammar_seg_with_op_override : 
  star_free prefix_grammar_seg_with_op_override = true.
Proof.
  vm_compute ; auto.
Qed.

Lemma star_free_prefix_grammar_seg_op_override : 
  star_free prefix_grammar_seg_op_override = true.
Proof.
  vm_compute ; auto.
Qed.

Lemma star_free_prefix_grammar_seg_override : 
  star_free prefix_grammar_seg_override = true.
Proof.
  vm_compute. auto.
Qed.

Lemma and_parse2rexp t (p1:grammar t) (ps:list (grammar t)) s v1 v2: 
  in_grammar p1 s v1 -> in_grammar (alts ps) s v2 -> 
  in_rexp (OptAnd_r (grammar2rexp p1) (alts_r (List.map (@grammar2rexp _) ps))) s.
Proof.
  intros. apply opt_and_r_corr. econstructor. eapply grammar2rexp_corr1 ; eauto.
  generalize ps H0. induction ps0. simpl. rewrite in_alts_g. simpl. intros. pinv.
  rewrite in_alts_g. simpl. intros. pv_opt. pinv. destruct H1. econstructor. 
  eapply grammar2rexp_corr1.
  eauto. eapply Alt_right_ri. apply IHps0. apply in_alts_g ; auto.
Qed.

(** An intermediate lemma that tells us that when all of the grammars
    in [p::ps] have been shown to be disjoint, then there is no 
    string in the domain of both [p] and [ps]. *)
Lemma check_all_p'_tail t n (p:grammar t) (ps:list (grammar t)) : 
  check_all_p' n (p::ps) = true -> 
  check_all_p' n ps = true /\ 
  (forall s v1, in_grammar p s v1 -> 
    forall s1 s2 v2, s = s1++s2 -> ~ in_grammar (alts ps) s1 v2) /\
  (forall s v1, in_grammar (alts ps) s v1 -> 
    forall s1 s2 v2, s = s1++s2 -> ~ in_grammar p s1 v2).
Proof.
  intros. generalize (andb_prop _ _ H). t. split. auto. clear H0.
  replace ((fix map (l:list(grammar t)) : list rexp := 
            match l with | nil => nil | a::t => grammar2rexp a :: map t end) ps) with
  (List.map (@grammar2rexp t) ps) in H1 ; auto. clear H.
  generalize (ckzeros_corr _ _ H1). intros. split ; intros ; intro ; subst.
  contradiction H. exists (s1 ++ s2). eapply opt_and_r_corr. econstructor.
  eapply opt_cat_r_corr. econstructor. eapply in_alts.  eauto.
  eapply star_any_all. eauto. eapply opt_cat_r_corr. econstructor.
  eapply grammar2rexp_corr1. eauto. eapply (star_any_all nil). 
  rewrite <- app_nil_end. auto.
  contradiction H. exists (s1 ++ s2). eapply opt_and_r_corr. econstructor.
  eapply opt_cat_r_corr. econstructor. eapply in_alts. eauto.
  eapply (star_any_all nil). rewrite <- app_nil_end. eauto. 
  eapply opt_cat_r_corr. econstructor. eapply grammar2rexp_corr1. eauto. 
  eapply (star_any_all s2). auto.
Qed.

Lemma in_alts_map2 t1 t2 (ps:list (grammar t1)) (p2:grammar t2) s v :
  in_grammar (alts (List.map (fun p1 => Cat p1 p2) ps)) s v -> 
  in_grammar (Cat (alts ps) p2) s v.
Proof.
  induction ps ; simpl ; intros ; rewrite in_alts_g in H ; simpl in H ; repeat pinv.
  econstructor. rewrite in_alts_g. simpl. apply in_alt_l. eauto. eauto. auto. auto.
  rewrite <- in_alts_g in H.
  specialize (IHps _ _ _ H). repeat pinv. econstructor. rewrite in_alts_g. simpl.
  apply in_alt_r. rewrite <- in_alts_g. eauto. eauto. auto. auto.
Qed.

(** More abstraction stuff to keep Coq from unwininding the definition 
    of [check_all_p]. *)
Module Type ABSTRACT_CHECK_ALL_P_SIG.
  Parameter abstract_check_all_p : nat -> forall t , list (grammar t) -> bool.
  Parameter abstract_check_all_p_eq : 
    abstract_check_all_p = check_all_p'.
End ABSTRACT_CHECK_ALL_P_SIG.

Module ABSTRACT_CHECK_ALL_P : ABSTRACT_CHECK_ALL_P_SIG.
  Definition abstract_check_all_p := check_all_p'.
  Definition abstract_check_all_p_eq := eq_refl check_all_p'.
End ABSTRACT_CHECK_ALL_P.

Import ABSTRACT_CHECK_ALL_P.
Transparent instruction_grammar_list.
(** Make the [check_all_p] for the instructions used in the grammar abstract. *)
Lemma abstract_check_all_p_instructions : 
  abstract_check_all_p 3 instruction_grammar_list = true.
Proof.
  unfold instruction_grammar_list.
  generalize all_instructions_check.
  unfold instruction_grammar_list.
  rewrite <- abstract_check_all_p_eq.
  auto.
Qed.

(*
(** This lemma tells us that if we build a grammar from two prefixes
    and two lists of grammars, such that the prefixes are star-free,
    and the grammars have been checked to be deterministic, and the
    concatenation of the prefixes on the grammars don't have any strings
    in common in their domain, then the resulting mongo grammar 
    is deterministic and furthermore, when [s] and [v] are in its
    denotation, then there is no prefix of [s] in the denotation. *)
Lemma grammar_determ' t1 t2 m (pfx1 pfx2:grammar t1) (ps1 ps2 :list (grammar t2)) : 
  star_free pfx1 = true -> 
  star_free pfx2 = true -> 
  check_determ_ps ps1 = true -> 
  check_determ_ps ps2 = true -> 
  abstract_check_all_p m ((List.map (fun p => pfx1 $ p) ps1) ++ 
                 (List.map (fun p => pfx2 $ p) ps2)) = true -> 
  check_all_pfx pfx1 ps1 = true -> 
  check_all_pfx pfx2 ps2 = true -> 
  forall s s1 s2 v1 v2,
    in_grammar (alts ((List.map (fun p => pfx1 $ p) ps1) ++ 
      (List.map (fun p => pfx2 $ p) ps2))) s v1 -> 
    s = s1 ++ s2 ->
    in_grammar (alts ((List.map (fun p => pfx1 $ p) ps1) ++ 
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
  contradiction H12. exists s2. exists v1. rewrite in_alts_g.
  apply in_alt_l. auto.
  contradiction. assert False ; clear IHps0 ; subst. contradiction H12.
  exists s2. exists v1. eapply in_alts_comm'.  rewrite in_alts_g. 
  apply in_alt_l. auto.
  contradiction. subst. assert (x8 = x5 /\ x6 = x9 /\ x7 = x10).
  eapply IHps0 ; clear IHps0 ; auto. intro. contradiction H14. t.
  exists x11. exists x12. rewrite in_alts_g. apply in_alt_r. rewrite <- in_alts_g.
  auto.
  intro ; t. eapply H12. exists x11 ; exists x12. rewrite in_alts_g. 
  apply in_alt_r. rewrite <- in_alts_g. auto. 
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
*)

Lemma check_determ_ps_app : forall t (ps1 ps2:list (grammar t)), 
  check_determ_ps (ps1 ++ ps2) = true -> 
  check_determ_ps ps1 = true /\ check_determ_ps ps2 = true.
Proof.
  induction ps1. simpl. auto. simpl. intros. 
  generalize (andb_prop _ _ H). t. generalize (IHps1 _ H1). t. 
  rewrite H0. rewrite H2. rewrite H3. auto.
Qed.

Lemma in_check_determ_ps t x (ps:list (grammar t)) : 
  In x ps -> check_determ_ps ps = true -> check_determ x = true.
Proof.
  induction ps ; simpl ; t. contradiction. generalize (andb_prop _ _ H0). t.
  destruct H. subst ; auto. apply IHps ; auto.
Qed.

Lemma instr_grammars_determ x : 
  (In x instr_grammars_rep \/
  In x instr_grammars_rep_or_repn \/ 
  In x instr_grammars_lock_with_op_override \/
  In x instr_grammars_lock_no_op_override \/
  In x  instr_grammars_seg_with_op_override \/
  In x instr_grammars_seg_op_override \/
  In x instr_grammars_seg_override) -> check_determ x = true.
Proof.
  intros. 
  assert (In x (instr_grammars_rep ++
  instr_grammars_rep_or_repn ++
  instr_grammars_lock_with_op_override ++
  instr_grammars_lock_no_op_override ++
  instr_grammars_seg_with_op_override ++
  instr_grammars_seg_op_override ++
  instr_grammars_seg_override)). 
  destruct H. apply in_app. auto. apply in_app ; right.
  destruct H. apply in_app. auto. apply in_app ; right.
  destruct H. apply in_app. auto. apply in_app ; right.
  destruct H. apply in_app. auto. apply in_app ; right.
  destruct H. apply in_app. auto. apply in_app ; right.
  apply in_app ; auto.
  apply (in_check_determ_ps _ _ H0). apply all_grammars_determ.
Qed.

Lemma in_check_all_pfx t1 t2 x (pre:grammar t1) (ps:list (grammar t2)) : 
  In x ps -> check_all_pfx pre ps = true -> check_pfx pre x = true.
Proof.
  induction ps ; simpl ; t. contradiction. generalize (andb_prop _ _ H0). clear H0 ; t.
  destruct H ; subst ; auto. 
Qed.

Lemma check_all_rep x : 
  In x instr_grammars_rep -> check_pfx prefix_grammar_rep x = true.
Proof.
  intros. generalize (andb_prop _ _ check_all_prefixed_instructions). t. repeat 
  match goal with 
    | [ H : _  && _ = true |- _ ] => generalize (andb_prop _ _ H) ; clear H ; t
  end.
  apply (in_check_all_pfx _ _ _ H H0).
Qed.

Lemma check_all_rep_or_repn x : 
  In x instr_grammars_rep_or_repn -> check_pfx prefix_grammar_rep_or_repn x = true.
Proof.
  intros. generalize (andb_prop _ _ check_all_prefixed_instructions). t. repeat 
  match goal with 
    | [ H : _  && _ = true |- _ ] => generalize (andb_prop _ _ H) ; clear H ; t
  end.
  apply (in_check_all_pfx _ _ _ H). auto.
Qed.

Lemma check_all_lock_with_op_override x : 
  In x instr_grammars_lock_with_op_override -> 
  check_pfx prefix_grammar_lock_with_op_override x = true.
Proof.
  intros. generalize (andb_prop _ _ check_all_prefixed_instructions). t. repeat 
  match goal with 
    | [ H : _  && _ = true |- _ ] => generalize (andb_prop _ _ H) ; clear H ; t
  end.
  apply (in_check_all_pfx _ _ _ H). auto.
Qed.

Lemma check_all_lock_no_op_override x : 
  In x instr_grammars_lock_no_op_override -> 
  check_pfx prefix_grammar_lock_no_op_override x = true.
Proof.
  intros. generalize (andb_prop _ _ check_all_prefixed_instructions). t. repeat 
  match goal with 
    | [ H : _  && _ = true |- _ ] => generalize (andb_prop _ _ H) ; clear H ; t
  end.
  apply (in_check_all_pfx _ _ _ H). auto.
Qed.

Lemma check_all_seg_with_op_override x : 
  In x instr_grammars_seg_with_op_override -> 
  check_pfx prefix_grammar_seg_with_op_override x = true.
Proof.
  intros. generalize (andb_prop _ _ check_all_prefixed_instructions). t. repeat 
  match goal with 
    | [ H : _  && _ = true |- _ ] => generalize (andb_prop _ _ H) ; clear H ; t
  end.
  apply (in_check_all_pfx _ _ _ H). auto.
Qed.

Lemma check_all_seg_op_override x : 
  In x instr_grammars_seg_op_override -> 
  check_pfx prefix_grammar_seg_op_override x = true.
Proof.
  intros. generalize (andb_prop _ _ check_all_prefixed_instructions). t. repeat 
  match goal with 
    | [ H : _  && _ = true |- _ ] => generalize (andb_prop _ _ H) ; clear H ; t
  end.
  apply (in_check_all_pfx _ _ _ H). auto.
Qed.

Lemma check_all_seg_override x : 
  In x instr_grammars_seg_override -> 
  check_pfx prefix_grammar_seg_override x = true.
Proof.
  intros. generalize (andb_prop _ _ check_all_prefixed_instructions). t. repeat 
  match goal with 
    | [ H : _  && _ = true |- _ ] => generalize (andb_prop _ _ H) ; clear H ; t
  end.
  apply (in_check_all_pfx _ _ _ H). auto.
Qed.

(** A key lemma:  This tells us that the [instruction_grammar] is deterministic --
    i.e., associates at most one value with a given string.  Furthermore, it tells
    us that if the [instruction_grammar] accepts a string [s], then there is no
    prefix of [s] that is accepted.  This is crucial for showing that a shortest-
    match strategy (used by both the DFA and the derivative-based grammarin the
    semantics) is complete. *)
Lemma grammar_determ : 
  forall s v1, 
    in_grammar instruction_grammar s v1 -> 
    forall s1 s2 v2, 
      s = s1 ++ s2 -> in_grammar instruction_grammar s1 v2 -> 
      s2 = nil /\ v1 = v2.
Proof.
  unfold instruction_grammar. (* unfold instruction_grammar_list. *)
  generalize all_instructions_check. intro.
  generalize (check_all_p'_corr 3 instruction_grammar_list H). clear H. intros. subst.
  generalize (H _ _ H2). generalize (H _ _ H0). clear H. t.
  assert (x = x2 /\ x3 = x0 /\ x4 = x1).
  generalize x2 x3 x4 H H5 H6 x x0 x1 H1 H3 H4.
  clear x2 x3 x4 H H5 H6 x x0 x1 H1 H3 H4.  clear H2 H0.
  generalize instruction_grammar_list. induction l.
  simpl. intros. generalize (nil_is_nil_app_nil _ _ H). t. discriminate H2.
  simpl in *. intros. destruct x2. simpl in H. injection H ; clear H ; intros ; subst.
  destruct x. simpl in *. injection H1 ; clear H1 ; intros ; subst. auto.
  simpl in *. injection H1. intros ; subst. clear H1. assert False.
  apply H4. exists s2. exists v1. rewrite in_alts_g. simpl. apply in_alt_l. auto.
  contradiction. simpl in H. injection H. intros. subst. clear H.
  destruct x. simpl in H1. injection H1 ; clear H1 ; intros ; subst.
  assert False ; [ idtac | contradiction ]. simpl in *. apply H4.
  exists s2. exists v1. apply in_alts_comm'. rewrite in_alts_g.
  simpl. apply in_alt_l. auto. simpl in *. injection H1. intros ; subst. clear H1.
  specialize (fun H1 H2 => IHl _ _ _ (eq_refl _) H5 H1 _ _ _ H H3 H2).
  assert (~ (exists (s3 : list char_p) (v' : prefix * instr),
               in_grammar (alts (x2 ++ x4)) ((s1 ++ s2) ++ s3) v')).
  intro. t. apply H6. exists x5. exists x6. rewrite in_alts_g.
  apply in_alt_r. rewrite in_alts_g in H0. apply H0. specialize (IHl H0).
  assert (~ (exists (s2 : list char_p) (v' : prefix * instr),
           in_grammar (alts (x ++ x1)) (s1 ++ s2) v')).
  intro. t. apply H4. exists x5. exists x6. rewrite in_alts_g. apply in_alt_r.
  apply in_alts_g. auto. specialize (IHl H1). t. subst. auto. t. subst. clear H1.
  assert (exists pre, exists g, x0 = (pre $ g) /\ 
                                star_free pre = true /\ 
                                check_determ g = true /\ 
                                check_pfx pre g = true) ; 
    [ idtac | t ; subst ; eapply check_pfx_determ' ; eauto].
  generalize (splits_in x0 x2 x1). rewrite <- H. intros.
  unfold instruction_grammar_list in H1.
  repeat rewrite in_app in H1. 
  repeat rewrite in_map_iff in H1.
  Ltac foo := 
    match goal with
      | [ H : _ \/ _ |- _ ] => 
        destruct H ; [t ; subst ; econstructor ; econstructor ; split ; eauto ; split | 
                      foo ]
      | _ => idtac
    end.
  foo. apply star_free_prefix_grammar_rep. split. apply instr_grammars_determ. auto.
  apply check_all_rep ; auto.
  apply star_free_prefix_grammar_rep_or_repn. split. apply instr_grammars_determ. auto.
  apply check_all_rep_or_repn ; auto.
  apply star_free_prefix_grammar_lock_with_op_override. split. 
  apply instr_grammars_determ ; auto. apply check_all_lock_with_op_override ; auto.
  apply star_free_prefix_grammar_lock_no_op_override. split.
  apply instr_grammars_determ ; auto. apply check_all_lock_no_op_override ; auto.
  apply star_free_prefix_grammar_seg_with_op_override. split.
  apply instr_grammars_determ ; auto 10. apply check_all_seg_with_op_override ; auto.
  apply star_free_prefix_grammar_seg_op_override. split.
  apply instr_grammars_determ ; auto 10. apply check_all_seg_op_override ; auto.
  t ; subst ; econstructor ; econstructor ; split ; eauto ; split.
  apply star_free_prefix_grammar_seg_override. split.
  apply instr_grammars_determ ; auto 10. apply check_all_seg_override ; auto.
Qed.
  
(** Now I want to relate the [simple_grammar] to the results above.
    Note that both the DFA and the simpler grammar assume that at
    least one byte is consumed.  So we have to establish that indeed,
    the grammars require at least one byte on all paths.  While I'm
    at it, I calculate the maximum number of bits on any path (but
    haven't bothered to prove it correct.) *)
Require Import Arith.Compare_dec.

Definition max(n1 n2:nat) : nat := if le_lt_dec n1 n2 then n2 else n1.
Definition min(n1 n2:nat) : nat := if le_lt_dec n1 n2 then n1 else n2.

(** Maximum number of bits consumed by a grammar.  Undefined if the
    grammar includes [Star_p]. *)
Fixpoint max_bit_count t (p:grammar t) : option nat := 
  match p with 
    | Eps => Some 0
    | Zero _ => Some 0
    | Char _ => Some 1
    | Any => Some 1
    | Cat _ _ p1 p2 => 
      match max_bit_count p1, max_bit_count p2 with
        | Some n1, Some n2 => Some (n1 + n2)
        | _,_ => None
      end
    | Map _ _ _ p => max_bit_count p
    | Xform _ _ _ p => max_bit_count p
    | Alt _ _ p1 p2 => 
      match max_bit_count p1, max_bit_count p2 with
        | Some n1, Some n2 => Some (max n1 n2)
        | _,_ => None
      end
    | Star _ _ => None
  end%nat.

Lemma max_count_corr : forall t (p: grammar t) s v,
  in_grammar p s v -> 
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

Lemma max_instruction_bits: 
  max_bit_count instruction_grammar = Some 104.
Proof.
  vm_compute; auto.
Qed.

(** Minimum number of bits consumed by the grammar.  This is undefined
    when the grammar is [Zero_p].  Or rather, we use [None] to represent
    "minimum infinity" to get this to work out properly. *)
Fixpoint min_bit_count t (p:grammar t) : option nat := 
  match p with 
    | Eps => Some 0
    | Zero _ => None
    | Char _ => Some 1
    | Any => Some 1
    | Cat _ _ p1 p2 => 
      match min_bit_count p1, min_bit_count p2 with
        | Some n1, Some n2 => Some (n1 + n2)
        | _,_ => None
      end
    | Map _ _ _ p => min_bit_count p
    | Xform _ _ _ p => min_bit_count p
    | Alt _ _ p1 p2 => 
      match min_bit_count p1, min_bit_count p2 with
        | Some n1, Some n2 => Some (min n1 n2)
        | Some n1, None => Some n1
        | None, Some n1 => Some n1
        | _, _ => None
      end
    | Star _ _ => Some 0
  end%nat.

(** If [s] is in the domain of [p], then [length s] is at least [min_bit_count p]. *)
Lemma min_count_corr : forall t (p:grammar t) s v,
  in_grammar p s v -> 
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

(** The [instruction_grammar] always consumes at least 8 bits.  *)
Lemma min_instruction_bits : 
  min_bit_count instruction_grammar = Some 8.
Proof.
  vm_compute ; auto.
Qed.

(** Probably goes in the Parser file.  In fact, this whole file would be
    much simpler if I could just calculate derivatives directly on grammars,
    instead of having to convert them to regexps.  *)
Ltac pinvopt := 
  match goal with 
    | [ H : in_grammar (OptAlt _ _) _ _ |- _ ] => rewrite <- opt_alt_corr in H
    | [ H : in_grammar (OptCat _ _) _ _ |- _ ] => rewrite <- opt_cat_corr in H
    | [ H : in_grammar (OptMap _ _ _) _ _ |- _] => rewrite <- opt_map_corr in H
    | [ H : in_grammar (OptXform _ _) _ _ |- _] => rewrite <- opt_xform_corr in H
    | [ |- in_grammar (OptAlt _ _) _ _ ] => rewrite <- opt_alt_corr
    | [ |- in_grammar (OptCat _ _) _ _ ] => rewrite <- opt_cat_corr
    | [ |- in_grammar (OptMap _ _ _) _ _ ] => rewrite <- opt_map_corr
    | [ |- in_grammar (OptXform _ _) _ _ ] => rewrite <- opt_xform_corr
    | _ => pinv
  end.

Lemma null_emp t (g:grammar t) cs v : 
  in_grammar (null g) cs v -> cs = nil.
Proof.
  induction g ; simpl ; intros ; repeat pinvopt ; eauto.  
  rewrite (IHg1 _ _ H) ; rewrite (IHg2 _ _ H0). auto.
Qed.

Lemma null_corr t (g:grammar t) cs v : 
  in_grammar (null g) cs v -> in_grammar g nil v.
Proof.
  induction g ; simpl ; intros ; repeat pinvopt ; eauto.
Qed.

Lemma star_inv t (g:grammar t) s v : 
  in_grammar (Star g) s v -> 
  ((s = nil /\ v = nil) \/ 
       (exists s1, exists s2, exists v1:interp t, exists v2:interp (List_t t),
         s1 <> nil /\ s = s1 ++ s2 /\ v = v1::v2 /\ 
         in_grammar g s1 v1 /\ in_grammar (Star g) s2 v2)).
Proof.
  intros. inversion H. subst. left ; auto. 
  repeat 
  match goal with 
    | [ H : existT ?f ?t ?x = existT ?f ?t ?y |- _ ] => 
      generalize (inj_pairT2 _ f t x y H) ; clear H
  end. intros ; subst ; auto.
  right.
  repeat 
  match goal with 
    | [ H : existT ?f ?t ?x = existT ?f ?t ?y |- _ ] => 
      generalize (inj_pairT2 _ f t x y H) ; clear H
  end. intros ; subst. exists s1. exists s2. exists v1. exists v2. auto.
Qed.

Lemma null_corr' t (g:grammar t) v : 
  in_grammar g nil v -> in_grammar (null g) nil v.
Proof.
  induction g ; intros ; simpl ; auto ; repeat pinvopt ; try discriminate H ; eauto.
  generalize (nil_is_nil_app_nil _ _ H1). t. subst. rewrite H1. econstructor ; eauto.
  econstructor ; eauto. generalize (star_inv H). intros. destruct H0 ; t.
  subst ; auto. generalize (nil_is_nil_app_nil _ _ H1). t ; subst. 
  congruence.
Qed.

Lemma deriv_corr t (g:grammar t) c v cs : 
  in_grammar (deriv g c) cs v <-> in_grammar g (c::cs) v.
Proof.
  induction g ; simpl ; intros ; split ; intros ; repeat pinvopt ; eauto.
  discriminate H. destruct (char_dec c0 c) ; subst ; repeat pinv ; eauto.
  destruct (char_dec c c) ; try congruence. econstructor ; eauto. 
  econstructor ; eauto. apply IHg1 ; eauto. auto. auto.
  generalize (null_emp _ H). generalize (null_corr _ H). intros.
  econstructor. eauto. apply IHg2 ; eauto. subst ; auto. auto. 
  destruct x. simpl in *. subst. specialize (IHg2 c x2 cs).
  econstructor ; eauto. pinvopt. eapply InAlt_r. pinvopt.
  econstructor. eapply null_corr'. eauto. eapply IHg2. eauto. auto.
  eauto. eauto. auto. simpl in H1 ; injection H1 ; clear H1 ; t ; subst.
  econstructor. pinvopt. eapply InAlt_l. pinvopt. econstructor.
  apply IHg1 ; eauto. eauto. auto. eauto. eauto. eauto.
  eapply InAlt_l. eapply IHg1 ; eauto. auto.
  eapply InAlt_r ; eauto. eapply IHg2 ; eauto.
  eapply InAlt_l ; eauto. eapply IHg1 ; eauto. eapply InAlt_r ; eauto.
  eapply IHg2 ; eauto. eapply InStar_cons. specialize (IHg c x2 x0).
  eapply IHg. eauto. eauto. congruence. auto. auto.
  generalize (star_inv H). clear H. t. destruct H ; t. congruence. subst.
  destruct x ; try congruence. simpl in H0 ; injection H0 ; intros ; subst ;
  clear H0. econstructor. pinvopt. econstructor. eapply IHg ; eauto.
  eauto. auto. eauto. auto. econstructor. eapply IHg ; eauto. auto.
  econstructor. eapply IHg ; eauto. auto. econstructor ; eauto.
  eapply IHg ; eauto. econstructor ; eauto ; eapply IHg ; eauto.
Qed.  

Fixpoint derivs t (g:grammar t) (cs : list char_p) : grammar t := 
  match cs with 
    | nil => g
    | c::cs' => derivs (deriv g c) cs'
  end.

Lemma derivs_corr t v cs2 cs1 (g:grammar t) : 
  in_grammar (derivs g cs1) cs2 v <-> in_grammar g (cs1 ++ cs2) v.
Proof.
  induction cs1 ; simpl ; intros ; split ; intros ; auto.
  eapply deriv_corr. eapply IHcs1. auto. eapply IHcs1.
  eapply deriv_corr. auto.
Qed.

Lemma in_derivs_app t (x1 x2:list char_p) (r:grammar t) (v:interp t): 
  in_grammar (derivs (derivs r x1) x2) nil v -> 
  in_grammar r (x1 ++ x2) v.
Proof.
  intros. eapply derivs_corr. generalize (derivs r x1) H ; clear H ; intros.
  replace (x2) with (x2 ++ nil). apply derivs_corr. auto. rewrite app_nil_end.
  auto.
Qed.  

Fixpoint extract_nil t (g:grammar t) : list (interp t) := 
  match g in grammar t return list (interp t) with
    | Eps => tt::nil
    | Zero t => nil
    | Char c => nil
    | Any => nil
    | Cat t1 t2 g1 g2 => cross_prod (extract_nil g1) (extract_nil g2)
    | Alt t1 t2 g1 g2 => 
      (List.map (fun x => inl _ x) (extract_nil g1)) ++ 
      (List.map (fun x => inr _ x) (extract_nil g2))
    | Star t g => nil::nil
    | Map t1 t2 f g => List.map f (extract_nil g)
    | Xform t1 t2 x g => List.map (xinterp x) (extract_nil g)
  end.                                                     

Lemma extract_nil_corr t (g:grammar t) v :
  in_grammar g nil v <-> In v (extract_nil g).
Proof.  
  induction g; simpl ; intros ; split ; intro ; repeat pinvopt ; auto ; 
  try (congruence || contradiction).
  generalize (nil_is_nil_app_nil _ _ H1). clear H1 ; t. subst.
  specialize (IHg1 x1). specialize (IHg2 x2). destruct IHg1. destruct IHg2.
  clear H2 H4. specialize (H1 H). specialize (H3 H0). clear H H0.
  generalize H1 H3 ; clear H1 H3. generalize (extract_nil g1) (extract_nil g2).
  clear g1 g2. induction l ; simpl ; intros ; auto. destruct H1.
  subst. apply in_app. left. induction l0 ; simpl in *. auto.
  destruct H3. subst. left ; auto. specialize (IHl0 H). auto. 
  apply in_app ; right. auto. destruct v as [x1 x2].
  specialize (IHg1 x1). specialize (IHg2 x2). destruct IHg1. destruct IHg2.
  clear H0 H2. replace (@nil char_p) with (@nil char_p ++ nil).
  econstructor ; eauto. apply H1. generalize (extract_nil g1) H.
  induction l ; simpl ; intros ; auto. rewrite in_app in H0. destruct H0.
  left. generalize (extract_nil g2) H0. induction l0 ; simpl ; intros ; 
  try contradiction. destruct H2 ; auto. injection H2 ; intros ; subst ; auto.
  right ; auto. apply H3. generalize (extract_nil g1) (extract_nil g2) H.
  induction l ; simpl ; intros ; try contradiction. rewrite in_app in H0.
  destruct H0. generalize H0 ; clear H0. induction l0 ; simpl ; intros ;
  try contradiction. destruct H0. left. injection H0 ; intros ; subst ; auto.
  right. auto. auto. auto. specialize (IHg1 x). destruct IHg1.
  specialize (H0 H). rewrite in_app. left. generalize (extract_nil g1) H0.
  induction l ; simpl ; intros ; try contradiction. destruct H2 ; [ left ; subst ; auto 
  | right ]. auto.
  specialize (IHg2 x). destruct IHg2. specialize (H0 H). apply in_app.
  right. generalize (extract_nil g2) H0. induction l ; simpl ; intros ;  
  try contradiction. destruct H2 ; [left ; subst ; auto | right ; auto].
  rewrite in_app in H. destruct v. eapply InAlt_l ; eauto. 
  destruct H. specialize (IHg1 i). destruct IHg1. apply H1. clear H0 H1 IHg2.
  generalize (extract_nil g1) H. induction l ; simpl ; intros ; try contradiction.
  destruct H0 ; auto. injection H0 ; intros ; subst ; auto. assert False.
  generalize (extract_nil g2) H. induction l ; simpl ; intros ; auto.
  destruct H0 ; auto. discriminate. contradiction. clear IHg1. specialize (IHg2 i).
  destruct IHg2. eapply InAlt_r ; eauto. apply H1. clear H0 H1. destruct H.
  assert False. generalize (extract_nil g1) H. induction l ; simpl ; intros ; auto. 
  destruct H0 ; auto. discriminate. contradiction.
  generalize (extract_nil g2) H. induction l ; simpl ; intros ; try contradiction.
  destruct H0. injection H0 ; intros ; subst. left ; auto. right ; auto.
  generalize (star_inv H). clear H. t. destruct H ; t ; subst ; auto.
  generalize (nil_is_nil_app_nil _ _ H0). t ; subst. contradiction.
  specialize (IHg x). destruct IHg. apply in_map. auto.
  assert (exists x, v = i x /\ In x (extract_nil g)). 
  generalize (extract_nil) H. 
  induction l ; simpl ; t ; try contradiction. destruct H0 ; eauto. 
  specialize (IHl H0). t. subst. eauto. t. subst.
  specialize (IHg x). destruct IHg. specialize (H2 H1).  
  econstructor ; eauto.
  specialize (IHg x0). destruct IHg. apply in_map. eauto.
  assert (exists z, v = xinterp x z /\ In z (extract_nil g)).
  generalize (extract_nil g) H. induction l ; simpl ; t. contradiction.
  destruct H0 ; eauto. specialize (IHl H0). t. eauto. t. subst.
  econstructor ; eauto. apply IHg. eauto.
Qed.

(*
(** If [apply_null] on [derivs p cs] is [nil], then there's no value associated
   with [cs] in the denotation of [p]. *)
Lemma apply_null_nil : 
  forall (c:ctxt_t) t (p:grammar t) (r:regexp t) cs,
    c = snd (parser2regexp p) ->
    r = deriv_parse' (fst (parser2regexp p)) cs ->
    forall (H:wf_regexp c r),
    apply_null c r H = nil -> 
    forall v, ~ in_grammar p cs v.
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
*)

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

(*
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
      ~ in_grammar p (flat_map byte_explode s1) v
  | Some (v,bytes3) => 
    exists bytes4,
      bytes2 = bytes4 ++ bytes3 /\ 
      in_grammar p (flat_map byte_explode (bytes1 ++ bytes4)) v /\
      (forall bytes5 bytes6,
        bytes2 = bytes5 ++ bytes6 -> 
        length bytes5 < length bytes4 -> 
        forall v, ~ in_grammar p (flat_map byte_explode (bytes1 ++ bytes5)) v)
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
*)

Lemma min_none : 
  forall t (g:grammar t),
    min_bit_count g = None -> extract_nil g = nil.
Proof.
  induction g ; simpl ; intros ; try congruence.
  destruct (min_bit_count g1) ; try congruence ; destruct (min_bit_count g2) ;  
  try congruence. rewrite IHg2. generalize (extract_nil g1). induction l ; auto. auto.
  rewrite IHg1 ; auto. rewrite IHg1 ; auto. destruct (min_bit_count g1) ; 
  destruct (min_bit_count g2) ; try congruence. rewrite IHg1 ; auto ; rewrite IHg2 ; auto.
  rewrite IHg ; auto. rewrite IHg ; auto.
Qed.

(** If the [min_bit_count] of [p] is greater than 0, then there's no 
    way that [apply_null] will succeed. *)
Lemma min_count_not_null : 
  forall t (p:grammar t) n,
    min_bit_count p = Some (S n) -> 
    extract_nil p = nil.
Proof.
  induction p ; simpl ; intros ; try congruence.
  remember (min_bit_count p1) as e1. remember (min_bit_count p2) as e2.
  destruct e1 ; try congruence. destruct e2 ; try congruence.
  destruct n0 ; destruct n1 ; simpl in * ; try congruence. 
  specialize (IHp2 _ (eq_refl _)). 
  rewrite IHp2. generalize (extract_nil p1). induction l ; simpl ; auto.
  specialize (IHp1 _ (eq_refl _)). rewrite IHp1. auto.
  specialize (IHp1 _ (eq_refl _)). rewrite IHp1. auto.
  remember (min_bit_count p1) as e1. remember (min_bit_count p2) as e2. 
  destruct e1 ; destruct e2 ; try congruence.
  unfold min in H. destruct (le_lt_dec n0 n1) ; injection H ; intros ; subst.
  specialize (IHp1 _ (eq_refl _)). rewrite IHp1.
  destruct n1. assert False. omega. contradiction. specialize (IHp2 _ (eq_refl _)).
  rewrite IHp2. auto. rewrite (IHp2 _ (eq_refl _)).
  destruct n0. assert False. omega. contradiction. rewrite (IHp1 _ (eq_refl _)). auto.
  injection H ; intros ; subst. rewrite (IHp1 _ (eq_refl _)). simpl. rewrite min_none ;
  auto. erewrite IHp2 ; eauto. rewrite min_none ; auto. erewrite IHp ; eauto.
  erewrite IHp ; eauto.
Qed.

(*XXXXXXXXX*)

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
  in_grammar (alts dir_cflow) s ins -> 
  dir_cflow_instr (mkPrefix None None false false) ins = true.
Proof.
  unfold dir_cflow. simpl ; 
  unfold dir_near_JMP_p, dir_near_Jcc_p, dir_near_CALL_p, never.
  intros. (repeat pinv) ; simpl ; unfold no_prefix ; simpl ; auto ; destruct x ; auto.
Qed.

(** Show that the [dir_cflow] parsers are sub-parsers of the [instruction_parser]. *)
Lemma dir_cflow_parser_subset : 
  forall s v, in_grammar (alts dir_cflow) s v -> 
    in_grammar instruction_parser s (mkPrefix None None false false, v).
Proof.
  intros. replace s with (nil ++ s) ; auto. 
  remember (mkPrefix None None false false) as p.
  assert (in_grammar prefix_parser_nooverride nil p). 
  unfold prefix_parser_nooverride. unfold option_perm2. subst.
  repeat econstructor. clear Heqp. unfold dir_cflow in H. simpl in H.
  Transparent instruction_parser.
  unfold instruction_parser. unfold instruction_parser_list. 
  Opaque instruction_parser. eapply in_alts_app. left. eapply in_map_alts.
  econstructor ; eauto. clear H0. repeat pinv ; unfold instr_parsers_nosize_pre ; simpl.
  repeat 
  match goal with 
    | [ |- in_grammar (JMP_p |+| _) _ _ ] => eapply Alt_left_pi
    | [ |- in_grammar (_ |+| _) _ _ ] => eapply Alt_right_pi
  end.
  unfold dir_near_JMP_p, JMP_p in *. pinv. destruct H.
  eapply Alt_left_pi. auto. eapply Alt_right_pi. eapply Alt_left_pi. auto.
  repeat 
  match goal with 
    | [ |- in_grammar (Jcc_p |+| _) _ _ ] => eapply Alt_left_pi
    | [ |- in_grammar (_ |+| _) _ _ ] => eapply Alt_right_pi
  end.
  unfold dir_near_Jcc_p, Jcc_p in *. auto.
  repeat 
  match goal with 
    | [ |- in_grammar (CALL_p |+| _) _ _ ] => eapply Alt_left_pi
    | [ |- in_grammar (_ |+| _) _ _ ] => eapply Alt_right_pi
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
        in_grammar (alts dir_cflow) (flat_map byte_explode bytes1) ins /\ 
        in_grammar instruction_parser (flat_map byte_explode bytes1) (pfx,ins) /\ 
        n = length bytes1 /\ 
        bytes = bytes1 ++ (List.map nat_to_byte nats2) /\ 
        dir_cflow_instr pfx ins = true /\
        (forall ts3 ts4,
          (length ts3 < length bytes1)%nat -> 
          bytes = ts3 ++ ts4 -> 
          forall v0, ~ in_grammar (alts dir_cflow) (flat_map byte_explode ts3) v0).
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
