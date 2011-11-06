(* Copyright (c) 2010-2011.
   Greg Morrisett, Gang Tan, Joseph Tassarotti, Jean-Baptiste Tristan, Edward Gan.
   All rights reserved. *)

(** Broke out the reasoning for the "masked jumps" used in the NaCL verifier
    so I don't have to wait for long compile times on DFACorrectness.v
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
Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.
Require ExtrOcamlNatInt.
Import X86_PARSER_ARG.
Import X86_PARSER.
Import X86_BASE_PARSER.
Import X86Syntax.
Require Import DFACorrectness.
Hint Constructors in_parser.

Import ABSTRACT_MAKE_DFA.

Lemma nacl_jmp_parser_splits' : 
  forall s v, 
    in_parser (alts nacljmp_mask) (flat_map byte_explode s) v -> 
    exists s1, exists s2, exists r,
      r <> ESP /\ 
      flat_map byte_explode s = s1 ++ s2 /\
      in_parser (nacl_MASK_p r) s1 (fst v) /\ 
      in_parser (nacl_JMP_p r |+| nacl_CALL_p r) s2 (snd v).
Proof.
  unfold nacljmp_mask. unfold nacljmp_p. simpl ; unfold never. intros. 
  repeat pinv ; simpl ; 
  econstructor ; econstructor ; econstructor ; repeat split ; eauto ; try congruence ;
  match goal with 
    | [ H : in_parser (nacl_JMP_p _) _ _ |- _ ] => eapply Alt_left_pi
    | [ H : in_parser (nacl_CALL_p _) _ _ |- _ ] => eapply Alt_right_pi
  end ; auto.
Qed.

Lemma byte_explode_bits b : 
  exists b1,exists b2,exists b3,exists b4,exists b5,exists b6,exists b7,exists b8,
    byte_explode b = b1::b2::b3::b4::b5::b6::b7::b8::nil.
Proof.
  unfold byte_explode. repeat econstructor.
Qed.

Local Open Scope nat_scope.
Lemma split_bytes_n : 
  forall n bs x1 x2,
    flat_map byte_explode bs = x1 ++ x2 ->
    length x1 = n * 8 -> 
    exists b1, exists b2, 
      bs = b1 ++ b2 /\ flat_map byte_explode b1 = x1 /\ flat_map byte_explode b2 = x2.
Proof.
  induction n ; simpl ; intros. destruct x1. simpl in *. exists nil. exists bs.
  simpl. auto. simpl in H0. congruence.

  destruct x1. simpl in H0 ; assert False ; [omega | contradiction].
  destruct x1. simpl in H0 ; assert False ; [omega | contradiction].
  destruct x1. simpl in H0 ; assert False ; [omega | contradiction].
  destruct x1. simpl in H0 ; assert False ; [omega | contradiction].
  destruct x1. simpl in H0 ; assert False ; [omega | contradiction].
  destruct x1. simpl in H0 ; assert False ; [omega | contradiction].
  destruct x1. simpl in H0 ; assert False ; [omega | contradiction].
  destruct x1. simpl in H0 ; assert False ; [omega | contradiction].
  simpl in H0. assert (length x1 = n*8). omega. destruct bs. simpl in H. congruence.
  replace (flat_map byte_explode (i :: bs)) with 
    (byte_explode i ++ flat_map byte_explode bs) in H; auto.
  generalize (byte_explode_bits i). t. rewrite H2 in *.
  injection H ; clear H ; intros ; subst.
  specialize (IHn bs x1 x2 H H1). t. 
  exists (i::x). exists x0. replace (flat_map byte_explode (i :: x)) with
  (byte_explode i ++ (flat_map byte_explode x)) ; auto. rewrite H2.
  split. simpl. rewrite H3. auto. split. rewrite H4. auto. auto.
Qed.

Lemma nacl_jmp_parser_splits : 
  forall bs v,
    in_parser (alts nacljmp_mask) (flat_map byte_explode bs) v -> 
    exists b1, exists b2, exists r,
      r <> ESP /\ 
      bs = b1 ++ b2 /\ 
      in_parser (nacl_MASK_p r) (flat_map byte_explode b1) (fst v) /\ 
      in_parser (nacl_JMP_p r |+| nacl_CALL_p r) (flat_map byte_explode b2) (snd v).
Proof.
  intros. generalize (nacl_jmp_parser_splits' _ H). t.
  assert (length x = 24). unfold nacl_MASK_p in H2. unfold bitsleft in H2.
  simpl in H2. repeat pinv ; simpl ; auto.
  generalize (split_bytes_n 3 _ _ _ H1 H4). t. exists x2. exists x3. exists x1.
  repeat split ; auto. rewrite H6. auto. rewrite H7. auto.
Qed.

Import CheckDeterministic.

Lemma byte2token_app xs n1 n2 :
  List.map byte2token xs = n1 ++ n2 -> 
  exists b1, exists b2, 
    xs = b1 ++ b2 /\ List.map byte2token b1 = n1 /\ List.map byte2token b2 = n2.
Proof.
  induction xs. simpl. intros. generalize (nil_is_nil_app_nil _ _ H). t. subst.
  exists nil ; exists nil ; auto.
  simpl ; intros ; destruct n1. simpl in *. destruct n2 ; try congruence.
  injection H ; clear H ; intros. specialize (IHxs nil n2 H). t. subst.
  exists x. exists (a::x0). assert (x = nil). destruct x ; auto. simpl in H2 ; 
  congruence. subst. simpl. auto. simpl in *. injection H ; clear H ; intros.
  specialize (IHxs n1 n2 H). t. exists (a::x). exists x0. rewrite H1.
  split ; auto. simpl. split. rewrite H0. rewrite H2. auto. auto.
Qed.

Lemma nat2bools_byte2token_is_byte_explode xs : 
  flat_map nat2bools (List.map byte2token xs) = flat_map byte_explode xs.
Proof.
  induction xs. auto. replace (flat_map byte_explode (a::xs)) with 
  (byte_explode a ++ (flat_map byte_explode xs)) ; auto.
  replace (flat_map nat2bools (List.map byte2token (a::xs))) with
    (nat2bools (byte2token a) ++ (flat_map nat2bools (List.map byte2token xs))) ; auto.
  rewrite IHxs. replace (nat2bools (byte2token a)) with (byte_explode a) ; auto.
  clear IHxs. unfold byte_explode. unfold nat2bools. replace (Z_of_nat (byte2token a))
  with (Word.unsigned a) ; auto. unfold byte2token.
  rewrite inj_Zabs_nat. unfold Word.unsigned. generalize (Word.intrange _ a).
  intros. rewrite (Zabs_eq _).  auto. omega.
Qed.

Lemma reg_parser r s : 
  in_parser (bitslist (register_to_bools r)) s tt -> 
  in_parser reg s r.
Proof.
  unfold reg, field ; destruct r ; simpl ; intros ; repeat pinv ; 
  repeat econstructor ; eauto.
Qed.

Lemma mask_parser s : 
  in_parser (bitslist (int_to_bools safeMask)) s tt -> 
  in_parser byte s safeMask.
Proof.
  simpl. unfold byte. unfold field. simpl. intros.
  repeat pinv. repeat econstructor.
Qed.

Lemma nacl_mask_subset r s i : 
  in_parser (nacl_MASK_p r) s i -> 
  in_parser instruction_parser s (mkPrefix None None false false, i).
Proof.
  unfold nacl_MASK_p. intros.
  unfold instruction_parser. unfold instruction_parser_list. eapply in_alts_app.
  left. eapply in_map_alts. replace s with (nil ++ s) ; auto. econstructor ; eauto.
  unfold prefix_parser_nooverride. unfold option_perm2. econstructor ; eauto.
  eapply Alt_left_pi. econstructor ; eauto. auto. unfold instr_parsers_nosize_pre.
  simpl. repeat  match goal with 
      | [ |- in_parser ((AND_p _) |+| _) _ _ ] => eapply Alt_left_pi 
      | [ |- in_parser (_ |+| _) _ _ ] => eapply Alt_right_pi
    end.
  unfold AND_p. unfold logic_or_arith_p. eapply Alt_right_pi. eapply Alt_left_pi.
  unfold bitsleft in H. repeat 
  match goal with 
    | [ H : in_parser (_ @ _) _ _ |- _ ] => generalize (inv_map_pi H) ; clear H ; t
    | [ H : in_parser (_ $ _) _ _ |- _ ] => generalize (inv_cat_pi H) ; clear H ; t
  end ; subst.
  econstructor. econstructor. econstructor. eauto. econstructor. econstructor.
  eauto. econstructor. econstructor. eauto. econstructor. econstructor. eauto.
  econstructor. eapply reg_parser. destruct x21. eauto. eapply mask_parser.
  destruct x22. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto. eauto. eauto. eauto. simpl. auto.
Qed.

Lemma nacl_jump_subset r s i : 
  in_parser (nacl_JMP_p r |+| nacl_CALL_p r) s i -> 
  in_parser instruction_parser s (mkPrefix None None false false, i).
Proof.
  intros. unfold instruction_parser. unfold instruction_parser_list. eapply in_alts_app.
  left. eapply in_map_alts. replace s with (nil ++ s) ; auto. econstructor ; eauto.
  unfold prefix_parser_nooverride, option_perm2. econstructor ; eauto.
  eapply Alt_left_pi ; eauto. econstructor ; eauto. auto.
  unfold instr_parsers_nosize_pre. simpl. repeat pinv.
  repeat match goal with 
           | [ |- in_parser (JMP_p |+| _) _ _ ] => eapply Alt_left_pi
           | [ |- in_parser (_ |+| _) _ _ ] => eapply Alt_right_pi
         end. 
  unfold nacl_JMP_p, JMP_p in *. eapply Alt_right_pi. eapply Alt_right_pi.
  eapply Alt_left_pi. unfold bitsleft in H. repeat
  match goal with 
    | [ H : in_parser (_ @ _) _ _ |- _ ] => generalize (inv_map_pi H) ; clear H ; t
    | [ H : in_parser (_ $ _) _ _ |- _ ] => generalize (inv_cat_pi H) ; clear H ; t
  end ; subst.
  econstructor. econstructor. econstructor. eapply H3. econstructor. econstructor.
  eauto. unfold ext_op_modrm2. econstructor. repeat eapply Alt_right_pi.
  econstructor. eauto. econstructor. eauto. unfold rm11. econstructor.
  eapply reg_parser. destruct x18. eauto. eauto. eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto. auto. eauto. eauto. simpl. auto.
  repeat match goal with 
           | [ |- in_parser (CALL_p |+| _) _ _ ] => eapply Alt_left_pi
           | [ |- in_parser (_ |+| _) _ _ ] => eapply Alt_right_pi
         end. 
  unfold nacl_CALL_p, CALL_p in *. eapply Alt_right_pi. 
  eapply Alt_left_pi. unfold bitsleft in H. repeat
  match goal with 
    | [ H : in_parser (_ @ _) _ _ |- _ ] => generalize (inv_map_pi H) ; clear H ; t
    | [ H : in_parser (_ $ _) _ _ |- _ ] => generalize (inv_cat_pi H) ; clear H ; t
  end ; subst.
  econstructor. econstructor. econstructor. eapply H3. econstructor. econstructor.
  eauto. unfold ext_op_modrm2. econstructor. repeat eapply Alt_right_pi.
  econstructor. eauto. econstructor. eauto. unfold rm11. econstructor.
  eapply reg_parser. destruct x18. eauto. eauto. eauto. eauto. eauto. eauto.
  eauto. eauto. eauto. eauto. auto. eauto. eauto. simpl. auto.
Qed.

Lemma nacl_jmp_parser_inv r s1 s2 i1 i2: 
  r <> ESP -> 
  in_parser (nacl_MASK_p r) s1 i1 -> 
  in_parser (nacl_JMP_p r |+| nacl_CALL_p r) s2 i2 -> 
  nacljmp_mask_instr (mkPrefix None None false false) i1 
                     (mkPrefix None None false false) i2 = true.
Proof.
  unfold nacl_MASK_p, nacl_JMP_p, nacl_CALL_p ; intros. 
  repeat pinv ; unfold nacljmp_mask_instr ; simpl ; destruct (register_eq_dec r ESP) ; 
  try congruence ; destruct (register_eq_dec r r) ; try congruence ; auto.
Qed.

Lemma nacljmp_dfa_corr1 : 
  forall (d:DFA),
    abstract_build_dfa 256 nat2bools 400 (par2rec (alts nacljmp_mask)) = Some d -> 
    forall (bytes:list int8) (n:nat) (nats2:list nat),
      dfa_recognize 256 d (List.map byte2token bytes) = Some (n,nats2) -> 
      exists bytes1, exists pfx1:prefix, exists ins1:instr, exists bytes2,
        exists pfx2:prefix, exists ins2:instr,
        in_parser (alts nacljmp_mask) (flat_map byte_explode (bytes1 ++ bytes2))
        (ins1,ins2) /\
        in_parser instruction_parser (flat_map byte_explode bytes1) (pfx1,ins1) /\ 
        in_parser instruction_parser (flat_map byte_explode bytes2) (pfx2,ins2) /\ 
        n = length (bytes1 ++ bytes2) /\ 
        bytes = bytes1 ++ bytes2 ++ (List.map nat_to_byte nats2) /\ 
        nacljmp_mask_instr pfx1 ins1 pfx2 ins2 = true /\
        (forall ts3 ts4,
          (length ts3 < length (bytes1 ++ bytes2))%nat -> 
          bytes = ts3 ++ ts4 ->
          forall v0, ~ in_parser (alts nacljmp_mask) (flat_map byte_explode ts3) v0).
Proof.
  intros. subst. rewrite build_dfa_eq in H.
  generalize (dfa_recognize_corr _ _ _ _ H (List.map byte2token bytes)
    (bytesLt256 _)). clear H. rewrite H0. clear H0. mysimp.
  generalize (byte2token_app _ _ _ H). t. subst.
  rewrite (nat2bools_byte2token_is_byte_explode _) in H1.
  generalize (nacl_jmp_parser_splits _ H1). clear H1. t. destruct x0. simpl in *.
  exists x. exists (mkPrefix None None false false). exists i.
  exists x3. exists (mkPrefix None None false false). exists i0. split.
  rewrite flat_map_app. unfold nacljmp_p. destruct x4 ; try congruence ;
  repeat (try (eapply Alt_left_pi ; econstructor ; eauto ; fail) ; eapply Alt_right_pi).
  split. apply (nacl_mask_subset H3). split. eapply (nacl_jump_subset H4). 
  split. rewrite H1. rewrite map_length. auto. split. subst. rewrite app_assoc.
  assert (x2 = List.map nat_to_byte (List.map byte2token x2)) ; [ idtac | congruence].
  rewrite n2bs. auto. split. eapply nacl_jmp_parser_inv ; eauto.
  intros. rewrite H1 in H2. specialize (H2 (List.map byte2token ts3)
  (List.map byte2token ts4)). repeat rewrite map_length in H2.
  specialize (H2 H5). subst. rewrite H6 in H2. rewrite map_app in H2.
  specialize (H2 (eq_refl _)). rewrite nat2bools_byte2token_is_byte_explode in H2.
  intro. apply (H2 v0 H1).
Qed.

Lemma flat_map_nil_is_nil x : 
  flat_map byte_explode x = nil -> x = nil.
Proof.
  induction x ; intros. auto. replace (flat_map byte_explode (a :: x))
  with (byte_explode a ++ (flat_map byte_explode x)) in H ; auto.
  generalize (nil_is_nil_app_nil _ _ (eq_sym H)). t.
  clear IHx H H1. assert False ; try contradiction. 
  unfold byte_explode in H0. congruence.
Qed.

(** This should get placed in DFACorrectness and used for the other 2 DFAs. *)
Lemma in_parser_implies_simple_parse
  bytes1 pfx ins bytes2 :
  in_parser instruction_parser (flat_map byte_explode bytes1) (pfx,ins) ->
  simple_parse (bytes1 ++ bytes2) = Some (pfx, ins, bytes2).
Proof.
  unfold simple_parse ; intros.
  Opaque instruction_parser. 
  generalize (@simple_parse'_corr2 
    instruction_parser (bytes1 ++ bytes2) initial_parser_state nil 
    (eq_refl _) (eq_refl _)).
  simpl ; intros. 
  assert (forall s1 s2, nil = s1 ++ s2 -> 
    apply_null (snd (parser2regexp instruction_parser))
          (deriv_parse' (fst (parser2regexp instruction_parser))
             (flat_map byte_explode s1))
          (wf_derivs (snd (parser2regexp instruction_parser))
             (flat_map byte_explode s1)
             (fst (parser2regexp instruction_parser))
             (p2r_wf instruction_parser initial_ctxt)) = nil). intros. clear H0.
  generalize (nil_is_nil_app_nil _ _ H1) ; t ; subst.
  generalize (min_count_not_null _ min_instruction_bits).
  generalize instruction_parser. clear H H1. simpl. intro.
  generalize (apply_null (snd(parser2regexp p)) (fst (parser2regexp p))).
  assert (wf_derivs (snd (parser2regexp p)) nil (fst (parser2regexp p))
    (p2r_wf p initial_ctxt) = p2r_wf p initial_ctxt). 
  apply Coqlib.proof_irrelevance. 
  generalize H. clear H. unfold parser2regexp.
  generalize (p2r_wf p initial_ctxt). intros. rewrite <- H in H0. auto.
  specialize (H0 H1). clear H1.
  destruct (simple_parse' initial_parser_state (bytes1 ++ bytes2)).
  destruct p. t. destruct p. assert (length bytes1 >= length x).
  assert (length bytes1 < length x -> False). intros.
  eapply (H2 bytes1 bytes2 (eq_refl _) H3 _ H). omega.
  assert (exists s2, bytes1 = x ++ s2). generalize bytes1 x H3 H0.
  induction bytes0 ; destruct x0 ; simpl ; intros. exists nil. auto.
  assert False. omega. contradiction. subst. eauto. injection H5 ; clear H5 ; t ; subst.
  assert (length bytes0 >= length x0). omega. specialize (IHbytes0 _ H6 H5). t.
  subst. eauto. t. subst. rewrite app_ass in H0. generalize (app_inv_head _ _ _ H0).
  intros. subst. rewrite flat_map_app in H. generalize (parser_determ H). intros.
  specialize (H4 _ _ (p,i) (eq_refl _) H1). t. injection H5 ; intros.
  rewrite (flat_map_nil_is_nil _ H4). subst.  auto.
  specialize (H0 bytes1 bytes2 (pfx,ins) (eq_refl _)). contradiction.
Qed.

Lemma nacljmp_dfa_corr : 
  forall (d:DFA),
    abstract_build_dfa 256 nat2bools 400 (par2rec (alts nacljmp_mask)) = Some d -> 
    forall (bytes:list int8) (n:nat) (nats2:list nat),
      dfa_recognize 256 d (List.map byte2token bytes) = Some (n, nats2) -> 
      exists bytes1, exists pfx1:prefix, exists ins1:instr, exists bytes2,
        exists pfx2:prefix, exists ins2:instr,
        simple_parse bytes = Some ((pfx1,ins1), bytes2 ++ List.map nat_to_byte nats2) /\
        simple_parse (bytes2 ++ List.map nat_to_byte nats2) = 
            Some ((pfx2,ins2), List.map nat_to_byte nats2) /\
        nacljmp_mask_instr pfx1 ins1 pfx2 ins2 = true /\
        n = length (bytes1 ++ bytes2) /\ 
        bytes = bytes1 ++ bytes2 ++ (List.map nat_to_byte nats2).
Proof.
  intros d H bytes n nats2 H1.
  generalize (@nacljmp_dfa_corr1 d H bytes n nats2 H1). t.
  exists x. exists x0. exists x1. exists x2. exists x3. exists x4. repeat split ; auto.
  rewrite H5. eapply in_parser_implies_simple_parse ; auto.
  eapply in_parser_implies_simple_parse ; auto.
Qed.

Lemma nacljmp_mask_dfa_length : 
  forall (d:DFA), 
    (* Need to use abstract_build_dfa for the same reason as above I believe *)
    abstract_build_dfa 256 nat2bools 400 (par2rec (alts nacljmp_mask)) = Some d -> 
    forall (bytes:list int8) (n:nat) (nats2:list nat),
      dfa_recognize 256 d (List.map byte2token bytes) = Some (n, nats2) -> 
        (n <= 15). 
Proof.
  intros. apply nacljmp_dfa_corr1 in H0.
   destruct H0. destruct H0.
   destruct H0. destruct H0. 
   destruct H0. destruct H0. 
   destruct H0.
   destruct H1. destruct H2.
   destruct H3.
   assert (max_bit_count (alts nacljmp_mask) = Some 40).
     vm_compute; trivial.
   eapply max_count_corr in H0.
   rewrite H5 in H0.
   rewrite byte_explode_mult_len in H0.
   rewrite H3. omega.
   auto.
Qed.
