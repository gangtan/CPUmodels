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
Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Program.

Require Import Shared.Coqlib.
Require Import Shared.CommonTacs.
Require Import Shared.Bits.
Require Import Shared.Maps.

Unset Automatic Introduction.
Set Implicit Arguments.
Local Open Scope Z_scope.


(* Module MIPS_PARSER. *)
(*   Module MIPS_BASE_PARSER := Parser.Parser(MIPS_PARSER_ARG). *)
  (* Import MIPS_BASE_PARSER. *)

  Require Import MIPSSyntax.
  Require Import MIPSModel.ParserArg.
  Require Import MIPSModel.BiGrammar.
  Import ParserArg.MIPS_PARSER_ARG.

  Definition int_t := User_t Int_t.
  Definition register_t := User_t Register_t.
  Definition instruction_t := User_t Instruction_t.
  Definition shamt5_t := User_t Shamt5_t.
  Definition imm16_t := User_t Imm16_t.
  Definition target26_t := User_t Target26_t.
  Definition ioperand_t := User_t Ioperand_t.
  Definition joperand_t := User_t Joperand_t.
  Definition reg2sh_operand_t := User_t Reg2sh_operand_t.
  Definition reg2_operand_t := User_t Reg2_operand_t.
  Definition reg3_operand_t := User_t Reg3_operand_t.
  Definition bz_operand_t := User_t BZ_operand_t.

  Local Ltac localcrush :=
    intros;
    repeat match goal with
      | [ |- invertible _ _ ] => invertible_tac
      | _ => crush
    end.
  
  Local Ltac localsimpl :=
    repeat match goal with
      | [v: unit |- _ ] => destruct v
      | [H: wf_bigrammar _ |- wf_grammar _] => destruct H
      | _ => unfold in_bigrammar_rng in *; in_bigrammar_inv; localcrush
    end.

  Local Ltac lineararith := 
    unfold two_power_nat, shift_nat in *; simpl in *; omega.


  Obligation Tactic := localcrush.

  (* combinators for building parsers *)
  (* Definition bit(x:bool) : grammar Char_t := Char x. *)
  (* Definition never t : grammar t := Zero t. *)
  (* Definition always t (x:interp t) : grammar t := @Map Unit_t t (fun (_:unit) => x) Eps. *)
  (* Definition alt t (p1 p2:grammar t) : grammar t :=  *)
  (*   Map _ (fun (x:interp (Sum_t t t)) => match x with inl a => a | inr b => b end)  *)
  (*       (Alt p1 p2). *)

  (* Fixpoint alts0 t (ps:list (grammar t)) : grammar t :=  *)
  (*   match ps with  *)
  (*     | nil => @never t *)
  (*     | p::nil => p *)
  (*     | p::rest => alt p (alts0 rest) *)
  (*   end. *)

  (* Fixpoint half A (xs ys zs: list A) : (list A) * (list A) :=  *)
  (*   match xs with  *)
  (*     | nil => (ys,zs)  *)
  (*     | h::t => half t zs (h::ys) *)
  (*   end. *)

  (* Fixpoint alts' n t (ps:list (grammar t)) : grammar t :=  *)
  (*   match n, ps with  *)
  (*     | 0%nat, _ => alts0 ps *)
  (*     | S n, nil => @never t *)
  (*     | S n, p::nil => p *)
  (*     | S n, ps =>  *)
  (*       let (ps1,ps2) := half ps nil nil in  *)
  (*         let g1 := alts' n ps1 in  *)
  (*           let g2 := alts' n ps2 in  *)
  (*             alt g1 g2 *)
  (*   end. *)

  (* Definition alts t (ps:list (grammar t)) : grammar t := alts' 20 ps. *)
  (* Definition map t1 t2 (p:grammar t1) (f:interp t1 -> interp t2) : grammar t2 :=  *)
  (*   @Map t1 t2 f p. *)
  (* Implicit Arguments map [t1 t2]. *)
  (* Definition seq t1 t2 (p1:grammar t1) (p2:grammar t2) : grammar (Pair_t t1 t2) := Cat p1 p2. *)

  (* Definition cons t (pair : interp (Pair_t t (List_t t))) : interp (List_t t) :=  *)
  (*   (fst pair)::(snd pair). *)
  (* Definition seqs t (ps:list (grammar t)) : grammar (List_t t) :=  *)
  (*   List.fold_right (fun p1 p2 => map (seq p1 p2) (@cons t))  *)
  (*     (@always (List_t t) (@nil (interp t))) ps. *)


  Definition bitvector_t n := User_t (BitVector_t n).

  (* Mapping old definitions to new . *)
  Notation char_t := Char_t.
  Notation list_t := List_t.
  Notation unit_t := Unit_t.
  Notation pair_t := Pair_t.
  Notation sum_t := Sum_t.
  Notation option_t := Option_t.

  (** * Basic operators for converting values between types including bits_n, (Z->bool), int n, Z, etc. *)

  (** ** Definitions *)

  Fixpoint bits_n (n:nat) : type := 
    match n with 
      | 0%nat => unit_t
      | S n => pair_t char_t (bits_n n)
    end.

  (* A signature function that is false above an index n *)
  Definition sig_false_above (n:nat) (f:Z->bool) := 
    forall z, (z >= Z_of_nat n)%Z -> f z = false.

  (** convert a sequence of bits to a signature function that maps position
     indexes to bits so that we are not restricted by the
     right-associateness of the bits when processing them; position indexes
     in the signature function start at 0 *)
  Fixpoint sig_of_bitsn (n:nat) : interp (bits_n n) -> (Z -> bool) := 
    match n with
      | O => fun _ _ => false
      | S n' => 
        fun v =>
          let f' := sig_of_bitsn n' (snd v) in
          fun x => if zeq x (Z_of_nat n') then fst v else f' x
    end.

  Fixpoint bitsn_of_sig (n:nat) (f:Z->bool) : interp (bits_n n) :=
    match n with
      | O => tt
      | S n' => (f (Z_of_nat n'), bitsn_of_sig n' f)
    end.

  (* Definition bits_sig (n:nat) := {f:Z->bool | sig_false_above n f}. *)

  (* Fixpoint sig_of_bits (n:nat) : interp (bits_n n) -> bits_sig n.  *)
  (*   intros n. *)
  (*   refine( *)
  (*     match n return interp (bits_n n) -> bits_sig n with *)
  (*       | O => fun _ => exist _ (fun _:Z => false) _ *)
  (*       | S n' => *)
  (*         fun v => *)
  (*           let f' := sig_of_bits n' (snd v) in *)
  (*           exist _ (fun x => if zeq x (Z_of_nat n') *)
  (*                             then fst v else (` f') x) _ *)
  (*     end). *)
  (*   - crush. *)
  (*   - unfold sig_false_above. *)
  (*     intros z H. *)
  (*     destruct_head.  *)
  (*     + nat_to_Z; omega. *)
  (*     + apply (proj2_sig f'). nat_to_Z; omega. *)
  (* Defined. *)

  (* Fixpoint bits_of_sig (n:nat) : bits_sig n -> interp (bits_n n) := *)
  (*   match n return bits_sig n -> interp (bits_n n) with *)
  (*     | O => fun _ => tt *)
  (*     | S n' => fun f => ((` f) (Z_of_nat n'), @bits_of_sig n' f) *)
  (*   end. *)

  Definition int_of_bitsn (n:nat) (v:interp (bits_n n)) : interp int_t := 
    Word.Z_of_bits n (sig_of_bitsn n v).

  Definition bitsn_of_int (n:nat) (i:interp int_t) : option (interp (bits_n n)) := 
    if (zle (0%Z) i) then
      if (zlt i (two_power_nat n)) then 
        Some (bitsn_of_sig n (Word.bits_of_Z n i))
      else None
    else None.

  (* Compared to repr (Z_of_bits f), this one doesn't do the extra modular op *)
  Definition intn_of_sig (n:nat) (f:Z->bool): Word.int n :=
    Word.mkint _ (Word.Z_of_bits (S n) f) (Word.Z_of_bits_range n f).

  Definition sig_of_intn (n:nat) (i:Word.int n) : Z->bool :=
    Word.bits_of_Z (S n) (Word.unsigned i).

  Definition intn_of_bitsn (n:nat) (bs:[|bits_n (S n)|]) : Word.int n :=
    intn_of_sig n (sig_of_bitsn (S n) bs).

  Definition bitsn_of_intn (n:nat) (v:Word.int n) : [|bits_n (S n)|] := 
    bitsn_of_sig (S n) (sig_of_intn v).

  (** ** Lemmas about the above conversion operators *)

  Lemma sig_of_bitsn_false_above n (v: [|bits_n n|]) :
    sig_false_above n (sig_of_bitsn n v).
  Proof. induction n.
    - crush.
    - unfold sig_false_above.
      intros v z H. simpl.
      destruct_head.
      + nat_to_Z; omega.
      + apply IHn. nat_to_Z; omega.
  Qed.

  Instance bitsn_of_sig_exten n:
    Proper (Word.sig_eq_below n ==> eq) (bitsn_of_sig n).
  Proof. induction n. crush.
    intros f1 f2 H.
    simpl. f_equiv.
    - apply H; nat_to_Z; omega.
    - apply IHn. apply Word.sig_eq_below_downward. trivial.
  Qed.

  Lemma bitsn_of_sig_inv : forall n v, bitsn_of_sig n (sig_of_bitsn n v) = v.
  Proof. induction n. crush.
    simpl; intros.
    destruct_head; try omega.
    assert (H: Word.sig_eq_below n 
              (fun x => if zeq x (Z.of_nat n) then fst v
                        else sig_of_bitsn n (snd v) x)
              (sig_of_bitsn n (snd v))).
       unfold Word.sig_eq_below.
       intros. destruct_head; try omega. trivial.
    rewrite H.
    destruct v. crush.
  Qed.

  Lemma sig_of_bitsn_inv :
    forall n f, Word.sig_eq_below n (sig_of_bitsn n (bitsn_of_sig n f)) f.
  Proof. 
    unfold Word.sig_eq_below. induction n.
    - simpl. intros. omega.
    - crush.
      destruct_head. congruence.
        rewrite Zpos_P_of_succ_nat in *.
        eapply IHn.
        omega.
  Qed.

  Hint Rewrite bitsn_of_sig_inv sig_of_bitsn_inv : inv_db.

  Lemma int_of_bitsn_range n v : (0 <= int_of_bitsn n v < two_power_nat n)%Z.
  Proof. unfold int_of_bitsn. intros.
    destruct n. 
      crush. 
      unfold two_power_nat, shift_nat. simpl. omega.
      apply Word.Z_of_bits_range.
  Qed.
  
  Lemma bitsn_of_int_inv n v: bitsn_of_int n (int_of_bitsn n v) = Some v.
  Proof. 
    unfold bitsn_of_int; intros.
    use_lemma (int_of_bitsn_range n v) by trivial.
    repeat (destruct_head; try omega).
    unfold int_of_bitsn. 
    autorewrite with inv_db. trivial.
  Qed.

  Lemma int_of_bitsn_inv : 
    forall n i v, bitsn_of_int n i = Some v -> int_of_bitsn n v = i.
  Proof.
    unfold int_of_bitsn, bitsn_of_int in *. intros.
    destruct_head in H; try congruence.
    destruct_head in H; try congruence.
    crush.
    autorewrite with inv_db.
    destruct n. 
      unfold two_power_nat, shift_nat in *. simpl in *. omega.
      apply Word.Z_of_bits_of_Z_lt_modulus.
      crush.
  Qed.

  Hint Rewrite bitsn_of_int_inv: inv_db.

  Instance intn_of_sig_exten n:
    Proper (Word.sig_eq_below (S n) ==> eq) (@intn_of_sig n).
  Proof. unfold Proper, respectful. intros.
    apply Word.mkint_eq.
    rewrite H. trivial.
  Qed.

  Lemma intn_of_sig_inv : forall n (i:Word.int n),
    @intn_of_sig n (sig_of_intn i) = i.
  Proof. unfold intn_of_sig, sig_of_intn. intros.
    destruct i. apply Word.mkint_eq.
    compute [Word.unsigned Word.intval].
    apply Word.Z_of_bits_of_Z_lt_modulus. trivial.
  Qed.

  Lemma sig_of_intn_inv: forall n f,
    Word.sig_eq_below (S n) (sig_of_intn (@intn_of_sig n f)) f.
  Proof. unfold intn_of_sig, sig_of_intn. intros.
    apply Word.bits_of_Z_of_bits.
  Qed.

  Hint Rewrite intn_of_sig_inv sig_of_intn_inv: inv_db.

  Lemma intn_of_bitsn_inv n (i:Word.int n) :
    intn_of_bitsn (bitsn_of_intn i) = i.
  Proof. unfold intn_of_bitsn, bitsn_of_intn; intros.
    autorewrite with inv_db. trivial.
  Qed.

  Lemma bitsn_of_intn_inv n (v:[|bits_n (S n)|]):
    bitsn_of_intn (intn_of_bitsn v) = v.
  Proof. unfold intn_of_bitsn, bitsn_of_intn; intros.
    autorewrite with inv_db. trivial.
  Qed.

  Hint Rewrite intn_of_bitsn_inv bitsn_of_intn_inv: inv_db.

  (* testing if a signed (n1+1)-bit immediate can be represented in a
     (n2+1)-bit immediate without loss of precision *)
  Definition repr_in_signed n1 n2 (w:Word.int n1) :=
    (Word.min_signed n2 <= Word.signed w <= Word.max_signed n2)%Z.

  Definition repr_in_signed_dec n1 n2 (w:Word.int n1) :
    {repr_in_signed n2 w} + {~(repr_in_signed n2 w)}.
    intros.
    refine (
      match (Z_le_dec (Word.signed w) (Word.max_signed n2)), 
            (Z_le_dec (Word.min_signed n2) (Word.signed w)) with
        | left _, left _ => left _ 
        | _, _ => right _
      end); unfold repr_in_signed; intuition.
  Defined.

  Definition repr_in_signed_byte (w:int32) := repr_in_signed 7 w.
  Definition repr_in_signed_halfword (w:int32) := repr_in_signed 15 w.

  Definition repr_in_signed_byte_dec (w:int32) :
    {repr_in_signed_byte w} + {~(repr_in_signed_byte w)} :=
    repr_in_signed_dec 7 w.

  Definition repr_in_signed_halfword_dec (w:int32) :
    {repr_in_signed_halfword w} + {~(repr_in_signed_halfword w)} :=
    repr_in_signed_dec 15 w.

  (* Ltac bg_pf_sim := *)
  (*   repeat match goal with *)
  (*     | [ |- context[repr_in_signed_byte_dec ?i]] =>  *)
  (*       destruct (repr_in_signed_byte_dec i) *)
  (*     | [ H: context[repr_in_signed_byte_dec ?i] |- _] => *)
  (*       destruct (repr_in_signed_byte_dec i) *)
  (*     | [ H: ~ (repr_in_signed_byte (sign_extend8_32 ?i)) |- _ ] => *)
  (*       contradict H; apply repr_in_signed_byte_extend8_32 *)

  (*     | [ |- context[repr_in_unsigned_byte_dec ?i]] =>  *)
  (*       destruct (repr_in_unsigned_byte_dec i)  *)
  (*     | [ H: context[repr_in_unsigned_byte_dec ?i] |- _] => *)
  (*       destruct (repr_in_unsigned_byte_dec i) *)
  (*     | [H: ~ (repr_in_unsigned_byte (zero_extend8_32 ?i)) |- _ ] => *)
  (*       contradict H; apply repr_in_unsigned_byte_extend8_32 *)
  (*     | [H: context[register_eq_dec ?r1 ?r2] |- _] =>  *)
  (*       destruct (register_eq_dec r1 r2); subst *)
  (*     | [ |- context[register_eq_dec ?r1 ?r2]] =>  *)
  (*       destruct (register_eq_dec r1 r2); subst *)
  (*     | [H: context[if Word.eq ?disp Word.zero then _ else _] |- _] => *)
  (*       let disp_eq := fresh "disp_eq" in *)
  (*       remember_rev (Word.eq disp Word.zero) as disp_eq; *)
  (*       destruct disp_eq *)
  (*     | [H: ?V <> ?V |- _] => contradict H; trivial *)
  (*   end. *)

  (** * Additional bigrammar constructors (assuming chars are bits) *)

  Program Definition bit (b:bool) : wf_bigrammar Char_t := Char b.
  Program Definition anybit : wf_bigrammar Char_t := Any.

  Fixpoint bits (s:string) : wf_bigrammar (bits_n (String.length s)) := 
    match s with 
      | EmptyString => empty
      | String c s' => 
        (seq (bit (if ascii_dec c "0"%char then false else true)) (bits s'))
    end.

  (** Turn a string of 0s and 1s into a right-associated tuple of trues and
      falses *)
  Fixpoint tuples_of_string (s:string): interp (bits_n (String.length s)) := 
    match s with
      | EmptyString => tt
      | String a s' =>
        (if ascii_dec a "0"%char then false else true, tuples_of_string s')
    end.

  Lemma in_bits_intro: forall str,
    in_bigrammar (` (bits str)) (string_to_bool_list str) (tuples_of_string str).
  Proof. induction str; localsimpl. Qed.

  Lemma in_bits_elim: 
    forall str s v, in_bigrammar (` (bits str)) s v ->
                    s = string_to_bool_list str /\ v = tuples_of_string str.
  Proof. induction str; localsimpl; intros; destruct (ascii_dec a "0"); crush_hyp.
  Qed.

  Lemma bits_rng: forall str,
    in_bigrammar_rng (` (bits str)) (tuples_of_string str).
  Proof. generalize in_bits_intro; localsimpl. Qed.
  Hint Resolve bits_rng: ibr_rng_db.
 
  Program Definition bitsmatch (s:string): wf_bigrammar Unit_t := 
    (bits s) @ (fun _ => tt:[|Unit_t|])
       & (fun _ => Some (tuples_of_string s)) & _.
  Notation "! s" := (bitsmatch s) (at level 60).

  Lemma in_bitsmatch_intro str s v: 
    in_bigrammar (` (bits str)) s v -> in_bigrammar (` (! str)) s ().
  Proof. crush. Qed.

  Lemma in_bitsmatch_elim str s:
    in_bigrammar (` (! str)) s () ->
    exists v, in_bigrammar (` (bits str)) s v.
  Proof. unfold bitsmatch. simpl.
    intros; in_bigrammar_inv. crush.
  Qed.

  Lemma bitsmatch_rng str: in_bigrammar_rng (` (! str)) (). 
  Proof. unfold in_bigrammar_rng. intros. eexists.
    eapply in_bitsmatch_intro. eapply in_bits_intro.
  Qed.
  Hint Resolve bitsmatch_rng: ibr_rng_db.

  Program Definition bitsleft t (s:string) (p:wf_bigrammar t) : wf_bigrammar t :=
    (bitsmatch s $ p) @ (@snd _ _)
                      & (fun v => Some (tt, v)) & _.
  Infix "$$" := bitsleft (right associativity, at level 70).

  Lemma in_bitsleft_intro: forall t (g: wf_bigrammar t) str s1 s2 v1 v2,
    in_bigrammar (` (bits str)) s1 v1 -> in_bigrammar (` g) s2 v2
      -> in_bigrammar (` (str $$ g)) (s1 ++ s2)%list v2.
  Proof. crush. Qed.

  Lemma in_bitsleft_elim: forall t str (g: wf_bigrammar t) s (v:interp t),
    in_bigrammar (` (str $$ g)) s v -> 
    exists s1 s2, s = (s1 ++ s2)% list /\ in_bigrammar (` g) s2 v.
  Proof. intros.
    simpl in H. in_bigrammar_inv. crush. destruct x.
    in_bigrammar_inv. crush.
  Qed.

  Lemma in_bigrammar_rng_bitsleft t str (g:wf_bigrammar t) v: 
    in_bigrammar_rng (` (str $$ g)) v <-> in_bigrammar_rng (` g) v.
  Proof. unfold in_bigrammar_rng; split; intros.
    - (* -> *)
      destruct H as [s H]. apply in_bitsleft_elim in H.
      destruct H as [s1 [s2 [H2 H4]]].
      crush.
    - (* <- *)
      destruct H as [s H]. 
      generalize (in_bits_intro str); intro.
      eexists.
      eapply in_bitsleft_intro; eassumption.
  Qed.

  (** the instruction decoder specific version of ibr_sim *)
  Ltac ins_ibr_sim :=
    repeat match goal with 
      | [H: in_bigrammar_rng (` (_ $$ _)) _ |- _] =>
        apply in_bigrammar_rng_bitsleft in H
      | [H: in_bigrammar_rng (` (_ |\/| _)) _ |- _] =>
        apply in_bigrammar_rng_union in H
      | [ |- in_bigrammar_rng (` (_ $$ _)) _ ] =>
        rewrite -> in_bigrammar_rng_bitsleft
      | [ |- in_bigrammar_rng (` (_ |\/| _)) _ ] =>
        apply in_bigrammar_rng_union
      | [ |- in_bigrammar_rng (` (! _)) () ] =>
        apply bitsmatch_rng
      | _ => ibr_sim
    end.

  Fixpoint field'(n:nat) : wf_bigrammar (bits_n n) := 
    match n with 
      | 0%nat => empty
      | S n => seq anybit (field' n)
    end.

  Fixpoint flatten_bits_n (n:nat) : (interp (bits_n n)) -> list bool := 
    match n with
      | O => fun _ => nil
      | S n' => fun v => (fst v) :: flatten_bits_n n' (snd v)
    end.

  Lemma in_field'_intro: forall n (v: interp (bits_n n)),
    in_bigrammar (` (field' n)) (flatten_bits_n n v) v.
  Proof. induction n. crush.
    intros. simpl. destruct v.
    eapply InCat; crush.
  Qed.

  Lemma field'_rng n (v : [|bits_n n|]): 
    in_bigrammar_rng (` (field' n)) v.
  Proof. unfold in_bigrammar_rng. intros. eexists.
    eapply in_field'_intro.
  Qed.
  Hint Resolve field'_rng: ibr_rng_db.

  Program Definition field (n:nat) : wf_bigrammar int_t := 
    (field' n) @ (int_of_bitsn n) & bitsn_of_int n & _.
  Next Obligation.
    - eapply int_of_bitsn_inv. trivial.
  Defined.

  Definition int_to_bool_list n v := 
    (flatten_bits_n n (bitsn_of_sig n (Word.bits_of_Z n v))).

  Lemma in_field_intro:
    forall n i, (0 <= i < two_power_nat n)%Z ->
                in_bigrammar (` (field n)) (int_to_bool_list n i) i.
  Proof. intros.
    eapply InMap. eapply in_field'_intro.
    unfold int_of_bitsn in *. simpl.
    autorewrite with inv_db.
    destruct n.
    - unfold two_power_nat, shift_nat in *. simpl in *. omega.
    - rewrite (Word.Z_of_bits_of_Z_lt_modulus); trivial.
  Qed.

  Lemma field_rng : 
    forall n i, (0 <= i < two_power_nat n)%Z <->
                in_bigrammar_rng (` (field n)) i.
  Proof. 
    split; intros.
    - unfold in_bigrammar_rng.
      eexists. eapply in_field_intro. trivial.
    - unfold field, in_bigrammar_rng in *.
      intros. crush; in_bigrammar_inv; crush' int_of_bitsn_range fail.
  Qed.
  Hint Extern 1 (in_bigrammar_rng (` (field _)) _) =>
    apply field_rng; omega : ibr_rng_db.

  (* remove; replaced by int_of_bitsn 
  Fixpoint bits2Z(n:nat)(a:Z) : interp (bits_n n) -> interp int_t := 
    match n with 
      | 0%nat => fun _ => a
      | S n => fun p => bits2Z n (2*a + (if (fst p) then 1 else 0)) (snd p)
    end.
  Definition bits2int(n:nat)(bs:interp (bits_n n)) : interp int_t := bits2Z n 0 bs.
  *)

  (* Fixpoint string2int' (s:string) (a:Z) : Z := *)
  (*   match s with *)
  (*     | EmptyString => a *)
  (*     | String c s' => string2int' s' (2*a+ (if (ascii_dec c "0"%char) then 0 else 1)) *)
  (*   end. *)

  (* remove: should be able to use int_of_bitsn to replace this *)
  (* Definition string2int (s:string) : Z := *)
  (*   string2int' s 0. *)

  (* notation for building parsers *)
  (* Infix "|+|" := alt (right associativity, at level 80). *)
  (* Infix "$" := seq (right associativity, at level 70). *)
  (* Infix "@" := map (right associativity, at level 75). *)
  (* Notation "e %% t" := (e : interp t) (at level 80). *)

  Ltac ins_destruct_var v :=
    match goal with
    | [H: match v with true => _ | false => _ end = _ |- _] =>
      case v as []
    | [H: match v with Reg _ => _ end = _ |- _] =>
      destruct v
    | [H: match v with Iop _ _ _ => _ end = _ |- _] =>
      destruct v
    | [H: match v with Jop _ => _ end = _ |- _] =>
      destruct v
    | [H: match v with Reg2sh_op _ _ _ => _ end = _ |- _] =>
      destruct v
    | [H: match v with Reg2_op _ _ => _ end = _ |- _] =>
      destruct v
    | [H: match v with Reg3_op _ _ _ => _ end = _ |- _] =>
      destruct v
    | [H: match v with BZ_op _ _ => _ end = _ |- _] =>
      destruct v
    end.

  Ltac ins_parsable_tac :=
    parsable_tac_gen ibr_sim ins_destruct_var.

  Ltac ins_printable_tac := printable_tac_gen ins_ibr_sim.
  Ltac ins_invertible_tac := 
    invertible_tac_gen unfold_invertible_ast ins_ibr_sim ins_destruct_var.


  Program Definition field_intn (n:nat) : wf_bigrammar (bitvector_t n) :=
    (field' (S n)) @ (@intn_of_bitsn n: _ -> [|bitvector_t n|])
                   & (fun i => Some (bitsn_of_intn i)) & _.

  Definition reg :wf_bigrammar register_t.
    refine((field_intn size5) @ (fun r => Reg r: interp register_t)
                       & (fun rg => match rg with Reg r => Some r end) & _);
    ins_invertible_tac.
  Defined.
  
  Definition imm_p: wf_bigrammar imm16_t := field_intn size16.
  Definition target_p: wf_bigrammar target26_t := field_intn size26.
  Definition shamt_p: wf_bigrammar shamt5_t := field_intn size5.

  Program Definition bitsmatch (s:string): wf_bigrammar Unit_t := 
    (bits s) @ (fun _ => tt:[|Unit_t|])
       & (fun _ => Some (tuples_of_string s)) & _.
  Notation "! s" := (bitsmatch s) (at level 60).

  (* replace this with bitsmatch *)
  (* Definition cfcode_p (s:string) : grammar Unit_t := *)
  (*   ((bits s)@(fun _ => tt %%Unit_t)). *)

  (*Generic Instruction Format Parsers*)

  Definition i_p_gen (opcode: string) 
             (rs_p : wf_bigrammar register_t)
             (rt_p : wf_bigrammar register_t) 
             (immf_p : wf_bigrammar imm16_t): wf_bigrammar ioperand_t.
    intros.
    refine((opcode $$ rs_p $ rt_p $ immf_p)
             @ (fun p =>
                  match p with
                  | (r1,(r2,immval)) => Iop r1 r2 immval
                  end %% (User_t Ioperand_t))
             & (fun op => 
                  match op with Iop r1 r2 immval => Some (r1,(r2,immval)) end)
             & _). ins_invertible_tac.
  Defined.

  Definition i_p (opcode: string) : wf_bigrammar ioperand_t :=
    i_p_gen opcode reg reg imm_p.

  Definition j_p_gen (opcode: string) (targetf_p : wf_bigrammar target26_t):
    wf_bigrammar joperand_t.
    intros.
    refine (opcode $$ targetf_p 
             @ (fun tval => Jop tval %% joperand_t)
             & (fun op => 
                  match op with Jop tval => Some tval end)
             & _). ins_invertible_tac.
  Defined.
                   
  Definition j_p (opcode: string) : wf_bigrammar joperand_t :=
    j_p_gen opcode target_p.

  Definition shift_p (fcode: string) : wf_bigrammar reg2sh_operand_t.
    intros.
    refine ("000000" $$ "00000" $$ reg $ reg $ shamt_p $ ! fcode
             @ (fun p =>
                  match p with
                  | (r1,(r2,(shval,_))) => 
                    Reg2sh_op r1 r2 shval %% reg2sh_operand_t
                  end)
             & (fun op =>
                  match op with 
                  | Reg2sh_op r1 r2 shval => Some (r1,(r2,(shval,tt)))
                  end)
             & _). ins_invertible_tac.
  Defined.

  (* a generic parser for parsing instructions that accept two registers *)
  Definition reg2_p (opcode: string) (fcode: string)
    : wf_bigrammar reg2_operand_t.
    intros.
    refine (opcode $$ reg $ reg $ "00000" $$ "00000" $$ ! fcode
             @ (fun p =>
                  match p with
                  | (r1,(r2,_)) => Reg2_op r1 r2 %% reg2_operand_t
                  end)
             & (fun op =>
                  match op with
                  | Reg2_op r1 r2 => Some (r1,(r2,tt))
                  end)
             & _). ins_invertible_tac.
  Defined.

  (* a generic parser for parsing instructions that accept three registers *)
  Definition reg3_p (opcode: string) (fcode: string)
    : wf_bigrammar reg3_operand_t.
    intros.
    refine (opcode $$ reg $ reg $ reg $ "00000" $$ ! fcode
              @ (fun p =>
                  match p with
                  | (r1,(r2,(r3,_))) => Reg3_op r1 r2 r3 %% reg3_operand_t
                  end)
              & (fun op =>
                  match op with
                  | Reg3_op r1 r2 r3 => Some (r1,(r2,(r3,tt)))
                  end)
             & _). ins_invertible_tac.
  Defined.

  (*Specific Instruction Parsers*)

  Definition ADD_p := reg3_p "000000" "100000".
  Definition ADDI_p := i_p "001000".
  Definition ADDIU_p := i_p "001001".
  Definition ADDU_p := reg3_p "000000" "100001".
  Definition AND_p := reg3_p "000000" "100100".
  Definition ANDI_p := i_p "001100".
  Definition BEQ_p := i_p "000100".

  Definition bz_p_gen (opcode1: string) (rs_p: wf_bigrammar register_t) (opcode2: string)
    (immf_p : wf_bigrammar imm16_t) : wf_bigrammar bz_operand_t.
    intros.
    refine (opcode1 $$ rs_p $ opcode2 $$ immf_p
              @ (fun p =>
                   match p with
                   | (r1,immval) => BZ_op r1 immval
                   end %% bz_operand_t)
              & (fun op =>
                   match op with
                   | BZ_op r1 immval => Some (r1,immval)
                   end)
              & _). ins_invertible_tac.
  Defined.

  Definition BGEZ_p := bz_p_gen "000001" reg "00001" imm_p.
  Definition BGEZAL_p := bz_p_gen "000001" reg "10001" imm_p.
  Definition BGTZ_p := bz_p_gen "000111" reg "00000" imm_p.
  Definition BLEZ_p := bz_p_gen "000110" reg "00000" imm_p.
  Definition BLTZ_p := bz_p_gen "000001" reg "00000" imm_p.
  Definition BLTZAL_p := bz_p_gen "000001" reg "10000" imm_p.

  Definition BNE_p := i_p "000101".
  Definition DIV_p := reg2_p "000000" "011010".
  Definition DIVU_p := reg2_p "000000" "011011".
  Definition J_p := j_p "000010".
  Definition JAL_p := j_p "000011".

  Definition JALR_p : wf_bigrammar reg2sh_operand_t. 
    refine ("000000" $$ reg $ "00000" $$ reg $ shamt_p $ ! "001001"
              @ (fun p =>
                   match p with
                   | (r1,(r2,(shval,_))) => Reg2sh_op r1 r2 shval
                   end %% reg2sh_operand_t)
              & (fun op =>
                   match op with
                   | Reg2sh_op r1 r2 shval => Some (r1,(r2,(shval,tt)))
                   end)
              & _). ins_invertible_tac.
  Defined.

  Definition JR_p: wf_bigrammar register_t.
    refine ("000000" $$ reg $ "00000" $$ "00000" $$ "00000" $$ ! "001000"
              @ (fun p =>
                   match p with
                   | (r,_) => r
                   end %% register_t)
              & (fun r => Some (r,tt))
              & _). ins_invertible_tac.
  Defined.

  Definition LB_p := i_p "100000".
  Definition LBU_p := i_p "100100".
  Definition LH_p := i_p "100001".
  Definition LHU_p := i_p "100101".
  Definition LUI_p := i_p "001111".
  Definition LW_p := i_p "100101".

  Definition MFHI_p: wf_bigrammar register_t.
    refine ("000000" $$ "00000" $$ "00000" $$ reg $ "00000" $$ ! "010000"
              @ (fun p =>
                   match p with
                   | (r,_) => r
                   end %% register_t)
              & (fun r => Some (r,tt))
              & _). ins_invertible_tac.
  Defined.

  Definition MFLO_p: wf_bigrammar register_t.
    refine ("000000" $$ "00000" $$ "00000" $$ reg $ "00000" $$ ! "010010"
              @ (fun p =>
                   match p with
                   | (r,_) => r
                   end %% register_t)
              & (fun r => (Some (r,tt)))
              & _). ins_invertible_tac.
  Defined.

  Definition MUL_p := reg3_p "000000" "000010".
  Definition MULT_p := reg2_p "000000" "011000".
  Definition MULTU_p := reg2_p "000000" "011001".
  Definition NOR_p := reg3_p "000000" "100111".
  Definition OR_p := reg3_p "000000" "100101".
  Definition ORI_p := i_p "001101".
  Definition SB_p := i_p "101000".

  Definition SEB_p: wf_bigrammar reg2_operand_t.
    refine ("011111" $$ "00000" $$ reg $ reg $ "10000" $$ ! "100000"
              @ (fun p =>
                   match p with
                   | (r1,(r2,_)) => Reg2_op r1 r2
                   end %% reg2_operand_t)
              & (fun op =>
                   match op with Reg2_op r1 r2 => Some (r1,(r2,tt)) end)
              & _). ins_invertible_tac.
  Defined.

  Definition SEH_p: wf_bigrammar reg2_operand_t.
    refine ("011111" $$ "00000" $$ reg $ reg $ "11000" $$ ! "100000"
              @ (fun p =>
                   match p with
                   | (r1,(r2,_)) => Reg2_op r1 r2
                   end %% reg2_operand_t)
              & (fun op =>
                   match op with Reg2_op r1 r2 => Some (r1,(r2,tt)) end)
              & _). ins_invertible_tac.
  Defined.

  Definition SH_p := i_p "101001".
  Definition SLL_p := shift_p "000000".
  Definition SLLV_p := reg3_p "000000" "000100".
  Definition SLT_p := reg3_p "000000" "101010".
  Definition SLTI_p := i_p "001010".
  Definition SLTU_p := reg3_p "000000" "101011".
  Definition SLTIU_p := i_p "001011".
  Definition SRA_p := shift_p "000011".
  Definition SRAV_p := reg3_p "000000" "000111".
  Definition SRL_p := shift_p "000010".
  Definition SRLV_p := reg3_p "000000" "000110".
  Definition SUB_p := reg3_p "000000" "100010".
  Definition SUBU_p := reg3_p "000000" "100011".
  Definition SW_p := i_p "101011".
  Definition XOR_p := reg3_p "000000" "100110".
  Definition XORI_p := i_p "001110".

To be organized.

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

Log: 2 hours + 1 hour + 2 hours
