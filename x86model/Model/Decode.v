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


(* This is now defined in ParserArg.v because of the bug with Extraction 
   Implicit.  

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
  | Double_Word_t : type
  | Ten_Byte_t : type
  | Scale_t : type
  | Condition_t : type
  | Address_t : type
  | Operand_t : type
  | Fpu_Register_t : type
  | Fp_Debug_Register_t : type
  | Fp_Operand_t : type 
  | MMX_Granularity_t : type
  | MMX_Register_t : type
  | MMX_Operand_t : type
  | SSE_Register_t : type
  | SSE_Operand_t : type
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
      | Double_Word_t => int64
      | Ten_Byte_t => int80
      | Scale_t => scale
      | Condition_t => condition_type
      | Address_t => address
      | Operand_t => operand
      | Fpu_Register_t => int3
      | Fp_Debug_Register_t => fp_debug_register
      | Fp_Operand_t => fp_operand  
      | MMX_Granularity_t => mmx_granularity
      | MMX_Register_t => mmx_register
      | MMX_Operand_t => mmx_operand
      | SSE_Register_t => sse_register
      | SSE_Operand_t => sse_operand
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
*)

(* Module X86_PARSER. *)
  (* Commented out because the Parser is no longer a functor, due to the
     bug with Extraction Implicit. 
     Module X86_BASE_PARSER := Parser.Parser(X86_PARSER_ARG).
  *)
  Require Import X86Syntax.
  Require Import Bits.
  Require ParserArg.
  Import ParserArg.X86_PARSER_ARG.
  Require Import BiGrammar.


  Definition option_t x := User_t (Option_t x).
  Definition int_t := User_t Int_t.
  Definition register_t := User_t Register_t.
  Definition byte_t := User_t Byte_t.
  Definition half_t := User_t Half_t.
  Definition word_t := User_t Word_t.
  Definition double_word_t := User_t Double_Word_t.
  Definition ten_byte_t := User_t Ten_Byte_t.
  Definition scale_t := User_t Scale_t.
  Definition condition_t := User_t Condition_t.
  Definition fpu_register_t := User_t Fpu_Register_t.
  Definition fp_debug_register_t := User_t Fp_Debug_Register_t.
  Definition mmx_granularity_t := User_t MMX_Granularity_t.
  Definition mmx_operand_t := User_t MMX_Operand_t.
  Definition mmx_register_t := User_t MMX_Register_t.
  Definition sse_operand_t := User_t SSE_Operand_t.
  Definition sse_register_t := User_t SSE_Register_t.
  Definition address_t := User_t Address_t.
  Definition operand_t := User_t Operand_t.
  Definition fp_operand_t := User_t Fp_Operand_t.  
  Definition instruction_t := User_t Instruction_t.
  Definition control_register_t := User_t Control_Register_t.
  Definition debug_register_t := User_t Debug_Register_t.
  Definition segment_register_t := User_t Segment_Register_t.
  Definition lock_or_rep_t := User_t Lock_or_Rep_t.
  Definition bool_t := User_t Bool_t.
  Definition prefix_t := User_t Prefix_t.
  Definition bitvector_t n := User_t (BitVector_t n).

  (* Mapping old definitions to new . *)
  (* Definition parser r := wf_bigrammar r. *)
  (* Definition result_m := interp. *)
  (* Definition result := type. *)
  (* Definition tipe_t := User_t. *)
  Notation char_t := Char_t.
  Notation list_t := List_t.
  Notation unit_t := Unit_t.
  Notation pair_t := Pair_t.
  Notation sum_t := Sum_t.
  Definition Any_p := Any.
  Definition Eps_p := Eps.


  Local Ltac localcrush :=
    repeat match goal with
             | [H: wf_bigrammar _ |- wf_grammar _] => destruct H
             | [ |- invertible _ _ ] => invertible_tac
             | _ => crush
           end.

  Local Ltac localsimpl :=
    repeat match goal with
      | [v: unit |- _ ] => destruct v
      | [H: wf_bigrammar _ |- _] => destruct H
      | _ => unfold in_bigrammar_rng in *; in_bigrammar_inv; localcrush
    end.

  Local Ltac destruct_union := 
    repeat match goal with 
             | [v: [| Sum_t _ _ |] |- _ ] => destruct v as [v | v]
             | [v: [| Unit_t |] |- _] => destruct v
           end.

  Local Ltac lineararith := 
    unfold two_power_nat, shift_nat in *; simpl in *; omega.

  Local Ltac local_printable_tac := 
    break_hyp;
    match goal with
      | [H: ?V <> ?V |- _] => contradict H; trivial
      | _ => printable_tac
    end.

  Obligation Tactic := localcrush.

  (** * Basic operartions for converting values between domains:
        bits_n, (Z->bool), int n, Z *)

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
      right-associateness of the bits when processing them; position
      indexes in the signature function start at 0 *)
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
  (* Implicit Arguments intn_of_sig [n]. *)

  Definition sig_of_intn (n:nat) (i:Word.int n) : Z->bool :=
    Word.bits_of_Z (S n) (Word.unsigned i).

  Definition intn_of_bitsn (n:nat) (bs:[|bits_n (S n)|]) : Word.int n :=
    intn_of_sig n (sig_of_bitsn (S n) bs).

  Definition bitsn_of_intn (n:nat) (v:Word.int n) : [|bits_n (S n)|] := 
    bitsn_of_sig (S n) (sig_of_intn v).

  (* Definition matches a register with a list of booleans that 
   * represents its bit encoding. *)
  Definition register_to_Z r : Z :=
    (match r with
      | EAX => 0
      | ECX => 1
      | EDX => 2
      | EBX => 3
      | ESP => 4
      | EBP => 5
      | ESI => 6
      | EDI => 7
    end)%Z.


  Definition condition_type_to_Z (ct: condition_type) : Z := 
    (match ct with
      | O_ct => 0 (* overflow *)
      | NO_ct => 1 (* not overflow *)
      | B_ct => 2 (* below, not above or equal *)
      | NB_ct => 3 (* not below, above or equal *)
      | E_ct => 4 (* equal, zero *)
      | NE_ct => 5 (* not equal, not zero *)
      | BE_ct => 6 (* below or equal, not above *)
      | NBE_ct => 7 (* not below or equal, above *)
      | S_ct => 8 (* sign *)
      | NS_ct => 9 (* not sign *)
      | P_ct => 10 (* parity, parity even *)
      | NP_ct => 11 (* not parity, parity odd *)
      | L_ct => 12  (* less than, not greater than or equal to *)
      | NL_ct => 13 (* not less than, greater than or equal to *)
      | LE_ct => 14 (* less than or equal to, not greater than *)
      | NLE_ct => 15
    end)%Z.

  Definition scale_to_Z s := (match s with
                               | Scale1 => 0
                               | Scale2 => 1
                               | Scale4 => 2
                               | Scale8 => 3
                              end)%Z.


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

  Local Ltac toztac := 
    repeat match goal with 
             | [w:Z |- _ ] => destruct w; (discriminate || eauto)
             | [ _ : context[match ?p with xH => _ | xI _  | xO _ => _ end] |- _ ]
               => destruct p; (discriminate || eauto)
           end.

  Lemma register_to_Z_inv : 
    forall z, (0 <= z < 8)%Z -> register_to_Z (Z_to_register z) = z.
  Proof. intros.
    remember (Z_to_register z) as r; destruct r; unfold Z_to_register in *; 
    toztac; simpl in *; pos_to_Z; omega.
  Qed.

  Lemma Z_to_register_inv : forall r, Z_to_register (register_to_Z r) = r.
  Proof. destruct r; crush. Qed.

  Lemma condition_type_to_Z_inv : 
    forall z, (0 <= z < 16)%Z -> condition_type_to_Z (Z_to_condition_type z) = z.
  Proof. intros.
    remember (Z_to_condition_type z) as ct;
    destruct ct; unfold Z_to_condition_type in *;
    toztac;
    simpl in *; pos_to_Z; omega.
  Qed.

  Lemma Z_to_condition_type_inv : 
    forall ct, Z_to_condition_type (condition_type_to_Z ct) = ct.
  Proof. destruct ct; crush. Qed.

  Lemma scale_to_Z_inv : 
    forall z, (0 <= z < 4)%Z -> scale_to_Z (Z_to_scale z) = z.
  Proof. intros.
    remember (Z_to_scale z) as r; destruct r; unfold Z_to_scale in *; 
    toztac; simpl in *; pos_to_Z; omega.
  Qed.

  Lemma Z_to_scale_inv : forall r, Z_to_scale (scale_to_Z r) = r.
  Proof. destruct r; crush. Qed.

  
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

  Lemma sign_extend_inv1 n1 n2 (w:Word.int n2):
    n1 <= n2 -> repr_in_signed n1 w ->
    @sign_extend n1 n2 (@sign_extend n2 n1 w) = w.
  Proof. unfold sign_extend; intros.
    rewrite Word.signed_repr by trivial.
    rewrite Word.repr_signed; trivial.
  Qed.


  Lemma sign_extend_inv2 n1 n2 (w:Word.int n2):
    n2 <= n1 -> @sign_extend n1 n2 (@sign_extend n2 n1 w) = w.
  Proof. unfold sign_extend; intros.
    assert (Word.min_signed n1 <= Word.signed w <= Word.max_signed n1)%Z.
      generalize (Word.signed_range n2 w).
      use_lemma max_signed_mono by eassumption.
      use_lemma min_signed_mono by eassumption.
      omega.
    rewrite Word.signed_repr by assumption.
    rewrite Word.repr_signed; trivial.
  Qed.

  Lemma repr_in_signed_extend n1 n2 n3 w:
    n1 <= n3 -> n1 <= n2 ->
    repr_in_signed n2 (@sign_extend n1 n3 w).
  Proof. unfold repr_in_signed, sign_extend; intros.
    generalize (Word.signed_range n1 w); intros.
    assert (Word.min_signed n3 <= Word.signed w <= Word.max_signed n3)%Z.
      use_lemma (@max_signed_mono n1 n3) by eassumption.
      use_lemma (@min_signed_mono n1 n3) by eassumption.
      omega.
    rewrite Word.signed_repr by assumption.
    use_lemma (@max_signed_mono n1 n2) by eassumption.
    use_lemma (@min_signed_mono n1 n2) by eassumption.
    omega.
  Qed.

  Definition sign_shrink32_8 := @sign_extend 31 7.
  Definition sign_shrink32_16 := @sign_extend 31 15.

  Lemma sign_extend8_32_inv (w:int32) : 
    repr_in_signed_byte w -> sign_extend8_32 (sign_shrink32_8 w) = w.
  Proof. unfold sign_extend8_32, sign_shrink32_8, repr_in_signed_byte. intros.
    apply sign_extend_inv1; [omega | trivial].
  Qed.
  
  Lemma sign_shrink32_8_inv (b:int8) : 
    sign_shrink32_8 (sign_extend8_32 b) = b.
  Proof. unfold sign_extend8_32, sign_shrink32_8. intros.
    apply sign_extend_inv2; omega.
  Qed.
  Hint Rewrite sign_shrink32_8_inv: inv_db.
  Hint Rewrite sign_extend8_32_inv using assumption: inv_db.

  Lemma repr_in_signed_byte_extend8_32 b: 
    repr_in_signed_byte (sign_extend8_32 b).
  Proof. unfold repr_in_signed_byte, sign_extend8_32; intros.
    apply repr_in_signed_extend; omega.
  Qed.

  Lemma sign_extend16_32_inv (w:int32) : 
    repr_in_signed_halfword w -> sign_extend16_32 (sign_shrink32_16 w) = w.
  Proof. unfold sign_extend16_32, sign_shrink32_16, repr_in_signed_halfword. intros.
    apply sign_extend_inv1; [omega | trivial].
  Qed.
  
  Lemma sign_shrink32_16_inv (hw:int16) : 
    sign_shrink32_16 (sign_extend16_32 hw) = hw.
  Proof. unfold sign_extend16_32, sign_shrink32_16. intros.
    apply sign_extend_inv2; omega.
  Qed.
  Hint Rewrite sign_shrink32_16_inv: inv_db.
  Hint Rewrite sign_extend16_32_inv using assumption: inv_db.

  Lemma repr_in_signed_byte_extend16_32 hw: 
    repr_in_signed_halfword (sign_extend16_32 hw).
  Proof. unfold repr_in_signed_halfword, sign_extend16_32; intros.
    apply repr_in_signed_extend; omega.
  Qed.

  Definition zero_shrink32_8 := @zero_extend 31 7.

  Definition repr_in_unsigned n1 n2 (w:Word.int n1) :=
    (Word.unsigned w <= Word.max_unsigned n2)%Z.

  Definition repr_in_unsigned_dec n1 n2 (w:Word.int n1) :
    {repr_in_unsigned n2 w} + {~(repr_in_unsigned n2 w)} :=
    Z_le_dec (Word.unsigned w) (Word.max_unsigned n2).

  Definition repr_in_unsigned_byte (w:int32) := repr_in_unsigned 7 w.
  Definition repr_in_unsigned_halfword (w:int32) := repr_in_unsigned 15 w.

  Definition repr_in_unsigned_byte_dec (w:int32) :
    {repr_in_unsigned_byte w} + {~(repr_in_unsigned_byte w)} :=
    repr_in_unsigned_dec 7 w.

  Lemma repr_in_unsigned_extend n1 n2 n3 w:
    n1 <= n3 -> n1 <= n2 ->
    repr_in_unsigned n2 (@zero_extend n1 n3 w).
  Proof. unfold repr_in_unsigned, zero_extend; intros.
    generalize (Word.unsigned_range w); intros.
    assert (0 <= Word.unsigned w <= Word.max_unsigned n3)%Z.
      use_lemma (@max_unsigned_mono n1 n3) by eassumption.
      unfold Word.max_unsigned in *.
      omega.
    rewrite Word.unsigned_repr by eassumption.
    use_lemma (@max_unsigned_mono n1 n2) by eassumption.
    unfold Word.max_unsigned in *.
    omega.
  Qed.

  Lemma repr_in_unsigned_byte_extend8_32 b: 
    repr_in_unsigned_byte (zero_extend8_32 b).
  Proof. unfold repr_in_unsigned_byte, zero_extend8_32; intros.
    apply repr_in_unsigned_extend; omega.
  Qed.

  Lemma zero_extend_inv1 n1 n2 (w:Word.int n2):
    n1 <= n2 -> repr_in_unsigned n1 w ->
    @zero_extend n1 n2 (@zero_extend n2 n1 w) = w.
  Proof. unfold zero_extend, repr_in_unsigned; intros.
    generalize (Word.unsigned_range w); intro.
    rewrite Word.unsigned_repr by omega.
    rewrite Word.repr_unsigned; trivial.
  Qed.

  Lemma zero_extend_inv2 n1 n2 (w:Word.int n2):
    n2 <= n1 -> @zero_extend n1 n2 (@zero_extend n2 n1 w) = w.
  Proof. unfold zero_extend. intros. 
    assert (0 <= Word.unsigned w <= Word.max_unsigned n1)%Z.
      generalize (Word.unsigned_range_2 n2 w); intros.
      use_lemma max_unsigned_mono by eassumption.
      omega.
    rewrite Word.unsigned_repr by assumption.
    rewrite Word.repr_unsigned; trivial.
  Qed.

  Lemma zero_extend8_32_inv (w:int32) : 
    repr_in_unsigned_byte w -> zero_extend8_32 (zero_shrink32_8 w) = w.
  Proof. unfold zero_extend8_32, zero_shrink32_8, repr_in_unsigned_byte. intros.
    apply zero_extend_inv1; [omega | trivial].
  Qed.

  Lemma zero_shrink32_8_inv (b:int8) : 
    zero_shrink32_8 (zero_extend8_32 b) = b.
  Proof. intros. apply zero_extend_inv2. omega. Qed.

  Hint Rewrite zero_shrink32_8_inv: inv_db.
  Hint Rewrite zero_extend8_32_inv using assumption: inv_db.

  (** * Definitions and tactics for combining a list of grammars using
        balanced ASTs *)

  (* Assume we have a list of grammars of type "wf_bigrammar pt_i". We want
     to combine them into a single grammar that produces semantic values of
     type t. One easy way of combining them is to do "(g_1 @ f_1) |\/|
     ... (g_n @ f_n)", where f_i is of type [|pt_i|] -> [|t|]. However,
     this leads to a reverse function which tries all cases and
     inefficient.

     Oftentimes, t is an inductive type and each g_i injects into one (or a
     few) case of the inductive type of t. The following definitions and
     tactics take advantage of this for more efficient reverse
     functions. Here are the general steps:

      - combine g_i using |+| to get "g_1 |+| ... |+| g_n". This doesn't
        lose any info as it generates values in an AST tree type.

      - then we need a map function that converts AST tree values to type
        t; tactic gen_ast_map is used to aotumate this process given an
        ast_env that specifies g_i and f_i.

      - for the reverse function, we should do case analysis over values of
        type t, and construct corresponding tree values. Tactic
        gen_rev_cases is used to facilitate the process by generating
        a list of functions mapping from a value to an ast tree value
       
    See the def of control_reg_p for a typical definition.
 *)
   
  (** The type for environments that include a list of grammars and
      semantic functions going from AST values to semantic values of type
      t.  An AST env is used in tactics that generate the map and the
      reverse function. *)
  Inductive AST_Env (t:type):= 
  | ast_env_nil : AST_Env t
  | ast_env_cons : 
      (* each grammar in an AST_Env including an index nat, the type of a
       grammar, the grammar, and a map function for constructing a semantic
       value given values produced by the grammar *)
      forall (n:nat) (pt:type), 
        wf_bigrammar pt -> (interp pt -> interp t) -> AST_Env t -> AST_Env t.
  Implicit Arguments ast_env_nil [t].
  Notation "{ n , g , f } ::: al" := 
    (ast_env_cons n g f al) (right associativity, at level 70).

  Fixpoint env_length t (ae:AST_Env t) :=
    match ae with
      | ast_env_nil => O
      | ast_env_cons _ _ _ _ ae' => S (env_length ae')
    end.

  (* compute ceiling(n/2) *)
  Fixpoint divide_by_two n :=
    match n with
      | O => O
      | S O => 1
      | S (S n') => S (divide_by_two n')
    end.

  (** Split the env list into two halves at the middle *)
  Fixpoint env_split t (ae:AST_Env t) := 
    let len:= env_length ae in
    let mid := divide_by_two len in
    (* using CPS to build the two lists in one pass *)
    let fix splitHelper i l k :=
        match beq_nat i mid with
          | true => k (ast_env_nil, l)
          | false => 
            match l with
              | ast_env_cons n _ g f ae' =>
                splitHelper (S i) ae'
                  (fun v => k (ast_env_cons n g (f: _ -> [|t|]) (fst v), snd v))
              | _ => (ast_env_nil, ast_env_nil) (* this case should never happen *)
            end
        end
    in splitHelper O ae (fun u => u).

  Ltac gen_ast_grammar ast_env :=
  match ast_env with
    | ast_env_cons ?n ?g ?f ast_env_nil => constr:(g)
    | ast_env_nil => never (* should not happen *)
    | _ =>
      let aepair := eval simpl in (env_split ast_env) in
      match aepair with
        | (?ael, ?aer) => 
          let g1 := gen_ast_grammar ael in
          let g2 := gen_ast_grammar aer in
          constr:(g1 |+| g2)
      end
  end.

  Ltac gen_ast_type ast_env :=
    match ast_env with
      | ast_env_cons ?n ?g ?f ast_env_nil =>
        let gt := type of g in
        match gt with
          | wf_bigrammar ?pt => pt
        end
      | ast_env_nil => unit_t (* should not happen *)
      | _ =>
        let aepair := eval simpl in (env_split ast_env) in
        match aepair with
          | (?ael, ?aer) => 
            let t1 := gen_ast_type ael in
            let t2 := gen_ast_type aer in
            constr:(sum_t t1 t2)
        end
    end.

  (** generate a map function from an AST tree to semantic values according
      to an ast_env; should not call it with ast_env_nil *)
  Ltac gen_ast_map_aux ast_env :=
  match ast_env with
    | ast_env_cons ?n ?g ?f ast_env_nil => 
      constr: (fun v => f v)
    | _ => 
      let aepair := eval simpl in (env_split ast_env) in
      match aepair with
        | (?ael, ?aer) => 
          let m1 := gen_ast_map_aux ael in
          let m2 := gen_ast_map_aux aer in
          constr:(fun v => 
                    match v with
                      | inl v1 => m1 v1
                      | inr v2 => m2 v2
                    end)
      end
  end.

  Ltac gen_ast_map ast_env := 
    let m := gen_ast_map_aux ast_env in
    eval simpl in m.

  Ltac gen_rev_case ast_env i := 
    let len := (eval compute in (env_length ast_env)) in
    let t := gen_ast_type ast_env in
    let rec gen_rev_case_aux i n t:= 
        let eq_1 := (eval compute in (beq_nat n 1)) in
        match eq_1 with
          | true => constr:(fun v: interp t => v)
          | false =>
            let n1 := (eval compute in (divide_by_two n)) in
            let b := (eval compute in (NPeano.ltb i n1)) in
            match t with
              | sum_t ?t1 ?t2 =>
                match b with
                  | true => 
                    let f := gen_rev_case_aux i n1 t1 in 
                    constr:(fun v => (inl  (f v)):(interp t))
                  | false => 
                    let n2 := (eval compute in (minus n n1)) in
                    let i1 := (eval compute in (minus i n1)) in
                    let f := gen_rev_case_aux i1 n2 t2 in
                    constr:(fun v => (inr (f v)):(interp t))
                end
            end
        end
    in gen_rev_case_aux i len t.

  Ltac gen_rev_cases ast_env := 
    let len := (eval compute in (env_length ast_env)) in
    let rec gen_rev_cases_aux i := 
        let eq_len := (eval compute in (beq_nat i len)) in
        match eq_len with
          | true => idtac
          | false => 
            let inj:=fresh "case" in
            let f := gen_rev_case ast_env i in
            let f1 := constr:(fun v => Some (f v)) in
            pose (inj:=f1); simpl in inj; 
            gen_rev_cases_aux (S i)
       end
    in let dummyf := constr:(fun v:unit => v) in
       pose (case:=dummyf);
       gen_rev_cases_aux 0.

  (** * given an ast env, generate a balanced grammar using |+|, a
        map function from ast values to values of the target type, 
        and a list of case functions for mapping from case values
        to ast values *)
  Ltac gen_ast_defs ast_env := 
    let g := gen_ast_grammar ast_env in pose (gr:=g);
    let m := gen_ast_map ast_env in pose (mp:=m);
    gen_rev_cases ast_env.

  Ltac clear_ast_defs :=
    repeat match goal with
             | [inj:= _ |- _] => compute [inj]; clear inj
           end.


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
  Proof. induction str; localsimpl; destruct (ascii_dec a "0"); crush_hyp.
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

  Ltac ibr_prover :=
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
      | _ => ibr_simpl
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
    - rewrite bitsn_of_int_inv. printable_tac.
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

  Definition reg : wf_bigrammar register_t.
    refine (field 3 @ (Z_to_register : _ -> [|register_t|])
              & (fun r => Some (register_to_Z r)) & _); 
    invertible_tac.
    - assert (0 <= v < 8)%Z.
        apply field_rng in H. lineararith.
      use_lemma register_to_Z_inv by eauto.
      crush.
    - generalize Z_to_register_inv. crush.
  Defined.

  Lemma reg_rng: forall r, in_bigrammar_rng (` reg) r.
  Proof. 
    destruct r; apply in_bigrammar_rng_map;
    [exists 0%Z | exists 1%Z | exists 2%Z | exists 3%Z |
     exists 4%Z | exists 5%Z | exists 6%Z | exists 7%Z ]; 
    (split; [(apply field_rng; lineararith) | trivial]).
  Qed.
  Hint Resolve reg_rng: ibr_rng_db.

  Definition int_n : forall n, wf_bigrammar (User_t (BitVector_t n)).
    intro;
    refine ((field (S n)) @ (@Word.repr n : _ ->  [|bitvector_t n|])
              & fun b => Some (@Word.unsigned n b) & _);
    invertible_tac.
    + assert (0 <= v <= Word.max_unsigned n)%Z.
        apply field_rng in H.
        unfold Word.max_unsigned, Word.modulus.
        rewrite two_power_nat_S in *.
        omega.
      use_lemma Word.unsigned_repr by eauto.
      crush.
    + crush.
      apply Word.repr_unsigned.
  Defined.

  Lemma in_int_n_intro:
    forall n (v: Word.int n), 
      in_bigrammar (` (int_n n)) (int_to_bool_list (S n) (Word.unsigned v)) v.
  Proof. intros. 
    eapply InMap.
    eapply in_field_intro.
    eapply Word.unsigned_range. simpl.
    rewrite Word.repr_unsigned. trivial.
  Qed.

  Lemma int_n_rng:
    forall n (v: Word.int n), in_bigrammar_rng (` (int_n n)) v.
  Proof. unfold in_bigrammar_rng. intros; eexists; eapply in_int_n_intro. Qed.
  Hint Extern 1 (in_bigrammar_rng (` (int_n _)) _) => apply int_n_rng : ibr_rng_db.

  Definition byte : wf_bigrammar byte_t := int_n 7.
  Definition halfword : wf_bigrammar half_t := int_n 15.
  Definition word : wf_bigrammar word_t := int_n 31.

  Hint Extern 1 (in_bigrammar_rng (` byte) _) => apply int_n_rng.
  Hint Extern 1 (in_bigrammar_rng (` halfword) _) => apply int_n_rng.
  Hint Extern 1 (in_bigrammar_rng (` word) _) => apply int_n_rng.

  (* I used the above grammars for halfword and word because they are
     easier for the proofs. The following defs of halfword and word from
     the old Decode.v seems to be more efficient because they accumulate
     one byte at a time.
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
  *)

  Definition tttn : wf_bigrammar condition_t. 
    refine ((field 4) @ (Z_to_condition_type : _ -> [|condition_t|])
              & (fun ct => Some (condition_type_to_Z ct)) & _);
    invertible_tac.
    - assert (0 <= v < 16)%Z.
        apply field_rng in H. lineararith.
      use_lemma condition_type_to_Z_inv by eauto.
      crush.
    - generalize Z_to_condition_type_inv. crush.
  Defined.

  Definition control_reg_env: AST_Env control_register_t := 
    {0, ! "000", (fun v => CR0 %% control_register_t)} :::
    {1, ! "010", (fun v => CR2 %% control_register_t)} :::
    {2, ! "011", (fun v => CR3 %% control_register_t)} :::
    {3, ! "100", (fun v => CR4 %% control_register_t)} :::
    ast_env_nil.

  Definition control_reg_p : wf_bigrammar control_register_t.
    gen_ast_defs control_reg_env.
    refine(gr @ (mp: _ -> [|control_register_t|])
             & (fun u =>
                  match u with
                    | CR0 => case0 ()
                    | CR2 => case1 ()
                    | CR3 => case2 ()
                    | CR4 => case3 ()
                  end)
             & _); clear_ast_defs; invertible_tac.
     - destruct_union; printable_tac.
     - destruct w; crush.
  Defined.

  (** * A bigrammar for modrm and other parsers such as immediate parsers *)

  (* Definition bitvector (n:nat) (bs:[|bits_n n|]) : Word.int n. *)

  Program Definition field_intn (n:nat) : wf_bigrammar (bitvector_t n) :=
    (field' (S n)) @ (@intn_of_bitsn n: _ -> [|bitvector_t n|])
                   & (fun i => Some (bitsn_of_intn i)) & _.

  Definition fpu_reg  : wf_bigrammar fpu_register_t := field_intn 2.
  Definition mmx_reg : wf_bigrammar mmx_register_t := field_intn 2.
  Definition sse_reg : wf_bigrammar sse_register_t := field_intn 2.

  Definition scale_p :wf_bigrammar scale_t. 
    refine ((field 2) @ (Z_to_scale : _ -> interp scale_t)
                      & (fun s => Some (scale_to_Z s)) & _);
    invertible_tac.
    - assert (0 <= v < 4)%Z.
        apply field_rng in H. lineararith.
      use_lemma scale_to_Z_inv by eauto.
      crush.
    - generalize Z_to_scale_inv. crush.
  Defined.

  Lemma scale_rng : forall s, in_bigrammar_rng (` scale_p) s.
  Proof. 
    destruct s; apply in_bigrammar_rng_map;
    [exists 0%Z | exists 1%Z | exists 2%Z | exists 3%Z];
    (split; [apply field_rng; lineararith | trivial]).
  Qed.    
  Hint Resolve scale_rng: ibr_rng_db.

  Definition reg_no_esp_env: AST_Env register_t := 
    {0, ! "000", (fun v => EAX %% register_t)} :::
    {1, ! "001", (fun v => ECX %% register_t)} :::
    {2, ! "010", (fun v => EDX %% register_t)} :::
    {3, ! "011", (fun v => EBX %% register_t)} :::
    (* esp case not allowed *)
    (* {0, ! "100", (fun v => ESX %% register_t)} ::: *)
    {4, ! "101", (fun v => EBP %% register_t)} :::
    {5, ! "110", (fun v => ESI %% register_t)} :::
    {6, ! "111", (fun v => EDI %% register_t)} :::
    ast_env_nil.

  (* This is used in a strange edge-case for modrm parsing. See the
     footnotes on p37 of the manual in the repo This is a case where I
     think intersections/complements would be nice operators *)
  (* JGM: we can handle this in the semantic action instead of the grammar, 
     so I replaced si, which used this and another pattern for [bits "100"]
     to the simpler case below -- helps to avoid some explosions in the 
     definitions. *)
  Definition reg_no_esp : wf_bigrammar register_t. 
    gen_ast_defs reg_no_esp_env.
    refine (gr @ (mp: _ -> [|register_t|])
               & (fun r => match r with
                          | EAX => case0 ()
                          | ECX => case1 ()
                          | EDX => case2 ()
                          | EBX => case3 ()
                          | ESP => None
                          | EBP => case4 ()
                          | ESI => case5 ()
                          | EDI => case6 ()
                        end)
               & _); clear_ast_defs; invertible_tac.
     - destruct_union; printable_tac.
     - destruct w; crush.
  Defined. 

  Lemma reg_no_esp_rng r:
    r <> ESP -> in_bigrammar_rng (` reg_no_esp) r.
  Proof. intros.
    compute - [in_bigrammar_rng bitsmatch].
    destruct r;
    break_hyp;
    match goal with
      | [H: ?V <> ?V |- _] => contradiction H; trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EAX] => 
        replace EAX with (fst fi (inl (inl (inl ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) ECX] => 
        replace ECX with (fst fi (inl (inl (inr ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EDX] => 
        replace EDX with (fst fi (inl (inr (inl ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EBX] => 
        replace EBX with (fst fi (inl (inr (inr ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EBP] => 
        replace EBP with (fst fi (inr (inl (inl ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) ESI] => 
        replace ESI with (fst fi (inr (inl (inr ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EDI] => 
        replace EDI with (fst fi (inr (inr ())))
          by trivial
      | _ => idtac
    end; ibr_prover; apply bitsmatch_rng.
  Qed.
  Hint Extern 1 (in_bigrammar_rng (` reg_no_esp) _) => 
    apply reg_no_esp_rng; discriminate: ibr_rng_db.

  Lemma reg_no_esp_neq r: in_bigrammar_rng (` reg_no_esp) r -> r <> ESP.
  Proof. intros.
    unfold in_bigrammar_rng. 
    destruct H as [s H]. simpl in H.
    in_bigrammar_inv. destruct H as [u [_ H]]. simpl in H.
    destruct_union; crush.
  Qed.

  Definition reg_no_ebp : wf_bigrammar register_t.
    refine (((! "000" |+| ! "001" |+| ! "010") |+|
             (! "011" |+|  ! "100")  (* |+| bits "101" <- this is ebp *) |+|
             (! "110" |+| ! "111"))
            @ (fun s => match s with
                          | inl (inl _) => EAX
                          | inl (inr (inl _)) => ECX
                          | inl (inr (inr _)) => EDX
                          | inr (inl (inl _)) => EBX
                          | inr (inl (inr _)) => ESP
                          | inr (inr (inl _)) => ESI
                          | inr (inr (inr _)) => EDI
                        end : interp register_t)
            & (fun r => match r with
                          | EAX => Some (inl (inl ()))
                          | ECX => Some (inl (inr (inl ())))
                          | EDX => Some (inl (inr (inr ())))
                          | EBX => Some (inr (inl (inl ())))
                          | ESP => Some (inr (inl (inr ())))
                          | EBP => None
                          | ESI => Some (inr (inr (inl ())))
                          | EDI => Some (inr (inr (inr ())))
                        end)
            & _); invertible_tac.
     - destruct_union; printable_tac.
     - destruct w; crush.
  Defined. 

  Lemma reg_no_ebp_rng r:
    r <> EBP -> in_bigrammar_rng (` reg_no_ebp) r.
  Proof. intros.
    compute - [in_bigrammar_rng bitsmatch].
    destruct r;
    break_hyp;
    match goal with
      | [H: ?V <> ?V |- _] => contradiction H; trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EAX] => 
        replace EAX with (fst fi (inl (inl ()))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) ECX] => 
        replace ECX with (fst fi (inl (inr (inl ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EDX] => 
        replace EDX with (fst fi (inl (inr (inr ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EBX] => 
        replace EBX with (fst fi (inr (inl (inl ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) ESP] => 
        replace ESP with (fst fi (inr (inl (inr ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) ESI] => 
        replace ESI with (fst fi (inr (inr (inl ())))) by trivial
      | [ |- in_bigrammar_rng (Map ?fi _) EDI] => 
        replace EDI with (fst fi (inr (inr (inr ()))))
          by trivial
      | _ => idtac
    end; ibr_prover; apply bitsmatch_rng.
  Qed.
  Hint Extern 1 (in_bigrammar_rng (` reg_no_ebp) _) => 
    apply reg_no_ebp_rng; discriminate: ibr_rng_db.

  Lemma reg_no_ebp_neq r: in_bigrammar_rng (` reg_no_ebp) r -> r <> EBP.
  Proof. intros.
    unfold in_bigrammar_rng. 
    destruct H as [s H]. simpl in H.
    in_bigrammar_inv. destruct H as [u [_ H]]. simpl in H.
    destruct_union; crush.
  Qed.

  Definition reg_no_esp_ebp : wf_bigrammar register_t.
    refine (((! "000" |+| ! "001" |+| ! "010")  |+|
             (! "011" |+| ! "110" |+| ! "111"))
             (* |+|  ! "100"  <- this is esp *) 
             (* |+| bits "101" <- this is ebp *) 
            @ (fun u => match u with
                          | inl (inl _) => EAX
                          | inl (inr (inl _)) => ECX
                          | inl (inr (inr _)) => EDX
                          | inr (inl _) => EBX
                          | inr (inr (inl _)) => ESI
                          | inr (inr (inr _)) => EDI
                        end : interp register_t)
            & (fun r => match r with
                          | EAX => Some (inl (inl ()))
                          | ECX => Some (inl (inr (inl ())))
                          | EDX => Some (inl (inr (inr ())))
                          | EBX => Some (inr (inl ()))
                          | ESP => None
                          | EBP => None
                          | ESI => Some (inr (inr (inl ())))
                          | EDI => Some (inr (inr (inr ())))
                        end)
            & _); invertible_tac.
     - destruct_union; printable_tac.
     - destruct w; crush.
  Defined. 

  Lemma reg_no_esp_ebp_rng r: 
    r <> ESP /\ r <> EBP -> in_bigrammar_rng (` reg_no_esp_ebp) r.
  Proof. intros.
    compute - [in_bigrammar_rng bitsmatch].
    destruct r;
      break_hyp;
      match goal with
        | [H: ?V <> ?V |- _] => contradiction H; trivial
        | [ |- in_bigrammar_rng (Map ?fi _) EAX] => 
          replace EAX with (fst fi (inl (inl tt))) by trivial
        | [ |- in_bigrammar_rng (Map ?fi _) ECX] => 
          replace ECX with (fst fi (inl (inr (inl tt)))) by trivial
        | [ |- in_bigrammar_rng (Map ?fi _) EDX] => 
          replace EDX with (fst fi (inl (inr (inr tt)))) by trivial
        | [ |- in_bigrammar_rng (Map ?fi _) EBX] => 
          replace EBX with (fst fi (inr (inl tt))) by trivial
        | [ |- in_bigrammar_rng (Map ?fi _) ESI] => 
          replace ESI with (fst fi (inr (inr (inl tt)))) by trivial
        | [ |- in_bigrammar_rng (Map ?fi _) EDI] => 
          replace EDI with (fst fi (inr (inr (inr tt))))
            by trivial
        | _ => idtac
      end; ibr_prover; apply bitsmatch_rng.
  Qed.
  Hint Extern 1 (in_bigrammar_rng (` reg_no_esp_ebp) _) => 
    apply reg_no_esp_ebp_rng; split; discriminate: ibr_rng_db.

  Lemma reg_no_esp_ebp_neq r: 
    in_bigrammar_rng (` reg_no_esp_ebp) r -> r <> ESP /\ r <> EBP.
  Proof. intros.
    unfold in_bigrammar_rng in H.
    destruct H as [s H]. simpl in H.
    in_bigrammar_inv.
    destruct H as [v [_ H]]. simpl in H.
    destruct_union; crush.
  Qed.

  Definition si_p: wf_bigrammar (option_t (UPair_t Scale_t Register_t)). 
    refine ((scale_p $ reg)
            @ (fun p => match snd p with 
                          | ESP => None
                          | _ => Some p
                        end %% option_t (UPair_t Scale_t Register_t))
            & (fun v => match v with
                          | None => Some (Scale1, ESP)
                          | Some (_, ESP) => None
                          | Some (s,p) => Some (s,p)
                        end)
            & _); invertible_tac.
    - destruct v as [s r]; destruct r; printable_tac; ibr_prover.
    - destruct w. 
      + destruct u as [sc r]; destruct r; crush.
      + crush.
  Defined.

  Lemma si_p_rng_some sc idx: 
    in_bigrammar_rng (` si_p) (Some (sc, idx)) -> idx <> ESP.
  Proof. unfold in_bigrammar_rng. intros sc idx H.
    destruct H as [s H].
    simpl in H.
    in_bigrammar_inv.
    destruct H as [[sc' idx'] [_ H]]. simpl in H.
    destruct idx'; crush.
  Qed.

  Lemma si_p_rng_none : in_bigrammar_rng (` si_p) None.
  Proof. unfold proj1_sig at 1; compute - [in_bigrammar_rng proj1_sig scale_p reg seq].
    match goal with
      | [ |- in_bigrammar_rng (Map ?fi ?g) None] => 
        assert (H:None = (fst fi (Scale1, ESP))) by trivial;
        rewrite H; clear H; apply in_bigrammar_rng_map2
    end; ibr_prover.
  Qed.
  Hint Resolve si_p_rng_none: ibr_rng_db.

  Definition sib_p := si_p $ reg.

  Lemma sib_p_rng_none r: in_bigrammar_rng (` sib_p) (None, r).
  Proof. intros; unfold sib_p. ibr_prover. Qed.
  Hint Resolve sib_p_rng_none: ibr_rng_db.

  Definition rm00_env: AST_Env address_t := 
    {0, reg_no_esp_ebp, 
       (fun r => mkAddress (Word.repr 0) (Some r) None %% address_t)} :::
    {1, "100" $$ si_p $ reg_no_ebp,
       (fun v => let (si,base):=v in
                 mkAddress (Word.repr 0) (Some base) si %% address_t)} :::
    {2, "100" $$ si_p $ "101" $$ word,
       (fun v => let (si,disp):=v in
                 mkAddress disp None si %% address_t)} :::
    {3, "101" $$ word,
       (fun disp => mkAddress disp None None %% address_t)} :::
    ast_env_nil.
  
  Definition rm00 : wf_bigrammar address_t.
    gen_ast_defs rm00_env.
    refine (gr @ (mp: _ -> [|address_t|])
            & (fun addr => 
                 match addr with
                   | {| addrDisp:=disp; addrBase:=None; addrIndex:=None |} =>
                     case3 disp
                   | {| addrDisp:=disp; addrBase:=None; addrIndex:=Some si |} =>
                     (* special case: disp32[index*scale]; the mod bits in mod/rm must be 00 *)
                     case2 (Some si, disp)
                   | {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=siopt |} =>
                     if (Word.eq disp Word.zero) then
                       match siopt with
                         | None => match bs with
                                     | EBP => None
                                     | ESP => case1 (None, ESP)
                                     | _ => case0 bs
                                   end
                         | Some (sc, ESP) => None
                         | Some (sc, idx) => 
                           match bs with 
                             | EBP => None
                             | _ => case1 (Some (sc, idx), bs)
                           end
                       end
                     else None
                 end)
            & _); clear_ast_defs; invertible_tac.
    - destruct_union.
      + (* case reg_no_esp_ebp *)
        rewrite Word.int_eq_refl.
        assert (v<>ESP /\ v<>EBP).
          ibr_prover. apply reg_no_esp_ebp_neq. trivial.
        destruct v; local_printable_tac.
      + (* case (! "100" $ si_p $ reg_no_ebp)) *)
        destruct v as [si base].
        rewrite Word.int_eq_refl.
        assert (base <> EBP).
          ibr_prover. apply reg_no_ebp_neq. trivial.
        destruct si as [[sc idx] | ].
        * assert (idx <> ESP).
            ibr_prover. eapply si_p_rng_some. eassumption.
          destruct idx; destruct base; local_printable_tac.
        * destruct base; local_printable_tac; ibr_prover.
      + (* case ! "100" $ si_p $ ! "101" $ word *)
        destruct v as [si disp].
        destruct si as [[sc idx] | ].
        * printable_tac.
        * printable_tac; ibr_prover; trivial.
      + (* case ! "101" $ word *)
        printable_tac.
    - destruct w.
      destruct addrBase as [bs | ].
      + (* addrBase = Some bs *)
        remember_head_in_hyp as disp_eq. 
        destruct disp_eq; [idtac | crush].
        apply Word.int_eq_true_iff2 in Hdisp_eq; subst addrDisp.
        destruct addrIndex as [[sc idx] | ].
        * (* addrIndex = Some (sc,idx) *)
          destruct idx; destruct bs; parsable_tac.
        * destruct bs; parsable_tac.
      + (* addrBase = None *)
        destruct addrIndex as [[sc idx] | ].
        * parsable_tac.
        * parsable_tac.
  Defined.

  Definition rm01 : wf_bigrammar address_t. 
    refine ((reg_no_esp $ byte |+| "100" $$ sib_p $ byte)
              @ (fun v => 
                   match v with
                     | inl (bs,disp) => 
                       (mkAddress (sign_extend8_32 disp) (Some bs) None)
                     | inr ((si,bs),disp) => 
                       (mkAddress (sign_extend8_32 disp) (Some bs) si)
                   end %% address_t)
              & (fun addr => 
                   if (repr_in_signed_byte_dec addr.(addrDisp)) then
                     match addr with
                       | {| addrDisp:=disp; addrBase:=Some bs; 
                            addrIndex:=siopt |} =>
                         match siopt with
                           | None => 
                             match bs with
                               | ESP => 
                                 Some (inr ((siopt, ESP), sign_shrink32_8 disp))
                               | _ => Some (inl (bs, sign_shrink32_8 disp))
                             end
                           | Some (_, ESP) => None
                           | _ => 
                             Some (inr ((siopt, bs), sign_shrink32_8 disp))
                         end
                       | _ => None
                     end
                   else None)
              & _ ); invertible_tac.
    - destruct_union.
      + (* case reg_no_esp $ byte *)
        destruct v as [bs disp].
        compute [addrDisp].
        generalize (repr_in_signed_byte_extend8_32 disp).
        destruct_head; [intro | intuition].
        rewrite sign_shrink32_8_inv.
        destruct bs; printable_tac; ibr_prover.
      + (* case ! "100" $ sib_p $ byte *)
        destruct v as [[si bs] disp].
        generalize (repr_in_signed_byte_extend8_32 disp).
        destruct_head; [intro | intuition].
        rewrite sign_shrink32_8_inv.
        destruct si as [[sc idx] | ].
        * assert (idx <> ESP).
            unfold sib_p in *; ibr_prover.
            eapply si_p_rng_some. eassumption.
          destruct idx; local_printable_tac.
        * destruct bs; printable_tac; ibr_prover.
    - destruct w. compute [X86Syntax.addrDisp] in *.
      destruct (repr_in_signed_byte_dec addrDisp); [idtac | discriminate].
      destruct addrBase as [bs | ].
      + (* addrBase = Some bs *)
        destruct addrIndex as [[sc idx] | ].
        * (* addrIndex = Some (sc,idx) *)
          destruct idx; parsable_tac.
        * destruct bs; parsable_tac.
      + (* addrBase = None *)
        destruct addrIndex as [[sc idx] | ]; parsable_tac.
  Defined.

  Definition rm10 : wf_bigrammar address_t. 
    refine ((reg_no_esp $ word |+| "100" $$ sib_p $ word)
              @ (fun v => 
                   match v with
                     | inl (bs,disp) => 
                       (mkAddress disp (Some bs) None)
                     | inr ((si,bs),disp) => 
                       (mkAddress disp (Some bs) si)
                   end %% address_t)
              & (fun addr => 
                   match addr with
                     | {| addrDisp:=disp; addrBase:=Some bs; 
                          addrIndex:=siopt |} =>
                       match siopt with
                         | None => 
                           match bs with
                             | ESP => 
                               Some (inr ((siopt, ESP), disp))
                             | _ => Some (inl (bs, disp))
                           end
                         | Some (_, ESP) => None
                         | _ => 
                           Some (inr ((siopt, bs), disp))
                       end
                     | _ => None
                     end)
              & _ ); invertible_tac.
    - destruct_union.
      + (* case reg_no_esp $ word *)
        destruct v as [bs disp].
        compute [addrDisp].
        destruct bs; printable_tac; ibr_prover.
      + (* case ! "100" $ sib_p $ byte *)
        destruct v as [[si bs] disp].
        destruct si as [[sc idx] | ].
        * assert (idx <> ESP).
            unfold sib_p in *; ibr_prover.
            eapply si_p_rng_some. eassumption.
          destruct idx; local_printable_tac.
        * destruct bs; printable_tac; ibr_prover.
    - destruct w. compute [X86Syntax.addrDisp] in *.
      destruct addrBase as [bs | ].
      + (* addrBase = Some bs *)
        destruct addrIndex as [[sc idx] | ].
        * (* addrIndex = Some (sc,idx) *)
          destruct idx; parsable_tac.
        * destruct bs; parsable_tac.
      + (* addrBase = None *)
        destruct addrIndex as [[sc idx] | ]; parsable_tac.
  Defined.

  Definition Address_op_inv op := 
    match op with
      | Address_op addr => Some addr
      | _ => None
    end.

  Definition SSE_Addr_op_inv op := 
    match op with
      | SSE_Addr_op addr => Some addr
      | _ => None
    end.

  Definition MMX_Addr_op_inv op := 
    match op with
      | MMX_Addr_op addr => Some addr
      | _ => None
    end.

  Definition FPM16_op_inv op := 
    match op with
      | FPM16_op addr => Some addr
      | _ => None
    end.

  Definition FPM32_op_inv op := 
    match op with
      | FPM32_op addr => Some addr
      | _ => None
    end.

  Definition FPM64_op_inv op := 
    match op with
      | FPM64_op addr => Some addr
      | _ => None
    end.

  Definition FPM80_op_inv op := 
    match op with
      | FPM80_op addr => Some addr
      | _ => None
    end.

  Local Ltac operand_p_tac :=
    invertible_tac; 
    match goal with
      | [ |- _ = ?w] => destruct w; crush
    end.

  Definition Reg_op_p : wf_bigrammar operand_t.
    refine(reg @ (fun r => Reg_op r : interp operand_t)
               & (fun op => match op with
                              | Reg_op r => Some r
                              | _ => None
                            end)
               & _); operand_p_tac.
  Defined.


  Definition SSE_XMM_Reg_op_p: wf_bigrammar sse_operand_t.
    refine (sse_reg @ (fun r => SSE_XMM_Reg_op r : interp sse_operand_t)
                    & (fun op => match op with
                                   | SSE_XMM_Reg_op r => Some r
                                   | _ => None
                                 end)
                    & _); operand_p_tac.
  Defined.

  Definition SSE_GP_Reg_op_p: wf_bigrammar sse_operand_t.
    refine (reg @ (fun r => SSE_GP_Reg_op r : interp sse_operand_t)
                & (fun op => match op with
                               | SSE_GP_Reg_op r => Some r
                               | _ => None
                             end)
                & _); operand_p_tac.
  Defined.

  Definition SSE_MM_Reg_op_p: wf_bigrammar sse_operand_t.
    refine (mmx_reg @ (fun r => SSE_MM_Reg_op r : interp sse_operand_t)
                & (fun op => match op with
                               | SSE_MM_Reg_op r => Some r
                               | _ => None
                             end)
                & _); operand_p_tac.
  Defined.

  Definition MMX_Reg_op_p: wf_bigrammar mmx_operand_t.
    refine (mmx_reg @ (fun r => MMX_Reg_op r : interp mmx_operand_t)
                    & (fun op => match op with 
                                   | MMX_Reg_op r => Some r
                                   | _ => None
                                 end)
                    & _); operand_p_tac.
  Defined.

  (* same as modrm_gen but no mod "11" case;
     that is, the second must produce an address in a mem operand *)
  (* using |\/| below as it's messy to distinguish the three cases in the inverse 
     function *)
  Program Definition modrm_gen_noreg (reg_t: type) 
    (reg_p: wf_bigrammar reg_t) 
    : wf_bigrammar (pair_t reg_t address_t) := 
           ("00" $$ reg_p $ rm00)
      |\/| ("01" $$ reg_p $ rm01)
      |\/| ("10" $$ reg_p $ rm10).
  Implicit Arguments modrm_gen_noreg [reg_t].

  (* Definition modrm_gen_noreg2 (reg_t res_t: type) *)
  (*   (reg_p: wf_bigrammar reg_t)  *)
  (*   (addr_op: funinv address_t res_t)  (* the constructor that converts an *) *)
  (*                                      (* address to result and its inverse *) *)
  (*   (pf: strong_invertible addr_op) *)
  (*   : wf_bigrammar (pair_t reg_t res_t). *)
  (*   intros. *)
  (*   refine ((modrm_gen_noreg reg_p) *)
  (*             @ (fun v => match v with *)
  (*                           | (r, addr) => (r, fst addr_op addr) *)
  (*                         end %% (pair_t reg_t res_t)) *)
  (*             & (fun u => match u with *)
  (*                           | (r, op2) => *)
  (*                             match snd addr_op op2 with *)
  (*                               | Some addr => Some (r, addr) *)
  (*                               | None => None *)
  (*                             end *)
  (*                         end) *)
  (*             & _); invertible_tac; *)
  (*   destruct addr_op as [f1 f2]; *)
  (*   unfold strong_invertible in pf; simpl in pf; *)
  (*   destruct pf as [pf1 pf2]. *)
  (*   - exists v. destruct v as [res addr]. *)
  (*     rewrite pf1. intuition. *)
  (*   - destruct v as [res addr]. *)
  (*     destruct w as [op1 op2]. *)
  (*     remember_rev (f2 op2) as fo. destruct fo. *)
  (*     + rewrite (pf2 addr op2); clear pf1 pf2 H; crush. *)
  (*     + discriminate. *)
  (* Defined. *)
  (* Implicit Arguments modrm_gen_noreg2 [reg_t res_t]. *)

  (** a general modrm grammar for integer, floating-point, sse, mmx instructions *)
  Definition modrm_gen (reg_t: type) 
    (reg_p : wf_bigrammar reg_t)  (* the grammar that parse a register *)
    : wf_bigrammar (sum_t (pair_t reg_t address_t) (pair_t reg_t reg_t)) :=
    modrm_gen_noreg reg_p |+| "11" $$ reg_p $ reg_p.
  Implicit Arguments modrm_gen [reg_t].

  (* Similar to mod/rm grammar except that the register field is fixed to a
   * particular bit-pattern, and the pattern starting with "11" is excluded. *)
  Program Definition ext_op_modrm_noreg_ret_addr
          (bs: string) : wf_bigrammar address_t :=
         ("00" $$ bs $$ rm00)
    |\/| ("01" $$ bs $$ rm01)
    |\/| ("10" $$ bs $$ rm10).

  Definition ext_op_modrm_noreg (bs: string): wf_bigrammar operand_t.
    intros;
    refine(ext_op_modrm_noreg_ret_addr bs
             @ (Address_op: [|address_t|] -> [|operand_t|])
             & Address_op_inv & _); unfold Address_op_inv; invertible_tac.
    - destruct w; parsable_tac.
  Defined.

  (* Similar to mod/rm grammar except that the register field is fixed to a
   * particular bit-pattern*)
  Definition ext_op_modrm_gen (reg_t: type)
    (reg_p: wf_bigrammar reg_t)
    (bs:string) : wf_bigrammar (sum_t address_t reg_t) :=
    ext_op_modrm_noreg_ret_addr bs |+| "11" $$ bs $$ reg_p.
  Implicit Arguments ext_op_modrm_gen [reg_t].

  (** modrm_reg returns a register as the first operand, and a second operand *)
  Definition modrm_ret_reg: wf_bigrammar (pair_t register_t operand_t).
    refine ((modrm_gen reg) 
            @ (fun v =>
                 match v with
                   | inl (r, addr) => (r, Address_op addr)
                   | inr (r1, r2) => (r1, Reg_op r2)
                 end %% (pair_t register_t operand_t))
            & (fun u => 
                 match u with
                   | (r, Address_op addr) => Some (inl (r, addr))
                   | (r1, Reg_op r2) => Some (inr (r1, r2))
                   | _ => None
                 end)
            & _); invertible_tac.
    - destruct_union; destruct v; printable_tac.
    - destruct w as [r op]; destruct op; parsable_tac.
  Defined.

  (** this version returns two operands *)
  Definition modrm: wf_bigrammar (pair_t operand_t operand_t).
    refine (modrm_ret_reg
              @ (fun v => match v with
                            | (r1, op2) => (Reg_op r1, op2)
                          end %% (pair_t operand_t operand_t))
              & (fun u => match u with
                            | (Reg_op r1, op2) => Some (r1, op2)
                            | _ => None
                          end)
              & _); invertible_tac.
    destruct v; destruct w as [op1 op2]; destruct op1; parsable_tac.
  Defined.

  Definition modrm_mmx : wf_bigrammar (pair_t mmx_register_t mmx_operand_t).
    refine ((modrm_gen mmx_reg)
            @ (fun v =>
                 match v with
                   | inl (r, addr) => (r, MMX_Addr_op addr)
                   | inr (r1, r2) => (r1, MMX_Reg_op r2)
                 end %% (pair_t mmx_register_t mmx_operand_t))
            & (fun u => 
                 match u with
                   | (r, MMX_Addr_op addr) => Some (inl (r, addr))
                   | (r1, MMX_Reg_op r2) => Some (inr (r1, r2))
                   | _ => None
                 end)
            & _); invertible_tac.
    - destruct_union; destruct v; printable_tac.
    - destruct w as [r op]; destruct op; parsable_tac.
  Defined.

  (* mod xmmreg r/m in manual*)
  Definition modrm_xmm : wf_bigrammar (pair_t sse_register_t sse_operand_t).
    refine ((modrm_gen sse_reg)
            @ (fun v =>
                 match v with
                   | inl (r, addr) => (r, SSE_Addr_op addr)
                   | inr (r1, r2) => (r1, SSE_XMM_Reg_op r2)
                 end %% (pair_t sse_register_t sse_operand_t))
            & (fun u => 
                 match u with
                   | (r, SSE_Addr_op addr) => Some (inl (r, addr))
                   | (r1, SSE_XMM_Reg_op r2) => Some (inr (r1, r2))
                   | _ => None
                 end)
            & _); invertible_tac.
    - destruct_union; destruct v; printable_tac.
    - destruct w as [r op]; destruct op; parsable_tac.
  Defined.

  (* mod mmreg r/m (no x) in manual; this uses mmx regs in sse instrs *)
  Definition modrm_mm : wf_bigrammar (pair_t mmx_register_t sse_operand_t).
    refine ((modrm_gen mmx_reg)
            @ (fun v =>
                 match v with
                   | inl (r, addr) => (r, SSE_Addr_op addr)
                   | inr (r1, r2) => (r1, SSE_MM_Reg_op r2)
                 end %% (pair_t mmx_register_t sse_operand_t))
            & (fun u => 
                 match u with
                   | (r, SSE_Addr_op addr) => Some (inl (r, addr))
                   | (r1, SSE_MM_Reg_op r2) => Some (inr (r1, r2))
                   | _ => None
                 end)
            & _); invertible_tac.
    - destruct_union; destruct v; printable_tac.
    - destruct w as [r op]; destruct op; parsable_tac.
  Defined.

  Definition modrm_noreg : wf_bigrammar (pair_t register_t address_t) :=
    modrm_gen_noreg reg.

  Definition modrm_bv2_noreg: wf_bigrammar (pair_t (bitvector_t 2) address_t) :=
    modrm_gen_noreg (field_intn 2).
  Notation modrm_xmm_noreg := modrm_bv2_noreg.
  Notation modrm_mm_noreg := modrm_bv2_noreg.

 (* note: can be replaced by modrm_noreg since it now produces register_t, address_t *)
  (* general-purpose regs used in SSE instructions *)
  (* Definition modrm_xmm_gp_noreg : wf_bigrammar (pair_t register_t address_t) := *)
  (*   modrm_gen_noreg reg. *)

  Definition ext_op_modrm (bs: string): wf_bigrammar operand_t.
    intros.
    refine ((ext_op_modrm_gen reg bs)
              @ (fun v => match v with
                            | inl addr => Address_op addr
                            | inr r => Reg_op r
                          end %% operand_t)
              & (fun u => match u with
                            | Address_op addr => Some (inl addr)
                            | Reg_op r => Some (inr r)
                            | _ => None
                          end)
              & _); invertible_tac.
    - destruct v; printable_tac.
    - destruct v; destruct w; parsable_tac.
  Defined.

  (** An parser that parses immediates; takes the opsize override into account; 
      always returns a word *)
  Definition imm_p (opsize_override: bool) : wf_bigrammar word_t. 
    intros.
    refine(match opsize_override with
             | false => word 
             | true => halfword @ (fun w => sign_extend16_32 w %% word_t)
                                & (fun w => 
                                     if repr_in_signed_halfword_dec w then
                                       Some (sign_shrink32_16 w)
                                     else None
                                  )
                                  & _
           end); invertible_tac.
    - rewrite sign_shrink32_16_inv. 
      generalize (repr_in_signed_byte_extend16_32 v); intro.
      destruct_head; [printable_tac | intuition].
    - destruct (repr_in_signed_halfword_dec w); parsable_tac.
  Defined.

  (** ** Lemmas about previous parsers *)

  Lemma modrm_gen_noreg_rng_inv reg_t (reg_p: wf_bigrammar reg_t)
        (r:[|reg_t|]) (addr:[|address_t|]):
    in_bigrammar_rng (` (modrm_gen_noreg reg_p)) (r,addr) ->
    in_bigrammar_rng (` reg_p) r.
  Proof. unfold modrm_gen_noreg; intros.
    ibr_prover; destruct H.
    - ibr_prover. 
    - ibr_prover; destruct H; ibr_prover.
  Qed.

  Lemma ext_op_modrm_rng_inv (bs:string) op :
    in_bigrammar_rng (` (ext_op_modrm bs)) op ->
    (exists r, op = Reg_op r) \/ (exists addr, op = Address_op addr).
  Proof. unfold ext_op_modrm; intros; ibr_prover.
    destruct v; subst op; [right | left]; eexists; trivial.
  Qed.

  Lemma Reg_op_p_rng op : 
    (exists r, op = Reg_op r) <-> in_bigrammar_rng (`Reg_op_p) op.
  Proof. intros. unfold Reg_op_p; split; intro; ibr_prover.
    - compute [fst]. generalize reg_rng. crush.
    - crush.
  Qed.

  Lemma Reg_op_p_rng2 r: in_bigrammar_rng (`Reg_op_p) (Reg_op r).
  Proof. intros; apply Reg_op_p_rng. eexists; trivial. Qed.
  Hint Resolve Reg_op_p_rng2: ibr_rng_db.

  Lemma modrm_ret_reg_rng_inv r op:
    in_bigrammar_rng (` modrm_ret_reg) (r,op) -> 
    (exists r, op = Reg_op r) \/ (exists addr, op = Address_op addr).
  Proof. unfold modrm_ret_reg; intros. ibr_prover.
    destruct v as [[r1 addr] | [r1 r2]]; clear H0.
    - right. crush. 
    - left. crush. 
  Qed.

  (* with more work, this lemma could be made more general; will do it if necessary *)
  Lemma modrm_ret_reg_rng r1 r2: in_bigrammar_rng (` modrm_ret_reg) (r1, Reg_op r2).
  Proof. intros. unfold modrm_ret_reg, modrm_gen. ibr_prover. compute [fst].
    exists (inr [|pair_t register_t address_t|] (r1, r2)).
    split; [ibr_prover | trivial].
  Qed.
  Hint Resolve modrm_ret_reg_rng: ibr_rng_db.

  Lemma imm_p_false_rng w: in_bigrammar_rng (` (imm_p false)) w.
  Proof. unfold imm_p; intros. ibr_prover. Qed.

  Lemma imm_p_true_rng w:
    repr_in_signed_halfword w -> 
    in_bigrammar_rng (` (imm_p true)) w.
  Proof. unfold imm_p; intros. ibr_prover. compute [fst].
    exists (sign_shrink32_16 w); split.
      - ibr_prover.
      - autorewrite with inv_db. trivial.
  Qed.

  Lemma imm_p_rng w opsize_override:
    repr_in_signed_halfword w -> 
    in_bigrammar_rng (` (imm_p opsize_override)) w.
  Proof. destruct opsize_override; intros.
    - apply imm_p_true_rng; trivial.
    - apply imm_p_false_rng.
  Qed.

  (** * An X86 bigrammar *)
  (* A better bigrammar for x86 instruction decoder/encoder. The encoder
     spec is more efficient:

     (1) Each individual instruction parser does not return values of
         instr, but instead returns the instruction's arguments; as a
         result, the inverse function does not need to perform a runtime
         test to see what instruction it is as the previous version
         does. At the top level, we disjoint union all instruction parsers
         and use a conversion function to convert abstract syntax trees
         (ast) produced by parsing to instructions.

     (2) The Jcc parser uses the biased union for the two sub-parsers, 
         avoiding runtime tests in those subparsers
   *)

  (* a tactic used to simplify proofs when proving bidirectional grammars *)
  Local Ltac bg_pf_sim :=
    ibr_prover;
    repeat match goal with
      | [ |- context[repr_in_signed_byte_dec ?i]] => 
        destruct (repr_in_signed_byte_dec i)
      | [ H: context[repr_in_signed_byte_dec ?i] |- _] =>
        destruct (repr_in_signed_byte_dec i)
      | [ H: ~ (repr_in_signed_byte (sign_extend8_32 ?i)) |- _ ] =>
        contradict H; apply repr_in_signed_byte_extend8_32

      | [ |- context[repr_in_unsigned_byte_dec ?i]] => 
        destruct (repr_in_unsigned_byte_dec i) 
      | [ H: context[repr_in_unsigned_byte_dec ?i] |- _] =>
        destruct (repr_in_unsigned_byte_dec i)
      | [H: ~ (repr_in_unsigned_byte (zero_extend8_32 ?i)) |- _ ] =>
        contradict H; apply repr_in_unsigned_byte_extend8_32

      | [H: in_bigrammar_rng (` (modrm_ret_reg)) (?r1 ?op2) |- _] => 
        let H2 := fresh "H" in
        generalize (modrm_ret_reg_rng_inv H); intro H2;
        destruct H2 as [H2 | H2]; destruct H2; subst op2
      | [H: in_bigrammar_rng (` (ext_op_modrm _)) ?op |- _] => 
        let H2 := fresh "H" in
        generalize (ext_op_modrm_rng_inv H); intro H2;
        destruct H2 as [H2 | H2]; destruct H2; subst op
    end.

  Definition AAA_p : wf_bigrammar unit_t := ! "00110111".
  Definition AAD_p : wf_bigrammar unit_t := ! "1101010100001010".
  Definition AAM_p : wf_bigrammar unit_t := ! "1101010000001010".
  Definition AAS_p : wf_bigrammar unit_t := ! "00111111".

  Definition logic_or_arith_env (opsize_override: bool) (opcode1 opcode2: string) : 
    AST_Env (pair_t bool_t (pair_t operand_t operand_t)) :=
    (* register/memory to register and vice versa -- the d bit specifies
       the direction. *)
    {0, opcode1 $$ "0" $$ anybit $ anybit $ modrm_ret_reg,
     fun v => match v with
                | (d, (w, (r1, op2))) => 
                  if (d:bool) then (w, (Reg_op r1, op2)) else (w, (op2, Reg_op r1))
              end %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* sign extend immediate byte to register *)
    {1, "1000" $$ "0011" $$ "11" $$ opcode2 $$ reg $ byte,
     fun v => let (r, imm) := v in
                  (true, (Reg_op r, Imm_op (sign_extend8_32 imm)))
              %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* zero-extend immediate byte to register *)
    {2, "1000" $$ "0000" $$ "11" $$ opcode2 $$ reg $ byte,
     fun v => let (r,imm) := v in
                  (false, (Reg_op r, Imm_op (zero_extend8_32 imm)))
              %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* immediate word to register *)
    {3, "1000" $$ "0001" $$ "11" $$ opcode2 $$ reg $ imm_p opsize_override,
     fun v => let (r, imm) := v in (true, (Reg_op r, Imm_op imm))
              %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* zero-extend immediate byte to EAX *)
    {4, opcode1 $$ "100" $$ byte,
     fun imm => (false, (Reg_op EAX, Imm_op (zero_extend8_32 imm)))
              %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* word to EAX *)
    {5, opcode1 $$ "101" $$ imm_p opsize_override,
     fun imm => (true, (Reg_op EAX, Imm_op imm))
              %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* zero-extend immediate byte to memory *)
    {6, "1000" $$ "0000" $$ ext_op_modrm_noreg_ret_addr opcode2 $ byte,
     fun v => let (addr,imm) := v in 
              (false, (Address_op addr, Imm_op (zero_extend8_32 imm)))
              %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* sign-extend immediate byte to memory *)
    {7, "1000" $$ "0011" $$ ext_op_modrm_noreg_ret_addr opcode2 $ byte,
     fun v => let (addr,imm) := v in 
              (true, (Address_op addr, Imm_op (sign_extend8_32 imm)))
              %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* immediate word to memory *)
    {8, "1000" $$ "0001" $$ ext_op_modrm_noreg_ret_addr opcode2 $
               imm_p opsize_override,
     fun v => let (addr,imm) := v in 
              (true, (Address_op addr, Imm_op imm))
              %% pair_t bool_t (pair_t operand_t operand_t)} :::
    ast_env_nil.


  (* The parsing for ADC, ADD, AND, CMP, OR, SBB, SUB, and XOR can be shared *)
  Definition logic_or_arith_p (opsize_override: bool)
    (opcode1 : string) (* first 5 bits for most cases *)
    (opcode2 : string) (* when first 5 bits are 10000, the next byte has 3 bits
                      that determine the opcode *)
    : wf_bigrammar (pair_t bool_t (pair_t operand_t operand_t)).
    intros.
    gen_ast_defs (logic_or_arith_env opsize_override opcode1 opcode2).
    refine(
        (gr @ (mp: _ -> [| pair_t bool_t (pair_t operand_t operand_t) |])
            & (fun u: [|pair_t bool_t (pair_t operand_t operand_t)|] =>
               let (w, ops) := u in
               let (op1, op2) := ops in
               match op1 with
                 | Reg_op r1 => 
                   match op2 with
                     | Reg_op r2 =>
                       (* alternate encoding:  
                          set the d bit false and reverse the two regs *)
                       case0 (true, (w, (r1, Reg_op r2)))
                     | Address_op a =>
                       case0 (true, (w, (r1, Address_op a)))
                     | Imm_op imm => 
                       match r1 with
                         | EAX =>
                           (* alternate encoding: use case 1, 2 and 3 above *)
                           if w then case5 imm
                           else
                             if (repr_in_unsigned_byte_dec imm) then
                               case4 (zero_shrink32_8 imm)
                             else None
                         | _ =>
                           if w then
                             if (repr_in_signed_byte_dec imm) then
                               case1 (r1, (sign_shrink32_8 imm))
                             else
                               case3 (r1, imm)
                           else
                             if (repr_in_unsigned_byte_dec imm) then
                               case2 (r1, (zero_shrink32_8 imm))
                             else None
                       end
                     | _ => None
                   end
                 | Address_op a =>
                   match op2 with
                     | Reg_op r2 =>
                       case0 (false, (w, (r2, Address_op a)))
                     | Imm_op imm => 
                       if w then
                         if (repr_in_signed_byte_dec imm) then
                           case7 (a, (sign_shrink32_8 imm))
                         else
                           case8 (a, imm)
                       else 
                         if (repr_in_unsigned_byte_dec imm) then
                           case6 (a, (zero_shrink32_8 imm))
                         else None
                     | _ => None
                   end
                 | _ => None
               end)
            & _)); clear_ast_defs; invertible_tac.
  - destruct_union.
    + (* case 0 *)
      destruct v as [d [w [r1 op2]]].
      destruct d; bg_pf_sim; printable_tac; ibr_prover.
    + (* case 1 *)
      destruct v as [r b]. bg_pf_sim.
      destruct r; printable_tac; ibr_prover.
      (* EAX case *)
      apply imm_p_rng; apply repr_in_signed_extend; omega.
    + (* case 2 *)
      destruct v as [r b]; bg_pf_sim.
      destruct r; printable_tac; ibr_prover.
    + (* case 3 *)
      destruct v as [r op2]; bg_pf_sim;
      destruct r; printable_tac; ibr_prover.
    + (* case 4 *)
      bg_pf_sim.
      printable_tac; ibr_prover.
    + (* case 5 *)
      ibr_prover. printable_tac; ibr_prover.
    + (* case 6 *)
      destruct v as [op b]. bg_pf_sim.
      printable_tac. ibr_prover.
    + (* case 7 *)
      destruct v as [op b]. bg_pf_sim.
      printable_tac; ibr_prover.
    + (* case 8 *)
      destruct v as [op1 op2]; bg_pf_sim;
      printable_tac; ibr_prover.
  - destruct w as [wd [op1 op2]].
    destruct op1; try parsable_tac.
    + (* op1 = Reg_op _ *)
      destruct op2; try parsable_tac.
      destruct r; destruct wd; bg_pf_sim; parsable_tac.
    + (* op1 = Address_op _ *)
      destruct op2; try parsable_tac.
      destruct wd; bg_pf_sim; parsable_tac.
  Defined.

  Definition ADC_p s := logic_or_arith_p s "00010" "010".
  Definition ADD_p s := logic_or_arith_p s "00000" "000".
  Definition AND_p s := logic_or_arith_p s "00100" "100".
  Definition CMP_p s := logic_or_arith_p s "00111" "111".
  Definition OR_p  s := logic_or_arith_p s "00001" "001".
  Definition SBB_p s := logic_or_arith_p s "00011" "011".
  Definition SUB_p s := logic_or_arith_p s "00101" "101".
  Definition XOR_p s := logic_or_arith_p s "00110" "110".

  Definition ARPL_p := "0110" $$ "0011" $$ modrm.
  Definition BOUND_p := "0110" $$ "0010" $$ modrm.
  Definition BSF_p := "0000" $$ "1111" $$ "1011" $$ "1100" $$ modrm.
  Definition BSR_p := "0000" $$ "1111" $$ "1011" $$ "1101" $$ modrm.
  Definition BSWAP_p : wf_bigrammar register_t := 
    "0000" $$ "1111" $$ "1100" $$ "1" $$ reg.

  Definition bit_test_env (opcode1 opcode2: string) : 
    AST_Env (pair_t operand_t operand_t) :=
    (* bit base a reg; bit offset a byte *)
    {0, "0000" $$ "1111" $$ "1011" $$ "1010" $$ "11" $$ opcode1 $$ reg $ byte,
     fun v => let (r1,b):=v in (Reg_op r1, Imm_op (zero_extend8_32 b))
                %% pair_t operand_t operand_t} :::
    (* bit base an address; bit offset a byte *)
    {1, "0000" $$ "1111" $$ "1011" $$ "1010"
               $$ ext_op_modrm_noreg_ret_addr opcode1 $ byte,
     fun v => let (addr,b):=v in (Address_op addr, Imm_op (zero_extend8_32 b))
                %% pair_t operand_t operand_t} :::
    (* bit base a reg or an address; bit offset a reg *)
    {2, "0000" $$ "1111" $$ "101" $$ opcode2 $$ "011" $$ modrm_ret_reg,
     fun v => let (r2,op1):=v in (op1, Reg_op r2)
                %% pair_t operand_t operand_t} :::
    ast_env_nil.

  Definition bit_test_p (opcode1:string) (opcode2:string) : 
    wf_bigrammar (pair_t operand_t operand_t).
    intros. gen_ast_defs (bit_test_env opcode1 opcode2).
    refine (gr @ (mp: _ -> [|pair_t operand_t operand_t|])
              & (fun u: [|pair_t operand_t operand_t|] =>
                   let (op1,op2):=u in
                   match op1 with
                     | Reg_op r1 =>
                       match op2 with
                         | Imm_op b =>
                           if repr_in_unsigned_byte_dec b
                           then case0 (r1, zero_shrink32_8 b)
                           else None
                           (* alternative encoding possible: switch the two register operands *)
                         | Reg_op r2 => case2 (r2,op1)
                         | _ => None
                       end
                     | Address_op addr =>
                       match op2 with
                         | Imm_op b =>
                           if repr_in_unsigned_byte_dec b
                           then case1 (addr, zero_shrink32_8 b)
                           else None
                         | Reg_op r2 => case2 (r2,op1)
                         | _ => None
                       end
                     | _ => None
                   end)
              & _); clear_ast_defs; invertible_tac.
    - destruct_union.
      + (* case 0 *)
         destruct v as [r1 b]. bg_pf_sim. printable_tac. ibr_prover.
      + (* case 1 *)
        destruct v as [addr b]. bg_pf_sim. printable_tac. ibr_prover.
      + (* case 2 *)
        destruct v as [r1 op2]. 
        bg_pf_sim; printable_tac; ibr_prover.
    - destruct w as [op1 op2]; destruct op1; destruct op2;
      bg_pf_sim; parsable_tac.
  Defined.

  Definition BT_p := bit_test_p "100" "00".
  Definition BTC_p := bit_test_p "111" "11".
  Definition BTR_p := bit_test_p "110" "10".
  Definition BTS_p := bit_test_p "101" "01".

 (* to be organized *)

  (* todo: move earlier *)
  Definition selector_t := BitVector_t 15.

(* todo: record errors in enc_bit_test *)

  Definition CALL_p : 
    wf_bigrammar (pair_t bool_t (pair_t bool_t (pair_t operand_t (option_t selector_t)))).
    refine((((* case 0 *)
             "1110" $$ "1000" $$ word |+|
             (* case 1 *)
             "1111" $$ "1111" $$ ext_op_modrm "010")
              |+|
            ((* case 2 *)
             "1001" $$ "1010" $$ word $ halfword |+|
             (* case 3 *)
             "1111" $$ "1111" $$ ext_op_modrm "011"))
             @ (fun v =>
                  match v with
                    | inl (inl w) => (true, (false, (Imm_op w, None)))
                    | inl (inr op) => (true, (true, (op, None)))
                    | inr (inl (w,hw)) => (false, (true, (Imm_op w, Some hw)))
                    | inr (inr op) => (false, (true, (op, None)))
                  end %% pair_t bool_t (pair_t bool_t (pair_t operand_t (option_t selector_t))))
             & (fun u: [|pair_t bool_t (pair_t bool_t (pair_t operand_t (option_t selector_t)))|] => 
                  let (near, u1) := u in
                  let (absolute,opsel) := u1 in
                  match near, absolute with
                    | true, false => 
                      match opsel with
                        | (Imm_op w, None) => Some (inl (inl w))
                        | _ => None
                      end
                    | true, true =>
                      match opsel with
                        | (Reg_op _, None) 
                        | (Address_op _, None) => Some (inl (inr (fst opsel)))
                        | _ => None
                      end
                    | false, true =>
                      match opsel with
                        | (Imm_op w, Some hw) => Some (inr (inl (w,hw)))
                        | (Reg_op _, None) 
                        | (Address_op _, None) => Some (inr (inr (fst opsel)))
                        | _ => None
                      end
                    | _, _ => None
                  end)
             & _); invertible_tac.
    - destruct_union; bg_pf_sim; printable_tac; ibr_prover.
    - destruct w as [near [absolute opsel]].
      destruct near; destruct absolute; destruct opsel as [op sel];
      destruct op; destruct sel; parsable_tac.
  Defined.

  Definition CDQ_p : wf_bigrammar unit_t := "1001" $$  ! "1001".
  Definition CLC_p : wf_bigrammar unit_t := "1111" $$ ! "1000".
  Definition CLD_p : wf_bigrammar unit_t := "1111" $$ ! "1100".
  Definition CLI_p : wf_bigrammar unit_t := "1111" $$ ! "1010".
  Definition CLTS_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "0000" $$ ! "0110".
  Definition CMC_p : wf_bigrammar unit_t := "1111" $$ ! "0101".
  Definition CMPS_p : wf_bigrammar Char_t := "1010" $$ "011" $$ anybit.

  Definition CMPXCHG_p := 
   "0000" $$ "1111" $$ "1011" $$ "000" $$ anybit $ modrm.

  Definition CPUID_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "1010" $$ ! "0010".
  Definition CWDE_p : wf_bigrammar unit_t := "1001" $$ ! "1000".
  Definition DAA_p : wf_bigrammar unit_t := "0010" $$ ! "0111".
  Definition DAS_p : wf_bigrammar unit_t := "0010" $$ ! "1111".

  Definition DEC_p: wf_bigrammar (pair_t bool_t operand_t).
    refine(((* case 0 *)
            "1111" $$ "111" $$ anybit $ "11001" $$ reg |+|
            (* case 1 *)
            "0100" $$ "1" $$ reg |+|
            (* case 2 *)
            "1111" $$ "111" $$ anybit $ ext_op_modrm_noreg_ret_addr "001")
             @ (fun v =>
                  match v with
                    | inl (w,r) => (w, Reg_op r)
                    | inr (inl r) => (true, Reg_op r)
                    | inr (inr (w,addr)) => (w, Address_op addr)
                  end %% pair_t bool_t operand_t)
             & (fun u : [| pair_t bool_t operand_t |] => 
                  match (snd u) with
                    | Reg_op r => 
                      (* alternate encoding possible, when "fst u" is true.
                         use case 1 above *)
                      Some (inl (fst u, r))
                    | Address_op addr => Some (inr (inr (fst u, addr)))
                    | _ => None
                  end)
             & _); invertible_tac.
    - destruct_union; try printable_tac.
      + (* case 1 *)
        ibr_prover.
    - destruct w as [bl op]; destruct op; parsable_tac.
  Defined.

  Definition DIV_p: wf_bigrammar (pair_t bool_t operand_t).
    refine (("1111" $$ "011" $$ anybit $ "11110" $$ reg |+|
             "1111" $$ "011" $$ anybit $ ext_op_modrm_noreg_ret_addr "110")
              @ (fun v =>
                   match v with
                     | inl (w,r) => (w, Reg_op r)
                     | inr (w,addr) => (w, Address_op addr)
                   end %% pair_t bool_t operand_t)
              & (fun u: [|pair_t bool_t operand_t|] =>
                   match snd u with
                     | Reg_op r => Some (inl (fst u, r))
                     | Address_op addr => Some (inr (fst u, addr))
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union; printable_tac.
    - destruct w as [bl op]; destruct op; parsable_tac.
  Defined.

  Definition HLT_p : wf_bigrammar unit_t := "1111" $$ ! "0100".

  Definition IDIV_p: wf_bigrammar (pair_t bool_t operand_t).
    refine (("1111" $$ "011" $$ anybit $ "11111" $$ reg |+|
             "1111" $$ "011" $$ anybit $ ext_op_modrm_noreg_ret_addr "111")
              @ (fun v =>
                   match v with
                     | inl (w,r) => (w, Reg_op r)
                     | inr (w, addr) => (w, Address_op addr)
                   end %% pair_t bool_t operand_t)
              & (fun u: [|pair_t bool_t operand_t|] =>
                   match snd u with
                     | Reg_op r => Some (inl (fst u, r))
                     | Address_op addr => Some (inr (fst u, addr))
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union; printable_tac.
    - destruct w as [bl op]; destruct op; parsable_tac.
  Defined.

  Definition IMUL_p (opsize_override:bool): 
    wf_bigrammar (pair_t bool_t (pair_t operand_t (pair_t (option_t Operand_t) (option_t Word_t)))).
    intros.
    refine((((* case 0 *)
             "1111" $$ "011" $$ anybit $ ext_op_modrm "101" |+|
             (* case 1 *)
             "0000" $$ "1111" $$ "1010" $$ "1111" $$ modrm_ret_reg)
              |+|
            ((* case 2 *)
              "0110" $$ "1011" $$ modrm_ret_reg $ byte |+|
             (* case 3 *)
              "0110" $$ "1001" $$ modrm_ret_reg $ imm_p opsize_override))
             @ (fun u =>
                  match u with
                    | inl (inl (w,op1)) => (w, (op1, (None, None)))
                    | inl (inr (r1,op2)) => (false, (Reg_op r1, (Some op2, None)))
                    | inr (inl ((r1,op2),b)) =>
                      (true, (Reg_op r1, (Some op2, Some (sign_extend8_32 b))))
                    | inr (inr ((r1,op2),imm)) =>
                      (negb opsize_override, (Reg_op r1, (Some op2, Some imm)))
                  end %%
                  pair_t bool_t (pair_t operand_t (pair_t (option_t Operand_t) (option_t Word_t))))
             & (fun u:[|pair_t bool_t
                          (pair_t operand_t (pair_t (option_t Operand_t) (option_t Word_t)))|] => 
                  let (w,u1):= u in
                  let (op1,u2):= u1 in
                  match u2 with
                    | (None,None) => 
                      match op1 with
                        | Reg_op _ | Address_op _ => Some (inl (inl (w,op1)))
                        | _ => None
                      end
                    | (Some op2, None) => 
                      match w,op1,op2 with
                        | false,Reg_op r1,Reg_op _ 
                        | false,Reg_op r1,Address_op _ => Some (inl (inr (r1, op2)))
                        | _,_,_=> None
                      end
                    | (Some op2, Some imm) =>
                      match op1, op2 with
                        | Reg_op r1, Reg_op _ | Reg_op r1, Address_op _ =>
                          if w then                                                 
                            if repr_in_signed_byte_dec imm then
                              (* alternate encoding possible when imm is a byte; use case 3 *)
                              Some (inr (inl ((r1,op2), sign_shrink32_8 imm)))
                            else if opsize_override then None
                                 else Some (inr (inr ((r1,op2),imm)))
                          else if opsize_override then Some (inr (inr ((r1,op2),imm)))
                               else None
                        | _,_ => None
                      end
                    | _ => None
                  end)
             & _); invertible_tac.
    - destruct_union.
      + (* case 0 *)
        destruct v as [w op1].
        bg_pf_sim; printable_tac; ibr_prover.
      + (* case 1 *)
        destruct v as [r1 op2]. 
        bg_pf_sim; printable_tac; ibr_prover.
      + (* case 2 *)
        destruct v as [[r1 op2] b].
        bg_pf_sim; printable_tac; ibr_prover.
      + (* case 3 *)
        destruct v as [[r1 op2] imm].
        bg_pf_sim; destruct opsize_override; compute [negb];
        printable_tac; ibr_prover.
    - destruct w as [bl [op1 [w1 w2]]]. 
      destruct op1; destruct bl;
      destruct w1 as [op2 | ];
      destruct w2; try parsable_tac;
      destruct op2; destruct opsize_override;
      bg_pf_sim; parsable_tac.
  Defined.

  Definition IN_p: wf_bigrammar (pair_t char_t (User_t (Option_t Byte_t))).
    refine (("1110" $$ "010" $$ anybit $ byte |+| 
             "1110" $$ "110" $$ anybit)
              @ (fun v => 
                   match v with
                     | inl (w,b) => (w, Some b)
                     | inr w => (w, None)
                   end %% (Pair_t Char_t (User_t (Option_t Byte_t))))
              & (fun u => 
                   match u with
                     | (w, Some b) => Some (inl (w,b))
                     | (w, None) => Some (inr w)
                   end)
              & _); invertible_tac.
    - destruct_union; destruct v; crush.
    - destruct w as [c [b | ]]; try discriminate; crush.
  Defined.

  Definition INC_p: wf_bigrammar (pair_t bool_t operand_t).
    refine (("1111" $$ "111" $$ anybit $ "11000" $$ reg |+|
             "0100" $$ "0" $$ reg |+|
             "1111" $$ "111" $$ anybit $ ext_op_modrm_noreg_ret_addr "000")
              @ (fun v => 
                   match v with
                     | inl (w,r) => (w, Reg_op r)
                     | inr (inl r) => (true, Reg_op r)
                     | inr (inr (w,addr)) => (w,Address_op addr)
                   end %% pair_t bool_t operand_t)
              & (fun u: [|pair_t bool_t operand_t|] =>
                   let (w,op):=u in
                   match op with
                     | Reg_op r => 
                       if w then Some (inr (inl r)) (* alternate encoding: case 0 *)
                       else Some (inl (w,r))
                     | Address_op addr => Some (inr (inr (w,addr)))
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union; ibr_prover.
      + destruct v as [w r].
        destruct w; printable_tac; ibr_prover.
      + printable_tac; ibr_prover.
      + printable_tac; ibr_prover.
    - destruct w as [w op]; destruct op; destruct w; parsable_tac.
  Defined.

  Definition INS_p : wf_bigrammar Char_t := "0110" $$ "110" $$ anybit.
  
  Definition INTn_p : wf_bigrammar byte_t := "1100" $$ "1101" $$ byte.
  Definition INT_p : wf_bigrammar unit_t := "1100" $$ ! "1100".
  Definition INTO_p : wf_bigrammar unit_t := "1100" $$ ! "1110".
  
  Definition INVD_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "0000" $$ ! "1000".

  Definition INVLPG_p: wf_bigrammar operand_t :=
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm_noreg "111".

  Definition IRET_p: wf_bigrammar unit_t := "1100" $$ ! "1111".

  Definition Jcc_p: wf_bigrammar (pair_t condition_t word_t). 
    refine (("0111" $$ tttn $ byte |+|
             "0000" $$ "1111" $$ "1000" $$ tttn $ word)
              @ (fun v => 
                   match v with
                     | inl (ct,b) => (ct, sign_extend8_32 b)
                     | inr (ct,imm) => (ct, imm)
                   end %% pair_t condition_t word_t)
              & (fun u: [|pair_t condition_t word_t|] => 
                   let (ct,imm) := u in
                   if repr_in_signed_byte_dec imm then
                     (* alternate encoding possible: case 1 *)
                     Some (inl (ct, sign_shrink32_8 imm))
                   else Some (inr (ct, imm)))
              & _); invertible_tac.
    - destruct_union.
      + destruct v as [ct v]; bg_pf_sim; printable_tac; ibr_prover.
      + destruct v as [ct imm]; bg_pf_sim; printable_tac; ibr_prover.
    - destruct w; bg_pf_sim; parsable_tac.
  Defined.

  Definition JCXZ_p := "1110" $$ "0011" $$ byte.

  Definition JMP_env :
    AST_Env (pair_t bool_t
                    (pair_t bool_t (pair_t operand_t (option_t selector_t)))) :=
    (* near relative jump; sign extend byte *)
    {0, "1110" $$ "1011" $$ byte,
     fun b => (true, (false, (Imm_op (sign_extend8_32 b), None)))
        %% pair_t bool_t
             (pair_t bool_t (pair_t operand_t (option_t selector_t)))} :::
    (* near relative jump via a word *)
    {1, "1110" $$ "1001" $$ word,
     fun imm => (true, (false, (Imm_op imm, None)))
        %% pair_t bool_t
             (pair_t bool_t (pair_t operand_t (option_t selector_t)))} :::
    (* near absolute jump via an operand *)
    {2, "1111" $$ "1111" $$ ext_op_modrm "100",
     fun op => (true, (true, (op, None)))
        %% pair_t bool_t
             (pair_t bool_t (pair_t operand_t (option_t selector_t)))} :::
    (* far absolute jump via base and offset *) 
    {3, "1110" $$ "1010" $$ word $ halfword,
     fun v => let (base,offset):=v in 
              (false, (true, (Imm_op base, Some offset)))
        %% pair_t bool_t
             (pair_t bool_t (pair_t operand_t (option_t selector_t)))} :::
    (* far abslute jump via operand *)
    {4, "1111" $$ "1111" $$ ext_op_modrm "101",
     fun op => (false, (true, (op, None)))
        %% pair_t bool_t
             (pair_t bool_t (pair_t operand_t (option_t selector_t)))} :::
    ast_env_nil.

  Definition JMP_p: 
    wf_bigrammar (pair_t bool_t
                         (pair_t bool_t (pair_t operand_t (option_t selector_t)))).
    gen_ast_defs JMP_env.
    refine (gr @ (mp: _ ->
                      [|pair_t bool_t
                        (pair_t bool_t (pair_t operand_t (option_t selector_t)))|])
              & (fun u: [|pair_t bool_t
                           (pair_t bool_t (pair_t operand_t (option_t selector_t)))|]
                 =>
                   let (near,u1):=u in
                   let (absolute,u2):=u1 in
                   match near, absolute with
                     | true,false =>
                       match u2 with
                         | (Imm_op imm, None) =>
                           if (repr_in_signed_byte_dec imm) then
                             (* alternate encoding: case 1 *)
                             case0 (sign_shrink32_8 imm)
                           else case1 imm
                         | _ => None
                       end
                     | true,true => 
                       match u2 with
                         | (Reg_op _, None)
                         | (Address_op _, None) => case2 (fst u2)
                         | _ => None
                       end
                     | false,true =>
                       match u2 with
                         | (Imm_op base, Some offset) =>
                           case3 (base,offset)
                         | (Reg_op _, None)
                         | (Address_op _, None) =>
                           case4 (fst u2)
                         | _ => None
                       end
                     | _,_ => None
                   end)
              & _); clear_ast_defs; invertible_tac.
    - destruct_union; bg_pf_sim; printable_tac; ibr_prover.
    - destruct w as [near [absolute [op w1]]]; destruct w1;
      destruct near; destruct absolute; destruct op; bg_pf_sim; parsable_tac.
  Defined.

  Definition LAHF_p := "1001" $$ ! "1111".
  Definition LAR_p := 
    "0000" $$ "1111" $$ "0000" $$ "0010" $$ modrm.
  Definition LDS_p := "1100" $$ "0101" $$ modrm.
  Definition LEA_p: wf_bigrammar (pair_t operand_t operand_t).
    refine ("1000" $$ "1101" $$ modrm_noreg
             @ (fun v => (Reg_op (fst v), Address_op (snd v))
                           %% pair_t operand_t operand_t)
             & (fun u: [|pair_t operand_t operand_t|] => 
                  match u with
                    | (Reg_op r, Address_op addr) => Some (r,addr)
                    | _ => None
                  end)
             & _); invertible_tac.
    - destruct w as [op1 op2]; destruct op1; destruct op2; parsable_tac.
  Defined.
  Definition LEAVE_p := "1100" $$ !"1001".
  Definition LES_p := "1100" $$ "0100" $$ modrm.
  Definition LFS_p := "0000" $$ "1111" $$ "1011" $$ "0100" $$ modrm.
  Definition LGDT_p : wf_bigrammar operand_t := 
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm_noreg "010".
  Definition LGS_p := "0000" $$ "1111" $$ "1011" $$ "0101" $$ modrm.
  Definition LIDT_p := 
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm_noreg "011".

  Definition LLDT_p: wf_bigrammar operand_t. 
    refine(("0000" $$ "1111" $$ "0000" $$ "0000" $$ "11" $$ "010" $$ reg 
             |+|
            "0000" $$ "1111" $$ "0000" $$ "0000"
               $$ ext_op_modrm_noreg_ret_addr "010")
             @ (fun v =>
                  match v with
                    | inl r => Reg_op r
                    | inr addr => Address_op addr
                  end %% operand_t)
             & (fun u =>
                  match u with
                    | Reg_op r => Some (inl r)
                    | Address_op addr => Some (inr addr)
                    | _ => None
                  end)
             & _); invertible_tac.
    - destruct_union; printable_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition LMSW_p : wf_bigrammar operand_t.
    refine (("0000" $$ "1111" $$ "0000" $$ "0001" $$ "11" $$ "110" $$ reg
             |+|
             "0000" $$ "1111" $$ "0000" $$ "0001" $$ "11"
                $$ ext_op_modrm_noreg_ret_addr "110" )
             @ (fun v =>
                  match v with
                    | inl r => Reg_op r
                    | inr addr => Address_op addr
                  end %% operand_t)
             & (fun u =>
                  match u with
                    | Reg_op r => Some (inl r)
                    | Address_op addr => Some (inr addr)
                    | _ => None
                  end)
             & _); invertible_tac.
    - destruct_union; printable_tac.
    - destruct w; parsable_tac.
  Defined.

  (* JGM: note, this isn't really an instruction, but rather a prefix.  So it
     shouldn't be included in the list of instruction grammars. *)
(*  Definition LOCK_p := "1111" $$ ! "0000" *)

  Definition LODS_p := "1010" $$ "110" $$ anybit.
  Definition LOOP_p := "1110" $$ "0010" $$ byte.
  Definition LOOPZ_p := "1110" $$ "0001" $$ byte.
  Definition LOOPNZ_p := "1110" $$ "0000" $$ byte.

  Definition LSL_p := "0000" $$ "1111" $$ "0000" $$ "0011" $$ modrm.
  Definition LSS_p := "0000" $$ "1111" $$ "1011" $$ "0010" $$ modrm.
  Definition LTR_p := "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "011".

  (* This may not be right. Need to test this thoroughly. 
     There is no 8bit mode for CMOVcc *)
  Definition CMOVcc_p := "0000" $$ "1111" $$ "0100" $$ tttn $ modrm.

  Definition MOV_env (opsize_override:bool):
    AST_Env (pair_t bool_t (pair_t operand_t operand_t)) :=
    (* op2 to op1 *)
    {0, "1000" $$ "101" $$ anybit $ modrm_ret_reg,
     fun v => match v with (w,(r1,op2)) => (w,(Reg_op r1,op2)) end
        %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* op1 to op2 *)
    {1, "1000" $$ "100" $$ anybit $ modrm_ret_reg,
     fun v => match v with (w,(r1,op2)) => (w,(op2,Reg_op r1)) end
        %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* immediate to reg *)
    {2, "1100" $$ "0111" $$ "11" $$ "000" $$ reg $ imm_p opsize_override,
     fun v => match v with (r,imm) => (true, (Reg_op r, Imm_op imm)) end
        %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* zero-extend byte to reg *)
    {3, "1100" $$ "0110" $$ "11" $$ "000" $$ reg $ byte,
     fun v => match v with
                  (r,b) => (false, (Reg_op r, Imm_op (zero_extend8_32 b)))
              end
        %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* immediate to reg; alternate encoding*)
    {4, "1011" $$ "1" $$ reg $ imm_p opsize_override,
     fun v => match v with (r,imm) => (true, (Reg_op r, Imm_op imm)) end
        %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* zero-extend byte to reg; alternate encoding *)
    {5, "1011" $$ "0" $$ reg $ byte,
     fun v => match v with
                  (r,b) => (false, (Reg_op r, Imm_op (zero_extend8_32 b)))
              end
        %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* immediate to mem *)
    {6, "1100" $$ "0111" $$ ext_op_modrm_noreg_ret_addr "000"
               $ imm_p opsize_override,
     fun v => match v with
                  (addr,imm) => (true, (Address_op addr, Imm_op imm))
              end
        %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* zero-extend byte to mem *)
    {7, "1100" $$ "0110" $$ ext_op_modrm_noreg_ret_addr "000" $ byte,
     fun v => match v with
                  (addr,b) => (false, (Address_op addr, Imm_op (zero_extend8_32 b)))
              end
        %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* 32-bit memory to EAX *)
    {8, "1010" $$ "0001" $$ word,
     fun imm => (true, (Reg_op EAX, Offset_op imm))
        %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* 8-bit memory to EAX *)
    {9, "1010" $$ "0000" $$ word,
     fun imm => (false, (Reg_op EAX, Offset_op imm))
        %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* EAX to memory (update 32 bits in mem) *)
    {10, "1010" $$ "0011" $$ word,
     fun imm => (true, (Offset_op imm, Reg_op EAX))
        %% pair_t bool_t (pair_t operand_t operand_t)} :::
    (* EAX to memory (update 8 bits in mem) *)
    {11, "1010" $$ "0010" $$ word,
     fun imm => (false, (Offset_op imm, Reg_op EAX))
        %% pair_t bool_t (pair_t operand_t operand_t)} :::
    ast_env_nil.


  Definition MOV_p (opsize_override:bool): 
    wf_bigrammar (pair_t bool_t (pair_t operand_t operand_t)).
    intros. gen_ast_defs (MOV_env opsize_override).
    refine (gr @ (mp: _ -> [|pair_t bool_t (pair_t operand_t operand_t)|])
              & (fun u: [|pair_t bool_t (pair_t operand_t operand_t)|] => 
                   let (w,u1):=u in
                   let (op1,op2):=u1 in
                   match op1 with
                     | Reg_op r1 => 
                       match op2 with
                         | Reg_op _
                         | Address_op _ =>
                           (* alternate encoding when both op1 and op2 are Reg_op: 
                              case1 and swap op1 and op2 *)
                           case0 (w, (r1, op2))
                         | Imm_op imm => 
                           if w then (* use case 4; alternate encoding: case 2 *)
                             case4 (r1,imm)
                           else
                             if (repr_in_unsigned_byte_dec imm)
                             then
                             (* use case 5; alternate encoding: case 3 *)
                               case5 (r1, zero_shrink32_8 imm)
                             else None
                         | Offset_op imm => 
                           match r1 with
                             | EAX => if w then case8 imm
                                      else case9 imm
                             | _ => None
                           end
                       end
                     | Address_op addr =>
                       match op2 with
                         | Reg_op r => 
                           case1 (w,(r, Address_op addr))
                         | Imm_op imm =>
                           if w then case6 (addr,imm)
                           else 
                             if (repr_in_unsigned_byte_dec imm)
                             then case7 (addr, zero_shrink32_8 imm)
                             else None
                         | _ => None
                       end
                     | Offset_op imm => 
                       match op2 with
                         | Reg_op EAX => 
                           if w then case10 imm else case11 imm
                         | _ => None
                       end
                     | _ => None
                   end)
              & _); clear_ast_defs; invertible_tac.
    - destruct_union;
      repeat match goal with 
               | [v: [| pair_t _ _ |] |- _ ] => destruct v
             end;
      bg_pf_sim; printable_tac; ibr_prover.
    - destruct w as [wd [op1 op2]]; destruct op1; try parsable_tac;
      destruct op2; bg_pf_sim; try parsable_tac;
      destruct wd; try parsable_tac;
      destruct r; parsable_tac.
  Defined.

(* todo: implicit argument deprecated *)

  Definition MOVCR_p :=
    "0000" $$ "1111" $$ "0010" $$ "00" $$ anybit $ "0" $$ "11"
           $$ control_reg_p $ reg.

  Definition debug_reg_env : AST_Env debug_register_t := 
    {0, ! "000", (fun _ => DR0 %% debug_register_t)} :::
    {1, ! "001", (fun _ => DR1 %% debug_register_t)} :::
    {2, ! "010", (fun _ => DR2 %% debug_register_t)} :::
    {3, ! "011", (fun _ => DR3 %% debug_register_t)} :::
    {4, ! "110", (fun _ => DR6 %% debug_register_t)} :::
    {5, ! "111", (fun _ => DR7 %% debug_register_t)} :::
    ast_env_nil.
     
  (* todo: move earlier *)
  (* Note:  apparently, the bit patterns corresponding to DR4 and DR5 either
   * (a) get mapped to DR6 and DR7 respectively or else (b) cause a fault,
   * depending upon the value of some control register.  My guess is that it's
   * okay for us to just consider this a fault. Something similar seems to
   * happen with the CR registers above -- e.g., we don't have a CR1. *)
  Definition debug_reg_p : wf_bigrammar debug_register_t.
    gen_ast_defs debug_reg_env.
    refine(gr @ (mp: _ -> [|debug_register_t|])
              & (fun u => 
                   match u with
                     | DR0 => case0 ()
                     | DR1 => case1 ()
                     | DR2 => case2 ()
                     | DR3 => case3 ()
                     | DR6 => case4 ()
                     | DR7 => case5 ()
                end)
              & _); clear_ast_defs; invertible_tac.
    - destruct_union; printable_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition MOVDR_p := 
    "0000" $$ "1111" $$ "0010" $$ "00" $$ anybit $ "111" $$ debug_reg_p $ reg.

(* Todo: record changes to the structure of instruction proofs; record errors in imul *)

TBC: 

Old grammars:


  Definition segment_reg_p := 
      bits "000" @ (fun _ => ES %% segment_register_t) 
  |+| bits "001" @ (fun _ => CS %% segment_register_t) 
  |+| bits "010" @ (fun _ => SS %% segment_register_t) 
  |+| bits "011" @ (fun _ => DS %% segment_register_t) 
  |+| bits "100" @ (fun _ => FS %% segment_register_t) 
  |+| bits "101" @ (fun _ => GS %% segment_register_t).

  Definition seg_modrm : grammar (Pair_t segment_register_t operand_t) := 
    (     ("00" $$ segment_reg_p $ rm00) 
      |+| ("01" $$ segment_reg_p $ rm01)
      |+| ("10" $$ segment_reg_p $ rm10)) @
            (fun p => match p with
                      | (sr, addr) => (sr, Address_op addr)
                      end %% (Pair_t segment_register_t operand_t))
   |+| ("11" $$ segment_reg_p $ reg_op).

  Definition MOVSR_p := 
    "1000" $$ "1110" $$ seg_modrm @ 
      (fun p => MOVSR true (fst p) (snd p) %% instruction_t)
  |+|
    "1000" $$ "1100" $$ seg_modrm @ 
     (fun p => MOVSR false (fst p) (snd p) %% instruction_t).

  Definition MOVBE_p := 
    "0000" $$ "1111" $$ "0011" $$ "1000" $$ "1111" $$ "0001" $$ modrm @
    (fun p => MOVBE (snd p) (fst p) %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "0011" $$ "1000" $$ "1111" $$ "0000" $$ modrm @ 
    (fun p => MOVBE (fst p) (snd p) %% instruction_t).

  Definition MOVS_p := "1010" $$ "010" $$ anybit @ (fun x => MOVS x %% instruction_t).

  Definition MOVSX_p := "0000" $$ "1111" $$ "1011" $$ "111" $$ anybit $ modrm @
    (fun p => match p with | (w,(op1,op2)) => MOVSX w op1 op2 end %% instruction_t).

  Definition MOVZX_p := "0000" $$ "1111" $$ "1011" $$ "011" $$ anybit $ modrm @
    (fun p => match p with | (w,(op1,op2)) => MOVZX w op1 op2 end %% instruction_t).

  Definition MUL_p := 
  "1111" $$ "011" $$ anybit $ ext_op_modrm "100" @ 
    (fun p => MUL (fst p) (snd p) %% instruction_t).

  Definition NEG_p := 
  "1111" $$ "011" $$ anybit $ ext_op_modrm "011" @ 
    (fun p => NEG (fst p) (snd p) %% instruction_t).

  Definition NOP_p := 
  (* The following is the same as the encoding of "XCHG EAX, EAX"
    "1001" $$ bits "0000" @ (fun _ => NOP None %% instruction_t)
  |+| *)
    "0000" $$ "1111" $$ "0001" $$ "1111" $$ ext_op_modrm "000" @ 
    (fun op => NOP op %% instruction_t).

  Definition NOT_p := 
    "1111" $$ "011" $$ anybit $ ext_op_modrm "010" @ 
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
    "1111" $$ "1111" $$ ext_op_modrm_noreg_ret_addr "110" @ (fun x => PUSH true x %% instruction_t)
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
    "1101" $$ "000" $$ anybit $ ext_op_modrm extop @ 
    (fun p => inst (fst p) (snd p) (Imm_ri (Word.repr 1)) %% instruction_t)
  |+|
    "1101" $$ "001" $$ anybit $ ext_op_modrm extop @
    (fun p => inst (fst p) (snd p) (Reg_ri ECX) %% instruction_t)
  |+|
    "1100" $$ "000" $$ anybit $ ext_op_modrm extop $ byte @
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
  Definition SGDT_p := "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm_noreg_ret_addr "000" @ 
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
  Definition SIDT_p := ("0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm_noreg_ret_addr "001") @ 
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
  Definition STR_p := 
    "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "001" @ 
    (fun x => STR x %% instruction_t).

  Definition TEST_p (opsize_override: bool) := 
    "1111" $$ "0111" $$ ext_op_modrm "000" $ imm_op opsize_override @ 
    (fun p => TEST true (fst p) (snd p) %% instruction_t)
  |+| 
    "1111" $$ "0110" $$ ext_op_modrm "000" $ byte @ 
    (fun p => TEST false (fst p) (Imm_op (zero_extend8_32 (snd p))) %% instruction_t)
  |+|
    "1000" $$ "010" $$ anybit $ modrm @
    (fun p => match p with | (w,(op1,op2)) => TEST w op1 op2 end %% instruction_t)
  |+|
    "1010" $$ "1001" $$ imm_op opsize_override @ (fun w => TEST true w (Reg_op EAX) %% instruction_t)
  |+|
    "1010" $$ "1000" $$ byte @ 
    (fun b => TEST true (Reg_op EAX) (Imm_op (zero_extend8_32 b)) %% instruction_t).
  
  Definition UD2_p := "0000" $$ "1111" $$ "0000" $$ bits "1011" @ 
    (fun _ => UD2 %% instruction_t).

  Definition VERR_p := "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "100" @ 
    (fun x => VERR x %% instruction_t).
  Definition VERW_p := "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "101" @ 
    (fun x => VERW x %% instruction_t).
  Definition WBINVD_p := "0000" $$ "1111" $$ "0000" $$ bits "1001" @ 
    (fun _ => WBINVD %% instruction_t).
  Definition WRMSR_p := "0000" $$ "1111" $$ "0011" $$ bits "0000" @ 
    (fun _ => WRMSR %% instruction_t).
  Definition XADD_p := 
    "0000" $$ "1111" $$ "1100" $$ "000" $$ anybit $ modrm @ 
    (fun p => match p with | (w,(op1,op2)) => XADD w op2 op1 end %% instruction_t).
  Definition XCHG_p := 
    "1000" $$ "011" $$ anybit $ modrm @ 
    (fun p => match p with | (w,(op1,op2)) => XCHG w op2 op1 end %% instruction_t)
  |+|
    "1001" $$ "0" $$ reg @ (fun r => XCHG false (Reg_op EAX) (Reg_op r) %% instruction_t).

  Definition XLAT_p := "1101" $$ bits "0111" @ (fun _ => XLAT %% instruction_t).

(*Floating-Point grammars, based on tables B.17 and B-39*)
  Definition F2XM1_p := "11011" $$ "001111" $$ bits "10000" @ (fun _ => F2XM1 %% instruction_t).
  Definition FABS_p :=  "11011" $$ "001111" $$ bits "00001" @ (fun _ => FABS %% instruction_t). 

  Definition FADD_p := 
    "11011" $$ "000" $$ ext_op_modrm_FPM32_noreg "000" @ 
      (fun x => FADD true x %% instruction_t)
  |+|
    "11011" $$ "100" $$ ext_op_modrm_FPM64_noreg "000" @
      (fun x => FADD true x %% instruction_t) 
  |+|  
    "11011" $$ anybit $ "0011000" $$ fpu_reg @ (fun p => let (d,s) := p in FADD d (FPS_op s) %% instruction_t).

  Definition FADDP_p := "11011" $$ "110" $$ "11000" $$ fpu_reg @ (fun x => FADDP (FPS_op x) %% instruction_t).
  Definition FBLD_p := "11011" $$ "111" $$ ext_op_modrm_FPM64_noreg "100" @
                          (fun x => FBLD x %% instruction_t).
  Definition FBSTP_p := "11011" $$ "111" $$ ext_op_modrm_FPM64_noreg "110" @
                          (fun x => FBSTP x %% instruction_t).
  Definition FCHS_p := "11011" $$ "001111" $$ bits "00000" @ (fun _ => FCHS %% instruction_t).

  Definition FCMOVcc_p :=
    ("11011" $$ "01" $$ anybit $ "110" $$ anybit $ anybit $ fpu_reg) @
    (fun p =>
      match p with 
        (b2, (b1, (b0, s))) => 
        let n := int_of_bits 3 (b2, (b1, (b0, tt))) in
        FCMOVcc (Z_to_fp_condition_type n) (FPS_op s) %% instruction_t
      end).

  Definition FCOM_p :=
    "11011" $$ "000" $$ ext_op_modrm_FPM32_noreg "010" @
        (fun x => FCOM x %% instruction_t)
  |+|
    "11011" $$ "100" $$ ext_op_modrm_FPM64_noreg "010" @
        (fun x => FCOM x %% instruction_t) 
  |+|  
    "11011" $$ "000" $$ "11010" $$ fpu_reg @ (fun x => FCOM (FPS_op x) %% instruction_t).

  Definition FCOMP_p :=
    "11011" $$ "000" $$ ext_op_modrm_FPM32_noreg "011" @
       (fun x => FCOMP x %% instruction_t)
  |+|
    "11011" $$ "100" $$ ext_op_modrm_FPM64_noreg "011" @
       (fun x => FCOMP x %% instruction_t) 
  |+|  
    "11011" $$ "000" $$ "11011" $$ fpu_reg @ (fun x => FCOMP (FPS_op x) %% instruction_t).

  Definition FCOMPP_p := "11011" $$ "110" $$ "11011" $$ bits "001" @ (fun _ => FCOMPP %% instruction_t).
  Definition FCOMIP_p := "11011" $$ "111" $$ "11110" $$ fpu_reg @ (fun x => FCOMIP (FPS_op x) %% instruction_t).
  Definition FCOS_p := "11011" $$ "001" $$ "111" $$ bits "11111" @ (fun _ => FCOS %% instruction_t).  
  Definition FDECSTP_p := "11011" $$ "001" $$ "111" $$ bits "10110" @ (fun _=> FDECSTP %% instruction_t).

  Definition FDIV_p :=
    "11011" $$ "000" $$ ext_op_modrm_FPM32_nroeg "110" @ 
       (fun x => FDIV true x %% instruction_t)
  |+|
    "11011" $$ "100" $$ ext_op_modrm_FPM64_noreg "110" @
       (fun x => FDIV true x %% instruction_t)
  |+|  
    "11011" $$ "0" $$ "00" $$ "1111" $$ "0" $$ fpu_reg @ 
    (fun i => FDIV true (FPS_op i) %% instruction_t)
  |+| 
    "11011" $$ "1" $$ "00" $$ "111" $$ "1" $$ "1" $$ fpu_reg @ 
    (fun i => FDIV false (FPS_op i) %% instruction_t).

  Definition FDIVP_p := "11011" $$ "110" $$ "11111" $$ fpu_reg @ (fun x => FDIVP (FPS_op x) %% instruction_t).

  Definition FDIVR_p :=
    "11011" $$ "000" $$ ext_op_modrm_FPM32_noreg "111" @
       (fun x => FDIVR true x %% instruction_t)
  |+|
    "11011" $$ "100" $$ ext_op_modrm_FPM64_noreg "111" @
       (fun x => FDIVR true x  %% instruction_t)
  |+|  
    "11011" $$ "0" $$ "00" $$ "111" $$ "1" $$ "1" $$ fpu_reg @ 
    (fun i => FDIVR true (FPS_op i) %% instruction_t)
  |+|  
    "11011" $$ "1" $$ "00" $$ "111" $$ "1" $$ "0" $$ fpu_reg @ 
    (fun i => FDIVR false (FPS_op i) %% instruction_t).

  Definition FDIVRP_p := "11011" $$ "110" $$ "11110" $$ fpu_reg @ (fun x => FDIVRP (FPS_op x) %% instruction_t).
  Definition FFREE_p := "11011" $$ "101" $$ "11000" $$ fpu_reg @ (fun x => FFREE (FPS_op x) %% instruction_t).
  Definition FIADD_p := 
    "11011" $$ "110" $$ ext_op_modrm_FPM16_noreg "000" @ (fun x => FIADD x %% instruction_t)
  |+|
    "11011" $$ "010" $$ ext_op_modrm_FPM32_noreg "000" @ (fun x => FIADD x %% instruction_t).
  
  Definition FICOM_p  := 
    "11011" $$ "110" $$ ext_op_modrm_FPM16_noreg "010" @ (fun x => FICOM x %% instruction_t)
  |+|
    "11011" $$ "010" $$ ext_op_modrm_FPM32_noreg "010" @ (fun x => FICOM x %% instruction_t).

  Definition FICOMP_p  := 
    "11011" $$ "110" $$ ext_op_modrm_FPM16_noreg "011" @ (fun x => FICOMP x %% instruction_t)
  |+|
    "11011" $$ "010" $$ ext_op_modrm_FPM32_noreg "011" @ (fun x => FICOMP x %% instruction_t).

  Definition FIDIV_p  := 
    "11011" $$ "110" $$ ext_op_modrm_FPM16_noreg "110" @ (fun x => FIDIV x %% instruction_t)
  |+|
    "11011" $$ "010" $$ ext_op_modrm_FPM32_noreg "110" @ (fun x => FIDIV x %% instruction_t).

  Definition FIDIVR_p  := 
    "11011" $$ "110" $$ ext_op_modrm_FPM16_noreg "111" @ (fun x => FIDIVR x %% instruction_t)
  |+|
    "11011" $$ "010" $$ ext_op_modrm_FPM32_noreg "111" @ (fun x => FIDIVR x %% instruction_t).

  Definition FILD_p  := 
    "11011" $$ "111" $$ ext_op_modrm_FPM16_noreg "000" @ (fun x => FILD x %% instruction_t)
  |+|
    "11011" $$ "011" $$ ext_op_modrm_FPM32_noreg "000" @ (fun x => FILD x %% instruction_t)
  |+|
    "11011" $$ "111" $$ ext_op_modrm_FPM64_noreg "101" @ (fun x => FILD x %% instruction_t).
  Definition FIMUL_p := 
    "11011" $$ "110" $$ ext_op_modrm_FPM16_noreg "001" @ (fun x => FIMUL x %% instruction_t)
  |+|
    "11011" $$ "010" $$ ext_op_modrm_FPM32_noreg "001" @ (fun x => FIMUL x %% instruction_t).
  Definition FINCSTP_p := "11011" $$ "001111" $$ bits "10111" @ (fun _ => FINCSTP %% instruction_t).
  Definition FIST_p :=
    "11011" $$ "111" $$ ext_op_modrm_FPM16_noreg "010" @ (fun x => FIST x %% instruction_t)
  |+|
    "11011" $$ "011" $$ ext_op_modrm_FPM32_noreg "010" @ (fun x => FIST x %% instruction_t).

  Definition FISTP_p :=
    "11011" $$ "111" $$ ext_op_modrm_FPM16_noreg "011" @ (fun x => FISTP x %% instruction_t)
  |+|
    "11011" $$ "011" $$ ext_op_modrm_FPM32_noreg "011" @ (fun x => FISTP x %% instruction_t)
  |+|
    "11011" $$ "111" $$ ext_op_modrm_FPM64_noreg "111" @ (fun x => FISTP x %% instruction_t).

  Definition FISUB_p :=
    "11011" $$ "110" $$ ext_op_modrm_FPM16_noreg "100" @ (fun x => FISUB x %% instruction_t)
  |+|
    "11011" $$ "010" $$ ext_op_modrm_FPM32_noreg "100" @ (fun x => FISUB x %% instruction_t).

  Definition FISUBR_p :=
    "11011" $$ "110" $$ ext_op_modrm_FPM16_noreg "101" @ (fun x => FISUBR x %% instruction_t)
  |+|
    "11011" $$ "010" $$ ext_op_modrm_FPM32_noreg "101" @ (fun x => FISUBR x %% instruction_t).

  Definition FLD_p :=
    "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "000" @ (fun x => FLD x %% instruction_t)
  |+|
    "11011" $$ "101" $$ ext_op_modrm_FPM64_noreg "000" @ (fun x => FLD x %% instruction_t)
  |+|
    "11011" $$ "011" $$ ext_op_modrm_FPM80_noreg "101" @ (fun x => FLD x %% instruction_t)
  |+|
    "11011" $$ "001" $$ "11000" $$ fpu_reg @ (fun x => FLD (FPS_op x) %% instruction_t).

  Definition FLD1_p := "11011" $$ "001111" $$ bits "01000" @ (fun _ => FLD1 %% instruction_t).
  Definition FLDCW_p := "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "101" @ (fun x => FLDCW x %% instruction_t).
  Definition FLDENV_p := "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "100" @ (fun x => FLDENV x %% instruction_t).
  Definition FLDL2E_p := "11011" $$ "001111" $$ bits "01010" @ (fun _ => FLDL2E %% instruction_t). 
  Definition FLDL2T_p := "11011" $$ "001111" $$ bits "01001" @ (fun _ => FLDL2T %% instruction_t). 
  Definition FLDLG2_p := "11011" $$ "001111" $$ bits "01100" @ (fun _ => FLDLG2 %% instruction_t). 
  Definition FLDLN2_p := "11011" $$ "001111" $$ bits "01101" @ (fun _ => FLDLN2 %% instruction_t). 
  Definition FLDPI_p := "11011" $$ "001111" $$ bits "01011" @ (fun _ => FLDPI %% instruction_t).
  Definition FLDZ_p := "11011" $$ "001111" $$ bits "01110" @ (fun _ => FLDZ %% instruction_t).

  Definition FMUL_p := 
    "11011" $$ "000" $$ ext_op_modrm_FPM32_noreg "001" @ (fun x => FMUL true x %% instruction_t)
  |+|
    "11011" $$ "100" $$ ext_op_modrm_FPM64_noreg "001" @ (fun x => FMUL true x %% instruction_t) 
  |+|  
    "11011" $$ anybit $ "00" $$ "11001" $$ fpu_reg @ (fun p => let (d,s) := p in FMUL d (FPS_op s) %% instruction_t).

  Definition FMULP_p := "11011" $$ "110" $$ "11001" $$ fpu_reg @ (fun x => FMULP (FPS_op x) %% instruction_t).
  Definition FNCLEX_p := "11011" $$ "011111" $$ bits "00010" @ (fun _ => FNCLEX %% instruction_t).
  Definition FNINIT_p := "11011" $$ "011111" $$ bits "00011" @ (fun _ => FNINIT %% instruction_t).
  Definition FNOP_p := "11011" $$ "001110" $$ bits "10000" @ (fun _ => FNOP %% instruction_t).
  Definition FNSAVE_p := "11011101" $$ ext_op_modrm_FPM64_noreg "110" @ (fun x => FNSAVE x %% instruction_t).
  Definition FNSTCW_p := "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "111" @ (fun x => FNSTCW x %% instruction_t).
  Definition FNSTSW_p := 
    "11011" $$ "111" $$ "111" $$ bits "00000" @ (fun _ => FNSTSW None %% instruction_t)
  |+|
    "11011" $$ "101" $$ ext_op_modrm_FPM32_noreg "111" @ (fun x => FNSTSW (Some x) %% instruction_t).

  Definition FPATAN_p := "11011" $$ "001111" $$ bits "10011" @ (fun _ => FPATAN %% instruction_t).
  Definition FPREM_p := "11011" $$ "001111" $$ bits "11000" @ (fun _ => FPREM %% instruction_t).
  Definition FPREM1_p := "11011" $$ "001111" $$ bits "10101" @ (fun _ => FPREM1 %% instruction_t).
  Definition FPTAN_p := "11011" $$ "001111" $$ bits "10010" @ (fun _ => FPTAN %% instruction_t).
  Definition FRNDINT_p := "11011" $$ "001111" $$ bits "11100" @ (fun _ => FRNDINT %% instruction_t).

  Definition FRSTOR_p := "11011" $$ "101" $$ ext_op_modrm_FPM32_noreg "100" @ (fun x => FRSTOR x %% instruction_t).

  Definition FSCALE_p := "11011" $$ "001111" $$ bits "11101" @ (fun _ => FSCALE %% instruction_t).
  Definition FSIN_p := "11011" $$ "001111" $$ bits "11110" @ (fun _ => FSIN %% instruction_t).
  Definition FSINCOS_p := "11011" $$ "001111" $$ bits "11011" @ (fun _ => FSINCOS %% instruction_t).
  Definition FSQRT_p := "11011" $$ "001111" $$ bits "11010" @ (fun _ => FSQRT %% instruction_t).

  Definition FST_p := 
    "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "010" @ (fun x => FST x %% instruction_t)
  |+|
    "11011" $$ "101" $$ ext_op_modrm_FPM64_noreg "010" @ (fun x => FST x %% instruction_t)
  |+|
    "11011" $$ "101" $$ "11010" $$ fpu_reg @ (fun x => FST (FPS_op x) %% instruction_t).

  (* FSTCW's encoding is the same as FWAIT followed by FNSTCW *)
  (* Definition FSTCW_p := "10011011" $$ "11011" $$ "001" $$ ext_op_modrm_FPM32 "111" @ (fun x => FSTCW x %% instruction_t). *)
  Definition FSTENV_p := "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "110" @ (fun x => FSTENV x %% instruction_t).
  Definition FSTP_p := 
    "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "011" @ (fun x => FSTP x %% instruction_t)
  |+|
    "11011" $$ "101" $$ ext_op_modrm_FPM64_noreg "011" @ (fun x => FSTP x %% instruction_t)
  |+|
    "11011" $$ "011" $$ ext_op_modrm_FPM80_noreg "111" @ (fun x => FSTP x %% instruction_t) 
  |+|  
    "11011" $$ "101" $$ "11011" $$ fpu_reg @ (fun x => FSTP (FPS_op x) %% instruction_t). 

  Definition FSUB_p :=
    "11011" $$ "000" $$ ext_op_modrm_FPM32_noreg "100" @ (fun x => FSUB true x %% instruction_t)
  |+|
    "11011" $$ "100" $$ ext_op_modrm_FPM64_noreg "100" @ (fun x => FSUB true x %% instruction_t) 
  |+|  
    "11011" $$ "0" $$ "00" $$ "111" $$ "0" $$ "0" $$ fpu_reg @ 
    (fun i => FSUB true (FPS_op i) %% instruction_t)
  |+|  
    "11011" $$ "1" $$ "00" $$ "111" $$ "0" $$ "1" $$ fpu_reg @ 
    (fun i => FSUB false (FPS_op i) %% instruction_t).

  Definition FSUBP_p := "11011" $$ "110" $$ "11101" $$ fpu_reg @ (fun x => FSUBP (FPS_op x) %% instruction_t).

  Definition FSUBR_p := 
    "11011" $$ "000" $$ ext_op_modrm_FPM32_noreg "101" @ (fun x => FSUBR true x %% instruction_t)
  |+|
    "11011" $$ "100" $$ ext_op_modrm_FPM64_noreg "101" @ (fun x => FSUBR true x %% instruction_t)
  |+|  
    "11011" $$ "0" $$ "00" $$ "111" $$ "0" $$ "1" $$ fpu_reg @ 
    (fun i => FSUBR true (FPS_op i) %% instruction_t)
  |+|  
    "11011" $$ "1" $$ "00" $$ "111" $$ "0" $$ "0" $$ fpu_reg @ 
    (fun i => FSUBR false (FPS_op i) %% instruction_t).

  Definition FSUBRP_p := "11011" $$ "110" $$ "11100" $$ fpu_reg @ (fun x => FSUBRP (FPS_op x) %% instruction_t). 
  Definition FTST_p := "11011" $$ "001111" $$ bits "00100" @ (fun _ => FTST %% instruction_t).
  Definition FUCOM_p := "11011" $$ "101" $$ "11100" $$ fpu_reg @ (fun x => FUCOM (FPS_op x) %% instruction_t). 
  Definition FUCOMP_p := "11011" $$ "101" $$ "11101" $$ fpu_reg @ (fun x => FUCOMP (FPS_op x) %% instruction_t). 
  Definition FUCOMPP_p := "11011" $$ "010111" $$ bits "01001" @ (fun _ => FUCOMPP %% instruction_t).
  Definition FUCOMI_p := "11011" $$ "011" $$ "11101" $$ fpu_reg @ (fun x => FUCOMI (FPS_op x) %% instruction_t).  
  Definition FUCOMIP_p := "11011" $$ "111" $$ "11101" $$ fpu_reg @ (fun x => FUCOMIP (FPS_op x) %% instruction_t). 
  Definition FXAM_p := "11011" $$ "001111" $$ bits "00101" @ (fun _ => FXAM %% instruction_t).
  Definition FXCH_p := "11011" $$ "001" $$ "11001" $$ fpu_reg @ (fun x => FXCH (FPS_op x) %% instruction_t). 

  Definition FXTRACT_p := "11011" $$ "001" $$ "1111" $$ bits "0100" @ (fun _ => FXTRACT %% instruction_t).
  Definition FYL2X_p := "11011" $$ "001111" $$ bits "10001" @ (fun _ => FYL2X %% instruction_t).
  Definition FYL2XP1_p := "11011" $$ "001111" $$ bits "11001" @ (fun _ => FYL2XP1 %% instruction_t).
  Definition FWAIT_p := bits "10011011" @ (fun _ => FWAIT %% instruction_t).
(*End of Floating-Point grammars*)

(*MMX Grammars*)

  (* grammar for the mmx granularity bits; the byte granularity is allowed
     iff when byte is true; same as twob, fourb and eightb *)
  Definition mmx_gg_p (byte twob fourb eightb : bool) := 
    let byte_p := if byte then 
      bits "00" @ (fun _ => MMX_8 %% mmx_granularity_t)
      else never mmx_granularity_t in
    let twobytes_p := if twob then 
      bits "01" @ (fun _ => MMX_16 %% mmx_granularity_t)
      else never mmx_granularity_t in
    let fourbytes_p := if fourb then 
      bits "10" @ (fun _ => MMX_32 %% mmx_granularity_t)
      else never mmx_granularity_t in
    let eightbytes_p := if eightb then 
      bits "11" @ (fun _ => MMX_64 %% mmx_granularity_t)
      else never mmx_granularity_t in
    byte_p |+| twobytes_p |+| fourbytes_p |+| eightbytes_p.

  Definition EMMS_p := "0000" $$ "1111" $$ "0111" $$ bits "0111" @ (fun _ => EMMS %% instruction_t).
  Definition MOVD_p := 
    "0000" $$ "1111" $$ "0110" $$ "1110" $$ "11" $$ mmx_reg $ reg @ (*reg to mmxreg*)
    (fun p => let (m, r) := p in MOVD (GP_Reg_op r) (MMX_Reg_op m) %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "0111" $$ "1110" $$ "11" $$ mmx_reg $ reg @ (*reg from mmxreg*)
    (fun p => let (m, r) := p in MOVD (GP_Reg_op r) (MMX_Reg_op m) %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "0110" $$ "1110" $$ (@modrm_gen_noreg _ mmx_operand_t mmx_reg_op MMX_Addr_op) @ (*mem to mmxreg *)
    (fun p => let (op1, op2) := p in MOVD op1 op2 %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "0111" $$ "1110" $$ (@modrm_gen_noreg _ mmx_operand_t mmx_reg_op MMX_Addr_op) @ (*mem from mmxreg *)
    (fun p => let (mem, mmx) := p in MOVD mmx mem %% instruction_t).

  Definition MOVQ_p :=
    "0000" $$ "1111" $$ "0110" $$ "1111" $$ modrm_mmx @ 
    (fun p => let (op1, op2) := p in MOVQ op1 op2 %% instruction_t)
  |+|
    "0000" $$ "1111" $$ "0111" $$ "1111" $$ modrm_mmx @ 
    (fun p => let (op1, op2) := p in MOVQ op2 op1 %% instruction_t).

  Definition PACKSSDW_p := 
    "0000" $$ "1111" $$ "0110" $$ "1011" $$ modrm_mmx @ 
    (fun p => let (op1, op2) := p in PACKSSDW op1 op2 %% instruction_t).

  Definition PACKSSWB_p := 
    "0000" $$ "1111" $$ "0110" $$ "0011" $$ modrm_mmx @ 
    (fun p => let (op1, op2) := p in PACKSSWB op1 op2 %% instruction_t).

  Definition PACKUSWB_p := 
  "0000" $$ "1111" $$ "0110" $$ "0111" $$ modrm_mmx @ 
    (fun p => let (op1, op2) := p in PACKUSWB op1 op2 %% instruction_t).

  Definition PADD_p := 
  "0000" $$ "1111" $$ "1111" $$ "11" $$ mmx_gg_p true true true false $ modrm_mmx @ 
    (fun p => match p with (gg, (op1, op2)) => PADD gg op1 op2 end %% instruction_t).

  Definition PADDS_p := 
  "0000" $$ "1111" $$ "1110" $$ "11" $$ mmx_gg_p true true false false $ modrm_mmx @
    (fun p => match p with (gg, (op1, op2)) => PADDS gg op1 op2 end %% instruction_t).

  Definition PADDUS_p := 
  "0000" $$ "1111" $$ "1101" $$ "11" $$ mmx_gg_p true true false false $ modrm_mmx @
    (fun p => match p with (gg, (op1, op2)) => PADDUS gg op1 op2 end %% instruction_t).

  Definition PAND_p := 
  "0000" $$ "1111" $$ "1101" $$ "1011" $$ modrm_mmx @ 
    (fun p => let (op1, op2) := p in PAND op1 op2 %% instruction_t).

  Definition PANDN_p := 
  "0000" $$ "1111" $$ "1101" $$ "1111" $$ modrm_mmx @ 
    (fun p => let (op1, op2) := p in PANDN op1 op2 %% instruction_t).

  Definition PCMPEQ_p :=
  "0000" $$ "1111" $$ "0111" $$ "01" $$ mmx_gg_p true true true false $ modrm_mmx @
    (fun p => match p with (gg, (op1, op2)) => PCMPEQ gg op1 op2 end %% instruction_t).

  Definition PCMPGT_p := 
  "0000" $$ "1111" $$ "0110" $$ "01" $$ mmx_gg_p true true true false $ modrm_mmx @
    (fun p => match p with (gg, (op1, op2)) => PCMPGT gg op1 op2 end %% instruction_t).

  Definition PMADDWD_p := 
  "0000" $$ "1111" $$ "1111" $$ "0101" $$ modrm_mmx @ 
    (fun p => let (op1, op2) := p in PMADDWD op1 op2 %% instruction_t).

  Definition PMULHUW_p := 
  "0000" $$ "1111" $$ "1110" $$ "0100" $$ modrm_mmx @ 
    (fun p => let (op1, op2) := p in PMULHUW op1 op2 %% instruction_t).

  Definition PMULHW_p := 
  "0000" $$ "1111" $$ "1110" $$ "0101" $$ modrm_mmx @ 
    (fun p => let (op1, op2) := p in PMULHW op1 op2 %% instruction_t).

  Definition PMULLW_p := 
  "0000" $$ "1111" $$ "1101" $$ "0101" $$ modrm_mmx @ 
    (fun p => let (op1, op2) := p in PMULLW op1 op2 %% instruction_t).

  Definition POR_p := 
  "0000" $$ "1111" $$ "1110" $$ "1011" $$ modrm_mmx @ 
    (fun p => let (op1, op2) := p in POR op1 op2 %% instruction_t).

  Definition PSLL_p := 
  "0000" $$ "1111" $$ "1111" $$ "00" $$ mmx_gg_p false true true true $ modrm_mmx @
    (fun p => match p with (gg, (op1, op2)) => PSLL gg op1 op2 end %% instruction_t)
  |+|
  "0000" $$ "1111" $$ "0111" $$ "00" $$ mmx_gg_p false true true true 
    $ "11110" $$ mmx_reg $ byte @ 
    (fun p => match p with (gg, (r, imm)) => PSLL gg (MMX_Reg_op r) (MMX_Imm_op (zero_extend8_32 imm)) end %% instruction_t).

  Definition PSRA_p :=
  "0000" $$ "1111" $$ "1110" $$ "00" $$ mmx_gg_p false true true false $ modrm_mmx @
    (fun p => match p with (gg, (op1, op2)) => PSRA gg op1 op2 end %% instruction_t)
  |+|
  "0000" $$ "1111" $$ "0111" $$ "00" $$ mmx_gg_p false true true false 
    $ "11100" $$ mmx_reg $ byte @ 
    (fun p => match p with (gg, (r, imm)) => PSRA gg (MMX_Reg_op r) (MMX_Imm_op (zero_extend8_32 imm)) end %% instruction_t).

  Definition PSRL_p := 
  "0000" $$ "1111" $$ "1101" $$ "00" $$ mmx_gg_p false true true true $ modrm_mmx @
    (fun p => match p with (gg, (op1, op2)) => PSRL gg op1 op2 end %% instruction_t)
  |+|
  "0000" $$ "1111" $$ "0111" $$ "00" $$ mmx_gg_p false true true true
    $ "11010" $$ mmx_reg $ byte @ 
    (fun p => match p with (gg, (r, imm)) => PSRL gg (MMX_Reg_op r) (MMX_Imm_op (zero_extend8_32 imm)) end %% instruction_t).

  Definition PSUB_p := 
  "0000" $$ "1111" $$ "1111" $$ "10" $$ mmx_gg_p true true true false $ modrm_mmx @
    (fun p => match p with (gg, (op1, op2)) => PSUB gg op1 op2 end %% instruction_t).

  Definition PSUBS_p := 
  "0000" $$ "1111" $$ "1110" $$ "10" $$ mmx_gg_p true true false false $ modrm_mmx @
    (fun p => match p with (gg, (op1, op2)) => PSUBS gg op1 op2 end %% instruction_t).

  Definition PSUBUS_p := 
  "0000" $$ "1111" $$ "1101" $$ "10" $$ mmx_gg_p true true false false $ modrm_mmx @
    (fun p => match p with (gg, (op1, op2)) => PSUBUS gg op1 op2 end %% instruction_t).

  Definition PUNPCKH_p := 
  "0000" $$ "1111" $$ "0110" $$ "10" $$ mmx_gg_p true true true false $ modrm_mmx @
    (fun p => match p with (gg, (op1, op2)) => PUNPCKH gg op1 op2 end %% instruction_t).

  Definition PUNPCKL_p := 
  "0000" $$ "1111" $$ "0110" $$ "00" $$ mmx_gg_p true true true false $ modrm_mmx @
    (fun p => match p with (gg, (op1, op2)) => PUNPCKL gg op1 op2 end %% instruction_t).

  Definition PXOR_p := 
  "0000" $$ "1111" $$ "1110" $$ "1111" $$ modrm_mmx @ 
    (fun p => let (op1, op2) := p in PXOR op1 op2 %% instruction_t).
(*End of MMX grammars *)

(*SSE grammars*)
Definition ADDPS_p := 
  "0000" $$ "1111" $$ "0101" $$ "1000" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in ADDPS op1 op2 %% instruction_t).

Definition ADDSS_p := 
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1000" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in ADDSS op1 op2 %% instruction_t).

Definition ANDNPS_p := 
  "0000" $$ "1111" $$ "0101" $$ "0101" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in ANDNPS op1 op2 %% instruction_t).

Definition ANDPS_p := 
  "0000" $$ "1111" $$ "0101" $$ "0100" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in ANDPS op1 op2 %% instruction_t).

Definition CMPPS_p := 
  "0000" $$ "1111" $$ "1100" $$ "0010" $$ modrm_xmm $ byte @ 
    (fun p => match p with ((op1, op2), imm)
                => CMPPS op1 op2 (SSE_Imm_op (zero_extend8_32 imm)) end %% instruction_t).

Definition CMPSS_p := 
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "1100" $$ "0010" $$ modrm_xmm $ byte @ 
    (fun p => match p with ((op1, op2), imm)
                => CMPSS op1 op2 (SSE_Imm_op (zero_extend8_32 imm)) end %% instruction_t).

Definition COMISS_p :=
  "0000" $$ "1111" $$ "0010" $$ "1111" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in COMISS op1 op2 %% instruction_t).

Definition CVTPI2PS_p :=
  "0000" $$ "1111" $$ "0010" $$ "1010" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in CVTPI2PS op1 op2 %% instruction_t).

Definition CVTPS2PI_p := 
  "0000" $$ "1111" $$ "0010" $$ "1101" $$ "11" $$ sse_reg $ mmx_reg @
    (fun p => let (sr, mr) := p in CVTPS2PI (SSE_XMM_Reg_op sr) (SSE_MM_Reg_op mr) %% instruction_t)
  |+|
  "0000" $$ "1111" $$ "0010" $$ "1101" $$ modrm_xmm_noreg @ 
    (fun p => let (xmm, mem) := p in CVTPS2PI xmm mem %% instruction_t).

Definition CVTSI2SS_p :=
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0010" $$ "1010" $$ "11" $$ sse_reg $ reg @
    (fun p => let (sr, r) := p in CVTSI2SS (SSE_XMM_Reg_op sr) (SSE_GP_Reg_op r) %% instruction_t)
  |+|
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0010" $$ "1010" $$ modrm_xmm_noreg @ 
    (fun p => let (xmm, mem) := p in CVTSI2SS xmm mem %% instruction_t).

Definition CVTSS2SI_p :=
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0010" $$ "1101" $$ "11" $$ reg $ sse_reg @
    (fun p => let (r, sr) := p in CVTSS2SI (SSE_GP_Reg_op r) (SSE_XMM_Reg_op sr) %% instruction_t)
  |+|
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0010" $$ "1101" $$ modrm_xmm_gp_noreg @ 
    (fun p => let (op1, mem) := p in CVTSS2SI op1 mem %% instruction_t).

Definition CVTTPS2PI_p :=
  "0000" $$ "1111" $$ "0010" $$ "1100" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in CVTTPS2PI op1 op2 %% instruction_t).

Definition CVTTSS2SI_p :=
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0010" $$ "1100" $$ "11" $$ reg $ sse_reg @
    (fun p => let (r, sr) := p in CVTTSS2SI (SSE_GP_Reg_op r) (SSE_XMM_Reg_op sr) %% instruction_t)
  |+|
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0010" $$ "1100" $$ modrm_xmm_gp_noreg @ 
    (fun p => let (op1, mem) := p in CVTTSS2SI op1 mem %% instruction_t).

Definition DIVPS_p := 
  "0000" $$ "1111" $$ "0101" $$ "1110" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in DIVPS op1 op2 %% instruction_t).

Definition DIVSS_p :=
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1110" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in DIVSS op1 op2 %% instruction_t).

Definition LDMXCSR_p := 
  "0000" $$ "1111" $$ "1010" $$ "1110" $$ ext_op_modrm_sse_noreg "010" @ (fun x => LDMXCSR x %% instruction_t).

Definition MAXPS_p := 
  "0000" $$ "1111" $$ "0101" $$ "1111" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in MAXPS op1 op2 %% instruction_t).

Definition MAXSS_p := 
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1111" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in MAXSS op1 op2 %% instruction_t).

Definition MINPS_p := 
  "0000" $$ "1111" $$ "0101" $$ "1101" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in MINPS op1 op2 %% instruction_t).

Definition MINSS_p :=
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1101" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in MINSS op1 op2 %% instruction_t).

Definition MOVAPS_p :=
  "0000" $$ "1111" $$ "0010" $$ "1000" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in MOVAPS op1 op2 %% instruction_t)
  |+|
  "0000" $$ "1111" $$ "0010" $$ "1001" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in MOVAPS op1 op2 %% instruction_t).

Definition MOVHLPS_p :=
  "0000" $$ "1111" $$ "0001" $$ "0010" $$ "11" $$ sse_reg $ sse_reg @
    (fun p => let (sr1, sr2) := p in MOVHLPS (SSE_XMM_Reg_op sr1) (SSE_XMM_Reg_op sr2) %% instruction_t).

Definition MOVHPS_p := 
  "0000" $$ "1111" $$ "0001" $$ "0110" $$ modrm_xmm_noreg @ 
    (fun p => let (op1, mem) := p in MOVHPS op1 mem %% instruction_t)
  |+|
  "0000" $$ "1111" $$ "0001" $$ "0111" $$ modrm_xmm_noreg @ 
    (fun p => let (op1, mem) := p in MOVHPS mem op1 %% instruction_t).

Definition MOVLHPS_p :=
  "0000" $$ "1111" $$ "0001" $$ "0110" $$ "11" $$ sse_reg $ sse_reg @
    (fun p => let (sr1, sr2) := p in MOVLHPS (SSE_XMM_Reg_op sr1) (SSE_XMM_Reg_op sr2) %% instruction_t).

Definition MOVLPS_p :=
  "0000" $$ "1111" $$ "0001" $$ "0010" $$ modrm_xmm_noreg @ 
    (fun p => let (op1, mem) := p in MOVLPS op1 mem %% instruction_t)
  |+|
  "0000" $$ "1111" $$ "0001" $$ "0011" $$ modrm_xmm_noreg @ 
    (fun p => let (op1, mem) := p in MOVLPS mem op1 %% instruction_t).

Definition MOVMSKPS_p := 
  "0000" $$ "1111" $$ "0001" $$ "0110" $$ "11" $$ reg $ sse_reg @
    (fun p => let (r, sr) := p in MOVMSKPS (SSE_GP_Reg_op r) (SSE_XMM_Reg_op sr) %% instruction_t).

Definition MOVSS_p :=
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0001" $$ "0000" $$  modrm_xmm @ 
    (fun p => let (op1, op2) := p in MOVSS op1 op2 %% instruction_t)
  |+|
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0001" $$ "0001" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in MOVSS op2 op1 %% instruction_t).

Definition MOVUPS_p := 
  "0000" $$ "1111" $$ "0001" $$ "0000" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in MOVUPS op1 op2 %% instruction_t)
  |+|
  "0000" $$ "1111" $$ "0001" $$ "0001" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in MOVUPS op2 op1 %% instruction_t).

Definition MULPS_p :=
  "0000" $$ "1111" $$ "0101" $$ "1001" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in MULPS op1 op2 %% instruction_t).

Definition MULSS_p :=
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1001" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in MULSS op1 op2 %% instruction_t).

Definition ORPS_p :=
  "0000" $$ "1111" $$ "0101" $$ "0110" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in ORPS op1 op2 %% instruction_t).

Definition RCPPS_p :=
  "0000" $$ "1111" $$ "0101" $$ "0011" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in RCPPS op1 op2 %% instruction_t).

Definition RCPSS_p :=
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "0011" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in RCPSS op1 op2 %% instruction_t).

Definition RSQRTPS_p :=
  "0000" $$ "1111" $$ "0101" $$ "0010" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in RSQRTPS op1 op2 %% instruction_t).

Definition RSQRTSS_p :=
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "0010" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in RSQRTSS op1 op2 %% instruction_t).

Definition SHUFPS_p :=
  "0000" $$ "1111" $$ "1100" $$ "0110" $$ modrm_xmm $ byte @ 
    (fun p => match p with ((op1, op2), imm)
                => SHUFPS op1 op2 (SSE_Imm_op (zero_extend8_32 imm)) end %% instruction_t).

Definition SQRTPS_p :=
  "0000" $$ "1111" $$ "0101" $$ "0001" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in SQRTPS op1 op2 %% instruction_t).

Definition SQRTSS_p :=
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "0001" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in SQRTSS op1 op2 %% instruction_t).

Definition STMXCSR_p := 
  "0000" $$ "1111" $$ "1010" $$ "1110" $$ ext_op_modrm_sse_noreg "011" @ (fun x => STMXCSR x %% instruction_t).

Definition SUBPS_p :=
  "0000" $$ "1111" $$ "0101" $$ "1100" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in SUBPS op1 op2 %% instruction_t).

Definition SUBSS_p :=
  "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1100" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in SUBSS op1 op2 %% instruction_t).

Definition UCOMISS_p :=
  "0000" $$ "1111" $$ "0010" $$ "1110" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in UCOMISS op1 op2 %% instruction_t).

Definition UNPCKHPS_p :=
  "0000" $$ "1111" $$ "0001" $$ "0101" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in UNPCKHPS op1 op2 %% instruction_t).

Definition UNPCKLPS_p :=
  "0000" $$ "1111" $$ "0001" $$ "0100" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in UNPCKLPS op1 op2 %% instruction_t).

Definition XORPS_p :=
  "0000" $$ "1111" $$ "0101" $$ "0111" $$ modrm_xmm @ 
    (fun p => let (op1, op2) := p in XORPS op1 op2 %% instruction_t).

(* todo: this needs to take operand-override prefix into account *)
Definition PAVGB_p :=
  "0000" $$ "1111" $$ "1110" $$ "0000" $$ modrm_mm @ 
    (fun p => let (op1, op2) := p in PAVGB op1 op2 %% instruction_t)
  |+|
  "0000" $$ "1111" $$ "1110" $$ "0011" $$ modrm_mm @ 
    (fun p => let (op1, op2) := p in PAVGB op2 op1 %% instruction_t).

Definition PEXTRW_p :=
  "0000" $$ "1111" $$ "1100" $$ "0101" $$ "11" $$ reg $ mmx_reg $ byte @
    (fun p => match p with (r32, (mmx, imm))
                => PEXTRW (SSE_GP_Reg_op r32) (SSE_MM_Reg_op mmx) (SSE_Imm_op (zero_extend8_32 imm)) end %% instruction_t).

Definition PINSRW_p :=
  "0000" $$ "1111" $$ "1100" $$ "0100" $$ "11" $$ mmx_reg $ reg $ byte @
    (fun p => match p with (mmx, (r32, imm)) => PINSRW (SSE_MM_Reg_op mmx) (SSE_GP_Reg_op r32) (SSE_Imm_op (zero_extend8_32 imm)) end %% instruction_t)
  |+|
  "0000" $$ "1111" $$ "1100" $$ "0100" $$ modrm_mm_noreg $ byte @ 
    (fun p => match p with ((op1, mem), imm) => PINSRW op1 mem (SSE_Imm_op (zero_extend8_32 imm)) end %% instruction_t).

Definition PMAXSW_p :=
  "0000" $$ "1111" $$ "1110" $$ "1110" $$ modrm_mm @ 
    (fun p => let (op1, op2) := p in PMAXSW op1 op2 %% instruction_t).

Definition PMAXUB_p :=
  "0000" $$ "1111" $$ "1101" $$ "1110" $$ modrm_mm @ 
    (fun p => let (op1, op2) := p in PMAXUB op1 op2 %% instruction_t).

Definition PMINSW_p :=
  "0000" $$ "1111" $$ "1110" $$ "1010" $$ modrm_mm @ 
    (fun p => let (op1, op2) := p in PMINSW op1 op2 %% instruction_t).

Definition PMINUB_p :=
  "0000" $$ "1111" $$ "1101" $$ "1010" $$ modrm_mm @ 
    (fun p => let (op1, op2) := p in PMINUB op1 op2 %% instruction_t).

Definition PMOVMSKB_p :=
  "0000" $$ "1111" $$ "1101" $$ "0111" $$ "11" $$ reg $ mmx_reg @
    (fun p => let (r, mr) := p in PMOVMSKB (SSE_GP_Reg_op r) (SSE_MM_Reg_op mr) %% instruction_t).

(*
  Already done in MMX grammar section

 Definition PMULHUW_p :=
  "0000" $$ "1111" $$ "1110" $$ "0100" $$ "11" $$ mmx_reg $ mmx_reg @
    (fun p => let (a, b) := p in PMULHUW (SSE_MM_Reg_op a) (SSE_MM_Reg_op b) %% instruction_t)
  |+|
  "0000" $$ "1111" $$ "1110" $$ "0100" $$ modrm_mm @ 
    (fun p => let (mem, mmx) := p in PMULHUW mem mmx %% instruction_t).
*)
Definition PSADBW_p :=
  "0000" $$ "1111" $$ "1111" $$ "0110" $$ modrm_mm @ 
    (fun p => let (op1, op2) := p in PSADBW op1 op2 %% instruction_t).

Definition PSHUFW_p :=
  "0000" $$ "1111" $$ "0111" $$ "0000" $$ modrm_mm $ byte @ 
    (fun p => match p with ((op1, op2), imm)
                => PSHUFW op1 op2 (SSE_Imm_op(zero_extend8_32 imm)) end %% instruction_t).

Definition MASKMOVQ_p :=
  "0000" $$ "1111" $$ "1111" $$ "0111" $$ "11" $$ mmx_reg $ mmx_reg @
    (fun p => let (mr1, mr2) := p in MASKMOVQ (SSE_MM_Reg_op mr1) (SSE_MM_Reg_op mr2) %% instruction_t).

Definition MOVNTPS_p :=
  "0000" $$ "1111" $$ "0010" $$ "1011" $$ modrm_xmm_noreg @ 
    (fun p => let (op1, mem) := p in MOVNTPS mem op1 %% instruction_t).

Definition MOVNTQ_p :=
  "0000" $$ "1111" $$ "1110" $$ "0111" $$ modrm_mm_noreg @ 
    (fun p => let (op1, mem) := p in MOVNTQ mem op1 %% instruction_t).

Definition PREFETCHT0_p :=
  "0000" $$ "1111" $$ "0001" $$ "1000" $$ ext_op_modrm_sse_noreg "001" @ (fun x => PREFETCHT0 x %% instruction_t).

Definition PREFETCHT1_p :=
  "0000" $$ "1111" $$ "0001" $$ "1000" $$ ext_op_modrm_sse_noreg "010" @ (fun x => PREFETCHT1 x %% instruction_t).

Definition PREFETCHT2_p := 
  "0000" $$ "1111" $$ "0001" $$ "1000" $$ ext_op_modrm_sse_noreg "011" @ (fun x => PREFETCHT2 x %% instruction_t).

Definition PREFETCHNTA_p :=
  "0000" $$ "1111" $$ "0001" $$ "1000" $$ ext_op_modrm_sse_noreg "000" @ (fun x => PREFETCHNTA x %% instruction_t).

Definition SFENCE_p := "0000" $$ "1111" $$ "1010" $$ "1110" $$ "1111" $$ 
                                   bits "1000" @ (fun _ => SFENCE %% instruction_t).

  (* Now glue all of the individual instruction grammars together into 
     one big grammar.  *)
  
  Fixpoint list2pair_t (l: list type) :=
    match l with
      | nil => Unit_t
      | r::r'::nil => Pair_t r r'
      | r::l' => Pair_t r (list2pair_t l')
    end.
 
  Definition lock_p : grammar lock_or_rep_t :=
    "1111" $$ bits "0000" @ (fun _ => lock %% lock_or_rep_t).

  Definition rep_or_repn_p : grammar lock_or_rep_t :=
    "1111" $$ bits "0010" @ (fun _ => repn %% lock_or_rep_t)
  |+|
    "1111" $$ bits "0011" @ (fun _ => rep  %% lock_or_rep_t).

  Definition rep_p : grammar lock_or_rep_t :=
    "1111" $$ bits "0011" @ (fun _ => rep  %% lock_or_rep_t).

  Definition lock_or_rep_p : grammar lock_or_rep_t :=
    ("1111" $$ ( bits "0000" @ (fun _ => lock %% lock_or_rep_t)
                 |+| bits "0010" @ (fun _ => repn %% lock_or_rep_t)
                 |+| bits "0011" @ (fun _ => rep  %% lock_or_rep_t))).

  Definition segment_override_p : grammar segment_register_t :=
  ("0010" $$ bits "1110" @ (fun _ => CS %% segment_register_t)
    |+| "0011" $$ bits "0110" @ (fun _ => SS %% segment_register_t)
    |+| "0011" $$ bits "1110" @ (fun _ => DS %% segment_register_t)
    |+| "0010" $$ bits "0110" @ (fun _ => ES %% segment_register_t)
    |+| "0110" $$ bits "0100" @ (fun _ => FS %% segment_register_t)
    |+| "0110" $$ bits "0101" @ (fun _ => GS %% segment_register_t)).

  Definition op_override_p : grammar bool_t :=
    "0110" $$ bits "0110" @ (fun _ => true %% bool_t).
  Definition addr_override_p : grammar bool_t :=
    "0110" $$ bits "0111" @ (fun _ => true %% bool_t).

  (* Ok, now I want all permutations of the above four grammars. 
     I make a little perm2 combinator that takes two grammars and gives you
     p1 $ p2 |+| p2 $ p1, making sure to swap the results in the second case *)
  
  Definition perm2 t1 t2 (p1: grammar t1) (p2: grammar t2) : grammar (Pair_t t1 t2) :=
      p1 $ p2 |+|
      p2 $ p1 @ (fun p => match p with (a, b) => (b, a) %% Pair_t t1 t2 end).

  (* Then I build that up into a perm3 and perm4. One could make a recursive
     function to do this, but I didn't want to bother with the necessary
     proofs and type-system juggling.*) 

  Definition perm3 t1 t2 t3 (p1: grammar t1) (p2: grammar t2) (p3: grammar t3)
    : grammar (Pair_t t1 (Pair_t t2 t3)) :=
    let r_t := Pair_t t1 (Pair_t t2 t3) in
       p1 $ (perm2 p2 p3)
   |+| p2 $ (perm2 p1 p3) @ (fun p => match p with (b, (a, c)) => (a, (b, c)) %% r_t end)
   |+| p3 $ (perm2 p1 p2) @ (fun p => match p with (c, (a, b)) => (a, (b, c)) %% r_t end).

  Definition perm4 t1 t2 t3 t4 (p1: grammar t1) (p2: grammar t2) (p3: grammar t3)
    (p4: grammar t4) : grammar (Pair_t t1 (Pair_t t2 (Pair_t t3 t4))) :=
    let r_t := Pair_t t1 (Pair_t t2 (Pair_t t3 t4)) in
       p1 $ (perm3 p2 p3 p4)
   |+| p2 $ (perm3 p1 p3 p4) @ 
         (fun p => match p with (b, (a, (c, d))) => (a, (b, (c, d))) %% r_t end)
   |+| p3 $ (perm3 p1 p2 p4) @ 
         (fun p => match p with (c, (a, (b, d))) => (a, (b, (c, d))) %% r_t end)
   |+| p4 $ (perm3 p1 p2 p3) @ 
         (fun p => match p with (d, (a, (b, c))) => (a, (b, (c, d))) %% r_t end). 

  (* In this case, prefixes are optional. Before, each of the above
     parsing rules for the prefixes accepted Eps, and this was how we
     handled this.  However, if the grammars you join with perm can
     each accept Eps, then the result is a _highly_ ambiguous grammar.

     Instead we have a different combinator, called option_perm, that 
     handles this without introducing extra ambiguity *)

  Definition option_perm t1 (p1: grammar (User_t t1)) 
     : grammar (option_t t1) :=
     let r_t := option_t t1 in 
         Eps @ (fun p => None %% r_t)  
     |+| p1 @ (fun p => (Some p) %% r_t ).


  (* This signature is slightly awkward - because there's no result
     type corresponding to option (and I'm hesitant to add it to
     Grammar at the moment) we can't just have a signature like grammar
     t1 -> grammar t2 -> grammar (option_t t1) (option_t t2)) *)
    
  Definition option_perm2 t1 t2 (p1: grammar (User_t t1)) (p2: grammar (User_t t2)) 
     : grammar (Pair_t (option_t t1) (option_t t2)) :=
     let r_t := Pair_t (option_t t1) (option_t t2) in 
         Eps @ (fun p => (None, None) %% r_t)  
     |+| p1 @ (fun p => (Some p, None) %% r_t ) 
     |+| p2 @ (fun p => (None, Some p) %% r_t) 
     |+| perm2 p1 p2 @ (fun p => match p with (a, b) => (Some a, Some b) %%r_t end). 

  Definition option_perm3 t1 t2 t3 (p1:grammar(User_t t1)) (p2:grammar(User_t t2))
    (p3:grammar(User_t t3)): grammar(Pair_t(option_t t1)(Pair_t(option_t t2) (option_t t3)))
    :=
    let r_t := Pair_t(option_t t1)(Pair_t(option_t t2) (option_t t3))  in
        Eps @ (fun p => (None, (None, None)) %% r_t)
    |+| p1 @ (fun p => (Some p, (None, None)) %% r_t)
    |+| p2 @ (fun p => (None, (Some p, None)) %% r_t)
    |+| p3 @ (fun p => (None, (None, Some p)) %% r_t)
    |+| perm2 p1 p2 @(fun p => match p with (a, b) => (Some a, (Some b, None)) %%r_t end)
    |+| perm2 p1 p3 @(fun p => match p with (a, c) => (Some a, (None, Some c)) %%r_t end)
    |+| perm2 p2 p3 @(fun p => match p with (b, c) => (None, (Some b, Some c)) %%r_t end)
    |+| perm3 p1 p2 p3 @ (fun p => match p with (a, (b, c))
                                    => (Some a, (Some b, Some c)) %%r_t end).

  (* t1 is optional, but t2 is a must *)
  Definition option_perm2_variation t1 t2 (p1: grammar (User_t t1))
    (p2: grammar (User_t t2)) 
     : grammar (Pair_t (option_t t1) (User_t t2)) :=
     let r_t := Pair_t (option_t t1) (User_t t2) in 
         p2 @ (fun p => (None, p) %% r_t) 
     |+| perm2 p1 p2 @ (fun p => match p with (a, b) => (Some a, b) %%r_t end). 

  (* in this def, t1 and t2 are optional, but t3 is a must *)
  Definition option_perm3_variation t1 t2 t3 (p1:grammar(User_t t1)) (p2:grammar(User_t t2))
    (p3:grammar(User_t t3)): grammar(Pair_t(option_t t1)(Pair_t(option_t t2) (User_t t3)))
    :=
    let r_t := Pair_t(option_t t1)(Pair_t(option_t t2) (User_t t3))  in
        p3 @ (fun p => (None, (None, p)) %% r_t)
    |+| perm2 p1 p3 @(fun p => match p with (a, c) => (Some a, (None, c)) %%r_t end)
    |+| perm2 p2 p3 @(fun p => match p with (b, c) => (None, (Some b, c)) %%r_t end)
    |+| perm3 p1 p2 p3 @ (fun p => match p with (a, (b, c))
                                    => (Some a, (Some b, c)) %%r_t end).

  (* This is beginning to get quite nasty. Someone should write a form for arbitrary
     n and prove it's correct :) *)
  Definition option_perm4 t1 t2 t3 t4 (p1:grammar(User_t t1)) (p2: grammar(User_t t2))
    (p3: grammar(User_t t3)) (p4: grammar(User_t t4)) :
      grammar(Pair_t(option_t t1) (Pair_t(option_t t2) (Pair_t(option_t t3) (option_t t4))))
      := 
    let r_t := Pair_t(option_t t1) (Pair_t(option_t t2)
      (Pair_t(option_t t3)(option_t t4))) in
        Eps @ (fun p => (None, (None, (None, None))) %% r_t)
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


  Definition prefix_grammar_rep :=
    option_perm3 rep_p segment_override_p op_override_p @
     (fun p => match p with (l, (s, op)) =>
                 mkPrefix l s (opt2b op false) false %% prefix_t end).

  (** this set of instructions can take prefixes in prefix_grammar_rep;
      that is, in lock_or_rep, only rep can be used; we put RET in this
      category because it turns out many binaries use "rep ret" to avoid the
      branch prediction panelty in AMD processors; intel processor seems to
      just ignore the rep prefix in "rep ret". *)
  Definition instr_grammars_rep :=
    INS_p :: OUTS_p :: MOVS_p :: LODS_p :: STOS_p :: RET_p :: nil.

  Definition prefix_grammar_rep_or_repn :=
    option_perm3 rep_or_repn_p segment_override_p op_override_p @
      (fun p => match p with (l, (s, op)) =>
                  mkPrefix l s (opt2b op false) false %% prefix_t end).

  (** this set of instructions can take prefixes in prefix_grammar_repn;
      that is, in lock_or_rep, either rep or repn can be used, but not lock *)
  Definition instr_grammars_rep_or_repn := CMPS_p :: SCAS_p :: nil.

  Definition prefix_grammar_lock_with_op_override :=
    option_perm3_variation lock_p segment_override_p op_override_p @
     (fun p => match p with (l, (s, op)) =>
                 mkPrefix l s op false %% prefix_t end).

  (** Instructions that can take prefixes in
     prefix_grammar_lock_with_op_override: in lock_or_rep, only lock can be
     used; segment override is optional; op_override prefix *must* be used
     *)
  Definition instr_grammars_lock_with_op_override := 
    ADD_p true :: ADC_p true :: AND_p true :: NEG_p :: NOT_p :: OR_p true
    :: SBB_p true :: SUB_p true :: XOR_p true :: XCHG_p :: nil.

  Definition prefix_grammar_lock_no_op_override :=
    option_perm2 lock_p segment_override_p @
     (fun p => match p with (l, s) =>
                 mkPrefix l s false false %% prefix_t end).

  (** Instructions that can take prefixes in
     prefix_grammar_lock_no_op_override; that is, in lock_or_rep, only lock
     can be used; segment override is optional; and op_override prefix
     *must not* be used *)
  Definition instr_grammars_lock_no_op_override := 
    ADD_p false :: ADC_p false :: AND_p false :: BTC_p :: BTR_p :: 
    BTS_p :: CMPXCHG_p :: DEC_p :: INC_p :: NEG_p :: NOT_p :: OR_p false
    :: SBB_p false :: SUB_p false :: XOR_p false :: XADD_p :: XCHG_p :: nil.

  Definition prefix_grammar_seg_with_op_override := 
    option_perm2_variation segment_override_p op_override_p @
     (fun p => match p with (s, op) =>
                 mkPrefix None s op false %% prefix_t end).

  (* this set of instructions can take prefixes in 
     prefix_grammar_seg_with_op_override;
     that is, it cannot take a lock_or_rep prefix, must take op_override
     prefix, can optionally take segment-override prefix *)
  Definition instr_grammars_seg_with_op_override := 
    CMP_p true ::  IMUL_p true :: MOV_p true :: TEST_p true :: nil.

  Definition prefix_grammar_seg_op_override :=
    option_perm2 segment_override_p op_override_p @
     (fun p => match p with (s, op) =>
                 mkPrefix None s (opt2b op false) false %% prefix_t end).

  (* this set of instructions can take prefixes in 
     prefix_grammar_seg_op_override;
     that is, it cannot take a lock_or_rep prefix, but can
     optionally take segment or op override prefix *)
  Definition instr_grammars_seg_op_override := 
    CDQ_p :: CMOVcc_p :: CWDE_p :: DIV_p :: IDIV_p :: 
    MOVSX_p :: MOVZX_p :: MUL_p :: NOP_p :: 
    ROL_p :: ROR_p :: SAR_p :: SHL_p :: SHLD_p :: SHR_p :: SHRD_p :: nil.

  Definition prefix_grammar_seg_override :=
    option_perm segment_override_p @
     (fun s => mkPrefix None s false false %% prefix_t).

  (* this set of instructions can take only the seg_override prefix *)
  Definition instr_grammars_seg_override := 
    AAA_p :: AAD_p :: AAM_p :: AAS_p :: CMP_p false ::
    ARPL_p :: BOUND_p :: BSF_p :: BSR_p :: BSWAP_p :: BT_p :: 
    CALL_p :: CLC_p :: CLD_p :: CLI_p :: CLTS_p :: CMC_p :: CPUID_p :: DAA_p :: DAS_p ::
    HLT_p :: IMUL_p false :: IN_p :: INTn_p :: INT_p :: INTO_p :: INVD_p :: INVLPG_p :: IRET_p :: Jcc_p :: JCXZ_p :: JMP_p :: 
    LAHF_p :: LAR_p :: LDS_p :: LEA_p :: LEAVE_p :: LES_p :: LFS_p :: LGDT_p :: LGS_p :: LIDT_p :: LLDT_p :: LMSW_p :: 
    LOOP_p :: LOOPZ_p :: LOOPNZ_p :: LSL_p :: LSS_p :: LTR_p :: MOV_p false :: MOVCR_p :: MOVDR_p :: 
    MOVSR_p :: MOVBE_p ::  OUT_p :: POP_p :: POPSR_p :: POPA_p :: POPF_p ::
    PUSH_p :: PUSHSR_p :: PUSHA_p :: PUSHF_p :: RCL_p :: RCR_p :: RDMSR_p :: RDPMC_p :: RDTSC_p :: RDTSCP_p :: 
    RSM_p :: SAHF_p :: SETcc_p :: SGDT_p :: SIDT_p :: SLDT_p :: SMSW_p :: STC_p :: STD_p :: STI_p :: 
    STR_p :: TEST_p false :: UD2_p :: VERR_p :: VERW_p :: WBINVD_p :: WRMSR_p :: XLAT_p :: F2XM1_p ::
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

  Local Open Scope list_scope.

  Definition instruction_grammar_list := 
    (List.map (fun (p:grammar instruction_t) => prefix_grammar_rep $ p)
      instr_grammars_rep) ++
    (List.map (fun (p:grammar instruction_t) => prefix_grammar_rep_or_repn $ p)
      instr_grammars_rep_or_repn) ++
    (List.map (fun (p:grammar instruction_t)
                => prefix_grammar_lock_with_op_override $ p)
      instr_grammars_lock_with_op_override) ++
    (List.map (fun (p:grammar instruction_t)
                => prefix_grammar_lock_no_op_override $ p)
      instr_grammars_lock_no_op_override) ++
    (List.map (fun (p:grammar instruction_t)
                => prefix_grammar_seg_with_op_override $ p)
      instr_grammars_seg_with_op_override) ++
    (List.map (fun (p:grammar instruction_t)
                => prefix_grammar_seg_op_override $ p)
      instr_grammars_seg_op_override) ++
    (List.map (fun (p:grammar instruction_t)
                => prefix_grammar_seg_override $ p)
      instr_grammars_seg_override).

  Definition instruction_grammar := alts instruction_grammar_list.


  (** Starting constructing the x86 parser *)
  Require Import Parser.

  Definition instruction_regexp := projT1 (split_grammar (instruction_grammar)).

  Definition ini_decoder_state := 
    initial_parser_state instruction_grammar.

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

Extraction Implicit never [t].
Extraction Implicit always [t].
Extraction Implicit alt [t].
Extraction Implicit alts0 [t].
Extraction Implicit alts' [t].
Extraction Implicit alts [t].
Extraction Implicit map [t1 t2].
Extraction Implicit seq [t1 t2].
Extraction Implicit cons [t].
Extraction Implicit seqs [t].
Extraction Implicit bitsleft [t].
Extraction Implicit modrm_gen [res_t].
Extraction Implicit modrm_gen_noreg [reg_t res_t].
Extraction Implicit ext_op_modrm_gen_noreg2 [res_t].
Extraction Implicit ext_op_modrm_gen [res_t].
Extraction Implicit perm2 [t1 t2].
Extraction Implicit perm3 [t1 t2 t3].
Extraction Implicit perm4 [t1 t2 t3 t4].
Extraction Implicit option_perm [t1].
Extraction Implicit option_perm2 [t1 t2].
Extraction Implicit option_perm3 [t1 t2 t3].
Extraction Implicit option_perm4 [t1 t2 t3 t4].
Extraction Implicit option_perm2_variation [t1 t2].
Extraction Implicit option_perm3_variation [t1 t2 t3].
