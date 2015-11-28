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
  Definition fp_condition_t := User_t Fp_Condition_t.
  Definition mmx_granularity_t := User_t MMX_Granularity_t.
  Definition mmx_operand_t := User_t MMX_Operand_t.
  Definition mmx_register_t := User_t MMX_Register_t.
  Definition sse_operand_t := User_t SSE_Operand_t.
  Definition sse_register_t := User_t SSE_Register_t.
  Definition address_t := User_t Address_t.
  Definition operand_t := User_t Operand_t.
  Definition reg_or_immed_t := User_t Reg_or_Immed_t.
  Definition fp_operand_t := User_t Fp_Operand_t.  
  Definition instruction_t := User_t Instruction_t.
  Definition control_register_t := User_t Control_Register_t.
  Definition debug_register_t := User_t Debug_Register_t.
  Definition segment_register_t := User_t Segment_Register_t.
  Definition lock_or_rep_t := User_t Lock_or_Rep_t.
  Definition bool_t := User_t Bool_t.
  Definition prefix_t := User_t Prefix_t.
  Definition bitvector_t n := User_t (BitVector_t n).
  Definition selector_t := BitVector_t 15.

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
  Notation option_t := Option_t.
  Definition Any_p := Any.

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

  (* todo: remove *)
  (* Local Ltac destruct_union :=  *)
  (*   repeat match goal with  *)
  (*            | [v: [| Sum_t _ _ |] |- _ ] => destruct v as [v | v] *)
  (*            | [v: [| Unit_t |] |- _] => destruct v *)
  (*          end. *)

  Local Ltac lineararith := 
    unfold two_power_nat, shift_nat in *; simpl in *; omega.

  Obligation Tactic := localcrush.

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

  (** * Definitions and tactics for combining a list of grammars using balanced ASTs *)

  (** Assume we have a list of grammars of type "wf_bigrammar pt_i". We want
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
      reverse function. Each entry in an AST env also includes a natural
      number label that is used in gen_rev_case_by_lbl to generate a
      reverse mapping function for the case idenfieid by the label.  In an
      AST_Env, the requirement for labels is that they be in the asending
      order; however, they don't need to be consecutive (although they
      could). *)
  Inductive AST_Env (t:type):= 
  | ast_env_nil : AST_Env t
  | ast_env_cons : 
      (* each grammar in an AST_Env including an index nat, the type of a
       grammar, the grammar, and a map function for constructing a semantic
       value given values produced by the grammar *)
      forall (l:nat) (pt:type), 
        wf_bigrammar pt -> (interp pt -> interp t) -> AST_Env t -> AST_Env t.
  Arguments ast_env_nil [t].
  Notation "{ l , g , f } ::: al" := 
    (ast_env_cons l g f al) (right associativity, at level 70).

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

  (** Cat p1 with every grammar inside the ast env *)
  Fixpoint ast_env_cat t1 t2 (p1:wf_bigrammar t1) (ae: AST_Env t2) :
    AST_Env (pair_t t1 t2) := 
    match ae with
      | ast_env_nil => ast_env_nil
      | ast_env_cons l pt p2 f ae' => 
        ast_env_cons l (p1 $ p2) (fun v => (fst v, f (snd v)) %% pair_t t1 t2)
                     (ast_env_cat p1 ae')
    end.
  Notation "p $$$ ae" := 
    (ast_env_cat p ae) (right associativity, at level 80).

  Fixpoint ast_env_app t (ae1 ae2: AST_Env t) : AST_Env t := 
    match ae1 with
      | ast_env_nil => ae2
      | ast_env_cons l pt p f ae1' =>
        ast_env_cons l p f (ast_env_app ae1' ae2)
    end.

  Notation "ael +++ aer" := 
    (ast_env_app ael aer) (right associativity, at level 85).

  Ltac gen_ast_grammar ast_env :=
  match ast_env with
    | ast_env_cons ?l ?g ?f ast_env_nil => constr:(g)
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
      | ast_env_cons ?l ?g ?f ast_env_nil =>
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
    | ast_env_cons ?l ?g ?f ast_env_nil => 
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

  (** generate a reverse mapping function for an AST env entry based on the
      index of the entry (not the label of the entry); the index starts
      from 0 *)
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

  (** generate a reverse mapping function for an AST env entry based on the
      label of the entry (not the index of the entry) *)
  Ltac gen_rev_case_by_lbl ast_env l := 
    let t := gen_ast_type ast_env in
    match ast_env with
      | ast_env_cons ?l1 _ _ ast_env_nil => 
        let eq_l_l1 := (eval compute in (beq_nat l l1)) in
        match eq_l_l1 with
          | true => constr:(fun v: interp t => v)
        end
      | _ =>
      let aepair := eval simpl in (env_split ast_env) in
      match aepair with
        | (?ael, ?aer) => 
          match aer with
            | ast_env_cons ?l2 _ _ ?aer1 =>
              let b := (eval compute in (NPeano.ltb l l2)) in
              match b with
                | true => 
                  let f := gen_rev_case_by_lbl ael l in 
                  constr:(fun v => (inl  (f v)):(interp t))
                | false => 
                  let f := gen_rev_case_by_lbl aer l in
                  constr:(fun v => (inr (f v)):(interp t))
              end
          end
      end
    end.

  (** given an ast env, generate a balanced grammar using |+|, a
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

  Local Ltac bg_pf_sim :=
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
      | [H: context[register_eq_dec ?r1 ?r2] |- _] => 
        destruct (register_eq_dec r1 r2); subst
      | [ |- context[register_eq_dec ?r1 ?r2]] => 
        destruct (register_eq_dec r1 r2); subst
      | [H: context[if Word.eq ?disp Word.zero then _ else _] |- _] =>
        let disp_eq := fresh "disp_eq" in
        remember_rev (Word.eq disp Word.zero) as disp_eq;
        destruct disp_eq
      | [H: ?V <> ?V |- _] => contradict H; trivial
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

  Definition debug_reg_env : AST_Env debug_register_t := 
    {0, ! "000", (fun _ => DR0 %% debug_register_t)} :::
    {1, ! "001", (fun _ => DR1 %% debug_register_t)} :::
    {2, ! "010", (fun _ => DR2 %% debug_register_t)} :::
    {3, ! "011", (fun _ => DR3 %% debug_register_t)} :::
    {4, ! "110", (fun _ => DR6 %% debug_register_t)} :::
    {5, ! "111", (fun _ => DR7 %% debug_register_t)} :::
    ast_env_nil.
     
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

  Definition segment_reg_env : AST_Env segment_register_t := 
    {0, ! "000", (fun _ => ES %% segment_register_t)} :::
    {1, ! "001", (fun _ => CS %% segment_register_t)} :::
    {2, ! "010", (fun _ => SS %% segment_register_t)} :::
    {3, ! "011", (fun _ => DS %% segment_register_t)} :::
    {4, ! "100", (fun _ => FS %% segment_register_t)} :::
    {5, ! "101", (fun _ => GS %% segment_register_t)} :::
    ast_env_nil.

  Definition segment_reg_p : wf_bigrammar segment_register_t.
    gen_ast_defs segment_reg_env.
    refine (gr @ (mp: _ -> [|segment_register_t|])
               & (fun u => 
                    match u with
                      | ES => case0 ()
                      | CS => case1 ()
                      | SS => case2 ()
                      | DS => case3 ()
                      | FS => case4 ()
                      | GS => case5 ()
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
    apply reg_no_esp_rng; congruence: ibr_rng_db.

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
    apply reg_no_ebp_rng; congruence: ibr_rng_db.

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
    apply reg_no_esp_ebp_rng; split; congruence: ibr_rng_db.

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

  (* Definition modrm_gen_noreg_env (reg_t:type) (reg_p:wf_bigrammar reg_t) *)
  (*           : AST_Env (pair_t reg_t address_t) := *)
  (*   (* mode 00 *) *)
  (*   {0, "00" $$ reg_p $ reg_no_esp_ebp, *)
  (*    fun v => *)
  (*      let (r1,base):=v in (r1, mkAddress (Word.repr 0) (Some base) None) *)
  (*      %% pair_t reg_t address_t} ::: *)
  (*   {1, "00" $$ reg_p $ "100" $$ si_p $ reg_no_ebp, *)
  (*    fun v => match v with *)
  (*               | (r,(si,base)) => *)
  (*                 (r, mkAddress (Word.repr 0) (Some base) si) *)
  (*             end %% pair_t reg_t address_t} ::: *)
  (*   {2, "00" $$ reg_p $ "100" $$ si_p $ "101" $$ word, *)
  (*    fun v => match v with *)
  (*               | (r,(si,disp)) => (r, mkAddress disp None si) *)
  (*             end %% pair_t reg_t address_t} ::: *)
  (*   {3, "00" $$ reg_p $ "101" $$ word, *)
  (*    fun v => let (r,disp):=v in (r, mkAddress disp None None) *)
  (*      %% pair_t reg_t address_t} ::: *)
  (*   (* mode 01 *) *)
  (*   {4, "01" $$ reg_p $ reg_no_esp $ byte, *)
  (*    fun v => match v with *)
  (*               | (r,(bs,disp)) => *)
  (*                 (r, mkAddress (sign_extend8_32 disp) (Some bs) None) *)
  (*             end %% pair_t reg_t address_t} ::: *)
  (*   {5, "01" $$ reg_p $ "100" $$ sib_p $ byte, *)
  (*    fun v => match v with *)
  (*               | (r, ((si,bs),disp)) => *)
  (*                 (r, mkAddress (sign_extend8_32 disp) (Some bs) si) *)
  (*             end %% pair_t reg_t address_t} ::: *)
  (*   (* mode 10 *) *)
  (*   {6, "10" $$ reg_p $ reg_no_esp $ word, *)
  (*    fun v => match v with *)
  (*               | (r,(bs,disp)) => (r, mkAddress disp (Some bs) None) *)
  (*             end %% pair_t reg_t address_t} ::: *)
  (*   {7, "10" $$ reg_p $ "100" $$ sib_p $ word, *)
  (*    fun v => match v with *)
  (*               | (r,((si,bs),disp)) => (r, mkAddress disp (Some bs) si) *)
  (*             end %% pair_t reg_t address_t} ::: *)
  (*   ast_env_nil. *)

  (* Definition modrm_gen_noreg (reg_t: type) *)
  (*   (reg_p: wf_bigrammar reg_t) : wf_bigrammar (pair_t reg_t address_t). *)
  (*   intros; gen_ast_defs (modrm_gen_noreg_env reg_p). *)
  (*   refine (gr @ (mp:_ -> [|pair_t reg_t address_t|]) *)
  (*              & (fun u:[|pair_t reg_t address_t|] => *)
  (*                   let (r,addr) := u in *)
  (*                   match addr with *)
  (*                     | {| addrDisp:=disp; addrBase:=None; addrIndex:=None |} => *)
  (*                       (* alternate encoding: mod00 case2, making reg in si_p be ESP *) *)
  (*                       case3 (r,disp) *)
  (*                     | {| addrDisp:=disp; addrBase:=None; addrIndex:=Some si |} => *)
  (*                       (* special case: disp32[index*scale]; *)
  (*                          the mod bits in mod/rm must be 00 *) *)
  (*                       case2 (r,(Some si,disp)) *)
  (*                     | {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=None |} => *)
  (*                       if (register_eq_dec bs ESP) then *)
  (*                           (* alternate encoding: when disp is not zero or cannot *)
  (*                              be represented as a byte, then case5/7 can always *)
  (*                              be used *) *)
  (*                           if (Word.eq disp Word.zero) then *)
  (*                             case1 (r, (None, ESP)) *)
  (*                           else *)
  (*                             if (repr_in_signed_byte_dec disp) then *)
  (*                               case5 (r, ((None, ESP), sign_shrink32_8 disp)) *)
  (*                             else case7 (r, ((None, ESP), disp)) *)
  (*                       else *)
  (*                         if (register_eq_dec bs EBP) then *)
  (*                           (* alternate encoding: case6 can always be used *) *)
  (*                           if (repr_in_signed_byte_dec disp) *)
  (*                           then case4 (r, (bs, sign_shrink32_8 disp)) *)
  (*                           else case6 (r, (bs, disp)) *)
  (*                         else *)
  (*                           (* alternate encoding: case4/6 can always be used depending *)
  (*                              on disp *) *)
  (*                           if (Word.eq disp Word.zero) then *)
  (*                             case0 (r, bs) *)
  (*                           else *)
  (*                             if (repr_in_signed_byte_dec disp) *)
  (*                             then case4 (r, (bs, sign_shrink32_8 disp)) *)
  (*                             else case6 (r, (bs, disp)) *)
  (*                     | {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=Some sci |} => *)
  (*                       if (register_eq_dec (snd sci) ESP) then None *)
  (*                       else if (register_eq_dec bs EBP) then *)
  (*                              (* alternate encoding: case7 can always be used *) *)
  (*                              if (repr_in_signed_byte_dec disp) then *)
  (*                                case5 (r, ((Some sci, bs), sign_shrink32_8 disp)) *)
  (*                              else case7 (r, ((Some sci, bs), disp)) *)
  (*                            else *)
  (*                              (* alternate encoding: case5/7 can be used *) *)
  (*                              if (Word.eq disp Word.zero) then *)
  (*                                case1 (r, (Some sci, bs)) *)
  (*                              else *)
  (*                                if (repr_in_signed_byte_dec disp) then *)
  (*                                  case5 (r, ((Some sci, bs), sign_shrink32_8 disp)) *)
  (*                                else case7 (r, ((Some sci, bs), disp)) *)
  (*                   end) *)
  (*              & _); clear_ast_defs. invertible_tac. *)
  (*   - destruct_union. *)
  (*     + (* case 0 *) *)
  (*       destruct v as [r bs]. *)
  (*       rewrite Word.int_eq_refl. *)
  (*       assert (bs<>ESP /\ bs<>EBP). *)
  (*         ibr_prover. apply reg_no_esp_ebp_neq. trivial. *)
  (*       abstract (sim; bg_pf_sim; printable_tac; ibr_prover). *)
  (*     + (* case 1 *) *)
  (*       destruct v as [r [si bs]]. *)
  (*       rewrite Word.int_eq_refl. *)
  (*       assert (bs <> EBP). *)
  (*         ibr_prover. apply reg_no_ebp_neq. trivial. *)
  (*       destruct si as [[sc idx] | ]. *)
  (*       * assert (idx <> ESP). *)
  (*           ibr_prover. eapply si_p_rng_some. eassumption. *)
  (*         abstract (bg_pf_sim; printable_tac). *)
  (*       * abstract (bg_pf_sim; printable_tac; ibr_prover). *)
  (*     + (* case 2 *) *)
  (*       destruct v as [r [si disp]]. *)
  (*       abstract (destruct si as [[sc idx] | ]; printable_tac; ibr_prover). *)
  (*     + (* case 3 *) *)
  (*       abstract printable_tac. *)
  (*     + (* case 4 *) *)
  (*       destruct v as [r [bs disp]]. *)
  (*       abstract (bg_pf_sim; try destruct_head; printable_tac; ibr_prover). *)
  (*     + (* case 5 *) *)
  (*       destruct v as [r [[si bs] disp]]. *)
  (*       rewrite sign_shrink32_8_inv. *)
  (*       destruct si as [[sc idx] | ]. *)
  (*       * unfold sib_p in *; *)
  (*         assert (idx <> ESP). *)
  (*           ibr_prover. eapply si_p_rng_some. eassumption. *)
  (*         abstract (bg_pf_sim; try destruct_head; printable_tac; ibr_prover). *)
  (*       * abstract (bg_pf_sim; try destruct_head; printable_tac; ibr_prover). *)
  (*     + (* case 6 *) *)
  (*       destruct v as [r [bs disp]]. *)
  (*       abstract (bg_pf_sim; try destruct_head; printable_tac; ibr_prover). *)
  (*     + (* case 7 *) *)
  (*       destruct v as [r [[si bs] disp]]. *)
  (*       destruct si as [[sc idx] | ]. *)
  (*       * unfold sib_p in *; *)
  (*         assert (idx <> ESP). *)
  (*           ibr_prover. eapply si_p_rng_some. eassumption. *)
  (*         abstract (bg_pf_sim; try destruct_head; printable_tac; ibr_prover). *)
  (*       * abstract (bg_pf_sim; try destruct_head; printable_tac; ibr_prover). *)
  (*   - destruct w as [r addr]. *)
  (*     destruct addr. *)
  (*     abstract (destruct addrBase as [bs | ]; *)
  (*               destruct addrIndex as [[si idx] | ]; *)
  (*               bg_pf_sim; try parsable_tac; *)
  (*               apply Word.int_eq_true_iff2 in Hdisp_eq;  *)
  (*               subst addrDisp; trivial). *)
  (* Defined. *)

  (** Moderm mode 00 *)
  Definition rm00 := 
    (* case 0 *)
    (reg_no_esp_ebp |+|
    (* case 1 *)
     "100" $$ si_p $ reg_no_ebp) |+|
    (* case 2 *)
    ("100" $$ si_p $ "101" $$ word |+|
    (* case 3 *)
     "101" $$ word).

  (** Moderm mode 01 *)
  Definition rm01 := 
    (* case 0 *)
    reg_no_esp $ byte |+|
    (* case 1 *)
    "100" $$ sib_p $ byte.

  (** Moderm mode 10 *)
  Definition rm10 := 
    (* case 0 *)
    reg_no_esp $ word |+|
    (* case 1 *)
    "100" $$ sib_p $ word.

  (** Same as modrm_gen but no mod "11" case; that is, the second must
      produce an address in a mem operand *)
  (* The old modrm_gen_noreg parser has three help parsers defined first:
     rm00, rm01, rm10; each of them constructs an address. However,
     combining those three would be difficult. In this version, we
     essentially list all possible cases of modes 00, 01, 10 and have a big
     inverse function; didn't use the gen_ast_def tactic because the following
     version using inl/inr explicitly is a bit faster for proofs. *)
  Definition modrm_gen_noreg (reg_t: type)
    (reg_p: wf_bigrammar reg_t) : wf_bigrammar (pair_t reg_t address_t).
    intros.
    refine ((    ("00" $$ reg_p $ rm00) 
             |+| ("01" $$ reg_p $ rm01)
             |+| ("10" $$ reg_p $ rm10))
              @ (fun v => 
                   match v with
                     (* mode 00 *)
                     | inl (r,v1) => 
                       let addr := 
                           match v1 with
                             (* mode 00, case 0 *)
                             | inl (inl base) =>
                               mkAddress (Word.repr 0) (Some base) None
                             (* mode 00, case 1 *)
                             | inl (inr (si,base)) =>
                               mkAddress (Word.repr 0) (Some base) si
                             (* mode 00, case 2 *)
                             | inr (inl (si,disp)) =>
                               mkAddress disp None si
                             (* mode 00, case 3 *)
                             | inr (inr disp) =>
                               mkAddress disp None None
                           end
                       in (r,addr)
                     (* mode 01 *)
                     | inr (inl (r,v1)) =>
                       let addr := 
                           match v1 with
                             (* mode 01, case 0 *)
                             | inl (bs,disp) =>
                               mkAddress (sign_extend8_32 disp) (Some bs) None
                             (* mode 01, case 1 *)
                             | inr ((si,bs),disp) =>
                               mkAddress (sign_extend8_32 disp) (Some bs) si
                           end 
                       in (r,addr)
                     (* mode 10 *)
                     | inr (inr (r,v1)) =>
                       let addr :=
                           match v1 with
                             (* mode 10, case 0 *)
                             | inl (bs,disp) =>
                               mkAddress disp (Some bs) None
                             (* mode 10, case 1 *)
                             | inr ((si,bs),disp) =>
                               mkAddress disp (Some bs) si
                           end
                       in (r,addr)
                   end %% pair_t reg_t address_t)
               & (fun u:[|pair_t reg_t address_t|] => 
                    let (r,addr) := u in
                    match addr with
                      | {| addrDisp:=disp; addrBase:=None; addrIndex:=None |} =>
                        (* alternate encoding: mod00 case2, making reg in si_p be ESP *)
                        Some (inl (r, (inr (inr disp))))
                      | {| addrDisp:=disp; addrBase:=None; addrIndex:=Some si |} =>
                        (* special case: disp32[index*scale]; 
                           the mod bits in mod/rm must be 00 *)
                        Some (inl (r, (inr (inl (Some si,disp)))))
                      | {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=None |} =>
                        if (register_eq_dec bs ESP) then
                            (* alternate encoding: when disp is not zero or cannot 
                               be represented as a byte, then mode01 case 1 and
                               mode10 case 1 can always be used *)
                            if (Word.eq disp Word.zero) then
                              Some (inl (r, (inl (inr (None, ESP)))))
                            else
                              if (repr_in_signed_byte_dec disp) then
                                Some (inr (inl (r, inr ((None, ESP), 
                                                        sign_shrink32_8 disp))))
                              else Some (inr (inr (r, inr ((None, ESP), disp))))
                        else
                          if (register_eq_dec bs EBP) then
                            (* alternate encoding: mode 10 case0 can always be used *)
                            if (repr_in_signed_byte_dec disp)
                            then Some (inr (inl (r, inl (bs, sign_shrink32_8 disp))))
                            else Some (inr (inr (r, inl (bs, disp))))
                          else
                            (* alternate encoding: mode 01 case 0 and mode 10 case 0 
                               can always be used depending on disp *)
                            if (Word.eq disp Word.zero) then
                              Some (inl (r, inl (inl bs)))
                            else
                              if (repr_in_signed_byte_dec disp)
                              then Some (inr (inl (r, inl (bs,
                                                           sign_shrink32_8 disp))))
                              else Some (inr (inr (r, inl (bs, disp))))
                      | {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=Some sci |} =>
                        if (register_eq_dec (snd sci) ESP) then None
                        else if (register_eq_dec bs EBP) then
                               (* alternate encoding: mode10 case1 *)
                               if (repr_in_signed_byte_dec disp) then
                                 Some (inr (inl (r, inr ((Some sci, bs),
                                                         sign_shrink32_8 disp))))
                               else Some (inr (inr (r, inr ((Some sci, bs), disp))))
                             else 
                               (* alternate encoding: mode01 case 1; mode10 case1 *)
                               if (Word.eq disp Word.zero) then
                                 Some (inl (r, (inl (inr (Some sci, bs)))))
                               else
                                 if (repr_in_signed_byte_dec disp) then
                                   Some (inr (inl (r, (inr ((Some sci, bs),
                                                            sign_shrink32_8 disp)))))
                                 else Some (inr (inr (r, inr ((Some sci, bs), disp))))
                    end)
               & _); invertible_tac.
    - destruct_union.
      + (* mode 00 *)
        destruct v as [r v].
        unfold rm00 in *; destruct_union.
        * (* case 0 *)
         rewrite Word.int_eq_refl.
         rename v into bs.
         assert (bs<>ESP /\ bs<>EBP).
           ibr_prover. apply reg_no_esp_ebp_neq. trivial.
         abstract (sim; bg_pf_sim; printable_tac; ibr_prover).
        * (* case 1 *)
          destruct v as [si bs].
          rewrite Word.int_eq_refl.
          assert (bs <> EBP).
            ibr_prover. apply reg_no_ebp_neq. trivial.
          destruct si as [[sc idx] | ].
          { assert (idx <> ESP).
              ibr_prover. eapply si_p_rng_some. eassumption.
            abstract (bg_pf_sim; printable_tac).
          }
          { abstract (bg_pf_sim; printable_tac; ibr_prover). }
        * (* case 2 *)
          destruct v as [si disp].
          abstract (destruct si as [[sc idx] | ];
                    printable_tac; ibr_prover).
        * (* case 3 *) abstract printable_tac.
      + (* mode 01 *)
        destruct v as [r v].
        unfold rm01 in *; destruct_union; ibr_prover.
        * (* case 0 *)
          destruct v as [bs disp].
          abstract (unfold rm00; bg_pf_sim;
                    try destruct_head; printable_tac; ibr_prover).
        * (* case 1 *)
          destruct v as [[si bs] disp].
          rewrite sign_shrink32_8_inv.
          destruct si as [[sc idx] | ].
          { unfold sib_p in *; 
            assert (idx <> ESP).
              ibr_prover. eapply si_p_rng_some. eassumption.
            abstract (unfold rm00; bg_pf_sim;
                      try destruct_head; printable_tac; ibr_prover). }
          { abstract (unfold rm00; bg_pf_sim;
                      try destruct_head; printable_tac; ibr_prover). }
      + (* mode 10 *)
        destruct v as [r v].
        unfold rm10 in *; destruct_union; ibr_prover.
        * (* case 0 *)
          destruct v as [bs disp].
          abstract (unfold rm00, rm01; bg_pf_sim; 
                    try destruct_head; printable_tac; ibr_prover).
        * (* case 7 *)
          destruct v as [[si bs] disp].
          destruct si as [[sc idx] | ].
          { unfold rm00, rm01, sib_p in *; 
            assert (idx <> ESP).
              ibr_prover. eapply si_p_rng_some. eassumption.
            abstract (bg_pf_sim; try destruct_head; printable_tac; ibr_prover).
          }
          { abstract (unfold rm00, rm01; bg_pf_sim; 
                      try destruct_head; printable_tac; ibr_prover). }
    - destruct w as [r addr].
      destruct addr.
      abstract (destruct addrBase as [bs | ];
                destruct addrIndex as [[si idx] | ];
                bg_pf_sim; try parsable_tac;
                apply Word.int_eq_true_iff2 in Hdisp_eq;
                subst addrDisp; trivial).
  Defined.

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
  (* Arguments modrm_gen_noreg2 [reg_t res_t]. *)

  (** a general modrm grammar for integer, floating-point, sse, mmx instructions *)
  Definition modrm_gen (reg_t: type)
    (reg_p : wf_bigrammar reg_t)  (* the grammar that parse a register *)
    : wf_bigrammar (sum_t (pair_t reg_t address_t) (pair_t reg_t reg_t)) :=
    modrm_gen_noreg reg_p |+| "11" $$ reg_p $ reg_p.

  (* Similar to mod/rm grammar except that the register field is fixed to a
   * particular bit-pattern, and the pattern starting with "11" is excluded. *)
  Definition ext_op_modrm_noreg_ret_addr
          (bs: string) : wf_bigrammar address_t.
    intros.
    refine ((modrm_gen_noreg (! bs))
              @ (fun v => snd v %% address_t)
              & (fun u => Some ((),u))
              & _); invertible_tac.
  Defined.

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

  Definition modrm_noreg : wf_bigrammar (pair_t register_t address_t) :=
    modrm_gen_noreg reg.

  Definition modrm_bv2_noreg: wf_bigrammar (pair_t (bitvector_t 2) address_t) :=
    modrm_gen_noreg (field_intn 2).

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

  Definition seg_modrm : wf_bigrammar (pair_t segment_register_t operand_t).
    refine((modrm_gen_noreg segment_reg_p |+| "11" $$ segment_reg_p $ reg)
           @ (fun v =>
                match v with
                    | inl (sr, addr) => (sr, Address_op addr)
                    | inr (sr, r) => (sr, Reg_op r)
                end %% (pair_t segment_register_t operand_t))
           & (fun u =>
                match u with
                  | (sr, Address_op addr) => Some (inl (sr, addr))
                  | (sr, Reg_op r) => Some (inr (sr, r))
                  | _ => None
                end)
           & _); invertible_tac.
    - destruct_union; destruct v; printable_tac.
    - destruct w as [r op]; destruct op; parsable_tac.
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
  Proof. intros; unfold modrm_gen_noreg in *. ibr_prover.
    destruct_union; destruct v; ibr_prover; crush.
  Qed.

  (* can prove a more precise range lemma if necessary *)
  Lemma modrm_gen_noreg_rng reg_t (reg_p: wf_bigrammar reg_t)
        (r1 r2:[|reg_t|]) addr: 
    in_bigrammar_rng (` (modrm_gen_noreg reg_p)) (r1, addr) ->
    in_bigrammar_rng (` reg_p) r2 -> 
    in_bigrammar_rng (` (modrm_gen_noreg reg_p)) (r2, addr).
  Proof. intros; unfold modrm_gen_noreg in *. ibr_prover.
    compute [fst].
    match goal with
      | [v: [|sum_t ?t1 (sum_t ?t2 ?t3)|] |- _] => 
        destruct_union; ibr_prover;
        destruct v as [r1' v];
        [exists (inl [|sum_t t2 t3|] (r2, v)) | 
         exists (inr [|t1|] (inl [|t3|] (r2,v))) |
         eexists (inr [|t1|] (inr [|t2|] (r2,v))) ]
    end;
    split; ibr_prover; crush.
  Qed.

  Lemma ext_op_modrm_rng1 bs r: 
    in_bigrammar_rng (` (ext_op_modrm bs)) (Reg_op r).
  Proof. unfold ext_op_modrm; intros; ibr_prover.
    exists (inr [|address_t|] r); compute [fst]. 
    split. 
    + unfold ext_op_modrm_gen; ibr_prover.
    + trivial.
  Qed.
  Hint Resolve ext_op_modrm_rng1: ibr_rng_db.

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

  Lemma modrm_ret_reg_rng1 r1 r2: in_bigrammar_rng (` modrm_ret_reg) (r1, Reg_op r2).
  Proof. intros. unfold modrm_ret_reg, modrm_gen. ibr_prover. compute [fst].
    exists (inr [|pair_t register_t address_t|] (r1, r2)).
    split; [ibr_prover | trivial].
  Qed.
  Hint Resolve modrm_ret_reg_rng1: ibr_rng_db.

  (* with more work, this lemma could be made more general; will do it if necessary *)
  Lemma modrm_ret_reg_rng2 r1 r2 addr: 
    in_bigrammar_rng (` modrm_ret_reg) (r1, Address_op addr) ->
    in_bigrammar_rng (` modrm_ret_reg) (r2, Address_op addr).
  Proof. unfold modrm_ret_reg; intros; ibr_prover; compute [fst].
    destruct v as [[r1' addr'] | [r1' r2']]; try congruence.
    sim; subst r1' addr'.
    unfold modrm_gen in *; ibr_prover.
    exists (inl [|pair_t register_t register_t|] (r2,addr)).
    split.
    - ibr_prover. eapply modrm_gen_noreg_rng. eassumption. ibr_prover.
    - trivial.
  Qed.
  Hint Extern 1 (in_bigrammar_rng (` (modrm_ret_reg)) (_, Address_op _)) =>
    eapply modrm_ret_reg_rng2; eassumption : ibr_rng_db.

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

  Lemma field_intn_rng n i: 
    in_bigrammar_rng (` (field_intn n)) i.
  Proof. unfold field_intn; intros. ibr_prover.
    exists (bitsn_of_intn i). split.
    - apply field'_rng.
    - simpl. autorewrite with inv_db. trivial.
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

  (* a tactic used to simplify proofs when proving bidirectional grammars about instrs *)
  Local Ltac ins_pf_sim :=
    ibr_prover; bg_pf_sim;
    repeat match goal with
      | [H: in_bigrammar_rng (` (modrm_ret_reg)) (?r1 ?op2) |- _] => 
        let H2 := fresh "H" in
        generalize (modrm_ret_reg_rng_inv H); intro H2;
        destruct H2 as [H2 | H2]; destruct H2; subst op2
      | [H: in_bigrammar_rng (` (ext_op_modrm _)) ?op |- _] => 
        let H2 := fresh "H" in
        generalize (ext_op_modrm_rng_inv H); intro H2;
        destruct H2 as [H2 | H2]; destruct H2; subst op
    end.

  Local Ltac local_printable_tac := 
    repeat match goal with
             | [v: [|pair_t _ _|] |- _] => destruct v
           end; ins_pf_sim; printable_tac; ibr_prover.

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
      destruct d; ins_pf_sim; printable_tac; ibr_prover.
    + (* case 1 *)
      destruct v as [r b]. 
      destruct r; ins_pf_sim; printable_tac; ibr_prover.
      (* EAX case *)
      apply imm_p_rng; apply repr_in_signed_extend; omega.
    + (* case 2 *)
      destruct v as [r b]; 
      destruct r; ins_pf_sim; printable_tac; ibr_prover.
    + (* case 3 *)
      destruct v as [r op2]; ins_pf_sim;
      destruct r; printable_tac; ibr_prover.
    + (* case 4 *)
      ins_pf_sim; printable_tac; ibr_prover.
    + (* case 5 *)
      ibr_prover; printable_tac; ibr_prover.
    + (* case 6 *)
      destruct v as [op b]; ins_pf_sim; printable_tac; ibr_prover.
    + (* case 7 *)
      destruct v as [op b]; ins_pf_sim;
      printable_tac; ibr_prover.
    + (* case 8 *)
      destruct v as [op1 op2]; ins_pf_sim;
      printable_tac; ibr_prover.
  - destruct w as [wd [op1 op2]].
    destruct op1; try parsable_tac.
    + (* op1 = Reg_op _ *)
      destruct op2; try parsable_tac.
      destruct r; destruct wd; ins_pf_sim; parsable_tac.
    + (* op1 = Address_op _ *)
      destruct op2; try parsable_tac.
      destruct wd; ins_pf_sim; parsable_tac.
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
    - destruct_union; local_printable_tac.
    - destruct w as [op1 op2]; destruct op1; destruct op2;
      ins_pf_sim; parsable_tac.
  Time Defined.

  Definition BT_p := bit_test_p "100" "00".
  Definition BTC_p := bit_test_p "111" "11".
  Definition BTR_p := bit_test_p "110" "10".
  Definition BTS_p := bit_test_p "101" "01".

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
    - destruct_union; local_printable_tac.
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
    - destruct_union; local_printable_tac.
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
    - destruct_union; try local_printable_tac.
      + (* case 3 *)
        destruct v as [[r1 op2] imm].
        destruct opsize_override; compute [negb];
        ins_pf_sim; printable_tac; ibr_prover.
    - abstract
        (destruct w as [bl [op1 [w1 w2]]];
         destruct op1; destruct bl;
         destruct w1 as [op2 | ];
         destruct w2; try parsable_tac;
         destruct op2; destruct opsize_override;
         ins_pf_sim; parsable_tac).
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
    - destruct_union; try local_printable_tac.
      + (* case 0 *)
        destruct v as [w r].
        destruct w; printable_tac; ibr_prover.
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
    - destruct_union; local_printable_tac.
    - destruct w; ins_pf_sim; parsable_tac.
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
    - abstract (destruct_union; local_printable_tac).
    - abstract
        (destruct w as [near [absolute [op w1]]]; destruct w1;
         destruct near; destruct absolute; destruct op;
         ins_pf_sim; parsable_tac).
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
    - abstract (destruct_union; local_printable_tac).
    - abstract 
        (destruct w as [wd [op1 op2]]; destruct op1; try parsable_tac;
         destruct op2; ins_pf_sim; try parsable_tac;
         destruct wd; try parsable_tac;
         destruct r; parsable_tac).
  Defined.

  Definition MOVCR_p :=
    "0000" $$ "1111" $$ "0010" $$ "00" $$ anybit $ "0" $$ "11"
           $$ control_reg_p $ reg.

  Definition MOVDR_p := 
    "0000" $$ "1111" $$ "0010" $$ "00" $$ anybit $ "111" $$ debug_reg_p $ reg.

  Definition MOVSR_p := "1000" $$ "11" $$ anybit $ "0" $$ seg_modrm.
  
  Definition MOVBE_p : wf_bigrammar (pair_t operand_t operand_t). 
    refine ("0000" $$ "1111" $$ "0011" $$ "1000" $$ "1111" $$ "000"
                   $$ anybit $ modrm_ret_reg
             @ (fun v: [|pair_t bool_t (pair_t register_t operand_t)|] => 
                  match v with
                    | (w,(r1,op2)) =>
                      if w then (op2, Reg_op r1) else (Reg_op r1, op2)
                  end %% pair_t operand_t operand_t)
             & (fun u => 
                  match u with
                    | (Reg_op r1, Reg_op r2) =>
                      (* alternate encoding: make w false and swap the two operands *)
                      Some (true, (r2, Reg_op r1)) 
                    | (Reg_op r1, Address_op _) => 
                      Some (false, (r1, snd u))
                    | (Address_op _, Reg_op r1) => 
                      Some (true, (r1, fst u))
                    | _ => None
                  end)
             & _); invertible_tac.
    - destruct v as [w [r1 op2]]. 
      destruct w; ins_pf_sim; printable_tac; ibr_prover.
    - destruct w as [op1 op2]; destruct op1; destruct op2; parsable_tac.
  Defined.
                                             
  Definition MOVS_p := "1010" $$ "010" $$ anybit. 
  Definition MOVSX_p := "0000" $$ "1111" $$ "1011" $$ "111" $$ anybit $ modrm.
  Definition MOVZX_p := "0000" $$ "1111" $$ "1011" $$ "011" $$ anybit $ modrm.

  Definition MUL_p := "1111" $$ "011" $$ anybit $ ext_op_modrm "100". 
  Definition NEG_p := "1111" $$ "011" $$ anybit $ ext_op_modrm "011".

  Definition NOP_p := 
  (* The following is the same as the encoding of "XCHG EAX, EAX"
    "1001" $$ bits "0000" @ (fun _ => NOP None %% instruction_t)
  |+| *)
    "0000" $$ "1111" $$ "0001" $$ "1111" $$ ext_op_modrm "000". 

  Definition NOT_p := "1111" $$ "011" $$ anybit $ ext_op_modrm "010".

  Definition OUT_p :wf_bigrammar (pair_t bool_t (option_t Byte_t)).
    refine ((("1110" $$ "011" $$ anybit $ byte) |+|
             ("1110" $$ "111" $$ anybit))
              @ (fun v =>
                   match v with
                     | inl (w, b) => (w, Some b)
                     | inr w => (w, None)
                   end %% pair_t bool_t (option_t Byte_t))
              & (fun u:[|pair_t bool_t (option_t Byte_t)|] => 
                   match u with
                     | (w, Some b) => Some (inl (w,b))
                     | (w, None) => Some (inr w)
                   end)
              & _); invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w as [wd [b | ]]; parsable_tac.
  Defined.

  Definition OUTS_p := "0110" $$ "111" $$ anybit.

  Definition POP_p : wf_bigrammar operand_t. 
    refine (("1000" $$ "1111" $$ ext_op_modrm "000" |+|
             "0101" $$ "1" $$ reg) 
              @ (fun v => 
                   match v with
                     | inl op => op
                     | inr r => Reg_op r
                   end %% operand_t)
              & (fun u =>
                   match u with
                     | Reg_op r => Some (inr r) (* alterante encoding: the first case *)
                     | Address_op addr => Some (inl u)
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition POPSR_env : AST_Env segment_register_t :=
    {0, "000" $$ "00" $$ ! "111", (fun v => ES %% segment_register_t)} :::
    {1, "000" $$ "10" $$ ! "111", (fun v => SS %% segment_register_t)} :::
    {2, "000" $$ "11" $$ ! "111", (fun v => DS %% segment_register_t)} :::
    {3, "0000" $$ "1111" $$ "10" $$ "100" $$ ! "001",
     (fun _ => FS %% segment_register_t)} :::
    {4, "0000" $$ "1111" $$ "10" $$ "101" $$ ! "001",
     (fun _ => GS %% segment_register_t)} :::
    ast_env_nil.

  Definition POPSR_p : wf_bigrammar segment_register_t.
    gen_ast_defs POPSR_env.
    refine (gr @ (mp: _ -> [|segment_register_t|])
               & (fun u => match u with
                             | ES => case0 ()
                             | SS => case1 ()
                             | DS => case2 ()
                             | FS => case3 ()
                             | GS => case4 ()
                             | _ => None
                           end)
               & _); clear_ast_defs; invertible_tac.
    - destruct_union; printable_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition POPA_p := "0110" $$ ! "0001".
  Definition POPF_p := "1001" $$ ! "1101".

  Definition PUSH_env : AST_Env (pair_t bool_t operand_t) :=
    {0, "1111" $$ "1111" $$ ext_op_modrm_noreg_ret_addr "110", 
     (fun addr => (true, Address_op addr) %% pair_t bool_t operand_t)} :::
    {1, "0101" $$ "0" $$ reg, 
     (fun r => (true, Reg_op r) %% pair_t bool_t operand_t)} :::
    {2, "0110" $$ "1010" $$ byte,
     (fun b => (false, Imm_op (sign_extend8_32 b)) %% pair_t bool_t operand_t)} :::
    {3, "0110" $$ "1000" $$ word,
     (fun w => (true, Imm_op w) %% pair_t bool_t operand_t)} :::
    ast_env_nil.

  Definition PUSH_p : wf_bigrammar (pair_t bool_t operand_t).
    gen_ast_defs PUSH_env.
    refine (gr @ (mp: _ -> [|pair_t bool_t operand_t|])
               & (fun u =>
                    match u with
                      | (true, Address_op addr) => case0 addr
                      | (true, Reg_op r) => case1 r
                      | (true, Imm_op w) => case3 w
                      | (false, Imm_op w) =>
                        if (repr_in_signed_byte_dec w) then case2 (sign_shrink32_8 w)
                        else None
                      | _ => None
                    end)
               & _); clear_ast_defs; invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w as [b op]; destruct b; destruct op; ins_pf_sim; parsable_tac.
  Defined.

  Definition PUSHSR_env : AST_Env segment_register_t :=
    {0, "000" $$ "00" $$ ! "110", (fun v => ES %% segment_register_t)} :::
    {1, "000" $$ "01" $$ ! "110", (fun v => CS %% segment_register_t)} :::
    {2, "000" $$ "10" $$ ! "110", (fun v => SS %% segment_register_t)} :::
    {3, "000" $$ "11" $$ ! "110", (fun v => DS %% segment_register_t)} :::
    {4, "0000" $$ "1111" $$ "10" $$ "100" $$ ! "000", 
     (fun v => FS %% segment_register_t)} :::
    {5, "0000" $$ "1111" $$ "10" $$ "101" $$ ! "000",
     (fun v => GS %% segment_register_t)} :::
    ast_env_nil.

  Definition PUSHSR_p : wf_bigrammar segment_register_t.
    gen_ast_defs PUSHSR_env.
    refine (gr @ (mp: _ -> [|segment_register_t|])
               & (fun u => 
                    match u with
                      | ES => case0 ()
                      | CS => case1 ()
                      | SS => case2 ()
                      | DS => case3 ()
                      | FS => case4 ()
                      | GS => case5 ()
                    end)
               & _); clear_ast_defs; invertible_tac.
     - destruct_union; printable_tac.
     - destruct w; crush.
  Defined.

  Definition PUSHA_p := "0110" $$ ! "0000".
  Definition PUSHF_p := "1001" $$ ! "1100".

  Definition rotate_p (extop:string): 
    wf_bigrammar (pair_t bool_t (pair_t operand_t reg_or_immed_t)).
    intros.
    refine (("1101" $$ "000" $$ anybit $ ext_op_modrm extop |+|
             "1101" $$ "001" $$ anybit $ ext_op_modrm extop |+|
             "1100" $$ "000" $$ anybit $ ext_op_modrm extop $ byte)
              @ (fun v => 
                   match v with
                     | inl (w, op) => (w, (op, Imm_ri (Word.repr 1)))
                     | inr (inl (w, op)) => (w, (op, Reg_ri ECX))
                     | inr (inr (w, (op, b))) => (w, (op, Imm_ri b))
                   end %% pair_t bool_t (pair_t operand_t reg_or_immed_t))
              & (fun u: [|pair_t bool_t (pair_t operand_t reg_or_immed_t)|] => 
                   let (w,u1) := u in
                   match u1 with
                     | (Reg_op _, Imm_ri b) 
                     | (Address_op _, Imm_ri b) => Some (inr (inr (w,(fst u1,b))))
                     | (Reg_op _, Reg_ri ECX)
                     | (Address_op _, Reg_ri ECX) => Some (inr (inl (w, fst u1)))
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w as [w [op ri]]; destruct op; try parsable_tac;
      destruct ri as [rg | ]; try parsable_tac;
      destruct rg; parsable_tac.
  Defined.

  Definition RCL_p := rotate_p "010".
  Definition RCR_p := rotate_p "011".

  Definition RDMSR_p := "0000" $$ "1111" $$ "0011" $$ ! "0010".
  Definition RDPMC_p := "0000" $$ "1111" $$ "0011" $$ ! "0011".
  Definition RDTSC_p := "0000" $$ "1111" $$ "0011" $$ ! "0001".
  Definition RDTSCP_p := "0000" $$ "1111" $$ "0000" $$ "0001" $$ "1111"
                                $$ ! "1001".

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

  Definition RET_env : AST_Env (pair_t bool_t (option_t Half_t)) := 
    {0, "1100" $$ ! "0011", 
     (fun v => (true, None) %% pair_t bool_t (option_t Half_t))} :::
    {1, "1100" $$ "0010" $$ halfword,
     (fun h => (true, Some h) %% pair_t bool_t (option_t Half_t))} :::
    {2, "1100" $$ ! "1011",
     (fun h => (false, None) %% pair_t bool_t (option_t Half_t))} :::
    {3, "1100" $$ "1010" $$ halfword,
     (fun h => (false, Some h) %% pair_t bool_t (option_t Half_t))} :::
    ast_env_nil.

  Definition RET_p : wf_bigrammar (pair_t bool_t (option_t Half_t)).
    gen_ast_defs RET_env.
    refine (gr @ (mp: _ -> [|pair_t bool_t (option_t Half_t)|])
               & (fun u => 
                    match u with
                      | (true, None) => case0 ()
                      | (true, Some h) => case1 h
                      | (false, None) => case2 ()
                      | (false, Some h) => case3 h
                    end)
               & _); clear_ast_defs; invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w as [b [h | ]]; destruct b; parsable_tac.
  Defined.

  Definition ROL_p := rotate_p "000".
  Definition ROR_p := rotate_p "001".
  Definition RSM_p := "0000" $$ "1111" $$ "1010" $$ ! "1010".
  Definition SAHF_p := "1001" $$ ! "1110".
  Definition SAR_p := rotate_p "111".
  Definition SCAS_p := "1010" $$ "111" $$ anybit.

  (* Intel manual says the reg field in modrm_ret_reg must be 000; however, it
     seems that an x86 processor accepts any combination in the reg field *)
  Definition SETcc_p : wf_bigrammar (pair_t condition_t operand_t).
    refine("0000" $$ "1111" $$ "1001" $$ tttn $ modrm_ret_reg
             @ (fun v => (fst v, snd (snd v)) %% pair_t condition_t operand_t)
             & (fun u => 
                  match snd u with
                    | Reg_op _ | Address_op _ =>
                      (* alternate encoding: the reg can be any register *)
                      Some (fst u, (EAX, snd u))
                    | _ => None
                  end)
             & _); invertible_tac.
    - destruct v as [ct [r op]]; ins_pf_sim; printable_tac; ibr_prover.
    - destruct w as [cd op]; destruct op; parsable_tac.
  Defined.

  Definition SGDT_p := "0000" $$ "1111" $$ "0000" $$ "0001"
                              $$ ext_op_modrm_noreg "000".
  Definition SHL_p := rotate_p "100".

  Definition shiftdouble_env (opcode:string) : 
    AST_Env (pair_t operand_t (pair_t register_t reg_or_immed_t)) :=
    {0, "0000" $$ "1111" $$ "1010" $$ opcode $$ "00" $$ "11" $$ reg $ reg $ byte,
     (fun v => match v with | (r2,(r1,b)) => (Reg_op r1, (r2, Imm_ri b)) end
                 %% pair_t operand_t (pair_t register_t reg_or_immed_t))} :::
    {1, "0000" $$ "1111" $$ "1010" $$ opcode $$ "00" $$ modrm_noreg $ byte,
     (fun v => match v with
                 | ((r,addr), b) => (Address_op addr, (r, Imm_ri b)) end
                 %% pair_t operand_t (pair_t register_t reg_or_immed_t))} :::
    {2, "0000" $$ "1111" $$ "1010" $$ opcode $$ "01" $$ "11" $$ reg $ reg,
    (fun v => match v with | (r2,r1) => (Reg_op r1, (r2, Reg_ri ECX)) end
                 %% pair_t operand_t (pair_t register_t reg_or_immed_t))} :::
    {3, "0000" $$ "1111" $$ "1010" $$ opcode $$ "01" $$ modrm_noreg,
    (fun v => match v with
                | (r,addr) => (Address_op addr, (r, Reg_ri ECX)) end
                 %% pair_t operand_t (pair_t register_t reg_or_immed_t))} :::
    ast_env_nil.

  Definition shiftdouble_p (opcode:string) :
    wf_bigrammar (pair_t operand_t (pair_t register_t reg_or_immed_t)).
    intros; gen_ast_defs (shiftdouble_env opcode).
    refine (gr @ (mp: _ -> 
                      [|pair_t operand_t (pair_t register_t reg_or_immed_t)|])
               & (fun u:[|pair_t operand_t (pair_t register_t reg_or_immed_t)|] => 
                    let (op1,u1):=u in
                    let (r2,ri):=u1 in
                    match op1 with
                      | Reg_op r1 => 
                        match ri with
                          | Imm_ri b => case0 (r2,(r1,b))
                          | Reg_ri ECX => case2 (r2,r1)
                          | _ => None
                        end
                      | Address_op addr =>
                        match ri with
                          | Imm_ri b => case1 ((r2,addr),b)
                          | Reg_ri ECX => case3 (r2,addr)
                          | _ => None
                        end
                      | _ => None
                    end)
               & _); clear_ast_defs; invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w as [op [r2 ri]]. 
      destruct op; destruct ri as [r3 | addr]; try parsable_tac;
      destruct r3; parsable_tac.
  Defined.
        
  Definition SHLD_p := shiftdouble_p "01".
  Definition SHR_p := rotate_p "101".
  Definition SHRD_p := shiftdouble_p "11".

  Definition SIDT_p := 
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm_noreg "001".
  Definition SLDT_p := 
    "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "000".
  Definition SMSW_p := 
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ ext_op_modrm "100".
  Definition STC_p := "1111" $$ ! "1001".
  Definition STD_p := "1111" $$ ! "1101".
  Definition STI_p := "1111" $$ ! "1011".
  Definition STOS_p := "1010" $$ "101" $$ anybit.
  Definition STR_p := 
    "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "001".

  Definition Test_env (opsize_override:bool) : 
    AST_Env (pair_t bool_t (pair_t operand_t operand_t)) :=
    {0, "1111" $$ "0111" $$ ext_op_modrm "000" $ imm_p opsize_override,
     (fun v => (true, (fst v, Imm_op (snd v)))
                 %% pair_t bool_t (pair_t operand_t operand_t))} :::
    {1, "1111" $$ "0110" $$ ext_op_modrm "000" $ byte,
     (fun v => (false, (fst v, Imm_op (zero_extend8_32 (snd v))))
                 %% pair_t bool_t (pair_t operand_t operand_t))} :::
    {2, "1000" $$ "010" $$ anybit $ modrm_ret_reg,
     (fun v => 
        match v with
          | (w,(r1,op2)) => (w, (Reg_op r1, op2))
        end %% pair_t bool_t (pair_t operand_t operand_t))} :::
    {3, "1010" $$ "1001" $$ imm_p opsize_override,
     (fun v => (true, (Imm_op v, Reg_op EAX))
                 %% pair_t bool_t (pair_t operand_t operand_t))} :::
    {4, "1010" $$ "1000" $$ byte,
     (fun b => (false, (Reg_op EAX, Imm_op (zero_extend8_32 b)))
                 %% pair_t bool_t (pair_t operand_t operand_t))} :::
    ast_env_nil.

  Definition Test_p (opsize_override: bool) : 
    wf_bigrammar (pair_t bool_t (pair_t operand_t operand_t)).
    intros; gen_ast_defs (Test_env opsize_override).
    refine (gr @ (mp: _ -> [|pair_t bool_t (pair_t operand_t operand_t)|])
               & (fun u:[|pair_t bool_t (pair_t operand_t operand_t)|] => 
                    let (w,u1) := u in
                    let (op1,op2):=u1 in
                    match op2 with
                      | Imm_op imm =>
                        match op1 with
                          | Reg_op _ | Address_op _ => 
                            if w then 
                              case0 (op1, imm)
                            else
                              if repr_in_unsigned_byte_dec imm then
                                (* alternate encoding: case4 when op1 is EAX
                                   and imm within a byte *)
                                case1 (op1, zero_shrink32_8 imm)
                              else None
                          | _ => None
                        end
                      | Reg_op r2 =>
                        match op1 with
                          | Reg_op r1 => case2 (w, (r1, op2))
                          | Imm_op i => 
                            if (register_eq_dec r2 EAX) then
                              if w then case3 i
                              else None
                            else None
                          | _ => None
                        end
                      | Address_op _ =>
                        match op1 with
                          | Reg_op r1 => case2 (w, (r1, op2))
                          | _ => None
                        end
                      | _ => None
                    end)
               & _); clear_ast_defs; invertible_tac.
    - abstract (destruct_union; local_printable_tac).
    - abstract 
        (destruct w as [b [op1 op2]]; destruct op2; destruct op1; destruct b;
         ins_pf_sim; parsable_tac).
  Defined.

  Definition UD2_p := "0000" $$ "1111" $$ "0000" $$ ! "1011".
  Definition VERR_p := 
    "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "100".
  Definition VERW_p := 
    "0000" $$ "1111" $$ "0000" $$ "0000" $$ ext_op_modrm "101".
  Definition WBINVD_p := "0000" $$ "1111" $$ "0000" $$ ! "1001".
  Definition WRMSR_p := "0000" $$ "1111" $$ "0011" $$ ! "0000".

  Definition XADD_p : 
    wf_bigrammar (pair_t bool_t (pair_t operand_t operand_t)).
    refine("0000" $$ "1111" $$ "1100" $$ "000" $$ anybit $ modrm
            @ (fun v => 
                 match v with | (w,(op1,op2)) => (w, (op2, op1))
                 end %% pair_t bool_t (pair_t operand_t operand_t))
            & (fun u =>
                 match u with | (w,(op2,op1)) => Some (w, (op1, op2))
                 end)
            & _); invertible_tac.
    destruct w as [b [op2 op1]]; parsable_tac.
  Defined.

  Definition XCHG_p : 
    wf_bigrammar (pair_t bool_t (pair_t operand_t operand_t)).
    refine (("1000" $$ "011" $$ anybit $ modrm_ret_reg |+|
             "1001" $$ "0" $$ reg)
              @ (fun v => 
                   match v with
                     | inl (w,(r1,op2)) => (w, (op2, Reg_op r1))
                     | inr r1 => (false, (Reg_op EAX, Reg_op r1))
                   end %% pair_t bool_t (pair_t operand_t operand_t))
              & (fun u:[|pair_t bool_t (pair_t operand_t operand_t)|] => 
                   let (w,u1):=u in
                   let (op2,op1):=u1 in
                   match op2 with
                     | Reg_op r2 =>
                       match op1 with
                         | Reg_op r1 =>
                           if (register_eq_dec r2 EAX) then
                             if w then Some (inl (w,(r1,op2)))
                             else Some (inr r1)
                           else Some (inl (w,(r1,op2)))
                         | _ => None
                       end
                     | Address_op addr =>
                       match op1 with
                         | Reg_op r1 => Some (inl (w,(r1,op2)))
                         | _ => None
                       end
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union.  
      + destruct v as [w [r1 op2]]; ins_pf_sim; bg_pf_sim;
        destruct w; printable_tac; ibr_prover.
      + local_printable_tac.
    - destruct w as [w [op1 op2]]; destruct op1; try parsable_tac;
      destruct op2; try parsable_tac; ins_pf_sim; destruct w; parsable_tac.
  Defined.

  Definition XLAT_p := "1101" $$ ! "0111".


  (** ** Defs used in grammars for floating-point instructions *)
  Definition fpu_reg_op_p : wf_bigrammar fp_operand_t.
    refine (fpu_reg @ (fun v => FPS_op v %% fp_operand_t)
                    & (fun u => match u with | FPS_op v => Some v | _ => None end)
                    & _); invertible_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition ext_op_modrm_FPM32_noreg (bs:string) : wf_bigrammar fp_operand_t.
    intros.
    refine ((ext_op_modrm_noreg_ret_addr bs)
              @ (fun v => FPM32_op v %% fp_operand_t)
              & (fun u => match u with | FPM32_op v => Some v | _ => None end)
                    & _); invertible_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition ext_op_modrm_FPM64_noreg (bs:string) : wf_bigrammar fp_operand_t.
    intros.
    refine ((ext_op_modrm_noreg_ret_addr bs)
              @ (fun v => FPM64_op v %% fp_operand_t)
              & (fun u => match u with | FPM64_op v => Some v | _ => None end)
                    & _); invertible_tac.
    - destruct w; parsable_tac.
  Defined.
  
  Definition fp_condition_type_to_Z (ct: fp_condition_type) : Z :=
    (match ct with
      | B_fct => 0
      | E_fct => 1
      | BE_fct => 2
      | U_fct => 3
      | NB_fct => 4
      | NE_fct => 5
      | NBE_fct => 6
      | NU_fct => 7
     end)%Z.

  Lemma fp_condition_type_to_Z_inv z:
    (0 <= z < 8)%Z -> 
    fp_condition_type_to_Z (Z_to_fp_condition_type z) = z.
  Proof. intros.
    remember (Z_to_fp_condition_type z) as ct;
    destruct ct; unfold Z_to_fp_condition_type in *;
    toztac;
    simpl in *; pos_to_Z; omega.
  Qed.

  Lemma Z_to_fp_condition_type_inv ct :
    Z_to_fp_condition_type (fp_condition_type_to_Z ct) = ct.
  Proof. destruct ct; crush. Qed.

  Hint Rewrite fp_condition_type_to_Z_inv
       using (apply int_of_bitsn_range): inv_db.
  Hint Rewrite Z_to_fp_condition_type_inv: inv_db.

  Ltac fp_invertible_tac :=
    unfold invertible; split; [unfold printable | unfold parsable];
    compute [snd fst]; intros;
    [destruct_union; local_printable_tac | 
     match goal with
       | [w:[|fp_operand_t|] |- _] => destruct w; parsable_tac
     end].

  (** ** Grammars for floating-point instructions, based on tables B.17 and B-39*)
  Definition F2XM1_p := "11011" $$ "001111" $$ ! "10000".
  Definition FABS_p :=  "11011" $$ "001111" $$ ! "00001".

  Definition fp_arith_env (bs0 bs1: string) :
    AST_Env (pair_t bool_t fp_operand_t) :=
    {0, "11011" $$ "000" $$ ext_op_modrm_noreg_ret_addr bs0,
     (fun addr => (true, FPM32_op addr) %% pair_t bool_t fp_operand_t)} :::
    {1, "11011" $$ "100" $$ ext_op_modrm_noreg_ret_addr bs0,
     (fun addr => (true, FPM64_op addr) %% pair_t bool_t fp_operand_t)} :::
    {2, "11011" $$ "0" $$ "0011" $$ bs0 $$ fpu_reg,
     (fun fr => (true, FPS_op fr) %% pair_t bool_t fp_operand_t)} :::
    {3, "11011" $$ "1" $$ "0011" $$ bs1 $$ fpu_reg,
     (fun fr => (false, FPS_op fr) %% pair_t bool_t fp_operand_t)} :::
    ast_env_nil.

  Definition fp_arith_p (bs0 bs1: string) : 
    wf_bigrammar (pair_t bool_t fp_operand_t).
    intros; gen_ast_defs (fp_arith_env bs0 bs1).
    refine (gr @ (mp: _ -> [|pair_t bool_t fp_operand_t|])
              & (fun u =>
                   match u with
                     | (true, FPM32_op addr) => case0 addr
                     | (true, FPM64_op addr) => case1 addr
                     | (true, FPS_op fr) => case2 fr
                     | (false, FPS_op fr) => case3 fr
                     | _ => None
                   end)
              & _); clear_ast_defs; invertible_tac.
    - destruct_union; try local_printable_tac.
    - destruct w as [d op]; destruct d; destruct op; parsable_tac.
  Defined.

  Definition FADD_p := fp_arith_p "000" "000".

  (* Possible todos: FADDP allows a fpu reg as an operand; can change the
     syntax of FADDP to take a fpureg as the argument, instead of
     fpu_operand; the same applies to many FPU instructions *)
  Definition FADDP_p := "11011" $$ "110" $$ "11000" $$ fpu_reg_op_p.

  Definition FBLD_p := "11011" $$ "111" $$ ext_op_modrm_FPM64_noreg "100".
  Definition FBSTP_p := "11011" $$ "111" $$ ext_op_modrm_FPM64_noreg "110".
  Definition FCHS_p := "11011" $$ "001111" $$ ! "00000".

  Definition FCMOVcc_p : 
    wf_bigrammar (pair_t fp_condition_t fp_operand_t).
    refine (("11011" $$ "01" $$ anybit $ "110" $$ anybit $ anybit $ fpu_reg_op_p)
              @ (fun v => 
                   match v with 
                       (b2, (b1, (b0, op))) => 
                       let n := int_of_bitsn 3 (b2, (b1, (b0, tt))) in
                       (Z_to_fp_condition_type n, op)
                   end %% pair_t fp_condition_t fp_operand_t)
              & (fun u:[|pair_t fp_condition_t fp_operand_t|] =>
                   let (ct,op) := u in
                   let bs :=
                       bitsn_of_int 3 (fp_condition_type_to_Z ct)
                   in
                   match bs with
                     | Some (b2,(b1,(b0,()))) => Some (b2,(b1,(b0,op)))
                     | None => None (* impossible case *)
                   end)
              & _); invertible_tac.
    - destruct w as [ct op].
      remember_rev (bitsn_of_int 3 (fp_condition_type_to_Z ct)) as u.
      destruct u as [[b2 [b1 [b0 b]]] | ]; try parsable_tac.
      destruct b. sim.
      erewrite int_of_bitsn_inv by eassumption.
      autorewrite with inv_db. trivial.
  Defined.

  Definition FCOM_p: wf_bigrammar fp_operand_t.
    refine (("11011" $$ "000" $$ ext_op_modrm_noreg_ret_addr "010" |+|
             "11011" $$ "100" $$ ext_op_modrm_noreg_ret_addr "010" |+|
             "11011" $$ "000" $$ "11010" $$ fpu_reg) 
              @ (fun v => 
                   match v with
                     | inl addr => FPM32_op addr
                     | inr (inl addr) => FPM64_op addr
                     | inr (inr fr) => FPS_op fr
                   end %% fp_operand_t)
              & (fun u => 
                   match u with
                     | FPS_op fr => Some (inr (inr fr))
                     | FPM32_op addr => Some (inl addr)
                     | FPM64_op addr => Some (inr (inl addr))
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  Definition FCOMP_p : wf_bigrammar fp_operand_t.
    refine (("11011" $$ "000" $$ ext_op_modrm_noreg_ret_addr "011" |+|
             "11011" $$ "100" $$ ext_op_modrm_noreg_ret_addr "011" |+|
             "11011" $$ "000" $$ "11011" $$ fpu_reg)
              @ (fun v => 
                   match v with
                     | inl addr => FPM32_op addr
                     | inr (inl addr) => FPM64_op addr
                     | inr (inr fr) => FPS_op fr
                   end %% fp_operand_t)
              & (fun u => 
                   match u with
                     | FPS_op fr => Some (inr (inr fr))
                     | FPM32_op addr => Some (inl addr)
                     | FPM64_op addr => Some (inr (inl addr))
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  Definition FCOMPP_p := "11011" $$ "110" $$ "11011" $$ ! "001".
  Definition FCOMIP_p := "11011" $$ "111" $$ "11110" $$ fpu_reg_op_p. 
  Definition FCOS_p := "11011" $$ "001" $$ "111" $$ ! "11111".
  Definition FDECSTP_p := "11011" $$ "001" $$ "111" $$ ! "10110".

  Definition FDIV_p := fp_arith_p "110" "111".
  Definition FDIVP_p := "11011" $$ "110" $$ "11111" $$ fpu_reg_op_p.
  Definition FDIVR_p := fp_arith_p "111" "110".
  Definition FDIVRP_p := "11011" $$ "110" $$ "11110" $$ fpu_reg_op_p.
  Definition FFREE_p := "11011" $$ "101" $$ "11000" $$ fpu_reg_op_p.

  (* floating-point arith involving an integer as one of the operands *)
  Definition fp_iarith_p (bs: string) : wf_bigrammar fp_operand_t.
    intros.
    refine (("11011" $$ "110" $$ ext_op_modrm_noreg_ret_addr bs |+|
             "11011" $$ "010" $$ ext_op_modrm_noreg_ret_addr bs)
              @ (fun v => 
                   match v with
                     | inl addr => FPM16_op addr
                     | inr addr => FPM32_op addr
                   end %% fp_operand_t)
              & (fun u =>
                   match u with
                     | FPM16_op addr => Some (inl addr)
                     | FPM32_op addr => Some (inr addr)
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  Definition FIADD_p := fp_iarith_p "000".
  Definition FICOM_p  := fp_iarith_p "010".
  Definition FICOMP_p  := fp_iarith_p "011".
  Definition FIDIV_p  := fp_iarith_p "110".
  Definition FIDIVR_p  := fp_iarith_p "111".

  Definition FILD_p : wf_bigrammar fp_operand_t.
    refine (("11011" $$ "111" $$ ext_op_modrm_noreg_ret_addr "000" |+|
             "11011" $$ "011" $$ ext_op_modrm_noreg_ret_addr "000" |+|
             "11011" $$ "111" $$ ext_op_modrm_noreg_ret_addr "101")
              @ (fun v =>
                   match v with
                     | inl addr => FPM16_op addr
                     | inr (inl addr) => FPM32_op addr
                     | inr (inr addr) => FPM64_op addr
                   end %% fp_operand_t)
              & (fun u => 
                   match u with
                     | FPM16_op addr => Some (inl addr)
                     | FPM32_op addr => Some (inr (inl addr))
                     | FPM64_op addr => Some (inr (inr addr))
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  Definition FIMUL_p := fp_iarith_p "001".
  Definition FINCSTP_p := "11011" $$ "001111" $$ ! "10111".

  Definition FIST_p : wf_bigrammar fp_operand_t.
    refine (("11011" $$ "111" $$ ext_op_modrm_noreg_ret_addr "010" |+|
             "11011" $$ "011" $$ ext_op_modrm_noreg_ret_addr "010")
              @ (fun v => 
                   match v with
                     | inl addr => FPM16_op addr
                     | inr addr => FPM32_op addr
                   end %% fp_operand_t)
              & (fun u =>
                   match u with
                     | FPM16_op addr => Some (inl addr)
                     | FPM32_op addr => Some (inr addr)
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  Definition FISTP_p : wf_bigrammar fp_operand_t.
    refine (("11011" $$ "111" $$ ext_op_modrm_noreg_ret_addr "011" |+|
             "11011" $$ "011" $$ ext_op_modrm_noreg_ret_addr "011" |+|
             "11011" $$ "111" $$ ext_op_modrm_noreg_ret_addr "111")
              @ (fun v =>
                   match v with
                     | inl addr => FPM16_op addr
                     | inr (inl addr) => FPM32_op addr
                     | inr (inr addr) => FPM64_op addr
                   end %% fp_operand_t)
              & (fun u => 
                   match u with
                     | FPM16_op addr => Some (inl addr)
                     | FPM32_op addr => Some (inr (inl addr))
                     | FPM64_op addr => Some (inr (inr addr))
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  Definition FISUB_p := fp_iarith_p "100".
  Definition FISUBR_p := fp_iarith_p "101".

  Definition FLD_env : AST_Env fp_operand_t :=
    {0, "11011" $$ "001" $$ ext_op_modrm_noreg_ret_addr "000",
     (fun addr => FPM32_op addr %% fp_operand_t)} :::
    {1, "11011" $$ "101" $$ ext_op_modrm_noreg_ret_addr "000",
     (fun addr => FPM64_op addr %% fp_operand_t)} :::
    {2, "11011" $$ "011" $$ ext_op_modrm_noreg_ret_addr "101",
     (fun addr => FPM80_op addr %% fp_operand_t)} :::
    {3, "11011" $$ "001" $$ "11000" $$ fpu_reg,
     (fun fr => FPS_op fr %% fp_operand_t)} :::
    ast_env_nil.

  Definition FLD_p: wf_bigrammar fp_operand_t.
    gen_ast_defs FLD_env.
    refine (gr @ (mp:_ -> [|fp_operand_t|])
               & (fun u =>
                    match u with
                      | FPM32_op addr => case0 addr
                      | FPM64_op addr => case1 addr
                      | FPM80_op addr => case2 addr
                      | FPS_op fr => case3 fr
                      | _ => None
                    end)
               & _); clear_ast_defs; fp_invertible_tac.
  Defined.

  Definition FLD1_p := "11011" $$ "001111" $$ ! "01000".
  Definition FLDCW_p := "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "101".

  Definition FLDENV_p := "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "100". 
  Definition FLDL2E_p := "11011" $$ "001111" $$ ! "01010".
  Definition FLDL2T_p := "11011" $$ "001111" $$ ! "01001".
  Definition FLDLG2_p := "11011" $$ "001111" $$ ! "01100".
  Definition FLDLN2_p := "11011" $$ "001111" $$ ! "01101". 
  Definition FLDPI_p := "11011" $$ "001111" $$ ! "01011".
  Definition FLDZ_p := "11011" $$ "001111" $$ ! "01110".

  Definition FMUL_p := fp_arith_p "001" "001".

  Definition FMULP_p := "11011" $$ "110" $$ "11001" $$ fpu_reg_op_p. 
  Definition FNCLEX_p := "11011" $$ "011111" $$ ! "00010".
  Definition FNINIT_p := "11011" $$ "011111" $$ ! "00011".
  Definition FNOP_p := "11011" $$ "001110" $$ ! "10000".
  Definition FNSAVE_p := "11011101" $$ ext_op_modrm_FPM64_noreg "110".
  Definition FNSTCW_p := "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "111".

  Definition FNSTSW_p : wf_bigrammar (option_t Fp_Operand_t).
    refine (("11011" $$ "111" $$ "111" $$ ! "00000" |+|
             "11011" $$ "101" $$ ext_op_modrm_FPM32_noreg "111")
              @ (fun v =>
                   match v with
                     | inl () => None
                     | inr op => Some op
                   end %% option_t Fp_Operand_t)
              & (fun u:[|option_t Fp_Operand_t|] =>
                   match u with
                     | Some op => Some (inr op)
                     | None => Some (inl ())
                   end)
              & _); invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition FPATAN_p := "11011" $$ "001111" $$ ! "10011".
  Definition FPREM_p := "11011" $$ "001111" $$ ! "11000".
  Definition FPREM1_p := "11011" $$ "001111" $$ ! "10101".
  Definition FPTAN_p := "11011" $$ "001111" $$ ! "10010".
  Definition FRNDINT_p := "11011" $$ "001111" $$ ! "11100".

  Definition FRSTOR_p := "11011" $$ "101" $$ ext_op_modrm_FPM32_noreg "100".

  Definition FSCALE_p := "11011" $$ "001111" $$ ! "11101".
  Definition FSIN_p := "11011" $$ "001111" $$ ! "11110".
  Definition FSINCOS_p := "11011" $$ "001111" $$ ! "11011".
  Definition FSQRT_p := "11011" $$ "001111" $$ ! "11010".

  Definition FST_p : wf_bigrammar fp_operand_t.
    refine (("11011" $$ "001" $$ ext_op_modrm_noreg_ret_addr "010" |+|
             "11011" $$ "101" $$ ext_op_modrm_noreg_ret_addr "010" |+|
             "11011" $$ "101" $$ "11010" $$ fpu_reg)
              @ (fun v =>
                   match v with
                     | inl addr => FPM32_op addr
                     | inr (inl addr) => FPM64_op addr
                     | inr (inr fr) => FPS_op fr
                   end %% fp_operand_t)
              & (fun u =>
                   match u with
                     | FPS_op fr => Some (inr (inr fr))
                     | FPM32_op addr => Some (inl addr)
                     | FPM64_op addr => Some (inr (inl addr))
                     | _ => None
                   end)
              & _); fp_invertible_tac.
  Defined.

  (* FSTCW's encoding is the same as FWAIT followed by FNSTCW *)
  (* Definition FSTCW_p := "10011011" $$ "11011" $$ "001" $$ ext_op_modrm_FPM32 "111". *)
  Definition FSTENV_p := "11011" $$ "001" $$ ext_op_modrm_FPM32_noreg "110".

  Definition FSTP_env : AST_Env fp_operand_t :=
    {0, "11011" $$ "001" $$ ext_op_modrm_noreg_ret_addr "011",
     (fun addr => FPM32_op addr %% fp_operand_t)} :::
    {1, "11011" $$ "101" $$ ext_op_modrm_noreg_ret_addr "011",
     (fun addr => FPM64_op addr %% fp_operand_t)} :::
    {2, "11011" $$ "011" $$ ext_op_modrm_noreg_ret_addr "111",
     (fun addr => FPM80_op addr %% fp_operand_t)} :::
    {3, "11011" $$ "101" $$ "11011" $$ fpu_reg,
     (fun fr => FPS_op fr %% fp_operand_t)} :::
    ast_env_nil.

  Definition FSTP_p: wf_bigrammar fp_operand_t.
    gen_ast_defs FSTP_env.
    refine (gr @ (mp:_ -> [|fp_operand_t|])
               & (fun u =>
                    match u with
                      | FPM32_op addr => case0 addr
                      | FPM64_op addr => case1 addr
                      | FPM80_op addr => case2 addr
                      | FPS_op fr => case3 fr
                      | _ => None
                    end)
               & _); clear_ast_defs; fp_invertible_tac.
  Defined.

  Definition FSUB_p := fp_arith_p "100" "101".
  Definition FSUBP_p := "11011" $$ "110" $$ "11101" $$ fpu_reg_op_p. 
  Definition FSUBR_p := fp_arith_p "101" "100".

  Definition FSUBRP_p := "11011" $$ "110" $$ "11100" $$ fpu_reg_op_p. 
  Definition FTST_p := "11011" $$ "001111" $$ ! "00100".
  Definition FUCOM_p := "11011" $$ "101" $$ "11100" $$ fpu_reg_op_p. 
  Definition FUCOMP_p := "11011" $$ "101" $$ "11101" $$ fpu_reg_op_p. 
  Definition FUCOMPP_p := "11011" $$ "010111" $$ ! "01001".
  Definition FUCOMI_p := "11011" $$ "011" $$ "11101" $$ fpu_reg_op_p. 
  Definition FUCOMIP_p := "11011" $$ "111" $$ "11101" $$ fpu_reg_op_p.
  Definition FXAM_p := "11011" $$ "001111" $$ ! "00101".
  Definition FXCH_p := "11011" $$ "001" $$ "11001" $$ fpu_reg_op_p.

  Definition FXTRACT_p := "11011" $$ "001" $$ "1111" $$ ! "0100".
  Definition FYL2X_p := "11011" $$ "001111" $$ ! "10001".
  Definition FYL2XP1_p := "11011" $$ "001111" $$ ! "11001".
  Definition FWAIT_p := ! "10011011".

  (** ** Definitions used in bigrammars for MMX instructions *)

  Definition modrm_mmx_noreg : wf_bigrammar (pair_t mmx_register_t address_t) := 
    modrm_gen_noreg mmx_reg.

  Definition modrm_mmx_ret_reg : wf_bigrammar (pair_t mmx_register_t mmx_operand_t).
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

  Definition modrm_mmx : wf_bigrammar (pair_t mmx_operand_t mmx_operand_t).
    refine (modrm_mmx_ret_reg
              @ (fun v => match v with
                            | (r1, op2) => (MMX_Reg_op r1, op2)
                          end %% (pair_t mmx_operand_t mmx_operand_t))
              & (fun u => match u with
                            | (MMX_Reg_op r1, op2) => Some (r1, op2)
                            | _ => None
                          end)
              & _); invertible_tac.
    destruct v; destruct w as [op1 op2]; destruct op1; parsable_tac.
  Defined.

  (* grammar for the mmx granularity bits, allowing 8, 16, 32 bits. *)
  Definition mmx_gg_p_8_16_32 : wf_bigrammar mmx_granularity_t.
    refine ((! "00" |+| ! "01" |+| ! "10")
              @ (fun v => 
                   match v with
                     | inl () => MMX_8
                     | inr (inl ()) => MMX_16
                     | inr (inr ()) => MMX_32
                   end %% mmx_granularity_t)
              & (fun u => 
                   match u with
                     | MMX_8 => Some (inl ())
                     | MMX_16 => Some (inr (inl ()))
                     | MMX_32 => Some (inr (inr ()))
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition mmx_gg_p_8_16 : wf_bigrammar mmx_granularity_t.
    refine ((! "00" |+| ! "01")
              @ (fun v => 
                   match v with
                     | inl () => MMX_8
                     | inr () => MMX_16
                   end %% mmx_granularity_t)
              & (fun u => 
                   match u with
                     | MMX_8 => Some (inl ())
                     | MMX_16 => Some (inr ())
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition mmx_gg_p_16_32_64 : wf_bigrammar mmx_granularity_t.
    refine ((! "01" |+| ! "10" |+| ! "11")
              @ (fun v => 
                   match v with
                     | inl () => MMX_16
                     | inr (inl ()) => MMX_32
                     | inr (inr ()) => MMX_64
                   end %% mmx_granularity_t)
              & (fun u => 
                   match u with
                     | MMX_16 => Some (inl ())
                     | MMX_32 => Some (inr (inl ()))
                     | MMX_64 => Some (inr (inr ()))
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition mmx_gg_p_16_32 : wf_bigrammar mmx_granularity_t.
    refine ((! "01" |+| ! "10")
              @ (fun v => 
                   match v with
                     | inl () => MMX_16
                     | inr () => MMX_32
                   end %% mmx_granularity_t)
              & (fun u => 
                   match u with
                     | MMX_16 => Some (inl ())
                     | MMX_32 => Some (inr ())
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w; parsable_tac.
  Defined.

  Lemma mmx_reg_rng: forall mr, in_bigrammar_rng (` mmx_reg) mr.
  Proof. intros; unfold mmx_reg.  apply field_intn_rng. Qed.
  Hint Resolve mmx_reg_rng: ibr_rng_db.

  Lemma modrm_mmx_ret_reg_rng1 mr1 mr2: 
    in_bigrammar_rng (` modrm_mmx_ret_reg) (mr1, MMX_Reg_op mr2).
  Proof. intros. unfold modrm_mmx_ret_reg, modrm_gen. ibr_prover. compute [fst].
    exists (inr [|pair_t mmx_register_t address_t|] (mr1, mr2)).
    split; [ibr_prover | trivial].
  Qed.
  Hint Resolve modrm_mmx_ret_reg_rng1: ibr_rng_db.

  Lemma modrm_mmx_ret_reg_rng_inv mr op:
    in_bigrammar_rng (` modrm_mmx_ret_reg) (mr,op) -> 
    (exists mr, op = MMX_Reg_op mr) \/ (exists addr, op = MMX_Addr_op addr).
  Proof. unfold modrm_mmx_ret_reg; intros. ibr_prover.
    destruct v as [[r1 addr] | [r1 r2]]; clear H0.
    - right. crush. 
    - left. crush. 
  Qed.

  Lemma modrm_mmx_rng1 mr1 mr2: 
    in_bigrammar_rng (` modrm_mmx) (MMX_Reg_op mr1, MMX_Reg_op mr2).
  Proof. unfold modrm_mmx; intros; ibr_prover. compute [fst].
     exists (mr1, MMX_Reg_op mr2); split; [ibr_prover | trivial].
  Qed.
  Hint Resolve modrm_mmx_rng1: ibr_rng_db.

  Lemma modrm_mmx_rng_inv1 op1 op2: 
    in_bigrammar_rng (` modrm_mmx) (op1,op2) -> exists mr, op1 = MMX_Reg_op mr.
  Proof. unfold modrm_mmx; intros; ibr_prover.
    destruct v as [mr op]. exists mr; congruence.
  Qed.

  Lemma modrm_mmx_rng_inv2 op1 op2: 
    in_bigrammar_rng (` modrm_mmx) (op1,op2) -> 
    (exists mr, op2 = MMX_Reg_op mr) \/ (exists addr, op2 = MMX_Addr_op addr).
  Proof. unfold modrm_mmx; intros; ibr_prover.
    destruct v as [mr op]. eapply modrm_mmx_ret_reg_rng_inv.
    sim; subst. eassumption.
  Qed.

  Local Ltac mmx_pf_sim :=
    ibr_prover; bg_pf_sim;
    repeat match goal with
      | [H: in_bigrammar_rng (` modrm_mmx) (?op1 ?op2) |- _] => 
        let H2 := fresh "H" in
        let H3 := fresh "H" in
        generalize (modrm_mmx_rng_inv1 H) (modrm_mmx_rng_inv2 H); intros H2 H3;
        destruct H2; subst;
        destruct H3 as [H3 | H3]; destruct H3; subst op2
      | [H: in_bigrammar_rng (` modrm_mmx_ret_reg) (?r1 ?op2) |- _] =>
        let H2 := fresh "H" in
        generalize (modrm_mmx_ret_reg_rng_inv H); intro H2;
        destruct H2 as [H2 | H2]; destruct H2; subst op2
    end.

  (** ** Bigrammars for MMX instructions *)

  Definition EMMS_p := "0000" $$ "1111" $$ "0111" $$ ! "0111".

  Definition MOVD_env : AST_Env (pair_t mmx_operand_t mmx_operand_t) :=
    (* gpreg to and from mmxreg *)
    {0, "0000" $$ "1111" $$ "011" $$ anybit $ "1110" $$ "11" $$ mmx_reg $ reg,
    (fun v => let (d,v1):=v in let (mr,r):=v1 in
              (if d then (MMX_Reg_op mr, GP_Reg_op r)
               else (GP_Reg_op r, MMX_Reg_op mr))
              %% pair_t mmx_operand_t mmx_operand_t) } :::
    (* mem to and from mmxreg *)
    {1, "0000" $$ "1111" $$ "011" $$ anybit $ "1110" $$ modrm_mmx_noreg,
     (fun v => let (d,v1):=v in let (mr,addr):=v1 in
               (if d then (MMX_Addr_op addr, MMX_Reg_op mr)
                else (MMX_Reg_op mr, MMX_Addr_op addr))
               %% pair_t mmx_operand_t mmx_operand_t) } :::
    ast_env_nil.

  Definition MOVD_d : wf_bigrammar (pair_t mmx_operand_t mmx_operand_t).
    gen_ast_defs MOVD_env.
    refine (gr @ (mp: _ -> [|pair_t mmx_operand_t mmx_operand_t|])
               & (fun u =>
                    match u with
                      | (MMX_Reg_op mr, GP_Reg_op r) => case0 (true,(mr,r))
                      | (GP_Reg_op r, MMX_Reg_op mr) => case0 (false,(mr,r))
                      | (MMX_Addr_op addr, MMX_Reg_op mr) => case1 (true,(mr,addr))
                      | (MMX_Reg_op mr, MMX_Addr_op addr) => case1 (false,(mr,addr))
                      | _ => None
                    end)
               & _); clear_ast_defs; invertible_tac.
    - destruct_union;
      destruct v as [d [mr r]]; destruct d; printable_tac; ibr_prover.
    - destruct w as [op1 op2]; destruct op1; destruct op2; parsable_tac.
  Defined.

  Definition MOVQ_d : wf_bigrammar (pair_t mmx_operand_t mmx_operand_t).
    refine (("0000" $$ "1111" $$ "011" $$ anybit $ "1111" $$ modrm_mmx)
             @ (fun v: [|pair_t char_t (pair_t mmx_operand_t mmx_operand_t)|] =>
                  let (d,v1):=v in let (op1,op2) :=v1 in
                    (if d then (op2, op1) else (op1, op2))
                      %% pair_t mmx_operand_t mmx_operand_t)
             & (fun u:[|pair_t mmx_operand_t mmx_operand_t|] =>
                  let (op1,op2):=u in
                  match op1 with
                    | MMX_Reg_op _ => 
                      (* alternate encoding: when op2 is also MMX_Reg_op *)
                      Some (false, (op1, op2))
                    | _ =>
                      match op2 with
                        | MMX_Reg_op _ => Some (true, (op2, op1))
                        | _ => None
                      end
                  end)
             & _); invertible_tac.
    - destruct v as [d [op1 op2]]; destruct d;
      mmx_pf_sim; printable_tac; ibr_prover. 
    - destruct w as [op1 op2]; destruct op1; destruct op2; parsable_tac.
  Defined.

  Definition PACKSSDW_p := 
    "0000" $$ "1111" $$ "0110" $$ "1011" $$ modrm_mmx.

  Definition PACKSSWB_p := 
    "0000" $$ "1111" $$ "0110" $$ "0011" $$ modrm_mmx.

  Definition PACKUSWB_p := 
    "0000" $$ "1111" $$ "0110" $$ "0111" $$ modrm_mmx.

  Definition PADD_p := 
    "0000" $$ "1111" $$ "1111" $$ "11" $$ mmx_gg_p_8_16_32 $ modrm_mmx. 

  Definition PADDS_p := 
    "0000" $$ "1111" $$ "1110" $$ "11" $$ mmx_gg_p_8_16 $ modrm_mmx.

  Definition PADDUS_p := 
    "0000" $$ "1111" $$ "1101" $$ "11" $$ mmx_gg_p_8_16 $ modrm_mmx. 

  Definition PAND_p := 
    "0000" $$ "1111" $$ "1101" $$ "1011" $$ modrm_mmx. 

  Definition PANDN_p := 
    "0000" $$ "1111" $$ "1101" $$ "1111" $$ modrm_mmx. 

  Definition PCMPEQ_p :=
    "0000" $$ "1111" $$ "0111" $$ "01" $$ mmx_gg_p_8_16_32 $ modrm_mmx.

  Definition PCMPGT_p := 
    "0000" $$ "1111" $$ "0110" $$ "01" $$ mmx_gg_p_8_16_32 $ modrm_mmx. 

  Definition PMADDWD_p := 
    "0000" $$ "1111" $$ "1111" $$ "0101" $$ modrm_mmx. 

  Definition PMULHUW_p := 
    "0000" $$ "1111" $$ "1110" $$ "0100" $$ modrm_mmx.

  Definition PMULHW_p := 
    "0000" $$ "1111" $$ "1110" $$ "0101" $$ modrm_mmx.

  Definition PMULLW_p := 
    "0000" $$ "1111" $$ "1101" $$ "0101" $$ modrm_mmx.

  Definition POR_p := 
    "0000" $$ "1111" $$ "1110" $$ "1011" $$ modrm_mmx.

  Definition pshift_p (bs:string) (gg_p:wf_bigrammar mmx_granularity_t) :
    wf_bigrammar (pair_t mmx_granularity_t
                         (pair_t mmx_operand_t mmx_operand_t)).
    intros.    
    refine (("0000" $$ "1111" $$ "11" $$ bs $$ "00"
                $$ gg_p $ modrm_mmx_ret_reg |+|
             "0000" $$ "1111" $$ "0111" $$ "00"
                $$ gg_p $ "11" $$ bs $$ "0" $$ mmx_reg $ byte)
              @ (fun v =>
                   match v with
                     | inl (gg,(r1,op2)) => (gg,(MMX_Reg_op r1, op2))
                     | inr (gg,(r1,imm)) => 
                       (gg, (MMX_Reg_op r1, MMX_Imm_op (zero_extend8_32 imm)))
                   end
                   %% pair_t mmx_granularity_t (pair_t mmx_operand_t mmx_operand_t))
              & (fun u: mmx_granularity * (mmx_operand * mmx_operand) => 
                   let (gg,u1):=u in
                   let (op1,op2):=u1 in
                   match op1 with
                     | MMX_Reg_op r1 =>
                       match op2 with
                         | MMX_Reg_op _ | MMX_Addr_op _ => Some (inl(gg,(r1,op2)))
                         | MMX_Imm_op imm => 
                           if (repr_in_unsigned_byte_dec imm) then
                               Some (inr(gg,(r1, zero_shrink32_8 imm)))
                           else None
                         | _ => None
                       end
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union. 
      + destruct v as [gg [r1 op2]]. 
        mmx_pf_sim; printable_tac; ibr_prover.
      + destruct v as [gg [r1 imm]].
        mmx_pf_sim; printable_tac; ibr_prover.
    - destruct w as [gg [op1 op2]]; destruct op1; destruct op2; 
      bg_pf_sim; parsable_tac.
  Defined.

  Definition PSLL_p := pshift_p "11" mmx_gg_p_16_32_64.
  Definition PSRA_p := pshift_p "10" mmx_gg_p_16_32.
  Definition PSRL_p := pshift_p "01" mmx_gg_p_16_32_64.

  Definition PSUB_p := 
    "0000" $$ "1111" $$ "1111" $$ "10" $$ mmx_gg_p_8_16_32 $ modrm_mmx. 

  Definition PSUBS_p := 
    "0000" $$ "1111" $$ "1110" $$ "10" $$ mmx_gg_p_8_16 $ modrm_mmx. 

  Definition PSUBUS_p := 
    "0000" $$ "1111" $$ "1101" $$ "10" $$ mmx_gg_p_8_16 $ modrm_mmx. 

  Definition PUNPCKH_p := 
    "0000" $$ "1111" $$ "0110" $$ "10" $$ mmx_gg_p_8_16_32 $ modrm_mmx. 

  Definition PUNPCKL_p := 
    "0000" $$ "1111" $$ "0110" $$ "00" $$ mmx_gg_p_8_16_32 $ modrm_mmx. 

  Definition PXOR_p := 
    "0000" $$ "1111" $$ "1110" $$ "1111" $$ modrm_mmx. 

  (** ** Bigrammars for SSE instructions *)

  (* mod xmmreg r/m in manual*)
  Definition modrm_xmm_ret_reg : 
    wf_bigrammar (pair_t sse_register_t sse_operand_t).
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

  Definition modrm_xmm : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine (modrm_xmm_ret_reg
              @ (fun v => match v with
                            | (sr1, op2) => (SSE_XMM_Reg_op sr1, op2)
                          end %% (pair_t sse_operand_t sse_operand_t))
              & (fun u => match u with
                            | (SSE_XMM_Reg_op sr1, op2) => Some (sr1, op2)
                            | _ => None
                          end)
              & _); invertible_tac.
    destruct v; destruct w as [op1 op2]; destruct op1; parsable_tac.
  Defined.

  (* mod mmreg r/m (no x) in manual; this uses mmx regs in sse instrs *)
  Definition modrm_mm_ret_reg : wf_bigrammar (pair_t mmx_register_t sse_operand_t).
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

  Definition modrm_mm : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine (modrm_mm_ret_reg
              @ (fun v => match v with
                            | (mr1, op2) => (SSE_MM_Reg_op mr1, op2)
                          end %% (pair_t sse_operand_t sse_operand_t))
              & (fun u => match u with
                            | (SSE_MM_Reg_op mr1, op2) => Some (mr1, op2)
                            | _ => None
                          end)
              & _); invertible_tac.
    destruct v; destruct w as [op1 op2]; destruct op1; parsable_tac.
  Defined.

  Notation modrm_xmm_noreg := modrm_bv2_noreg.
  Notation modrm_mm_noreg := modrm_bv2_noreg.

  Lemma modrm_xmm_ret_reg_rng1 sr1 sr2: 
    in_bigrammar_rng (` modrm_xmm_ret_reg) (sr1, SSE_XMM_Reg_op sr2).
  Proof. intros. unfold modrm_xmm_ret_reg, modrm_gen. ibr_prover. compute [fst].
    exists (inr [|pair_t sse_register_t address_t|] (sr1, sr2)).
    split; [ibr_prover | trivial].
  Qed.
  Hint Resolve modrm_xmm_ret_reg_rng1: ibr_rng_db.

  Lemma modrm_xmm_ret_reg_rng_inv sr op:
    in_bigrammar_rng (` modrm_xmm_ret_reg) (sr,op) -> 
    (exists sr, op = SSE_XMM_Reg_op sr) \/ (exists addr, op = SSE_Addr_op addr).
  Proof. unfold modrm_xmm_ret_reg; intros. ibr_prover.
    destruct v as [[r1 addr] | [r1 r2]]; clear H0.
    - right. crush. 
    - left. crush. 
  Qed.

  Lemma modrm_xmm_rng1 sr1 sr2: 
    in_bigrammar_rng (` modrm_xmm) (SSE_XMM_Reg_op sr1, SSE_XMM_Reg_op sr2).
  Proof. unfold modrm_xmm; intros; ibr_prover. compute [fst].
     exists (sr1, SSE_XMM_Reg_op sr2); split; [ibr_prover | trivial].
  Qed.
  Hint Resolve modrm_xmm_rng1: ibr_rng_db.

  Lemma modrm_xmm_rng_inv1 op1 op2: 
    in_bigrammar_rng (` modrm_xmm) (op1,op2) -> 
    exists sr, op1 = SSE_XMM_Reg_op sr.
  Proof. unfold modrm_xmm; intros; ibr_prover.
    destruct v as [sr op]. exists sr; congruence.
  Qed.

  Lemma modrm_xmm_rng_inv2 op1 op2: 
    in_bigrammar_rng (` modrm_xmm) (op1,op2) -> 
    (exists sr, op2 = SSE_XMM_Reg_op sr) \/ (exists addr, op2 = SSE_Addr_op addr).
  Proof. unfold modrm_xmm; intros; ibr_prover.
    destruct v as [sr op]. eapply modrm_xmm_ret_reg_rng_inv.
    sim; subst. eassumption.
  Qed.

  Lemma modrm_mm_ret_reg_rng1 mr1 mr2: 
    in_bigrammar_rng (` modrm_mm_ret_reg) (mr1, SSE_MM_Reg_op mr2).
  Proof. intros. unfold modrm_mm_ret_reg, modrm_gen. ibr_prover. compute [fst].
    exists (inr [|pair_t sse_register_t address_t|] (mr1, mr2)).
    split; [ibr_prover | trivial].
  Qed.
  Hint Resolve modrm_mm_ret_reg_rng1: ibr_rng_db.

  Lemma modrm_mm_ret_reg_rng_inv mr op:
    in_bigrammar_rng (` modrm_mm_ret_reg) (mr,op) -> 
    (exists mr, op = SSE_MM_Reg_op mr) \/ (exists addr, op = SSE_Addr_op addr).
  Proof. unfold modrm_mm_ret_reg; intros. ibr_prover.
    destruct v as [[r1 addr] | [r1 r2]]; clear H0.
    - right. crush. 
    - left. crush. 
  Qed.

  Lemma modrm_mm_rng1 mr1 mr2: 
    in_bigrammar_rng (` modrm_mm) (SSE_MM_Reg_op mr1, SSE_MM_Reg_op mr2).
  Proof. unfold modrm_mm; intros; ibr_prover. compute [fst].
     exists (mr1, SSE_MM_Reg_op mr2); split; [ibr_prover | trivial].
  Qed.
  Hint Resolve modrm_mm_rng1: ibr_rng_db.

  Lemma modrm_mm_rng_inv1 op1 op2: 
    in_bigrammar_rng (` modrm_mm) (op1,op2) -> 
    exists mr, op1 = SSE_MM_Reg_op mr.
  Proof. unfold modrm_mm; intros; ibr_prover.
    destruct v as [mr op]. exists mr; congruence.
  Qed.

  Lemma modrm_mm_rng_inv2 op1 op2: 
    in_bigrammar_rng (` modrm_mm) (op1,op2) -> 
    (exists mr, op2 = SSE_MM_Reg_op mr) \/ (exists addr, op2 = SSE_Addr_op addr).
  Proof. unfold modrm_mm; intros; ibr_prover.
    destruct v as [mr op]. eapply modrm_mm_ret_reg_rng_inv.
    sim; subst. eassumption.
  Qed.

  Definition modrm_xmm_byte :
    wf_bigrammar (pair_t sse_operand_t (pair_t sse_operand_t byte_t)). 
    refine ((modrm_xmm $ byte)
              @ (fun v => 
                   match v with 
                     | ((op1, op2), b) => (op1,(op2,b))
                   end %% pair_t sse_operand_t (pair_t sse_operand_t byte_t))
              & (fun u:sse_operand*(sse_operand*int8) => 
                   let (op1,u1):=u in
                   let (op2,b):=u1 in
                   Some ((op1,op2),b))
              & _); invertible_tac.
    - destruct w as [op1 [op2 b]]; parsable_tac.
  Defined.

  Definition ext_op_modrm_sse_noreg (bs: string): wf_bigrammar sse_operand_t.
    intros;
    refine(ext_op_modrm_noreg_ret_addr bs
             @ (SSE_Addr_op: [|address_t|] -> [|sse_operand_t|])
             & SSE_Addr_op_inv & _); unfold SSE_Addr_op_inv; invertible_tac.
    - destruct w; parsable_tac.
  Defined.

  Local Ltac sse_pf_sim :=
    ibr_prover; bg_pf_sim;
    repeat match goal with
      | [H: in_bigrammar_rng (` modrm_xmm) (?op1 ?op2) |- _] => 
        let H2 := fresh "H" in
        let H3 := fresh "H" in
        generalize (modrm_xmm_rng_inv1 H) (modrm_xmm_rng_inv2 H); intros H2 H3;
        destruct H2; subst;
        destruct H3 as [H3 | H3]; destruct H3; subst op2
      | [H: in_bigrammar_rng (` modrm_xmm_ret_reg) (?r1 ?op2) |- _] =>
        let H2 := fresh "H" in
        generalize (modrm_xmm_ret_reg_rng_inv H); intro H2;
        destruct H2 as [H2 | H2]; destruct H2; subst op2
      | [H: in_bigrammar_rng (` modrm_mm) (?op1 ?op2) |- _] => 
        let H2 := fresh "H" in
        let H3 := fresh "H" in
        generalize (modrm_mm_rng_inv1 H) (modrm_mm_rng_inv2 H); intros H2 H3;
        destruct H2; subst;
        destruct H3 as [H3 | H3]; destruct H3; subst op2
      | [H: in_bigrammar_rng (` modrm_mm_ret_reg) (?r1 ?op2) |- _] =>
        let H2 := fresh "H" in
        generalize (modrm_mm_ret_reg_rng_inv H); intro H2;
        destruct H2 as [H2 | H2]; destruct H2; subst op2
    end.


  Definition ADDPS_p := 
    "0000" $$ "1111" $$ "0101" $$ "1000" $$ modrm_xmm. 

  Definition ADDSS_p := 
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1000" $$ modrm_xmm. 

  Definition ANDNPS_p := 
    "0000" $$ "1111" $$ "0101" $$ "0101" $$ modrm_xmm. 

  Definition ANDPS_p := 
    "0000" $$ "1111" $$ "0101" $$ "0100" $$ modrm_xmm. 

  Definition CMPPS_p := 
    "0000" $$ "1111" $$ "1100" $$ "0010" $$ modrm_xmm_byte.

  Definition CMPSS_p := 
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "1100" $$ "0010" $$ modrm_xmm_byte.

  Definition COMISS_p :=
    "0000" $$ "1111" $$ "0010" $$ "1111" $$ modrm_xmm. 

  Definition CVTPI2PS_p :=
    "0000" $$ "1111" $$ "0010" $$ "1010" $$ modrm_xmm.

  Definition CVTPS2PI_p : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine (("0000" $$ "1111" $$ "0010" $$ "1101" $$ "11" $$ sse_reg $ mmx_reg |+|
             "0000" $$ "1111" $$ "0010" $$ "1101" $$ modrm_xmm_noreg)
              @ (fun v => 
                   match v with
                     | inl (sr,mr) => (SSE_XMM_Reg_op sr, SSE_MM_Reg_op mr)
                     | inr (sr,addr) => (SSE_XMM_Reg_op sr, SSE_Addr_op addr)
                   end %% pair_t sse_operand_t sse_operand_t)
              & (fun u:sse_operand*sse_operand=> 
                   let (op1,op2):=u in
                   match op1 with
                     | SSE_XMM_Reg_op sr =>
                       match op2 with
                         | SSE_MM_Reg_op mr => Some (inl(sr,mr))
                         | SSE_Addr_op addr => Some (inr(sr,addr))
                         | _ => None
                       end
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w as [op1 op2]; destruct op1; destruct op2; parsable_tac.
  Defined.

  Definition CVTSI2SS_p : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine(("1111" $$ "0011" $$ "0000" $$ "1111" $$ "0010"
                   $$ "1010" $$ "11" $$ sse_reg $ reg |+|
            "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0010"
                   $$ "1010" $$ modrm_xmm_noreg)
             @ (fun v =>
                  match v with
                    | inl (sr,r) => (SSE_XMM_Reg_op sr, SSE_GP_Reg_op r)
                    | inr (sr,addr) => (SSE_XMM_Reg_op sr, SSE_Addr_op addr)
                  end %% pair_t sse_operand_t sse_operand_t)
             & (fun u:sse_operand*sse_operand=> 
                   let (op1,op2):=u in
                   match op1 with
                     | SSE_XMM_Reg_op sr =>
                       match op2 with
                         | SSE_GP_Reg_op r => Some (inl(sr,r))
                         | SSE_Addr_op addr => Some (inr(sr,addr))
                         | _ => None
                       end
                     | _ => None
                   end)
             & _); invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w as [op1 op2]; destruct op1; destruct op2; parsable_tac.
  Defined.

  Definition ss2si_p (bs:string) :
    wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    intros.
    refine (("1111" $$ "0011" $$ "0000" $$ "1111"
                    $$ "0010" $$ bs $$ "11" $$ reg $ sse_reg |+|
             "1111" $$ "0011" $$ "0000" $$ "1111"
                    $$ "0010" $$ bs $$ modrm_noreg)
              @ (fun v =>
                  match v with
                    | inl (r,sr) => (SSE_GP_Reg_op r, SSE_XMM_Reg_op sr)
                    | inr (r,addr) => (SSE_GP_Reg_op r, SSE_Addr_op addr)
                  end %% pair_t sse_operand_t sse_operand_t)
             & (fun u:sse_operand*sse_operand=> 
                   let (op1,op2):=u in
                   match op1 with
                     | SSE_GP_Reg_op r =>
                       match op2 with
                         | SSE_XMM_Reg_op sr => Some (inl(r,sr))
                         | SSE_Addr_op addr => Some (inr(r,addr))
                         | _ => None
                       end
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w as [op1 op2]; destruct op1; destruct op2; parsable_tac.
  Defined.

  Definition CVTSS2SI_p := ss2si_p "1101".

  Definition CVTTPS2PI_p :=
    "0000" $$ "1111" $$ "0010" $$ "1100" $$ modrm_xmm. 

  Definition CVTTSS2SI_p := ss2si_p "1100".

  Definition DIVPS_p := 
    "0000" $$ "1111" $$ "0101" $$ "1110" $$ modrm_xmm.

  Definition DIVSS_p :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1110" $$ modrm_xmm. 

  Definition LDMXCSR_p := 
    "0000" $$ "1111" $$ "1010" $$ "1110" $$ ext_op_modrm_sse_noreg "010". 

  Definition MAXPS_p := 
    "0000" $$ "1111" $$ "0101" $$ "1111" $$ modrm_xmm. 

  Definition MAXSS_p := 
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1111" $$ modrm_xmm. 

  Definition MINPS_p := 
    "0000" $$ "1111" $$ "0101" $$ "1101" $$ modrm_xmm. 

  Definition MINSS_p :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1101" $$ modrm_xmm. 

  Definition sse_mov_p (bs:string) : 
    wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    intros.
    refine(bs $$ anybit $ modrm_xmm
             @ (fun v: bool*(sse_operand*sse_operand) =>
                  match v with
                    | (d,(op1,op2)) => 
                      if d then (op2,op1) else (op1,op2)
                  end %% pair_t sse_operand_t sse_operand_t)
             & (fun u => 
                  match u with
                    | (SSE_XMM_Reg_op _, SSE_XMM_Reg_op _)
                    | (SSE_XMM_Reg_op _, SSE_Addr_op _) =>
                      (* alternate encoding when both are regs: 
                         reverse the operands and made d true *)
                      Some (false,u)
                    | (SSE_Addr_op _, SSE_XMM_Reg_op _) =>
                      Some (true, (snd u, fst u))
                    | _ => None
                  end)
             & _); invertible_tac.
    - destruct v as [d [op1 op2]]; 
      destruct d; sse_pf_sim; printable_tac; ibr_prover.
    - destruct w as [op1 op2]; destruct op1; destruct op2; parsable_tac.
  Defined.

  Definition MOVAPS_p := sse_mov_p "000011110010100".

  Definition MOVHLPS_p :=
    "0000" $$ "1111" $$ "0001" $$ "0010" $$ "11"
           $$ SSE_XMM_Reg_op_p $ SSE_XMM_Reg_op_p.

  Definition sse_mov_ps_p (bs:string) : 
    wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    intros.
    refine ("0000" $$ "1111" $$ "0001" $$ bs $$ anybit $ modrm_xmm_noreg
              @ (fun v:bool*_ =>
                   match v with
                     | (d,(sr,addr)) =>
                       if d then (SSE_Addr_op addr, SSE_XMM_Reg_op sr)
                       else (SSE_XMM_Reg_op sr, SSE_Addr_op addr)
                   end %% pair_t sse_operand_t sse_operand_t)
              & (fun u => 
                   match u with
                     | (SSE_XMM_Reg_op sr, SSE_Addr_op addr) =>
                       Some (false,(sr,addr))
                     | (SSE_Addr_op addr, SSE_XMM_Reg_op sr) =>
                       Some (true,(sr,addr))
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct v as [d [op1 op2]]; 
      destruct d; sse_pf_sim; printable_tac; ibr_prover.
    - destruct w as [op1 op2]; destruct op1; destruct op2; parsable_tac.
  Defined.

  Definition MOVHPS_p := sse_mov_ps_p "011".

  Definition MOVLHPS_p :=
    "0000" $$ "1111" $$ "0001" $$ "0110" $$ "11"
           $$ SSE_XMM_Reg_op_p $ SSE_XMM_Reg_op_p.

  Definition MOVLPS_p := sse_mov_ps_p "001".

  Definition MOVMSKPS_p :=
    "0000" $$ "1111" $$ "0001" $$ "0110" $$ "11"
           $$ SSE_GP_Reg_op_p $ SSE_XMM_Reg_op_p.
  
  Definition MOVSS_p := sse_mov_p "11110011000011110001000".
  Definition MOVUPS_p := sse_mov_p "000011110001000".

  Definition MULPS_p :=
    "0000" $$ "1111" $$ "0101" $$ "1001" $$ modrm_xmm. 

  Definition MULSS_p :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1001" $$ modrm_xmm.

  Definition ORPS_p :=
    "0000" $$ "1111" $$ "0101" $$ "0110" $$ modrm_xmm.

  Definition RCPPS_p :=
    "0000" $$ "1111" $$ "0101" $$ "0011" $$ modrm_xmm. 

  Definition RCPSS_p :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "0011" $$ modrm_xmm.

  Definition RSQRTPS_p :=
    "0000" $$ "1111" $$ "0101" $$ "0010" $$ modrm_xmm.

  Definition RSQRTSS_p :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "0010" $$ modrm_xmm.

  Definition SHUFPS_p :=
    "0000" $$ "1111" $$ "1100" $$ "0110" $$ modrm_xmm_byte.

  Definition SQRTPS_p :=
    "0000" $$ "1111" $$ "0101" $$ "0001" $$ modrm_xmm.

  Definition SQRTSS_p :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "0001" $$ modrm_xmm.

  Definition STMXCSR_p := 
    "0000" $$ "1111" $$ "1010" $$ "1110" $$ ext_op_modrm_sse_noreg "011".

  Definition SUBPS_p :=
    "0000" $$ "1111" $$ "0101" $$ "1100" $$ modrm_xmm.

  Definition SUBSS_p :=
    "1111" $$ "0011" $$ "0000" $$ "1111" $$ "0101" $$ "1100" $$ modrm_xmm.

  Definition UCOMISS_p :=
    "0000" $$ "1111" $$ "0010" $$ "1110" $$ modrm_xmm.

  Definition UNPCKHPS_p :=
    "0000" $$ "1111" $$ "0001" $$ "0101" $$ modrm_xmm.

  Definition UNPCKLPS_p :=
    "0000" $$ "1111" $$ "0001" $$ "0100" $$ modrm_xmm.

  Definition XORPS_p :=
    "0000" $$ "1111" $$ "0101" $$ "0111" $$ modrm_xmm.

  (* possible todo: this needs to take operand-override prefix into account *)
  Definition PAVGB_p : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine (("0000" $$ "1111" $$ "1110" $$ "0000" $$ modrm_mm_ret_reg |+|
             "0000" $$ "1111" $$ "1110" $$ "0011" $$ modrm_mm_ret_reg)
              @ (fun v =>
                   match v with
                     | inl (mr1,op2) => (SSE_MM_Reg_op mr1,op2)
                     | inr (mr1,op2) => (op2,SSE_MM_Reg_op mr1)
                   end %% pair_t sse_operand_t sse_operand_t)
              & (fun u => 
                   match u with
                     | (SSE_MM_Reg_op mr1, SSE_MM_Reg_op _)
                     | (SSE_MM_Reg_op mr1, SSE_Addr_op _) =>
                       (* alternate encoding when two regs: swap the operands *)
                       Some (inl (mr1, snd u))
                     | (SSE_Addr_op addr, SSE_MM_Reg_op mr1) =>
                       Some (inr (mr1, fst u))
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union; destruct v as [mr1 op2];
      sse_pf_sim; printable_tac; ibr_prover.
    - destruct w as [op1 op2]; destruct op1; destruct op2; parsable_tac.
  Defined.

  Definition PEXTRW_p :=
    "0000" $$ "1111" $$ "1100" $$ "0101" $$ "11"
           $$ SSE_GP_Reg_op_p $ SSE_MM_Reg_op_p $ byte.

  Definition PINSRW_p : 
    wf_bigrammar (pair_t sse_operand_t (pair_t sse_operand_t byte_t)).
    refine (("0000" $$ "1111" $$ "1100" $$ "0100" $$ "11"
                    $$ mmx_reg $ reg $ byte |+|
             "0000" $$ "1111" $$ "1100" $$ "0100" $$ modrm_mm_noreg $ byte)
              @ (fun v =>
                   match v with
                     | inl (mr,(r,imm)) =>
                       (SSE_MM_Reg_op mr, (SSE_GP_Reg_op r, imm))
                     | inr ((mr,addr),imm) =>
                       (SSE_MM_Reg_op mr, (SSE_Addr_op addr, imm))
                   end %% pair_t sse_operand_t (pair_t sse_operand_t byte_t))
              & (fun u => 
                   match u with
                     | (SSE_MM_Reg_op mr, (SSE_GP_Reg_op r, imm)) =>
                       Some (inl (mr,(r,imm)))
                     | (SSE_MM_Reg_op mr, (SSE_Addr_op addr, imm)) =>
                       Some (inr ((mr,addr),imm))
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct_union; local_printable_tac.
    - destruct w as [op1 [op2 b]]; destruct op1; destruct op2; parsable_tac.
  Defined.

  Definition PMAXSW_p :=
    "0000" $$ "1111" $$ "1110" $$ "1110" $$ modrm_mm.

  Definition PMAXUB_p :=
    "0000" $$ "1111" $$ "1101" $$ "1110" $$ modrm_mm. 

  Definition PMINSW_p :=
    "0000" $$ "1111" $$ "1110" $$ "1010" $$ modrm_mm. 

  Definition PMINUB_p :=
    "0000" $$ "1111" $$ "1101" $$ "1010" $$ modrm_mm. 

  Definition PMOVMSKB_p :=
    "0000" $$ "1111" $$ "1101" $$ "0111" $$ "11"
           $$ SSE_GP_Reg_op_p $ SSE_MM_Reg_op_p.

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
    "0000" $$ "1111" $$ "1111" $$ "0110" $$ modrm_mm.

  Definition PSHUFW_p : 
    wf_bigrammar (pair_t sse_operand_t (pair_t sse_operand_t byte_t)).
    refine ("0000" $$ "1111" $$ "0111" $$ "0000" $$ modrm_mm $ byte 
              @ (fun v => 
                   match v with
                     | ((op1, op2), imm) => (op1, (op2, imm))
                   end %% pair_t sse_operand_t (pair_t sse_operand_t byte_t))
              & (fun u => 
                   match u with
                     | (op1,(op2,imm)) => Some ((op1,op2),imm)
                   end)
              & _); invertible_tac.
    - destruct w as [op1 [op2 b]]; parsable_tac.
  Defined.

  Definition MASKMOVQ_p :=
    "0000" $$ "1111" $$ "1111" $$ "0111" $$ "11"
           $$ SSE_MM_Reg_op_p $ SSE_MM_Reg_op_p.

  Definition MOVNTPS_p : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine ("0000" $$ "1111" $$ "0010" $$ "1011" $$ modrm_xmm_noreg
              @ (fun v =>
                   match v with
                     | (mr, addr) => (SSE_Addr_op addr, SSE_XMM_Reg_op mr)
                   end %% pair_t sse_operand_t sse_operand_t)
              & (fun u => 
                   match u with
                     | (SSE_Addr_op addr, SSE_XMM_Reg_op mr) =>
                       Some (mr,addr)
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct w as [op1 op2]; destruct op1; destruct op2; parsable_tac.
  Defined.

  Definition MOVNTQ_p : wf_bigrammar (pair_t sse_operand_t sse_operand_t).
    refine ("0000" $$ "1111" $$ "1110" $$ "0111" $$ modrm_mm_noreg
              @ (fun v =>
                   match v with
                     | (mr, addr) => (SSE_Addr_op addr, SSE_MM_Reg_op mr)
                   end %% pair_t sse_operand_t sse_operand_t)
              & (fun u => 
                   match u with
                     | (SSE_Addr_op addr, SSE_MM_Reg_op mr) =>
                       Some (mr,addr)
                     | _ => None
                   end)
              & _); invertible_tac.
    - destruct w as [op1 op2]; destruct op1; destruct op2; parsable_tac.
  Defined.

  Definition PREFETCHT0_p :=
    "0000" $$ "1111" $$ "0001" $$ "1000" $$ ext_op_modrm_sse_noreg "001".

  Definition PREFETCHT1_p :=
    "0000" $$ "1111" $$ "0001" $$ "1000" $$ ext_op_modrm_sse_noreg "010". 

  Definition PREFETCHT2_p := 
    "0000" $$ "1111" $$ "0001" $$ "1000" $$ ext_op_modrm_sse_noreg "011". 

  Definition PREFETCHNTA_p :=
    "0000" $$ "1111" $$ "0001" $$ "1000" $$ ext_op_modrm_sse_noreg "000". 

  Definition SFENCE_p := "0000" $$ "1111" $$ "1010" $$ "1110" $$ "1111"
                                $$ ! "1000".

  (** ** Glue all individual instruction grammars together into one big
         grammar.  *)


(* todo: make the following tactic printable_tac; remove local_printable_tac *)

  (* todo: remove *)
  (* Local Ltac destruct_ibr_vars := *)
  (*   repeat match goal with *)
  (*       | [v:[|sum_t _ _|] |- _] => destruct v *)
  (*       | [v:[|unit_t|] |- _] => destruct v *)
  (*       | [v:[|pair_t _ _|] |- _] => destruct v *)
  (*       | [v:[|option_t _|] |- _] => destruct v *)
  (*   end. *)

  (* Local Ltac new_printable_tac :=  *)
  (*   destruct_ibr_vars; printable_tac; ibr_prover. *)

  Definition lock_p : wf_bigrammar lock_or_rep_t. 
    refine("1111" $$ ! "0000"
             @ (fun v => lock %% lock_or_rep_t)
             & (fun lr => 
                  match lr with
                    | lock => Some ()
                    | _ => None
                  end)
             & _); invertible_tac.
    - new_printable_tac.
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
              & _); invertible_tac.
    - destruct_union; new_printable_tac.
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
              & _); invertible_tac.
    - new_printable_tac.
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
              & _); invertible_tac.
    - destruct_union; new_printable_tac.
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
               & _); clear_ast_defs; invertible_tac.
    - destruct_union; new_printable_tac.
    - destruct w; parsable_tac.
  Defined.

  (* Definition op_override_p : wf_bigrammar unit_t := "0110" $$ ! "0110". *)

  Definition op_override_p : wf_bigrammar bool_t.
    refine ("0110" $$ ! "0110"
              @ (fun v => true %% bool_t)
              & (fun u =>
                   match u with
                     | true => Some ()
                     | false => None
                   end)
              & _); invertible_tac.
    - new_printable_tac.
    - destruct w; parsable_tac.
  Defined.

  Definition addr_override_p : wf_bigrammar bool_t.
    refine ("0110" $$ ! "0111"
              @ (fun v => true %% bool_t)
              & (fun u =>
                   match u with
                     | true => Some ()
                     | false => None
                   end)
              & _); invertible_tac.
    - new_printable_tac.
    - destruct w; parsable_tac.
  Defined.

(* todo: convert some tactics in ibr_prover to use Hint Extern *)

  Definition opt2b (a: option bool) (default: bool) :=
    match a with
      | Some b => b
      | None => default
    end.

  (* todo: move earlier *)
  Lemma op_override_p_rng_inv op :
    in_bigrammar_rng (` op_override_p) op -> op = true.
  Proof. unfold op_override_p; intros; ibr_prover. Qed.

  (* Hint Extern 0 => *)
  (*   match goal with *)
  (*     | [H:in_bigrammar_rng (` op_override_p) ?op |- _] => *)
  (*       apply op_override_p_rng_inv in H *)
  (*   end : ibr_rng_db. *)

  (* Local Ltac prefix_pf_sim :=  *)
  (*   ibr_prover; bg_pf_sim; *)
  (*   repeat match goal with *)
  (*     | [H:in_bigrammar_rng (` op_override_p) ?op |- _] => *)
  (*       apply op_override_p_rng_inv in H *)
  (*   end. *)

  (* todo: organize some of the ibr_simpl and ibr_prover cases as
     Hint Rewrite stuff *)

  (* todo: clena up proofs for prefix grammars *)

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
              & _); invertible_tac.
    - destruct v as [l [s op]]. 
      compute [op_override addr_override lock_rep seg_override].
      destruct op as [op | ]; [destruct op | ]; compute [opt2b].
      + new_printable_tac.
      + match goal with
          | [H:in_bigrammar_rng (` (option_perm3 _ _ _)) (_,(_,_)) |- _] =>
            rewrite <- option_perm3_rng in H; 
            let H1:=fresh "H" in let H2:=fresh "H" in let H3:=fresh "H" in
            destruct H as [H1 [H2 H3]];
            rewrite option_perm_rng1 in H3;
            apply op_override_p_rng_inv in H3; inversion H3
        end.
      + new_printable_tac.
    - destruct w as [l s op addr];
      compute [op_override addr_override lock_rep seg_override] in *.
      destruct op; destruct addr; parsable_tac.
  Defined.

  (** this set of instructions can take prefixes in prefix_grammar_rep;
      that is, in lock_or_rep, only rep can be used; we put RET in this
      category because it turns out many binaries use "rep ret" to avoid the
      branch prediction panelty in AMD processors; intel processor seems to
      just ignore the rep prefix in "rep ret". *)
  Definition instr_grammars_rep_env : AST_Env instruction_t :=
    {0, INS_p, (fun v => INS v %% instruction_t)} :::
    {1, OUTS_p, (fun v => OUTS v %% instruction_t)} :::
    {2, MOVS_p, (fun v => MOVS v %% instruction_t)} :::
    {3, LODS_p, (fun v => LODS v %% instruction_t)} :::
    {4, STOS_p, (fun v => STOS v %% instruction_t)} :::
    {5, RET_p, (fun v => RET (fst v) (snd v) %% instruction_t)} :::
    ast_env_nil.

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
              & _); invertible_tac.
    - destruct v as [l [s op]]. 
      compute [op_override addr_override lock_rep seg_override].
      destruct op as [op | ]; [destruct op | ]; compute [opt2b].
      + new_printable_tac.
      + match goal with
          | [H:in_bigrammar_rng (` (option_perm3 _ _ _)) (_,(_,_)) |- _] =>
            rewrite <- option_perm3_rng in H; 
            let H1:=fresh "H" in let H2:=fresh "H" in let H3:=fresh "H" in
            destruct H as [H1 [H2 H3]];
            rewrite option_perm_rng1 in H3;
            apply op_override_p_rng_inv in H3; inversion H3
        end.
      + new_printable_tac.
    - destruct w as [l s op addr];
      compute [op_override addr_override lock_rep seg_override] in *.
      destruct op; destruct addr; parsable_tac.
  Defined.

  (** this set of instructions can take prefixes in prefix_grammar_repn;
      that is, in lock_or_rep, either rep or repn can be used, but not lock *)
  Definition instr_grammars_rep_or_repn_env : AST_Env instruction_t :=
    {10, CMPS_p, (fun v => CMPS v %% instruction_t)} :::
    {11, SCAS_p, (fun v => SCAS v %% instruction_t)} :::
    ast_env_nil.                                  

  Definition instr_grammar_env := 
    ast_env_cat prefix_grammar_rep instr_grammars_rep_env +++
    ast_env_cat prefix_grammar_rep_or_repn
      instr_grammars_rep_or_repn_env.

  Definition instr_grammar_type : type.
    let t:=gen_ast_type instr_grammar_env in exact(t).
  Defined.

  Definition from_instr (u:prefix * instr) : option [|instr_grammar_type|].
    intro.
    refine (match snd u with
              | CMPS a => _
              | INS a => _
              | LODS a => _
              | MOVS a => _
              | OUTS a => _
              | RET a1 a2 => _
              | SCAS a => _
              | STOS a => _
              | _ => None
            end).
    Local Ltac gen lbl u arg :=
      let f:=gen_rev_case_by_lbl instr_grammar_env lbl in 
      let f1 := eval simpl in f in
      exact (Some (f1 (fst u, arg))).
    * (* CMPS *) gen 10 u a.
    * (* INS *) gen 0 u a.
    * (* LODS *) gen 3 u a.
    * (* MOVS *) gen 2 u a.
    * (* OUTS *) gen 1 u a.
    * (* RET *) gen 5 u (a1,a2).
    * (* SCAS *) gen 11 u a.
    * (* STOS *) gen 4 u a.
  Defined.

  Definition instruction_grammar : wf_bigrammar (pair_t prefix_t instruction_t).
    let g := gen_ast_grammar instr_grammar_env in pose (gr:=g);
    let m := gen_ast_map instr_grammar_env in pose (mp:=m).
    refine (gr @ (mp: _ -> [|pair_t prefix_t instruction_t|])
               & from_instr
               & _); clear_ast_defs; unfold from_instr; invertible_tac.
    - Time new_printable_tac.
    - destruct w as [p ins]; destruct ins; parsable_tac.
  Defined.


TBC:

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



Old grammars:

  Fixpoint list2pair_t (l: list type) :=
    match l with
      | nil => Unit_t
      | r::r'::nil => Pair_t r r'
      | r::l' => Pair_t r (list2pair_t l')
    end.
 
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
