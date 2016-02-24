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
  Definition i_instr1_t := User_t I_Instr1_t.
  Definition i_instr2_t := User_t I_Instr2_t.
  Definition i_instr3_t := User_t I_Instr3_t.
  Definition i_instr4_t := User_t I_Instr4_t.
  Definition i_instr5_t := User_t I_Instr5_t.
  Definition i_instr6_t := User_t I_Instr6_t.
  Definition f_instr1_t := User_t F_Instr1_t.
  Definition f_instr2_t := User_t F_Instr2_t.
  Definition m_instr_t := User_t M_Instr_t.
  Definition s_instr1_t := User_t S_Instr1_t.
  Definition s_instr2_t := User_t S_Instr2_t.
  Definition instruction_t := User_t Instruction_t.
  Definition control_register_t := User_t Control_Register_t.
  Definition debug_register_t := User_t Debug_Register_t.
  Definition segment_register_t := User_t Segment_Register_t.
  Definition lock_or_rep_t := User_t Lock_or_Rep_t.
  Definition bool_t := User_t Bool_t.
  Definition prefix_t := User_t Prefix_t.
  Definition bitvector_t n := User_t (BitVector_t n).
  Definition selector_t := User_t (BitVector_t 15).

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

  Local Ltac destruct_union :=
    repeat match goal with
             | [v: [| Sum_t _ _ |] |- _ ] => destruct v as [v | v]
             | [v: [| Unit_t |] |- _] => destruct v
           end.

  Local Ltac lineararith := 
    unfold two_power_nat, shift_nat in *; simpl in *; omega.

  Local Ltac ins_destruct_var v := 
    match goal with
      | [ H: match v with | EAX => _ | ECX => _ | EDX => _ | EBX => _ 
                       | ESP => _ | EBP => _ | ESI => _ | EDI => _ end 
             = _ |- _ ] =>
        destruct v
      | [ H: match v with | Imm_op _ => _ | Reg_op _ => _ 
                       | Address_op _ => _ | Offset_op _ => _ end
             = _ |- _ ] =>
        destruct v
      | [ H: match v with | Reg_ri _ => _ | Imm_ri _ => _ end
             = _ |- _ ] =>
        destruct v
      | [ H: match v with | ES => _ | CS => _ | SS => _ | DS => _ 
                       | FS => _ | GS => _ end 
             = _ |- _ ] =>
        destruct v
      | _ => destruct_var v
    end.

  Local Ltac ins_parsable_tac := 
    parsable_tac_gen ibr_sim ins_destruct_var.

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
      tactics take advantage of this to get more efficient reverse
      functions. Here are the general steps:

      - combine g_i using balanced alts to get "g_1 |+| ... |+| g_n". This
        doesn't lose any info as it generates values in an AST tree type.

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
      reverse mapping function for the case identified by the label.  In an
      AST_Env, labels must be in the asending order; however, they don't
      need to be consecutive (although they could). *)
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

  (** Cat p1 to every grammar inside the ast env *)
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

  (** Append two ast envs *)
  Fixpoint ast_env_app t (ae1 ae2: AST_Env t) : AST_Env t := 
    match ae1 with
      | ast_env_nil => ae2
      | ast_env_cons l pt p f ae1' =>
        ast_env_cons l p f (ast_env_app ae1' ae2)
    end.

  Notation "ael +++ aer" := 
    (ast_env_app ael aer) (right associativity, at level 85).

  (* compute ceiling(n/2) *)
  Fixpoint divide_by_two n :=
    match n with
      | O => O
      | S O => 1
      | S (S n') => S (divide_by_two n')
    end.

  (** Split the env list into two halves at the middle *)
  (* possible todo: change env_split to output a AST tree
     and reuse that tree in other tacitics so that it 
     doesn't need to be called multiple times. *)
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

  Ltac env_length ast_env := 
    match ast_env with
      | ast_env_nil => O
      | ast_env_cons _ _ _ ?ae' => 
        let l := env_length ae' in
        constr: (S l)
    end.

  (* The ltac version of env_split; using the Gallina version of env_split
     can be problematic in "eval simpl in (env_split ...)" because the
     simpl tactic would unfold the environment in unexpected ways *)
  Ltac env_split ae :=
    let len := env_length ae in
    let mid := eval compute in (divide_by_two len) in
    let aet := type of ae in
    let t := match aet with
               | AST_Env ?t => t
             end in
    (* using CPS to build the two lists in one pass *)
    let rec splitHelper i l k :=
        let eq := eval compute in (beq_nat i mid) in
        match eq with
          | true => constr:(k (ast_env_nil, l))
          | false =>
            match l with
              | ast_env_cons ?n ?g ?f ?ae' =>
                let res := splitHelper (S i) ae'
                             (fun v => k (ast_env_cons n g
                                         (f: _ -> [|t|]) (fst v), snd v)) in
                constr:(res)
            end
        end
    in let aepair := splitHelper O ae (fun u:aet*aet => u) in
       eval cbv beta delta [fst snd] iota in aepair.

  Ltac gen_ast_grammar ast_env :=
  match ast_env with
    | ast_env_cons ?l ?g ?f ast_env_nil => constr:(g)
    | ast_env_nil => never (* should not happen *)
    | _ =>
      let aepair := env_split ast_env in
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
        let aepair := env_split ast_env in
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
      let aepair := env_split ast_env in
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
    let len := env_length ast_env in
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
    let len := env_length ast_env in
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
      label of the entry (not the index of the entry); parameter t could be
      calculated from ast_env, but passing it for efficiency. *)
  Ltac gen_rev_case_lbl l ast_env t := 
    match ast_env with
      | ast_env_cons ?l1 _ _ ast_env_nil => 
        let eq_l_l1 := (eval compute in (beq_nat l l1)) in
        match eq_l_l1 with
          | true => constr:(fun v: interp t => v)
        end
      | _ =>
      let aepair := env_split ast_env in
      match aepair with
        | (?ael, ?aer) =>
          match aer with
            | ast_env_cons ?l2 _ _ ?aer1 =>
              match t with
                | sum_t ?t1 ?t2 =>
                  let b := (eval compute in (NPeano.ltb l l2)) in
                  match b with
                    | true => 
                      let f := gen_rev_case_lbl l ael t1 in 
                      constr:(fun v => (inl  (f v)):(interp t))
                    | false => 
                      let f := gen_rev_case_lbl l aer t2 in
                      constr:(fun v => (inr (f v)):(interp t))
                  end
              end
          end
      end
    end.

  (** given an ast env, generate a balanced grammar using |+|, a
      map function from ast values to values of the target type, 
      and a list of case functions for mapping from case values
      to ast values *)
  Ltac gen_ast_defs ast_env := 
    pose (ae:=ast_env);
    autounfold with env_unfold_db in ae;
    let ae1 := eval cbv delta [ae] in ae in
      let g := gen_ast_grammar ae1 in pose (gr:=g);
      let m := gen_ast_map ae1 in pose (mp:=m);
      gen_rev_cases ae1;
      clear ae.

  (* testing the above tactics *)
  (* Definition test_env: AST_Env register_t := *)
  (*   {0, empty, (fun v => EAX %% register_t)} ::: *)
  (*   {1, empty, (fun v => ECX %% register_t)} ::: *)
  (*   {2, empty, (fun v => EDX %% register_t)} ::: *)
  (*   {3, empty, (fun v => EBX %% register_t)} ::: *)
  (*   {4, empty, (fun v => EBP %% register_t)} ::: *)
  (*   {5, empty, (fun v => ESI %% register_t)} ::: *)
  (*   {6, empty, (fun v => EDI %% register_t)} ::: *)
  (*   ast_env_nil. *)
  (* Hint Unfold test_env : env_unfold_db. *)

  (* Goal False. *)
  (*   gen_ast_defs test_env. *)

  (* let ae:= eval unfold test_env in test_env in *)
  (*   gen_ast_defs ae. *)
  (* let cs := gen_rev_case_by_lbl ae 3 in *)
  (* let cs' := eval cbv beta delta [interp] iota in cs in *)
  (* pose cs'. *)

  (* let m := gen_ast_map ae in *)
  (* pose m. *)

  (* let l := env_split ae in *)
  (* pose l. *)

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
  Hint Unfold control_reg_env: env_unfold_db.

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
     - destruct w; parsable_tac.
  Defined.

  Definition debug_reg_env : AST_Env debug_register_t := 
    {0, ! "000", (fun _ => DR0 %% debug_register_t)} :::
    {1, ! "001", (fun _ => DR1 %% debug_register_t)} :::
    {2, ! "010", (fun _ => DR2 %% debug_register_t)} :::
    {3, ! "011", (fun _ => DR3 %% debug_register_t)} :::
    {4, ! "110", (fun _ => DR6 %% debug_register_t)} :::
    {5, ! "111", (fun _ => DR7 %% debug_register_t)} :::
    ast_env_nil.
  Hint Unfold debug_reg_env: env_unfold_db.
     
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
  Hint Unfold segment_reg_env: env_unfold_db.

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
     - destruct w; parsable_tac.
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
  Hint Unfold reg_no_esp_env : env_unfold_db.

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
     - destruct w; parsable_tac.
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
    end; ins_ibr_sim; apply bitsmatch_rng.
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
     - destruct w; parsable_tac.
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
    end; ins_ibr_sim; apply bitsmatch_rng.
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
     - destruct w; parsable_tac.
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
      end; ins_ibr_sim; apply bitsmatch_rng.
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

  Definition si_p: wf_bigrammar (option_t (pair_t scale_t register_t)). 
    refine ((scale_p $ reg)
            @ (fun p => match snd p with 
                          | ESP => None
                          | _ => Some p
                        end %% option_t (pair_t scale_t register_t))
            & (fun v => match v with
                          | None => Some (Scale1, ESP)
                          | Some (_, ESP) => None
                          | Some (s,p) => Some (s,p)
                        end)
            & _); invertible_tac.
    - destruct v as [s r]; destruct r; printable_tac.
    - ins_parsable_tac.
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
    end; ins_ibr_sim.
  Qed.
  Hint Resolve si_p_rng_none: ibr_rng_db.

  Definition sib_p := si_p $ reg.

  Lemma sib_p_rng_none r: in_bigrammar_rng (` sib_p) (None, r).
  Proof. intros; unfold sib_p. ins_ibr_sim. Qed.
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

  Definition Reg_op_p : wf_bigrammar operand_t.
    refine(reg @ (fun r => Reg_op r : interp operand_t)
               & (fun op => match op with
                              | Reg_op r => Some r
                              | _ => None
                            end)
               & _); invertible_tac; ins_parsable_tac.
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
  (*         ins_ibr_sim. apply reg_no_esp_ebp_neq. trivial. *)
  (*       abstract (sim; bg_pf_sim; printable_tac; ins_ibr_sim). *)
  (*     + (* case 1 *) *)
  (*       destruct v as [r [si bs]]. *)
  (*       rewrite Word.int_eq_refl. *)
  (*       assert (bs <> EBP). *)
  (*         ins_ibr_sim. apply reg_no_ebp_neq. trivial. *)
  (*       destruct si as [[sc idx] | ]. *)
  (*       * assert (idx <> ESP). *)
  (*           ins_ibr_sim. eapply si_p_rng_some. eassumption. *)
  (*         abstract (bg_pf_sim; printable_tac). *)
  (*       * abstract (bg_pf_sim; printable_tac; ins_ibr_sim). *)
  (*     + (* case 2 *) *)
  (*       destruct v as [r [si disp]]. *)
  (*       abstract (destruct si as [[sc idx] | ]; printable_tac; ins_ibr_sim). *)
  (*     + (* case 3 *) *)
  (*       abstract printable_tac. *)
  (*     + (* case 4 *) *)
  (*       destruct v as [r [bs disp]]. *)
  (*       abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim). *)
  (*     + (* case 5 *) *)
  (*       destruct v as [r [[si bs] disp]]. *)
  (*       rewrite sign_shrink32_8_inv. *)
  (*       destruct si as [[sc idx] | ]. *)
  (*       * unfold sib_p in *; *)
  (*         assert (idx <> ESP). *)
  (*           ins_ibr_sim. eapply si_p_rng_some. eassumption. *)
  (*         abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim). *)
  (*       * abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim). *)
  (*     + (* case 6 *) *)
  (*       destruct v as [r [bs disp]]. *)
  (*       abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim). *)
  (*     + (* case 7 *) *)
  (*       destruct v as [r [[si bs] disp]]. *)
  (*       destruct si as [[sc idx] | ]. *)
  (*       * unfold sib_p in *; *)
  (*         assert (idx <> ESP). *)
  (*           ins_ibr_sim. eapply si_p_rng_some. eassumption. *)
  (*         abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim). *)
  (*       * abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim). *)
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
           ins_ibr_sim. apply reg_no_esp_ebp_neq. trivial.
         abstract (sim; bg_pf_sim; printable_tac; ins_ibr_sim).
        * (* case 1 *)
          destruct v as [si bs].
          rewrite Word.int_eq_refl.
          assert (bs <> EBP).
            ins_ibr_sim; apply reg_no_ebp_neq; trivial.
          destruct si as [[sc idx] | ].
          { assert (idx <> ESP).
              ins_ibr_sim. eapply si_p_rng_some. eassumption.
            abstract (bg_pf_sim; printable_tac).
          }
          { abstract (bg_pf_sim; printable_tac; ins_ibr_sim). }
        * (* case 2 *)
          destruct v as [si disp].
          abstract (destruct si as [[sc idx] | ];
                    printable_tac; ins_ibr_sim).
        * (* case 3 *) abstract printable_tac.
      + (* mode 01 *)
        destruct v as [r v].
        unfold rm01 in *; destruct_union; ins_ibr_sim.
        * (* case 0 *)
          destruct v as [bs disp].
         abstract (unfold rm00; bg_pf_sim;
                   try destruct_head; printable_tac; ins_ibr_sim).
        * (* case 1 *)
          destruct v as [[si bs] disp].
          rewrite sign_shrink32_8_inv.
          destruct si as [[sc idx] | ].
          { unfold sib_p in *; 
            assert (idx <> ESP).
              ins_ibr_sim. eapply si_p_rng_some. eassumption.
            abstract (unfold rm00; bg_pf_sim;
                      try destruct_head; printable_tac; ins_ibr_sim). }
          { abstract (unfold rm00; bg_pf_sim;
                      try destruct_head; printable_tac; ins_ibr_sim). }
       + (* mode 10 *)
        destruct v as [r v].
        unfold rm10 in *; destruct_union; ins_ibr_sim.
        * (* case 0 *)
          destruct v as [bs disp].
         abstract (unfold rm00, rm01; bg_pf_sim; 
                   try destruct_head; printable_tac; ins_ibr_sim).
        * (* case 1 *)
          destruct v as [[si bs] disp].
          destruct si as [[sc idx] | ].
          { unfold rm00, rm01, sib_p in *; 
            assert (idx <> ESP).
              ins_ibr_sim. eapply si_p_rng_some. eassumption.
            abstract (bg_pf_sim; try destruct_head; printable_tac; ins_ibr_sim).
          }
          { abstract (unfold rm00, rm01; bg_pf_sim; 
                      try destruct_head; printable_tac; ins_ibr_sim). }
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
             & Address_op_inv & _); 
    unfold Address_op_inv; invertible_tac; ins_parsable_tac.
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
    - ins_parsable_tac.
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
              & _); invertible_tac; ins_parsable_tac.
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
              & _); invertible_tac; ins_parsable_tac.
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
           & _); invertible_tac; ins_parsable_tac.
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
  Proof. intros; unfold modrm_gen_noreg in *. 
         repeat (ins_ibr_sim || destruct_pr_var); crush. Qed.

  (* can prove a more precise range lemma if necessary *)
  Lemma modrm_gen_noreg_rng reg_t (reg_p: wf_bigrammar reg_t)
        (r1 r2:[|reg_t|]) addr: 
    in_bigrammar_rng (` (modrm_gen_noreg reg_p)) (r1, addr) ->
    in_bigrammar_rng (` reg_p) r2 -> 
    in_bigrammar_rng (` (modrm_gen_noreg reg_p)) (r2, addr).
  Proof. intros; unfold modrm_gen_noreg in *. ins_ibr_sim.
    compute [fst].
    match goal with
      | [v: [|sum_t ?t1 (sum_t ?t2 ?t3)|] |- _] => 
        destruct_union; ins_ibr_sim;
        destruct v as [r1' v];
        [exists (inl [|sum_t t2 t3|] (r2, v)) | 
         exists (inr [|t1|] (inl [|t3|] (r2,v))) |
         eexists (inr [|t1|] (inr [|t2|] (r2,v))) ]
    end;
    split; ins_ibr_sim; crush.
  Qed.

  Lemma ext_op_modrm_rng1 bs r: 
    in_bigrammar_rng (` (ext_op_modrm bs)) (Reg_op r).
  Proof. unfold ext_op_modrm; intros; ins_ibr_sim.
    exists (inr [|address_t|] r); compute [fst]. 
    split. 
    + unfold ext_op_modrm_gen; ins_ibr_sim.
    + trivial.
  Qed.
  Hint Resolve ext_op_modrm_rng1: ibr_rng_db.

  Lemma ext_op_modrm_rng_inv (bs:string) op :
    in_bigrammar_rng (` (ext_op_modrm bs)) op ->
    (exists r, op = Reg_op r) \/ (exists addr, op = Address_op addr).
  Proof. unfold ext_op_modrm; intros; ins_ibr_sim.
    destruct v; subst op; [right | left]; eexists; trivial.
  Qed.

  Lemma Reg_op_p_rng op : 
    (exists r, op = Reg_op r) <-> in_bigrammar_rng (`Reg_op_p) op.
  Proof. intros. unfold Reg_op_p; split; intro; ins_ibr_sim.
    - compute [fst]. generalize reg_rng. crush.
    - crush.
  Qed.

  Lemma Reg_op_p_rng2 r: in_bigrammar_rng (`Reg_op_p) (Reg_op r).
  Proof. intros; apply Reg_op_p_rng. eexists; trivial. Qed.
  Hint Resolve Reg_op_p_rng2: ibr_rng_db.

  Lemma modrm_ret_reg_rng_inv r op:
    in_bigrammar_rng (` modrm_ret_reg) (r,op) -> 
    (exists r, op = Reg_op r) \/ (exists addr, op = Address_op addr).
  Proof. unfold modrm_ret_reg; intros. ins_ibr_sim.
    destruct v as [[r1 addr] | [r1 r2]]; clear H0.
    - right. crush. 
    - left. crush. 
  Qed.

  Lemma modrm_ret_reg_rng1 r1 r2: in_bigrammar_rng (` modrm_ret_reg) (r1, Reg_op r2).
  Proof. intros. unfold modrm_ret_reg, modrm_gen. ins_ibr_sim. compute [fst].
    exists (inr [|pair_t register_t address_t|] (r1, r2)).
    split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_ret_reg_rng1: ibr_rng_db.

  (* with more work, this lemma could be made more general; will do it if necessary *)
  Lemma modrm_ret_reg_rng2 r1 r2 addr: 
    in_bigrammar_rng (` modrm_ret_reg) (r1, Address_op addr) ->
    in_bigrammar_rng (` modrm_ret_reg) (r2, Address_op addr).
  Proof. unfold modrm_ret_reg; intros; ins_ibr_sim; compute [fst].
    destruct v as [[r1' addr'] | [r1' r2']]; try congruence.
    sim; subst r1' addr'.
    unfold modrm_gen in *; ins_ibr_sim.
    exists (inl [|pair_t register_t register_t|] (r2,addr)).
    split.
    - ins_ibr_sim. eapply modrm_gen_noreg_rng. eassumption. ins_ibr_sim.
    - trivial.
  Qed.
  Hint Extern 1 (in_bigrammar_rng (` (modrm_ret_reg)) (_, Address_op _)) =>
    eapply modrm_ret_reg_rng2; eassumption : ibr_rng_db.

  Lemma imm_p_false_rng w: in_bigrammar_rng (` (imm_p false)) w.
  Proof. unfold imm_p; intros. ins_ibr_sim. Qed.

  Lemma imm_p_true_rng w:
    repr_in_signed_halfword w -> 
    in_bigrammar_rng (` (imm_p true)) w.
  Proof. unfold imm_p; intros. ins_ibr_sim. compute [fst].
    exists (sign_shrink32_16 w); split.
      - ins_ibr_sim.
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
  Proof. unfold field_intn; intros. ins_ibr_sim.
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
    ins_ibr_sim; bg_pf_sim;
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

  Local Ltac ins_printable_tac := printable_tac_gen ins_pf_sim.
  Local Ltac ins_invertible_tac := invertible_tac_gen ins_pf_sim ins_destruct_var.

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
  Hint Unfold logic_or_arith_env : env_unfold_db.

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
      destruct v as [d [w [r1 op2]]].  destruct d; ins_printable_tac.
    + (* case 1 *)
      destruct v as [r b]. 
      destruct r; ins_printable_tac.
      (* EAX case *)
      apply imm_p_rng; apply repr_in_signed_extend; omega.
    + (* case 2 *)
      destruct v as [r b]; destruct r; ins_printable_tac.
    + (* case 3 *)
      destruct v as [r op2]; 
      destruct r; ins_printable_tac.
    + (* case 4 *)
      ins_printable_tac.
    + (* case 5 *)
      ins_printable_tac.
    + (* case 6 *)
      destruct v as [op b]; ins_printable_tac.
    + (* case 7 *)
      destruct v as [op b]; ins_printable_tac.
    + (* case 8 *)
      destruct v as [op1 op2]; ins_printable_tac.
  - destruct w as [wd [op1 op2]].
    destruct op1; try parsable_tac.
    + (* op1 = Reg_op _ *)
      destruct op2; try parsable_tac.
      destruct r; destruct wd; ins_pf_sim; parsable_tac.
    + (* op1 = Address_op _ *)
      destruct op2; try parsable_tac; ins_pf_sim; parsable_tac.
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
  Hint Unfold bit_test_env : env_unfold_db.

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
              & _); clear_ast_defs; ins_invertible_tac.
  Defined.

  Definition BT_p := bit_test_p "100" "00".
  Definition BTC_p := bit_test_p "111" "11".
  Definition BTR_p := bit_test_p "110" "10".
  Definition BTS_p := bit_test_p "101" "01".

  Definition CALL_p : 
    wf_bigrammar (pair_t bool_t (pair_t bool_t (pair_t operand_t
                                                  (option_t selector_t)))).
    set (t:= (pair_t bool_t (pair_t bool_t (pair_t operand_t
                                              (option_t selector_t))))).
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
                  end %% t)
             & (fun u: [|t|] => 
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
             & _); unfold t; ins_invertible_tac.
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
                  let (b,op):=u in
                  match op with
                    | Reg_op r => 
                      (* alternate encoding possible, when "fst u" is true.
                         use case 1 above *)
                      Some (inl (fst u, r))
                    | Address_op addr => Some (inr (inr (fst u, addr)))
                    | _ => None
                  end)
             & _); ins_invertible_tac.
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
                   let (b,op):=u in
                   match op with
                     | Reg_op r => Some (inl (fst u, r))
                     | Address_op addr => Some (inr (fst u, addr))
                     | _ => None
                   end)
              & _); ins_invertible_tac.
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
                   let (b,op):=u in
                   match op with
                     | Reg_op r => Some (inl (fst u, r))
                     | Address_op addr => Some (inr (fst u, addr))
                     | _ => None
                   end)
              & _); ins_invertible_tac.
  Defined.

  Definition IMUL_p (opsize_override:bool): 
    wf_bigrammar (pair_t bool_t (pair_t operand_t (pair_t (option_t operand_t)
                                                     (option_t word_t)))).
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
                  pair_t bool_t (pair_t operand_t (pair_t (option_t operand_t) (option_t word_t))))
             & (fun u:[|pair_t bool_t
                          (pair_t operand_t (pair_t (option_t operand_t) (option_t word_t)))|] => 
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
             & _); ins_invertible_tac.
    - destruct_union; try ins_printable_tac.
      + (* case 3 *)
        destruct v as [[r1 op2] imm].
        destruct opsize_override; compute [negb];
        ins_printable_tac.
    - abstract
        (destruct w as [bl [op1 [w1 w2]]];
         destruct op1; destruct bl;
         destruct w1 as [op2 | ];
         destruct w2; try parsable_tac;
         destruct op2; destruct opsize_override;
         ins_pf_sim; parsable_tac).
  Defined.

  Definition IN_p: wf_bigrammar (pair_t char_t (option_t byte_t)).
    refine (("1110" $$ "010" $$ anybit $ byte |+| 
             "1110" $$ "110" $$ anybit)
              @ (fun v => 
                   match v with
                     | inl (w,b) => (w, Some b)
                     | inr w => (w, None)
                   end %% (pair_t char_t (option_t byte_t)))
              & (fun u => 
                   match u with
                     | (w, Some b) => Some (inl (w,b))
                     | (w, None) => Some (inr w)
                   end)
              & _); ins_invertible_tac.
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
              & _); ins_invertible_tac.
    - destruct_union; try ins_printable_tac.
      + (* case 0 *)
        destruct v as [w r].
        destruct w; ins_printable_tac.
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
              & _); ins_invertible_tac.
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
  Hint Unfold JMP_env : env_unfold_db.

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
              & _); clear_ast_defs; ins_invertible_tac.
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
             & _); ins_invertible_tac.
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
             & _); ins_invertible_tac.
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
             & _); ins_invertible_tac.
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
  Hint Unfold MOV_env : env_unfold_db.

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
              & _); clear_ast_defs; ins_invertible_tac.
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
             & _); ins_invertible_tac.
    - destruct v as [w [r1 op2]]. 
      destruct w; ins_pf_sim; printable_tac; ins_ibr_sim.
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

  Definition OUT_p :wf_bigrammar (pair_t bool_t (option_t byte_t)).
    refine ((("1110" $$ "011" $$ anybit $ byte) |+|
             ("1110" $$ "111" $$ anybit))
              @ (fun v =>
                   match v with
                     | inl (w, b) => (w, Some b)
                     | inr w => (w, None)
                   end %% pair_t bool_t (option_t byte_t))
              & (fun u:[|pair_t bool_t (option_t byte_t)|] => 
                   match u with
                     | (w, Some b) => Some (inl (w,b))
                     | (w, None) => Some (inr w)
                   end)
              & _); ins_invertible_tac.
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
              & _); ins_invertible_tac.
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
  Hint Unfold POPSR_env : env_unfold_db.

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
               & _); clear_ast_defs; ins_invertible_tac.
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
  Hint Unfold PUSH_env : env_unfold_db.

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
               & _); clear_ast_defs; ins_invertible_tac.
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
  Hint Unfold PUSHSR_env : env_unfold_db.

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
               & _); clear_ast_defs; ins_invertible_tac.
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
              & _); ins_invertible_tac.
    - ins_parsable_tac; destruct r; ins_parsable_tac.
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

  Definition RET_env : AST_Env (pair_t bool_t (option_t half_t)) := 
    {0, "1100" $$ ! "0011", 
     (fun v => (true, None) %% pair_t bool_t (option_t half_t))} :::
    {1, "1100" $$ "0010" $$ halfword,
     (fun h => (true, Some h) %% pair_t bool_t (option_t half_t))} :::
    {2, "1100" $$ ! "1011",
     (fun h => (false, None) %% pair_t bool_t (option_t half_t))} :::
    {3, "1100" $$ "1010" $$ halfword,
     (fun h => (false, Some h) %% pair_t bool_t (option_t half_t))} :::
    ast_env_nil.
  Hint Unfold RET_env : env_unfold_db.

  Definition RET_p : wf_bigrammar (pair_t bool_t (option_t half_t)).
    gen_ast_defs RET_env.
    refine (gr @ (mp: _ -> [|pair_t bool_t (option_t half_t)|])
               & (fun u => 
                    match u with
                      | (true, None) => case0 ()
                      | (true, Some h) => case1 h
                      | (false, None) => case2 ()
                      | (false, Some h) => case3 h
                    end)
               & _); clear_ast_defs; ins_invertible_tac.
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
             & (fun u:condition_type*operand => 
                  let (ct,op):=u in
                  match op with
                    | Reg_op _ | Address_op _ =>
                      (* alternate encoding: the reg can be any register *)
                      Some (fst u, (EAX, snd u))
                    | _ => None
                  end)
             & _); ins_invertible_tac.
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
  Hint Unfold shiftdouble_env : env_unfold_db.

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
               & _); clear_ast_defs; ins_invertible_tac.
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

  Definition TEST_env (opsize_override:bool) : 
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
  Hint Unfold TEST_env : env_unfold_db.

  Definition TEST_p (opsize_override: bool) : 
    wf_bigrammar (pair_t bool_t (pair_t operand_t operand_t)).
    intros; gen_ast_defs (TEST_env opsize_override).
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
    - abstract (destruct_union; ins_printable_tac).
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
              & _); ins_invertible_tac.
    - destruct_union.  
      + destruct v as [w [r1 op2]]; ins_pf_sim; bg_pf_sim;
        destruct w; printable_tac; ins_ibr_sim.
      + ins_printable_tac.
  Defined.

  Definition XLAT_p := "1101" $$ ! "0111".

  (** ** Defs used in grammars for floating-point instructions *)

  Local Ltac fp_destruct_var v := 
    match goal with
      | [ H: match v with | FPS_op _ => _ | FPM16_op _ => _ | FPM32_op _ => _
                       | FPM64_op _ => _ | FPM80_op _ => _ end
             = _ |- _ ] =>
        destruct v
      | _ => ins_destruct_var v
    end.

  Local Ltac fp_parsable_tac := parsable_tac_gen ins_pf_sim fp_destruct_var.
  Local Ltac fp_invertible_tac := invertible_tac_gen ins_pf_sim fp_destruct_var.

  Definition fpu_reg_op_p : wf_bigrammar fp_operand_t.
    refine (fpu_reg @ (fun v => FPS_op v %% fp_operand_t)
                    & (fun u => match u with | FPS_op v => Some v | _ => None end)
                    & _); fp_invertible_tac.
  Defined.

  Definition ext_op_modrm_FPM32_noreg (bs:string) : wf_bigrammar fp_operand_t.
    intros.
    refine ((ext_op_modrm_noreg_ret_addr bs)
              @ (fun v => FPM32_op v %% fp_operand_t)
              & (fun u => match u with | FPM32_op v => Some v | _ => None end)
                    & _); fp_invertible_tac.
  Defined.

  Definition ext_op_modrm_FPM64_noreg (bs:string) : wf_bigrammar fp_operand_t.
    intros.
    refine ((ext_op_modrm_noreg_ret_addr bs)
              @ (fun v => FPM64_op v %% fp_operand_t)
              & (fun u => match u with | FPM64_op v => Some v | _ => None end)
                    & _); fp_invertible_tac.
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
  Hint Unfold fp_arith_env : env_unfold_db.

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
              & _); clear_ast_defs; fp_invertible_tac.
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
  Hint Unfold FLD_env : env_unfold_db.

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

  Definition FNSTSW_p : wf_bigrammar (option_t fp_operand_t).
    refine (("11011" $$ "111" $$ "111" $$ ! "00000" |+|
             "11011" $$ "101" $$ ext_op_modrm_FPM32_noreg "111")
              @ (fun v =>
                   match v with
                     | inl () => None
                     | inr op => Some op
                   end %% option_t fp_operand_t)
              & (fun u:[|option_t fp_operand_t|] =>
                   match u with
                     | Some op => Some (inr op)
                     | None => Some (inl ())
                   end)
              & _); invertible_tac.
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
  Hint Unfold FSTP_env : env_unfold_db.

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

  Local Ltac mmx_destruct_var v := 
    match goal with
      | [ H: match v with | GP_Reg_op _ => _ | MMX_Addr_op _ => _
                       | MMX_Reg_op _ => _ | MMX_Imm_op _ => _ end
             = _ |- _ ] =>
        destruct v
      | [ H: match v with | MMX_8 => _ | MMX_16 => _
                       | MMX_32 => _ | MMX_64 => _ end
             = _ |- _ ] =>
        destruct v
      | _ => ins_destruct_var v
    end.

  Local Ltac mmx_parsable_tac := 
    parsable_tac_gen ins_pf_sim mmx_destruct_var.

  Definition MMX_Reg_op_p: wf_bigrammar mmx_operand_t.
    refine (mmx_reg @ (fun r => MMX_Reg_op r : interp mmx_operand_t)
                    & (fun op => match op with 
                                   | MMX_Reg_op r => Some r
                                   | _ => None
                                 end)
                    & _); ins_invertible_tac; mmx_parsable_tac.
  Defined.

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
    - mmx_parsable_tac.
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
              & _); invertible_tac; mmx_parsable_tac.
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
              & _); ins_invertible_tac; mmx_parsable_tac.
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
              & _); ins_invertible_tac; mmx_parsable_tac.
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
              & _); ins_invertible_tac; mmx_parsable_tac.
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
              & _); ins_invertible_tac; mmx_parsable_tac.
  Defined.

  Lemma mmx_reg_rng: forall mr, in_bigrammar_rng (` mmx_reg) mr.
  Proof. intros; unfold mmx_reg.  apply field_intn_rng. Qed.
  Hint Resolve mmx_reg_rng: ibr_rng_db.

  Lemma modrm_mmx_ret_reg_rng1 mr1 mr2: 
    in_bigrammar_rng (` modrm_mmx_ret_reg) (mr1, MMX_Reg_op mr2).
  Proof. intros. unfold modrm_mmx_ret_reg, modrm_gen. ins_ibr_sim. compute [fst].
    exists (inr [|pair_t mmx_register_t address_t|] (mr1, mr2)).
    split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_mmx_ret_reg_rng1: ibr_rng_db.

  Lemma modrm_mmx_ret_reg_rng_inv mr op:
    in_bigrammar_rng (` modrm_mmx_ret_reg) (mr,op) -> 
    (exists mr, op = MMX_Reg_op mr) \/ (exists addr, op = MMX_Addr_op addr).
  Proof. unfold modrm_mmx_ret_reg; intros. ins_ibr_sim.
    destruct v as [[r1 addr] | [r1 r2]]; clear H0.
    - right. crush. 
    - left. crush. 
  Qed.

  Lemma modrm_mmx_rng1 mr1 mr2: 
    in_bigrammar_rng (` modrm_mmx) (MMX_Reg_op mr1, MMX_Reg_op mr2).
  Proof. unfold modrm_mmx; intros; ins_ibr_sim. compute [fst].
     exists (mr1, MMX_Reg_op mr2); split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_mmx_rng1: ibr_rng_db.

  Lemma modrm_mmx_rng_inv1 op1 op2: 
    in_bigrammar_rng (` modrm_mmx) (op1,op2) -> exists mr, op1 = MMX_Reg_op mr.
  Proof. unfold modrm_mmx; intros; ins_ibr_sim.
    destruct v as [mr op]. exists mr; congruence.
  Qed.

  Lemma modrm_mmx_rng_inv2 op1 op2: 
    in_bigrammar_rng (` modrm_mmx) (op1,op2) -> 
    (exists mr, op2 = MMX_Reg_op mr) \/ (exists addr, op2 = MMX_Addr_op addr).
  Proof. unfold modrm_mmx; intros; ins_ibr_sim.
    destruct v as [mr op]. eapply modrm_mmx_ret_reg_rng_inv.
    sim; subst. eassumption.
  Qed.

  Local Ltac mmx_pf_sim :=
    ins_ibr_sim; bg_pf_sim;
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

  Local Ltac mmx_invertible_tac := 
    invertible_tac_gen mmx_pf_sim mmx_destruct_var.

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
  Hint Unfold MOVD_env : env_unfold_db.

  Definition MOVD_p : wf_bigrammar (pair_t mmx_operand_t mmx_operand_t).
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
               & _); clear_ast_defs; mmx_invertible_tac.
    - destruct_union;
      destruct v as [d [mr r]]; destruct d; printable_tac; ins_ibr_sim.
  Defined.

  Definition MOVQ_p : wf_bigrammar (pair_t mmx_operand_t mmx_operand_t).
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
             & _); mmx_invertible_tac.
    - destruct v as [d [op1 op2]]; destruct d;
      mmx_pf_sim; printable_tac; ins_ibr_sim. 
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
              & _); mmx_invertible_tac.
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

  Local Ltac sse_destruct_var v := 
    match goal with
      | [ H: match v with | SSE_XMM_Reg_op _ => _ | SSE_MM_Reg_op _ => _
                       | SSE_Addr_op _ => _ | SSE_GP_Reg_op _ => _
                       | SSE_Imm_op _ => _ end
             = _ |- _ ] =>
        destruct v
      | _ => ins_destruct_var v
    end.

  Local Ltac sse_parsable_tac := parsable_tac_gen ins_pf_sim sse_destruct_var.

  Definition SSE_XMM_Reg_op_p: wf_bigrammar sse_operand_t.
    refine (sse_reg @ (fun r => SSE_XMM_Reg_op r : interp sse_operand_t)
                    & (fun op => match op with
                                   | SSE_XMM_Reg_op r => Some r
                                   | _ => None
                                 end)
                    & _); invertible_tac; sse_parsable_tac.
  Defined.

  Definition SSE_GP_Reg_op_p: wf_bigrammar sse_operand_t.
    refine (reg @ (fun r => SSE_GP_Reg_op r : interp sse_operand_t)
                & (fun op => match op with
                               | SSE_GP_Reg_op r => Some r
                               | _ => None
                             end)
                & _); invertible_tac; sse_parsable_tac.
  Defined.

  Definition SSE_MM_Reg_op_p: wf_bigrammar sse_operand_t.
    refine (mmx_reg @ (fun r => SSE_MM_Reg_op r : interp sse_operand_t)
                & (fun op => match op with
                               | SSE_MM_Reg_op r => Some r
                               | _ => None
                             end)
                & _); invertible_tac; sse_parsable_tac.
  Defined.

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
    - sse_parsable_tac.
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
              & _); invertible_tac; sse_parsable_tac.
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
    - sse_parsable_tac.
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
              & _); invertible_tac; sse_parsable_tac.
  Defined.

  Notation modrm_xmm_noreg := modrm_bv2_noreg.
  Notation modrm_mm_noreg := modrm_bv2_noreg.

  Lemma modrm_xmm_ret_reg_rng1 sr1 sr2: 
    in_bigrammar_rng (` modrm_xmm_ret_reg) (sr1, SSE_XMM_Reg_op sr2).
  Proof. intros. unfold modrm_xmm_ret_reg, modrm_gen. ins_ibr_sim. compute [fst].
    exists (inr [|pair_t sse_register_t address_t|] (sr1, sr2)).
    split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_xmm_ret_reg_rng1: ibr_rng_db.

  Lemma modrm_xmm_ret_reg_rng_inv sr op:
    in_bigrammar_rng (` modrm_xmm_ret_reg) (sr,op) -> 
    (exists sr, op = SSE_XMM_Reg_op sr) \/ (exists addr, op = SSE_Addr_op addr).
  Proof. unfold modrm_xmm_ret_reg; intros. ins_ibr_sim.
    destruct v as [[r1 addr] | [r1 r2]]; clear H0.
    - right. crush. 
    - left. crush. 
  Qed.

  Lemma modrm_xmm_rng1 sr1 sr2: 
    in_bigrammar_rng (` modrm_xmm) (SSE_XMM_Reg_op sr1, SSE_XMM_Reg_op sr2).
  Proof. unfold modrm_xmm; intros; ins_ibr_sim. compute [fst].
     exists (sr1, SSE_XMM_Reg_op sr2); split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_xmm_rng1: ibr_rng_db.

  Lemma modrm_xmm_rng_inv1 op1 op2: 
    in_bigrammar_rng (` modrm_xmm) (op1,op2) -> 
    exists sr, op1 = SSE_XMM_Reg_op sr.
  Proof. unfold modrm_xmm; intros; ins_ibr_sim.
    destruct v as [sr op]. exists sr; congruence.
  Qed.

  Lemma modrm_xmm_rng_inv2 op1 op2: 
    in_bigrammar_rng (` modrm_xmm) (op1,op2) -> 
    (exists sr, op2 = SSE_XMM_Reg_op sr) \/ (exists addr, op2 = SSE_Addr_op addr).
  Proof. unfold modrm_xmm; intros; ins_ibr_sim.
    destruct v as [sr op]. eapply modrm_xmm_ret_reg_rng_inv.
    sim; subst. eassumption.
  Qed.

  Lemma modrm_mm_ret_reg_rng1 mr1 mr2: 
    in_bigrammar_rng (` modrm_mm_ret_reg) (mr1, SSE_MM_Reg_op mr2).
  Proof. intros. unfold modrm_mm_ret_reg, modrm_gen. ins_ibr_sim. compute [fst].
    exists (inr [|pair_t sse_register_t address_t|] (mr1, mr2)).
    split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_mm_ret_reg_rng1: ibr_rng_db.

  Lemma modrm_mm_ret_reg_rng_inv mr op:
    in_bigrammar_rng (` modrm_mm_ret_reg) (mr,op) -> 
    (exists mr, op = SSE_MM_Reg_op mr) \/ (exists addr, op = SSE_Addr_op addr).
  Proof. unfold modrm_mm_ret_reg; intros. ins_ibr_sim.
    destruct v as [[r1 addr] | [r1 r2]]; clear H0.
    - right. crush. 
    - left. crush. 
  Qed.

  Lemma modrm_mm_rng1 mr1 mr2: 
    in_bigrammar_rng (` modrm_mm) (SSE_MM_Reg_op mr1, SSE_MM_Reg_op mr2).
  Proof. unfold modrm_mm; intros; ins_ibr_sim. compute [fst].
     exists (mr1, SSE_MM_Reg_op mr2); split; [ins_ibr_sim | trivial].
  Qed.
  Hint Resolve modrm_mm_rng1: ibr_rng_db.

  Lemma modrm_mm_rng_inv1 op1 op2: 
    in_bigrammar_rng (` modrm_mm) (op1,op2) -> 
    exists mr, op1 = SSE_MM_Reg_op mr.
  Proof. unfold modrm_mm; intros; ins_ibr_sim.
    destruct v as [mr op]. exists mr; congruence.
  Qed.

  Lemma modrm_mm_rng_inv2 op1 op2: 
    in_bigrammar_rng (` modrm_mm) (op1,op2) -> 
    (exists mr, op2 = SSE_MM_Reg_op mr) \/ (exists addr, op2 = SSE_Addr_op addr).
  Proof. unfold modrm_mm; intros; ins_ibr_sim.
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
  Defined.

  Definition ext_op_modrm_sse_noreg (bs: string): wf_bigrammar sse_operand_t.
    intros;
    refine(ext_op_modrm_noreg_ret_addr bs
             @ (SSE_Addr_op: [|address_t|] -> [|sse_operand_t|])
             & SSE_Addr_op_inv & _); unfold SSE_Addr_op_inv; invertible_tac;
    sse_parsable_tac.
  Defined.

  Local Ltac sse_pf_sim :=
    ins_ibr_sim; bg_pf_sim;
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

  Local Ltac sse_invertible_tac := invertible_tac_gen sse_pf_sim sse_destruct_var.

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
              & _); sse_invertible_tac.
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
             & _); sse_invertible_tac.
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
              & _); sse_invertible_tac.
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
             & _); sse_invertible_tac.
    - destruct v as [d [op1 op2]]; 
      destruct d; sse_pf_sim; printable_tac; ins_ibr_sim.
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
              & _); sse_invertible_tac.
    - destruct v as [d [op1 op2]]; 
      destruct d; sse_pf_sim; printable_tac; ins_ibr_sim.
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
              & _); sse_invertible_tac.
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
              & _); sse_invertible_tac.
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
              & _); sse_invertible_tac.
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
              & _); sse_invertible_tac.
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
              & _); sse_invertible_tac.
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

  (** ** Glue all individual x86 instruction grammars together into one big
         grammar.  *)

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
    Time gen_ast_defs i_instr1_env.
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
               & _); clear_ast_defs; invertible_tac.
     - Time abstract (destruct w; parsable_tac).
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
    Local Ltac gen4 lbl u arg :=
      let ige := eval unfold i_instr4_grammar_env
                 in i_instr4_grammar_env in
      let t := eval unfold i_instr4_grammar_type
                 in i_instr4_grammar_type in
      let f:=gen_rev_case_lbl lbl ige t in
      let f1 := eval simpl in f in
      exact (Some (f1 (fst u, arg))).
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
    Time refine (gr @ (mp: _ -> [|pair_t prefix_t i_instr4_t|])
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
    Time refine (gr @ (mp: _ -> [|pair_t prefix_t i_instr5_t|])
                 & from_instr5
                 & _); clear_ast_defs; unfold from_instr5;
    unfold invertible; split; [unfold printable | unfold parsable];
    compute [snd fst]; intros.
    - abstract ins_com_printable.
    - abstract (destruct w as [p ins]; destruct ins; ins_com_parsable).
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
    - abstract (destruct w; parsable_tac).
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
    - abstract (destruct w; parsable_tac).
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
    - abstract (destruct w; parsable_tac).
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
    - abstract (destruct w; parsable_tac).
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


Todo: integrate the BiGrammar with the rest of the code development

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