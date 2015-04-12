Require Import Bool.
Require Import ZArith.
Require Import List.

Require Import String.
Require Import Structures.OrdersAlt.

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
  Inductive type : Set := 
  | Int_t : type
  | Register_t : type
  | BitVector_t : nat -> type (* a bit vector of a certain width *)
  (* | Byte_t : type *)
  (* | Half_t : type *)
  (* | Word_t : type *)
  (* | Double_Word_t : type *)
  (* | Ten_Byte_t : type *)
  | Scale_t : type
  | Condition_t : type
  | Address_t : type
  | Operand_t : type
  (* | Fpu_Register_t : type *)
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
  | UPair_t (t1 t2: type) : type. 

  Definition Byte_t := BitVector_t 7.
  Definition Half_t := BitVector_t 15.
  Definition Word_t := BitVector_t 31.
  Definition Double_Word_t := BitVector_t 63.
  Definition Ten_Byte_t := BitVector_t 79.
  Definition Fpu_Register_t := BitVector_t 2.

  Definition tipe := type.
  Definition tipe_eq : forall (t1 t2:tipe), {t1=t2} + {t1<>t2}.
    intros ; decide equality.
    apply eq_nat_dec.
  Defined.

  Fixpoint tipe_m (t:tipe) := 
    match t with 
      | Int_t => Z
      | Register_t => register
      | BitVector_t n => Word.int n
      (* | Byte_t => int8 *)
      (* | Half_t => int16 *)
      (* | Word_t => int32 *)
      (* | Double_Word_t => int64 *)
      (* | Ten_Byte_t => int80 *)
      | Scale_t => scale
      | Condition_t => condition_type
      | Address_t => address
      | Operand_t => operand
      (* | Fpu_Register_t => int3 *)
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
      | UPair_t t1 t2 => ((tipe_m t1) * (tipe_m t2))%type
    end.

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

  Definition user_type := type.
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
