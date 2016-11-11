Require Export Coq.Bool.Bool.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List.

Require Import Coq.Strings.String.
Require Import Coq.Structures.OrdersAlt.

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

(* a module for generating the parser for MIPS instructions *)
Module MIPS_PARSER_ARG.
  Require Import MIPSModel.MIPSSyntax.
  Require Import Shared.Bits.
  Local Open Scope Z_scope.
  
  Definition char_p : Set := bool.

  Definition char_dec : forall (c1 c2:char_p), {c1=c2}+{c1<>c2} := bool_dec.

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

  Inductive tipe : Set := 
  | Int_t
  | Register_t
  | BitVector_t : nat -> tipe (* a bit vector of a certain width *)
  | Ioperand_t
  | Joperand_t
  | Reg2_operand_t
  | Reg3_operand_t
  | Reg2sh_operand_t
  | BZ_operand_t
  | Instruction_t
  | UPair_t: tipe -> tipe -> tipe. 

  Definition tipe_eq : forall (t1 t2:tipe), {t1=t2} + {t1<>t2}.
    intros ; decide equality.
    apply eq_nat_dec.
  Defined.

  Definition Shamt5_t := BitVector_t size5.
  Definition Imm16_t := BitVector_t size16.
  Definition Target26_t := BitVector_t size26.

  Fixpoint tipe_m (t:tipe) := 
    match t with 
      | Int_t => Z
      | Register_t => register
      | BitVector_t n => Word.int n
      | Ioperand_t => ioperand
      | Joperand_t => joperand
      | Reg2_operand_t => reg2_operand
      | Reg3_operand_t => reg3_operand
      | Reg2sh_operand_t => reg2sh_operand
      | BZ_operand_t => bz_operand
      | Instruction_t => instr
      | UPair_t t1 t2 => (tipe_m t1 * (tipe_m t2))%type
    end.

  Definition user_type := tipe.
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

End MIPS_PARSER_ARG.

Require Import Coq.Structures.OrdersAlt.
Module CharOrderedTypeAlt <: OrderedTypeAlt.
  Definition t : Type := MIPS_PARSER_ARG.char_p.
  Definition compare : t -> t -> comparison := MIPS_PARSER_ARG.char_cmp.

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
