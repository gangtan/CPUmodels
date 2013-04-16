(* Copyright (c) 2012. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

(** A reworking of the parsing functionality -- no semantics or proofs
    yet, but this time, includes a construction of a table-based parser
    (not just a recognizer.)  
*)
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
Require Import Coqlib.  (* for extensionality & proof_irrelevance *)
Require Import List.
Require Import Arith.
Require Import Bool.
Require Import Eqdep.
Require Import Omega.
Require Import Program.
Unset Automatic Introduction.
Set Implicit Arguments.
Open Scope nat_scope.

Module Type NEW_PARSER_ARG.
  (* the type of characters used in the grammar specifications *)
  Parameter char_p : Set.
  (* equality on characters -- should change this to a boolean function,
     paired with a proof that it's an equality so that
     we get faster symbolic computation. *)
  Parameter char_dec : forall (c1 c2:char_p), {c1=c2} + {c1<>c2}.
  (* a name for user types embedded within our AST grammar types. *)
  Parameter user_type : Set.
  (* equality on user type names. *)
  Parameter user_type_dec : forall (t1 t2:user_type), {t1=t2} + {t1<>t2}.
  (* a semantic interpretation function for user type names. *)
  Parameter user_type_denote : user_type -> Set.

  (* when we parse, instead of working in terms of individual characters,
     we work in terms of tokens.   For instance, the x86 grammar is specified
     with characters as bits, and tokens as bytes (8-bits. *)
  Definition token_id := nat.
  (* this is the total number of tokens that we can have -- e.g., for the
     x86 parser it is 256 because they have 8 bits. *)
  Variable num_tokens : nat.
  (* this converts tokens to a list of characters -- it's used only during
     the table construction for the parser. *)
  Variable token_id_to_chars : token_id -> list char_p.
End NEW_PARSER_ARG.

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
  | UPair_t (t1 t2: type) : type. 

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
      | UPair_t t1 t2 => ((tipe_m t1) * (tipe_m t2))%type
    end.
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
End X86_PARSER_ARG.

(******************************************************************************)
(* I would like to put this in a module but alas, the Extraction Implicit     *)
(* stuff breaks then.  So I've had to break this out to top-level.            *)
(******************************************************************************)
(* Module X86_BASE_PARSER(NewParser(PA : NEW_PARSER_ARG). *)
(*Import PA.*)
Import X86_PARSER_ARG.

(** The [type]s for our grammars. *)
Inductive type : Type := 
| Unit_t : type
| Char_t : type
| Void_t : type
| Pair_t : type -> type -> type
| Sum_t : type -> type -> type
| List_t : type -> type
| User_t : user_type -> type.

(** [type] equality is decidable -- we only use this in proofs, so
    we don't need to worry about efficiency. *)  
Definition type_dec : forall (t1 t2:type), {t1=t2} + {t1<>t2}.
  decide equality ; apply user_type_dec.
Defined.

(** [void] is an empty type. *)
Inductive void : Type := .

(** The interpretation of [type]s as Coq [Type]s. *)
Fixpoint interp (t:type) : Type := 
  match t with 
    | Unit_t => unit
    | Char_t => char_p
    | Void_t => void
    | Pair_t t1 t2 => (interp t1) * (interp t2)
    | Sum_t t1 t2 => (interp t1) + (interp t2)
    | List_t t => list (interp t)
    | User_t t => user_type_denote t
  end%type.

(** An [xform] is first-order combinator syntax for a particular class of
    functions that we use in grammars, and in grammar transformations.
    We make the syntax explicit so that we can optimize them before
    turning them into actual functions.
*)
Reserved Notation "t1 ->> t2" (left associativity, at level 69, t2 at next level).
Inductive xform : type -> type -> Type := 
| Xid    : forall t, t ->> t
| Xzero  : forall t, Void_t ->> t
| Xcomp  : forall t1 t2 t3, (t1 ->> t2) -> (t2 ->> t3) -> (t1 ->> t3)
| Xchar  : forall t, char_p -> t ->> Char_t
| Xunit  : forall t, t ->> Unit_t 
| Xempty : forall t1 t2, t1 ->> List_t t2 
| Xpair  : forall t t1 t2, (t ->> t1) -> (t ->> t2) -> (t ->> Pair_t t1 t2)
| Xfst   : forall t1 t2, (Pair_t t1 t2) ->> t1
| Xsnd   : forall t1 t2, (Pair_t t1 t2) ->> t2
| Xinl   : forall t1 t2, t1 ->> (Sum_t t1 t2)    
| Xinr   : forall t1 t2, t2 ->> (Sum_t t1 t2)    
| Xmatch : forall t1 t2 t, (t1 ->> t) -> (t2 ->> t) -> (Sum_t t1 t2 ->> t)
| Xcons  : forall t1 t2, (t1 ->> t2) -> (t1 ->> List_t t2) -> (t1 ->> List_t t2)
| Xmap   : forall t1 t2, (t1 ->> t2) -> (List_t t1 ->> List_t t2)  
where "t1 ->> t2" := (xform t1 t2).

(** These declarations ensure that the types will be erased upon extraction.
    But we must make sure not to ever eliminate these types... *)
Extraction Implicit Xid [t].
Extraction Implicit Xzero [t].
Extraction Implicit Xcomp [t1 t2 t3].
Extraction Implicit Xchar [t].
Extraction Implicit Xunit [t].
Extraction Implicit Xempty [t1 t2].
Extraction Implicit Xpair [t t1 t2].
Extraction Implicit Xfst [t1 t2].
Extraction Implicit Xsnd [t1 t2].
Extraction Implicit Xinl [t1 t2].
Extraction Implicit Xinr [t1 t2].
Extraction Implicit Xmatch [t1 t2 t].
Extraction Implicit Xcons [t1 t2].
Extraction Implicit Xmap [t1 t2].

(** Interpret an [t1 ->> t2] xform as a function [interp t1 -> interp t2]. *)
Fixpoint xinterp t1 t2 (x: t1 ->> t2) : interp t1 -> interp t2 := 
  match x in t1 ->> t2 return interp t1 -> interp t2 with 
    | Xid t => fun (x:interp t) => x
    | Xzero t => fun (x:interp Void_t) => match x with end
    | Xcomp t1 t2 t3 f1 f2 => 
      let f1' := xinterp f1 in 
        let f2' := xinterp f2 in 
          fun (x:interp t1) => f2' (f1' x)
    | Xchar t c => fun (x:interp t) => c
    | Xunit t => fun (x:interp t) => tt
    | Xempty t1 t2 => fun (x:interp t1) => @nil (interp t2)
    | Xpair t t1 t2 f1 f2 => 
      let f1' := xinterp f1 in 
        let f2' := xinterp f2 in 
          fun (x:interp t) => (f1' x, f2' x)
    | Xfst t1 t2 => fun (x:interp (Pair_t t1 t2)) => fst x
    | Xsnd t1 t2 => fun (x:interp (Pair_t t1 t2)) => snd x
    | Xinl t1 t2 => fun (x:interp t1) => inl (interp t2) x
    | Xinr t1 t2 => fun (x:interp t2) => inr (interp t1) x
    | Xmatch t1 t2 t f1 f2 => 
      let f1' := xinterp f1 in 
        let f2' := xinterp f2 in 
      fun (x:interp (Sum_t t1 t2)) => 
        match x with 
          | inl x1 => f1' x1 
          | inr x2 => f2' x2 
        end
    | Xcons t1 t2 f1 f2 => 
      let f1' := xinterp f1 in 
        let f2' := xinterp f2 in 
          fun (x:interp t1) => (f1' x)::(f2' x)
    | Xmap t1 t2 f => 
      let f' := xinterp f in 
        fun (x:interp (List_t t1)) => List.map f' x
  end.
Extraction Implicit xinterp [t1 t2].

(** * Grammars *)
(** Our user-facing [grammar]s, indexed by a [type], reflecting the type of the
    semantic value returned by the grammar when used in parsing. *)
Inductive grammar : type -> Type := 
| Eps : grammar Unit_t
| Zero : forall t, grammar t
| Char : char_p -> grammar Char_t
| Any : grammar Char_t
| Cat : forall t1 t2, grammar t1 -> grammar t2 -> grammar (Pair_t t1 t2)
| Alt : forall t1 t2, grammar t1 -> grammar t2 -> grammar (Sum_t t1 t2)
| Star : forall t, grammar t -> grammar (List_t t)
| Map : forall t1 t2, (interp t1 -> interp t2) -> grammar t1 -> grammar t2
| Xform : forall t1 t2, t1 ->> t2 -> grammar t1 -> grammar t2.
Extraction Implicit Zero [t].
Extraction Implicit Cat [t1 t2].
Extraction Implicit Alt [t1 t2].
Extraction Implicit Star [t].
Extraction Implicit Map [t1 t2].
Extraction Implicit Xform [t1 t2].

(** * Denotation of Grammars *)
(** I'm a little annoyed that I had to break out so many equalities, but
    found this worked a little better for both inversion and proving. *)
Inductive in_grammar : forall t, grammar t -> list char_p -> (interp t) -> Prop := 
| InEps : forall s v, s = nil -> v = tt -> in_grammar Eps s v
| InChar : forall c s v, s = c::nil -> v = c -> in_grammar (Char c) s v
| InAny : forall c s v, s = c::nil -> v = c -> in_grammar Any s v
| InCat : forall t1 t2 (g1:grammar t1) (g2:grammar t2) s1 s2 v1 v2 s v, 
    in_grammar g1 s1 v1 -> in_grammar g2 s2 v2 -> 
    s = s1 ++ s2 -> v = (v1,v2) -> in_grammar (Cat g1 g2) s v
| InAlt_l : forall t1 t2 (g1:grammar t1) (g2:grammar t2) s v1 v, 
    in_grammar g1 s v1 -> v = inl _ v1 -> in_grammar (Alt g1 g2) s v
| InAlt_r : forall t1 t2 (g1:grammar t1) (g2:grammar t2) s v2 v, 
    in_grammar g2 s v2 -> v = inr _ v2 -> in_grammar (Alt g1 g2) s v
| InStar_eps : forall t (g:grammar t) s v, s = nil -> v = nil -> in_grammar (Star g) s v
| InStar_cons : forall t (g:grammar t) s1 v1 s2 v2 s v, 
    in_grammar g s1 v1 -> in_grammar (Star g) s2 v2 -> 
    s1 <> nil -> s = s1 ++ s2 -> v = v1::v2 -> in_grammar (Star g) s v
| InMap : forall t1 t2 (f:interp t1 -> interp t2) (g:grammar t1) s v1 v2, 
    in_grammar g s v1 -> v2 = f v1 -> in_grammar (@Map t1 t2 f g) s v2
| InXform : forall t1 t2 (f: t1 ->> t2) (g:grammar t1) s v1 v2,
    in_grammar g s v1 -> v2 = xinterp f v1 -> in_grammar (Xform f g) s v2.
Hint Constructors in_grammar.

(** * Optimize an [xform]. *)
(** Need some explicit casting to get things to type-check. *)
Definition xcoerce t1 t2 t3 t4 (x:xform t1 t2) : t1 = t3 -> t2 = t4 -> xform t3 t4.
  intros. subst. apply x.
Defined.
Extraction Implicit xcoerce [t1 t2 t3 t4].

(** A note:  It would be much more natural to index [grammar] and [xform] by 
    the corresponding Coq [Type]s instead of my own internal [type] syntax,
    which then has to be interpreted.  In particular, I could get rid of
    the need to use [Extraction Implicit] which is a bit of a hack for 
    getting rid of the [type]s in the extracted code.  However, I wouldn't
    be able to prove these crucial injectivity properties of sums and
    products. *)
Definition eq_pair_fst t1 t2 t3 t4 : (Pair_t t1 t2 = Pair_t t3 t4) -> t3 = t1.
  intros ; injection H. intros. apply (eq_sym H1).
Defined.
Definition eq_pair_snd t1 t2 t3 t4 : (Pair_t t1 t2 = Pair_t t3 t4) -> t4 = t2.
  intros ; injection H. intros. apply (eq_sym H0).
Defined.
Definition eq_sum_fst t1 t2 t3 t4 : (Sum_t t1 t2 = Sum_t t3 t4) -> t3 = t1.
  intros ; injection H. intros. apply (eq_sym H1).
Defined.
Definition eq_sum_snd t1 t2 t3 t4 : (Sum_t t1 t2 = Sum_t t3 t4) -> t4 = t2.
  intros ; injection H. intros. apply (eq_sym H0).
Defined.
Definition list_t_eq : forall t1 t2, (List_t t1 = List_t t2) -> t2 = t1.
  intros. injection H. intro. apply (eq_sym H0).
Defined.
Definition pair_eq_snd t1 t2 t3 t4 : Pair_t t3 t4 = Pair_t t1 t2 -> 
  Pair_t t1 t2 = Pair_t t1 t4.
Proof. intros. injection H. intros ; subst. auto.
Defined.

(** These next two functions reduce [Xpair Xfst Xsnd] to [Xid].  
    It's incredibly tedious to propagate the right types and equations around, 
    so I had to break it into two functions. *)
Definition xpair_fst ta tc (x2:ta->>tc):forall t1 t2, 
  (ta = Pair_t t1 t2) -> ta ->>(Pair_t t1 tc) := 
  match x2 in ta->>tc return forall t1 t2,ta=Pair_t t1 t2 -> ta->>(Pair_t t1 tc) with
    | Xsnd t3 t4 => fun t1 t2 H => xcoerce (Xid _) (eq_sym H) (pair_eq_snd H)
    | x2 => fun t1 t2 H => Xpair (xcoerce (Xfst t1 t2) (eq_sym H) (eq_refl _)) x2
  end.
Extraction Implicit xpair_fst [ta tc t1 t2].

Definition xpair_r ta tb tc (x2:ta ->> tc) : (ta ->> tb) -> ta ->> (Pair_t tb tc) := 
  match x2 in ta ->> tc return ta->>tb -> ta->>(Pair_t tb tc) with
    | Xzero _ => fun x1 => Xzero _
    | x2 => fun x1 => Xpair x1 x2
  end.
Extraction Implicit xpair_r [ta tb tc].

Definition xpair ta tb tc (x1:ta ->> tb) (x2:ta ->> tc) : ta ->> (Pair_t tb tc) := 
 match x1 in ta ->> tb return ta->>tc -> ta->>(Pair_t tb tc) with
   | Xfst t1 t2 => fun x2 => xpair_fst x2 (eq_refl _)
   | Xzero t => fun x2 => Xzero _
   | x1 => fun x2 => xpair_r x2 x1 
  end x2.
Extraction Implicit xpair [ta tb tc].

(** The [xpair] optimization preserves meaning. *)
Lemma xpair_corr ta tb tc (x1:ta->>tb) (x2:ta->>tc) v : 
  xinterp (xpair x1 x2) v = xinterp (Xpair x1 x2) v.
Proof.
  Ltac xpair_corr_simp := 
    match goal with | [ H : void |- _ ] => destruct H | _ => auto end.  
  destruct x1 ; simpl in * ; auto ; intros ; xpair_corr_simp ; 
  dependent destruction x2 ; simpl in * ; xpair_corr_simp.
  destruct v. auto.
Qed.

Definition xmatch_inl t1 t2 tb tc (x2:tb->>tc) : 
  (tc=Sum_t t1 t2) -> Sum_t t1 tb ->> Sum_t t1 t2.
refine (fun t1 t2 tb tc x2 => 
  match x2 in tb->>tc return (tc=Sum_t t1 t2) -> Sum_t t1 tb ->> Sum_t t1 t2 with
    | Xinr t1' t2' => fun H => xcoerce (Xid (Sum_t t1' t2')) _ H
    | x2' => fun H => Xmatch (Xinl t1 t2) (xcoerce x2' (eq_refl _) H)
  end
). injection H ; intros ; subst. auto.
Defined.
Extraction Implicit xmatch_inl [t1 t2 tb tc].

(** This function and the two above implement the reduction
    [match x with inl a => inl a | inr b => inr b end = id]. *)
Definition xmatch ta tb tc (x1:ta->>tc) (x2:tb->>tc) : Sum_t ta tb ->> tc := 
  match x1 in ta->>tc return tb->>tc -> Sum_t ta tb ->> tc with
    | Xinl t1 t2 => fun x2' => xmatch_inl x2' (eq_refl _)
    | x1' => Xmatch x1'
  end x2.
Extraction Implicit xmatch [ta tb tc].

(** Correctness of eta-reduction for sums. *)
Lemma xmatch_corr ta tb tc (x1:ta->>tc) (x2:tb->>tc) v : 
  xinterp (xmatch x1 x2) v = xinterp (Xmatch x1 x2) v.
Proof.
  destruct x1 ; simpl ; auto ; intros. dependent destruction x2 ; simpl ; destruct v ; 
  auto.
Qed.

(** These next few functions implement specific reductions for when a particular
    combinator is composed with another.  
*)
(** (f1, f2) o id = (f1, f2)
    (f1, f2) o (char c) = char c
    (f1, f2) o unit = unit
    (f1, f2) o empty = empty
    (f1, f2) o fst = f1
    (f1, f2) o snd = f2
    (f1, f2) o (g1, g2) = ((f1, f2) o g1, (f1, f2) o g2)
*)
Definition xcomp_pair t21 t22 (x2:t21 ->> t22) : 
  forall ta tb tc (x11:ta->>tb) (x12:ta->>tc), (Pair_t tb tc = t21) -> ta ->> t22 := 
    match x2 in t21 ->> t22 return
      forall ta tb tc (x11:ta->>tb) (x12:ta->>tc), (Pair_t tb tc = t21) -> ta ->> t22 with
      | Xid t => fun ta tb tc x11 x12 H => xcoerce (Xpair x11 x12) (eq_refl _) H
      | Xchar t c => fun ta tb tc x11 x12 H => Xchar _ c
      | Xunit t => fun ta tb tc x11 x12 H => Xunit _
      | Xempty t1 t2 => fun ta tb tc x11 x12 H => Xempty _ _
      | Xfst te tf =>
        fun ta tb tc x11 x12 H => xcoerce x11 (eq_refl _) (eq_pair_fst (eq_sym H))
      | Xsnd te tf => 
        fun ta tb tc x11 x12 H => xcoerce x12 (eq_refl _) (eq_pair_snd (eq_sym H))
      | Xpair u1 u2 u3 x21 x22 => 
        fun ta tb tc x11 x12 H => 
          Xpair (Xcomp (Xpair x11 x12) (xcoerce x21 (eq_sym H) (eq_refl _))) 
                (Xcomp (Xpair x11 x12) (xcoerce x22 (eq_sym H) (eq_refl _)))
      | x2' => 
        fun ta tb tc x11 x12 H => 
          Xcomp (Xpair x11 x12) (xcoerce x2' (eq_sym H) (eq_refl _))
    end.
Extraction Implicit xcomp_pair [t21 t22 ta tb tc].

(** [xcomp_pair] is correct. *)
Lemma xcomp_pair_corr t21 t22 (x2:t21->>t22) ta tb tc (x11:ta->>tb) (x12:ta->>tc) H v: 
  xinterp (xcomp_pair x2 x11 x12 H) v = 
  xinterp (Xcomp (Xpair x11 x12) (xcoerce x2 (eq_sym H) (eq_refl _))) v.
Proof.
  destruct x2 ; simpl ; intros ; subst ; simpl ; auto ; injection H ; intros ; subst ; 
    rewrite (proof_irrelevance _ H (eq_refl _)) ; auto.
Qed.

(**  inl o id = inl
     inl o (char c) = char c
     inl o unit = unit
     inl o empty = empty
     inl o (match f1 f2) = f o f1 
*)
Definition xcomp_inl t21 t22 (x2:t21 ->> t22) : 
  forall ta tb, (Sum_t ta tb = t21) -> ta ->> t22 :=
    match x2 in t21->>t22 return 
      forall ta tb, (Sum_t ta tb = t21) -> ta ->> t22 with
      | Xid t => fun ta tb H => xcoerce (Xinl _ _) (eq_refl _) H 
      | Xchar t c => fun ta tb H => Xchar _ c
      | Xunit t => fun ta tb H => Xunit _
      | Xempty t1 t2 => fun ta tb H => Xempty _ _ 
      | Xmatch td te tf x21 x22 => 
        fun ta tb H => xcoerce x21 (eq_sum_fst H) (eq_refl _)
      | x2' => 
        fun ta tb H => Xcomp (Xinl _ _) (xcoerce x2' (eq_sym H) (eq_refl _))
    end.
Extraction Implicit xcomp_inl [t21 t22 ta tb].

(** [xcomp_inl] is correct *)
Lemma xcomp_inl_corr t21 t22 (x2:t21->>t22) ta tb (H:Sum_t ta tb = t21) v: 
  xinterp (xcomp_inl x2 H) v = 
  xinterp (Xcomp (Xinl _ _) (xcoerce x2 (eq_sym H) (eq_refl _))) v.
Proof.
  destruct x2 ; simpl ; intros ; subst ; simpl ; auto. injection H ; intros ; subst.
  rewrite (proof_irrelevance _ H (eq_refl _)). auto.
Qed.

(**  (inr f) o id = inr f
     (inr f) o (char c) = char c
     (inr f) o unit = unit
     (inr f) o empty = empty
     (inr f) o (match f1 f2) = f o f2
*)
Definition xcomp_inr t21 t22 (x2:t21 ->> t22) : 
  forall ta tb, (Sum_t ta tb = t21) -> tb ->> t22 :=
    match x2 in t21->>t22 return 
      forall ta tb, (Sum_t ta tb = t21) -> tb ->> t22 with
      | Xid t => fun ta tb H => xcoerce (Xinr _ _) (eq_refl _) H 
      | Xchar t c => fun ta tb H => Xchar _ c
      | Xunit t => fun ta tb H => Xunit _
      | Xempty t1 t2 => fun ta tb H => Xempty _ _ 
      | Xmatch td te tf x21 x22 => 
        fun ta tb H => xcoerce x22 (eq_sum_snd H) (eq_refl _)
      | x2' => 
        fun ta tb H => Xcomp (Xinr _ _) (xcoerce x2' (eq_sym H) (eq_refl _))
    end.
Extraction Implicit xcomp_inr [t21 t22 ta tb].

(** [xcomp_inr] is correct. *)
Lemma xcomp_inr_corr t21 t22 (x2:t21->>t22) ta tb (H:Sum_t ta tb = t21) v: 
  xinterp (xcomp_inr x2 H) v = 
  xinterp (Xcomp (Xinr _ _) (xcoerce x2 (eq_sym H) (eq_refl _))) v.
Proof.
  destruct x2 ; simpl ; intros ; subst ; simpl ; auto. injection H ; intros ; subst.
  rewrite (proof_irrelevance _ H (eq_refl _)). auto.
Qed.

(**  (map f) o id = map f
     (map f) o (char c) = char c
     (map f) o unit = unit
     (map f) o empty = empty
     (map f) o (map g) = map (f o g) 
*)
Definition xcomp_map t21 t22 (x2:t21 ->> t22) : 
  forall ta tb (x11:ta->>tb), (List_t tb = t21) -> (List_t ta) ->> t22 := 
    match x2 in t21 ->> t22 return 
      forall ta tb (x11:ta->>tb), (List_t tb = t21) -> (List_t ta) ->> t22 with
      | Xid t => 
          fun ta tb x11 H => xcoerce (Xmap x11) (eq_refl _) H
      | Xchar t c => fun ta tb _ H => Xchar _ c
      | Xunit t => fun ta tb _ H => Xunit _
      | Xempty t1 t2 => fun ta tb _ H => Xempty _ _ 
      | Xmap tc td x21 => 
          fun ta tb x11 H => Xmap (Xcomp x11 (xcoerce x21 (list_t_eq H) (eq_refl _)))
      | x2' => 
          fun ta tb x11 H => Xcomp (Xmap x11) (xcoerce x2' (eq_sym H) (eq_refl _))
    end.
Extraction Implicit xcomp_map [t21 t22 ta tb].

(** [xcomp_map] is correct. *)
Lemma xcomp_map_corr t21 t22 (x2:t21->>t22) ta tb (x11:ta->>tb) (H:List_t tb = t21) v : 
  xinterp (xcomp_map x2 x11 H) v = 
  xinterp (Xcomp (Xmap x11) (xcoerce x2 (eq_sym H) (eq_refl _))) v.
Proof.
  destruct x2 ; simpl ; intros ; subst ; simpl ; auto. injection H ; intros ; subst.
  rewrite (proof_irrelevance _ H (eq_refl _)). unfold list_t_eq. simpl. 
  unfold xcoerce. unfold eq_rec_r. simpl. rewrite map_map. auto.
Qed.

(** empty o id = id
    empty o (char c) = char c
    empty o unit = unit
    empty o empty = empty
    empty o (map f) = empty
*)
Definition xcomp_empty t21 t22 (x2:t21 ->> t22) : 
  forall ta tb, (List_t tb = t21) -> ta ->> t22 := 
    match x2 in t21 ->> t22 return forall ta tb, (List_t tb = t21) -> ta ->> t22 with
      | Xid t => fun ta tb H => xcoerce (Xempty ta tb) (eq_refl _) H
      | Xchar t c => fun ta tb H => Xchar _ c
      | Xunit t => fun ta tb H => Xunit _
      | Xempty t1 t2 => fun ta tb H => Xempty _ _ 
      | Xmap tc td f => fun ta tb H => Xempty _ _
      | x2' => fun ta tb H => Xcomp (Xempty _ _) (xcoerce x2' (eq_sym H) (eq_refl _))
    end.
Extraction Implicit xcomp_empty [t21 t22 ta tb].

(** [xcomp_empty] is correct. *)
Lemma xcomp_empty_corr t21 t22 (x2:t21->>t22) ta tb (H:List_t tb = t21) v : 
  xinterp (xcomp_empty x2 ta H) v = 
  xinterp (Xcomp (Xempty _ _) (xcoerce x2 (eq_sym H) (eq_refl _))) v.
Proof.
  destruct x2 ; simpl ; intros ; subst ; simpl ; auto. injection H ; intros ; subst.
  rewrite (proof_irrelevance _ H (eq_refl _)). auto.
Qed.

(** (cons f1 f2) o id = (cons f1 f2)
    (cons f1 f2) o (char c) = char c
    (cons f1 f2) o unit = unit
    (cons f1 f2) o empty = empty
    (cons f1 f2) o (map f) = cons (f1 o f) (f2 o (map f))
*)
Definition xcomp_cons t21 t22 (x2:t21 ->> t22) : 
  forall ta tb (x11:ta->>tb) (x12:ta->>List_t tb), (List_t tb = t21) -> ta ->> t22 := 
    match x2 in t21 ->> t22 return
      forall ta tb (x11:ta->>tb) (x12:ta->>List_t tb), (List_t tb = t21) -> ta ->> t22 with
      | Xid t => fun ta tb x11 x12 H => xcoerce (Xcons x11 x12) (eq_refl _) H
      | Xchar t c => fun ta tb x11 x12 H => Xchar _ c
      | Xunit t => fun ta tb x11 x12 H => Xunit _
      | Xempty tc td => fun ta tb x11 x12 H => Xempty _ _
      | Xmap tc td x => fun ta tb x11 x12 H => 
        Xcons (Xcomp x11 (xcoerce x (list_t_eq H) (eq_refl _))) 
        (Xcomp x12 (xcoerce (Xmap x) (eq_sym H) (eq_refl _)))
      | x2' => fun ta tb x11 x21 H => 
        Xcomp (Xcons x11 x21) (xcoerce x2' (eq_sym H) (eq_refl _))
    end.
Extraction Implicit xcomp_cons [t21 t22 ta tb].

(** [xcomp_cons] is correct. *)
Lemma xcomp_cons_corr t21 t22 (x2:t21->>t22) ta tb (x11:ta->>tb) (x12:ta->>List_t tb) H v: 
  xinterp (xcomp_cons x2 x11 x12 H) v = xinterp (Xcomp (Xcons x11 x12) (xcoerce x2 (eq_sym H) (eq_refl _))) v.
Proof.
  destruct x2 ; simpl ; intros ; subst ; simpl ; auto. injection H. intros. subst.
  rewrite (proof_irrelevance _ H (eq_refl _)). simpl. unfold list_t_eq. simpl. 
  unfold xcoerce. unfold eq_rec_r. simpl. auto.
Qed.

(** Cut eliminations on the right here:
     f o id = f
     f o (char c) = char c
     f o unit = unit
     f o empty = empty
*)
Definition xcomp_r t21 t22 (x2:t21 ->> t22) : forall t11, t11 ->> t21 -> t11 ->> t22 :=
  match x2 in t21 ->> t22 return forall t11, t11 ->> t21 -> t11 ->> t22 with
    | Xid t => fun t1 x1 => x1
    | Xchar t c => fun t1 x1 => Xchar _ c
    | Xunit t => fun t1 x1 => Xunit _
    | Xempty t1 t2 => fun t1 x1 => Xempty _ _
    | Xpair t t21 t22 x21 x22 => fun t1 x1 => Xpair (Xcomp x1 x21) (Xcomp x1 x22)
    | x2' => fun t1 x1 => Xcomp x1 x2'
  end.
Extraction Implicit xcomp_r [t21 t22 t11].

(** [xcomp_r] is correct. *)
Lemma xcomp_r_corr t21 t22 (x2:t21->>t22) t11 (x1:t11->>t21) v : 
  xinterp (xcomp_r x2 x1) v = xinterp (Xcomp x1 x2) v.
Proof.
  induction x2 ; simpl ; intros ; auto.
Qed.

(** Optimization for composition of combinators, takes advantage
    of all of the specialized functions above, plus a few more:
     id o f = f
     zero o f = zero
     (f1 o f2) o f3 = f1 o (f2 o f3)
     (match f1 f2) o f3 = match (f1 o f3) (f2 o f3)
     plus the reductions in the functions above
*)
Fixpoint xcomp t11 t12 (x1:t11 ->> t12) : forall t22, t12 ->> t22 -> t11 ->> t22 := 
    match x1 in t11 ->> t12 return forall t22, t12 ->> t22 -> t11 ->> t22 with
      | Xid _ => fun t22 x2 => x2
      | Xzero _ => fun t22 x2 => Xzero t22
      | Xcomp ta tb tc x11 x12 => 
        fun t22 x2 => xcomp x11 (xcomp x12 x2)
      | Xpair ta tb tc x11 x12 => 
        fun t22 x2 => xcomp_pair x2 x11 x12 (eq_refl _)
      | Xinl ta tb => fun t22 x2 => xcomp_inl x2 (eq_refl _)
      | Xinr ta tb => fun t22 x2 => xcomp_inr x2 (eq_refl _)
      | Xmap ta tb x11 => fun t22 x2 => xcomp_map x2 x11 (eq_refl _)
      | Xempty ta tb => fun t22 x2 => xcomp_empty x2 _ (eq_refl _)
      | Xcons ta tb x11 x12 => fun t22 x2 => xcomp_cons x2 x11 x12 (eq_refl _)
      | Xmatch ta tb tc x11 x12 => fun t22 x2 => Xmatch (xcomp x11 x2) (xcomp x12 x2)
      | x1' => fun t22 x2 => xcomp_r x2 x1'
    end.
Extraction Implicit xcomp [t11 t12 t22].

(** [xcomp] is correct. *)
Lemma xcomp_corr t1 t2 (x1:t1->>t2) t3 (x2:t2->>t3) v : 
  xinterp (xcomp x1 x2) v = xinterp (Xcomp x1 x2) v.
Proof.
  induction x1 ; simpl ; intros ; auto ; 
  match goal with 
    | [ v : void |- _ ] => destruct v
    | [ |- xinterp (xcomp_r ?x2 ?x1) ?v = _ ] => apply (xcomp_r_corr x2 x1 v)
    | _ => idtac
  end.
  simpl in *. rewrite <- IHx1_2. rewrite <- IHx1_1. auto.
  apply xcomp_empty_corr. apply xcomp_pair_corr.  apply xcomp_inl_corr.
  apply xcomp_inr_corr. destruct v ; auto. rewrite IHx1_1. auto. rewrite IHx1_2. auto.
  apply xcomp_cons_corr. apply xcomp_map_corr.
Qed.

(** The [xcomp'] function is an extra loop to try to get more reductions
    to fire. *)
Fixpoint xcomp' tb tc (x2:tb->>tc) : forall ta, ta->>tb -> ta->>tc := 
  match x2 in tb->>tc return forall ta, ta->>tb -> ta->>tc with 
    | Xcomp td te tf x21 x22 => fun ta x1 => xcomp' x22 (xcomp' x21 x1)
    | Xpair td te tf x21 x22 => fun ta x1 => Xpair (xcomp' x21 x1) (xcomp' x22 x1)
    | x2' => fun ta x1 => xcomp x1 x2'
  end.
Extraction Implicit xcomp' [tb tc ta].

Lemma xcomp'_corr tb tc (x2:tb->>tc) ta (x1:ta->>tb) v : 
  xinterp (xcomp' x2 x1) v = xinterp (Xcomp x1 x2) v.
Proof.
  induction x2 ; simpl ; intros ; auto ; try (rewrite xcomp_corr ; auto).
  rewrite IHx2_2. simpl. rewrite IHx2_1. auto. 
  rewrite IHx2_1. rewrite IHx2_2. auto.
Qed.

(** Optimize an [xform].  Most of the reductions are in the
    [Xcomp] (composition) case, though there are a couple of
    eta reductions for [Xpair] and [Xmatch] respectively. *)
Fixpoint xopt t1 t2 (x:t1 ->> t2) : t1 ->> t2 := 
  match x with
    | Xpair ta tb tc x1 x2 => xpair (xopt x1) (xopt x2)
    | Xmatch ta tb tc x1 x2 => xmatch (xopt x1) (xopt x2)
    | Xcomp ta tb tc x1 x2 => xcomp' (xopt x2) (xopt x1) 
    | Xcons ta tb x1 x2 => Xcons (xopt x1) (xopt x2)
    | Xmap ta tb x1 => Xmap (xopt x1)
    | x' => x'
  end.
Extraction Implicit xopt [t1 t2].

(** [xopt] is correct. *)
Lemma xopt_corr t1 t2 (x:t1 ->> t2) : xinterp (xopt x) = xinterp x.
Proof.
  induction x ; simpl ; intros ; auto ; try (rewrite <- IHx ; auto) ; 
    try (rewrite <- IHx1 ; rewrite <- IHx2 ; auto) ; apply extensionality ; intros.
  apply xcomp'_corr. apply xpair_corr. apply xmatch_corr.
Qed.

(** * Optimizing constructors for grammars.  These try to reduce the
      grammar, but must make adjustments to the semantic actions.  We 
      use optimized transforms to get this effect. *)

(** g ++ 0 ==> g @ inl *)
Definition OptAlt_r t2 (g2:grammar t2) : forall t1, grammar t1 -> grammar (Sum_t t1 t2) :=
  match g2 in grammar t2' return forall t1, grammar t1 -> grammar (Sum_t t1 t2') with
    | Zero t2 => fun t1 g1 => Xform (Xinl _ _) g1
    | g2' => fun t1 g1 => Alt g1 g2'
  end.
Extraction Implicit OptAlt_r [t2 t1].

(** 0 ++ g ==> g @ inr *)
Definition OptAlt_l t1 (g1:grammar t1) : forall t2, grammar t2 -> grammar (Sum_t t1 t2) :=
  match g1 in grammar t1' return forall t2, grammar t2 -> grammar (Sum_t t1' t2) with
    | Zero t1 => fun t2 g2 => Xform (Xinr _ _) g2
    | g1' => fun t2 g2 => OptAlt_r g2 g1'
  end.
Extraction Implicit OptAlt_l [t1 t2].

(** We would like to reduce (g ++ g) ==> g but this loses information and
    turns a potentially ambiguous grammar into one that is not.  More 
    importantly, we can't actually compare grammars for equality because
    we are trying to keep the [type] index computationally irrelevant.
*)
Definition OptAlt t1 t2 (g1:grammar t1) (g2:grammar t2) := OptAlt_l g1 g2.
Extraction Implicit OptAlt [t1 t2].

(** g $ 0 ==> 0 @ zero_to_t
    g $ eps ==> g @ add_unit_r *)
Definition OptCat_r t2 (g2:grammar t2) : forall t1, grammar t1 -> grammar (Pair_t t1 t2) :=
  match g2 in grammar t2' return forall t1, grammar t1 -> grammar (Pair_t t1 t2') with
    | Zero t2' => fun t1 (g2 : grammar t1) => Zero _
    | Eps => fun t1 (g1 : grammar t1) => Xform (Xpair (Xid _) (Xunit _)) g1
    | g2' => fun t1 (g1 : grammar t1) => Cat g1 g2'
  end.
Extraction Implicit OptCat_r [t2 t1].

(** 0 $ g ==> 0 @ zero_to_t
    eps $ g ==> g @ add_unit_l *)
Definition OptCat t1 (g1:grammar t1) : forall t2, grammar t2 -> grammar (Pair_t t1 t2) :=
  match g1 in grammar t1' return forall t2, grammar t2 -> grammar (Pair_t t1' t2) with
    | Zero t1' => fun t2 (g2 : grammar t2) => Zero _
    | Eps => fun t2 (g2 : grammar t2) => Xform (Xpair (Xunit _) (Xid _)) g2
    | g1' => fun t2 (g2 : grammar t2) => OptCat_r g2 g1'
  end.
Extraction Implicit OptCat [t1 t2].

(** star (star g) ==> (star g) @ mklist
    star eps ==> eps @ to_empty_list
    star 0 ==> eps @ to_empty_list 
*)
Definition OptStar t (g:grammar t) : grammar (List_t t) := 
  match g in grammar t' return grammar (List_t t') with
    | Star u g' => Xform (Xcons (Xid _) (Xempty _ _)) (Star g')
    | Eps => Xform (Xempty _ _) Eps
    | Zero t => Xform (Xempty _ _) Eps
    | g' => Star g'
  end.
Extraction Implicit OptStar [t].

(** 0 @ f ==> 0
    g @ f1 @ f2 ==> g @ (f1 o f2)
*)
Definition OptMap' t1 (g:grammar t1) : forall t2, (interp t1 -> interp t2) -> grammar t2 := 
  match g in grammar t1' return forall t2, (interp t1' -> interp t2) -> grammar t2 with
    | Zero t => fun t2 f => Zero t2
    | Map u1 u2 f' g' => fun t2 f => @Map u1 t2 (fun x => f (f' x)) g'
    | g' => fun t2 f => @Map _ t2 f g'
  end.
Extraction Implicit OptMap' [t1 t2].

Definition OptMap t1 t2 (f:interp t1 -> interp t2) (g:grammar t1) : grammar t2 := 
  @OptMap' t1 g t2 f.
Extraction Implicit OptMap [t1 t2].

Definition OptXform' t1 (g:grammar t1) : forall t2, t1->>t2 -> grammar t2 :=
  match g in grammar t1' return forall t2, t1'->>t2 -> grammar t2 with
    | Zero t => fun t2 x => Zero t2
    | Xform u1 u2 x' g' => fun t2 x => Xform (xcomp x' x) g'
    | g' => fun t2 x => Xform x g'
  end.
Extraction Implicit OptXform' [t1 t2].

Definition OptXform t1 t2 (x:t1->>t2) (g:grammar t1) := @OptXform' t1 g t2 x.
Extraction Implicit OptXform [t1 t2].

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

(** Explicit inversion principles for the grammars -- needed because
    of typing dependencies, though a little awkward that we can't just
    use [dependent inversion] to solve them. *)
Lemma EpsInv : forall cs v, in_grammar Eps cs v -> cs = nil /\ v = tt.
  intros. inversion H ; mysimp.
Qed.
Lemma AnyInv : forall cs v, in_grammar Any cs v -> cs = v::nil.
  intros. inversion H ; subst ; mysimp.
Qed.
Lemma CharInv : forall c cs v, in_grammar (Char c) cs v -> cs = c::nil /\ v = c.
  intros. inversion H ; subst ; mysimp.
Qed.
Lemma CatInv : forall t1 t2 (g1:grammar t1) (g2:grammar t2) cs v, 
  in_grammar (Cat g1 g2) cs v -> 
  exists cs1, exists cs2, exists v1, exists v2, 
    in_grammar g1 cs1 v1 /\ in_grammar g2 cs2 v2 /\ cs = cs1++cs2 /\ v = (v1,v2).
Proof.
  intros. inversion H ; subst ; mysimp. repeat econstructor ; eauto.
Qed.
Lemma AltInv : forall t1 t2 (g1:grammar t1) (g2:grammar t2) cs v, 
  in_grammar (Alt g1 g2) cs v -> 
  (exists v1, in_grammar g1 cs v1 /\ v = inl _ v1) \/
  (exists v2, in_grammar g2 cs v2 /\ v = inr _ v2).
Proof.
  intros ; inversion H ; subst ; mysimp ; [ left | right ] ; econstructor ; eauto.
Qed.
Lemma StarInv : forall t (g:grammar t) cs v, 
  in_grammar (Star g) cs v -> (cs = nil /\ v = nil) \/ 
  (exists cs1, exists v1, exists cs2, exists v2, 
    cs1 <> nil /\ in_grammar g cs1 v1 /\ in_grammar (Star g) cs2 v2 /\ 
    cs = cs1 ++ cs2 /\ v = v1::v2).
Proof.
  intros ; inversion H ; clear H ; subst ; mysimp ; right ; exists s1 ; exists v1 ; 
  exists s2 ; exists v2 ; auto.
Qed.
Lemma MapInv : forall t1 t2 (f:interp t1 -> interp t2) (g:grammar t1) cs v,
  in_grammar (@Map t1 t2 f g) cs v -> exists v', in_grammar g cs v' /\ v = f v'.
Proof.
  intros ; inversion H ; subst ; mysimp ; eauto. 
Qed.
Lemma ZeroInv : forall t cs v, in_grammar (Zero t) cs v -> False.
  intros ; inversion H.
Qed.
Lemma XformInv : forall t1 t2 (x:t1->>t2) (g:grammar t1) cs v,
  in_grammar (Xform x g) cs v -> exists v', in_grammar g cs v' /\ v = xinterp x v'.
Proof.
  intros ; inversion H ; mysimp. exists v1. auto.
Qed.

(** Tactic for invoking inversion principles on a proof that some string
    and value are in the denotation of a grammar.  We don't unroll the 
    [Star] case because that would loop. *)
Ltac in_inv := 
  repeat 
    match goal with 
      | [ H : in_grammar Eps _ _ |- _ ] => generalize (EpsInv H) ; clear H
      | [ H : in_grammar Any _ _ |- _ ] => generalize (AnyInv H) ; clear H
      | [ H : in_grammar (Char _) _ _ |- _ ] => generalize (CharInv H) ; clear H
      | [ H : in_grammar (Alt _ _) _ _ |- _ ] => generalize (AltInv H) ; clear H
      | [ H : in_grammar (Cat _ _) _ _ |- _ ] => generalize (CatInv H) ; clear H
      | [ H : in_grammar (Zero _) _ _ |- _ ] => contradiction (ZeroInv H)
      | [ H : in_grammar (Map _ _ _) _ _ |- _ ] => generalize (MapInv H) ; clear H
      | [ H : in_grammar (Xform _ _) _ _ |- _ ] => generalize (XformInv H) ; clear H
      | _ => mysimp ; subst ; eauto
    end.

(** Correctness proofs for the optimizing grammar constructors. *)
Lemma opt_alt_corr : forall t1 t2 (g1:grammar t1) (g2:grammar t2) s v, 
    in_grammar (Alt g1 g2) s v <-> in_grammar (OptAlt g1 g2) s v.
Proof.
  destruct g1 ; destruct g2 ; simpl ; try tauto ; repeat mysimp ; in_inv.
Qed.

Lemma in_cat_eps : forall t (g:grammar t) s v1 v, in_grammar g s v1 -> v = (v1,tt) -> 
  in_grammar (Cat g Eps) s v.
Proof.
  intros ; econstructor ; eauto. apply app_nil_end.
Qed.
Hint Resolve in_cat_eps.

Lemma opt_cat_corr : forall t1 t2 (g1:grammar t1) (g2:grammar t2) s v,
  in_grammar (Cat g1 g2) s v <-> in_grammar (OptCat g1 g2) s v.
Proof.
  destruct g1 ; destruct g2 ; simpl ; try tauto ; repeat mysimp ; in_inv.
Qed.

Lemma opt_map_corr : forall t1 t2 (f:interp t1 -> interp t2) (g:grammar t1) s v,
  in_grammar (@Map t1 t2 f g) s v <-> in_grammar (@OptMap t1 t2 f g) s v.
Proof.
  destruct g ; simpl ; try tauto ; repeat mysimp; in_inv.
Qed.

Lemma opt_xform_corr : forall t1 t2 (x:t1->>t2) (g:grammar t1) s v,
  in_grammar (Xform x g) s v <-> in_grammar (OptXform x g) s v.
Proof.
  destruct g ; simpl ; try tauto ; repeat mysimp ; in_inv ;
  eapply InXform ; eauto ; rewrite xcomp_corr ;auto.
Qed.

(** Conceptually, returns [Eps] if [g] accepts the empty string, and 
    [Zero] otherwise.  In practice, we won't get exactly [Eps] since
    we could have [Map]s, [Xform]s, etc. in there. *)
Fixpoint null t (g:grammar t) : grammar t := 
  match g in grammar t' return grammar t' with
    | Zero t => Zero t
    | Eps => Eps
    | Any => Zero _
    | Char c => Zero _
    | Alt t1 t2 g1 g2 => OptAlt (null g1) (null g2)
    | Cat t1 t2 g1 g2 => OptCat (null g1) (null g2)
    | Map t1 t2 f g => OptMap t2 f (null g)
    | Xform t1 t2 x g => OptXform x (null g)
    | Star t g => Xform (Xempty _ _) Eps
  end.
Extraction Implicit null [t].

(** Computes the derivative of [g] with respect to [c]. Denotationally,
    this is { (s,v) | (c::s,v) in_grammar[g] }. *)
Fixpoint deriv t (g:grammar t) (c:char_p) : grammar t := 
  match g in grammar t' return grammar t' with
    | Zero t => Zero t
    | Eps => Zero Unit_t
    | Char c' => if char_dec c c' then Xform (Xchar _ c') Eps else Zero _
    | Any => Xform (Xchar _ c) Eps
    | Alt t1 t2 g1 g2 => OptAlt (deriv g1 c) (deriv g2 c)
    | Map t1 t2 f g => OptMap t2 f (deriv g c)
    | Xform t1 t2 x g => OptXform x (deriv g c)
    | Cat t1 t2 g1 g2 => 
        OptXform (Xmatch (Xid _) (Xid _))
          (OptAlt (OptCat (deriv g1 c) g2) (OptCat (null g1) (deriv g2 c)))
    | Star t g => 
        OptXform (Xcons (Xfst _ _) (Xsnd _ _)) (OptCat (deriv g c) (Star g))
  end.
Extraction Implicit deriv [t].

(** * AST Grammars *)

(** An [astgram] is similar to a grammar except that it has no [Map] or [Xform] 
    constructor, and it's not indexed by a [type].  Rather, we can compute the 
    expected [type] from the grammar itself which is effectively a polynomial 
    type representing an abstract syntax tree.  Below, we translate a [grammar] 
    to a pair of an [astgram] and a function that takes the result of the 
    [astgram] and maps it to the semantic values we would get back, given the 
    initial [grammar].  In essence, this lifts all of the semantic actions to
    the top-level, allowing us to only manipulate [astgram]s.  *)
Inductive astgram : Set := 
| aEps : astgram
| aZero : astgram
| aChar : char_p -> astgram
| aAny : astgram
| aCat : astgram -> astgram -> astgram
| aAlt : astgram -> astgram -> astgram
| aStar : astgram -> astgram.

Definition astgram_dec : forall (a1 a2:astgram), {a1=a2} + {a1<>a2}.
  decide equality. apply char_dec.
Defined.

(** Compute the return [type] of an [astgram]. *)
Fixpoint astgram_type (pg : astgram) : type := 
  match pg with 
    | aEps => Unit_t
    | aZero => Void_t
    | aChar _ => Char_t
    | aAny => Char_t
    | aCat pg1 pg2 => Pair_t (astgram_type pg1) (astgram_type pg2)
    | aAlt pg1 pg2 => Sum_t (astgram_type pg1) (astgram_type pg2)
    | aStar pg => List_t (astgram_type pg)
  end.

(** Semantics of [astgram]s -- same as for grammars. *)
Inductive in_astgram : forall (a:astgram), list char_p -> interp (astgram_type a) -> Prop :=
| InaEps : forall s v, s = nil -> v = tt -> in_astgram aEps s v
| InaChar : forall c s v, s = c::nil -> v = c -> in_astgram (aChar c) s v
| InaAny : forall c s v, s = c::nil -> v = c -> in_astgram aAny s v
| InaCat : forall a1 a2 s1 s2 v1 v2 s v,
  in_astgram a1 s1 v1 -> in_astgram a2 s2 v2 -> s = s1 ++ s2 -> v = (v1,v2) -> 
  in_astgram (aCat a1 a2) s v
| InaAlt_l : forall a1 a2 s v1 v, 
  in_astgram a1 s v1 -> v = inl _ v1 -> in_astgram (aAlt a1 a2) s v
| InaAlt_r : forall a1 a2 s v2 v, 
  in_astgram a2 s v2 -> v = inr _ v2 -> in_astgram (aAlt a1 a2) s v
| InaStar_eps : forall a s v, s = nil -> v = nil -> in_astgram (aStar a) s v
| InaStar_cons : forall a s1 v1 s2 v2 s v,
  in_astgram a s1 v1 -> in_astgram (aStar a) s2 v2 -> 
  s1 <> nil -> s = s1 ++ s2 -> v = v1::v2 -> in_astgram (aStar a) s v.
Hint Constructors in_astgram.

(** Some abbreviations for "fix-up" functions. *)
Definition fixfn (ag:astgram) (t:type) := interp (astgram_type ag) -> interp t.
Definition ag_and_fn (t:type) (ag:astgram) (f:fixfn ag t) : { ag : astgram & fixfn ag t } :=
  existT (fun ag => fixfn ag t) ag f.
Implicit Arguments ag_and_fn [t].
Extraction Implicit ag_and_fn [t].

(** Split a [grammar] into a simplified [astgram] (with no maps) and a top-level fix-up
    function that can turn the results of the [astgram] back into the user-specified 
    values.  Notice that the resulting astgram has no [Map] or [Xform] inside of it. *)
Fixpoint split_astgram t (g:grammar t) : { ag : astgram & fixfn ag t} := 
  match g in grammar t' return { ag : astgram & fixfn ag t'} with
    | Eps => ag_and_fn aEps (fun x => x)
    | Zero t => ag_and_fn aZero (fun x => match x with end)
    | Char c => ag_and_fn (aChar c) (fun x => x)
    | Any => ag_and_fn aAny (fun x => x)
    | Cat t1 t2 g1 g2 => 
      let (ag1, f1) := split_astgram g1 in 
        let (ag2, f2) := split_astgram g2 in 
          ag_and_fn (aCat ag1 ag2) 
          (fun p => (f1 (fst p), f2 (snd p)) : interp (Pair_t t1 t2))
    | Alt t1 t2 g1 g2 => 
      let (ag1, f1) := split_astgram g1 in 
        let (ag2, f2) := split_astgram g2 in 
          ag_and_fn (aAlt ag1 ag2)
          (fun s => match s with 
                      | inl x => inl _ (f1 x)
                      | inr y => inr _ (f2 y)
                    end : interp (Sum_t t1 t2))
    | Star t g => 
      let (ag, f) := split_astgram g in 
        ag_and_fn (aStar ag) (fun xs => (List.map f xs) : interp (List_t t))
    | Map t1 t2 f1 g => 
      let (ag, f2) := split_astgram g in 
        ag_and_fn ag (fun x => f1 (f2 x))
    | Xform t1 t2 f g => 
      let (ag, f2) := split_astgram g in 
        ag_and_fn ag (fun x => (xinterp f) (f2 x))
  end.
Extraction Implicit split_astgram [t].

(** Inversion principles for [astgram]s. *)
Lemma inv_aeps : forall s v, in_astgram aEps s v -> s = nil /\ v = tt.
  intros. inversion H. mysimp.
Qed.
Lemma inv_achar : forall c s v, in_astgram (aChar c) s v -> s = c::nil /\ v = c.
  intros. inversion H. subst. mysimp.
Qed.
Lemma inv_aany : forall s v, in_astgram aAny s v -> s = v::nil.
  intros. inversion H. subst. mysimp.
Qed.
Lemma inv_acat : forall ag1 ag2 s v, in_astgram (aCat ag1 ag2) s v -> 
  exists s1, exists s2, exists v1, exists v2, 
    in_astgram ag1 s1 v1 /\ in_astgram ag2 s2 v2 /\ s = s1++s2 /\ v = (v1,v2).
Proof.
  intros ; inversion H ; subst ; mysimp. exists s1. exists s2. exists v1. exists v2.
  auto.
Qed.
Lemma inv_aalt : forall ag1 ag2 s v, in_astgram (aAlt ag1 ag2) s v -> 
  (exists v1, in_astgram ag1 s v1 /\ v = inl _ v1) \/
  (exists v2, in_astgram ag2 s v2 /\ v = inr _ v2) .
Proof.
  intros ; inversion H ; subst ; mysimp ; [left | right] ; eauto.
Qed.
Lemma inv_azero : forall s v, in_astgram aZero s v -> False.
  intros. inversion H.
Qed.

(** Inversion tactic for [astgram]. *)
Ltac ainv := 
  match goal with 
    | [ H: in_astgram aZero _ _ |- _ ] => contradiction (inv_azero H)
    | [ H : in_astgram aEps _ _ |- _ ] => 
      generalize (inv_aeps H) ; clear H ; intros ; mysimp 
    | [ H : in_astgram (aChar _) _ _ |- _] => 
      generalize (inv_achar H) ; clear H ; intros ; mysimp
    | [ H : in_astgram aAny _ _ |- _] => 
      generalize (inv_aany H) ; clear H ; intros ; subst ; mysimp ; eauto
    | [ H : in_astgram (aCat _ _) _ _ |- _] => 
      generalize (inv_acat H) ; clear H ; intros ; subst ; mysimp ; eauto
    | [ H : in_astgram (aAlt _ _) _ _ |- _] => 
      generalize (inv_aalt H) ; clear H ; intros ; subst ; mysimp ; eauto
    | [ H : match split_astgram ?g with | existT _ _ => _ end |- _ ] => 
      let p := fresh "p" in
        remember (split_astgram g) as p ; destruct p ; simpl in *
    | [ |- forall _, _ ] => intros
    | [ |- _ <-> _ ] => split ; repeat in_inv ; mysimp
    | [ H : forall _ _, _ <-> _ |- _ ] => 
      generalize (fun x y => proj1 (H x y)) (fun x y => proj2 (H x y)) ; clear H ; 
        intros
    | [ H : (_ (fst ?v),_) = (_,_) |- _ ] => 
      injection H ; intros ; subst ; destruct v ; simpl in *
    | [ H : match ?v with inl _ => _ | inr _ => _ end = _ |- _ ] => destruct v ; 
      try congruence
    | [ H : inl _ = inl _ |- _ ] => injection H ; intros ; subst
    | [ H : inr _ = inr _ |- _ ] => injection H ; intros ; subst
    | _ => subst ; eauto
  end.

(** Correctness of [split_astgram] part 1:  This direction is a little easier. *)
Lemma split_astgram_corr1 t (g:grammar t) : 
  let (ag,f) := split_astgram g in 
    forall s v, in_astgram ag s v -> in_grammar g s (f v).
Proof.
  induction g ; simpl ; repeat ainv.
   dependent induction H ; subst ; simpl ; eauto. 
Qed.

(** Correctness of [split_astgram] part 2:  This direction requires a quantifier 
    so is a little harder. *)
Lemma split_astgram_corr2 t (g:grammar t) : 
  let (ag, f) := split_astgram g in 
    forall s v, in_grammar g s v -> exists v', in_astgram ag s v' /\ v = f v'.
Proof.
  induction g ; simpl ; repeat (in_inv ; ainv) ; repeat
  match goal with 
    | [ IH : forall _ _, in_grammar ?g _ _ -> _, H : in_grammar ?g ?s ?v |- _] => 
      specialize (IH s v H) ; mysimp ; subst
  end. exists (x4,x5). mysimp. eauto. econstructor. split. eapply InaAlt_l. eauto. eauto.
  auto. econstructor. split. eapply InaAlt_r. eauto. eauto. auto.
  dependent induction H ; subst. exists (@nil (interp (astgram_type x))). eauto.
  clear IHin_grammar1. specialize (IHin_grammar2 _ g f Heqp IHg v2 (eq_refl _) 
  (JMeq_refl _) (JMeq_refl _)). specialize (IHg _ _ H). mysimp. subst.
  exists (x0::x1). split ; auto. eapply InaStar_cons ; eauto. exists x1. eauto.
  exists x2. eauto.
Qed.

(** * Optimizing [astgram]'s coupled with an [xform]. *)
(** Below, we often end up manipulating a pair of an [astgram] and an [xform].
    that maps us from the type of [astgram] to some other type [t].  In particular,
    various optimizations on [astgrams] require us to generate a "fix-up" function,
    which we express as an [xform].  In turn, those [xform]s can be optimized using
    the definitions above. *)

Definition agxf (t:type) (ag:astgram) (f:astgram_type ag ->> t) : 
  {ag : astgram & astgram_type ag ->> t} := existT _ ag f.
Extraction Implicit agxf [t].

Definition in_agxf t (e: {ag : astgram & astgram_type ag ->> t}) cs v := 
  match e with 
    | existT ag x => exists v', in_astgram ag cs v' /\ xinterp x v' = v
  end.

(** Optimized [aAlt] constructor -- gets rid of [aZero]. *)
Fixpoint append_alt (ag1:astgram) (ag2:astgram) : 
  {ag:astgram & astgram_type ag ->> astgram_type (aAlt ag1 ag2)} := 
  match ag1 return {ag:astgram & astgram_type ag ->> astgram_type (aAlt ag1 ag2)} with
    | aZero => agxf ag2 (Xinr _ _)
    | ag1' => 
      match ag2 return {ag:astgram & astgram_type ag ->> astgram_type (aAlt ag1' ag2)} with
        | aZero => agxf ag1' (Xinl _ _)
        | ag2' => agxf (aAlt ag1' ag2') (Xid _)
      end
  end.

Lemma append_alt_corr1 (ag1 ag2:astgram) cs v : 
  in_astgram (aAlt ag1 ag2) cs v -> in_agxf (append_alt ag1 ag2) cs v.
Proof.
  destruct ag1 ; unfold agxf ; intros ; 
    try (destruct ag2 ; simpl in *; repeat (ainv ; subst) ; fail). 
Qed.

Lemma append_alt_corr2 (ag1 ag2:astgram) cs v : 
  in_agxf (append_alt ag1 ag2) cs v -> in_astgram (aAlt ag1 ag2) cs v.
Proof.
  destruct ag1 ; try (destruct ag2 ; mysimp ; simpl ; unfold agxf ; repeat (ainv ; auto)).
Qed.

(** Optimized [aCat] constructor, gets rid of [aEps] and [aZero]. *)        
Fixpoint append_cat (ag1:astgram) (ag2:astgram) : 
  {ag:astgram & astgram_type ag ->> astgram_type (aCat ag1 ag2)} := 
  match ag1 return {ag:astgram & astgram_type ag ->> astgram_type (aCat ag1 ag2)} with
    | aZero => agxf aZero (Xzero _)
    | aEps => agxf ag2 (Xpair (Xunit _) (Xid _))
    | ag1' => 
      match ag2 return {ag:astgram & astgram_type ag ->> astgram_type (aCat ag1' ag2)} with
        | aZero => agxf aZero (Xzero _)
        | aEps => agxf ag1' (Xpair (Xid _) (Xunit _))
        | ag2' => agxf (aCat ag1' ag2') (Xid _)
      end
  end.

Lemma append_cat_corr1 (ag1 ag2:astgram) cs v : 
  in_astgram (aCat ag1 ag2) cs v -> in_agxf (append_cat ag1 ag2) cs v.
Proof.
  destruct ag1 ; destruct ag2 ; simpl ; intros ; repeat ainv.
  rewrite <- app_nil_end. eauto.
Qed.

Lemma append_cat_corr2 (ag1 ag2:astgram) cs v : 
  in_agxf (append_cat ag1 ag2) cs v -> in_astgram (aCat ag1 ag2) cs v.
Proof.
  destruct ag1 ; destruct ag2 ; mysimp ; repeat ainv.
  econstructor. econstructor. eauto. eauto. eauto. simpl. eauto. eauto.
  econstructor. eauto. eauto. rewrite <- app_nil_end. eauto. eauto.
  rewrite (app_nil_end (x0 ++ x1)). econstructor. econstructor. eauto. eauto. 
  eauto. eauto. econstructor. eauto. eauto. eauto. eauto.
  rewrite (app_nil_end cs). econstructor. eauto. eauto. auto. auto.
  rewrite (app_nil_end cs). econstructor. eauto. eauto. auto. auto.
  rewrite (app_nil_end cs). econstructor. eauto. eauto. auto. auto.
Qed.
  
(** Optimize an [astgram] -- returns a pair of a new [astgram] and an [xform] that
    maps us from the new AST to the old one. *)
Definition opt_ag (ag:astgram) : {ag2:astgram & astgram_type ag2 ->> astgram_type ag} :=
  match ag return {ag2:astgram & astgram_type ag2 ->> astgram_type ag} with
    | aAlt ag1 ag2 => append_alt ag1 ag2
    | aCat ag1 ag2 => append_cat ag1 ag2
    | aStar aZero => agxf aEps (Xempty Unit_t Void_t)
(* This optimization is not valid! *)
(*    | aStar (aStar ag') => agxf (aStar ag') (Xcons (Xid _) (Xempty _ _)) *)
    | ag' => agxf ag' (Xid _)
  end.

Definition cast_interp t1 (v:interp (astgram_type t1)) t2 (H:t1 = t2) : 
  interp (astgram_type t2).
  intros. rewrite <- H. apply v.
Defined.
Extraction Implicit cast_interp [t1 t2].

Lemma astar_azero : forall ag cs v (H1:in_astgram ag cs v) (H2:ag = aStar aZero),
  cs = nil /\ @cast_interp ag v _ H2 = nil.
Proof.
  induction 1 ; intros ; try congruence. subst. injection H2. intros. subst.
  rewrite (@proof_irrelevance _ H2 (eq_refl _)). auto. injection H2. intros.
  subst. inversion H1_.
Qed.

Lemma inv_astar : forall ag s v, 
  in_astgram (aStar ag) s v -> 
  (s = nil /\ v = nil) \/ 
  (exists v1, exists v2, exists s1, exists s2, 
    s1 <> nil /\ s = s1 ++ s2 /\ v = v1::v2 /\
    in_astgram ag s1 v1 /\ in_astgram (aStar ag) s2 v2).
Proof.
  intros ag s v H ; inversion H ; fold interp in * ; fold astgram_type in *.
  subst. mysimp. right. subst. repeat mysimp. exists v1. exists v2. 
  exists s1. exists s2. eauto.
Qed.

Lemma opt_ag_corr1 (ag:astgram) cs v : 
  in_astgram ag cs v -> in_agxf (opt_ag ag) cs v.
Proof.
  destruct ag ; try (simpl ; eauto ; fail || apply append_cat_corr1 || 
  apply append_alt_corr1). intros. generalize (inv_astar H). clear H.
  fold interp. fold astgram_type. intros. 
  destruct H ; mysimp ; subst ; destruct ag ; simpl ; eauto.
  generalize (astar_azero H3 (eq_refl _)). inversion H2.
Qed.

Lemma opt_ag_corr2 (ag:astgram) cs v : 
  in_agxf (opt_ag ag) cs v -> in_astgram ag cs v.
Proof.
  destruct ag ; try (mysimp ; subst ; eauto).
  apply append_cat_corr2 ; auto. apply append_alt_corr2 ; auto.
  destruct ag ; mysimp ; subst ; eauto. ainv.
Qed.

(** Optimize the [astgram] and optimize the resulting [xform]. *)
Definition opt_agxf (t:type) (ag:astgram) (f:astgram_type ag ->> t) := 
  let (ag', f') := opt_ag ag in agxf ag' (xcomp f' f).
Extraction Implicit opt_agxf [t].

Lemma opt_agxf_corr1 t ag (f:astgram_type ag ->> t) cs v : 
  in_agxf (existT _ ag f) cs v -> in_agxf (opt_agxf ag f) cs v.
Proof.
  unfold in_agxf. mysimp. unfold opt_agxf. 
  generalize (opt_ag_corr1 H). remember (opt_ag ag) as agxf. destruct agxf.
  generalize (xcomp_corr x1 f). intros. unfold agxf. unfold in_agxf in H2. mysimp.
  subst. econstructor ; split. eauto. rewrite H1. auto.
Qed.

Lemma opt_agxf_corr2 t ag (f:astgram_type ag ->> t) cs v : 
  in_agxf (opt_agxf ag f) cs v -> in_agxf (existT _ ag f) cs v.
Proof.
  unfold opt_agxf. simpl. unfold in_agxf. intros.
  remember (opt_ag ag) as e1. destruct e1. unfold agxf in H. mysimp.
  rewrite (xcomp_corr x0 f) in H0. 
  generalize (@opt_ag_corr2 ag cs). rewrite <- Heqe1. simpl. intros.
  simpl in H0. exists (xinterp x0 x1). specialize (H1 (xinterp x0 x1)).
  split ; auto. apply H1. eauto.
Qed.

(** Compute the "null" of an [astgram].  Formally, if [null_and_split ag = (ag', f)], 
    then [in_astgram ag nil v] iff there is a [v'] such that [in_astgram ag' nil v'] and
    [v = f v'].   So this is computing a grammar that maps the empty string to 
    the same set of values as the original grammar, but rejects all other strings. *)
Fixpoint null_and_split (ag1:astgram):{ag2:astgram & astgram_type ag2->>astgram_type ag1}:=
  match ag1 return {ag2:astgram & astgram_type ag2->>astgram_type ag1} with
    | aEps => agxf aEps (Xid Unit_t)
    | aZero => agxf aZero (Xzero _)
    | aChar c => agxf aZero (Xzero Char_t)
    | aAny => agxf aZero (Xzero Char_t)
    | aAlt ag11 ag12 => 
      let (ag11', f1) := null_and_split ag11 in 
        let (ag12', f2) := null_and_split ag12 in 
          opt_agxf (aAlt ag11' ag12') (Xmatch (Xcomp f1 (Xinl _ _)) (Xcomp f2 (Xinr _ _)))
    | aCat ag11 ag12 => 
      let (ag11', f1) := null_and_split ag11 in 
        match ag11' with 
          | aZero => agxf aZero (Xzero _)
          | ag11'' => 
            let (ag12', f2) := null_and_split ag12 in 
              opt_agxf (aCat ag11'' ag12') (Xpair (Xcomp (Xfst _ _) f1) (Xcomp (Xsnd _ _) f2))
        end
    | aStar ag11 => agxf aEps (Xempty Unit_t (astgram_type ag11))
  end.

(* Todo:  need to clean up this proof. *)
Lemma null_and_split_corr1 (ag:astgram) cs v : 
  in_astgram ag cs v -> cs = nil -> in_agxf (null_and_split ag) cs v.
Proof.
  induction 1 ; mysimp ; subst ; eauto ; try discriminate. 
  generalize (app_eq_nil _ _ H3). mysimp. specialize (IHin_astgram1 H1).
  specialize (IHin_astgram2 H2). subst. clear H3. 
  remember (null_and_split a1) as e1 ; destruct e1.
  assert (match x with | aZero => agxf aZero (Xzero _) | 
            ag11' => let (ag12',f2) := null_and_split a2 in 
              opt_agxf (aCat ag11' ag12') (Xpair (Xcomp (Xfst _ _) x0) (Xcomp (Xsnd _ _) f2))
          end = let (ag12',f2) := null_and_split a2 in 
              opt_agxf (aCat x ag12') (Xpair (Xcomp (Xfst _ _) x0) (Xcomp (Xsnd _ _) f2))).
  destruct x ; auto. remember (null_and_split a2) as e2. destruct e2.
  simpl. unfold opt_agxf. simpl. auto. rewrite H1. clear H1.
  remember (null_and_split a2) as e2. destruct e2. eapply opt_agxf_corr1.
  simpl. unfold in_agxf in *. mysimp. subst. exists (x3,x4). split.
  rewrite (app_nil_end []). eauto. eauto. 
  specialize (IHin_astgram (eq_refl _)). remember (null_and_split a1) as e1 ; 
  destruct e1. remember (null_and_split a2) as e2 ; destruct e2. simpl in *.
  mysimp. eapply opt_agxf_corr1. simpl. exists (inl (interp (astgram_type x1)) x3).
  rewrite H1. split ; eauto. 
  specialize (IHin_astgram (eq_refl _)). remember (null_and_split a1) as e1 ;
  destruct e1. remember (null_and_split a2) as e2 ; destruct e2. simpl in *.
  mysimp. eapply opt_agxf_corr1. simpl. exists (inr (interp (astgram_type x)) x3).
  rewrite H1. split ; eauto. 
  generalize (app_eq_nil _ _ H4). mysimp. congruence.
Qed.  

(* Todo: need to clean up this proof. *)
Lemma null_and_split_corr2 (ag:astgram) v : 
  in_agxf (null_and_split ag) nil v -> in_astgram ag nil v.
Proof.
  induction ag ; mysimp ; subst ; auto ; ainv.
  remember (null_and_split ag1) as e1 ; remember (null_and_split ag2) as e2.
  destruct e1 as [ag11' f1] ; destruct e2 as [ag12' f2].
  assert (
    match ag11' with | aZero => agxf aZero (Xzero _) |
      ag11' => opt_agxf (aCat ag11' ag12') (Xpair (Xcomp (Xfst _ _) f1) (Xcomp (Xsnd _ _) f2)) end = 
        opt_agxf (aCat ag11' ag12') (Xpair (Xcomp (Xfst _ _) f1) (Xcomp (Xsnd _ _) f2))).
  destruct ag11' ; auto. rewrite H0 in H. clear H0.
  generalize (opt_agxf_corr2 _ _ _ _ H). simpl. mysimp. subst. 
  rewrite (app_nil_end []). specialize (IHag1 (xinterp f1 (fst x))).
  specialize (IHag2 (xinterp f2 (snd x))). destruct x. rewrite (app_nil_end []) in H0.
  ainv. generalize (app_eq_nil _ _ (eq_sym H2)). mysimp. subst.
  injection H3 ; intros ; subst. rewrite (app_nil_end []). econstructor ; eauto.
  remember (null_and_split ag1) as e1 ; destruct e1 as [ag11' f1].
  remember (null_and_split ag2) as e2 ; destruct e2 as [ag12' f2].
  simpl in *. generalize (opt_agxf_corr2 _ _ _ _ H). clear H. simpl.
  mysimp. ainv ; subst. specialize (IHag1 (xinterp f1 x0)).
  econstructor ; eauto. specialize (IHag2 (xinterp f2 x0)). eauto.
Qed.

(** Compute the derivative of an [astgram] with respect to a character.  Formally,
    when [deriv_and_split ag1 c = (ag2,f)] then [in_astgram ag2 s v] holds when
    [in_astgram ag1 (c::s) (f v)].  So the new [astgram] is effectively the
    residual you get when matching and removing the first character [c]. 

    Some care is taken here to optimize the computation and avoid computing
    derivatives that are unnecessary in the [aCat] case, when for instance,
    the [null_and_split] of the first grammar term is [aZero], we can avoid
    computing the derivative of the second grammar term.
*)
Fixpoint deriv_and_split (ag1:astgram) (c:char_p) : 
  {ag2:astgram & astgram_type ag2 ->> astgram_type ag1} := 
  match ag1 return {ag2:astgram & astgram_type ag2 ->> astgram_type ag1} with
    | aEps => agxf aZero (Xzero _)
    | aZero => agxf aZero (Xzero _)
    | aChar c' => if char_dec c c' then agxf aEps (Xchar _ c) else agxf aZero (Xzero _)
    | aAny => agxf aEps (Xchar _ c)
    | aAlt ag11 ag12 => 
      let (ag11', f1) := deriv_and_split ag11 c in 
        let (ag12', f2) := deriv_and_split ag12 c in 
          opt_agxf (aAlt ag11' ag12') (Xmatch (Xcomp f1 (Xinl _ _)) (Xcomp f2 (Xinr _ _)))
    | aCat ag11 ag12 => 
      let (ag11', f1) := deriv_and_split ag11 c in 
        let (ag_left, f_left) := opt_ag (aCat ag11' ag12) in
          let (ag11null', fnull) := null_and_split ag11 in 
            match ag11null' with 
              | aZero => 
                agxf ag_left (Xcomp f_left
                  (Xpair (Xcomp (Xfst _ (astgram_type ag12)) f1)
                         (Xsnd (astgram_type ag11') _)))
              | ag11null => 
                let (ag12', f2) := deriv_and_split ag12 c in 
                  let (ag_right, f_right) := opt_ag (aCat ag11null ag12') in
                    opt_agxf (aAlt ag_left ag_right) 
                    (Xmatch (Xcomp f_left (Xpair (Xcomp (Xfst _ _) f1) (Xsnd _ _)))
                      (Xcomp f_right (Xpair (Xcomp (Xfst _ _) fnull) (Xcomp (Xsnd _ _) f2))))
            end
    | aStar ag0 => 
      let (ag0', f) := deriv_and_split ag0 c in 
        opt_agxf (aCat ag0' (aStar ag0)) (Xcons (Xcomp (Xfst _ _) f) (Xsnd _ _))
  end.

(* Todo: need to clean up this proof. *)
Lemma deriv_and_split_corr1 ag1 cs v : 
  in_astgram ag1 cs v -> 
  forall c cs', cs = c::cs' -> in_agxf (deriv_and_split ag1 c) cs' v.
Proof.
  induction 1 ; intros ; subst ; try discriminate ; simpl. injection H1. intros ; subst. 
  destruct (char_dec c0 c0) ; try congruence. simpl. eauto.
  injection H1 ; intros ; subst. eauto. fold astgram_type.
  destruct s1.
  specialize (IHin_astgram2 c cs' H3) ; clear IHin_astgram1.
  remember (deriv_and_split a1 c) as e1 ; destruct e1.
  remember (append_cat x a2) as e2 ; destruct e2.
  generalize (@null_and_split_corr1 a1 nil) ; remember (null_and_split a1) as e3 ;
  destruct e3 ; simpl ; mysimp. specialize (H1 v1 H (eq_refl _)).
  destruct x3 ; try (remember (deriv_and_split a2 c) as e4 ; destruct e4 ; 
    try (mysimp ; ainv ; congruence)) ; 
  match goal with 
    | [ |- context[append_cat ?e1 ?e2] ] => 
      generalize (@append_cat_corr1 e1 e2) ; 
      remember (append_cat e1 e2) as e5 ; destruct e5 ; clear Heqe5 ; 
        mysimp ; eapply opt_agxf_corr1 ; simpl ; try (
          assert (exists v', in_astgram x6 cs' v' /\ xinterp x7 v' = (x8,x9)) ; 
            [ apply H2 ; eauto | idtac] ; mysimp ; econstructor ; split ; 
              [ eapply InaAlt_r | idtac ] ; eauto ; simpl ; rewrite H8 ; simpl ; 
                congruence)
    | _ => idtac
  end.
  assert (exists v', in_astgram x7 cs' v' /\ xinterp x8 v' = (x9,x10)) ; 
    [ apply H2 ; eauto | idtac] ; mysimp ; econstructor ; split ; 
      [ eapply InaAlt_r | idtac ] ; eauto ; simpl ; rewrite H8 ; simpl ; 
                congruence.
  simpl in H3. injection H3 ; intros ; subst. clear H3.
  specialize (IHin_astgram1 c s1 (eq_refl _)). remember (deriv_and_split a1 c) as e1 ; 
  destruct e1. 
  generalize (@append_cat_corr1 x a2).
  remember (append_cat x a2) as e2 ; destruct e2. 
  remember (null_and_split a1) as e3 ; destruct e3. intros.
  destruct x3 ; 
  remember (deriv_and_split a2 c) as e4 ; destruct e4 ; 
  match goal with 
    | [ |- context[append_cat ?e1 ?e2] ] => 
      remember (append_cat e1 e2) as e5 ; destruct e5 ; mysimp ; 
        eapply opt_agxf_corr1 ; simpl ; subst ;
          assert (exists v', in_astgram x1 (s1 ++ s2) v' /\ xinterp x2 v' = (x8,v2)) ; 
            [ apply H1 ; eauto | mysimp ; econstructor ; split ; [eapply InaAlt_l ; eauto | 
              simpl ; rewrite H4 ; simpl ; auto]]
    | _ => idtac
  end. 
  simpl in *. mysimp. subst. 
  specialize (H1 (s1++s2) (x6,v2) (InaCat H2 H0 (eq_refl _) (eq_refl _))). mysimp. 
  exists x7. rewrite H3. simpl. auto.
  remember (append_cat (aStar x3) x5) as e5 ; destruct e5 ; mysimp.
  eapply opt_agxf_corr1 ; simpl ; subst. clear Heqe5.  
  specialize (H1 (s1 ++ s2) (x9,v2) (InaCat H2 H0 (eq_refl _) (eq_refl _))).
  mysimp. econstructor ; split. eapply InaAlt_l ; eauto. simpl. rewrite H3. simpl. auto.
  specialize (IHin_astgram c cs' (eq_refl _)). 
  remember (deriv_and_split a1 c) as e1 ; destruct e1. 
  remember (deriv_and_split a2 c) as e2 ; destruct e2.
  eapply opt_agxf_corr1 ; simpl in *. mysimp. subst. eauto.
  specialize (IHin_astgram c cs' (eq_refl _)).
  remember (deriv_and_split a1 c) as e1 ; destruct e1. 
  remember (deriv_and_split a2 c) as e2 ; destruct e2.
  eapply opt_agxf_corr1 ; simpl in *. mysimp. subst. eauto.
  destruct s1 ; try congruence. simpl in H4.
  specialize (IHin_astgram1 c0 s1 (eq_refl _)). injection H4 ; intros ; subst.
  remember (deriv_and_split a c) as e1 ; destruct e1. eapply opt_agxf_corr1. 
  simpl in *. mysimp. subst. eauto.
Qed.

(** This definition is useful below, as it characterizes the output
    grammars we get from [null_and_split].  *)
Fixpoint null_and_split_form (ag:astgram) : Prop :=
  match ag with 
    | aEps => True
    | aZero => True
    | aAlt ag1 ag2 => null_and_split_form ag1 /\ null_and_split_form ag2
    | aCat ag1 ag2 => null_and_split_form ag1 /\ null_and_split_form ag2
    | _ => False
  end.

Lemma has_null_and_split_form ag : 
  match null_and_split ag with 
    | existT ag' _ => null_and_split_form ag'
  end.
Proof.
  induction ag ; simpl ; auto ;
  destruct (null_and_split ag1) as [n1 x1]; destruct n1 ; try contradiction ; 
    destruct (null_and_split ag2) as [n2 x2] ; try contradiction ; simpl ; auto ;
  destruct n2 ; simpl ; auto. 
Qed.

Lemma null_and_split_imp_nil ag cs v: 
  in_astgram ag cs v -> null_and_split_form ag -> cs = [].
Proof.
  induction 1 ; simpl ; intros ; try contradiction ; subst ; mysimp ; auto.
  rewrite IHin_astgram1 ; auto ; rewrite IHin_astgram2 ; auto.
Qed.

(* Todo:  need to clean up this proof. *)
Lemma deriv_and_split_corr2' ag c agd x : 
  existT _ agd x = deriv_and_split ag c ->
  forall cs v, in_astgram agd cs v -> in_astgram ag (c::cs) (xinterp x v).
Proof.
  Ltac ex_simp := 
  match goal with 
    | [ H : existT _ _ _ = existT _ _ _ |- _] => 
      generalize (eq_sigT_fst H) ; intros ; subst ; mysimp
  end.

  induction ag ; mysimp ; unfold agxf in * ; repeat ex_simp ; ainv ; subst ; eauto ; 
    fold astgram_type in *.
  destruct (char_dec c0 c) ; subst ; ex_simp ; ainv ; subst ; eauto.
  remember (deriv_and_split ag1 c) as agxf1. destruct agxf1 as [ag1d x1].
  specialize (IHag1 _ _ _ Heqagxf1).
  generalize (@append_cat_corr2 ag1d ag2). intro.
  remember (append_cat ag1d ag2) as agxf_left. destruct agxf_left as [ag_left x_left]. 
  generalize (@null_and_split_corr2 ag1). intro.
  remember (null_and_split ag1) as agxf_null. destruct agxf_null as [ag_null x_null].
  remember (deriv_and_split ag2 c) as agxf2. destruct agxf2 as [ag2d x2].
  specialize (IHag2 _ _ _ Heqagxf2).
  generalize (@append_cat_corr2 ag_null ag2d). intro.
  remember (append_cat ag_null ag2d) as agxf_right. destruct agxf_right as [ag_right x_right].
  destruct ag_null ; 
  match goal with 
    | [ H0 : in_astgram ?agd ?cs ?v, 
        H : existT _ _ ?z = opt_agxf ?f ?x |- _] => 
      generalize (@opt_agxf_corr2 _ f x) ; 
        let H4 := fresh "H" in intro H4 ; rewrite <- H in H4 ; 
          specialize (H4 cs (xinterp z v)) ; 
            let H5 := fresh "H" in 
            assert (H5:in_agxf (existT _ agd z) cs (xinterp z v)) ; 
              [ unfold in_agxf ; simpl ; eauto | specialize (H4 H5) ; clear H5] ; 
              mysimp ; ainv ; subst ; 
                [ specialize (H1 cs (xinterp x_left x3)) ; 
                  let H6 := fresh "H" in 
                    assert (H6: in_astgram (aCat ag1d ag2) cs (xinterp x_left x3)) ; 
                      [ apply H1 ; eauto | idtac] ; ainv ; subst ; econstructor ; eauto ; 
                        rewrite <- H5 ; rewrite H9 ; auto
                | specialize (H3 cs (xinterp x_right x3)) ; 
                  specialize (H3 (ex_intro (fun v' : interp (astgram_type ag_right) => 
                    in_astgram ag_right cs v' /\ xinterp x_right v' = xinterp x_right x3) 
                  x3 (conj H4 (eq_refl _)))) ; ainv ; subst ; 
                  try (ainv ; subst) ; simpl in * ; 
                    try (econstructor ; eauto ; try (rewrite <- H5) ; try (rewrite H9) ; 
                    try (rewrite H8) ; auto ; fail) ; 
                    try (generalize (has_null_and_split_form ag1) ; 
                      rewrite <- Heqagxf_null ; mysimp ; try contradiction ; 
                        repeat 
                          match goal with
                            | [ H1 : null_and_split_form ?ag, 
                                H2 : in_astgram ?ag ?cs ?v |- _] => 
                            generalize (null_and_split_imp_nil H2 H1) ; 
                              intros ; subst ; clear H1 ; simpl in * 
                          end ; try (econstructor ; eauto ; rewrite <- H5 ; rewrite H8 ; auto)

)
                ]
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => 
      generalize (eq_sigT_fst H) ; intros ; subst ; mysimp ; 
        assert (in_astgram (aCat ag1d ag2) cs (xinterp x_left v)) ; 
          [apply H1 ; eauto | idtac] ; ainv ; subst ; mysimp ;
            econstructor ; eauto ; rewrite H6 ; auto
    | _ => idtac
  end.
  specialize (IHag1 c).  specialize (IHag2 c).
  remember (deriv_and_split ag1 c) as agxf1 ; destruct agxf1 as [ag1d x1].
  remember (deriv_and_split ag2 c) as agxf2 ; destruct agxf2 as [ag2d x2].
  match goal with 
    | [ H : existT _ ?agd ?x = opt_agxf ?f ?y |- _] => 
      generalize (@opt_agxf_corr2 _ f y) ; rewrite <- H ; simpl ; intros ;
        specialize (H1 cs (xinterp x v)) 
  end.
  assert (exists v', in_astgram agd cs v' /\ xinterp x v' = xinterp x v) ; eauto. 
  specialize (H1 H2) ; mysimp. ainv ; subst ; eauto.
  specialize (IHag c).
  remember (deriv_and_split ag c) as agxf ; destruct agxf as [ag1d x1].
  match goal with 
    | [ H : existT _ ?agd ?x = opt_agxf ?f ?y |- _] => 
      generalize (@opt_agxf_corr2 _ f y) ; rewrite <- H ; simpl ; intros ;
        specialize (H1 cs (xinterp x v)) 
  end.
  assert (exists v', in_astgram agd cs v' /\ xinterp x v' = xinterp x v) ; eauto.
  specialize (H1 H2) ; mysimp. ainv. subst. 
  eapply InaStar_cons ; eauto. congruence.
Qed.
  
Lemma deriv_and_split_corr2 ag1 c cs v : 
  in_agxf (deriv_and_split ag1 c) cs v -> in_astgram ag1 (c::cs) v.
Proof.
  intros. unfold in_agxf in H. 
  generalize (deriv_and_split_corr2' ag1 c). destruct (deriv_and_split ag1 c).
  mysimp. subst. apply H0 ; auto.
Qed.

(* Todo: this needs to go in a library. *)
Definition cross_prod t1 t2 (xs:list t1) (ys:list t2) : list (t1 * t2) := 
  (fold_right (fun v a => (map (fun w => (v,w)) ys) ++ a) nil xs).

Lemma in_cross_prod A B (x:A) (y:B) : 
  forall xs, In x xs -> 
    forall ys, In y ys -> 
      In (x,y) (fold_right (fun v a => (map (fun w => (v,w)) ys) ++ a) nil xs).
Proof.
  induction xs ; intro H ; [ contradiction H | destruct H ] ; mysimp ; subst ; 
    apply in_or_app ; [ idtac | firstorder ].
  left ; clear IHxs ; induction ys ; 
    [ contradiction H0 | destruct H0 ; mysimp ; subst ; auto].
Qed.

Lemma InConcatMap1 A B (x:A) (y:B) xs ys : 
  In (x,y) (fold_right (fun v a => (map (fun w => (v,w)) ys) ++ a) nil xs) -> 
  In x xs.
Proof.
  induction xs ; mysimp ; repeat
    match goal with 
      | [ H : In _ _ |- _ ] => destruct (in_app_or _ _ _ H) ; [left | right ; eauto]
      | [ H : In (?x, _) (map _ ?ys) |- _ ] => 
        let l := fresh "l" in generalize H ; generalize ys as l; 
          induction l ; mysimp ; firstorder ; congruence
    end.
Qed.

Lemma InConcatMap2 A B (x:A) (y:B) xs ys : 
  In (x,y) (fold_right (fun v a => (map (fun w => (v,w)) ys) ++ a) nil xs) -> 
  In y ys.
Proof.
  induction xs ; mysimp ; firstorder ;
    match goal with 
      | [ H : In _ (map _ ?ys ++ _) |- _ ] => 
        let H0 := fresh "H" in let l := fresh "l" in 
          generalize (in_app_or _ _ _ H) ; intro H0 ; destruct H0 ; auto ; 
            generalize H0 ; generalize ys as l ; induction l ; mysimp ; left ; congruence
    end.
Qed.

(** This function computes the list of all values v, such that 
    [in_astgram nil v] holds. *)
Fixpoint astgram_extract_nil (ag:astgram) : list (interp (astgram_type ag)) := 
  match ag return list (interp (astgram_type ag)) with
    | aEps => tt::nil
    | aZero => nil
    | aChar _ => nil
    | aAny => nil
    | aCat ag1 ag2 => cross_prod (astgram_extract_nil ag1) (astgram_extract_nil ag2)
    | aAlt ag1 ag2 => 
      (List.map (fun x => inl _ x) (astgram_extract_nil ag1)) ++ 
      (List.map (fun x => inr _ x) (astgram_extract_nil ag2))
    | aStar ag => nil::nil
  end.

Lemma astgram_extract_nil_corr1 ag cs v : 
  in_astgram ag cs v -> cs = [] -> In v (astgram_extract_nil ag).
Proof.
  induction 1 ; simpl ; intros ; subst ; try congruence ; eauto.
  generalize (app_eq_nil _ _ H3). mysimp ; subst.
  eapply in_cross_prod ; eauto. eapply in_or_app.  left.
  apply in_map ; auto. eapply in_or_app. right. apply in_map ; auto.
  generalize (app_eq_nil _ _ H4) ; mysimp ; subst.
Qed.

Lemma astgram_extract_nil_corr2 ag v : 
  In v (astgram_extract_nil ag) -> in_astgram ag [] v.
Proof.
  induction ag ; mysimp ; try contradiction. destruct v.
  generalize (InConcatMap1 _ _ _ _ H) (InConcatMap2 _ _ _ _ H). eauto. 
  generalize (in_app_or _ _ _ H). intro. destruct v.
  eapply InaAlt_l ; eauto. eapply IHag1. 
  destruct H0. generalize (astgram_extract_nil ag1) H0. induction l ; mysimp.
  injection H1 ; mysimp. assert False. generalize (astgram_extract_nil ag2) H0.
  induction l ; mysimp ; congruence. contradiction.
  eapply InaAlt_r ; eauto. eapply IHag2.
  destruct H0. assert False. generalize (astgram_extract_nil ag1) H0.
  induction l ; mysimp ; congruence. contradiction.
  generalize (astgram_extract_nil ag2) H0. induction l ; mysimp. 
  injection H1 ; eauto.
Qed.

(** Lift the derivative from a character to a string. *)
Fixpoint derivs_and_split (ag:astgram) (cs:list char_p) : 
  {ag2:astgram & astgram_type ag2 ->> astgram_type ag} := 
  match cs with 
    | nil => agxf ag (Xid _)
    | c::cs' => let (ag1, x1) := deriv_and_split ag c in 
                let (ag2, x2) := derivs_and_split ag1 cs' in 
                  agxf ag2 (xopt (xcomp' x1 x2))
  end.

Lemma derivs_and_split_corr1 cs ag v : 
  in_astgram ag cs v -> in_agxf (derivs_and_split ag cs) nil v.
Proof.
  induction cs ; simpl ; eauto. intros.
  generalize (deriv_and_split_corr1 H). intros. specialize (H0 _ _ (eq_refl _)).
  unfold in_agxf in *. destruct (deriv_and_split ag a). mysimp. 
  remember (derivs_and_split x cs) as e. destruct e. 
  unfold agxf. 
  specialize (IHcs _ _ H0). rewrite <- Heqe in IHcs. mysimp. 
  subst. generalize (xcomp'_corr x0 x3 x4). intros.
  exists x4. split ; auto. rewrite xopt_corr. auto.
Qed.

Lemma derivs_and_split_corr2 cs ag v : 
  in_agxf (derivs_and_split ag cs) nil v -> in_astgram ag cs v.
Proof.
  induction cs ; simpl. intros ; mysimp. subst. auto.
  intros. generalize (deriv_and_split_corr2 ag a). intros.
  remember (deriv_and_split ag a) as e ; destruct e.  
  remember (derivs_and_split x cs) as e2 ; destruct e2. 
  unfold in_agxf in H. unfold agxf in H. mysimp. rewrite xopt_corr in H1.
  eapply H0.
  generalize (xcomp'_corr x0 x2 x3). intros. rewrite H2 in H1. simpl in H1.
  unfold in_agxf in IHcs. specialize (IHcs x). 
  rewrite <- Heqe2 in IHcs. subst. exists (xinterp x2 x3). split ; auto.
  eapply IHcs. eauto.
Qed.
  
(** Naive parser: split out the user-defined functions using [split_astgram], 
    then calculate the derivative with respect to the string, then call
    [astgram_extract_nil] to get a list of ASTs, then apply the the final
    transform [xfinal] to map them back to values of the type of the original
    [astgram], and then apply the split out user-level function to get back a 
    list of [t] results. *)
Definition parse t (g:grammar t) (cs : list char_p) : list (interp t) := 
  let (ag, fuser) := split_astgram g in 
    let (agfinal, xfinal) := derivs_and_split ag cs in 
    List.map (fun x => fuser (xinterp xfinal x)) (astgram_extract_nil agfinal).
Extraction Implicit parse [t].

Lemma parse_corr1 : forall t (g:grammar t) cs v, in_grammar g cs v -> In v (parse g cs).
Proof.
  intros. unfold parse. 
  generalize (split_astgram_corr2 g). intros.
  remember (split_astgram g). destruct s. specialize (H0 _ _ H). mysimp. subst.
  generalize (@derivs_and_split_corr1 cs x). unfold in_agxf. 
  intros. specialize (H1 _ H0). remember (derivs_and_split x cs) as e. destruct e ;
  mysimp. subst. generalize (astgram_extract_nil_corr1 H1 (eq_refl _)). intro.
  apply (in_map (fun x => f (xinterp x2 x)) (astgram_extract_nil x1) _ H2).
Qed.

Lemma parse_corr2 : forall t (g:grammar t) cs v, In v (parse g cs) -> in_grammar g cs v.
Proof.
  unfold parse. intros. remember (split_astgram g) as s. destruct s.
  remember (derivs_and_split x cs) as e ; destruct e. 
  generalize (astgram_extract_nil_corr2 x0).
  assert (exists z, v = f (xinterp x1 z) /\ In z (astgram_extract_nil x0)). 
  generalize (astgram_extract_nil x0) v H. 
  induction l ; simpl ; intros ; try contradiction. destruct H0. subst.
  exists a. split ; auto. specialize (IHl _ H0). mysimp. subst.
  exists x2. split ; auto. mysimp. subst. clear H. specialize (H1 _ H2).
  clear H2. generalize (derivs_and_split_corr2 cs x). unfold in_agxf.
  intros. rewrite <- Heqe in H. assert (in_astgram x cs (xinterp x1 x2)).
  eapply H. eauto. generalize (split_astgram_corr1 g). rewrite <- Heqs.
  intros. eauto.
Qed.

(** * Construction of a deterministic-finite-state transducer
      for table-based parsing *)
Section DFA.
  (** Our [DFA] (really a deterministic finite-state transducer) has a number
     of states [n].  Each state corresponds to an [astgram], and in particular
     dfa_states[0] corresponds to the original grammar, and each other state
     corresponds to the derivative of dfa_states[0] with respect to some string
     of tokens [t1,...,tn].  We transition from states using the transition table.
     In particular, if we are in state [i], given input token [t], we compute
     our next state as [next_state] of [transition[i][t]].  The [next_xform] in 
     [transition[i][t]] says how to transform AST values extracted from 
     [next_state(transition[i][t])] to the type of AST values in [states[i]].  
     The [accept] row records which states are accepting states, while the
     [rejects] row records which states are failing states.  
     *)
  (* Todo:  should use something more efficient than lists for this stuff. *)

  Definition states_t := list astgram.
  Notation "s .[ i ] " := (nth i s aZero) (at level 40).

  (** Entries in the transition matrix *)
  Record entry_t(row:nat)(states:states_t) := 
    { (** which state do we go to next *)
      next_state : nat ; 
      next_state_lt : next_state < length states ; 
      (** how do we transform ASTs from the next state back to this state *)
      next_xform : 
        interp (astgram_type (states.[next_state])) -> interp (astgram_type (states.[row])) 
    }.

  (** Rows in the transition matrix -- an entry for each token *)  
  Definition row_t(i:nat)(s:states_t) := list (entry_t i s).

  Record transition_t(s:states_t) := {
    (** which row are we talking about *)
    row_num : nat ; 
    row_num_lt : row_num < length s ;
    (** what are the transition entries *)
    row_entries : list (entry_t row_num s) ; 
    (** have an entry for each token *)
    row_entries_len : length row_entries = num_tokens
  }.

  (** The transition matrix is then a list of rows *)
  Definition transitions_t(s:states_t) := list (transition_t s).

  Record DFA := {
    (** number of states in the DFA *)
    dfa_num_states : nat ; 
    (** the list of [astgram]s for the states *)
    dfa_states : states_t ; 
    dfa_states_len : length dfa_states = dfa_num_states ; 
    (** the transition matrix for the DFA. *)
    dfa_transition : transitions_t dfa_states ; 
    dfa_transition_len : length dfa_transition = dfa_num_states ; 
    dfa_transition_r : forall i, match nth_error dfa_transition i with 
                                   | Some r => row_num r = i
                                   | None => True
                                 end ;
    (** which states are accepting states *)
    dfa_accepts : list bool ; 
    dfa_accepts_len : length dfa_accepts = dfa_num_states ; 
    (** which states are failure states *)
    dfa_rejects : list bool ;
    dfa_rejects_len : length dfa_rejects = dfa_num_states
  }.
  
  (** Instead of working directly in terms of lists of [char_p]'s, we instead
     work in terms of [token_id]'s where a [token_id] is just a [nat] in the
     range 0..[num_tokens]-1.  We assume that each [token_id] can be mapped
     to a list of [char_p]'s.  For example, in the x86 parser, our characters
     are bits, but our tokens represent bytes in the range 0..255.  So the
     [token_id_to_chars] function should extract the n bits corresponding to the
     byte value.  *)
  (** Find the index of an [astgram] in the list of [states]. *)
  Fixpoint find_index' (g:astgram) (n:nat) (states:states_t) : option nat := 
    match states with 
      | nil => None
      | h::t => if astgram_dec g h then Some n else find_index' g (1+n) t
    end.

  Definition find_index (g:astgram) (states:states_t) : option nat := 
    find_index' g 0 states.

  (** Find the index of an [astgram] in the list of [states].  We return
     a delta to add to the states in case the [astgram] is not there and
     we need to add it. *)
  Definition find_or_add (g:astgram) (states:states_t) : states_t * nat := 
    match find_index g states with 
      | None => ((g::nil), length states)
      | Some i => (nil, i)
    end.

  (** Various helper lemmas regarding [nth] and [nth_error] -- these
      should probably be put in another file. *)
  Lemma nth_lt : forall xs ys n, n < length xs -> (xs ++ ys).[n] = xs.[n].
  Proof.
    induction xs ; mysimp. assert False. omega. contradiction. 
    destruct n. auto. apply IHxs. omega.
  Qed.

  Lemma find_index_some' g s j n : find_index' g j s = Some n -> (n - j) < length s.
  Proof.
    intro g. unfold find_index. induction s ; simpl ; intros. discriminate.
    destruct (astgram_dec g a). injection H ; intros ; subst. 
    assert (n - n = 0). auto with arith. rewrite H0. auto with arith.
    specialize (IHs _ _ H). omega.
  Qed.
  
  Lemma find_index_some g s n : find_index g s = Some n -> n < length s.
  Proof.
    intros. generalize (find_index_some' _ _ _ H). assert (n - 0 = n). auto with arith.
    rewrite H0. auto.
  Qed.

  Lemma nth_error_some n s r : nth_error s n = Some r -> s.[n] = r.
    induction n ; simpl ; intros ; destruct s. discriminate. injection H.
    intros ; subst. auto. discriminate. simpl. apply IHn. auto.
  Qed.

  Lemma nth_error_some_lt A n s (r:A) : nth_error s n = Some r -> n < length s.
    induction n; simpl ; destruct s ; simpl ; intros ; try discriminate.
    injection H. intros ; subst. auto with arith. specialize (IHn _ _ H).
      auto with arith.
  Qed.

  Definition app_length_lt A n (s1 s2:list A) : n < length s1 -> n < length (s1 ++ s2).
    intros. rewrite app_length. omega.
  Qed.

  Lemma nth_error_none A (s:list A) n : nth_error s n = None -> n >= length s.
  Proof.
    induction s ; destruct n ; simpl ; intros ; auto with arith. discriminate.
    specialize (IHs _ H). omega.
  Qed.

  Lemma nth_error_lt A n (xs:list A) : n < length xs -> exists r, nth_error xs n = Some r.
  Proof.
    induction n ; simpl; intros. destruct xs. assert False. simpl in *. omega. 
    contradiction. exists a. auto. destruct xs. simpl in H. assert False. omega.
    contradiction. simpl in H. eapply IHn. omega.
  Qed.

  Lemma nth_error_gt A n (xs:list A) : n >= length xs -> nth_error xs n = None.
    induction n ; simpl ; intros ; destruct xs ; simpl in * ; auto.
    assert False. omega. contradiction. apply IHn. omega.
  Qed.

  Lemma nth_error_lt_app A n (xs ys:list A) : n < length xs -> 
    nth_error (xs ++ ys) n = nth_error xs n.
  Proof.
    induction n ; destruct xs ; simpl ; intros ; 
      try (assert False ; [ omega | contradiction ]). auto. apply IHn. omega.
  Qed.

  Lemma nth_error_app_gt A n (xs ys:list A) : n >= length xs -> 
    nth_error (xs ++ ys) n = nth_error ys (n - (length xs)).
  Proof.
    induction n ; destruct xs ; simpl ; auto. intros. assert False. omega.
    contradiction. intros. apply IHn. omega.
  Qed.
  (** End helper lemmas. *)

  (** Simple facts about [find_index] and [find_or_add_index]. *)
  Lemma find_index'_mono g s j n : find_index' g j s = Some n -> n >= j.
    induction s ; simpl ; intros. discriminate. destruct (astgram_dec g a). 
    injection H ; intros ; subst ; auto. specialize (IHs _ _ H). omega.
  Qed.

  Lemma find_index_prop' g s j n : 
    find_index' g j s = Some (n + j) -> s.[n] = g.
  Proof.
    intro g. induction s ; simpl ; intros. discriminate. destruct (astgram_dec g a).
    injection H. intros. assert (n = 0). omega. rewrite H1. auto.
    generalize (find_index'_mono _ _ _ H). intros. destruct n. assert False. omega.
    contradiction. specialize (IHs (S j) n).
    assert (n + S j = S n + j). omega. rewrite H1 in IHs. specialize (IHs H). auto.
  Qed.

  Lemma find_index_prop g s n : find_index g s = Some n -> s.[n] = g.
    intros. unfold find_index in *. assert (n = n + 0). omega. rewrite H0 in H.
    apply (find_index_prop' _ _ _ _ H).
  Qed.

  Lemma find_or_add_app : forall g' s s2,
    g' = (s ++ (fst (find_or_add g' s)) ++ s2).[snd (find_or_add g' s)].
  Proof.
    intros. unfold find_or_add. remember (find_index g' s) as popt. destruct popt ; simpl.
    Focus 2. simpl. rewrite app_nth2. assert (length s - length s = 0). omega.
    rewrite H. auto. auto. rewrite nth_lt. 
    rewrite (find_index_prop g' s (eq_sym Heqpopt)). auto.  
    apply (find_index_some g'). auto.
  Qed.

  (** Returns [true] iff the [astgram] accepts the empty string. *)
  Fixpoint accepts_null (g:astgram) : bool := 
    match g with 
      | aEps => true
      | aChar _ => false
      | aAny => false
      | aZero => false
      | aAlt g1 g2 => accepts_null g1 || accepts_null g2
      | aCat g1 g2 => accepts_null g1 && accepts_null g2
      | aStar _ => true
    end.

  (** Build a map saying which states are accepting states *)
  Definition build_accept_table (s:states_t) : list bool := 
    List.map accepts_null s.

  (** Returns [true] iff the [astgram] rejects all strings. *)
  Fixpoint always_rejects (g:astgram) : bool := 
    match g with 
      | aEps => false
      | aChar _ => false
      | aAny => false
      | aZero => true
      | aAlt g1 g2 => always_rejects g1 && always_rejects g2
      | aCat g1 g2 => always_rejects g1 || always_rejects g2
      | aStar _ => false
    end.

  (** Build a map saying which states are rejecting states *)
  Definition build_reject_table (s:states_t) : list bool := 
    List.map always_rejects s.

  (** Generate the transition matrix row for the state corresponding to the
      astgram [g].  In general, this will add new states. *)
  Section GENROW.
    Variable g : astgram.
    Variable gpos : nat.

    Definition gen_row' 
      (n:nat) (s:states_t) (tid:token_id) (H:s.[gpos] = g) (H1:gpos < length s): 
      { s' : states_t & { r : row_t gpos (s ++ s') & length r = n }}.
      refine (
        fix gen_row' (n:nat) (s:states_t) (tid:token_id) 
                (H:s.[gpos] = g) (H1:gpos < length s) : 
                { s' : states_t & { r : row_t gpos (s ++ s') & length r = n }} := 
        match n with 
          | 0 => existT _ nil (existT _ nil _)
          | S n' => 
            let (g',x) := derivs_and_split g (token_id_to_chars tid) in
              let p := find_or_add g' s in 
                let (s2, row) := gen_row' n' (s ++ (fst p)) (1 + tid) _ _ in 
                  let e : entry_t gpos ((s ++ (fst p)) ++ s2) := 
                    {| next_state := (snd p) ; 
                       next_state_lt := _ ; 
                       next_xform := xinterp (xcoerce x _ _) |} in
                    existT _ ((fst p) ++ s2) _
        end) ; auto.
      rewrite nth_lt ; auto. rewrite app_length. omega.
      generalize (find_index_some g' s).
      unfold find_or_add in p. intros. destruct (find_index g' s).  simpl.
      specialize (H0 n0 (eq_refl _)). rewrite <- app_nil_end. rewrite app_length.
      omega. simpl. rewrite app_length. rewrite app_length. simpl. omega.
      generalize (find_or_add_app g' s s2). intro. rewrite H0. clear H0. 
      rewrite app_ass. auto.  rewrite <- H. rewrite app_ass. 
      rewrite nth_lt ; auto. rewrite <- app_ass. 
      destruct row as [row e']. refine (existT _ (e::row) _). simpl. rewrite e'. auto.
    Defined.

    Definition gen_row (s:states_t) (H:s.[gpos] = g) (H1: gpos < length s) :=
      gen_row' num_tokens s 0 H H1.
  End GENROW.

  (** We build some entries in the transition matrix before we've discovered
      all of the states.  So we have to coerce these entries to work with the
      bigger set of states, which unfortunately, isn't just done at the top-level. *)
  Definition coerce_entry r s s1 (H:r < length s) (e:entry_t r s) : entry_t r (s ++ s1).
    intros.
    refine (
      {| next_state := next_state e ; 
         next_state_lt := app_length_lt s s1 (next_state_lt e) ; 
         next_xform := _ (next_xform e) 
      |}
    ). rewrite app_nth1. rewrite nth_lt ; auto. apply (next_state_lt e).
  Defined.

  Definition coerce_transitions s1 s (ts:transitions_t s) : transitions_t (s ++ s1) := 
    List.map (fun (t:transition_t s) => 
      {| row_num := row_num t ; 
         row_num_lt := app_length_lt s s1 (row_num_lt t) ;
         row_entries := List.map (coerce_entry _ (row_num_lt t)) (row_entries t) ; 
         row_entries_len := eq_ind_r (fun n : nat => n = num_tokens)
                        (row_entries_len t)
                        (list_length_map (coerce_entry s1 (row_num_lt t))
                           (row_entries t)) |}) ts.

  (** Build a transition table by closing off the reachable states.  The invariant
     is that we've closed the table up to the [next_state] and have generated the
     appropriate transition rows for the states in the range 0..[next_state-1].
     So we first check to see if [next_state] is outside the range of states, and
     if so, we are done.  Otherwise, we generate the transition row for the
     derivative at the position [next_state], add it to the list of rows, and
     then move on to the next position in the list of states.  Note that when 
     we generate the transition row, we may end up adding new states.  So we 
     have to go back and coerce the earlier transition entries to be compatible
     with those additional states.  

     Technically, we should prove termination using ideas from Brzowski (sp?).
     I think the essence of this is that at each step, we are either reducing
     the "size" of the regexp (by stripping off a token/char) or else we
     are stripping off a Star.  Not quite sure how to formalize yet, so am
     using an arbitrary "fuel" nat to bound this.
  *)
  Fixpoint build_table (n:nat) (s:states_t) (rows:transitions_t s) (next_state:nat) :
    option {s':states_t & transitions_t s'} := 
    match n with 
      | 0 => None
      | S n' => 
        match nth_error s next_state as popt 
          return (nth_error s next_state = popt) -> _ with 
          | None => fun H => Some (existT _ s rows)
          | Some r => 
            fun H => 
              let (s1, row_ex) := @gen_row r next_state s (nth_error_some _ _ H)
                                   (nth_error_some_lt _ _ H) in 
              let (row, row_len) := row_ex in                                  
              let t := {| row_num := next_state ; 
                          row_num_lt := app_length_lt _ _ (nth_error_some_lt _ _ H) ; 
                          row_entries := row ; 
                          row_entries_len := row_len |} in
                @build_table n' (s++s1) ((coerce_transitions _ rows)++[t]) (1 + next_state)
              end (eq_refl _)
        end.

  (** We start with the initial [astgram] in state 0 and then try to close off the table. *)
  Definition build_transition_table n (r:astgram) := @build_table n (r::nil) nil 0.

  (** When we're done building the table, the number of rows in the transition table
      is equal to the number of states. *)
  Lemma build_trans_len' n s t i s' t' :
    @build_table n s t i = Some (existT _ s' t') -> 
    length t = i -> i <= length s -> length t' = length s'.
  Proof.
    induction n ; simpl ; intros. discriminate. generalize H. clear H.
    generalize (nth_error_some i s). generalize (nth_error_some_lt i s).
    remember (nth_error s i) as popt. destruct popt. intros.
    remember (gen_row s (e a eq_refl) (l a eq_refl)) as r. destruct r. destruct s0.
    apply (IHn _ _ _ _ _ H). simpl. unfold coerce_transitions. 
    rewrite app_length. rewrite map_length. rewrite H0. simpl. omega. 
    assert (i < length s). eapply (nth_error_some_lt i s). eauto. rewrite app_length. 
    omega. intros. clear l e. injection H. clear H. intros. subst. mysimp.
    generalize (nth_error_none _ _ (eq_sym Heqpopt)). intros. omega.
  Qed.

  Lemma build_trans_len n a s t : 
    build_transition_table n a = Some (existT _ s t) -> length t = length s.
  Proof.
    intros. eapply build_trans_len'. eapply H. eauto. auto with arith.
  Qed.

  (** When we build the table, then row number [i] is labelled as having 
      [row_num] i. *)
  Lemma build_trans_r' n s t i s' t' : 
    @build_table n s t i = Some (existT _ s' t') -> 
    i = length t -> 
    (forall j, match nth_error t j with 
                | Some r => row_num r = j
                | None => True 
              end) -> 
    forall j, match nth_error t' j with
                | Some r => row_num r = j
                | None => True
              end.
  Proof.
    induction n ; simpl. intros. discriminate. intros s t i s' t'.
    generalize (nth_error_some i s). generalize (nth_error_some_lt i s).
    remember (nth_error s i) as popt. destruct popt. intros.
    remember (gen_row s (e a eq_refl) (l a eq_refl)). destruct s0. 
    assert (length t = length (coerce_transitions x t)). unfold coerce_transitions.
    rewrite map_length. auto. destruct s0.
    apply (IHn _ _ _ _ _ H) ;  clear IHn. rewrite app_length. simpl. omega. intros.
    assert (j0 < length t \/ j0 >= length t). omega. destruct H3.
    specialize (H1 j0). rewrite nth_error_lt_app ; auto. unfold coerce_transitions.
    generalize (nth_error_lt t H3). mysimp. rewrite H4 in H1.
    rewrite (map_nth_error _ j0 t H4). simpl. auto. omega.
    rewrite (nth_error_app_gt). assert (j0 = length t \/ j0 > length t). omega.
    destruct H4. rewrite <- H2 ; rewrite <- H4. assert (j0 - j0 = 0). omega.
    rewrite H5. simpl. subst. auto. rewrite <- H2. remember (j0 - length t).
    destruct n0. assert False. omega. contradiction. simpl. 
    rewrite nth_error_gt ; auto. simpl. omega. omega.
    intros. clear IHn. injection H ; intros ; clear H. subst. mysimp. apply H1.
  Qed.

  Lemma build_trans_r n a s t : 
    build_transition_table n a = Some (existT _ s t) -> 
    forall i, match nth_error t i with 
                | Some r => row_num r = i 
                | None => True
              end.
  Proof.
    intros. apply (build_trans_r' _ _ H (eq_refl _)). intros. rewrite nth_error_gt.
    auto. simpl. auto with arith.
  Qed.

  (** Now we can build the [DFA] using all of the helper functions.  I've
      only included enough information here to make it possible to run the
      parser and get something out that's type-correct, but not enough
      info to prove that the parser is correct. *)
  Definition build_dfa (n:nat) (a:astgram) : option DFA := 
    match build_transition_table n a as p return 
      (build_transition_table n a = p) -> option DFA with
      | None => fun _ => None
      | Some (existT states table) => 
        fun H => 
        Some {| dfa_num_states := length states ; 
                dfa_states := states ; 
                dfa_states_len := eq_refl _ ;
                dfa_transition := table ; 
                dfa_transition_len := build_trans_len _ _ H ; 
                dfa_transition_r := build_trans_r _ _ H ; 
                dfa_accepts := build_accept_table states ; 
                dfa_accepts_len := map_length _ _ ; 
                dfa_rejects := build_reject_table states ;
                dfa_rejects_len := map_length _ _
             |}
    end (eq_refl _).

  Lemma table_cast (d:DFA) i r : (nth_error (dfa_transition d) i = Some r) ->
    astgram_type (dfa_states d .[ i]) = astgram_type (dfa_states d .[row_num r]).
    intros. generalize (dfa_transition_r d i). rewrite H. intro. rewrite H0. auto.
  Qed.

  (** If we build a [DFA] from [a], then [a] will be the 0th state in the [DFA]. *)
  Lemma build_table_zero n s r i s' t' : 
    @build_table n s r i = Some (existT _ s' t') -> s <> nil -> s.[0] = s'.[0].
  Proof.
    induction n ; simpl. intros. discriminate. intros s r i s' t'.
    generalize (nth_error_some i s) (nth_error_some_lt i s). 
    remember (nth_error s i). destruct e. Focus 2. intros. injection H ; intros ; subst.
    mysimp. intros. remember (gen_row s (e a eq_refl) (l a eq_refl)). destruct s0.
    destruct s0. specialize (IHn _ _ _ _ _ H). destruct s ; simpl in * ; try congruence.
    apply IHn. congruence.
  Qed.

  Lemma build_dfa_zero : 
    forall n ag d, build_dfa n ag = Some d -> (dfa_states d).[0] = ag.
  Proof.
    unfold build_dfa. intros n ag d.
    generalize (build_trans_len n ag). generalize (build_trans_r n ag).
    remember (build_transition_table n ag) as p. destruct p. Focus 2.
    intros. discriminate. destruct s. intros. injection H ; intros ; subst. clear H.
    simpl. unfold build_transition_table in Heqp. 
    generalize (@build_table_zero n (ag::nil) nil 0 x t (eq_sym Heqp)). simpl.
    intros. apply eq_sym. apply H. congruence.
  Qed.

  (** And thus the type of [dfa_states d.[0]] will be the same as for the original
      [astgram]. *)
  Lemma dfa_zero_coerce : 
    forall n ag d, build_dfa n ag = Some d -> 
      astgram_type (dfa_states d.[0]) = astgram_type ag.
  Proof.
    intros. rewrite (build_dfa_zero _ _ H). auto.
  Qed.

  Lemma dfa_is_deriv_cast : 
    forall (d:DFA) (x y:nat), x = y -> 
    astgram_type (dfa_states d .[x]) = astgram_type (dfa_states d .[y]).
  Proof.
    intros. rewrite H. auto.
  Qed.

  Lemma build_table_at_least_one n s r i s' t' : 
    @build_table n s r i = Some (existT _ s' t') -> s <> nil -> s' <> nil.
  Proof.
    induction n ; simpl. intros. discriminate. intros s r i s' t'.
    generalize (nth_error_some i s) (nth_error_some_lt i s).
    remember (nth_error s i). destruct e. intros. 
    remember (gen_row s (e a eq_refl) (l a eq_refl)). destruct s0. destruct s0.
    specialize (IHn _ _ _ _ _ H). destruct s ; simpl in * ; try congruence.
    apply IHn. congruence. intros. injection H ; subst. intros ; subst. auto.
  Qed.

  Lemma dfa_at_least_one : 
    forall n ag d, build_dfa n ag = Some d -> 
      0 < dfa_num_states d.
  Proof.
    intros n ag d. unfold build_dfa. 
    generalize (build_trans_len n ag) (build_trans_r n ag). 
    remember (build_transition_table n ag) as p.
    intros. destruct p ; try congruence. destruct s.
    generalize (build_table_at_least_one _ _ _ (eq_sym Heqp)). 
    injection H ; intros ; subst ; simpl. clear H e y. destruct x.
    contradiction H1. congruence. auto. simpl. auto with arith.
  Qed.

  (** Here's one table-based parser, which stops on the first match.
     It returns the [astgram] corresponding to the final state, an
     accumulated [xform] that can map us from the type of the [astgram]
     to the original grammar type [t], and the unconsumed tokens from [ts]. 
     This would be a whole lot faster if we were using a balanced finite
     map instead of lists.  But this version models arrays pretty well. 
  *)
  Section TABLE_PARSE.
    Variable d : DFA.
    Variable t : type.

    Definition coerce_dom (A A':type) (H:A=A') (B:Type) (f:interp A->B) : interp A' -> B.
      intros A A' H. rewrite H. apply (fun B (f:interp A'->B) => f).
    Defined.

    Fixpoint table_parse' (i:nat) (ts:list token_id) 
      (f:interp (astgram_type ((dfa_states d).[i])) -> interp t) : 
      option { a:astgram & ((interp (astgram_type a) -> interp t) * (list token_id))%type } := 
        if nth i (dfa_accepts d) false then
          (* we are in an accepting state -- since this is shortest match, stop here *)
          Some (existT _ ((dfa_states d).[i])  (f, ts))
        else 
          match ts with 
            | nil => None  (* already determined this state doesn't accept empty string *)
            | c::ts' => 
              (* our input token is c -- find the new state by looking up the
                 transition table row for the current state [i] *)
              match nth_error (dfa_transition d) i as p return 
                (nth_error (dfa_transition d) i = p) -> _
                with 
                | None => fun _ => None (* impossible *)
                | Some row => 
                  fun H => 
                    (* then look up the entry in column [c] of our row *)
                    match nth_error (row_entries row) c as q return 
                      (nth_error (row_entries row) c = q) -> _
                      with
                      | None => fun _ => None (* impossible *)
                      | Some e => 
                        (* and continue parsing with ts -- note that we have to 
                           compose the entry [e]'s [xform] with our accumulated
                           [xform]. *)
                        fun H' => table_parse' (next_state e) ts' 
                          (fun x => (coerce_dom (table_cast _ _ H) f) ((next_xform e) x))
                    end (eq_refl _)
              end (eq_refl _)
          end.
  End TABLE_PARSE.


  Definition coerce_rng (B B':type) (H:B=B') (A:Type) (f:A->interp B) : A->interp B'.
    intros B B' H. rewrite H. apply (fun A (f:A->interp B') => f).
  Defined.

  (** At the top-level, we take in a [grammar t], split it into an [astgram] [ag], and 
      fix-up function [f] that maps ASTs from [ag] into [t] values.  Then we build the
      [DFA], and then call [table_parse'].  Assuming that returns something, we 
      then take the resulting state and call [astgram_extract_ni] to get a list of
      AST values.  We then map the accumulated [xform] over those AST values to get
      back values of the type specified by [ag].  Finally, we apply the fix-up
      function [f] to the values to get back a list of [t] values.  *)
  Definition table_parse n t (g:grammar t) (ts:list token_id) : 
    option ((list token_id) * list (interp t)) := 
    let (ag, f) := split_astgram g in 
    match build_dfa n ag as d 
      return (build_dfa n ag = d) -> _ with 
      | None => fun _ => None
      | Some d => 
        fun H => 
          match table_parse' d _ 0 ts (fun x => x) with
            | None => None
            | Some (existT a' (xf, ts')) => 
              let vs := astgram_extract_nil a' in
                let xf' := coerce_rng (dfa_zero_coerce _ _ H) xf in 
                Some (ts', List.map (fun z => f (xf' z)) vs)
          end
    end (eq_refl _).

  (** Our real parser wants to be incremental, where we feed it one
      token at a time.  So an [instParserState] encapsulates the intermediate
      state of the parse engine, including the [DFA] and the current 
      state ([row_ps]) as well as the current fix-up function to transform
      us from the current state's type back to the original grammar type [t]. *)
  Record instParserState (t:type) := mkPS { 
    dfa_ps : DFA ; 
    row_ps : nat ; 
    row_ps_lt : row_ps < dfa_num_states (dfa_ps) ;
    fixup_ps : fixfn ((dfa_states dfa_ps).[row_ps]) t
  }.

  (** Build the initial [instParserState].  This must be an option because
      we don't know whether [n] is big enough to cause the [DFA] table generation
      to complete.  The initial fix-up function is obtained by taking the grammar
      and splitting it into an [astgram] and a fix-up function.  We then generate
      the [DFA] from this [astgram].  Finally, we start off in the initial state
      of the [DFA], which is 0. *)
  Definition opt_initial_parser_state (n:nat) t (g:grammar t) : option(instParserState t) :=
    let (ag, f) := split_astgram g in 
      match build_dfa n ag as x 
        return build_dfa n ag = x -> option (instParserState t) 
        with 
        | None => fun H => None
        | Some d => fun H => 
          Some (@mkPS _ d 0 (dfa_at_least_one _ _ H)
                  (coerce_dom (eq_sym (dfa_zero_coerce n ag H)) f))
      end (eq_refl _).  

  (** Given an [instParserState] and a token, advance the parser.  We first
      lookup the transition row of the current state ([row_ps ps]), and then
      extract the entry in that row corresponding to the token [tk].  These
      lookups will never fail, but we don't bother to show that here.  
      We then check to see if this new state [next_i] is an accepting state.  
      If so, we extract the abstract syntax values [vs] from the current state's
      [astgram] by calling [astgram_extract_nil].  We then apply the fixup-function
      to each value in this list, go get out a [t] value, where [t] is the
      original type of the grammar that was used to build the [DFA] and
      [instParserState].  If [next_i] is not an accepting state, then we
      update the fixup-function with the current entry's transform, and
      build a new [instParserState] where [next_i] becomes the current state. 
      Note that the caller can restart the parser even upon success. *)
  (* Todo:  the calculation of [astgram_extract_nil] can be done at DFA-generation
     time (and in fact, should be.)  Then we wouldn't even need the accepting
     state test, because if it's not accepting, we would get back an empty list.
  *)
  Definition parse_token t (ps:instParserState t) (tk:token_id) (tk_lt:tk < num_tokens) : 
    instParserState t * list (interp t).
  refine (fun t ps tk tk_lt => 
    let d := dfa_ps ps in 
      match nth_error (dfa_transition d) (row_ps ps) as p return
        (nth_error (dfa_transition d) (row_ps ps) = p) -> _ 
        with 
        | None => fun H => _
        | Some row => fun H => 
          match nth_error (row_entries row) tk as q return
            (nth_error (row_entries row) tk = q) -> _
            with 
            | None => fun H' => _
            | Some e => fun H' => 
              let f := next_xform e in 
              let next_i := next_state e in 
              let g := fun z => (fixup_ps ps) _ in
              let vs' := 
                (if nth next_i (dfa_accepts d) false then 
                  let ag' := nth next_i (dfa_states d) aZero in 
                  let vs := astgram_extract_nil ag' in 
                    List.map g vs 
                else 
                  nil) in
                (@mkPS _ d next_i _ g, vs')
          end (eq_refl _)
      end (eq_refl _)
  ). 
  generalize (dfa_transition_r d (row_ps ps)) ; rewrite H ; intro g ; rewrite <- g ;
  apply (f z).
  assert (next_state e < dfa_num_states d) ; auto.
  destruct e ; destruct d ; simpl in *. rewrite <- dfa_states_len0. auto.
  destruct row. destruct d. simpl in *. rewrite <- row_entries_len0 in tk_lt.
  generalize (nth_error_none _ _ H'). intro. assert False. omega. contradiction.
  generalize (nth_error_none _ _ H). intros. assert False ; [ idtac | contradiction ].
  generalize (row_ps_lt ps). intro. 
  generalize (dfa_transition_len (dfa_ps ps)). intro.
  rewrite <- H2 in H1. assert (row_ps ps >= length (dfa_transition (dfa_ps ps))). auto.
  omega.
  Defined.

End DFA.

Extraction Implicit table_parse [t].
Extraction Implicit opt_initial_parser_state [t].
Extraction Implicit parse_token [t].
Recursive Extraction parse_token.

(** [to_string] takes a grammar [a] and an abstract syntax value [v] of
    type [astgram_type a] and produces an optional string [s] with the property
    that [in_astgram a s v].  So effectively, it's a pretty printer for
    ASTs given a grammar.  It's only a partial function for two reasons:
    First, the type only describes the shape of the AST value [v] and not
    the characters within it.  If they don't match what's in the grammar,
    we must fail.  Second, the treatment of [aStar] in [in_astgram] demands
    that the strings consumed in the [InaStar_cons] case are non-empty.  
*)
Fixpoint to_string (a:astgram) : interp (astgram_type a) -> option (list char_p) :=
  match a return interp (astgram_type a) -> option (list char_p) with
    | aEps => fun (v:unit) => Some nil
    | aZero => fun (v:void) => match v with end
    | aChar c1 => fun (c2:char_p) => if char_dec c1 c2 then Some (c1::nil) else None
    | aAny => fun (c:char_p) => Some (c::nil)
    | aCat a1 a2 => 
      fun (v:(interp (astgram_type a1)) * (interp (astgram_type a2))) => 
        match to_string a1 (fst v), to_string a2 (snd v) with 
          | Some s1, Some s2 => Some (s1 ++ s2)
          | _, _ => None
        end
    | aAlt a1 a2 => 
      fun (v:(interp (astgram_type a1)) + (interp (astgram_type a2))) => 
        match v with 
          | inl v1 => to_string a1 v1
          | inr v2 => to_string a2 v2
        end
    | aStar a1 => 
      fun (v:list (interp (astgram_type a1))) => 
        List.fold_right 
        (fun v1 sopt => 
          match to_string a1 v1, sopt with
            | Some (c::s1), Some s2 => Some ((c::s1) ++ s2)
            | _, _ => None
          end) (Some nil) v
  end.

Lemma to_string_corr1 : forall a (v:interp (astgram_type a)) s, 
  to_string a v = Some s -> in_astgram a s v.
Proof.
  Ltac myinj :=     
    match goal with 
      | [ H : Some _ = Some _ |- _ ] => injection H ; intros ; clear H ; subst
      | _ => idtac
    end.
  induction a ; simpl ; intros ; eauto ; myinj ; try (destruct v ; eauto ; fail).
   destruct (char_dec c v) ; try congruence ; myinj ; eauto.
   destruct v as [v1 v2] ; simpl in *. remember (to_string a1 v1) as sopt1 ; 
   remember (to_string a2 v2) as sopt2 ; destruct sopt1 ; destruct sopt2 ; try congruence ;
   myinj ; eauto. 
   generalize s H. clear s H.
   induction v ; intros ; simpl in * ; myinj ; eauto.
   remember (to_string a a0) as sopt1. destruct sopt1 ; try congruence.
   destruct l ; try congruence.
   match goal with 
     | [ H : match ?e with | Some _ => _ | None => _ end = _ |- _] => 
       remember e as sopt2 ; destruct sopt2 ; try congruence
   end. myinj. specialize (IHa _ _ (eq_sym Heqsopt1)).
   eapply InaStar_cons ; eauto ; congruence.
Defined.

Lemma to_string_corr2 : forall a (s:list char_p) (v:interp (astgram_type a)),
  in_astgram a s v -> to_string a v = Some s.
Proof.
  induction 1 ; subst ; simpl ; mysimp ; try congruence ; 
  try (rewrite IHin_astgram1 ; try rewrite IHin_astgram2 ; auto).
  destruct s1 ; try congruence. auto.
Qed.

(*End NewParser.*)
(*End X86_BASE_PARSER.*)
