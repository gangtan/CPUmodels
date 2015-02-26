(** Gang Tan: Bi-directional grammars for both parsing and pretty-printing *)

Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
Require Import Coqlib.  (* for extensionality & proof_irrelevance *)
Require Import List.
Require Import Arith.
Require Import Bool.
Require Import Eqdep.
Require Import Omega.
Require Import CommonTacs.
Require Import Program.
Unset Automatic Introduction. 
Set Implicit Arguments.
Open Scope nat_scope.

Require Import Monad.
Local Open Scope monad_scope.

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

  Definition Byte_t := BitVector_t 7.
  Definition Half_t := BitVector_t 15.
  Definition Word_t := BitVector_t 31.
  Definition Double_Word_t := BitVector_t 63.
  Definition Ten_Byte_t := BitVector_t 79.

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
  repeat decide equality.
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

(** Bi-directional grammars, which are used to generate parsers and pretty printers. *)
(** Our user-facing [grammar]s, indexed by a [type], reflecting the type of the
    semantic value returned by the grammar when used in parsing. *)
(** After erasing the pretty-print functions, we can go easily from a bi-directional grammar 
    to a regular grammar that specifies parsing. 
    We can perform optimizations on regular grammars as usual. It seems we should
    avoid optimizations on bi-directional grammars, which requires adjustments on 
    both parse and pretty-print functions.
*)
Inductive bigrammar : type -> Type := 
| Eps : bigrammar Unit_t
| Zero : forall t, bigrammar t
| Char : char_p -> bigrammar Char_t
| Any : bigrammar Char_t
| Cat : forall t1 t2, bigrammar t1 -> bigrammar t2 -> bigrammar (Pair_t t1 t2)
| Alt : forall t1 t2, bigrammar t1 -> bigrammar t2 -> bigrammar (Sum_t t1 t2)
(* todo: add Star back *)
(* | Star : forall t, bigrammar t -> bigrammar (List_t t) *)
| Map : forall t1 t2, 
          (interp t1 -> interp t2) ->  (* a parse function *)
          (interp t2 -> option (interp t1)) ->  (* a pretty print function *)
          bigrammar t1 -> bigrammar t2.

(** Denotation of Bi-Grammars *)
(** I'm a little annoyed that I had to break out so many equalities, but
    found this worked a little better for both inversion and proving. *)
Inductive in_bigrammar : forall t, bigrammar t -> list char_p -> (interp t) -> Prop := 
| InEps : forall s v, s = nil -> v = tt -> in_bigrammar Eps s v
| InChar : forall c s v, s = c::nil -> v = c -> in_bigrammar (Char c) s v
| InAny : forall c s v, s = c::nil -> v = c -> in_bigrammar Any s v
| InCat : forall t1 t2 (g1:bigrammar t1) (g2:bigrammar t2) s1 s2 v1 v2 s v, 
    in_bigrammar g1 s1 v1 -> in_bigrammar g2 s2 v2 -> 
    s = s1 ++ s2 -> v = (v1,v2) -> in_bigrammar (Cat g1 g2) s v
| InAlt_l : forall t1 t2 (g1:bigrammar t1) (g2:bigrammar t2) s v1 v, 
    in_bigrammar g1 s v1 -> v = inl _ v1 -> in_bigrammar (Alt g1 g2) s v
| InAlt_r : forall t1 t2 (g1:bigrammar t1) (g2:bigrammar t2) s v2 v, 
    in_bigrammar g2 s v2 -> v = inr _ v2 -> in_bigrammar (Alt g1 g2) s v
(* | InStar_eps : forall t (g:bigrammar t) s v, s = nil -> v = nil -> in_bigrammar (Star g) s v *)
(* | InStar_cons : forall t (g:bigrammar t) s1 v1 s2 v2 s v,  *)
(*     in_bigrammar g s1 v1 -> in_bigrammar (Star g) s2 v2 ->  *)
(*     s1 <> nil -> s = s1 ++ s2 -> v = v1::v2 -> in_bigrammar (Star g) s v *)
| InMap : forall t1 t2 (f:interp t1 -> interp t2) (finv: interp t2 -> option (interp t1))
                 (g:bigrammar t1) s v1 v2, 
    in_bigrammar g s v1 -> v2 = f v1 -> in_bigrammar (@Map t1 t2 f finv g) s v2.
Hint Constructors in_bigrammar.

(** Explicit inversion principles for the grammars -- needed because
    of typing dependencies, though a little awkward that we can't just
    use [dependent inversion] to solve them. *)
Lemma EpsInv : forall cs v, in_bigrammar Eps cs v -> cs = nil /\ v = tt.
  intros. inversion H; crush.
Qed.
Lemma AnyInv : forall cs v, in_bigrammar Any cs v -> cs = v::nil.
  intros. inversion H ; subst ; crush.
Qed.
Lemma CharInv : forall c cs v, in_bigrammar (Char c) cs v -> cs = c::nil /\ v = c.
  intros. inversion H ; subst ; crush.
Qed.
Lemma CatInv : forall t1 t2 (g1:bigrammar t1) (g2:bigrammar t2) cs v, 
  in_bigrammar (Cat g1 g2) cs v -> 
  exists cs1, exists cs2, exists v1, exists v2, 
    in_bigrammar g1 cs1 v1 /\ in_bigrammar g2 cs2 v2 /\ cs = cs1++cs2 /\ v = (v1,v2).
Proof.
  intros. inversion H ; subst ; crush. eauto 8.
Qed.
Lemma AltInv : forall t1 t2 (g1:bigrammar t1) (g2:bigrammar t2) cs v, 
  in_bigrammar (Alt g1 g2) cs v -> 
  (exists v1, in_bigrammar g1 cs v1 /\ v = inl _ v1) \/
  (exists v2, in_bigrammar g2 cs v2 /\ v = inr _ v2).
Proof.
  intros ; inversion H ; subst ; crush; eauto.
Qed.
 (*Lemma StarInv : forall t (g:bigrammar t) cs v,  
   in_bigrammar (Star g) cs v -> (cs = nil /\ v = nil) \/  
   (exists cs1, exists v1, exists cs2, exists v2,  
     cs1 <> nil /\ in_bigrammar g cs1 v1 /\ in_bigrammar (Star g) cs2 v2 /\  
    cs = cs1 ++ cs2 /\ v = v1::v2).
 Proof. 
   intros ; inversion H ; clear H ; subst ; mysimp ; right ; exists s1 ; exists v1 ;  
   exists s2 ; exists v2 ; auto. 
 Qed. *)
Lemma MapInv : forall t1 t2 (f:interp t1 -> interp t2) finv (g:bigrammar t1) cs v,
  in_bigrammar (@Map t1 t2 f finv g) cs v -> exists v', in_bigrammar g cs v' /\ v = f v'.
Proof.
  intros ; inversion H ; subst ; crush. 
Qed.
Lemma ZeroInv : forall t cs v, in_bigrammar (Zero t) cs v -> False.
  intros ; inversion H.
Qed.
(*
Lemma XformInv : forall t1 t2 (x:t1->>t2) (g:grammar t1) cs v,
  in_bigrammar (Xform x g) cs v -> exists v', in_bigrammar g cs v' /\ v = xinterp x v'.
Proof.
  intros ; inversion H ; mysimp. exists v1. auto.
Qed.
*)

(** Tactic for invoking inversion principles on a proof that some string
    and value are in the denotation of a grammar.  We don't unroll the 
    [Star] case because that would loop. *)
Local Ltac in_inv := 
  repeat 
    match goal with 
      | [ H : in_bigrammar Eps _ _ |- _ ] => generalize (EpsInv H) ; clear H
      | [ H : in_bigrammar Any _ _ |- _ ] => generalize (AnyInv H) ; clear H
      | [ H : in_bigrammar (Char _) _ _ |- _ ] => generalize (CharInv H) ; clear H
      | [ H : in_bigrammar (Alt _ _) _ _ |- _ ] => generalize (AltInv H) ; clear H
      | [ H : in_bigrammar (Cat _ _) _ _ |- _ ] => generalize (CatInv H) ; clear H
      | [ H : in_bigrammar (Zero _) _ _ |- _ ] => contradiction (ZeroInv H)
      | [ H : in_bigrammar (Map _ _ _ _) _ _ |- _ ] => generalize (MapInv H) ; clear H
      | _ => idtac
    end.

Definition in_bigrammar_rng t (g: bigrammar t) (v: interp t) := 
  exists s, in_bigrammar g s v.

Definition bigrammar_rng_subset t1 t2 (g1: bigrammar t1) (f: interp t1 -> interp t2)
           (g2: bigrammar t2) := 
  forall v1, in_bigrammar_rng g1 v1 -> in_bigrammar_rng g2 (f v1).

Definition invertible t1 t2 (f:interp t1 -> interp t2) 
             (finv:interp t2 -> option (interp t1)) (g:bigrammar t1) := 
  (forall v:interp t1, 
     in_bigrammar_rng g v ->
     (* need the second conjunct to prove pretty_print_corr1 for the map case *)
     (exists v', finv (f v) = Some v' /\ in_bigrammar_rng g v')) /\
  (forall (v:interp t1) (w:interp t2), 
     in_bigrammar_rng g v -> finv w = Some v -> f v = w).

(* well-formedness of grammars *)
Fixpoint wf_grammar t (g:bigrammar t) : Prop := 
  match g with 
      | Cat t1 t2 g1 g2 => wf_grammar g1 /\ wf_grammar g2
      | Alt t1 t2 g1 g2 => wf_grammar g1 /\ wf_grammar g2
      (* | Star t g => wf_grammar g *)
      | Map t1 t2 f finv g => 
        wf_grammar g /\ invertible _ f finv g
      | g' => True
  end.

(* a well-formed bigrammar: a bigrammar with a proof that it is well-formed *)
Notation wf_bigrammar t := {g:bigrammar t | wf_grammar g}.

(********************************* Pretty Printer *************************************)

Fixpoint pretty_print t (g:bigrammar t) : interp t -> option (list char_p) :=
  match g in bigrammar t' return interp t' -> option (list char_p) with
    | Eps => fun v => Some nil
    | Char c => fun c' => if char_dec c c' then Some (c::nil) else None
    | Any => fun c => Some (c::nil)
    | Zero t => fun impos => None
    | Cat t1 t2 g1 g2 =>
      fun p =>
        s1 <- pretty_print g1 (fst p);
        s2 <- pretty_print g2 (snd p);
        ret (s1 ++ s2)
    | Alt t1 t2 g1 g2 =>
      fun v => match v with
                 | inl x1 => pretty_print g1 x1
                 | inr x2 => pretty_print g2 x2
               end
    (* | Star t g => *)
    (*   (* this is a non-tail-recusive version, which is easier to prover *) *)
    (*   fix loop (v:interp (List_t t)) : option (list char_p) := *)
    (*      match v with *)
    (*        | nil => Some nil *)
    (*        | hd::tl => *)
    (*          s' <- pretty_print g hd; *)
    (*          match s' with *)
    (*            | nil => None (* g cannot match the empty input list *) *)
    (*            | _ => s <- loop tl; ret s' ++ s *)
    (*          end *)
    (*      end *)
    (*   (* (fix loop (s : list char_p)(v:interp (List_t t)) : option (list char_p) := *) *)
    (*   (*    match v with *) *)
    (*   (*      | nil => Some s *) *)
    (*   (*      | hd::tl => *) *)
    (*   (*        s' <- pretty_print g hd; *) *)
    (*   (*        match s' with *) *)
    (*   (*          | nil => None (* g cannot match the empty input list *) *) *)
    (*   (*          | _ => loop (s ++ s') tl *) *)
    (*   (*        end *) *)
    (*   (*    end) nil *) *)
    | Map t1 t2 f finv g =>
      fun v => x <- finv v; pretty_print g x
  end.

Locate "<-".

Local Ltac localsimpl := 
  repeat 
    match goal with
      | [v: unit |- _ ] => destruct v
      | [ |- context[char_dec ?x ?y] ] => destruct (char_dec x y) 
      | [_: context[char_dec ?x ?y] |- _] => destruct (char_dec x y)
      | [H: wf_bigrammar _ |- _] => destruct H
      | _ => unfold invertible, in_bigrammar_rng in *; in_inv; crush
    end.

Lemma pretty_print_corr2: forall t (g:bigrammar t) (v:interp t) s,
  pretty_print g v = Some s -> wf_grammar g -> in_bigrammar g s v.
Proof. 
  induction g; try (localsimpl; fail).

  Case "Cat".
    localsimpl.
    destruct v. simpl in *.
    remember_head_in_hyp as e1; destruct e1; try discriminate.
    remember_head_in_hyp as e2; destruct e2; try discriminate.
    crush.

  Case "Alt".
    localsimpl.
    destruct v; eauto using InAlt_l, InAlt_r.

  (* Case "Star". *)
  (*   induction v; simprover. *)
  (*   remember_head_in_hyp as e1; destruct e1; try discriminate. *)
  (*   destruct l; try discriminate. *)
  (*   remember_head_in_hyp as e2; destruct e2; try discriminate. *)
  (*   eapply InStar_cons; (eauto || simprover). *)
  
  Case "Map".
    localsimpl.
    remember_head_in_hyp as e1; destruct e1; try discriminate.
    guess v H2. crush.
Qed.

Lemma pretty_print_corr1: forall t (g:bigrammar t) (v:interp t) s,
  in_bigrammar g s v -> wf_grammar g -> exists s', pretty_print g v = Some s'.
Proof. 
  induction g; try (localsimpl; fail).

  Case "Cat".
    localsimpl. crush_hyp.
    
  (* Case "Star". *)
  (*   induction v. simprover; eauto. *)
  (*   intros. *)
  (*   in_inv. *)
  (*   apply StarInv in H. *)
  (*   simprover. *)
  (*   assert (exists s1, pretty_print g x0 = Some s1); eauto. *)
  (*   assert (exists s2, pretty_print (Star g) x2 = Some s2); eauto. *)
  (*   simprover. *)
  (*   eexists. *)
  (*   simprover. *)
  (*   eauto. rewrite H3. *)
  (*   ??? *)
  
  Case "Map".
    localsimpl. guess x H1. crush.
Qed.

  (* the following is adapted from Decode.v *)
  Require Import String.
  Require Import Ascii.
  Require Import Bits.
  Require Import X86Syntax.


  Definition option_t x := User_t (Option_t x).
  Definition int_t := User_t Int_t.
  Definition register_t := User_t Register_t.
  Definition byte_t := User_t (BitVector_t 7).
  Definition half_t := User_t (BitVector_t 15).
  Definition word_t := User_t (BitVector_t 31).
  Definition double_word_t := User_t (BitVector_t 63).
  Definition ten_byte_t := User_t (BitVector_t 79).
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

  (* combinators for building parsers; those construtor should always return
     well-formed bigrammars as defined below *)

  Obligation Tactic := crush.

  Program Definition empty : wf_bigrammar Unit_t := Eps.
  Program Definition anybit : wf_bigrammar Char_t := Any.

  Program Definition bit (x:bool) : wf_bigrammar Char_t := Char x.
  Program Definition never t : wf_bigrammar t := Zero t.

  (* Note:  could have the test return option(a=b) instead of {a=b}+{a<>b}. *)
  Program Definition always t (teq : forall (a b:interp t), {a=b}+{a<>b})(x:interp t)
  : wf_bigrammar t := 
  @Map Unit_t t (fun (_:unit) => x) (fun y => if teq x y then Some tt else None) Eps.
  Next Obligation.
    localsimpl.
    destruct (teq x x); crush.
    destruct (teq x w); crush.
  Defined.

  Definition map t1 t2 (g:wf_bigrammar t1) (f:interp t1 -> interp t2) 
               (finv: interp t2 -> option (interp t1)) 
               (pf: invertible _ f finv (` g)) : wf_bigrammar t2.
    intros.
    refine (exist (fun g0 : bigrammar t2 => wf_grammar g0)
                  (Map t2 f finv (` g)) _).
    destruct g. simpl. auto.
  Defined.
  Implicit Arguments map [t1 t2].

  Program Definition seq t1 t2 (p1:wf_bigrammar t1) (p2:wf_bigrammar t2) : wf_bigrammar (Pair_t t1 t2) :=
    Cat p1 p2.
  Next Obligation. localsimpl. localsimpl.
  Defined.

  (* Definition cons t (pair : interp (Pair_t t (List_t t))) : interp (List_t t) :=  *)
  (*   (fst pair)::(snd pair). *)

  (* doesn't seem this is used *)
  (* Definition seqs t (ps:list (wf_bigrammar t)) : wf_bigrammar (List_t t) :=  *)
  (*   List.fold_right (fun p1 p2 => map (seq p1 p2) (@cons t))  *)
  (*     (@always (List_t t) (@nil (interp t))) ps. *)

  Program Definition alt t1 t2 (p1:wf_bigrammar t1) (p2:wf_bigrammar t2) : 
    wf_bigrammar (Sum_t t1 t2) :=
    Alt p1 p2.
  Next Obligation. localsimpl. localsimpl.
  Defined.



  (* a union operator for two grammars; should always avoid to use *)
  Program Definition union t (g1 g2:wf_bigrammar t) : wf_bigrammar t := 
    @Map (Sum_t t t) t 
         (fun w : interp (Sum_t t t) => match w with inl x => x | inr y => y end)
         (fun v : interp t => 
            match pretty_print (Alt g1 g2) (inl _ v) with 
              | Some _ => Some (inl _ v)
              | None => match pretty_print (Alt g1 g2) (inr _ v) with 
                          | Some _ => Some (inr _ v)
                          | None => None
                        end
            end)
         (Alt g1 g2).
  Next Obligation.
    localsimpl. localsimpl.

    unfold invertible; split.

    Case "prop1".
      generalize pretty_print_corr1, pretty_print_corr2; intros.
      destruct v.

      remember_destruct_head as v1; eauto.
      remember_destruct_head as v2; eauto.
      repeat (localsimpl; in_inv). eexists. eauto.
      localsimpl. guess x1 H. crush.

      localsimpl.
      remember_destruct_head as v1. eauto 6.
      remember_destruct_head as v2. eauto 6.
      repeat (crush; in_inv).
      guess x1 H. crush.

    Case "prop2".
      crush.
      remember_head_in_hyp as e1; destruct e1; try crush.
      remember_head_in_hyp as e2; destruct e2; crush.
  Defined.

  Fixpoint unions0 t (ps:list (wf_bigrammar t)) : wf_bigrammar t := 
    match ps with 
      | nil => @never t
      | p::nil => p
      | p::rest => union p (unions0 rest)
    end.

  Fixpoint half A (xs ys zs: list A) : (list A) * (list A) := 
    match xs with 
      | nil => (ys,zs) 
      | h::t => half t zs (h::ys)
    end.

  Fixpoint unions' n t (ps:list (wf_bigrammar t)) : wf_bigrammar t := 
    match n, ps with 
      | 0, _ => unions0 ps
      | S n, nil => @never t
      | S n, p::nil => p
      | S n, ps => 
        let (ps1,ps2) := half ps nil nil in 
          let g1 := unions' n ps1 in 
            let g2 := unions' n ps2 in 
              union g1 g2
    end.

  Definition unions t (ps:list (wf_bigrammar t)) : wf_bigrammar t := unions' 20 ps.

  (* Biased union: the pretty printer for "g1 + g2" always uses the left
     pretty printer; it requires the second grammar's range is a subset of
     the first grammar's *)
  Program Definition biased_union t1 t2 (g1: wf_bigrammar t1) (g2: wf_bigrammar t2)
          (f: interp t2 -> interp t1)
          (pfs: bigrammar_rng_subset g2 f g1) : wf_bigrammar t1 := 
    @Map (Sum_t t1 t2) t1
         (fun v : interp (Sum_t t1 t2) => match v with inl x => x | inr y => f y end)
         (fun w : interp t1 => Some (inl w))
         (Alt g1 g2).
  Next Obligation.
    localsimpl. localsimpl.

    unfold invertible; split.
    Case "prop1".
      intros. destruct v. crush.
      unfold bigrammar_rng_subset, in_bigrammar_rng in *.
      guess i pfs. 
      assert (exists s, in_bigrammar (` g2) s i). 
        crush. in_inv. crush. inversion H0. crush.
      apply pfs in H0.
      crush.
    Case "prop2". crush.
  Defined.

  Fixpoint bits_n (n:nat) : type := 
    match n with 
      | 0%nat => Unit_t
      | S n => Pair_t Char_t (bits_n n)
    end.

  Fixpoint bits (x:string) : wf_bigrammar (bits_n (String.length x)) := 
    match x with 
      | EmptyString => empty
      | String c s => 
        (seq (bit (if ascii_dec c "0"%char then false else true)) (bits s))
    end.

  (* notation for building parsers *)
  Infix "|+|" := alt (right associativity, at level 80).
  Infix "|\/|" := union (right associativity, at level 80).
  Infix "$" := seq (right associativity, at level 70).
  Notation "e %% t" := (e : interp t) (at level 80).
  Notation "g @ f & finv & pf" :=(map g f finv pf) (at level 75).
  (* Infix "@" := map (right associativity, at level 75). *)

  Fixpoint string_to_bool_list (s:string) : list bool := 
    match s with
      | EmptyString => nil
      | String a s => 
        (if ascii_dec a "0"%char then false else true)::(string_to_bool_list s)
    end.

  Fixpoint bits_of_string (s:string): interp (bits_n (String.length s)) := 
    match s with
      | EmptyString => tt
      | String a s =>
        (if ascii_dec a "0"%char then false else true, bits_of_string s)
    end.

  Lemma in_bits_intro: forall str,
    in_bigrammar (` (bits str)) (string_to_bool_list str) (bits_of_string str).
  Proof. induction str; localsimpl. Qed.

  Lemma in_bits_elim: 
    forall str s v, in_bigrammar (` (bits str)) s v ->
                    s = string_to_bool_list str /\ v = bits_of_string str.
  Proof. induction str; localsimpl; destruct (ascii_dec a "0"); crush_hyp.
  Qed.

  Obligation Tactic := auto.

  Definition bitsleft t (s:string) (p:wf_bigrammar t) : wf_bigrammar t.
    intros.
    refine ((bits s $ p) @ (@snd _ _) & (fun v => Some (bits_of_string s, v)) & _).
    localsimpl.
    crush' in_bits_elim fail.
  Defined.
  Infix "$$" := bitsleft (right associativity, at level 70).

  Lemma in_bitsleft_intro: forall t (g: wf_bigrammar t) str s1 s2 v1 v2,
    in_bigrammar (` (bits str)) s1 v1 -> in_bigrammar (` g) s2 v2
      -> in_bigrammar (` (str $$ g)) (s1 ++ s2)%list v2.
  Proof. crush. Qed.

  Lemma in_bitsleft_elim: forall t str (g: wf_bigrammar t) s (v:interp t),
    in_bigrammar (` (str $$ g)) s v -> 
    exists s1 s2, s = (s1 ++ s2)% list /\ in_bigrammar (` g) s2 v.
  Proof. intros.
    simpl in H. in_inv. crush. destruct x.
    in_inv. crush.
  Qed.

  (* Mapping old definitions to new -- we should substitute these away when
     we replace Decode.v with NewDecode.v. *)
  Definition parser r := wf_bigrammar r.
  Definition char_t := Char_t.
  Definition result_m := interp.
  Definition result := type.
  Definition pair_t := Pair_t.
  Definition list_t := List_t.
  Definition unit_t := Unit_t.
  Definition tipe_t := User_t.
  Definition Any_p := Any.
  Definition Eps_p := Eps.

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

  (* convert a sequence of bits to a signature function that maps position indexes
     to bits so that we are not restricted by the right-associateness of the bits
      when processing them;
     position indexes in the signature function start at 0 *)
  Fixpoint bits2sig (n:nat) : interp (bits_n n) -> (Z -> bool) := 
    match n with
      | O => fun _ _ => false
      | S n' => 
        fun v =>
          let f' := bits2sig n' (snd v) in
          fun x => if zeq x (Z_of_nat n') then fst v else f' x
    end.

  Fixpoint sig2bits (n:nat) (f:Z->bool) : interp (bits_n n) :=
    match n with
      | O => tt
      | S n' => (f (Z_of_nat n'), sig2bits n' f)
    end.

  Definition bits2int (n:nat) (v:interp (bits_n n)) : interp int_t := 
    Word.Z_of_bits n (bits2sig n v).

  Definition int2bits (n:nat) (i:interp int_t) : option (interp (bits_n n)) := 
    if (zle (0%Z) i) then
      if (zlt i (two_power_nat n)) then 
        Some (sig2bits n (Word.bits_of_Z n i))
      else None
    else None.

  (* equality of two signature functions below index n *)
  Definition sig_eq_below n (f1 f2: Z -> bool) := 
    forall z, (0 <= z < Z_of_nat n)%Z -> f1 z = f2 z.

  Lemma sig2bits_exten : 
    forall n f1 f2, sig_eq_below n f1 f2 -> sig2bits n f1 = sig2bits n f2.
  Proof. induction n. crush.
    crush. unfold sig_eq_below in *.
    rewrite (IHn f1 f2).
    rewrite H. trivial.
    nat_to_Z; omega.
    intros; apply H. 
    nat_to_Z; omega.
  Qed.

  Lemma sig2bits_bits2sig : forall n v, sig2bits n (bits2sig n v) = v.
  Proof. induction n. localsimpl.
    crush.
    destruct_head; try omega.
    assert (sig_eq_below n 
              (fun x => if zeq x (Z.of_nat n) then fst v else bits2sig n (snd v) x)
              (bits2sig n (snd v))).
       unfold sig_eq_below.
       intros. destruct_head; try omega. trivial.
    erewrite sig2bits_exten by eauto.
    destruct v. crush.
  Qed.

  Lemma bits2sig_sig2bits :
    forall n f, sig_eq_below n (bits2sig n (sig2bits n f)) f.
  Proof. 
    unfold sig_eq_below. induction n.
    Case "n=0". simpl. intros. omega.
    Case "S n".
    crush.
    destruct_head. congruence.
      rewrite Zpos_P_of_succ_nat in *.
      eapply IHn.
      omega.
  Qed.

  Lemma bits2int_range : forall n v, (0 <= bits2int n v < two_power_nat n)%Z.
  Proof. unfold bits2int. intros.
    destruct n. 
      crush. 
      unfold two_power_nat, shift_nat. simpl. omega.
      apply Word.Z_of_bits_range.
  Qed.
  
  Lemma int2bits_bits2int : forall n v, int2bits n (bits2int n v) = Some v.
  Proof. 
    unfold int2bits; intros.
    use_lemma (bits2int_range n v) by trivial.
    repeat (destruct_head; try omega).
    unfold bits2int.
    assert (sig_eq_below n (Word.bits_of_Z n (Word.Z_of_bits n (bits2sig n v)))
              (bits2sig n v)).
      generalize Word.bits_of_Z_of_bits. unfold sig_eq_below. crush.
    erewrite sig2bits_exten by eauto.
    erewrite sig2bits_bits2sig. auto.
  Qed.

  Lemma bits2int_int2bits : 
    forall n i v, int2bits n i = Some v -> bits2int n v = i.
  Proof.
    unfold bits2int, int2bits in *. intros.
    destruct_head in H; try congruence.
    destruct_head in H; try congruence.
    crush.
    assert (sig_eq_below n (bits2sig n (sig2bits n (Word.bits_of_Z n i)))
                         (Word.bits_of_Z n i)).
      eapply bits2sig_sig2bits.
    erewrite Word.Z_of_bits_exten by eauto.
    destruct n. 
      unfold two_power_nat, shift_nat in *. simpl in *. omega.
      apply Word.Z_of_bits_of_Z_lt_modulus.
      crush.
  Qed.

  Definition field (n:nat) : wf_bigrammar int_t.
    intros.
    refine ((field' n) @ (bits2int n) & int2bits n & _).
    localsimpl.
    Case "Prop1".
      crush' int2bits_bits2int fail.

    Case "Prop2".
      eapply bits2int_int2bits. trivial.
  Defined.

  Definition int_to_bool_list n v := 
    (flatten_bits_n n (sig2bits n (Word.bits_of_Z n v))).

  Lemma in_field_intro:
    forall n v, (0 <= v < two_power_nat n)%Z ->
                in_bigrammar (` (field n)) (int_to_bool_list n v) v.
  Proof. intros.
    eapply InMap. eapply in_field'_intro.
    unfold bits2int in *.
    assert (sig_eq_below n (bits2sig n (sig2bits n (Word.bits_of_Z n v)))
                         (Word.bits_of_Z n v)).
      eapply bits2sig_sig2bits.
    erewrite Word.Z_of_bits_exten by eauto.
    destruct n. 
      unfold two_power_nat, shift_nat in *. simpl in *. omega.
      rewrite (Word.Z_of_bits_of_Z_lt_modulus). trivial.
      unfold Word.modulus. trivial.
  Qed.

  Lemma field_range : 
    forall n i, in_bigrammar_rng (` (field n)) i -> (0 <= i < two_power_nat n)%Z.
  Proof. unfold field, in_bigrammar_rng. 
    intros. crush; in_inv; crush' bits2int_range fail.
  Qed.

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

  Local Ltac r2ztac := 
    repeat match goal with 
             | [w:Z |- _ ] => destruct w; (discriminate || eauto)
             | [ _ : context[match ?p with xH => _ | xI _  | xO _ => _ end] |- _ ]
               => destruct p; (discriminate || eauto)
           end.

  Lemma register_to_Z_inv1 : 
    forall z, (0 <= z < 8)%Z -> register_to_Z (Z_to_register z) = z.
  Proof. intros.
    remember (Z_to_register z) as r; destruct r; unfold Z_to_register in *; 
    r2ztac; simpl in *; pos_to_Z; omega.
  Qed.

  Lemma register_to_Z_inv2 : forall r, Z_to_register (register_to_Z r) = r.
  Proof. destruct r; crush. Qed.

  Local Ltac lineararith := 
    unfold two_power_nat, shift_nat in *; simpl in *; omega.


  Definition reg : wf_bigrammar register_t.
    refine (field 3 @ (Z_to_register : _ -> result_m register_t)
              & (fun r => Some (register_to_Z r)) & _).
    unfold invertible; split.

    Case "prop1".
      intros v H.
      assert (0 <= v < 8)%Z.
      use_lemma field_range by eauto. lineararith.
      use_lemma register_to_Z_inv1 by eauto.
      crush.

    Case "prop2".
      generalize register_to_Z_inv2. crush.
  Defined.

  Definition int_n : forall n, wf_bigrammar (User_t (BitVector_t n)).
    intro.
    refine ((field (S n)) @ (@Word.repr n : _ -> result_m (User_t (BitVector_t n)))
              & fun b => Some (@Word.unsigned n b) & _).
    unfold invertible; split.
    Case "prop1".
      intros v H.
      assert (0 <= v <= Word.max_unsigned n)%Z.
        use_lemma field_range by eauto. 
        unfold Word.max_unsigned, Word.modulus.
        rewrite two_power_nat_S in *.
        omega.
      use_lemma Word.unsigned_repr by eauto.
      crush.

    Case "prop2".
      intros. crush.
      apply Word.repr_unsigned.
  Defined.

  Lemma in_int_n_intro:
    forall n (v: Word.int n), 
      in_bigrammar (` (int_n n)) (int_to_bool_list (S n) (Word.unsigned v)) v.
  Proof. intros. 
    eapply InMap.
    eapply in_field_intro.
    eapply Word.unsigned_range.
    SearchAbout Word.repr.
    rewrite Word.repr_unsigned. trivial.
  Qed.


  Definition byte : wf_bigrammar byte_t := int_n 7.
  Definition halfword : wf_bigrammar half_t := int_n 15.
  Definition word : wf_bigrammar word_t := int_n 31.

  (* I used the above parsers for halfword and word because they are
     easier for the proofs. Would the following defs of halfword
     and word from Decode.v be more efficient? We just need to show
     they are equivalent

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

  Lemma condition_type_to_Z_inv1 : 
    forall z, (0 <= z < 16)%Z -> condition_type_to_Z (Z_to_condition_type z) = z.
  Proof. intros.
    remember (Z_to_condition_type z) as ct;
    destruct ct; unfold Z_to_condition_type in *;
    r2ztac;
    simpl in *; pos_to_Z; omega.
  Qed.

  Lemma condition_type_to_Z_inv2 : 
    forall ct, Z_to_condition_type (condition_type_to_Z ct) = ct.
  Proof. destruct ct; crush. Qed.

  Definition tttn : wf_bigrammar condition_t. 
    refine ((field 4) @ (Z_to_condition_type : _ -> result_m condition_t)
              & (fun ct => Some (condition_type_to_Z ct)) & _).
    unfold invertible. split.
    Case "prop1".
      intros v H.
      assert (0 <= v < 16)%Z.
      use_lemma field_range by eauto. lineararith.
      use_lemma condition_type_to_Z_inv1 by eauto.
      crush.

    Case "prop2".
      generalize condition_type_to_Z_inv2. crush.
  Defined.

  (* perform signed casts from a bitvector of width s1 to a bitvector of width s2 *)
  Definition sign_cast (s1 s2: nat) (w: Word.int s1) : Word.int s2 :=
    Word.repr (Word.signed w).

  (* checking whether a signed cast does not lose info *)
  Definition safe_sign_cast (s1 s2: nat) (w: Word.int s1) : bool := 
    if (Z_le_dec (@Word.min_signed s2) (Word.signed w)) then
      if (Z_le_dec (Word.signed w) (@Word.max_signed s2)) then true
      else false
    else false.

  Lemma safe_sign_cast_sound : forall s1 s2 (w: Word.int s1),
    safe_sign_cast s2 w = true ->
      (@Word.min_signed s2 <= Word.signed w <= @Word.max_signed s2)%Z.
  Proof. unfold safe_sign_cast. intros.
    repeat (destruct_head in H; try discriminate).
    crush.
  Qed.

  Lemma min_signed_monotone:
    forall s1 s2, s1 <= s2 -> (Word.min_signed s2 <= Word.min_signed s1)%Z.
  Proof. unfold Word.min_signed, Word.half_modulus, Word.modulus,
         Word.wordsize in *.
    intros.
    assert ((two_power_nat (S s1) / 2) <= two_power_nat (S s2) / 2)%Z.
      apply Z_div_le. omega.
      eapply two_power_nat_monotone. omega.
    omega.
  Qed.
    
  Lemma max_signed_monotone:
    forall s1 s2, s1 <= s2 -> (Word.max_signed s1 <= Word.max_signed s2)%Z.
  Proof. unfold Word.max_signed, Word.half_modulus, Word.modulus,
         Word.wordsize in *.
    intros.
    assert ((two_power_nat (S s1) / 2) <= two_power_nat (S s2) / 2)%Z.
      apply Z_div_le. omega.
      eapply two_power_nat_monotone. omega.
    omega.
  Qed.

  Lemma wider_safe_sign_cast : forall s1 s2 (w:Word.int s1),
    s1 <= s2 -> safe_sign_cast s2 w = true.                                 
  Proof. intros. unfold safe_sign_cast.
    use_lemma (Word.signed_range s1 w) by auto.
    use_lemma min_signed_monotone by eauto.
    use_lemma max_signed_monotone by eauto.
    repeat (destruct_head; try omega).
    trivial.
  Qed.
    
  Lemma sign_cast_inv :
    forall (s1 s2: nat) (w: Word.int s1), 
      safe_sign_cast s2 w = true ->
      @sign_cast s2 s1 (@sign_cast s1 s2 w) = w.
  Proof. intros. unfold sign_cast.
    use_lemma safe_sign_cast_sound by eauto.
    rewrite Word.signed_repr by trivial.
    rewrite Word.repr_signed. trivial.
  Qed.

  Lemma sign_cast_rev_safe: forall s1 s2 w,
    @safe_sign_cast s2 s1 (@sign_cast s1 s2 w) = true.
  Proof. intros.
    destruct (le_gt_dec s2 s1).
      apply wider_safe_sign_cast. trivial.
      unfold safe_sign_cast, sign_cast.
      generalize (Word.signed_range s1 w); intro.
      rewrite Word.signed_repr.
      repeat (destruct_head; try omega). trivial.
      use_lemma (@min_signed_monotone s1 s2) by omega.
      use_lemma (@max_signed_monotone s1 s2) by omega.
      omega.
  Qed.


Lemma ibrv2: forall v,
  in_bigrammar_rng (` (bits "000" |+| bits "001" |+| bits "010" |+|
     bits "011" |+| bits "110" |+| bits "111" )) v ->
  v = inl (bits_of_string "000") \/
  v = inr (inl (bits_of_string "001")) \/
  v = inr (inr (inl (bits_of_string "010"))) \/
  v = inr (inr (inr (inl (bits_of_string "011")))) \/
  v = inr (inr (inr (inr (inl (bits_of_string "110"))))) \/
  v = inr (inr (inr (inr (inr (bits_of_string "111"))))).
Proof.
  unfold in_bigrammar_rng. intros. crush. 
  
  apply AltInv in H. crush. repeat (in_inv; crush).
  apply AltInv in H. crush. repeat (in_inv; crush).
  apply AltInv in H. crush. repeat (in_inv; crush).
  apply AltInv in H. crush. repeat (in_inv; crush).
  apply AltInv in H. crush. repeat (in_inv; crush).
    right. right. right. right. left. reflexivity.
  repeat (in_inv; crush).
    right. right. right. right. right. reflexivity.
Qed.



Definition rm00_1 : wf_bigrammar address_t.
  refine(
    ((bits "000") |+| (bits "001") |+| (bits "010") |+| 
     (bits "011") |+| (bits "110") |+| (bits "111"))
  @ (fun s =>
       (match s with
         | inl bs | inr (inl bs) 
         | inr (inr (inl bs)) 
         | inr (inr (inr (inl bs))) 
         | inr (inr (inr (inr (inl bs)))) 
         | inr (inr (inr (inr (inr bs)))) =>
             (mkAddress (Word.repr 0) (Some (Z_to_register(bits2int 3 bs))) None)
       end) %% address_t)
  & (fun a =>
       if Word.eq (addrDisp a) (Word.repr 0) then
         (match (addrBase a), (addrIndex a) with
           | Some EAX, None => 
               Some (inl (bits_of_string "000"))
           | Some ECX, None =>
               Some (inr (inl (bits_of_string "001")))
           | Some EDX, None =>
               Some (inr (inr (inl (bits_of_string "010"))))
           | Some EBX, None =>
               Some (inr (inr (inr (inl (bits_of_string "011")))))
           | Some ESI, None =>
               Some (inr (inr (inr (inr (inl (bits_of_string "110"))))))
           | Some EDI, None =>
               Some (inr (inr (inr (inr (inr (bits_of_string "111"))))))
           | _, _ => None
         end)
       else None)
  & _).
Proof.
  unfold invertible. split. 
  Case "invertible 1".
    intros. exists v. split. 
    SCase "finv (f v) = Some v".
      apply ibrv2 in H.
      repeat match goal with 
               | [H: ?V = _ \/ _ |- _] =>
                 destruct H; [(subst v; simpl; trivial) | idtac]
             end.
      subst v; simpl; trivial.
    SCase "in_bigrammar_rng g v". assumption.
  Case "invertible 2".
    intros.
    destruct w. simpl in H0.
    remember_rev (Word.eq (addrDisp) (Word.repr 0)) as ae.
    destruct ae; [idtac | discriminate].
    destruct addrBase; [idtac | discriminate].
    apply Word.int_eq_true_iff2 in Hae.
    destruct r;
      (destruct addrIndex; [discriminate | inversion H0; crush]).
Qed.


  (* (* a more efficient version for testing if a signed 32-bit immediate can *)
  (*    be represented in a byte; that is, if it's within [-128,127] *) *)
  (* Definition repr_in_signed_byte (imm:int32) := *)
  (*   andb (Word.lt imm (Word.repr 128)) (Word.lt (Word.repr (-129)) imm). *)
  
  (* Lemma repr_in_signed_byte_sound : forall imm, *)
  (*   repr_in_signed_byte imm = safe_signed_cast 7 imm. *)
  (* Proof. intro. unfold repr_in_signed_byte, safe_signed_cast. *)
     
  Definition sign_i32_to_i8 (w:int32) : int8 := @sign_cast 31 7 w.

  Lemma sign_extend8_32_inv1 : 
    forall w, sign_i32_to_i8 (sign_extend8_32 w) = w.
  Proof. intros.
    unfold sign_i32_to_i8, sign_extend8_32.
    use_lemma (@wider_safe_sign_cast 7 31 w) by omega.
    apply sign_cast_inv; trivial.
  Qed.

  Lemma sign_extend8_32_inv2 : 
    forall w, safe_sign_cast 7 w = true ->
              (sign_extend8_32 (sign_i32_to_i8 w)) = w.
  Proof. 
    unfold sign_i32_to_i8, sign_extend8_32 in *.
    intros. 
    apply sign_cast_inv; trivial.
  Qed.


  (* --------------------------------------------------------------------- *)
  (* the following x86 bigrammar uses unions for alternatives and is therefore
     efficient *)

  Definition AAA_p' : wf_bigrammar instruction_t.
    refine ("00110111" $$ empty @ (fun x => AAA %% instruction_t)
               & (fun i => match i with | AAA => Some tt | _ => None end) & _).
    unfold invertible. split.
    crush. destruct v. crush.
    crush. destruct w; crush.
  Defined.

  Definition AAD_p' : wf_bigrammar instruction_t.
    refine ("1101010100001010" $$ empty @ (fun x => AAD %% instruction_t)
              & (fun i => match i with | AAD => Some tt | _ => None end) & _).
    unfold invertible. split.
    crush. destruct v. crush.
    crush. destruct w; crush.
  Defined.

  Definition AAM_p' : wf_bigrammar instruction_t.
    refine ("1101010000001010" $$ empty @ (fun x => AAM %% instruction_t)
              & (fun i => match i with | AAM => Some tt | _ => None end) & _).
    unfold invertible. split.
    crush. destruct v. crush.
    crush. destruct w; crush.
  Defined.

    Definition AAS_p' : wf_bigrammar instruction_t.
    refine ("00111111" $$ empty @ (fun x => AAS %% instruction_t)
              & (fun i => match i with | AAS => Some tt | _ => None end) & _).
    unfold invertible. split.
    crush. destruct v. crush.
    crush. destruct w; crush.
  Defined.

(* Print wf_bigrammar. *)
(* Print instruction_t. *)

  Definition BSWAP_p' : wf_bigrammar instruction_t.
    refine ("0000" $$ "1111" $$ "1100" $$ "1" $$ reg
              @ (fun r => BSWAP r %% instruction_t)
              & (fun i => match i with | BSWAP r => Some r | _ => None end) & _).
    unfold invertible. split.
    crush. 
    crush. destruct w; crush.
  Defined.

  Definition IN_p1' : wf_bigrammar instruction_t.
    refine ("1110" $$ "010" $$ anybit $ byte
              @ (fun p => let (w,pt) := p in IN w (Some pt) %% instruction_t)
              & (fun i => match i with | IN w (Some pt) => Some (w,pt) | _ => None end)
              & _).
    unfold invertible. split.
    destruct v; crush. 
    crush. destruct w; crush.
    destruct p; crush.
  Defined.
    
  Definition IN_p2' : wf_bigrammar instruction_t.
    refine ("1110" $$ "010" $$ anybit
              @ (fun w => IN w None %% instruction_t)
              & (fun i => match i with | IN w None => Some w | _ => None end)
              & _).
    unfold invertible. split.
    destruct v; crush. 
    crush. destruct w; crush.
    destruct p; crush.
  Defined.

  Definition IN_p' := IN_p1' |\/| IN_p2'.

  Definition Jcc_p1' : wf_bigrammar instruction_t.
    refine ("0111" $$ tttn $ byte
              @  (fun p => let (ct,imm) := p in 
                           Jcc ct (sign_extend8_32 imm) %% instruction_t)
              & (fun i => 
                   match i with
                     | Jcc ct imm => 
                       if (safe_sign_cast 7 imm) then Some (ct, sign_i32_to_i8 imm)
                       else None
                     | _ => None
                   end)
              & _).
    unfold invertible. split.
    intro. destruct v.
      remember_destruct_head as tst.
      rewrite sign_extend8_32_inv1. crush.
      unfold in_bigrammar_rng. intro.
      destruct H. apply in_bitsleft_elim in H.
      crush; in_inv. crush.
      use_lemma (@sign_cast_rev_safe 7 31 x4) by auto.
      unfold sign_extend8_32, sign_cast in *. congruence.

    intros. destruct w; crush.
    destruct v; crush.
    remember_head_in_hyp as tst; destruct tst; try discriminate.
    crush.
    rewrite sign_extend8_32_inv2 by trivial. trivial.
  Defined.

  Definition Jcc_p2': wf_bigrammar instruction_t.
    refine ("0000" $$ "1111" $$ "1000" $$ tttn $ word
             @ (fun p => let (ct,imm) := p in Jcc ct imm %% instruction_t)
              & (fun i => 
                   match i with
                     | Jcc ct imm => Some (ct, imm)
                     | _ => None
                   end)
              & _).
    unfold invertible; split.    
    intros. destruct v. crush.

    intros. destruct v. destruct w; crush.
  Defined.

  Definition Jcc_p': wf_bigrammar instruction_t :=
    Jcc_p1' |\/| Jcc_p2'.

  Definition instruction_grammar' := unions [AAA_p'; BSWAP_p'; IN_p'; Jcc_p'].

  (* --------------------------------------------------------------------- *)
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

  Definition AAA_p : wf_bigrammar unit_t := "00110111" $$ empty.
  Definition AAD_p : wf_bigrammar unit_t := "1101010100001010" $$ empty.
  Definition AAM_p : wf_bigrammar unit_t := "1101010000001010" $$ empty.
  Definition AAS_p : wf_bigrammar unit_t := "00111111" $$ empty.

  Definition BSWAP_p : wf_bigrammar register_t := 
    "0000" $$ "1111" $$ "1100" $$ "1" $$ reg.
    
  Definition CDQ_p : wf_bigrammar unit_t := "1001" $$  "1001" $$ empty.
  Definition CLC_p : wf_bigrammar unit_t := "1111" $$ "1000" $$ empty.
  Definition CLD_p : wf_bigrammar unit_t := "1111" $$ "1100" $$ empty.
  Definition CLI_p : wf_bigrammar unit_t := "1111" $$ "1010" $$ empty.
  Definition CLTS_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "0000" $$ "0110" $$ empty.
  Definition CMC_p : wf_bigrammar unit_t := "1111" $$ "0101" $$ empty.
  Definition CMPS_p : wf_bigrammar Char_t := "1010" $$ "011" $$ anybit.
  (*Skipped CMPXCHG_p, requires modrm*)
  Definition CPUID_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "1010" $$ "0010" $$ empty.
  Definition CWDE_p : wf_bigrammar unit_t := "1001" $$ "1000" $$ empty.
  Definition DAA_p : wf_bigrammar unit_t := "0010" $$ "0111" $$ empty.
  Definition DAS_p : wf_bigrammar unit_t := "0010" $$ "1111" $$ empty.

  Definition DEC_p1  :=
    "1111" $$ "111" $$ anybit $ "11001" $$ reg.
  Definition DEC_p2 := "0100" $$ "1" $$ reg.
  (*Definition DEC_p3 : //Skipped due to ext_op_modrm function*)
  
  Definition DIV_p1 : wf_bigrammar (Pair_t Char_t register_t) := 
  "1111" $$ "011" $$ anybit $ "11110" $$ reg.
  (*Definition DIV_p2 : //Skipped due to ext_op_modrm function*)
  
  Definition HLT_p : wf_bigrammar unit_t := "1111" $$ "0100" $$ empty.
  
  Definition IDIV_p1 : wf_bigrammar (Pair_t Char_t register_t)  :=
 "1111" $$ "011" $$ anybit $ "11111" $$ reg.
 (*Definition IDIV_p2 : //ext_op_modrm function*)
 
 (*Definition IMUL_p : //ext_op_modrm, modrm*)
 
  Definition IN_p1 := "1110" $$ "010" $$ anybit $ byte.
  Definition IN_p2 := "1110" $$ "010" $$ anybit.
  
  (*Definition IN_P : wf_bigrammar (pair_t char_t (User_t (Option_t Byte_t))) :=
  IN_p1 |+| IN_p2.*)
  
  (*Definition IN_p := IN_p1 |+| IN_p2.
Check IN_p.*)

  Definition IN_p : wf_bigrammar (pair_t char_t (User_t (Option_t Byte_t))).
    refine ((IN_p1 |+| IN_p2)
              @ (fun x => 
                   match x with
                     | inl (w,b) => (w, Some b)
                     | inr w => (w, None)
                   end %% (Pair_t Char_t (User_t (Option_t Byte_t))))
              & (fun x => 
                   match x with
                     | (w, Some b) => Some (inl (w,b))
                     | (w, None) => Some (inr w)
                   end)
              & _).
    unfold invertible. split.
    destruct v; destruct i; crush.
    destruct w. destruct i0; try discriminate; crush.
  Defined.
  
  Definition INC_p1 :=  "1111" $$ "111" $$ anybit  $ "11000" $$ reg.
  Definition INC_p2 := "0100" $$ "0" $$ reg.
  (*Definition INC_p3 := "1111" $$ "111" $$ anybit $ ext_op_modrm "000".*)
  
  Definition INS_p : wf_bigrammar Char_t := "0110" $$ "110" $$ anybit.
  
  Definition INTn_p : wf_bigrammar byte_t := "1100" $$ "1101" $$ byte.
  
  Definition INT_p : wf_bigrammar unit_t := "1100" $$ "1100" $$ empty.
  
  Definition INTO_p : wf_bigrammar unit_t := "1100" $$ "1110" $$ empty.
  
  Definition INVD_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "0000" $$ "1000" $$ empty.
  
  (*Definition INVLPG_p := //ext_op_modrm function*)
  
  Definition IRET_p : wf_bigrammar unit_t := "1100" $$ "1111" $$ empty.
  
  Definition Jcc_p1 := "0111" $$ tttn $ byte.
  Definition Jcc_p2 := "0000" $$ "1111" $$ "1000" $$ tttn $ word.

  Definition Jcc_p : wf_bigrammar (pair_t condition_t word_t).
    refine (@biased_union _ _ Jcc_p2 Jcc_p1 
              (fun x => let (ct, b) := x in (ct, sign_extend8_32 b))
              _).
    unfold bigrammar_rng_subset, in_bigrammar_rng. intros.
    sim. apply in_bitsleft_elim in H. sim.
    unfold seq in H0. eapply CatInv in H0.
    sim. rewriter.

    eexists.
    repeat (eapply in_bitsleft_intro; [eapply in_bits_intro | idtac]).
    eapply InCat; (eauto || eapply in_int_n_intro).
  Defined.
  
  Definition JCXZ_p : wf_bigrammar byte_t := "1110" $$ "0011" $$ byte.
  
  (*JMP //do later*)
  
  Definition LAHF_p : wf_bigrammar unit_t := "1001" $$ "1111" $$ empty.
  
  (* LAR - LMSW use ext_op_modrm or modrm*)
  
  Definition LODS_p : wf_bigrammar Char_t := "1010" $$ "110" $$ anybit.
  Definition LOOP_p : wf_bigrammar byte_t := "1110" $$ "0010" $$ byte.
  Definition LOOPZ_p : wf_bigrammar byte_t := "1110" $$ "0001" $$ byte.
  Definition LOOPNZ_p : wf_bigrammar byte_t := "1110" $$ "0000" $$ byte.
  (*Definition LSL_p - LTR //uses modrm*)
  
  (*Control registers, segment registers, etc*)
  
  Definition MOVS_p : wf_bigrammar Char_t := "1010" $$ "010" $$ anybit.
  
  Definition OUT_p1 := "1110" $$ "011" $$ anybit $ byte.
  Definition OUT_p2 := "1110" $$ "111" $$ anybit.
  
  Definition OUT_p : wf_bigrammar (pair_t char_t (User_t (Option_t Byte_t))).
    refine ((OUT_p1 |+| OUT_p2)
              @ (fun x => 
                   match x with
                     | inl (w,b) => (w, Some b)
                     | inr w => (w, None)
                   end %% (Pair_t Char_t (User_t (Option_t Byte_t))))
              & (fun x => 
                   match x with
                     | (w, Some b) => Some (inl (w,b))
                     | (w, None) => Some (inr w)
                   end)
              & _).
    unfold invertible. split.
    destruct v; destruct i; crush.
    destruct w. destruct i0; try discriminate; crush.
  Defined.

  Definition OUTS_p : wf_bigrammar Char_t := "0110" $$ "111" $$ anybit.
  
(*Come back to this later.*)
  Definition POPSR_p1 := "000" $$ "00" $$ "111" $$ empty.
  Definition POPSR_p2 := "000" $$ "10" $$ "111" $$ empty.
  Definition POPSR_p3 := "000" $$ "11" $$ "111" $$ empty.
  Definition POPSR_p4 := "0000" $$ "1111" $$ "10" $$ "100" $$ "001" $$ empty.
  Definition POPSR_p5 := "0000" $$ "1111" $$ "10" $$ "101" $$ "001" $$ empty.

Definition POPSR_check := POPSR_p1 |+| POPSR_p2 |+| POPSR_p3 |+| POPSR_p4 |+| POPSR_p5.
Check POPSR_check.
  
  Definition POPSR_p : wf_bigrammar segment_register_t.
  refine ((POPSR_p1 |+| POPSR_p2 |+| POPSR_p3 |+| POPSR_p4 |+| POPSR_p5)
           @ (fun x =>
               match x with
                  | inl tt => ES
                  | inr (inl tt) => SS
                  | inr (inr (inl tt)) => DS
                  | inr (inr (inr (inl tt))) => FS
                  | inr (inr (inr (inr tt))) => GS
                  end %% segment_register_t)
            & (fun x => 
                match x with
                  | ES => Some (inl tt)
                  | SS => Some (inr (inl tt))
                  | DS => Some (inr (inr (inl tt)))
                  | FS => Some (inr (inr (inr (inl tt))))
                  | GS => Some (inr (inr (inr (inr tt))))
                  | CS => None
                  end)
            & _).
   unfold invertible. split.
   
   intros. destruct v. sim. unfold in_bigrammar_rng. destruct i; crush.
   destruct i. sim. unfold in_bigrammar_rng. destruct i. crush. 
   unfold in_bigrammar_rng. destruct i. eexists. crush. eexists.
   destruct i; crush.
   
   intros. destruct v; destruct i; destruct w; crush. Qed.
   
   

  Definition POPA_p : wf_bigrammar unit_t := "0110" $$ "0001" $$ empty.
  Definition POPF_p : wf_bigrammar unit_t := "1001" $$ "1101" $$ empty.
  
  Definition PUSHA_p : wf_bigrammar unit_t := "0110" $$ "0000" $$ empty.
  Definition PUSHF_p : wf_bigrammar unit_t := "1001" $$ "1100" $$ empty.
  
  Definition RDMSR_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "0011" $$ "0010" $$ empty.
  Definition RDPMC_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "0011" $$ "0011" $$ empty.
  Definition RDTSC_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "0011" $$ "0001" $$ empty.
  Definition RDTSCP_p : wf_bigrammar unit_t := 
    "0000" $$ "1111" $$ "0000" $$ "0001" $$ "1111" $$ "1001" $$ empty.
  
  (*Come back to this one too.*)
  Definition RET_p1 := "1100" $$ "0011" $$ empty.
  Definition RET_p2 := "1100" $$ "0010" $$ halfword.
  Definition RET_p3 := "1100" $$ "1011" $$ empty.
  Definition RET_p4 := "1100" $$ "1010" $$ halfword.
  
  Definition RET_c := RET_p1 |+| RET_p2 |+| RET_p3 |+| RET_p4.
  Check RET_c.
  
  Definition RET_p : wf_bigrammar (pair_t char_t (option_t Half_t)).
     refine((RET_p1 |+| RET_p2 |+| RET_p3 |+| RET_p4)
        @ (fun x =>
            match x with
              | inl tt=> (true, None)
              | inr (inl c) => (true, Some c)
              | inr (inr (inl tt)) => (false, None)
              | inr (inr (inr c)) => (false, Some c)
              end %% (pair_t char_t (option_t Half_t)))
        & (fun x =>
            match x with
              | (true, None) => Some (inl tt)
              | (true, Some c) => Some (inr (inl c))
              | (false, None) => Some (inr (inr (inl tt)))
              | (false, Some c) => Some (inr (inr (inr c)))
            end)
        & _).
      unfold invertible. split.

      unfold in_bigrammar_rng.
      intros. sim. eexists.
      destruct v; destruct i; crush. destruct i; crush.
      
      unfold in_bigrammar_rng. intros.
      destruct v; destruct w; destruct i; destruct i0; destruct i1; crush.
      Qed.
  
  Definition RSM_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "1010" $$ "1010" $$ empty.
  Definition SAHF_p : wf_bigrammar unit_t := "1001" $$ "1110" $$ empty.
  
  Definition SCAS_p : wf_bigrammar Char_t := "1010" $$ "111" $$ anybit.
  
  Definition UD2_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "0000" $$ "1011" $$ empty.
  
  Definition WBINVD_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "0000" $$ "1001" $$ empty.
  
  Definition WRMSR_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "0011" $$ "0000" $$ empty.
  
  Definition XLAT_p : wf_bigrammar unit_t := "1101" $$ "0111" $$ empty.
  
  Definition F2XM1_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "10000" $$ empty.
  Definition FABS_p : wf_bigrammar unit_t :=  "11011" $$ "001111" $$ "00001" $$ empty.
  (*Modrm definitions needed here*)
  
  (*Definition FADDP_p : wf_bigrammar fpu_register_t= "11011" $$ "110" $$ "11000" $$ fpu_reg.*)
  
  Definition FCHS_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "00000" $$ empty.
  
  Definition FCOMPP_p : wf_bigrammar unit_t := "11011" $$ "110" $$ "11011" $$ "001" $$ empty.
  
  Definition FCOS_p : wf_bigrammar unit_t := "11011" $$ "001" $$ "111" $$ "11111" $$ empty.
  
  Definition FDECSTP_p : wf_bigrammar unit_t := "11011" $$ "001" $$ "111" $$ "10110" $$ empty.
  
  Definition FLD1_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "01000" $$ empty.
  
  Definition FLDL2E_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "01010" $$ empty.
  Definition FLDL2T_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "01001" $$ empty.
  Definition FLDLG2_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "01100" $$ empty.
  Definition FLDLN2_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "01101" $$ empty.
  Definition FLDPI_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "01011" $$ empty.
  Definition FLDZ_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "01110" $$ empty.
  
  Definition FNCLEX_p : wf_bigrammar unit_t := "11011" $$ "011111" $$ "00010" $$ empty.
  Definition FNINIT_p : wf_bigrammar unit_t := "11011" $$ "011111" $$ "00011" $$ empty.
  Definition FNOP_p : wf_bigrammar unit_t := "11011" $$ "001110" $$ "10000" $$ empty.
  
  Definition FPATAN_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "10011" $$ empty.
  Definition FPREM_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "11000" $$ empty.
  Definition FPREM1_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "10101" $$ empty.
  Definition FPTAN_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "10010" $$ empty.
  Definition FRNDINT_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "11100" $$ empty.
  
  Definition FSCALE_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "11101" $$ empty.
  Definition FSIN_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "11110" $$ empty.
  Definition FSINCOS_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "11011" $$ empty.
  Definition FSQRT_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "11010" $$ empty.
  
  Definition FTST_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "00100" $$ empty.
  
  Definition FUCOMPP_p : wf_bigrammar unit_t := "11011" $$ "010111" $$ "01001" $$ empty.

  Definition FXAM_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "00101" $$ empty.
  
  Definition FXTRACT_p : wf_bigrammar unit_t := "11011" $$ "001" $$ "1111" $$ "0100" $$ empty.
  Definition FYL2X_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "10001" $$ empty.
  Definition FYL2XP1_p : wf_bigrammar unit_t := "11011" $$ "001111" $$ "11001" $$ empty.
  Definition FWAIT_p : wf_bigrammar unit_t := "10011011" $$ empty.
  
  (*MMX Grammars*)
  
  Definition EMMS_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "0111" $$ "0111" $$ empty.
  
  (*End MMX Grammars*)
  
  Definition SFENCE_p : wf_bigrammar unit_t := "0000" $$ "1111" $$ "1010" $$ "1110" $$ "1111" $$ 
                                    "1000" $$ empty.
                                    
  
          
  (* An instruction environment type that help produce to_instr and from_instr
     via tactics *)
  Inductive Instr_Env := 
    | instr_env_nil : Instr_Env
    | instr_env_cons : 
        forall (s:string) (t:type), (interp t -> instr) -> Instr_Env -> Instr_Env.
        (* each case in an Instr_Env including an index string for an instr, 
           the type of the instr's parameters, and a constructor for constructing
           the instr given a set of arguments *)
  Notation "{ s , t ,  f } ::: il" := 
    (instr_env_cons s t f il) (right associativity, at level 70).

  (* The ordering in instr_env is important and should be the same as
     the one in instr_p' *)
  Definition instr_env := 
    {"AAA",  unit_t, (fun x:unit => AAA)} :::
    {"AAD", unit_t, (fun x:unit => AAD)} :::
    {"AAM", unit_t, (fun x:unit => AAM)} :::
    {"AAS", unit_t, (fun x:unit => AAS)} :::
    {"BSWAP", register_t,  (fun r => BSWAP r)} :::
    {"CDQ", unit_t, (fun x => CDQ)} :::
    {"CLC", unit_t, (fun x => CLC)} :::
    {"CLD", unit_t, (fun x => CLD)} :::
    {"CLI", unit_t, (fun x => CLI)} :::
    {"CLTS", unit_t, (fun x => CLTS)} :::
    {"CMC", unit_t, (fun x => CMC)} :::
    {"CMPS", char_t, (fun x => CMPS x)} :::
    {"CPUID", unit_t, (fun x => CPUID)} :::
    {"CWDE", unit_t, (fun x => CWDE)} :::
    {"DAA", unit_t, (fun x => DAA)} :::
    {"DAS", unit_t, (fun x => DAS)} :::
    {"F2XM1", unit_t, (fun x => F2XM1)} :::
    {"FABS", unit_t, (fun x => FABS)} :::
    {"FCHS", unit_t, (fun x => FCHS)} :::
    {"FCOMPP", unit_t, (fun x => FCOMPP)} :::
    {"FCOS", unit_t, (fun x => FCOS)} :::
    {"FDECSTP", unit_t, (fun x => FDECSTP)} :::
    {"FLD1", unit_t, (fun x => FLD1)} :::
    {"FLDL2E", unit_t, (fun x => FLDL2E)} :::
    {"FLDL2T", unit_t, (fun x => FLDL2T)} :::
    {"FLDLG2", unit_t, (fun x => FLDLG2)} :::
    {"FLDLN2", unit_t, (fun x => FLDLN2)} :::
    {"FLDPI", unit_t, (fun x => FLDPI)} :::
    {"FLDZ", unit_t, (fun x => FLDZ)} :::
    {"FNCLEX", unit_t, (fun x => FNCLEX)} :::
    {"FNINIT", unit_t, (fun x => FNINIT)} :::
    {"FNOP", unit_t, (fun x => FNOP)} :::
    {"FPATAN", unit_t, (fun x => FPATAN)} :::
    {"FPREM", unit_t, (fun x => FPREM)} :::
    {"FPREM1", unit_t, (fun x => FPREM1)} :::
    {"FPTAN", unit_t, (fun x => FPTAN)} :::
    {"FRNDINT", unit_t, (fun x => FRNDINT)} :::
    {"FSCALE", unit_t, (fun x => FSCALE)} :::
    {"FSIN", unit_t, (fun x => FSIN)} :::
    {"FSINCOS", unit_t, (fun x => FSINCOS)} :::
    {"FSQRT", unit_t, (fun x => FSQRT)} :::
    {"FTST", unit_t, (fun x => FTST)} :::
    {"FUCOMPP", unit_t, (fun x => FUCOMPP)} :::
    {"FXAM", unit_t, (fun x => FXAM)} :::
    {"FXTRACT", unit_t, (fun x => FXTRACT)} :::
    {"FYL2X", unit_t, (fun x => FYL2X)} :::
    {"FYL2XP1", unit_t, (fun x => FYL2XP1)} :::
    {"FWAIT", unit_t, (fun x => FWAIT)} :::
    {"EMMS", unit_t, (fun x => EMMS)} :::
    {"SFENCE", unit_t, (fun x => SFENCE)} :::
    {"HLT", unit_t, (fun x => HLT)} :::
    {"IN", pair_t char_t (User_t (Option_t Byte_t)), 
     (fun v => let (w, opb):= v in IN w opb)} :::
    {"INS", char_t, (fun x => INS x)} :::
    {"INTn", byte_t, (fun x => INTn x)} :::
    {"INT", unit_t, (fun x => INT)} :::
    {"INTO", unit_t, (fun x => INTO)} :::
    {"INVD", unit_t, (fun x => INVD)} :::
    {"IRET", unit_t, (fun x => IRET)} :::
    {"Jcc", pair_t condition_t word_t,
     (fun v => let (ct, w):= v in Jcc ct w)} :::
    {"JCXZ", byte_t, (fun x => JCXZ x)} :::
    {"LAHF", unit_t, (fun x => LAHF)} :::
    {"LODS", char_t, (fun x => LODS x)} :::
    {"LOOP", byte_t, (fun x => LOOP x)} :::
    {"LOOPZ", byte_t, (fun x => LOOPZ x)} :::
    {"LOOPNZ", byte_t, (fun x => LOOPNZ x)} :::
    {"MOVS", char_t, (fun x => MOVS x)} :::
    {"OUT", pair_t char_t (User_t (Option_t Byte_t)),
    (fun p => OUT (fst p) (snd p))} :::
    {"OUTS", char_t, (fun x => OUTS x)} :::
    {"POPSR", segment_register_t, (fun x => POPSR x)} :::
    {"POPA", unit_t, (fun x => POPA)} :::
    {"POPF", unit_t, (fun x => POPF)} :::
    {"PUSHA", unit_t, (fun x => PUSHA)} :::
    {"PUSHF", unit_t, (fun x => PUSHF)} :::
    {"RDMSR", unit_t, (fun x => RDMSR)} :::
    {"RDPMC", unit_t, (fun x => RDPMC)} :::
    {"RDTSC", unit_t, (fun x => RDTSC)} :::
    {"RDTSCP", unit_t, (fun x => RDTSCP)} :::
    {"RET", (pair_t char_t (option_t Half_t)), 
     (fun x => let (c, h) := x in RET c h)} :::
    {"RSM", unit_t, (fun x => RSM)} :::
    {"SAHF", unit_t, (fun x => SAHF)} :::
    {"SCAS", char_t, (fun x => SCAS x)} :::
    {"UD2", unit_t, (fun x => UD2)} :::
    {"WBINVD", unit_t, (fun x => WBINVD)} :::
    {"WRMSR", unit_t, (fun x => WRMSR)} :::
    {"XLAT", unit_t, (fun x => XLAT)} :::
    instr_env_nil.

  Fixpoint gen_instr_type (ie: Instr_Env) := 
    match ie with
      | instr_env_nil => Void_t
      | instr_env_cons _ t _ ie' =>
        Sum_t t (gen_instr_type ie')
    end.

  Definition instr': type := gen_instr_type instr_env.
  (* Eval compute in instr'. *)

  Definition instr_p': wf_bigrammar instr' :=
    AAA_p |+| AAD_p |+| AAM_p |+| AAS_p |+| BSWAP_p |+| 
    CDQ_p |+| CLC_p |+| CLD_p |+| CLI_p |+| CLTS_p |+|
    CMC_p |+| CMPS_p |+| CPUID_p |+| CWDE_p |+| DAA_p |+|
    DAS_p |+| F2XM1_p |+| FABS_p |+|
    FCHS_p |+| FCOMPP_p |+| FCOS_p |+| FDECSTP_p |+| FLD1_p |+|
    FLDL2E_p |+| FLDL2T_p |+| FLDLG2_p |+| FLDLN2_p |+| FLDPI_p |+|
    FLDZ_p |+| FNCLEX_p |+| FNINIT_p |+| FNOP_p |+| FPATAN_p |+| FPREM_p |+|
    FPREM1_p |+| FPTAN_p |+| FRNDINT_p |+| FSCALE_p |+| FSIN_p |+|
    FSINCOS_p |+| FSQRT_p |+| FTST_p |+| FUCOMPP_p |+|
    FXAM_p |+| FXTRACT_p |+| FYL2X_p |+| FYL2XP1_p |+| FWAIT_p |+| EMMS_p |+|
    SFENCE_p |+| HLT_p |+| IN_p |+| INS_p |+| INTn_p |+|
    INT_p |+| INTO_p |+| INVD_p |+| IRET_p |+| Jcc_p |+|
    JCXZ_p |+| LAHF_p |+| LODS_p |+| LOOP_p |+| LOOPZ_p |+|
    LOOPNZ_p |+| MOVS_p |+| OUT_p |+| OUTS_p |+| POPSR_p |+| POPA_p |+| POPF_p |+|
    PUSHA_p |+| PUSHF_p |+| RDMSR_p |+| RDPMC_p |+| RDTSC_p |+|
    RDTSCP_p |+| RET_p |+| RSM_p |+| SAHF_p |+| SCAS_p |+| UD2_p |+|
    WBINVD_p |+| WRMSR_p |+| XLAT_p |+| (@never Void_t).


  Ltac gen_to_instr instr_env :=
    match instr_env with
      | instr_env_cons _ ?t ?icons ?ie =>
        let sub_to_instr := gen_to_instr ie in
        constr:(fun (ast: interp t + _) =>
                  match ast with
                    | inl v => icons v
                    | inr ast' => sub_to_instr ast'
                  end)
      | instr_env_nil => constr: (fun v:void => AAA) (* dummy case *)
    end.

  (* We want to write a function that converts values in instr' to instr,
     as follows; we use tactics to help generate this function.
    Definition to_instr (ast: interp t') : instr :=
     match ast with
      | inl _ => AAA
      | inr (inl r) => BSWAP r
      | inr (inr (inl (w, opb))) => IN w opb
      | inr (inr (inr (inl (ct, w)))) => Jcc ct w
      | _ => AAA (* dummy case *)
     end.
   *)
  Definition to_instr (ast: interp instr') : instr.
    let instr_env := instr_env in pose (ie:=instr_env).
    (* unfold unit_t and pair_t so that the pattern maching in gen_to_instr works *)
    unfold instr_env in ie.

    let ie := eval unfold ie in ie in
    let t := gen_to_instr ie in pose t.
    simpl in *.
    exact i.
  Defined.

  (* given a instruction env and an index string for an instruction, 
     return the numeric index of the instruction *)
  Fixpoint get_instr_index (ie:Instr_Env) (s:string) := 
    let fix aux ie n := 
        match ie with 
          | instr_env_cons s' _ _ ie' =>
            if (string_dec s s') then n 
            else aux ie' (S n)
          | instr_env_nil => n (* no match, return the length of instr_env *)
        end
    in aux ie O.
  (* Eval compute in (get_instr_index instr_env "Jcc"). *)

  Ltac gen_from_constr n arg t := 
    match n with
      | O => match t with
               | Sum_t ?lt ?rt => constr:(@inl (interp lt) (interp rt) arg)
               | _ => fail
             end
      | S ?n' =>
        match t with
          | Sum_t ?lt ?rt => 
            let tm := gen_from_constr n' arg rt in
            constr:(@inr (interp lt) (interp rt) tm)
          | _ => fail
        end
    end.

  (* We need a function that converts values in instr to instr' as follows;
     we use tactics to help generate this function.
    Definition from_instr (i: instr) : option (interp instr')  :=
      match i with
        | AAA => Some (inl tt)
        | BSWAP r => Some (inr (inl r))
        | IN w opb => Some (inr (inr (inl (w, opb))))
        | Jcc ct w => Some (inr (inr (inr (inl (ct, w)))))
        | _ => None
      end.
  *)
  Definition from_instr (i: instr) : option (interp instr').
    intro i.
    refine (match i with
              | AAA => _
              | AAD => _
              | AAM => _
              | AAS => _
              | BSWAP r => _
              | CDQ => _
              | CLC => _
              | CLD => _
              | CLI => _
              | CLTS => _
              | CMC => _
              | CMPS c => _
              | CPUID => _
              | CWDE => _
              | DAA => _
              | DAS => _
              | F2XM1 => _
              | FABS => _
              | FCHS => _
              | FCOMPP => _
              | FCOS => _
              | FDECSTP => _
              | FLD1 => _
              | FLDL2E => _
              | FLDL2T => _
              | FLDLG2 => _
              | FLDLN2 => _
              | FLDPI => _
              | FLDZ => _
              | FNCLEX => _
              | FNINIT => _
              | FNOP => _
              | FPATAN => _
              | FPREM => _
              | FPREM1 => _
              | FPTAN => _
              | FRNDINT => _
              | FSCALE => _
              | FSIN => _
              | FSINCOS => _
              | FSQRT => _
              | FTST => _
              | FUCOMPP => _
              | FXAM => _
              | FXTRACT => _
              | FYL2X => _
              | FYL2XP1 => _
              | FWAIT => _
              | EMMS => _
              | SFENCE => _
              | HLT => _
              | IN w opb => _
              | INS c => _
              | INTn b => _
              | INT => _
              | INTO => _
              | INVD => _
              | IRET => _
              | Jcc ct w => _
              | JCXZ b => _
              | LAHF => _
              | LODS c => _
              | LOOP b => _
              | LOOPZ b => _
              | LOOPNZ b => _
              | MOVS c => _
              | OUT p1 p2 => _
              | OUTS c => _
              | POPSR r => _
              | POPA => _
              | POPF => _
              | PUSHA => _
              | PUSHF => _
              | RDMSR => _
              | RDPMC => _
              | RDTSC => _
              | RDTSCP => _
              | RET c h => _
              | RSM => _
              | SAHF => _
              | SCAS c => _
              | UD2 => _
              | WBINVD => _
              | WRMSR => _
              | XLAT => _
              | _ => None
            end).
    Local Ltac gen Case arg := 
      let s := eval unfold Case in Case in
      let n := eval compute in (get_instr_index instr_env s) in
      let instr'_type := eval compute in instr' in
      let tm := gen_from_constr n arg instr'_type in
      exact (Some tm).

    Case "AAA". gen Case tt.
    Case "AAD". gen Case tt.
    Case "AAM". gen Case tt.
    Case "AAS". gen Case tt.
    Case "BSWAP". gen Case r.
    Case "CDQ". gen Case tt.
    Case "CLC". gen Case tt.
    Case "CLD". gen Case tt.
    Case "CLI". gen Case tt.
    Case "CLTS". gen Case tt.
    Case "CMC". gen Case tt.
    Case "CMPS". gen Case c.
    Case "CPUID". gen Case tt.
    Case "CWDE". gen Case tt.
    Case "DAA". gen Case tt.
    Case "DAS". gen Case tt.
    Case "F2XM1". gen Case tt.
    Case "FABS". gen Case tt.
    Case "FCHS". gen Case tt.
    Case "FCOMPP". gen Case tt.
    Case "FCOS". gen Case tt.
    Case "FDECSTP". gen Case tt.
    Case "FLD1". gen Case tt.
    Case "FLDL2E". gen Case tt.
    Case "FLDL2T". gen Case tt.
    Case "FLDLG2". gen Case tt.
    Case "FLDLN2". gen Case tt.
    Case "FLDPI". gen Case tt.
    Case "FLDZ". gen Case tt.
    Case "FNCLEX". gen Case tt.
    Case "FNINIT". gen Case tt.
    Case "FNOP". gen Case tt.
    Case "FPATAN". gen Case tt.
    Case "FPREM". gen Case tt.
    Case "FPREM1". gen Case tt.
    Case "FPTAN". gen Case tt.
    Case "FRNDINT". gen Case tt.
    Case "FSCALE". gen Case tt.
    Case "FSIN". gen Case tt.
    Case "FSINCOS". gen Case tt.
    Case "FSQRT". gen Case tt.
    Case "FTST". gen Case tt.
    Case "FUCOMPP". gen Case tt.
    Case "FXAM". gen Case tt.
    Case "FXTRACT". gen Case tt.
    Case "FYL2X". gen Case tt.
    Case "FYL2XP1". gen Case tt.
    Case "FWAIT". gen Case tt.
    Case "EMMS". gen Case tt.
    Case "SFENCE". gen Case tt.
    Case "HLT". gen Case tt.
    Case "IN". gen Case (w,opb).
    Case "INS". gen Case c.
    Case "INTn". gen Case b.
    Case "INT". gen Case tt.
    Case "INTO". gen Case tt.
    Case "INVD". gen Case tt.
    Case "IRET". gen Case tt.
    Case "Jcc". gen Case (ct,w).
    Case "JCXZ". gen Case b.
    Case "LAHF". gen Case tt.
    Case "LODS". gen Case c.
    Case "LOOP". gen Case b.
    Case "LOOPZ". gen Case b.
    Case "LOOPNZ". gen Case b.
    Case "MOVS". gen Case c.
    Case "OUT". gen Case (p1,p2).
    Case "OUTS". gen Case c.
    Case "POPSR". gen Case r.
    Case "POPA". gen Case tt.
    Case "POPF". gen Case tt.
    Case "PUSHA". gen Case tt.
    Case "PUSHF". gen Case tt.
    Case "RDMSR". gen Case tt.
    Case "RDPMC". gen Case tt.
    Case "RDTSC". gen Case tt.
    Case "RDTSCP". gen Case tt.
    Case "RET". gen Case (c,h).
    Case "RSM". gen Case tt.
    Case "SAHF". gen Case tt.
    Case "SCAS". gen Case c.
    Case "UD2". gen Case tt.
    Case "WBINVD". gen Case tt.
    Case "WRMSR". gen Case tt.
    Case "XLAT". gen Case tt.
  Defined.

  Lemma from_instr_to_instr : forall v, from_instr (to_instr v) = Some v.
  Proof. simpl. intros.
    repeat match goal with
      | [ H: (_ + _)%type |- _] => destruct H
      | [ H: (_ * _)%type |- _] => destruct H
      | [ H: void |- _ ] => destruct v
      | _ => crush
    end.
    Qed.

  Lemma to_instr_from_instr : forall i v, from_instr i = Some v -> to_instr v = i.
  Proof. simpl. intros. destruct i; crush.
  Qed.

  Definition instr_p : wf_bigrammar instruction_t.
    refine (instr_p' @ (to_instr: _ -> interp (instruction_t)) & from_instr & _).
    unfold invertible; split.
    intros. rewrite from_instr_to_instr. crush.
    intros. eapply to_instr_from_instr. trivial.
  Defined.
      











(* Definition desc_union t (g1 g2:bigrammar t) (test:interp t -> bool) : bigrammar t := *)
(*   @Map (Sum_t t t) t (fun x => match x with | inl a => a | inr b => b end) *)
(*        (fun x => Some (if test x then inl _ x else inr _ x)) (Alt g1 g2). *)

(* Lemma desc_union_wf t (g1 g2:bigrammar t) (test:interp t -> bool) : *)
(*   wf_grammar g1 -> wf_grammar g2 -> *)
(*   (forall v:interp t, (exists s, in_bigrammar g1 s v) -> test v = true) -> *)
(*   (forall v:interp t, (exists s, in_bigrammar g2 s v) -> test v = false) -> *)
(*   wf_grammar (desc_union g1 g2 test). *)
(* Proof. *)
(*   intros. unfold desc_union. crush. *)
(*   unfold invertible. split. *)

(*   crush. destruct w. *)
(*   remember (test i) as ti. destruct ti. crush. *)
(*   in_inv. crush. *)
(*   assert (test i = true). eapply H1. inversion H4. subst. eauto. *)
(*   congruence. *)

(*   remember (test i) as ti. destruct ti.  *)
(*   in_inv. crush. *)
(*   assert (test i = false). eapply H2. inversion H4. subst. eauto. *)
(*   congruence. *)
(*   crush. *)

(*   crush. *)
(*   remember (test v1) as tv. destruct tv; crush. *)
(* Qed. *)


(* Definition perm t1 t2 (p1:grammar t1) (p2:grammar t2) : grammar (Pair_t t1 t2) := *)
(*   union (Cat p1 p2) (@Map (Pair_t t2 t1) (Pair_t t1 t2) (fun p => (snd p, fst p)) *)
(*                           (fun p => Some (snd p, fst p)) (Cat p2 p1)). *)

(* Lemma perm_wf t1 t2 (p1:grammar t1) (p2:grammar t2) :  *)
(*   wf_grammar p1 ->  *)
(*   wf_grammar p2 ->  *)
(*   wf_grammar (perm p1 p2). *)
(* Proof. *)
(*   intros. unfold perm. eapply union_wf. simpl ; auto. simpl.  *)
(*   split ; auto. split. intros. mysimp. destruct w. exists (i, i0). *)
(*   split ; auto. in_inv. *)
(*   intros. injection H2. intros. subst. *)
(*  simpl.  destruct v1. simpl. auto. *)
(* Qed.   *)


(* Definition drop_left (c:char_p) t2 (g2:grammar t2) : grammar t2 := *)
(*   @Map (Pair_t Char_t t2) t2 *)
(*        (fun p : interp (Pair_t Char_t t2) => snd p) *)
(*        (fun v : interp t2 => Some (c,v)) *)
(*        (Cat (Char c) g2). *)
(* Lemma drop_left_wf c t2 (g2:grammar t2) : *)
(*   wf_grammar g2 -> wf_grammar (drop_left c g2). *)
(* Proof. *)
(*   intros. unfold drop_left ; simpl. split ; auto. split. *)
(*   intros. in_inv. econstructor ; split ; eauto. *)
(*   intros. injection H1. intros ; subst. auto. *)
(* Qed. *)





(*End NewParser.*)
(*End X86_BASE_PARSER.*)
