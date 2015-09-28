(** Gang Tan: Bi-directional grammars for both parsing and pretty-printing *)

Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
Require Import Coqlib.  (* for extensionality & proof_irrelevance *)
Require Import Arith.
Require Import Eqdep.
Require Import Omega.
Require Import CommonTacs.
Require Import Program.

Unset Automatic Introduction. 
Set Implicit Arguments.

Require Import Monad.
Local Open Scope monad_scope.

Require Import ParserArg.

(* Module Type NEW_PARSER_ARG. *)
(*   (* the type of characters used in the grammar specifications *) *)
(*   Parameter char_p : Set. *)
(*   (* equality on characters -- should change this to a boolean function, *)
(*      paired with a proof that it's an equality so that *)
(*      we get faster symbolic computation. *) *)
(*   Parameter char_dec : forall (c1 c2:char_p), {c1=c2} + {c1<>c2}. *)
(*   (* a name for user types embedded within our AST grammar types. *) *)
(*   Parameter user_type : Set. *)
(*   (* equality on user type names. *) *)
(*   Parameter user_type_dec : forall (t1 t2:user_type), {t1=t2} + {t1<>t2}. *)
(*   (* a semantic interpretation function for user type names. *) *)
(*   Parameter user_type_denote : user_type -> Set. *)

(*   (* when we parse, instead of working in terms of individual characters, *)
(*      we work in terms of tokens.   For instance, the x86 grammar is specified *)
(*      with characters as bits, and tokens as bytes (8-bits. *) *)
(*   Definition token_id := nat. *)
(*   (* this is the total number of tokens that we can have -- e.g., for the *)
(*      x86 parser it is 256 because they have 8 bits. *) *)
(*   Variable num_tokens : nat. *)
(*   (* this converts tokens to a list of characters -- it's used only during *)
(*      the table construction for the parser. *) *)
(*   Variable token_id_to_chars : token_id -> list char_p. *)
(* End NEW_PARSER_ARG. *)

(* a module for generating the parser for x86 instructions *)
(* Module X86_PARSER_ARG. *)
(*   Require Import X86Syntax. *)
(*   Require Import Bits. *)
(*   Local Open Scope Z_scope. *)
  
(*   Definition char_p : Set := bool. *)
(*   Definition char_dec : forall (c1 c2:char_p), {c1=c2}+{c1<>c2} := bool_dec. *)
(*   Inductive type : Set :=  *)
(*   | Int_t : type *)
(*   | Register_t : type *)
(*   | BitVector_t : nat -> type (* a bit vector of a certain width *) *)
(*   (* | Byte_t : type *) *)
(*   (* | Half_t : type *) *)
(*   (* | Word_t : type *) *)
(*   (* | Double_Word_t : type *) *)
(*   (* | Ten_Byte_t : type *) *)
(*   | Scale_t : type *)
(*   | Condition_t : type *)
(*   | Address_t : type *)
(*   | Operand_t : type *)
(*   | Fpu_Register_t : type *)
(*   | Fp_Debug_Register_t : type *)
(*   | Fp_Operand_t : type  *)
(*   | MMX_Granularity_t : type *)
(*   | MMX_Register_t : type *)
(*   | MMX_Operand_t : type *)
(*   | SSE_Register_t : type *)
(*   | SSE_Operand_t : type *)
(*   | Instruction_t : type *)
(*   | Control_Register_t : type *)
(*   | Debug_Register_t : type *)
(*   | Segment_Register_t : type *)
(*   | Lock_or_Rep_t : type *)
(*   | Bool_t : type *)
(*   | Prefix_t : type *)
(*   | Option_t (t: type) : type *)
(*   (* Need pairs at this level if I want to have options of pairs*) *)
(*   | UPair_t (t1 t2: type) : type.  *)

(*   Definition Byte_t := BitVector_t 7. *)
(*   Definition Half_t := BitVector_t 15. *)
(*   Definition Word_t := BitVector_t 31. *)
(*   Definition Double_Word_t := BitVector_t 63. *)
(*   Definition Ten_Byte_t := BitVector_t 79. *)

(*   Definition tipe := type. *)
(*   Definition tipe_eq : forall (t1 t2:tipe), {t1=t2} + {t1<>t2}. *)
(*     intros ; decide equality. *)
(*     apply eq_nat_dec. *)
(*   Defined. *)

(*   Fixpoint tipe_m (t:tipe) :=  *)
(*     match t with  *)
(*       | Int_t => Z *)
(*       | Register_t => register *)
(*       | BitVector_t n => Word.int n *)
(*       (* | Byte_t => int8 *) *)
(*       (* | Half_t => int16 *) *)
(*       (* | Word_t => int32 *) *)
(*       (* | Double_Word_t => int64 *) *)
(*       (* | Ten_Byte_t => int80 *) *)
(*       | Scale_t => scale *)
(*       | Condition_t => condition_type *)
(*       | Address_t => address *)
(*       | Operand_t => operand *)
(*       | Fpu_Register_t => int3 *)
(*       | Fp_Debug_Register_t => fp_debug_register *)
(*       | Fp_Operand_t => fp_operand   *)
(*       | MMX_Granularity_t => mmx_granularity *)
(*       | MMX_Register_t => mmx_register *)
(*       | MMX_Operand_t => mmx_operand *)
(*       | SSE_Register_t => sse_register *)
(*       | SSE_Operand_t => sse_operand *)
(*       | Instruction_t => instr *)
(*       | Control_Register_t => control_register *)
(*       | Debug_Register_t => debug_register *)
(*       | Segment_Register_t => segment_register *)
(*       | Lock_or_Rep_t => lock_or_rep *)
(*       | Bool_t => bool *)
(*       | Prefix_t => prefix *)
(*       | Option_t t => option (tipe_m t) *)
(*       | UPair_t t1 t2 => ((tipe_m t1) * (tipe_m t2))%type *)
(*     end. *)
(*   Definition user_type := type. *)
(*   Definition user_type_dec : forall (t1 t2:user_type), {t1=t2} + {t1<>t2} :=  *)
(*     tipe_eq. *)
(*   Definition user_type_denote := tipe_m. *)

(*   Definition byte_explode (b:int8) : list bool :=  *)
(*   let bs := Word.bits_of_Z 8 (Word.unsigned b) in *)
(*     (bs 7)::(bs 6)::(bs 5)::(bs 4)::(bs 3)::(bs 2)::(bs 1)::(bs 0)::nil. *)

(*   Definition nat_explode (n:nat) : list bool :=  *)
(*     byte_explode (Word.repr (Z_of_nat n)). *)

(*   Definition token_id := nat. *)
(*   Definition num_tokens : token_id := 256%nat. *)
(*   Definition token_id_to_chars : token_id -> list char_p := nat_explode. *)
(* End X86_PARSER_ARG. *)

Definition char_p := X86_PARSER_ARG.char_p.
Definition char_dec := X86_PARSER_ARG.char_dec.
Definition user_type := X86_PARSER_ARG.user_type.
Definition user_type_dec := X86_PARSER_ARG.user_type_dec.
Definition user_type_denote := X86_PARSER_ARG.user_type_denote.
Definition token_id := X86_PARSER_ARG.token_id.
Definition num_tokens := X86_PARSER_ARG.num_tokens.
Definition token_id_to_chars := X86_PARSER_ARG.token_id_to_chars.


(** The [type]s for our grammars. *)
Inductive type : Type := 
| Unit_t : type
| Char_t : type
| Void_t : type
| Pair_t : type -> type -> type
| Sum_t : type -> type -> type
| List_t : type -> type
| User_t : user_type -> type.

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

(* Notation [[ t ]] would interfere with "destruct H as [v [H2 H4]]" *)
Notation "[| t |]" := (interp t).

(** A pair of a function and its inverse *)
Notation funinv t1 t2 := (([|t1|] -> [|t2|]) * 
                          ([|t2|] -> option ([|t1|])))%type.

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
| Map : forall t1 t2
          (fi: (funinv t1 t2)), (* a parse function and a pretty print function *)
          bigrammar t1 -> bigrammar t2.
Implicit Arguments Map [t1 t2].

(** Denotation of Bi-Grammars *)
(* I'm a little annoyed that I had to break out so many equalities, but
   found this worked a little better for both inversion and proving. *)
Inductive in_bigrammar : 
  forall t, bigrammar t -> list char_p -> (interp t) -> Prop := 
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
| InMap : forall t1 t2 (fi:funinv t1 t2) (g:bigrammar t1) s v1 v2, 
    in_bigrammar g s v1 -> v2 = fst fi v1 -> in_bigrammar (@Map t1 t2 fi g) s v2.
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
Lemma MapInv : forall t1 t2 (fi: funinv t1 t2) (g:bigrammar t1) cs v,
  in_bigrammar (@Map t1 t2 fi g) cs v -> exists v', in_bigrammar g cs v' /\ v = fst fi v'.
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
Ltac in_bigrammar_inv := 
  repeat 
    match goal with 
      | [ H : in_bigrammar Eps _ _ |- _ ] => generalize (EpsInv H) ; clear H; intro
      | [ H : in_bigrammar Any _ _ |- _ ] => generalize (AnyInv H) ; clear H; intro
      | [ H : in_bigrammar (Char _) _ _ |- _ ] => 
        generalize (CharInv H) ; clear H; intro
      | [ H : in_bigrammar (Alt _ _) _ _ |- _ ] => 
        generalize (AltInv H) ; clear H; intro
      | [ H : in_bigrammar (Cat _ _) _ _ |- _ ] => 
        generalize (CatInv H) ; clear H; intro
      | [ H : in_bigrammar (Zero _) _ _ |- _ ] => contradiction (ZeroInv H)
      | [ H : in_bigrammar (Map _ _) _ _ |- _ ] => 
        generalize (MapInv H) ; clear H; intro
      | _ => idtac
    end.

Definition in_bigrammar_rng t (g: bigrammar t) (v: interp t) := 
  exists s, in_bigrammar g s v.

Definition bigrammar_rng_subset t (g1 g2: bigrammar t) := 
  forall v, in_bigrammar_rng g1 v -> in_bigrammar_rng g2 v.

Definition printable t1 t2 (fi: funinv t1 t2) (g:bigrammar t1) :=
  forall v: [|t1|],
    in_bigrammar_rng g v ->
    (* need the second conjunct to prove pretty_print_corr1 for the map case *)
    (exists v', (snd fi) (fst fi v) = Some v' /\ in_bigrammar_rng g v').
Implicit Arguments printable [t1 t2].

Definition parsable t1 t2 (fi: funinv t1 t2) (g:bigrammar t1) :=
  forall (v:[|t1|]) (w:[|t2|]),
    in_bigrammar_rng g v -> snd fi w = Some v -> fst fi v = w.
Implicit Arguments parsable [t1 t2].

Definition invertible t1 t2 (fi: funinv t1 t2) (g:bigrammar t1) :=
  printable fi g /\ parsable fi g.
Implicit Arguments invertible [t1 t2].

(** A stronger notion of invertibility; doesn't require this
    in a well-formed bigrammar, but it's sometimes more convenient to use 
    since it doesn't take a grammar g as a parameter *)
Definition strong_invertible t1 t2 (fi: funinv t1 t2) :=
  (forall v: [|t1|], (snd fi) (fst fi v) = Some v) /\
  (forall (v:[|t1|]) (w:[|t2|]), snd fi w = Some v -> fst fi v = w).
Implicit Arguments strong_invertible [t1 t2].

(** compose two pairs of functions and inverses *)
Definition funinv_compose t1 t2 t3 (fi2: funinv t2 t3) (fi1: funinv t1 t2) :=
  (compose (fst fi2) (fst fi1), 
   fun w => match snd fi2 w with
              | None => None
              | Some u => snd fi1 u
            end).
Implicit Arguments funinv_compose [t1 t2 t3].


(* The following version of invertible uses subset types to simplify the
   definition, but I found it's difficult to work this definition with
   tactics; whenever there is a value of the subset type, I need to
   destruct that value.
*)
(* Notation in_rng_val t g := {v:t | in_bigrammar_rng g v}. *)
(* Definition invertible t1 t2 (f:interp t1 -> interp t2)  *)
(*              (finv:interp t2 -> option (interp t1)) (g:bigrammar t1) :=  *)
(*   (forall v: in_rng_val _ g, *)
(*      exists v': in_rng_val _ g, finv (f (` v)) = Some (` v')) /\ *)
(*   (forall (v: in_rng_val _ g) (w:interp t2),  *)
(*      finv w = Some (` v) -> f (` v) = w). *)

(* well-formedness of grammars *)
Fixpoint wf_grammar t (g:bigrammar t) : Prop := 
  match g with 
      | Cat t1 t2 g1 g2 => wf_grammar g1 /\ wf_grammar g2
      | Alt t1 t2 g1 g2 => wf_grammar g1 /\ wf_grammar g2
      (* | Star t g => wf_grammar g *)
      | Map t1 t2 fi g => 
        wf_grammar g /\ invertible fi g
      | g' => True
  end.

(* a well-formed bigrammar: a bigrammar with a proof that it is well-formed *)
Notation wf_bigrammar t := {g:bigrammar t | wf_grammar g}.

Create HintDb ibr_rng_db.
Require Import Bits.
(* "Create HintDb inv_db" would not create an empty rewrite db *)
Hint Rewrite Word.bits_of_Z_of_bits Word.Z_of_bits_of_Z : inv_db.

(** convert variables of grammar types to their interpreted types *)
Ltac simpl_grammar_ty :=
  repeat match goal with
          | [v: [|Pair_t _ _|] |- _] => simpl in v
        end.

(* proving parsable in the special situation when the existential value
   is the same as the original one. *)
Ltac printable_tac := 
  break_hyp; simpl_grammar_ty; destruct_vars;
  autorewrite with inv_db; 
  match goal with 
    | [ |- exists v', Some ?v = Some v' /\ in_bigrammar_rng _ _] => 
      exists v; split; auto with ibr_rng_db
  end.

Ltac parsable_tac := 
  match goal with
    | [H:None = Some _ |- _] => discriminate
    | [H:Some _ = Some _ |- _] => inversion H; autorewrite with inv_db; trivial
  end.

Ltac invertible_tac := 
  unfold invertible; split; [unfold printable | unfold parsable]; 
  compute [snd fst]; intros;
  [try (printable_tac; fail) | try (parsable_tac; fail)].

Local Ltac localsimpl :=
  repeat
    match goal with
      | [v: unit |- _ ] => destruct v
      | [ |- context[char_dec ?x ?y] ] => destruct (char_dec x y)
      | [_: context[char_dec ?x ?y] |- _] => destruct (char_dec x y)
      | [H: wf_bigrammar _ |- _] => destruct H
      | _ => unfold invertible, printable, parsable, in_bigrammar_rng in *;
            in_bigrammar_inv; crush
    end.

(** * Lemmas about in_bigrammar_rng and other defs*)

Lemma in_bigrammar_rng_eps: in_bigrammar_rng Eps ().
Proof. unfold in_bigrammar_rng; crush. Qed.

Lemma in_bigrammar_rng_any c: in_bigrammar_rng Any c.
Proof. localsimpl. Qed.
Hint Resolve in_bigrammar_rng_any: ibr_rng_db.

Lemma in_bigrammar_rng_alt_inl
      t1 t2 (g1:bigrammar t1) (g2:bigrammar t2) (v:[|t1|]) :
  in_bigrammar_rng (Alt g1 g2) (inl v) <->
  in_bigrammar_rng g1 v. 
Proof. localsimpl. Qed.

Lemma in_bigrammar_rng_alt_inr
      t1 t2 (g1:bigrammar t1) (g2:bigrammar t2) (v:[|t2|]) :
  in_bigrammar_rng (Alt g1 g2) (inr v) <->
  in_bigrammar_rng g2 v. 
Proof. localsimpl. Qed.

Lemma in_bigrammar_rng_cat
      t1 t2 (g1:bigrammar t1) (g2:bigrammar t2) (v1:[|t1|]) (v2:[|t2|]) :
  in_bigrammar_rng (Cat g1 g2) (v1, v2) <->
  in_bigrammar_rng g1 v1 /\ in_bigrammar_rng g2 v2. 
Proof. localsimpl. Qed.

Lemma in_bigrammar_rng_map t1 t2 (g:bigrammar t1) (fi: funinv t1 t2) v:
  (exists v', in_bigrammar_rng g v' /\ v = fst fi v') <->
  in_bigrammar_rng (Map fi g) v.
Proof. localsimpl. Qed.

Lemma in_bigrammar_rng_map2 t1 t2 (g:bigrammar t1) (fi: funinv t1 t2) v:
  in_bigrammar_rng g v ->
  in_bigrammar_rng (Map fi g) (fst fi v).
Proof. localsimpl. Qed.

Lemma strong_inv_imp_inv t1 t2 (fi: funinv t1 t2) g : 
  strong_invertible fi -> invertible fi g.
Proof. unfold strong_invertible, invertible, printable, parsable. crush. Qed.

Lemma compose_invertible
      t1 t2 t3 (g:bigrammar t1) (fi1:funinv t1 t2) (fi2: funinv t2 t3):
      invertible fi1 g -> invertible fi2 (Map fi1 g) ->
      invertible (funinv_compose fi2 fi1) g.
Proof. 
  unfold invertible, printable, parsable; 
  intros; break_hyp; simpl; unfold compose.
  split; intros;
  use_lemma (@in_bigrammar_rng_map2 _ _ g fi1) by crush.
  - match goal with
      | [H: forall x, in_bigrammar_rng (Map fi1 g) _ -> _ |- _] =>
        guess (fst fi1 v) H; localsimpl
    end.
  - remember_head_in_hyp as sf.
    destruct sf; try discriminate.
    match goal with
      | [H: forall V W, _ -> _ -> fst fi1 V = W |- _] => 
        erewrite H in * by eauto; crush
    end.
Qed.

(** * Pretty printer and its correctness lemmas *)
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
    | Map t1 t2 fi g =>
      fun v => x <- snd fi v; pretty_print g x
  end.

Lemma pretty_print_corr1: forall t (g:bigrammar t) (v:interp t) s,
  in_bigrammar g s v -> wf_grammar g -> exists s', pretty_print g v = Some s'.
Proof. 
  induction g; try (localsimpl; fail).

  - (* Cat *)
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
  
  - (* Map *)
    localsimpl. guess x H1. crush.
Qed.

Lemma pretty_print_corr2: forall t (g:bigrammar t) (v:interp t) s,
  pretty_print g v = Some s -> wf_grammar g -> in_bigrammar g s v.
Proof. 
  induction g; try (localsimpl; fail).

  - (* Cat *)
    localsimpl.
    destruct v. simpl in *.
    remember_head_in_hyp as e1; destruct e1; try discriminate.
    remember_head_in_hyp as e2; destruct e2; try discriminate.
    crush.

  - (* Alt *)
    localsimpl.
    destruct v; eauto using InAlt_l, InAlt_r.

  (* Case "Star". *)
  (*   induction v; simprover. *)
  (*   remember_head_in_hyp as e1; destruct e1; try discriminate. *)
  (*   destruct l; try discriminate. *)
  (*   remember_head_in_hyp as e2; destruct e2; try discriminate. *)
  (*   eapply InStar_cons; (eauto || simprover). *)

  - (* Map. *)
    localsimpl.
    remember_head_in_hyp as e1; destruct e1; try discriminate.
    guess v H2. crush.
Qed.


(** * Constructors for wf bigrammars *)

Local Ltac localcrush :=
  repeat match goal with
           | [H: wf_bigrammar _ |- wf_grammar _] => destruct H
           | [ |- invertible _ _ ] => invertible_tac
           | _ => crush
         end.

Obligation Tactic := localcrush.

Program Definition empty : wf_bigrammar Unit_t := Eps.
Program Definition never t : wf_bigrammar t := Zero t.

Program Definition map t1 t2 (g:wf_bigrammar t1) (fi:funinv t1 t2)
             (pf: invertible fi (` g)) : wf_bigrammar t2 := 
  Map fi (` g).
Implicit Arguments map [t1 t2].
Notation "g @ f & fi & pf" :=(map g (f, fi) pf) (at level 75).

(* could also have the test return option(a=b) instead of {a=b}+{a<>b}. *)
Program Definition always t (teq: forall (a b:interp t), {a=b}+{a<>b})
        (x:interp t) : wf_bigrammar t := 
  Eps @ (fun (_:unit) => x) & (fun y => if teq x y then Some tt else None)
      & _.
Next Obligation. 
  - destruct (teq x x).
    + printable_tac.
    + crush.
  - destruct (teq x w); crush.
Defined.

Program Definition seq t1 t2 (p1:wf_bigrammar t1) (p2:wf_bigrammar t2) : 
  wf_bigrammar (Pair_t t1 t2) :=
  Cat p1 p2.

Program Definition alt t1 t2 (p1:wf_bigrammar t1) (p2:wf_bigrammar t2) : 
  wf_bigrammar (Sum_t t1 t2) :=
  Alt p1 p2.


(* Definition cons t (pair : interp (Pair_t t (List_t t))) : interp (List_t t) :=  *)
(*   (fst pair)::(snd pair). *)

(* doesn't seem that this is used; removed for now *)
(* Definition seqs t (ps:list (wf_bigrammar t)) : wf_bigrammar (List_t t) :=  *)
(*   List.fold_right (fun p1 p2 => map (seq p1 p2) (@cons t))  *)
(*     (@always (List_t t) (@nil (interp t))) ps. *)


(** A union operator for two grammars; it uses the pretty printer to try
      the left branch; only if it fails, it tries the right branch.  This
      operator should be avoided if possible for the following reasons.
      Suppose we union n grammars, each of size m. Pretty-print each
      grammar takes times linear to m.  Pretty print (g1+g2+...gn) would
      take the worst case n*m time as it may try all n possibilities. *)
Definition union t (g1 g2:wf_bigrammar t) : wf_bigrammar t.
  intros.
  refine ((alt g1 g2)
            @ (fun w : interp (Sum_t t t) => match w with inl x => x | inr y => y end)
            & (fun v : interp t => 
                 match pretty_print (Alt (` g1) (` g2)) (inl _ v) with 
                   | Some _ => Some (inl _ v)
                   | None => match pretty_print (Alt (` g1)  (` g2)) (inr _ v) with 
                               | Some _ => Some (inr _ v)
                               | None => None
                             end
                 end)
            & _); invertible_tac.
  - destruct v.
    + remember_destruct_head as v1; eauto.
      remember_destruct_head as v2.
      * localsimpl. eexists. eauto using pretty_print_corr1, pretty_print_corr2.
      * localsimpl. generalize pretty_print_corr1; crush_hyp.
    + localsimpl.
      remember_destruct_head as v1; eauto 6 using pretty_print_corr2.
      remember_destruct_head as v2; eauto 6.
      generalize pretty_print_corr1; crush_hyp.
  - remember_head_in_hyp as e1; destruct e1; try crush.
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

(* notation for building bigrammars *)
Infix "|+|" := alt (right associativity, at level 80).
Infix "|\/|" := union (right associativity, at level 80).
Infix "$" := seq (right associativity, at level 70).
Notation "e %% t" := (e : interp t) (at level 80).

Ltac ibr_simpl :=
  repeat match goal with 
           | [H: in_bigrammar_rng (` (_ |+| _)) _ |- _] =>
             unfold proj1_sig at 1, alt at 1 in H
           | [H: in_bigrammar_rng (` (_ $ _)) _ |- _] => 
             unfold proj1_sig at 1, seq at 1 in H
           | [H: in_bigrammar_rng (` (map _ _ _)) _ |- _] => 
             unfold proj1_sig at 1, map in H
           | [H: in_bigrammar_rng (Alt _ _) (inl _) |- _] =>
             apply in_bigrammar_rng_alt_inl in H
           | [H: in_bigrammar_rng (Alt _ _) (inr _) |- _] =>
             apply in_bigrammar_rng_alt_inr in H
           | [H: in_bigrammar_rng (Map _ _) _ |- _] =>
             apply in_bigrammar_rng_map in H; 
               let v := fresh "v" in let h1 := fresh "H" in
               let h2 := fresh "H" in 
               destruct H as [v [h1 h2]]; simpl in h2
           | [H: in_bigrammar_rng (Cat _ _) (_,_) |- _] => 
             apply in_bigrammar_rng_cat in H; destruct H
           | [ |- in_bigrammar_rng (Alt _ _) (inl _)] =>
             apply in_bigrammar_rng_alt_inl
           | [ |- in_bigrammar_rng (Alt _ _) (inr _)] =>
             apply in_bigrammar_rng_alt_inr
           | [ |- in_bigrammar_rng (Cat _ _) (_,_) ] => 
             apply in_bigrammar_rng_cat; split
           | [ |- in_bigrammar_rng (Map ?fi _) (fst _ _) ] =>
             apply in_bigrammar_rng_map2
           | [ |- in_bigrammar_rng (Map ?fi _) _ ] =>
             apply in_bigrammar_rng_map
           | [ |- in_bigrammar_rng Eps () ] =>
             apply in_bigrammar_rng_eps
           | [ |- in_bigrammar_rng (` (_ |+| _)) _] =>
             unfold proj1_sig at 1, alt at 1
           | [ |- in_bigrammar_rng (` (_ $ _)) _ ] => 
             unfold proj1_sig at 1, seq at 1
           | [ |- in_bigrammar_rng (` (map _ _ _)) _ ] => 
             unfold proj1_sig at 1, map
           | _ => auto with ibr_rng_db
         end.

Definition pred_options t (g1 g2: wf_bigrammar t) := 
  forall x: [|t|], ({in_bigrammar_rng (` g1) x} + {in_bigrammar_rng (` g2) x}) +
                   {not (in_bigrammar_rng (` g1) x) /\ 
                    not (in_bigrammar_rng (` g2) x)}.

(** Three-way predicated union: the pretty printer for "g1 + g2" uses the
    left one if x is in the range of g1, uses the right one if x is in
    the range of g2, or it aborts when x is not in the range of either g1
    or g2.*)
Definition predicated_union_three_way t (g1 g2: wf_bigrammar t)
           (pred: @pred_options t g1 g2) : wf_bigrammar t.
  intros.
  refine((alt g1 g2)
           @ (fun v : interp (Sum_t t t) => match v with inl x => x | inr y => y end)
           & (fun w : [|t|] => 
                match (pred w) with
                  | inleft (left _) => Some (inl w)
                  | inleft (right _) => Some (inr w)
                  | inright _ => None
                end)
           & _); invertible_tac.
  - destruct v as [v|v]; simpl.
    + destruct (pred v) as [[H2|H2]|H2];
      try (eexists; localsimpl; fail).
      ibr_simpl; crush.
    + destruct (pred v) as [[H2|H2]|H2];
      try (eexists; localsimpl; fail).
      ibr_simpl; crush.
  - destruct v; destruct (pred w) as [[H2|H2]|H2]; crush.
Defined. 

(** Predicated union: the pretty printer for "g1 + g2" uses the left one
    if x is in the range of g1 and uses the right one if x is in the
    range of g2; it bias towards g1 if x is in the range of both. *)
Definition predicated_union t (g1 g2: wf_bigrammar t)
           (pred: forall x:interp t,  {in_bigrammar_rng (` g1) x} + 
                                      {in_bigrammar_rng (` g2) x}) :
  wf_bigrammar t.
  intros;
  refine ((alt g1 g2)
            @ (fun v : interp (Sum_t t t) => 
                 match v with inl x => x | inr y => y end)
            & (fun w : [|t|] => if (pred w) then Some (inl w) else Some (inr w))
            & _); invertible_tac.
  - destruct v as [v|v]; simpl;
    destruct (pred v); printable_tac; ibr_simpl; crush.
  - crush; destruct v; destruct (pred w); crush. 
Defined.

(* This version also works, but its extracted code is inefficient *)
(* Program Definition predicated_union t (g1 g2: wf_bigrammar t) *)
(*         (pred: forall x:interp t,  {in_bigrammar_rng g1 x} +  *)
(*                                    {in_bigrammar_rng g2 x}) : *)
(*   wf_bigrammar t :=  *)
(*   @predicated_union_three_way t g1 g2 (fun w => inleft (pred w)). *)


(* Left biased toward g1, for the special case when rng(g2) is 
     a subset of rng(g1). *)
Program Definition biased_union t (g1 g2: wf_bigrammar t)
        (ss: bigrammar_rng_subset g2 g1) : wf_bigrammar t := 
  (alt g1 g2) 
    @ (fun v : interp (Sum_t t t) => match v with inl x => x | inr y => y end)
    & (fun w : [|t|] => Some (inl w))
    & _.
Next Obligation.
  destruct v; try crush.
  eexists; crush.
  ibr_simpl.
Defined.

(* The following def works for g1 and g2 that have different types; we
     could use the above def together with a map that uses f to go from
     t1 to t2, at the cost of some inefficiency. *)
(* Definition bigrammar_rng_subset t1 t2 (g1: bigrammar t1) (f: interp t1 -> interp t2) *)
(*            (g2: bigrammar t2) :=  *)
(*   forall v1, in_bigrammar_rng g1 v1 -> in_bigrammar_rng g2 (f v1). *)
(* Program Definition biased_union t1 t2 (g1: wf_bigrammar t1) (g2: wf_bigrammar t2) *)
(*         (f: interp t2 -> interp t1) *)
(*         (pfs: bigrammar_rng_subset g2 f g1) : wf_bigrammar t1 :=  *)
(*   @Map (Sum_t t1 t2) t1 *)
(*        (fun v : interp (Sum_t t1 t2) => match v with inl x => x | inr y => f y end, *)
(*         fun w : interp t1 => Some (inl w)) *)
(*        (Alt g1 g2). *)
(* Next Obligation. *)
(*   - localsimpl.  *)
(*   - localsimpl. *)
(*   - unfold invertible; split. *)
(*     * intros. destruct v. crush. *)
(*       unfold bigrammar_rng_subset, in_bigrammar_rng in *. *)
(*       guess i pfs.  *)
(*       assert (exists s, in_bigrammar (` g2) s i).  *)
(*         crush. in_bigrammar_inv. crush. inversion H0. crush. *)
(*       apply pfs in H0. *)
(*       crush. *)
(*     * crush. *)
(* Defined. *)

(** * Lemmas about wf bigrammar constructors *)

Lemma in_bigrammar_rng_union t (g1 g2:wf_bigrammar t) v:
  in_bigrammar_rng (` (g1 |\/| g2)) v <->
  in_bigrammar_rng (` g1) v \/ in_bigrammar_rng (` g2) v.
Proof. intros; unfold union; split; intros.
  - ibr_simpl; destruct v0; ibr_simpl; crush.
  - ibr_simpl. simpl.
    destruct H.
    + exists (inl [|t|] v). split; ibr_simpl.
    + exists (inr [|t|] v). split; ibr_simpl.
Qed.