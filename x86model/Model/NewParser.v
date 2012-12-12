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

Module NewParser(PA : NEW_PARSER_ARG).
Import PA.

(** The [type]s for our grammars -- later, we'll need to extend this with user-defined 
     types. *)
Inductive type : Type := 
| Unit_t : type
| Char_t : type
| Void_t : type
| Pair_t : type -> type -> type
| Sum_t : type -> type -> type
| List_t : type -> type
| User_t : user_type -> type.

(** [type] equality is decidable. *)  
Definition type_dec : forall (t1 t2:type), {t1=t2} + {t1<>t2}.
  decide equality ; apply user_type_dec.
Defined.

Inductive void : Type := .

(** The interpretation of [type]s as [Type]s. *)
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

(** An [xform] is first-order syntax for a particular class of
    functions that we use in grammars, and in grammar transformations.
    We make the syntax explicit so that we can (a) compare [xform]'s
    for equality, and (b) to optimize them.  
*)
Inductive xform : type -> type -> Type := 
| Xid : forall t, xform t t
| Xzero : forall t, xform Void_t t
| Xcomp : forall t1 t2 t3, xform t1 t2 -> xform t2 t3 -> xform t1 t3
| Xchar : forall t, char_p -> xform t Char_t  
| Xunit : forall t, xform t Unit_t            
| Xempty : forall t1 t2, xform t1 (List_t t2) 
| Xpair : forall t t1 t2, xform t t1 -> xform t t2 -> xform t (Pair_t t1 t2) 
| Xfst : forall t1 t2 t, xform t1 t -> xform (Pair_t t1 t2) t   
| Xsnd : forall t1 t2 t, xform t2 t -> xform (Pair_t t1 t2) t   
| Xinl : forall t t1 t2, xform t t1 -> xform t (Sum_t t1 t2)    
| Xinr : forall t t1 t2, xform t t2 -> xform t (Sum_t t1 t2)    
| Xmatch : forall t1 t2 t, xform t1 t -> xform t2 t -> xform (Sum_t t1 t2) t  
| Xcons : forall t1 t2, xform t1 t2 -> xform t1 (List_t t2) -> xform t1 (List_t t2) 
| Xmap : forall t1 t2, xform t1 t2 -> xform (List_t t1) (List_t t2)  
.
Notation "t1 ->> t2" := (xform t1 t2) (left associativity, at level 69, t2 at next level).

(** Interpret an [t1 ->> t2] xform as a function [interp t1 -> interp t2]. *)
Fixpoint xinterp t1 t2 (x: t1 ->> t2) : interp t1 -> interp t2 := 
  match x in t1 ->> t2 return interp t1 -> interp t2 with 
    | Xid t => fun (x:interp t) => x
    | Xzero t => fun (x:interp Void_t) => match x with end
    | Xcomp t1 t2 t3 f1 f2 => fun (x:interp t1) => xinterp f2 (xinterp f1 x)
    | Xchar t c => fun (x:interp t) => c
    | Xunit t => fun (x:interp t) => tt
    | Xempty t1 t2 => fun (x:interp t1) => @nil (interp t2)
    | Xpair t t1 t2 f1 f2 => fun (x:interp t) => (xinterp f1 x, xinterp f2 x)
    | Xfst t1 t2 t f => fun (x:interp (Pair_t t1 t2)) => xinterp f (fst x)
    | Xsnd t1 t2 t f => fun (x:interp (Pair_t t1 t2)) => xinterp f (snd x)
    | Xinl t t1 t2 f => fun (x:interp t) => inl (interp t2) (xinterp f x)
    | Xinr t t1 t2 f => fun (x:interp t) => inr (interp t1) (xinterp f x)
    | Xmatch t1 t2 t f1 f2 => 
      fun (x:interp (Sum_t t1 t2)) => 
        match x with 
          | inl x1 => xinterp f1 x1
          | inr x2 => xinterp f2 x2
        end
    | Xcons t1 t2 f1 f2 => fun (x:interp t1) => (xinterp f1 x)::(xinterp f2 x)
    | Xmap t1 t2 f => fun (x:interp (List_t t1)) => List.map (xinterp f) x
  end.

(** * Decidable equality for [xform]'s. *)
Lemma existT_neq (A:Type) (P:A->Type) (x y:A) (vx:P x) (vy:P y) : 
  x <> y -> (existT P x vx) <> (existT P y vy).
Proof.
  intros. intro. apply (simplification_existT1 _ P _ x y vx vy) ; auto.
Qed.

Definition type_pair_dec (p1 p2:type*type) : {p1=p2} + {p1<>p2}.
  intros. destruct p1. destruct p2. destruct (type_dec t t1) ; subst ;
  [ destruct (type_dec t0 t2) ; subst ; [left | right ] | right ] ; 
  congruence.
Defined.

Definition xform_dec' t1 t2 (x:t1 ->> t2) t3 t4 (y:t3 ->> t4) : 
  {@existT (type*type)%type (fun p => fst p ->> snd p) (t1,t2) x = 
   @existT (type*type)%type (fun p => fst p ->> snd p) (t3,t4) y}
+ {@existT (type*type)%type (fun p => fst p ->> snd p) (t1,t2) x <> 
   @existT (type*type)%type (fun p => fst p ->> snd p) (t3,t4) y}.
Proof.
  Ltac xdec := 
    match goal with 
      | [ H : existT ?f ?t ?x = existT ?f ?t ?y |- _ ] => 
        generalize (inj_pairT2 _ f t x y H) ; clear H ; intro H ; subst 
      | [ H : List_t _ = List_t _ |- _ ] => injection H ; clear H ; intros ; subst
      | [ H : Pair_t _ _ = Pair_t _ _ |- _ ] => injection H ; clear H ; intros ; subst
      | [ H : Sum_t _ _ = Sum_t _ _ |- _ ] => injection H ; clear H ; intros ; subst
      | _ => idtac
    end.
  intros. destruct (type_pair_dec (t1,t2) (t3,t4)) ; 
  [idtac | right ; apply existT_neq ; auto]. injection e. clear e.
  generalize t3 t4 y ; clear t3 t4 y. induction x ; destruct y ; intros ; repeat xdec ; 
  try (subst ; congruence) ; try (subst ; left ; auto ; fail) ; 
  repeat subst ; try (right ; intro ; xdec ; discriminate).
   destruct (type_dec t2 t4). subst. specialize (IHx1 _ _ y1 (eq_refl _) (eq_refl _)).
   specialize (IHx2 _ _ y2 (eq_refl _) (eq_refl _)). 
   destruct IHx1 ; [ destruct IHx2 ; [left | right ] | right] ; repeat xdec ; auto.
   intro. xdec. injection H. intros. xdec. xdec. apply n ; auto.
   intro. xdec. injection H. intros. xdec. xdec. apply n ; auto.
   right. intro. xdec. injection H. intros. repeat xdec. congruence.
   destruct (char_dec c c0). subst. left. auto. right. intro. xdec.
   injection H0. auto. specialize (IHx1 _ _ y1 (eq_refl _) (eq_refl _)).
   specialize (IHx2 _ _ y2 (eq_refl _) (eq_refl _)).  
   destruct IHx1 ; [ destruct IHx2 ; [ left | right ] | right] ; repeat xdec ; auto.
   intro ; xdec. injection H ; intros ; repeat xdec. apply n ; auto.
   intro ; xdec. injection H ; intros ; repeat xdec. apply n ; auto.
   specialize (IHx _ _ y (eq_refl _) (eq_refl _)). destruct IHx ; [ left | right ] ; 
   repeat xdec ; auto. intro. xdec. injection H ; intros ; subst. repeat xdec. apply n.
   auto. specialize (IHx _ _ y (eq_refl _) (eq_refl _)). destruct IHx ; [left | right ] ; 
   repeat xdec ; auto. intro ; xdec ; injection H ; intros ; subst. repeat xdec.
   apply n ; auto. specialize (IHx _ _ y (eq_refl _) (eq_refl _)). destruct IHx ; 
   [left | right ] ; repeat xdec ; auto ; intro ; xdec ; injection H ; intros ; subst.
   repeat xdec. apply n ; auto. specialize (IHx _ _ y (eq_refl _) (eq_refl _)).
   destruct IHx ; [left | right ] ; xdec ; auto. intro ; xdec ; injection H ; intros ; 
   subst ; repeat xdec. apply n ; auto. specialize (IHx1 _ _ y1 (eq_refl _) (eq_refl _)).
   specialize (IHx2 _ _ y2 (eq_refl _) (eq_refl _)). 
   destruct IHx1 ; [ destruct IHx2 ; [left | right ] | right ] ; repeat xdec ; auto ; 
     intro H ; repeat xdec ; injection H ; intros ; subst ; repeat xdec ; apply n ; auto.
   specialize (IHx1 _ _ y1 (eq_refl _) (eq_refl _)).
   specialize (IHx2 _ _ y2 (eq_refl _) (eq_refl _)).  
   destruct IHx1 ; [ destruct IHx2 ; [left | right ] | right ] ; repeat xdec ; auto ; 
     intro H ; repeat xdec ; injection H ; intros ; subst ; repeat xdec ; apply n ; auto.
   specialize (IHx _ _ y (eq_refl _) (eq_refl _)). destruct IHx ; [left | right ] ; 
   repeat xdec ; auto. intro. xdec. injection H ; intros ; subst. repeat xdec.
   apply n ; auto.
Defined.

Definition xform_dec t1 t2 (x1 x2:t1 ->> t2) : {x1 = x2} + {x1 <> x2}.
  intros. destruct (xform_dec' x1 x2). xdec. left. auto. right.
  intro. subst. apply n. auto.
Defined.

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

(** These next three functions help reduce [Xpair (Xfst Xid) (Xsnd Xid)] to [Xid].
    It's incredibly tedious to propagate the right types and equations around, 
    so I had to break it into three functions. *)
Definition xpair_fst_xid_snd td te (x21 : td ->> te) : forall tc t1 t2, 
  (Pair_t tc td = Pair_t t1 t2) -> (Pair_t tc td) ->> Pair_t t1 te.
  intros td te x21.
  refine (
    match x21 in td ->> te return forall tc t1 t2, (Pair_t tc td = Pair_t t1 t2) -> (Pair_t tc td) ->> Pair_t t1 te with
      | Xid t => fun tc t1 t2 H => xcoerce (Xid (Pair_t tc t)) (eq_refl _) _
      | x21' => fun tc t1 t2 H => 
        Xpair (xcoerce (Xfst _ (Xid _)) (eq_sym H) (eq_refl _)) 
        (xcoerce (xcoerce (Xsnd _ x21') H (eq_refl _)) (eq_sym H) (eq_refl _))
    end
  ). injection H. intros. subst. auto.
Defined.

Definition xpair_fst_xid ta tb (x2: ta ->> tb) : forall t1 t2, ta = Pair_t t1 t2 -> 
  ta ->> Pair_t t1 tb :=
  match x2 in ta ->> tb return forall t1 t2, ta = Pair_t t1 t2 -> ta ->> Pair_t t1 tb with
    | Xsnd tc td te x21 => (* x21 : td ->> te, tb = te *)
      fun t1 t2 (H:Pair_t tc td = Pair_t t1 t2) => xpair_fst_xid_snd x21 H 
    | x2' => 
      fun t1 t2 H => 
        Xpair (xcoerce (Xfst _ (Xid t1)) (eq_sym H) (eq_refl _)) x2'
  end.

(** This function and the two above implement:  (fst id, snd id) = id *)
Definition xpair ta tb tc (x1:ta ->> tb) (x2:ta ->> tc) : ta ->> (Pair_t tb tc) := 
  match x1 in ta ->> tb return (ta ->> tc) -> ta ->> (Pair_t tb tc)  with 
    | Xfst t1 t2 tb x11 => 
      match x11 in t1 ->> tb return 
        ((Pair_t t1 t2) ->> tc) -> (Pair_t t1 t2) ->> (Pair_t tb tc) with
        | Xid t1 => fun x2 => xpair_fst_xid x2 (eq_refl _)
        | x11 => Xpair (Xfst _ x11)
      end
    | x1 => Xpair x1
  end x2.

(** The [xpair] optimization preserves meaning. *)
Lemma xpair_corr ta tb tc (x1:ta->>tb) (x2:ta->>tc) v : 
  xinterp (xpair x1 x2) v = xinterp (Xpair x1 x2) v.
Proof.
  destruct x1 ; simpl ; auto. intros. dependent destruction x1 ; simpl ; auto.
  dependent destruction x2 ; simpl ; auto. dependent destruction x2 ; simpl ; auto.
  destruct v. auto.
Qed.

(** Used below in the eta-reduction for sums. *)
Definition xmatch_inl_id_inr tc te (x22:tc->>te) : 
  forall td ta tb, (Sum_t td te = Sum_t ta tb) -> Sum_t ta tc ->> Sum_t td te.
  intros tc te x22.
  refine (
  match x22 in tc->>te return 
    forall td ta tb, (Sum_t td te = Sum_t ta tb) -> Sum_t ta tc ->> Sum_t td te with
    | Xid t => fun td ta tb H => xcoerce (Xid (Sum_t _ _)) (eq_refl _) _
    | x22' => fun td ta tb H => 
      xcoerce (Xmatch (Xinl _ (Xid _)) (Xinr _ x22')) (eq_refl _) _
  end
  ) ; injection H ; intros ; subst ; auto. Grab Existential Variables. auto. auto.
 auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
 auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
Defined.

(** Used below in the eta-reduction for sums. *)
Definition xmatch_inl_id t1 t2 (x2:t1->>t2) : 
  forall ta tb, t2 = Sum_t ta tb -> Sum_t ta t1 ->> t2 := 
  match x2 in t1->>t2 return 
    forall ta tb, t2 = Sum_t ta tb -> Sum_t ta t1 ->> t2 with
    | Xinr tc td te x22 => fun ta tb H => xmatch_inl_id_inr x22 H
    | x2' => 
      fun ta tb H => 
        xcoerce (Xmatch (Xinl _ (Xid _)) (xcoerce x2' (eq_refl _) H)) (eq_refl _) 
        (eq_sym H)
  end.

(** This function and the two above implement the reduction
    [match x with inl a => inl a | inr b => inr b end = id]. *)
Definition xmatch ta tb tc (x1:ta->>tc) (x2:tb->>tc) : Sum_t ta tb ->> tc :=
  match x1 in ta->>tc return tb->>tc -> Sum_t ta tb ->> tc with
    | Xinl t1 t2 t3 x11 => 
      (* tc = Sum_t t2 t3, ta=t1 *)
      match x11 in t1->>t2 return (tb->>Sum_t t2 t3) -> Sum_t t1 tb ->> Sum_t t2 t3 with
        | Xid t => fun x2 => xmatch_inl_id x2 (eq_refl _)
        | x11' => Xmatch (Xinl _ x11')
      end
    | x1' => Xmatch x1'
  end x2.

(** Correctness of eta-reduction for sums. *)
Lemma xmatch_corr ta tb tc (x1:ta->>tc) (x2:tb->>tc) v : 
  xinterp (xmatch x1 x2) v = xinterp (Xmatch x1 x2) v.
Proof.
  destruct x1 ; simpl ; auto ; intros. dependent destruction x1 ; simpl ; destruct v ; 
  auto ; dependent destruction x2 ; simpl ; auto. dependent destruction x2 ; auto.
  dependent destruction x2 ; auto.
Qed.

(** These next few functions implement specific reductions for when a particular
    combinator is composed with another.  Together, they implement the cut
    elimination for the sequent language. *)
(** (f1, f2) o id = (f1, f2)
    (f1, f2) o (char c) = char c
    (f1, f2) o unit = unit
    (f1, f2) o empty = empty
    (f1, f2) o (fst f) = f1 o f
    (f1, f2) o (snd f) = f2 o f

    (f1, f2) o (fst o g1, snd o g2) = (f1 o g1, f2 o g2) ?
*)

(*
Definition xcomp_pair_pair_fst_snd 
  t t1 (f1:t ->> t1) t2 (f2:t ->> t2)
  t3 (g1 : t1 ->> t3) t4 (g2: t2 ->> t4) : t ->> (Pair_t t3 t4) := 
  (Xcomp (Xpair f1 f2) (Xpair (Xcomp (Xfst _ (Xid _)) g1) (Xcomp (Xsnd _ (Xid _)) g2))).

Definition opt_xcomp_pair_pair_fst_snd 
  t t1 (f1:t ->> t1) t2 (f2:t ->> t2)
  t3 (g1 : t1 ->> t3) t4 (g2: t2 ->> t4) : t ->> (Pair_t t3 t4) := 
  (Xpair (Xcomp f1 g1) (Xcomp f2 g2)).
*)

Definition xcomp_pair t21 t22 (x2:t21 ->> t22) : 
  forall ta tb tc (x11:ta->>tb) (x12:ta->>tc), (Pair_t tb tc = t21) -> ta ->> t22 := 
    match x2 in t21 ->> t22 return
      forall ta tb tc (x11:ta->>tb) (x12:ta->>tc), (Pair_t tb tc = t21) -> ta ->> t22 with
      | Xid t => fun ta tb tc x11 x12 H => xcoerce (Xpair x11 x12) (eq_refl _) H
      | Xchar t c => fun ta tb tc x11 x12 H => Xchar _ c
      | Xunit t => fun ta tb tc x11 x12 H => Xunit _
      | Xempty t1 t2 => fun ta tb tc x11 x12 H => Xempty _ _
      | Xfst te tf tg x22 =>
        fun ta tb tc x11 x12 H => Xcomp x11 (xcoerce x22 (eq_pair_fst H) (eq_refl _))
      | Xsnd te tf tg x22 => 
        fun ta tb tc x11 x12 H => Xcomp x12 (xcoerce x22 (eq_pair_snd H) (eq_refl _))
      | x2' => 
        fun ta tb tc x11 x12 H => 
          Xcomp (Xpair x11 x12) (xcoerce x2' (eq_sym H) (eq_refl _))
    end.

(** [xcomp_pair] is correct. *)
Lemma xcomp_pair_corr t21 t22 (x2:t21->>t22) ta tb tc (x11:ta->>tb) (x12:ta->>tc) H v: 
  xinterp (xcomp_pair x2 x11 x12 H) v = 
  xinterp (Xcomp (Xpair x11 x12) (xcoerce x2 (eq_sym H) (eq_refl _))) v.
Proof.
  destruct x2 ; simpl ; intros ; subst ; simpl ; auto ; injection H ; intros ; subst ; 
    rewrite (proof_irrelevance _ H (eq_refl _)) ; auto.
Qed.

(**  (inl f) o id = inl f
     (inl f) o (char c) = char c
     (inl f) o unit = unit
     (inl f) o empty = empty
     (inl f) o (match f1 f2) = f o f1 
*)
Definition xcomp_inl t21 t22 (x2:t21 ->> t22) : 
  forall ta tb tc (x11:ta->>tb), (Sum_t tb tc = t21) -> ta ->> t22 :=
    match x2 in t21->>t22 return 
      forall ta tb tc (x11:ta->>tb), (Sum_t tb tc = t21) -> ta ->> t22 with
      | Xid t => fun ta tb tc x11 H => xcoerce (Xinl _ x11) (eq_refl _) H 
      | Xchar t c => fun ta tb tc _ H => Xchar _ c
      | Xunit t => fun ta tb tc _ H => Xunit _
      | Xempty t1 t2 => fun ta tb tc _ H => Xempty _ _ 
      | Xmatch td te tf x21 x22 => 
        fun ta tb tc x11 H => Xcomp x11 (xcoerce x21 (eq_sum_fst H) (eq_refl _))
      | x2' => 
        fun ta tb tc x11 H => Xcomp (Xinl _ x11) (xcoerce x2' (eq_sym H) (eq_refl _))
    end.

(** [xcomp_inl] is correct *)
Lemma xcomp_inl_corr t21 t22 (x2:t21->>t22) ta tb tc (x11:ta->>tb) (H:Sum_t tb tc = t21) v: 
  xinterp (xcomp_inl x2 x11 H) v = 
  xinterp (Xcomp (Xinl _ x11) (xcoerce x2 (eq_sym H) (eq_refl _))) v.
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
  forall ta tb tc (x11:ta->>tc), (Sum_t tb tc = t21) -> ta ->> t22 :=
    match x2 in t21->>t22 return 
      forall ta tb tc (x11:ta->>tc), (Sum_t tb tc = t21) -> ta ->> t22 with
      | Xid t => fun ta tb tc x11 H => xcoerce (Xinr _ x11) (eq_refl _) H 
      | Xchar t c => fun ta tb tc _ H => Xchar _ c
      | Xunit t => fun ta tb tc _ H => Xunit _
      | Xempty t1 t2 => fun ta tb tc _ H => Xempty _ _ 
      | Xmatch td te tf x21 x22 => 
        fun ta tb tc x11 H => Xcomp x11 (xcoerce x22 (eq_sum_snd H) (eq_refl _))
      | x2' => 
        fun ta tb tc x11 H => Xcomp (Xinr _ x11) (xcoerce x2' (eq_sym H) (eq_refl _))
    end.

(** [xcomp_inr] is correct. *)
Lemma xcomp_inr_corr t21 t22 (x2:t21->>t22) ta tb tc (x11:ta->>tc) (H:Sum_t tb tc = t21) v: 
  xinterp (xcomp_inr x2 x11 H) v = 
  xinterp (Xcomp (Xinr _ x11) (xcoerce x2 (eq_sym H) (eq_refl _))) v.
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
    | x2' => fun t1 x1 => Xcomp x1 x2'
  end.

(** [xcomp_r] is correct. *)
Lemma xcomp_r_corr t21 t22 (x2:t21->>t22) t11 (x1:t11->>t21) v : 
  xinterp (xcomp_r x2 x1) v = xinterp (Xcomp x1 x2) v.
Proof.
  induction x2 ; simpl ; intros ; auto.
Qed.

(** Cut elimination:
     id o f = f
     zero o f = zero
     (f1 o f2) o f3 = f1 o (f2 o f3)
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
      | Xinl ta tb tc x11 => fun t22 x2 => xcomp_inl x2 x11 (eq_refl _)
      | Xinr ta tb tc x11 => fun t22 x2 => xcomp_inr x2 x11 (eq_refl _)
      | Xmap ta tb x11 => fun t22 x2 => xcomp_map x2 x11 (eq_refl _)
      | Xempty ta tb => fun t22 x2 => xcomp_empty x2 _ (eq_refl _)
      | Xcons ta tb x11 x12 => fun t22 x2 => xcomp_cons x2 x11 x12 (eq_refl _)
      | x1' => fun t22 x2 => xcomp_r x2 x1'
    end.

(** [xcomp] (cut elimination) is correct. *)
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
  apply xcomp_empty_corr. apply xcomp_pair_corr. apply xcomp_inl_corr.
  apply xcomp_inr_corr. apply xcomp_cons_corr. apply xcomp_map_corr.
Qed.

(** Optimize an [xform].  Most of the reductions are in the
    [Xcomp] (composition) case, though there are a couple of
    eta reductions for [Xpair] and [Xmatch] respectively. *)
Fixpoint xopt t1 t2 (x:t1 ->> t2) : t1 ->> t2 := 
  match x with
    | Xpair ta tb tc x1 x2 => xpair (xopt x1) (xopt x2)
    | Xmatch ta tb tc x1 x2 => xmatch (xopt x1) (xopt x2)
    | Xcomp ta tb tc x1 x2 => xcomp (xopt x1) (xopt x2)
    | Xinl ta tb tc x1 => Xinl _ (xopt x1)
    | Xinr ta tb tc x1 => Xinr _ (xopt x1)
    | Xcons ta tb x1 x2 => Xcons (xopt x1) (xopt x2)
    | Xfst ta tb tc x1 => Xfst _ (xopt x1)
    | Xsnd ta tb tc x1 => Xsnd _ (xopt x1)
    | Xmap ta tb x1 => Xmap (xopt x1)
    | x' => x'
  end.

(** [xopt] is correct. *)
Lemma xopt_corr t1 t2 (x:t1 ->> t2) : xinterp (xopt x) = xinterp x.
Proof.
  induction x ; simpl ; intros ; auto ; try (rewrite <- IHx ; auto) ; 
    try (rewrite <- IHx1 ; rewrite <- IHx2 ; auto) ; apply extensionality ; intros.
  apply xcomp_corr. apply xpair_corr. apply xmatch_corr.
Qed.

(** * Optimizing constructors for grammars *)

(** g ++ 0 ==> g @ inl *)
Definition OptAlt_r t2 (g2:grammar t2) : forall t1, grammar t1 -> grammar (Sum_t t1 t2) :=
  match g2 in grammar t2' return forall t1, grammar t1 -> grammar (Sum_t t1 t2') with
    | Zero t2 => fun t1 g1 => Xform (Xinl _ (Xid _)) g1
    | g2' => fun t1 g1 => Alt g1 g2'
  end.

(** 0 ++ g ==> g @ inr *)
Definition OptAlt_l t1 (g1:grammar t1) : forall t2, grammar t2 -> grammar (Sum_t t1 t2) :=
  match g1 in grammar t1' return forall t2, grammar t2 -> grammar (Sum_t t1' t2) with
    | Zero t1 => fun t2 g2 => Xform (Xinr _ (Xid _)) g2
    | g1' => fun t2 g2 => OptAlt_r g2 g1'
  end.

(** Should reduce (g ++ g) ==> g and perhaps re-order according to some
    total order on the grammars. *)
Definition OptAlt t1 t2 (g1:grammar t1) (g2:grammar t2) := OptAlt_l g1 g2.

(** g $ 0 ==> 0 @ zero_to_t
    g $ eps ==> g @ add_unit_r *)
Definition OptCat_r t2 (g2:grammar t2) : forall t1, grammar t1 -> grammar (Pair_t t1 t2) :=
  match g2 in grammar t2' return forall t1, grammar t1 -> grammar (Pair_t t1 t2') with
    | Zero t2' => fun t1 (g2 : grammar t1) => Zero _
    | Eps => fun t1 (g1 : grammar t1) => Xform (Xpair (Xid _) (Xunit _)) g1
    | g2' => fun t1 (g1 : grammar t1) => Cat g1 g2'
  end.

(** 0 $ g ==> 0 @ zero_to_t
    eps $ g ==> g @ add_unit_l *)
Definition OptCat t1 (g1:grammar t1) : forall t2, grammar t2 -> grammar (Pair_t t1 t2) :=
  match g1 in grammar t1' return forall t2, grammar t2 -> grammar (Pair_t t1' t2) with
    | Zero t1' => fun t2 (g2 : grammar t2) => Zero _
    | Eps => fun t2 (g2 : grammar t2) => Xform (Xpair (Xunit _) (Xid _)) g2
    | g1' => fun t2 (g2 : grammar t2) => OptCat_r g2 g1'
  end.

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

(** 0 @ f ==> 0
    g @ f1 @ f2 ==> g @ (f1 o f2)
*)
Definition OptMap' t1 (g:grammar t1) : forall t2, (interp t1 -> interp t2) -> grammar t2 := 
  match g in grammar t1' return forall t2, (interp t1' -> interp t2) -> grammar t2 with
    | Zero t => fun t2 f => Zero t2
    | Map u1 u2 f' g' => fun t2 f => @Map u1 t2 (fun x => f (f' x)) g'
    | g' => fun t2 f => @Map _ t2 f g'
  end.

Definition OptMap t1 t2 (f:interp t1 -> interp t2) (g:grammar t1) : grammar t2 := 
  @OptMap' t1 g t2 f.

Definition OptXform' t1 (g:grammar t1) : forall t2, t1->>t2 -> grammar t2 :=
  match g in grammar t1' return forall t2, t1'->>t2 -> grammar t2 with
    | Zero t => fun t2 x => Zero t2
    | Xform u1 u2 x' g' => fun t2 x => Xform (xcomp x' x) g'
    | g' => fun t2 x => Xform x g'
  end.

Definition OptXform t1 t2 (x:t1->>t2) (g:grammar t1) := @OptXform' t1 g t2 x.

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
        OptXform (Xcons (Xfst _ (Xid _)) (Xsnd _ (Xid _))) (OptCat (deriv g c) (Star g))
  end.

(** * AST Grammars *)

(** An [astgram] is similar to a grammar except that it has no [Map] or [Xform] 
    constructor, and it's not indexed by a [type].  Rather, we can compute the 
    expected [type] from the grammar itself which is effectively a polynomial 
    type representing an abstract syntax tree.  Below, we translate a [grammar] 
    to a pair of an [astgram] and a function that takes the result of the 
    [astgram] and maps it to the semantic values we would get back, given the 
    initial [grammar]. *)
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

Definition assoc_left_sum t1 t2 t3 : Sum_t t1 (Sum_t t2 t3) ->> Sum_t (Sum_t t1 t2) t3 := 
  Xmatch (Xinl _ (Xinl _ (Xid _)))
         (Xmatch (Xinl _ (Xinr _ (Xid _)))
                         (Xinr _ (Xid _))).

(** Flatten out and right-associate a list of [aAlt]s. *)
Fixpoint append_alt (ag1:astgram) (ag2:astgram) : 
  {ag:astgram & astgram_type ag ->> astgram_type (aAlt ag1 ag2)} := 
  match ag1 return {ag:astgram & astgram_type ag ->> astgram_type (aAlt ag1 ag2)} with
    | aZero => agxf ag2 (Xinr _ (Xid _))
(*
    | aAlt aga agb => 
      let (agd, xd) := append_alt agb ag2 in 
        let (agc, xc) := append_alt aga agd in 
          agxf agc (Xcomp xc (Xcomp (Xmatch (Xinl _ (Xid _)) (Xinr _ xd))
                                     (assoc_left_sum _ _ _)))
*)
    | ag1' => 
      match ag2 return {ag:astgram & astgram_type ag ->> astgram_type (aAlt ag1' ag2)} with
        | aZero => agxf ag1' (Xinl _ (Xid _))
        | ag2' => agxf (aAlt ag1' ag2') (Xid _)
      end
  end.

Definition in_agxf t (e: {ag : astgram & astgram_type ag ->> t}) cs v := 
  match e with 
    | existT ag x => exists v', in_astgram ag cs v' /\ xinterp x v' = v
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

Definition assoc_left_pair t1 t2 t3 : 
  Pair_t t1 (Pair_t t2 t3) ->> Pair_t (Pair_t t1 t2) t3 := 
  Xpair (Xpair (Xfst _ (Xid _)) (Xsnd _ (Xfst _ (Xid _)))) (Xsnd _ (Xsnd _ (Xid _))).

(** Flatten out and right-associate a list of [aCat]s. *)        
Fixpoint append_cat (ag1:astgram) (ag2:astgram) : 
  {ag:astgram & astgram_type ag ->> astgram_type (aCat ag1 ag2)} := 
  match ag1 return {ag:astgram & astgram_type ag ->> astgram_type (aCat ag1 ag2)} with
    | aZero => agxf aZero (Xzero _)
    | aEps => agxf ag2 (Xpair (Xunit _) (Xid _))
(*
    | aCat aga agb => 
      let (agd, xd) := append_cat agb ag2 in 
        let (agc, xc) := append_cat aga agd in 
          agxf agc (Xcomp xc (Xcomp (Xpair (Xfst _ (Xid _)) (Xsnd _ xd)) 
                                     (assoc_left_pair _ _ _)))
*)
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

Definition cast_interp t1 (v:interp (astgram_type t1)) t2 (H:t1 = t2) : interp (astgram_type t2).
  intros. rewrite <- H. apply v.
Defined.

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
          opt_agxf (aAlt ag11' ag12') (Xmatch (Xinl _ f1) (Xinr _ f2))
    | aCat ag11 ag12 => 
      let (ag11', f1) := null_and_split ag11 in 
        match ag11' with 
          | aZero => agxf aZero (Xzero _)
          | ag11'' => 
            let (ag12', f2) := null_and_split ag12 in 
              opt_agxf (aCat ag11'' ag12') (Xpair (Xfst _ f1) (Xsnd _ f2))
        end
    | aStar ag11 => agxf aEps (Xempty Unit_t (astgram_type ag11))
  end.

Lemma null_and_split_corr1 (ag:astgram) cs v : 
  in_astgram ag cs v -> cs = nil -> in_agxf (null_and_split ag) cs v.
Proof.
  induction 1 ; mysimp ; subst ; eauto ; try discriminate. 
  generalize (app_eq_nil _ _ H3). mysimp. specialize (IHin_astgram1 H1).
  specialize (IHin_astgram2 H2). subst. clear H3. 
  remember (null_and_split a1) as e1 ; destruct e1.
  assert (match x with | aZero => agxf aZero (Xzero _) | 
            ag11' => let (ag12',f2) := null_and_split a2 in 
              opt_agxf (aCat ag11' ag12') (Xpair (Xfst _ x0) (Xsnd _ f2))
          end = let (ag12',f2) := null_and_split a2 in 
              opt_agxf (aCat x ag12') (Xpair (Xfst _ x0) (Xsnd _ f2))).
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

Lemma null_and_split_corr2 (ag:astgram) v : 
  in_agxf (null_and_split ag) nil v -> in_astgram ag nil v.
Proof.
  induction ag ; mysimp ; subst ; auto ; ainv.
  remember (null_and_split ag1) as e1 ; remember (null_and_split ag2) as e2.
  destruct e1 as [ag11' f1] ; destruct e2 as [ag12' f2].
  assert (
    match ag11' with | aZero => agxf aZero (Xzero _) |
      ag11' => opt_agxf (aCat ag11' ag12') (Xpair (Xfst _ f1) (Xsnd _ f2)) end = 
        opt_agxf (aCat ag11' ag12') (Xpair (Xfst _ f1) (Xsnd _ f2))).
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
    residual you get when matching and removing the first character [c]. *)
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
          opt_agxf (aAlt ag11' ag12') (Xmatch (Xinl _ f1) (Xinr _ f2))
    | aCat ag11 ag12 => 
      let (ag11', f1) := deriv_and_split ag11 c in 
        let (ag_left, f_left) := opt_ag (aCat ag11' ag12) in
          let (ag11null', fnull) := null_and_split ag11 in 
            match ag11null' with 
              | aZero => 
                agxf ag_left (Xcomp f_left
                  (Xpair (Xfst (astgram_type ag12) f1)
                         (Xsnd (astgram_type ag11') (Xid (astgram_type ag12)))))
              | ag11null => 
                let (ag12', f2) := deriv_and_split ag12 c in 
                  let (ag_right, f_right) := opt_ag (aCat ag11null ag12') in
                    opt_agxf (aAlt ag_left ag_right) 
                    (Xmatch (Xcomp f_left (Xpair (Xfst _ f1) (Xsnd _ (Xid _))))
                      (Xcomp f_right (Xpair (Xfst _ fnull) (Xsnd _ f2))))
            end
    | aStar ag0 => 
      let (ag0', f) := deriv_and_split ag0 c in 
        opt_agxf (aCat ag0' (aStar ag0)) (Xcons (Xfst _ f) (Xsnd _ (Xid _)))
  end.

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

Definition cross_prod t1 t2 (xs:list t1) (ys:list t2) : list (t1 * t2) := 
  (fold_right (fun v a => (map (fun w => (v,w)) ys) ++ a) nil xs).

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

Lemma astgram_extract_nil_corr1 ag cs v : 
  in_astgram ag cs v -> cs = [] -> In v (astgram_extract_nil ag).
Proof.
  induction 1 ; simpl ; intros ; subst ; try congruence ; eauto.
  generalize (app_eq_nil _ _ H3). mysimp ; subst.
  eapply in_cross_prod ; eauto. eapply in_or_app.  left.
  apply in_map ; auto. eapply in_or_app. right. apply in_map ; auto.
  generalize (app_eq_nil _ _ H4) ; mysimp ; subst.
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
                  agxf ag2 (xcomp x2 x1)
  end.

Lemma derivs_and_split_corr1 cs ag v : 
  in_astgram ag cs v -> in_agxf (derivs_and_split ag cs) nil v.
Proof.
  induction cs ; simpl ; eauto. intros.
  generalize (deriv_and_split_corr1 H). intros. specialize (H0 _ _ (eq_refl _)).
  unfold in_agxf in *. destruct (deriv_and_split ag a). mysimp. 
  remember (derivs_and_split x cs) as e. destruct e. 
  unfold agxf. specialize (IHcs _ _ H0). rewrite <- Heqe in IHcs. mysimp. 
  subst. generalize (xcomp_corr x3 x0 x4).  intros. exists x4. split ; auto.
Qed.

Lemma derivs_and_split_corr2 cs ag v : 
  in_agxf (derivs_and_split ag cs) nil v -> in_astgram ag cs v.
Proof.
  induction cs ; simpl. intros ; mysimp. subst. auto.
  intros. generalize (deriv_and_split_corr2 ag a). intros.
  remember (deriv_and_split ag a) as e ; destruct e.  
  remember (derivs_and_split x cs) as e2 ; destruct e2. 
  unfold in_agxf in H. unfold agxf in H. mysimp. eapply H0.
  generalize (xcomp_corr x2 x0 x3). intros. rewrite H2 in H1. simpl in H1.
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

(** * Construction of a deterministic-finite-state automata (really transducer)
      for table-based parsing *)
Section DFA.

  Definition states_t := list astgram.
  Notation "s .[ i ] " := (nth i s aZero) (at level 40).

  Record entry_t(row:nat)(states:states_t) := 
    { next_state : nat ; 
      next_state_lt : next_state < length states ; 
      next_xform : astgram_type (states.[next_state]) ->> astgram_type (states.[row])
    }.

  Definition row_t(i:nat)(s:states_t) := list (entry_t i s).
  Record transition_t(s:states_t) := {
    row_num : nat ; 
    row_num_lt : row_num < length s ;
    row_entries : list (entry_t row_num s)
  }.
  Definition transitions_t(s:states_t) := list (transition_t s).
  (* Our [DFA] (really a deterministic finite-state transducer) has a number
     of states [n].  Each state corresponds to an astgrammar, and in particular
     dfa_states[0] corresponds to the original grammar, and each other state
     corresponds to the derivative of dfa_states[0] with respect to some string
     of tokens t1,...,tn.  We transition from states using the transition table.
     In particular, if we are in state i, given input token [t], we compute
     our next state as next_state of transition[i][t].  The next_xform in transition[i][t]
     says how to transform AST values extracted from next_state(transition[i][t]) 
     to the type of AST values in states[i].  The accept and rejects rows 
     record whether there is any "null" value that can be extracted from the 
    a current state.  
     
     The right thing to do is really convert this to finite maps...
     *)
  Record DFA := {
    dfa_num_states : nat ; 
    dfa_states : states_t ; 
    dfa_states_len : length dfa_states = dfa_num_states ; 
    dfa_transition : transitions_t dfa_states ; 
    dfa_transition_len : length dfa_transition = dfa_num_states ; 
    dfa_transition_r : forall i, match nth_error dfa_transition i with 
                                   | Some r => row_num r = i
                                   | None => True
                                 end ;
    dfa_accepts : list bool ; 
    dfa_accepts_len : length dfa_accepts = dfa_num_states ; 
    dfa_rejects : list bool ;
    dfa_rejects_len : length dfa_rejects = dfa_num_states 
  }.
  
  (** Instead of working directly in terms of lists of [char_p]'s, we instead
     work in terms of [token_id]'s where a [token_id] is just a [nat] in the
     range 0..[num_tokens]-1.  We assume that each [token_id] can be mapped
     to a list of [char_p]'s.  For example, in the x86 parser, our characters
     are bits, but our tokens represent bytes in the range 0..255.  So the
     [token_id_to_chars] function should extract the n bits correspond to the
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
      { s' : states_t & row_t gpos (s ++ s') }.
      refine (
        fix gen_row' (n:nat) (s:states_t) (tid:token_id) 
                (H:s.[gpos] = g) (H1:gpos < length s) : 
                { s' : states_t & row_t gpos (s ++ s') } := 
        match n with 
          | 0 => existT _ nil nil
          | S n' => 
            let (g',x) := derivs_and_split g (token_id_to_chars tid) in
              let p := find_or_add g' s in 
                let (s2, row) := gen_row' n' (s ++ (fst p)) (1 + tid) _ _ in 
                  let e : entry_t gpos ((s ++ (fst p)) ++ s2) := 
                    {| next_state := (snd p) ; 
                       next_state_lt := _ ; 
                       next_xform := (xcoerce x _ _) |} in
                    existT _ ((fst p) ++ s2) _
        end). rewrite nth_lt ; auto. rewrite app_length. omega.
      generalize (find_index_some g' s).
      unfold find_or_add in p. intros. destruct (find_index g' s).  simpl.
      specialize (H0 n0 (eq_refl _)). rewrite <- app_nil_end. rewrite app_length.
      omega. simpl. rewrite app_length. rewrite app_length. simpl. omega.
      generalize (find_or_add_app g' s s2). intro. rewrite H0. clear H0. 
      rewrite app_ass. auto.  rewrite <- H. rewrite app_ass. 
      rewrite nth_lt ; auto. rewrite <- app_ass. apply (e::row).
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
         next_xform := xcoerce (next_xform e) _ _
      |}
    ) ; rewrite app_nth1 ; auto. apply (next_state_lt e). 
  Defined.

  Definition coerce_transitions s1 s (ts:transitions_t s) : transitions_t (s ++ s1) := 
    List.map (fun (t:transition_t s) => 
      {| row_num := row_num t ; 
         row_num_lt := app_length_lt s s1 (row_num_lt t) ;
         row_entries := List.map (coerce_entry _ (row_num_lt t)) (row_entries t) |}) ts.

  (** Build a transition table by closing off the reachable states.  The invariant
     is that we've closed the table up to the [next_state] and have generated the
     appropriate transition rows for the states in the range 0..next_state-1.
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
              let (s1, row) := @gen_row r next_state s (nth_error_some _ _ H)
                                 (nth_error_some_lt _ _ H) in 
              let t := {| row_num := next_state ; 
                          row_num_lt := app_length_lt _ _ (nth_error_some_lt _ _ H) ; 
                                row_entries := row |} in
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
    remember (gen_row s (e a eq_refl) (l a eq_refl)) as r. destruct r. 
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
    rewrite map_length. auto.
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
    specialize (IHn _ _ _ _ _ H). destruct s ; simpl in * ; try congruence.
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

  Definition lookup_trans (d:DFA) (row : nat) (col : nat) : 
    option { ag : astgram & astgram_type ag ->> astgram_type (dfa_states d .[row]) } := 
    match nth_error (dfa_transition d) row as x return 
      match x with | Some r => row_num r = row | None => True end ->
      option { ag : astgram & astgram_type ag ->> astgram_type (dfa_states d .[row])}
      with
      | None => fun _ => None
      | Some r => fun H => 
        match nth_error (row_entries r) col with
          | None => None
          | Some e => Some (existT _ ((dfa_states d).[next_state e])
            (xcoerce (next_xform e) (eq_refl _) (dfa_is_deriv_cast d H)))
        end
    end (dfa_transition_r d row).
    
(*
  Lemma gen_row_is_deriv g gpos n s tid H H1 : 
    match gen_row' n s tid H H1 with 
      | existT s' r => 
        forall j, 
          match nth_error r j with
            | None => True
            | Some e => deriv_and_split g j = 
              Some (existT _ (s'.[next_state e]) (
                (xcoerce (next_xform e) (eq_refl _) 

  Lemma dfa_is_deriv : 
    forall n ag0 d, build_dfa n ag0 = Some d -> 
      forall i, i < dfa_num_states d -> 
        forall j, j < num_tokens ->
          lookup_trans d i j = 
          Some (derivs_and_split ((dfa_states d).[i]) (token_id_to_chars j)).
  Proof.
    intros n ag0 d H. induction i.
    destruct n ; unfold build_dfa in H ; simpl in H. discriminate. 
    unfold build_transition_table in H. simpl in H. 
*)
    
          

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

    Fixpoint table_parse' (i:nat) (ts:list token_id) 
      (f:astgram_type ((dfa_states d).[i]) ->> t) : 
      option { a : astgram & ((astgram_type a ->> t) * (list token_id))%type } := 
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
                          (xcomp (next_xform e) (xcoerce f (table_cast _ _ H) (eq_refl _)))
                    end (eq_refl _)
              end (eq_refl _)
          end.
  End TABLE_PARSE.

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
    match build_dfa n ag as d return (build_dfa n ag = d) -> _ with 
      | None => fun _ => None
      | Some d => 
        fun H => 
          match table_parse' d 0 ts (Xid _) with
            | None => None
            | Some (existT a' (xf, ts')) => 
              let vs := astgram_extract_nil a' in
                let xf' := xcoerce xf (eq_refl _) (dfa_zero_coerce _ _ H) in 
                Some (ts', List.map (fun z => f (xinterp xf' z)) vs)
          end
    end (eq_refl _).

End DFA.

(** Alas, the overhead of manipulating the types with the [xform]'s 
    makes the approach developed above unworkable.  In particular,
    the time it takes to construct the DFA table is just too long
    to be of use.

    So here, we develop an "untyped" version of [xform]'s which we
    call [uform].  The [uform]s are not decorated by types except
    in a few key places---just enough that we can reconstruct an
    [xform] given the input type.  Furthermore, the types that are
    on the [uform]s are computed lazily.  This avoids the need to
    actually compute some very expensive [astgram] types during the
    table construction.

    This development mirrors the development with the typed [xform]s
    and indeed, shows that we can re-decorate all of the calculated
    [uform]s with types and get out something equivalent to the 
    [xform]s calculated above. 

    The resulting DFA construction is much, much faster and only takes
    a few seconds (for extracted Ocaml code.)
*)

(** Used to simulate lazy evaluation *)
Inductive memo(A:Type) := 
| Val : A -> memo A
| Thunk : (unit -> A) -> memo A.

Definition force {A} (m:memo A) : A := 
  match m with 
    | Val x => x
    | Thunk f => f tt
  end.

Definition force_opt {A} (m:option (memo A)) : option A := 
  match m with 
    | None => None
    | Some m => Some (force m)
  end.

(** (Mostly) untyped transforms.  We leave types on the few cases
    where it's not easy to infer things. *)
Inductive uform : Type := 
| Uid : uform
| Uzero : memo type -> uform 
| Ucomp : uform -> uform -> uform
| Uchar : char_p -> uform
| Uunit : uform 
| Uempty : memo type -> uform 
| Upair : uform -> uform -> uform 
| Ufst : uform -> uform
| Usnd : uform -> uform
| Uinl : memo type -> uform -> uform
| Uinr : memo type -> uform -> uform
| Umatch : uform -> uform -> uform
| Ucons : uform -> uform -> uform
| Umap : uform -> uform.

(** Given an input (memoized) type and a [uform], calculate the 
    output [type].  Note that the output type will be meaningless
    if the [uform] is not well-formed, but it's easier to work with
    a total function than a partial function. *)
Fixpoint synth (t1:memo type) (u:uform) : memo type := 
  match u with 
    | Uid => t1
    | Uzero t => t
    | Ucomp u1 u2 => synth (synth t1 u1) u2
    | Uchar _ => Val Char_t
    | Uunit => Val Unit_t
    | Uempty t => Thunk (fun _ => List_t (force t))
    | Upair u1 u2 => Thunk (fun _ => (Pair_t (force (synth t1 u1)) (force (synth t1 u2))))
    | Ufst u => 
      Thunk (fun _ => 
        match force t1 with 
          | Pair_t ta tb => force (synth (Val ta) u)
          | _ => Unit_t
        end)
    | Usnd u =>
      Thunk (fun _ => 
        match force t1 with 
          | Pair_t ta tb => force (synth (Val tb) u)
          | _ => Unit_t
        end)
    | Uinl tb u => Thunk (fun _ => (Sum_t (force (synth t1 u)) (force tb)))
    | Uinr ta u => Thunk (fun _ => (Sum_t (force ta) (force (synth t1 u))))
    | Umatch u1 u2 => 
      Thunk (fun _ => 
        match force t1 with 
          | Sum_t ta tb => force (synth (Val ta) u1)
          | _ => Unit_t
        end)
    | Ucons u1 u2 => Thunk (fun _ => List_t (force (synth t1 u1)))
    | Umap u1 => 
      Thunk (fun _ => 
        match force t1 with 
          | List_t t => List_t (force (synth (Val t) u1))
          | _ => Unit_t
        end)
  end.

(** Erase the types on an [xform] to get a [uform]. *)
Fixpoint erase t1 t2 (x : t1 ->> t2) : uform := 
  match x with 
    | Xid t => Uid 
    | Xzero t => Uzero (Val t)
    | Xcomp _ _ _ x1 x2 => Ucomp (erase x1) (erase x2)
    | Xchar t c => Uchar c
    | Xunit t => Uunit 
    | Xempty t1 t2 => Uempty (Val t2)
    | Xpair _ _ _ x1 x2 => Upair (erase x1) (erase x2)
    | Xfst _ _ _ x1 => Ufst (erase x1)
    | Xsnd _ _ _ x1 => Usnd (erase x1)
    | Xinl _ t1 t2 x1 => Uinl (Val t2) (erase x1)
    | Xinr _ t1 t2 x1 => Uinr (Val t1) (erase x1)
    | Xmatch _ _ _ x1 x2 => Umatch (erase x1) (erase x2)
    | Xcons _ _ x1 x2 => Ucons (erase x1) (erase x2)
    | Xmap _ _ x1 => Umap (erase x1)
  end.

(** Show that after erasing and then synthesizing the type, we get
    the same type out. *)
Lemma erase_synth : forall t1 t2 (x:t1 ->> t2), 
  forall m, force m = t1 -> force (synth m (erase x)) = t2.
Proof.
  induction x ; simpl ; auto ; intros. rewrite (IHx1 _ H). rewrite (IHx2 _ H). auto.
  rewrite H. rewrite (IHx (Val t1) (eq_refl _)). auto. rewrite H. 
  rewrite (IHx (Val t2) (eq_refl _)) ; auto. rewrite (IHx _ H). auto.
  rewrite (IHx _ H) ; auto. rewrite H. rewrite (IHx1 (Val t1) (eq_refl _)). auto.
  rewrite (IHx1 _ H). auto. rewrite H. rewrite (IHx (Val t1) (eq_refl _)). auto.
Qed.

Lemma erase_synth_val : forall t1 t2 (x:t1 ->> t2), 
  force (synth (Val t1) (erase x)) = t2.
Proof.
  intros. apply erase_synth. auto.
Qed.

(** The [decorate] function takes an input type and a [uform] and produces
    an optional output type and [t1 ->> t2].  This will succeed iff the
    [uform] is well-formed with respect to input type [t1].  So this is
    effectively a computable type-checking judgment for [uform]s. *)
Fixpoint decorate t1 (u:uform) : option { t2 : type & xform t1 t2 } := 
  match u with 
    | Uid => Some (existT _ t1 (Xid t1))
    | Uzero m => 
      match t1 return option { t2 : type & xform t1 t2 } with
        | Void_t => let t2 := force m in Some (existT _ t2 (Xzero t2))
        | _ => None
      end
    | Ucomp u1 u2 => 
      match decorate t1 u1 with 
        | Some (existT t x1) => 
          match decorate t u2 with 
            | Some (existT t2 x2) => Some (existT _ t2 (Xcomp x1 x2))
            | None => None
          end
        | None => None
      end
    | Uchar c => Some (existT _ Char_t (Xchar t1 c))
    | Uunit => Some (existT _ Unit_t (Xunit t1))
    | Uempty m => let t := force m in Some (existT _ (List_t t) (Xempty t1 t))
    | Upair u1 u2 => 
      match decorate t1 u1, decorate t1 u2 with 
        | Some (existT ta xa), Some (existT tb xb) => 
          Some (existT _ (Pair_t ta tb) (Xpair xa xb))
        | _, _ => None
      end
    | Ufst u1 => 
      match t1 with 
        | Pair_t ta tb => 
          match decorate ta u1 with 
            | Some (existT t2 x1) => Some (existT _ t2 (Xfst tb x1))
            | None => None
          end
        | _ => None
      end
    | Usnd u1 => 
      match t1 with 
        | Pair_t ta tb => 
          match decorate tb u1 with 
            | Some (existT t2 x1) => Some (existT _ t2 (Xsnd ta x1))
            | None => None
          end
        | _ => None
      end
    | Uinl m u1 => 
      match decorate t1 u1 with 
        | Some (existT ta x1) => 
          let tb := force m in Some (existT _ (Sum_t ta tb) (Xinl tb x1))
        | _ => None
      end
    | Uinr m u1 => 
      match decorate t1 u1 with 
        | Some (existT tb x1) => 
          let ta := force m in Some (existT _ (Sum_t ta tb) (Xinr ta x1))
        | _ => None
      end
    | Umatch u1 u2 => 
      match t1 with 
        | Sum_t ta tb => 
          match decorate ta u1, decorate tb u2 with 
            | Some (existT tt1 x1), Some (existT tt2 x2) => 
              match type_dec tt1 tt2 with 
                | left H => Some (existT _ tt2 (Xmatch (xcoerce x1 (eq_refl _) H) x2))
                | right _ => None
              end
            | _, _ => None
          end
        | _ => None
      end
    | Ucons u1 u2 => 
      match decorate t1 u1, decorate t1 u2 with 
        | Some (existT ta x1), Some (existT (List_t tb) x2) => 
          match type_dec ta tb with 
            | left H => Some (existT _ (List_t tb) (Xcons (xcoerce x1 (eq_refl _) H) x2))
            | right _ => None
          end
        | _, _ => None
      end
    | Umap u1 => 
      match t1 return option { t2 : type & t1 ->> t2 } with
        | List_t t => 
          match decorate t u1 with 
            | Some (existT t2 x1) => Some (existT _ (List_t t2) (Xmap x1))
            | None => None
          end
        | _ => None
      end
  end.

(** Erasing and then decorating is an identity. *)
Lemma erase_decorate : forall t1 t2 (x:t1 ->> t2), 
  decorate t1 (erase x) = Some (existT _ t2 x).
Proof.
  induction x ; simpl ; auto ; try (rewrite IHx ; auto) ; rewrite IHx1 ; rewrite IHx2 ; auto.
  destruct (type_dec t t) ; try congruence ; auto. assert (e = eq_refl _).
  apply proof_irrelevance. rewrite H. auto. 
  destruct (type_dec t2 t2) ; try congruence. assert (e = eq_refl _).
  apply proof_irrelevance. rewrite H. auto.
Defined.

(** Now replicate the optimizations on [xform]s at the [uform] level. *)
Definition upair (u1 u2:uform) : uform := 
  match u1, u2 with 
    | Ufst Uid, Usnd Uid => Uid
    | u1', u2' => Upair u1' u2'
  end.

Definition umatch (u1 u2:uform) : uform := 
  match u1, u2 with 
    | Uinl _ Uid, Uinr _ Uid => Uid
    | u1', u2' => Umatch u1 u2
  end.

Fixpoint ucomp u1 u2 := 
  match u1, u2 with 
    | Uid, u2' => u2'
    | Uzero t, u2' => Uzero (synth t u2')
    | Ucomp u11 u12, u2' => ucomp u11 (ucomp u12 u2')
    | u1', Uid => u1'
    | _, Uchar c => Uchar c
    | _, Uunit => Uunit
    | _, Uempty t => Uempty t
    | Upair u11 u12, Ufst u2' => Ucomp u11 u2'
    | Upair u11 u12, Usnd u2' => Ucomp u12 u2'
    | Uinl _ u11, Umatch u21 u22 => Ucomp u11 u21
    | Uinr _ u12, Umatch u21 u22 => Ucomp u12 u22
    | Umap u11, Umap u12 => Umap (Ucomp u11 u12)
    | Uempty t, Umap u => Uempty (synth t u)
    | Ucons u11 u12, Umap u => Ucons (Ucomp u11 u) (Ucomp u12 (Umap u))
    | u1', u2' => Ucomp u1' u2'
  end.

Fixpoint uopt (u:uform) : uform := 
  match u with 
    | Upair u1 u2 => upair (uopt u1) (uopt u2)
    | Umatch u1 u2 => umatch (uopt u1) (uopt u2)
    | Ucomp u1 u2 => ucomp (uopt u1) (uopt u2)
    | Uinl t u1 => Uinl t (uopt u1)
    | Uinr t u2 => Uinr t (uopt u2)
    | Ucons u1 u2 => Ucons (uopt u1) (uopt u2)
    | Ufst u1 => Ufst (uopt u1)
    | Usnd u1 => Usnd (uopt u1)
    | Umap u1 => Umap (uopt u1)
    | u' => u'
  end.

Lemma decorate_synth u m t (x:force m ->> t) : 
  decorate (force m) u = Some (existT _ t x) -> 
  force (synth m u) = t.
Proof.
  induction u ; simpl ; intros. injection H. mysimp.
  remember (force m0) as e. destruct e ; try congruence.
  remember (decorate (force m) u1) as e1.
  destruct e1 ; try congruence. destruct s. specialize (IHu1 _ _ _ (eq_sym Heqe1)).
  remember (decorate x0 u2) as e2. destruct e2 ; try congruence. destruct s.
  injection H. mysimp. subst. mysimp. specialize (IHu2 _ _ _ (eq_sym Heqe2)). auto.
  injection H. mysimp. injection H. mysimp. injection H. mysimp.
  remember (decorate (force m) u1) as e1. destruct e1 ; try congruence.
  destruct s. specialize (IHu1 _ _ _ (eq_sym Heqe1)). 
  remember (decorate (force m) u2) as e2. destruct e2 ; try congruence.
  destruct s. specialize (IHu2 _ _ _ (eq_sym Heqe2)). injection H. mysimp. subst. auto.
  remember (force m) as e. destruct e ; try congruence.
  remember (decorate e1 u) as e. destruct e ; try congruence. destruct s.
  injection H. mysimp. subst. mysimp. clear H. 
  specialize (IHu (Val e1) _ _ (eq_sym Heqe0)). auto.
  remember (force m) as e. destruct e ; try congruence. 
  remember (decorate e2 u) as e. destruct e ; try congruence. destruct s.
  injection H. mysimp. subst. mysimp. clear H.
  specialize (IHu (Val e2) _ _ (eq_sym Heqe0)). auto.
  remember (decorate (force m0) u) as e1. destruct e1 ; try congruence. destruct s.
  injection H. mysimp. subst. specialize (IHu _ _ _ (eq_sym Heqe1)). rewrite IHu. auto.
  remember (decorate (force m0) u) as e1. destruct e1 ; try congruence. destruct s.
  injection H. mysimp. subst. mysimp. clear H.
  rewrite (IHu _ _ _ (eq_sym Heqe1)). auto. 
  remember (force m) as t0. destruct t0 ; try congruence.
  remember (decorate t0_1 u1) as e1. destruct e1 ; try congruence. destruct s.
  specialize (IHu1 (Val t0_1) _ _ (eq_sym Heqe1)). 
  remember (decorate t0_2 u2) as e2. destruct e2 ; try congruence. destruct s.
  destruct (type_dec x0 x2) ; try congruence.
  remember (decorate (force m) u1) as e1. destruct e1 ; try congruence. destruct s.
  specialize (IHu1 _ _ _ (eq_sym Heqe1)). 
  remember (decorate (force m) u2) as e2. destruct e2 ; try congruence. destruct s.
  specialize (IHu2 _ _ _ (eq_sym Heqe2)).
  destruct x2 ; try congruence. destruct (type_dec x0 x2) ; try congruence.
  remember (force m) as z. destruct z ; try congruence.
  remember (decorate z u) as e1. destruct e1 ; try congruence. destruct s.
  injection H. mysimp. subst. rewrite (IHu (Val z) _ _ (eq_sym Heqe1)). auto.
Qed.
  
Ltac uc_simp := 
  unfold xcoerce, eq_rec_r, eq_rec, eq_rect ; auto ;
    match goal with 
      | [ H : Some _ = Some _ |- _ ] => injection H ; clear H ; mysimp ; subst ; mysimp
      | [ H : match decorate ?t ?u with | Some _ => _ | None => _ end = _ |- _ ] => 
        let x := fresh in remember (decorate t u) as x ; destruct x ; try congruence 
      | [ s : { _ : type & _ ->> _ } |- _ ] => destruct s
      | [ H : match type_dec ?x ?y with | left _ => _ | right _ => _ end = _ |- _ ] => 
        destruct (type_dec x y) ; try congruence ; subst
    end.

(** Prove that untyped composition is equivalent to the typed composition. *)
Lemma ucomp_corr : forall u1 t1 t2 (x1:t1 ->> t2),
  decorate t1 u1 = Some (existT _ t2 x1) ->
  forall t3 (x2:t2 ->> t3) u2, 
    decorate t2 u2 = Some (existT _ t3 x2) -> 
    decorate t1 (ucomp u1 u2) = Some (existT _ t3 (xcomp x1 x2)).
Proof.
  induction u1 ; simpl ; intros ; auto ; try congruence ; repeat uc_simp. 
  destruct t1 ; try congruence. uc_simp. rewrite (decorate_synth _ _ H0). auto.
  simpl. specialize (IHu1_1 _ _ _ (eq_sym HeqH1) t3 (xcomp x4 x2) (ucomp u1_2 u2)). 
  apply IHu1_1. clear IHu1_1. specialize (IHu1_2 _ _ _ (eq_sym HeqH0) t3 x2 u2). 
  apply IHu1_2. auto. destruct u2 ; simpl in * ; try congruence ; repeat uc_simp.
  destruct x1 ; try congruence. repeat uc_simp. 
  destruct u2 ; simpl in * ; repeat uc_simp ; try congruence.
  destruct x1 ; try congruence. repeat uc_simp.
  destruct u2 ; simpl in * ; repeat uc_simp ; try congruence.
  destruct x1 ; try congruence ; repeat uc_simp. simpl.
  rewrite (@decorate_synth u2 m _ x0 (eq_sym HeqH)). auto.
  destruct u2 ; simpl in * ; repeat uc_simp ; try congruence ; simpl. 
  rewrite <- HeqH1. rewrite <- HeqH0. simpl ; uc_simp.
  rewrite <- HeqH1. rewrite <- HeqH0. rewrite <- HeqH. rewrite <- HeqH2.
  simpl ; uc_simp. rewrite <- HeqH1. rewrite <- HeqH0. rewrite <- HeqH. rewrite <- HeqH2. 
  simpl ; uc_simp. rewrite <- HeqH1. rewrite <- HeqH. simpl ; uc_simp.
  rewrite <- HeqH0. rewrite <- HeqH. simpl ; uc_simp. 
  rewrite <- HeqH1. rewrite <- HeqH0. rewrite <- HeqH. simpl ; uc_simp.
  rewrite <- HeqH1. rewrite <- HeqH0. rewrite <- HeqH. simpl ; uc_simp.
  destruct x6 ; try congruence. repeat uc_simp. rewrite <- HeqH1. rewrite <- HeqH0.
  rewrite <- HeqH2. rewrite <- HeqH. destruct (type_dec x6 x6) ; try congruence.
  rewrite (proof_irrelevance _ e (eq_refl _)). simpl ; uc_simp.
  destruct t1 ; try congruence ; repeat uc_simp. destruct u2 ; simpl in * ; repeat uc_simp ; 
  rewrite <- HeqH1 ; auto. destruct t2 ; try congruence ; repeat uc_simp.
  rewrite <- HeqH. rewrite <- HeqH0. auto. rewrite <- HeqH. rewrite <- HeqH0. auto.
  destruct t2 ; try congruence ; repeat uc_simp. destruct t2 ; try congruence ; 
  repeat uc_simp. rewrite <- HeqH. auto. rewrite <- HeqH ; auto. 
  destruct t2 ; try congruence ; repeat uc_simp. destruct x3 ; try congruence ; 
  repeat uc_simp. rewrite <- HeqH. rewrite <- HeqH0. destruct (type_dec x3 x3) ; try
  congruence. rewrite (proof_irrelevance _ e (eq_refl _)). simpl ; uc_simp.
  destruct t2 ; try congruence ; repeat uc_simp. 
  destruct t1 ; try congruence ; repeat uc_simp. 
  specialize (IHu1 _ _ x0 (eq_sym HeqH1) _ x2 u2 H0). 
  destruct u2 ; simpl in * ; repeat uc_simp. rewrite <- HeqH1.  auto.
  rewrite <- HeqH1. destruct t2 ; try congruence. repeat uc_simp.
  rewrite <- HeqH1. rewrite <- HeqH. rewrite <- HeqH0. auto.
  rewrite <- HeqH1. rewrite <- HeqH. rewrite <- HeqH0. auto.
  rewrite <- HeqH1. destruct t2 ; try congruence ; repeat uc_simp.
  rewrite <- HeqH1. destruct t2 ; try congruence ; repeat uc_simp.
  rewrite <- HeqH1. rewrite <- HeqH. auto. rewrite <- HeqH1. rewrite <- HeqH. auto.
  rewrite <- HeqH1. destruct t2 ; try congruence ; repeat uc_simp.
  rewrite <- HeqH1. rewrite <- HeqH. rewrite <- HeqH0. destruct x3 ; 
  try congruence ; repeat uc_simp. rewrite <- HeqH1. destruct t2 ; 
  try congruence ; repeat uc_simp. 
  destruct u2 ; simpl in * ; try congruence ; repeat uc_simp ; 
    rewrite <- HeqH1 ; simpl ; try uc_simp ; rewrite <- HeqH ; simpl ; try uc_simp ; 
      rewrite <- HeqH0 ; simpl ; try uc_simp.
  destruct x4 ; try congruence ; repeat uc_simp.
  destruct u2 ; simpl in * ; try congruence ; repeat uc_simp ; 
    rewrite <- HeqH1 ; simpl ; try uc_simp ; try rewrite <- HeqH ; try rewrite <- HeqH0 ; 
      simpl ; try uc_simp. destruct x4 ; try congruence ; repeat uc_simp.
  destruct t1 ; try congruence ; repeat uc_simp.
  destruct u2 ; simpl in * ; try congruence ; repeat uc_simp ; rewrite <- HeqH1 ; 
    try rewrite <- HeqH ; try rewrite <- HeqH0 ; simpl ; try uc_simp ; 
  try (destruct (type_dec t2 t2) ; try congruence ; 
    rewrite (proof_irrelevance _ e (eq_refl _))).
  destruct (type_dec t3 t3) ; try congruence ; 
    rewrite (proof_irrelevance _ e (eq_refl _)) ; simpl ; repeat uc_simp.
  destruct t2 ; try congruence ; simpl ; repeat uc_simp. 
  rewrite <- HeqH. rewrite <- HeqH2. auto. rewrite <- HeqH2. rewrite <- HeqH. auto.
  destruct t2 ; try congruence ; simpl ; repeat uc_simp.
  destruct t2 ; try congruence ; simpl ; repeat uc_simp.
  rewrite <- HeqH. auto. rewrite <- HeqH. auto. 
  destruct t2 ; try congruence ; simpl ; repeat uc_simp.
  destruct x3 ; try congruence ; simpl ; repeat uc_simp. rewrite <- HeqH.
  rewrite <- HeqH2. destruct (type_dec x3 x3) ; try congruence.
  rewrite (proof_irrelevance _ e0 (eq_refl _)). simpl ; uc_simp.
  destruct t2 ; try congruence ; simpl ; repeat uc_simp.
  destruct x3 ; try congruence ; simpl ; repeat uc_simp.
  destruct u2 ; simpl in * ; try congruence ; repeat uc_simp ; rewrite <- HeqH1 ; 
    rewrite <- HeqH0 ; try (
  destruct (type_dec x3 x3) ; try congruence ; rewrite (proof_irrelevance _ e (eq_refl _)) ; 
    simpl ; repeat uc_simp) ; try rewrite <- HeqH ; try rewrite <- HeqH2 ; simpl ; 
    repeat uc_simp. destruct x5 ; try congruence. 
  destruct (type_dec x x5) ; try congruence. subst. simpl. repeat uc_simp.
  destruct (type_dec x x) ; try congruence. rewrite (proof_irrelevance _ e (eq_refl _)).
  simpl ; repeat uc_simp. destruct t1 ; try congruence.
  destruct u2 ; simpl in * ; try congruence ; repeat uc_simp ; try congruence ; 
    rewrite <- HeqH1 ; simpl ; repeat uc_simp ; rewrite <- HeqH2 ; simpl ; repeat uc_simp.
  destruct x3 ; try congruence. destruct (type_dec x x3) ; try congruence.
  subst. repeat uc_simp.
Qed.

Ltac up_simp := 
  match goal with 
    | [ H : ?e = Some _ |- match ?e with | Some _ => _ | None => _ end = _ ] => 
      rewrite H
  end.

Ltac up_help := simpl in * ; try congruence ; repeat uc_simp ; repeat up_simp ; auto.
Ltac up_rw := 
  match goal with 
    | [ H : Some _ = match decorate ?e1 ?e2 with | Some _ => _ | None => _ end |- _] => 
      let x := fresh in remember (decorate e1 e2) as x ; 
        destruct x ; try congruence ; up_help
    | [ H : match ?t as _ return _ with 
              | Unit_t => _ | Char_t => _ | Void_t => _ | Pair_t _ _ => _ | Sum_t _ _ => _
              | List_t _ => _ | User_t _ => _ 
            end = Some _ |- _ ] => destruct t ; try congruence ; up_help
    | [ H : Some _ = 
      match ?t as _ return _ with 
        | Unit_t => _ | Char_t => _ | Void_t => _ | Pair_t _ _ => _ | Sum_t _ _ => _
        | List_t _ => _ | User_t _ => _ 
      end |- _ ] => destruct t ; try congruence ; up_help
    | [ H : Some _ = match ?t as _ return _ with 
                       | Unit_t => _ | Char_t => _ | Void_t => _ 
                       | Pair_t _ _ => _ | Sum_t _ _ => _
                       | List_t _ => _ | User_t _ => _ 
                     end _ |- _ ] => destruct t ; try congruence ; up_help
    | [ H : match ?t as _ return _ with 
              | Unit_t => _ | Char_t => _ | Void_t => _ | Pair_t _ _ => _ | Sum_t _ _ => _
              | List_t _ => _ | User_t _ => _ 
            end _ = Some _ |- _ ] => destruct t ; try congruence ; up_help
    | [H : Some _ = match type_dec ?x ?y with | left _ => _ | right _ => _ end |- _ ] => 
      destruct (type_dec x y) ; try congruence ; up_help
    | [H : ?x = ?x |- _ ] => rewrite (proof_irrelevance _ H (eq_refl _))
  end.

(** Prove that the untyped eta-reduction for pairs is equivalent to the
    typed one. *)
Lemma upair_corr : forall u1 ta tb (x1:ta->>tb),
  decorate ta u1 = Some (existT _ tb x1) -> 
  forall u2 tc (x2:ta->>tc),
  decorate ta u2 = Some (existT _ tc x2) -> 
  decorate ta (upair u1 u2) = Some (existT _ (Pair_t tb tc) (xpair x1 x2)).
Proof.
  intros.
  destruct u1 ; up_help ; repeat up_rw.
  destruct u1 ; up_help ; repeat up_rw.
  destruct u2 ; up_help ; repeat up_rw.
  destruct u2 ; up_help ; repeat up_rw.
Qed.

Ltac us_help := 
  match goal with 
    | [ |- context[match type_dec ?x ?y with | left _ => _ | right _ => _ end] ] => 
      destruct (type_dec x y) ; try congruence ; simpl ; auto
    | [ H : ?x = ?x |- _ ] => 
      rewrite (@proof_irrelevance (x = x) H (eq_refl _)) ; simpl ; auto
    | _ => up_rw 
    | _ => unfold sumbool_rec, sumbool_rect 
  end.  

(** Prove that the untyped eta-reduction for matches (sums) is equivalent
    to the typed one. *)
Lemma umatch_corr : forall u1 ta t (x1:ta->>t),
  decorate ta u1 = Some (existT _ t x1) -> 
  forall u2 tb (x2:tb->>t),
    decorate tb u2 = Some (existT _ t x2) -> 
    decorate (Sum_t ta tb) (umatch u1 u2) = Some (existT _ t (xmatch x1 x2)).
Proof.
  intros.
  destruct u1 ; up_help ; repeat us_help.
  destruct u1 ; up_help ; repeat us_help.
  destruct u2 ; up_help ; repeat us_help ; try discriminate. rewrite H0 in H. mysimp. 
  generalize HeqH H. clear HeqH H. rewrite e0. simpl. clear H0. 
  rewrite <- e0. intros. mysimp.
  destruct u2 ; up_help ; repeat us_help ; subst ; 
    try (clear H0 e ; generalize (force m) e0 x0 H ; clear e0 x0 H ; intros t e0 ; subst ; 
      simpl ; intros ; mysimp ; fail) ; simpl ; uc_simp. 
  clear e0 H0. generalize (force m) e1 x0 H ; clear e1 x0 H. intros t e1 ; subst ; 
  simpl ; intros ; mysimp. subst. repeat uc_simp. up_help. repeat us_help.
  repeat uc_simp. up_help. repeat us_help.
Qed.

(** Prove that the untyped optimizer for [uform]s is equivalent to the
    typed one for [xform]s.  *)
Lemma uopt_corr : forall t1 t2 (x:t1 ->> t2), 
  decorate t1 (uopt (erase x)) = Some (existT _ t2 (xopt x)).
Proof.
  induction x ; simpl ; auto ; try (rewrite IHx ; auto). 
  apply (ucomp_corr _ IHx1 _ IHx2).
  apply (upair_corr _ IHx1 _ IHx2).
  apply (umatch_corr _ IHx1 _ IHx2). 
  rewrite IHx1. rewrite IHx2. destruct (type_dec t2 t2) ; try congruence. 
  rewrite (proof_irrelevance _ e (eq_refl _)). uc_simp.
Qed.

Definition thunk {A B} (f:A -> B) (x:A) : memo B := Thunk (fun _ => f x).

(** Now build optimizations for [astgram]s paired with [uform]s as done
    above with [xform]s and prove they are equivalent. *)
Definition uassoc_left_sum t1 t2 t3 := 
  Umatch (Uinl t3 (Uinl t2 Uid))
         (Umatch (Uinl t3 (Uinr t1 Uid)) 
                 (Uinr (Thunk (fun _ => Sum_t (force t1) (force t2))) Uid)).

Fixpoint uappend_alt (ag1 ag2:astgram) : astgram * uform := 
  match ag1 with 
    | aZero => (ag2, Uinr (Val Void_t) Uid)
(*
   Too expensive to do all the time, so omit.  The longer proof of 
   equivalence is also commented out below. 
    | aAlt aga agb => 
      let (agd, xd) := uappend_alt agb ag2 in 
        let (agc, xc) := uappend_alt aga agd in 
          (agc, Ucomp xc (Ucomp (Umatch (Uinl (thunk astgram_type (aAlt agb ag2)) Uid)
                                        (Uinr (thunk astgram_type aga) xd))
                                (uassoc_left_sum (thunk astgram_type aga)
                                  (thunk astgram_type agb) (thunk astgram_type ag2))))
*)
    | ag1' => 
      match ag2 with 
        | aZero => (ag1', Uinl (Val Void_t) Uid)
        | ag2' => (aAlt ag1' ag2', Uid)
      end
  end.

Lemma uappend_alt_corr ag1 ag2 : 
  match append_alt ag1 ag2 with 
    | existT ag x => 
      ag = fst (uappend_alt ag1 ag2) /\ 
      decorate (astgram_type ag) (snd (uappend_alt ag1 ag2)) = 
      Some (existT _ (astgram_type (aAlt ag1 ag2)) x)
  end.
Proof.
  destruct ag1 ; try (simpl ; auto ; fail) ; 
    try (simpl ; destruct ag2 ; simpl ; auto ; fail).
Qed.
(*
  induction ag1 ; try (simpl ; auto ; fail) ; 
    try (simpl ; destruct ag2 ; simpl ; auto ; fail).
  intros. simpl. fold astgram_type. specialize (IHag1_2 ag2).
  remember (append_alt ag1_2 ag2) as e1 ; destruct e1. destruct IHag1_2 ; subst.
  specialize (IHag1_1 (fst (uappend_alt ag1_2 ag2))). 
  remember (append_alt ag1_1 (fst (uappend_alt ag1_2 ag2))) as e2 ; destruct e2. 
  simpl. destruct IHag1_1. subst. remember (uappend_alt ag1_2 ag2) as e3 ; 
  destruct e3. simpl in *. remember (uappend_alt ag1_1 a) as e4. destruct e4. 
  split ; auto. simpl in H1. simpl. rewrite H1. rewrite H0. unfold sumbool_rec, 
  sumbool_rect. 
  assert (type_dec (astgram_type ag1_1) (astgram_type ag1_1) = left (eq_refl _)).
  destruct (type_dec (astgram_type ag1_1) (astgram_type ag1_1)) ; 
  try congruence. rewrite (proof_irrelevance _ e (eq_refl _)). auto. rewrite H.
  assert (type_dec (astgram_type ag1_2) (astgram_type ag1_2) = left (eq_refl _)). 
  destruct (type_dec (astgram_type ag1_2) (astgram_type ag1_2)) ; try congruence.
  rewrite (proof_irrelevance _ e (eq_refl _)). auto. rewrite H2. simpl.
  assert (type_dec (astgram_type ag2) (astgram_type ag2) = left (eq_refl _)).
  destruct (type_dec (astgram_type ag2) (astgram_type ag2)) ; try congruence.
  rewrite (proof_irrelevance _ e (eq_refl _)). auto. rewrite H3. simpl.
  rewrite H2. simpl. rewrite H3. simpl. rewrite H. simpl. rewrite H2. simpl.
  rewrite H3. simpl. uc_simp.
Qed.
*)

Fixpoint uappend_cat (ag1 ag2:astgram) : astgram * uform := 
  match ag1 with 
    | aZero => (aZero, Uzero (thunk astgram_type (aCat ag1 ag2)))
    | aEps => (ag2, Upair Uunit Uid)
(*
   Too expensive to do all the time, so commented out.  The proof of
   equivalence for this case is also commented out below. 
    | aCat aga agb => 
      let (agd, xd) := uappend_cat agb ag2 in 
        let (agc, xc) := uappend_cat aga agd in 
          (agc, Ucomp xc (Ucomp (Upair (Ufst Uid) (Usnd xd)) 
            (Upair (Upair (Ufst Uid) (Usnd (Ufst Uid))) (Usnd (Usnd Uid)))))
*)
    | ag1' => 
      match ag2 with 
        | aZero => (aZero, Uzero (thunk astgram_type (aCat ag1' ag2)))
        | aEps => (ag1', Upair Uid Uunit)
        | ag2' => (aCat ag1' ag2', Uid)
      end
  end.

Lemma uappend_cat_corr ag1 ag2 : 
  match append_cat ag1 ag2 with 
    | existT ag x => 
      ag = fst (uappend_cat ag1 ag2) /\ 
      decorate (astgram_type ag) (snd (uappend_cat ag1 ag2)) = 
      Some (existT _ (astgram_type (aCat ag1 ag2)) x)
  end.
Proof.
  destruct ag1 ; try (simpl ; auto ; fail) ; 
    try (destruct ag2 ; simpl ; auto ; fail).
Qed.
(*
  intros ag1. induction ag1; try (simpl ; auto ; fail) ; 
  try (destruct ag2 ; simpl ; auto ; fail). intros.
  simpl. fold astgram_type. specialize (IHag1_2 ag2). remember (append_cat ag1_2 ag2) as e1.
  destruct e1. destruct IHag1_2 ; subst. specialize (IHag1_1 (fst (uappend_cat ag1_2 ag2))).
  remember (append_cat ag1_1 (fst (uappend_cat ag1_2 ag2))) as e2. destruct e2.
  simpl in *. destruct IHag1_1 ; subst. simpl in *.
  remember (uappend_cat ag1_2 ag2) as e3 ; destruct e3. simpl in *.
  remember (uappend_cat ag1_1 a) as e4 ; destruct e4. simpl in *. split ; auto. 
  rewrite H1. rewrite H0. simpl. unfold assoc_left_pair. auto.
Qed.
*)

(** Optimize an [astgram], producing a new [astgram] and [uform] *)
Definition uopt_ag (ag:astgram) : astgram * uform := 
  match ag with 
    | aAlt ag1 ag2 => uappend_alt ag1 ag2
    | aCat ag1 ag2 => uappend_cat ag1 ag2
    | aStar aZero => (aEps, Uempty (Val Void_t))
      (*
    | aStar (aStar ag') => (aStar ag', Ucons Uid (Uempty (thunk astgram_type (aStar ag'))))
    *)
    | ag' => (ag', Uid)
  end.

(** Prove that this is equivalent to the typed version. *)
Lemma uopt_ag_corr (ag:astgram) : 
  match opt_ag ag with 
    | existT ag' x => 
      ag' = fst (uopt_ag ag) /\ 
      decorate (astgram_type ag') (snd (uopt_ag ag)) = 
      Some (existT _ (astgram_type ag) x)
  end.
Proof.
  destruct ag ; try (simpl ; auto). apply (uappend_cat_corr ag1 ag2).
  apply (uappend_alt_corr ag1 ag2). destruct ag ; simpl ; auto.
Qed.

Definition opt_aguf (ag:astgram) (f:uform) := 
  let (ag', f') := uopt_ag ag in 
    (ag', ucomp f' f).

Lemma opt_aguf_corr t (ag:astgram) (f:astgram_type ag ->> t) (u:uform) 
  (H:decorate (astgram_type ag) u = Some (existT _ t f)) : 
  match opt_agxf ag f with
    | existT ag' x' => 
      ag' = fst (opt_aguf ag u) /\ 
      decorate (astgram_type ag') (snd (opt_aguf ag u)) = 
      Some (existT _ t x')
  end.
Proof.
  unfold opt_agxf, opt_aguf. intros.
  generalize (uopt_ag_corr ag). remember (opt_ag ag) as e1 ; destruct e1. 
  intros. destruct H0. unfold agxf. remember (uopt_ag ag) as e2 ; destruct e2.
  subst ; simpl in * ; split ; auto. apply (ucomp_corr u0 H1 u H).
Qed.

(** Null-and-split calculation using [uform]s.  *)
Fixpoint unull_and_split (ag1:astgram) : astgram * uform := 
  match ag1 with 
    | aEps => (aEps, Uid)
    | aZero => (aZero, Uzero (Val Void_t))
    | aChar c => (aZero, Uzero (Val Char_t))
    | aAny => (aZero, Uzero (Val Char_t))
    | aAlt ag11 ag12 => 
      let (ag11', f1) := unull_and_split ag11 in
        let (ag12', f2) := unull_and_split ag12 in
          opt_aguf (aAlt ag11' ag12')
                    (Umatch (Uinl (thunk astgram_type ag12) f1) 
                            (Uinr (thunk astgram_type ag11) f2))
    | aCat ag11 ag12 =>
      let (ag11', f1) := unull_and_split ag11 in 
        match ag11' with 
          | aZero => (aZero, Uzero (thunk astgram_type (aCat ag11 ag12)))
          | ag11'' => 
            let (ag12', f2) := unull_and_split ag12 in 
              opt_aguf (aCat ag11'' ag12') (Upair (Ufst f1) (Usnd f2))
        end
    | aStar ag11 => (aEps, Uempty (thunk astgram_type ag11))
  end.

(** Null-and-split for [uform]s is equivalent to null-and-split for
    the typed transforms. *)
Lemma unull_and_split_corr ag1 :
  match null_and_split ag1 with 
    | existT ag2 x => 
      ag2 = fst (unull_and_split ag1) /\ 
      decorate (astgram_type ag2) (snd (unull_and_split ag1)) = 
      Some (existT _ (astgram_type ag1) x)
  end.
Proof.
  induction ag1 ; simpl ; auto ;
  remember (null_and_split ag1_1) as e1 ; destruct e1 ;
  remember (null_and_split ag1_2) as e2 ; destruct e2 ; simpl in * ; mysimp ;
  remember (unull_and_split ag1_1) as e3 ; destruct e3 ; 
  remember (unull_and_split ag1_2) as e4 ; destruct e4 ; simpl in * ; subst ; 
  try (
  match goal with 
    | [ |- let (_,_) := opt_agxf ?ag ?x in _ ] => 
      eapply (@opt_aguf_corr _ ag x) 
  end ; simpl ; rewrite H2 ; rewrite H0 ; auto ; us_help ; auto ; us_help).
  destruct a ; try (simpl ; auto ; fail) ;
  match goal with 
    | [ |- let (_,_) := opt_agxf ?ag ?x in _] => eapply (@opt_aguf_corr _ ag x) ; 
      simpl in * ; rewrite H2 ; rewrite H0 ; auto
  end. 
Qed.

(** Derivative-and-split using [uform]s. *)
Fixpoint uderiv_and_split (ag1:astgram) (c:char_p) : astgram * uform := 
  match ag1 with 
    | aEps => (aZero, Uzero (Val Unit_t))
    | aZero => (aZero, Uzero (Val Void_t))
    | aChar c' => if char_dec c c' then (aEps, Uchar c) else (aZero, Uzero (Val Char_t))
    | aAny => (aEps, Uchar c)
    | aAlt ag11 ag12 => 
      let (ag11', f1) := uderiv_and_split ag11 c in 
        let (ag12', f2) := uderiv_and_split ag12 c in 
          opt_aguf (aAlt ag11' ag12') 
            (Umatch (Uinl (thunk astgram_type ag12) f1) (Uinr (thunk astgram_type ag11) f2))
    | aCat ag11 ag12 => 
      let (ag11', f1) := uderiv_and_split ag11 c in 
        let (ag_left, f_left) := uopt_ag (aCat ag11' ag12) in
          let (ag11null', fnull) := unull_and_split ag11 in 
            match ag11null' with 
              | aZero => (ag_left, Ucomp f_left (Upair (Ufst f1) (Usnd Uid)))
              | ag11null => 
                let (ag12', f2) := uderiv_and_split ag12 c in 
                  let (ag_right, f_right) := uopt_ag (aCat ag11null ag12') in
                    opt_aguf (aAlt ag_left ag_right)
                    (Umatch (Ucomp f_left (Upair (Ufst f1) (Usnd Uid))) 
                      (Ucomp f_right (Upair (Ufst fnull) (Usnd f2))))
            end
    | aStar ag0 => 
      let (ag0', f) := uderiv_and_split ag0 c in 
        opt_aguf (aCat ag0' (aStar ag0)) (Ucons (Ufst f) (Usnd Uid))
  end.

(** Proof that untyped derivative-and-split is equivalent to typed one. *)
Lemma uderiv_and_split_corr c ag1 : 
  match deriv_and_split ag1 c with 
    | existT ag2 x => 
      ag2 = fst (uderiv_and_split ag1 c) /\ 
      decorate (astgram_type ag2) (snd (uderiv_and_split ag1 c)) = 
      Some (existT _ (astgram_type ag1) x)
  end.
Proof.
  induction ag1 ; try (simpl ; auto ; fail).
  simpl ; destruct (char_dec c c0) ; simpl ; auto.
  generalize (unull_and_split_corr ag1_1). intro.
  simpl in *. fold astgram_type. 
  remember (deriv_and_split ag1_1 c) as e1 ; destruct e1.
  remember (null_and_split ag1_1) as e2 ; destruct e2.
  remember (deriv_and_split ag1_2 c) as e2 ; destruct e2. 
  generalize (uopt_ag_corr (aCat x ag1_2)) (uopt_ag_corr (aCat x1 x3)). intros. 
  simpl in *. fold astgram_type.
  remember (append_cat x ag1_2) as e9 ; destruct e9.
  remember (append_cat x1 x3) as e10 ; destruct e10. 
  repeat match goal with | [ H : _ /\ _ |- _ ] => destruct H end ; subst ;
  remember (uderiv_and_split ag1_1 c) as e3 ; destruct e3 ;
  remember (unull_and_split ag1_1) as e4 ; destruct e4 ;
  remember (uderiv_and_split ag1_2 c) as e5 ; destruct e5 ;
  remember (uappend_cat a ag1_2) as e8 ; destruct e8 ;
  remember (uappend_cat a0 a1) as e9 ; destruct e9. 
  simpl.
  generalize (@opt_aguf_corr _ (aAlt (fst (uappend_cat a ag1_2)) (fst (uappend_cat a0 a1)))
    (Xmatch (Xcomp x6 (Xpair (Xfst (astgram_type ag1_2) x0) 
      (Xsnd (astgram_type a) (Xid (astgram_type ag1_2)))))
      (Xcomp x8 (Xpair (Xfst (astgram_type a1) x2) (Xsnd (astgram_type a0) x4))))
    (Umatch (Ucomp u2 (Upair (Ufst u) (Usnd Uid))) (Ucomp u3 (Upair (Ufst u0) (Usnd u1))))).
  
  subst ; simpl in *. assert (H:u2 = snd (uappend_cat a ag1_2)) ;
  [ rewrite <- Heqe8 ; auto | idtac ] ; rewrite <- H in H3 ; rewrite H3 ; rewrite H8.
  assert (H0:u3 = snd (uappend_cat a0 a1)). rewrite <- Heqe6 ; auto. rewrite <- H0 in H2.
  rewrite H2. rewrite H4. rewrite H6. 
  repeat us_help ; unfold xcoerce, eq_rec_r, eq_rec, eq_rect ; simpl ;
  intro H1 ; specialize (H1 (eq_refl _)).
  remember (opt_agxf (aAlt (fst (uappend_cat a ag1_2)) (fst (uappend_cat a0 a1)))
    (Xmatch (Xcomp x6 (Xpair (Xfst (astgram_type ag1_2) x0) 
      (Xsnd (astgram_type a) (Xid (astgram_type ag1_2)))))
      (Xcomp x8 (Xpair (Xfst (astgram_type a1) x2) (Xsnd (astgram_type a0) x4))))) as x.
  destruct x. destruct H1. subst. 
  assert (a2 = fst (uappend_cat a ag1_2)). rewrite <- Heqe8 ; auto.
  assert (a3 = fst (uappend_cat a0 a1)). rewrite <- Heqe6 ; auto. subst. 
  destruct a0 ; auto. simpl. split ; auto. clear Heqe6 Heqe8. clear H5 Heqx x1. 
  rewrite H3. rewrite H8. auto.
  simpl in *.
  remember (deriv_and_split ag1_1 c) as e1 ; destruct e1.
  remember (deriv_and_split ag1_2 c) as e2 ; destruct e2.
  remember (uderiv_and_split ag1_1 c) as e3 ; destruct e3.
  remember (uderiv_and_split ag1_2 c) as e4 ; destruct e4. mysimp. subst.
  eapply opt_aguf_corr. simpl in *. rewrite H2. rewrite H0. repeat us_help.
  simpl in *.
  remember (deriv_and_split ag1 c) as e1 ; destruct e1.
  remember (uderiv_and_split ag1 c) as e2 ; destruct e2. mysimp. subst.
  eapply opt_aguf_corr. simpl in *. rewrite H0. repeat us_help.
Qed.

(** Derivative and split for a list of characters. *)
Fixpoint uderivs_and_split (ag:astgram) (cs:list char_p) : astgram * uform := 
  match cs with 
    | nil => (ag, Uid)
    | c::cs' => 
      let (ag1, x1) := uderiv_and_split ag c in 
        let (ag2, x2) := uderivs_and_split ag1 cs' in 
          (ag2, ucomp x2 x1)
  end.

Lemma uderivs_and_split_corr cs ag : 
  match derivs_and_split ag cs with 
    | existT ag' f => 
      ag' = fst (uderivs_and_split ag cs) /\ 
      decorate (astgram_type ag') (snd (uderivs_and_split ag cs)) = 
      Some (existT _ (astgram_type ag) f)
  end.
Proof.
  induction cs. simpl ; auto. simpl. intro. 
  generalize (uderiv_and_split_corr a ag).
  remember (deriv_and_split ag a) as e1 ; destruct e1. intros. destruct H.
  specialize (IHcs x). subst.
  remember (derivs_and_split (fst (uderiv_and_split ag a)) cs) as e2. destruct e2. 
  destruct IHcs. subst. simpl. remember (uderiv_and_split ag a) as e3. destruct e3.
  simpl in *. remember (uderivs_and_split a0 cs) as e4. destruct e4 ; simpl in *.
  split ; auto. eapply ucomp_corr ; auto.
Qed.
  
(** Construction of "untyped" DFA. *)
Section UDFA.
  Notation "s .[ i ] " := (nth i s aZero) (at level 40).

  Record uentry_t := { unext_state : nat ; unext_uform : uform }.
  Definition urow_t := list uentry_t.
  Definition utable_t := list urow_t.

  Record UDFA := { 
    udfa_num_states : nat ;
    udfa_states : states_t ; 
    udfa_transition : utable_t ; 
    udfa_accepts : list bool ;
    udfa_rejects : list bool
  }.

  Section UGENROW.
    Variable g : astgram.
    (** Generate a row in the transition table, with the ith column representing
        the index of the derivative of the state's [astgram] with respect to the
        ith character.  This may add new states on the end of the list of states. 
        Here, [n] represents the decreasing count of tokens, [tid] is the current
        token id (increasing upwards), and [s] is the list set of states.
    *)
    Fixpoint ugen_row' (n:nat) (tid:token_id) (s:states_t) : states_t * urow_t := 
      match n with 
        | 0 => (nil, nil)
        | S n' => 
          let (g', u) := uderivs_and_split g (token_id_to_chars tid) in 
            let p := find_or_add g' s in 
              let (s2, row) := ugen_row' n' (1 + tid) (s ++ (fst p))  in
              let e : uentry_t := {| unext_state := (snd p) ; unext_uform := u |} in
                ((fst p) ++ s2, e::row)
      end.
    Definition ugen_row (s:states_t) : states_t * urow_t := 
      ugen_row' num_tokens 0 s.
  End UGENROW.

  (** Build the transition table.  We start with the original [astgram] as the
      initial state, and then build its transitions, according to all of the
      possible input derivatives.  This may generate new states, which we then
      build transitions for and so on.  Terminates when the table is closed or
      we run out of fuel. *)
  Fixpoint ubuild_table' (n:nat) (rows:utable_t) (next_state:nat) (s:states_t) : 
    option (states_t * utable_t) := 
    match n with 
      | 0 => None
      | S n' => 
        match nth_error s next_state with 
          | None => Some (s, rows)
          | Some r => 
            let (s1, row) := ugen_row r s in 
              ubuild_table' n' (rows ++ [row]) (1 + next_state) (s++s1)
        end
    end.
  
  Definition ubuild_table (n:nat) (g:astgram) := ubuild_table' n nil 0 (g::nil).

  (** Build the untyped dfa. *)
  Definition ubuild_dfa (n:nat) (g:astgram) : option UDFA := 
    match ubuild_table n g with 
      | None => None
      | Some (s,t) => 
        Some {| udfa_num_states := length s ; 
                udfa_states := s ; 
                udfa_transition := t ; 
                udfa_accepts := build_accept_table s ; 
                udfa_rejects := build_reject_table s
              |}
    end.

  Section UTABLE_PARSE.
    (** A simple parser that uses the untyped dfa.  This just accumulates a
        big [uform] which can be applied to the results extracted from the
        final accepting [astgram]. *)
    Variable d : UDFA.
    Fixpoint utable_parse' (i:nat) (ts:list token_id) (u:uform) :
      option (astgram * uform * (list token_id)) := 
      if nth i (udfa_accepts d) false then
        Some (nth i (udfa_states d) aZero, u, ts)
      else 
        match ts with 
          | nil => None
          | c::ts' => 
            match nth_error (udfa_transition d) i with
              | None => None
              | Some row => 
                match nth_error row c with 
                  | None => None
                  | Some e => utable_parse' (unext_state e) ts' (ucomp (unext_uform e) u)
                end
            end
        end.

    (* Assuming we have built the untyped DFA [d] from the [astgram] [ag], 
       this function takes a list of tokens and runs [utable_parse'] on
       them.  If it succeeds, then we get back the final accepting state
       [ag'], a uform [u], and the unconsumed tokens [ts'].  We run 
       [astgram_extract_nil] to get out a list of values [vs] generated by
       the accepting state [ag'].  

       We then try to convert the uform to an [xform] mapping us from 
       [astgram_type ag'] to [astgram_type ag].  (This should always succeed 
       and in fact, in the future, I hope to prove this so that we can get 
       rid of the type equality test below.)  Then we interpret the [xform] 
       to get a function, which is applied to all of the [vs].  We then
       return those values of type [interp (astgram_type ag)] and the 
       unconsumed tokens. *)
    Variable ag : astgram.
    Definition utable_parse (ts:list token_id) :
      option ((list token_id) * list (interp (astgram_type ag))) := 
      match utable_parse' 0 ts Uid with 
        | None => None
        | Some (ag', u, ts') => 
          let vs := astgram_extract_nil ag' in 
            match decorate (astgram_type ag') u with
              | None => None
              | Some (existT t' x) => 
                match type_dec t' (astgram_type ag) with
                  | right _ => None
                  | left H => 
                    let xf' : xform (astgram_type ag') (astgram_type ag) := 
                      xcoerce x (eq_refl _) H in
                      Some (ts', List.map (fun z => xinterp xf' z) vs)
                end
            end
      end.
  End UTABLE_PARSE. 

  (** Given some fuel [n] and a grammar [g] of type [t], splits [g] into 
      an [astgram] [ag] and a semantic function [f], and then generates the
      untyped parsing table for [a] and returns a parsing function that
      uses that table.  This returns semantic values of type [astgram_type a],
      which we then map to [t] using [f].  [gen_parser] fails if it isn't
      given enough fuel to build the table.  *)
  Definition gen_uparser n t (g:grammar t) : 
    option ((list token_id) -> option ((list token_id) * list (interp t))) := 
      let (ag, f) := split_astgram g in 
        match ubuild_dfa n ag with 
          | None => None
          | Some d => 
            Some (fun ts => 
                    match @utable_parse d ag ts with 
                      | None => None
                      | Some (ts', vs) => Some (ts', List.map f vs)
                    end)
        end.


  Record instParserState (t:type) := mkPS {
    udfa : UDFA;  (* the untyped parser table *)
    agram: astgram; (* the original astgram after spliting *)
    fixup: fixfn agram t;  (* the fix-up function *)

    row : nat;  (* the current astgram *)
    uf : uform (* the untyped transform *)
  }.

  Definition opt_initial_parser_state n t (g:grammar t)
    : option (instParserState t) := 
    let (ag, f) := split_astgram g in
        match ubuild_dfa n ag with 
          | None => None
          | Some d => Some (mkPS d f 0 Uid)
        end.

  Definition parse_token t (ps:instParserState t) (tk:token_id) : 
    option (instParserState t * list (interp t)) := 
    let d := udfa ps in
    let i := row ps in
    let ag := agram ps in
      match nth_error (udfa_transition d) i with
        | None => None
        | Some row => 
          match nth_error row tk with 
            | None => None
            | Some e => 
              let next_i := unext_state e in
                if nth next_i (udfa_accepts d) false then
                  (* get to an acceptance state *)
                  let ag' := nth next_i (udfa_states d) aZero in
                    let vs := astgram_extract_nil ag' in 
                      match decorate (astgram_type ag') 
                        (ucomp (unext_uform e) (uf ps)) with
                        | None => None
                        | Some (existT t' x) => 
                          match type_dec t' (astgram_type ag) with
                            | right _ => None
                            | left H => 
                              let xf' : xform (astgram_type ag') (astgram_type ag) := 
                                xcoerce x (eq_refl _) H in
                                Some (ps, 
                                  List.map (fun z => (fixup ps) (xinterp xf' z)) vs)
                          end
                      end
                else
                  Some (mkPS d (fixup ps) next_i (ucomp (unext_uform e) (uf ps)),
                        nil)
          end
      end.

  End UDFA.

End NewParser.