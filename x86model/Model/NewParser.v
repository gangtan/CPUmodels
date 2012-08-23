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
  Parameter char_p : Set.
  Parameter char_dec : forall (c1 c2:char_p), {c1=c2} + {c1<>c2}.
  Parameter user_type : Set.
  Parameter user_type_dec : forall (t1 t2:user_type), {t1=t2} + {t1<>t2}.
  Parameter user_type_denote : user_type -> Set.
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
  ) ; injection H ; intros ; subst ; auto.
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
*)
Definition xcomp_pair t21 t22 (x2:t21 ->> t22) : 
  forall ta tb tc (x11:ta->>tb) (x21:ta->>tc), (Pair_t tb tc = t21) -> ta ->> t22 := 
    match x2 in t21->>t22 return 
      forall ta tb tc (x11:ta->>tb) (x21:ta->>tc), (Pair_t tb tc = t21) -> ta ->> t22 with
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

(**  (inr f) o id = inr f
     (inr f) o (char c) = char c
     (inr f) o unit = unit
     (inr f) o empty = empty
     (inr f) o (match f1 f2) = f o f2 
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

(**  (inl f) o id = inl f
     (inl f) o (char c) = char c
     (inl f) o unit = unit
     (inl f) o empty = empty
     (inl f) o (match f1 f2) = f o f1
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
   eapply InStar_cons. eapply IHg. eauto. eapply IHin_astgram2 ; eauto. auto. auto. auto.
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

Definition agxf' (t:type) (ag:astgram) (f:astgram_type ag ->> t) : 
  {ag : astgram & astgram_type ag ->> t} := existT _ ag f.

Definition assoc_left_sum t1 t2 t3 : Sum_t t1 (Sum_t t2 t3) ->> Sum_t (Sum_t t1 t2) t3 := 
  Xmatch (Xinl _ (Xinl _ (Xid _)))
         (Xmatch (Xinl _ (Xinr _ (Xid _)))
                         (Xinr _ (Xid _))).

(** Flatten out and right-associate a list of [aAlt]s. *)
Fixpoint append_alt (ag1:astgram) (ag2:astgram) : 
  {ag:astgram & astgram_type ag ->> astgram_type (aAlt ag1 ag2)} := 
  match ag1 return {ag:astgram & astgram_type ag ->> astgram_type (aAlt ag1 ag2)} with
    | aZero => agxf' ag2 (Xinr _ (Xid _))
    | aAlt aga agb => 
      let (agd, xd) := append_alt agb ag2 in 
        let (agc, xc) := append_alt aga agd in 
          agxf' agc (Xcomp xc (Xcomp (Xmatch (Xinl _ (Xid _)) (Xinr _ xd))
                                     (assoc_left_sum _ _ _)))
    | ag1' => 
      match ag2 return {ag:astgram & astgram_type ag ->> astgram_type (aAlt ag1' ag2)} with
        | aZero => agxf' ag1' (Xinl _ (Xid _))
        | ag2' => agxf' (aAlt ag1' ag2') (Xid _)
      end
  end.

Definition assoc_left_pair t1 t2 t3 : 
  Pair_t t1 (Pair_t t2 t3) ->> Pair_t (Pair_t t1 t2) t3 := 
  Xpair (Xpair (Xfst _ (Xid _)) (Xsnd _ (Xfst _ (Xid _)))) (Xsnd _ (Xsnd _ (Xid _))).

(** Flatten out and right-associate a list of [aCat]s. *)        
Fixpoint append_cat (ag1:astgram) (ag2:astgram) : 
  {ag:astgram & astgram_type ag ->> astgram_type (aCat ag1 ag2)} := 
  match ag1 return {ag:astgram & astgram_type ag ->> astgram_type (aCat ag1 ag2)} with
    | aZero => agxf' aZero (Xzero _)
    | aEps => agxf' ag2 (Xpair (Xunit _) (Xid _))
    | aCat aga agb => 
      let (agd, xd) := append_cat agb ag2 in 
        let (agc, xc) := append_cat aga agd in 
          agxf' agc (Xcomp xc (Xcomp (Xpair (Xfst _ (Xid _)) (Xsnd _ xd)) 
                                     (assoc_left_pair _ _ _)))
    | ag1' => 
      match ag2 return {ag:astgram & astgram_type ag ->> astgram_type (aCat ag1' ag2)} with
        | aZero => agxf' aZero (Xzero _)
        | aEps => agxf' ag1' (Xpair (Xid _) (Xunit _))
        | ag2' => agxf' (aCat ag1' ag2') (Xid _)
      end
  end.
  
(** Optimize an [astgram] -- returns a pair of a new [astgram] and an [xform] that
    maps us from the new AST to the old one. *)
Definition opt_ag (ag:astgram) : {ag2:astgram & astgram_type ag2 ->> astgram_type ag} :=
  match ag return {ag2:astgram & astgram_type ag2 ->> astgram_type ag} with
    | aAlt ag1 ag2 => append_alt ag1 ag2
    | aCat ag1 ag2 => append_cat ag1 ag2
    | aStar aZero => agxf' aEps (Xempty Unit_t Void_t)
    | aStar (aStar ag') => agxf' (aStar ag') (Xcons (Xid _) (Xempty _ _))
    | ag' => agxf' ag' (Xid _)
  end.

(** Optimize the [astgram] and optimize the resulting [xform]. *)
Definition agxf (t:type) (ag:astgram) (f:astgram_type ag ->> t) := 
  let (ag', f') := opt_ag ag in agxf' ag' (xcomp f' f).

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
          agxf (aAlt ag11' ag12') (Xmatch (Xinl _ f1) (Xinr _ f2))
    | aCat ag11 ag12 => 
      let (ag11', f1) := null_and_split ag11 in 
        let (ag12', f2) := null_and_split ag12 in 
          agxf (aCat ag11' ag12') (Xpair (Xfst _ f1) (Xsnd _ f2))
    | aStar ag11 => agxf aEps (Xempty Unit_t (astgram_type ag11))
  end.

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
          agxf (aAlt ag11' ag12') (Xmatch (Xinl _ f1) (Xinr _ f2))
    | aCat ag11 ag12 => 
      let (ag11', f1) := deriv_and_split ag11 c in 
        let (ag11null, fnull) := null_and_split ag11 in 
          let (ag12', f2) := deriv_and_split ag12 c in 
            agxf (aAlt (aCat ag11' ag12) (aCat ag11null ag12'))
            (Xmatch (Xpair (Xfst _ f1) (Xsnd _ (Xid _))) 
                    (Xpair (Xfst _ fnull) (Xsnd _ f2)))
    | aStar ag0 => 
      let (ag0', f) := deriv_and_split ag0 c in 
        agxf (aCat ag0' (aStar ag0)) (Xcons (Xfst _ f) (Xsnd _ (Xid _)))
  end.

Definition flatten t (xs: list (list t)) : list t := 
  List.fold_right (fun x xs => x ++ xs) nil xs.

Definition cross_prod t1 t2 (xs:list t1) (ys:list t2) : list (t1 * t2) := 
  flatten (List.map (fun x => List.map (fun y => (x,y)) ys) xs).

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

(** Lift the derivative from a character to a string. *)
Fixpoint derivs_and_split (ag:astgram) (cs:list char_p) : 
  {ag2:astgram & astgram_type ag2 ->> astgram_type ag} := 
  match cs with 
    | nil => agxf ag (Xid _)
    | c::cs' => let (ag1, x1) := deriv_and_split ag c in 
                let (ag2, x2) := derivs_and_split ag1 cs' in 
                  agxf ag2 (xcomp x2 x1)
  end.

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
     current state.  
     
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
  Definition token_id := nat.
  Variable num_tokens : nat.
  Variable token_id_to_chars : token_id -> list char_p.

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
    induction n; simpl ; destruct s ; simpl ; intros ; try discriminate ; 
      injection H ; intros ; subst. auto with arith. specialize (IHn _ _ H).
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

  (** Returns [false] iff the [astgram] rejects all strings. *)
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
  Definition table_parse n t (g:grammar t) (ts:list token_id) : option (list(interp t)) := 
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
                Some (List.map (fun z => f (xinterp xf' z)) vs)
          end
    end (eq_refl _).

End DFA.
(*


  Lemma nth_error_app : forall A (xs ys:list A), 
    nth_error (xs ++ ys) (length xs) = nth_error ys 0.
  Proof.
    induction xs ; mysimp.
  Qed.

  Lemma find_index'_prop : forall r s2 s1, 
    match find_index' r (length s1) s2 with
      | Some i => nth_error (s1 ++ s2) i = Some r
      | _ => True
    end.
  Proof.
    induction s2. mysimp. simpl. intros.
    destruct (astgram_dec r a). repeat (mysimp ; subst). rewrite nth_error_app. auto.
    generalize (IHs2 (s1 ++ (a::nil))).
    assert (length (s1 ++ a::nil) = S (length s1)). rewrite app_length. simpl. omega.
    rewrite H. rewrite app_ass. simpl. auto.
  Qed.
  
  Lemma nth_error_ext : forall A n (xs ys:list A) (v:A), 
    Some v = nth_error xs n -> nth_error (xs ++ ys) n = Some v.
  Proof.
    induction n. destruct xs. simpl. unfold error. intros. congruence. 
    simpl. intros. auto. simpl. destruct xs ; simpl ; unfold error ; intros.
    congruence. auto.
  Qed.
  
  Lemma nth_error_lt : forall A (xs ys:list A) n, 
    n < length xs -> nth_error (xs ++ ys) n = nth_error xs n.
  Proof.
    induction xs ; mysimp. assert False. omega. contradiction. 
    destruct n. auto. simpl. apply IHxs. omega.
  Qed.

  (** Calling [find_or_add_prop a s] ensures that if we lookup the returned index, 
     we get [a], and that the state is only extended. *)
    Lemma find_or_add_prop : forall r s, 
      match find_or_add r s with 
        | (s',i) => nth_error s' i = Some r /\ (exists s1, s' = s ++ s1) 
      end.
    Proof.
      unfold find_or_add, find_index. intros. generalize (find_index'_prop r s nil). 
      simpl. intros. destruct (find_index' r 0 s).  mysimp. exists (@nil astgram). 
      apply app_nil_end. split. rewrite nth_error_app. auto. 
      exists (r::nil). auto. 
    Qed.

    (** This is the main loop-invariant for [gen_row'].  Given an astgram [a], 
        a list of states [s], and a token number [n], running 
        [gen_row' n r s (num_tokens - n)] yields a list of states [s2]
        and transition-table [row2] such that the length of [row2] is [n], 
        [s2] is an extension of [s], and for all [m], the [mth] element of 
        [row2] is a pair (p,x) such that the [pth] element of [s2] is a
        an astgram a', and the pair (a',x) is the [deriv_and_split] of [a]
        with respect to the token [m+num_tokens-n]. *)
    Lemma gen_row'_prop r n s : 
      n <= num_tokens -> 
      match gen_row' n r s (num_tokens - n) with 
        | (s2, row2) => 
          length row2 = n /\ 
          (exists s1, s2 = s ++ s1) /\ 
          forall m, 
            m < n -> 
            match nth m row2 (num_tokens, Xzero_to_t Void_t) with
              | (p,x) => 
                match nth_error s2 p with
                  | Some r' => 
                    (r',x) = derivs_and_split r (token_id_to_chars (m + num_tokens - n)) 
                  | None => False
                end
            end
      end.
    Proof.
      induction n. mysimp. exists (@nil astgram). apply app_nil_end. 
      intros. assert False. omega. contradiction. simpl. intros.
      remember (derivs_and_split r (token_id_to_chars (num_tokens - S n))). destruct p.
      simpl. remember (find_or_add a s). destruct p ; simpl.
      generalize (find_or_add_prop a s). rewrite <- Heqp0. assert (n <= num_tokens).
      omega. intros. destruct H1. destruct H2.
      generalize (IHn s0 H0). clear IHn.
      assert (S (num_tokens - S n) = num_tokens - n). omega. rewrite <- H3.
      remember (gen_row' n r s0 (S (num_tokens - S n))). destruct p. mysimp.
      subst. rewrite app_ass. eauto. destruct m. intros. simpl. subst. 
      rewrite (nth_error_ext n0 (s ++ x0) x1 (eq_sym H1)). auto.
      intros. assert (m < n). omega. generalize (H6 _ H8).
      assert (S m + num_tokens - S n = m + num_tokens - n). omega.
      rewrite H9. auto.
   Qed.
  
   (** This is the main invariant for the [build_table] routine.  Given a 
       list of states [s] and a list of transition-table rows [ros], then for 
       all [i < n], [s(i)] and [r(i)] are defined, and the row [r(i)] is well-formed
       with respect to the state [s(i)]. *)
   Definition build_table_inv s rows n := 
     forall i, i < n -> 
       match nth_error s i, nth_error rows i with 
         | Some r, Some row => 
           length row = num_tokens /\ 
           forall t, t < num_tokens -> 
             match nth t row (num_tokens, Xzero_to_t Void_t) with
               | (p,x) => 
                 match nth_error s p with 
                   | Some r' => (r',x) = derivs_and_split r (token_id_to_chars t)
                   | None => False
                 end
             end
         | _, _ => False
       end.

   Lemma nth_error_some : forall A (xs:list A) n (v:A), 
     Some v = nth_error xs n -> n < length xs.
   Proof.
     induction xs ; destruct n ; simpl in * ; unfold error, value in * ; mysimp ; 
     try congruence. omega. generalize (IHxs n v H). intros. omega.
   Qed.

   Lemma build_table_inv_imp s rows n : 
     build_table_inv s rows n -> n <= length s /\ n <= length rows.
   Proof.
     unfold build_table_inv ; destruct n. intros. auto with arith.
     intros. assert (n < S n). auto with arith. generalize (H n H0).
     remember (nth_error s n) as e1. remember (nth_error rows n) as e2.
     destruct e1; destruct e2 ; try tauto. intros. generalize (nth_error_some _ _ Heqe1).
     generalize (nth_error_some _ _ Heqe2). intros. omega.
   Qed.

   Lemma nth_error_none A (xs:list A) n : None = nth_error xs n -> length xs <= n.
   Proof.
     induction xs ; destruct n ; simpl in * ; unfold error, value in * ; mysimp ; 
       auto with arith. congruence.
   Qed.

   (** This lemma establishes that the [build_table'] loop maintains the
       [build_table_inv] and only adds to the states and rows of the table. *)
   Lemma build_table'_prop n s rows : 
     build_table_inv s rows (length rows) -> 
     match build_table' n s rows (length rows) with 
       | None => True
       | Some (s', rows') => 
         length rows' = length s' /\ 
         build_table_inv s' rows' (length rows') /\ 
         (exists s1, s' = s ++ s1) /\ 
         (exists rows1, rows' = rows ++ rows1)
     end.
   Proof.
     induction n ; intros. mysimp.
     generalize (build_table_inv_imp H). 
     remember (build_table' (S n) s rows (length rows)) as e. destruct e ; auto.
     destruct p. simpl in Heqe. 
     remember (nth_error s (length rows)) as e. 
     destruct e. Focus 2. injection Heqe. intros ; subst.
     generalize (nth_error_none _ _ Heqe0). mysimp. auto with arith.
     exists nil. apply app_nil_end. exists nil. apply app_nil_end.
     
     assert (Some (s0, t) = 
       build_table' n (fst (gen_row a s)) (rows ++ (snd (gen_row a s))::nil) (S (length rows))).
     destruct (gen_row a s). auto. clear Heqe.
     specialize(IHn (fst (gen_row a s)) (rows ++ snd (gen_row a s)::nil)).
     remember (gen_row a s) as p. destruct p. simpl in *. 
     assert (length (rows ++ r :: nil) = S (length rows)). rewrite app_length. 
     apply plus_comm. rewrite H1 in IHn. rewrite <- H0 in IHn.
     generalize (gen_row'_prop a s (le_refl num_tokens)). 
     rewrite minus_diag. unfold gen_row in Heqp.
     rewrite <- Heqp. intros. destruct H3. destruct H2 as [H2 [[s2 H5] H6]].
     assert (build_table_inv s1 (rows ++ r :: nil) (S (length rows))). 
     Focus 2.
     specialize (IHn H7). mysimp ; subst; econstructor ; rewrite app_ass ; eauto.
     clear IHn. subst.
     unfold build_table_inv. intros. 
     assert (i < length rows \/ i = length rows). omega.
     destruct H7. specialize (H i H7). assert (i < length s). omega.
     remember (nth_error s i) as e. destruct e ; simpl ; try tauto.
     rewrite (nth_error_ext i s s2 Heqe). 
     remember (nth_error rows i) as e. destruct e ; simpl ; try tauto.
     rewrite (nth_error_ext i rows (r::nil) Heqe1). mysimp.
     intros. generalize (H9 _ H10). 
     remember (nth t0 l (num_tokens, Xzero_to_t Void_t)) as e. destruct e.
     remember (nth_error s n0) as e. destruct e ; simpl ; try tauto.
     rewrite (nth_error_ext n0 s s2 Heqe3). auto.
     subst. rewrite (nth_error_app rows (r::nil)). simpl.
     rewrite (nth_error_ext (length rows) s s2 Heqe0). mysimp.
     intros. generalize (H6 _ H7). assert (t0 + length r - length r = t0).
     omega. rewrite H8. auto.
  Qed.


  Section DFA_PARSE.
    Variable d : DFA.

    Fixpoint dfa_loop (state:nat) (x:xform) (count:nat) (ts:list token_id) : 
      option (nat * astgram * xform * list token_id) := 
      if nth state (dfa_accepts d) false then
        Some (count, nth state (dfa_states d) aZero, x, ts)
      else 
        match ts with 
          | nil => None
          | t::ts' => 
            let row := nth state (dfa_transition d) nil in 
              let (new_s,x') := nth t row (num_tokens, Xzero_to_t Void_t) in 
                dfa_loop new_s (xcomp x' x) (1+count) ts'
        end.

    Definition dfa_parse (ts:list token_id) : option (nat * astgram * xform * list token_id)
      := dfa_loop 0 (Xid (astgram_type (nth 0 (dfa_states d) aZero))) 0 ts.
  End DFA_PARSE.
  
  Lemma init_table_inv : 
    forall n ag s' rows', 
      build_table' n (ag::nil) nil 0 = Some (s', rows') -> 
      length rows' = length s' /\ 
      build_table_inv s' rows' (length rows') /\ 
      (exists s1, s' = ag::s1).
  Proof.
    intros. generalize (@build_table'_prop n (ag::nil) (@nil row_t)).
    simpl. rewrite H. intros. assert (build_table_inv (ag::nil) nil 0).
    intros i H1. assert False. omega. contradiction. specialize (H0 H1).
    mysimp. eauto.
  Qed.

  Lemma dfa_loop_corr' : 
    forall n ag d, build_dfa n ag = Some d -> 
      forall ts2 state x c ts1, 
        let curr_ag := nth state (dfa_states d) aZero in 
          derivs_and_split ag (flatten (List.map token_id_to_chars ts1)) = (curr_ag, x) -> 
          c = length ts1 -> 
          match dfa_loop d state x c ts2 with
            | None => True
            | Some (c', state', x', ts) => 
              exists ts3,  
                ts2 = ts3 ++ ts /\ c = length (ts1 ++ ts3) /\ 
                derivs_and_split ag (flatten (List.map token_id_to_chars (ts1 ++ ts3))) = 
                (state', xcomp x' x)
          end.
   Admitted.

  Lemma dfa_loop_corr : 
    forall n ag d, build_dfa n ag = Some d -> 
      
              
  Lemma dfa_loop_corr : 
    forall n ag d, build_dfa n ag = Some d -> 
      forall ts, 
        match dfa_loop d 0 (Xid (astgram_type (nth 0 (dfa_states d) aZero))) 0 ts with
          | None => True
          | Some (count, ag', x, ts') => 
            exists H : wf_xform x (astgram_type ag') (astgram_type ag), 
              parse_astgram ag (flatten (List.map token_id_to_chars ts)) = 
              List.map (xform_interp H) (astgram_extract_nil ag')
        end.
   Proof.
     intros.
     unfold build_dfa in H. remember (build_transition_table n ag) as e.
     destruct e ; try congruence. destruct p. injection H ; intros ; subst. clear H.
     unfold build_transition_table in Heqe.
     generalize (init_table_inv _ _ (eq_sym Heqe)). mysimp. subst.
     generalize ts. clear ts. induction ts. simpl. remember (accepts_null ag) as e.
     destruct e ; auto.
     assert (wf_xform (Xid (astgram_type ag)) (astgram_type ag) (astgram_type ag)). 
     eauto. exists H1.  unfold parse_astgram. simpl. 
     match goal with 
       | [ |- map ?e1 _ = map ?e2 _ ] => assert (H2: e1 = e2) ; 
         [ idtac | rewrite H2 ; auto]
     end.  
     unfold xform_interp. unfold eq_rect_r. unfold eq_rect. simpl.
     assert (derivs_and_split_pres nil ag = H1). apply proof_irrelevance.
     rewrite H2. assert (xtype_corr H1 = eq_refl _). apply proof_irrelevance.
     rewrite H3. auto.
     simpl. remember (accepts_null ag) as e. destruct e.
End DFA.

  (* Conceptually, after calling dfa_loop and getting back (n,ag,x,ts), 
     we should be able to call extract_null on ag to get back a list of
     values of type agram_type(ag).  Furthermore, x should be a well-formed
     xform that maps values of type agram_type(ag) to 
     agram_type(nth (dfa_states d) 0 aZero)  (i.e., the original astgram we
     build the DFA from.)  So we should be able to coerce x to a function
     of that type, map it across the list of values we get from extract_null ag,
     and get back a list of values.  Then at the top level, we map the 
     split-out user function to finally get back the "T" value we were expecting.

     Worried that we are doing a deep equality test on xinterp of Xcomp, but
     I don't see any easy way around it, unless we switch back to xform's
     that are more typed.  We could use wf_xform (in Type, not Prop) as the
     representation, but then have to do dependent pattern matching from hell
     to do the optimization and so forth.  Plus, we're carrying around a hell
     of a lot more type information thatn we need to.  Or, we could just add a Prop to
     the Xcomp case that demands we show rng(x1) = dom(x2), but then that
     will require an equality check when we build xcomps.  
     *)
*)
End NewParser.