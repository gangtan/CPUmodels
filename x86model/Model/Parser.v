(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

(** * Regular expression matcher based on derivatives, inspired by the paper
      of Owens, Reppy, and Turon.
*) 
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
Require Import List.
Require Import Arith.
Require Import Bool.
Require Import Eqdep.
Unset Automatic Introduction.
Set Implicit Arguments.
Axiom proof_irrelevance : forall (P:Prop) (H1 H2:P), H1 = H2.

(** ** Argument to the module that builds the parser *)
Module Type PARSER_ARG.
  (** We parameterize the development over a set of characters *)
  Parameter char_p : Set.
  Parameter char_eq : forall (c1 c2:char_p), {c1=c2} + {c1<>c2}.
  (** Now we also parameterize over names for types used in the semantic actions. *)
  Parameter tipe : Set.
  (** And we require a decidable equality for type names. *)
  Parameter tipe_eq : forall (t1 t2:tipe), {t1=t2} + {t1<>t2}.
  (** And we require an interpretation of type names as sets. *)
  Parameter tipe_m : tipe -> Set.
End PARSER_ARG.

(** ** The Parser functor *)
Module Parser(PA : PARSER_ARG).
  Import PA.

  (** An inductively generated set of names for the types of results
      returned by the parser.  We need at least unit, char, pairs, and
      lists, as well as user-defined types (tipe). *)
  Inductive result : Set := 
  | unit_t : result
  | char_t : result
  | pair_t : result -> result -> result
  | list_t : result -> result
  | sum_t  : result -> result -> result
  | tipe_t : tipe -> result.

  (** This allows us to build an equality on results. *)
  Definition result_eq : forall (r1 r2:result), {r1=r2}+{r1<>r2}.
    decide equality. apply tipe_eq.
  Defined.

  (** Now we give an interpretation of results as Coq sets. *)
  Fixpoint result_m(t:result) : Set := 
    (match t with 
       | unit_t => unit
       | char_t => char_p
       | pair_t t1 t2 => (result_m t1) * (result_m t2)
       | list_t t1 => list (result_m t1)
       | sum_t t1 t2 => (result_m t1) + (result_m t2)
       | tipe_t t => tipe_m t
     end)%type.

  (** ** Constructors for regular expression parsers. *)
  (** The parsers are indexed by the return type as a [result], and we've
      added a new kind of parser [Map_p] which is used to transform the
      result of one parser to another. *)
  Inductive parser : result -> Set := 
  | Any_p : parser char_t
  | Char_p : char_p -> parser char_t
  | Eps_p : parser unit_t
  | Cat_p : forall t1 t2 (r1:parser t1) (r2:parser t2), parser (pair_t t1 t2)
  | Zero_p : forall t, parser t
  | Alt_p : forall t (r1 r2:parser t), parser t
  | Star_p : forall t, parser t -> parser (list_t t)
  | Map_p : forall t1 t2, ((result_m t1) -> (result_m t2)) -> parser t1 -> parser t2.

  (** ** Denotational semantics for parsers *)
  (** The semantics relates input strings (as lists of characters) to result values. *)
  Inductive in_parser : forall t, parser t -> list char_p -> (result_m t) -> Prop := 
  | Any_pi : forall c cs v, cs = c::nil -> v = c -> in_parser Any_p cs v
  | Char_pi : forall c cs v, cs = c::nil -> v = c-> in_parser (Char_p c) cs v
  | Eps_pi : forall cs v, cs = nil -> v = tt -> in_parser Eps_p cs v
  | Alt_left_pi : forall t (p1 p2:parser t) cs (v:result_m t), 
    in_parser p1 cs v -> in_parser (Alt_p p1 p2) cs v
  | Alt_right_pi : forall t (p1 p2:parser t) cs (v:result_m t), 
    in_parser p2 cs v -> in_parser (Alt_p p1 p2) cs v
  | Cat_pi : forall t1 t2 (p1:parser t1) (p2:parser t2) cs v cs1 cs2 v1 v2,
    in_parser p1 cs1 v1 -> in_parser p2 cs2 v2 -> cs = cs1 ++ cs2 -> v = (v1,v2) -> 
    in_parser (Cat_p p1 p2) cs v
  | Star_eps_pi : forall t (p:parser t) cs v, cs = nil -> v = nil -> 
    in_parser (Star_p p) cs v
  | Star_cat_pi : forall t (p:parser t) cs v cs1 cs2 v1 v2,
    in_parser p cs1 v1 -> in_parser (Star_p p) cs2 v2 -> 
    cs = cs1 ++ cs2 -> v = (v1::v2) -> cs1 <> nil -> 
    in_parser (Star_p p) cs v
  | Map_pi : forall t1 t2 (f:result_m t1 -> result_m t2) (p:parser t1) cs v v1, 
    in_parser p cs v1 -> v = f v1 -> in_parser (Map_p _ f p) cs v.
  (** Note that for [Star_cat_pi] we require [cs1] to be non-empty -- this is 
     crucial for ensuring that any regular expression matches a string and 
     returns a finite list of associated values. Otherwise, something like
     [Star Eps] would take the empty string to an infinite set of possible 
     values. *)

  (** ** Internal Representation of Parsers: [regexp]s *)
  (** Internally, we translate parsers to a representation called [regexp] 
     where all of the functions are replaced with a function name that we can 
     look up in an environment.  This will allow us to put together a decidable 
     equality on regular expressions, which will in turn, allow us to hash-cons 
     them (though we don't take advantage of this yet.) *)

  (** We'll represent function names as positions in an environment list. *)
  Definition fn_name := nat.
  Definition fn_name_eq := eq_nat_dec. 

  (** In addition to user-level functions, we need a few built-in functions that 
     are used during optimization.
  *)
  Inductive fn : result -> result -> Set := 
  | Fn_name : forall (f:fn_name) t1 t2, fn t1 t2
  | Fn_const_char : forall (c:char_p), fn unit_t char_t  (* \x:unit.c *)
  | Fn_empty_list : forall t, fn unit_t (list_t t)     (* \x:unit.@nil t *)
  | Fn_cons : forall t, fn (pair_t t (list_t t)) (list_t t) (* \x:(t*list t).(fst x)::(snd x) *)
  | Fn_unit_left : forall t, fn t (pair_t unit_t t) (* \x:t.(tt,x) *)
  | Fn_unit_right : forall t, fn t (pair_t t unit_t) (* \x:t.(x,tt) *)
  | Fn_unit : forall t, fn t unit_t (* \x:t.tt *)
  .

  (** Finally, a [regexp] is just like a [parser] except that the [Map] constructor
     takes a [fn] instead of an actual function. Note that this syntax doesn't preclude 
     us from using a function name with the wrong type -- we'll capture this constraint
     later on. *)
  Inductive regexp : result -> Set :=
  | Any  : regexp char_t
  | Char : char_p -> regexp char_t
  | Eps  : regexp unit_t
  | Cat  : forall t1 t2, regexp t1 -> regexp t2 -> regexp (pair_t t1 t2)
  | Alt  : forall t, regexp t -> regexp t -> regexp t
  | Zero : forall t, regexp t
  | Star : forall t, regexp t -> regexp (list_t t)
  | Map  : forall (t u:result) (f:fn t u), regexp t -> regexp u.

  (** A simplification tactic used through the development *)
  Ltac mysimp := 
      simpl in * ; intros ; 
        repeat match goal with 
                 | [ |- context[char_eq ?x ?y] ] => destruct (char_eq x y) ; auto 
                 | [ |- _ /\ _ ] => split
                 | [ H : context[result_eq ?e1 ?e2] |- _ ] => 
                   destruct (result_eq e1 e2) ; simpl in * ; try discriminate
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
  (** Simplificaton followed by substitution. *)
  Ltac s := repeat (mysimp ; subst).

  (** Now we can try to define a syntactic equality checker on regexps.  We'll
      begin by writing some simple functions that calculate booleans to avoid
      some hair with dependencies.  *)
  Definition s2b (P Q:Prop) (x:{P}+{Q}) : bool := 
    match x with 
      | left _ => true
      | right _ => false
    end.

  (** Function equality *)
  Definition fn_eq t1 u1 (f1:fn t1 u1) t2 u2 (f2:fn t2 u2) : bool := 
    match f1, f2 with 
      | Fn_name f1 t1 u1, Fn_name f2 t2 u2 => 
        s2b (fn_name_eq f1 f2) && s2b (result_eq t1 t2) && s2b (result_eq u1 u2)
      | Fn_const_char c1, Fn_const_char c2 => if char_eq c1 c2 then true else false
      | Fn_empty_list t1, Fn_empty_list t2 => s2b (result_eq t1 t2)
      | Fn_cons t1, Fn_cons t2 => s2b (result_eq t1 t2)
      | Fn_unit_left t1, Fn_unit_left t2 => s2b (result_eq t1 t2)
      | Fn_unit_right t1, Fn_unit_right t2 => s2b (result_eq t1 t2)
      | Fn_unit t1, Fn_unit t2 => s2b (result_eq t1 t2)
      | _, _ => false
    end.

  (** Regexp equality *)
  Fixpoint regexp_eq' t1 (r1:regexp t1) t2 (r2:regexp t2) : bool := 
    match r1, r2 with 
      | Any, Any => true
      | Char c1, Char c2 => if char_eq c1 c2 then true else false
      | Eps, Eps => true
      | Cat t1a t1b r1a r1b, Cat t2a t2b r2a r2b => 
        regexp_eq' r1a r2a && regexp_eq' r1b r2b
      | Alt t1 r1a r1b, Alt t2 r2a r2b => 
        regexp_eq' r1a r2a && regexp_eq' r1b r2b
      | Zero t1, Zero t2 => s2b(result_eq t1 t2)
      | Star t1 r1a, Star t2 r2a => regexp_eq' r1a r2a
      | Map t1 u1 f1 r1a, Map t2 u2 f2 r2a => fn_eq f1 f2 && regexp_eq' r1a r2a
      | _, _ => false
    end.

  (** A tactic for help in proving the correctness of the equality routines *)
  Ltac eq_help := 
    match goal with 
      | [ |- _ /\ _ ] => split ; auto
      | [ H : context[char_eq ?c ?c0] |- _ ] => 
        destruct (char_eq c c0) ; subst ; auto ; try congruence
      | [ H : _ && _ = true |- _ ] => generalize (andb_prop _ _ H) ; clear H ; intro H ; 
        destruct H
      | [ H : _ /\ _ |- _] => destruct H ; subst
      | [ H : s2b ?e = true |- _ ] => destruct e ; simpl in H ; subst ; try congruence
      | _ => auto
    end.

  (** If [fn_eq] returns true, then we know the functions and their types are equal. *)
  Lemma fn_eq_corr : forall t1 u1 (f1:fn t1 u1) t2 u2 (f2:fn t2 u2), 
    fn_eq f1 f2 = true -> 
    t1 = t2 /\ u1 = u2 /\
    (existT (fun p => fn (fst p) (snd p)) (t1,u1) f1) = 
    (existT (fun p => fn (fst p) (snd p)) (t2,u2) f2).
  Proof.
    induction f1 ; induction f2 ; simpl ; intros; try congruence ; 
      repeat eq_help.
  Qed.
  
  (** If [regexp_eq'] returns true, then we know the regexps and their types are equal. *)
  Lemma regexp_eq'_corr : forall t1 (r1:regexp t1) t2 (r2:regexp t2), 
    regexp_eq' r1 r2 = true -> 
    t1 = t2 /\ (existT regexp t1 r1) = (existT regexp t2 r2).
  Proof.
    induction r1 ; destruct r2 ; simpl ; intros ; try congruence ; repeat (eq_help ; 
    match goal with 
      | [ IH : forall _ _, regexp_eq' ?r1 _ = true -> _, H : regexp_eq' ?r1 _ = true |- _]=>
        generalize (IH _ _ H) ; clear IH ; intros ; s
      | [ H : fn_eq ?f1 ?f2 = true |- _ ] => generalize (fn_eq_corr _ _ H) ; intros ; 
        clear H
      | _ => auto
    end).
    mysimp.
  Qed.

  (** Now we can use this routine when we try to optimize [Alt]. *)
  Definition regexp_eq t (r1 r2:regexp t) : {r1 = r2} + {True} := 
    match regexp_eq' r1 r2 as x return (regexp_eq' r1 r2 = x) -> {r1 = r2} + {True} with
      | true => fun H => left _ (inj_pairT2 _ _ _ _ _ (proj2 (regexp_eq'_corr _ _ H)))
      | false => fun H => right _ I
    end (eq_refl _).

  (** ** Environments for function names *)

  (** Function contexts map function names to a dependent pair consisting of
      - a pair of [result]s [(t1,t2)]
      - a function of type [result_m t1 -> result_m t2]. *)
  Definition fn_result_m(p:result*result) := result_m (fst p) -> result_m (snd p).
  Definition ctxt_t := list (sigT fn_result_m).
  Definition fn_result'(G:ctxt_t)(n:fn_name) : option (result*result)%type := 
    match nth_error G n with 
      | None => None
      | Some (existT p _) => Some p
    end.
  (** An empty set *)
  Inductive void : Set := .

  Definition fn_result_m_opt(p:option(result*result)) : Set := 
    match p with | None => void | Some p => fn_result_m p end.

  (** This looks up a function in the environment, given a proof that 
      the function name is in bounds. *)
  Fixpoint lookup_fn'(n:fn_name) :
    forall (G:ctxt_t), n < length G -> fn_result_m_opt (fn_result' G n) := 
    match n return forall G, n < length G -> fn_result_m_opt (fn_result' G n) with 
      | 0 => 
        fun G => 
          match G return 0 < length G -> fn_result_m_opt (fn_result' G 0) with 
            | nil => fun H => match lt_n_O _ H with end
            | (existT p f)::_ => fun H => f
          end
      | S m => 
        fun G => 
          match G return (S m) < length G -> fn_result_m_opt (fn_result' G (S m)) with
            | nil => fun H => match lt_n_O _ H with end
            | _::G' => fun H => lookup_fn' G' (lt_S_n _ _ H) 
          end
    end. 

  (** In this section, we assume some context and some map for function names. *)
  Section FNMAP.
  Variable fn_ctxt : ctxt_t.

  (** Specialize the lookup to the parameters *)
  Definition fn_result := fn_result' fn_ctxt.
  Definition lookup_fn(n:fn_name)(H:n < length fn_ctxt) := lookup_fn' fn_ctxt H.
                
  (** A function is well-formed if all of the function names have the right
      types when we look them up in the [fn_ctxt]. *)
  Definition wf_fn t u (f:fn t u) : Prop := 
    match f in fn u' v' with 
      | Fn_name f t1 t2 => f < length fn_ctxt /\ fn_result f = Some (t1,t2)
      | _ => True
    end.
  
  (** A predicate for determining if a [regexp] is type-consistent with
     the given [fn_ctxt].  Note that by construction, the only things that
     can be ill-typed are the embedded [fn]s in a [Map]. *)
  Fixpoint wf_regexp t (r:regexp t) : Prop := 
    match r in regexp t' with
      | Any => True
      | Char _ => True
      | Eps => True
      | Cat _ _ r1 r2 => wf_regexp r1 /\ wf_regexp r2
      | Alt _ r1 r2 => wf_regexp r1 /\ wf_regexp r2
      | Zero _ => True
      | Star _ r => wf_regexp r
      | Map _ _ f r => wf_regexp r /\ wf_fn f
    end.
  
  (** Convert a well-formed [fn] to an actual function, using the [fn_map]. *)
  Definition apply_fn t1 t2 (f:fn t1 t2) : wf_fn f -> result_m t1 -> result_m t2.
    refine (fun t1 t2 (f:fn t1 t2) => 
      match f in fn t1' t2' return wf_fn f -> result_m t1' -> result_m t2' with
        | Fn_name f t1 t2 => fun H => _
        | Fn_const_char c => fun _ => fun _ => c
        | Fn_empty_list t => fun _ => fun _ => nil
        | Fn_cons t => fun _ => fun p => (fst p)::(snd p)
        | Fn_unit_left t => fun _ => fun x => (tt,x)
        | Fn_unit_right t => fun _ => fun x => (x,tt)
        | Fn_unit t => fun _ => fun x => tt
      end) ; simpl in * ; destruct H ; unfold fn_result in * ; 
    generalize (@lookup_fn f0 H). rewrite H0. auto.
  Defined.

  (** ** Denotational Semantics for [regexp] *)  
  (** Now we can give a semantic interpretation to the regexps under a given context. *)
  Inductive in_regexp : forall t, regexp t -> list char_p -> (result_m t) -> Prop := 
  | Any_i : forall c cs v, cs = c::nil -> v = c -> in_regexp Any cs v
  | Char_i : forall c cs v, cs = c::nil -> v = c -> in_regexp (Char c) cs v
  | Eps_i : forall cs v, cs = nil -> v = tt -> in_regexp Eps cs v
  | Alt_left_i : forall t (r1 r2:regexp t) cs (v:result_m t), 
    in_regexp r1 cs v -> in_regexp (Alt r1 r2) cs v
  | Alt_right_i : forall t (r1 r2:regexp t) cs (v:result_m t), 
    in_regexp r2 cs v -> in_regexp (Alt r1 r2) cs v
  | Cat_i : forall t1 t2 (r1:regexp t1) (r2:regexp t2) cs v cs1 cs2 v1 v2, 
    in_regexp r1 cs1 v1 -> in_regexp r2 cs2 v2 -> 
    cs = cs1 ++ cs2 -> v = (v1,v2) -> 
    in_regexp (Cat r1 r2) cs v
  | Star_eps_i : forall t (r:regexp t) cs v, 
    cs = nil -> v = nil -> in_regexp (Star r) cs v
  | Star_cat_i : forall t (r:regexp t) cs1 cs2 v1 v2 cs v,
    in_regexp (Star r) cs2 v2 -> 
    cs = cs1 ++ cs2 -> v = (v1::v2) -> 
    cs1 <> nil -> in_regexp r cs1 v1 -> 
    in_regexp (Star r) (cs1++cs2) (v1::v2)
  | Map_i : forall t1 t2 (f:fn t1 t2) (r:regexp t1) cs v1 v2 (H:wf_fn f), 
    in_regexp r cs v1 -> apply_fn f H v1 = v2 -> in_regexp (Map f r) cs v2.
  Hint Resolve Any_i Char_i Eps_i Alt_left_i Alt_right_i Cat_i Star_eps_i Star_cat_i Map_i : dfa.
  
  Notation "[[ r ]]" := (in_regexp r) (at level 0).
  
  (** Equivalence of regular expression parsers. *)  
  Definition reg_eq t (r1 r2: regexp t) : Prop := forall cs v, [[r1]] cs v <-> [[r2]] cs v.
  Infix "[=]" := reg_eq (right associativity, at level 85).

  (** Reflexivity *)  
  Lemma reg_eq_refl : forall t (r:regexp t), r [=] r.
    unfold reg_eq ; tauto.
  Qed.
  Hint Resolve reg_eq_refl : dfa.

  (** Transitivity *)
  Lemma reg_eq_trans : forall t (r1 r2 r3: regexp t), r1 [=] r2 -> r2 [=] r3 -> r1 [=] r3.
    unfold reg_eq ; mysimp ; generalize (H cs v) (H0 cs v) ; firstorder.
  Qed.

  (** Symmetry *)  
  Lemma reg_eq_sym : forall t (r1 r2: regexp t), r1 [=] r2 -> r2 [=] r1.
    unfold reg_eq ; mysimp ;  generalize (H cs v) ; firstorder.
  Qed.

  (** We define some explicit inversion principles for the [regexp] constructors
      so that we can invert them even when the arguments aren't variables.  If
      we tried to use inversion otherwise, then Coq will choke because of the
      dependencies. *)

  (** An inversion principle for [Eps]. *)
  Lemma EpsInv : forall cs v, in_regexp Eps cs v -> cs = nil /\ v = tt.
    intros cs v H; inversion H ; mysimp.
  Qed.

  (** Inversion principle for [Any]. *)
  Lemma AnyInv : forall cs v, [[Any]] cs v -> cs = v::nil.
    intros cs v H. inversion H ; s.
  Qed.

  (** Inversion principle for [Char c]. *)
  Lemma CharInv : forall c cs v, [[Char c]] cs v -> cs = c::nil /\ v = c.
    intros c cs v H ; inversion H ; s.
  Qed.

  (** Inversion principle for [Cat r1 r2].*)
  Lemma CatInv : forall t1 t2 (r1:regexp t1) (r2:regexp t2) cs v, [[Cat r1 r2]] cs v -> 
    exists cs1, exists cs2, exists v1, exists v2, 
    [[r1]] cs1 v1 /\ [[r2]] cs2 v2 /\ cs = cs1 ++ cs2 /\ v = (v1,v2).
  Proof.
    intros t1 t2 r1 r2 cs v H ; inversion H ; mysimp. repeat econstructor ; eauto.
  Qed.

  (** Inversion principle for [Alt r1 r2]. *)
  Lemma AltInv : forall t (r1 r2:regexp t) cs v, [[Alt r1 r2]] cs v -> 
    ([[r1]] cs v \/ [[r2]] cs v).
    intros t r1 r2 cs v H ; inversion H ; s.
  Qed.

  (** Inversion principle for [Star r]. *)
  Lemma StarInv : forall t (r:regexp t) cs v, [[Star r]] cs v -> 
    (cs = nil /\ v = nil) \/ 
    (exists cs1, exists v1, exists cs2, exists v2, 
      cs1 <> nil /\ [[r]] cs1 v1 /\ [[Star r]] cs2 v2 /\ cs = cs1 ++ cs2 /\ v = v1::v2).
  Proof.
    intros t r cs v H ; inversion H ; mysimp ; right.
    exists cs1 ; econstructor ; exists cs2 ; econstructor ; eauto.
  Qed.

  (** Inversion principle for [Map f r]. *)
  Lemma MapInv : forall t1 t2 (f:fn t1 t2) (r:regexp t1) cs v, [[Map f r]] cs v -> 
    exists H:wf_fn f, 
      exists v1, in_regexp r cs v1 /\ apply_fn f H v1 = v.
    intros t1 t2 f r cs v H; inversion H ; mysimp. repeat econstructor ; eauto. 
  Qed.

  (** Inversion principle for [Zero]. *)
  Lemma ZeroInv : forall t cs v, [[Zero t]] cs v -> False.
    intros t cs v H; inversion H.
  Qed.

  (** A little tactic that takes care of inversion for the [in_regexp] relation. *)
  Ltac in_inv := 
    (repeat match goal with 
      | [ H : [[Eps]] _ _ |- _ ] => generalize (EpsInv H) ; clear H
      | [ H : [[Any]] _ _ |- _ ] => generalize (AnyInv H) ; clear H
      | [ H : [[Char _]] _ _ |- _] => generalize (CharInv H) ; clear H
      | [ H : [[Cat _ _]] _ _ |- _] => generalize (CatInv H) ; clear H
      | [ H : [[Alt _ _]] _ _ |- _] => generalize (AltInv H) ; clear H
      | [ H : [[Zero _]] _ _ |- _] => contradiction (ZeroInv H)
      (* Note: we don't invert Star as this would loop in a repeat. *)
      (*| [ H : [[Star _]] _ _ |- _] => generalize (StarInv H) ; clear H*)
      | [ H : [[Map _ _]] _ _ |- _] => generalize (MapInv H) ; clear H
      | [ H : wf_fn ?f |- [[Map ?f ?r]] ?cs ?v2 ] => eapply (@Map_i _ _ f r cs _ v2 H)
      | [ H1 : ?f < length _, H2 : fn_result ?f = Some _ |- [[Map (Fn_name ?f ?t1 ?t2) ?r]] ?cs ?v] =>
        eapply (@Map_i t1 t2 (Fn_name f t1 t2) r cs _ v (conj H1 H2))
      | [ |- [[Map ?f ?r]] ?cs ?v2 ] => eapply (@Map_i _ _ f r cs _ v2 I)
      | _ => mysimp ; subst
    end) ; eauto with dfa.

  (** [Cat r Eps] is equivalent to [r] *)
  Lemma cat_eps_r : forall t (r:regexp t), (Cat r Eps) [=] (Map (Fn_unit_right t) r).
  Proof.
    unfold reg_eq ; in_inv. rewrite (app_nil_end cs). eauto with dfa.
  Qed.

  (** [Cat Eps r] is equivalent to [r] *)
  Lemma cat_eps_l : forall t (r:regexp t), (Cat Eps r) [=] (Map (Fn_unit_left t) r).
    unfold reg_eq ; in_inv. 
  Qed.
  
  (** [Cat r Zero] is equivalent to [Zero] *)
  Lemma cat_zero_r : forall t1 t2 (r:regexp t1), (Cat r (Zero t2)) [=] Zero _.
    unfold reg_eq ; in_inv. 
  Qed.

  (** [Cat Zero r] is equivalent to [Zero] *)
  Lemma cat_zero_l : forall t1 t2 (r:regexp t2), (Cat (Zero t1) r) [=] Zero _.
    unfold reg_eq ; in_inv. 
  Qed.

  (** In the simple matcher code, we could fuse OptCat and OptCat_r into
      a single definition.  Here, we broke it out to make the dependency
      a little simpler to reason about. *)

  (** Used in an optimizing constructor for [Cat]. *)
  Definition OptCat_r t1 t2 (r2:regexp t2) (r1:regexp t1) := 
    match r2 in regexp t2' return regexp (pair_t t1 t2') with
      | Zero _ => Zero _
      | Eps => Map (Fn_unit_right t1) r1
      | r2 => Cat r1 r2
    end.

  (** An optimized constructor for [Cat]. *)
  Definition OptCat t1 t2 (r1:regexp t1) (r2:regexp t2) := 
    match r1 in regexp t1' return regexp (pair_t t1' t2) with
      | Zero _ => Zero _
      | Eps => Map (Fn_unit_left t2) r2
      | r1 => OptCat_r r2 r1
    end.

  (** [OptCat r1 r2] is equivalent to [Cat r1 r2] *)
  Lemma opt_cat_r : forall t1 t2 (r1:regexp t1) (r2:regexp t2), 
    OptCat_r r2 r1 [=] Cat r1 r2.
  Proof.
    destruct r2 ; simpl ; apply reg_eq_sym ; 
      (apply reg_eq_refl || apply cat_eps_r || apply cat_zero_r).
  Qed.
  
  Lemma opt_cat : forall t1 t2 (r1:regexp t1) (r2:regexp t2), 
    OptCat r1 r2 [=] Cat r1 r2.
    destruct r1 ; intros ; simpl ; try (apply reg_eq_refl || apply opt_cat_r) ; 
      apply reg_eq_sym ; (apply cat_eps_l || apply cat_zero_l).
  Qed.

  (** [Alt r Zero] is equivalent to [r]. *)
  Lemma alt_zero_r : forall t (r:regexp t), (Alt r (Zero _)) [=] r.
    unfold reg_eq ; in_inv. 
  Qed.

  (** [Alt Zero r] is equivalent to [r]. *)
  Lemma alt_zero_l : forall t (r:regexp t), (Alt (Zero _) r) [=] r.
    unfold reg_eq ; in_inv. 
  Qed.

  (** Used in an optimizing version of [Alt]. *)
  Definition OptAlt_r t (r2:regexp t) : regexp t -> regexp t := 
    match r2 in regexp t' return regexp t' -> regexp t' with
      | Zero _ => fun r => r
      | r => fun r1 => if regexp_eq r r1 then r else Alt r1 r
    end.

  (** Optimized version of [Alt]. *)
  Definition OptAlt t (r1:regexp t) : regexp t -> regexp t := 
    match r1 in regexp t' return regexp t' -> regexp t' with
      | Zero _ => fun r => r
      | r => fun r2 => OptAlt_r r2 r
    end.

  (** [Alt r r] is equivalent to [r] *)
  Lemma alt_refl t (r:regexp t) : Alt r r [=] r.
  Proof.
    unfold reg_eq ; in_inv.
  Qed.

  (** [OptAlt r1 r2] is equivalent to [Alt r1 r2] *)
  Lemma opt_alt_r t (r1 r2:regexp t) : OptAlt_r r2 r1 [=] Alt r1 r2.
    destruct r2 ; simpl ; repeat 
    match goal with 
      | [ |- context[regexp_eq ?r1 ?r2] ] => destruct (regexp_eq r1 r2) ; subst
      | [ |- ?r [=] Alt ?r ?r ] => apply reg_eq_sym ; apply alt_refl
      | [ |- ?r [=] ?r ] => apply reg_eq_refl
      | [ |- ?r [=] Alt ?r (Zero _) ] => apply reg_eq_sym ; apply alt_zero_r
      | _ => idtac
    end.
  Qed.

  Lemma opt_alt : forall t1 (r1 r2: regexp t1), OptAlt r1 r2 [=] Alt r1 r2.
    destruct r1 ; simpl ; intros ; try (apply opt_alt_r) ; apply reg_eq_sym ;
      apply alt_zero_l.
  Qed.

  (** Optimizing version of [Map]. *)

  (* This is currently only used in the DFA construction as it's
     recursively pushing the maps in.  The goal is to ignore the
     semantic actions and always return unit if we ever return a
     value. *)
  Fixpoint MapUnit t (r:regexp t) : regexp unit_t := 
    match r with 
      | Any => Map (Fn_unit _) Any
      | Char b => Map (Fn_unit _) (Char b)
      | Eps => Eps
      | Cat t1 t2 p1 p2 => 
        match OptCat (MapUnit p1) (MapUnit p2) with 
          | Map _ _ _ r => Map (Fn_unit _) r
          | r => Map (Fn_unit _) r
        end
      | Zero t => Zero unit_t
      | Alt t p1 p2 => OptAlt (MapUnit p1) (MapUnit p2)
      | Star t p1 => Map (Fn_unit _) (Star (MapUnit p1))
      | Map t1 t2 f p => MapUnit p
    end.

  (* This isn't currently used... *)
  Definition OptMap' (t u:result) (f: fn t u) : regexp t -> regexp u := 
    match f in fn t' u' return regexp t' -> regexp u' with 
      | Fn_unit t' => @MapUnit t'
      | f1 => fun r => Map f1 r
    end.

  Definition OptMap (t u: result) (f: fn t u) (r1: regexp t) : regexp u :=
    match r1 in regexp t' return fn t' u -> regexp u with
      | Zero _ => fun _ => Zero _
      | r1 => fun f => Map f r1
    end f.

  (** [OptMap f r] is equivalent to [Map f r]. *)
  (** Used for induction over proofs of [(cs,v)] in [Star r]. *)
  Fixpoint in_unwind t (r:regexp t) n cs (v:result_m (list_t t)) : Prop := 
    match n with 
      | 0 => cs = nil /\ v = nil
      | S m => 
        exists cs1, exists cs2, 
          exists v1, exists v2, 
            cs = cs1 ++ cs2 /\ v = (v1::v2) /\ 
            cs1 <> nil /\ 
            in_regexp r cs1 v1 /\ in_unwind r m cs2 v2
    end.

  Definition coerce_reg t1 t2 (r:regexp t1) : t1 = t2 -> regexp t2.
    intros. rewrite H in r. apply r.
  Defined.

  Definition coerce_val t1 t2 (v:result_m t1) : t1 = t2 -> result_m t2.
    intros. rewrite H in v. apply v.
  Defined.

  (** If [(cs,v)] is in [Star r] then there exists some [n] such that
      [(cs,v)] is in the nth unwinding of [r].  
      This gives us an easy inner induction. *)
  Lemma star_rep : forall t (r:regexp t) cs (v:result_m t), 
    in_regexp r cs v -> 
    forall t1 (r1 : regexp t1) (H: t = list_t t1), 
      coerce_reg r H = Star r1 -> 
      exists n, in_unwind r1 n cs (coerce_val v H).
  Proof.
    unfold coerce_reg, coerce_val; induction 1 ; s ; try discriminate ; repeat
    match goal with 
      | [ H : list_t _ = list_t _ |- _] => injection H ; intros ; subst ;
        rewrite (proof_irrelevance H (eq_refl _)) in * ; simpl in *
      | [ H : Star _ = Star _ |- _ ] => injection H ; mysimp 
      | _ => idtac
    end ; [ exists 0 ; mysimp | idtac].
    destruct (IHin_regexp1 t1 r1 (eq_refl _) (eq_refl _)) ; exists (S x) ;
      repeat econstructor ; mysimp.
  Qed.

  (** Show that the optimizing constructors preserve well-formedness. *)
  Lemma wf_cat_opt : forall t1 t2 (r1:regexp t1) (r2:regexp t2), 
    wf_regexp r1 -> wf_regexp r2 -> wf_regexp (OptCat r1 r2).
  Proof.
    destruct r1 ; mysimp ; destruct r2 ; mysimp.
  Qed.
  Hint Resolve wf_cat_opt : dfa.

  Lemma wf_alt_opt : forall t (r1 r2:regexp t), 
    wf_regexp r1 -> wf_regexp r2 -> wf_regexp (OptAlt r1 r2).
  Proof.
    dependent destruction r1 ; mysimp ; dependent destruction r2 ; mysimp ; 
    match goal with 
      | [ |- context[regexp_eq ?r1 ?r2] ] => destruct (regexp_eq r1 r2) ; auto
    end ;
    mysimp.
  Qed.
  Hint Resolve wf_alt_opt : dfa.

  Lemma wf_map_opt' : forall t u (f: fn t u) (r1: regexp t),
     wf_regexp r1 -> wf_fn f -> wf_regexp (OptMap' f r1).
  Proof.
    destruct f ; mysimp. induction r1 ; mysimp ; auto with dfa. 
    assert (wf_regexp (OptCat (MapUnit r1_1) (MapUnit r1_2))). auto with dfa.
    generalize H2. generalize (OptCat (MapUnit r1_1) (MapUnit r1_2)).
    generalize (pair_t unit_t unit_t) as t. destruct r ; mysimp ; auto with dfa.
  Qed.
  Hint Resolve wf_map_opt' : dfa.

  Lemma wf_map_opt : forall t u (f: fn t u) (r1: regexp t),
     wf_regexp r1 -> wf_fn f -> wf_regexp (OptMap f r1).
  Proof.
    destruct r1 ; mysimp ; apply wf_map_opt' ; mysimp.
  Qed.
  Hint Resolve wf_map_opt : dfa.

  Lemma map_unit1 : forall t (r:regexp t) cs v, 
    [[Map (Fn_unit t) r]] cs v -> wf_regexp r -> [[MapUnit r]] cs v.
  Proof.
    induction r ; mysimp. 
    generalize (MapInv H). s. generalize (EpsInv H1). s.
    generalize (MapInv H). clear H. s.
    generalize (CatInv H). clear H. s.
    assert ([[Map (Fn_unit _) (OptCat (MapUnit r1) (MapUnit r2))]] (x1 ++ x2) tt).
    apply (@Map_i _ _ (Fn_unit _) (OptCat (MapUnit r1) (MapUnit r2)) (x1 ++ x2) (tt,tt) tt I). 
    generalize (opt_cat (MapUnit r1) (MapUnit r2) (x1 ++ x2) (tt, tt)). mysimp. apply H4.
    eapply Cat_i ; eauto. eapply IHr1 ; in_inv. eapply IHr2 ; in_inv. auto.
    generalize H3. generalize (OptCat (MapUnit r1) (MapUnit r2)).
    generalize (pair_t unit_t unit_t) as t. 
    destruct r ; auto. intros. generalize (MapInv H4). s. generalize (MapInv H5). s.
    apply (Map_i(v1:=x7) (Fn_unit t) I) ; auto.
    generalize (opt_alt (MapUnit r1) (MapUnit r2) cs v). mysimp. apply H3. clear H2 H3.
    generalize (MapInv H). s. clear H. generalize (AltInv H2). mysimp.
    apply Alt_left_i. apply IHr1 ; auto. 
    apply (@Map_i _ _ (Fn_unit _) r1 cs x0 tt I) ; auto.
    apply Alt_right_i. apply IHr2 ; auto.
    apply (@Map_i _ _ (Fn_unit _) r2 cs x0 tt I) ; auto.
    in_inv. generalize (MapInv H). clear H. s.
    apply (@Map_i _ _ (Fn_unit _) (Star (MapUnit r)) cs (List.map (fun _ => tt) x0) tt I).
    generalize (@star_rep _ _ _ _ H t r (eq_refl _) (eq_refl _)).
    mysimp. clear H. generalize cs x0 H1. clear x cs x0 H1. induction x1 ; s. in_inv.
    eapply Star_cat_i ; eauto. eapply IHr ; in_inv. auto.
    generalize (MapInv H). s. clear H. generalize (MapInv H2). s. clear H2.
    eapply IHr. eapply (@Map_i _ _ (Fn_unit _) r cs x2 tt I) ; auto. auto.
  Qed.

  Lemma map_unit2 : forall t (r:regexp t) cs v,
    [[MapUnit r]] cs v -> wf_regexp r -> [[Map (Fn_unit t) r]] cs v.
  Proof.
    induction r ; mysimp. destruct v. apply (Map_i(v1:=tt) (Fn_unit unit_t) I) ; auto.
    assert (
      wf_regexp (OptCat (MapUnit r1) (MapUnit r2)) -> 
      [[Map (Fn_unit _) (OptCat (MapUnit r1) (MapUnit r2))]] cs v).
    generalize H. generalize (OptCat (MapUnit r1) (MapUnit r2)). 
    generalize (pair_t unit_t unit_t) as t. destruct r ; mysimp.
    intros. generalize (MapInv H2). s. apply (Map_i(v1:=apply_fn f H4 x0) (Fn_unit _) I).
    apply (Map_i(v1:=x0) f H4) ; auto. auto. clear H.
    assert ([[Map (Fn_unit (pair_t unit_t unit_t)) (OptCat (MapUnit r1) (MapUnit r2))]] cs v).
    apply H2. apply wf_cat_opt. generalize (wf_map_opt' (Fn_unit _) r1). simpl.
    auto with dfa. generalize (wf_map_opt' (Fn_unit _) r2). simpl. auto with dfa. clear H2.
    generalize (MapInv H) ; clear H ; s. 
    generalize (proj1 (opt_cat (MapUnit r1) (MapUnit r2) cs x0) H) ; clear H ; mysimp.
    generalize (CatInv H). clear H ; s. 
    generalize (IHr1 _ _ H H0). clear IHr1 H. generalize (IHr2 _ _ H2 H1). clear IHr2 H2.
    mysimp. generalize (MapInv H). generalize (MapInv H2). s. clear H H2.
    apply (Map_i(v1:=(x7,x5)) (Fn_unit (pair_t t1 t2)) I) ; in_inv.
    generalize (proj1 (opt_alt (MapUnit r1) (MapUnit r2) cs v) H) ; clear H ; mysimp.
    generalize (AltInv H) ; clear H ; s.
    generalize (IHr1 _ _ H H0). mysimp. generalize (MapInv H2). s. 
    apply (Map_i(v1:=x0) (Fn_unit t) I). apply Alt_left_i ; auto. auto.
    generalize (IHr2 _ _ H H1). mysimp. generalize (MapInv H2). s.
    apply (Map_i(v1:=x0) (Fn_unit t) I). apply Alt_right_i ; auto. auto. in_inv.
    generalize (MapInv H) ; clear H ; s. 
    generalize (@star_rep _ _ _ _ H unit_t (MapUnit r) (eq_refl _) (eq_refl _)). clear H x.
    mysimp. assert (exists vs, [[Star r]] cs vs). generalize cs x0 H ; clear cs x0 H. 
    induction x ; s. exists nil. in_inv. generalize (IHr _ _ H3 H0). mysimp.
    generalize (MapInv H). s. generalize (IHx _ _ H4). s. 
    exists (x5::x3). in_inv. mysimp. apply (Map_i(v1:=x1) (Fn_unit (list_t t)) I) ; auto.
    generalize (IHr _ _ H H0). s. generalize (MapInv H2) ; s. 
    apply (Map_i(v1:=apply_fn f H1 x0) (Fn_unit u) I) ; auto.
    apply (Map_i(v1:=x0) f H1) ; auto.
  Qed.

  Lemma opt_map'1 : forall t u (f:fn t u) (r:regexp t) cs v, 
    [[Map f r]] cs v -> wf_regexp r -> [[OptMap' f r]] cs v.
  Proof.
    destruct f ; mysimp. apply map_unit1 ; auto.
  Qed.

  Lemma opt_map'2 : forall t u (f:fn t u) (r:regexp t) cs v,
    [[OptMap' f r]] cs v -> wf_regexp r -> [[Map f r]] cs v.
  Proof.
    destruct f ; mysimp. apply map_unit2 ; auto.
  Qed.

  Lemma opt_map1 : forall t u (f:fn t u) (r:regexp t) cs v, 
    [[Map f r]] cs v -> wf_regexp r -> [[OptMap f r]] cs v.
  Proof.
     destruct r ; mysimp ; try apply opt_map'1 ; mysimp. in_inv.
  Qed.

  Lemma opt_map2 : forall t u (f:fn t u) (r:regexp t) cs v,
    [[OptMap f r]] cs v -> wf_regexp r -> [[Map f r]] cs v.
  Proof.
    destruct r ; mysimp ; try apply opt_map'2 ; mysimp. in_inv.
  Qed.

  Lemma opt_map: forall (t u: result) (f: fn t u) (r1: regexp t), 
    wf_regexp r1 -> OptMap f r1 [=] Map f r1.
  Proof.
    intros ; split ; intros ; [ apply opt_map2 | apply opt_map1 ] ; auto.
  Qed.

 (** Now we define what it means for a function to be a valid
     parser.  A function [f: regexp t -> list char_p -> list (result_m t)], is a
     valid parser if, when given a [regexp] and a string of characters [s], it
     returns a list of values [[v1,...,vn]], such that { (s,vi) } is the 
     relation denoted by the regular expression. *)
  Definition is_parser (f: forall t (r:regexp t), wf_regexp r -> list char_p -> list (result_m t)) : Prop :=
    forall t (r: regexp t) (H:wf_regexp r) (cs: list char_p) (v:result_m t), 
      ([[r]] cs v -> In v (f t r H cs)) /\ (In v (f t r H cs) -> [[r]] cs v).
  (** -----------------------------------------------------*)
  (** ** Now we define the actual derivative-based parser. *)
  (** -----------------------------------------------------*)

  (** Returns a regexp denoting { (null,v) | (null,v) in r }. *)
  Fixpoint null t (r:regexp t) : regexp t := 
    match r in regexp t' return regexp t' with 
      | Any => Zero _
      | Char _ => Zero _
      | Eps => Eps
      | Zero _ => Zero _
      | Alt t r1 r2 => OptAlt (null r1) (null r2)
      | Cat t1 t2 r1 r2 => OptCat (null r1) (null r2)
      | Star t _ => OptMap (Fn_empty_list t) Eps
      | Map _ _ f r1 => OptMap f (null r1) 
    end.

  Definition OptCatDelayed t1 t2 (r1:regexp t1)(d:char_p -> regexp t2)(c:char_p) : regexp (pair_t t1 t2) :=
    match r1 in regexp t1' return regexp (pair_t t1' t2) with
      | Zero _ => Zero _
      | r1 => OptCat r1 (d c)
    end.

  Lemma OptCatDelayed_corr t1 t2 (r1:regexp t1) (d:char_p -> regexp t2) c : 
    OptCatDelayed r1 d c = OptCat r1 (d c).
  Proof.
    unfold OptCatDelayed, OptCat. auto.
  Qed.
  Hint Resolve OptCatDelayed_corr.

  (** This is the heart of the algorithm.  It returns a regexp denoting 
      { (cs,v) | (c::cs,v) in r }.  *)
  Fixpoint deriv t (r:regexp t) (c:char_p) : regexp t := 
    match r in regexp t' return regexp t' with 
      | Any => OptMap (Fn_const_char c) Eps 
      | Char c' => if char_eq c c' then OptMap (Fn_const_char c) Eps else Zero _
      | Eps => Zero _
      | Zero _ => Zero _
      | Alt t r1 r2 => OptAlt (deriv r1 c) (deriv r2 c)
      | Cat t1 t2 r1 r2 => OptAlt (OptCat (deriv r1 c) r2) (OptCatDelayed (null r1) (deriv r2) c)
      | Star t r as r' => OptMap (Fn_cons t) (OptCat (deriv r c) r')
      | Map _ _ f r1 => OptMap f (deriv r1 c)
    end.

  (** A specialized derivative for the case where we want to ignore the
      semantic actions -- note, we probably want to use this instead 
      of [null] above, because of the issue with [Star]. *)
  Fixpoint accepts_null t (r:regexp t) : bool := 
    match r with 
      | Any => false
      | Char _ => false
      | Eps => true
      | Zero _ => false
      | Alt t r1 r2 => accepts_null r1 || accepts_null r2
      | Cat t1 t2 r1 r2 => accepts_null r1 && accepts_null r2
      | Star t _ => true
      | Map _ _ f r1 => accepts_null r1
    end.

  Fixpoint unit_deriv t (r:regexp t) (c:char_p) : regexp unit_t := 
    match r with
      | Any => Eps
      | Char c' => if char_eq c c' then Eps else Zero _
      | Eps => Zero _
      | Zero _ => Zero _
      | Alt t r1 r2 => OptAlt (unit_deriv r1 c) (unit_deriv r2 c)
      | Cat t1 t2 r1 r2 => 
        match unit_deriv r1 c, accepts_null r1 with 
          | Zero _, true => unit_deriv r2 c
          | Zero _, false => Zero _ 
          | r1', false => MapUnit (OptCat r1' r2)
          | r1', true => OptAlt (MapUnit (OptCat r1' r2)) (unit_deriv r2 c)
        end
      | Star t r as r' => 
        match unit_deriv r c with 
          | Zero _ => Zero _
          | r1' => MapUnit (OptCat r1' r')
        end
      | Map _ _ f r1 => unit_deriv r1 c
    end.

  Fixpoint unit_derivs (r:regexp unit_t) (cs:list char_p) : regexp unit_t := 
    match cs with 
      | nil => r
      | c::cs' => unit_derivs (unit_deriv r c) cs'
    end.

  (** When we are done parsing using a [regexp] r, we are left with a [regexp] denoting 
     { (null,v) | exists s.(s,v) in r }.  This function computes all of the 
     values [v] in this set.  To do so, it needs to be well-formed with respect to the
     context. *)
  Definition apply_null t (r:regexp t) : wf_regexp r -> list (result_m t).
    refine (
      fix apply_null t (r:regexp t) : wf_regexp r -> list (result_m t) := 
      match r in regexp t' return wf_regexp r -> list (result_m t') with 
        | Any => fun H => nil
        | Char _ => fun H => nil
        | Zero _ => fun H => nil
        | Eps => fun H => tt::nil
        | Star _ r => fun H => nil::nil
        | Alt _ r1 r2 => fun H => (apply_null _ r1 _) ++ (apply_null _ r2 _)
        | Cat _ _ r1 r2 => 
          fun H => 
            let res1 := apply_null _ r1 _ in 
              let res2 := apply_null _ r2 _ in 
                fold_right (fun v1 a => (map (fun v2 => (v1,v2)) res2) ++ a) nil res1
        | Map _ _ f r1 => fun H => map (apply_fn f _) (apply_null _ r1 _)
      end
    ) ; mysimp.
  Defined.

  Lemma InConcatMap A B (x:A) (y:B) : 
    forall xs, In x xs -> 
      forall ys, In y ys -> 
        In (x,y) (fold_right (fun v a => (map (fun w => (v,w)) ys) ++ a) nil xs).
  Proof.
    induction xs ; intro H ; [ contradiction H | destruct H ] ; s ; 
    apply in_or_app ; [ idtac | firstorder ].
    left ; clear IHxs ; induction ys ; [ contradiction H0 | destruct H0 ; s ].
  Qed.

  (** Show that if [(nil,v)] is in [r] then [apply_null r] returns [v] as a result *)
  Lemma ApplyNull1 t (r:regexp t) cs v H :
    [[r]] cs v -> cs = nil -> In v (apply_null r H).
  Proof.
    induction 1 ; s ; try congruence ; repeat 
    match goal with 
      | [ v : prod _ _ |- _] => destruct v
      | [ H : ?x ++ ?y = nil |- _ ] => generalize (app_eq_nil _ _ H) ; clear H ; mysimp
      | [ |- In _ (fold_right _ nil _) ] => apply InConcatMap ; auto
      | [ H : wf_regexp ?r, IH : forall _ : wf_regexp ?r, nil = nil -> _ |- _ ] => 
        let l := fresh "l" in 
          generalize (IH H (eq_refl _)) ; 
            generalize (apply_null r H) as l ; induction l ; s ; left
      | [ |- apply_fn ?f ?H1 _ = apply_fn ?f ?H2 _] => 
        rewrite (proof_irrelevance H1 H2) ; auto
      | [ H : None = Some _ |- _ ] => congruence
      | [ |- In _ (_ ++ _) ] => apply in_or_app ; auto
    end.
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

  (** Show that if [apply_null r] returns [v] as a result, then [(nil,v)] is in [r] *)
  Lemma ApplyNull2 t (r:regexp t) H v : 
    In v (apply_null r H) -> [[r]] nil v.
  Proof.
    induction r ; s ; try contradiction ; auto with dfa ; 
    match goal with 
      | [ v : prod _ _, H1:forall _,_, H2:forall _,_ |- [[ Cat _ _ ]] _ _ ] => 
        destruct v ; econstructor ; 
          [ eapply IHr1 ; eapply InConcatMap1 ; eauto | 
            eapply IHr2 ; eapply InConcatMap2 ; eauto | auto | auto ]
      | [ IHr1:forall _,_, IHr2:forall _,_, H0 : In _ (_ ++ _) |- [[ Alt _ _ ]] _ _ ] => 
        generalize (in_app_or _ _ _ H0) ; clear H0 ; intro H0 ; destruct H0 ;
        [ apply Alt_left_i ; eapply IHr1 ; eauto 
        | eapply Alt_right_i ; eapply IHr2 ; eauto ] 
      | [ IHr: forall _, _, 
          H:wf_regexp ?r, H0: In _ (map _ _) |- in_regexp (Map _ _) _ _ ] =>
        let l := fresh "l" in 
          generalize (apply_null r H) (IHr H) H0 ; intro l ; induction l ; 
            clear IHr H0 ; mysimp ; try tauto ; eapply Map_i ; eauto
    end.
  Qed.

  (** Show that [null r] is well-formed if [r] is well-formed. *)
  Lemma wf_null : forall t (r:regexp t), wf_regexp r -> wf_regexp (null r).
    induction r ; mysimp ; 
      (apply wf_cat_opt || apply wf_alt_opt || apply wf_map_opt) ; auto.
  Qed.
  Hint Resolve wf_null : dfa.

  (** Show that [deriv r c] is well-formed if [r] is well-formed. *)
  Lemma wf_deriv : forall t (r:regexp t) c, wf_regexp r -> wf_regexp (deriv r c).
  Proof.
    induction r; mysimp ; 
      repeat (apply wf_cat_opt || apply wf_alt_opt || apply wf_null || apply wf_map_opt) ; 
        simpl ; auto. 
  Qed.
  Hint Resolve wf_deriv : dfa.

  Fixpoint deriv_parse' t (r:regexp t) (cs:list char_p) : regexp t := 
    match cs with 
      | nil => r
      | c::cs' => deriv_parse' (deriv r c) cs'
    end.

  Lemma wf_derivs : forall cs t (r:regexp t), wf_regexp r -> wf_regexp (deriv_parse' r cs).
    induction cs ; simpl ; intros ; auto. apply IHcs. apply wf_deriv. auto.
  Qed.
  Hint Resolve wf_derivs : dfa.

  (** Finally, the derivative-based parser simply runs through the input, calculating
      derivatives based on the characters it sees, and calls [apply_null] when it gets
      to the end of the input. *)
  Definition deriv_parse t (r:regexp t) (H:wf_regexp r) cs : list (result_m t) := 
    apply_null (deriv_parse' r cs) (wf_derivs cs r H).

  (** Tactic for helping to reason about the optimizing constructors. *)
  Ltac pv_opt := 
    match goal with 
      | [ |- in_regexp (OptAlt ?r1 ?r2) ?cs ?v ] => 
        apply (proj2 (opt_alt r1 r2 cs v))
      | [ |- in_regexp (OptCat ?r1 ?r2) ?cs ?v ] => 
        apply (proj2 (opt_cat r1 r2 cs v))
      | [ |- in_regexp (OptMap ?f ?r) ?cs ?v ] => 
        apply (@opt_map1 _ _ f r cs v) ; mysimp
      | [ H : ?x ++ ?y = nil |- _] => 
        generalize (app_eq_nil _ _ H) ; clear H ; mysimp
      | [ H : nil = ?x ++ ?y |- _] => 
        generalize (app_eq_nil _ _ (eq_sym H)) ; clear H ; mysimp
      | [ H : in_regexp (OptCat ?r1 ?r2) ?cs ?v |- _] => 
        generalize (proj1 (opt_cat r1 r2 cs v) H) ; clear H ; intro H
      | [ H : in_regexp (OptAlt ?r1 ?r2) ?cs ?v |- _] => 
        generalize (proj1 (opt_alt r1 r2 cs v) H) ; clear H ; intro H
      | [ H : wf_regexp ?r -> [[Map ?f ?r]] ?cs ?v |- _ ] => 
        assert ([[Map f r]] cs v) ; [ auto with dfa | clear H ]
      | [ H : in_regexp (OptMap ?f ?r) ?cs ?v |- _] => 
        generalize (@opt_map2 _ _ f r cs v H) ; clear H ; mysimp
      | [ v : prod (result_m _) (result_m _) |- _ ] => destruct v
      | [ H : (_,_) = (_,_) |- _ ] => injection H ; clear H ; mysimp
      | [ H1 : wf_fn ?f, H2 : wf_fn ?f |- _] => 
        rewrite (proof_irrelevance H1 H2) in * ; clear H1 ; mysimp
      | _ => auto with dfa
    end.
    
  (** [apply_null] is correct. *)
  Lemma Null1 : forall t (r:regexp t) cs v, [[r]] cs v -> cs = nil -> 
    wf_regexp r -> [[null r]] cs v.
  Proof.
    induction 1 ; s ; try congruence ; auto with dfa ; repeat pv_opt ; in_inv ; 
      try congruence.
  Qed.

  Lemma Null2 : forall t (r:regexp t) cs v, 
    [[null r]] cs v -> cs = nil -> wf_regexp r -> [[r]] cs v.
  Proof.
    induction r ; simpl ; intros ; pv_opt ; repeat (pv_opt ; in_inv).
  Qed.

  (** [deriv] is correct part 1. *)
  Lemma Deriv1 : forall t (r:regexp t) c cs v, 
    [[r]] (c::cs) v -> wf_regexp r -> [[deriv r c]] cs v.
  Proof.
    induction r ; simpl ; intros ; 
      match goal with 
        | [ H : in_regexp (Star _) _ _ |- _] => 
          generalize (StarInv H); clear H ; mysimp ; subst
        | _ => in_inv
      end ; try congruence ;
    repeat (pv_opt ; match goal with 
      | [ _ : (?c :: ?cs) = (?x ++ _) |- in_regexp (Alt _ _) ?cs _] => 
        destruct x ; s ; [eapply Alt_right_i | eapply Alt_left_i] ; pv_opt ; pv_opt
      | [ H : in_regexp ?r1 nil _ |- in_regexp (Cat (null ?r1) _) ?cs _ ] => 
        let H := fresh "H" in 
          assert (H:cs=nil++cs) ; [ auto | rewrite H ] ; 
            eapply Cat_i ; eauto with dfa ; apply Null1 ; auto
      | [ H2 : _::?cs = ?x ++ ?x1 |- _ ] => 
        destruct x ; try congruence ; simpl in H2 ; injection H2 ; s ; in_inv 
      | [ |- context[OptCatDelayed _ _ _] ] => rewrite OptCatDelayed_corr
      | _ => s ; in_inv ; eauto with dfa
    end).
  Qed.

  (** If [null r] matches [cs] returning [v], then [cs] must be empty *)
  Lemma NullNil : forall t (r:regexp t) cs v, wf_regexp r -> [[null r]] cs v -> cs = nil.
  Proof.
    induction r ; mysimp ; repeat 
    match goal with 
      | [ IHr : forall cs v, wf_regexp ?r -> in_regexp (null ?r) _ _ -> _ = _, 
          H1 : wf_regexp ?r, 
          H : in_regexp (null ?r) _ _ |- _] => 
        rewrite (IHr _ _ H1 H) ; clear IHr ; auto with dfa
      | _ => pv_opt ; in_inv
    end.
  Qed.
    
  (** [deriv] is correct part 2. *)
  Lemma Deriv2 : forall t (r:regexp t) c cs v, 
    wf_regexp r -> [[deriv r c]] cs v -> [[r]] (c::cs) v.
  Proof.
    induction r ; simpl ; intros ; repeat
    (match goal with 
       | [ H : context[char_eq ?c1 ?c2] |- _ ] => destruct (char_eq c1 c2) ; s
       | [ H2: wf_regexp ?r, H : in_regexp (null ?r) _ _ |- 
         in_regexp (Cat _ _) (?c::?x++?x0) _ ] => 
       let H1 := fresh "H" in 
         generalize (NullNil _ H2 H) ; s ; 
           assert (H1:c::x0 = nil ++ (c::x0)) ; [auto | rewrite H1] ; 
             eapply Cat_i ; eauto ; try apply Null2 ; eauto
       | [ |- in_regexp (Star _) (?c :: ?x1 ++ ?x2) _ ] => 
         let H := fresh "H" in 
           assert (H:c :: x1 ++ x2 = (c::x1) ++ x2) ; [ auto | rewrite H ] ; 
             eapply Star_cat_i ; eauto ; congruence
       | [ H : context[OptCatDelayed _ _ _] |- _ ] => rewrite OptCatDelayed_corr in H
       | _ => repeat pv_opt ; in_inv 
    end).
  Qed. 

  (** First half of correctness for [deriv_parse]. *)
  Lemma Deriv'1 cs t (r:regexp t) v : 
    wf_regexp r -> [[deriv_parse' r cs]] nil v -> [[r]] cs v.
  Proof.
    induction cs ; mysimp ; apply Deriv2 ; auto ; apply IHcs ; auto with dfa.
  Qed.

  Lemma Deriv'2 cs t (r:regexp t) v : 
    wf_regexp r -> [[r]] cs v -> [[deriv_parse' r cs]] nil v.
  Proof.
    induction cs ; mysimp ; apply IHcs ; auto with dfa ; apply Deriv1 ; auto.
  Qed.

  Lemma DerivParse1 cs t (r:regexp t) H vs : 
    deriv_parse r H cs = vs -> forall v, In v vs -> [[r]] cs v.
  Proof.
    unfold deriv_parse. intros. subst. 
    generalize (ApplyNull2 _ _ _ H1). apply Deriv'1 ; auto.
  Qed.

  (** Second half of correctness for [deriv_parse]. *)
  Lemma DerivParse2 cs t (r:regexp t) v H : 
    [[r]] cs v -> In v (deriv_parse r H cs).
  Proof.
    unfold deriv_parse ; intros ; eapply ApplyNull1 ; auto ; eapply Deriv'2 ; auto.
  Qed.

  Theorem DerivParse_is_parser : is_parser deriv_parse.
  Proof.
    unfold is_parser ; mysimp ; [apply DerivParse2 | eapply DerivParse1] ; eauto.
  Qed.

  (** * DFA Construction *)
  Section TABLE.
    (** In this section, we build a table-driven DFA recognizer for a [regexp].  It's
        crucial that the regexp has been built using [par2rec] to ensure that all of
        the semantic actions get mapped to return [tt].  What we return is:
        - A list of states which are really derivatives of the original regexp.
          The position of the regexp determins an identity (i.e., index) for the 
          state.  The initial regexp is always at position 0.  
        - A transition table as a list of list of nats.  If [T(i,j) = k], then 
          this says that in state [i], if we see an input list of characters 
          corresponding to the [token_id] [j], then we can transition to state [k].
          Obviously, [i] and [k] should be indexes of regular expressions in the
          list of [states].  Furthermore, it should be that [states(k)] is the
          derivative of [states(i)] with respect to the token_id [j].
        - An accept table as a list of booleans.  [accept(i) = true] iff 
          [states(i)] accepts the empty string.
    *)
    Record DFA := { 
      dfa_num_states : nat ; 
      dfa_states : list (regexp unit_t) ; 
      dfa_transition : list (list nat) ; 
      dfa_accepts : list bool ;
      dfa_rejects : list bool
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

    (** Our DFA states correspond to nth derivatives of a starting regexp.  We take
        the position of a regexp in the [states] list to be its name. *)
    Definition states := list (regexp unit_t).
    
    (** Find the index of a [regexp] in the list of [states]. *)
    Fixpoint find_index' (r:regexp unit_t) n (s:states) : option nat := 
      match s with 
        | nil => None
        | h::tl => if regexp_eq r h then Some n else find_index' r (1+n) tl
      end.
    Definition find_index (r:regexp unit_t) (s:states) : option nat := find_index' r 0 s.

    (** Find the index of a [regexp] in the list of [states], and if it's not
        present, add it to the end of the list. *)
    Definition find_or_add (r:regexp unit_t) (s:states) : (states * nat) := 
      match find_index r s with 
        | None => (s ++ (r::nil), length s)
        | Some i => (s, i)
      end.

    (** Generate the transition matrix row for the state corresponding to the
        regexp [r].  In general, this will add new states. *)
    Fixpoint gen_row' n (r:regexp unit_t) (s:states) token_id : (states * list nat) := 
      match n with 
        | 0 => (s, nil)
        | S n' => 
          let (s1, d) := find_or_add (unit_derivs r (token_id_to_chars token_id)) s in
          let (s2, row) := gen_row' n' r s1 (1 + token_id) in
            (s2, d::row)
      end.
    Definition gen_row (r:regexp unit_t) (s:states) : (states * list nat) := 
      gen_row' num_tokens r s 0.

    (** Build a transition table by closing off the reachable states.  The invariant
        is that we've closed the table up to the [next_state] and have generated the
        appropriate transition rows for the states in the range 0..next_state-1.
        So we first check to see if [next_state] is outside the range of states, and
        if so, we are done.  Otherwise, we generate the transition row for the
        derivative at the position [next_state], add it to the list of rows, and
        then move on to the next position in the list of states.  Note that when 
        we generate the transition row, we may end up adding new states.  

        I believe it's too difficult to show that this process eventually terminates,
        so we cheat and only run for [n] steps, returning [None] if we run out of
        steps.  Actually, if the regexp has any occurrences of [Star] that aren't
        wrapped by a [Map (Fn_unit _)] then this won't terminate in general.  But 
        the [par2rec] translation should take care of this. And of course, for the
        x86 parser, we never use [Star]. *)        
    Fixpoint build_table' n (s:states) (rows:list (list nat)) (next_state:nat) : 
      option (states * list (list nat)) := 
      match n with 
        | 0 => None
        | S n' => 
          match nth_error s next_state with 
            | None => Some (s, rows)
            | Some r => 
              let (s1, row) := gen_row r s in 
                build_table' n' s1 (rows ++ (row::nil)) (1 + next_state)
          end
      end.

    (** We start with the initial [regexp] in state 0 and then try to close off the table. *)
    Definition build_transition_table n (r:regexp unit_t) := build_table' n (r::nil) nil 0.

    Definition build_accept_table (s:states) : list bool := List.map (@accepts_null unit_t) s.

    Fixpoint always_rejects t (r:regexp t) : bool := 
      match r with 
        | Zero _ => true
        | Map _ _ _ r => always_rejects r
        | Alt _ r1 r2 => always_rejects r1 && always_rejects r2
        | Cat _ _ r1 r2 => always_rejects r1 || always_rejects r2
        | Eps => false
        | Star _ _ => false
        | Any => false
        | Char _ => false
      end.

    Definition build_rejects (s:states) := List.map (@always_rejects unit_t) s.

    Definition build_dfa n (r:regexp unit_t) : option DFA := 
      match build_transition_table n r with 
        | None => None
        | Some (states, table) => 
          Some {| dfa_num_states := length states ; 
                  dfa_states := states ; 
                  dfa_transition := table ;
                  dfa_accepts := build_accept_table states ; 
                  dfa_rejects := build_rejects states |}
      end.

    Section DFA_RECOGNIZE.
      Variable d : DFA.
      (** This loop is intended to find the shortest match (if any) for
          a sequence of tokens, given a [DFA].  It returns [(Some (n,
          ts'))] when there is a match and where [ts'] is the
          unconsumed input and n is the length of the consumed input.
          If there is no match, it returns [None].  This is just one
          example of a recognizer that can be built with the DFA. *)

      Fixpoint dfa_loop state (count: nat) (ts : list token_id) : 
        option (nat * list token_id) := 
        if nth state (dfa_accepts d) false then Some (count, ts)
        else 
          match ts with 
          | nil => None
          | t::ts' => let row := nth state (dfa_transition d) nil in 
                      let new_state := nth t row num_tokens in
                      dfa_loop new_state (S count) ts'
        end.

      Definition dfa_recognize (ts:list token_id) : option (nat * list token_id) := 
        dfa_loop 0 0 ts.
    End DFA_RECOGNIZE.


    (** In what follows, we try to give some lemmas for reasoning about the
        DFA constructed from a parser. *)
    Require Import Omega.

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
      destruct (regexp_eq r a). s. rewrite nth_error_app. auto.
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

    (** A list of states (as regexps) is well-formed if each regexp is well-formed *)
    Definition wf_states(s:states) := 
      forall i, i < length s -> 
        match nth_error s i with 
          | None => True
          | Some r => wf_regexp r
        end.

    (** Calling [find_or_add_prop r s] yields a well-formed state, ensures that
        if we lookup the returned index, we get [r], and that the state is only
        extended. *)
    Lemma find_or_add_prop : forall r s, 
      wf_regexp r -> 
      wf_states s -> 
      match find_or_add r s with 
        | (s',i) => nth_error s' i = Some r /\ (exists s1, s' = s ++ s1) /\ wf_states s'
      end.
    Proof.
      unfold find_or_add, find_index. intros. generalize (find_index'_prop r s nil). 
      simpl. intros. destruct (find_index' r 0 s).  mysimp. exists nil. 
      apply app_nil_end. split. rewrite nth_error_app. auto. split.
      exists (r::nil). auto. unfold wf_states in *. rewrite app_length. simpl. intros.
      assert (i < length s \/ i = length s).  omega. destruct H3.
      rewrite (nth_error_lt _ _ H3). apply H0 ; auto. subst. rewrite nth_error_app.
      simpl. auto.
    Qed.

    (** [MapUnit r] is always well-formed. *)
    Lemma wf_map_unit t (r:regexp t) : wf_regexp (MapUnit r).
    Proof.
      induction r ; mysimp. assert (wf_regexp (OptCat (MapUnit r1) (MapUnit r2))).
      apply wf_cat_opt ; auto. destruct (OptCat (MapUnit r1) (MapUnit r2)) ; mysimp.
      apply wf_alt_opt ; auto.
    Qed.
    Hint Resolve wf_map_unit : dfa.

    (** [unit_deriv r c] is always well-formed. *)
    Lemma wf_unit_deriv c t (r:regexp t) : wf_regexp (unit_deriv r c).
    Proof.
      Ltac wf_ud := 
        match goal with 
          | [ |- wf_regexp (MapUnit _) ] => apply wf_map_unit
          | [ |- wf_regexp (OptAlt _ _)] => apply wf_alt_opt
          | [ |- wf_regexp (OptCat _ _) ] => apply wf_cat_opt
          | [ |- _ /\ _ ] => split
          | _ => auto
        end.
      induction r ; simpl ; auto. destruct (char_eq c c0) ; simpl ; auto.
      generalize IHr1. generalize (unit_deriv r1 c). dependent destruction r ; 
      destruct (accepts_null r1) ; intros ; repeat wf_ud. repeat wf_ud.
      generalize IHr. generalize (unit_deriv r c). dependent destruction r0 ; 
      intros ; simpl ; repeat wf_ud ; simpl in *.
      assert (wf_regexp (OptCat (OptAlt (MapUnit r0_1) (MapUnit r0_2))
        (Map (Fn_unit (list_t unit_t)) (Star (MapUnit r))))).
      repeat wf_ud. simpl. repeat wf_ud.
      generalize H. clear H.
      generalize (OptCat (OptAlt (MapUnit r0_1) (MapUnit r0_2))
        (Map (Fn_unit (list_t unit_t)) (Star (MapUnit r)))).
      dependent destruction r0 ; simpl ; wf_ud. mysimp.
      assert (wf_regexp (OptCat (MapUnit r0) (Map (Fn_unit (list_t unit_t)) 
        (Star (MapUnit r))))).
      repeat (simpl ; wf_ud). generalize H ; clear H.
      generalize ((OptCat (MapUnit r0) 
        (Map (Fn_unit (list_t unit_t)) (Star (MapUnit r))))).
      dependent destruction r1 ; mysimp.
    Qed.
  
    (** [unit_derivs r cs] is always well-formed. *)
    Lemma wf_unit_derivs : forall cs r, 
      wf_regexp r -> wf_regexp (unit_derivs r cs).
    Proof.
      induction cs. auto. simpl. intros. apply IHcs. apply wf_unit_deriv. 
    Qed.

    (** This is the main loop-invariant for [gen_row'].  Given a well-formed
        regexp [r], a well-formed list of states [s], and a token number [n], 
        running [gen_row' n r s (num_tokens - n)] yields a list of states [s2]
        and transition-table [row2] such that [s2] is well-formed, the
        length of [row2] is [n], [s2] is an extension of [s], and for all
        [m], the [mth] element of [s2] is the [unit_derivs] of [r] with 
        respect to the token [m+num_tokens-n]. *)
    Lemma gen_row'_prop n r s : 
      wf_regexp r -> 
      wf_states s -> 
      n <= num_tokens -> 
      match gen_row' n r s (num_tokens - n) with 
        | (s2, row2) => 
          wf_states s2 /\ 
          length row2 = n /\ 
          (exists s1, s2 = s ++ s1) /\ 
          forall m, 
            m < n -> 
            match nth_error s2 (nth m row2 num_tokens) with 
              | Some r' => r' = unit_derivs r (token_id_to_chars (m + num_tokens - n)) 
              | None => False
            end
      end.
    Proof.
      induction n. mysimp. exists nil. apply app_nil_end. intros. assert False. omega.
      contradiction. simpl. intros.
      remember (find_or_add (unit_derivs r (token_id_to_chars (num_tokens - S n))) s).
      destruct p. remember (gen_row' n r s0 (S (num_tokens - S n))). destruct p.
      assert (wf_regexp (unit_derivs r (token_id_to_chars (num_tokens - S n)))).
      apply wf_unit_derivs ; auto.
      generalize (find_or_add_prop 
        (unit_derivs r (token_id_to_chars (num_tokens - S n))) H2 H0).
      rewrite <- Heqp.
      assert (n <= num_tokens). omega. intros. destruct H4. destruct H5.
      generalize (IHn _ s0 H H6 H3). clear IHn.
      assert (S (num_tokens - S n) = num_tokens - n). omega. rewrite <- H7.
      rewrite <- Heqp0. mysimp. subst. rewrite app_ass. exists (x0 ++ x). auto.
      destruct m. intros. simpl. subst. 
      rewrite (nth_error_ext n0 (s ++ x0) x (eq_sym H4)). auto.
      intros. assert (m < n). omega. generalize (H11 _ H13).
      assert (S m + num_tokens - S n = m + num_tokens - n). omega.
      rewrite H14. auto.
   Qed.

   (** This is the main invariant for the [build_table] routine.  Given a well-formed
       list of states [s] and a list of transition-table rows [ros], then for 
       all [i < n], [s(i)] and [r(i)] are defined, and the row [r(i)] is well-formed
       with respect to the state [s(i)]. *)
   Definition build_table_inv s rows n := 
     wf_states s /\ 
     forall i, i < n -> 
       match nth_error s i, nth_error rows i with 
         | Some r, Some row => 
           length row = num_tokens /\ 
           forall t, t < num_tokens -> 
             match nth_error s (nth t row num_tokens) with 
               | Some r' => r' = unit_derivs r (token_id_to_chars t)
               | None => False
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
     intros. assert (n < S n). auto with arith. destruct H as [_ H]. generalize (H n H0).
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
     induction n. mysimp.
     intros. generalize (build_table_inv_imp H). mysimp.
     remember (nth_error s (length rows)). destruct e.
     Focus 2. mysimp. generalize (nth_error_none _ _ Heqe). intros. omega.
     exists nil. apply app_nil_end. exists nil. apply app_nil_end.
     
     generalize (nth_error_some _ _ Heqe). intros.
     remember (gen_row r s) as p. destruct p.
     unfold gen_row in Heqp. assert (num_tokens <= num_tokens) ; auto.
     unfold build_table_inv in H. destruct H as [Y H]. assert (Z: wf_regexp r). 
     generalize (Y (length rows)). rewrite <- Heqe. auto.
     generalize (gen_row'_prop r Z Y H3). clear H3. assert (num_tokens - num_tokens = 0).
     omega. rewrite H3. rewrite <- Heqp. clear H3. mysimp.
     remember (build_table' n s0 (rows ++ l::nil) (S (length rows))) as popt.
     destruct popt ; auto. destruct p. 
     generalize (IHn s0 (rows ++ l::nil)). clear IHn.
     assert (length (rows ++ l::nil) = S (length rows)). rewrite app_length.
     simpl. omega. rewrite H7. rewrite <- Heqpopt. intros.
     
     assert (build_table_inv s0 (rows ++ l ::nil) (S (length rows))).
     Focus 2. generalize (H8 H9). s ; rewrite app_ass. exists (x ++ x1). auto.
     simpl. exists (l::x0). auto. clear H8. 

     unfold build_table_inv. split. auto. intros. 
     assert (i < length rows \/ i = length rows).
     omega. destruct H9. generalize (H i H9). subst. 
     remember (nth_error s i) as e. destruct e ; simpl ; try tauto.
     remember (nth_error rows i) as e. destruct e ; simpl ; try tauto. intros.
     rewrite (nth_error_ext i s x Heqe0).
     rewrite (nth_error_ext i rows (l::nil) Heqe1). 
     intros. destruct H5 as [H10 H5]. split. auto. clear H10. 
     intros.
     generalize (H5 _ H10). remember (nth_error s (nth t l1 (length l))) as e.
     destruct e ; simpl ; try tauto.
     rewrite (nth_error_ext (nth t l1 (length l)) s x Heqe2). auto.

     subst.
     rewrite (nth_error_ext (length rows) s x Heqe).
     rewrite (nth_error_app rows (l::nil)). simpl. mysimp.
     intros. generalize (H6 _ H5). assert (t + length l - length l = t).
     omega. rewrite H9. auto.
  Qed.

  (** This predicate captures the notion of a correct [DFA] with respect to
      an initial regexp [r].  In essence, it says that the lengths of all of
      the lists is equal to [dfa_num_states d], that [r] is at [dfa_states(0)],
      each row of the [dfa_transition] table is well-formed, that 
      [accepts(i)] holds iff the corresponding state accepts the empty string,
      and when [rejects(i)] is true, the corresponding state rejects all strings. *)
  Definition wf_dfa (r:regexp unit_t) (d:DFA) := 
    let num_states := dfa_num_states d in
    let states := dfa_states d in 
    let transition := dfa_transition d in 
    let accepts := dfa_accepts d in 
    let rejects := dfa_rejects d in 
    num_states = length states /\ 
    num_states = length transition /\ 
    num_states = length accepts /\ 
    num_states = length rejects /\ 
    nth_error states 0 = Some r /\ 
    forall i, i < num_states -> 
      let r' := nth i states (Zero _) in
      let acc := nth i accepts false in 
      let rej := nth i rejects false in 
      let row := nth i transition nil in 
        wf_regexp r' /\ 
        length row = num_tokens /\ 
        (acc = true <-> in_regexp r' nil tt) /\ 
        (rej = true -> forall s, ~in_regexp r' s tt) /\ 
        (forall t, t < num_tokens -> 
          nth t row num_tokens < num_states /\
          nth (nth t row num_tokens) states (Zero _) = 
          unit_derivs r' (token_id_to_chars t)).

    Lemma nth_error_nth A (xs:list A) n (v dummy:A) : 
      Some v = nth_error xs n -> nth n xs dummy = v.
    Proof.
      induction xs ; destruct n ; simpl in * ; unfold error, value in * ; mysimp ; 
        try congruence.
    Qed.

    (** These next few lemmas establish the correctness of [accepts_null]. *)
    Lemma accepts_null_corr1' t (r:regexp t) : 
      wf_regexp r ->
      accepts_null r = true -> 
      exists v, in_regexp r nil v.
    Proof.
      induction r ; mysimp ; try congruence. exists tt. constructor. auto. auto.
      generalize (andb_prop _ _ H0). mysimp. generalize (IHr1 H H2) (IHr2 H1 H3). mysimp.
      exists (x0,x). econstructor ; eauto. generalize (orb_prop _ _ H0). mysimp.
      generalize (IHr1 H H2). mysimp. exists x. constructor ; auto.
      generalize (IHr2 H1 H2). mysimp. exists x. apply Alt_right_i. auto.
      exists nil. constructor ; auto. generalize (IHr H H0). mysimp.
      exists (apply_fn f H1 x). econstructor ; auto. auto.
    Qed.

    Lemma accepts_null_corr1 (r:regexp unit_t) : 
      wf_regexp r -> accepts_null r = true -> in_regexp r nil tt.
    Proof.
      intros. generalize (accepts_null_corr1' _ H H0). mysimp. destruct x. auto.
    Qed.

    Lemma accepts_null_corr2' t (r:regexp t) v : 
      in_regexp r nil v -> 
      wf_regexp r -> 
      accepts_null r = true.
    Proof.
      intros t r v H. dependent induction H ; s ; try congruence.
      generalize (IHin_regexp H0). unfold orb. intros. rewrite H2. auto.
      unfold orb. rewrite (IHin_regexp H1). destruct (accepts_null r1) ; auto.
      destruct cs1 ; simpl in * ; try congruence. subst.
      unfold andb. rewrite IHin_regexp1 ; auto.
    Qed.

    Lemma accepts_null_corr2 (r:regexp unit_t) : 
      wf_regexp r -> in_regexp r nil tt -> accepts_null r = true.
    Proof.
      intros. apply (@accepts_null_corr2' unit_t r tt H0 H).
    Qed.

    (** [accepts_null] is correct. *)
    Lemma accepts_null_corr (r:regexp unit_t) : 
      wf_regexp r -> (accepts_null r = true <-> in_regexp r nil tt).
    Proof.
      intros. split. apply accepts_null_corr1 ; auto. apply accepts_null_corr2 ; auto.
    Qed.

    (** [always_rejects] is correct. *)
    Lemma always_rejects_corr t (r:regexp t) : 
      always_rejects r = true -> forall s v, ~ in_regexp r s v.
    Proof.
      induction r ; mysimp ; try congruence.
      generalize (orb_prop _ _ H). mysimp. generalize (IHr1 H0). intros.
      intro. generalize (CatInv H2). mysimp. subst. apply (H1 x x1). auto.
      generalize (IHr2 H0). intros. intro. generalize (CatInv H2).
      mysimp. s. apply (H1 x0 x2) ; auto.
      generalize (andb_prop _ _ H). mysimp. intro. generalize (AltInv H2). mysimp.
      eapply IHr1 ; eauto. eapply IHr2 ; eauto. intro. apply (ZeroInv H0).
      intro. generalize (MapInv H0). mysimp. eapply IHr ; eauto.
    Qed.

    (** [build_dfa] is (partially) correct.  Note that we do not show that there's
        always an [n], hence the partiality. *)
    Lemma build_dfa_wf (r:regexp unit_t) (d:DFA) :
      wf_regexp r -> forall n, build_dfa n r = Some d -> wf_dfa r d.
    Proof.
      unfold build_dfa, build_transition_table. intros.
      assert (build_table_inv (r::nil) nil 0). 
      unfold build_table_inv. split. unfold wf_states. simpl. intros.
      destruct i. simpl. auto. assert False. omega. contradiction.
      intros i H1. assert False. omega.
      contradiction. generalize (build_table'_prop n H1). simpl. intros. 
      destruct (build_table' n (r::nil) nil 0) ; try congruence. 
      destruct p as [s' rows']. injection H0. intros. subst. clear H0.
      unfold wf_dfa. simpl. mysimp. unfold build_accept_table.
      rewrite map_length. auto. unfold build_rejects. rewrite map_length. auto.
      rewrite H3. unfold value. auto. intros. rewrite <- H0 in H5. 
      unfold build_table_inv in H2. destruct H2 as [Y H2].
      generalize (H2 _ H5). clear H2.
      intros. remember (nth_error s' i) as e. destruct e ; try contradiction.
      remember (nth_error rows' i) as e. destruct e ; try contradiction. destruct H2.
      split. assert (i < length s'). omega. generalize (Y i H7). 
      rewrite <- Heqe. intros.  rewrite (nth_error_nth s' i (Zero _) Heqe). auto. split.
      rewrite (nth_error_nth rows' i nil Heqe0). auto. 
      rewrite (nth_error_nth s' i (Zero _) Heqe).
      unfold build_accept_table. unfold build_rejects.
      rewrite (map_nth (@accepts_null _) s' (Zero _)).
      rewrite (map_nth (@always_rejects _) s' Eps).
      rewrite (nth_error_nth s' i (Zero _) Heqe).
      rewrite (nth_error_nth s' i Eps Heqe). split.
      intros. apply accepts_null_corr ; auto. assert (i < length s'). omega.
      generalize (Y i H7). rewrite <- Heqe. auto. split.
      intros. apply always_rejects_corr. auto. intros. subst.
      rewrite (nth_error_nth x i nil Heqe0). rewrite H2 in *.
      generalize (H6 _ H7). 
      remember (nth_error (r::x0) (nth t l num_tokens)). destruct e ; try tauto. intros.
      subst. rewrite (nth_error_nth (r::x0) (nth t l (length l)) (Zero _) Heqe1). 
      split ; auto. generalize Heqe1. clear Heqe1.  
      generalize (nth t l (length l)) (r::x0). induction n0 ; destruct l0 ; simpl ; 
      unfold error, value ; intros ; try congruence. omega. generalize (IHn0 _ Heqe1).
      intros. omega.
   Qed.

  (** ** Building a recognizer which ignores semantic actions. *)
  Fixpoint par2rec t (p:parser t) : regexp unit_t := 
    match p with
      | Any_p => Map (Fn_unit _) Any
      | Char_p b => Map (Fn_unit _) (Char b)
      | Eps_p => Eps
      | Cat_p t1 t2 p1 p2 => Map (Fn_unit _) (OptCat (par2rec p1) (par2rec p2))
      | Zero_p t => Zero unit_t
      | Alt_p t p1 p2 => OptAlt (par2rec p1) (par2rec p2)
      | Star_p t p1 => Map (Fn_unit _) (Star (par2rec p1))
      | Map_p t1 t2 f p => par2rec p
    end.

  (** Recognizer is well-formed *)
  Lemma par2rec_wf t (p:parser t) : wf_regexp (par2rec p).
  Proof.
    induction p ; mysimp. apply wf_cat_opt ; auto. apply wf_alt_opt ; auto.
  Qed.

  (** The translation from parsers to regexps which throws away the maps is correct. *)
  Lemma par2rec_corr1 t (p:parser t) cs v : 
    in_parser p cs v -> in_regexp (par2rec p) cs tt.
  Proof.
    induction 1 ; s ; repeat
    match goal with 
      | [ |- in_regexp (OptAlt ?r1 ?r2) ?cs ?v ] => 
        apply (proj2 (opt_alt r1 r2 cs v))
      | [ |- in_regexp (OptCat ?r1 ?r2) ?cs ?v ] => 
        apply (proj2 (opt_cat r1 r2 cs v))
      | [ IH1 : in_regexp (par2rec ?p) ?cs1 _, 
          IH2 : in_regexp (Map (Fn_unit _) (Star (par2rec ?p))) ?cs2 _,
          H : _ <> nil |- in_regexp (Map _ (Star _)) _ _ ] => 
        generalize (MapInv IH2) ; mysimp ;
        match goal with 
        | [ H : in_regexp (Star (par2rec _)) _ ?x0 |- _] => 
          apply (@Map_i _ _ (Fn_unit (list_t unit_t)) (Star (par2rec p)) (cs1 ++ cs2) 
            (tt::x0) tt I) ; try eapply Star_cat_i ; eauto ; simpl ; auto 
        end
      | [ |- in_regexp (Map (Fn_unit ?t1) ?r) ?cs ?v2 ] => 
        eapply (@Map_i _ _ (Fn_unit t1) r cs _ v2 I) 
      | [ H : in_regexp (par2rec ?p) _ _ |- in_regexp (Alt _ (par2rec ?p)) _ _ ] => 
        eapply Alt_right_i ; eauto
      | _ => in_inv ; econstructor ; eauto 
    end.
  Qed.    

  Lemma par2rec_corr2 t (p:parser t) cs : 
    in_regexp (par2rec p) cs tt -> exists v, in_parser p cs v.
  Proof.
    induction p ; mysimp ; repeat (
    match goal with 
      | [ H : in_regexp (OptCat ?r1 ?r2) ?cs ?v |- _ ] => 
        generalize (proj1 (opt_cat r1 r2 cs v) H) ; clear H
      | [ H : in_regexp (OptAlt ?r1 ?r2) ?cs ?v |- _ ] => 
        generalize (proj1 (opt_alt r1 r2 cs v) H) ; clear H
      | [ H : in_regexp (Map _ _) _ _ |- _ ] => generalize (MapInv H) ; clear H 
      | [ H : in_regexp (Alt _ _) _ _ |- _ ] => generalize (AltInv H) ; clear H 
      | [ H : in_regexp (Cat _ _) _ _ |- _ ] => generalize (CatInv H) ; clear H 
      | [ H : in_regexp (Zero _) _ _ |- _ ] => 
        generalize (ZeroInv H) ; mysimp ; contradiction
      | [ H : in_regexp (Char _) _ _ |- _ ] => generalize (CharInv H) ; clear H 
      | [ H : in_regexp Any _ _ |- _ ] => generalize (AnyInv H) ; clear H 
      | [ H : in_regexp Eps _ _ |- _ ] => generalize (EpsInv H) ; clear H
      | [ |- exists _:unit, _ ] => exists tt
      | [ v : unit |- _ ] => destruct v
      | [ IHp1 : forall _, in_regexp (par2rec ?p) _ _ -> _, 
          H1 : in_regexp (par2rec ?p) _ _ |- _] => generalize (IHp1 _ H1) ; clear IHp1
      | _ => eauto
    end ; s) ; try ((econstructor ; econstructor ; eauto ; fail) || 
                    (econstructor ; eapply Alt_right_pi ; eauto)).
    generalize (star_rep(r1:=(par2rec p)) H (eq_refl _) (eq_refl _)). clear H.
    mysimp. generalize cs x0 H. clear cs x0 H. induction x1 ; s.
    exists nil ; constructor ; auto. destruct x4. generalize (IHp _ H3).
    generalize (IHx1 _ _ H4). mysimp. econstructor ; eapply Star_cat_pi ; eauto.
  Qed.

  (** A simple recognizer -- given a parser [p] and string [cs], returns a 
     proof that either either [cs] matches the grammar in [p] (i.e., there is
     some semantic value that [cs] would parse into) or else there is no 
     match (i.e., there is no value that it can parse into.) *)
  Definition recognize t (p:parser t) cs : 
    {exists v, in_parser p cs v} + {forall v, ~ in_parser p cs v}.
    intros.
    remember (deriv_parse (par2rec p) (par2rec_wf p) cs).
    destruct l ; [ right ; intros v H | left ; intros].
    generalize (par2rec_corr1 H). intro. generalize (DerivParse2 (par2rec_wf p) H0).
    rewrite <- Heql. simpl. auto. destruct r.
    generalize (DerivParse1 cs (par2rec p) (par2rec_wf p) (eq_sym Heql)). 
    mysimp. assert (in_regexp (par2rec p) cs tt). apply H. left ; auto.
    apply (par2rec_corr2 _ H0).
  Defined.

   Definition flat_map A B (f:A->list B) (xs:list A) : list B := 
     fold_right (fun v a => (f v) ++ a) nil xs.

   (** This is a simple function which runs a DFA on an entire string, returning
       true if the DFA accepts the string, and false otherwise.  In what follows,
       we prove that [run_dfa] is correct... *)
   Fixpoint run_dfa (d:DFA) (state:nat) (ts:list token_id) : bool := 
     match ts with 
       | nil => nth state (dfa_accepts d) false
       | t::ts' => run_dfa d (nth t (nth state (dfa_transition d) nil) num_tokens) ts'
     end.

   (** A key part of the reasoning is showing that [unit_deriv] is correct.  But
       this turns out to be complicated because of the type dependencies, as well
       as the optimizations that we're doing.  So I've broken it up into a number
       of smaller lemmas. *)
   Lemma unit_deriv_cat0 : forall c t1 t2 (r1:regexp t1) (r2:regexp t2), 
     wf_regexp r1 -> wf_regexp r2 -> 
     accepts_null r1 = true -> 
     (forall cs, [[unit_deriv r1 c]] cs tt -> (exists v, [[r1]] (c::cs) v)) -> 
     (forall cs, [[unit_deriv r2 c]] cs tt -> (exists v, [[r2]] (c::cs) v)) -> 
     forall cs, [[OptAlt (MapUnit (OptCat (unit_deriv r1 c) r2)) (unit_deriv r2 c)]] cs tt -> 
       exists v, [[Cat r1 r2]] (c::cs) v.
   Proof.
     intros. pv_opt. in_inv. assert (wf_regexp (OptCat (unit_deriv r1 c) r2)). 
     apply wf_cat_opt. apply wf_unit_deriv. auto.
     generalize (map_unit2 _ H4 H5).  mysimp. in_inv. pv_opt. in_inv. destruct x3.
     generalize (H2 _ H6). mysimp. exists (x0,x4). in_inv.
     generalize (accepts_null_corr1' _ H H1). mysimp. generalize (H3 _ H4). mysimp. 
     exists (x,x0). eapply Cat_i. eapply H5. eapply H6. auto. auto.
   Qed.
   
   Lemma unit_deriv_cat1 : forall c t1 t2 (r1:regexp t1) (r2:regexp t2), 
     wf_regexp r1 -> wf_regexp r2 -> 
     accepts_null r1 = true -> 
     (forall cs, [[unit_deriv r1 c]] cs tt -> exists v, [[r1]] (c::cs) v) -> 
     (forall cs, [[unit_deriv r2 c]] cs tt -> exists v, [[r2]] (c::cs) v) -> 
     unit_deriv r1 c = Zero _ -> 
     forall cs, [[unit_deriv r2 c]] cs tt -> exists v, [[Cat r1 r2]] (c::cs) v.
   Proof.
     intros. generalize (accepts_null_corr1' _ H H1). mysimp.
     generalize (H3 _ H5). mysimp. exists (x, x0). in_inv.
   Qed.
   
   Lemma unit_deriv_cat2 : forall c t1 t2 (r1:regexp t1) (r2:regexp t2), 
     wf_regexp r1 -> wf_regexp r2 -> 
     accepts_null r1 = false -> 
     (forall cs, [[unit_deriv r1 c]] cs tt -> exists v, [[r1]] (c::cs) v) -> 
     (forall cs, [[unit_deriv r2 c]] cs tt -> exists v, [[r2]] (c::cs) v) -> 
     forall cs, [[MapUnit (OptCat (unit_deriv r1 c) r2)]] cs tt -> 
       exists v, [[Cat r1 r2]] (c::cs) v.
   Proof.
     mysimp. assert (wf_regexp (OptCat (unit_deriv r1 c) r2)). apply wf_cat_opt.
     apply wf_unit_deriv. auto. generalize (map_unit2 _ H4 H5). mysimp. in_inv.
     pv_opt. in_inv. destruct x3. generalize (H2 _ H6). mysimp.
     exists (x0,x4). in_inv.
   Qed.
   
   Lemma unit_deriv_cat : forall c t1 t2 (r1:regexp t1) (r2:regexp t2), 
     wf_regexp r1 -> wf_regexp r2 -> 
     (forall cs, [[unit_deriv r1 c]] cs tt -> exists v, [[r1]] (c::cs) v) -> 
     (forall cs, [[unit_deriv r2 c]] cs tt -> exists v, [[r2]] (c::cs) v) -> 
     forall cs, 
       [[match unit_deriv r1 c, accepts_null r1 with 
           | Zero _, true => unit_deriv r2 c
           | Zero _, false => Zero _
           | r1', false => MapUnit (OptCat r1' r2)
           | r1', true => OptAlt (MapUnit (OptCat r1' r2)) (unit_deriv r2 c)
         end]] cs tt -> 
       exists v, [[Cat r1 r2]] (c::cs) v.
   Proof.
     intros c t1 t2 r1. remember (unit_deriv r1 c). generalize Heqr. clear Heqr.
     remember (accepts_null r1) as b. generalize (eq_sym Heqb). clear Heqb.
     dependent destruction r ; destruct b ; intros ; (try (in_inv ; fail)) ; 
       rewrite Heqr in * ; 
         try (apply unit_deriv_cat0 ; auto ; fail) ; 
           try (apply unit_deriv_cat2 ; auto ; fail) ; 
             try (apply unit_deriv_cat1 ; auto ; fail).
   Qed.

   Lemma unit_deriv_star' : forall t (r:regexp t) cs vs,
     [[Star (MapUnit r)]] cs vs -> wf_regexp r -> exists vs', [[Star r]] cs vs'.
   Proof.
     intros t r cs vs H. dependent induction H ; s. exists nil. econstructor ; eauto.
     generalize (map_unit2 _ H3 H4). intros. in_inv. clear H3.
     generalize (IHin_regexp1 t r v2 (eq_refl _) (JMeq_refl _) (JMeq_refl _) H4).
     mysimp. exists (x0::x1). in_inv.
   Qed.

   Lemma unit_deriv_star0 : forall c t (r:regexp t), 
     wf_regexp r -> 
     (forall cs, [[unit_deriv r c]] cs tt -> exists v, [[r]] (c::cs) v) -> 
     forall cs, 
       [[ MapUnit (OptCat (unit_deriv r c) (Star r)) ]] cs tt -> 
       exists v, [[ Star r ]] (c::cs) v.
   Proof.
     intros. assert (wf_regexp (OptCat (unit_deriv r c) (Star r))). 
     apply wf_cat_opt. apply wf_unit_deriv. auto with dfa.
     generalize (map_unit2 _ H1 H2). clear H1. mysimp. in_inv. pv_opt.
     in_inv. destruct x3. generalize (H0 _ H1). mysimp. 
     exists (x0::x4). assert (c::x1++x2 = (c::x1) ++ x2). auto. rewrite H6.
     eapply Star_cat_i ; eauto. congruence.
   Qed.

   Lemma unit_deriv_star : forall c t (r:regexp t), 
     wf_regexp r -> 
     (forall cs, [[unit_deriv r c]] cs tt -> exists v, [[r]] (c::cs) v) -> 
     forall cs, 
       [[ match unit_deriv r c with 
            | Zero _ => Zero _
            | r1' => MapUnit (OptCat r1' (Star r))
          end ]] cs tt -> exists v, [[ Star r ]] (c::cs) v.
   Proof.
     intros c t r. remember (unit_deriv r c) as rc. generalize Heqrc. clear Heqrc.
     dependent destruction rc ; intros ; rewrite Heqrc in * ; try 
     (apply unit_deriv_star0 ; auto). rewrite <- Heqrc in *. in_inv.
   Qed.

   Lemma StarMapUnit : forall t (r:regexp t) cs vs, 
     [[ Star r ]] cs vs -> 
     wf_regexp r -> 
     [[ Star (MapUnit r) ]] cs (map (fun _ => tt) vs).
   Proof.
     intros t r cs vs H. dependent induction H. s. eapply Star_eps_i ; auto. subst.
     intros.
     eapply (@Star_cat_i unit_t (MapUnit r) cs1 cs2 tt (map (fun _ => tt) v2) (cs1++cs2));
       auto. apply map_unit1 ; auto. 
     apply (@Map_i _ _ (Fn_unit _) r cs1 v1 tt I) ; auto.
   Qed.

   (** So this is a crucial result:  it says that if [unit_deriv r c] returns a 
       regexp that matches [cs] and [tt], then there is some [v] such that 
       [r] matches [c::cs] and [v]. *)
   Lemma unit_deriv_corr1 t (r:regexp t) c cs : 
     in_regexp (unit_deriv r c) cs tt -> wf_regexp r -> exists v, in_regexp r (c::cs) v.
   Proof.
     induction r ; s ; in_inv ; pv_opt. destruct (char_eq c0 c) ; s ; in_inv. 
     apply unit_deriv_cat ; auto.
     in_inv. generalize (IHr1 _ _ H H0). mysimp. exists x. in_inv.
     generalize (IHr2 _ _ H H1). mysimp. exists x. in_inv.
     apply unit_deriv_star ; auto. generalize (IHr _ _ H H0). mysimp.
     exists (apply_fn f H1 x). econstructor ; eauto.
   Qed.

   (** This lifts the [unit_deriv_corr1] to strings. *)
   Lemma unit_derivs_corr1 cs1 (r:regexp unit_t) cs2 : 
     in_regexp (unit_derivs r cs1) cs2 tt -> wf_regexp r -> 
     exists v, in_regexp r (cs1 ++ cs2) v.
   Proof.
     induction cs1 ; mysimp. exists tt. auto.  
     generalize (IHcs1 (unit_deriv r a) cs2 H (wf_unit_deriv a r)). mysimp.
     destruct x. generalize (unit_deriv_corr1 r a H1 H0). auto.
   Qed.
     
   (** This lemma proves the other half of the correctness of [unit_deriv]:  If
       [r] matches [c::cs] and [v], then [unit_deriv r c] matchs [cs] and [tt]. 
       This proof needs to be abstracted and cleaned up a lot... *)
   Lemma unit_deriv_corr2 t (r:regexp t) c cs v : 
     in_regexp r (c::cs) v -> wf_regexp r -> in_regexp (unit_deriv r c) cs tt.
   Proof.
     intros t r c cs v H. dependent induction H ; s ; auto with dfa ; try congruence ; 
     pv_opt. apply Alt_left_i. eapply IHin_regexp ; eauto. apply Alt_right_i.
     eapply IHin_regexp ; eauto. destruct cs1. s.
     rewrite (accepts_null_corr2' H H3). generalize (IHin_regexp2 c cs (eq_refl _) H4).
     clear IHin_regexp2 IHin_regexp1. intros. generalize (unit_deriv r1 c) as r.
     dependent destruction r ; pv_opt ; try (apply Alt_right_i ; auto).
     simpl in H1. injection H1. s. clear H1 H2. generalize (IHin_regexp1 c0 cs1
     (eq_refl _) H3). clear IHin_regexp1. remember (unit_deriv r1 c0) as r.
     generalize Heqr ; clear Heqr. destruct (accepts_null r1). 
     dependent destruction r ; s ; in_inv ; pv_opt. 
     apply Alt_left_i. eapply map_unit1 ; auto with dfa.
     apply (@Map_i _ _ (Fn_unit t2) r2 cs2 v2 tt I H0 (eq_refl _)).
     apply Alt_left_i. eapply map_unit1 ; auto.
     apply (@Map_i _ _ (Fn_unit _) (OptCat (Alt r3 r4) r2) (cs1++cs2) (tt,v2) tt I).
     pv_opt. eapply Cat_i. eapply Alt_left_i. eauto. eauto. auto. auto. auto.
     apply (wf_cat_opt (Alt r3 r4) r2). rewrite Heqr. apply wf_unit_deriv. auto.
     apply Alt_left_i. eapply map_unit1 ; auto.
     apply (@Map_i _ _ (Fn_unit _) (OptCat (Alt r3 r4) r2) (cs1++cs2) (tt,v2) tt I) ; auto.
     pv_opt. eapply Cat_i. eapply Alt_right_i. eauto. eauto. auto. auto.
     apply (wf_cat_opt (Alt r3 r4) r2). rewrite Heqr. apply wf_unit_deriv. auto.
     apply Alt_left_i. eapply map_unit1 ; auto. 
     apply (@Map_i _ _ (Fn_unit _) (OptCat (Map f r) r2) (cs1++cs2) (tt,v2) tt I).
     pv_opt. eapply Cat_i ; eauto. apply (@Map_i _ _ f r cs1 x0 tt x H1 H2). auto.
     apply (wf_cat_opt (Map f r) r2). rewrite Heqr. apply wf_unit_deriv. auto.
     dependent destruction r ; s ; in_inv ; apply map_unit1 ; auto.
     apply (@Map_i _ _ (Fn_unit _) r2 cs2 v2 tt I H0 (eq_refl _)).
     apply (@Map_i _ _ (Fn_unit _) (OptCat (Alt r3 r4) r2) (cs1++cs2) (tt,v2) tt I).
     pv_opt. eapply Cat_i. eapply Alt_left_i ; eauto. eauto. auto. auto. auto.
     apply (wf_cat_opt (Alt r3 r4) r2). rewrite Heqr. apply wf_unit_deriv. auto.
     apply (@Map_i _ _ (Fn_unit _) (OptCat (Alt r3 r4) r2) (cs1++cs2) (tt,v2) tt I).
     pv_opt. eapply Cat_i. eapply Alt_right_i ; eauto. eauto. auto. auto. auto.
     apply (wf_cat_opt (Alt r3 r4) r2). rewrite Heqr. apply wf_unit_deriv. auto.
     apply (@Map_i _ _ (Fn_unit _) (OptCat (Map f r) r2) (cs1++cs2) (tt,v2) tt I).
     pv_opt. eapply Cat_i ; eauto. eapply (@Map_i _ _ f r cs1 x0 tt x H1 H2). auto.
     apply (wf_cat_opt (Map f r) r2) ; auto. rewrite Heqr. apply wf_unit_deriv.
     destruct cs1 ; try congruence. simpl in x ; injection x ; s.
     generalize (IHin_regexp2 c cs1 (eq_refl _) H4). clear IHin_regexp2. 
     clear H0 H1 H2. assert (forall cs, cs2 = c::cs -> [[unit_deriv (Star r) c]] cs tt).
     intros. apply IHin_regexp1. auto. auto. clear IHin_regexp1. 
     remember (unit_deriv r c) as rb. generalize Heqrb. clear Heqrb.
     dependent destruction rb ; intros. generalize (EpsInv H1). intros. destruct H2.
     subst. clear H5. clear H1.
     generalize (StarMapUnit H H4). intros.
     apply (@Map_i _ _ (Fn_unit _) (Star (MapUnit r)) cs2 (map (fun _ => tt) v2) tt I) ; 
       auto.
     assert ([[MapUnit (OptCat (Alt rb1 rb2) (Star r))]] (cs1 ++ cs2) tt) ; auto.
     eapply map_unit1. eapply (@Map_i _ _ (Fn_unit _) (OptCat (Alt rb1 rb2) (Star r))
     (cs1 ++ cs2) (tt,v2) tt I) ; auto. pv_opt ; auto. eapply Cat_i ; auto. auto. auto.
     apply wf_cat_opt. rewrite Heqrb. apply wf_unit_deriv. auto. 
     in_inv.
     assert ([[MapUnit (Cat (Map f rb) (Star r))]] (cs1++cs2) tt) ; auto.
     eapply map_unit1. 
     apply (@Map_i _ _ (Fn_unit _) (Cat (Map f rb) (Star r)) (cs1++cs2) (tt,v2) tt I) ; 
       auto.
     eapply Cat_i ; eauto. rewrite Heqrb. split. apply wf_unit_deriv. auto.
   Qed.

   (** Lifts [unit_deriv_corr2] to strings. *)
   Lemma unit_derivs_corr2 cs (r:regexp unit_t) : 
     wf_regexp r -> [[r]] cs tt -> [[unit_derivs r cs]] nil tt.
   Proof.
     induction cs. auto. simpl. intros. apply IHcs. apply wf_unit_deriv.
     eapply unit_deriv_corr2. eauto. auto.
   Qed.

   Definition list_all(A:Type)(P:A->Prop) : list A -> Prop := 
     fold_right (fun x a => P x /\ a) True.

   Lemma lt_nth_error : forall A (xs:list A) n dummy v, 
     n < length xs -> nth n xs dummy = v -> nth_error xs n = Some v.
   Proof.
     induction xs ; destruct n ; mysimp ; try (assert False ; [ omega | contradiction] ); 
       unfold error, value in * ; s. apply (IHxs n dummy). omega. auto.
   Qed.

   Lemma flat_map_app A B (f:A->list B) (ts1 ts2:list A) : 
     flat_map f (ts1 ++ ts2) = (flat_map f ts1) ++ (flat_map f ts2).
   Proof.
     induction ts1 ; mysimp. rewrite app_ass. rewrite IHts1. auto.
   Qed.
   
   Lemma unit_derivs_flat_map r ts1 ts2 : 
     unit_derivs r (flat_map token_id_to_chars (ts1 ++ ts2)) = 
     unit_derivs (unit_derivs r (flat_map token_id_to_chars ts1)) 
     (flat_map token_id_to_chars ts2).
   Proof.
     intros. rewrite flat_map_app. generalize (flat_map token_id_to_chars ts1) r
     (flat_map token_id_to_chars ts2). induction l ; mysimp. 
   Qed.

   (** This lemma tells us that if we start with a parser [p], build a [DFA],
       and then run the [DFA] on a list of tokens, then we get [true] iff
       the parser would've accepted the string and produced a value.  *)
   Lemma dfa_corr' : forall t (p:parser t) n (d:DFA), 
     build_dfa n (par2rec p) = Some d -> 
     forall ts2 ts1 state, 
       nth_error (dfa_states d) state = 
       Some (unit_derivs (par2rec p) (flat_map token_id_to_chars ts1)) -> 
       list_all (fun t => t < num_tokens) ts2 ->
       if run_dfa d state ts2 then
         exists v, in_parser p (flat_map token_id_to_chars (ts1 ++ ts2)) v
       else 
         forall v, ~ in_parser p (flat_map token_id_to_chars (ts1 ++ ts2)) v.
   Proof.
     intros t p n d H. assert (wf_dfa (par2rec p) d). eapply build_dfa_wf.
     eapply par2rec_wf. eauto. unfold wf_dfa in H0. induction ts2 ; mysimp.
     assert (state < dfa_num_states d). rewrite H0. generalize H1. 
     generalize (unit_derivs (par2rec p) (flat_map token_id_to_chars ts1)).
     generalize (dfa_states d) state. 
     induction l ; destruct state0 ;  mysimp ; unfold error, value in * ; try congruence. 
     subst. omega. subst. generalize (IHl _ _ H8). intros. omega. 
     generalize (H7 _ H8). mysimp. remember (nth state (dfa_accepts d) false) as e.
     destruct e. generalize (H11 (eq_refl _)).
     rewrite (nth_error_nth (dfa_states d) state _ (eq_sym H1)). intros.
     generalize (unit_derivs_corr1 _ _ H15 (par2rec_wf _)).
     rewrite <- app_nil_end. mysimp. destruct x. apply (par2rec_corr2 p H16).
     unfold not. intros. assert (false = true).
     apply H14. rewrite (nth_error_nth (dfa_states d) state _ (eq_sym H1)).
     generalize (@par2rec_corr1 t p (flat_map token_id_to_chars ts1) v H15). intro.
     apply unit_derivs_corr2 ; auto. apply par2rec_wf. congruence.
     
     generalize (IHts2 (ts1 ++ a::nil) 
       (nth a (nth state (dfa_transition d) nil) num_tokens)). 
     rewrite app_ass. simpl. intros. apply H9 ; auto. clear H9 IHts2.
     assert (state < dfa_num_states d). rewrite H0. generalize H1.
     generalize (unit_derivs (par2rec p) (flat_map token_id_to_chars ts1)).
     generalize (dfa_states d) state. induction l ; destruct state0 ; mysimp ; 
     unfold error, value in * ; try congruence; try omega. 
     generalize (IHl _ _ H9). intros. omega.
     generalize (H8 _ H9) ; mysimp. generalize (H14 _ H2). mysimp.
     rewrite unit_derivs_flat_map. simpl. rewrite <- app_nil_end.
     generalize (H14 _ H2). mysimp. rewrite H0 in H18.
     apply (lt_nth_error (dfa_states d) (Zero unit_t) H18). rewrite H19.
     rewrite (nth_error_nth _ _ (Zero unit_t) (eq_sym H1)). auto.
  Qed.

  (** Here is the key correctness property for the DFAs. *)
  Lemma dfa_corr t (p:parser t) n (d:DFA) :
    build_dfa n (par2rec p) = Some d -> 
    forall ts, 
      list_all (fun t => t < num_tokens) ts -> 
      if run_dfa d 0 ts then 
        exists v, in_parser p (flat_map token_id_to_chars ts) v
      else 
        forall v, ~ in_parser p (flat_map token_id_to_chars ts) v.
  Proof.
    intros. assert (ts = nil ++ ts) ; auto. rewrite H1. eapply dfa_corr' ; eauto.
    assert (wf_dfa (par2rec p) d). eapply build_dfa_wf. apply par2rec_wf. eauto.
    unfold wf_dfa in H2. mysimp.
  Qed.

  Definition accepts_at_most_one_null t (r:regexp t) (H:wf_regexp r) : bool := 
    if le_gt_dec (List.length (apply_null r H)) 1 then true else false.

  Fixpoint enum_tokens (f:token_id -> bool) (n:nat) : bool := 
    match n with 
      | 0 => true
      | S m => (f m) && enum_tokens f m
    end.

  Definition forall_tokens (f:token_id -> bool) : bool := enum_tokens f num_tokens.

  Lemma wf_deriv_parse' cs t (r:regexp t) (H:wf_regexp r) : wf_regexp (deriv_parse' r cs).
  Proof.
    induction cs ; mysimp. apply IHcs. apply wf_deriv. auto.
  Qed.

  End TABLE.
  End FNMAP.

  (** ** Now we need to translate our external representation, [parser] to 
         our internal representation [regexp] and build an appropriate [ctxt]
         mapping function names to functions of the right type. *)

  (** Add a new function to the end of the context and return its position as 
      a "fresh" function name, along with the new context. *)
  Definition extend_state(s:ctxt_t) t1 t2 (f:fn_result_m(t1,t2)) : (fn_name * ctxt_t) := 
    (length s, s ++ (existT fn_result_m (t1,t2) f)::nil).

  (** Convert a parser with inlined functions to a regexp and a function map. *)
  Fixpoint par2reg t (p:parser t)(s:ctxt_t) : (regexp t) * ctxt_t := 
    match p in parser t return (regexp t) * ctxt_t with
      | Any_p => (Any, s)
      | Char_p b => (Char b, s)
      | Eps_p => (Eps, s)
      | Cat_p t1 t2 p1 p2 => 
        let (r1,s1) := par2reg p1 s in 
        let (r2,s2) := par2reg p2 s1 in 
          (Cat r1 r2, s2)
      | Zero_p t => (Zero t, s)
      | Alt_p t p1 p2 => 
        let (r1,s1) := par2reg p1 s in 
        let (r2,s2) := par2reg p2 s1 in 
          (Alt r1 r2, s2)
      | Star_p t p1 => 
        let (r1,s1) := par2reg p1 s in
          (Star r1, s1)
      | Map_p t1 t2 f p => 
        let (r,s1) := par2reg p s in 
        let (n,s2) := extend_state s1 f in
          (@Map t1 t2 (Fn_name n t1 t2) r, s2)
    end.

  (** Initial state for the translation. *)
  Definition initial_ctxt : ctxt_t := nil.

  (** Top-level translation of parsers to regexps. *)
  Definition parser2regexp t (p:parser t) : (regexp t) * ctxt_t := 
    par2reg p initial_ctxt.

  (** ** Now we need to prove that the translation [parser2regexp] preserves
         meaning. *)

  (** Tactic to propagate information about the translation. *)
  Ltac unfold_par2reg := 
    match goal with 
      | [ |- context[par2reg ?p ?s] ] => 
        let H := fresh "H" in 
          let x := fresh "x" in
            let r := fresh "r" in 
              let s := fresh "s" in 
                assert (H : exists x, x = par2reg p s) ; [eauto | idtac] ; 
                  destruct H as [x H]; 
                    rewrite <- H in * ; destruct x as [r s] 
    end.

  (** Define a partial order on contexts, which the translation respects.  That is,
      the input context is always less than the output context. *)
  Definition ctxt_leq(c1 c2:ctxt_t) : Prop := 
    exists c:ctxt_t, c2 = c1 ++ c.

  Lemma ctxt_leq_trans : forall c1 c2 c3, 
    ctxt_leq c1 c2 -> ctxt_leq c2 c3 -> ctxt_leq c1 c3.
  Proof.
    unfold ctxt_leq ; s. rewrite app_ass. eauto.
  Qed.

  Lemma ctxt_leq_refl : forall c, ctxt_leq c c.
    unfold ctxt_leq ; s. exists nil. apply app_nil_end.
  Qed.
  Hint Resolve ctxt_leq_refl : dfa.

  Lemma ctxt_ext : forall c c', ctxt_leq c (c ++ c').
    unfold ctxt_leq ; s. eauto.
  Qed.
  Hint Resolve ctxt_ext : dfa.

  (** Simplify reasoning about inductive hypotheses that depend upon a context. *)
  Ltac p2rsimp := 
    match goal with 
      | [ |- context[length(?x ++ ?y)] ] => rewrite (@app_length _ x y)
      | [ IH : forall _:ctxt_t, _, H : _ = par2reg ?p ?s |- _ ] => 
        generalize (IH s) ; 
          match goal with 
            | [ |- context[par2reg ?p ?s] ] => 
              let H' := fresh "H" in generalize (IH s) ; clear IH ; rewrite <- H ; simpl ; 
                intro H'
            | _ => fail
          end 
      | _ => idtac
    end.

  (** The translation only results in a greater or equal ctxt *)
  Lemma p2r_extends : forall t (p:parser t) (c:ctxt_t), ctxt_leq c (snd (par2reg p c)).
  Proof.
    unfold ctxt_leq ; induction p ; simpl ; unfold extend_state ; intros ; 
      repeat unfold_par2reg ; simpl ; 
      try (exists nil ; mysimp ; fail) ; repeat p2rsimp ; s ; 
    try rewrite app_ass ; econstructor ; eauto.
  Qed.

  (** Functions stay well-typed under greater or equal contexts. *)
  Lemma extends_wf_fn : forall t1 t2 (f:fn t1 t2) c c', ctxt_leq c c' ->
   wf_fn c f -> wf_fn c' f.
  Proof.
    unfold ctxt_leq ; s ; destruct f ; auto ; simpl in * ; generalize c H0 ; clear c H0 ; 
    unfold fn_result, fn_result' in * ; induction f ; destruct c ; 
      [ mysimp | mysimp | mysimp | intro ] ; try congruence ;
    simpl in *. firstorder.
    destruct H0. generalize (IHf _ (conj (lt_S_n _ _ H) H0)). mysimp. firstorder.
  Qed.

  (** Regexps stay well-typed under greater or equal contexts. *)
  Lemma extends_wf_regexp : forall t (r:regexp t) c c', 
    ctxt_leq c c' -> wf_regexp c r -> wf_regexp c' r.
  Proof.
    induction r ; simpl ; s ; firstorder. eapply extends_wf_fn ; eauto. econstructor ; eauto.
  Qed.

  (** Tactic for remembering a translated sub-term is well-formed. *)
  Ltac p2rext := 
    match goal with 
      | [ H : (?r,?s2) = par2reg ?p ?s |- _ ] => 
        generalize (p2r_extends p s) ; rewrite <- H ; simpl ; intro ; clear H
    end.

  Lemma FnResult : forall s p r, 
    fn_result (s ++ existT fn_result_m p r :: nil) (length s) = Some p.
  Proof.
    induction s ; mysimp ; firstorder.
  Qed.
  Hint Resolve FnResult.

  (** The translation results in a well-formed regexp. *)
  Lemma p2r_wf : forall t (p:parser t) c, wf_regexp (snd (par2reg p c)) (fst (par2reg p c)).
  Proof.
    induction p ; mysimp ; repeat unfold_par2reg ; repeat p2rsimp ; mysimp ; p2rext ; 
    try (eapply (@extends_wf_regexp _ _ s); eauto) ; try econstructor ; eauto with arith.
  Qed.

  (** Applying the same function in an extended environment yields the same result. *)
  Lemma extend_apply : forall x t1 t2 (f:fn t1 t2) s (H:wf_fn s f) v1 H', 
    apply_fn (s ++ x) f H' v1 = apply_fn s f H v1.
  Proof.
    destruct f ; auto. simpl. 
    mysimp. generalize f l0 e0 l e ; clear f l0 e0 l e. 
    induction s ; destruct f ; mysimp ; firstorder ; 
      unfold fn_result, fn_result' in * |- ; simpl in * ;
      try congruence. destruct a. rewrite (proof_irrelevance e0 e) in *. auto.
  Qed.
  Hint Resolve extend_apply : dfa.

  (** [in_regexp] respects weakening on states. *)
  Lemma in_leq : forall t (r:regexp t) s cs v, 
    in_regexp s r cs v -> 
    forall s', ctxt_leq s s' -> in_regexp s' r cs v.
  Proof.
    unfold ctxt_leq ; induction 1 ; s ; 
    match goal with 
      | [ IH : forall _, _ -> in_regexp _ ?r2 _ _ |- in_regexp _ (Alt _ ?r2) _ _ ] => 
        eapply Alt_right_i ; eauto with dfa
      | [ H : ?cs1 <> nil |- in_regexp _ (Star _) _ _ ] => 
        eapply Star_cat_i ; eauto with dfa
      | [ |- in_regexp _ (Map ?f ?r) ?cs (apply_fn _ ?f ?H ?v1) ] => 
        apply (Map_i(v1:=v1) f (@extends_wf_fn t1 t2 f _ _ (ctxt_ext s x) H)) ; 
          eauto with dfa
      | _ => econstructor ; eauto with dfa 
    end.
  Qed.

  (** Newly-allocated functions are well-formed with respect to the resulting context. *)
  Lemma new_fn_wf : forall t1 t2 f s, wf_fn (s ++ existT fn_result_m (t1,t2) f :: nil)
    (Fn_name (length s) t1 t2).
  Proof.
    induction s; mysimp ; firstorder.
  Qed.
  Hint Resolve new_fn_wf : dfa.

  (** If [(cs,v)] is in [[p]] then [(cs,v)] is in [[r]] under the output context [s]. *)
  Lemma p2r_ok : forall t (p:parser t) cs v, 
    in_parser p cs v -> 
    forall s, 
      in_regexp (snd (par2reg p s)) (fst (par2reg p s)) cs v.
  Proof.
    induction 1 ; simpl ; intro s ;
      repeat (try unfold_par2reg ; simpl in * ; repeat p2rsimp ; repeat p2rext ; intros) ;
        s ; 
        match goal with 
          | [ H : in_regexp _ ?r _ _ |- in_regexp _ (Alt _ ?r) _ _] => 
            eapply Alt_right_i ; eauto
          | [ |- in_regexp _ (Map _ _) _ _ ] => idtac
          | [ H1 : in_regexp _ ?r _ _, 
              H2: in_regexp _ (Star ?r) _ _ |- in_regexp _ (Star ?r) _ _ ] => 
          s ; eapply Star_cat_i ; eauto
          | _ => econstructor ; eauto ; eapply in_leq ; eauto 
        end.
    apply (Map_i(v1:=v1) (Fn_name (length s0) t1 t2) (new_fn_wf f s0)).
    eapply in_leq ; eauto ; unfold ctxt_leq ; eauto. 
    generalize s0 (new_fn_wf f s0). induction s1 ; mysimp ; 
    unfold fn_result, fn_result' in * ; 
    simpl in *. rewrite (proof_irrelevance e (eq_refl _)). auto. 
    generalize (IHs1 (conj (lt_S_n _ _ l) e)). clear IHs1. auto.
  Qed.

  (** If [(cs,v)] is in [[r]] under context [s2], and [r] is well-formed with respect to
     context [s1], and [s1 <= s2], then [(cs,v)] is in [[r]] under context [s1]. *)
  Lemma extends_in : 
    forall t (r:regexp t) cs v s1 s2, 
      in_regexp s2 r cs v -> 
      wf_regexp s1 r -> 
      ctxt_leq s1 s2 -> 
      in_regexp s1 r cs v.
  Proof.
    induction 1 ; simpl ; intros ; s ; (econstructor ; eauto ; fail) || 
    (eapply Alt_right_i ; eauto) || (eapply Star_cat_i ; eauto) || idtac.
    apply (@Map_i s1 t1 t2 f r cs v1 (apply_fn s2 f H v1) H4).
    apply IHin_regexp ; auto. destruct H3. subst. symmetry. eapply extend_apply.
  Qed.
  Hint Resolve extends_in : dfa.

  (** If [(cs,v)] is in [r] under context [s], where [(r,s) = par2reg p], then
      [(cs,v)] is in [p]. *)
  Lemma r2p_ok : forall t (p:parser t) s cs v, 
    in_regexp (snd (par2reg p s)) (fst (par2reg p s)) cs v -> 
    in_parser p cs v.
  Proof.
    induction p ; simpl ; intros s cs v ; try (repeat unfold_par2reg) ; 
      simpl in * ; intros ; (generalize (AnyInv H) || generalize (CharInv H) || 
          generalize (EpsInv H) || generalize (CatInv H1) || generalize (AltInv H1) || 
            generalize (MapInv H0) || generalize (ZeroInv H) || idtac) ; s ; 
      try (econstructor ; eauto ; fail) ;
    repeat match goal with 
      | [ IH : forall _ _ _, in_regexp (snd (par2reg ?p _)) _ _ _ -> _, 
          H : _ = par2reg ?p ?s |- _ ] => 
      generalize (IH s) ; generalize (p2r_extends p s) ; generalize (p2r_wf p s) ; 
        rewrite <- H ; simpl ; clear IH ; intros
    end ; 
    try contradiction || 
      (econstructor ; eauto with dfa ; fail) || (eapply Alt_right_pi ; eauto with dfa).
    generalize (star_rep H0 (eq_refl _) (eq_refl _)). mysimp. clear H0. 
    generalize cs v H4. clear cs v H4.
    induction x ; s. constructor ; auto. eapply Star_cat_pi ; eauto. 
    match goal with 
      | [ |- in_parser (Map_p _ r _) _ (?f x) ] => assert (f = r)
    end.
    
    generalize s0 e l. induction s1 ; unfold value, error, fn_result, fn_result' ; mysimp.
    rewrite (proof_irrelevance e0 (eq_refl _)). auto.
    rewrite H5. eapply (Map_pi _ r). apply H4. 
    apply (@extends_in _ r0 cs x s0 (snd (extend_state s0 r)) H1 H2). unfold extend_state.
    simpl. auto with dfa. auto.
  Qed.

  (** The translation preserves meaning *)
  Theorem parser2regexp_equiv : 
    forall t (p:parser t) cs v, 
      in_parser p cs v <-> 
      in_regexp (snd (parser2regexp p)) (fst (parser2regexp p)) cs v.
  Proof.
    unfold parser2regexp ; mysimp ; firstorder ; [eapply p2r_ok | eapply r2p_ok] ; eauto.
  Qed.

  (** Finally -- convert the parser to a regexp and then run the 
     derivative-based parser on this. *)
  Definition parse t (p:parser t) : list char_p -> list (result_m t) := 
    deriv_parse (snd (parser2regexp p))
                (fst (parser2regexp p)) (p2r_wf p _).

  Theorem parse_correct : forall t (p:parser t) cs v, 
    in_parser p cs v <-> In v (parse p cs).
  Proof.
    intros t p cs v.
    
    generalize (DerivParse_is_parser (snd (parser2regexp p)) (fst (parser2regexp p))
      (p2r_wf p initial_ctxt) cs v) ; intro H ; destruct H ;
    generalize (parser2regexp_equiv p cs v) ; intro  H1 ; destruct H1 ; split ; auto.
  Qed.

  (** Properties of dfa_recognize *)
  Lemma dfa_loop_run : forall num_tokens ts d state count count2 ts2,
    dfa_loop num_tokens d state count ts = Some (count2, ts2) -> 
    exists ts1, 
      ts = ts1 ++ ts2 /\ count2 = length ts1 + count /\ 
      run_dfa num_tokens d state ts1 = true /\
      forall ts1' ts2',
        ts = ts1' ++ ts2' -> 
        length ts1' < length ts1 -> 
        ~ run_dfa num_tokens d state ts1' = true.
  Proof.
    induction ts ; mysimp ; remember (nth state (dfa_accepts d) false) ; 
    destruct b ; try congruence ; try (injection H ; mysimp ; clear H ; subst). 
    exists nil. rewrite Heqb. repeat split ; auto. intros. simpl in H0.
    assert False. omega. contradiction.
    exists nil. simpl. rewrite Heqb. repeat split ; auto.
    intros. assert False. omega. contradiction.
    specialize (IHts d _ _ _ _ H0). mysimp. subst. exists (a::x). simpl.
    repeat split ; auto. intros. destruct ts1'. injection H ; intros ; clear H ; subst.
    simpl. congruence. simpl in H. injection H ; intros ; clear H ; subst.
    specialize (H3 _ _ H4). assert (length ts1' < length x). simpl in *.
    omega. specialize (H3 H). simpl. congruence.
  Qed.

  Lemma list_all_app : forall A (f:A->Prop) (xs ys:list A), 
    list_all f (xs ++ ys) -> list_all f xs /\ list_all f ys.
  Proof.
    induction xs ; mysimp ; specialize (IHxs _ H0) ; mysimp.
  Qed.

  Lemma dfa_recognize_corr (num_tokens:nat) (token_id_to_chars : token_id -> list char_p) : 
    forall t (p:parser t) n (d:DFA),
    build_dfa num_tokens token_id_to_chars n (par2rec p) = Some d -> 
    forall ts, 
      list_all (fun t => t < num_tokens) ts -> 
      match dfa_recognize num_tokens d ts with 
        | None => True
        | Some (count,ts2) => 
          exists ts1, exists v, 
            ts = ts1 ++ ts2 /\ count = length ts1 /\ 
            in_parser p (flat_map token_id_to_chars ts1) v /\
            forall ts3 ts4,
              length ts3 < length ts1 ->
              ts = ts3 ++ ts4 -> 
              forall v, ~ in_parser p (flat_map token_id_to_chars ts3) v
      end.
  Proof.
    intros. unfold dfa_recognize. remember (dfa_loop num_tokens d 0 0 ts) as e.
    destruct e ; auto. destruct p0. 
    generalize (dfa_loop_run _ _ _ _ _ (eq_sym Heqe)). mysimp. subst.
    exists x. generalize (list_all_app _ _ _ H0).  mysimp.
    generalize (dfa_corr nil _ _ _ _ H _ H1). rewrite H3. mysimp. 
    rewrite plus_comm. simpl. exists x0. repeat split ; auto.
    intros. specialize (H4 _ _ H7 H6). intro. apply H4.
    rewrite H7 in H0. generalize (list_all_app _ _ _ H0). mysimp.
    generalize (@dfa_corr nil num_tokens token_id_to_chars _ p n d H ts3 H9).
    destruct (run_dfa num_tokens d 0 ts3). auto. intros. assert False.
    eapply H11. eauto. contradiction.
  Qed.
    
End Parser.
