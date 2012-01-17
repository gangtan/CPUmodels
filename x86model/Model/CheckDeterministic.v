(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

   
(** CheckDeterministic.v:  This file provides some routines to help try to
    prove that parsers are deterministic.  In particular, there's a function
    [disjoint_p p1 p2] which when it returns true, ensures that there is no
    string of tokens (i.e., bytes) that is accepted by both [p1] and [p2].
    This is achieved by computing the intersection of the two [regexps] 
    corresponding to [p1] and [p2] and trying to show that that intersection
    is equivalent to [Zero].  

    I coded a new version of regexps, here called [rexp] to avoid conflicts
    with the definition in [Parser.v], which includes intersection ([And_r]).
    To determine if an [rexp] is equivalent to [Zero], we (a) check to see
    if the [rexp] is nullable (if so, then it accepts [nil] so it's not
    equivalent to [Zero]), and otherwise, calculate the derivative of the
    [rexp] with respect to each possible input token, and then recursively
    see if the derivatives are zero.  If all of the derivatives are zero,
    then the original expression is equivalent to zero.
*)
Require Import Coqlib.
Require Import Parser.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import Bits.
Require Import Decode.
Require Import Eqdep.
Unset Automatic Introduction.
Set Implicit Arguments.
Open Scope char_scope.
Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.
Require ExtrOcamlNatInt.
Import X86_PARSER_ARG.
Import X86_PARSER.
Import X86_BASE_PARSER.

(** Our regular expressions with intersection ([And_r]).  We need
    the support for intersection to test whether two parsers overlap
    on strings.  *)
Inductive rexp : Type := 
| Any_r : rexp
| Char_r : char_p -> rexp
| Eps_r : rexp
| Cat_r : rexp -> rexp -> rexp
| Zero_r : rexp
| Alt_r : rexp -> rexp -> rexp
| Star_r : rexp -> rexp
| And_r : rexp -> rexp -> rexp.

(** Denotational semantics of regular expressions. *)
Inductive in_rexp : rexp -> list char_p -> Prop := 
| Any_ri : forall c, in_rexp Any_r (c::nil)
| Char_ri : forall c, in_rexp (Char_r c) (c::nil)
| Eps_ri : in_rexp Eps_r nil
| Cat_ri : forall r1 r2 cs1 cs2 cs, 
  in_rexp r1 cs1 -> in_rexp r2 cs2 -> 
  cs = cs1 ++ cs2 -> in_rexp (Cat_r r1 r2) cs
| Alt_left_ri : forall r1 r2 cs, in_rexp r1 cs -> in_rexp (Alt_r r1 r2) cs
| Alt_right_ri : forall r1 r2 cs, in_rexp r2 cs -> in_rexp (Alt_r r1 r2) cs
| Star_eps_ri : forall r, in_rexp (Star_r r) nil
| Star_cat_ri : forall r cs1 cs2 cs, 
  cs1 <> nil -> in_rexp r cs1 -> in_rexp (Star_r r) cs2 -> 
  cs = cs1 ++ cs2 ->
  in_rexp (Star_r r) cs
| And_ri : forall r1 r2 cs, in_rexp r1 cs -> in_rexp r2 cs -> in_rexp (And_r r1 r2) cs.
Hint Constructors in_rexp.

Ltac mysimp := 
  simpl in * ; intros ; 
    repeat match goal with 
             | [ |- context[char_eq ?x ?y] ] => destruct (char_eq x y) ; auto 
             | [ |- _ /\ _ ] => split
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ |- context[ _ ++ nil ] ] => rewrite <- app_nil_end
             | [ H : exists x, _ |- _ ] => destruct H
             | [ H : _ \/ _ |- _] => destruct H
             | [ H : _ <-> _ |- _] => destruct H
             | [ |- _ <-> _ ] => split
             | [ H : _::_ = _::_ |- _] => injection H ; clear H
             | _ => idtac
           end ; auto.
Ltac s := repeat (mysimp ; subst).

Lemma cons_app A (x:A) (ys:list A) : x :: ys = (x::nil) ++ ys. auto. Qed.

(** I coded [rexp_eq] explicitly to return a [bool], because this seems
    to run faster than if we compute a proof of equality. *)
Fixpoint rexp_eq(r1 r2:rexp) : bool := 
  match r1, r2 with 
    | Any_r, Any_r => true
    | Any_r, _ => false
    | Char_r c1, Char_r c2 => if char_eq c1 c2 then true else false
    | Char_r _, _ => false
    | Eps_r, Eps_r => true
    | Eps_r, _ => false
    | Cat_r r1 r2, Cat_r r3 r4 => rexp_eq r1 r3 && rexp_eq r2 r4
    | Cat_r _ _, _ => false
    | Zero_r, Zero_r => true
    | Zero_r, _ => false
    | Alt_r r1 r2, Alt_r r3 r4 => rexp_eq r1 r3 && rexp_eq r2 r4
    | Alt_r _ _, _ => false
    | Star_r r1, Star_r r2 => rexp_eq r1 r2
    | Star_r _, _ => false
    | And_r r1 r2, And_r r3 r4 => rexp_eq r1 r3 && rexp_eq r2 r4
    | And_r _ _, _ => false
  end.

(** Proof that [rexp_eq] really does compute equality. *)
Lemma rexp_eq_corr r1 r2 : 
  if rexp_eq r1 r2 then r1 = r2 else r1 <> r2.
Proof.
  induction r1 ; destruct r2 ; simpl ; try congruence ; unfold andb in * ; 
    repeat
  match goal with 
    | [ |- context[if char_eq ?c ?c0 then _ else _] ] => 
      destruct (char_eq c c0) ; subst ; try congruence
    | [ H : (forall r2, if rexp_eq ?r1 r2 then _ else _) |-
            context[if rexp_eq ?r1 ?r2 then _ else _] ] => 
    generalize (H r2) ; clear H ; intro H ; destruct (rexp_eq r1 r2) ; subst
    | _ => try congruence ; auto
  end.
Qed.

Ltac in_inv := 
  match goal with 
    | [ H : in_rexp Eps_r _ |- _ ] => inversion H ; clear H ; subst
    | [ H : in_rexp Any_r _ |- _ ] => inversion H ; clear H ; subst
    | [ H : in_rexp (Char_r _) _ |- _ ] => inversion H ; clear H ; subst
    | [ H : in_rexp (Cat_r _ _) _ |- _ ] => inversion H ; clear H ; subst
    | [ H : in_rexp (Alt_r _ _) _ |- _ ] => inversion H ; clear H ; subst
    | [ H : in_rexp (And_r _ _) _ |- _ ] => inversion H ; clear H ; subst
    | [ H : in_rexp Zero_r _ |- _ ] => inversion H
    | [ |- context [if rexp_eq ?r1 ?r2 then _ else _] ] => 
      generalize (rexp_eq_corr r1 r2) ; intro ;
      destruct (rexp_eq r1 r2) ; try congruence
    | [ H : context [if rexp_eq ?r1 ?r2 then _ else _] |- _ ] => 
      generalize (rexp_eq_corr r1 r2) ; intro ; 
      destruct (rexp_eq r1 r2) ; try congruence
    | _ => s
  end.

(** Optimizing [cat] constructor. *)
Definition OptCat_r(r1 r2:rexp) : rexp := 
  match r1, r2 with 
    | Zero_r, _ => Zero_r
    | Eps_r, r2 => r2
    | _, Zero_r => Zero_r
    | r1, Eps_r => r1
    | r1, r2 => Cat_r r1 r2
  end.

(** [OptCat_r] is equivalent to [Cat_r]. *)
Lemma opt_cat_r_corr : forall r1 r2 s, 
  in_rexp (Cat_r r1 r2) s <-> in_rexp (OptCat_r r1 r2) s.
Proof.
  destruct r1 ; repeat in_inv ; eauto ; destruct r2 ; repeat in_inv ; eauto ; 
    try (rewrite cons_app ; eauto ; fail) ;
    try (rewrite app_nil_end ; eauto ; fail).
Qed.
Hint Resolve opt_cat_r_corr.

(** Optimizing [alt] constructor. *)
Definition OptAlt_r(r1 r2:rexp) : rexp := 
  match r1, r2 with 
    | Zero_r, r2 => r2
    | r1, Zero_r => r1
    | Char_r true, Char_r false => Any_r
    | Char_r false, Char_r true => Any_r
    | r1, r2 => if rexp_eq r1 r2 then r1 else Alt_r r1 r2
  end.

(** [Alt_r r r] is equivalent to [r] *)
Lemma eq_rexp_alt1 r s:
  in_rexp (Alt_r r r) s <-> in_rexp r s.
Proof.
  repeat in_inv.
Qed.
Hint Resolve eq_rexp_alt1.

(** [OptAlt_r] is equivalent to [Alt]. *)
Lemma opt_alt_r_corr : forall r1 r2 s, 
  in_rexp (Alt_r r1 r2) s <-> in_rexp (OptAlt_r r1 r2) s.
Proof.
  destruct r1 ; simpl ; destruct r2 ; unfold andb ; simpl ; repeat in_inv ; 
    repeat 
    match goal with 
      | [ H : _ = _ |- _] => injection H ; clear H ; intros ; subst ; eauto 
      | [ |- in_rexp (if ?c then _ else _) _ ] => destruct c ; simpl ; eauto      
      | [ H : in_rexp (if ?c then _ else _) _ |- _] => destruct c ; simpl in * ; 
        repeat in_inv ; eauto
      | _ => eauto
    end ; destruct c ; eauto.
Qed.
Hint Resolve opt_alt_r_corr.

(** Returns [Eps_r] if [r] accepts the empty string, else returns [Zero_r]. *)
Fixpoint null_r (r:rexp) : rexp := 
  match r with 
    | Any_r => Zero_r
    | Char_r _ => Zero_r
    | Eps_r => Eps_r
    | Zero_r => Zero_r
    | Alt_r r1 r2 => OptAlt_r (null_r r1) (null_r r2)
    | Cat_r r1 r2 => OptCat_r (null_r r1) (null_r r2)
    | Star_r r => Eps_r
    | And_r r1 r2 => match null_r r1, null_r r2 with 
                       | Zero_r, _ => Zero_r
                       | _, Zero_r => Zero_r
                       | _, _ => Eps_r
                     end
  end.

(** [null_r] returns either [Eps_r] or [Zero_r]. *)
Lemma null_r_eps_zero : forall r, null_r r = Eps_r \/ null_r r = Zero_r.
Proof.
  induction r ; s ;
    repeat 
  match goal with 
    | [ H : ?r = Eps_r |- _ ] => rewrite H ; clear H ; simpl 
    | [ H : ?r = Zero_r |- _ ] => rewrite H ; clear H ; simpl
    | _ => idtac
  end ; auto. 
Qed.

(** If [s] is in denotation of [null_r r] then [s] is [nil]. *)
Lemma null_r_corr' : forall r s, 
  in_rexp r s -> 
  forall r', r = null_r r' -> s = nil.
Proof.
  induction 1 ; intros ; generalize (null_r_eps_zero r') ; intro NEZ ; destruct NEZ ; 
    try congruence.
Qed.

Lemma null_r_corr1 : forall r s, in_rexp (null_r r) s -> s = nil.
Proof.
  intros ; eapply null_r_corr' ; eauto.
Qed.

Lemma nil_is_nil_app_nil : forall A (cs1 cs2:list A), 
  nil = cs1 ++ cs2 -> cs1 = nil /\ cs2 = nil.
Proof.
  destruct cs1 ; destruct cs2 ; simpl ; intros ; try congruence. auto.
Qed.

(** If [nil] is in the denotation of [r], then it's also in [null_r r]. *)
Lemma null_r_corr2 : forall r s, in_rexp r s -> s = nil -> in_rexp (null_r r) s.
Proof.
  induction 1 ; repeat in_inv ; try congruence ; 
    try (apply opt_alt_r_corr ; eauto).
  generalize (nil_is_nil_app_nil _ _ (sym_eq H2)). repeat in_inv.
  apply opt_cat_r_corr. rewrite app_nil_end. eauto.
  generalize (nil_is_nil_app_nil _ _ (sym_eq H3)). repeat in_inv.
  generalize (null_r_eps_zero r1) (null_r_eps_zero r2). 
  generalize (IHin_rexp1 (eq_refl _)). generalize (IHin_rexp2 (eq_refl _)).
  repeat in_inv ; rewrite H3 in * ; rewrite H4 in * ; in_inv ; eauto.
Qed.
Hint Resolve null_r_corr2.

(** If [nil] is in the denotation of [null_r r], then it's also in the 
    denotation of [r]. *)
Lemma null_r_corr3 r : in_rexp (null_r r) nil -> in_rexp r nil.
Proof.
  induction r ; repeat in_inv ; 
  try (generalize (proj2 (opt_alt_r_corr _ _ _) H)) ; 
  try (generalize (proj2 (opt_and_r_corr _ _ _) H)) ; 
    repeat in_inv.
  generalize (proj2 (opt_cat_r_corr _ _ _) H). clear H. repeat in_inv. rewrite H5.
  generalize (nil_is_nil_app_nil _ _ H5). in_inv. rewrite app_nil_end. eauto.
  generalize (null_r_eps_zero r1) (null_r_eps_zero r2) ; intros A1 A2.
  destruct A1 as [A1 | A1]; rewrite A1 in * ; 
    destruct A2 as [A2 | A2 ] ; rewrite A2 in * ; eauto.
Qed.

(** If [null_r r] is [Eps_r], then it accepts [nil]. *)
Lemma null_r_corr4 : forall r, null_r r = Eps_r -> in_rexp r nil.
Proof.
  induction r ; simpl ; intros ; try congruence ; eauto ; try (
  generalize (null_r_eps_zero r1) (null_r_eps_zero r2) ; intros H1 H2 ; 
    destruct H1 as [H1 | H1 ]; rewrite H1 in * ; simpl in * ; try congruence ; 
      destruct H2 as [H2 | H2]; rewrite H2 in * ; simpl in * ; try congruence) ; eauto.
Qed.
Hint Resolve null_r_corr4.

(** Optimizing [And_r r1 r2]. *)
Definition OptAnd_r(r1 r2:rexp) : rexp := 
  match r1, r2 with 
    | _, Zero_r => Zero_r
    | Zero_r, _ => Zero_r
    | Eps_r, r2 => null_r r2
    | r1, Eps_r => null_r r1
    | Any_r, Char_r c => Char_r c
    | Char_r c, Any_r => Char_r c
    | Char_r c1, Char_r c2 => if char_eq c1 c2 then Char_r c1 else Zero_r
    | r1, r2 => if rexp_eq r1 r2 then r1 else And_r r1 r2
  end.

Ltac pv_opt := 
  repeat 
  match goal with 
    | [ |- in_rexp (OptCat_r _ _) _ ] => apply opt_cat_r_corr 
    | [ |- in_rexp (OptAlt_r _ _) _ ] => apply opt_alt_r_corr 
    | [ H : nil = ?cs1 ++ ?cs2 |- _] => generalize (nil_is_nil_app_nil _ _ H) ; s    
    | [ H : in_rexp (OptCat_r _ _) _ |- _ ] => 
      generalize (proj2 (opt_cat_r_corr _ _ _) H) ; clear H ; repeat in_inv
    | [ H : in_rexp (OptAlt_r _ _) _ |- _ ] => 
      generalize (proj2 (opt_alt_r_corr _ _ _) H) ; clear H ; repeat in_inv
    | [ H : in_rexp (null_r ?r) _ |- _ ] => 
      let H1 := fresh "H" in 
      let H2 := fresh "H" in     
      let H3 := fresh "H" in 
      generalize (null_r_corr1 _ H)  ; intro ; subst ; 
      generalize (null_r_corr3 _ H) ; 
      generalize (null_r_corr2 H (eq_refl _)) ; 
      generalize (null_r_eps_zero r) ; 
        intros H1 H2 H3 ; destruct H1 ; rewrite H1 in * ; s ; clear H
    | [ H : in_rexp ?r nil |- context [null_r ?r] ] => 
      let H1 := fresh "H" in
      let H2 := fresh "H" in 
        generalize (null_r_corr2 H (eq_refl _)) ; 
          generalize (null_r_eps_zero r) ; 
            intros H1 H2 ; destruct H1 ; rewrite H1 in *
    | [ H : in_rexp (match null_r ?r with | Any_r => _ | Char_r _ => _ | Eps_r => _
                       | Cat_r _ _ => _ | Zero_r => _ | Alt_r _ _ => _ | Star_r _ => _
                         | And_r _ _ => _ end) _ |- _] => 
    let H := fresh "H" in 
      generalize (null_r_eps_zero r) ; intros H ; destruct H ; rewrite H in *
    | [ |- in_rexp (And_r _ _) _ ] => constructor
    | [ H : Cat_r _ _ = Cat_r _ _ |- _] => injection H ; clear H ; s
    | [ H : Alt_r _ _ = Alt_r _ _ |- _] => injection H ; clear H ; s
    | [ H : And_r _ _ = And_r _ _ |- _] => injection H ; clear H ; s
    | [ H : Star_r _ = Star_r _ |- _] => injection H ; clear H ; s
    | _ => in_inv ; eauto
  end.

(** [OptAnd_r] is equivalent to [And_r]. *)
Lemma opt_and_r_corr : forall r1 r2 s, 
  in_rexp (And_r r1 r2) s <-> in_rexp (OptAnd_r r1 r2) s.
Proof.
  destruct r1 ; simpl ; destruct r2 ; unfold andb ; simpl; 
    repeat in_inv ; try congruence ; pv_opt.
Qed.

(** Convert a [parser] to an [rexp]. *)
Fixpoint parser2rexp t (p:parser t) : rexp := 
  match p with 
    | Any_p => Any_r
    | Char_p c => Char_r c
    | Eps_p => Eps_r
    | Cat_p t1 t2 r1 r2 => OptCat_r (parser2rexp r1) (parser2rexp r2)
    | Zero_p t => Zero_r
    | Alt_p t r1 r2 => OptAlt_r (parser2rexp r1) (parser2rexp r2)
    | Star_p t r => Star_r (parser2rexp r)
    | Map_p t1 t2 f r => parser2rexp r
  end.

(** If [s] and [v] are in the denotation of [p], then [s] is in the denotation of
    [parser2rexp p]. *)
Lemma parse2rexp_corr1 t (p:parser t) s v : 
  in_parser p s v -> in_rexp (parser2rexp p) s.
Proof.
  induction 1 ; subst ; repeat in_inv ; 
    try (apply opt_alt_r_corr ||apply opt_cat_r_corr) ; eauto.
Qed.

(** If [s] is in the denotation of [parser2rexp p], then there exists some [v],
    such that [s] and [v] are in the denotation of [p]. *)
Lemma parse2rexp_corr2 t (p:parser t) s : 
  in_rexp (parser2rexp p) s -> 
    exists v, in_parser p s v.
Proof.
  induction p ; repeat in_inv ; try (econstructor ; econstructor ; eauto ; fail).
   generalize (proj2 (opt_cat_r_corr (parser2rexp p1) (parser2rexp p2) s) H).
   repeat in_inv. generalize (IHp1 _ H3). generalize (IHp2 _ H4). s. 
   repeat econstructor ; eauto.
   generalize (proj2 (opt_alt_r_corr _ _ _) H). repeat in_inv. 
   generalize (IHp1 _ H4) ; repeat in_inv. repeat econstructor ; eauto.
   generalize (IHp2 _ H4) ; repeat in_inv. econstructor. eapply Alt_right_pi. eauto.
   Focus 2. generalize (IHp _ H). s. econstructor. econstructor. eauto. eauto.
   generalize s H IHp. clear s H IHp. generalize (parser2rexp p).
   intros r s H. remember (Star_r r) as r'. generalize Heqr'. clear Heqr'.
   induction H ; intros ; try congruence ; injection Heqr' ; intros ; subst ; clear
     Heqr'. exists nil. constructor ; auto. generalize (IHin_rexp2 (eq_refl _) IHp).
   clear IHin_rexp1 IHin_rexp2. intros. destruct H2. generalize (IHp _ H0). 
   intros. destruct H3. econstructor. eapply Star_cat_pi. eauto. eauto. auto.
   eauto. auto.
Qed.

(** Returns true if [r] accepts the empty string, false otherwise -- it's
    faster to just compute this directly than to call [null_r]. *)
Fixpoint ck_null (r:rexp) : bool := 
  match r with 
    | Eps_r => true
    | Char_r _ => false
    | Any_r => false
    | Zero_r => false
    | Alt_r r1 r2 => ck_null r1 || ck_null r2
    | Cat_r r1 r2 => ck_null r1 && ck_null r2
    | And_r r1 r2 => ck_null r1 && ck_null r2
    | Star_r _ => true
  end.

(** [ck_null] is correct. *)
Lemma ck_null_corr r : if ck_null r then in_rexp r nil else ~ in_rexp r nil.
Proof.
  induction r ; simpl ; auto ; try (intro ; in_inv) ; 
    repeat 
      match goal with 
        | [ H : if ck_null ?r then _ else _ |- _ ] => destruct (ck_null r) ; simpl
        | [ |- in_rexp (Cat_r _ _) nil ] => 
          let H := fresh "H" in
          assert (H: @nil char_p = nil ++ nil) ; [ auto | rewrite H ] ; eauto
        | [ |- ~ _ ] => intro ; in_inv
        | [ H : nil = ?cs1 ++ ?cs2 |- _] => generalize (nil_is_nil_app_nil cs1 cs2 H) ; 
          clear H ; s
        | [ H : in_rexp ?r ?s, H1 : ~ in_rexp ?r ?s |- _ ] => contradiction H1
        | _ => eauto
      end.
Qed.

(** Calculate the derivative of an [rexp] with respect to a character. *)
Fixpoint deriv_r (r:rexp) (c:char_p) : rexp := 
  match r with 
    | Any_r => Eps_r
    | Char_r c' => if char_eq c c' then Eps_r else Zero_r
    | Eps_r => Zero_r
    | Zero_r => Zero_r
    | Alt_r r1 r2 => OptAlt_r (deriv_r r1 c) (deriv_r r2 c)
    | Cat_r r1 r2 => 
      OptAlt_r (OptCat_r (deriv_r r1 c) r2) 
               (if ck_null r1 then deriv_r r2 c else Zero_r)
    | Star_r r as r' => OptCat_r (deriv_r r c) r'
    | And_r r1 r2 => OptAnd_r (deriv_r r1 c) (deriv_r r2 c)
  end.

(** Derivative is correct part 1 *)
Lemma deriv_r_corr1 r s : 
  in_rexp r s -> forall c cs, s = c::cs -> in_rexp (deriv_r r c) cs.
Proof.
  induction 1 ; try (repeat in_inv ; try congruence ; 
    try (apply opt_alt_r_corr) ; try (apply opt_and_r_corr) ; 
          try (apply opt_cat_r_corr) ; eauto).
  destruct cs1. simpl in *. subst. apply Alt_right_ri. 
  generalize (ck_null_corr r1). destruct (ck_null r1). intros. eauto.
  intros. contradiction H1. s. apply Alt_left_ri. apply opt_cat_r_corr. eauto.
  destruct cs1. congruence. simpl in *. injection H3 ; intros ; subst ; clear H3.
  econstructor ; eauto.
Qed.

(** Derivative is correct part 2 *)
Lemma deriv_r_corr2 r c cs : in_rexp (deriv_r r c) cs -> in_rexp r (c::cs).
Proof.
  induction r ; repeat in_inv. destruct (char_eq c0 c). subst. in_inv. constructor.
  in_inv. generalize (proj2 (opt_alt_r_corr _ _ _) H). clear H ; intro.
  in_inv. generalize (proj2 (opt_cat_r_corr _ _ _) H3). clear H3 ; intro ; 
  in_inv. econstructor ; eauto. generalize (ck_null_corr r1).  destruct (ck_null r1).
  intros. assert (c::cs = nil ++ c::cs) ; auto. rewrite H0. eauto. in_inv.
  generalize (proj2 (opt_alt_r_corr _ _ _) H). clear H. repeat in_inv.
  generalize (proj2 (opt_cat_r_corr _ _ _) H). clear H. repeat in_inv.
  eapply Star_cat_ri ; eauto. congruence. generalize opt_and_r_corr.
  repeat in_inv. generalize (proj2 (opt_and_r_corr _ _ _) H). clear H. repeat in_inv.
Qed.

(** A string [c::cs] is in the denotation of [r] iff [cs] is in the 
    denotation of [deriv_r r c]. *)
Lemma deriv_r_corr r c cs : in_rexp r (c::cs) <-> in_rexp (deriv_r r c) cs.
Proof.
  intros ; split ; intros. eapply deriv_r_corr1; eauto. eapply deriv_r_corr2 ; eauto.
Qed.

(** Extend derivatives to strings -- i.e., lists of characters. *)
Fixpoint derivs_r (r:rexp) (cs:list char_p) : rexp := 
  match cs with 
    | nil => r
    | c::cs' => derivs_r (deriv_r r c) cs'
  end.

(** A string [cs1 ++ cs2] is in the denotation of [r] iff the string [cs2] is
    in the denotation of [derivs_r r cs1]. *)
Lemma derivs_r_corr cs1 r cs2 : in_rexp r (cs1 ++ cs2) <-> in_rexp (derivs_r r cs1) cs2.
Proof.
  intros ; split ; generalize r cs2 ; clear r cs2 ; induction cs1 ; simpl ; intros ; auto.
  eapply IHcs1. apply deriv_r_corr ; auto.
  apply deriv_r_corr. apply IHcs1. auto.
Qed.

(** Specialization of [deriv] for the case where we are going to take the
    derivative with respect to all characters. This avoids doing a case
    split on [Any_r] into the characters and provides a big speedup. *)
Fixpoint DerivAny (r:rexp) : rexp := 
  match r with 
    | Any_r => Eps_r
    | Char_r _ => Eps_r
    | Zero_r => Zero_r
    | Eps_r => Zero_r
    | Alt_r r1 r2 => OptAlt_r (DerivAny r1) (DerivAny r2)
    | And_r r1 r2 => OptAnd_r (DerivAny r1) (DerivAny r2)
    | Cat_r r1 r2 => 
      OptAlt_r (OptCat_r (DerivAny r1) r2) 
               (if ck_null r1 then DerivAny r2 else Zero_r)
    | Star_r r as r' => OptCat_r (DerivAny r) r'
  end.

(** Calculate the derivative of one [rexp] with respect to another.  This is
    only meaningful when [r2] is a star-free [rexp] which is why we get an 
    option out.  As we'll see, we get an over approximation of the set of
    strings accepted by the derivative of [r1] with respect to the strings
    in [r2].   This provides a fast test for checking whether an intersection
    is empty and is in fact sufficient for our needs. *)
Fixpoint Deriv (r1:rexp) (r2:rexp) : option rexp := 
  match r2 with 
    | Any_r => Some (DerivAny r1)
    | Char_r c => Some (deriv_r r1 c)
    | Zero_r => Some (Zero_r)
    | Eps_r => Some r1
    | Alt_r ra rb => 
      match Deriv r1 ra with 
        | Some Zero_r => Deriv r1 rb 
        | Some d1 => match Deriv r1 rb with 
                       | Some d2 => Some (OptAlt_r d1 d2)
                       | None => None
                     end
        | None => None
      end
    | Cat_r ra rb => 
      match Deriv r1 ra with
        | Some Zero_r as d => d 
        | Some d1 => Deriv d1 rb
        | None => None
      end
    | And_r ra rb => 
      match Deriv r1 ra, Deriv r1 rb with 
        | Some d1, Some d2 => Some (OptAnd_r d1 d2)
        | _, _ => None
      end
    | Star_r ra => None
  end.

Ltac Dsimp := 
  match goal with 
    | [ H : Some ?x = Some ?y |- _ ] => 
      assert (x = y) ; [injection H ; auto | clear H ; subst]
    | [ H : in_rexp (deriv_r _ ?c) _ |- exists cs, _ /\ _ ] => 
      exists (c::nil) ; split ; [constructor | apply deriv_r_corr ; auto]
    | [ H : (match Deriv ?r1 ?r2 with | Some _ => _ | None => _ end = _) |- _ ] => 
      let d := fresh "d" in
        remember (Deriv r1 r2) as d ; destruct d
    | [ H : Some _ = Deriv _ _ |- _] => generalize (eq_sym H) ; clear H ; intro H
    | [ IH : forall _ _, Deriv _ ?r2 = Some _ -> _, H : Deriv _ ?r2 = Some _ |- _ ] => 
      specialize (IH _ _ H)
    | [ IH : forall _, in_rexp ?r _ -> _, H : in_rexp ?r _ |- _ ] => 
      specialize (IH _ H)
    | [ H : Some _ = None |- _ ] => congruence
    | [ H : None = Some _ |- _ ] => congruence
    | [ H : in_rexp (OptAnd_r _ _) _ |- _] => 
      generalize (proj2 (opt_and_r_corr _ _ _) H) ; clear H ; intro H
    | _ => idtac
  end.

(** If [c::cs'] is in the denotation of [r] then [cs'] is in the denotation
    of [DerivAny r]. *)
Lemma DerivAny_corr1 : forall r cs, in_rexp r cs -> 
  forall c cs', cs = c::cs' -> in_rexp (DerivAny r) cs'.
Proof.
  induction 1 ; simpl ; repeat (in_inv ; pv_opt) ; try congruence.
  destruct cs1. eapply Alt_right_ri. generalize (ck_null_corr r1).
  destruct (ck_null r1). intros. pv_opt. intros. contradiction H1.
  eapply Alt_left_ri. pv_opt. destruct cs1. pv_opt. congruence. simpl in H3. injection H3.
  intros ; subst. pv_opt. apply opt_and_r_corr. pv_opt.
Qed.

(** If [cs1] is in the denotation of [r2] and [cs1++cs2] is in the denotation of [r1],
    then [cs2] is in the denotation of [Deriv r1 r2]. *)
Lemma Deriv_corr1 : forall r2 r1 r3, Deriv r1 r2 = Some r3 -> 
  forall cs1 cs2, 
    in_rexp r2 cs1 -> 
    in_rexp r1 (cs1 ++ cs2) -> 
    in_rexp r3 cs2.
Proof.
  induction r2 ; repeat (in_inv ; Dsimp ; pv_opt). eapply DerivAny_corr1 ; eauto.
  apply deriv_r_corr ; auto. rewrite <- app_assoc in H1. destruct r ; Dsimp ; eauto.
  specialize (IHr2_1 _ _ H4 H1). inversion IHr2_1. destruct r ; repeat Dsimp ; pv_opt.
  specialize (IHr2_1 _ _ H5 H1). pv_opt. destruct r ; repeat Dsimp ; pv_opt.
  apply opt_and_r_corr. eauto.
Qed.

(** If [Deriv r1 r2] is [Zero_r], then there is no string in the intersection 
    of the denotations of [r1] and [r2]. *)
Lemma Deriv_Zero : forall r1 r2, 
  Deriv r1 r2 = Some Zero_r -> 
  ~ (exists cs, in_rexp (And_r r1 r2) cs).
Proof.
  intros. generalize (Deriv_corr1 H). intros. intro. destruct H1.
  inversion H1. subst ; clear H1. generalize (H0 x nil H6). rewrite <- app_nil_end.
  intros. specialize (H1 H4). inversion H1.
Qed.
  
(* Note the other direction does not hold, due to And_r: 

  Lemma Deriv_corr1 : forall r2 r1 r3, Deriv r1 r2 = Some r3 -> 
    forall cs2, in_rexp r3 cs2 -> exists cs1, in_rexp r2 cs1 /\ in_rexp r1 (cs1 ++ cs2).

  The problem is that what we return as the [Deriv] is an over-approximation of
  the set of strings in the derivative of [r1] with respect to the strings in [r2].
  Fortunately, we don't need this fact.
*)

(** Convert a nat representing a byte to a list of bits *)
Definition n2b(n:nat) : list bool := 
  let bs := Word.bits_of_Z 8 (Z_of_nat n) in
    (bs 7)::(bs 6)::(bs 5)::(bs 4)::(bs 3)::(bs 2)::(bs 1)::(bs 0)::nil.

Definition token_id_to_chars := n2b.
Definition num_tokens := 256%nat.
Opaque token_id_to_chars.
Opaque num_tokens.

(* Check whether [r] is equivalent to [Zero_r].  Note that to check whether
   [And_r r1 r2] is equivalent to [Zero_r], we take the derivative of [r1]
   with respect to [r2] and then check whether the resulting [rexp] is 
   equivalent to [Zero_r].  

   Note that [n] here is used for "fuel" so as long as you find some [n]
   that returns [true], you know that [r] is equivalent to [Zero_r].
*)
Fixpoint ckzero (n:nat) (r:rexp) : bool := 
  match n with 
    | 0%nat => false
    | S n => 
      match r with 
        | Zero_r => true
        | Eps_r => false
        | Any_r => false
        | Char_r _ => false
        | Cat_r r1 r2 => ckzero n r1 || ckzero n r2
        | Alt_r r1 r2 => ckzero n r1 && ckzero n r2
        | Star_r _ => false
        | And_r r1 r2 => 
          match Deriv r1 r2 with 
            | Some r => ckzero n r
            | None => 
              negb (ck_null r1 && ck_null r2) &&
              ckzero n (OptAlt_r (OptAnd_r (deriv_r r1 true) (deriv_r r2 true))
                       (OptAnd_r (deriv_r r1 false) (deriv_r r2 false)))
          end
      end
  end.

(** Correctness for [ckzero]:  If [ckzero n r] returns [true] for some [n], then
    there is no string in the denotation of [r]. *)
Lemma ckzero_corr n r : ckzero n r = true -> ~(exists s, in_rexp r s).
Proof.
  induction n ; simpl ; intros ; try congruence ; destruct r ; try congruence ; intro ;
    mysimp ; repeat in_inv ; unfold andb, orb, negb in *.
  generalize (IHn r1). destruct (ckzero n r1). intros. apply H0 ; auto. eauto.
  intros. apply (IHn _ H). eauto. generalize (IHn r1). destruct (ckzero n r1).
  intros. apply H0 ; eauto. congruence. generalize (IHn r2). destruct (ckzero n r1) ; 
  destruct (ckzero n r2) ; try congruence. intros. apply H0 ; eauto.
  generalize (@Deriv_corr1 r2 r1). intros. remember (Deriv r1 r2) as e.
  destruct e. generalize (H0 r (eq_refl _) x nil H5) (IHn _ H). intros.
  apply H2. exists nil. apply H1. rewrite <- app_nil_end. auto.
  generalize (ck_null_corr r1) (ck_null_corr r2) ; 
  destruct (ck_null r1) ; destruct (ck_null r2) ; intros ; try congruence ; 
    destruct x ; auto ; generalize (IHn _ H) ; clear H ; intro H ; 
    apply H ; clear H ; exists x ; pv_opt ; destruct c ; clear H1 H2 ;
  try (apply Alt_left_ri ; apply opt_and_r_corr ; constructor ; eapply deriv_r_corr1 ; eauto ; fail) ; 
    apply Alt_right_ri ; apply opt_and_r_corr ; constructor ; eapply deriv_r_corr1 ; eauto.
Qed.

(** Check whether [r1] and [r2] denote disjoint sets of strings -- we simply
    check whether their intersection is equivalent to [Zero_r]. *)
Definition ckdisj_r (n:nat) (r1 r2:rexp) := ckzero n (OptAnd_r r1 r2).

(** Correctness of [ckdisj_r]. *)
Lemma ckdisj_r_corr n r1 r2 : ckdisj_r n r1 r2 = true -> ~(exists s, in_rexp r1 s /\ 
  in_rexp r2 s).
Proof.
  unfold ckdisj_r ; intros. generalize (ckzero_corr n H).  intros. intro.
  apply H0. mysimp. exists x. apply opt_and_r_corr. auto.
Qed.

(** Lift [ckdisj_r] to operate on parsers. *)
Definition ckdisj_p (n:nat) t (p1:parser t) (p2:parser t) := 
  ckdisj_r n (parser2rexp p1) (parser2rexp p2).

(** Correctness of [ckdisj_p] -- here we see that if [p1] and [p2] are disjoint,
    then there is no string [s] and values [v1] and [v2], such that [s] and [v1]
    are in the denotation of [p1], and [s] and [v2] are in the denotation of [p2]. *)
Lemma ckdisj_p_corr n t (p1 p2:parser t) : 
  ckdisj_p n p1 p2 = true -> ~(exists s, exists v1, exists v2, in_parser p1 s v1 /\ 
    in_parser p2 s v2).
Proof.
  unfold ckdisj_p. intros. intro. generalize (ckdisj_r_corr _ H). intros. mysimp.
  apply H1. exists x. split ; eapply parse2rexp_corr1 ; eauto. 
Qed.

(** Multi [OptAlt_r]. *)
Definition alts_r := List.fold_right OptAlt_r Zero_r.

(** Count up from [i] to [m] and try to check if [r] is equivalent to [Zero_r]
    using [i] as the bound.  This tries to avoid checking to deeply when it's
    not necessary. *)
Fixpoint ckzeros i m r := 
  match i with 
    | 0%nat => false
    | S i => ckzero (m - (S i)) r || ckzeros i m r
  end.

(** Correctness of [ckzeros]. *)
Lemma ckzeros_corr : forall i m r,
  ckzeros i m r = true -> ~ (exists s, in_rexp r s).
Proof.
  induction i ; simpl ; intros. congruence. intro.
  generalize (@ckzero_corr (m - S i) r). intro.
  destruct (ckzero (m - S i) r). apply H1 ; auto. simpl in H.
  apply (IHi _ _ H). auto.
Qed.

(** [check_all_r] checks that all [rexp]s in the list [rs] are mutually disjoint.
    I tried a divide and conquer strategy, where we do O(n lg n) tests but it 
    turns out to be no faster than this rather brute force approach because the
    derivatives were growing.  Here, we do O(n^2) tests which is still better 
    than doing all pair-wise comparisons. *)
Fixpoint check_all_r m (rs:list rexp) := 
  match rs with 
    | nil => true
    | r::rs => check_all_r m rs && ckzeros m m (OptAnd_r r (alts_r rs)) 
  end.

(** Correctness of [check_all_r]:  If [check_all_r m rs] returns [true], then
    we know that if [s] is in the denotation of [alts_r rs], then there is some
    [r] in [rs], such that [s] is in the denotation of [r], and furthermore,
    [s] is not in the denotation of any of the rest of the [rexp]s. *)
Lemma check_all_r_corr m rs : 
  check_all_r m rs = true -> 
  forall s, in_rexp (alts_r rs) s -> 
    exists rs1, exists r, exists rs2, 
      rs = rs1 ++ r::rs2 /\
      in_rexp r s /\ ~ in_rexp (alts_r (rs1 ++ rs2)) s.
Proof.
  induction rs ; simpl ; intros. in_inv. 
  generalize (proj2 (opt_alt_r_corr a (alts_r rs) s) H0). clear H0. intro.
  remember (check_all_r m rs) as e. destruct e ; simpl in * ; try congruence.
  specialize (IHrs (eq_refl _) s). generalize (ckzeros_corr m m H). intros.
  inversion H0. subst. exists nil. exists a. exists rs. simpl. split ; auto.
  split. auto. intro. apply H1. exists s. apply opt_and_r_corr. eauto. subst.
  specialize (IHrs H5). destruct IHrs. destruct H2. destruct H2. destruct H2.
  destruct H3. subst. exists (a::x). exists x0. exists x1. simpl. split.
  auto. split. auto. intro. apply H1. exists s. 
  generalize (proj2 (opt_alt_r_corr _ _ _) H2). clear H2. intro.
  apply opt_and_r_corr.
  constructor. inversion H2. subst. auto. subst. contradiction H4 ; auto. 
  apply H5.
Qed.

(** Lift [check_all_r] up to parsers. *)
Definition check_all_p m t (ps:list (parser t)) := 
  check_all_r m (List.map (@parser2rexp _) ps).

Fixpoint check_all_r' m (rs:list rexp) := 
  match rs with 
    | nil => true
    | r::rs => 
      check_all_r' m rs && 
      ckzeros m m (OptAnd_r (OptCat_r (alts_r rs) (Star_r Any_r)) (OptCat_r r (Star_r Any_r)))
  end.

Definition check_all_p' m t (ps:list (parser t)) := 
  check_all_r' m (List.map (@parser2rexp _) ps).

Lemma all_instructions_check : 
  check_all_p' 3 instruction_parser_list = true.
Proof.
  Time vm_compute. auto.
Qed.

Lemma star_any_all : forall s, in_rexp (Star_r Any_r) s.
Proof.
  induction s. econstructor. replace (a::s) with ((a::nil) ++ s) ; auto.
  eapply Star_cat_ri ; eauto. congruence.
Qed.

Lemma check_all_r'_corr m rs : 
  check_all_r' m rs = true -> 
  forall s, in_rexp (alts_r rs) s -> 
    exists rs1, exists r, exists rs2,
      rs = rs1 ++ r :: rs2 /\ 
      in_rexp r s /\ ~ exists s2, in_rexp (alts_r (rs1 ++ rs2)) (s ++ s2).
Proof.
  induction rs ; simpl ; intros. in_inv.
  generalize (proj2 (opt_alt_r_corr a (alts_r rs) s) H0). clear H0. intro.
  remember (check_all_r' m rs) as e. destruct e ; simpl in * ; try congruence.
  specialize (IHrs (eq_refl _) s). generalize (ckzeros_corr m m H). intros.
  inversion H0 ; clear H0. subst. exists nil. exists a. exists rs. simpl. split ; auto.
  split ; auto. intro. apply H1. destruct H0. exists (s ++ x). apply opt_and_r_corr.
  econstructor. eapply opt_cat_r_corr. rewrite app_nil_end. econstructor.
  eauto. econstructor. auto. eapply opt_cat_r_corr. generalize (star_any_all x). 
  intros. econstructor ; eauto.
  subst. specialize (IHrs H5). destruct IHrs. destruct H0. destruct H0. destruct H0.
  destruct H2. subst. exists (a::x). exists x0. exists x1. simpl. split ; auto.
  split ; auto. intro. destruct H0. generalize (proj2 (opt_alt_r_corr a _ (s++x2)) H0).
  clear H0. intro. inversion H0 ; clear H0 ; subst. clear H Heqe.
  contradiction H1. exists (s ++ x2). apply opt_and_r_corr. constructor.
  apply opt_cat_r_corr. econstructor. eapply H5. eapply (star_any_all x2). auto.
  apply opt_cat_r_corr. econstructor. eapply H8. eapply (star_any_all nil). 
  rewrite app_ass. rewrite <- app_nil_end. auto. contradiction H3.
  exists x2. auto.
Qed.

(** Lemma for reasoning about [alts]. *)
Lemma in_alts t (ps:list (parser t)) s v: 
  in_parser (alts ps) s v -> in_rexp (alts_r (List.map (@parser2rexp _) ps)) s.
Proof.
  induction ps ; simpl ; intros. unfold never in *. inversion H. 
  apply opt_alt_r_corr. inversion H ; repeat
  match goal with 
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => 
      generalize (inj_pairT2 _ _ _ _ _ H) ; clear H ; intros ; subst
  end. eapply Alt_left_ri. eapply parse2rexp_corr1. eauto.
  eapply Alt_right_ri. eauto.
Qed.

(** A sort of injection lemma for [List.map] over lists. *)
Lemma map_split : forall A B (f:A -> B) (ys1:list B) (y:B) (ys2:list B) (xs:list A),
  List.map f xs = ys1 ++ y::ys2 -> 
  exists xs1, exists x, exists xs2, 
    xs = xs1 ++ x :: xs2 /\
    ys1 = List.map f xs1 /\ 
    y = f x /\ 
    ys2 = List.map f xs2.
Proof.
  induction ys1 ; simpl ; intros ; destruct xs ; simpl in * ; try congruence.
  exists nil. exists a. exists xs. injection H. intros. subst. simpl. auto.
  injection H. intros. subst. specialize (IHys1 y ys2 xs H0). s.
  exists (a0 :: x). exists x0. exists x1. simpl. auto.
Qed.

(** Denotation of [alts] is commutative. *)
Lemma in_alts_comm t (ps1:list (parser t)) (p:parser t) (ps2:list (parser t)) s v : 
  in_parser (alts (ps1 ++ p :: ps2)) s v -> 
  in_parser (Alt_p p (alts (ps1 ++ ps2))) s v.
Proof.
  induction ps1. simpl. auto. intros. simpl in *. inversion H ; repeat
  match goal with 
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => 
      generalize (inj_pairT2 _ _ _ _ _ H) ; clear H ; intros ; subst
  end.  apply Alt_right_pi. apply Alt_left_pi. auto.
  specialize (IHps1 p ps2 s v H4). inversion IHps1 ; repeat
  match goal with 
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => 
      generalize (inj_pairT2 _ _ _ _ _ H) ; clear H ; intros ; subst
  end. apply Alt_left_pi.   auto. apply Alt_right_pi. apply Alt_right_pi. auto.
Qed.

(** [check_all_p] is correct -- if [check_all_p m ps] returns [true], then
   if [s] and [v] are in the denotation of [alts ps], then we know there is 
   a unique [p] in [ps] such that [s] and [v] are in the denotation of [p],
   but that [s] is not in the denotation of any other parser in [ps]. *)
Lemma check_all_p_corr m t (ps:list (parser t)) :
  check_all_p m ps = true -> 
  forall s v, 
    in_parser (alts ps) s v ->
    (exists ps1, exists p, exists ps2, 
      ps = ps1 ++ p :: ps2 /\
      in_parser p s v /\
      ~ exists v' : result_m t, in_parser (alts (ps1 ++ ps2)) s v').
Proof.
  unfold check_all_p. intros. generalize (check_all_r_corr m _ H). intros.
  specialize (H1 s (in_alts _ H0)). destruct H1. destruct H1. destruct H1.
  destruct H1. destruct H2. generalize (map_split (@parser2rexp t) x x0 x1 ps H1).
  intros. mysimp. subst. exists x2. exists x3. exists x4. split. auto.
  generalize (in_alts_comm x2 x3 x4 H0). intros.
  assert (~ exists v', in_parser (alts (x2 ++ x4)) s v'). intro.
  destruct H5. apply H3. generalize (in_alts (x2 ++ x4) H5). rewrite map_app. auto.
  split ; auto. inversion H4 ; repeat
  match goal with 
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => 
      generalize (inj_pairT2 _ _ _ _ _ H) ; clear H ; intros ; subst
  end. auto. contradiction H5. eauto.
Qed.

Lemma check_all_p'_corr m t (ps:list (parser t)) :
  check_all_p' m ps = true -> 
  forall s v, 
    in_parser (alts ps) s v ->
    (exists ps1, exists p, exists ps2, 
      ps = ps1 ++ p :: ps2 /\
      in_parser p s v /\
      ~ exists s2, exists v' : result_m t, in_parser (alts (ps1 ++ ps2)) (s++s2) v').
Proof.
  unfold check_all_p. intros. generalize (check_all_r'_corr m _ H). intros.
  specialize (H1 s (in_alts _ H0)). destruct H1. destruct H1. destruct H1.
  destruct H1. destruct H2. generalize (map_split (@parser2rexp t) x x0 x1 ps H1).
  intros. mysimp. subst. exists x2. exists x3. exists x4. split. auto.
  generalize (in_alts_comm x2 x3 x4 H0). intros.
  assert (~ exists s2, exists v', in_parser (alts (x2 ++ x4)) (s ++ s2) v'). intro.
  destruct H5. destruct H5.
  apply H3. exists x. generalize (in_alts (x2 ++ x4) H5). rewrite map_app. auto.
  split ; auto. inversion H4 ; repeat
  match goal with 
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => 
      generalize (inj_pairT2 _ _ _ _ _ H) ; clear H ; intros ; subst
  end. auto. contradiction H5. exists nil. rewrite <- app_nil_end. eauto.
Qed.

(** Check that all of the instruction parsers are mutually disjoint -- if you
    pass in a number like 3 this should evaluate to true -- but it takes a
    really long time.  So I suggest extracting this function and running it
    in ML. *)
Definition check_all_instructions m := check_all_p m instruction_parser_list.

Transparent token_id_to_chars.
Transparent num_tokens.
(** FIX:  This is admitted now, just because it takes a long time to run, 
    but it should be trivial. *)
Lemma all_instructions_disjoint : check_all_instructions 3 = true.
Proof.
(*Admitted.*)

  unfold check_all_instructions.
  vm_compute.
  auto.
Qed.

Opaque instruction_parser_list.

Ltac t := repeat
  match goal with 
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : exists _, _ |- _ ] => destruct H
    | [ |- forall _, _ ] => intros
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => 
      generalize (inj_pairT2 _ _ _ _ _ H) ; clear H ; intros ; subst
  end.

(** If [s] and [v] are in the denotation of [alts (p::(ps1++ps2))] then
    [s] and [v] are in the denotation of [alts (ps1++p::ps2)]. *)
Lemma in_alts_comm' : forall t (ps1 ps2:list (parser t)) (p:parser t) s v,
  in_parser (alts (p :: (ps1 ++ ps2))) s v -> 
  in_parser (alts (ps1 ++ p :: ps2)) s v.
Proof.
  induction ps1. simpl. auto. intros. simpl in *. inversion H  ; clear H ; t.
  eapply Alt_right_pi. eapply IHps1. eapply Alt_left_pi. auto.
  inversion H4  ; clear H4 ; t. eapply Alt_left_pi. auto. 
  eapply Alt_right_pi. eapply IHps1. eapply Alt_right_pi. auto.
Qed.

(** If [s] and [v] are in the denotation of [alts (ps1 ++ p :: ps2)], and
    [s] and [v] are also in the denotation of [p] and not in the 
    denotation of [alts (ps1 ++ ps2)], then if we split [ps1++p::ps2] into
    some other [ps1'++p'::ps2'] such that [s] and [v] are in [p'], then
    [ps1=ps1'] and [p=p'] and [ps2=ps2']. *)
Lemma splits_unique t (ps : list (parser t)) : 
  forall s v, 
    in_parser (alts ps) s v -> 
    forall ps1 p ps2, 
      ps = ps1 ++ p :: ps2 -> 
      in_parser p s v /\ (~ exists v', in_parser (alts (ps1 ++ ps2)) s v') -> 
      forall ps1' p' ps2' v', 
        ps = ps1' ++ p' :: ps2' /\ in_parser p' s v' -> 
        ps1 = ps1' /\ p = p' /\ ps2 = ps2'.
Proof.
  induction ps. simpl. intros. destruct ps1 ; simpl in * ; congruence. t.
  destruct ps1. injection H0 ; clear H0 ; intros ; subst.
  destruct ps1'. injection H2 ; clear H2 ; intros ; subst ; auto.
  simpl in *. injection H2 ; clear H2 ; intros ; subst. contradiction H4.
  exists v'. eapply in_alts_comm'. simpl. eapply Alt_left_pi ; eauto.
  simpl in *. injection H0 ; intros ; subst ; clear H0.
  destruct ps1' ; simpl in *. injection H2 ; intros ; clear H2 ; subst.
  contradiction H4. exists v'. eapply Alt_left_pi ; eauto. 
  injection H2. clear H2 ; intros ; subst. inversion H ; t ; clear H.
  contradiction H4. exists v. eapply Alt_left_pi ; eauto.
  assert (~ exists v', in_parser (alts (ps1 ++ ps2)) s v').
  intro. apply H4. t. exists x. eapply Alt_right_pi. eauto.
  specialize (IHps _ _ H8 ps1 p ps2 (eq_refl _) (conj H1 H) ps1' p' ps2' v' (conj H0 H3)).
  t. subst. auto.
Qed.

(** If [s] and [v] are in the denotation of [alts ps], then there is 
    some [ps1++p::ps2=ps] such that [s] and [v] are in the denotation of [p]. *)
Lemma in_alts_split : forall t (ps:list (parser t)) s v, 
  in_parser (alts ps) s v -> 
  exists ps1, exists p, exists ps2, 
    ps = ps1 ++ p :: ps2 /\ in_parser p s v.
Proof.
  induction ps ; simpl. unfold never. intros. inversion H.
  intros. inversion H ; clear H ; t. exists nil. exists a. exists ps. auto.
  specialize (IHps s v H4). in_inv. exists (a::x). exists x0. exists x1. auto.
Qed.

(** If [p] is an element of [ps] and [s] and [v] are in the denotation of
    [p], then they are also in the denotation of [alts ps]. *)
Lemma elt_in_alts : forall t (p:parser t) (ps:list (parser t)) s v,
  In p ps -> 
  in_parser p s v -> 
  in_parser (alts ps) s v.
Proof.
  induction ps ; simpl ; intros. contradiction H. destruct H. subst. 
  apply Alt_left_pi. auto. apply Alt_right_pi. auto.
Qed.
  
(** If [s] and [v] are in the denotation of [alts ps1] and [ps1] is
    a subset of [ps2], then [s] and [v] are also in [alts ps2]. *)
Lemma subset_in : forall t (ps1 ps2 : list (parser t)) s v,
  in_parser (alts ps1) s v -> 
  (forall p, In p ps1 -> In p ps2) -> 
  in_parser (alts ps2) s v.
Proof.
  induction ps1. simpl. intros. unfold never in *. inversion H. simpl.
  intros. inversion H ; clear H ; repeat
  match goal with 
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => 
      generalize (inj_pairT2 _ _ _ _ _ H) ; clear H ; intros ; subst
  end. assert (In a ps2).  apply H0. left ; auto. eapply elt_in_alts ; eauto. auto.
Qed.

Lemma in_splits A (x:A) (xs:list A) :
  In x xs -> exists xs1, exists xs2, xs = xs1 ++ x :: xs2.
Proof.
  induction xs ; simpl ; t. contradiction H. destruct H. subst.
  exists nil. exists xs. auto. specialize (IHxs H). t. subst.
  exists (a::x0). exists x1. auto.
Qed.

Lemma splits_in A (x:A) (x1s x2s:list A) : 
  In x (x1s ++ x::x2s).
Proof.
  induction x1s ; simpl ; auto.
Qed.

(** If all of the [ps] are disjoint (according to [check_all_p]), then 
    for each subset [p1s] of [ps], if [s] and [v] are in [alts ps1] then
    they are also in [alts ps] and if [s] and [v'] are in [alts ps] then
    [s] and [v'] are in [alts p1s].  *)
Lemma parse_split' : 
  forall t m (ps:list (parser t)), check_all_p m ps = true ->
  forall p1s s v, 
  (forall p, In p p1s -> In p ps) ->
  in_parser (alts p1s) s v -> 
  in_parser (alts ps) s v /\ 
  (forall v', in_parser (alts ps) s v' -> 
    in_parser (alts p1s) s v').
Proof.
  t. split. generalize (in_alts_split p1s H1). t. subst. eapply subset_in ; eauto.
  t. generalize (check_all_p_corr m _ H H2). clear m H. t.
  generalize (in_alts_split _ H1). t. assert (In x3 p1s). rewrite H5. apply splits_in. 
  generalize (H0 _ H7). intros. generalize (@in_splits _ _ _ H8). t.
  generalize (@splits_unique _ _ _ _ H2 _ _ _ H (conj H3 H4) x5 x3 x6 v (conj H9 H6)).
  t. subst. generalize (in_alts_comm _ _ _ H2). intros. inversion H5 ; t.
  eapply in_alts_comm'. eapply Alt_left_pi. auto. contradiction H4. eauto.
Qed.

(** This lemma tells us that if we take a sublist [ps] of the parsers in the list of
    instruction parsers (e.g., used to build a DFA), and if [ps] accepts some string
    [s] and produces some value [v], then (a) running the heavyweight parser will also
    accept [s] and produce [v], and (b) if the heavyweight parser can produce a 
    different value [v'] from [s], then [ps] can do that as well.  So if [ps] is
    deterministic, then running either [ps] or the heavyweight parser will result
    in at most one unique value [v].
*)
Lemma parse_split : 
  forall ps,
    (forall p, In p ps -> In p instruction_parser_list) ->
    forall s v,
      in_parser (alts ps) s v -> 
        in_parser (alts instruction_parser_list) s v /\ 
        (forall v', in_parser (alts instruction_parser_list) s v' -> in_parser (alts ps) s v').
Proof.
  intros. apply (parse_split' 3 instruction_parser_list all_instructions_disjoint _ H H0). 
Qed.

