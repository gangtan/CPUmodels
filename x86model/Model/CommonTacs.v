(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List.
Require Export Coq.omega.Omega.

Require Import Coq.Logic.Eqdep.

Set Implicit Arguments.

Ltac bool_intro_tac :=
  repeat match goal with
           | [ |- andb ?b1 ?b2 = true ] =>
            apply andb_true_iff; split
         end.

Ltac bool_elim_tac :=
  repeat match goal with
           | [ H: negb ?b = true |- _ ] => 
             apply negb_true_iff in H
           | [ H: andb ?b1 ?b2 = true |- _ ] => 
             apply andb_prop in H; destruct H
           | [ H: orb ?b1 ?b2 = true |- _ ] =>
             apply orb_true_iff in H; destruct H
         end.

(* Find contradiction in the hypothesis *)
Ltac find_contra :=
  match goal with
    | [H:?p, H1:~ ?p |- _] => contradict H; trivial
    | [H: forall v, ~ ?P v, H1: ?P ?V |- _] => contradict H1; apply H
  end.

(* Make a duplicate of the hypothesis *)
Ltac dupHyp H := 
  let t := type of H in
  let H' := fresh H in
    assert t as H' by assumption.

(** Destruct the head *)
Tactic Notation "destruct_head" :=
  match goal with
    | [ |- context[if ?X then _ else _]] => destruct X
     (* the following matches let (_,_) := _ in _ *)
    | [ |- context[match ?X with (_, _)  => _ end]]
      => destruct X
    | [ |- context[match ?X with existT _ _ _ => _ end]] => destruct X
    | [ |- context[match ?X with nil => _ | cons _ _ => _ end]]
      => destruct X
    | [ |- context[match ?X with Some _ => _ | None => _ end]]
      => destruct X
    | [ |- context[match ?X with 0%Z => _ | Zpos _  | Zneg _ => _ end]]
      => destruct X
  end.

(** Destruct the head in a hypothesis *)
Tactic Notation "destruct_head" "in" ident(H) :=
    match type of H with
      | context[if ?X then _ else _] => destruct X
        (* the following matches let (_,_) := _ in _ *)
      | context[match ?X with (_, _)  => _ end] => destruct X
      | context[match ?X with existT _ _ _ => _ end] => destruct X
      | context[match ?X with nil => _ | cons _ _ => _ end] => destruct X
      | context[match ?X with Some _ => _ | None => _ end] => destruct X
      | context[match ?X with 0%Z => _ | Zpos _  | Zneg _ => _ end] =>
        destruct X
    end.

(** Similar to remember, but instead of generating "id=term", generate
    "term=id" instead *)
Tactic Notation "remember_rev" constr(E) "as" ident(X) :=
  set (X := E) in *; 
  let HX := fresh "H" X in assert (HX : E = X) by reflexivity; clearbody X.


Tactic Notation "remember_head" "as" ident(name) := 
    match goal with
      | [|- context[if ?X then _ else _]] => remember_rev X as name
        (* the following matches let (_,_) := _ in _ *)
      | [|-context[match ?X with (_, _)  => _ end]] => remember_rev X as name
      | [|-context[match ?X with existT _ _ _ => _ end]] => 
        remember_rev X as name
      | [|- context[match ?X with nil => _ | cons _ _ => _ end]]
        => remember_rev X as name
      | [|- context[match ?X with Some _ => _ | None => _ end]]
        => remember_rev X as name
      | [|- context[match ?X with 0%Z => _ | Zpos _  | Zneg _ => _ end]]
        => remember_rev X as name
    end.

Tactic Notation "remember_head" "in" ident(H) "as" ident(name) := 
  let t := type of H in
    match t with
      | context[if ?X then _ else _] => remember_rev X as name
        (* the following matches let (_,_) := _ in _ *)
      | context[match ?X with (_, _)  => _ end] => remember_rev X as name
      | context[match ?X with existT _ _ _ => _ end] =>
        remember_rev X as name
      | context[match ?X with nil => _ | cons _ _ => _ end]
        => remember_rev X as name
      | context[match ?X with Some _ => _ | None => _ end]
        => remember_rev X as name
      | context[match ?X with 0%Z => _ | Zpos _  | Zneg _ => _ end]
        => remember_rev X as name
    end.

Tactic Notation "remember_head_in_hyp" "as" ident(name) := 
    match goal with
      | [_ : context[if ?X then _ else _] |- _] => remember_rev X as name
        (* the following matches let (_,_) := _ in _ *)
      | [_ : context[match ?X with (_, _) => _ end] |- _] => remember_rev X as name
      | [_ : context[match ?X with existT _ _ _ => _ end] |- _] =>
        remember_rev X as name
      | [_ : context[match ?X with nil => _ | cons _ _ => _ end] |- _]
        => remember_rev X as name
      | [_ : context[match ?X with Some _ => _ | None => _ end] |- _]
        => remember_rev X as name
      | [_ : context[match ?X with 0%Z => _ | Zpos _  | Zneg _ => _ end] |- _]
        => remember_rev X as name
    end.

Tactic Notation "remember_destruct_head" "as" ident(name) :=
  remember_head as name; destruct name.

Tactic Notation "remember_destruct_head" "in" ident(H) "as" ident(name) :=
  remember_head in H as name; destruct name.

Ltac clear_dup :=
  match goal with
    | [ H : ?X |- _ ] =>
      match goal with
        | [ H' : ?Y |- _ ] =>
          match H with
            | H' => fail 2
            | _ => unify X Y ; (clear H' || clear H)
          end
      end
  end.
Ltac clear_dups := repeat clear_dup.

(* Find two variables of the same type; prove their equivalence; 
   then do a subst *)
Ltac congruence_subst :=
  match goal with
    | [v1:?tp, v2:?tp |- _] =>
      assert (v1=v2) by congruence; subst v2
  end.
Ltac congruence_substs := repeat congruence_subst.

(* Checking P is not a hypothesis already *)
Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.

(* extend teh context to have pf, if it's not already there *)
Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.

(* Add a lemma and all facts that can be dervied from it to the context;
   tac is used to prove subgoals when applying the lemma; this tactic performs
   forward reasoning *)
Tactic Notation "use_lemma" constr(lm) "by" tactic(tac) :=
  let H := fresh "H" in
    generalize lm; intro H;
    repeat match type of H with
             | forall x : ?T, _ =>
               match type of T with
                 | Prop =>
                   (let H' := fresh "H'" in
                     assert (H' : T); 
                       [solve [ tac ] | generalize (H H'); clear H H'; intro H ])
                   || fail 1
                 | _ =>
                   let x := fresh "x" in
                     evar (x : T);
                     let x' := eval cbv delta [x] in x in
                       clear x; generalize (H x'); clear H; intro H
               end
           end.

(* simple hypothesis simplification *)
Ltac break_hyp :=
  repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : _ <-> _ |- _] => destruct H
           | [ H : exists x, _ |- _ ] => destruct H
         end.

(* break variables of tuple and unit types *)
Ltac destruct_vars := 
  repeat match goal with
    | [v: unit |- _ ] => destruct v
    | [v: prod _ _ |- _ ] => destruct v
  end.

(* ----------------------------------------------------------------------- *)
(* Begin of tactics from Adam Chlipala's cpdt book. 
   Two changes were made to crush: (1) The use of intuition is replaced
   by "intros; eauto", which seems faster; (2) as a result of (1), 
   added first-order simplification cases in simplHyp.
 *)

(** Try calling tactic function [f] on all hypotheses, keeping the first application that doesn't fail. *)
Ltac appHyps f :=
  match goal with
    | [ H : _ |- _ ] => f H
  end.

(** Succeed iff [x] is in the list [ls], represented with left-associated nested tuples. *)
Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

(** Try calling tactic function [f] on every element of tupled list [ls], keeping the first call not to fail. *)
Ltac app f ls :=
  match ls with
    | (?LS, ?X) => f X || app f LS || fail 1
    | _ => f ls
  end.

(** Run [f] on every element of [ls], not just the first that doesn't fail. *)
Ltac all f ls :=
  match ls with
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.

(** Workhorse tactic to simplify hypotheses for a variety of proofs.
   * Argument [invOne] is a tuple-list of predicates for which we always do inversion automatically. *)
Ltac simplHyp invOne :=
  (** Helper function to do inversion on certain hypotheses, where [H] is the hypothesis and [F] its head symbol *)
  let invert H F :=
    (** We only proceed for those predicates in [invOne]. *)
    inList F invOne;
    (** This case covers an inversion that succeeds immediately, meaning no constructors of [F] applied. *)
      (inversion H; fail)
    (** Otherwise, we only proceed if inversion eliminates all but one constructor case. *)
      || (inversion H; [idtac]; clear H; try subst) in

  match goal with
     (* elimination of first-order constructors *)
     | [ |- _ /\ _ ] => split
     | [ H : _ /\ _ |- _ ] => destruct H
     | [ H : _ \/ _ |- _] => destruct H
     | [ H : _ <-> _ |- _] => destruct H
     | [ |- _ <-> _ ] => split
     | [ H : exists x, _ |- _ ] => destruct H

    (** Eliminate all existential hypotheses. *)
    | [ H : ex _ |- _ ] => destruct H

    (** Find opportunities to take advantage of injectivity of data constructors, for several different arities. *)
    | [ H : ?F ?X = ?F ?Y |- ?G ] =>
      (** This first branch of the [||] fails the whole attempt iff the arguments of the constructor applications are already easy to prove equal. *)
      (assert (X = Y); [ assumption | fail 1 ])
      (** If we pass that filter, then we use injection on [H] and do some simplification as in [inject].
         * The odd-looking check of the goal form is to avoid cases where [injection] gives a more complex result because of dependent typing, which we aren't equipped to handle here. *)
      || (injection H;
        match goal with
          | [ |- X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
      (assert (X = Y); [ assumption
        | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H;
        match goal with
          | [ |- U = V -> X = Y -> G ] =>
            try clear H; intros; try subst
        end)

    (** Consider some different arities of a predicate [F] in a hypothesis that we might want to invert. *)
    | [ H : ?F _ |- _ ] => invert H F
    | [ H : ?F _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ _ |- _ ] => invert H F

    (** Use an (axiom-dependent!) inversion principle for dependent pairs, from the standard library. *)
    | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H

    (** If we're not ready to use that principle yet, try the standard inversion, which often enables the previous rule. *)
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H

    (** Similar logic to the cases for constructor injectivity above, but specialized to [Some], since the above cases won't deal with polymorphic constructors. *)
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
    | [ H : (_,_) = (_,_) |- _ ] => inversion H; clear H
  end.

Ltac sim := repeat (simplHyp fail).

(** Find some hypothesis to rewrite with, ensuring that [auto] proves all of the extra subgoals added by [rewrite]. *)
Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H by solve [ auto ]
  end.

(** Combine [autorewrite] with automatic hypothesis rewrites. *)
Ltac rewriterP := repeat (rewriteHyp; autorewrite with core in *).
Ltac rewriter := autorewrite with core in *; rewriterP.

(** Hints for manipulating lists. *)
Hint Rewrite app_ass app_nil_r app_length.

(** Devious marker predicate to use for encoding state within proof goals *)
Definition done (T : Type) (x : T) := True.

(** Try a new instantiation of a universally quantified fact, proved by [e].
   * [trace] is an accumulator recording which instantiations we choose. 

    One weakness of inster is that it processes from left to right and does
    not deal with implicit arguments very well. For instance, if lm is of
    type "forall (A:Set) (x:A), ...", then inster has to first find a term
    of type Set in the local context. If that term is nat, then nat:Set is
    not gonna be in the local context.  In this case, we have to provide
    (lm nat) explicitly. *)
Ltac inster e trace :=
  (** Does [e] have any quantifiers left? *)
  match type of e with
    | forall x : _, _ =>
      (** Yes, so let's pick the first context variable of the right type. *)
      match goal with
        | [ H : _ |- _ ] =>
          inster (e H) (trace, H)
        | _ => fail 2
      end
    | _ =>
      (** No more quantifiers, so now we check if the trace we computed was already used. *)
      match trace with
        | (_, _) =>
          (** We only reach this case if the trace is nonempty, ensuring that [inster] fails if no progress can be made. *)
          match goal with
            | [ H : done (trace, _) |- _ ] =>
              (** Uh oh, found a record of this trace in the context!  Abort to backtrack to try another trace. *)
              fail 1
            | _ =>
              (** What is the type of the proof [e] now? *)
              let T := type of e in
                match type of T with
                  | Prop =>
                    (** [e] should be thought of as a proof, so let's add it to the context, and also add a new marker hypothesis recording our choice of trace. *)
                    generalize e; intro;
                      assert (done (trace, tt)) by constructor
                  | _ =>
                    (** [e] is something beside a proof.  Better make sure no element of our current trace was generated by a previous call to [inster], or we might get stuck in an infinite loop!  (We store previous [inster] terms in second positions of tuples used as arguments to [done] in hypotheses.  Proofs instantiated by [inster] merely use [tt] in such positions.) *)
                    all ltac:(fun X =>
                      match goal with
                        | [ H : done (_, X) |- _ ] => fail 1
                        | _ => idtac
                      end) trace;
                    (** Pick a new name for our new instantiation. *)
                    let i := fresh "i" in (pose (i := e);
                      assert (done (trace, i)) by constructor)
                end
          end
      end
  end.

(** After a round of application with the above, we will have a lot of junk [done] markers to clean up; hence this tactic. *)
Ltac un_done :=
  repeat match goal with
           | [ H : done _ |- _ ] => clear H
         end.

Require Import Coq.Logic.JMeq.

(** A more parameterized version of the famous [crush].  Extra arguments are:
   * - A tuple-list of lemmas we try [inster]-ing 
   * - A tuple-list of predicates we try inversion for *)
Ltac crush' lemmas invOne :=
  (** A useful combination of standard automation *)
  let sintuition := simpl in *; intros; eauto; try subst;
    repeat (simplHyp invOne; intros; eauto; try subst); try congruence in

  (** A fancier version of [rewriter] from above, which uses [crush'] to discharge side conditions *)
  let rewriter := autorewrite with core in *;
    repeat (match goal with
              | [ H : ?P |- _ ] =>
                match P with
                  | context[JMeq] => fail 1 (** JMeq is too fancy to deal with here. *)
                  | _ => rewrite H by crush' lemmas invOne
                end
            end; autorewrite with core in *) in

  (** Now the main sequence of heuristics: *)
    (sintuition; rewriter;
      match lemmas with
        | false => idtac (** No lemmas?  Nothing to do here *)
        | _ =>
          (** Try a loop of instantiating lemmas... *)
          repeat ((app ltac:(fun L => inster L L) lemmas
          (** ...or instantiating hypotheses... *)
            || appHyps ltac:(fun L => inster L L));
          (** ...and then simplifying hypotheses. *)
          repeat (simplHyp invOne; intros; eauto)); un_done
      end;
      sintuition; rewriter; sintuition;
      (** End with a last attempt to prove an arithmetic fact with [omega], or prove any sort of fact in a context that is contradictory by reasoning that [omega] can do. *)
      try omega; try (elimtype False; omega)).

(** [crush] instantiates [crush'] with the simplest possible parameters. *)
Ltac crush := crush' false fail.

Ltac crush_hyp := crush' true fail.

(** Instantiate a quantifier in a hypothesis [H] with value [v], or, if [v] doesn't have the right type, with a new unification variable.
   * Also prove the lefthand sides of any implications that this exposes, simplifying [H] to leave out those implications. *)
Ltac guess v H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
               | Prop =>
                 (let H' := fresh "H'" in
                   assert (H' : T); [
                     solve [ eauto 6 ]
                     | specialize (H H'); clear H' ])
                 || fail 1
               | _ =>
                 specialize (H v)
                 || let x := fresh "x" in
                   evar (x : T);
                   let x' := eval unfold x in x in
                     clear x; specialize (H x')
             end
         end.

(** Version of [guess] that leaves the original [H] intact *)
Ltac guessKeep v H :=
  let H' := fresh "H'" in
    generalize H; intro H'; guess v H'.

(* End of cpdt tactics *)
(* ----------------------------------------------------------------------- *)

(* The following tactics are from the book "Software Foundations"
   by Pierce, Casinghino and Greenberg *)

Require Coq.Strings.String. 
Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Ltac Case name := Case_aux Case name.
Ltac SCase name := Case_aux SCase name.
Ltac SSCase name := Case_aux SSCase name.
Ltac SSSCase name := Case_aux SSSCase name.
Ltac SSSSCase name := Case_aux SSSSCase name.
Ltac SSSSSCase name := Case_aux SSSSSCase name.
Ltac SSSSSSCase name := Case_aux SSSSSSCase name.
Ltac SSSSSSSCase name := Case_aux SSSSSSSCase name.


(** ** Tactics related to nats, positives and Z *)

(** convert nat to Z *)
Hint Rewrite Nat2Z.inj_add Nat2Z.inj_mul : nat_to_Z.
Hint Rewrite Nat2Z.inj_sub using omega : nat_to_Z.
Hint Rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P : nat_to_Z.

Lemma Z_of_nat_0 : Z_of_nat 0 = 0%Z. trivial. Qed.
Lemma Z_of_nat_1 : Z_of_nat 1 = 1%Z. trivial. Qed.
Hint Rewrite Z_of_nat_0 Z_of_nat_1 : nat_to_Z.

Lemma inj_S2 : forall n, (Z_of_nat (S n) = Z_of_nat n + 1)%Z.
Proof. intros. apply inj_S. Qed.
Hint Rewrite inj_S2 : nat_to_Z.

Hint Rewrite Zabs2Nat.id_abs : nat_to_Z.
Hint Rewrite Z.abs_eq using omega : nat_to_Z.

(* Converting hypothesis about nats to Z:
     * n1 = n2 ===> Z_of_nat n1 = Z_of_nat n2
     * n1 > n2 ===> Z_of_nat n1 > Z_of_nat n2
     * ...  
   This would not be necessary if we used omega instead of lia.
   Since lia cannot mix facts of Z and nat, we have to
   convert every equality and inquality between nat to Z;
   we also have to add hypothesis (Z_of_nat n >=0) for every
   nat n.
*)
Ltac nat_hyp_to_Z :=
  repeat match goal with
           | [H : ?X = ?Y |- _] =>
             match type of X with
               | nat => apply inj_eq in H
               | _ => fail 1
             end
           | [H: le ?X ?Y |- _] =>  apply inj_le in H
           | [H: Peano.gt ?X ?Y |- _] =>  apply inj_gt in H
           | [H: ge ?X ?Y |- _] =>  apply inj_ge in H
           | [H: Peano.lt ?X ?Y |- _] =>  apply inj_lt in H
           | [n: nat |- _] => extend (Zle_0_nat n)
         end.

(* need to repeat autorewrite below because rewritng rules such as inj_minus1 might
   depend on the results of other rewriting rules so that omega will succeed *)
Ltac nat_to_Z :=  nat_hyp_to_Z; repeat autorewrite with nat_to_Z in *.
Ltac nat_to_Z_in_goal :=  autorewrite with nat_to_Z.
Ltac nat_to_Z_in H :=  autorewrite with nat_to_Z in H.

(** convert Z to nat *)
Hint Rewrite <- Nat2Z.inj_add Nat2Z.inj_mul: Z_to_nat.
Hint Rewrite <- Nat2Z.inj_sub using omega : Z_to_nat.
Hint Rewrite <- Z_of_nat_0 Z_of_nat_1 : Z_to_nat.

Ltac Z_to_nat_in_goal := autorewrite with Z_to_nat.
Ltac Z_to_nat_in H := autorewrite with Z_to_nat in H.

(** convert positives to Z *)

(* check if P isn't a constant positive *)
Ltac notConstantPos P := 
  match P with
    | xI ?Q => notConstantPos Q
    | xO ?Q => notConstantPos Q
    | xH => fail 1
    | _ => idtac
  end.
    
(* convert "Zpos (p ~ 0)" to 2 * (Zpos x) and
   "Zpos (p ~ 1)" to 2 * (Zpos x) + 1, except when p = xH *)
Ltac pos_bits_to_Z :=
  repeat match goal with
    | [ |- context[(Zpos ?P ~ 0)%positive] ] => 
      notConstantPos P; rewrite (Pos2Z.inj_xO P)
    | [ H : context[(Zpos ?P ~ 0)%positive] |- _ ] =>
      notConstantPos P; rewrite (Pos2Z.inj_xO P) in H
    | [ |- context[(Zpos ?P ~ 1)%positive] ] => 
      notConstantPos P; rewrite (Pos2Z.inj_xI P)
    | [ H : context[(Zpos ?P ~ 1)%positive] |- _ ] => 
      notConstantPos P; rewrite (Pos2Z.inj_xI P) in H
  end.

(* Add hypothesis of the form "Z.pos P > 0" and "Z.neg P < 0" *)
Ltac pos_completer := 
  repeat match goal with
    | [H: context [Z.pos ?P] |- _ ] => 
      notConstantPos P; extend (Zgt_pos_0 P)
    | [|- context [Z.pos ?P]]  => 
      notConstantPos P; extend (Zgt_pos_0 P)
    | [H: context [Z.neg ?P] |- _ ] => 
      notConstantPos P; extend (Zlt_neg_0 P)
    | [|- context [Z.neg ?P]]  => 
      notConstantPos P; extend (Zlt_neg_0 P)
  end.

Ltac pos_to_Z := pos_bits_to_Z; pos_completer; autorewrite with pos_to_Z in *.

Hint Rewrite Zpos_plus_distr : pos_to_Z.

