(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

Require Bool.
Require Import ZArith.
Require Import Eqdep List.

Set Implicit Arguments.

Ltac bool_intro_tac :=
  repeat match goal with
           | [ |- andb ?b1 ?b2 = true ] =>
            apply Bool.andb_true_iff; split
         end.

Ltac bool_elim_tac :=
  repeat match goal with
           | [ H: andb ?b1 ?b2 = true |- _ ] => 
             apply andb_prop in H; destruct H
           | [ H: orb ?b1 ?b2 = true |- _ ] =>
             apply Bool.orb_true_iff in H; destruct H
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
      | [|- context[match ?X with nil => _ | cons _ _ => _ end]]
        => remember_rev X as name
      | [|- context[match ?X with Some _ => _ | None => _ end]]
        => remember_rev X as name
      | [|- context[match ?X with 0%Z => _ | Zpos _  | Zneg _ => _ end]]
        => remember_rev X as name
    end.

Tactic Notation "remember_destruct_head" "as" ident(name) :=
  remember_head as name; destruct name.

Tactic Notation "remember_head" "in" ident(H) "as" ident(name) := 
  let t := type of H in
    match t with
      | context[if ?X then _ else _] => remember_rev X as name
        (* the following matches let (_,_) := _ in _ *)
      | context[match ?X with (_, _)  => _ end] => remember_rev X as name
      | context[match ?X with nil => _ | cons _ _ => _ end]
        => remember_rev X as name
      | context[match ?X with Some _ => _ | None => _ end]
        => remember_rev X as name
      | context[match ?X with 0%Z => _ | Zpos _  | Zneg _ => _ end]
        => remember_rev X as name
    end.

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

(* Simplify hypothesis *)
Ltac simplHyp := 
  repeat match goal with 
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : _ <-> _ |- _] => destruct H
           | [ H : exists x, _ |- _ ] => destruct H
         end.

Ltac genSimpl := 
   match goal with 
     (* elimination of first-order constructors *)
     | [ |- _ /\ _ ] => split
     | [ H : _ /\ _ |- _ ] => destruct H
     | [ H : _ \/ _ |- _] => destruct H
     | [ H : _ <-> _ |- _] => destruct H
     | [ |- _ <-> _ ] => split
     | [ H : exists x, _ |- _ ] => destruct H
     | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => 
       generalize (inj_pair2 _ _ _ _ _ H); clear H
         
     (* using injection *)
     | [ H : ?F ?X = ?F ?Y |- _ ] => injection H;
       match goal with
         | [ |- F X = F Y -> _ ] => fail 1
         | [ |- _ = _ -> _ ] => try clear H; intros; try subst
       end
     | [ H : ?F _ _ = ?F _ _ |- _ ] => injection H;
       match goal with
         | [ |- _ = _ -> _ = _ -> _ ] => try clear H; intros; try subst
       end
       
     | _ => idtac
   end.

(* Note: directly using intuition will result in a slow tactic; since it is
   equivalent to "intuition auto with *", which means the auto with try lemmas
   in *all* hint databases *)

Ltac simtuition tac:= 
  simpl in *; intuition tac; try subst; 
    repeat (genSimpl; intuition tac; try subst); try congruence.

Ltac rewriter := 
  repeat (match goal with
            | [ H :  _ = _ |- _ ] => rewrite H
            | [ H : _ -> _ = _ |- _ ] => rewrite H; [ | solve [ simtuition ] ]
            | [ H : _ -> _ -> _ = _ |- _] =>
              rewrite H; [ | solve [ simtuition] | solve [ simtuition] ]
          end).

(* a generic prover *)
Ltac prover := 
  simtuition ltac:(auto with core arith zarith); rewriter; simtuition ltac:(auto with *).

Ltac appHyps f :=
  match goal with
    | [ H : _ |- _ ] => f H
  end.

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

(* The following tactics are from the book "Software Foundations"
   by Pierce, Casinghino and Greenberg *)

Require String. Open Scope string_scope.

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
