(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

Require Import Coqlib.
Require Import List.
Set Implicit Arguments.

Class Monad(M:Type->Type) : Type := {
  Return : forall (A:Type), A -> M A ; 
  Bind : forall (A B:Type), M A -> (A -> M B) -> M B ; 
  ret_left_unit : forall A B (x:A) (f:A -> M B), Bind (Return x) f = f x ; 
  ret_right_unit : forall A (c:M A), Bind c (@Return _) = c ; 
  bind_assoc : forall A B C (f:M A) (g:A -> M B) (h:B -> M C), 
    Bind (Bind f g) h = Bind f (fun x => Bind (g x) h)
}.

Notation "'ret' x" := (Return x) (at level 75) : monad_scope.
Notation "x <- c1 ; c2" := (Bind _ c1 (fun x => c2)) 
  (right associativity, at level 84, c1 at next level) : monad_scope.
Notation "c1 ;; c2" := (Bind _ c1 (fun _ => c2))
  (right associativity, at level 84) : monad_scope.
Notation "[ x , y ] <- c1 ; c2" := 
  (Bind _ c1 (fun v => match v with | (x,y) => c2 end)) 
  (right associativity, at level 84) : monad_scope.

Instance OptionMonad : Monad option := { 
  Return := fun A x => Some x ; 
  Bind := fun A B c f => match c with | None => None | Some v => f v end 
}.
auto. destruct c ; auto. intros. destruct f ; auto.
Defined.

Definition ST(S A:Type) := S -> S * A.

Instance StateMonad(S:Type) : Monad (ST S) := { 
  Return := fun A x s => (s,x) ; 
  Bind := fun A B c f s => match c s with | (s',x) => f x s' end
}.
 intros. apply extensionality ; auto. 
 intros. apply extensionality. intro. destruct (c x) ; auto.
 intros. apply extensionality ; auto. intros. destruct (f x) ; auto.
Defined.

Instance ListMonad : Monad list := { 
  Return := fun A x => x::nil ; 
  Bind := fun A B c f => list_flatten (map f c)
}.
  intros. simpl. rewrite app_nil_end. auto.
  intros. induction c ; auto. simpl. rewrite IHc ; auto.
  intros. induction f ; auto. simpl. rewrite map_app. 
  rewrite <- flatten_distr. rewrite IHf. auto.
Defined.

