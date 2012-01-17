(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

Require Coqlib.
Require Import Parser.
Require Import Ascii.
Require Import String.
Require Import List.
Unset Automatic Introduction.
Set Implicit Arguments.
Open Scope char_scope.


Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.
(*Require ExtrOcamlNatInt.*)

Module TEST_PARSER_ARG.
  Definition char_p := bool.
  Definition char_eq := Bool.bool_dec.

  Inductive type : Set := 
  | Int_t : type.

  Definition tipe := type.
  Definition tipe_eq : forall (t1 t2:tipe), {t1=t2} + {t1<>t2}.
    intros ; decide equality.
  Defined.
  Definition tipe_m (t:tipe) := 
    match t with 
      | Int_t => nat
    end.
End TEST_PARSER_ARG.

Module TEST_PARSER.
Module T := Parser.Parser(TEST_PARSER_ARG).
Import TEST_PARSER_ARG.
Import T.
Infix "|+|" := Alt_p (right associativity, at level 80).
Infix "$" := Cat_p (right associativity, at level 70).
Definition map_p t1 t2 (p:parser t1) (f:result_m t1 -> result_m t2) := @Map_p t1 t2 f p.
Implicit Arguments map_p [t1 t2].
Infix "@" := map_p (right associativity, at level 75).
Definition Plus_p t (p:parser t) := 
  (Cat_p p (Star_p p)) @ (fun p => ((fst p)::(snd p)): result_m (list_t t)).
Definition Alts_p t (ps:list (parser t)) := 
  List.fold_right (@Alt_p t) (Zero_p t) ps.
Definition int_t := tipe_t Int_t.
Notation "e %% t" := (e : result_m t) (at level 80).

Definition one := Char_p true @ (fun _ => 1 %% int_t).
Definition zero := Char_p false @ (fun _ => 0 %% int_t).
Definition bit' := zero |+| one.
Definition bit := Any_p @ (fun c => (if c then 1 else 0) %% int_t).
Definition nibble := 
  bit $ bit $ bit $ bit @ 
  (fun x => match x with 
              | (b3,(b2,(b1,b0))) => b0 + 2*b1 + 4*b2 + 8*b3
            end %% int_t).
Definition byte := 
  nibble $ nibble @ (fun p => (snd p + (fst p)*256) %% int_t).

(* is a parser deterministic for strings up to length n? *)
Definition is_deterministic t (p:parser t) n := 
  is_determ (snd (parser2regexp p)) 2 (fun n => (match n with 0 => false | _ => true end)::nil) n
  (fst (parser2regexp p)) (p2r_wf p _).

Lemma is_deterministic_byte : is_deterministic byte 8 = true.
Proof.
  auto.
Qed.

Definition ambiguous_p := nibble |+| nibble.

Lemma is_deterministic_ambiguous_p : is_deterministic ambiguous_p 4 = false.
Proof.
  auto.
Qed.

Fixpoint explode(s:string) : list bool := 
  match s with 
    | ""%string => nil
    | String "0" t => false::(explode t)
    | String _ t => true::(explode t)
  end.

Definition lex t (p:parser t) s := parse p (explode s).

(*
Opaque result_m.
Opaque p2r_wf.
Opaque wf_derivs.
Eval compute in lex (nibble) "0101". *)
End TEST_PARSER.

  

