(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

Require Coqlib.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import ZArith.

Require ParserArg.
Import ParserArg.X86_PARSER_ARG.
Require Import Parser.
Require Import Bits.

Unset Automatic Introduction.
Set Implicit Arguments.
Open Scope char_scope.
Local Open Scope Z_scope.


Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.
(*Require ExtrOcamlNatInt.*)


Section Grammar1.

  Definition int_t := User_t Int_t.

  Definition byte_t := User_t Byte_t.

  Definition map t1 t2 (p:grammar t1) (f:interp t1 -> interp t2) : grammar t2 := 
    @Map t1 t2 f p.
  Implicit Arguments map [t1 t2].

  Definition seq t1 t2 (p1:grammar t1) (p2:grammar t2) : grammar (Pair_t t1 t2) := 
    Cat p1 p2.

  Definition alt t (p1 p2:grammar t) : grammar t := 
    Map _ (fun (x:interp (Sum_t t t)) => match x with inl a => a | inr b => b end) 
        (Alt p1 p2).

  Infix "$" := seq (right associativity, at level 70).
  Infix "@" := map (right associativity, at level 75).
  Infix "|+|" := alt (right associativity, at level 80).
  Notation "e %% t" := (e : interp t) (at level 80).

  Fixpoint bits_n (n:nat) : type := 
    match n with 
      | 0%nat => Unit_t
      | S n => Pair_t Char_t (bits_n n)
    end.

  Fixpoint bits (x:string) : grammar (bits_n (String.length x)) := 
    match x with 
      | EmptyString => Eps
      | String c s => 
        (Cat (Char (if ascii_dec c "0"%char then false else true)) (bits s))
    end.

  Fixpoint bits2Z(n:nat)(a:Z) : interp (bits_n n) -> interp int_t := 
    match n with 
      | 0%nat => fun _ => a
      | S n => fun p => bits2Z n (2*a + (if (fst p) then 1 else 0)) (snd p)
    end.

  Fixpoint field'(n:nat) : grammar (bits_n n) := 
    match n with 
      | 0%nat => Eps
      | S n => Cat Any (field' n)
    end.

  Definition bits2int(n:nat)(bs:interp (bits_n n)) : interp int_t := bits2Z n 0 bs.

  Definition field(n:nat) := (field' n) @ (bits2int n).
  Definition byte := (field 8) @ (@Word.repr 7 : _ -> interp byte_t).

  Definition listint_t := List_t (User_t Int_t).

  (* g_n consumes 2^n bytes and has 2^(2^n) cases *)
  Definition g0 := (bits "11111110" |+| bits "11111111")
                     @ (fun v => (bits2int 8 v) :: nil %% listint_t).
  Definition g1 := (g0 $ g0) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g2 := (g1 $ g1) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g3 := (g2 $ g2) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g4 := (g3 $ g3) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g5 := (g4 $ g4) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g6 := (g5 $ g5) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g7 := (g6 $ g6) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g8 := (g7 $ g7) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g9 := (g8 $ g8) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g10 := (g9 $ g9) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g11 := (g10 $ g10) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g12 := (g11 $ g11) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g13 := (g12 $ g12) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g14 := (g13 $ g13) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g15 := (g14 $ g14) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g16 := (g15 $ g15) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g17 := (g16 $ g16) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g18 := (g17 $ g17) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g19 := (g18 $ g18) @ (fun p => app (fst p) (snd p) %% listint_t).
  Definition g20 := (g19 $ g19) @ (fun p => app (fst p) (snd p) %% listint_t).

(* prefix_n consumes 2^n 0xff bytes *)
Definition prefix0 := bits "11111111" @ (fun v => (bits2int 8 v) :: nil %% listint_t).
Definition prefix1 := (prefix0 $ prefix0) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition prefix2 := (prefix1 $ prefix1) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition prefix3 := (prefix2 $ prefix2) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition prefix4 := (prefix3 $ prefix3) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition prefix5 := (prefix4 $ prefix4) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition prefix6 := (prefix5 $ prefix5) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition prefix7 := (prefix6 $ prefix6) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition prefix8 := (prefix7 $ prefix7) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition prefix9 := (prefix8 $ prefix8) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition prefix10 := (prefix9 $ prefix9) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition prefix11 := (prefix10 $ prefix10) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition prefix12 := (prefix11 $ prefix11) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition prefix13 := (prefix12 $ prefix12) @ (fun p => app (fst p) (snd p) %% listint_t).

Fixpoint perm (l:list (grammar listint_t)) : list (grammar listint_t) := 
  match l with
    | nil => nil
    | h::t =>
      ((bits "11111111" $ h) @ (fun p => (bits2int 8 (fst p) :: snd p) %% listint_t)) ::
      ((bits "11111110" $ h) @ (fun p => (bits2int 8 (fst p) :: snd p) %% listint_t)) ::
      perm t
  end.

(* p_n consumes n bytes, each byte can be a 0xff or a 0xfe *)
Definition p0 := (Eps @ (fun _ => nil %% listint_t)) :: nil.
Definition p1 := perm p0.
Definition p2 := perm p1.
Definition p3 := perm p2.
Definition p4 := perm p3.
Definition p5 := perm p4.
Definition p6 := perm p5.
Definition p7 := perm p6.
Definition p8 := perm p7.
Definition p9 := perm p8.
Definition p10 := perm p9.
Definition p11 := perm p10.
Definition p12 := perm p11.
Definition p13 := perm p12.

  Definition never t : grammar t := Zero t.

  Fixpoint alts0 t (ps:list (grammar t)) : grammar t := 
    match ps with 
      | nil => @never t
      | p::nil => p
      | p::rest => alt p (alts0 rest)
    end.

  Fixpoint half A (xs ys zs: list A) : (list A) * (list A) := 
    match xs with 
      | nil => (ys,zs) 
      | h::t => half t zs (h::ys)
    end.

  Fixpoint alts' n t (ps:list (grammar t)) : grammar t := 
    match n, ps with 
      | 0%nat, _ => alts0 ps
      | S n, nil => @never t
      | S n, p::nil => p
      | S n, ps => 
        let (ps1,ps2) := half ps nil nil in 
          let g1 := alts' n ps1 in 
            let g2 := alts' n ps2 in 
              alt g1 g2
    end.

  Definition alts t (ps:list (grammar t)) : grammar t := alts' 20 ps.


Definition a0 := (prefix0 $ alts p0) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition a1 := (prefix1 $ alts p1) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition a2 := (prefix2 $ alts p2) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition a3 := (prefix3 $ alts p3) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition a4 := (prefix4 $ alts p4) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition a5 := (prefix5 $ alts p5) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition a6 := (prefix6 $ alts p6) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition a7 := (prefix7 $ alts p7) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition a8 := (prefix8 $ alts p8) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition a9 := (prefix9 $ alts p9) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition a10 := (prefix10 $ alts p10) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition a11 := (prefix11 $ alts p11) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition a12 := (prefix12 $ alts p12) @ (fun p => app (fst p) (snd p) %% listint_t).
Definition a13 := (prefix13 $ alts p13) @ (fun p => app (fst p) (snd p) %% listint_t).

End Grammar1.








(* Module TEST_PARSER_ARG. *)
(*   Definition char_p := bool. *)
(*   Definition char_eq := Bool.bool_dec. *)

(*   Inductive type : Set :=  *)
(*   | Int_t : type. *)

(*   Definition tipe := type. *)
(*   Definition tipe_eq : forall (t1 t2:tipe), {t1=t2} + {t1<>t2}. *)
(*     intros ; decide equality. *)
(*   Defined. *)
(*   Definition tipe_m (t:tipe) :=  *)
(*     match t with  *)
(*       | Int_t => nat *)
(*     end. *)
(* End TEST_PARSER_ARG. *)

(* Module TEST_PARSER. *)
(* Module T := Parser.Parser(TEST_PARSER_ARG). *)
(* Import TEST_PARSER_ARG. *)
(* Import T. *)
(* Infix "|+|" := Alt_p (right associativity, at level 80). *)
(* Infix "$" := Cat_p (right associativity, at level 70). *)
(* Definition map_p t1 t2 (p:parser t1) (f:result_m t1 -> result_m t2) := @Map_p t1 t2 f p. *)
(* Implicit Arguments map_p [t1 t2]. *)
(* Infix "@" := map_p (right associativity, at level 75). *)
(* Definition Plus_p t (p:parser t) :=  *)
(*   (Cat_p p (Star_p p)) @ (fun p => ((fst p)::(snd p)): result_m (list_t t)). *)
(* Definition Alts_p t (ps:list (parser t)) :=  *)
(*   List.fold_right (@Alt_p t) (Zero_p t) ps. *)
(* Definition int_t := tipe_t Int_t. *)
(* Notation "e %% t" := (e : result_m t) (at level 80). *)

(* Definition one := Char_p true @ (fun _ => 1 %% int_t). *)
(* Definition zero := Char_p false @ (fun _ => 0 %% int_t). *)
(* Definition bit' := zero |+| one. *)
(* Definition bit := Any_p @ (fun c => (if c then 1 else 0) %% int_t). *)
(* Definition nibble :=  *)
(*   bit $ bit $ bit $ bit @  *)
(*   (fun x => match x with  *)
(*               | (b3,(b2,(b1,b0))) => b0 + 2*b1 + 4*b2 + 8*b3 *)
(*             end %% int_t). *)
(* Definition byte :=  *)
(*   nibble $ nibble @ (fun p => (snd p + (fst p)*256) %% int_t). *)

(* (* is a parser deterministic for strings up to length n?  *)
(* Definition is_deterministic t (p:parser t) n :=  *)
(*   is_determ (snd (parser2regexp p)) 2 (fun n => (match n with 0 => false | _ => true end)::nil) n *)
(*   (fst (parser2regexp p)) (p2r_wf p _). *)

(* Lemma is_deterministic_byte : is_deterministic byte 8 = true. *)
(* Proof. *)
(*   auto. *)
(* Qed. *)

(* Definition ambiguous_p := nibble |+| nibble. *)

(* Lemma is_deterministic_ambiguous_p : is_deterministic ambiguous_p 4 = false. *)
(* Proof. *)
(*   auto. *)
(* Qed. *)
(* *) *)
(* Fixpoint explode(s:string) : list bool :=  *)
(*   match s with  *)
(*     | ""%string => nil *)
(*     | String "0" t => false::(explode t) *)
(*     | String _ t => true::(explode t) *)
(*   end. *)

(* Definition lex t (p:parser t) s := parse p (explode s). *)

(* (* *)
(* Opaque result_m. *)
(* Opaque p2r_wf. *)
(* Opaque wf_derivs. *)
(* *) *)
(* Eval simpl in lex (nibble) "011".  *)
(* Eval simpl in explode("1000111"). *)
(* Eval simpl in nibble 1. *)
(* End TEST_PARSER. *)

  

