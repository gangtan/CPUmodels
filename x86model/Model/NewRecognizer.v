(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

(** * DFA Construction *)
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
Require Import List.
Require Import Arith.
Require Import Bool.
Require Import Eqdep.
Require Import Parser.
Import X86_PARSER_ARG.
Set Implicit Arguments.
Unset Automatic Introduction.

Require Import CommonTacs.

(** In this section, we build a table-driven DFA recognizer for a [grammar].  
    This is very similar to the table-driven parser we build in Parser.v 
    except we don't need any semantic actions.  In essence, we just translate
    the grammar to an [astgram] (and throw away the semantic action function),
    then build a DFA structure very similar to, but much simpler than, the 
    DFA structure constructed in Parser.v.  In particular, what we build is:
        - A list of states which are really derivatives of the original astgram.
          The position of the astgram determines an identity (i.e., index) for the 
          state.  The initial astgram is always at position 0.  
        - A transition table as a list of list of nats.  If [T(i,j) = k], then 
          this says that in state [i], if we see an input list of characters 
          corresponding to the [token_id] [j], then we can transition to state [k].
          Obviously, [i] and [k] should be indexes of astgrams in the
          list of [states].  Furthermore, it should be that [states(k)] is the
          derivative of [states(i)] with respect to the token_id [j].
        - An accept table as a list of booleans.  [dfa_accepts(i) = true] iff 
          [states(i)] accepts the empty string.
        - A reject table as a list of booleans.  [dfa_rejects(i) = true] iff
          [states(i)] rejects all strings.

    It may be worth rewriting this to use the table construction (and proofs) 
    we already have in Parser.v.  For instance, we could take the Parser DFA
    structure and erase the stuff we don't need.  But it was simpler for now
    to just take the old code and adapt it to the new environment.  
*)


Require Import Coq.Structures.OrdersAlt.
Require Import Coq.MSets.MSetAVL.
Require Import Coq.MSets.MSetProperties.
(* Require Import Coq.MSets.MSetFacts. *)

(* astgram is essentially the syntax of regexps *)
Definition regexp := astgram.


(** * Ordering for regexps *)

(** Use lexicographic ordering when ordering two regexps. *)
Fixpoint compare_re (r1 r2:regexp) : comparison := 
  match r1 with
    | aEps => match r2 with
                | aEps => Eq
                | _ => Lt
              end
    | aZero => match r2 with
                 | aEps => Gt
                 | aZero => Eq
                 | _ => Lt
               end
    | aChar c1 => 
      match r2 with
        | aEps | aZero => Gt
        (* todo: the following uses the fact that char_p = bool;
                      we should paramatrize an OrderedType char_p in the parser *)
        | aChar c2 => 
          match c1, c2 with
            | true, true | false, false => Eq
            | true, false => Lt
            | false, true => Gt
          end
        | _ => Lt
      end
    | aAny => match r2 with
                | aEps | aZero | aChar _ => Gt
                | aAny => Eq
                | _ => Lt
              end
    | aCat r11 r12 =>
      match r2 with
        | aEps | aZero | aChar _ | aAny => Gt
        | aCat r21 r22 =>
          let cp := compare_re r11 r21 in
          match cp with
            | Eq => compare_re r12 r22
            | _ => cp
          end
        | _ => Lt
      end
    | aAlt r11 r12 =>
      match r2 with
        | aEps | aZero | aChar _ | aAny | aCat _ _ => Gt
        | aAlt r21 r22 =>
          let cp := compare_re r11 r21 in
          match cp with
            | Eq => compare_re r12 r22
            | _ => cp
          end
        | _ => Lt
      end
    | aStar r11 => 
      match r2 with
        | aEps | aZero | aChar _ | aAny | aCat _ _ | aAlt _ _ => Gt
        | aStar r21 => compare_re r11 r21
      end
  end.

Lemma compare_re_eq_leibniz: 
  forall r1 r2, compare_re r1 r2 = Eq -> r1 = r2.
Proof. induction r1; try (destruct r2; simpl; congruence; fail). 
       Case "aChar".
       destruct r2; simpl; try congruence. 
       destruct c; destruct c0; congruence.
       Case "aCat".
       destruct r2; simpl; try congruence.
       remember_rev (compare_re r1_1 r2_1) as cmp.
       destruct cmp; crush_hyp.
       Case "aAlt".
       destruct r2; simpl; try congruence.
       remember_rev (compare_re r1_1 r2_1) as cmp.
       destruct cmp; crush_hyp.
       Case "aStar".
       destruct r2; simpl; try congruence.
       crush_hyp.
Qed.

Module REOrderedTypeAlt <: OrderedTypeAlt.
  Definition t:=regexp.
  Definition compare := compare_re.

  Lemma compare_sym : forall r1 r2, compare r2 r1 = CompOpp (compare r1 r2).
  Proof. induction r1; try (destruct r2; trivial; fail).
    Case "aChar".
      destruct r2; trivial. destruct c0, c; trivial.
    Case "aCat".
      destruct r2; trivial. simpl.
        rewrite (IHr1_1 r2_1). destruct (compare r1_1 r2_1); simpl; eauto.
    Case "aAlt".
      destruct r2; trivial. simpl.
        rewrite (IHr1_1 r2_1). destruct (compare r1_1 r2_1); simpl; eauto.
    Case "aStar".
      destruct r2; trivial. simpl. eauto.
  Qed.

  Lemma compare_trans:
    forall cmp r1 r2 r3,
      compare r1 r2 = cmp -> compare r2 r3 = cmp -> compare r1 r3 = cmp.
  Proof. intros cmp r1. generalize cmp.
    induction r1;
    try (destruct r2; destruct r3; simpl; congruence; fail).
    Local Ltac trans_simp :=
      match goal with
        | [H:compare ?R1 ?R2 = Eq |- _] => 
          apply compare_re_eq_leibniz in H; subst R2
      end.
    Case "aChar".
      destruct r2; destruct r3; simpl; try congruence.
      destruct c; destruct c0; destruct c1; try congruence.
    Case "aCat".
      destruct r2; destruct r3; simpl; try congruence.
      remember_rev (compare r1_1 r2_1) as cmp1.
      remember_rev (compare r2_1 r3_1) as cmp2.
      destruct cmp1; destruct cmp2; 
        try (repeat trans_simp; crush; fail).
        assert (H10:compare r1_1 r3_1 = Eq) by eauto.
        rewrite H10. eauto.
        assert (H10:compare r1_1 r3_1 = Lt) by eauto.
        rewrite H10. eauto.
        assert (H10:compare r1_1 r3_1 = Gt) by eauto.
        rewrite H10. eauto.
    Case "aAlt".
      destruct r2; destruct r3; simpl; try congruence.
      remember_rev (compare r1_1 r2_1) as cmp1.
      remember_rev (compare r2_1 r3_1) as cmp2.
      destruct cmp1; destruct cmp2; 
        try (repeat trans_simp; crush; fail).
        assert (H10:compare r1_1 r3_1 = Eq) by eauto.
        rewrite H10. eauto.
        assert (H10:compare r1_1 r3_1 = Lt) by eauto.
        rewrite H10. eauto.
        assert (H10:compare r1_1 r3_1 = Gt) by eauto.
        rewrite H10. eauto.
    Case "aStar".  
      destruct r2; destruct r3; simpl; (congruence || eauto).
  Qed.

End REOrderedTypeAlt.

Module REOrderedType := OT_from_Alt REOrderedTypeAlt.

Lemma InA_regexp_eq_In: 
  forall x l, InA REOrderedType.eq x l -> In x l.
Proof. intros. apply InA_alt in H. 
  sim. apply compare_re_eq_leibniz in H. congruence.
Qed.

(** * Define [RESet], a set of regexps *)

(** A set of regexps *)
Module RESet :=  MSetAVL.Make REOrderedType.
Module RESetP := MSetProperties.Properties RESet.

Local Ltac re_set_simpl :=
  repeat 
    (simpl in *;
     match goal with
       | [H:RESet.In _ RESet.empty |- _] =>
         apply RESetP.Dec.F.empty_iff in H; contradict H
       | [H:REOrderedTypeAlt.compare _ _ = Eq |- _] =>
         apply compare_re_eq_leibniz in H; subst
       | [H:RESet.In _ (RESet.singleton _) |- _] =>
         apply RESetP.Dec.F.singleton_iff in H;
         apply compare_re_eq_leibniz in H; subst
     end).

Definition re_set_map (f:RESet.elt -> RESet.elt) (s:RESet.t) : RESet.t :=
  RESet.fold 
    (fun (r:regexp) (news:RESet.t) => RESet.add (f r) news)
    s RESet.empty.

Lemma add_cardinal_ineq : 
  forall x s, 
    RESet.cardinal s 
    <= RESet.cardinal (RESet.add x s) 
    <= S (RESet.cardinal s).
Proof. intros.
  destruct (RESetP.In_dec x s).
    use_lemma RESetP.add_cardinal_1 by eassumption. omega.
    use_lemma RESetP.add_cardinal_2 by eassumption. omega.
Qed.

(** ** Lemmas abot re_set_map *)

Lemma re_set_map_cardinal: 
  forall f s, RESet.cardinal (re_set_map f s) <= RESet.cardinal s.
Proof. unfold re_set_map. intros. 
  rewrite RESetP.fold_spec_right.
  rewrite (RESet.cardinal_spec s).
  rewrite <- (rev_length (RESet.elements s)).
  remember (rev (RESet.elements s)) as l. clear Heql.
  induction l.
  Case "l0=nil". simpl. trivial.
  Case "cons". simpl. 
    eapply le_trans.
    apply add_cardinal_ineq.
    apply le_n_S. assumption.
Qed.

Lemma re_set_map_intro_helper : forall (x y:RESet.elt) f (s:RESet.t),
  List.In y (rev (RESet.elements s)) -> x = f y
    -> RESet.In x (re_set_map f s).
Proof. unfold re_set_map. intros.
  rewrite RESetP.fold_spec_right.
  induction (rev (RESet.elements s)).
  Case "nil". simpl in *. crush.
  Case "a cons l". destruct H.
    SCase "y=a". simpl. 
      apply RESetP.FM.add_1. 
      subst. apply REOrderedType.eq_equiv.
    SCase "y in l". simpl. apply RESetP.FM.add_2.
      crush.
Qed.

Lemma re_set_map_intro : forall (x y:RESet.elt) f (s:RESet.t),
  RESet.In y s -> x = f y -> RESet.In x (re_set_map f s).
Proof. intros. eapply re_set_map_intro_helper; try eassumption.
  rewrite <- in_rev.
  apply RESetP.FM.elements_iff in H.
  auto using InA_regexp_eq_In.
Qed.

Lemma re_set_map_elim_helper : forall (x:RESet.elt) f (s:RESet.t),
  RESet.In x (re_set_map f s)
    -> exists y, List.In y (rev (RESet.elements s)) /\ x = f y.
Proof.  unfold re_set_map. intros.
  rewrite RESetP.fold_spec_right in H.
  induction (rev (RESet.elements s)).
  Case "nil". simpl in *. re_set_simpl.
  Case "a::l". simpl in *.
    apply RESetP.Dec.F.add_iff in H.
    destruct H.
    SCase "(f a) = x". re_set_simpl. eauto.
    SCase "x in the rest".
      apply IHl in H. crush.
Qed.
      
Lemma re_set_map_elim : forall (x:RESet.elt) f (s:RESet.t),
  RESet.In x (re_set_map f s)
    -> exists y, RESet.In y s /\ x = f y.
Proof. intros. apply re_set_map_elim_helper in H.
  destruct H as [y [H2 H4]].
  rewrite <- in_rev in H2. 
  (* rewrite <- RESet.elements_spec1 in H2. *)
  apply (In_InA REOrderedType.eq_equiv) in H2.
  apply RESet.elements_spec1 in H2.
  eauto.
Qed.

Lemma re_set_map_subset : forall f s1 s2 ,
  RESet.Subset s1 s2
    -> RESet.Subset (re_set_map f s1) (re_set_map f s2).
Proof.  intros. unfold RESet.Subset. intros.
  apply re_set_map_elim in H0. sim.
  eauto using re_set_map_intro.
Qed.

(** * The notion of prebase of a regexp and partial-derivative sets.

  The relation between prebases and partial derivative sets are in the
  paper "From Mirkin's prebases to Antimirov's Word Partial Derivatives"
  by Champarnaud and Ziadi.  *)

(** Concat regexp r to the right of every regexp in a regexp set *)
Definition set_cat_re (s:RESet.t) (r:regexp): RESet.t := 
  match r with
    | aEps => s (* not stricitly necessary; an optimization *)
    | aZero => RESet.empty
    | _ => re_set_map (fun r1 => aCat r1 r) s
  end.
Notation "s $ r" := (set_cat_re s r) (at level 60, no associativity).

(** Prebase of a regexp:
    prebase(zero) = {} 
    prebase(epsilon) = {} 
    prebase(a) = {epsilon}, for a in the alphabet
    prebase(r1+r2) = prebase(r1) \/ prebase(r2)
    prebase(r1 r2) = prebase(r1)r2 \/ prebase(r2)
    prebase(r_star) = prebase(r)r_star 
*)
Fixpoint prebase (r:regexp): RESet.t := 
  match r with
    | aEps | aZero => RESet.empty
    | aChar _ | aAny => RESet.singleton aEps
    | aCat r1 r2 => RESet.union ((prebase r1) $ r2) (prebase r2)
    | aAlt r1 r2 => RESet.union (prebase r1) (prebase r2)
    | aStar r1 => (prebase r1) $ (aStar r1)
  end.

(** The set of possible partial derivatives*)
Definition pdset (r:regexp): RESet.t := RESet.add r (prebase r).

(** Number of symbols in a regexp:
    |zero| = |epsilon| = 0
    |a| = 1 
    |r1 + r2| = |r1| + |r2|
    |r1 r2| = |r1| + |r2|
    |r*| = |r| *)
Fixpoint num_of_syms (r: regexp): nat := 
  match r with
    | aEps | aZero => 0
    | aChar _ => 1 
    (* Since aAny is (aChar c1 + aChar c2 + ...), it appears it should
       return n in this case, where n is the number of chars in the alphabet;
       however, return 1 in this case seems fine; that is, prebase_upper_bound
       can still be proved *)
    | aAny => 1 
    | aCat r1 r2 | aAlt r1 r2 => num_of_syms r1 + num_of_syms r2
    | aStar r => num_of_syms r
  end.

(** ** Lemmas about set_cat_re *)

Lemma set_cat_re_intro1 : forall r s r2,
  RESet.In r s -> r2 = aEps -> RESet.In r (s $ r2).
Proof. crush. Qed.

Lemma set_cat_re_intro2 : forall r s r1 r2,
  RESet.In r1 s -> r = aCat r1 r2 -> r2 <> aEps -> r2 <> aZero
    -> RESet.In r (s $ r2).
Proof. destruct r2; 
  (congruence || simpl; intros; eapply re_set_map_intro; eassumption).
Qed.

Lemma set_cat_re_elim : forall r s r2,
  RESet.In r (s $ r2) -> 
    (r2=aEps /\ RESet.In r s) \/
    (r2=aZero /\ False) \/
    (r2<>aEps /\ r2<>aZero /\ exists r1, RESet.In r1 s /\ r = aCat r1 r2).
Proof. intros. destruct r2; 
  try (right; right; simpl in H; 
       apply re_set_map_elim in H; destruct H as [y [H2 H4]]; 
       eexists; crush).
  Case "r2=aEps". left. auto.
  Case "r2=aZero". right; left. simpl in *. re_set_simpl.
Qed.

Lemma set_cat_re_cardinal: 
  forall s r, RESet.cardinal (s $ r) <= RESet.cardinal s.
Proof. unfold set_cat_re. 
  destruct r; auto using re_set_map_cardinal.
  Case "aZero".
    repeat rewrite RESet.cardinal_spec. simpl.
    auto using le_0_n.
Qed.

Lemma set_cat_re_subset : forall s1 s2 r,
  RESet.Subset s1 s2 -> RESet.Subset (s1 $ r) (s2 $ r).
Proof. destruct r; simpl; intros; try (auto using re_set_map_subset).
  trivial.
  apply RESetP.subset_refl.
Qed.  

(** ** Lemmas about prebase *)

Lemma prebase_upper_bound : 
  forall r, RESet.cardinal (prebase r) <= num_of_syms r.
Proof. induction r; try (simpl; trivial).
  Case "aCat". 
    generalize
      (RESetP.union_cardinal_le (prebase r1 $ r2) (prebase r2)).
    generalize (set_cat_re_cardinal (prebase r1) r2).
    omega.
  Case "aAlt". 
    generalize
      (RESetP.union_cardinal_le (prebase r1) (prebase r2)).
    omega.
  Case "aStar". 
    generalize (set_cat_re_cardinal (prebase r) (aStar r)). crush.
Qed. 

Lemma prebase_trans :
  forall r1 r2 r3, 
    RESet.In r2 (prebase r1) -> RESet.In r3 (prebase r2) 
      -> RESet.In r3 (prebase r1).
Proof. induction r1; try (simpl; intros; re_set_simpl; fail).
  Case "aCat". simpl. intros.
    apply RESet.union_spec in H; destruct H.
    SCase "r2 in (prebase r1_1 $ r1_2)".
      apply set_cat_re_elim in H; destruct H as [|[|]]; 
        try (apply RESetP.FM.union_2; crush; fail).
      SSCase "r1_2<>eps and r1_2<>zero". sim. subst. simpl in *.
        apply RESetP.FM.union_1 in H0.
        destruct H0.
        SSSCase "r3 in prebase _ $ r1_2".
          apply set_cat_re_elim in H0; 
            destruct H0 as [|[|]]; try crush.
          apply RESetP.FM.union_2.
          assert (RESet.In x0 (prebase r1_1)). crush.
          eapply set_cat_re_intro2; try eassumption. trivial.
        SSSCase "r3 in prebase r1_2".
          apply RESetP.FM.union_3. crush.
    SCase "r2 in prebase(r1_2)".
      apply RESetP.FM.union_3. crush.
  Case "aAlt". simpl; intros.
    apply RESet.union_spec in H; destruct H.
      apply RESetP.FM.union_2; crush.
      apply RESetP.FM.union_3; crush.
  Case "aStar". simpl; intros.
    apply re_set_map_elim in H; sim; subst.
    simpl in H0.
    apply RESet.union_spec in H0; destruct H0.
    SCase "r3 in (prebase x) $ (r1*)".
      apply re_set_map_elim in H0; sim; subst.
      assert (RESet.In x0 (prebase r1)) by crush.
      eapply re_set_map_intro; crush.
    SCase "r3 in (prebase r1) $ (r1*)".
      apply re_set_map_elim in H0; sim; subst.
      assert (RESet.In x0 (prebase r1)) by crush.
      eapply re_set_map_intro; crush.
Qed.

(** ** Lemmas about pdset *)

Lemma pdset_upper_bound : 
  forall r, RESet.cardinal (pdset r) <= S (num_of_syms r).
Proof. unfold pdset. intros.
  generalize (prebase_upper_bound r); intros.
  destruct (RESetP.In_dec r (prebase r)).
    use_lemma RESetP.add_cardinal_1 by eassumption. omega.
    use_lemma RESetP.add_cardinal_2 by eassumption. omega.
Qed.

Lemma pdset_trans : forall r1 r2 r3, 
    RESet.In r2 (pdset r1) -> RESet.In r3 (pdset r2)
      -> RESet.In r3 (pdset r1).
Proof. unfold pdset; intros.
  apply RESet.add_spec in H; apply RESet.add_spec in H0.
  destruct H; destruct H0; re_set_simpl.
    apply RESetP.FM.add_1; apply REOrderedType.eq_equiv.
    apply RESetP.FM.add_2; assumption.
    apply RESetP.FM.add_2; assumption.
    apply RESetP.FM.add_2. eauto using prebase_trans.
Qed.

(** * Definition the notion of partial derivatives.

    Partial derivatives are introduced in "Partial derivatives of regular
    expressions and finite automata construction" by Antimirov. *)

(** Nullable (r) returns true iff r can match the empty string *)
Fixpoint nullable (r:regexp) : bool := 
  match r with
    | aZero | aChar _ | aAny => false
    | aEps => true
    | aCat r1 r2 => nullable r1 && nullable r2
    | aAlt r1 r2 => nullable r1 || nullable r2
    | aStar r1 => true
  end.

(** Partial derivatives:
  pdrv(a, void) = pdrv(a, epsilon) = {}
  pdrv(a, b) = if a=b then {epsilon} else {}
  pdrv(a, r1+r2) = pdrv(a,r1) \/ pdrv(a,r2)
  pdrv(a, r1 r2) =
    pdrv(a, r1)r2 \/ pdrv(a, r2),   if nullable(r1)
    pdrv(a, r1)r2, otherwise
  pdrv(a, r_star) = pdrv(a,r)r_star
*)
Fixpoint pdrv (a: char_p) (r:regexp) : RESet.t := 
  match r with
    | aZero | aEps => RESet.empty
    | aChar b => 
      if char_dec a b then RESet.singleton aEps else RESet.empty
    | aAny => RESet.singleton aEps
    | aCat r1 r2 => 
      if nullable r1 then RESet.union ((pdrv a r1) $ r2) (pdrv a r2)
      else (pdrv a r1) $ r2
    | aAlt r1 r2 => RESet.union (pdrv a r1) (pdrv a r2)
    | aStar r1 => (pdrv a r1) $ (aStar r1)
  end.

Lemma pdrv_subset_prebase: 
  forall a r, RESet.Subset (pdrv a r) (prebase r).
Proof. induction r; simpl; try (apply RESetP.subset_refl).
  Case "aChar". 
    destruct_head; [apply RESetP.subset_refl | apply RESetP.subset_empty].
  Case "aCat".
    destruct_head.
      apply RESetP.FM.union_s_m. auto using set_cat_re_subset.
        trivial.
      eapply RESetP.FM.Subset_trans. 
        eapply set_cat_re_subset. eassumption.
      apply RESetP.union_subset_1.        
  Case "aAlt". apply RESetP.FM.union_s_m; assumption.
  Case "aStar". apply re_set_map_subset. assumption.
Qed.


(* NEXT: prove the correctness of partial derivatives;
  (1) define in_regexp for the seamntics of regexps
      [[eps]] = {epsilon}
      [[zero]] = {}
      [[char c]] = {c}
      [[r1 + r2]] = [[r1]] \/ [[r2]]
  (2) define in_re_set 
  (3) prove (a::l) in [[r]] iff l in [[pdrv(a,r)]]
*)


SearchAbout RESet.Subset.
Print Module RESet.
Print Module RESetP.

(*Inductive in_astgram : forall (a:astgram), list char_p -> interp (astgram_type a) -> Prop :=
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
*)






(* todo: unorganized *)

    Record DFA := { 
      dfa_num_states : nat ; 
      dfa_states : list astgram ; 
      dfa_transition : list (list nat) ; 
      dfa_accepts : list bool ;
      dfa_rejects : list bool
    }.



    (** Our DFA states correspond to nth derivatives of a starting regexp.  We take
        the position of a regexp in the [states] list to be its name. *)
    Definition states := list astgram.

    (* Poorly named, but basically calculates the derivative of an [astgram] and
       throws away the adjustment function. *)
    Definition unit_derivs r s := let (r', _) := derivs_and_split r s in r'.
    
    (** Generate the transition matrix row for the state corresponding to the
        regexp [r].  In general, this will add new states. *)
    Fixpoint gen_row' n (r:astgram) (s:states) token_id : (states * list nat) := 
      match n with 
        | 0 => (s, nil)
        | S n' => 
          let (s1, d) := find_or_add (unit_derivs r (token_id_to_chars token_id)) s in
          let (s2, row) := gen_row' n' r (s ++ s1) (1 + token_id) in
            (s2, d::row)
      end.
    Definition gen_row (r:astgram) (s:states) : (states * list nat) := 
      gen_row' num_tokens r s 0.

    (** Build a transition table by closing off the reachable states.  The invariant
        is that we've closed the table up to the [next_state] and have generated the
        appropriate transition rows for the states in the range 0..next_state-1.
        So we first check to see if [next_state] is outside the range of states, and
        if so, we are done.  Otherwise, we generate the transition row for the
        derivative at the position [next_state], add it to the list of rows, and
        then move on to the next position in the list of states.  Note that when 
        we generate the transition row, we may end up adding new states.  
     *)
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

    (** We start with the initial [astgram] in state 0 and then try to close 
        off the table. *)
    Definition build_transition_table n (r:astgram) := build_table' n (r::nil) nil 0.

    Definition build_accept_table (s:states) : list bool := List.map accepts_null s.
    Definition build_rejects (s:states) : list bool := List.map always_rejects s.

    Definition build_dfa n (r:astgram) : option DFA := 
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

    Ltac s := repeat (mysimp ; subst).

    Lemma find_index'_prop : forall r s2 s1, 
      match find_index' r (length s1) s2 with
        | Some i => nth_error (s1 ++ s2) i = Some r
        | _ => True
      end.
    Proof.
      induction s2. mysimp. simpl. intros.
      destruct (astgram_dec r a). s. rewrite nth_error_app. auto.
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

    (** Calling [find_or_add_prop r s] yields a well-formed state, ensures that
        if we lookup the returned index, we get [r], and that the state is only
        extended. *)
    Lemma find_or_add_prop : forall r s, 
      match find_or_add r s with 
        | (s',i) => nth_error (s ++ s') i = Some r 
      end.
    Proof.
      unfold find_or_add, find_index. intros. generalize (find_index'_prop r s nil). 
      simpl. intros. destruct (find_index' r 0 s).  mysimp. 
      rewrite nth_error_app. auto.
    Qed.

    (** This is the main loop-invariant for [gen_row'].  Given a 
        astgram [r], a list of states [s], and a token number [n], 
        running [gen_row' n r s (num_tokens - n)] yields a list of states [s2]
        and transition-table [row2] such that the
        length of [row2] is [n], [s2] is an extension of [s], and for all
        [m], the [mth] element of [s2] is the [unit_derivs] of [r] with 
        respect to the token [m+num_tokens-n]. *)
    Lemma gen_row'_prop n r s : 
      n <= num_tokens -> 
      match gen_row' n r s (num_tokens - n) with 
        | (s2, row2) => 
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
      contradiction. Opaque token_id_to_chars. Opaque num_tokens. simpl. intros.
      remember (find_or_add (unit_derivs r (token_id_to_chars (num_tokens - S n))) s).
      destruct p. remember (gen_row' n r (s ++ s0) (S (num_tokens - S n))). destruct p.
      generalize (find_or_add_prop 
        (unit_derivs r (token_id_to_chars (num_tokens - S n))) s).
      rewrite <- Heqp.
      assert (n <= num_tokens). omega. intros. 
      specialize (IHn r (s ++ s0) H0). 
      assert (S (num_tokens - S n) = num_tokens - n). omega. rewrite <- H2 in IHn.
      rewrite <- Heqp0 in IHn. mysimp. rewrite app_ass in H4. exists (s0 ++ x). auto.
      destruct m. intros. simpl. subst. 
      rewrite (nth_error_ext n0 (s ++ s0) x (eq_sym H1)). auto.
      intros. assert (m < n). omega. specialize (H5 _ H7).
      assert (S m + num_tokens - S n = m + num_tokens - n). omega.
      rewrite H8. auto.
   Qed.

   (** This is the main invariant for the [build_table] routine.  Given a well-formed
       list of states [s] and a list of transition-table rows [ros], then for 
       all [i < n], [s(i)] and [r(i)] are defined, and the row [r(i)] is well-formed
       with respect to the state [s(i)]. *)
   Definition build_table_inv s rows n := 
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
     intros. assert (n < S n). auto with arith. generalize (H n H0).
     remember (nth_error s n) as e1. remember (nth_error rows n) as e2.
     destruct e1; destruct e2 ; try tauto. intros. 
     generalize (nth_error_some _ _ Heqe1).
     generalize (nth_error_some _ _ Heqe2). intros. omega.
   Qed.

   Lemma nth_error_none A n (xs:list A) : None = nth_error xs n -> length xs <= n.
   Proof.
     induction n ; destruct xs ; simpl in * ; 
     unfold error, value in * ; intros ; auto with arith ; congruence.
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
     induction n. simpl. auto.
     intros. generalize (build_table_inv_imp H). intros. destruct H0. simpl.
     remember (nth_error s (length rows)). destruct e.
     Focus 2. mysimp. generalize (nth_error_none _ _ Heqe). intros. 
     apply le_antisym ; auto.
     exists nil. apply app_nil_end. exists nil. apply app_nil_end.
     unfold gen_row.
     assert (num_tokens <= num_tokens). omega. 
     generalize (gen_row'_prop a s H2). rewrite minus_diag.
     remember (gen_row' num_tokens a s 0) as p. destruct p. mysimp.
     match goal with 
       | [ |- match build_table' n s0 ?e1 ?e2 with | Some _ => _ | None => _ end ] => 
         specialize (IHn s0 e1) ; remember (build_table' n s0 e1 e2) as popt ; 
         assert (length e1 = S (length rows))
     end.
     rewrite app_length ; simpl ; rewrite plus_comm ; auto.
     rewrite <- H6 in Heqpopt. unfold token_id in *. 
     rewrite <- Heqpopt in IHn.
     destruct popt ; auto. destruct p.
           
     assert (build_table_inv s0 (rows ++ l ::nil) (S (length rows))).
     Focus 2. rewrite <- H6 in H7. specialize (IHn H7). s ; rewrite app_ass. 
     exists (x ++ x1). auto.  simpl. exists (l::x0). auto. clear IHn.

     unfold build_table_inv. intros. 
     assert (i < length rows \/ i = length rows).
     omega. destruct H8. generalize (H i H8). subst. 
     remember (nth_error s i) as e. destruct e ; simpl ; try tauto.
     remember (nth_error rows i) as e. destruct e ; simpl ; try tauto. intros.
     rewrite (nth_error_ext i s x Heqe0). unfold token_id.
     rewrite (nth_error_ext i rows (l::nil) Heqe1). 
     intros. unfold token_id in *.  rewrite <- Heqe1 in H4. destruct H4. split. auto. 
     intros.
     specialize (H9 _ H10). 
     remember (nth_error s (nth t l1 num_tokens)) as e. destruct e ; try contradiction.
     remember (nth_error_ext (nth t l1 num_tokens) s x Heqe2). rewrite e. auto.
     subst. unfold token_id in *. rewrite <- Heqe1. intro ; contradiction.
     subst.
     rewrite (nth_error_ext (length rows) s x Heqe). unfold token_id in *.
     rewrite (nth_error_app rows (l::nil)). simpl. mysimp.
     intros. generalize (H5 _ H4). assert (t + num_tokens - num_tokens = t).
     omega. rewrite H8. auto.
  Qed.

  (** This predicate captures the notion of a correct [DFA] with respect to
      an initial astgram [r].  In essence, it says that the lengths of all of
      the lists is equal to [dfa_num_states d], that [r] is at [dfa_states(0)],
      each row of the [dfa_transition] table is well-formed, that 
      [accepts(i)] holds iff the corresponding state accepts the empty string,
      and when [rejects(i)] is true, the corresponding state rejects all strings. *)
  Definition wf_dfa (r:astgram) (d:DFA) := 
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
      let r' := nth i states aZero in
      let acc := nth i accepts false in 
      let rej := nth i rejects false in 
      let row := nth i transition nil in 
        length row = num_tokens /\ 
        (acc = true <-> exists v:interp (astgram_type r'), in_astgram r' nil v) /\ 
        (rej = true -> forall s, ~(exists v, in_astgram r' s v)) /\ 
        (forall t, t < num_tokens -> 
          nth t row num_tokens < num_states /\
          nth (nth t row num_tokens) states aZero = 
          unit_derivs r' (token_id_to_chars t)).

    Lemma nth_error_nth A (xs:list A) n (v dummy:A) : 
      Some v = nth_error xs n -> nth n xs dummy = v.
    Proof.
      induction xs ; destruct n ; simpl in * ; unfold error, value in * ; mysimp ; 
        try congruence.
    Qed.

    (** These next few lemmas establish the correctness of [accepts_null]. *)
    Lemma accepts_null_corr1' (r:astgram) : 
      accepts_null r = true -> 
      exists v, in_astgram r nil v.
    Proof.
      induction r ; mysimp ; try congruence. exists tt. constructor. auto. auto.
      generalize (andb_prop _ _ H). mysimp. generalize (IHr1 H0) (IHr2 H1). mysimp.
      exists (x0,x). econstructor ; eauto. generalize (orb_prop _ _ H). mysimp.
      generalize (IHr1 H0). mysimp. exists (inl _ x). econstructor ; auto. auto.
      generalize (IHr2 H0). mysimp. exists (inr _ x). eapply InaAlt_r ; auto. auto.
      exists nil. constructor ; auto. 
    Qed.

    Lemma accepts_null_corr1 (r:astgram) : 
      accepts_null r = true -> exists v, in_astgram r nil v.
    Proof.
      intros. generalize (accepts_null_corr1' _ H). mysimp. exists x ; eauto.
    Qed.

    Lemma accepts_null_corr2' (r:astgram) v : 
      in_astgram r nil v -> 
      accepts_null r = true.
    Proof.
      intros r v H. dependent induction H ; s ; try congruence.
      generalize (app_eq_nil _ _ (eq_sym H1)). mysimp. subst.
      rewrite (IHin_astgram2 (eq_refl _)). rewrite (IHin_astgram1 (eq_refl _)). auto.
      rewrite IHin_astgram. auto. rewrite IHin_astgram. 
      destruct (accepts_null a1) ; auto.
    Qed.

    Lemma accepts_null_corr2 (r:astgram) v : 
      in_astgram r nil v -> accepts_null r = true.
    Proof.
      intros. apply (@accepts_null_corr2' r v H).
    Qed.

    (** [accepts_null] is correct. *)
    Lemma accepts_null_corr (r:astgram) : 
      accepts_null r = true <-> (exists v, in_astgram r nil v).
    Proof.
      intros. split. apply accepts_null_corr1 ; auto. mysimp. 
      apply (accepts_null_corr2 H).
    Qed.

    (** [always_rejects] is correct. *)
    Lemma always_rejects_corr (r:astgram) : 
      always_rejects r = true -> forall s v, ~ in_astgram r s v.
    Proof.
      induction r ; mysimp ; try congruence. destruct v ; auto.
      generalize (orb_prop _ _ H). mysimp. generalize (IHr1 H0). intros.
      intro. generalize (inv_acat H2). mysimp. subst. apply (H1 x x1). auto.
      generalize (IHr2 H0). intros. intro. generalize (inv_acat H2).
      mysimp. s. apply (H1 x0 x2) ; auto.
      generalize (andb_prop _ _ H). mysimp. intro. generalize (inv_aalt H2). mysimp.
      eapply IHr1 ; eauto. eapply IHr2 ; eauto. 
    Qed.

    (** [build_dfa] is (partially) correct.  Note that we do not show that there's
        always an [n], hence the partiality. *)
    Lemma build_dfa_wf (r:astgram) (d:DFA) :
      forall n, build_dfa n r = Some d -> wf_dfa r d.
    Proof.
      unfold build_dfa, build_transition_table. intros.
      assert (build_table_inv (r::nil) nil 0). 
      unfold build_table_inv. intros. 
      destruct i. simpl. assert False. omega. contradiction. simpl.
      assert False. omega.
      contradiction. generalize (build_table'_prop n H0). simpl. intros. 
      unfold token_id in *.
      destruct (build_table' n (r::nil) nil 0) ; try congruence.
      destruct p as [s' rows']. injection H ; clear H ; intros ; mysimp. 
      unfold wf_dfa. simpl. mysimp ; try (subst ; simpl ;  auto ; fail).
      subst. simpl. unfold build_accept_table.
      rewrite map_length. auto. subst. simpl. unfold build_rejects. 
      rewrite map_length. auto.
      (*rewrite H1. unfold value. auto. intros. rewrite <- H0 in H5. *)
      unfold build_table_inv in H2. rewrite H1 in H2. intros.
      rewrite <- H in H5 ; simpl in H5.
      specialize (H2 _ H5). 
      remember (nth_error s' i) as e. destruct e ; try contradiction. 
      unfold token_id in *.
      remember (nth_error rows' i) as e. destruct e ; try contradiction. destruct H2.
      split. assert (i < length x). subst. omega. rewrite <- H. simpl. rewrite <- H2.
      rewrite (nth_error_nth rows' i _ Heqe0). auto. 
      (* split. rewrite (nth_error_nth rows' i nil Heqe0). auto. 
      rewrite (nth_error_nth s' i (Zero _) Heqe). *)
      rewrite <- H ; simpl.
      unfold build_accept_table. unfold build_rejects. unfold token_id.
      generalize (map_nth accepts_null s' aZero i). intro. simpl in H7. rewrite H7.
      generalize (map_nth always_rejects s' aEps i). intro. simpl in H8. rewrite H8.
      rewrite (nth_error_nth s' i _ Heqe). 
      rewrite (nth_error_nth s' i _ Heqe). split. apply accepts_null_corr. split.
      intros. intro. mysimp. eapply always_rejects_corr ; eauto. 
      intros. subst.
      rewrite (nth_error_nth x i _ Heqe0). 
      generalize (H6 _ H9). 
      remember (nth_error (r::x0) (nth t l num_tokens)). destruct e ; try tauto. intros.
      subst. unfold token_id in *.
      rewrite (nth_error_nth (r::x0) (nth t l num_tokens) _ Heqe1).
      split ; auto. generalize Heqe1. clear Heqe1.  rewrite <- H2.
      generalize (nth t l (length l)) (r::x0). induction n0 ; destruct l0 ; simpl ; 
      unfold error, value ; intros ; try congruence. omega. generalize (IHn0 _ Heqe1).
      intros. omega.
   Qed.

  (** ** Building a recognizer which ignores semantic actions. *)
  Definition par2rec t (g:grammar t) : astgram := 
    let (ag, _) := split_astgram g in ag.

  (** The translation from parsers to regexps which throws away the maps is correct. *)
  Lemma par2rec_corr1 t (g:grammar t) cs v : 
    in_grammar g cs v -> exists v, in_astgram (par2rec g) cs v.
  Proof.
    unfold par2rec.
    induction 1 ; s ; eauto ; unfold ag_and_fn, fixfn ; 
    try (remember (split_astgram g1) as e1 ; remember (split_astgram g2) as e2 ; 
         destruct e1 ; destruct e2 ; eauto) ; 
    try (remember (split_astgram g) as e ; destruct e ; eauto).
  Qed.

  Lemma par2rec_corr2 t (g:grammar t) cs v1 : 
    in_astgram (par2rec g) cs v1 -> exists v2, in_grammar g cs v2.
  Proof.
    unfold par2rec.
    induction g ; mysimp ; unfold ag_and_fn, fixfn in * ; 
    try (remember (split_astgram g) as e ; destruct e) ; 
    try (remember (split_astgram g1) as e1 ; destruct e1 ; 
         remember (split_astgram g2) as e2 ; destruct e2) ; 
    ainv ; subst ; mysimp ; eauto ; repeat 
    match goal with 
        | [ H1 : forall cs v, in_astgram ?x _ _ -> _ ,
            H2 :  in_astgram ?x _ _ |- _ ] => specialize (H1 _ _ H2) ; mysimp ; eauto
    end.
    dependent induction H. eauto. clear IHin_astgram1.
    specialize (IHin_astgram2 _ _ _ Heqe IHg v2 (eq_refl _) (JMeq_refl _)). mysimp.
    specialize (IHg _ _ H). mysimp.
    econstructor ; eapply InStar_cons ; eauto. 
  Qed.

  (** A simple recognizer -- given a grammar [g] and string [cs], returns a 
     proof that either either [cs] matches the grammar [g] (i.e., there is
     some semantic value that [cs] would parse into) or else there is no 
     match (i.e., there is no value that it can parse into.)  I don't think
     we actually use this anywhere.  Just here for fun.  *)
  Definition recognize t (g:grammar t) cs : 
    {exists v, in_grammar g cs v} + {forall v, ~ in_grammar g cs v}.
    intros.
    remember (derivs_and_split (par2rec g) cs) as p.
    destruct p as [a f].
    remember (accepts_null a) as b.
    destruct b ; [ left | right ].
    unfold par2rec in *. generalize (split_astgram_corr1 g). intro.
    remember (split_astgram g) as e. destruct e.
    generalize (accepts_null_corr1' a (eq_sym Heqb)). intro. destruct H0.
    generalize (@derivs_and_split_corr2 cs x (xinterp f x0)). unfold in_agxf.
    rewrite <- Heqp. intros. 
    assert (in_astgram x cs (xinterp f x0)). apply H1. eauto.
    specialize (H _ _ H2). eauto.
    intros. intro. unfold par2rec in *. generalize (split_astgram_corr2 g).
    intro. remember (split_astgram g) as e ; destruct e. specialize (H0 _ _ H).
    destruct H0. destruct H0. subst.
    generalize (@derivs_and_split_corr1 cs x x0 H0). unfold in_agxf. simpl.
    rewrite <- Heqp. mysimp. subst. generalize (accepts_null_corr2 H1). intro.
    rewrite H2 in Heqb. discriminate Heqb.
  Defined.

   (** This is a simple function which runs a DFA on an entire string, returning
       true if the DFA accepts the string, and false otherwise.  In what follows,
       we prove that [run_dfa] is correct... *)
   Fixpoint run_dfa (d:DFA) (state:nat) (ts:list token_id) : bool := 
     match ts with 
       | nil => nth state (dfa_accepts d) false
       | t::ts' => run_dfa d (nth t (nth state (dfa_transition d) nil) num_tokens) ts'
     end.

   (** This lifts the [unit_deriv_corr1] to strings. *)
   Lemma unit_derivs_corr1 cs1 (r:astgram) cs2 v : 
     in_astgram (unit_derivs r cs1) cs2 v -> 
     exists v, in_astgram r (cs1 ++ cs2) v.
   Proof.
     unfold unit_derivs. 
     induction cs1 ; simpl ; eauto. intros.
     generalize (@deriv_and_split_corr2 r a (cs1 ++ cs2)). unfold in_agxf. intro.
     remember (deriv_and_split r a) as e ; destruct e.
     specialize (IHcs1 x cs2). remember (derivs_and_split x cs1) as e ; destruct e.
     unfold agxf in *. specialize (IHcs1 _ H). destruct IHcs1 as [v' IHcs1]. 
     exists (xinterp x0 v'). apply H0. exists v'. auto.
   Qed.

   (** Lifts [unit_deriv_corr2] to strings. *)
   Lemma unit_derivs_corr2 cs t (g:grammar t) v : 
     in_grammar g cs v -> 
     let (a,_) := split_astgram g in 
     let a' := unit_derivs a cs in
     exists v', in_astgram a' nil v'.
   Proof.
     intros. generalize (split_astgram_corr2 g). remember (split_astgram g) as e.
     destruct e. intro. specialize (H0 _ _ H). mysimp. subst.
     unfold unit_derivs. remember (derivs_and_split x cs) as e. destruct e.
     generalize (derivs_and_split_corr1 H0). unfold in_agxf. rewrite <- Heqe0.
     mysimp. subst. eauto.
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
     (flat_map token_id_to_chars ts2). unfold unit_derivs. induction l ; mysimp. 
     remember (deriv_and_split r0 a) as e ; destruct e. 
     specialize (IHl x l0). remember (derivs_and_split x (l ++ l0)) as e ; destruct e.
     remember (derivs_and_split x l) as e ; destruct e. subst. unfold agxf. auto.
   Qed.

   (** This lemma tells us that if we start with a grammar [g], build a [DFA],
       and then run the [DFA] on a list of tokens, then we get [true] iff
       the grammar would've accepted the string and produced a value.  *)
   Lemma dfa_corr' : forall t (g:grammar t) n (d:DFA), 
     build_dfa n (par2rec g) = Some d -> 
     forall ts2 ts1 state, 
       nth_error (dfa_states d) state = 
       Some (unit_derivs (par2rec g) (flat_map token_id_to_chars ts1)) -> 
       list_all (fun t => t < num_tokens) ts2 ->
       if run_dfa d state ts2 then
         exists v, in_grammar g (flat_map token_id_to_chars (ts1 ++ ts2)) v
       else 
         forall v, ~ in_grammar g (flat_map token_id_to_chars (ts1 ++ ts2)) v.
   Proof.
     intros t p n d H. assert (wf_dfa (par2rec p) d). eapply build_dfa_wf ; eauto.
     unfold wf_dfa in H0. induction ts2 ; mysimp.
     assert (state < dfa_num_states d). rewrite H0. generalize H1. 
     generalize (unit_derivs (par2rec p) (flat_map token_id_to_chars ts1)).
     generalize (dfa_states d) state. 
     induction l ; destruct state0 ;  mysimp ; unfold error, value in * ; try congruence. 
     subst. omega. subst. generalize (IHl _ _ H8). intros. omega. 
     generalize (H7 _ H8). mysimp. remember (nth state (dfa_accepts d) false) as e.
     destruct e. generalize (H10 (eq_refl _)).
     rewrite (nth_error_nth (dfa_states d) state _ (eq_sym H1)). intros. mysimp.
     generalize (unit_derivs_corr1 _ _ H14).
     rewrite <- app_nil_end. mysimp. apply (par2rec_corr2 p H15).
     unfold not. intros. assert (false = true).
     apply H13. rewrite (nth_error_nth (dfa_states d) state _ (eq_sym H1)).
     generalize (@par2rec_corr1 t p (flat_map token_id_to_chars ts1) v H14). intro.
     generalize (unit_derivs_corr2 H14). unfold par2rec. 
     remember (split_astgram p) as e. destruct e. auto. congruence.
     
     generalize (IHts2 (ts1 ++ a::nil) 
       (nth a (nth state (dfa_transition d) nil) num_tokens)). 
     rewrite app_ass. simpl. intros. apply H9 ; auto. clear H9 IHts2.
     assert (state < dfa_num_states d). rewrite H0. generalize H1.
     generalize (unit_derivs (par2rec p) (flat_map token_id_to_chars ts1)).
     generalize (dfa_states d) state. induction l ; destruct state0 ; mysimp ; 
     unfold error, value in * ; try congruence; try omega. 
     generalize (IHl _ _ H9). intros. omega.
     generalize (H8 _ H9) ; mysimp. generalize (H13 _ H2). mysimp.
     rewrite unit_derivs_flat_map. simpl. rewrite <- app_nil_end.
     generalize (H13 _ H2). mysimp. (*rewrite H0 in H18.*)
     apply (lt_nth_error (dfa_states d) aZero). omega. rewrite H18.
     rewrite (nth_error_nth _ _ aZero (eq_sym H1)). auto.
  Qed.

  (** Here is the key correctness property for the DFAs. *)
  Lemma dfa_corr t (g:grammar t) n (d:DFA) :
    build_dfa n (par2rec g) = Some d -> 
    forall ts, 
      list_all (fun t => t < num_tokens) ts -> 
      if run_dfa d 0 ts then 
        exists v, in_grammar g (flat_map token_id_to_chars ts) v
      else 
        forall v, ~ in_grammar g (flat_map token_id_to_chars ts) v.
  Proof.
    intros. assert (ts = nil ++ ts) ; auto. rewrite H1. eapply dfa_corr' ; eauto.
    assert (wf_dfa (par2rec g) d). eapply build_dfa_wf ; eauto.
    unfold wf_dfa in H2. mysimp.
  Qed.

  Definition accepts_at_most_one_null (a:astgram) : bool := 
    if le_gt_dec (List.length (astgram_extract_nil a)) 1 then true else false.

  Fixpoint enum_tokens (f:token_id -> bool) (n:nat) : bool := 
    match n with 
      | 0 => true
      | S m => (f m) && enum_tokens f m
    end.

  Definition forall_tokens (f:token_id -> bool) : bool := enum_tokens f num_tokens.

  (** Properties of dfa_recognize *)
  Lemma dfa_loop_run : forall ts d state count count2 ts2,
    dfa_loop d state count ts = Some (count2, ts2) -> 
    exists ts1, 
      ts = ts1 ++ ts2 /\ count2 = length ts1 + count /\ 
      run_dfa d state ts1 = true /\
      forall ts1' ts2',
        ts = ts1' ++ ts2' -> 
        length ts1' < length ts1 -> 
        ~ run_dfa d state ts1' = true.
  Proof.
    induction ts ; mysimp ; remember (nth state (dfa_accepts d) false) ; 
    destruct y ; try congruence ; try (injection H ; mysimp ; clear H ; subst). 
    exists nil. rewrite Heqy. repeat split ; auto. intros. simpl in H0.
    assert False. omega. contradiction.
    exists nil. simpl. rewrite Heqy. repeat split ; auto.
    intros. assert False. omega. contradiction.
    specialize (IHts d _ _ _ _ H). mysimp. exists (a::x). simpl.
    split. subst ; auto. split ; subst ; auto. split ; auto. intros.
    destruct ts1'. simpl in *. rewrite <- Heqy. auto. simpl in H0.
    injection H0 ; intros ; subst; clear H0. 
    specialize (H3 _ _ H4). assert (length ts1' < length x). simpl in *.
    omega. specialize (H3 H0). simpl. congruence.
  Qed.

  Lemma list_all_app : forall A (f:A->Prop) (xs ys:list A), 
    list_all f (xs ++ ys) -> list_all f xs /\ list_all f ys.
  Proof.
    induction xs ; mysimp ; specialize (IHxs _ H0) ; mysimp.
  Qed.

  Lemma dfa_recognize_corr :
    forall t (g:grammar t) n (d:DFA),
    build_dfa n (par2rec g) = Some d -> 
    forall ts, 
      list_all (fun t => t < num_tokens) ts -> 
      match dfa_recognize d ts with 
        | None => True
        | Some (count,ts2) => 
          exists ts1, exists v, 
            ts = ts1 ++ ts2 /\ count = length ts1 /\ 
            in_grammar g (flat_map token_id_to_chars ts1) v /\
            forall ts3 ts4,
              length ts3 < length ts1 ->
              ts = ts3 ++ ts4 -> 
              forall v, ~ in_grammar g (flat_map token_id_to_chars ts3) v
      end.
  Proof.
    intros. unfold dfa_recognize. remember (dfa_loop d 0 0 ts) as e.
    destruct e ; auto. destruct p. 
    generalize (dfa_loop_run _ _ _ _ (eq_sym Heqe)). mysimp. subst.
    exists x. generalize (list_all_app _ _ _ H0).  mysimp.
    generalize (dfa_corr _ _ H _ H1).  rewrite H3. mysimp. 
    rewrite plus_comm. simpl. exists x0. repeat split ; auto.
    intros. specialize (H4 _ _ H7 H6). intro. apply H4.
    rewrite H7 in H0. generalize (list_all_app _ _ _ H0). mysimp.
    generalize (@dfa_corr _ g n d H ts3 H9).
    destruct (run_dfa d 0 ts3). auto. intros. assert False.
    eapply H11. eauto. contradiction.
  Qed.
