(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

(** In this section, we build a table-driven DFA parser for a [grammar]. *)

Require Import Coq.Program.Equality.
(* Require Import Coq.Classes.Morphisms. *)
(* Require Import Coq.Program.Basics. *)
(* Require Import Coq.Init.Logic. *)
(* Require Import Eqdep. *)
Require Import Coq.Lists.SetoidList.
Require Import List.
Require Import Arith.
Require Import Bool.
Require Import MSetsMore.
Require Import ZArith.

Require Import Regexp.
Require Import ParserArg.
Import X86_PARSER_ARG.
Require Import Xform.

Require Import CommonTacs.
Set Implicit Arguments.

Local Ltac false_elim :=
  match goal with
    | [H:False |- _] => destruct H
  end.

Local Hint Resolve in_map in_prod in_or_app.

(* Require Import Coq.Structures.OrdersAlt. *)
(* Require Import Coq.MSets.MSetAVL. *)
(* Require Import Coq.MSets.MSetProperties. *)
(* Require Import Coq.MSets.MSetFacts. *)

(* todo: move to regexp ??? *)
(* Lemma InA_regexp_eq_In:  *)
(*   forall x l, InA REOrderedType.eq x l -> In x l. *)
(* Proof. intros. apply InA_alt in H.  *)
(*   sim. apply compare_re_eq_leibniz in H. congruence. *)
(* Qed. *)

(** * Define [RESet], a set of regexps *)
Require Import RESet.

(** A set of regexps *)
Module RES := RESet.RESETXFORM.
(* Module RESet := MSetAVL.Make REOrderedType. *)
Module RESF := MapSet RES.
Module RESP := MSetProperties.Properties RES.


(** ** Abbreviations and definitions for [RESet] *)

Definition rs_xf_pair := RES.rs_xf_pair.

Local Ltac re_set_simpl :=
  repeat 
    (simpl in *;
     match goal with
       | [H:RES.In _ RES.empty |- _] =>
         apply RESP.Dec.F.empty_iff in H; contradict H
       | [H:REOrderedTypeAlt.compare _ _ = Eq |- _] =>
         apply compare_re_eq_leibniz in H; subst
       | [H:RES.In _ (RES.singleton _) |- _] =>
         apply RESP.Dec.F.singleton_iff in H;
         apply compare_re_eq_leibniz in H; subst
     end).

Lemma re_set_map_intro: forall (x y:RES.elt) m (s:RES.t),
  RES.In y s -> x = RESF.get_fun m y -> RES.In x (RESF.map m s).
Proof. intros. 
  eapply RESF.map_intro.
    eassumption.
    subst. apply REOrderedType.eq_equiv.
Qed.

Lemma re_set_map_elim: forall (x:RES.elt) m (s:RES.t),
  RES.In x (RESF.map m s) -> 
  exists y, RES.In y s /\ x = RESF.get_fun m y.
Proof. intros. apply RESF.map_elim in H.
  sim. apply compare_re_eq_leibniz in H0. crush.
Qed.

Lemma re_set_map_proper: forall f, Proper (RES.E.eq ==> RES.E.eq) f.
Proof. unfold Proper, respectful. intros.
  apply compare_re_eq_leibniz in H. subst. 
  apply REOrderedType.eq_equiv.
Qed.

Definition re_set_build_map (f: regexp -> regexp) : RESF.proper_map :=
  exist _ f (re_set_map_proper f).

(** Concat regexp r to the right of every regexp in a regexp set *)
Definition set_cat_re (s:RES.t) (r:regexp): RES.t := 
  match r with
    | Eps => s (* not stricitly necessary; an optimization *)
    | Zero => RES.empty
    | _ => RESF.map (re_set_build_map (fun r1 => Cat r1 r)) s
  end.
Notation "s $ r" := (set_cat_re s r) (at level 60, no associativity).

(**************************************************************************)

(* Some definitions and assumed axioms; these should be later moved and
   proved to other files *)

Definition re_xf_pair := RES.re_xf_pair.
Definition in_re_set := RES.in_re_set.
Definition in_re_set_xform := RES.in_re_set_xform.
Definition in_re_xform := RES.in_re_xform.

Axiom cat_re_xform: forall ty,
  RES.rs_xf_pair ty -> 
  forall r:regexp, RES.rs_xf_pair (Pair_t ty (regexp_type r)).

Lemma cat_re_xform_erase: forall t rx1 r,
  projT1 (@cat_re_xform t rx1 r) = set_cat_re (projT1 rx1) r.
Admitted.

Lemma cat_re_xform_corr: forall ty (rx:RES.rs_xf_pair ty) r s v,
  in_re_set_xform (cat_re_xform rx r) s v <->
  exists s1 s2 v1 v2, s = s1++s2 /\ v=(v1,v2) /\
    in_re_set_xform rx s1 v1 /\ in_regexp r s2 v2.
Admitted.

Definition xsingleton {t} : t ->> List_t t := @xcons t t xid xempty.

(* Definition xmatchlist {t1 t2}: *)
(*   (Unit_t ->> t2) -> (Pair_t t1 (List_t t1) ->> t2) -> (List_t t1 ->> t2) :=  *)

Lemma xcross_corr2 {t1 t2} (vs: interp (Pair_t (List_t t1) (List_t t2))):
  xinterp xcross vs = List.list_prod (fst vs) (snd vs).
Admitted.

Definition rx_imply ty (rx1 rx2: rs_xf_pair ty) := 
  forall s v, in_re_set_xform rx1 s v -> in_re_set_xform rx2 s v.

Definition rx_equal ty (rx1 rx2: rs_xf_pair ty) := 
  forall s v, in_re_set_xform rx1 s v <-> in_re_set_xform rx2 s v.

Instance in_re_set_xform_equal ty: 
  Proper ((@rx_equal ty) ==> eq ==> eq ==> iff) (@in_re_set_xform ty).
Proof. intros rx1 rx2 H1 s1 s2 H2 v1 v2 H3.
  unfold rx_equal in H1. rewrite H1. crush.
Qed.

Axiom Equal_xform: forall (s s':RES.t), 
  RES.Equal s s' -> RES.re_set_type s' ->> RES.re_set_type s.

Lemma Equal_xform_corr rs1 rs2 (H:RES.Equal rs1 rs2)
      ty (f:RES.re_set_type rs1 ->> List_t ty) str v:
  in_re_set_xform (existT _ rs1 f) str v <->
  in_re_set_xform (existT _ rs2 (xcomp (Equal_xform H) f)) str v.
Admitted.

Lemma in_re_xform_intro: forall t (rex:re_xf_pair t) s v v',
  in_regexp (projT1 rex) s v' -> In v (xinterp (projT2 rex) v') -> 
    in_re_xform rex s v.
Proof. intros. unfold in_re_xform. destruct rex as [r f].  
       exists v'; crush.
Qed.

Lemma in_re_xform_intro2: 
  forall t r (f:regexp_type r ->> (List_t t)) s v v',
  in_regexp r s v' -> In v (xinterp f v') -> 
    in_re_xform (existT _ r f) s v.
Proof. generalize in_re_xform_intro; crush. Qed.

Lemma in_re_xform_elim: forall t (rex:re_xf_pair t) s v,
  in_re_xform rex s v -> 
    exists v', in_regexp (projT1 rex) s v' /\ In v (xinterp (projT2 rex) v').
Proof. unfold in_re_xform; intros. destruct rex as [r f]. crush. Qed.

Lemma in_re_xform_elim2: 
  forall t r (f: regexp_type r ->> (List_t t)) s v,
  in_re_xform (existT _ r f) s v -> 
    exists v', in_regexp r s v' /\ In v (xinterp f v').
Proof. generalize in_re_xform_elim. crush. Qed.


Opaque RES.union_xform RES.singleton_xform.
Opaque xcross xmap xapp xcomp xflatten.

Ltac xinterp_simpl :=
  repeat match goal with
    | [|- context[xcomp ?X1 ?X2]] => rewrite (xcomp_corr X1 X2); simpl
    | [H:context[xcomp ?X1 ?X2] |- _] => 
      rewrite (xcomp_corr X1 X2) in H; simpl in H
    | [|- context[xinterp (xpair _ _) _]] => rewrite xpair_corr; simpl
    | [H:context[xinterp (xpair _ _) _] |- _] => 
      rewrite xpair_corr in H; simpl in H
    | [|- context[xinterp xcross _]] => rewrite xcross_corr2; simpl
    | [H:context[xinterp xcross _] |- _] => 
      rewrite xcross_corr2 in H; simpl in H
    | [|- context [xinterp xapp (_,_)]] => rewrite xapp_corr; simpl
    | [H:context [xinterp xapp (_,_)] |- _] => 
      rewrite xapp_corr in H; simpl in H
    | [|- context [xinterp (xmap _) ?V]] => 
      rewrite (@xmap_corr _ _ _ V); simpl
    | [H:context [xinterp (xmap _) ?V] |- _] => 
      rewrite (@xmap_corr _ _ _ V) in H; simpl in H
    | [|- context[xinterp xflatten _]] => rewrite xflatten_corr2; simpl
    | [H:context[xinterp xflatten _] |- _] => 
      rewrite xflatten_corr2 in H; simpl in H
  end.

Lemma in_re_set_xform_intro: forall t (rx:RES.rs_xf_pair t) s v v',
  in_re_set (projT1 rx) s v' -> In v (xinterp (projT2 rx) v') -> 
    in_re_set_xform rx s v.
Proof. intros. unfold in_re_set_xform. destruct rx as [rs f].  
       exists v'; crush.
Qed.

Lemma in_re_set_xform_intro2: 
  forall t rs (f:RES.re_set_type rs ->> (List_t t)) s v v',
  in_re_set rs s v' -> In v (xinterp f v') -> 
    in_re_set_xform (existT _ rs f) s v.
Proof.  generalize in_re_set_xform_intro; crush. Qed.

Lemma in_re_set_xform_elim: forall t (rx:RES.rs_xf_pair t) s v,
  in_re_set_xform rx s v -> 
    exists v', in_re_set (projT1 rx) s v' /\ In v (xinterp (projT2 rx) v').
Proof. unfold in_re_set_xform; intros. destruct rx as [rs f]. crush. Qed.

Lemma in_re_set_xform_elim2: 
  forall t rs (f: RES.re_set_type rs ->> (List_t t)) s v,
  in_re_set_xform (existT _ rs f) s v -> 
    exists v', in_re_set rs s v' /\ In v (xinterp f v').
Proof. intros. generalize in_re_set_xform_elim. crush. Qed.

Lemma in_re_set_xform_comp: 
  forall t1 t2 (rx:RES.rs_xf_pair t1) s (g:t1 ->> t2) v' rs f,
  rx = existT _ rs f ->
  (in_re_set_xform (existT _ rs (xcomp f (xmap g))) s v' <->
   exists v,  in_re_set_xform rx s v /\ v' = xinterp g v).
Proof. intros. 
  split; intros.
  Case "->".
    apply in_re_set_xform_elim2 in H0. 
    destruct H0 as [v1 H0]. 
    xinterp_simpl. sim. 
    apply Coqlib.list_in_map_inv in H1. crush.
  Case "<-". destruct H0 as [v H0]. sim.
    subst rx.
    apply in_re_set_xform_elim2 in H0.
    destruct H0 as [v1 H0]. 
    exists v1; crush.
    xinterp_simpl. crush. 
Qed.

Lemma in_re_set_xform_comp2: 
  forall t1 t2 (rx:RES.rs_xf_pair t1) s (g:t1 ->> t2) v',
  in_re_set_xform (let (rs, f) := rx in existT _ rs (xcomp f (xmap g))) s v' <->
  exists v,  in_re_set_xform rx s v /\ v' = xinterp g v.
Proof. intros. destruct rx as [rs f]. apply in_re_set_xform_comp. trivial. Qed.

Definition erase (ty:type) (rx:rs_xf_pair ty): RES.t := projT1 rx.
Notation "| rx |" := (erase rx) (at level 40, no associativity).

(** Equality of the RESets in [rs_xf_pair]s *)
Definition erase_subset ty1 ty2 (rx1:rs_xf_pair ty1) (rx2:rs_xf_pair ty2) :=
  RES.Subset (|rx1|) (|rx2|).
Definition erase_eq ty1 ty2 (rx1:rs_xf_pair ty1) (rx2:rs_xf_pair ty2) :=
  RES.Equal (|rx1|) (|rx2|).

Lemma erase_subset_antisym: 
  forall ty1 ty2 (rx1: rs_xf_pair ty1) (rx2: rs_xf_pair ty2),
  erase_subset rx1 rx2 -> erase_subset rx2 rx1 -> erase_eq rx1 rx2.
Proof. unfold erase_subset, erase_eq. intros.
  apply RESP.subset_antisym; trivial.
Qed.

(* todo: move to Regexp.v *)
(** This function computes the list of all values v, such that 
    [in_regexp nil v] holds. *)
Fixpoint regexp_extract_nil (r:regexp) : list (interp (regexp_type r)) := 
  match r return list (interp (regexp_type r)) with
    | Eps => tt::nil
    | Zero => nil
    | Char _ => nil
    | Any => nil
    | Cat ag1 ag2 => list_prod (regexp_extract_nil ag1) (regexp_extract_nil ag2)
    | Alt ag1 ag2 => 
      (List.map (fun x => inl _ x) (regexp_extract_nil ag1)) ++ 
      (List.map (fun x => inr _ x) (regexp_extract_nil ag2))
    | Star ag => nil::nil
  end.

Axiom re_set_extract_nil: forall (rs:RES.t), list (interp (RES.re_set_type rs)).

(* todo: move to Coqlib.v *)      
Lemma plus_minus_assoc a b c: c <= b -> a + (b - c) = a + b - c.
Proof. intros. omega. Qed.

Lemma xcoerce_eq t1 t2 (f:t1 ->> t2) (H1:t1=t1) (H2:t2=t2):
  xcoerce f H1 H2 = f.
Proof. assert (H1=eq_refl _). apply proof_irrelevance.
  assert (H2=eq_refl _). apply proof_irrelevance.
  subst. unfold xcoerce, eq_rec_r. simpl. trivial.
Qed.
            
(* End of assumed axioms *)
(**************************************************************************)

(** * The notion of prebase of a regexp and partial-derivative sets.

  The relation between prebases and partial derivative sets are in the
  paper "From Mirkin's prebases to Antimirov's Word Partial Derivatives"
  by Champarnaud and Ziadi.  *)

(** Prebase of a regexp:
    prebase(zero) = {} 
    prebase(epsilon) = {} 
    prebase(a) = {epsilon}, for a in the alphabet
    prebase(r1+r2) = prebase(r1) \/ prebase(r2)
    prebase(r1 r2) = prebase(r1)r2 \/ prebase(r2)
    prebase(r_star) = prebase(r)r_star 
*)
Fixpoint prebase (r:regexp): RES.t := 
  match r with
    | Eps | Zero => RES.empty
    | Char _ | Any => RES.singleton Eps
    | Cat r1 r2 => RES.union ((prebase r1) $ r2) (prebase r2)
    | Alt r1 r2 => RES.union (prebase r1) (prebase r2)
    | Star r1 => (prebase r1) $ (Star r1)
  end.

(** The set of possible partial derivatives*)
Definition pdset (r:regexp): RES.t := RES.add r (prebase r).

(** Number of symbols in a regexp:
    |zero| = |epsilon| = 0
    |a| = 1 
    |r1 + r2| = |r1| + |r2|
    |r1 r2| = |r1| + |r2|
    |r*| = |r| *)
Fixpoint num_of_syms (r: regexp): nat := 
  match r with
    | Eps | Zero => 0
    | Char _ => 1 
    (* Since Any is (Char c1 + Char c2 + ...), it appears it should
       return n in this case, where n is the number of chars in the alphabet;
       however, return 1 in this case seems fine; that is, prebase_upper_bound
       can still be proved *)
    | Any => 1 
    | Cat r1 r2 | Alt r1 r2 => num_of_syms r1 + num_of_syms r2
    | Star r => num_of_syms r
  end.

(** ** Lemmas about set_cat_re *)

Lemma set_cat_re_intro1 : forall r s r2,
  RES.In r s -> r2 = Eps -> RES.In r (s $ r2).
Proof. crush. Qed.

Lemma set_cat_re_intro2 : forall r s r1 r2,
  RES.In r1 s -> r = Cat r1 r2 -> r2 <> Eps -> r2 <> Zero
    -> RES.In r (s $ r2).
Proof. destruct r2; 
  (congruence || simpl; intros; eapply re_set_map_intro; eassumption).
Qed.

Lemma set_cat_re_elim : forall r s r2,
  RES.In r (s $ r2) -> 
    (r2=Eps /\ RES.In r s) \/
    (r2=Zero /\ False) \/
    (r2<>Eps /\ r2<>Zero /\ exists r1, RES.In r1 s /\ r = Cat r1 r2).
Proof. intros. destruct r2;
  try (right; right; simpl in H; 
       apply RESF.map_elim in H; 
       destruct H as [y [H2 H4]]; 
       apply compare_re_eq_leibniz in H4;
       eexists; crush; fail).
  Case "r2=Eps". left. auto.
  Case "r2=Zero". right; left. simpl in *. re_set_simpl.
Qed.

Lemma set_cat_re_cardinal: 
  forall s r, RES.cardinal (s $ r) <= RES.cardinal s.
Proof. unfold set_cat_re. 
  destruct r; auto using RESF.map_cardinal_le.
  Case "Zero".
    repeat rewrite RES.cardinal_spec. simpl.
    auto using le_0_n.
Qed.

Lemma set_cat_re_subset : forall s1 s2 r,
  RES.Subset s1 s2 -> RES.Subset (s1 $ r) (s2 $ r).
Proof. destruct r; simpl; intros; try (auto using RESF.map_subset).
  trivial.
  apply RESP.subset_refl.
Qed.  

(** ** Lemmas about prebase *)

Lemma prebase_upper_bound : 
  forall r, RES.cardinal (prebase r) <= num_of_syms r.
Proof. induction r; try (simpl; trivial).
  Case "Cat". 
    generalize
      (RESP.union_cardinal_le (prebase r1 $ r2) (prebase r2)).
    generalize (set_cat_re_cardinal (prebase r1) r2).
    omega.
  Case "Alt". 
    generalize
      (RESP.union_cardinal_le (prebase r1) (prebase r2)).
    omega.
  Case "Star". 
    generalize (set_cat_re_cardinal (prebase r) (Star r)). crush.
Qed.

Lemma prebase_trans :
  forall r1 r2 r3, 
    RES.In r2 (prebase r1) -> RES.In r3 (prebase r2) 
      -> RES.In r3 (prebase r1).
Proof. induction r1; try (simpl; intros; re_set_simpl; fail).
  Case "Cat". simpl. intros.
    apply RES.union_spec in H; destruct H.
    SCase "r2 in (prebase r1_1 $ r1_2)".
      apply set_cat_re_elim in H; destruct H as [|[|]]; 
        try (apply RESP.FM.union_2; crush; fail).
      SSCase "r1_2<>eps and r1_2<>zero". sim. subst. simpl in *.
        apply RESP.FM.union_1 in H0.
        destruct H0.
        SSSCase "r3 in prebase _ $ r1_2".
          apply set_cat_re_elim in H0; 
            destruct H0 as [|[|]]; try crush.
          apply RESP.FM.union_2.
          assert (RES.In x0 (prebase r1_1)). crush.
          eapply set_cat_re_intro2; try eassumption. trivial.
        SSSCase "r3 in prebase r1_2".
          apply RESP.FM.union_3. crush.
    SCase "r2 in prebase(r1_2)".
      apply RESP.FM.union_3. crush.
  Case "Alt". simpl; intros.
    apply RES.union_spec in H; destruct H.
      apply RESP.FM.union_2; crush.
      apply RESP.FM.union_3; crush.
  Case "Star". simpl; intros.
    apply re_set_map_elim in H; sim; subst.
    simpl in H0.
    apply RES.union_spec in H0; destruct H0.
    SCase "r3 in (prebase x) $ (r1*)".
      apply re_set_map_elim in H0; sim; subst.
      assert (RES.In x0 (prebase r1)) by crush.
      eapply re_set_map_intro; crush.
    SCase "r3 in (prebase r1) $ (r1*)".
      apply re_set_map_elim in H0; sim; subst.
      assert (RES.In x0 (prebase r1)) by crush.
      eapply re_set_map_intro; crush.
Qed.

(** ** Lemmas about pdset *)

Lemma pdset_upper_bound : 
  forall r, RES.cardinal (pdset r) <= S (num_of_syms r).
Proof. unfold pdset. intros.
  generalize (prebase_upper_bound r); intros.
  destruct (RESP.In_dec r (prebase r)).
    use_lemma RESP.add_cardinal_1 by eassumption. omega.
    use_lemma RESP.add_cardinal_2 by eassumption. omega.
Qed.

Lemma pdset_trans : forall r1 r2 r3, 
    RES.In r2 (pdset r1) -> RES.In r3 (pdset r2)
      -> RES.In r3 (pdset r1).
Proof. unfold pdset; intros.
  apply RES.add_spec in H; apply RES.add_spec in H0.
  destruct H; destruct H0; re_set_simpl.
    apply RESP.FM.add_1; apply REOrderedType.eq_equiv.
    auto with set.
    auto with set.
    apply RESP.FM.add_2. eauto using prebase_trans.
Qed.

(** * Definition of the notion of partial derivatives.

    Partial derivatives are introduced in "Partial derivatives of regular
    expressions and finite automata construction" by Antimirov. *)

(* todo: revise the following *)
(** reset_nullable(rs) is true iff one of the regexp in rs is nullable *)
(* Definition reset_nullable (rs:RES.t): bool := *)
(*   RES.exists_ nullable rs. *)

Fixpoint always_rejects (g:regexp) : bool := 
  match g with 
    | Eps => false
    | Char _ => false
    | Any => false
    | Zero => true
    | Alt g1 g2 => always_rejects g1 && always_rejects g2
    | Cat g1 g2 => always_rejects g1 || always_rejects g2
    | Star _ => false
  end.

(** reset_always_rejects(rs) is true iff all regexps in rs always rejects *)
Definition reset_always_rejects (rs:RES.t): bool :=
  RES.for_all always_rejects rs.

(* todo: add calls to opt_ag to nullable and pdrv as in Parser.v *)

Definition bool_type (b:bool) := 
  match b with true => Unit_t | false => Void_t end.

(** nullable (r) returns (true, f) iff r can match the empty string and 
    f returns all values that are the results of parsing the empty string. *)
Fixpoint nullable (r:regexp) : 
  {b:bool & bool_type b ->> List_t (regexp_type r)} :=
  match r return {b:bool & bool_type b ->> List_t (regexp_type r)} with
    | Zero => existT _ false xzero
    | Eps => existT _ true (xcons xid xempty)
    | Char _ | Any => existT _ false xzero
    | Cat r1 r2 => 
      match nullable r1, nullable r2 with
        | existT true f1, existT true f2 => 
          existT _ true (xcomp (xpair f1 f2) xcross)
        | _, _ => existT _ false xzero
      end
    | Alt r1 r2 => 
      match nullable r1, nullable r2 with
        | existT true f1, existT true f2 => 
          existT _ true
            (xcomp (xpair (xcomp f1 (xmap xinl)) (xcomp f2 (xmap xinr))) xapp)
        | existT true f1, existT false f2 => 
          existT _ true (xcomp f1 (xmap xinl))
        | existT false f1, existT true f2 => 
          existT _ true (xcomp f2 (xmap xinr))
        | _, _ => existT _ false xzero
      end
    | Star r1 => existT _ true (xcons xempty xempty)
  end.

(** Partial derivatives of a regular grammar w.r.t. a char. The following
  equations are for the case of a regexps.  For regular grammars, we also
  need to add xforms to get the list of parsing results.

  pdrv(a, void) = pdrv(a, epsilon) = {}
  pdrv(a, b) = if a=b then {epsilon} else {}
  pdrv(a, r1+r2) = pdrv(a,r1) \/ pdrv(a,r2)
  pdrv(a, r1 r2) =
    pdrv(a, r1)r2 \/ pdrv(a, r2),   if nullable(r1)
    pdrv(a, r1)r2, otherwise
  pdrv(a, r_star) = pdrv(a,r)r_star
*)
Fixpoint pdrv (a:char_t) (r:regexp): rs_xf_pair (regexp_type r) := 
  match r return rs_xf_pair (regexp_type r) with
    | Eps | Zero => @RES.empty_xform _
    | Char b => 
      if char_eq_dec a b then
        let (rs,f) := RES.singleton_xform Eps in
          existT _ rs (xcomp f (xmap (xchar a)))
      else @RES.empty_xform _
    | Any => 
      let (rs,f) := RES.singleton_xform Eps in
          existT _ rs (xcomp f (xmap (xchar a)))
    | Alt r1 r2 => 
      let (rs1, f1) := pdrv a r1 in
      let (rs2, f2) := pdrv a r2 in
        RES.union_xform (existT _ rs1 (xcomp f1 (xmap xinl)))
                        (existT _ rs2 (xcomp f2 (xmap xinr)))
    | Cat r1 r2 => 
      let rxc := cat_re_xform (pdrv a r1) r2 in
      match nullable r1 with
        | existT true fnull => 
          let (rs2, f2) := pdrv a r2 in
          RES.union_xform rxc
            (existT _ rs2 (xcomp f2 (xcomp (xpair (xcomp xunit fnull) xid) xcross)))
        | existT false _ => rxc
      end
    | Star r1 => 
      let (rsc, fc) := cat_re_xform (pdrv a r1) (Star r1) in
        existT _ rsc (xcomp fc (xmap (xcons xfst xsnd)))
  end.

(** pdrv_rex performs partial derviative calculation, similar to
    pdrv. However, it takes a re_xf_pair as input instead a regexp *)
Definition pdrv_rex (ty:type) (a:char_t) (rex:re_xf_pair ty) : rs_xf_pair ty := 
  let (r, f) := rex in
  let (rs, frs) := pdrv a r in
  existT _ rs (xcomp frs (xcomp (xmap f) xflatten)).

(** Partial derivatives over a regexp set; the result of the union 
    of taking partial derivatives on every regexp in the set *)
Definition pdrv_set (ty:type) (a:char_t) (rx:rs_xf_pair ty) : rs_xf_pair ty :=
  RES.fold_xform (fun rex rx1 => RES.union_xform (pdrv_rex a rex) rx1)
                 rx (@RES.empty_xform ty).

(* Definition pdrv_set (ty:type) (a:char_t) (rx:rs_xf_pair (List_t ty)) := *)
(*   projT1 (pdrv_set_xform a rx). *)

(** Word partial derivatives; 
    wpdrv(nil, rs) = rs
    wpdrv(a cons w, rs) = wpdrv(w, pdrv_set(a, rs)) *)
Fixpoint wpdrv ty (s:list char_t) (rx:rs_xf_pair ty): rs_xf_pair ty := 
  match s with
    | nil => rx
    | a:: s' => wpdrv s' (pdrv_set a rx)
  end.

Definition wpdrv_re_set s (rs:RES.t) : rs_xf_pair (RES.re_set_type rs)
  := wpdrv s (existT _ rs xsingleton).

(** ** Relating partial derivatives to prebase *)
Lemma pdrv_subset_prebase: 
  forall a r, RES.Subset (|pdrv a r|) (prebase r).
Proof. unfold erase; induction r; simpl; try (apply RESP.subset_refl).
  Case "Char".
    destruct_head; [apply RESP.subset_refl | apply RESP.subset_empty].
  Case "Cat".
    remember_rev (cat_re_xform (pdrv a r1) r2) as crx.
    destruct crx as [rsc fc].
    assert (H4: rsc = projT1 (pdrv a r1) $ r2).
      rewrite <- cat_re_xform_erase. rewrite Hcrx. trivial.
    destruct (nullable r1) as [b fnull]; destruct b.
    SCase "b=true".
      destruct (pdrv a r2) as [rs2 f2]. simpl.
      rewrite RES.union_xform_erase. simpl.
      rewrite H4. 
      apply RESP.FM.union_s_m. auto using set_cat_re_subset. trivial.
    SCase "b=false". simpl. rewrite H4.
      eapply RESP.FM.Subset_trans.
        eapply set_cat_re_subset. eassumption.
      apply RESP.union_subset_1.
  Case "Alt". 
    destruct (pdrv a r1) as [rs1 f1].
    destruct (pdrv a r2) as [rs2 f2].
    rewrite RES.union_xform_erase.
    apply RESP.FM.union_s_m; assumption.
  Case "Star". 
    remember_rev (cat_re_xform (pdrv a r) (Star r)) as crx.
    destruct crx as [rsc fc].
    assert (H4: rsc = projT1 (pdrv a r) $ (Star r)).
      rewrite <- cat_re_xform_erase. rewrite Hcrx. trivial.
    simpl. rewrite H4.
    apply RESF.map_subset. assumption.
Qed.

Lemma pdrv_subset_pdset: 
  forall a r, RES.Subset (|pdrv a r|) (pdset r).
Proof. unfold pdset; intros. 
  apply RESP.subset_add_2. apply pdrv_subset_prebase.
Qed.


(** Denotation semantics of regexp sets *)
(* Definition in_re_set (rs:RES.t) (s:list char_t) := *)
(*   exists r, RES.In r rs /\ in_re r s. *)

(* todo: restore the following lemmas about the new def of in_re_set *)

(* (** forall rs1 rs2 s1 s2, rs1 subseteq rs2 -> s1=s2 -> *)
(*       in_re_set rs1 s1 -> in_re_set rs2 s2 *) *)
(* Instance in_re_set_subset: Proper (RES.Subset ==> eq ==> impl) in_re_set. *)
(* Proof. intros rs1 rs2 H1 s1 s2 H2 H3. unfold in_re_set in *. *)
(*   sim. eexists.  *)
(*   split. eapply RESP.in_subset; eassumption. *)
(*     congruence. *)
(* Qed. *)

(* Instance in_re_set_equal: Proper (RES.Equal ==> eq ==> impl) in_re_set. *)
(* Proof. intros rs1 rs2 H1 s1 s2 H2 H3. unfold in_re_set in *. *)
(*   sim. exists x.  *)
(*   split. rewrite <- H1. assumption. *)
(*   crush. *)
(* Qed. *)

(* Lemma in_re_set_empty : forall s v, not (in_re_set RES.empty s v). *)
(* Proof. unfold in_re_set. intros. intro H. *)
(*   destruct H as [r [H2 _]]. *)
(*   apply RESP.Dec.F.empty_iff in H2. crush. *)
(* Qed. *)

(* Lemma in_re_set_singleton: *)
(*   forall r s, in_re_set (RES.singleton r) s <-> in_re r s. *)
(* Proof. unfold in_re_set.  *)
(*   intros; split; intros. *)
(*   Case "->". *)
(*     destruct H as [r0 [H2 H4]]. *)
(*     apply RESP.Dec.F.singleton_1 in H2. *)
(*     apply compare_re_eq_leibniz in H2. congruence. *)
(*   Case "<-". *)
(*     eauto using RESP.Dec.MSetDecideTestCases.test_In_singleton. *)
(* Qed. *)
        
(* Lemma in_re_set_union : forall rs1 rs2 s, *)
(*     in_re_set (RES.union rs1 rs2) s <-> *)
(*     in_re_set rs1 s \/ in_re_set rs2 s. *)
(* Proof.  split; intros. *)
(*   Case "->". *)
(*     unfold in_re_set in *. *)
(*     destruct H as [r [H2 H4]]. *)
(*     apply RESP.FM.union_1 in H2. *)
(*     destruct H2; [left | right]; eauto. *)
(*   Case "<-". *)
(*     destruct H. *)
(*       eapply in_re_set_subset. *)
(*         apply RESP.union_subset_1. reflexivity. trivial. *)
(*       eapply in_re_set_subset. *)
(*         apply RESP.union_subset_2. reflexivity. trivial. *)
(* Qed.       *)

(* Lemma in_re_set_map: forall m rs s, *)
(*   in_re_set (RESF.map m rs) s <->  *)
(*   exists r, RES.In r rs /\ in_re (RESF.get_fun m r) s. *)
(* Proof. unfold in_re_set; split; intros. *)
(*   Case "->".  *)
(*     destruct H as [r [H2 H4]]. *)
(*     apply re_set_map_elim in H2. crush. *)
(*   Case "<-". *)
(*     destruct H as [r [H2 H4]]. *)
(*     exists (RESF.get_fun m r).  *)
(*     split; try assumption. *)
(*     apply re_set_map_intro with (y:=r); trivial. *)
(* Qed. *)

(* Lemma in_re_set_cat_re : forall rs r s, *)
(*   in_re_set (rs $ r) s <-> *)
(*   exists s1 s2, s=s1++s2 /\ in_re_set rs s1 /\ in_re r s2. *)
(* Proof. intros. split; intros. *)
(*   Case "->". *)
(*     destruct r; simpl in H; *)
(*       try (apply (in_re_set_map _ rs s) in H; *)
(*            destruct H as [r10 [H2 H4]]; *)
(*            inversion_clear H4; *)
(*            unfold in_re_set; *)
(*            exists s1, s2; eauto). *)
(*     exists s, nil. *)
(*       crush. *)
(*       contradict H; apply in_re_set_empty. *)
(*   Case "<-". *)
(*     destruct H as [s1 [s2 [H2 [H4 H6]]]]. *)
(*     destruct r; simpl; *)
(*       try (apply in_re_set_map; *)
(*            unfold in_re_set in *; *)
(*            generalize InrCat; crush; fail). *)
(*       crush' false in_re. *)
(*       crush' false in_re. *)
(* Qed. *)

(** ** Correctness of partial derivatives:
      (a::l) in [[r]] iff l in [[pdrv(a,r)]] *)
Section PDRV_CORRECT.
  Hint Rewrite app_nil_l in_prod_iff.

  Local Ltac lprover :=
    repeat match goal with
      | [H: _ :: _ = nil |- _] => inversion H
      | [H:in_re_set RES.empty _ _ |- _] =>
        contradiction (RES.in_re_set_empty H)
      | [H:in_re_set_xform (RES.empty_xform _) _ _ |- _] =>
        contradiction (RES.empty_xform_corr H)
      | [H:in_re_set_xform (RES.singleton_xform ?r) _ _ |- _] => 
        apply (RES.singleton_xform_corr r) in H
      (* | [H: in_re_set (RES.singleton _) _ |- _] => *)
      (*   apply in_re_set_singleton in H *)
      (* | [|- in_re_set (RES.singleton _) _] => *)
      (*   apply in_re_set_singleton *)
      (* | [H: in_re_set (RES.union _ _) _ |- _] => *)
      (*   apply in_re_set_union in H *)
      (* | [|- in_re_set (RES.union _ _) _] => *)
      (*   apply in_re_set_union *)
      (* | [|- in_re _ _] => econstructor *)
      | _ => in_regexp_inv
    end.

  Local Ltac in_regexp_contra :=
    match goal with 
      | [H1: forall v, ~ in_regexp ?R ?S v, H: in_regexp ?R ?S ?V |- _] => 
        contradict H; crush
    end.

  Lemma nullable_corr: forall r,
    match nullable r with
      | existT true f => 
        (exists v, in_regexp r nil v) /\
        (forall v, in_regexp r nil v -> In v (xinterp f tt)) /\
        (forall v, In v (xinterp f tt) -> in_regexp r nil v)
      | existT false f => forall v, ~ in_regexp r nil v
    end.
  Proof. induction r; fold interp in *.
    Case "Eps". crush.
    Case "Zero". intro. destruct v.
    Case "Char". intro. intro. in_regexp_inv.
    Case "Any". intro. intro. in_regexp_inv.
    Case "Cat". simpl.
      destruct (nullable r1) as [x1 f1]; destruct x1;
      destruct (nullable r2) as [x2 f2]; destruct x2;
      try (intros; intro; in_regexp_inv; in_regexp_contra).
      split; [crush | idtac].
        intros. split; intros.
        SCase "->". in_regexp_inv. xinterp_simpl; crush_hyp.
        SCase "<-". xinterp_simpl. destruct v as [v1 v2]. crush.
    Case "Alt". simpl.
      destruct (nullable r1) as [x1 f1]; destruct x1;
      destruct (nullable r2) as [x2 f2]; destruct x2.
      SCase "true true".
        split; [crush | idtac].
        xinterp_simpl.
        split; intros. 
          in_regexp_inv.
          match goal with
            | [H:In v (map inl _ ++ map inr _) |- _] =>
              apply in_app_or in H; destruct H;
              apply Coqlib.list_in_map_inv in H; crush
          end.
      SCase "true false".
        xinterp_simpl. crush. 
          in_regexp_inv; in_regexp_contra.
          apply Coqlib.list_in_map_inv in H. crush.
      SCase "false true".
        xinterp_simpl. crush. 
          in_regexp_inv; in_regexp_contra.
          apply Coqlib.list_in_map_inv in H. crush.
      SCase "false false".
        intros. intro. in_regexp_inv; crush_hyp.
    Case "Star". simpl. 
      crush. in_regexp_inv.
  Qed.

  Lemma nullable_corr2: forall r v,
    in_regexp r nil v -> 
    match nullable r with
      | existT true f => In v ((xinterp f) tt)
      | existT false f => False
    end.
  Proof. intros. generalize (nullable_corr r); intro.
    destruct (nullable r) as [x f].
    destruct x; crush_hyp.
  Qed.

  (* todo: revise the following *)
  (* Instance nullable_proper: Proper (RES.E.eq ==> eq) nullable. *)
  (* Proof. unfold Proper, respectful. intros. *)
  (*   apply compare_re_eq_leibniz in H. crush. *)
  (* Qed. *)

  Hint Extern 3 (in_re_set_xform (RES.singleton_xform ?r) ?s ?v) =>
    apply RES.singleton_xform_corr.

  Lemma pdrv_corr : forall r a s v, 
     in_regexp r (a :: s) v <-> in_re_set_xform (pdrv a r) s v.
  Proof. induction r.
    Case "Eps". simpl; split; intros; sim; [lprover | destruct x].
    Case "Zero". simpl. split; intros; sim; [lprover | destruct x].
    Case "Char".
      intros; simpl.
      destruct (char_eq_dec a c).
      SCase "a=c". subst.
        rewrite in_re_set_xform_comp2.
        split; intros.
          in_regexp_inv.
          sim; lprover.
      SCase "a<>c". split; intros; lprover.
    Case "Any". simpl; intros. rewrite in_re_set_xform_comp2.
      split; intros.
      in_regexp_inv. 
      sim; lprover.
    Case "Cat". simpl; intros.
      remember_rev (cat_re_xform (pdrv a r1) r2) as cx. 
      destruct cx as [rsc fc].
      generalize (nullable_corr r1); intro H10.
      remember_rev (nullable r1) as nr. destruct nr as [n fnull].
      remember_rev (pdrv a r2) as pr2. destruct pr2 as [rs2 f2].
      split; intros.
      SCase "->".
        apply inv_cat in H. destruct H as [s1 [s2 [v1 [v2]]]]. crush.
        destruct s1 as [| b s1'].
        SSCase "s1=nil".
          destruct n.
          SSSCase "nullable r1".
            rewrite RES.union_xform_corr. right.
            assert (H4:in_re_set_xform (pdrv a r2) s v2).
              apply IHr2; crush.
            rewrite Hpr2 in H4.
            apply in_re_set_xform_elim2 in H4.
            destruct H4 as [v' H4]. exists v'. xinterp_simpl. crush.
          SSSCase "~ (nullable r1)". in_regexp_contra.
        SSCase "s1=b::s1'".
          destruct n;
            [rewrite RES.union_xform_corr; left | idtac];
            rewrite <- Hcx;
            apply cat_re_xform_corr; exists s1', s2, v1, v2;
            clear H10 IHr2 Hpr2; crush_hyp.
      SCase "<-".
        destruct n.
        SSCase "nullable r1".
          apply RES.union_xform_corr in H.
          destruct H.
          SSSCase "s in (pdrv a r1) $ r2".
            rewrite <- Hcx in H.
            apply cat_re_xform_corr in H.
            destruct H as [s1 [s2 [v1 [v2 H]]]]. 
            apply InCat with (s1:= (a::s1)) (s2:=s2) (v1:=v1) (v2:=v2); crush.
          SSSCase "s in (pdrv a r2)".
            destruct v as [v1 v2].
            apply in_re_set_xform_elim2 in H.
            destruct H as [v' H]. 
            xinterp_simpl. sim.
            apply in_prod_iff in H0.
            apply InCat with (s1:=nil) (s2:=a::s) (v1:=v1) (v2:=v2); crush.
        SSCase "not (nullable r1)".
          rewrite <- Hcx in H.
          apply cat_re_xform_corr in H; fold interp in *.
          destruct H as [s1 [s2 [v1 [v2 H]]]]. 
          apply InCat with (s1:= (a::s1)) (s2:=s2) (v1:=v1) (v2:=v2); crush.
    Case "Alt". simpl; intros.
      remember_rev (pdrv a r1) as pr1. destruct pr1 as [rs1 f1].
      remember_rev (pdrv a r2) as pr2. destruct pr2 as [rs2 f2].
      rewrite RES.union_xform_corr.
      split; intros.
      SCase "->".
        in_regexp_inv; 
           [left; apply IHr1 in H; rewrite Hpr1 in H | 
            right; apply IHr2 in H; rewrite Hpr2 in H];
          apply in_re_set_xform_elim2 in H;
          destruct H as [v' H]; exists v';
          xinterp_simpl; crush.
      SCase "<-". 
        destruct H;
          apply in_re_set_xform_elim2 in H; sim;
          xinterp_simpl; apply Coqlib.list_in_map_inv in H0;
          sim; [eapply InAlt_l | eapply InAlt_r]; crush.
    Case "Star". simpl; intros.
      rewrite in_re_set_xform_comp2.
      split; intros.
      SCase "->".
        in_regexp_inv.
        exists (x1, x2); split; [idtac | trivial].
        apply cat_re_xform_corr with (r:=Star r).
        destruct x as [|b x']; [crush | idtac].
        exists x', x0, x1, x2. crush_hyp.
      SCase "<-".
        destruct H as [[v1 v2] [H2 H4]].
        apply cat_re_xform_corr with (r:=Star r) in H2.
        destruct H2 as [s1 [s2 H2]].
        apply InStar_cons with (s1:= (a::s1)) (s2:=s2) (v1:=v1) (v2:=v2); crush.
  Qed.

End PDRV_CORRECT.

(* todo: restore the following lemmas *)

(* Lemma reset_nullable_corr rs: reset_nullable rs = true <-> in_re_set rs nil. *)
(* Proof. unfold reset_nullable, in_re_set.  *)
(*     generalize (nullable_proper); intro. *)
(*     split; intro. *)
(*     Case "->". *)
(*       apply RES.exists_spec in H0; [idtac | trivial]. *)
(*       unfold RES.Exists in H0. *)
(*       generalize nullable_corr; crush_hyp. *)
(*     Case "<-". *)
(*       apply RES.exists_spec; [trivial | idtac]. *)
(*       unfold RES.Exists. *)
(*       generalize nullable_corr; crush_hyp. *)
(* Qed. *)
      
(** [always_rejects] is correct. *)
(* Lemma always_rejects_corr (r:regexp) :  *)
(*   always_rejects r = true -> forall ls, ~ in_re r ls. *)
(* Proof. *)
(*   induction r; crush. *)
(*   Case "Zero". intro H2. inversion H2. *)
(*   Case "Cat". intro H2. *)
(*     apply orb_prop in H. *)
(*     destruct H; inversion H2; crush_hyp. *)
(*   Case "Alt". intro H2. *)
(*     apply andb_prop in H. inversion H2; crush_hyp. *)
(* Qed. *)

(* Instance always_rejects_proper: Proper (RES.E.eq ==> eq) always_rejects. *)
(* Proof. unfold Proper, respectful. intros. *)
(*   apply compare_re_eq_leibniz in H. crush. *)
(* Qed. *)

(* Lemma reset_always_rejects_corr rs:  *)
(*   reset_always_rejects rs = true -> forall ls, ~ in_re_set rs ls. *)
(* Proof. unfold reset_always_rejects, in_re_set. intros. intro H2. *)
(*   apply RES.for_all_spec in H; [idtac | apply always_rejects_proper]. *)
(*   unfold RES.For_all in H.  *)
(*   generalize always_rejects_corr. crush_hyp. *)
(* Qed. *)


(* Definition reset_always_rejects (rs:RES.t): bool := *)
(*   RES.for_all always_rejects rs. *)


(** ** Properties of [pdrv_rex], [pdrv_set], and [wpdrv] *)

Lemma pdrv_rex_erase: forall ty a (rex: re_xf_pair ty),
  |pdrv_rex a rex| = |pdrv a (projT1 rex)|.
Proof. intros. unfold pdrv_rex.
  destruct rex as [r f]. 
  remember (pdrv a r) as pa; destruct pa as [rs frs].
  simpl. rewrite <- Heqpa. trivial.
Qed.

Lemma pdrv_rex_corr: forall t (rex:re_xf_pair t) a s v,
  in_re_xform rex (a::s) v <-> in_re_set_xform (pdrv_rex a rex) s v.
Proof. intros.
    unfold pdrv_rex. destruct rex as [r f].
    remember_rev (pdrv a r) as px. destruct px as [rs frs]. simpl.
    intros; split; intros.
    Case "->". destruct H as [v' [H2 H4]].
      apply pdrv_corr in H2.
      rewrite Hpx in H2.
      apply in_re_set_xform_elim2 in H2. destruct H2 as [v1 H2].
      exists v1. 
      split; [crush | idtac].
      xinterp_simpl. apply Coqlib.in_flatten_iff; crush.
    Case "<-". destruct H as [v' [H2 H4]].
      xinterp_simpl. apply Coqlib.in_flatten_iff in H4.
      destruct H4 as [l [H4 H6]].
      apply in_map_iff in H4. destruct H4 as [v1 [H4 H8]].
      exists v1. rewrite pdrv_corr. crush.
Qed.

Lemma pdrv_set_in: forall ty (rx:rs_xf_pair ty) r a,
  RES.In r (|pdrv_set a rx|) <->
  exists r', RES.In r' (|rx|) /\ RES.In r (|pdrv a r'|).
Proof. intros. unfold erase. unfold pdrv_set. 
  rewrite RES.fold_xform_erase
    with (comb2:=fun r rs1 => RES.union (|pdrv a r|) rs1).
  split.
  Case "->". 
    simpl.
    apply RESP.fold_rec_nodep; intros.
    SCase "rs=empty". re_set_simpl.
    SCase "rs nonempty".
      apply RESP.FM.union_1 in H1; destruct H1; crush.
  Case "<-".
    apply RESP.fold_rec_bis; intros.
      sim. apply H0. exists x. crush.
      sim; re_set_simpl.
      sim. apply RES.union_spec.
        apply RESP.FM.add_iff in H2; destruct H2.
          apply compare_re_eq_leibniz in H2. crush.
        crush.
  Case "assumption of fold_xform_erase".
    intros. rewrite RES.union_xform_erase.
    f_equal. apply pdrv_rex_erase.
Qed.

Lemma pdrv_set_trans: forall ty r (rx:rs_xf_pair ty) a, 
  RES.Subset (|rx|) (pdset r) -> 
  RES.Subset (|pdrv_set a rx|) (pdset r).
Proof. intros. intro r1; intro H2.
  apply pdrv_set_in in H2. destruct H2 as [r' [H4 H6]].
  apply pdrv_subset_pdset in H6.
  eauto using pdset_trans.
Qed.

Lemma pdrv_set_erase_subset: 
  forall ty1 ty2 a (rx1:rs_xf_pair ty1) (rx2:rs_xf_pair ty2),
    erase_eq rx1 rx2 ->
    erase_subset (pdrv_set a rx1) (pdrv_set a rx2).
Proof. unfold erase_eq. 
  intros ty1 ty2 a rs1 rs2 H r H2.
  apply pdrv_set_in in H2. sim.
  apply pdrv_set_in. exists x. rewrite <- H. crush.
Qed.

Lemma pdrv_set_erase_eq:
  forall ty1 ty2 a (rx1:rs_xf_pair ty1) (rx2:rs_xf_pair ty2),
    erase_eq rx1 rx2 ->
    erase_eq (pdrv_set a rx1) (pdrv_set a rx2).
Proof.  intros. apply erase_subset_antisym.
  apply pdrv_set_erase_subset. trivial.
  apply pdrv_set_erase_subset. unfold erase_eq in *. symmetry. trivial.
Qed.

Lemma pdrv_set_corr: forall ty a (rx:rs_xf_pair ty) s v,
  in_re_set_xform (pdrv_set a rx) s v <-> 
  in_re_set_xform rx (a::s) v.
Proof. intros. unfold pdrv_set.
  apply RES.fold_xform_rec.
  Case "equality respecting".
    intros. rewrite H0. trivial.
  Case "inductive case".
    intros.
    rewrite RES.union_xform_corr.
    rewrite RES.add_xform_corr.
    rewrite pdrv_rex_corr.
    crush. 
      right; apply H; apply H1.
      right. apply H0; apply H1.
  Case "base".
    split; intro H.
      contradict H; generalize RES.empty_xform_corr; crush.
      apply in_re_set_xform_elim2 in H. sim. 
        contradiction (RES.in_re_set_empty H).
Qed.

Lemma wpdrv_app: forall ty w1 w2 (rx:rs_xf_pair ty),
  wpdrv (w1 ++ w2) rx = wpdrv w2 (wpdrv w1 rx). 
Proof. induction w1; intros. 
  simpl; trivial.
  simpl. rewrite IHw1. trivial.
Qed.

Lemma wpdrv_corr: forall ty s1 s2 (rx:rs_xf_pair ty) v, 
  in_re_set_xform (wpdrv s1 rx) s2 v <-> in_re_set_xform rx (s1 ++ s2) v.
Proof. induction s1. crush.
  intros. simpl.
  split; intros.
    apply IHs1 in H. apply pdrv_set_corr in H. trivial.
    apply IHs1. apply pdrv_set_corr. trivial.
Qed.

Lemma wpdrv_pdset_trans : forall ty w (rx:rs_xf_pair ty) r, 
  RES.Subset (|rx|) (pdset r) -> 
  RES.Subset (|wpdrv w rx|) (pdset r).
Proof. induction w; [auto | idtac].
  intros; simpl; eauto using pdrv_set_trans.
Qed.

Theorem wpdrv_subset_pdset : forall w r,
  RES.Subset (| wpdrv_re_set w (RES.singleton r) |) (pdset r).
Proof.  intros; apply wpdrv_pdset_trans.
  unfold pdset. intro r'; intros.
  apply RESP.FM.singleton_iff in H.
  auto with set.
Qed.

Lemma wpdrv_erase_eq:
  forall ty1 ty2 s (rx1:rs_xf_pair ty1) (rx2:rs_xf_pair ty2),
    erase_eq rx1 rx2 ->
    erase_eq (wpdrv s rx1) (wpdrv s rx2).
Proof. induction s. crush.
  intros. simpl. apply IHs. apply pdrv_set_erase_eq. trivial.
Qed.

(* todo: a trivial lemma; maybe remove *)
Lemma wpdrv_re_set_pdset_trans : forall w rs r,
  RES.Subset rs (pdset r) -> RES.Subset (|wpdrv_re_set w rs|) (pdset r).
Proof. generalize wpdrv_pdset_trans. crush. Qed.

Lemma wpdrv_re_set_corr rs w str v:
  in_re_set rs (w++str) v <->
  in_re_set_xform (wpdrv_re_set w rs) str v.
Proof. unfold wpdrv_re_set.
  rewrite wpdrv_corr. 
  simpl. split; intros; crush.
Qed.
    
(** * Define [RESetSet], which is a set of RES. 

  It supports (1) a powerset operation from RESet, and (2) a get_index
  operation that returns the index of a RES. *)

Module POW := ListPowerSet RES.

(** A set of regexp sets *)
Module RESetSet.
  Include POW.MM.
  Include WMoreProperties POW.MM.

  (** The following operations assume the set is implemented by a list. *)

  Definition get_element (n:nat) (s:t) : option elt := 
    nth_error (elements s) n.

  (** Given an element e, find its index in the set *)
  Definition get_index (e:elt) (s:t) : option nat :=
    Coqlib.find_index E.eq E.eq_dec e (elements s).

  (** add set s2 to s1; when they are disjoint, the elments
     of the resulting set should be (elements s1) ++ (elements s2) *)
  (* Definition add_set (s1 s2:t) := union s2 s1. *)
  Definition add_set (s1 s2:t) := fold add s2 s1.

  (** s2's elements are an extension of s1's elements *)
  Definition elements_ext (s1 s2:t) := 
    exists s, elements s2 = elements s1 ++ elements s.

  (* Lemmas *)

  (** The strong spec of add given that the set is implemented by a list. *)
  Lemma add_elements: forall s elm,
    if (mem elm s) then elements (add elm s) = elements s
    else elements (add elm s) = elements s ++ (elm :: nil).
  Proof. intros. simpl.
    unfold elements, Raw.elements, mem.
    remember (this s) as ls. generalize ls.
    induction ls0; intros; [crush | idtac].
      remember_destruct_head as me.
      Case "Raw.mem elm (a:: ls0)".
        simpl in Hme. simpl.
        destruct_head; [trivial| rewrite Hme in IHls0; congruence].
      Case "not (Raw.mem elm (a:: ls0))".
        simpl in Hme. simpl.
        destruct_head. crush.
          rewrite Hme in IHls0. crush.
  Qed.

  Lemma add_elements_1: forall s elm,
    mem elm s = true -> elements (add elm s) = elements s.
  Proof. intros. generalize (add_elements s elm); intro.
    rewrite H in H0. trivial.
  Qed.

  Lemma add_elements_2: forall s elm,
    mem elm s = false -> elements (add elm s) = elements s ++ (elm :: nil).
  Proof. intros. generalize (add_elements s elm); intro.
    rewrite H in H0. trivial.
  Qed.

  Lemma add_ext elm s: elements_ext s (add elm s).
  Proof. unfold elements_ext. 
    generalize (add_elements s elm).
    destruct (mem elm s); intros.
      exists empty. crush.
      exists (singleton elm). crush.
  Qed.

  Lemma add_cardinal_leq e s: cardinal s <= cardinal (add e s).
  Proof. intros. repeat rewrite cardinal_spec.
    generalize (add_elements s e). intro H;
    destruct_head in H; crush.
  Qed.

  Lemma add_cardinal e s :
    mem e s = false -> cardinal (add e s) = 1 + cardinal s.
  Proof. intros. repeat rewrite cardinal_spec.
    rewrite add_elements_2 by assumption.
    rewrite app_length. simpl. omega.
  Qed.

  (* todo: merge this with in_regexp_contra and move to commontacs.v *)
  Ltac find_contra :=
    match goal with
      | [H1:?p, H2:~ ?p |- _] => contradict H1; trivial
    end.

  Lemma add_set_elements: forall s2 s1,
    disjoint s1 s2 -> elements (add_set s1 s2) = elements s1 ++ elements s2.
  Proof. unfold add_set, disjoint, fold, POW.MM.In.
    destruct s2 as [ls2 ok2]. simpl.
    induction ls2.
    Case "base". crush.
    Case "a::ls2". simpl; intros.
      assert (forall x : POW.MM.elt,
                ~ (POW.MM.Raw.In x (POW.MM.this (add a s1)) /\ POW.MM.Raw.In x ls2)).
        intros x. generalize (H x). unfold POW.MM.Raw.In.
        intro. contradict H0. simpl in *.
        destruct H0 as [H2 H4].
        generalize (is_ok s1); intro.
        apply Raw.add_spec in H2; [idtac | assumption].
        destruct H2.
        SCase "x=a".
          rewrite H1 in H4.
          inversion ok2. find_contra.
        SCase "x in s1". split; auto.
      assert (POW.MM.Raw.Ok ls2).
        inversion ok2. assumption.
      use_lemma IHls2 by eassumption.
      unfold flip.
      rewrite H2.
      generalize (add_elements s1 a); intro.
      remember_destruct_head in H3 as mm.
      SCase "a in s1".
        generalize (H a). intro H4.
        contradict H4.
        apply POW.PP.FM.mem_2 in Hmm.
        split.  assumption.
          unfold  POW.MM.Raw.In. auto with set.
      SCase "~ a in s1". crush.
  Qed.

  Lemma add_set_ext s1 s2:
    disjoint s1 s2 -> elements_ext s1 (add_set s1 s2).
  Proof. unfold elements_ext. intros.
    exists s2. auto using add_set_elements. 
  Qed.
     
  Lemma add_set_in: forall x s1 s2,
    In x (add_set s1 s2) -> In x s1 \/ In x s2.
  Proof. unfold add_set. intros x s1 s2.
    apply POW.PP.fold_rec_bis.
      intros. destruct (H0 H1); rewrite <- H; crush.
      crush.
      intros. 
        apply POW.PP.FM.add_iff in H2; destruct H2;
          auto with set.
        destruct (H1 H2); auto with set.
  Qed.

  Lemma add_set_empty: forall s, add_set s empty = s.
  Proof. unfold add_set. intros. rewrite POW.PP.fold_empty. trivial. Qed.

  Lemma get_element_some_lt: forall n s e,
    get_element n s = Some e -> n < cardinal s.
  Proof. unfold get_element, cardinal, Raw.cardinal. 
     eauto using Coqlib.nth_error_some_lt.
  Qed.

  Lemma get_element_eq: forall s1 s2 n,
    elements s1 = elements s2 -> get_element n s1 = get_element n s2.
  Proof. unfold get_element; crush. Qed.

  Lemma get_element_ext s1 s2 n:
    elements_ext s1 s2 -> n < cardinal s1
      -> get_element n s2 = get_element n s1.
  Proof. unfold elements_ext, get_element. intros. sim.
    rewrite H. generalize Coqlib.nth_error_app_lt. crush.
  Qed. 

  Lemma get_element_add: forall n s e1 e,
    get_element n s = Some e -> get_element n (add e1 s) = Some e.
  Proof. intros. generalize (add_ext e1 s). 
    use_lemma get_element_some_lt by eassumption. intro.
    erewrite get_element_ext; eassumption. 
  Qed.

  Lemma get_element_add_set: forall n s s' e,
    get_element n s = Some e -> get_element n (add_set s s') = Some e.
  Proof.
    unfold add_set. intros.
    apply POW.PP.fold_rec. crush.
      auto using get_element_add.
  Qed.

  Lemma get_index_spec: forall e s n,
    get_index e s = Some n <-> Coqlib.first_occur E.eq e (elements s) n.
  Proof. unfold get_index; intros.
    apply Coqlib.find_index_spec. apply E.eq_equiv.
  Qed.

  Lemma get_index_none: forall e s,
    get_index e s = None -> mem e s = false.
  Proof. unfold get_index. intros.
    apply Coqlib.find_index_none in H.
    apply negb_true_iff. unfold negb.
    remember_destruct_head as mm; try trivial.
      apply POW.MM.mem_spec in Hmm.
      apply POW.PP.FM.elements_iff in Hmm.
      crush.
  Qed.

  Lemma get_index_get_element: forall e s n,
    get_index e s = Some n -> 
    exists e', get_element n s = Some e' /\ E.eq e e'.
  Proof. intros. apply get_index_spec in H.
    unfold Coqlib.first_occur in H. crush.
  Qed.

  Lemma get_index_none_get_element e s: 
    get_index e s = None ->
    get_element (cardinal s) (add e s) = Some e.
  Proof. intros. apply get_index_none in H.
    unfold get_element. 
    rewrite add_elements_2 by assumption.
    rewrite cardinal_spec.
    rewrite Coqlib.nth_error_app_eq by trivial.
    trivial.
  Qed.

  Lemma get_index_some_lt: forall e s n,
    get_index e s = Some n -> n < cardinal s.
  Proof. intros. apply get_index_spec in H.
    unfold Coqlib.first_occur in H. destruct H as [_ [y [H2 _]]].
    apply Coqlib.nth_error_some_lt in H2. auto.
  Qed.

  Lemma get_index_ext s1 s2 e n:
    elements_ext s1 s2 -> get_index e s1 = Some n ->
    get_index e s2 = Some n.
  Proof. unfold elements_ext, get_index.
    repeat (rewrite Coqlib.find_index_spec by apply E.eq_equiv).
    generalize Coqlib.first_occur_app. crush.
  Qed.

  Lemma get_index_add_monotone: forall e e1 s n,
    get_index e s = Some n <->
    n < cardinal s /\ get_index e (add e1 s) = Some n.
  Proof. intros.
    generalize (add_elements s e1); intro.
    destruct_head in H.
    Case "mem e1 s".
      unfold get_index.
      generalize get_index_some_lt; crush.
    Case "~ mem e1 s". 
      unfold elt, RES.t in *.
      split; intros. 
      SCase "->". 
        use_lemma get_index_some_lt by eassumption.
        apply get_index_spec in H0. 
        unfold Coqlib.first_occur in H0. sim. trivial.
        apply get_index_spec; unfold Coqlib.first_occur.
        rewrite H. rewrite Coqlib.firstn_eq_lt by trivial.
        split; [crush | idtac].
          exists x. rewrite Coqlib.nth_error_app_lt by trivial. crush.
      SCase "<-".
        sim. apply get_index_spec in H1. apply get_index_spec.
        unfold Coqlib.first_occur in *.
        sim. 
          erewrite <- Coqlib.firstn_eq_lt by trivial.
            rewrite H in H1. eassumption.
          exists x. erewrite <- Coqlib.nth_error_app_lt by trivial.
            rewrite H in H2. crush.
  Qed.

  Lemma disjoint_add_add_set: forall s ss1 ss2, mem s ss1 = false ->
    disjoint (add s ss1) ss2 -> disjoint ss1 (add_set (singleton s) ss2).
  Proof. intros. unfold disjoint. intros x H2.
    destruct H2.
    apply add_set_in in H2. destruct H2.
    Case "x in {s}".
      apply POW.PP.FM.singleton_1 in H2. rewrite <- H2 in H1.
      apply POW.PP.FM.mem_1 in H1. congruence.
    Case "x in ss2".
      unfold disjoint in H0.
      generalize (H0 x); intro H3; contradict H3.
      auto with set.
  Qed.

  Lemma disjoint_add_singleton: forall s ss1 ss2,
    disjoint (add s ss1) ss2 -> disjoint (singleton s) ss2.
  Proof. unfold disjoint; intros. intro H2.
    destruct H2.
    apply POW.PP.FM.singleton_1 in H0.
    generalize (H x). intro H4.
    contradict H4. auto with set.
  Qed.

End RESetSet.

(* seems to need this to get around of a coq bug *)
Module RESS := RESetSet.
Module RESSP :=MSetProperties.WProperties RESetSet.
Module RESSMP :=WMoreProperties RESetSet.

(** * Constructing a DFA from a regexp. The transforms in the DFA constructs
  the AST for the regexp. *)

Section DFA.
  (** Our [DFA] (really a deterministic finite-state transducer) has a number
     of states [n].  Each state corresponds to an [astgram], and in particular
     dfa_states[0] corresponds to the original grammar, and each other state
     corresponds to the derivative of dfa_states[0] with respect to some string
     of tokens [t1,...,tn].  We transition from states using the transition table.
     In particular, if we are in state [i], given input token [t], we compute
     our next state as [next_state] of [transition[i][t]].  The [next_xform] in 
     [transition[i][t]] says how to transform AST values extracted from 
     [next_state(transition[i][t])] to the type of AST values in [states[i]].  
     The [accept] row records which states are accepting states, while the
     [rejects] row records which states are failing states.  
     *)

  (** Instead of working directly in terms of lists of [char_p]'s, we instead
     work in terms of [token_id]'s where a [token_id] is just a [nat] in the
     range 0..[num_tokens]-1.  We assume that each [token_id] can be mapped
     to a list of [char_p]'s.  For example, in the x86 parser, our characters
     are bits, but our tokens represent bytes in the range 0..255.  So the
     [token_id_to_chars] function should extract the n bits corresponding to the
     byte value.  *)

  (** The initial regexp from which we will build the DFA *)
  Variable r: regexp.

  (** A state is a set of regexps, corresponding to partial derivatives of
      the starting regexp w.r.t. some word. *)
  Definition state := RES.t.

  (** a set of states; can use something more efficient than lists *) 
  Definition states := RESS.t.

  Definition state_is_wf (s:state) : Prop :=
    exists w, RES.Equal s (| wpdrv_re_set w (RES.singleton r) |).
  Definition wf_state := {s:state | state_is_wf s}.

  Definition states_are_wf (ss: states) : Prop := RESS.For_all state_is_wf ss.
  Definition wf_states := {ss:states | states_are_wf ss}.

  Definition extract_wf_state (ss: wf_states) (n:nat)
             (s: {s:state | state_is_wf s
                            /\ RESS.get_element n (proj1_sig ss) = Some s})
    : wf_state.
    destruct s. destruct a.
    refine (exist _ x _).
    apply H.
  Defined.

  (** ** Operations listed to the well-formed states level *)

  Definition cardinal_wfs (ss:wf_states) := RESS.cardinal (proj1_sig ss).

  Definition elements_wfs (ss: wf_states) := RESS.elements (proj1_sig ss).

  (** ss2 is an element extension of ss1 *)
  Definition wfs_ext (ss1 ss2: wf_states) := 
    exists ss, elements_wfs ss2 = elements_wfs ss1 ++ elements_wfs ss.

  Instance state_wf_imp: Proper (RESet.Equal ==> impl) state_is_wf.
  Proof. unfold Proper, respectful, impl. intros s1 s2; intros.
    destruct H0 as [w H2].
    exists w. rewrite <- H. trivial.
  Qed.
    
  Instance state_wf_equal: Proper (RESet.Equal ==> iff) state_is_wf.
  Proof. unfold Proper, respectful. intros s1 s2 H.
    split; apply state_wf_imp; [trivial | symmetry; trivial].
  Qed.

  (** A pair of well-formed states and xforms *)
  Definition wfs_xf_pair (ty:type) := 
    {s: wf_state & RES.re_set_type (proj1_sig s) ->> List_t ty}.

  Definition wpdrv_wf (w: list char_t) (s: wf_state): 
    wfs_xf_pair (RES.re_set_type (proj1_sig s)).
    refine (existT _ (exist _ (| wpdrv_re_set w (proj1_sig s) |) _) _).
    simpl. apply (projT2 (wpdrv_re_set w (proj1_sig s))).
    Grab Existential Variables.
    simpl.
    unfold state_is_wf; intros.
    destruct s as [s [w1 H]].
    unfold wpdrv. simpl in *.
    exists (w1++w). unfold wpdrv_re_set.
    rewrite wpdrv_app.
    apply wpdrv_erase_eq. trivial.
  Defined.

  (* Recursive Extraction wpdrv_wf. *)

  Definition emp_wfs: wf_states.
    refine (exist _ RESS.empty _).
    unfold states_are_wf, RESS.For_all. intros.
    apply RESSP.FM.empty_iff in H. destruct H.
  Defined.

  Definition singleton_wfs (s:wf_state): wf_states.
    refine (exist _ (RESS.singleton (proj1_sig s)) _).
    unfold states_are_wf, RESS.For_all. intros.
    apply RESSP.FM.singleton_1 in H.
    generalize (proj2_sig s). intro. rewrite <- H. trivial.
  Defined.

  Definition add_wfs (s:wf_state) (ss:wf_states): wf_states.
    refine (exist _ (RESS.add (proj1_sig s) (proj1_sig ss)) _).
    unfold states_are_wf; intros.
    unfold RESS.For_all. intros.
    destruct s as [s H2].
    destruct ss as [ss H4].
    apply RESSP.FM.add_iff in H. destruct H.
      simpl in H. rewrite <- H. trivial.
      apply H4. trivial.
  Defined.
  Notation "s ::: ss" := (add_wfs s ss) (at level 60, no associativity).

  Definition add_set_wfs (ss1 ss2:wf_states): wf_states.
    refine (exist _ (RESS.add_set (proj1_sig ss1) (proj1_sig ss2)) _).
    unfold RESS.add_set.
    apply RESSP.fold_rec_bis. crush.
      apply (proj2_sig ss1).
      intros.
      unfold states_are_wf.
      intros y H2.
      apply RESSP.FM.add_iff in H2.
      destruct H2.
        rewrite <- H2. apply (proj2_sig ss2). trivial.
        auto.
  Defined.
  Notation "ss1 +++ ss2" := (add_set_wfs ss1 ss2) (at level 59, left associativity).

  Definition get_index_wfs (s:wf_state) (ss:wf_states): option nat :=
    RESS.get_index (proj1_sig s) (proj1_sig ss).

  (** Strong spec of get_index_wfs *)
  Definition get_index_wfs2 (s:wf_state) (ss:wf_states) :
    {n | get_index_wfs s ss = Some n} + {get_index_wfs s ss = None}.
  refine (let gi := get_index_wfs s ss in
          (match gi return get_index_wfs s ss = gi -> _ with
            | Some n => fun H => inleft (exist _ n _)
            | None => fun H => inright _
           end) eq_refl); crush.
  Defined.

  Definition get_element_wfs (n:nat) (ss:wf_states) :=
    RESS.get_element n (proj1_sig ss).

  (** Strong spec of get_elemeng_wfs *)
  Definition get_element_wfs2 (n:nat) (ss:wf_states):
    {s: wf_state | get_element_wfs n ss = Some (proj1_sig s)}
    + {n >= cardinal_wfs ss}.
    refine (let ge := get_element_wfs n ss in
            (match ge return get_element_wfs n ss = ge -> _ with
               | Some rs => 
                 fun H => inleft (exist _ (exist state_is_wf rs _) _)
               | None => fun H => inright _ 
             end) eq_refl).
    Case "Some".
      simpl. trivial.
    Case "None".
      apply Coqlib.nth_error_none in H. trivial.
    Grab Existential Variables.
      unfold get_element_wfs in H.
      destruct ss as [ss H2]. simpl in *.
      apply H2.
        apply Coqlib.nth_error_in in H.
        assert (InA RESet.Equal rs (RESS.elements ss)).
          apply In_InA. apply RESet.eq_equiv. assumption.
        apply RESS.elements_spec1. trivial.
  Defined.

  (** ** Defining the DFA type *)
  
  (** Return the nth state in ss; if out of bound, return RES.empty *)
  Definition get_state (n:nat) (ss:wf_states): RES.t := 
    match get_element_wfs2 n ss with
      | inleft s => proj1_sig (proj1_sig s)
      | inright _ => RES.empty
    end.
  Notation "s .[ i ] " := (get_state i s) (at level 40).

  (** Entries in the transition matrix *)
  Record entry_t(rownum:nat)(ss:wf_states) := 
    { (** which state do we go to next *)
      next_state : nat ; 
      (** the [next_state] is in bounds with respect to the number of states *)
      next_state_lt : next_state < cardinal_wfs ss ; 
      (** how do we transform ASTs from the next state back to this state *)
      next_xform : RES.re_set_type (ss.[next_state]) ->>
                   List_t (RES.re_set_type (ss.[rownum]))
        (* interp (RES.re_set_type (ss.[next_state]))->  *)
        (* interp (List_t (RES.re_set_type (ss.[rownum]))) *)
    }.

  (** Rows in the transition matrix -- an entry for each token *)  
  Definition row_t(i:nat)(ss:wf_states) := list (entry_t i ss).

  (** This predicate captures the fact that the ith entry in a row holds
      the derivative of that row's corresponding RESet with respect
      to the ith token. *)
  (* Definition wf_row(gpos:nat)(ss:wf_states)(r:row_t gpos ss)(i:nat)(t:token_id) := *)
  (*   match nth_error r i with *)
  (*     | Some e =>  wpdrv_re_set (token_id_to_chars t) (ss.[gpos]) = *)
  (*                 existT _ (ss.[next_state e]) x  *)
  (*                 (* /\ xinterp x = (next_xform e) *) *)
  (*                 (* no longer true, because of the backward edges from  *)
  (*                    ss.[gpos] to some old state *) *)
  (*     | None => True *)
  (*   end. *)

  Definition wf_row (gpos:nat)(ss:wf_states)(row:row_t gpos ss)
             (i:nat)(t:token_id) :=
    match nth_error row i with
      | Some e =>
        forall str v, 
          in_re_set (ss.[gpos]) ((token_id_to_chars t) ++ str) v <->
          in_re_set_xform (existT _ (ss.[next_state e]) (next_xform e)) str v
      | None => True
    end.

  Record transition_t(ss:wf_states) := {
    (** which row are we talking about *)
    row_num : nat ; 
    (** the row's index is in range for the number of states we have *)
    row_num_lt : row_num < RESS.cardinal (proj1_sig ss) ;
    (** what are the transition entries *)
    row_entries : list (entry_t row_num ss) ;
    (** the list of values we get from this state when it is an accepting state *)
    row_nils : list (interp (RES.re_set_type (ss.[row_num]))) ; 
    (** have an entry in the row for each token *)
    row_entries_len : length row_entries = num_tokens ;
    (** each entry is the appropriate derivative *)
    row_entries_wf: forall i, wf_row row_entries i i ;
    (** the row_nils are what you get when you run [astgram_extract_nil] on the
        row's [astgram]. *)
    row_nils_wf : row_nils = re_set_extract_nil (ss.[row_num])
  }.

  (** The transition matrix is then a list of rows *)
  Definition transitions_t (ss:wf_states) := list (transition_t ss).

  Record DFA := {
    (** number of states in the DFA *)
    dfa_num_states : nat ; 
    (** the list of [astgram]s for the states *)
    dfa_states : wf_states ; 
    dfa_states_len : RESS.cardinal (proj1_sig dfa_states) = dfa_num_states ; 
    (** the transition matrix for the DFA -- see above. *)
    dfa_transition : transitions_t dfa_states ; 
    (** the number of states equals the number of rows. *)
    dfa_transition_len : length dfa_transition = dfa_num_states ; 
    (** the [row_num] of the ith row should be i *)
    dfa_transition_r : forall i, match nth_error dfa_transition i with 
                                   | Some r => row_num r = i
                                   | None => True
                                 end ;
    (** which states are accepting states -- no longer used *)
    dfa_accepts : list bool ; 
    dfa_accepts_len : length dfa_accepts = dfa_num_states ; 
    (** which states are failure states -- no longer used *)
    dfa_rejects : list bool ;
    dfa_rejects_len : length dfa_rejects = dfa_num_states
  }.
  
  (** ** Lemmas about wfs-level operations *)

  Hint Rewrite RESS.add_set_empty.

  Instance wfs_ext_refl: Reflexive wfs_ext.
  Proof. unfold wfs_ext. intro. exists emp_wfs; crush. Qed.

  Instance wfs_ext_trans: Transitive wfs_ext.
  Proof. unfold wfs_ext. intros ss1 ss2 ss3 H1 H2.
    destruct H1 as [ss1' H4].
    destruct H2 as [ss2' H8].
    assert (RESS.Subset (proj1_sig ss1') (proj1_sig ss2)).
      eapply RESSMP.elements_app_subset2; eassumption.
    use_lemma RESSMP.elements_app_disjoint by eassumption.
    assert (RESS.disjoint (proj1_sig ss1') (proj1_sig ss2')).
      rewrite H. assumption.
    exists (add_set_wfs ss1' ss2').
    unfold add_set_wfs, elements_wfs in *. simpl in *.
    rewrite RESS.add_set_elements by assumption.
    crush.
  Qed.

  Lemma wfs_ext_elements_ext ss ss':
    wfs_ext ss ss' -> RESS.elements_ext (proj1_sig ss) (proj1_sig ss').
  Proof. unfold wfs_ext, RESS.elements_ext. crush. Qed.

  Lemma wfs_ext_cardinal_leq: forall ss ss',
    wfs_ext ss ss' -> cardinal_wfs ss <= cardinal_wfs ss'.
  Proof. unfold cardinal_wfs, wfs_ext, elements_wfs. intros.
    repeat rewrite RESS.cardinal_spec. sim. rewrite H; crush.
  Qed.

  Lemma get_element_wfs_ext n ss ss': 
    wfs_ext ss ss' -> n < cardinal_wfs ss
      -> get_element_wfs n ss' = get_element_wfs n ss.
  Proof. intros. apply wfs_ext_elements_ext in H. 
    apply RESS.get_element_ext; auto.
  Qed.

  Lemma get_element_wfs_ext2: forall ss ss' n e,
    wfs_ext ss ss' -> get_element_wfs n ss = Some e
      -> get_element_wfs n ss' = Some e.
  Proof. intros. use_lemma RESS.get_element_some_lt by eassumption.
    erewrite get_element_wfs_ext; eassumption.
  Qed.

  Lemma get_index_get_element_wfs: forall s ss n,
    get_index_wfs s ss = Some n -> 
    exists rs, get_element_wfs n ss = Some rs /\ 
               RES.Equal (proj1_sig s) rs.
  Proof. unfold get_index_wfs, get_element_wfs. intros.
    apply RESS.get_index_get_element in H. crush.
  Qed.

  Lemma get_index_wfs_ext: forall s ss ss' n,
    wfs_ext ss ss' -> get_index_wfs s ss = Some n -> 
    get_index_wfs s ss' = Some n.
  Proof. unfold get_index_wfs. intros.
    use_lemma wfs_ext_elements_ext by eassumption.
    generalize RESS.get_index_ext. crush.
  Qed.


  Opaque RESS.elements. 
  Lemma wfs_ext_add s ss:
    RESS.mem (proj1_sig s) (proj1_sig ss) = false
    -> wfs_ext ss (add_wfs s ss).
  Proof. unfold wfs_ext, elements_wfs. intros.
    unfold add_set_wfs, add_wfs in *. simpl in *.
    exists (singleton_wfs s).
    rewrite RESS.add_elements_2 by assumption.
    crush.
  Qed.

  Lemma wfs_ext_add2 s ss:
    get_index_wfs s ss = None -> wfs_ext ss (s ::: ss).
  Proof. intros. apply wfs_ext_add. apply RESS.get_index_none. trivial.
  Qed.

  Lemma get_element_add_wfs_ext s ss ss' : 
    wfs_ext (s ::: ss) ss' 
      -> RESS.mem (proj1_sig s) (proj1_sig ss) = false
      -> get_element_wfs (cardinal_wfs ss) ss' = Some (proj1_sig s).
  Proof. unfold wfs_ext, elements_wfs, add_wfs, cardinal_wfs. simpl. intros.
    destruct H as [ss1 H2].
    unfold get_element_wfs, RESS.get_element.
    rewrite RESS.add_elements_2 in H2 by assumption.
    rewrite H2.
    rewrite app_ass.
    assert (H12:cardinal_wfs ss = length (RESS.elements (proj1_sig ss))).
      unfold cardinal_wfs. rewrite POW.MM.cardinal_spec. omega.
    rewrite Coqlib.nth_error_app_eq by crush.
    rewrite <- app_comm_cons. 
    crush.
  Qed.

  Lemma add_wfs_cardinal_leq s ss: 
    cardinal_wfs ss <= cardinal_wfs (s ::: ss).
  Proof. unfold add_wfs, cardinal_wfs. simpl. 
         generalize RESS.add_cardinal_leq. crush.
  Qed.

  Lemma add_wfs_cardinal s ss:
    get_index_wfs s ss = None ->
    cardinal_wfs (s ::: ss) = 1 + cardinal_wfs ss.
  Proof. intros.
    unfold cardinal_wfs. simpl.
    apply RESS.add_cardinal. apply RESS.get_index_none. trivial.
  Qed.

  Lemma add_singleton_cardinal (s:wf_state) ss:
    RESS.mem (proj1_sig s) (proj1_sig ss) = false ->
    cardinal_wfs (ss +++ singleton_wfs s) = 1 + cardinal_wfs ss.
  Proof. intros. unfold cardinal_wfs. repeat rewrite RESS.cardinal_spec.
    unfold add_set_wfs. simpl.
    rewrite RESS.add_set_elements. rewrite app_length.
    rewrite <- (RESS.cardinal_spec (RESS.singleton (proj1_sig s))).
    rewrite RESSP.singleton_cardinal. omega.
    apply RESSMP.disjoint_singleton. trivial.
  Qed.

  Transparent RESS.elements. 

  Lemma add_set_wfs_ext: forall ss ss',
    RESS.disjoint (proj1_sig ss) (proj1_sig ss') ->
    wfs_ext ss (ss +++ ss').
  Proof. unfold wfs_ext. intros.
    exists ss'. 
    unfold elements_wfs; simpl.
    apply RESS.add_set_elements. assumption.
  Qed.

  Lemma get_state_wfs_ext : forall n ss ss',
    wfs_ext ss ss' -> n < cardinal_wfs ss -> ss.[n] = ss'.[n].
  Proof. unfold get_state; intros.
    use_lemma wfs_ext_cardinal_leq by eassumption.
    destruct (get_element_wfs2 n ss); [idtac | omega].
    destruct s as [[rs1 H3] H4]. simpl in *.
    use_lemma RESS.get_element_some_lt by eassumption.
    destruct (get_element_wfs2 n ss'); [idtac | omega].
    destruct s as [[rs2 H6] H8]. simpl in *.
    rewrite (get_element_wfs_ext H) in H8 by assumption.
    crush.
  Qed.

  Lemma get_state_get_index_some: forall s ss n,
    get_index_wfs s ss = Some n ->
    RES.Equal (proj1_sig s) (ss.[n]).
  Proof. intros. 
      apply get_index_get_element_wfs in H. sim.
      unfold get_state.
      destruct (get_element_wfs2 n ss).
        destruct s0 as [[rs H4] H6].
          simpl. simpl in H6.
            assert (x=rs) by congruence. subst. assumption.
        apply RESS.get_element_some_lt in H. unfold cardinal_wfs in *. omega.
  Qed.

  Lemma get_state_get_index_none s ss:
    get_index_wfs s ss = None ->
    proj1_sig s = (s ::: ss).[cardinal_wfs ss].
  Proof. intros; unfold get_state.
    destruct (get_element_wfs2 (cardinal_wfs ss) (s ::: ss)).
      destruct s0 as [[rs H2] H4].
        simpl.
        apply RESS.get_index_none_get_element in H.
        unfold cardinal_wfs, add_wfs, get_element_wfs in H4. simpl in *.
        congruence.
      apply RESS.get_index_none in H.
      use_lemma RESS.add_cardinal by eassumption.
      unfold cardinal_wfs, add_wfs in *. simpl in *. omega.
  Qed.

  Lemma get_state_get_element_some: forall rs ss n,
    get_element_wfs n ss = Some rs -> rs = ss.[n].
  Proof. intros. unfold get_state.
    destruct (get_element_wfs2 n ss).
      destruct s as [s H2]. simpl. crush.
    apply RESS.get_element_some_lt in H. 
      unfold cardinal_wfs in *. omega.
  Qed.

  Lemma wpdrv_wf_corr w s s1 f1:
    wpdrv_wf w s = existT _ s1 f1 ->
    forall str v, 
      in_re_set (proj1_sig s) (w++str) v <-> 
      in_re_set_xform (existT _ (proj1_sig s1) f1) str v.
  Proof. intros.
    unfold wpdrv_wf in H. simpl in H. inversion H.
    subst s1. simpl in *.
    generalize (inj_pair2 _ _ _ _ _ H); clear H; intro.
    subst f1.
    rewrite wpdrv_re_set_corr.
    unfold in_re_set_xform, RES.in_re_set_xform.
    remember_rev (wpdrv_re_set w (proj1_sig s)) as wrs.
    destruct wrs as [rs f]. simpl; crush.
  Qed.

  Lemma wf_row_nil n ss i t: @wf_row n ss nil i t.
  Proof. unfold wf_row. rewrite Coqlib.nth_error_nil. trivial. Qed.

  (* Definition find_or_add (s:wf_state) (ss:wf_states) : wf_states * nat := *)
  (*   match get_index_wfs s ss with *)
  (*     | Some n => (emp_wfs, n) *)
  (*     | None => (singleton_wfs s, RESS.cardinal (proj1_sig ss)) *)
  (*   end. *)

  (* Lemma find_or_add_wfs_ext: forall s ss, *)
  (*   wfs_ext ss (ss +++ (fst (find_or_add s ss))). *)
  (* Proof. intros. apply add_set_wfs_ext.  *)
  (*    unfold find_or_add. *)
  (*   remember_rev (get_index_wfs s ss) as gopt. *)
  (*   destruct gopt; simpl. *)
  (*   Case "Some n". apply RESS.disjoint_empty. *)
  (*   Case "None". apply RESSMP.disjoint_singleton. *)
  (*     unfold get_index_wfs.  *)
  (*     generalize RESS.get_index_none; crush. *)
  (* Qed. *)

  (* Lemma find_or_add_app : forall s ss ss', *)
  (*   wfs_ext (ss +++ (fst (find_or_add s ss))) ss' -> *)
  (*   RES.Equal (proj1_sig s) (ss'.[snd (find_or_add s ss)]). *)
  (* Proof. intros. *)
  (*   generalize (find_or_add_wfs_ext s ss). intros. *)
  (*   unfold find_or_add in *. *)
  (*   remember_rev (get_index_wfs s ss) as gopt. *)
  (*   destruct gopt; simpl. *)
  (*   Case "Some n". *)
  (*     assert (H2:get_index_wfs s ss' = Some n). *)
  (*       apply get_index_wfs_ext with (ss:=ss); *)
  (*       eauto using wfs_ext_trans. *)
  (*     apply RESS.get_index_get_element in H2. *)
  (*     unfold get_state. *)
  (*     destruct (get_element_wfs2 n ss'). *)
  (*       destruct s0 as [s1 [H4 H6]]. *)
  (*         crush. assert (x=s1) by congruence. subst. reflexivity. *)
  (*       sim. apply RESS.get_element_some_lt in H1. unfold cardinal_wfs in *. omega. *)
  (*   Case "None". *)
  (*     simpl in *. *)
  (*     unfold get_state. *)
  (*     destruct (get_element_wfs2 (RESS.cardinal (proj1_sig ss)) ss'). *)
  (*       destruct s0 as [s1 [H4 H6]]. simpl. *)
  (*         apply RESS.get_index_none_get_element in Hgopt. *)
  (*         assert (RESS.get_element (RESS.cardinal (proj1_sig ss)) (proj1_sig ss') = *)
  (*                 Some (proj1_sig s)). *)
  (*           eapply get_element_wfs2_ext2; eassumption. *)
  (*         assert (s1 = proj1_sig s) by congruence. *)
  (*         subst. reflexivity. *)
  (*         apply wfs_ext_cardinal_leq in H. *)
  (*         rewrite add_singleton_cardinal in H.  *)
  (*           unfold cardinal_wfs in *. omega. *)
  (*           apply RESS.get_index_none. trivial. *)
  (*  Qed. *)
      
  (** Returns [true] iff the [astgram] accepts the empty string. *)
  (* Fixpoint accepts_null (g:astgram) : bool :=  *)
  (*   match g with  *)
  (*     | aEps => true *)
  (*     | aChar _ => false *)
  (*     | aAny => false *)
  (*     | aZero => false *)
  (*     | aAlt g1 g2 => accepts_null g1 || accepts_null g2 *)
  (*     | aCat g1 g2 => accepts_null g1 && accepts_null g2 *)
  (*     | aStar _ => true *)
  (*   end. *)

  (** Build a map saying which states are accepting states *)
  (* Definition build_accept_table (s:states_t) : list bool :=  *)
  (*   List.map accepts_null s. *)

  (** Returns [true] iff the [astgram] rejects all strings. *)
  (* Fixpoint always_rejects (g:astgram) : bool :=  *)
  (*   match g with  *)
  (*     | aEps => false *)
  (*     | aChar _ => false *)
  (*     | aAny => false *)
  (*     | aZero => true *)
  (*     | aAlt g1 g2 => always_rejects g1 && always_rejects g2 *)
  (*     | aCat g1 g2 => always_rejects g1 || always_rejects g2 *)
  (*     | aStar _ => false *)
  (*   end. *)

  (** Build a map saying which states are rejecting states *)
  (* Definition build_reject_table (s:states_t) : list bool :=  *)
  (*   List.map always_rejects s. *)

  (** Generate the transition matrix row for the state corresponding to a
      well-forrmed state s. The table has been closed up to gpos.
      In general, this will add new states. *)
  Section GENROW.

    (** Generate an xform in the case that the newly generated state is set
        equal to some existing state; the important thing is to use [Equal_xform].
     *)
    Definition gen_backward_xform s ss ss' n:
      wfs_ext ss ss' ->
      get_index_wfs s ss = Some n ->
      RES.re_set_type (ss'.[n]) ->> RES.re_set_type (proj1_sig s).
      intros. 
      assert (H2: RES.Equal (proj1_sig s) (ss'.[n])).
        apply get_state_get_index_some. eapply get_index_wfs_ext; eassumption.
      exact (Equal_xform H2).
    Defined.

    Lemma gen_row1 s ss ss' n:
      wfs_ext ss ss' -> 
      get_index_wfs s ss = Some n ->
      n < cardinal_wfs ss'.
    Proof. intros. eapply RESS.get_index_some_lt. 
      eapply get_index_wfs_ext; eassumption.
    Qed.

    Lemma gen_row4 : forall s ss ss',
      get_index_wfs s ss = None -> wfs_ext (s ::: ss) ss' ->
      RES.re_set_type (proj1_sig s) =
      RES.re_set_type (ss'.[cardinal_wfs ss]).
    Proof. intros.
      erewrite get_state_get_index_none by eassumption.
      assert (cardinal_wfs ss < cardinal_wfs (s ::: ss)).
        generalize (add_wfs_cardinal s ss H). omega.
      erewrite get_state_wfs_ext by eassumption.
      trivial.
    Qed.

    Lemma gen_row5 : forall n rs ss ss',
      ss.[n] = rs -> n < cardinal_wfs ss ->
      wfs_ext ss ss' ->
      List_t (RES.re_set_type rs) = List_t (RES.re_set_type (ss'.[n])).
    Proof. intros. repeat f_equal. generalize get_state_wfs_ext; crush. Qed.

    Lemma gen_row6 (s s1:wf_state) (ss:wf_states) n:
      get_index_wfs s1 ss = None ->
      n < cardinal_wfs ss ->
      ss.[n] = proj1_sig s ->
      (s1 ::: ss).[n] = proj1_sig s.
    Proof. intros.
      rewrite <- H1. symmetry.
      apply get_state_wfs_ext.
        apply wfs_ext_add2. assumption.
        trivial.
    Qed.

    Lemma gen_row7 (s s1:wf_state) gpos ss ss':
      ss.[gpos] = proj1_sig s -> gpos < cardinal_wfs ss ->
      get_index_wfs s1 ss = None ->
      wfs_ext (s1 ::: ss) ss' ->
      List_t (RES.re_set_type (proj1_sig s)) = List_t (RES.re_set_type (ss'.[gpos])).
    Proof. intros.
      eapply gen_row5. eassumption. assumption.
      eapply wfs_ext_trans.
        eapply wfs_ext_add2. eassumption.
        trivial.
    Qed.

    Variable s : wf_state.
    Variable gpos : nat.

    (* todo: should we use | instead of & before wfs_ext *)
    (* Return type of gen_row' *)
    Definition gen_row_ret_t (ss:wf_states) (n:nat) (tid:token_id) :=
      {ss':wf_states & {row : row_t gpos ss' & wfs_ext ss ss'}}.

    (** This hideous function is basically calculating the derivative
         of [ss[gpos]] with respect to all tokens from [num_tokens] down to 0,
         and adding the corresponding entries to the row.  At the same
         time, it's collecting the new states and adding them to [ss].
         We must carry around a lot of auxiliary information to ensure
         that [gpos] is in bounds, and to build a well-formed entry. 
         What we get out is a new set of states, [ss'], a new [row_t]
         for [gpos] with respect to [ss'], and a proof that the 
         [ss'] is an extension of [ss]. *)
    Fixpoint gen_row'
      (n:nat) (ss:wf_states) (tid:token_id) (H:ss.[gpos] = proj1_sig s)
      (H1:gpos < cardinal_wfs ss) : gen_row_ret_t ss n tid.
      refine (match n with
          | 0 => existT _ ss (existT _ nil _)
          | S n' => 
            match wpdrv_wf (token_id_to_chars tid) s with
              | existT s1 f1 =>
                match get_index_wfs2 s1 ss with
                  | inleft (exist n Hgi) =>
                      let (ss', r) := gen_row' n' ss (1 + tid) H H1 in
                      let (row, Hwfs) := r in
                      let f_back := gen_backward_xform _ Hwfs Hgi in
                      let e : entry_t gpos ss' :=
                          {| next_state := n ;
                             next_state_lt := gen_row1 s1 Hwfs Hgi;
                             next_xform := xcomp f_back
                                             (xcoerce f1 eq_refl
                                               (gen_row5 H H1 Hwfs)) |} in
                      existT _ ss' (existT _ (e::row) _)
                  | inright Hgi =>
                      let (ss', r) := gen_row' n' (s1 ::: ss) (1 + tid) _ _ in
                      let (row, Hwfs) := r in
                      let e : entry_t gpos ss' :=
                          {| next_state := cardinal_wfs ss;
                             next_state_lt := _ ;
                             next_xform := xcoerce f1 (gen_row4 Hgi Hwfs) 
                                                   (gen_row7 s H H1 Hgi Hwfs) |} in
                      existT _ ss' (existT _ (e::row) _)
                end
            end
      end); clear gen_row'.
      apply wfs_ext_refl.
      trivial.
      apply gen_row6; trivial.
      abstract (generalize (add_wfs_cardinal_leq s1 ss); omega).
      apply wfs_ext_cardinal_leq in Hwfs.
      abstract (generalize (add_wfs_cardinal s1 ss Hgi); omega).
      eapply wfs_ext_trans. 
        eapply wfs_ext_add2. eassumption.
        trivial.
    Defined.


  (* Fixpoint gen_row' (n:nat) (s:wf_state) (ss:wf_states) (tk_id:token_id) :  *)
  (*   (wf_states * list nat) := *)
  (*   match n with *)
  (*     | 0 => (ss, nil) *)
  (*     | S n' => *)
  (*       let s1 := wpdrv_wf (token_id_to_chars tk_id) s in *)
  (*       match get_index_wfs s1 ss with *)
  (*         | Some n => *)
  (*           let (ss1, row) := gen_row' n' s ss (1 + tk_id) in *)
  (*           (ss1, n :: row) *)
  (*         | None => *)
  (*           let (ss1, row) := gen_row' n' s (add_wfs s1 ss) (1 + tk_id) in *)
  (*           (ss1, cardinal_wfs ss :: row) *)
  (*       end *)
  (*   end. *)

  (* Definition gen_row (s:wf_state) (ss:wf_states) : (wf_states * list nat) :=  *)
  (*   gen_row' num_tokens s ss 0. *)

    (** Kick off the row generation starting with [num_tokens.] *)
    Definition gen_row (ss:wf_states)
               (H:ss.[gpos] = proj1_sig s) (H1: gpos < cardinal_wfs ss) :
               gen_row_ret_t ss num_tokens 0 :=
      gen_row' num_tokens ss 0 H H1.
  
    (** This is the main loop-invariant for [gen_row'].  Given a state [s],
      a list of states [ss], and a token number [n], running [gen_row' n ss
      tid] yields a list of states [ss'] and transition-table [row'] such
      that the length of [row'] is [n], [ss'] is an extension of [ss], and
      for all [tid'], the well-formed row inv holds. *)
    Lemma gen_row'_prop: forall n ss tid (H:ss.[gpos] = proj1_sig s) 
          (H1:gpos < cardinal_wfs ss),
      n <= num_tokens -> tid = num_tokens-n ->
      match gen_row' n ss tid H H1 with 
        | existT ss1 (existT row1 Hwfs) => 
          length row1 = n /\
          forall tid', tid' >= tid -> wf_row row1 (tid'-tid) tid'
      end.
    Proof. induction n.
      Case "base". intros. compute [gen_row'].
        split; [trivial | idtac].
        intros. subst. apply wf_row_nil.
      Case "S n". intros.
        remember_rev (gen_row' (S n) ss tid H H1) as gr.
        destruct gr as [ss1 rss].
        destruct rss as [row' Hwfs].
        compute [gen_row'] in Hgr. fold gen_row' in Hgr.
        remember_rev (wpdrv_wf (token_id_to_chars tid) s) as sxf.
        destruct sxf as [s1 f1].
        remember_rev (get_index_wfs2 s1 ss) as gi.
        destruct gi.
        SCase "s1 in ss".
          destruct s0 as [n0 Hgiw].
          remember_rev (gen_row' n ss (1 + tid) H H1) as grr.
          destruct grr as [ss' rr].
          destruct rr as [row Hwfs1].
          inversion_clear Hgr. simpl.
          use_lemma (IHn ss (1+tid) H H1) by omega.
          rewrite Hgrr in *. destruct H3 as [H4 H6].
          split; [auto | idtac].
          use_lemma RESS.get_index_some_lt by eassumption.
          assert (H8:ss'.[gpos] = proj1_sig s).
            erewrite <- get_state_wfs_ext; eassumption.
          intros. 
          match goal with 
            | [H:tid' >= tid |- _] => apply le_lt_or_eq in H; destruct H
          end.
          SSCase "tid < tid'".
            replace (tid'-tid) with (S (tid' - (1 + tid))) by omega.
            unfold wf_row. compute [nth_error].
            apply H6. omega.
          SSCase "tid = tid'".
            subst tid'. rewrite minus_diag.
            unfold wf_row. compute [nth_error value next_state next_xform].
            generalize (gen_row5 H H1 Hwfs1).
            rewrite H8.
            intros.
            rewrite wpdrv_wf_corr by eassumption.
            unfold gen_backward_xform.
            generalize ((get_state_get_index_some s1 ss'
                 (get_index_wfs_ext s1 Hwfs1 Hgiw))). intro H10.
            rewrite (Equal_xform_corr H10).
            rewrite xcoerce_eq.
            split; intros; trivial.
        SCase "s1 notin ss".
          remember (gen_row6 s s1 ss e H1 H) as H4.
          remember (gen_row'_subproof (S n) ss tid H H1 n s1 f1 e) as H6.
          remember_rev (gen_row' n (s1 ::: ss) (1 + tid) H4 H6) as grr.
          destruct grr as [ss' rr].
          destruct rr as [row Hwfs1].
          inversion_clear Hgr. simpl.
          assert (H8:ss'.[gpos] = proj1_sig s).
            rewrite <- H. symmetry. 
            apply get_state_wfs_ext.
              eapply wfs_ext_trans. 
                eapply wfs_ext_add2. eassumption.
                trivial.
              trivial.
          use_lemma (IHn (s1:::ss) (1+tid) H4 H6) by omega.
          rewrite Hgrr in H3.
          destruct H3 as [H10 H12].
          split. omega.
          intros. 
          match goal with 
            | [H:tid' >= tid |- _] => apply le_lt_or_eq in H; destruct H
          end.
          SSCase "tid < tid'".
            replace (tid'-tid) with (S (tid' - (1 + tid))) by omega.
            unfold wf_row. compute [nth_error].
            apply H12. omega.
          SSCase "tid = tid'".
            subst tid'. rewrite minus_diag.
            unfold wf_row. compute [nth_error value next_state next_xform].
            generalize (gen_row4 e Hwfs1) (gen_row7 s H H1 e Hwfs1).
            rewrite H8.
            use_lemma get_state_get_index_none by eassumption.
            assert (H14:proj1_sig s1 = ss'.[cardinal_wfs ss]).
              erewrite <- get_state_wfs_ext. eassumption. assumption.
              generalize (add_wfs_cardinal s1 ss e).  omega.
            rewrite <- H14.
            intros.
            rewrite wpdrv_wf_corr by eassumption.
            rewrite xcoerce_eq.
            split; intros; trivial.
    Qed.

    Lemma gen_row_prop: forall ss (H:ss.[gpos] = proj1_sig s) 
          (H1:gpos < cardinal_wfs ss),
      match gen_row ss H H1 with 
        | existT ss1 (existT row1 Hwfs) => 
          length row1 = num_tokens /\
          forall tid, wf_row row1 tid tid
      end.
    Proof. unfold gen_row. intros.
      use_lemma (@gen_row'_prop num_tokens ss 0 H H1) by omega.
      remember (gen_row' num_tokens ss 0 H H1) as gr.
      destruct gr as [ss1 rr].
      destruct rr as [row1 Hwfs].
      clear Heqgr. 
      split. crush.
      sim. intro.
      rewrite (minus_n_O tid) at 1.
      apply H2. omega.
    Qed.

  End GENROW.

  Definition coerce_entry_help n ss ss' (e:entry_t n ss): 
    wfs_ext ss ss' -> n < cardinal_wfs ss ->
    RES.re_set_type (ss'.[next_state e]) ->> 
      List_t (RES.re_set_type (ss'.[n])).
    generalize (next_state_lt e); intros.
    assert (H4:ss.[next_state e] = ss'.[next_state e]).
      apply get_state_wfs_ext; assumption.
    assert (H6:ss.[n] = ss'.[n]).
      apply get_state_wfs_ext; assumption.
    rewrite <- H4. rewrite <- H6. exact (next_xform e).
  Defined.

  (** We build some entries in the transition matrix before we've discovered
      all of the states.  So we have to coerce these entries to work with the
      bigger set of states, which unfortunately, isn't just done at the top-level. *)
  Definition coerce_entry n ss ss' (H:wfs_ext ss ss') (H1:n < cardinal_wfs ss)  
             (e:entry_t n ss) : entry_t n ss' :=
      {| next_state := next_state e ;
         next_state_lt := 
           lt_le_trans _ _ _ (next_state_lt e) (wfs_ext_cardinal_leq H) ;
         next_xform := coerce_entry_help e H H1
      |}.

  (** Similarly, we have to coerce the pre-computed [astgram_extract_nil] values
      for previous rows. *)
  Definition coerce_nils ss ss' i (H: wfs_ext ss ss') (H1: i < cardinal_wfs ss) 
             (v:interp (RES.re_set_type (ss.[i]))) :
    interp (RES.re_set_type (ss'.[i])).
    intros. erewrite <- (get_state_wfs_ext H H1). assumption.
  Defined.

  (** Helper lemmas for coercing previous transition rows once we've added in
      some new states. *)
  Lemma coerce_transitions1 ss ss' (H:wfs_ext ss ss') (t:transition_t ss):
    forall i : nat,
       wf_row (map (coerce_entry H (row_num_lt t)) (row_entries t)) i i.
  Proof. intros. generalize (row_entries_wf t i). 
    unfold wf_row. rewrite Coqlib.list_map_nth.
    remember_rev (nth_error (row_entries t) i) as ne.
    destruct ne; auto.
    intros. unfold Coqlib.option_map.
    destruct t; destruct e.
    Opaque in_re_set_xform in_re_set token_id_to_chars. simpl in *.
    unfold coerce_entry_help.
    unfold eq_rec, eq_rect.
    generalize (get_state_wfs_ext H row_num_lt0).
    generalize (get_state_wfs_ext H
                  (next_state_lt {|
                       next_state := next_state0;
                       next_state_lt := next_state_lt0;
                       next_xform := next_xform0 |})).
    intros H10 H12. simpl in H10.
    rewrite <- H12. rewrite <- H10.
    auto.
  Qed.

  Lemma coerce_transitions2 ss ss' (H:wfs_ext ss ss') t:
     map (coerce_nils H (row_num_lt t)) (row_nils t) =
     re_set_extract_nil (ss'.[row_num t]).
  Proof.
     destruct t. simpl. rewrite row_nils_wf0.
     clear row_entries_wf0 row_entries_len0 row_entries0. clear row_nils_wf0.
     clear row_nils0. unfold coerce_nils. unfold eq_rect_r. unfold eq_rect.
     generalize (get_state_wfs_ext H row_num_lt0). intro H2.
     rewrite H2. apply map_id.
  Qed.

  (** Used to coerce previous rows so that instead of being indexed by the *)
  (*     original set of states [s], they are now indexed by [s ++ s1]. *)
  Definition coerce_transitions ss ss' (H:wfs_ext ss ss') 
              (ts:transitions_t ss) : transitions_t ss'.
    refine (List.map (fun (t:transition_t ss) =>
      {| row_num := row_num t ;
         row_num_lt := 
           (lt_le_trans _ _ _ (row_num_lt t) (wfs_ext_cardinal_leq H)) ;
         row_entries := 
           List.map (coerce_entry H (row_num_lt t)) (row_entries t) ;
         row_entries_len := _ ;
         row_nils := List.map (coerce_nils H (row_num_lt t)) (row_nils t) ;
         row_entries_wf := coerce_transitions1 H t ;
         row_nils_wf := coerce_transitions2 H t
      |}) ts).
   Case "row_entries_len".
     rewrite Coqlib.list_length_map. apply (row_entries_len t).
  Defined.

  (** Build a transition table by closing off the reachable states.  The invariant
     is that we've closed the table up to the [next_state] and have generated the
     appropriate transition rows for the states in the range 0..[next_state-1].
     So we first check to see if [next_state] is outside the range of states, and
     if so, we are done.  Otherwise, we generate the transition row for the
     derivative at the position [next_state], add it to the list of rows, and
     then move on to the next position in the list of states.  Note that when 
     we generate the transition row, we may end up adding new states.  So we 
     have to go back and coerce the earlier transition entries to be compatible
     with those additional states.  
  *)

    (* TBC *)

  (** A relation that puts an upper bound on nats *)
  Definition limit_nat (m:nat) : relation nat :=
    fun n1 n2: nat => m - n1 < m - n2.

  Lemma limit_nat_wf_helper :
    forall n k m, m - k < n -> Acc (limit_nat m) k.
  Proof. induction n; intros; [omega | idtac].
    apply Acc_intro; intros. unfold limit_nat in H0.
    apply IHn. omega.
  Defined.

  Lemma limit_nat_wf: 
    forall m, well_founded (limit_nat m).
  Proof. intros. intro n.
    apply Acc_intro; intros.
    unfold limit_nat in H.
    eauto using limit_nat_wf_helper.
  Defined.

  (* max number of partial derivatives of r *)
  Definition max_pdrv := NPeano.pow 2 (1 + num_of_syms r).
    (* Pos.add 1 (shift_nat (1 + num_of_syms r) 1). *)

  (** The termination metric for function [build_table'] *)
  Definition build_table_metric := limit_nat max_pdrv.

  Lemma states_upper_bound: forall (ss: wf_states),
    cardinal_wfs ss <= max_pdrv.
  Proof. intros.
    destruct ss as [ss H].
    assert (H2: RESS.Subset ss (POW.powerset (pdset r))).
      intros s H2. apply POW.powerset_spec.
      apply H in H2. unfold wf_state in H2.
      destruct H2 as [w H2].
      rewrite H2. apply wpdrv_subset_pdset.
    apply RESSP.subset_cardinal in H2.
    rewrite POW.powerset_cardinal in H2.
    assert (NPeano.pow 2 (RESet.cardinal (pdset r)) <= 
            NPeano.pow 2 (1 + num_of_syms r)).
      apply NPeano.Nat.pow_le_mono_r. omega.
      apply pdset_upper_bound.
    unfold max_pdrv.
    unfold cardinal_wfs. simpl in *.
    omega.
  Qed.

  Lemma build_table_metric_dec : forall n ss,
    n < cardinal_wfs ss -> build_table_metric (S n) n.
  Proof. intros. unfold build_table_metric, limit_nat.
    apply plus_lt_reg_l with (p:= S n).
    assert (S n <= max_pdrv). 
     generalize (states_upper_bound ss).
      omega.
    repeat rewrite NPeano.Nat.add_sub_assoc by omega.
    repeat rewrite NPeano.Nat.add_sub_swap by omega.
    omega.
  Qed.

  Definition gen_row_2 (s:wf_state) (gpos:nat) (ss:wf_states)
     (H:ss.[gpos]=proj1_sig s) (H1:gpos<cardinal_wfs ss) :
     {gr: gen_row_ret_t gpos ss num_tokens 0 | 
        @gen_row s gpos ss H H1 = gr} :=
    (match @gen_row s gpos ss H H1 as gr
           return @gen_row s gpos ss H H1 = gr -> _ with
       | gr => fun Hgr => exist _ gr Hgr
     end) eq_refl.

  Lemma build_table_help1 n (s:wf_state) ss: 
    get_element_wfs n ss = Some (proj1_sig s) ->
    ss.[n] = proj1_sig s.
  Proof. symmetry. apply get_state_get_element_some. trivial. Qed.

  Lemma build_table_help2 n (s:wf_state) ss: 
    get_element_wfs n ss = Some (proj1_sig s) ->
    n < cardinal_wfs ss.
  Proof. intros.
    apply RESS.get_element_some_lt in H. unfold cardinal_wfs. trivial.
  Qed.

  (* Unset Implicit Arguments. *)
  (* Require Import Coq.Program.Wf. *)
  (* Definition extract_wf_state (ss: wf_states) (n:nat) *)
  (*            (s: {s:state | state_is_wf s *)
  (*                           /\ RESS.get_element n (proj1_sig ss) = Some s}) *)
  (*   : wf_state. *)
  (*   destruct s. destruct a. *)
  (*   refine (exist _ x _). *)
  (*   apply H. *)
  (* Defined. *)
  (* Program Fixpoint build_table' (ss:wf_states) (rows:list (list nat)) (next_state:nat) *)
  (*          {wf build_table_metric next_state} : *)
  (*   wf_states * list (list nat) := *)
  (*   match get_element_wfs2 next_state ss with *)
  (*      | inleft s =>  *)
  (*        let (ss1, row1) := gen_row (extract_wf_state _ _ s) ss in *)
  (*        build_table' ss1 (rows ++ (row1::nil)) (1 + next_state) *)
  (*      | inright _ => (ss, rows) *)
  (*   end. *)

  Unset Implicit Arguments.
  Require Import Coq.Program.Wf.
  Program Fixpoint build_table (ss:wf_states) (rows:transitions_t ss)
          (next_state:nat) {wf build_table_metric next_state} : 
    {ss':wf_states & transitions_t ss'} :=
    match get_element_wfs2 next_state ss with
         | inright _ => existT _ ss rows
         | inleft s0 =>
           let (s, Hge) := s0 in
           (match (gen_row s ss (build_table_help1 _ _ _ Hge)
                          (build_table_help2 _ _ _ Hge)) as gr
              return (gen_row s ss (build_table_help1 _ _ _ Hge)
                          (build_table_help2 _ _ _ Hge) = gr -> _)  with
             | existT ss' (existT row Hwfs) =>
               fun Hgr =>
                 let t : transition_t ss' := {|
                       row_num := next_state ;
                       row_num_lt := _ ;
                       row_entries := row ;
                       row_entries_len := _ ;
                       (* todo: we shouldn't need to recompute the following every time *)
                       row_nils := re_set_extract_nil _ ; 
                       row_entries_wf := _ ;
                       row_nils_wf := eq_refl _
                     |} in
                 (* existT _ ss rows *)
                 build_table ss' ((coerce_transitions Hwfs rows) ++ (t::nil))
                             (1 + next_state)
            end) eq_refl
    end.
  Next Obligation.
    eapply lt_le_trans. eapply RESS.get_element_some_lt. eassumption.
      apply wfs_ext_cardinal_leq. assumption.
  Defined.
  Next Obligation.
    generalize (gen_row_prop s ss (build_table_help1 _ _ _ Hge)
                  (build_table_help2 _ _ _ Hge)); intro H2.
      rewrite Hgr in H2.
      crush.
  Defined.
  Next Obligation.
    generalize (gen_row_prop s ss (build_table_help1 _ _ _ Hge)
                  (build_table_help2 _ _ _ Hge)); intro H2.
      rewrite Hgr in H2.
      crush.
    (* todo: simplify the above *)
  Defined.
  Next Obligation.
    destruct Heq_anonymous.
    apply RESS.get_element_some_lt in H.
    eauto using build_table_metric_dec.
  Defined.
  Next Obligation.
    apply measure_wf. apply limit_nat_wf.
  Defined.

End DFA.

Recursive Extraction build_table.


(* Definition test0:= Eps. *)
(* Definition test1 := Char true. *)
(* Definition test2 := Cat (Char true) (Char false). *)
(* Definition test3 := Cat (Char false)  *)
(*                          (Cat (Char false) *)
(*                                (Cat (Char false) *)
(*                                (Cat (Char false) *)
(*                                (Cat (Char false) *)
(*                                (Cat (Char false) *)
(*                                (Cat (Char false) (Char false))))))). *)

(* Time Eval compute in (build_dfa test1). *)
(* Time Eval compute in (build_dfa test3). *)


Section DFA_RECOGNIZE.
  Variable d : DFA.

  (** This loop is intended to find the shortest match (if any) for a
      sequence of tokens, given a [DFA].  It returns [(Some (n, ts'))] when
      there is a match and where [ts'] is the unconsumed input and n is the
      length of the consumed input.  If there is no match, it returns
      [None].  This is just one example of a recognizer that can be built
      with the DFA. *)
  Fixpoint dfa_loop state (count: nat) (ts : list token_id) : 
    option (nat * list token_id) := 
    if nth state (dfa_accepts d) false then Some (count, ts)
    else 
      match ts with 
        | nil => None
        | t::ts' => let row := nth state (dfa_transition d) nil in 
                    let new_state := nth t row num_tokens in
                    dfa_loop new_state (1 + count) ts'
      end.

  Definition dfa_recognize (ts:list token_id) : option (nat * list token_id) := 
    dfa_loop 0 0 ts.

   (** This is a simple function which runs a DFA on an entire string, returning
       true if the DFA accepts the string, and false otherwise.  In what follows,
       we prove that [run_dfa] is correct... *)
  Fixpoint run_dfa (d:DFA) (st:nat) (ts:list token_id) : bool := 
    match ts with 
      | nil => nth st (dfa_accepts d) false
      | t::ts' => run_dfa d (nth t (nth st (dfa_transition d) nil) num_tokens) ts'
    end.

  (** This lemma tells us that if we start with a grammar [g], build a [DFA],
      and then run the [DFA] on a list of tokens, then we get [true] iff
      the grammar would've accepted the string and produced a value.  *)
  Lemma run_dfa_corr' : forall (r: regexp), 
    build_dfa r = d -> 
    forall ts2 ts1 st rs, 
      RESS.get_element st (dfa_states d) = Some rs ->
      RES.Equal rs
        (wpdrv (flat_map token_id_to_chars ts1) (proj1_sig (ini_state r))) ->
      Forall (fun t => t < num_tokens) ts2 ->
      if run_dfa d st ts2 then
        in_re r (flat_map token_id_to_chars (ts1 ++ ts2))
      else ~ in_re r (flat_map token_id_to_chars (ts1 ++ ts2)).
  Proof. intros r H.
    generalize (build_dfa_wf r); intro.
    unfold wf_dfa in H0. sim.
    induction ts2.
    Case "nil". intros. simpl.
      rewrite app_nil_r.
      assert (st < dfa_num_states (build_dfa r)).
        use_lemma RESS.get_element_some_lt by eassumption. 
        rewrite H0. congruence.
      use_lemma (H5 st) by eassumption.
      rewrite H in H10. rewrite H6 in H10. sim.
      remember_destruct_head as nn.
      SCase "nth n (dfa_accepts d) false = true".
        apply in_re_set_singleton.
        rewrite <- app_nil_r.
        apply wpdrv_corr.
        rewrite <- H7. auto.
      SCase "nth n (dfa_accepts d) false = false".
        intro.
        cut (false = true). congruence.
        apply H14. rewrite H7.
        apply wpdrv_corr. apply in_re_set_singleton. rewrite app_nil_r.
        assumption.
    Case "a::ts2". intros. simpl.
      remember (nth a (nth st (dfa_transition d) nil) num_tokens) as st'.
      assert (st < dfa_num_states (build_dfa r)).
        use_lemma RESS.get_element_some_lt by eassumption. 
        rewrite H0. congruence.
      use_lemma (H5 st) by eassumption.
      rewrite H in H10. rewrite H6 in H10. sim.
      use_lemma Forall_inv by eassumption.
      use_lemma H13 by eassumption. sim.
      rewrite <- Heqst' in H17.
      remember_destruct_head in H17 as gn; [idtac | false_elim].
      assert (H20: RES.Equal e
              (wpdrv (flat_map token_id_to_chars (ts1 ++ (a::nil)))
                     (proj1_sig (ini_state r)))).
        rewrite H17.
        rewrite Coqlib.flat_map_app. rewrite wpdrv_app.
        change (flat_map token_id_to_chars (a :: nil)) with
          (token_id_to_chars a ++ nil).
        rewrite app_nil_r.
        rewrite H7. reflexivity.
      inversion H8.
      use_lemma IHts2 by eassumption.
      rewrite <- app_assoc in H23. assumption.
  Qed. 

  (** Here is the key correctness property for [run_dfa]. *)
  Lemma run_dfa_corr (r: regexp) :
    build_dfa r = d -> 
    forall ts, 
      Forall (fun t => t < num_tokens) ts -> 
      if run_dfa d 0 ts then 
        in_re r (flat_map token_id_to_chars ts)
      else ~ in_re r (flat_map token_id_to_chars ts).
  Proof. intros. 
    generalize (build_dfa_wf r); unfold wf_dfa; intro. sim.
    change ts with (nil++ts).
    eapply run_dfa_corr'; try eassumption; subst; eauto.
     simpl; reflexivity.
  Qed.

  (** Properties of dfa_recognize *)
  Lemma dfa_loop_run : forall ts st count count2 ts2,
    dfa_loop st count ts = Some (count2, ts2) -> 
    exists ts1, 
      ts = ts1 ++ ts2 /\ count2 = length ts1 + count /\ 
      run_dfa d st ts1 = true /\
      forall ts1' ts2',
        ts = ts1' ++ ts2' -> 
        length ts1' < length ts1 -> 
        ~ run_dfa d st ts1' = true.
  Proof. induction ts; simpl; intros; remember (nth st (dfa_accepts d) false) as acc;
    destruct acc. 
      exists nil; crush.
      congruence.
      exists nil; crush.
      Case "a::ts, when acc is false".
        remember (nth a (nth st (dfa_transition d) nil) num_tokens) as st'.
        apply IHts in H. destruct H as [ts1 H]. sim.
        exists (a::ts1). crush.
          destruct ts1'. crush.
          crush; eapply H2; crush.
  Qed.

  Lemma dfa_recognize_corr :  forall (r:regexp),
    build_dfa r = d -> 
    forall ts, 
      Forall (fun t => t < num_tokens) ts -> 
      match dfa_recognize ts with 
        | None => True
        | Some (count,ts2) => 
          exists ts1, 
            ts = ts1 ++ ts2 /\ count = length ts1 /\ 
            in_re r (flat_map token_id_to_chars ts1) /\
            forall ts3 ts4,
              length ts3 < length ts1 ->
              ts = ts3 ++ ts4 -> 
              ~ in_re r (flat_map token_id_to_chars ts3)
      end.
  Proof. intros. red. remember_rev (dfa_loop 0 0 ts) as e.
    destruct e ; auto. destruct p. 
    use_lemma dfa_loop_run by eassumption. 
    destruct H1 as [ts1 H1]. sim.
    exists ts1. crush.
      apply Coqlib.Forall_app in H0. destruct H0.
        generalize (run_dfa_corr _ H H0).
        remember_destruct_head as rd; crush.
      use_lemma H4 by eassumption.
        rewrite H2 in H0.
        apply Coqlib.Forall_app in H0. destruct H0.
        generalize (run_dfa_corr _ H H0).
        remember_destruct_head as rd; crush.
  Qed.

End DFA_RECOGNIZE.

Require Import Parser.
Definition par2rec t (g:grammar t) : regexp := 
  let (ag, _) := split_regexp g in ag.


stuff that need to be copied from Parser.v
  - def of grammar, in_grammar
  - inversion lemmas for grammars such as EpsInv
  - the split function from a grammar to a regexp and an xform
  - optimization constructors for grammars
  - optimizing constructors for regexps
  - def of naive_parse and its correctness proofs.
