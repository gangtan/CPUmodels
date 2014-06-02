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

Definition re_xf_pair (ty:type) := {r : regexp & regexp_type r ->> ty }.

Axiom in_re_set: 
  forall s:RES.t, list char_t -> interp (RES.re_set_type s) -> Prop.

Lemma in_re_set_empty : forall s v, not (in_re_set RES.empty s v).
Admitted.

Definition in_re_set_xform
           t (rx:RES.rs_xf_pair (List_t t)) s (v:interp t) := 
  let (rs, f) := rx in
  exists v', in_re_set rs s v' /\ In v (xinterp f v').

Definition singleton_xform (r:regexp) : RES.rs_xf_pair (List_t (regexp_type r)) :=
  existT _ (RES.singleton r) 
    (xcons (xmatch xzero (xmatch xid xzero)) xempty).

Lemma singleton_xform_erase: forall r, 
  projT1 (@singleton_xform r) = (RES.singleton r).
Admitted.

Lemma singleton_xform_corr: forall r s v,
  in_re_set_xform (singleton_xform r) s v <-> in_regexp r s v.
Admitted.

Axiom cat_re_xform: forall ty,
  RES.rs_xf_pair (List_t ty) -> 
  forall r:regexp, RES.rs_xf_pair (List_t (Pair_t ty (regexp_type r))).

Lemma cat_re_xform_erase: forall t rx1 r,
  projT1 (@cat_re_xform t rx1 r) = set_cat_re (projT1 rx1) r.
Admitted.

Lemma cat_re_xform_corr: forall t (rx:RES.rs_xf_pair (List_t t)) r s v,
  in_re_set_xform (cat_re_xform rx r) s v <->
  exists s1 s2 v1 v2, s = s1++s2 /\ v=(v1,v2) /\
    in_re_set_xform rx s1 v1 /\ in_regexp r s2 v2.
Admitted.

Lemma empty_xform_corr: forall t s v,
   ~ in_re_set_xform (RES.empty_xform (List_t t)) s v.
Admitted.

Lemma union_xform_corr: forall t (rx1 rx2: RES.rs_xf_pair (List_t t)) s v,
  in_re_set_xform (RES.union_xform rx1 rx2) s v
  <-> in_re_set_xform rx1 s v \/ in_re_set_xform rx2 s v.
Admitted.
  
Definition xsingleton {t} : t ->> List_t t := @xcons t t xid xempty.

(* Definition xmatchlist {t1 t2}: *)
(*   (Unit_t ->> t2) -> (Pair_t t1 (List_t t1) ->> t2) -> (List_t t1 ->> t2) :=  *)

Lemma xcross_corr {t1 t2} (vs: interp (Pair_t (List_t t1) (List_t t2))):
  xinterp xcross vs = List.list_prod (fst vs) (snd vs).
Admitted.

Lemma xflatten_corr2 {t} (vs: interp (List_t (List_t t))):
  xinterp xflatten vs = Coqlib.list_flatten vs.
Admitted.

Definition in_re_xform t (rex:re_xf_pair (List_t t)) s (v:interp t) := 
  let (r, f) := rex in exists v', in_regexp r s v' /\ In v (xinterp f v').

Axiom add_xform: 
  forall ty (rex: re_xf_pair (List_t ty)) (rx: rs_xf_pair (List_t ty)), 
    rs_xf_pair (List_t ty).

Lemma add_xform_erase: forall ty (rex:re_xf_pair (List_t ty)) rx,
  projT1 (add_xform rex rx) = RES.add (projT1 rex) (projT1 rx).
Admitted.

Lemma add_xform_corr: forall ty (rex:re_xf_pair (List_t ty)) rx s v,
  in_re_set_xform (add_xform rex rx) s v <->
  in_re_xform rex s v \/ in_re_set_xform rx s v.
Admitted.

Definition rx_imply ty (rx1 rx2: rs_xf_pair (List_t ty)) := 
  forall s v, in_re_set_xform rx1 s v -> in_re_set_xform rx2 s v.

Definition rx_equal ty (rx1 rx2: rs_xf_pair (List_t ty)) := 
  forall s v, in_re_set_xform rx1 s v <-> in_re_set_xform rx2 s v.

Instance in_re_set_xform_equal ty: 
  Proper ((@rx_equal ty) ==> eq ==> eq ==> iff) (@in_re_set_xform ty).
Proof. intros rx1 rx2 H1 s1 s2 H2 v1 v2 H3.
  unfold rx_equal in H1. rewrite H1. crush.
Qed.

(* The following type is slightly different from the one in RESet.v, but
   is isomorphic *)
Axiom fold_xform: forall (ty:type) (A:Type) (comb: re_xf_pair ty -> A -> A),
                    (rs_xf_pair ty) -> A -> A.

Lemma fold_xform_erase: forall ty
  (comb1:re_xf_pair ty -> rs_xf_pair ty -> rs_xf_pair ty) 
  (comb2:regexp -> RES.t -> RES.t) rx ini_rx,
  (forall rex rx, projT1 (comb1 rex rx) = comb2 (projT1 rex) (projT1 rx)) ->
  projT1 (fold_xform comb1 rx ini_rx) = RES.fold comb2 (projT1 rx) (projT1 ini_rx).
Admitted.

Lemma fold_xform_rec: 
  forall (ty:type) (A : Type) (P : rs_xf_pair (List_t ty) -> A -> Type)
         (f : re_xf_pair (List_t ty) -> A -> A)
         (i : A) (rx : rs_xf_pair (List_t ty)),
    (forall (rx1 rx2:rs_xf_pair (List_t ty)) (a : A), 
       rx_equal rx1 rx2 -> P rx1 a -> P rx2 a) ->
    P (@RES.empty_xform (List_t ty)) i ->
    (forall (rex : re_xf_pair (List_t ty)) (a : A) 
            (rx' rx'' : rs_xf_pair (List_t ty)),
       RES.In (projT1 rex) (projT1 rx) ->
       ~ RES.In (projT1 rex) (projT1 rx') ->
       P rx' a -> P (add_xform rex rx') (f rex a)) ->
    P rx (fold_xform f rx i).
Admitted.

Lemma in_re_xform_intro: forall t (rex:re_xf_pair (List_t t)) s v v',
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

Lemma in_re_xform_elim: forall t (rex:re_xf_pair (List_t t)) s v,
  in_re_xform rex s v -> 
    exists v', in_regexp (projT1 rex) s v' /\ In v (xinterp (projT2 rex) v').
Proof. unfold in_re_xform; intros. destruct rex as [r f]. crush. Qed.

Lemma in_re_xform_elim2: 
  forall t r (f: regexp_type r ->> (List_t t)) s v,
  in_re_xform (existT _ r f) s v -> 
    exists v', in_regexp r s v' /\ In v (xinterp f v').
Proof. generalize in_re_xform_elim. crush. Qed.


Opaque RES.union_xform RES.singleton_xform singleton_xform.
Opaque xcross xmap xapp xcomp xflatten.

Ltac xinterp_simpl :=
  repeat match goal with
    | [|- context[xcomp ?X1 ?X2]] => rewrite (xcomp_corr X1 X2); simpl
    | [H:context[xcomp ?X1 ?X2] |- _] => 
      rewrite (xcomp_corr X1 X2) in H; simpl in H
    | [|- context[xinterp (xpair _ _) _]] => rewrite xpair_corr; simpl
    | [H:context[xinterp (xpair _ _) _] |- _] => 
      rewrite xpair_corr in H; simpl in H
    | [|- context[xinterp xcross _]] => rewrite xcross_corr; simpl
    | [H:context[xinterp xcross _] |- _] => 
      rewrite xcross_corr in H; simpl in H
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

Lemma in_re_set_xform_intro: forall t (rx:RES.rs_xf_pair (List_t t)) s v v',
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

Lemma in_re_set_xform_elim: forall t (rx:RES.rs_xf_pair (List_t t)) s v,
  in_re_set_xform rx s v -> 
    exists v', in_re_set (projT1 rx) s v' /\ In v (xinterp (projT2 rx) v').
Proof. unfold in_re_set_xform; intros. destruct rx as [rs f]. crush. Qed.

Lemma in_re_set_xform_elim2: 
  forall t rs (f: RES.re_set_type rs ->> (List_t t)) s v,
  in_re_set_xform (existT _ rs f) s v -> 
    exists v', in_re_set rs s v' /\ In v (xinterp f v').
Proof. intros. generalize in_re_set_xform_elim. crush. Qed.

Lemma in_re_set_xform_comp: 
  forall t1 t2 (rx:RES.rs_xf_pair (List_t t1)) s (g:t1 ->> t2) v' rs f,
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
  forall t1 t2 (rx:RES.rs_xf_pair (List_t t1)) s (g:t1 ->> t2) v',
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
  forall ty1 ty2 (rx1: rs_xf_pair (List_t ty1)) (rx2: rs_xf_pair (List_t ty2)),
  erase_subset rx1 rx2 -> erase_subset rx2 rx1 -> erase_eq rx1 rx2.
Proof. unfold erase_subset, erase_eq. intros.
  apply RESP.subset_antisym; trivial.
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
Fixpoint pdrv (a:char_t) (r:regexp): rs_xf_pair (List_t (regexp_type r)) := 
  match r return rs_xf_pair (List_t (regexp_type r)) with
    | Eps | Zero => @RES.empty_xform _
    | Char b => 
      if char_eq_dec a b then
        let (rs,f) := singleton_xform Eps in
          existT _ rs (xcomp f (xmap (xchar a)))
      else @RES.empty_xform _
    | Any => 
      let (rs,f) := singleton_xform Eps in
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
Definition pdrv_rex (ty:type) (a:char_t) (rex:re_xf_pair (List_t ty)) :
  rs_xf_pair (List_t ty) := 
  let (r, f) := rex in
  let (rs, frs) := pdrv a r in
  existT _ rs (xcomp frs (xcomp (xmap f) xflatten)).

(** Partial derivatives over a regexp set; the result of the union 
    of taking partial derivatives on every regexp in the set *)
Definition pdrv_set (ty:type) (a:char_t) (rx:rs_xf_pair (List_t ty)) :
  rs_xf_pair (List_t ty) :=
  fold_xform (fun rex rx1 => RES.union_xform (pdrv_rex a rex) rx1)
             rx (@RES.empty_xform (List_t ty)).

(* Definition pdrv_set (ty:type) (a:char_t) (rx:rs_xf_pair (List_t ty)) := *)
(*   projT1 (pdrv_set_xform a rx). *)

(** Word partial derivatives; 
    wpdrv(nil, rs) = rs
    wpdrv(a cons w, rs) = wpdrv(w, pdrv_set(a, rs)) *)
Fixpoint wpdrv ty (s:list char_t) (rx:rs_xf_pair (List_t ty)): 
  rs_xf_pair (List_t ty) := 
  match s with
    | nil => rx
    | a:: s' => wpdrv s' (pdrv_set a rx)
  end.

Definition wpdrv_re_set s (rs:RES.t) : rs_xf_pair (List_t (RES.re_set_type rs))
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
        contradiction (in_re_set_empty H)
      | [H:in_re_set_xform (RES.empty_xform (List_t _)) _ _ |- _] =>
        contradiction (empty_xform_corr H)
      | [H:in_re_set_xform (singleton_xform ?r) _ _ |- _] => 
        apply (singleton_xform_corr r) in H
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

  Hint Extern 3 (in_re_set_xform (singleton_xform ?r) ?s ?v) =>
    apply singleton_xform_corr.

  Lemma pdrv_corr : forall r a s v, 
     in_regexp r (a :: s) v <-> in_re_set_xform (pdrv a r) s v.
  Proof. induction r.
    Case "Eps". simpl; split; intros; sim; lprover.
    Case "Zero". simpl. split; intros; sim; lprover.
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
            rewrite union_xform_corr. right.
            assert (H4:in_re_set_xform (pdrv a r2) s v2).
              apply IHr2; crush.
            rewrite Hpr2 in H4.
            apply in_re_set_xform_elim2 in H4.
            destruct H4 as [v' H4]. exists v'. xinterp_simpl. crush.
          SSSCase "~ (nullable r1)". in_regexp_contra.
        SSCase "s1=b::s1'".
          destruct n;
            [rewrite union_xform_corr; left | idtac];
            rewrite <- Hcx;
            apply cat_re_xform_corr; exists s1', s2, v1, v2;
            clear H10 IHr2 Hpr2; crush_hyp.
      SCase "<-".
        destruct n.
        SSCase "nullable r1".
          apply union_xform_corr in H.
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
      rewrite union_xform_corr.
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

Lemma pdrv_rex_erase: forall ty a (rex: re_xf_pair (List_t ty)),
  |pdrv_rex a rex| = |pdrv a (projT1 rex)|.
Proof. intros. unfold pdrv_rex.
  destruct rex as [r f]. 
  remember (pdrv a r) as pa; destruct pa as [rs frs].
  simpl. rewrite <- Heqpa. trivial.
Qed.

Lemma pdrv_rex_corr: forall t (rex:re_xf_pair (List_t t)) a s v,
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

Lemma pdrv_set_in: forall ty (rx:rs_xf_pair (List_t ty)) r a,
  RES.In r (|pdrv_set a rx|) <->
  exists r', RES.In r' (|rx|) /\ RES.In r (|pdrv a r'|).
Proof. intros. unfold erase. unfold pdrv_set. 
  rewrite fold_xform_erase
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

Lemma pdrv_set_trans: forall ty r (rx:rs_xf_pair (List_t ty)) a, 
  RES.Subset (|rx|) (pdset r) -> 
  RES.Subset (|pdrv_set a rx|) (pdset r).
Proof. intros. intro r1; intro H2.
  apply pdrv_set_in in H2. destruct H2 as [r' [H4 H6]].
  apply pdrv_subset_pdset in H6.
  eauto using pdset_trans.
Qed.

Lemma pdrv_set_erase_subset: 
  forall ty1 ty2 a (rx1:rs_xf_pair (List_t ty1)) (rx2:rs_xf_pair (List_t ty2)),
    erase_eq rx1 rx2 ->
    erase_subset (pdrv_set a rx1) (pdrv_set a rx2).
Proof. unfold erase_eq. 
  intros ty1 ty2 a rs1 rs2 H r H2.
  apply pdrv_set_in in H2. sim.
  apply pdrv_set_in. exists x. rewrite <- H. crush.
Qed.

Lemma pdrv_set_erase_eq:
  forall ty1 ty2 a (rx1:rs_xf_pair (List_t ty1)) (rx2:rs_xf_pair (List_t ty2)),
    erase_eq rx1 rx2 ->
    erase_eq (pdrv_set a rx1) (pdrv_set a rx2).
Proof.  intros. apply erase_subset_antisym.
  apply pdrv_set_erase_subset. trivial.
  apply pdrv_set_erase_subset. unfold erase_eq in *. symmetry. trivial.
Qed.

Lemma pdrv_set_corr: forall ty a (rx:rs_xf_pair (List_t ty)) s v,
  in_re_set_xform (pdrv_set a rx) s v <-> 
  in_re_set_xform rx (a::s) v.
Proof. intros. unfold pdrv_set.
  apply fold_xform_rec.
  Case "equality respecting".
    intros. rewrite H0. trivial.
  Case "base".
    split; intro H; contradict H; generalize empty_xform_corr; crush.
  Case "inductive case".
    intros.
    rewrite union_xform_corr.
    rewrite add_xform_corr.
    rewrite pdrv_rex_corr.
    crush.
Qed.

Lemma wpdrv_app: forall ty w1 w2 (rx:rs_xf_pair (List_t ty)),
  wpdrv (w1 ++ w2) rx = wpdrv w2 (wpdrv w1 rx). 
Proof. induction w1; intros. 
  simpl; trivial.
  simpl. rewrite IHw1. trivial.
Qed.

Lemma wpdrv_corr: forall ty s1 s2 (rx:rs_xf_pair (List_t ty)) v, 
  in_re_set_xform (wpdrv s1 rx) s2 v <-> in_re_set_xform rx (s1 ++ s2) v.
Proof. induction s1. crush.
  intros. simpl.
  split; intros.
    apply IHs1 in H. apply pdrv_set_corr in H. trivial.
    apply IHs1. apply pdrv_set_corr. trivial.
Qed.

Lemma wpdrv_pdset_trans : forall ty w (rx:rs_xf_pair (List_t ty)) r, 
  RES.Subset (|rx|) (pdset r) -> 
  RES.Subset (|wpdrv w rx|) (pdset r).
Proof. induction w; [auto | idtac].
  intros; simpl; eauto using pdrv_set_trans.
Qed.

(* todo: a trivial lemma; maybe remove *)
Lemma wpdrv_re_set_pdset_trans : forall w rs r,
  RES.Subset rs (pdset r) -> RES.Subset (|wpdrv_re_set w rs|) (pdset r).
Proof. generalize wpdrv_pdset_trans. crush. Qed.

Theorem wpdrv_subset_pdset : forall w r,
  RES.Subset (| wpdrv_re_set w (RES.singleton r) |) (pdset r).
Proof.  intros; apply wpdrv_pdset_trans.
  unfold pdset. intro r'; intros.
  apply RESP.FM.singleton_iff in H.
  auto with set.
Qed.

Lemma wpdrv_erase_eq:
  forall ty1 ty2 s (rx1:rs_xf_pair (List_t ty1)) (rx2:rs_xf_pair (List_t ty2)),
    erase_eq rx1 rx2 ->
    erase_eq (wpdrv s rx1) (wpdrv s rx2).
Proof. induction s. crush.
  intros. simpl. apply IHs. apply pdrv_set_erase_eq. trivial.
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

  Definition get_element_2 (n:nat) (s:t) : 
    {elt | get_element n s = Some elt} + {get_element n s = None}.
    refine (let ge := get_element n s in
            (match ge return get_element n s = ge -> _
             with
               | Some e => fun H => inleft (exist _ e _)
               | None => fun H => inright _
             end) eq_refl); crush.
  Defined.

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

  Lemma get_index_some_lt: forall e s n,
    get_index e s = Some n -> n < cardinal s.
  Proof. intros. apply get_index_spec in H.
    unfold Coqlib.first_occur in H. destruct H as [_ [y [H2 _]]].
    apply Coqlib.nth_error_some_lt in H2. auto.
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




(* todo: the following defs and proofs haven't been migrated to the case of parsers yet *)

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

  (** The initial regexp from which we will build the DFA *)
  Variable r: regexp.

  (** A state is a set of regexps, corresponding to partial derivatives of
      the starting regexp w.r.t. some word. *)
  Definition state := RES.t.

  (** a set of states; can use something more efficient than lists *) 
  Definition states := RESS.t.

  (* todo: remove *)
  (* Definition states_t := list astgram. *)
  (* Notation "s .[ i ] " := (nth i s aZero) (at level 40). *)

  Definition state_is_wf (s:state) : Prop :=
    exists w, RES.Equal s (| wpdrv_re_set w (RES.singleton r) |).
  Definition wf_state := {s:state | state_is_wf s}.

  Definition states_are_wf (ss: states) : Prop := RESS.For_all state_is_wf ss.
  Definition wf_states := {ss:states | states_are_wf ss}.

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
    {s: wf_state & RES.re_set_type (proj1_sig s) ->> ty}.

  Definition wpdrv_wf (w: list char_t) (s: wf_state): 
    wfs_xf_pair (List_t (RES.re_set_type (proj1_sig s))).
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

  (* TBC *)

  (* Definition emp_wfs: wf_states. *)
  (*   refine (exist _ RESS.empty _). *)
  (*   unfold states_are_wf, RESS.For_all. intros. *)
  (*   apply RESSP.FM.empty_iff in H. destruct H. *)
  (* Defined. *)

  (* Definition singleton_wfs (s:wf_state): wf_states. *)
  (*   refine (exist _ (RESS.singleton (proj1_sig s)) _). *)
  (*   unfold states_are_wf, RESS.For_all. intros. *)
  (*   apply RESSP.FM.singleton_1 in H. *)
  (*   generalize (proj2_sig s). intro. rewrite <- H. trivial. *)
  (* Defined.     *)

  (* Definition add_wfs (s:wf_state) (ss:wf_states): wf_states. *)
  (*   refine (exist _ (RESS.add (proj1_sig s) (proj1_sig ss)) _). *)
  (*   unfold states_are_wf; intros. *)
  (*   unfold RESS.For_all. intros. *)
  (*   destruct s as [s H2]. *)
  (*   destruct ss as [ss H4]. *)
  (*   apply RESSP.FM.add_iff in H. destruct H. *)
  (*     simpl in H. rewrite <- H. trivial. *)
  (*     apply H4. trivial. *)
  (* Defined. *)

  (* Definition add_set_wfs (ss1 ss2:wf_states): wf_states. *)
  (*   refine (exist _ (RESS.add_set (proj1_sig ss1) (proj1_sig ss2)) _). *)
  (*   unfold RESS.add_set. *)
  (*   apply RESSP.fold_rec_bis. crush. *)
  (*     apply (proj2_sig ss1). *)
  (*     intros. *)
  (*     unfold states_are_wf. *)
  (*     intros y H2. *)
  (*     apply RESSP.FM.add_iff in H2. *)
  (*     destruct H2.  *)
  (*       rewrite <- H2. apply (proj2_sig ss2). trivial. *)
  (*       auto. *)
  (* Defined. *)

  (* Hint Rewrite RESS.add_set_empty. *)




  



  (** Entries in the transition matrix *)
  Record entry_t(row:nat)(states:states_t) := 
    { (** which state do we go to next *)
      next_state : nat ; 
      (** the [next_state] is in bounds with respect to the number of states *)
      next_state_lt : next_state < length states ; 
      (** how do we transform ASTs from the next state back to this state *)
      next_xform : 
        interp (astgram_type (states.[next_state])) -> interp (astgram_type (states.[row])) 
    }.

  (** Rows in the transition matrix -- an entry for each token *)  
  Definition row_t(i:nat)(s:states_t) := list (entry_t i s).

  (** This predicate captures the fact that the ith entry in a row holds
      the derivative of that row's corresponding [astgram] with respect
      to the ith token. *)
  Definition row_wf(gpos:nat)(s:states_t)(r:row_t gpos s)(i:nat)(t:token_id) :=
    match nth_error r i with 
      | Some e => 
        exists x, derivs_and_split (s.[gpos]) (token_id_to_chars t) = 
                  existT _ (s.[next_state e]) x /\ 
                  xinterp x = (next_xform e)
      | None => True
    end.

  Record transition_t(s:states_t) := {
    (** which row are we talking about *)
    row_num : nat ; 
    (** the row's index is in range for the number of states we have *)
    row_num_lt : row_num < length s ;
    (** what are the transition entries *)
    row_entries : list (entry_t row_num s) ;
    (** the list of values we get from this state when it is an accepting state *)
    row_nils : list (interp (astgram_type (s.[row_num]))) ; 
    (** have an entry in the row for each token *)
    row_entries_len : length row_entries = num_tokens ;
    (** each entry is the appropriate derivative *)
    row_entries_wf: forall i, row_wf row_entries i i ;
    (** the row_nils are what you get when you run [astgram_extract_nil] on the
        row's [astgram]. *)
    row_nils_wf : row_nils = astgram_extract_nil (s.[row_num])
  }.

  (** The transition matrix is then a list of rows *)
  Definition transitions_t(s:states_t) := list (transition_t s).

  Record DFA := {
    (** number of states in the DFA *)
    dfa_num_states : nat ; 
    (** the list of [astgram]s for the states *)
    dfa_states : states_t ; 
    dfa_states_len : length dfa_states = dfa_num_states ; 
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
  
  (** Instead of working directly in terms of lists of [char_p]'s, we instead
     work in terms of [token_id]'s where a [token_id] is just a [nat] in the
     range 0..[num_tokens]-1.  We assume that each [token_id] can be mapped
     to a list of [char_p]'s.  For example, in the x86 parser, our characters
     are bits, but our tokens represent bytes in the range 0..255.  So the
     [token_id_to_chars] function should extract the n bits corresponding to the
     byte value.  *)
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

  Definition app_length_lt A n (s1 s2:list A) : n < length s1 -> n < length (s1 ++ s2).
    intros. rewrite app_length. omega.
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

  (** Returns [true] iff the [astgram] rejects all strings. *)
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
