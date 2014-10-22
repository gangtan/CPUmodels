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
Require Vector.
Require Import Regexp.
Require Import ParserArg.
(* Import X86_PARSER_ARG. *)
Require Export Xform.
Require Export Grammar.

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

(** * Define [RESet], a set of regexps *)

(** A set of regexps *)
(* Require Import RESet. *)
(* Module RES := RESet.RESetXform. *)
Require RESet.
Module RES := RESet.

(* Module RESet := MSetAVL.Make REOrderedType. *)
Module RESF := MapSet RES.
Module RESP := MSetProperties.Properties RES.

Opaque RES.union_xform RES.singleton_xform RES.cat_re_xform.
Opaque xcross xmap xapp xcomp xflatten.

(** ** Abbreviations and definitions for [RESet] *)

(* (* The following should be moved to RESet.v *) *)

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
    | rEps => s (* not stricitly necessary; an optimization *)
    | rZero => RES.empty
    | _ => RESF.map (re_set_build_map (fun r1 => rCat r1 r)) s
  end.
Local Notation "s $ r" := (set_cat_re s r) (at level 60, no associativity).

Definition rs_xf_pair := RES.rs_xf_pair.
Definition re_xf_pair := RES.re_xf_pair.
Definition in_re_set := RES.in_re_set.
Definition in_re_set_xform := RES.in_re_set_xform.
Definition in_re_xform := RES.in_re_xform.

Lemma cat_re_xform_erase2: forall t rx1 r,
  projT1 (@RES.cat_re_xform t rx1 r) = set_cat_re (projT1 rx1) r.
Proof. apply RES.cat_re_xform_erase. Qed.

Lemma cat_re_xform_corr2: forall ty (rx:RES.rs_xf_pair ty) r s v,
  in_re_set_xform (RES.cat_re_xform rx r) s v <->
  exists s1 s2 v1 v2, s = s1++s2 /\ v=(v1,v2) /\
    in_re_set_xform rx s1 v1 /\ in_regexp r s2 v2.
Proof. apply RES.cat_re_xform_corr. Qed.

(* Definition rx_imply ty (rx1 rx2: rs_xf_pair ty) :=  *)
(*   forall s v, in_re_set_xform rx1 s v -> in_re_set_xform rx2 s v. *)

(* Definition rx_equal ty (rx1 rx2: rs_xf_pair ty) :=  *)
(*   forall s v, in_re_set_xform rx1 s v <-> in_re_set_xform rx2 s v. *)

(* Instance in_re_set_xform_equal ty:  *)
(*   Proper ((@rx_equal ty) ==> eq ==> eq ==> iff) (@in_re_set_xform ty). *)
(* Proof. intros rx1 rx2 H1 s1 s2 H2 v1 v2 H3. *)
(*   unfold rx_equal in H1. rewrite H1. crush. *)
(* Qed. *)

Lemma in_re_xform_intro: forall t (rex:re_xf_pair t) s v v',
  in_regexp (projT1 rex) s v' -> In v (xinterp (projT2 rex) v') -> 
    in_re_xform rex s v.
Proof. intros. unfold in_re_xform. destruct rex as [r f].  
       exists v'; crush.
Qed.

Lemma in_re_xform_intro2: 
  forall t r (f:regexp_type r ->> (xList_t t)) s v v',
  in_regexp r s v' -> In v (xinterp f v') -> 
    in_re_xform (existT _ r f) s v.
Proof. generalize in_re_xform_intro; crush. Qed.

Lemma in_re_xform_elim: forall t (rex:re_xf_pair t) s v,
  in_re_xform rex s v -> 
    exists v', in_regexp (projT1 rex) s v' /\ In v (xinterp (projT2 rex) v').
Proof. unfold in_re_xform; intros. destruct rex as [r f]. crush. Qed.

Lemma in_re_xform_elim2: 
  forall t r (f: regexp_type r ->> (xList_t t)) s v,
  in_re_xform (existT _ r f) s v -> 
    exists v', in_regexp r s v' /\ In v (xinterp f v').
Proof. generalize in_re_xform_elim. crush. Qed.

Lemma in_re_set_xform_intro: forall t (rx:RES.rs_xf_pair t) s v v',
  in_re_set (projT1 rx) s v' -> In v (xinterp (projT2 rx) v') -> 
    in_re_set_xform rx s v.
Proof. intros. unfold in_re_set_xform. destruct rx as [rs f].  
       exists v'; crush.
Qed.

Lemma in_re_set_xform_intro2: 
  forall t rs (f:RES.re_set_type rs ->> (xList_t t)) s v v',
  in_re_set rs s v' -> In v (xinterp f v') -> 
    in_re_set_xform (existT _ rs f) s v.
Proof.  generalize in_re_set_xform_intro; crush. Qed.

Lemma in_re_set_xform_elim: forall t (rx:RES.rs_xf_pair t) s v,
  in_re_set_xform rx s v -> 
    exists v', in_re_set (projT1 rx) s v' /\ In v (xinterp (projT2 rx) v').
Proof. unfold in_re_set_xform; intros. destruct rx as [rs f]. crush. Qed.

Lemma in_re_set_xform_elim2: 
  forall t rs (f: RES.re_set_type rs ->> (xList_t t)) s v,
  in_re_set_xform (existT _ rs f) s v -> 
    exists v', in_re_set rs s v' /\ In v (xinterp f v').
Proof. intros. generalize in_re_set_xform_elim. crush. Qed.

Lemma in_re_set_xform_xopt ty rs (f:RES.re_set_type rs ->> xList_t ty) str v:
  in_re_set_xform (existT _ rs (xopt f)) str v <->
  in_re_set_xform (existT _ rs f) str v.
Proof. unfold in_re_set_xform, RES.in_re_set_xform.
  rewrite xopt_corr. crush.
Qed.

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

Definition erase ty (rx:rs_xf_pair ty): RES.t := projT1 rx.
Extraction Implicit erase [ty].
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

Lemma xcoerce_eq t1 t2 (f:t1 ->> t2) (H1:t1=t1) (H2:t2=t2):
  xcoerce f H1 H2 = f.
Proof. assert (H1=eq_refl _). apply proof_irrelevance.
  assert (H2=eq_refl _). apply proof_irrelevance.
  subst. unfold xcoerce, eq_rec_r. simpl. trivial.
Qed.

(* (** reset_nullable(rs) is true iff one of the regexp in rs is nullable *) *)
(* Definition reset_nullable (rs:RESet.t): bool := *)
(*   RESet.exists_ regexp_nullable rs. *)

(* (** reset_always_rejects(rs) is true iff all regexps in rs always rejects *) *)
(* Definition reset_always_rejects (rs:RESet.t): bool := *)
(*   RESet.for_all regexp_always_rejects rs. *)
            
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
    | rEps | rZero => RES.empty
    | rChar _ | rAny => RES.singleton rEps
    | rCat r1 r2 => RES.union ((prebase r1) $ r2) (prebase r2)
    | rAlt r1 r2 => RES.union (prebase r1) (prebase r2)
    | rStar r1 => (prebase r1) $ (rStar r1)
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
    | rEps | rZero => 0
    | rChar _ => 1 
    (* Since Any is (Char c1 + Char c2 + ...), it appears it should
       return n in this case, where n is the number of chars in the alphabet;
       however, return 1 in this case seems fine; that is, prebase_upper_bound
       can still be proved *)
    | rAny => 1 
    | rCat r1 r2 | rAlt r1 r2 => num_of_syms r1 + num_of_syms r2
    | rStar r => num_of_syms r
  end.

(** ** Lemmas about set_cat_re *)

Lemma set_cat_re_intro1 : forall r s r2,
  RES.In r s -> r2 = rEps -> RES.In r (s $ r2).
Proof. crush. Qed.

Lemma set_cat_re_intro2 : forall r s r1 r2,
  RES.In r1 s -> r = rCat r1 r2 -> r2 <> rEps -> r2 <> rZero
    -> RES.In r (s $ r2).
Proof. destruct r2; 
  (congruence || simpl; intros; eapply re_set_map_intro; eassumption).
Qed.

Lemma set_cat_re_elim : forall r s r2,
  RES.In r (s $ r2) -> 
    (r2=rEps /\ RES.In r s) \/
    (r2=rZero /\ False) \/
    (r2<>rEps /\ r2<>rZero /\ exists r1, RES.In r1 s /\ r = rCat r1 r2).
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
    generalize (set_cat_re_cardinal (prebase r) (rStar r)). crush.
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

(* todo: add calls to opt_ag to nullable and pdrv as in Parser.v *)

Definition bool_type (b:bool) := 
  match b with true => xUnit_t | false => xVoid_t end.

(** nullable (r) returns (true, f) iff r can match the empty string and 
    f returns all values that are the results of parsing the empty string. *)
Fixpoint nullable (r:regexp) : 
  {b:bool & bool_type b ->> xList_t (regexp_type r)} :=
  match r return {b:bool & bool_type b ->> xList_t (regexp_type r)} with
    | rZero => existT _ false xzero
    | rEps => existT _ true (xcons xid xempty)
    | rChar _ | rAny => existT _ false xzero
    | rCat r1 r2 => 
      match nullable r1, nullable r2 with
        | existT true f1, existT true f2 => 
          existT _ true (xcomp (xpair f1 f2) xcross)
        | _, _ => existT _ false xzero
      end
    | rAlt r1 r2 => 
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
    | rStar r1 => existT _ true (xcons xempty xempty)
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
    | rEps | rZero => @RES.empty_xform _
    | rChar b => 
      if char_eq_dec a b then
        let (rs,f) := RES.singleton_xform rEps in
          existT _ rs (xcomp f (xmap (xchar a)))
      else @RES.empty_xform _
    | rAny => 
      let (rs,f) := RES.singleton_xform rEps in
          existT _ rs (xcomp f (xmap (xchar a)))
    | rAlt r1 r2 => 
      let (rs1, f1) := pdrv a r1 in
      let (rs2, f2) := pdrv a r2 in
        RES.union_xform (existT _ rs1 (xcomp f1 (xmap xinl)))
                        (existT _ rs2 (xcomp f2 (xmap xinr)))
    | rCat r1 r2 => 
      let rxc := RES.cat_re_xform (pdrv a r1) r2 in
      match nullable r1 with
        | existT true fnull => 
          let (rs2, f2) := pdrv a r2 in
          RES.union_xform rxc
            (existT _ rs2 (xcomp f2 (xcomp (xpair (xcomp xunit fnull) xid) xcross)))
        | existT false _ => rxc
      end
    | rStar r1 => 
      let (rsc, fc) := RES.cat_re_xform (pdrv a r1) (rStar r1) in
        existT _ rsc (xcomp fc (xmap (xcons xfst xsnd)))
  end.

(** pdrv_rex performs partial derviative calculation, similar to
    pdrv. However, it takes a re_xf_pair as input instead a regexp *)
Definition pdrv_rex ty (a:char_t) (rex:re_xf_pair ty) : rs_xf_pair ty := 
  let (r, f) := rex in
  let (rs, frs) := pdrv a r in
  existT _ rs (xcomp frs (xcomp (xmap f) xflatten)).
Extraction Implicit pdrv_rex [ty].

(* Definition pdrv_rex ty (a:char_t) (rex:re_xf_pair ty) : rs_xf_pair ty :=  *)
(*   let (r, f) := rex in *)
(*   let (rs, frs) := pdrv a r in *)
(*   existT _ rs (xopt (xcomp frs (xcomp (xmap f) xflatten))). *)

(** Partial derivatives over a regexp set; the result of the union 
    of taking partial derivatives on every regexp in the set *)
Definition pdrv_set ty (a:char_t) (rx:rs_xf_pair ty) : rs_xf_pair ty :=
  RES.fold_xform (fun rex rx1 => RES.union_xform (pdrv_rex a rex) rx1)
                 rx (@RES.empty_xform ty).
Extraction Implicit pdrv_set [ty].

(** Word partial derivatives; 
    wpdrv(nil, rs) = rs
    wpdrv(a cons w, rs) = wpdrv(w, pdrv_set(a, rs)) *)
Fixpoint wpdrv ty (s:list char_t) (rx:rs_xf_pair ty): rs_xf_pair ty := 
  match s with
    | nil => rx
    | a:: s' => let (rs, f) := pdrv_set a rx in
                wpdrv s' (existT _ rs (xopt f))
  end.
Extraction Implicit wpdrv [ty].

Definition wpdrv_re_set s (rs:RES.t) : rs_xf_pair (RES.re_set_type rs) :=
  wpdrv s (existT _ rs xsingleton).

(** ** Relating partial derivatives to prebase *)
Lemma pdrv_subset_prebase: 
  forall a r, RES.Subset (|pdrv a r|) (prebase r).
Proof. unfold erase; induction r; simpl; try (apply RESP.subset_refl).
  Case "Char".
    destruct_head; [apply RESP.subset_refl | apply RESP.subset_empty].
  Case "Cat".
    remember_rev (RES.cat_re_xform (pdrv a r1) r2) as crx.
    destruct crx as [rsc fc].
    assert (H4: rsc = projT1 (pdrv a r1) $ r2).
      rewrite <- cat_re_xform_erase2. rewrite Hcrx. trivial.
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
    remember_rev (RES.cat_re_xform (pdrv a r) (rStar r)) as crx.
    destruct crx as [rsc fc].
    assert (H4: rsc = projT1 (pdrv a r) $ (rStar r)).
      rewrite <- cat_re_xform_erase2. rewrite Hcrx. trivial.
    simpl. rewrite H4.
    apply RESF.map_subset. assumption.
Qed.

Lemma pdrv_subset_pdset: 
  forall a r, RES.Subset (|pdrv a r|) (pdset r).
Proof. unfold pdset; intros. 
  apply RESP.subset_add_2. apply pdrv_subset_prebase.
Qed.

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
      | _ => in_regexp_inv
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
      try (intros; intro; in_regexp_inv; find_contra).
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
          in_regexp_inv; find_contra.
          apply Coqlib.list_in_map_inv in H. crush.
      SCase "false true".
        xinterp_simpl. crush. 
          in_regexp_inv; find_contra.
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
      remember_rev (RES.cat_re_xform (pdrv a r1) r2) as cx. 
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
          SSSCase "~ (nullable r1)". find_contra.
        SSCase "s1=b::s1'".
          destruct n;
            [rewrite RES.union_xform_corr; left | idtac];
            rewrite <- Hcx;
            apply cat_re_xform_corr2; exists s1', s2, v1, v2;
            clear H10 IHr2 Hpr2; crush_hyp.
      SCase "<-".
        destruct n.
        SSCase "nullable r1".
          apply RES.union_xform_corr in H.
          destruct H.
          SSSCase "s in (pdrv a r1) $ r2".
            rewrite <- Hcx in H.
            apply cat_re_xform_corr2 in H.
            destruct H as [s1 [s2 [v1 [v2 H]]]]. 
            apply InrCat with (s1:= (a::s1)) (s2:=s2) (v1:=v1) (v2:=v2); crush.
          SSSCase "s in (pdrv a r2)".
            destruct v as [v1 v2].
            apply in_re_set_xform_elim2 in H.
            destruct H as [v' H]. 
            xinterp_simpl. sim.
            apply in_prod_iff in H0.
            apply InrCat with (s1:=nil) (s2:=a::s) (v1:=v1) (v2:=v2); crush.
        SSCase "not (nullable r1)".
          rewrite <- Hcx in H.
          apply cat_re_xform_corr2 in H; fold interp in *.
          destruct H as [s1 [s2 [v1 [v2 H]]]]. 
          apply InrCat with (s1:= (a::s1)) (s2:=s2) (v1:=v1) (v2:=v2); crush.
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
          sim; [eapply InrAlt_l | eapply InrAlt_r]; crush.
    Case "Star". simpl; intros.
      rewrite in_re_set_xform_comp2.
      split; intros.
      SCase "->".
        in_regexp_inv.
        exists (x1, x2); split; [idtac | trivial].
        apply cat_re_xform_corr2 with (r:=rStar r).
        destruct x as [|b x']; [crush | idtac].
        exists x', x0, x1, x2. crush_hyp.
      SCase "<-".
        destruct H as [[v1 v2] [H2 H4]].
        apply cat_re_xform_corr2 with (r:=rStar r) in H2.
        destruct H2 as [s1 [s2 H2]].
        apply InrStar_cons with (s1:= (a::s1)) (s2:=s2) (v1:=v1) (v2:=v2); crush.
  Qed.

End PDRV_CORRECT.

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
  simpl. destruct (pdrv_set a rx) as [rs f].
  rewrite IHw1. trivial.
Qed.

Lemma wpdrv_corr: forall ty str1 str2 (rx:rs_xf_pair ty) v, 
  in_re_set_xform (wpdrv str1 rx) str2 v <-> 
  in_re_set_xform rx (str1 ++ str2) v.
Proof. induction str1. crush.
  intros. simpl.
  remember_rev (pdrv_set a rx) as rx1.
  destruct rx1 as [rs f].
  rewrite IHstr1. rewrite in_re_set_xform_xopt.
  rewrite <- Hrx1. apply pdrv_set_corr.
Qed.

Lemma wpdrv_pdset_trans : forall ty w (rx:rs_xf_pair ty) r, 
  RES.Subset (|rx|) (pdset r) -> 
  RES.Subset (|wpdrv w rx|) (pdset r).
Proof. induction w; [auto | idtac].
  intros; simpl. 
  remember_rev (pdrv_set a rx) as rx1.
  destruct rx1 as [rs f].
  apply IHw. 
  apply pdrv_set_trans with (a:=a) in H. rewrite Hrx1 in H.
  unfold erase in *. simpl in *. crush.
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
  intros. unfold erase_eq. simpl.
  remember_rev (pdrv_set a rx1) as rx1'.
  destruct rx1' as [rs1 f1].
  remember_rev (pdrv_set a rx2) as rx2'.
  destruct rx2' as [rs2 f2].
  apply IHs. 
  apply pdrv_set_erase_eq with (a:=a) in H.
  rewrite Hrx1' in H. rewrite Hrx2' in H.
  unfold erase_eq in *. simpl in *. crush.
Qed.

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

  (* Lemmas about the above definitions *)

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
  Definition wfs_xf_pair (ty:xtype) := 
    {s: wf_state & RES.re_set_type (proj1_sig s) ->> xList_t ty}.

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
  Record entry_t (rownum:nat) (ss:wf_states) := 
    { (** which state do we go to next *)
      next_state : nat ; 
      (** the [next_state] is in bounds with respect to the number of states *)
      next_state_lt : next_state < cardinal_wfs ss ; 
      (** how do we transform ASTs from the next state back to this state *)
      next_xform : (* RES.re_set_type (ss.[next_state]) ->>
                   xList_t (RES.re_set_type (ss.[rownum])) *)
        xt_interp (RES.re_set_type (ss.[next_state]))->  
        xt_interp (xList_t (RES.re_set_type (ss.[rownum]))) 
    }.

  (** Entries for a row in the transition matrix -- an entry for each token *)  
  Definition entries_t (i:nat) (ss:wf_states) := list (entry_t i ss).

  Definition in_re_set_interp_xform 
             ty rs (f: xt_interp (RES.re_set_type rs) -> xt_interp (xList_t ty)) s v := 
    exists v', RES.in_re_set rs s v' /\ In v (f v').

  (** This predicate captures the fact that the ith entry in a row is
      semantically well-formed: if the transition edge goes to
      [next_state], then [next_xform] is the correct xform going from values
      of type ss.[gpos] back to values of type ss.[next_state] *)
  Definition wf_entries (gpos:nat)(ss:wf_states)(entries:entries_t gpos ss)
             (i:nat)(t:token_id) :=
    match nth_error entries i with
      | Some e =>
        forall str v, 
          in_re_set (ss.[gpos]) ((token_id_to_chars t) ++ str) v <->
          in_re_set_interp_xform (ss.[next_state e]) (next_xform e) str v
      | None => True
    end.

  Record transition_t(ss:wf_states) := {
    (** which row are we talking about *)
    row_num : nat ; 
    (** the row's index is in range for the number of states we have *)
    row_num_lt : row_num < RESS.cardinal (proj1_sig ss) ;
    (** what are the transition entries *)
    row_entries : entries_t row_num ss ;
    (** the list of values we get from this state when it is an accepting state *)
    row_nils : list (xt_interp (RES.re_set_type (ss.[row_num]))) 
  }.

  (** The transition matrix is then a list of rows *)
  Definition transitions_t (ss:wf_states) := list (transition_t ss).

  Record DFA := {
    (** number of states in the DFA *)
    dfa_num_states : nat ; 
    (** the list of [astgram]s for the states *)
    dfa_states : wf_states ; 
    dfa_states_len : cardinal_wfs dfa_states = dfa_num_states ; 
    (** the transition matrix for the DFA -- see above. *)
    dfa_transition : transitions_t dfa_states ; 
    (** the number of states equals the number of rows. *)
    dfa_transition_len : length dfa_transition = dfa_num_states ; 
    (** the [row_num] of the ith row should be i *)
    dfa_transition_r : forall i, match nth_error dfa_transition i with 
                                   | Some r => row_num r = i
                                   | None => True
                                 end
    (** which states are accepting states -- no longer used *)
    (* dfa_accepts : list bool ;  *)
    (* dfa_accepts_len : length dfa_accepts = dfa_num_states ;  *)
    (** which states are failure states -- no longer used *)
    (* dfa_rejects : list bool ; *)
    (* dfa_rejects_len : length dfa_rejects = dfa_num_states *)
  }.

  (** Same as above, but using vectors instead of lists for the
      transition matrix. *)
   Definition ventries_t (i:nat) (ss:wf_states) := Vector.vector (entry_t i ss).

   Record vtransition_t(ss:wf_states) := {
    (** which row are we talking about *)
    vrow_num : nat ; 
    (** the row's index is in range for the number of states we have *)
    vrow_num_lt : vrow_num < RESS.cardinal (proj1_sig ss) ;
    (** what are the transition entries *)
    vrow_entries : ventries_t vrow_num ss ;
    (** the list of values we get from this state when it is an accepting state *)
    vrow_nils : list (xt_interp (RES.re_set_type (ss.[vrow_num]))) 
  }.

  Definition vtransitions_t (ss:wf_states) := Vector.vector (vtransition_t ss).

  Record vDFA := { 
    vdfa_num_states : nat ; 
    vdfa_states : wf_states ; 
    vdfa_states_len : cardinal_wfs vdfa_states = vdfa_num_states ; 
    vdfa_transition : vtransitions_t vdfa_states ; 
    vdfa_transition_len : Vector.length vdfa_transition = vdfa_num_states ; 
    vdfa_transition_r : forall i (H:i < Vector.length vdfa_transition), 
                          vrow_num (Vector.get vdfa_transition i H) = i
  }.

  Definition transition_to_vtransition (ss:wf_states) (t:transition_t ss) :=
    {| vrow_num := row_num t ; 
       vrow_num_lt := row_num_lt t ; 
       vrow_entries := Vector.of_list (row_entries t) ; 
       vrow_nils := row_nils t
    |}.

  Definition dfa_to_vdfa (d:DFA) : vDFA.
  refine (
   {| vdfa_num_states := dfa_num_states d; 
      vdfa_states := dfa_states d; 
      vdfa_states_len := dfa_states_len d; 
      vdfa_transition := Vector.of_list (map (@transition_to_vtransition (dfa_states d)) 
                                         (dfa_transition d)); 
      vdfa_transition_len := _ ;
      vdfa_transition_r := _
   |}
  ).
  rewrite Vector.length_of_list. rewrite map_length. apply (dfa_transition_len d).
  intros. generalize (Vector.get_of_list _ (map (transition_to_vtransition (ss:=dfa_states d)) (dfa_transition d)) i H). intro.
  generalize (Coqlib.map_nth_error_imply _ _ _ H0). crush.
  specialize (dfa_transition_r d i). rewrite H1. rewrite <- H2.
  destruct x. simpl. auto.
  Defined.

  (* provide a way to dump out info on a DFA *)
  Section DFA_TO_STRING.
    Require Import Coq.Program.Wf.
    Require Import String.
    Definition digit2string (n:nat) :string := 
      match n with 
        | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
        | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
      end.

    Program Fixpoint nat_show (n:nat) {measure n} : string :=
      if Compare_dec.le_gt_dec n 9 then
        digit2string n
      else
        let n' := NPeano.div n 10 in
        (@nat_show n' _) ++ (digit2string (n - 10 * n')).
    Next Obligation.
      assert (NPeano.div n 10 < n) ; eauto.
      eapply NPeano.Nat.div_lt ; omega.
    Defined.

    Definition nl := String (Ascii.ascii_of_nat 10) EmptyString.

    Definition entry_show {n ss} (e:entry_t n ss) : string := nat_show (next_state e).
    Fixpoint list_show' {A} (show:A -> string) (sep:string) (stop:string) (xs:list A) : 
      string := 
      match xs with 
        | nil => stop
        | x::xs' => (show x) ++ sep ++ (list_show' show sep stop xs')
      end.
    Definition list_show {A} (show:A -> string) (start sep stop:string) (xs:list A) :=
      start ++ (list_show' show sep stop xs).
    Definition entries_show {i ss} (xs:list (entry_t i ss)) : string := 
      nat_show i ++ ": " ++ (list_show entry_show "[" "," "]" xs).
    Definition transition_show {ss} (t:transition_t ss) : string := 
      entries_show (row_entries t).
    Definition transitions_show {ss} (ts:transitions_t ss) : string := 
      list_show transition_show "{" (";" ++ nl) "}" ts.
    Definition dfa_show (d:DFA) : string := transitions_show (dfa_transition d).
  End DFA_TO_STRING.
  
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

  Lemma wfs_ext_cardinal_leq_trans n ss ss':
    wfs_ext ss ss' -> n < cardinal_wfs ss -> n < cardinal_wfs ss'.
  Proof. intros; eapply lt_le_trans. eassumption.
    apply wfs_ext_cardinal_leq. trivial.
  Qed.

  Lemma wfs_ext_gew_cardinal_leq n ss ss' s: 
    wfs_ext ss ss' -> get_element_wfs n ss = Some s -> n < cardinal_wfs ss'.
  Proof. intros.
    eapply wfs_ext_cardinal_leq_trans. eassumption.
      eapply RESS.get_element_some_lt. eassumption.
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
    assert (H12:cardinal_wfs ss = List.length (RESS.elements (proj1_sig ss))).
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
    wfs_ext ss ss' -> n < cardinal_wfs ss -> ss'.[n] = ss.[n].
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
    (s ::: ss).[cardinal_wfs ss] = proj1_sig s.
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
    get_element_wfs n ss = Some rs -> ss.[n] = rs.
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

  Lemma wf_entries_nil n ss i t: @wf_entries n ss nil i t.
  Proof. unfold wf_entries. rewrite Coqlib.nth_error_nil. trivial. Qed.

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

  (** ** Generate the transition matrix row for the state.
      The table has been closed up to gpos.  In general, this will add new
      states. *)

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
      exact (RES.equal_xform (RES.Equal_sym H2)).
    Defined.

    Lemma gen_row_help1 s ss ss' n:
      wfs_ext ss ss' ->
      get_index_wfs s ss = Some n ->
      n < cardinal_wfs ss'.
    Proof. intros. eapply RESS.get_index_some_lt.
      eapply get_index_wfs_ext; eassumption.
    Qed.

    Lemma gen_row_help2 : forall s ss ss',
      get_index_wfs s ss = None -> wfs_ext (s ::: ss) ss' ->
      RES.re_set_type (proj1_sig s) =
      RES.re_set_type (ss'.[cardinal_wfs ss]).
    Proof. intros.
      erewrite <- get_state_get_index_none by eassumption.
      assert (cardinal_wfs ss < cardinal_wfs (s ::: ss)).
        generalize (add_wfs_cardinal s ss H). omega.
      erewrite <- get_state_wfs_ext by eassumption.
      trivial.
    Qed.

    Lemma gen_row_help3 : forall n rs ss ss',
      ss.[n] = rs -> n < cardinal_wfs ss ->
      wfs_ext ss ss' ->
      xList_t (RES.re_set_type rs) = xList_t (RES.re_set_type (ss'.[n])).
    Proof. intros. repeat f_equal. 
      erewrite get_state_wfs_ext by eassumption. crush.
    Qed.

    Lemma gen_row_help4 (s s1:wf_state) (ss:wf_states) n:
      get_index_wfs s1 ss = None ->
      n < cardinal_wfs ss ->
      ss.[n] = proj1_sig s ->
      (s1 ::: ss).[n] = proj1_sig s.
    Proof. intros.
      rewrite <- H1. 
      apply get_state_wfs_ext.
        apply wfs_ext_add2. assumption.
        trivial.
    Qed.

    Lemma gen_row_help5 (s s1:wf_state) gpos ss ss':
      ss.[gpos] = proj1_sig s -> gpos < cardinal_wfs ss ->
      get_index_wfs s1 ss = None ->
      wfs_ext (s1 ::: ss) ss' ->
      xList_t (RES.re_set_type (proj1_sig s)) = 
      xList_t (RES.re_set_type (ss'.[gpos])).
    Proof. intros.
      eapply gen_row_help3. eassumption. assumption.
      eapply wfs_ext_trans.
        eapply wfs_ext_add2. eassumption.
        trivial.
    Qed.

    Variable s : wf_state.
    Variable gpos : nat.

    (* todo: should we use | instead of & before wfs_ext *)
    (* Return type of gen_row' *)
    Definition gen_row_ret_t (ss:wf_states) (n:nat) (tid:token_id) :=
      {ss':wf_states & {entries : entries_t gpos ss' & wfs_ext ss ss'}}.

    Definition fcoerce {t1 t2 t3 t4:xtype} (f:xt_interp t1 -> xt_interp t2) : 
      t1 = t3 -> t2 = t4 -> xt_interp t3 -> xt_interp t4.
    Proof.
      intros. subst. apply (f X).
    Defined.    

    (** This hideous function is basically calculating the derivative
         of [ss[gpos]] with respect to all tokens from [num_tokens] down to 0,
         and adding the corresponding entries to the row.  At the same
         time, it's collecting the new states and adding them to [ss].
         We must carry around a lot of auxiliary information to ensure
         that [gpos] is in bounds, and to build a well-formed entry. 
         What we get out is a new set of states, [ss'], a new [entries_t]
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
                      let (entries, Hwfs) := r in
                      let f_back := gen_backward_xform _ Hwfs Hgi in
                      let e : entry_t gpos ss' :=
                          {| next_state := n ;
                             next_state_lt := gen_row_help1 _ Hwfs Hgi;
                             next_xform := 
                               xinterp (xopt (xcomp f_back
                                               (xcoerce f1 eq_refl
                                                 (gen_row_help3 H H1 Hwfs)))) |} in
                      existT _ ss' (existT _ (e::entries) _)
                  | inright Hgi =>
                      let (ss', r) := gen_row' n' (s1 ::: ss) (1 + tid) _ _ in
                      let (entries, Hwfs) := r in
                      let e : entry_t gpos ss' :=
                          {| next_state := cardinal_wfs ss;
                             next_state_lt := _ ;
                             next_xform := xinterp (xcoerce f1 (gen_row_help2 Hgi Hwfs) 
                                             (gen_row_help5 s H H1 Hgi Hwfs)) |} in
                      existT _ ss' (existT _ (e::entries) _)
                end
            end
      end); clear gen_row'.
      apply wfs_ext_refl.
      trivial.
      apply gen_row_help4; trivial.
      abstract (generalize (add_wfs_cardinal_leq s1 ss); omega).
      apply wfs_ext_cardinal_leq in Hwfs.
      abstract (generalize (add_wfs_cardinal s1 ss Hgi); omega).
      eapply wfs_ext_trans. 
        eapply wfs_ext_add2. eassumption.
        trivial.
    Defined.

    (** Kick off the row generation starting with [num_tokens.] *)
    Definition gen_row (ss:wf_states)
               (H:ss.[gpos] = proj1_sig s) (H1: gpos < cardinal_wfs ss) :
               gen_row_ret_t ss num_tokens 0 :=
      gen_row' num_tokens ss 0 H H1.
  
    (** This is the main loop-invariant for [gen_row'].  Given a state [s],
      a list of states [ss], and a token number [n], running [gen_row' n ss
      tid] yields a list of states [ss1] and transition-table [entries1] such
      that the length of [entries1] is [n], [ss1] is an extension of [ss], and
      for all [tid'], the well-formed entries inv holds. *)
    Lemma gen_row'_prop: forall n ss tid (H:ss.[gpos] = proj1_sig s) 
          (H1:gpos < cardinal_wfs ss),
      n <= num_tokens -> tid = num_tokens-n ->
      match gen_row' n ss tid H H1 with 
        | existT ss1 (existT entries1 Hwfs) => 
          List.length entries1 = n /\
          forall tid', tid' >= tid -> wf_entries entries1 (tid'-tid) tid'
      end.
    Proof. induction n.
      Case "base". intros. compute [gen_row'].
        split; [trivial | idtac].
        intros. subst. apply wf_entries_nil.
      Case "S n". intros.
        remember_rev (gen_row' (S n) ss tid H H1) as gr.
        destruct gr as [ss1 rss].
        destruct rss as [entries' Hwfs].
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
            erewrite get_state_wfs_ext; eassumption.
          intros. 
          match goal with 
            | [H:tid' >= tid |- _] => apply le_lt_or_eq in H; destruct H
          end.
          SSCase "tid < tid'".
            replace (tid'-tid) with (S (tid' - (1 + tid))) by omega.
            unfold wf_entries. compute [nth_error].
            apply H6. omega.
          SSCase "tid = tid'".
            subst tid'. rewrite minus_diag.
            unfold wf_entries. compute [nth_error value next_state next_xform].
            generalize (gen_row_help3 H H1 Hwfs1).
            rewrite H8.
            intros.
            rewrite wpdrv_wf_corr by eassumption.
            unfold gen_backward_xform.
            generalize ((get_state_get_index_some s1 ss'
                 (get_index_wfs_ext s1 Hwfs1 Hgiw))). intro H10.
            rewrite (RES.equal_xform_corr2 H10).
            rewrite xcoerce_eq. repeat rewrite xopt_corr.
            split; intros; trivial. 
        SCase "s1 notin ss".
          remember (gen_row_help4 s s1 ss e H1 H) as H4.
          remember (gen_row'_subproof (S n) ss tid H H1 n s1 f1 e) as H6.
          remember_rev (gen_row' n (s1 ::: ss) (1 + tid) H4 H6) as grr.
          destruct grr as [ss' rr].
          destruct rr as [entries Hwfs1].
          inversion_clear Hgr. simpl.
          assert (H8:ss'.[gpos] = proj1_sig s).
            rewrite <- H. 
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
            unfold wf_entries. compute [nth_error].
            apply H12. omega.
          SSCase "tid = tid'".
            subst tid'. rewrite minus_diag.
            unfold wf_entries. compute [nth_error value next_state next_xform].
            generalize (gen_row_help2 e Hwfs1) (gen_row_help5 s H H1 e Hwfs1).
            rewrite H8.
            use_lemma get_state_get_index_none by eassumption.
            assert (H14:ss'.[cardinal_wfs ss] = proj1_sig s1).
              erewrite get_state_wfs_ext with (ss:=s1:::ss).
              eassumption. assumption.
              generalize (add_wfs_cardinal s1 ss e).  omega.
            rewrite H14.
            intros.
            rewrite wpdrv_wf_corr by eassumption.
            rewrite xcoerce_eq.
            split; intros; trivial.
    Qed.

    Lemma gen_row_prop: forall ss (H:ss.[gpos] = proj1_sig s) 
          (H1:gpos < cardinal_wfs ss),
      match gen_row ss H H1 with 
        | existT ss1 (existT entries1 Hwfs) => 
          List.length entries1 = num_tokens /\
          forall tid, wf_entries entries1 tid tid
      end.
    Proof. unfold gen_row. intros.
      use_lemma (@gen_row'_prop num_tokens ss 0 H H1) by omega.
      remember (gen_row' num_tokens ss 0 H H1) as gr.
      destruct gr as [ss1 rr].
      destruct rr as [entries1 Hwfs].
      clear Heqgr. 
      split. crush.
      sim. intro.
      rewrite (minus_n_O tid) at 1.
      apply H2. omega.
    Qed.

  End GENROW.

  (** ** Build transitions tables of the DFA *)

  (** We build some entries in the transition matrix before we've discovered
      all of the states.  So we have to coerce these entries to work with the
      bigger set of states, which unfortunately, isn't just done at the top-level. *)
  Lemma coerce_entry_help1 n ss ss': 
    wfs_ext ss ss' -> n < cardinal_wfs ss ->
    RES.re_set_type (ss.[n]) = RES.re_set_type (ss'.[n]).
  Proof. intros. f_equal. symmetry; auto using get_state_wfs_ext. Qed.

  Lemma coerce_entry_help2 n ss ss': 
    wfs_ext ss ss' -> n < cardinal_wfs ss ->
    xList_t (RES.re_set_type (ss.[n])) = 
    xList_t (RES.re_set_type (ss'.[n])).
  Proof. intros. f_equal. auto using coerce_entry_help1. Qed.

  Definition coerce_entry n ss ss' (H:wfs_ext ss ss') (H1:n < cardinal_wfs ss)  
             (e:entry_t n ss) : entry_t n ss' :=
       {| next_state := next_state e ;
          next_state_lt := wfs_ext_cardinal_leq_trans H (next_state_lt e) ;
          next_xform := fcoerce (next_xform e) 
                          (coerce_entry_help1 H (next_state_lt e))
                          (coerce_entry_help2 H H1)
       |}.

  (** Similarly, we have to coerce the pre-computed [astgram_extract_nil] values
      for previous rows. *)
  Definition coerce_nils ss ss' i (H: wfs_ext ss ss') (H1: i < cardinal_wfs ss) 
             (v:xt_interp (RES.re_set_type (ss.[i]))) :
    xt_interp (RES.re_set_type (ss'.[i])).
    intros. erewrite (get_state_wfs_ext H H1). assumption.
  Defined.

  (** Used to coerce previous rows so that instead of being indexed by the *)
  (*     original set of states [s], they are now indexed by [s ++ s1]. *)
  Definition coerce_transitions ss ss' (H:wfs_ext ss ss')
              (ts:transitions_t ss) : transitions_t ss' :=
    List.map (fun (t:transition_t ss) =>
      {| row_num := row_num t ;
         row_num_lt :=
           (lt_le_trans _ _ _ (row_num_lt t) (wfs_ext_cardinal_leq H)) ;
         row_entries :=
           List.map (coerce_entry H (row_num_lt t)) (row_entries t) ;
         row_nils := List.map (coerce_nils H (row_num_lt t)) (row_nils t) 
      |}) ts.

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
  
  Lemma build_table_help1 n (s:wf_state) ss: 
    get_element_wfs n ss = Some (proj1_sig s) ->
    ss.[n] = proj1_sig s.
  Proof. intros; apply get_state_get_element_some. trivial. Qed.

  Lemma build_table_help2 n (s:wf_state) ss: 
    get_element_wfs n ss = Some (proj1_sig s) ->
    n < cardinal_wfs ss.
  Proof. intros.
    apply RESS.get_element_some_lt in H. unfold cardinal_wfs. trivial.
  Qed.

  Definition cons_transition n ss 
             (entries:entries_t n ss) (H:n<cardinal_wfs ss) := 
     {| row_num := n; 
        row_num_lt := H;
        row_entries := entries;
        row_nils := RES.re_set_extract_nil (ss.[n]) |}.

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
  Unset Implicit Arguments.
  Require Import List.
  Require Import Coq.Program.Wf.
  Program Fixpoint build_table (ss:wf_states) (rows:transitions_t ss)
          (next_state:nat) {wf build_table_metric next_state} : 
    {ss':wf_states & transitions_t ss'} :=
    match get_element_wfs2 next_state ss with
         | inright _ => existT _ ss rows
         | inleft s0 =>
           let (s, Hge) := s0 in
           match (gen_row s ss (build_table_help1 _ _ _ Hge)
                    (build_table_help2 _ _ _ Hge)) with
             | existT ss' (existT entries Hwfs) =>
                 build_table ss' 
                   (coerce_transitions Hwfs rows ++ 
                     cons_transition entries 
                       (wfs_ext_gew_cardinal_leq _ Hwfs Hge)::nil) (1+next_state)
            end
    end.
  Next Obligation.
    destruct Heq_anonymous.
    apply RESS.get_element_some_lt in H.
    eauto using build_table_metric_dec.
  Defined.
  Next Obligation.
    apply measure_wf. apply limit_nat_wf.
  Defined.
  Set Implicit Arguments.

  Import WfExtensionality.
  Lemma build_table_unfold (ss:wf_states) rows next_state:
    build_table ss rows next_state  =
    match get_element_wfs2 next_state ss with
         | inright _ => existT _ ss rows
         | inleft s0 =>
           let (s, Hge) := s0 in
           match (gen_row s ss (build_table_help1 _ _ _ Hge)
                    (build_table_help2 _ _ _ Hge)) with
             | existT ss' (existT entries Hwfs) =>
                 build_table ss' 
                   (coerce_transitions Hwfs rows ++ 
                     cons_transition entries 
                       (wfs_ext_gew_cardinal_leq _ Hwfs Hge)::nil) (1+next_state)
            end
    end.
  Proof.
    unfold build_table at 1.
    unfold_sub build_table_func 
     (build_table_func 
        (existT (fun ss0 : wf_states => {_ : transitions_t ss0 & nat}) ss
                (existT (fun _ : transitions_t ss => nat) rows next_state))).
    simpl.
    destruct (get_element_wfs2 next_state ss); [idtac | trivial].
    destruct s. 
    generalize (build_table_help1 next_state x ss e)
               (build_table_help2 next_state x ss e).
    intros H2 H4.
    destruct (gen_row x ss H2 H4). simpl.
    destruct s. trivial.
  Qed.

  Definition ini_state: wf_state.
    refine (exist _ (RESet.singleton r) _).
    exists nil. simpl. reflexivity. 
  Defined.

  Definition ini_states: wf_states.
    refine (exist _ (RESS.singleton (proj1_sig ini_state)) _).
    intros s H.
    apply RESSP.FM.singleton_1 in H. rewrite <- H.
    apply (proj2_sig ini_state).
  Defined.

  (** We start with the initial [regexp] in state 0 and then try to close
      off the table. *)
  Definition build_transition_table := build_table ini_states nil 0.

  (** This is the main invariant for the [build_table] routine. *)
  Definition build_table_inv n (ss:wf_states) (rows:transitions_t ss) := 
     1 <= cardinal_wfs ss /\ n <= cardinal_wfs ss /\
     forall i, i < n -> 
       match nth_error rows i with 
         | Some ts => 
           (* have an entry in the row for each token *)
           List.length (row_entries ts) = num_tokens /\ 
           (* row_num is the right number *)
           row_num ts = i /\
           (* each entry in the row is semantically correct *)
           (forall tid, wf_entries (row_entries ts) tid tid) /\
           (* the row_nils are what you get when running [re_set_extract_nil] on the 
              row's RESet *)
           row_nils ts = RES.re_set_extract_nil (ss.[row_num ts])
         | _ => False
       end.

  Definition wf_table ss rows := @build_table_inv (List.length rows) ss rows.

  Lemma fcoerce_eq t1 t2 (f : xt_interp t1 -> xt_interp t2) (H1 : t1 = t1) (H2 : t2 = t2) :
    fcoerce f H1 H2 = f.
  Proof.
    rewrite (@proof_irrelevance _ H1 eq_refl).
    rewrite (@proof_irrelevance _ H2 eq_refl).
    auto.
  Qed.

  Opaque token_id_to_chars in_re_set_xform.
  Lemma wf_entries_coerce_entry n ss ss' i tid 
        (entries:entries_t n ss) (Hwfs:wfs_ext ss ss') (H1:n < cardinal_wfs ss):
    wf_entries entries i tid ->
    wf_entries (map (coerce_entry Hwfs H1) entries) i tid.
  Proof. unfold coerce_entry, wf_entries. intros.
    remember_destruct_head as ne; [idtac | trivial].
    apply Coqlib.map_nth_error_imply in Hne.
    destruct Hne as [en [H2 H4]].
    subst e. simpl.
    rewrite H2 in H.
    generalize (coerce_entry_help1 Hwfs (next_state_lt en))
               (coerce_entry_help2 Hwfs H1).
    assert (H4:ss'.[n] = ss.[n]). auto using get_state_wfs_ext.
    assert (H6:ss'.[next_state en] = ss.[next_state en]). 
      generalize (next_state_lt en). auto using get_state_wfs_ext.
    rewrite H4, H6. 
    intros. rewrite fcoerce_eq by assumption.
    trivial.
  Qed.
  Transparent token_id_to_chars in_re_set_xform.

  Lemma coerce_nils_corr n ss ss'
   (Hwfs:wfs_ext ss ss') (H1:n<cardinal_wfs ss):
   map (coerce_nils Hwfs H1) (RES.re_set_extract_nil (ss.[n]))
     = RES.re_set_extract_nil (ss'.[n]).
  Proof. 
    assert (ss'.[n]=ss.[n]).
      apply get_state_wfs_ext; assumption.
    unfold coerce_nils. generalize (get_state_wfs_ext Hwfs H1).
    rewrite H. intros. rewrite (proof_irrelevance _ e eq_refl). 
    unfold eq_rect_r, eq_rect. simpl.
    apply Coqlib.list_map_identity.
  Qed.

  Lemma build_table_inv_imp n ss (rows:transitions_t ss) :
    build_table_inv n rows -> 
    1 <= cardinal_wfs ss /\ n <= cardinal_wfs ss /\ n <= List.length rows.
  Proof.
    unfold build_table_inv ; destruct n.
      intros; repeat split; [crush | crush | auto with arith].
      intros. assert (n < S n) by omega.
        destruct H as [H [H2 H4]].
        generalize (H4 n H0).
        remember_destruct_head as ne; [idtac | crush].
        intros.
        apply Coqlib.nth_error_some_lt in Hne.
        crush.
  Qed.

  Hint Rewrite Coqlib.list_length_map.

  Lemma gen_row_build_table_inv n ss rows :
    n = List.length rows ->
    match get_element_wfs2 n ss with
      | inleft s0 =>
        let (s, Hge) := s0 in
        forall ss1 entries (Hwfs:wfs_ext ss ss1),
         gen_row s ss (build_table_help1 _ _ _ Hge) (build_table_help2 _ _ _ Hge)
           = existT _ ss1 (existT _ entries Hwfs)
         -> build_table_inv n rows
         -> build_table_inv (1+n) 
              (coerce_transitions Hwfs rows ++ 
                 cons_transition entries 
                 (wfs_ext_gew_cardinal_leq _ Hwfs Hge)::nil)
      | inright _ => True
    end.
  Proof. remember_rev (get_element_wfs2 n ss) as gew.
    destruct gew; [idtac | crush]. clear Hgew.
    destruct s as [s Hgew].
    generalize (build_table_help1 n s ss Hgew) (build_table_help2 n s ss Hgew).
    intros H2 H4. intros.
    assert (n=List.length (coerce_transitions Hwfs rows)).
      unfold coerce_transitions. crush.
    generalize (gen_row_prop _ _ H2 H4).
    rewrite H0. intros. sim.
    unfold build_table_inv in *.
    use_lemma wfs_ext_cardinal_leq by eassumption.
    destruct H1 as [H14 [H16 H18]].
    repeat split; [crush | crush | idtac].
    intros.
    match goal with
      | [H:i<1+n |- _] => destruct (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H))
    end.
    Case "i<n".
      rewrite Coqlib.nth_error_app_lt by omega.
      remember_rev (nth_error (coerce_transitions Hwfs rows) i) as ne.
      destruct ne as [ts1 | ].
      SCase "ne=Some ...".
        unfold coerce_transitions in Hne.
        apply Coqlib.map_nth_error_imply in Hne.
        destruct Hne as [ts [H10 H12]].
        specialize (H18 i H8). rewrite H10 in H18.
        subst ts1. simpl.
        repeat split; crush.
          auto using wf_entries_coerce_entry. 
          apply coerce_nils_corr.
      SCase "ne=None".
        use_lemma Coqlib.nth_error_none by eassumption. omega.
    Case "i=n". subst i.
      rewrite Coqlib.nth_error_app_eq by omega. simpl.
      crush.
  Qed.

  (** This lemma establishes that the [build_table] loop maintains the
      [build_table_inv] and only adds to the states and rows of the table. *)
  Lemma build_table_prop: forall n ss rows,
     n = List.length rows -> build_table_inv n rows ->
     match build_table ss rows n with 
       | existT ss' rows' => 
         List.length rows' = cardinal_wfs ss' /\ 
         wf_table rows' /\ wfs_ext ss ss'
         (* /\ exists rows1, rows' = rows ++ rows1 *)
     end.
  Proof. induction n using (well_founded_ind (limit_nat_wf max_pdrv)).
    intros. remember_head as gw.
    destruct gw as [ss' rows'].
    rewrite build_table_unfold in Hgw.
    use_lemma (@gen_row_build_table_inv n ss rows) by eassumption.
    destruct (get_element_wfs2 n ss).
    Case "ss[n] exists".
      destruct s as [s ge].
      remember (gen_row s ss (build_table_help1 n s ss ge)
                  (build_table_help2 n s ss ge)) as gr.
      destruct gr as [ss1 [entries Hwfs]].
      specialize (H2 ss1 entries Hwfs eq_refl H1).
      remember (cons_transition entries
                  (wfs_ext_gew_cardinal_leq _ Hwfs ge)) as row.
      remember (coerce_transitions Hwfs rows ++ row :: nil) as rows1.
      assert (n < cardinal_wfs ss).
        use_lemma RESS.get_element_some_lt by eassumption. trivial.
      use_lemma build_table_metric_dec by eassumption. 
      assert (S n = List.length rows1). 
        unfold coerce_transitions in Heqrows1. crush.
      assert (build_table_inv (1+n) rows1) by crush.
      use_lemma H by eassumption. clear H.
      simpl in Hgw.
      rewrite Hgw in *.
      crush. reflexivity.
    Case "ss[n] not exists".
      use_lemma build_table_inv_imp by eassumption.
      crush. reflexivity.
  Qed.

  Lemma build_table_inv_ini: @build_table_inv 0 ini_states nil.
  Proof. unfold build_table_inv. crush. Qed.

  Lemma build_transition_table_prop: 
    match build_transition_table with
      | existT ss rows =>
        List.length rows = cardinal_wfs ss /\ wf_table rows /\
        wfs_ext ini_states ss
    end.
  Proof. unfold build_transition_table.
    use_lemma build_table_inv_ini by assumption.
    generalize (@build_table_prop 0 ini_states nil). intro.
    use_lemma H0 by trivial. 
    remember (build_table ini_states nil 0) as bt.
    destruct bt. crush.
  Qed.

  (** ** Build the DFA from a [regexp]. *)

  Lemma build_dfa_help1 ss rows:
    build_transition_table = existT _ ss rows -> 
    List.length rows = cardinal_wfs ss.
  Proof. intros. generalize build_transition_table_prop.
    rewrite H. crush.
  Qed.

  Lemma build_dfa_help2 ss rows:
    build_transition_table = existT _ ss rows -> 
    forall i, match nth_error rows i with
                | Some row => row_num row = i
                | None => True
              end.
  Proof. intros. generalize build_transition_table_prop.
    rewrite H.
    unfold wf_table, build_table_inv. intros. sim.
    remember_destruct_head as nt; [idtac | trivial].
    use_lemma Coqlib.nth_error_some_lt by eassumption.
    specialize (H4 i). rewrite Hnt in H4. crush.
  Defined.

  (** Now we can build the [DFA] using all of the helper functions.  I've
      only included enough information here to make it possible to run the
      parser and get something out that's type-correct, but not enough
      info to prove that the parser is correct. *)
  Definition build_dfa : DFA :=
    (match build_transition_table as bt
           return build_transition_table = bt -> _ with
       | existT ss table => fun Hbt =>
          {| dfa_num_states := cardinal_wfs ss ; 
             dfa_states := ss ; 
             dfa_states_len := eq_refl _ ;
             dfa_transition := table ; 
             dfa_transition_len := build_dfa_help1 Hbt ;
             dfa_transition_r := build_dfa_help2 Hbt
           |}
     end) eq_refl.

  Definition build_vdfa : vDFA := dfa_to_vdfa build_dfa.

  Definition wf_ventry(gpos:nat)(ss:wf_states)(e:entry_t gpos ss) (t:token_id) :=
    forall str v, 
      in_re_set (ss.[gpos]) ((token_id_to_chars t) ++ str) v <->
      in_re_set_interp_xform (ss.[next_state e]) (next_xform e) str v.

  Definition wf_vtable ss (rows:vtransitions_t ss) := 
   1 <= cardinal_wfs ss /\ (Vector.length rows) <= cardinal_wfs ss /\ 
   forall i (H: i < Vector.length rows),
     let ts := Vector.get rows i H in 
     Vector.length (vrow_entries ts) = num_tokens /\ 
     vrow_num ts = i /\ 
     (forall tid (H' : tid < Vector.length (vrow_entries ts)),
        wf_ventry (Vector.get (vrow_entries ts) tid H') tid) /\ 
     vrow_nils ts = RES.re_set_extract_nil (ss.[vrow_num ts]).

  Definition wf_dfa (d:DFA) := 
    wf_table (dfa_transition d) /\
    d = build_dfa /\
    (dfa_states d).[0] = RES.singleton r.

  Definition wf_vdfa (d: vDFA) := 
    wf_vtable (vdfa_transition d) /\ 
    d = dfa_to_vdfa build_dfa /\ 
    (vdfa_states d).[0] = RES.singleton r.

  Lemma build_dfa_prop: wf_dfa build_dfa.
  Proof. unfold wf_dfa, build_dfa.
    generalize build_transition_table_prop; intro H.
    generalize build_dfa_help1, build_dfa_help2.
    remember build_transition_table as bt.
    destruct bt as [ss rows]. intros. 
    split; [crush | idtac].
    subst. simpl.
    assert (H6: 0 < cardinal_wfs ini_states).
      unfold ini_states, cardinal_wfs. simpl.
      rewrite RESSP.singleton_cardinal. omega.
    destruct H as [H [H2 H4]].
    erewrite get_state_wfs_ext by eassumption.
    unfold get_state, ini_states. simpl. crush.
  Qed.

  Lemma build_vdfa_prop : wf_vdfa build_vdfa.
  Proof. generalize build_dfa_prop. unfold wf_dfa, wf_vdfa.
    unfold build_vdfa. intros [H1 [H2 H3]]. split ; 
    [idtac | split ; auto]. unfold dfa_to_vdfa. simpl. 
    unfold wf_vtable. destruct H1 as [H4 [H5 H6]].
    split ; auto. split. rewrite Vector.length_of_list.
    rewrite map_length. auto. intros.
    assert (i < Datatypes.length (dfa_transition build_dfa)).
    rewrite Vector.length_of_list in H. rewrite map_length in H.
    auto. specialize (H6 _ H0). 
    specialize (Vector.get_of_list _ _ _ H). intro. 
    rewrite Coqlib.list_map_nth in H1.
    remember (nth_error (dfa_transition build_dfa) i) as e.
    destruct e ; try contradiction. simpl in H1. injection H1 ; 
    intros ; clear H1. rewrite <- H7. 
    destruct H6 as [H8 [H9 [H10 H11]]].
    unfold transition_to_vtransition ; simpl. split. 
    rewrite Vector.length_of_list. auto. split ; auto. 
    split ; auto. intros. specialize (H10 tid). 
    unfold wf_entries in H10. 
    generalize (Vector.get_of_list _ _ _ H'). intros.
    rewrite H1 in H10. intros str v. specialize (H10 str v). auto.
  Qed.
  
  (** A DFA has at least one state. *)
  Lemma dfa_at_least_one: 0 < dfa_num_states build_dfa.
  Proof. intros.
    use_lemma build_dfa_prop by eassumption.
    unfold wf_dfa, wf_table, build_table_inv in H.
    sim. generalize (dfa_states_len build_dfa). omega.
  Qed.

  Lemma vdfa_at_least_one : 0 < vdfa_num_states build_vdfa.
  Proof. 
    unfold build_vdfa, dfa_to_vdfa. simpl. apply dfa_at_least_one.
  Qed.
  
End DFA.

Extraction Implicit entry_t [r rownum ss].
Extraction Implicit entries_t [r i ss].
Extraction Implicit ventries_t [r i ss].
Extraction Implicit transition_t [r ss].
Extraction Implicit vtransition_t [r ss].
Extraction Implicit transitions_t [r ss].
Extraction Implicit vtransitions_t [r ss].
Extraction Implicit DFA [r].
Extraction Implicit vDFA [r].

Extraction Implicit cardinal_wfs [r].
Extraction Implicit wpdrv_wf [r].
Extraction Implicit add_wfs [r].
Extraction Implicit get_index_wfs [r].
Extraction Implicit get_index_wfs2 [r].
Extraction Implicit get_element_wfs [r].
Extraction Implicit get_element_wfs2 [r].
Extraction Implicit get_state [r].
Extraction Implicit gen_backward_xform [r ss].
Extraction Implicit gen_row' [r gpos].
Extraction Implicit gen_row [r gpos].

Extraction Implicit coerce_entry [r n ss ss'].
Extraction Implicit coerce_nils [r ss ss' i].
Extraction Implicit coerce_transitions [r].
Extraction Implicit cons_transition [r].
Extraction Implicit build_table_func [r].
Extraction Implicit build_table [r].
Extraction Implicit transition_to_vtransition [r].
Extraction Implicit dfa_to_vdfa [r].

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


(** * Splitting a [grammar] into a [regexp] and a top-level fix-up function *)

Definition fixfn (r:regexp) (t:type) := 
  xt_interp (regexp_type r) -> interp t.

Definition re_and_fn (t:type) (r:regexp) (f:fixfn r t): {r:regexp & fixfn r t } :=
  existT (fun r => fixfn r t) r f.
Extraction Implicit re_and_fn [t].

(** Split a [grammar] into a simplified [regexp] (with no maps) and a top-level fix-up
    function that can turn the results of the [regexp] back into the user-specified 
    values.  Notice that the resulting regexp has no [gMap] or [gXform] inside of it. *)
Fixpoint split_grammar t (g:grammar t) : { ag : regexp & fixfn ag t} := 
  match g in grammar t' return { ag : regexp & fixfn ag t'} with
    | Eps => @re_and_fn Unit_t rEps (fun x => x)
    | Zero t => @re_and_fn _ rZero (fun x => match x with end)
    | Char c => @re_and_fn Char_t (rChar c) (fun x => x)
    | Any => @re_and_fn Char_t rAny (fun x => x)
    | Cat t1 t2 g1 g2 => 
      let (ag1, f1) := split_grammar g1 in 
        let (ag2, f2) := split_grammar g2 in 
          @re_and_fn _ (rCat ag1 ag2) 
          (fun p => (f1 (fst p), f2 (snd p)) : interp (Pair_t t1 t2))
    | Alt t1 t2 g1 g2 => 
      let (ag1, f1) := split_grammar g1 in 
        let (ag2, f2) := split_grammar g2 in 
          @re_and_fn _ (rAlt ag1 ag2)
          (fun s => match s with 
                      | inl x => inl _ (f1 x)
                      | inr y => inr _ (f2 y)
                    end : interp (Sum_t t1 t2))
    | Star t g => 
      let (ag, f) := split_grammar g in 
        @re_and_fn _ (rStar ag) (fun xs => (List.map f xs) : interp (List_t t))
    | Map t1 t2 f1 g => 
      let (ag, f2) := split_grammar g in 
        @re_and_fn _ ag (fun x => f1 (f2 x))
    (* | Xform t1 t2 f g =>  *)
    (*   let (ag, f2) := split_grammar g in  *)
    (*     @re_and_fn _ ag (fun x => (xinterp f) (f2 x)) *)
  end.
Extraction Implicit split_grammar [t].

Definition par2rec t (g:grammar t) : regexp := 
  let (ag, _) := split_grammar g in ag.
Extraction Implicit par2rec [t].

Local Ltac break_split_grammar := 
  repeat 
    match goal with
      | [ H : match split_grammar ?g with | existT _ _ => _ end |- _ ] =>  
        let p := fresh "p" in
        remember (split_grammar g) as p ; destruct p ; simpl in *
    end. 

Lemma split_grammar_corr1 t (g:grammar t) : 
  let (r,f) := split_grammar g in 
    forall s v, in_regexp r s v -> in_grammar g s (f v).
Proof.
  induction g ; simpl ; repeat in_regexp_inv; break_split_grammar; intros;
   dependent induction H ; subst ; simpl ; eauto. 
Qed.

(** Correctness of [split_grammar] part 2:  This direction requires a quantifier 
    so is a little harder. *)
Lemma split_grammar_corr2 t (g:grammar t) : 
  let (r, f) := split_grammar g in 
    forall s v, in_grammar g s v -> exists v', in_regexp r s v' /\ v = f v'.
Proof.
  induction g; simpl ; repeat in_grammar_inv ; repeat in_regexp_inv;
  break_split_grammar; intros.
  Case "Cat".
    repeat in_grammar_inv. crush_hyp.
  Case "Alt".
    in_grammar_inv. intros. crush_hyp.
  Case "Star".
    dependent induction H. 
    SCase "InStar_eps". crush.
    SCase "InStar_cons". 
      use_lemma IHg by eassumption.
      destruct H2 as [v' [H2 H4]].
      clear IHin_grammar1. 
      specialize (IHin_grammar2 _ g f Heqp IHg v2 (eq_refl _)
                    (JMeq_refl _) (JMeq_refl _)). 
      destruct IHin_grammar2 as [v'' [H6 H8]].
      exists (v'::v''). crush.
  Case "Map". in_grammar_inv. intros. crush_hyp.
  (* Case "Xform". in_grammar_inv. intros. crush_hyp. *)
Qed.



(** * An naive, online derivative parser.

   This parser is not really used, but only for speed comparison. *)


Definition coerce_rx (t1 t2:xtype) (H:t1=t2) (f:rs_xf_pair t1) : rs_xf_pair t2.
   rewrite <- H. trivial.
Defined.

Definition coerce_dom (t1 t2:xtype) (H:t1=t2) (B:Type) (f:xt_interp t1->B) : 
  xt_interp t2 -> B.
   rewrite <- H. trivial.
Defined.

Section NAIVE_PARSE.

  (** Naive parser: split out the user-defined functions using [split_grammar], 
    then calculate the derivative with respect to the string, then call
    [astgram_extract_nil] to get a list of ASTs, then apply the the final
    transform [xfinal] to map them back to values of the type of the original
    [astgram], and then apply the split out user-level function to get back a 
    list of [t] results. *)
  Definition naive_parse t (g:grammar t) (cs : list char_p) : list (interp t) :=
  let (r, fuser) := split_grammar g in 
  let (rs, f) := wpdrv cs (RES.singleton_xform r) in
    flat_map (compose (List.map fuser) (xinterp f)) 
             (RES.re_set_extract_nil rs).

  Lemma naive_parse_corr1 : forall t (g:grammar t) cs v, in_grammar g cs v -> 
                                                       In v (naive_parse g cs).
  Proof.
    intros. unfold naive_parse. 
    generalize (split_grammar_corr2 g). intros.
    remember_head as sg. destruct sg as [r fuser]. 
    specialize (H0 _ _ H). destruct H0 as [v1 [H2 H4]].
    subst.
    remember_head as wr. destruct wr as [rs f].
    apply RES.singleton_xform_corr in H2.
    rewrite <- (app_nil_r cs) in H2.
    apply wpdrv_corr in H2.
    rewrite Hwr in H2.
    apply in_re_set_xform_elim2 in H2.
    destruct H2 as [v2 [H6 H8]].
    apply in_flat_map. 
    exists v2. rewrite <- RES.re_set_extract_nil_corr.
    split. trivial.
    unfold compose. auto using in_map.
  Qed.

  Lemma naive_parse_corr2 : forall t (g:grammar t) cs v, In v (naive_parse g cs) -> 
                                                 in_grammar g cs v.
  Proof.
    unfold naive_parse. intros. 
    generalize (split_grammar_corr1 g). intro H0.
    remember_head in H as sg. destruct sg as [r fuser].
    remember_head in H as wr. destruct wr as [rs f].
    apply in_flat_map in H.
    destruct H as [v1 [H2 H4]].
    unfold compose in H4.
    apply Coqlib.list_in_map_inv in H4.
    destruct H4 as [v2 [H6 H8]].
    assert (H10:in_re_set_xform (existT _ rs f) nil v2).
      eapply in_re_set_xform_intro2.
      apply RES.re_set_extract_nil_corr in H2. eassumption.
      assumption.
    rewrite <- Hwr in H10.
    apply wpdrv_corr in H10.
    rewrite app_nil_r in H10.
    rewrite RES.singleton_xform_corr in H10.
    crush.
  Qed.

  Record naiveParserState (t1:xtype) (t2:type) := mkNPS { 
    rx_nps : rs_xf_pair t1; (* a reset and a transform back to type t1 *)
    fixup_nps : xt_interp t1 -> interp t2 (* the top fixup function *)
  }.

  Definition naive_parse_token t1 t2 (nps:naiveParserState t1 t2) (tk:token_id) 
    : naiveParserState t1 t2 * list (interp t2) :=
    let (rs,f) := wpdrv (token_id_to_chars tk) (rx_nps nps) in 
    let v := RES.re_set_extract_nil rs in
    (@mkNPS _ _ (existT _ rs f) (fixup_nps nps),
     flat_map (compose (List.map (fixup_nps nps)) (xinterp f)) v).

  (** The semantics of naive parser states *)
  Definition in_nps t1 t2 (nps:naiveParserState t1 t2) (str:list char_t) (v: interp t2) :=
    exists v', in_re_set_xform (rx_nps nps) str v' /\
               v = fixup_nps nps v'.

  Opaque token_id_to_chars.
  Lemma naive_parse_token_corr t r (nps1:naiveParserState t r) tk nps2 vs2:
    naive_parse_token nps1 tk = (nps2, vs2) ->
    (forall v, In v vs2 <-> in_nps nps2 nil v) /\
    forall str v, in_nps nps1 ((token_id_to_chars tk) ++ str) v <->
                  in_nps nps2 str v.
  Proof. intro H. unfold naive_parse_token in H.
    remember_head in H as wp. destruct wp as [rs f].
    split. intros.
    Case "In v vs2 <-> in_nps nps2 nil v".
      inversion_clear H. unfold in_nps. simpl.
      rewrite in_flat_map. unfold compose. 
      split; intros.
      SCase "->".
        destruct H as [v1 [H2 H4]].
        rewrite <- RES.re_set_extract_nil_corr in H2.
        apply Coqlib.list_in_map_inv in H4.
        destruct H4 as [v2 [H6 H8]].
        exists v2. crush.
      SCase "<-".
        destruct H as [v1 [H2 H4]].
        destruct H2 as [v2 [H6 H8]].
        exists v2.
        split. apply RES.re_set_extract_nil_corr. trivial.
          subst. apply in_map. trivial.
    Case "in_nps ... <-> in_nps ...".
      intros. inversion_clear H. unfold in_nps. simpl.
      split; intros.
      SCase "->".
        destruct H as [v1 [H2 H4]].
        apply wpdrv_corr in H2.
        rewrite Hwp in H2.
        apply in_re_set_xform_elim2 in H2.
        destruct H2 as [v2 [H6 H8]].
        crush.
      SCase "<-".
        destruct H as [v1 [[v2 [H2 H4]] H6]].
        exists v1.
        split; [idtac | trivial].
        apply wpdrv_corr. rewrite Hwp.
        eapply in_re_set_xform_intro2; crush.
  Qed.

  Lemma inps_help1 t (g:grammar t) r f:
    split_grammar g = existT _ r f ->
    regexp_type r = regexp_type (projT1 (split_grammar g)).
  Proof. crush. Qed.


  Definition initial_naive_parser_state t (g:grammar t) : 
    naiveParserState (regexp_type (projT1 (split_grammar g))) t.
    refine (match split_grammar g as sr return split_grammar g = sr -> _ with
              | existT r f => fun Hsr =>
                 @mkNPS _ _ (coerce_rx (inps_help1 g Hsr) (RES.singleton_xform r))
                        (coerce_dom (inps_help1 g Hsr) f)
            end eq_refl).
  Defined.

End NAIVE_PARSE.

Extraction Implicit naive_parse [t].
Extraction Implicit naiveParserState [t1 t2].
Extraction Implicit naive_parse_token [t1 t2].
Extraction Implicit initial_naive_parser_state [t].

(** * A table-based parser. 

  Given a grammar, it splits the grammar into a regexp and a fixup function.
  Then it builds a DFA using the regexp. Then a first-parse parser is built
  by using the DFA.
*)

Notation "s .[ i ] " := (get_state i s) (at level 40).

Section DFA_PARSE.

  Opaque build_dfa.

  Definition re_set_fixfn (rs:RESet.t) (t:type) := 
    xt_interp (RES.re_set_type rs) -> interp (List_t t).

  (** Our real parser wants to be incremental, where we feed it one
      token at a time.  So an [instParserState] encapsulates the intermediate
      state of the parse engine, including the [DFA] and the current 
      state ([row_ps]) as well as the current fix-up function to transform
      us from the current state's type back to the original grammar type [t]. 
      We also need a proof that the current [row_ps] is in bounds for the
      number of states in the [dfa_ps] to avoid a run-time error. *)
  Record instParserState (t:type) (r:regexp) := mkPS { 
    dfa_ps : DFA r; 
    dfa_wf : wf_dfa dfa_ps ;
    row_ps : nat ; 
    row_ps_lt : row_ps < dfa_num_states (dfa_ps) ;
    fixup_ps : re_set_fixfn ((dfa_states dfa_ps).[row_ps]) t
  }.

  (** Build the initial [instParserState].  The initial fix-up function is
      obtained by taking the grammar and splitting it into an [regexp] and
      a fix-up function.  We then generate the [DFA] from this [regexp].
      Finally, we start off in the initial state of the [DFA], which is
      0. *)

  Definition coerce_dfa r1 r2: r1 = r2 -> DFA r1 -> DFA r2.
    intros. rewrite <- H. trivial.
  Defined.

  Lemma ips_help1 t (g:grammar t) r r2 (H:r=r2):
    dfa_states (coerce_dfa H (build_dfa r)).[0] = projT1 (RES.singleton_xform r2).
  Proof. rewrite RES.singleton_xform_erase.
    rewrite H. simpl.
    generalize (@build_dfa_prop r2). unfold wf_dfa. intros; sim.
    auto.
  Qed.

  Lemma ips_help2 t (g:grammar t) r r2 (H:r=r2):
    RES.re_set_type (projT1 (RES.singleton_xform r)) =
    RES.re_set_type (dfa_states (coerce_dfa H (build_dfa r)).[0]).
  Proof. f_equal. rewrite (ips_help1 g). rewrite H. trivial. Qed.

  Lemma ips_help3 t (g:grammar t) r r2 (H:r=r2):
    wf_dfa (coerce_dfa H (build_dfa r)).
  Proof. rewrite H. simpl. apply build_dfa_prop. Qed.

  Lemma ips_help4 t (g:grammar t) r r2 (H:r=r2):
    0 < dfa_num_states (coerce_dfa H (build_dfa r)).
  Proof. rewrite H. simpl. apply dfa_at_least_one. Qed.

  Lemma ips_help5 t (g:grammar t) r f:
    split_grammar g = existT _ r f -> r = projT1 (split_grammar g).
  Proof. crush. Qed.

  Definition initial_parser_state t (g:grammar t) :
    instParserState t (projT1 (split_grammar g)).
    refine (
      match split_grammar g as sr return split_grammar g = sr -> _ with
        | existT r f => fun Hsr =>
          match build_dfa r with
            | d => 
                let f1 := projT2 (RES.singleton_xform r) in
                let H := (ips_help5 g Hsr) in
                @mkPS _ _ (coerce_dfa H d) _ 0 _
                   (coerce_dom (ips_help2 g H)
                     (compose (map f) (xinterp f1)))
          end
      end eq_refl).
    apply (ips_help3 g).
    apply (ips_help4 g).
  Defined.

  (** Given an [instParserState] and a token, advance the parser.  We first
      lookup the transition row of the current state ([row_ps ps]), and then
      extract the entry in that row corresponding to the token [tk].  These
      lookups will never fail (and some of the lemmas below are used to show
      this.)  

      We then compute the updated fixup-function by composing the current
      parsing state's [fixup_ps] with the [next_i] entry's [next_xform].
      We must do various type-casts to get these things to line up.  

      Finally, we grab [next_i]'s [row_nils] which correspond to the semantic
      values that state [next_i] associates with the empty string and apply
      the newly-composed fixup-function to each of these values.  We then
      return the list of these semantic values and a new parser state, 
      where [next_i] becomes the current row.  Note that if there is no 
      semantic value associated with [next_i], then we will get an empty
      list of semantic values, so one should continue parsing tokens using
      the new [instParserState]. 

      TODO:  we should have some way of signaling that we are in a failure
      (i.e., Zero) state.  Otherwise, a parsing loop will just consume all
      of the tokens before realizing that there is never a match.
  *)

  (** Various lemmas needed to help discharge proof obligations in [parse_token.] *)
  Definition parse_token_help1 (t:type) r (ps: instParserState t r)
             (row: transition_t (dfa_states (dfa_ps ps)))
             (H: nth_error (dfa_transition (dfa_ps ps)) (row_ps ps) = Some row) :
    RES.re_set_type  (dfa_states (dfa_ps ps).[row_ps ps]) =
    RES.re_set_type (dfa_states (dfa_ps ps).[row_num row]).
  Proof.
    intros ; generalize (dfa_transition_r (dfa_ps ps) (row_ps ps)). 
    rewrite H. intro g ;
    rewrite <- g. apply eq_refl.
  Defined.

  Lemma parse_token_help2 t r (ps:instParserState t r) 
        (row:transition_t (dfa_states (dfa_ps ps)))
        (H: nth_error (dfa_transition (dfa_ps ps)) (row_ps ps) = Some row)
        (e:entry_t (row_num row) (dfa_states (dfa_ps ps))) :
    next_state e < dfa_num_states (dfa_ps ps).
  Proof.
    intros. rewrite <- (dfa_states_len (dfa_ps ps)).
    destruct ps. simpl in *. destruct dfa_ps0 ; simpl in *. destruct e.
    simpl in *. subst. auto.
  Defined.

  (* Definition lt_and_gte_inconst (x y:nat) : x < y -> x >= y -> void. *)
  (*   intros. omega. *)
  (* Defined. *)
    
  Definition parse_token_help3 t r (ps:instParserState t r) (tk:token_id)
             (tk_lt:tk < num_tokens)
             (row:transition_t (dfa_states (dfa_ps ps)))
             (H:nth_error (dfa_transition (dfa_ps ps)) (row_ps ps) = Some row)
             (H':nth_error (row_entries row) tk = None) : void.
  Proof. intros. generalize (Coqlib.nth_error_none _ _ H').
    generalize (dfa_wf ps). unfold wf_dfa, wf_table, build_table_inv.
    intro H2. destruct H2 as [[H3 [H4 H5]] H6].
    assert (H10:row_ps ps < List.length (dfa_transition (dfa_ps ps))).
      eapply Coqlib.nth_error_some_lt. eassumption.
    specialize (H5 (row_ps ps) H10).
    rewrite H in H5.
    crush.
  Defined.

  Definition parse_token_help4 t r (ps:instParserState t r)
             (H:nth_error (dfa_transition (dfa_ps ps)) (row_ps ps) = None) : void.
  Proof.
    intros. generalize (Coqlib.nth_error_none _ _ H). generalize (row_ps_lt ps).
    intros. generalize (dfa_transition_len (dfa_ps ps)). intros.
    rewrite H2 in H1. omega.
  Defined.

  Lemma parse_token_help5 r (d: DFA r) (row : transition_t (dfa_states d))
        (e : entry_t (row_num row) (dfa_states d))
        (row' : transition_t (dfa_states d))
        (H3 : nth_error (dfa_transition d) (next_state e) = Some row') :
    row_num row' = next_state e.
  Proof.
    intros. generalize (dfa_transition_r d (next_state e)). rewrite H3.
    auto.
  Qed.

  Lemma parse_token_help6 r (d:DFA r) (row : transition_t (dfa_states d))
        (e : entry_t (row_num row) (dfa_states d))
        (row' : transition_t (dfa_states d))
        (H3 : nth_error (dfa_transition d) (next_state e) = Some row') :
    list (xt_interp (RES.re_set_type (dfa_states d.[row_num row']))) =
    list (xt_interp (RES.re_set_type (dfa_states d.[next_state e]))).
  Proof.
    intros. rewrite (parse_token_help5 d row e H3). auto.
  Qed.

  Definition coerce (A B:Type) (H:A=B) : A -> B := 
    match H in (_ = C) return A -> C with 
      | eq_refl => fun x => x
    end.

  Definition nth_error2 A (l:list A) (n:nat):
    {e:A | nth_error l n = Some e} + {nth_error l n = None}.
    refine (let ne := nth_error l n in
            (match ne return nth_error l n = ne -> _ with
               | Some e => 
                 fun H => inleft (exist _ e H)
               | None => fun H => inright H
             end) eq_refl).
  Defined.

  Definition parse_token t r (ps:instParserState t r) (tk:token_id) 
              (tk_lt:tk < num_tokens) : instParserState t r * list (interp t).
    refine(
      match nth_error2 (dfa_transition (dfa_ps ps)) (row_ps ps) with
        | inright Hnd => match parse_token_help4 ps Hnd with end (*impossible*)
        | inleft (exist row Hnd) =>
          match nth_error2 (row_entries row) tk with 
            | inright Hnr =>
              match parse_token_help3 ps tk_lt Hnd Hnr with end (*impossible*)
            | inleft (exist e Hnr) => 
              let next_i := next_state e in 
              let next_fixup := coerce_dom (parse_token_help1 ps Hnd) (fixup_ps ps) in
              let g:= compose (flat_map next_fixup)
                        ((*xinterp*) (next_xform e)) in
              let vs0 : list (xt_interp 
                                (RES.re_set_type 
                                   (dfa_states (dfa_ps ps).[next_state e]))) :=
                  match nth_error2 (dfa_transition (dfa_ps ps)) next_i with
                    | inright H => nil (* impossible but not worth proving? *)
                    | inleft (exist row' H) =>
                      @coerce _ _ (parse_token_help6 (dfa_ps ps) row e H)
                              (row_nils row')
                  end in
              let vs' := flat_map g vs0 in
                (@mkPS t r (dfa_ps ps) (dfa_wf ps)
                      next_i (parse_token_help2 ps Hnd e) g, vs')
          end
      end).
  Defined.

  Fixpoint list_all A (P : A -> Prop) (xs:list A) : Prop := 
    match xs with 
      | nil => True
      | h::t => P h /\ list_all P t
    end.

  (* todo: an optimization would be to reuse the row_nils stored in dfa_ps,
     instead of doing re_set_extract_nil again *)
  Definition ps_extract_nil t r (ps:instParserState t r) :=
    flat_map (fixup_ps ps)
             (RES.re_set_extract_nil (dfa_states (dfa_ps ps).[row_ps ps])).

  (** A first-parse parser -- this consumes the tokens until it gets a successful
      semantic value. *)
  Fixpoint parse_tokens t r (ps:instParserState t r) (tks:list token_id) := 
    match tks return list_all (fun tk => tk < num_tokens) tks -> 
                     (list token_id) * (instParserState t r) * list (interp t) 
    with 
      | nil => fun _ => (nil, ps, ps_extract_nil ps)
      | tk::rest => 
        fun H => 
          match H with 
            | conj H1 H2 => 
              let pair := parse_token ps H1 in 
              match snd pair with
                | nil => parse_tokens (fst pair) rest H2
                | vs => (rest, (fst pair), vs)
              end
          end
    end.

  (** The semantics of parser states *)
  Definition in_ps t r (ps:instParserState t r) (str:list char_t) (v: interp t) :=
    exists v', in_re_set (dfa_states (dfa_ps ps).[row_ps ps]) str v' /\
               In v ((fixup_ps ps) v').

  Opaque RES.re_set_type.
  Lemma initial_parser_state_corr t (g:grammar t) str v:
    in_ps (initial_parser_state g) str v <-> in_grammar g str v.
  Proof. unfold initial_parser_state.
    generalize (ips_help3 g) (ips_help4 g) (ips_help5 g).
    generalize (ips_help2 g).
    remember_rev (split_grammar g) as sr.
    destruct sr as [r f]. 
    intros.
    rewrite (proof_irrelevance _ (e0 r f eq_refl) eq_refl). simpl.
    assert (H2:projT1 (RES.singleton_xform r) =
               dfa_states (build_dfa r).[0]).
      generalize (build_dfa_prop r). unfold wf_dfa. crush.
    remember_rev (projT2 (RES.singleton_xform r)) as f1.
    simpl in f1.
    generalize (e r r eq_refl).
    simpl. unfold in_ps. simpl.
    rewrite <- H2. intros.
    rewrite (proof_irrelevance _ e1 eq_refl). simpl.
    unfold in_ps; simpl; split; intros.
    Case "->".
      generalize (split_grammar_corr1 g). rewrite Hsr. intros.
      destruct H as [v' [H4 H6]].
      unfold compose in H6.
      apply Coqlib.list_in_map_inv in H6.
      destruct H6 as [v1 [H6 H8]].
      subst. apply H0.
      apply RES.singleton_xform_corr.
      eapply in_re_set_xform_intro; eassumption. 
    Case "<-".
      generalize (split_grammar_corr2 g). rewrite Hsr. intros.
      use_lemma H0 by eassumption.
      destruct H1 as [v' [H4 H6]].
      apply RES.singleton_xform_corr in H4.
      apply in_re_set_xform_elim in H4.
      destruct H4 as [v1 [H8 H10]].
      exists v1. 
      split; [assumption | idtac].
      subst. unfold compose.
      apply in_map. assumption.
  Qed.

  Local Ltac match_emp_contra := 
    intros;
    match goal with
      | [H: match ?P with end = _ |- _] => destruct P
    end.

  Opaque token_id_to_chars in_re_set_xform.
  Lemma parse_token_corr t r (ps1:instParserState t r) tk 
        (H:tk<num_tokens) ps2 vs2:
    parse_token ps1 H = (ps2, vs2) ->
    (forall v, In v vs2 <-> in_ps ps2 nil v) /\
    forall str v, in_ps ps1 ((token_id_to_chars tk) ++ str) v <->
                  in_ps ps2 str v.
  Proof. generalize (dfa_wf ps1). unfold wf_dfa. intro H0.
    destruct H0 as [H0 [H1 _]].
    assert (H2:row_ps ps1 < List.length (dfa_transition (dfa_ps ps1))).
      rewrite (dfa_transition_len (dfa_ps ps1)).
      apply (row_ps_lt ps1).
    unfold parse_token.
    destruct (nth_error2 (dfa_transition (dfa_ps ps1)) (row_ps ps1));
           [idtac | match_emp_contra].
    destruct s as [row Hnd].
    destruct (nth_error2 (row_entries row) tk); [idtac | match_emp_contra].
    destruct s as [entries Hne].
    unfold wf_table, build_table_inv in H0.
    destruct H0 as [_ [_ H3]].
    generalize (H3 (row_ps ps1) H2). intro H14.
    rewrite Hnd in H14.
    assert (H4:row_ps ps1 = row_num row) by crush.
    destruct H14 as [H14 [H16 [H18 _]]].
    specialize (H18 tk). unfold wf_entries in H18. simpl in H18.
    rewrite Hne in H18.
    destruct (nth_error2 (dfa_transition (dfa_ps ps1)) (next_state entries)).
    Case "Some e".
      destruct s as [row' H6].
      intros. inversion_clear H0.
      unfold in_ps. simpl.
      generalize (parse_token_help1 ps1 Hnd), (fixup_ps ps1).
      rewrite H4. intros.
      rewrite (proof_irrelevance _ e eq_refl). simpl.
      unfold compose.
      split.
      SCase "In v vs <-> in_ps ps2 nil v".
        assert (H8:next_state entries < List.length (dfa_transition (dfa_ps ps1))).
          rewrite (dfa_transition_len (dfa_ps ps1)).
          rewrite <- (dfa_states_len (dfa_ps ps1)).
          apply (next_state_lt entries).
        generalize (H3 (next_state entries) H8). intro H9.
        rewrite H6 in H9.
        destruct H9 as [H9 [H10 [H11 H12]]].
        generalize H12.
        generalize (parse_token_help6 (dfa_ps ps1) row entries H6).
        generalize (row_nils row').
        rewrite H10.
        intros.
        rewrite (proof_irrelevance _ e0 eq_refl). simpl.
        rewrite in_flat_map.
        split; intro H20.
        SSCase "->".
          destruct H20 as [v' H20].
          exists v'. 
          split. apply RES.re_set_extract_nil_corr. crush.
            crush.
        SSCase "<-".
          destruct H20 as [v' [H20 H22]].
          apply RES.re_set_extract_nil_corr in H20.
          exists v'. crush.
      SCase "forall str v, ... <-> ...".
      split; intro H10.
        SSCase "->".
          destruct H10 as [v' [H10 H12]].
          rewrite H18 in H10.
          destruct H10 as [v1 [H20 H22]].
          exists v1.
          split. assumption.
            apply in_flat_map. crush.
        SSCase "<-".
          destruct H10 as [v' [H10 H12]].
          apply in_flat_map in H12.
          destruct H12 as [l [H12 H24]].
          assert (H30:in_re_set_interp_xform (dfa_states (dfa_ps ps1).[next_state entries])
                                             (next_xform entries) str l).
          econstructor ; eauto. 
          apply H18 in H30.
          exists l. crush.
    Case "None".
      use_lemma Coqlib.nth_error_none by eassumption.
      generalize (next_state_lt entries), (dfa_states_len (dfa_ps ps1)).
      generalize (dfa_transition_len (dfa_ps ps1)).
      intros.
      contradict H5. omega.
  Qed.  

  Lemma ps_extract_nil_corr t r (ps:instParserState t r):
    forall v, In v (ps_extract_nil ps) <-> in_ps ps nil v.
  Proof. fold interp. intros. unfold ps_extract_nil, in_ps.
    rewrite in_flat_map.
    split; intros.
    Case "->". destruct H as [v' H].
      rewrite <- RES.re_set_extract_nil_corr in H.
      crush.
    Case "<-". destruct H as [v' H].
      rewrite RES.re_set_extract_nil_corr in H.
      crush.
  Qed.

  Lemma parse_tokens_corr t r: forall ts1 (ps1:instParserState t r)
        (Hts1:list_all (fun tk => tk < num_tokens) ts1) ts2 ps2 vs2,
    parse_tokens ps1 ts1 Hts1 = (ts2, ps2, vs2) ->
    (forall v, In v vs2 <-> in_ps ps2 nil v) /\
    (exists ts', ts1 = ts' ++ ts2 /\
     forall str v, in_ps ps1 ((flat_map token_id_to_chars ts') ++ str) v <->
                   in_ps ps2 str v).
  Proof. induction ts1 as [ | tk ts1]; intros.
    Case "nil". simpl in H. inversion_clear H.
      split. apply ps_extract_nil_corr. 
        exists nil; crush.
    Case "tk::ts1".
      simpl in Hts1. destruct Hts1 as [Htk Hts1].
      simpl in H.
      remember_rev (fst (parse_token ps1 Htk)) as ps1'.
      remember_rev (snd (parse_token ps1 Htk)) as vs1'.
      assert (H2: parse_token ps1 Htk = (ps1', vs1')).
        apply injective_projections; trivial.
      generalize (parse_token_corr ps1 Htk H2). 
      destruct_head in H.
      SCase "vs1'=nil".
        apply IHts1 in H.
        destruct H as [H4 [ts1' [H6 H8]]].
        split; [crush | idtac].
        exists (tk::ts1'). 
        split. crush.
        intros. rewrite <- H8.
          simpl. rewrite app_assoc_reverse. crush.
      SCase "vs1'<>nil".
        inversion H. subst.
        inversion_clear H.
        split. crush.
        exists (tk::nil). 
        split. crush.
          intros. simpl. rewrite app_assoc_reverse. crush.
  Qed.

  (** Proof that if you build an initial parsing state from a grammar [g],
      and then run [parse_tokens] on a list of tokens [tks], you'll get back
      (a) some suffix of [tks], corresponding to the unconsumed tokens, 
      (b) a list of semantic values [vs], such that for each [v] in [vs],
      and a guarantee that [v] is is related by [g] and the consumed tokens. *)
  Lemma parse_tokens_initial_ps : 
    forall t (g:grammar t) ps0, 
      initial_parser_state g = ps0 -> 
      forall ts0 (H:list_all (fun tk => tk < num_tokens) ts0),
        match parse_tokens ps0 ts0 H with 
            | (ts2, ps2, vs) => 
              exists ts1, ts0 = ts1 ++ ts2 /\ 
                forall v, In v vs -> in_grammar g (flat_map token_id_to_chars ts1) v
        end.
  Proof. intros.
    remember_head as pt. destruct pt as [[ts2 ps2] vs].
    generalize (parse_tokens_corr _ _ H0 Hpt). intro H2.
    destruct H2 as [H2 [ts1 [H4 H6]]].
    exists ts1. 
    split. trivial.
    intros.
    apply initial_parser_state_corr. rewrite H.
    rewrite <- (app_nil_r (flat_map token_id_to_chars ts1)).
    apply H6. apply H2. trivial.
  Qed.

End DFA_PARSE.

Section VDFA_PARSE.
  Opaque build_dfa.

  Record vinstParserState (t:type) (r:regexp) := mkvPS {
    vdfa_ps : vDFA r ; 
    vdfa_wf : wf_vdfa vdfa_ps ; 
    vrow_ps : nat ; 
    vrow_ps_lt : vrow_ps < Vector.length (vdfa_transition vdfa_ps) ; 
    vfixup_ps : re_set_fixfn ((vdfa_states vdfa_ps).[vrow_ps]) t
  }.

  Definition coerce_vdfa r1 r2 : r1 = r2 -> vDFA r1 -> vDFA r2.
    intros. rewrite <- H. trivial.
  Defined.

  Lemma vips_help1 t (g:grammar t) r r2 (H:r=r2):
    vdfa_states (coerce_vdfa H (build_vdfa r)).[0] = projT1 (RES.singleton_xform r2).
  Proof. rewrite RES.singleton_xform_erase.
    rewrite H. simpl.
    generalize (@build_vdfa_prop r2). unfold wf_vdfa. intros; sim.
    auto.
  Qed.
  
  Definition vips_help2 t (g:grammar t) r r2 (H:r=r2):
    RES.re_set_type (projT1 (RES.singleton_xform r)) =
    RES.re_set_type (vdfa_states (coerce_vdfa H (build_vdfa r)).[0]).
  Proof. f_equal. rewrite (vips_help1 g). rewrite H. trivial. Qed.

  Lemma vips_help3 t (g:grammar t) r r2 (H:r=r2):
    wf_vdfa (coerce_vdfa H (build_vdfa r)).
  Proof. rewrite H. simpl. apply build_vdfa_prop. Qed.

  Lemma vips_help4 t (g:grammar t) r r2 (H:r=r2):
    0 < Vector.length (vdfa_transition (coerce_vdfa H (build_vdfa r))).
  Proof. rewrite H. 
         generalize (vdfa_transition_len (build_vdfa r2)).
         simpl. intros. rewrite H0. apply vdfa_at_least_one. 
  Qed.

  Definition vinitial_parser_state t (g:grammar t) : 
    vinstParserState t (projT1 (split_grammar g)).
    refine (
      match split_grammar g as sr return split_grammar g = sr -> _ with
        | existT r f => fun Hsr => 
          match build_vdfa r with 
            | d =>
              let f1 := projT2 (RES.singleton_xform r) in 
              let H := ips_help5 g Hsr in 
              @mkvPS _ _ (coerce_vdfa H d) _ 0 _ 
                     (coerce_dom (vips_help2 g H)
                                 (compose (map f) (xinterp f1)))
          end
      end eq_refl).
    apply (vips_help3 g).
    apply (vips_help4 g).
  Defined.

  Lemma wf_vdfa_imp_tk_lt {r} {d:vDFA r} : 
    wf_vdfa d -> 
    forall i (H: i < Vector.length (vdfa_transition d)) tk, 
      tk < num_tokens -> 
      tk < Vector.length (vrow_entries (Vector.get (vdfa_transition d) i H)).
  Proof.
    unfold wf_vdfa. intros [H1 [H2 H3]]. destruct H1 as [H4 [H5 H6]].
    intros. specialize (H6 i H). 
    remember (Vector.get (vdfa_transition d) i H) as e.
    simpl in H6. destruct H6 as [H7 _]. rewrite H7. auto.
  Qed.    
    
  Lemma vparse_token_help1 {t r} (ps : vinstParserState t r) 
        (row : vtransition_t (vdfa_states (vdfa_ps ps))) : 
        (Vector.get (vdfa_transition (vdfa_ps ps)) (vrow_ps ps) (vrow_ps_lt ps) 
         = row) ->
        RES.re_set_type (vdfa_states (vdfa_ps ps).[vrow_ps ps]) = 
        RES.re_set_type (vdfa_states (vdfa_ps ps).[vrow_num row]).
  Proof.
    intro H. rewrite <- H.
    rewrite (vdfa_transition_r (vdfa_ps ps) (vrow_ps_lt ps)). auto.
  Defined.

  Lemma vparse_token_help2 {t r} (ps: vinstParserState t r)
        (row:vtransition_t (vdfa_states (vdfa_ps ps)))
        (H: Vector.get (vdfa_transition (vdfa_ps ps)) (vrow_ps ps)
                       (vrow_ps_lt ps) = row)
        (e: entry_t (vrow_num row) (vdfa_states (vdfa_ps ps))) : 
    next_state e < Vector.length (vdfa_transition (vdfa_ps ps)).
  Proof.
    rewrite (vdfa_transition_len (vdfa_ps ps)).
    rewrite <- (vdfa_states_len (vdfa_ps ps)).
    destruct ps. simpl in *. destruct vdfa_ps0 ; simpl in *. destruct e.
    simpl in *. subst. auto.
  Defined.

  Definition flat_map' {A B} (f: A -> list B) := 
    fix flat_map' (xs:list A) : list B := 
      match xs with 
        | nil => nil
        | x::nil => f x
        | x::t => f x ++ flat_map' t
      end.

  Lemma flat_map_simp {A B} : @flat_map' A B = @flat_map A B.
  Proof.
    eapply Coqlib.extensionality. intro f.
    eapply Coqlib.extensionality. intro xs.  
    induction xs ; crush. destruct xs ; crush.
  Qed.

  Definition compose_flat_map {A B C} (f:A->list B) (g:C->list A) : C -> list B := 
    fun x => flat_map' f (g x).

  Lemma compose_flat_map_simp {A B C} (f:A->list B) (g:C ->list A) : 
    compose_flat_map f g = compose (flat_map f) g.
  Proof.
    unfold compose_flat_map, compose. rewrite flat_map_simp. auto.
  Qed.

  Definition vparse_token {t r} (ps:vinstParserState t r) (tk:token_id) 
              (tk_lt:tk < num_tokens) : 
      { vips : vinstParserState t r & 
        list (xt_interp (RES.re_set_type (vdfa_states (vdfa_ps vips).[(vrow_ps vips)]))) }.
    refine(
        let row := Vector.get (vdfa_transition (vdfa_ps ps)) 
                              (vrow_ps ps) (vrow_ps_lt ps) in 
        let e := Vector.get (vrow_entries row)
                            tk (wf_vdfa_imp_tk_lt (vdfa_wf ps) 
                                                  (vrow_ps_lt ps) tk_lt) in
        let next_i := next_state e in 
        let next_fixup := coerce_dom (vparse_token_help1 _ eq_refl) (vfixup_ps ps) in 
        (* call a slightly optimized version of compose (flat_map ...) *)
        let g := (*compose (flat_map next_fixup) (next_xform e) in *)
                 compose_flat_map next_fixup (next_xform e) in
        let row' := Vector.get (vdfa_transition (vdfa_ps ps)) next_i (vparse_token_help2 _ eq_refl _) in
        let vs0 : list (xt_interp (RES.re_set_type 
                                     (vdfa_states (vdfa_ps ps).[next_state e])))
            := @coerce _ _ _ (vrow_nils row') in
        (* We used to return this but we avoid calling the flat_map now until the
           caller knows that the list is non-empty. *)
        (* let vs' := flat_map' g vs0 in *)
        existT _ (@mkvPS t r (vdfa_ps ps) (vdfa_wf ps) next_i (vparse_token_help2 _ eq_refl _) g) vs0
  ).
  replace (vrow_num row') with (next_state e) ; auto.
  generalize (vdfa_transition_r (vdfa_ps ps) (vparse_token_help2 ps eq_refl e)).
  replace (next_state e) with next_i ; auto.
  Defined.

  Definition vps_extract_nil {t r} (ps:vinstParserState t r) :=
    flat_map' (vfixup_ps ps)
             (RES.re_set_extract_nil (vdfa_states (vdfa_ps ps).[vrow_ps ps])).

  (** The semantics of vparser states *)
  Definition in_vps t r (ps:vinstParserState t r)(str:list char_t)(v:interp t) := 
    exists v', in_re_set (vdfa_states (vdfa_ps ps).[vrow_ps ps]) str v' /\ 
               In v ((vfixup_ps ps) v').

  Lemma vinitial_parser_state_corr t (g:grammar t) str v:
    in_vps (vinitial_parser_state g) str v <-> in_grammar g str v.
  Proof. unfold vinitial_parser_state.
    generalize (vips_help2 g) (vips_help3 g) (vips_help4 g) (ips_help5 g).
    remember_rev (split_grammar g) as sr.
    destruct sr as [r f]. 
    intros.
    rewrite (proof_irrelevance _ (e0 r f eq_refl) eq_refl). simpl.
    assert (H2:projT1 (RES.singleton_xform r) =
               dfa_states (build_dfa r).[0]).
      generalize (build_dfa_prop r). unfold wf_dfa. crush.
    remember_rev (projT2 (RES.singleton_xform r)) as f1.
    simpl in f1. 
    generalize (e r _ eq_refl).
    simpl. unfold in_vps. simpl.
    rewrite <- H2. intros.
    rewrite (proof_irrelevance _ e1 eq_refl). simpl.
    unfold in_ps; simpl; split; intros.
    Case "->".
      generalize (split_grammar_corr1 g). rewrite Hsr. intros.
      destruct H as [v' [H4 H6]].
      unfold compose in H6.
      apply Coqlib.list_in_map_inv in H6.
      destruct H6 as [v1 [H6 H8]].
      subst. apply H0.
      apply RES.singleton_xform_corr.
      eapply in_re_set_xform_intro; eassumption. 
    Case "<-".
      generalize (split_grammar_corr2 g). rewrite Hsr. intros.
      use_lemma H0 by eassumption.
      destruct H1 as [v' [H4 H6]].
      apply RES.singleton_xform_corr in H4.
      apply in_re_set_xform_elim in H4.
      destruct H4 as [v1 [H8 H10]].
      exists v1. 
      split; [assumption | idtac].
      subst. unfold compose.
      apply in_map. assumption.
  Qed.

  Opaque token_id_to_chars.

  Lemma vparse_token_corr1 t r (ps1:vinstParserState t r) tk 
        (H:tk<num_tokens) : 
    match vparse_token ps1 H with
        | existT ps2 vs2 => 
          (forall v, In v (flat_map' (vfixup_ps ps2) vs2) <-> in_vps ps2 nil v)
    end.
  Proof.
    fold interp. unfold vparse_token. unfold in_vps. simpl.
    generalize (vparse_token_help2 ps1 eq_refl
                       (Vector.get
                          (vrow_entries
                             (Vector.get (vdfa_transition (vdfa_ps ps1))
                                (vrow_ps ps1) (vrow_ps_lt ps1))) tk
                          (wf_vdfa_imp_tk_lt (vdfa_wf ps1) (vrow_ps_lt ps1) H))) as H1.
    generalize (wf_vdfa_imp_tk_lt (vdfa_wf ps1) (vrow_ps_lt ps1) H) as H2.
    generalize (vdfa_transition_r (vdfa_ps ps1) (vrow_ps_lt ps1)) as H3.
    intros.
    generalize (eq_sym (vdfa_transition_r (vdfa_ps ps1) H1)) as H4. intro.
    remember (Vector.get (vdfa_transition (vdfa_ps ps1)) (vrow_ps ps1) (vrow_ps_lt ps1))
    as row. 
    remember (Vector.get (vrow_entries row) tk H2) as entry.
    remember (Vector.get (vdfa_transition (vdfa_ps ps1)) (next_state entry) H1) as row2.
    destruct ps1 ; destruct row ; destruct entry ; simpl in *.
    destruct row2 ; simpl in *. subst. simpl.
    rewrite compose_flat_map_simp. rewrite flat_map_simp.
    remember (compose (flat_map vfixup_ps0) next_xform0) as fixup. fold interp in fixup.
    destruct vdfa_wf0 as [[H6 [H7 H9]] [H4 H5]].
    specialize (H9 _ H1). 
    rewrite <- Heqrow2 in H9. simpl in H9. destruct H9 as [H10 [H11 [H12 H13]]].
    rewrite H13.
    generalize (RES.re_set_extract_nil_corr (vdfa_states vdfa_ps0.[vrow_num1])).
    clear Heqrow2 Heqentry.
    remember (vdfa_states vdfa_ps0.[vrow_num1]) as s.
    clear Heqs. intros. rewrite in_flat_map. split ; intro H3 ; destruct H3 as [x [H3 H30]] ;
    exists x ; split ; auto. rewrite H0 ; auto. rewrite <- H0 ; auto.
  Qed.

  Lemma vparse_token_corr2 t r (ps1:vinstParserState t r) tk (H:tk < num_tokens) : 
    match vparse_token ps1 H with 
      | existT ps2 vs2 => 
        forall str v, in_vps ps1 ((token_id_to_chars tk) ++ str) v <->
                      in_vps ps2 str v
    end.
  Proof.
    unfold vparse_token. unfold in_vps. simpl.
    generalize (wf_vdfa_imp_tk_lt (vdfa_wf ps1) (vrow_ps_lt ps1) H) as H1.
    generalize (vdfa_transition_r (vdfa_ps ps1) (vrow_ps_lt ps1)).
    remember (Vector.get (vdfa_transition (vdfa_ps ps1))
                               (vrow_ps ps1) (vrow_ps_lt ps1)) as row. 
    intros.
    remember (Vector.get (vrow_entries row) tk H1) as entry.
    destruct ps1 ; destruct row ; destruct entry ; simpl in *. subst. simpl in *.
    rewrite compose_flat_map_simp.
    destruct vdfa_wf0 as [[H6 [H7 H8]] [H4 H5]].
    generalize (H8 _ vrow_ps_lt0) ; intro H9.
    rewrite <- Heqrow in H9. simpl in H9. destruct H9 as [H10 [H11 [H12 H13]]].
    specialize (H12 _ H1). unfold wf_ventry in H12.
    split ; intros [v' [H14 H15]]. 
    specialize (proj1 (H12 str v') H14). intros. destruct H0 as [x [H16 H17]].
    generalize v' H14 H15 x H16 H17 ; clear v' H14 H15 x H16 H17.
    rewrite <- Heqentry. simpl. intros. exists x. split ; auto.
    unfold compose. rewrite in_flat_map. exists v'. auto.
    unfold compose in H15. rewrite in_flat_map in H15. destruct H15.
    exists x. destruct H0. split ; auto.
    specialize (H12 str x). apply H12. unfold in_re_set_interp_xform.
    rewrite <- Heqentry. simpl. exists v' ; eauto.
  Qed.

  Lemma vparse_token_corr t r (ps1:vinstParserState t r) tk (H: tk < num_tokens) ps2 vs2 :
    vparse_token ps1 H = existT _ ps2 vs2 -> 
    ((forall v, In v (flat_map' (vfixup_ps ps2) vs2) <-> in_vps ps2 nil v) /\
     (forall str v, in_vps ps1 ((token_id_to_chars tk) ++ str) v <->
                      in_vps ps2 str v)).
  Proof.
    specialize (vparse_token_corr1 ps1 H).
    specialize (vparse_token_corr2 ps1 H). fold interp.
    remember (vparse_token ps1 H) as x. destruct x. intros. crush.
    apply H1. auto. apply H0. auto.
  Qed.

  Lemma vps_extract_nil_corr t r (ps:vinstParserState t r):
    forall v, In v (vps_extract_nil ps) <-> in_vps ps nil v.
  Proof. fold interp. intros. unfold vps_extract_nil, in_vps.
    rewrite flat_map_simp.
    rewrite in_flat_map.
    split; intros.
    Case "->". destruct H as [v' H].
      rewrite <- RES.re_set_extract_nil_corr in H.
      crush.
    Case "<-". destruct H as [v' H].
      rewrite RES.re_set_extract_nil_corr in H.
      crush.
  Qed.

  Fixpoint vparse_tokens {t r} (ps:vinstParserState t r) (tks:list token_id) := 
    match tks return list_all (fun tk => tk < num_tokens) tks -> 
                     (list token_id) * (vinstParserState t r) * list (interp t) 
    with 
      | nil => fun _ => (nil, ps, vps_extract_nil ps)
      | tk::rest => 
        fun H => 
          match H with 
            | conj H1 H2 => 
              let pair := vparse_token ps H1 in 
              let (ps2,vs) := pair in 
              match vs with
                | nil => vparse_tokens ps2 rest H2
                | vs => (rest, ps2, flat_map (vfixup_ps ps2) vs)
              end
          end
    end.

End VDFA_PARSE.

Extraction Implicit instParserState [t r].
Extraction Implicit initial_parser_state [t].
Extraction Implicit vinitial_parser_state [t].
Extraction Implicit coerce_dfa [r1 r2].
Extraction Implicit coerce_dom [t1 t2].
Extraction Implicit parse_token [t r].
Extraction Implicit ps_extract_nil [t r].
Extraction Implicit parse_tokens [t r].
Extraction Implicit dfa_show [r].
Extraction Implicit transitions_show [r ss].
Extraction Implicit transition_show [r ss].
Extraction Implicit entries_show [r ss].
Extraction Implicit entry_show [r ss].
Extraction Implicit vparse_token [t r].


(** [to_string] takes a grammar [a] and an abstract syntax value [v] of
    type [regexp_type a] and produces an optional string [s] with the property
    that [in_regexp a s v].  So effectively, it's a pretty printer for
    ASTs given a grammar.  It's only a partial function for two reasons:
    First, the type only describes the shape of the AST value [v] and not
    the characters within it.  If they don't match what's in the grammar,
    we must fail.  Second, the treatment of [aStar] in [in_regexp] demands
    that the strings consumed in the [InaStar_cons] case are non-empty.  
*)
(* Fixpoint to_string (a:regexp) : interp (regexp_type a) -> option (list char_p) := *)
(*   match a return interp (regexp_type a) -> option (list char_p) with *)
(*     | aEps => fun (v:unit) => Some nil *)
(*     | aZero => fun (v:void) => match v with end *)
(*     | aChar c1 => fun (c2:char_p) => if char_dec c1 c2 then Some (c1::nil) else None *)
(*     | aAny => fun (c:char_p) => Some (c::nil) *)
(*     | aCat a1 a2 =>  *)
(*       fun (v:(interp (regexp_type a1)) * (interp (regexp_type a2))) =>  *)
(*         match to_string a1 (fst v), to_string a2 (snd v) with  *)
(*           | Some s1, Some s2 => Some (s1 ++ s2) *)
(*           | _, _ => None *)
(*         end *)
(*     | aAlt a1 a2 =>  *)
(*       fun (v:(interp (regexp_type a1)) + (interp (regexp_type a2))) =>  *)
(*         match v with  *)
(*           | inl v1 => to_string a1 v1 *)
(*           | inr v2 => to_string a2 v2 *)
(*         end *)
(*     | aStar a1 =>  *)
(*       fun (v:list (interp (regexp_type a1))) =>  *)
(*         List.fold_right  *)
(*         (fun v1 sopt =>  *)
(*           match to_string a1 v1, sopt with *)
(*             | Some (c::s1), Some s2 => Some ((c::s1) ++ s2) *)
(*             | _, _ => None *)
(*           end) (Some nil) v *)
(*   end. *)

(* Lemma to_string_corr1 : forall a (v:interp (regexp_type a)) s,  *)
(*   to_string a v = Some s -> in_regexp a s v. *)
(* Proof. *)
(*   Ltac myinj :=      *)
(*     match goal with  *)
(*       | [ H : Some _ = Some _ |- _ ] => injection H ; intros ; clear H ; subst *)
(*       | _ => idtac *)
(*     end. *)
(*   induction a ; simpl ; intros ; eauto ; myinj ; try (destruct v ; eauto ; fail). *)
(*    destruct (char_dec c v) ; try congruence ; myinj ; eauto. *)
(*    destruct v as [v1 v2] ; simpl in *. remember (to_string a1 v1) as sopt1 ;  *)
(*    remember (to_string a2 v2) as sopt2 ; destruct sopt1 ; destruct sopt2 ; try congruence ; *)
(*    myinj ; eauto.  *)
(*    generalize s H. clear s H. *)
(*    induction v ; intros ; simpl in * ; myinj ; eauto. *)
(*    remember (to_string a a0) as sopt1. destruct sopt1 ; try congruence. *)
(*    destruct l ; try congruence. *)
(*    match goal with  *)
(*      | [ H : match ?e with | Some _ => _ | None => _ end = _ |- _] =>  *)
(*        remember e as sopt2 ; destruct sopt2 ; try congruence *)
(*    end. myinj. specialize (IHa _ _ (eq_sym Heqsopt1)). *)
(*    eapply InaStar_cons ; eauto ; congruence. *)
(* Defined. *)

(* Lemma to_string_corr2 : forall a (s:list char_p) (v:interp (regexp_type a)), *)
(*   in_regexp a s v -> to_string a v = Some s. *)
(* Proof. *)
(*   induction 1 ; subst ; simpl ; mysimp ; try congruence ;  *)
(*   try (rewrite IHin_regexp1 ; try rewrite IHin_regexp2 ; auto). *)
(*   destruct s1 ; try congruence. auto. *)
(* Qed. *)


(* stuff that can be copied from the old Parser.v *)
(*   - optimizing constructors for regexps *)
(*   - def of naive_parse and its correctness proofs. *)
