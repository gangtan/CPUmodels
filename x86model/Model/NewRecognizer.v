(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
Require Import List.
Require Import Arith.
Require Import Bool.
Require Import Eqdep.
(* Require Import PArith. *)
Require Import ZArith.

Require Import Parser.
Import X86_PARSER_ARG.
Require Import CommonTacs.
Set Implicit Arguments.

Local Ltac false_elim :=
  match goal with
    | [H:False |- _] => destruct H
  end.

(** * Define a series of augmented MSets. 
      This should be moved to a separate file *)

Require Import MSets.MSetInterface.
Require Import MSets.MSetProperties.
Require Import MSets.MSetWeakList.

(** ** Additional properties of sets *)
Module Type WMOREPROPERTIES (M:WSets).
  Parameter add_transpose:
    forall (A : Type) (f : A -> M.elt),
       transpose M.Equal (fun (x : A) (s : M.t) => M.add (f x) s).

  Parameter subset_empty_uniq:
    forall s : M.t, M.Subset s M.empty -> M.Equal s M.empty.

  Definition disjoint s1 s2 := forall x, ~(M.In x s1 /\ M.In x s2).

  Parameter disjoint_spec: forall s1 s2,
    disjoint s1 s2 <-> M.Equal (M.inter s1 s2) M.empty.

  Declare Instance disjoint_subset: 
    Proper (flip M.Subset ==> flip M.Subset ==> impl) disjoint.

  Parameter disjoint_symm: forall s1 s2, disjoint s1 s2 -> disjoint s2 s1.
    
  Parameter disjoint_empty: forall s, disjoint s M.empty.

  Parameter inclA_subset: forall s1 s2,
    inclA M.E.eq (M.elements s1) (M.elements s2) -> M.Subset s1 s2.

  Parameter elements_app_subset1: forall s1 s2 s3,
    M.elements s1 = M.elements s2 ++ M.elements s3 -> M.Subset s2 s1.

  Parameter elements_app_subset2: forall s1 s2 s3,
    M.elements s1 = M.elements s2 ++ M.elements s3 -> M.Subset s3 s1.

  Parameter elements_app_disjoint: forall s s1 s2,
    M.elements s = M.elements s1 ++ M.elements s2 -> disjoint s1 s2.

End WMOREPROPERTIES.

Module WMoreProperties (M:WSets) : WMOREPROPERTIES M.
  Module P:= WProperties M.

  Lemma add_transpose :
    forall A (f:A->M.elt), 
      @transpose A _ M.Equal (fun x s => M.add (f x) s).
  Proof. unfold transpose. intros. apply P.add_add. Qed.

  Lemma subset_empty_uniq: 
    forall s, M.Subset s M.empty -> M.Equal s M.empty.
  Proof. intros. 
    apply P.subset_antisym. assumption. apply P.subset_empty.
  Qed.

  Definition disjoint s1 s2 := forall x, ~(M.In x s1 /\ M.In x s2).

  Lemma disjoint_spec: forall s1 s2,
    disjoint s1 s2 <-> M.Equal (M.inter s1 s2) M.empty.
  Proof. unfold disjoint; intros; split; intros. 
    apply P.subset_antisym.
      intros x H2. apply M.inter_spec in H2. apply H in H2. inversion H2.
      apply P.subset_empty.
    intro.
      assert (M.In x (M.inter s1 s2)).
        apply M.inter_spec; auto.
      rewrite H in H1.
      apply P.FM.empty_iff in H1. trivial.
  Qed.

  Instance disjoint_subset: 
    Proper (flip M.Subset ==> flip M.Subset ==> impl) disjoint.
  Proof. unfold Proper, respectful, impl.
    intros s1' s1 H s2' s2 H2 H4.
    apply disjoint_spec in H4. apply disjoint_spec.
    apply P.subset_antisym.
      intros x H6. apply H4. rewrite H. rewrite H2.
      assumption.
      apply P.subset_empty.
  Qed.

  Lemma disjoint_symm: forall s1 s2, disjoint s1 s2 -> disjoint s2 s1.
  Proof. unfold disjoint. intros. intro. destruct H0. apply (H x). auto. Qed.
    
  Lemma disjoint_empty: forall s, disjoint s M.empty.
  Proof. unfold disjoint. intros. intro. destruct H. 
    apply P.FM.empty_iff in H0. trivial.
  Qed.

  Lemma inclA_subset s1 s2:
    inclA M.E.eq (M.elements s1) (M.elements s2) -> M.Subset s1 s2.
  Proof. unfold M.Subset; intros.
    apply M.elements_spec1.
    apply M.elements_spec1 in H0.
    auto.
  Qed.

  Lemma elements_app_subset1 s1 s2 s3:
    M.elements s1 = M.elements s2 ++ M.elements s3 
      -> M.Subset s2 s1.
  Proof. intros; apply inclA_subset. rewrite H.
    eapply Coqlib.inclA_app_l. apply M.E.eq_equiv.
  Qed.

  Lemma elements_app_subset2 s1 s2 s3:
    M.elements s1 = M.elements s2 ++ M.elements s3 
      -> M.Subset s3 s1.
  Proof. intros; apply inclA_subset. rewrite H.
    eapply Coqlib.inclA_app_r. apply M.E.eq_equiv.
  Qed.

  Lemma elements_app_disjoint s s1 s2: 
    M.elements s = M.elements s1 ++ M.elements s2 
      -> disjoint s1 s2.
  Proof. intro. intros x H2. destruct H2.
    apply M.elements_spec1 in H0.
    apply M.elements_spec1 in H1.
    generalize (M.elements_spec2w s). intro.
    rewrite H in H2.
    generalize (Coqlib.NoDupA_app_if M.E.eq_equiv H2). 
    crush_hyp.
  Qed.
    
End WMoreProperties.

(** ** A map function for sets *)
Module Type MAPSET (M:WSets) (M':WSets).
  Definition proper_map := 
    {f: M.elt -> M'.elt | Proper (M.E.eq ==> M'.E.eq) f}.

  Definition get_fun (m:proper_map) := proj1_sig m.

  Definition eq_proper_map (m1 m2: proper_map) := 
    (M.E.eq ==> M'.E.eq)%signature (get_fun m1) (get_fun m2).

  Definition injective (m: proper_map) (s:M.t) :=
    forall x y,  M.In x s -> M.In y s ->
                 M'.E.eq (get_fun m x) (get_fun m y) -> M.E.eq x y.

  Parameter map: proper_map -> M.t -> M'.t.

  Declare Instance injective_eq:
    forall m, Proper (M.eq ==> iff) (injective m).

  Declare Instance injective_subset: 
    forall m, Proper (flip M.Subset ==> impl) (injective m).

  Parameter injective_empty: forall m, injective m M.empty.

  Parameter map_intro :
    forall (m : proper_map) (s : M.t) (x : M.elt) (y : M'.E.t),
      M.In x s -> M'.E.eq (get_fun m x) y -> M'.In y (map m s).

  Parameter map_elim :
    forall (m : proper_map) (s : M.t) (y : M'.elt),
      M'.In y (map m s) ->
      exists x : M.elt, M.In x s /\ M'.E.eq (get_fun m x) y.

  Parameter map_subset :
    forall (m : proper_map) (s1 s2 : M.t),
      M.Subset s1 s2 -> M'.Subset (map m s1) (map m s2).

  Parameter map_union :
    forall (m : proper_map) (s1 s2 : M.t),
      M'.Equal (map m (M.union s1 s2)) (M'.union (map m s1) (map m s2)).

  Parameter map_equal :
    Proper (eq_proper_map ==> M.Equal ==> M'.Equal) map.

  Parameter map_cardinal :
    forall (m : proper_map) (s : M.t),
      injective m s -> M'.cardinal (map m s) = M.cardinal s.

  Parameter map_cardinal_le :
    forall (m : proper_map) (s : M.t),
      M'.cardinal (map m s) <= M.cardinal s.
End MAPSET.

Module MapSetGen (M:WSets)(M':WSets) : MAPSET M M'.
  Module P:=WProperties M.
  Module P':=WProperties M'.
  Module PM':=WMoreProperties M'.

  Definition proper_map := 
    {f: M.elt -> M'.elt | Proper (M.E.eq ==> M'.E.eq) f}.

  Definition get_fun (m:proper_map) := proj1_sig m.

  Definition eq_proper_map (m1 m2: proper_map) := 
    (M.E.eq ==> M'.E.eq)%signature (get_fun m1) (get_fun m2).

  Section Map.

    Variable m: proper_map.

    Instance m_proper : Proper (M.E.eq ==> M'.E.eq) (get_fun m).
    Proof. apply (proj2_sig m). Qed.

    Definition injective (s:M.t) := 
      forall x y, 
        M.In x s -> M.In y s
          -> M'.E.eq (get_fun m x) (get_fun m y) -> M.E.eq x y.

    Instance injective_eq: Proper (M.eq ==> iff) injective.
    Proof. intros s1 s2 H; split; unfold injective. 
      intros. rewrite <- H in H1, H2. crush.
      intros. rewrite H in H1, H2. crush.
    Qed.

    Instance injective_subset: Proper (flip M.Subset ==> impl) injective.
    Proof. intros s1 s2 H. unfold injective, impl. intros.
      unfold flip in H. 
      assert (M.In x s1).
        apply P.in_subset with (s1:=s2); assumption.
      auto.
    Qed.

    Lemma injective_empty: injective M.empty.
    Proof. unfold injective. intros.
     apply P.FM.empty_iff in H; contradict H.
    Qed.

    Definition map s := 
      M.fold (fun x s => M'.add (get_fun m x) s) s M'.empty.

    Lemma map_intro: forall s x y,
      M.In x s -> M'.E.eq (get_fun m x) y -> M'.In y (map s).
    Proof. unfold map. intros s x y.
      apply P.fold_rec_bis; intros.
        apply H0; crush.
        apply P.FM.empty_iff in H; contradict H.
        apply P.FM.add_iff in H2; destruct H2.
          rewrite H2; auto with set.
          auto with set.
    Qed.

    Lemma map_elim: forall s y, 
      M'.In y (map s)
        -> exists x, M.In x s /\ M'.E.eq (get_fun m x) y.
    Proof. unfold map. intros s y.
        apply P.fold_rec_nodep; intros.
          apply P'.FM.empty_iff in H; contradict H.
          apply P'.FM.add_iff in H1; destruct H1; crush.
    Qed.

    Lemma map_subset: forall s1 s2 ,
       M.Subset s1 s2 -> M'.Subset (map s1) (map s2).
    Proof. intros. unfold M'.Subset. intros.
      apply map_elim in H0. sim.
      eapply map_intro; eauto.
    Qed.

    Lemma map_union: forall s1 s2, 
      M'.Equal (map (M.union s1 s2)) (M'.union (map s1) (map s2)).
    Proof. unfold M'.Equal. intros; split; intro.
      Case "->". apply map_elim in H. sim.
        apply M'.union_spec.
        apply M.union_spec in H; destruct H; 
          [left|right]; eapply map_intro; eauto.
      Case "<-". 
        apply M'.union_spec in H; destruct H;
          apply map_elim in H; sim.
        eapply map_intro; [(apply M.union_spec; left; eassumption) | trivial].
        eapply map_intro; [(apply M.union_spec; right; eassumption) | trivial].
    Qed.

    Lemma map_cardinal_aux : forall s,
      injective s -> 
        M'.cardinal (map s) = M.cardinal s /\
        forall y, M'.In y (map s) -> 
                  exists x, M.In x s /\ M'.E.eq y (get_fun m x).
    Proof.  unfold map. intros s.
      apply P.fold_rec_bis.
      Case "proper P". intros. rewrite <- H in H1. use_lemma H0 by assumption.
        split; [crush | idtac].
        intros. sim. use_lemma H4 by eassumption.
        sim. exists x. rewrite <- H. crush.
      Case "base".
        intro.
        rewrite P'.empty_cardinal. rewrite P.empty_cardinal.
        split; [crush | idtac].
        intros y H2. apply P'.FM.empty_iff in H2. contradict H2.
      Case "ind".
        intros.
        assert (H4: injective s').
          eapply injective_subset; try eassumption.
          apply P.subset_add_2. reflexivity.
        use_lemma H1 by assumption.
        assert (H6: not (M'.In (get_fun m x) a)).
          contradict H0. sim. use_lemma H5 by eassumption. sim.
          assert (M.E.eq x x0).
            apply H2.
              apply P.FM.add_1. reflexivity.
              auto with set.
              trivial.
          rewrite H8. trivial.
        split.
          rewrite P.add_cardinal_2 by assumption.
            rewrite P'.add_cardinal_2 by assumption.
            crush.
          intros.
            apply P'.FM.add_iff in H5; destruct H5.
            exists x. 
              split. apply P.FM.add_1. reflexivity.
                symmetry. trivial.
              sim. use_lemma H7 by eassumption.
              sim. exists x0.
              split; auto with set.
    Qed.

    Lemma map_cardinal : forall s,
      injective s -> M'.cardinal (map s) = M.cardinal s.
    Proof. intros. use_lemma map_cardinal_aux by eassumption. crush. Qed.

  End Map.

  Instance map_equal:
    Proper (eq_proper_map ==> M.Equal ==> M'.Equal) map.
  Proof. unfold Proper, respectful, map. intros m1 m2 H x.
    apply P.fold_rec_bis.
      intros. assert (M.Equal s y) by (transitivity s'; assumption).
        crush.
      Case "base". intros.
        rewrite P.fold_1.
          reflexivity.
          apply M'.eq_equiv.
          apply P.empty_is_empty_2. symmetry; trivial.
      Case "ind". intros.
        rewrite P.fold_2; try eassumption.
        f_equiv.
          apply H. reflexivity.
          apply H2. reflexivity.
        apply M'.eq_equiv.
        f_equiv.
        generalize (proj2_sig m2); intro; solve_proper.
        apply PM'.add_transpose.
        apply P.Add_Equal. symmetry. trivial.
  Qed.

  Lemma map_cardinal_le: forall m s, M'.cardinal (map m s) <= M.cardinal s.
  Proof. unfold map; intros.
    apply P.fold_rec; intros.
    Case "base". 
      rewrite P'.empty_cardinal. omega.
    Case "ind".
      apply P.Add_Equal in H1.
      apply P.Equal_cardinal in H1.
      apply P.add_cardinal_2 in H0.
      destruct (P'.In_dec (get_fun m x) a).
        use_lemma P'.add_cardinal_1 by eassumption. omega.
        use_lemma P'.add_cardinal_2 by eassumption. omega.
  Qed.

End MapSetGen.

Module MapSet (M:WSets) : MAPSET M M := MapSetGen M M.

(* gtan: I really want to do the following; but it seems like that a Coq
   bug prevents it; in particular, I cannot use operations in M somehow. *)
(* Module SetWithMap (M:WSets). *)
(*   Include M. *)
(*   Include MapSetGen M M. *)
(* End SetWithMap. *)

(** ** Power sets *)
Module Type POWERSET (M:WSets).

  Declare Module MM : WSets with Definition E.t:=M.t.

  Parameter powerset: M.t -> MM.t.

  Parameter powerset_spec: 
    forall s s', MM.In s' (powerset s) <-> M.Subset s' s.

  Parameter powerset_cardinal: 
    forall s, MM.cardinal (powerset s) = NPeano.pow 2 (M.cardinal s).

End POWERSET.

Module ListPowerSet (M:WSets) <: POWERSET M.

  Module MM := MSetWeakList.Make M.
  Module MMF := MapSet MM.
  Module P := MSetProperties.WProperties M.
  Module PM := WMoreProperties M.
  Module PP := MSetProperties.WProperties MM.
  Module PPM := WMoreProperties MM.

  (** Add x to every set in a set of sets *)
  Definition add_elm (x: M.elt) : MMF.proper_map.
    refine (exist _ (M.add x) _).
    abstract (solve_proper).
  Defined.

  Instance add_elm_proper: Proper (M.E.eq ==> MMF.eq_proper_map) add_elm.
  Proof. unfold Proper, MMF.eq_proper_map, respectful. simpl. intros.
   rewrite H, H0. reflexivity.
  Qed.

  Definition powerset_fold_op :=
    fun (x:M.elt)(ss:MM.t) => MM.union ss (MMF.map (add_elm x) ss).

  Definition powerset s := 
    M.fold powerset_fold_op s (MM.singleton M.empty).

  Lemma powerset_base: 
    forall s, M.Empty s -> MM.eq (powerset s) (MM.singleton M.empty).
  Proof. unfold powerset; intros.
    rewrite P.fold_1. reflexivity.
    apply MM.eq_equiv. trivial.
  Qed.

  Lemma map_add_transpose: 
    transpose MM.Equal (fun x s => MMF.map (add_elm x) s).
  Proof. 
    assert (forall x y ss, 
              MM.Subset (MMF.map (add_elm x) (MMF.map (add_elm y) ss))
                        (MMF.map (add_elm y) (MMF.map (add_elm x) ss))).
      intros. intros mm H.
      apply MMF.map_elim in H. destruct H as [mm1 [H2 H4]].
      apply MMF.map_elim in H2. destruct H2 as [mm2 [H6 H8]].
      assert (MM.In (M.add x mm2) (MMF.map (add_elm x) ss)).
        eapply MMF.map_intro. eassumption. reflexivity.
      assert (M.Equal (M.add y (M.add x mm2)) mm).
        rewrite <- H4. simpl. rewrite <- H8. simpl.
        apply PM.add_transpose with (f:= fun x => x).
      eapply MMF.map_intro. eassumption. eassumption.
    unfold transpose. intros x y ss mm; split; intro;
      apply H; trivial.
  Qed.

  Lemma powerset_fold_op_transpose: transpose MM.Equal powerset_fold_op.
  Proof. unfold transpose, powerset_fold_op. intros.
    do 2 rewrite PP.union_assoc.
    f_equiv.
    do 2 (rewrite MMF.map_union by solve_proper).
    rewrite <- PP.union_assoc.
    rewrite (@PP.union_sym (MMF.map (add_elm y) z)).
    rewrite PP.union_assoc.
    do 2 f_equiv.
    apply map_add_transpose.
  Qed.

  Lemma powerset_step : 
    forall s1 s2 x, not (M.In x s1) -> P.Add x s1 s2 ->
       MM.eq (powerset s2) 
             (MM.union (powerset s1) (MMF.map (add_elm x) (powerset s1))).
  Proof. unfold powerset at 1. intros.
    rewrite (@P.fold_2 s1 s2 x MM.t MM.Equal). reflexivity.
      apply MM.eq_equiv.
      unfold powerset_fold_op.
        solve_proper.
      apply powerset_fold_op_transpose.
      assumption.
      assumption.
  Qed.

  Theorem powerset_spec : forall s s', MM.In s' (powerset s) <-> M.Subset s' s.
  Proof. induction s using P.set_induction.
    Case "empty(s)". intros.
      assert (H2:MM.Equal (powerset s) (MM.singleton M.empty)).
        unfold powerset; rewrite P.fold_1.
        reflexivity.
        apply MM.eq_equiv.
        assumption.
      rewrite H2.
      apply P.empty_is_empty_1 in H. rewrite H.
      split; intros.
      SCase "->".
        apply PP.FM.singleton_1 in H0. rewrite <- H0.
        reflexivity.
      SCase "<-".
        apply PM.subset_empty_uniq in H0. rewrite H0.
        apply MM.singleton_spec. reflexivity.
    Case "add x s1 = s2". intros s.
      rewrite powerset_step by eassumption.
      apply P.Add_Equal in H0. rewrite H0.
      split; intro.
      SCase "->".
        apply MM.union_spec in H1; destruct H1. 
        SSCase "s in (powerset s1)".
          apply P.subset_add_2. apply IHs1. assumption. 
        SSCase "s in map (add x) (powerset s1)".
          apply MMF.map_elim in H1. destruct H1 as [s' [H2 H4]].
          rewrite <- H4. simpl. f_equiv. apply IHs1. assumption.
      SCase "<-".
        assert (M.Subset (M.remove x s) s1).
          intro a; intros. 
          apply M.remove_spec in H2. destruct H2.
          apply H1 in H2. apply M.add_spec in H2. crush.
        apply IHs1 in H2.
        apply MM.union_spec.
        destruct (P.In_dec x s).
          SSCase "x in s". right.
            eapply MMF.map_intro; try eassumption.
            apply P.add_remove. assumption.
          SSCase "x notin s". left.
            rewrite P.remove_equal in H2 by assumption.
            assumption.
  Qed.

  (* Require Import Coq.PArith.BinPos. *)
  (* Definition two_power (n:nat) := shift_nat n 1. *)
  (* Lemma two_power_S:  *)
  (*   forall n, two_power (S n) = (2 * two_power n)%positive. *)
  (* Proof. unfold two_power, shift_nat. simpl. trivial. Qed. *)

  Lemma powerset_add_disjoint: forall x s,
    ~ M.In x s -> 
    PPM.disjoint (powerset s) (MMF.map (add_elm x) (powerset s)).
  Proof. unfold PPM.disjoint. intros. 
    intro H2; destruct H2 as [H2 H4].
    apply MMF.map_elim in H4; destruct H4 as [s' [H6 H8]].
    apply powerset_spec in H2. apply powerset_spec in H6. 
    rewrite <- H8 in H2.
    assert (M.In x s).
      apply H2. apply P.FM.add_1. reflexivity.
    crush.
  Qed.

  Lemma powerset_add_injective: forall x s,
    ~ M.In x s -> MMF.injective (add_elm x) (powerset s).
  Proof. unfold MMF.injective. intros x s H. 
    assert (H2: forall s1 s2, 
              MM.In s1 (powerset s) -> MM.In s2 (powerset s) -> 
              M.Equal (M.add x s1) (M.add x s2) ->
              M.Subset s1 s2).
      intros.
      assert (~ M.In x s1).
        intro. apply powerset_spec in H0. crush.
      intro x1; intro.
      assert (H6: M.In x1 (M.add x s1)).
        apply M.add_spec. right. assumption.
      rewrite H2 in H6.
      apply M.add_spec in H6.
      destruct H6 as [H6|H6].
        rewrite H6 in H4. crush.
        crush.
     intros s1 s2. intros.
     apply P.subset_antisym.
       apply H2; assumption.
       apply H2; try assumption. symmetry; assumption.
  Qed.

  Theorem powerset_cardinal: 
    forall s, MM.cardinal (powerset s) = NPeano.pow 2 (M.cardinal s).
  Proof. induction s using P.set_induction.
    Case "empty(s)".
      rewrite powerset_base by assumption.
      rewrite PP.singleton_cardinal.
      apply P.empty_is_empty_1 in H. rewrite H.
      rewrite P.empty_cardinal. trivial.
    Case "s2 = add x s1".
      rewrite powerset_step by eassumption.
      assert (PPM.disjoint (powerset s1)
                           (MMF.map (add_elm x) (powerset s1))).
        eauto using powerset_add_disjoint.
      rewrite PP.union_cardinal by eassumption.
      assert (MMF.injective (add_elm x) (powerset s1)).
        apply powerset_add_injective; eassumption.
      rewrite MMF.map_cardinal by assumption.
      rewrite IHs1.
      rewrite P.Add_Equal in H0. rewrite H0.
      rewrite P.add_cardinal_2 by assumption. 
      simpl.
      omega.
  Qed.

End ListPowerSet.


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
Module RESet := MSetAVL.Make REOrderedType.
Module RESetF := MapSet RESet.
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

Lemma re_set_map_intro: forall (x y:RESet.elt) m (s:RESet.t),
  RESet.In y s -> x = RESetF.get_fun m y -> RESet.In x (RESetF.map m s).
Proof. intros. 
  eapply RESetF.map_intro.
    eassumption.
    subst. apply REOrderedType.eq_equiv.
Qed.

Lemma re_set_map_elim: forall (x:RESet.elt) m (s:RESet.t),
  RESet.In x (RESetF.map m s) -> 
  exists y, RESet.In y s /\ x = RESetF.get_fun m y.
Proof. intros. apply RESetF.map_elim in H.
  sim. apply compare_re_eq_leibniz in H0. crush.
Qed.

Lemma re_set_map_proper: forall f, Proper (RESet.E.eq ==> RESet.E.eq) f.
Proof. unfold Proper, respectful. intros.
  apply compare_re_eq_leibniz in H. subst. 
  apply REOrderedType.eq_equiv.
Qed.

Definition re_set_build_map (f: regexp -> regexp) : RESetF.proper_map :=
  exist _ f (re_set_map_proper f).

(** * The notion of prebase of a regexp and partial-derivative sets.

  The relation between prebases and partial derivative sets are in the
  paper "From Mirkin's prebases to Antimirov's Word Partial Derivatives"
  by Champarnaud and Ziadi.  *)

(** Concat regexp r to the right of every regexp in a regexp set *)
Definition set_cat_re (s:RESet.t) (r:regexp): RESet.t := 
  match r with
    | aEps => s (* not stricitly necessary; an optimization *)
    | aZero => RESet.empty
    | _ => RESetF.map (re_set_build_map (fun r1 => aCat r1 r)) s
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
       apply RESetF.map_elim in H; 
       destruct H as [y [H2 H4]]; 
       apply compare_re_eq_leibniz in H4;
       eexists; crush; fail).
  Case "r2=aEps". left. auto.
  Case "r2=aZero". right; left. simpl in *. re_set_simpl.
Qed.

Lemma set_cat_re_cardinal: 
  forall s r, RESet.cardinal (s $ r) <= RESet.cardinal s.
Proof. unfold set_cat_re. 
  destruct r; auto using RESetF.map_cardinal_le.
  Case "aZero".
    repeat rewrite RESet.cardinal_spec. simpl.
    auto using le_0_n.
Qed.

Lemma set_cat_re_subset : forall s1 s2 r,
  RESet.Subset s1 s2 -> RESet.Subset (s1 $ r) (s2 $ r).
Proof. destruct r; simpl; intros; try (auto using RESetF.map_subset).
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
    auto with set.
    auto with set.
    apply RESetP.FM.add_2. eauto using prebase_trans.
Qed.

(** * Definition of the notion of partial derivatives.

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

(** reset_nullable(rs) is true iff one of the regexp in rs is nullable *)
Definition reset_nullable (rs:RESet.t): bool :=
  RESet.exists_ nullable rs.

(** reset_always_rejects(rs) is true iff all regexps in rs always rejects *)
Definition reset_always_rejects (rs:RESet.t): bool :=
  RESet.for_all always_rejects rs.


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

(** Partial derivatives over a regexp set; the result of the union 
    of taking partial derivatives on every regexp in the set *)
Definition pdrv_set (a:char_p) (rs:RESet.t) : RESet.t :=
  RESet.fold (fun r rs1 => RESet.union (pdrv a r) rs1) rs RESet.empty.

(** Word partial derivatives; 
  wpdrv(nil, rs) = rs
  wpdrv(a cons w, rs) = wpdrv(w, pdrv_set(a, rs)) *)
Fixpoint wpdrv (s:list char_p) (rs:RESet.t) : RESet.t := 
  match s with
    | nil => rs
    | a :: s' => wpdrv s' (pdrv_set a rs)
  end.

(** ** Relating partial derivatives to prebase *)

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
  Case "aStar". apply RESetF.map_subset. assumption.
Qed.

Lemma pdrv_subset_pdset: 
  forall a r, RESet.Subset (pdrv a r) (pdset r).
Proof. unfold pdset; intros. 
  apply RESetP.subset_add_2. apply pdrv_subset_prebase.
Qed.

(** ** Denotation semantics of regexps *)

Inductive in_regexp : forall (r:regexp), list char_p -> Prop :=
| InrEps : forall s, s = nil -> in_regexp aEps s
| InrChar : forall c s, s = c::nil -> in_regexp (aChar c) s
| InrAny : forall c s, s = c::nil -> in_regexp aAny s
| InrCat : forall a1 a2 s1 s2 s,
  in_regexp a1 s1 -> in_regexp a2 s2 -> s = s1 ++ s2 -> 
  in_regexp (aCat a1 a2) s
| InrAlt_l : forall a1 a2 s,
  in_regexp a1 s -> in_regexp (aAlt a1 a2) s
| InrAlt_r : forall a1 a2 s,
  in_regexp a2 s -> in_regexp (aAlt a1 a2) s
| InrStar_eps : forall a s, s = nil -> in_regexp (aStar a) s
| InrStar_cons : forall a s1 s2 s,
  in_regexp a s1 -> in_regexp (aStar a) s2 -> 
  s1 <> nil -> s = s1 ++ s2 -> in_regexp (aStar a) s.

Hint Local Constructors in_regexp.

(** Denotation semantics of regexp sets *)
Definition in_re_set (rs:RESet.t) (s:list char_p) :=
  exists r, RESet.In r rs /\ in_regexp r s.

(** forall rs1 rs2 s1 s2, rs1 subseteq rs2 -> s1=s2 ->
      in_re_set rs1 s1 -> in_re_set rs2 s2 *)
Instance in_re_set_subset: Proper (RESet.Subset ==> eq ==> impl) in_re_set.
Proof. intros rs1 rs2 H1 s1 s2 H2 H3. unfold in_re_set in *.
  sim. eexists. 
  split. eapply RESetP.in_subset; eassumption.
    congruence.
Qed.

Instance in_re_set_equal: Proper (RESet.Equal ==> eq ==> impl) in_re_set.
Proof. intros rs1 rs2 H1 s1 s2 H2 H3. unfold in_re_set in *.
  sim. exists x. 
  split. rewrite <- H1. assumption.
  crush.
Qed.

Lemma in_re_set_empty : forall s, not (in_re_set RESet.empty s).
Proof. unfold in_re_set. intros. intro H.
  destruct H as [r [H2 _]].
  apply RESetP.Dec.F.empty_iff in H2. crush.
Qed.

Lemma in_re_set_singleton:
  forall r s, in_re_set (RESet.singleton r) s <-> in_regexp r s.
Proof. unfold in_re_set. 
  intros; split; intros.
  Case "->".
    destruct H as [r0 [H2 H4]].
    apply RESetP.Dec.F.singleton_1 in H2.
    apply compare_re_eq_leibniz in H2. congruence.
  Case "<-".
    eauto using RESetP.Dec.MSetDecideTestCases.test_In_singleton.
Qed.
        
Lemma in_re_set_union : forall rs1 rs2 s,
    in_re_set (RESet.union rs1 rs2) s <->
    in_re_set rs1 s \/ in_re_set rs2 s.
Proof.  split; intros.
  Case "->".
    unfold in_re_set in *.
    destruct H as [r [H2 H4]].
    apply RESetP.FM.union_1 in H2.
    destruct H2; [left | right]; eauto.
  Case "<-".
    destruct H.
      eapply in_re_set_subset.
        apply RESetP.union_subset_1. reflexivity. trivial.
      eapply in_re_set_subset.
        apply RESetP.union_subset_2. reflexivity. trivial.
Qed.      

Lemma in_re_set_map: forall m rs s,
  in_re_set (RESetF.map m rs) s <-> 
  exists r, RESet.In r rs /\ in_regexp (RESetF.get_fun m r) s.
Proof. unfold in_re_set; split; intros.
  Case "->". 
    destruct H as [r [H2 H4]].
    apply re_set_map_elim in H2. crush.
  Case "<-".
    destruct H as [r [H2 H4]].
    exists (RESetF.get_fun m r). 
    split; try assumption.
    apply re_set_map_intro with (y:=r); trivial.
Qed.

Lemma in_re_set_cat_re : forall rs r s,
  in_re_set (rs $ r) s <->
  exists s1 s2, s=s1++s2 /\ in_re_set rs s1 /\ in_regexp r s2.
Proof. intros. split; intros.
  Case "->".
    destruct r; simpl in H;
      try (apply (in_re_set_map _ rs s) in H;
           destruct H as [r10 [H2 H4]];
           inversion_clear H4;
           unfold in_re_set;
           exists s1, s2; eauto).
    exists s, nil.
      crush.
      contradict H; apply in_re_set_empty.
  Case "<-".
    destruct H as [s1 [s2 [H2 [H4 H6]]]].
    destruct r; simpl;
      try (apply in_re_set_map;
           unfold in_re_set in *;
           generalize InrCat; crush; fail).
      crush' false in_regexp.
      crush' false in_regexp.
Qed.

(** ** Correctness of partial derivatives:
      (a::l) in [[r]] iff l in [[pdrv(a,r)]] *)
Section PDRV_CORRECT.

  Local Ltac lprover := 
    repeat match goal with
      | [H: _ :: _ = nil |- _] => inversion H
      | [H: in_re_set RESet.empty _ |- _] =>
        contradict H; apply in_re_set_empty
      | [H: in_re_set (RESet.singleton _) _ |- _] =>
        apply in_re_set_singleton in H
      | [|- in_re_set (RESet.singleton _) _] =>
        apply in_re_set_singleton
      | [H: in_re_set (RESet.union _ _) _ |- _] => 
        apply in_re_set_union in H
      | [|- in_re_set (RESet.union _ _) _] => 
        apply in_re_set_union
      | [|- in_regexp _ _] => econstructor
      | _ => sim; crush' false in_regexp
    end.

  Instance nullable_proper: Proper (RESet.E.eq ==> eq) nullable.
  Proof. unfold Proper, respectful. intros.
    apply compare_re_eq_leibniz in H. crush.
  Qed.
    
  Lemma nullable_corr :
    forall r, nullable r = true <-> in_regexp r nil.
  Proof. induction r.
    Case "aEps".  crush.
    Case "aZero". lprover.
    Case "aChar". lprover.
    Case "aAny". lprover.
    Case "aCat". split.
      SCase "->". simpl; intro; bool_elim_tac. crush.
      SCase "<-". intro; inversion_clear H.
        symmetry in H2.
        apply app_eq_nil in H2.
        simpl; sim; subst. bool_intro_tac; auto.
    Case "aAlt". split.
      SCase "->". simpl; intro; bool_elim_tac; crush.
      SCase "<-". intro; simpl. apply orb_true_iff.
        inversion H; crush.
    Case "aStar". crush.
  Qed.

  Lemma pdrv_corr : 
    forall r a s, in_regexp r (a :: s) <-> in_re_set (pdrv a r) s.
  Proof. induction r.
    Case "aEps".
      simpl. split; intros; lprover.
    Case "aZero".
      simpl. split; intros; lprover.
    Case "aChar".
      intros; simpl.
      destruct (char_dec a c).
      SCase "a=c". subst. split; intros; lprover.
      SCase "a<>c". split; intros; lprover.
    Case "aAny". simpl. split; intros; lprover.
    Case "aCat". simpl. split; intros.
      SCase "->". inversion_clear H.
        destruct s1 as [| b s1'].
        SSCase "s1=nil".
          remember_destruct_head as nl.
          SSSCase "nullable r1".
            apply in_re_set_union. right. crush_hyp.
          SSSCase "not (nullable r1)".
            apply nullable_corr in H0. crush.
        SSCase "s1=b::s1'".
          destruct_head; [apply in_re_set_union; left | idtac];
          apply in_re_set_cat_re; exists s1', s2; crush_hyp.
      SCase "<-".
        remember_destruct_head in H as nl.
        SSCase "nullable r1".
          apply in_re_set_union in H.
          destruct H.
          SSSCase "s in (pdrv a r1) $ r2".
            apply in_re_set_cat_re in H.
            destruct H as [s1 [s2]]; sim.
            apply InrCat with (s1:= (a::s1)) (s2:=s2); crush.
          SSSCase "s in (pdrv a r2)".
            apply InrCat with (s1:= nil) (s2:=a::s); 
               crush' nullable_corr fail.
        SSCase "not (nullable r1)".
          apply in_re_set_cat_re in H.
          destruct H as [s1 [s2]]; sim.
          apply InrCat with (s1:= (a::s1)) (s2:=s2); crush.
    Case "aAlt". simpl; split; intros.
      SCase "->". 
        lprover; inversion_clear H; [left|right]; crush_hyp.
      SCase "<-". apply in_re_set_union in H.
        destruct H.
          apply InrAlt_l. crush_hyp.
          apply InrAlt_r. crush_hyp.
    Case "aStar". split; intros.
      SCase "->".
        inversion_clear H; [congruence | idtac].
        destruct s1; [congruence | idtac].
        inversion_clear H3.
        apply in_re_set_cat_re. fold pdrv.
        exists s1, s2. crush_hyp.
      SCase "<-".
        compute [pdrv] in H. fold pdrv in H.
        apply in_re_set_cat_re in H.
        destruct H as [s1 [s2]]; sim.
        apply InrStar_cons with (s1:= (a::s1)) (s2:=s2); crush.
  Qed.


End PDRV_CORRECT.

Lemma reset_nullable_corr rs: reset_nullable rs = true <-> in_re_set rs nil.
Proof. unfold reset_nullable, in_re_set. 
    generalize (nullable_proper); intro.
    split; intro.
    Case "->".
      apply RESet.exists_spec in H0; [idtac | trivial].
      unfold RESet.Exists in H0.
      generalize nullable_corr; crush_hyp.
    Case "<-".
      apply RESet.exists_spec; [trivial | idtac].
      unfold RESet.Exists.
      generalize nullable_corr; crush_hyp.
Qed.
      
(** [always_rejects] is correct. *)
Lemma always_rejects_corr (r:regexp) : 
  always_rejects r = true -> forall ls, ~ in_regexp r ls.
Proof.
  induction r; crush.
  Case "aZero". intro H2. inversion H2.
  Case "aCat". intro H2.
    apply orb_prop in H.
    destruct H; inversion H2; crush_hyp.
  Case "aAlt". intro H2.
    apply andb_prop in H. inversion H2; crush_hyp.
Qed.

Instance always_rejects_proper: Proper (RESet.E.eq ==> eq) always_rejects.
Proof. unfold Proper, respectful. intros.
  apply compare_re_eq_leibniz in H. crush.
Qed.

Lemma reset_always_rejects_corr rs: 
  reset_always_rejects rs = true -> forall ls, ~ in_re_set rs ls.
Proof. unfold reset_always_rejects, in_re_set. intros. intro H2.
  apply RESet.for_all_spec in H; [idtac | apply always_rejects_proper].
  unfold RESet.For_all in H. 
  generalize always_rejects_corr. crush_hyp.
Qed.


(* Definition reset_always_rejects (rs:RESet.t): bool := *)
(*   RESet.for_all always_rejects rs. *)



(** ** Properties of [pdrv_set] and [wpdrv] *)

Lemma pdrv_set_in: forall rs r a,
  RESet.In r (pdrv_set a rs) <->
  exists r', RESet.In r' rs /\ RESet.In r (pdrv a r').
Proof. split.
  Case "->". unfold pdrv_set.
    apply RESetP.fold_rec_nodep; intros.
    SCase "rs=empty". re_set_simpl.
    SCase "rs nonempty". 
      apply RESetP.FM.union_1 in H1; destruct H1; crush.
  Case "<-". unfold pdrv_set.
    apply RESetP.fold_rec_bis; intros.
      sim. apply H0. exists x. crush.
      sim; re_set_simpl.
      sim. apply RESet.union_spec.
        apply RESetP.FM.add_iff in H2; destruct H2.
          apply compare_re_eq_leibniz in H2. crush.
        crush.
Qed.

Lemma pdrv_set_trans: forall rs r a, 
  RESet.Subset rs (pdset r) -> RESet.Subset (pdrv_set a rs) (pdset r).
Proof. intros. intro r1; intro H2.
  apply pdrv_set_in in H2. destruct H2 as [r' [H4 H6]].
  apply pdrv_subset_pdset in H6.
  eauto using pdset_trans.
Qed.

Instance pdrv_set_subset: 
  forall a, Proper (RESet.Equal ==> RESet.Subset) (pdrv_set a).
Proof. unfold Proper, respectful. intros a rs1 rs2 H r H2.
  apply pdrv_set_in in H2. sim.
  apply pdrv_set_in. exists x. rewrite <- H. crush.
Qed.

Instance pdrv_set_equal: 
  forall a, Proper (RESet.Equal ==> RESet.Equal) (pdrv_set a).
Proof. unfold Proper, respectful. intros a rs1 rs2 H.
  apply RESetP.subset_antisym; rewrite H; reflexivity.
Qed.

Lemma pdrv_set_corr rs a s:
  in_re_set (pdrv_set a rs) s <-> in_re_set rs (a::s).
Proof. unfold in_re_set. split; intros.
  Case "->".
    destruct H as [r [H2 H4]].
    apply pdrv_set_in in H2.
    destruct H2 as [r' [H6 H8]].
    assert (H10:in_re_set (pdrv a r') s).
      unfold in_re_set. crush.
    apply pdrv_corr in H10.
    exists r'. crush.
  Case "<-".
    destruct H as [r [H2 H4]].
    apply pdrv_corr in H4.
    unfold in_re_set in H4.
    destruct H4 as [r' [H6 H8]].
    assert (RESet.In r' (pdrv_set a rs)).
      apply pdrv_set_in. crush.
    crush.
Qed.

Lemma wpdrv_corr: forall s1 s2 rs, 
  in_re_set (wpdrv s1 rs) s2 <-> in_re_set rs (s1 ++ s2).
Proof. induction s1. crush.
  intros. simpl.
  split; intros.
    apply IHs1 in H. apply pdrv_set_corr in H. trivial.
    apply IHs1. apply pdrv_set_corr. trivial.
Qed.
  
Lemma wpdrv_pdset_trans : forall w rs r, 
  RESet.Subset rs (pdset r) -> RESet.Subset (wpdrv w rs) (pdset r).
Proof. induction w; [auto | idtac].
  intros; simpl; eauto using pdrv_set_trans.
Qed.

Theorem wpdrv_subset_pdset : forall w r,
  RESet.Subset (wpdrv w (RESet.singleton r)) (pdset r).
Proof.  intros; apply wpdrv_pdset_trans.
  unfold pdset. intro r'; intros.
  apply RESetP.FM.singleton_iff in H.
  auto with set.
Qed.

Instance wpdrv_set_equal:
  forall s, Proper (RESet.Equal ==> RESet.Equal) (wpdrv s).
Proof. unfold Proper, respectful. induction s. crush.
  intros. simpl. apply IHs. rewrite H. reflexivity.
Qed.

Lemma wpdrv_app: forall w1 w2 rs,
  wpdrv (w1 ++ w2) rs = wpdrv w2 (wpdrv w1 rs). 
Proof. induction w1; intros. 
  simpl; trivial.
  simpl. rewrite IHw1. trivial.
Qed.

(** * Define [RESetSet], which is a set of RESet. 

  It supports (1) a powerset operation from RESet, and (2) a get_index
  operation that returns the index of a RESet. *)

Module POW := ListPowerSet RESet.

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
          inversion ok2. congruence.
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
     eauto using nth_error_some_lt.
  Qed.

  Lemma get_element_eq: forall s1 s2 n,
    elements s1 = elements s2 -> get_element n s1 = get_element n s2.
  Proof. unfold get_element; crush. Qed.

  Lemma get_element_ext s1 s2 n:
    elements_ext s1 s2 -> n < cardinal s1
      -> get_element n s2 = get_element n s1.
  Proof. unfold elements_ext, get_element. intros. sim.
    rewrite H. generalize nth_error_lt_app. crush.
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
    apply nth_error_some_lt in H2. auto.
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
      unfold elt, RESet.t in *.
      split; intros. 
      SCase "->". 
        use_lemma get_index_some_lt by eassumption.
        apply get_index_spec in H0. 
        unfold Coqlib.first_occur in H0. sim. trivial.
        apply get_index_spec; unfold Coqlib.first_occur.
        rewrite H. rewrite Coqlib.firstn_eq_lt by trivial.
        split; [crush | idtac].
          exists x. rewrite nth_error_lt_app by trivial. crush.
      SCase "<-".
        sim. apply get_index_spec in H1. apply get_index_spec.
        unfold Coqlib.first_occur in *.
        sim. 
          erewrite <- Coqlib.firstn_eq_lt by trivial.
            rewrite H in H1. eassumption.
          exists x. erewrite <- nth_error_lt_app by trivial.
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

Section DFA.

  (** The initial regexp from which we will build the DFA *)
  Variable r: regexp.

  Record DFA := { 
    dfa_num_states : nat ; 
    dfa_states : RESS.t ; 
    dfa_transition : list (list nat) ; 
    dfa_accepts : list bool ;
    dfa_rejects : list bool
  }.

  Hint Rewrite Coqlib.nth_error_app_eq using omega.

  (** A state is a set of regexps, corresponding to partial derivatives of
      the starting regexp w.r.t. some word. *)
  Definition state := RESet.t.

  (** a set of states *) 
  Definition states := RESS.t.

  Definition state_is_wf (s:state) : Prop := 
    exists w, RESet.Equal s (wpdrv w (RESet.singleton r)).
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

  Definition wpdrv_wf (w: list char_p) (s: wf_state): wf_state.
    refine (exist _ (wpdrv w (proj1_sig s)) _).
    unfold state_is_wf; intros. 
    destruct s as [s [w1 H]].
    exists (w1++w).
    rewrite wpdrv_app. simpl. rewrite H. reflexivity.
  Defined.

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

  Lemma get_element_wfs_ext n ss ss': 
    wfs_ext ss ss' -> n < cardinal_wfs ss
      -> RESS.get_element n (proj1_sig ss') = RESS.get_element n (proj1_sig ss).
  Proof. intros. apply wfs_ext_elements_ext in H. 
    apply RESS.get_element_ext; auto.
  Qed.

  Lemma get_element_wfs_ext2: forall ss1 ss2 n e,
    wfs_ext ss1 ss2 -> RESS.get_element n (proj1_sig ss1) = Some e
      -> RESS.get_element n (proj1_sig ss2) = Some e.
  Proof. intros. use_lemma RESS.get_element_some_lt by eassumption.
    erewrite get_element_wfs_ext; eassumption.
  Qed.

  Definition get_index_wfs (s:wf_state) (ss:wf_states): option nat :=
    RESS.get_index (proj1_sig s) (proj1_sig ss).

  Definition get_element_wfs (n:nat) (ss:wf_states):
    {s:state | state_is_wf s /\ RESS.get_element n (proj1_sig ss) = Some s}
    + {n >= cardinal_wfs ss}.
    refine (let ge := RESS.get_element n (proj1_sig ss) in
            (match ge return RESS.get_element n (proj1_sig ss) = ge -> _
             with
               | Some s => fun H => inleft (exist _ s _)
               | None => fun H => inright _
             end) eq_refl).
    Case "state_is_wf s".
      split.
        destruct ss as [ss H2].
          apply H2.
          apply Coqlib.nth_error_in in H.
          assert (InA RESet.Equal s (RESS.elements ss)).
            apply In_InA. apply RESet.eq_equiv. assumption.
          apply RESS.elements_spec1. trivial.
        trivial.
    Case "n>=|ss|".
      apply nth_error_none in H. trivial.
  Defined.

  Opaque RESS.elements. 
  Lemma wfs_ext_add s ss1 ss2: 
    RESS.mem (proj1_sig s) (proj1_sig ss1) = false
    -> wfs_ext (add_wfs s ss1) ss2 -> wfs_ext ss1 ss2.
  Proof. unfold wfs_ext, elements_wfs. intros.
    destruct H0 as [ss H2].
    use_lemma RESSMP.elements_app_disjoint by eassumption.
    unfold add_set_wfs, add_wfs in *. simpl in *.
    rewrite RESS.add_elements_2 in H2 by assumption.
    exists (add_set_wfs (singleton_wfs s) ss).
    use_lemma RESS.disjoint_add_add_set by eassumption.
    use_lemma RESS.disjoint_add_singleton by eassumption.
    simpl. rewrite RESS.add_set_elements by assumption.
    crush.
  Qed.

  Lemma get_element_add_wfs_ext s ss ss' : 
    wfs_ext (add_wfs s ss) ss' 
      -> RESS.mem (proj1_sig s) (proj1_sig ss) = false
      -> RESS.get_element (cardinal_wfs ss) (proj1_sig ss') = Some (proj1_sig s).
  Proof. unfold wfs_ext, elements_wfs, add_wfs, cardinal_wfs. simpl. intros.
    destruct H as [ss1 H2].
    unfold RESS.get_element.
    rewrite RESS.add_elements_2 in H2 by assumption.
    rewrite H2.
    rewrite app_ass.
    assert (H12:cardinal_wfs ss = length (RESS.elements (proj1_sig ss))).
      unfold cardinal_wfs. rewrite POW.MM.cardinal_spec. omega.
    rewrite Coqlib.nth_error_app_eq by crush.
    rewrite <- app_comm_cons. 
    crush.
  Qed.
  Transparent RESS.elements. 


  (** Generate the transition matrix row for the state s.  In general, this
      will add new states. *)
  Fixpoint gen_row' (n:nat) (s:wf_state) (ss:wf_states) (tk_id:token_id) : 
    (wf_states * list nat) :=
    match n with
      | 0 => (ss, nil)
      | S n' =>
        let s1 := wpdrv_wf (token_id_to_chars tk_id) s in
        match get_index_wfs s1 ss with
          | Some n =>
            let (ss1, row) := gen_row' n' s ss (1 + tk_id) in
            (ss1, n :: row)
          | None =>
            let (ss1, row) := gen_row' n' s (add_wfs s1 ss) (1 + tk_id) in
            (ss1, cardinal_wfs ss :: row)
        end
    end.

  Definition gen_row (s:wf_state) (ss:wf_states) : (wf_states * list nat) := 
    gen_row' num_tokens s ss 0.

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

  (** Build a transition table by closing off the reachable states.  The
      invariant is that we've closed the table up to the [next_state] and
      have generated the appropriate transition rows for the states in the
      range 0..next_state-1.  So we first check to see if [next_state] is
      outside the range of states, and if so, we are done.  Otherwise, we
      generate the transition row for the derivative at the position
      [next_state], add it to the list of rows, and then move on to the
      next position in the list of states.  Note that when we generate the
      transition row, we may end up adding new states.  *)
  Unset Implicit Arguments.
  Require Import Coq.Program.Wf.
  Definition extract_wf_state (ss: wf_states) (n:nat)
             (s: {s:state | state_is_wf s
                            /\ RESS.get_element n (proj1_sig ss) = Some s})
    : wf_state.
    destruct s. destruct a.
    refine (exist _ x _).
    apply H.
  Defined.
  Program Fixpoint build_table' (ss:wf_states) (rows:list (list nat)) (next_state:nat)
           {wf build_table_metric next_state} :
    wf_states * list (list nat) :=
    match get_element_wfs next_state ss with
       | inleft s => 
         let (ss1, row1) := gen_row (extract_wf_state _ _ s) ss in
         build_table' ss1 (rows ++ (row1::nil)) (1 + next_state)
         (* let gr := gen_row (extract_wf_state _ _ s) ss in *)
         (* build_table' (fst gr) (rows ++ ((snd gr)::nil)) (1 + next_state) *)
       | inright _ => (ss, rows)
    end.
  Next Obligation.
    destruct Heq_anonymous.
    apply RESS.get_element_some_lt in e.
    eauto using build_table_metric_dec.
  Defined.
  Next Obligation.
    apply measure_wf. apply limit_nat_wf.
  Defined.
  Set Implicit Arguments.

  (* gtan: the following QED doesn't finish for some reason *)
  (* Unset Implicit Arguments. *)
  (* Require Import Coq.Program.Wf. *)
  (* Require Import Recdef. *)
  (* Function build_table' (ss:wf_states) (rows:list (list nat)) (next_state:nat) *)
  (*          {wf build_table_metric next_state} : *)
  (*   wf_states * list (list nat) := *)
  (*   match get_element_wfs next_state ss with *)
  (*      | inleft s =>  *)
  (*        let gr := gen_row (extract_wf_state _ _ s) ss in *)
  (*        build_table' (fst gr) (rows ++ ((snd gr)::nil)) (1 + next_state) *)
  (*      | inright _ => (ss, rows) *)
  (*   end. *)
  (* Case "descreasing metric". *)
  (*   intros. *)
  (*   clear teq. *)
  (*   destruct s as [s [H H2]]. *)
  (*   eauto using build_table_metric_dec. *)
  (* Case "measure wf". *)
  (*   apply limit_nat_wf. *)
  (* Qed. *)
  (* Set Implicit Arguments. *)

  Import WfExtensionality.
  Lemma build_table'_unfold (ss:wf_states) rows next_state:
    build_table' ss rows next_state  =
    match get_element_wfs next_state ss with
       | inleft s => 
         let (ss1, row1) := gen_row (extract_wf_state _ _ s) ss in
         build_table' ss1 (rows ++ (row1::nil)) (1 + next_state)
       | inright _ => (ss, rows)
    end.
  Proof.
   unfold build_table' at 1.
   unfold_sub build_table'_func 
     (build_table'_func 
        (existT (fun _ : wf_states => {_ : list (list nat) & nat}) ss
                (existT (fun _ : list (list nat) => nat) rows next_state))).
   simpl.
   destruct (get_element_wfs next_state ss); trivial.  
  Qed.

  (* Recursive Extraction build_table'. *)

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

  (** We start with the initial [astgram] in state 0 and then try to close 
      off the table. *)
  Definition build_table := 
    build_table' ini_states nil 0. 
 
  Definition build_accept_table (ss:wf_states) : list bool := 
    List.map reset_nullable (RESS.elements (proj1_sig ss)).

  Definition build_rejects (ss:wf_states) : list bool := 
    List.map reset_always_rejects (RESS.elements (proj1_sig ss)).

  Definition build_dfa: DFA := 
    match build_table with 
      | (wstates, table) => 
         {| dfa_num_states := cardinal_wfs wstates ; 
            dfa_states := proj1_sig wstates ; 
            dfa_transition := table ;
            dfa_accepts := build_accept_table wstates ; 
            dfa_rejects := build_rejects wstates |}
    end.

  (** This is the main loop-invariant for [gen_row'].  Given a state [s],
      a list of states [ss], and a token number [n], running [gen_row' n s ss
      (num_tokens - n)] yields a list of states [ss2] and transition-table
      [row2] such that the length of [row2] is [n], [ss2] is an extension of
      [ss], and for all [i], the [ith] element of [ss2] is the [wpdrv]
      of [s] with respect to the token [i+num_tokens-n]. *)
  Lemma gen_row'_prop: forall n s ss,
    n <= num_tokens -> 
    match gen_row' n s ss (num_tokens - n) with 
      | (ss2, row2) => 
        length row2 = n /\ wfs_ext ss ss2 /\
        forall i, 
          i < n -> 
          match RESS.get_element (nth i row2 num_tokens) (proj1_sig ss2) with
            | Some s' => 
              RESet.Equal s'
                (wpdrv (token_id_to_chars (i + num_tokens - n)) (proj1_sig s))
            | None => False
          end
    end.
  Proof. induction n.
    Case "base". intros. compute [gen_row'].
      repeat split; crush. reflexivity.
    Case "S n". intros.
      remember_destruct_head as gr.
      Opaque token_id_to_chars num_tokens.
      simpl in Hgr.
      replace (S (num_tokens - S n)) with (num_tokens - n) in Hgr by omega.
      remember (wpdrv_wf (token_id_to_chars (num_tokens - S n)) s) as s'.
      remember_rev (get_index_wfs s' ss) as gi.
      destruct gi.
      SCase "s' in ss".
        remember_destruct_head in Hgr as grr.
        use_lemma (IHn s ss) by omega.
        rewrite Hgrr in H0.
        split. crush.
          destruct H0 as [H2 [H4 H8]].
          split. crush. 
          destruct i; intros.
          SSCase "i=0".
            apply RESS.get_index_get_element in Hgi.
            destruct Hgi as [e' [H10 H12]].
            crush. erewrite get_element_wfs_ext2 by eassumption.
            crush. reflexivity.
          SSCase "S i". 
            use_lemma (H8 i) by omega. crush.
      SCase "s' notin ss".
        remember_destruct_head in Hgr as grr.
        use_lemma (IHn s (add_wfs s' ss)) by omega.
        rewrite Hgrr in H0.
        split. crush. 
          inversion Hgr. subst w0 l. clear Hgr.
          destruct H0 as [H2 [H4 H8]].
          use_lemma RESS.get_index_none by crush.
          split. eapply wfs_ext_add; eassumption.
            destruct i; intro.
            SSSCase "i=0". simpl.  
              erewrite get_element_add_wfs_ext by eassumption.
              crush. reflexivity.
            SSSCase "S i".
              use_lemma (H8 i) by omega. crush.
  Qed.

  Lemma gen_row_prop: forall s ss,
    match gen_row s ss with 
      | (ss2, row2) => 
        length row2 = num_tokens /\ wfs_ext ss ss2 /\
        forall i, 
          i < num_tokens -> 
          match RESS.get_element (nth i row2 num_tokens) (proj1_sig ss2) with
            | Some s' => 
              RESet.Equal s' (wpdrv (token_id_to_chars i) (proj1_sig s))
            | None => False
          end
    end.
  Proof. unfold gen_row. intros.
    use_lemma (@gen_row'_prop num_tokens s ss) by omega.
    rewrite minus_diag in H.
    remember_destruct_head as gr.
    crush.
    use_lemma (H2 i) by assumption. 
    replace (i+num_tokens-num_tokens) with i in H3 by omega.
    crush.
  Qed.

  (** This is the main invariant for the [build_table] routine.  Given a well-formed
      list of states [ss] and a list of transition-table rows [rows], then for 
      all [i < n], [ss(i)] and [r(i)] are defined, and the row [r(i)] is well-formed
      with respect to the state [ss(i)]. *)
  Definition build_table_inv (ss: wf_states) (rows: list (list nat)) n := 
     forall i, i < n -> 
       match RESS.get_element i (proj1_sig ss), nth_error rows i with 
         | Some s, Some row => 
           length row = num_tokens /\ 
           forall j, j < num_tokens -> 
             match RESS.get_element (nth j row num_tokens) (proj1_sig ss) with 
               | Some s' => 
                 RESet.Equal s' (wpdrv (token_id_to_chars j) s)
               | None => False
             end
         | _, _ => False
       end.

  Lemma build_table_inv_imp ss rows n :
    build_table_inv ss rows n -> n <= cardinal_wfs ss /\ n <= length rows.
  Proof. 
    unfold build_table_inv ; destruct n. 
      auto with arith.
      intros. assert (n < S n) by omega.
        generalize (H n H0).
        remember_destruct_head as ge; [idtac | crush].
        remember_destruct_head as ne; [idtac | crush].
        intros.
        apply RESS.get_element_some_lt in Hge.
        apply nth_error_some_lt in Hne.
        crush.
  Qed.

  Lemma gen_row_build_table_inv n ss
        ss1 rows row1:
    n = length rows ->
    match get_element_wfs n ss with
      | inleft s =>
        gen_row (extract_wf_state ss n s) ss = (ss1, row1)
         -> build_table_inv ss rows n
         -> build_table_inv ss1 (rows ++ row1 :: nil) (1 + n)
      | inright _ => True
    end.
  Proof.
    remember_rev (get_element_wfs n ss) as gew.
    destruct gew; [idtac | crush]. clear Hgew.
    intros.
    use_lemma build_table_inv_imp by eassumption.
    unfold build_table_inv in *.
    use_lemma (gen_row_prop (extract_wf_state ss n s) ss) by eassumption.
    rewrite H0 in H3.
    intros.
    destruct (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H4)); sim.
    Case "i<n".
      rewrite (get_element_wfs_ext H6) by omega.
      rewrite nth_error_lt_app by omega.
      use_lemma H1 by eassumption.
      remember_destruct_head as ge; [idtac | crush].
      remember_destruct_head as ne; [idtac | crush].
      split. crush.
        intros. sim.
        use_lemma H11 by eassumption.
        remember_destruct_head in H12 as ge2; [idtac | crush].
        use_lemma get_element_wfs_ext2 by eassumption.
        crush. reflexivity.
    Case "i=n". subst i.
      destruct s as [s [H20 H22]].
      assert (n < cardinal_wfs ss).
        use_lemma RESS.get_element_some_lt by eassumption. 
        unfold cardinal_wfs. trivial.
      rewrite (get_element_wfs_ext H6) by assumption.
      crush.
  Qed.

     
   (** This lemma establishes that the [build_table'] loop maintains the
       [build_table_inv] and only adds to the states and rows of the table. *)
  Lemma build_table'_prop: forall n ss rows,
     n = length rows -> build_table_inv ss rows n ->
     match build_table' ss rows n with 
       | (ss', rows') => 
         length rows' = cardinal_wfs ss' /\ 
         build_table_inv ss' rows' (length rows') /\ 
         wfs_ext ss ss' /\ exists rows1, rows' = rows ++ rows1
     end.
  Proof. induction n using (well_founded_ind (limit_nat_wf max_pdrv)).
    intros. remember_head as gw.
    destruct gw as [ss' rows'].
    rewrite build_table'_unfold in Hgw.
    remember_rev (get_element_wfs n ss) as ge.
    destruct ge.
    Case "ss[n] exists".
      remember_head in Hgw as gr.
      destruct gr as [ss1 row1].
      use_lemma (@gen_row_build_table_inv n ss ss1 rows row1) by eassumption.
      rewrite Hge in H2.
      use_lemma (gen_row_prop (extract_wf_state ss n s) ss) by eassumption.
      rewrite Hgr in H3.
      remember (rows ++ row1 :: nil) as rows1.
      assert (n < cardinal_wfs ss).
        destruct s as [s [H8 H10]]. 
        use_lemma RESS.get_element_some_lt by eassumption. trivial.
      use_lemma build_table_metric_dec by eassumption. 
      assert (S n = length rows1) by crush.
      assert (build_table_inv ss1 rows1 (1 + n)) by crush.
      use_lemma H by eassumption.
      simpl in Hgw.
      rewrite Hgw in H8.
      crush. reflexivity.
    Case "ss[n] not exists".
      use_lemma build_table_inv_imp by eassumption.
      crush. reflexivity.
        exists nil. crush.
  Qed.

  Lemma build_table_inv_ini: build_table_inv ini_states nil 0.
  Proof. unfold build_table_inv. crush. Qed.

  Lemma build_table_prop :
    match build_table with
      | (ss, rows) => 
        length rows = cardinal_wfs ss /\
        build_table_inv ss rows (length rows) /\
        wfs_ext ini_states ss
    end.
  Proof. generalize build_table_inv_ini. intro. unfold build_table. 
    generalize (@build_table'_prop 0 ini_states nil). intro.
    use_lemma H0 by crush.
    remember_destruct_head as bt. crush.
  Qed.

  (** This predicate captures the notion of a correct [DFA] with respect to
      an initial astgram [r].  In essence, it says that the lengths of all of
      the lists is equal to [dfa_num_states d], that {r} is at [dfa_states(0)],
      each row of the [dfa_transition] table is well-formed, that 
      [accepts(i)] holds iff the corresponding state accepts the empty string,
      and when [rejects(i)] is true, the corresponding state rejects all strings. *)
  Definition wf_dfa (d:DFA) := 
    let num_states := dfa_num_states d in
    let states := dfa_states d in 
    let transition := dfa_transition d in 
    let accepts := dfa_accepts d in 
    let rejects := dfa_rejects d in 
    num_states = RESS.cardinal states /\ 
    num_states = length transition /\ 
    num_states = length accepts /\ 
    num_states = length rejects /\ 
    RESS.get_element 0 states = Some (proj1_sig ini_state) /\
    forall i, i < num_states -> 
      match RESS.get_element i states with
        | Some s =>
          let acc := nth i accepts false in 
          let rej := nth i rejects false in 
          let row := nth i transition nil in 
          length row = num_tokens /\
          (acc = true <-> in_re_set s nil) /\
          (rej = true -> forall ls, ~ in_re_set s ls) /\
          (forall j, j < num_tokens ->
            nth j row num_tokens < num_states /\
            match RESS.get_element (nth j row num_tokens) states with
              | Some s' => 
                RESet.Equal s' (wpdrv (token_id_to_chars j) s)
              | None => False
            end)
        | None => False
      end.

  Hint Rewrite Coqlib.list_length_map.

  (** [build_dfa] is correct. *)
  Lemma build_dfa_wf: wf_dfa build_dfa.
  Proof. generalize build_table_prop. 
    unfold build_dfa, build_table. intros.
    remember_head as bt. 
    destruct bt as [ss rows]. 
    unfold wf_dfa. simpl.
    unfold build_accept_table, build_rejects.
    crush.
    erewrite get_element_wfs_ext by crush; crush.
    unfold build_table_inv in *.
    use_lemma H1 by crush.
    remember_destruct_head as ge; [idtac | false_elim].
    remember_destruct_head in H3 as ne; [idtac | false_elim].
    split. erewrite Coqlib.nth_error_some_nth by eassumption; crush.
    split.
    Case "accept states correct".
      change false with (reset_nullable RESet.empty).
      rewrite map_nth.
      erewrite Coqlib.nth_error_some_nth by eassumption.
      apply reset_nullable_corr.
    split.
    Case "reject states correct".
      change false with (reset_always_rejects (RESet.singleton aEps)).
      rewrite map_nth.
      erewrite Coqlib.nth_error_some_nth by eassumption.
      apply reset_always_rejects_corr.
    Case "invariant forall j, ...".
      intros. destruct H3 as [H5 H6].
      use_lemma H6 by eassumption.
      remember_destruct_head in H3 as ge2; [idtac | false_elim].
      assert (H8: nth i rows nil = l).
        auto using Coqlib.nth_error_some_nth. 
      rewrite H8.
      use_lemma RESS.get_element_some_lt by eassumption.
      split. assumption.
        rewrite Hge2. crush.
  Qed.

End DFA.

(* Definition test0:= aEps. *)
(* Definition test1 := aChar true. *)
(* Definition test2 := aCat (aChar true) (aChar false). *)
(* Definition test3 := aCat (aChar false)  *)
(*                          (aCat (aChar false) *)
(*                                (aCat (aChar false) *)
(*                                (aCat (aChar false) *)
(*                                (aCat (aChar false) *)
                               
(*                                (aCat (aChar false) *)
(*                                (aCat (aChar false) (aChar false))))))). *)

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
      RESet.Equal rs
        (wpdrv (flat_map token_id_to_chars ts1) (proj1_sig (ini_state r))) ->
      Forall (fun t => t < num_tokens) ts2 ->
      if run_dfa d st ts2 then
        in_regexp r (flat_map token_id_to_chars (ts1 ++ ts2))
      else ~ in_regexp r (flat_map token_id_to_chars (ts1 ++ ts2)).
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
      assert (H20: RESet.Equal e
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
        in_regexp r (flat_map token_id_to_chars ts)
      else ~ in_regexp r (flat_map token_id_to_chars ts).
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
            in_regexp r (flat_map token_id_to_chars ts1) /\
            forall ts3 ts4,
              length ts3 < length ts1 ->
              ts = ts3 ++ ts4 -> 
              ~ in_regexp r (flat_map token_id_to_chars ts3)
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

Definition par2rec t (g:grammar t) : astgram := 
  let (ag, _) := split_astgram g in ag.
