(** * Define a series of augmented MSets. *)

Require Coqlib.
Require Import CommonTacs.
Set Implicit Arguments.

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
