Require Import MSets.MSetInterface.
Require Import MSets.MSetProperties.
Require Import MSets.MSetAVL.

Require Import Structures.OrdersAlt.

Require Import Xform.
Require Import Regexp.

Require Import CommonTacs.
Require Import Coqlib.  (* for proof_irrelevance *)

Set Implicit Arguments.

(** A set of regexps paired with xforms *)
Module Type RESetXform.
  Include WSetsOn REOrderedType.

  (* note: in the rest t is the type for RESets *)

  (** Given a RESet grammar, returns the types of values returned by the
      grammar *)
  Parameter re_set_type: t -> type.

  Definition rs_xf_pair (ty:type) := {rs : t & re_set_type rs ->> List_t ty }.

  Definition re_xf_pair (ty:type) := {r : regexp & regexp_type r ->> List_t ty}.

  Parameter in_re_set: 
    forall (rs:t), list char_t -> interp (re_set_type rs) -> Prop.

  Definition in_re_xform ty (rx : re_xf_pair ty) s (v:interp ty) := 
    let (r,x) := rx in 
    exists v', in_regexp r s v' /\ List.In v (xinterp x v').

  Definition in_re_set_xform ty (rx : rs_xf_pair ty) s (v:interp ty) := 
    let (rs, f) := rx in 
    exists v', in_re_set rs s v' /\ List.In v (xinterp f v').

  Parameter in_re_set_empty : forall rs v, not (in_re_set empty rs v).

  (* the following type for union_xform is motivated by the case of doing
     partial derivatives over r1+r2
        pdrv(a, r1+r2) =
          let (rs1, f1) = pdrv(a, r1) in
          let (rs2, f2) = pdrv(a, r2) in
            union_xform (rs1, f1) (rs2, f2)
  *)
  Parameter union_xform: forall ty1,
    rs_xf_pair ty1 -> rs_xf_pair ty1 -> rs_xf_pair ty1.
  (* note: def equality may not be necessary here *)
  Parameter union_xform_erase: forall ty1 rx1 rx2,
    projT1 (@union_xform ty1 rx1 rx2) = union (projT1 rx1) (projT1 rx2).
  Parameter union_xform_corr: forall ty rs1 rs2 str v,
    in_re_set_xform (@union_xform ty rs1 rs2) str v <-> 
    in_re_set_xform rs1 str v \/ in_re_set_xform rs2 str v.

  Parameter empty_xform: forall ty, rs_xf_pair ty.
  Parameter empty_xform_erase: forall ty, projT1 (@empty_xform ty) = empty.
  Parameter empty_xform_corr: forall ty (s : list char_t) (v : interp ty),
    ~ in_re_set_xform (empty_xform ty) s v.

  Parameter singleton_xform: forall r:regexp, rs_xf_pair (regexp_type r).
  Parameter singleton_xform_erase: forall r, 
    projT1 (@singleton_xform r) = (singleton r).
  Parameter singleton_xform_corr : forall r s v, 
    in_re_set_xform (singleton_xform r) s v <-> in_regexp r s v.


  (* note: the following operation is motivated by the case of doing
     partial derives over "r1 cat r2" when r1 is not nullable.
        pdrv(a, r1 r2) =
          let (rs1, f1) := pdrv (a, r1) in
            cat_re_xform (rs1, f1) r2
  *)
  (* Parameter cat_re_xform: forall ty, *)
  (*   rs_xf_pair ty -> forall r:regexp, rs_xf_pair (Pair_t ty (regexp_type r)). *)
  (* can also state a erasure lemma, need to bring the set_cat_re definition,
     which is in NewRecognizer.v *)

End RESetXform.

Module RESet := MSetAVL.Make REOrderedType.
Module RESETXFORM <: RESetXform.
  Include RESet.  

  Definition re_xf_pair (ty:type) := {r : regexp & regexp_type r ->> List_t ty}.

  Definition in_re_xform ty (rx : re_xf_pair ty) s (v:interp ty) := 
    let (r,x) := rx in 
    exists v', in_regexp r s v' /\ List.In v (xinterp x v').

  Fixpoint tree_to_regexp (t : Raw.tree) : regexp := 
    match t with 
      | Raw.Leaf => Zero
      | Raw.Node i lft r rgt => Alt (tree_to_regexp lft) (Alt r (tree_to_regexp rgt))
    end.

  Definition tree_type (t : Raw.tree) : type := 
    regexp_type (tree_to_regexp t).

  Definition in_tree (t: Raw.tree) (str : list char_t) (v: interp (tree_type t)) := 
    in_regexp (tree_to_regexp t) str v.

  Definition tree_xf_pair (ty:type) := { t : Raw.tree & tree_type t ->> List_t ty }.

  Definition in_tree_xform ty (tx : tree_xf_pair ty) str (v : interp ty) := 
    let (t,x) := tx in 
    exists v', in_tree t str v' /\ List.In v (xinterp x v').

  Definition re_set_type (rs : t) : type := tree_type (this rs). 

  Definition in_re_set (rs : t) (str : list char_t) (v : interp (re_set_type rs)) := 
    in_tree (this rs) str v.
  
  Lemma in_re_set_empty : forall s v, not (in_re_set empty s v).
  Proof.
    simpl. intros. destruct v.
  Qed.

  Definition rs_xf_pair (ty:type) := {rs : t & re_set_type rs ->> List_t ty }.

  Definition in_re_set_xform ty (rx : rs_xf_pair ty) s (v:interp ty) := 
    let (rs, f) := rx in 
    exists v', in_re_set rs s v' /\ List.In v (xinterp f v').

  Definition empty_xform (ty:type) : rs_xf_pair ty := 
    existT _ empty xzero.
  
  Lemma empty_xform_erase : forall ty, projT1 (@empty_xform ty) = empty.
    auto.
  Qed.

  Lemma empty_xform_corr ty (str : list char_t) (v : interp ty) : 
    ~ in_re_set_xform (empty_xform ty) str v.
  Proof.
    unfold in_re_set_xform. unfold not. crush. destruct x.
  Qed.

  Definition singleton_xform (r:regexp) : rs_xf_pair (regexp_type r) := 
    existT _ (singleton r) (xcons (xmatch xzero (xmatch xid xzero)) xempty).

  Lemma singleton_xform_erase : forall r, projT1 (@singleton_xform r) = (singleton r).
    auto.
  Qed.

  Lemma singleton_xform_corr : forall r s v, 
    in_re_set_xform (singleton_xform r) s v <-> in_regexp r s v.
  Proof.
    unfold in_re_set_xform. simpl. crush. destruct x. destruct v.
    destruct s0. unfold in_re_set, in_tree in H. simpl in H. 
    repeat in_regexp_inv. destruct v.
    exists (inr (inl v)). unfold in_re_set, in_tree. simpl.
    eauto.
  Qed.

  Open Scope Z_scope.

  (* These definitions parallel those in the Raw module, but add in an xform. *)
  Definition create_xform ty (l:Raw.tree) (fl : tree_type l ->> List_t ty)
                             (x:regexp) (fx : regexp_type x ->> List_t ty)
                             (r:Raw.tree) (fr : tree_type r ->> List_t ty) : 
    tree_xf_pair ty := 
    existT _ (Raw.Node (Int.Z_as_Int.plus (Int.Z_as_Int.max (Raw.height l) 
                                                            (Raw.height r)) 1)
                       l x r) (xmatch fl (xmatch fx fr)).

  Lemma create_xform_erase : 
    forall ty l fl x fx r fr, projT1 (@create_xform ty l fl x fx r fr) = Raw.create l x r.
    auto.
  Qed.

  Opaque xcross xmap xapp xcomp xmatch xflatten.

  Ltac xmatch_simpl_hyp := 
    repeat 
      match goal with
        | [ H : context[xinterp (xmatch ?f1 ?f2) ?v] |- _ ] => 
          rewrite (xmatch_corr f1 f2) in H ; simpl in H
        | [H:context[xcomp ?X1 ?X2] |- _] => 
          rewrite (xcomp_corr X1 X2) in H ; simpl in H
      end.

  Ltac xmatch_simpl := 
    repeat
      match goal with
        | [ |- context[xinterp (xmatch ?f1 ?f2) ?v] ] => 
          rewrite (xmatch_corr f1 f2) ; simpl
        | [|- context[xcomp ?X1 ?X2]] => rewrite (xcomp_corr X1 X2); simpl
      end.

  Lemma create_xform_corr ty l fl x fx r fr str v : 
    in_tree_xform (@create_xform ty l fl x fx r fr) str v <-> 
    in_tree_xform (existT _ l fl) str v \/
    in_re_xform (existT _ x fx) str v \/
    in_tree_xform (existT _ r fr) str v.
  Proof.
    simpl. unfold in_tree. crush.
    repeat in_regexp_inv ; xmatch_simpl_hyp ; crush.
    econstructor ; crush ; xmatch_simpl ; crush.
    econstructor ; crush ; xmatch_simpl ; crush.
    econstructor ; crush ; xmatch_simpl ; crush.
  Qed.

  Definition assert_false_xform := create_xform.

  Lemma assert_false_xform_erase : 
    forall t l fl x fx r fr, projT1 (@assert_false_xform t l fl x fx r fr) = 
                             Raw.assert_false l x r.
    auto.
  Qed.

  Lemma assert_false_xform_corr ty l fl x fx r fr str v : 
    in_tree_xform (@create_xform ty l fl x fx r fr) str v <-> 
    in_tree_xform (existT _ l fl) str v \/
    in_re_xform (existT _ x fx) str v \/
    in_tree_xform (existT _ r fr) str v.
  Proof.
    apply (create_xform_corr l fl x fx r fr str v).
  Qed.

  Definition bal_xform t (l:Raw.tree) (fl : tree_type l ->> List_t t)
                         (x:regexp) (fx : regexp_type x ->> List_t t)
                         (r:Raw.tree) (fr : tree_type r ->> List_t t) : 
    tree_xf_pair t :=
    let hl := Raw.height l in 
    let hr := Raw.height r in 
    if Int.Z_as_Int.gt_le_dec hl (Int.Z_as_Int.plus hr 2) then
      match l return tree_type l ->> List_t t -> {s:Raw.tree & tree_type s ->> List_t t}
      with 
        | Raw.Leaf => fun _ => assert_false_xform l fl x fx r fr
        | Raw.Node i ll lx lr => 
          if Int.Z_as_Int.ge_lt_dec (Raw.height ll) (Raw.height lr) then
            fun fl0 =>  
              let (r',fr') := (create_xform lr (xcomp (xcomp xinr xinr) fl0) x fx r fr) in 
              create_xform ll (xcomp xinl fl0) lx (xcomp (xcomp xinl xinr) fl0) r' fr'
          else 
            match lr return tree_type (Raw.Node i ll lx lr) ->> List_t t -> 
                            { s:Raw.tree & tree_type s ->> List_t t}
            with
              | Raw.Leaf => fun _ => assert_false_xform l fl x fx r fr
              | Raw.Node j lrl lrx lrr => 
                fun fl0 => 
                  let (l',fl') := 
                      create_xform ll (xcomp xinl fl0) 
                                   lx (xcomp (xcomp xinl xinr) fl0) 
                                   lrl (xcomp (xcomp xinl (xcomp xinr xinr)) fl0) in 
                  let (r',fr') := 
                      create_xform lrr 
                                   (xcomp (xcomp xinr (xcomp xinr (xcomp xinr xinr))) fl0) 
                                   x fx r fr in 
                  create_xform l' fl' 
                               lrx (xcomp (xcomp xinl (xcomp xinr (xcomp xinr xinr))) fl0)
                               r' fr'
            end 
      end fl
    else if Int.Z_as_Int.gt_le_dec hr (Int.Z_as_Int.plus hl 2) then 
      match r return tree_type r ->> List_t t -> {rs:Raw.tree & tree_type rs ->> List_t t}
      with 
        | Raw.Leaf => fun _ => assert_false_xform l fl x fx r fr
        | Raw.Node i rl rx rr => 
          if Int.Z_as_Int.ge_lt_dec (Raw.height rr) (Raw.height rl) then 
            fun fr0 => 
              let (l',f') := create_xform l fl x fx rl (xcomp xinl fr0) in 
              create_xform l' f' rx (xcomp (xcomp xinl xinr) fr0) 
                           rr (xcomp (xcomp xinr xinr) fr0)
          else 
            match rl return (tree_type (Raw.Node i rl rx rr)) ->> List_t t -> 
                            {rs:Raw.tree & tree_type rs ->> List_t t}
            with 
              | Raw.Leaf => fun _ => assert_false_xform l fl x fx r fr
              | Raw.Node j rll rlx rlr => 
                fun fr0 => 
                  let (l',fl') := 
                      create_xform l fl x fx rll (xcomp (xcomp xinl xinl) fr0) in 
                  let (r',fr') := 
                      create_xform rlr (xcomp (xcomp xinr (xcomp xinr xinl)) fr0)
                                   rx (xcomp (xcomp xinl xinr) fr0)
                                   rr (xcomp (xcomp xinr xinr) fr0) in 
                  create_xform l' fl' rlx (xcomp (xcomp xinl (xcomp xinr xinl)) fr0) r' fr'
            end
      end fr
         else create_xform l fl x fx r fr.

  Lemma bal_xform_erase : 
    forall t l fl x fx r fr, projT1 (@bal_xform t l fl x fx r fr) = Raw.bal l x r.
  Proof.
    intros. unfold bal_xform, Raw.bal.
    replace 2 with (Int.Z_as_Int._2) ; auto.
    destruct (Int.Z_as_Int.gt_le_dec (Raw.height l) (Int.Z_as_Int.plus (Raw.height r) Int.Z_as_Int._2)).
    destruct l. apply assert_false_xform_erase.
    destruct (Int.Z_as_Int.ge_lt_dec (Raw.height l1) (Raw.height l2)).
    remember (create_xform l2 (xcomp (xcomp xinr xinr) fl) x fx r fr) as e.
    destruct e as [r' fr']. rewrite (create_xform_erase). 
    replace (Raw.create l2 x r) with r' ; auto.
    assert (r' = projT1 (existT (fun s:Raw.tree => tree_type s ->> List_t t0) r' fr')).
    auto.
    rewrite Heqe in H. rewrite (create_xform_erase) in H. auto.
    destruct l2. apply assert_false_xform_erase.
    remember (create_xform l1 (xcomp xinl fl) t2 (xcomp (xcomp xinl xinr) fl)
                           l2_1 (xcomp (xcomp xinl (xcomp xinr xinr)) fl)) as e1.
    remember (create_xform l2_2 (xcomp (xcomp xinr (xcomp xinr (xcomp xinr xinr))) fl) 
                           x fx r fr) as e2.
    destruct e1 as [l' fl']. destruct e2 as [r' fr'].
    rewrite create_xform_erase.
    replace (l') with (projT1 (existT (fun s => tree_type s->>List_t t0) l' fl')) ; auto.
    rewrite Heqe1. rewrite create_xform_erase.
    replace (r') with (projT1 (existT (fun s => tree_type s ->> List_t t0) r' fr')) ; auto.
    rewrite Heqe2. rewrite create_xform_erase. auto.
    destruct (Int.Z_as_Int.gt_le_dec (Raw.height r) 
                                     (Int.Z_as_Int.plus (Raw.height l) Int.Z_as_Int._2)).
    destruct r. apply assert_false_xform_erase.
    destruct (Int.Z_as_Int.ge_lt_dec (Raw.height r2) (Raw.height r1)).
    remember (create_xform l fl x fx r1 (xcomp xinl fr)) as e.
    destruct e. rewrite create_xform_erase.
    replace x0 with (projT1 (existT (fun s => tree_type s ->>List_t t0) x0 x1)) ; auto.
    rewrite Heqe. rewrite create_xform_erase. auto.
    destruct r1. apply assert_false_xform_erase.
    remember (create_xform l fl x fx r1_1 (xcomp (xcomp xinl xinl) fr)) as e1.
    remember (create_xform r1_2 
                           (xcomp (xcomp xinr (xcomp xinr xinl)) fr) t2
                           (xcomp (xcomp xinl xinr) fr) r2 
                           (xcomp (xcomp xinr xinr) fr)) as e2.
    destruct e1 as [l' fl']. destruct e2 as [r' fr'].
    rewrite create_xform_erase. 
    replace l' with (projT1 (existT (fun s => tree_type s ->> List_t t0) l' fl')) ; auto.
    rewrite Heqe1. rewrite create_xform_erase.
    replace r' with (projT1 (existT (fun s => tree_type s ->> List_t t0) r' fr')) ; auto.
    rewrite Heqe2. rewrite create_xform_erase. auto.
    apply create_xform_erase.
  Qed.

  Lemma bal_xform_corr1 ty l fl x fx r fr str v : 
    in_tree_xform (@bal_xform ty l fl x fx r fr) str v -> 
    in_tree_xform (existT _ l fl) str v \/ 
    in_re_xform (existT _ x fx) str v \/
    in_tree_xform (existT _ r fr) str v.
  Proof.
    Ltac reduce_if_hyp := 
    match goal with 
      | [ H : context[if ?e then _ else _] |- _ ] => destruct e
    end.

    simpl ; unfold bal_xform ; intros. reduce_if_hyp.
    destruct l. generalize (proj1 (assert_false_xform_corr _ _ _ _ _ _ _ _) H). crush.
    reduce_if_hyp. 
    unfold create_xform in H. simpl in H. unfold in_tree in *. crush.
    (repeat in_regexp_inv) ; xmatch_simpl_hyp ; crush ; left ; econstructor ; crush.
    destruct l2. generalize (proj1 (assert_false_xform_corr _ _ _ _ _ _ _ _) H). crush.
    unfold create_xform in H. simpl in H. unfold in_tree in *. crush.
    (repeat in_regexp_inv) ; xmatch_simpl_hyp ; crush. left ; crush. 
    left ; econstructor ; crush. left ; econstructor ; crush. left ; econstructor ; crush.
    reduce_if_hyp. destruct r.
    generalize (proj1 (assert_false_xform_corr _ _ _ _ _ _ _ _) H). crush.
    reduce_if_hyp. unfold create_xform in H. simpl in H.
    unfold in_tree in *. crush. repeat in_regexp_inv ; xmatch_simpl_hyp ; crush.
    right ; right ; crush. right ; right ; crush. right ; right ; crush.
    destruct r1.
    generalize (proj1 (assert_false_xform_corr _ _ _ _ _ _ _ _) H) ; crush.
    unfold create_xform in H. unfold in_tree in *. crush. unfold in_tree in *.
    crush. (repeat in_regexp_inv) ; xmatch_simpl_hyp ; crush. 
    right ; right ; crush. right ; right ; econstructor ; crush.
    right ; right ; econstructor ; split ; crush. right ; right ; econstructor ; 
    split ; crush. right ; right ; econstructor ; split ; crush.
    generalize (proj1 (create_xform_corr _ _ _ _ _ _ _ _) H) ; crush.
  Qed.

  Lemma bal_xform_corr2 ty l fl x fx r fr str v : 
    in_tree_xform (existT _ l fl) str v \/ 
    in_re_xform (existT _ x fx) str v \/ 
    in_tree_xform (existT _ r fr) str v -> 
    in_tree_xform (@bal_xform ty l fl x fx r fr) str v.
  Proof.
    unfold bal_xform. intros. 
    repeat match goal with [ |- in_tree_xform (if ?e then _ else _) _ _] => destruct e end.
    destruct l. apply assert_false_xform_corr. auto.
    match goal with [ |- in_tree_xform ((if ?e then _ else _) _) _ _ ] => destruct e end.
    unfold create_xform ; crush ; unfold in_tree in * ; crush ; repeat in_regexp_inv ; 
    econstructor ; split ; eauto ; xmatch_simpl ; crush.
    destruct l2. 
    unfold assert_false_xform ; crush ; unfold in_tree in * ; crush ; repeat in_regexp_inv ;
    econstructor ; split ; eauto ; xmatch_simpl ; crush.
    unfold create_xform ; simpl. unfold in_tree_xform in *. unfold in_tree in *.
    simpl in *. crush; repeat in_regexp_inv ; econstructor ; split ; eauto ; 
    xmatch_simpl ; crush.
    destruct r. apply assert_false_xform_corr ; auto.
    match goal with [ |- in_tree_xform ((if ?e then _ else _) _) _ _] => destruct e end.
    unfold create_xform. unfold in_tree_xform in *. unfold in_tree in *. simpl in *.
    crush ; (repeat in_regexp_inv) ; econstructor ; split ; eauto ; 
    xmatch_simpl ; crush.
    destruct r1. apply assert_false_xform_corr ; auto.
    unfold create_xform. unfold in_tree_xform in *. unfold in_tree in *. simpl in *.
    crush ; (repeat in_regexp_inv) ; econstructor ; split ; eauto ; 
    xmatch_simpl ; crush.
    apply create_xform_corr ; auto.
  Qed.

  Lemma bal_xform_corr ty l fl x fx r fr str v : 
    in_tree_xform (existT _ l fl) str v \/ 
    in_re_xform (existT _ x fx) str v \/ 
    in_tree_xform (existT _ r fr) str v <-> 
    in_tree_xform (@bal_xform ty l fl x fx r fr) str v.
  Proof.
    intros. split. apply bal_xform_corr2. apply bal_xform_corr1.
  Qed.    

  Lemma cmp_leib : forall r1 r2, REOrderedTypeAlt.compare r1 r2 = Eq -> r1 = r2.
    apply compare_re_eq_leibniz.
  Qed.

  Fixpoint add_xform_tree 
           (t: type)
           (x:regexp) 
           (f1:regexp_type x ->> List_t t) 
           (s:Raw.tree) : (tree_type s ->> List_t t) ->
           {rs:Raw.tree & tree_type rs ->> List_t t} := 
    match s return tree_type s ->> List_t t -> {rs:Raw.tree & tree_type rs ->> List_t t} 
    with
        | Raw.Leaf => 
          fun f2 => 
            existT _ (Raw.Node 1 Raw.Leaf x Raw.Leaf) 
                   (xcomp (xmatch xzero (xmatch xid xzero)) f1)
        | Raw.Node h l y r => 
          match REOrderedTypeAlt.compare x y as p 
          return REOrderedTypeAlt.compare x y = p -> _
          with 
            | Eq => fun H f2 => 
                      existT _ (Raw.Node h l y r)
                       (xmatch (xcomp xinl f2)
                         (xmatch (xcomp (xpair (xcomp (xcomp xinl xinr) f2) (eq_rec x
                           (fun y0 : regexp => regexp_type y0 ->> List_t t)
                           f1 y (cmp_leib x y H))) xapp)
                                 (xcomp (xcomp xinr xinr) f2)))
            | Lt => fun H f2 => 
                      match add_xform_tree x f1 l (xcomp xinl f2) with
                        | existT l' f' => 
                          bal_xform l' f' y (xcomp (xcomp xinl xinr) f2) r 
                                    (xcomp (xcomp xinr xinr) f2)
                      end
            | Gt => fun H f2 => 
                      match add_xform_tree x f1 r (xcomp (xcomp xinr xinr) f2) with
                        | existT r' f' => 
                          bal_xform l (xcomp xinl f2) y (xcomp (xcomp xinl xinr) f2) r' f'
                      end
          end eq_refl
    end.

  Lemma add_xform_tree_erase : 
    forall t s x f1 f, 
      projT1 (@add_xform_tree t x f1 s f) = Raw.add x s.
  Proof.
    induction s ; intros ; auto. unfold add_xform_tree.
    fold add_xform_tree. unfold Raw.add. fold Raw.add.
    generalize (cmp_leib x t2).
    destruct (REOrderedTypeAlt.compare x t2) ; auto ; intros.
    specialize (IHs1 x f1 (xcomp xinl f)).
    match goal with 
        | [ |- projT1 (match ?e with | existT _ _ => _ end) = _ ] => remember e as e1
    end.
    destruct e1. rewrite bal_xform_erase. 
    fold tree_type in IHs1. 
    fold regexp_type in IHs1. fold tree_to_regexp in IHs1.
    unfold tree_type in IHs1, Heqe1. 
    rewrite <- Heqe1 in IHs1. rewrite <- IHs1. auto.
    specialize (IHs2 x f1 (xcomp (xcomp xinr xinr) f)).
    fold regexp_type in IHs2. fold tree_to_regexp in IHs2. 
    unfold tree_type in *.
    match goal with 
      | [ |- projT1 (match ?e with | existT _ _ => _ end) = _ ] => remember e as e1
    end.
    destruct e1. rewrite bal_xform_erase. rewrite <- IHs2. auto.
  Qed.

  Ltac xinterp_simpl :=
  repeat match goal with
    | [|- context[xinterp (xmatch ?X1 ?X2) ?v]] => rewrite (xmatch_corr X1 X2); simpl
    | [H:context[xinterp (xmatch ?X1 ?X2) ?v] |- _ ] => 
      rewrite (xmatch_corr X1 X2) in H ; simpl
    | [|- context[xcomp ?X1 ?X2]] => rewrite (xcomp_corr X1 X2); simpl
    | [H:context[xcomp ?X1 ?X2] |- _] => 
      rewrite (xcomp_corr X1 X2) in H; simpl in H
    | [|- context[xinterp (xpair _ _) _]] => rewrite xpair_corr; simpl
    | [H:context[xinterp (xpair _ _) _] |- _] => 
      rewrite xpair_corr in H; simpl in H
(*
    | [|- context[xinterp xcross _]] => rewrite xcross_corr; simpl
    | [H:context[xinterp xcross _] |- _] => 
      rewrite xcross_corr in H; simpl in H
*)
    | [|- context [xinterp xapp (_,_)]] => rewrite xapp_corr; simpl
    | [H:context [xinterp xapp (_,_)] |- _] => 
      rewrite xapp_corr in H; simpl in H
    | [|- context [xinterp (xmap _) ?V]] => 
      rewrite (@xmap_corr _ _ _ V); simpl
    | [H:context [xinterp (xmap _) ?V] |- _] => 
      rewrite (@xmap_corr _ _ _ V) in H; simpl in H
(*
    | [|- context[xinterp xflatten _]] => rewrite xflatten_corr2; simpl
    | [H:context[xinterp xflatten _] |- _] => 
      rewrite xflatten_corr2 in H; simpl in H
*)
  end.

  Lemma add_xform_tree_corr : 
    forall ty tr ftr x fx str v,
      in_tree_xform (@add_xform_tree ty x fx tr ftr) str v <-> 
      in_re_xform (existT _ x fx) str v \/ in_tree_xform (existT _ tr ftr) str v.
  Proof.
    induction tr ; intros ; split ; crush.
    unfold in_tree in H. simpl in H. repeat in_regexp_inv. xmatch_simpl_hyp ; crush.
    unfold in_tree. simpl. econstructor ; crush. xmatch_simpl ; crush. destruct x0.
    generalize H ; clear H. generalize (cmp_leib x t1). 
    generalize (REOrderedTypeAlt.compare x t1). destruct c. intro.
    generalize (e eq_refl). intro. subst. simpl. crush. unfold in_tree in *.
    simpl in *. (repeat in_regexp_inv) ; repeat (xinterp_simpl ; crush).
    generalize (in_app_or _ _ _ H0). crush. right ; econstructor ; crush.
    right ; econstructor ; crush. intros.
    specialize (IHtr1 (xcomp xinl ftr) x fx str v) ; clear IHtr2.
    fold regexp_type in IHtr1. fold tree_to_regexp in IHtr1.
    unfold tree_type in H.
    match goal with 
      | [ H : in_tree_xform (match ?exp with existT _ _ => _ end) _ _ |- _ ] => 
        remember exp as e1
    end.
    destruct e1. generalize (bal_xform_corr1 _ _ _ _ _ _ _ _ H). intros.
    destruct H0. generalize (proj1 IHtr1 H0). clear IHtr1 H0 H. intro.
    destruct H. crush. unfold in_tree in *. crush ; xinterp_simpl. crush.
    crush ; xinterp_simpl ; unfold in_tree in * ; right ; econstructor ; crush.
    intros. specialize (IHtr2 (xcomp (xcomp xinr xinr) ftr) x fx str v). clear IHtr1.
    fold regexp_type in IHtr2. fold tree_to_regexp in IHtr2. unfold tree_type in H.
    match goal with 
      | [ H : in_tree_xform (match ?exp with existT _ _ => _ end) _ _ |- _ ] => 
        remember exp as e1
    end.
    destruct e1. generalize (bal_xform_corr1 _ _ _ _ _ _ _ _ H) ; intros.
    destruct H0. crush. xinterp_simpl. unfold in_tree. right ; econstructor ; crush.
    destruct H0. unfold in_tree. crush. xinterp_simpl. right ; econstructor ; crush.
    generalize (proj1 IHtr2 H0). clear IHtr2 H0 H. intro. destruct H. crush.
    unfold in_tree in *. crush. xinterp_simpl. right ; econstructor ; crush.
    generalize (cmp_leib x t1). generalize (REOrderedTypeAlt.compare x t1).
    destruct c ; intro. generalize (e eq_refl) ; intro ; subst. simpl. 
    unfold in_tree. econstructor ; crush. xinterp_simpl. apply in_or_app.
    right ; auto. specialize (IHtr1 (xcomp xinl ftr) x fx str v). clear IHtr2.
    fold regexp_type in IHtr1. fold tree_to_regexp in IHtr1. unfold tree_type.
    match goal with 
      | [ |- in_tree_xform (match ?exp with existT _ _ => _ end) _ _ ] => 
        remember exp as e1
    end.
    destruct e1. apply bal_xform_corr2. left. apply IHtr1. left. crush.
    clear IHtr1. specialize (IHtr2 (xcomp (xcomp xinr xinr) ftr) x fx str v).
    fold regexp_type in IHtr2. fold tree_to_regexp in IHtr2. unfold tree_type.
    match goal with 
      | [ |- in_tree_xform (match ?exp with existT _ _ => _ end) _ _ ] => 
        remember exp as e1
    end.
    destruct e1. apply bal_xform_corr2. right. right. apply IHtr2. left ; crush.
    generalize (cmp_leib x t1). generalize (REOrderedTypeAlt.compare x t1).
    destruct c ; intros. generalize (e eq_refl) ; intros ; subst. simpl.
    exists x0. split. auto. xinterp_simpl. destruct x0. xinterp_simpl. auto.
    xinterp_simpl. destruct s. xinterp_simpl. apply in_or_app. left ; auto.
    xinterp_simpl ; auto.
    specialize (IHtr1 (xcomp xinl ftr) x fx str v). clear IHtr2.
    fold regexp_type in IHtr1. fold tree_to_regexp in IHtr1. unfold tree_type.
    match goal with 
      | [ |- in_tree_xform (match ?exp with existT _ _ => _ end) _ _ ] => 
        remember exp as e1
    end.
    destruct e1. apply bal_xform_corr2. unfold in_tree in H. simpl in H.
    generalize (inv_alt H) ; clear H. intros. destruct H. 
    destruct H as [v1 [H1 H2]]. subst. left. apply IHtr1. unfold in_tree.
    right ; econstructor ; split ; eauto. xinterp_simpl. auto.
    destruct H as [v2 [H1 H2]]. subst. generalize (inv_alt H1). clear H1.
    intro H1. destruct H1. destruct H as [v1 [H1 H2]]. subst.
    right ; left. simpl. econstructor ; split ; eauto. xinterp_simpl ; auto.
    destruct H as [v3 [H1 H2]]. subst. right ; right. simpl. unfold in_tree.
    econstructor ; split ; eauto ; xinterp_simpl ; auto.
    clear IHtr1. specialize (IHtr2 (xcomp (xcomp xinr xinr) ftr) x fx str v).
    fold regexp_type in IHtr2. fold tree_to_regexp in IHtr2. unfold tree_type.
    match goal with 
      | [ |- in_tree_xform (match ?exp with existT _ _ => _ end) _ _ ] => 
        remember exp as e1
    end.
    destruct e1. apply bal_xform_corr2. simpl in *. unfold in_tree in *. simpl in *.
    generalize (inv_alt H) ; clear H ; intro H. destruct H. 
    destruct H as [v1 [H1 H2]]. subst. left. econstructor ; split ; eauto.
    xinterp_simpl ; auto. destruct H as [v2 [H1 H2]]. subst.
    generalize (inv_alt H1) ; clear H1 ; intro H. destruct H.
    destruct H as [v1 [H1 H2]]. subst. right ; left. econstructor ; split ; eauto.
    xinterp_simpl ; auto. destruct H as [v3 [H1 H2]]. subst. right ; right.
    apply IHtr2. right. econstructor. split ; eauto. xinterp_simpl ; auto.
  Qed.

  Fixpoint join_xform t (l:Raw.tree) : 
    tree_type l->>List_t t -> 
    forall x, regexp_type x->>List_t t -> 
           forall r, tree_type r->>List_t t -> {rs:Raw.tree & tree_type rs ->> List_t t} :=
    match l return 
          tree_type l->>List_t t -> 
          forall x, regexp_type x->>List_t t -> 
                    forall r, tree_type r->>List_t t -> 
                              {rs:Raw.tree & tree_type rs ->> List_t t}
    with 
      | Raw.Leaf => fun _ => (@add_xform_tree t)
      | Raw.Node lh ll lx lr => 
        fun fl x fx => 
          fix join_aux (r:Raw.tree) : 
            tree_type r->>List_t t -> {rs:Raw.tree & tree_type rs ->> List_t t} := 
          match r return 
                tree_type r->>List_t t -> {rs:Raw.tree & tree_type rs ->> List_t t}
          with 
            | Raw.Leaf => fun _ => add_xform_tree x fx (Raw.Node lh ll lx lr) fl
            | Raw.Node rh rl rx rr => 
              fun fr => 
                if Int.Z_as_Int.gt_le_dec lh 
                                          (Int.Z_as_Int.plus rh Int.Z_as_Int._2) then
                  let (r',fr') := (join_xform lr (xcomp (xcomp xinr xinr) fl) x fx 
                                              (Raw.Node rh rl rx rr) fr) in
                  bal_xform ll (xcomp xinl fl) lx (xcomp (xcomp xinl xinr) fl) r' fr'
                else 
                  if Int.Z_as_Int.gt_le_dec rh 
                                            (Int.Z_as_Int.plus lh Int.Z_as_Int._2) then
                    let (l',fl') := join_aux rl (xcomp xinl fr) in
                    bal_xform l' fl' rx (xcomp (xcomp xinl xinr) fr) 
                              rr (xcomp (xcomp xinr xinr) fr)
                  else create_xform (Raw.Node lh ll lx lr) fl x fx 
                                    (Raw.Node rh rl rx rr) fr
          end
    end.

  Lemma join_xform_erase : forall t l fl x fx r fr, 
      projT1 (@join_xform t l fl x fx r fr) = Raw.join l x r.
  Proof.                             
    induction l. intros ; simpl ; apply add_xform_tree_erase.
    intros fl x fx. 
    unfold join_xform. fold join_xform.
    unfold Raw.join. fold Raw.join.
    match goal with 
      | [ |- forall _ _, projT1 (?fexp1 _ _) = ?fexp2 _ ] => 
        remember fexp1 as join_aux_xform ; remember fexp2 as join_aux
    end.
    induction r ; intros. 
      rewrite Heqjoin_aux ; rewrite Heqjoin_aux_xform ; 
      rewrite add_xform_tree_erase ; auto.
    rewrite Heqjoin_aux. rewrite <- Heqjoin_aux.
    rewrite Heqjoin_aux_xform. rewrite <- Heqjoin_aux_xform.
    destruct (Int.Z_as_Int.gt_le_dec t1 (Int.Z_as_Int.plus t3 Int.Z_as_Int._2)).
    specialize (IHl2 (xcomp (xcomp xinr xinr) fl) x fx (Raw.Node t3 r1 t4 r2) fr).
    remember (join_xform l2 (xcomp (xcomp xinr xinr) fl) x fx (Raw.Node t3 r1 t4 r2) fr)
             as e.
    destruct e.
    rewrite bal_xform_erase. rewrite <- IHl2. auto.
    destruct (Int.Z_as_Int.gt_le_dec t3 (Int.Z_as_Int.plus t1 Int.Z_as_Int._2)).
    specialize (IHr1 (xcomp xinl fr)). 
    remember (join_aux_xform r1 (xcomp xinl fr)) as e. 
    destruct e. rewrite bal_xform_erase. rewrite <- IHr1. auto.
    rewrite create_xform_erase. auto.
  Qed.

  Lemma join_xform_corr : forall ty l fl x fx r fr str v,
    in_tree_xform (@join_xform ty l fl x fx r fr) str v <-> 
      in_tree_xform (existT _ l fl) str v \/ 
      in_re_xform (existT _ x fx) str v \/ 
      in_tree_xform (existT _ r fr) str v.
  Proof.
    induction l. split. simpl ; intro. 
    generalize (proj1 (add_xform_tree_corr r fr x fx str v) H). crush.
    intros. apply add_xform_tree_corr. crush. destruct x0.
    intros fl x fx. unfold join_xform. fold join_xform.
    match goal with 
        [ |- forall _ _ _ _, in_tree_xform (?fexp _ _) _ _ <-> _ ] => 
        remember fexp as join_aux_xform
    end.
    induction r. rewrite Heqjoin_aux_xform. split. intro H.
    generalize (proj1 (add_xform_tree_corr _ _ _ _ _ _) H). simpl. crush.
    intros. apply add_xform_tree_corr. crush. destruct x0.
    rewrite Heqjoin_aux_xform. intros. 
    split ; intro.
    destruct (Int.Z_as_Int.gt_le_dec t0 (Int.Z_as_Int.plus t2 Int.Z_as_Int._2)).
    clear IHl1 IHr1 IHr2. specialize (IHl2 (xcomp (xcomp xinr xinr) fl) x fx
                                           (Raw.Node t2 r1 t3 r2) fr str v).
    remember (join_xform l2 (xcomp (xcomp xinr xinr) fl) x fx
                                   (Raw.Node t2 r1 t3 r2) fr) as e.
    destruct e. generalize (bal_xform_corr1 _ _ _ _ _ _ _ _ H). clear H.
    intros. crush ; unfold in_tree ; xinterp_simpl ; crush. left.
    econstructor ; crush. specialize (H0 (@ex_intro _ _ x2 (conj H H2))).
    crush. xinterp_simpl. left ; econstructor ; crush.
    rewrite <- Heqjoin_aux_xform in H.
    destruct (Int.Z_as_Int.gt_le_dec t2 (Int.Z_as_Int.plus t0 Int.Z_as_Int._2)).
    specialize (IHr1 (xcomp xinl fr) str v). clear IHl1 IHl2 Heqjoin_aux_xform IHr2.
    remember (join_aux_xform r1 (xcomp xinl fr)) as e. destruct e.
    generalize (bal_xform_corr1 _ _ _ _ _ _ _ _ H). clear H. 
    intros ; crush ; unfold in_tree ; xinterp_simpl ; crush. clear H1.
    specialize (H0 (ex_intro _ x2 (conj H H2))). crush. xinterp_simpl.
    right. right. econstructor ; crush. 
    xinterp_simpl ; right ; right ; econstructor ; crush.
    xinterp_simpl ; right ; right ; econstructor ; crush.
    clear Heqjoin_aux_xform IHr1 IHr2 IHl1 IHl2. crush. unfold in_tree in *.
    crush. repeat in_regexp_inv ; xinterp_simpl ; crush. left ; econstructor ; crush.
    left ; econstructor ; crush. xinterp_simpl ; right ; left ; econstructor ; crush.
    xinterp_simpl ; right ; right ; econstructor ; crush.
    xinterp_simpl ; right ; right ; econstructor ; crush.
    xinterp_simpl ; right ; right ; econstructor ; crush.
    rewrite <- Heqjoin_aux_xform.
    destruct (Int.Z_as_Int.gt_le_dec t0 (Int.Z_as_Int.plus t2 Int.Z_as_Int._2)).
    specialize (IHl2 (xcomp (xcomp xinr xinr) fl) x fx (Raw.Node t2 r1 t3 r2) fr str v).
    clear IHl1 Heqjoin_aux_xform IHr1 IHr2.
    remember (join_xform l2 (xcomp (xcomp xinr xinr) fl) x fx (Raw.Node t2 r1 t3 r2) fr)
    as e. destruct e. apply bal_xform_corr. crush. unfold in_tree in *. simpl in *.
    repeat in_regexp_inv ; xinterp_simpl ; crush. left ; econstructor ; split ; eauto.
    xinterp_simpl ; auto. right ; left ; econstructor ; split ; eauto. 
    xinterp_simpl ; auto. right. right. apply H1. left ; econstructor ; split ; eauto.
    xinterp_simpl ; auto. right. right. apply H1. right ; left ; econstructor ; split.
    eauto. auto. unfold in_tree in *. simpl in *. repeat in_regexp_inv ; xinterp_simpl.
    right ; right. apply H1. right ; right. econstructor ; crush.
    right ; right ; apply H1. right ; right ; econstructor ; crush.
    right ; right ; apply H1. right ; right ; econstructor ; crush.
    destruct (Int.Z_as_Int.gt_le_dec t2 (Int.Z_as_Int.plus t0 Int.Z_as_Int._2)).
    clear Heqjoin_aux_xform IHl1 IHl2 IHr2. specialize (IHr1 (xcomp xinl fr) str v).
    remember (join_aux_xform r1 (xcomp xinl fr)) as e. destruct e.
    apply bal_xform_corr. crush. unfold in_tree in *. simpl in *.
    repeat in_regexp_inv ; xinterp_simpl ; crush. left ; apply H1.
    right ; right ; econstructor ; split ; eauto. xinterp_simpl ; auto.
    right ; left ; econstructor ; split ; eauto ; xinterp_simpl ; auto.
    right ; right ; econstructor ; split ; eauto ; xinterp_simpl ; auto.
    clear Heqjoin_aux_xform IHl1 IHl2 IHr1 IHr2. 
    crush ; unfold in_tree in * ; simpl in * ; repeat in_regexp_inv ; 
    xinterp_simpl ; crush ; econstructor ; split ; eauto ; xinterp_simpl ; auto.
  Qed.
 
  Record triple_xform (t:type) (x:regexp) : Type := 
    mkTX { t_left : Raw.tree ; t_left_xform : tree_type t_left ->> List_t t ; 
           t_in : option (regexp_type x ->> List_t t) ; 
           t_right : Raw.tree ; t_right_xform : tree_type t_right ->> List_t t
         }.

  Fixpoint split_xform t (x:regexp) (s : Raw.tree) :
                                  tree_type s ->> List_t t -> triple_xform t x := 
    match s return tree_type s ->> List_t t -> triple_xform t x with 
      | Raw.Leaf => fun f => {| t_left := Raw.Leaf ; t_left_xform := xzero ; 
                                t_in := None ; 
                                t_right := Raw.Leaf ; t_right_xform := xzero |}
      | Raw.Node i l y r => 
        fun f => 
          match REOrderedTypeAlt.compare x y as c return 
                REOrderedTypeAlt.compare x y = c -> triple_xform t x with
            | Eq => fun H => 
                      {| t_left := l ; t_left_xform := xcomp xinl f ; 
                       t_in := 
                         Some (xcomp (eq_rec y 
                                      (fun y0 => regexp_type y0 ->> 
                                         tree_type (Raw.Node i l y r)) 
                                      (xcomp xinl xinr) x (eq_sym (cmp_leib x y H))) f) ; 
                       t_right := r ; t_right_xform := xcomp (xcomp xinr xinr) f |}
            | Lt => fun _ => 
                      let (ll, fll, opt, rl, frl) := split_xform x l (xcomp xinl f) in 
                      let (r',fr') := join_xform rl frl y (xcomp (xcomp xinl xinr) f) r
                                                 (xcomp (xcomp xinr xinr) f) in
                      {| t_left := ll ; t_left_xform := fll ; 
                         t_in := opt ; 
                         t_right := r' ; t_right_xform := fr' |}
            | Gt => fun _ => 
                      let (rl, frl, opt, rr, frr) := split_xform x r 
                                                      (xcomp (xcomp xinr xinr) f) in 
                      let (l',fl') := join_xform l (xcomp xinl f) y 
                                                 (xcomp (xcomp xinl xinr) f) 
                                                 rl frl in
                      {| t_left := l' ; t_left_xform := fl' ; 
                         t_in := opt ; 
                         t_right := rr ; t_right_xform := frr |}
          end eq_refl
    end.

  Lemma split_xform_erase : forall t x s fs, 
      Raw.split x s = 
      match @split_xform t x s fs with
        | mkTX l _ None r _ => Raw.mktriple l false r
        | mkTX l _ _ r _ => Raw.mktriple l true r
      end.
  Proof.
    induction s ; intros ; auto. unfold Raw.split. fold Raw.split.
    unfold split_xform. fold split_xform. generalize (cmp_leib x t2).
    destruct (REOrderedTypeAlt.compare x t2) ; auto ; intro e ; clear e.
    specialize (IHs1 (xcomp xinl fs)). 
    remember (split_xform x s1 (xcomp xinl fs)) as e1.
    destruct e1. 
    remember (join_xform t_right0 t_right_xform0 t2 (xcomp (xcomp xinl xinr) fs)
                         s2 (xcomp (xcomp xinr xinr) fs)) as e2.
    destruct e2. rewrite IHs1. 
    replace x0 with (projT1 (existT (fun rs => tree_type rs->>List_t t0) x0 x1)) ; auto.
    rewrite Heqe2. rewrite join_xform_erase. destruct t_in0 ; auto.
    specialize (IHs2 (xcomp (xcomp xinr xinr) fs)).
    rewrite IHs2. destruct (split_xform x s2 (xcomp (xcomp xinr xinr) fs)).
    remember (join_xform s1 (xcomp xinl fs) t2 (xcomp (xcomp xinl xinr) fs) t_left0
                         t_left_xform0) as e1.
    destruct e1. 
    replace x0 with (projT1 (existT (fun rs => tree_type rs->>List_t t0) x0 x1)) ; auto.
    rewrite Heqe1. rewrite join_xform_erase. destruct t_in0 ; auto.
  Qed.

  Definition in_triple_xform ty x (trip : @triple_xform ty x) str v := 
    in_tree_xform (existT _ (t_left trip) (t_left_xform trip)) str v \/ 
    in_tree_xform (existT _ (t_right trip) (t_right_xform trip)) str v \/ 
    match (t_in trip) with 
      | Some f => in_re_xform (existT _ x f) str v
      | None => False
    end.

  Lemma split_xform_corr : forall ty x s f str v,
    in_triple_xform (@split_xform ty x s f) str v <-> 
    in_tree_xform (existT _ s f) str v.
  Proof.
    induction s ;  intros. 
    unfold in_triple_xform ; crush ; unfold tree_type in * ; crush ; 
    match goal with [ v : void |- _ ] => destruct v end. 
    simpl. split. generalize (cmp_leib x t1). 
    generalize (REOrderedTypeAlt.compare x t1). destruct c. intro e.
    generalize (e eq_refl). intros ; subst. unfold in_tree. 
    unfold in_triple_xform in H. crush ; xinterp_simpl ; crush. 
    intros. specialize (IHs1 (xcomp xinl f) str v).
    remember (split_xform x s1 (xcomp xinl f)) as e1. destruct e1.
    generalize (join_xform_corr t_right0 t_right_xform0 t1 
                                (xcomp (xcomp xinl xinr) f) s2 
                                (xcomp (xcomp xinr xinr) f) str v). intro.
    remember (join_xform t_right0 t_right_xform0 t1 
                         (xcomp (xcomp xinl xinr) f) s2 
                                (xcomp (xcomp xinr xinr) f)) as e1.
    destruct e1. 
    unfold in_triple_xform in *.  simpl in *. destruct H.
    generalize (proj1 IHs1 (@or_introl _ _ H)). crush. xinterp_simpl. simpl.
    unfold in_tree. econstructor ; split ; eauto. simpl. eauto.
    destruct H. generalize (proj1 H0 H). clear H0 ; intro H0.
    destruct H0. generalize (proj1 IHs1 (@or_intror _ _ (@or_introl _ _ H0))).
    crush. xinterp_simpl. crush. unfold in_tree. simpl. econstructor ; split ; eauto.
    destruct H0. crush ; xinterp_simpl. unfold in_tree. simpl. econstructor ; split ;
    crush. crush ; xinterp_simpl ; unfold in_tree ; simpl. econstructor ; crush.
    destruct t_in0 ; [ idtac | crush]. 
    specialize (proj1 IHs1 (@or_intror _ _ (@or_intror _ _ H))). crush.
    unfold in_tree. xinterp_simpl. crush.
    specialize (IHs2 (xcomp (xcomp xinr xinr) f) str v). clear IHs1. intros.
    remember (split_xform x s2 (xcomp (xcomp xinr xinr) f)) as e1. destruct e1.
    generalize (proj1 (join_xform_corr s1 (xcomp xinl f) t1 (xcomp (xcomp xinl xinr) f)
                                       t_left0 t_left_xform0 str v)). intros.
    remember (join_xform s1 (xcomp xinl f) t1 (xcomp (xcomp xinl xinr) f)
                         t_left0 t_left_xform0) as e1 ; destruct e1.
    unfold in_triple_xform in * ; simpl in *. destruct H.
    generalize (H0 H). clear H0. intro. destruct H0. 
    unfold in_tree in * ; xinterp_simpl ; crush. xinterp_simpl ; econstructor ; crush.
    destruct H0. unfold in_tree. crush ; xinterp_simpl. crush.
    generalize (proj1 IHs2 (@or_introl _ _ H0)). 
    unfold in_tree ; crush ; xinterp_simpl ; crush.
    destruct H. specialize (proj1 IHs2 (@or_intror _ _ (@or_introl _ _ H))).
    unfold in_tree ; crush ; xinterp_simpl ; crush.
    destruct t_in0 ; [idtac | crush]. 
    specialize (proj1 IHs2 (@or_intror _ _ (@or_intror _ _ H))). 
    unfold in_tree ; crush ; xinterp_simpl ; crush.
    generalize (cmp_leib x t1). generalize (REOrderedTypeAlt.compare x t1). destruct c. 
    intros. generalize (e eq_refl). intros ; subst. unfold in_triple_xform. crush.
    unfold in_tree in H ; simpl in H. repeat in_regexp_inv. left.
    econstructor ; split ; eauto. xinterp_simpl ; auto.
    right ; right. econstructor ; split ; eauto. xinterp_simpl ; auto.
    right ; left ; econstructor ; split ; eauto ; xinterp_simpl ; auto.
    intros. crush. unfold in_tree in H ; simpl in H.
    specialize (proj2 (IHs1 (xcomp xinl f) str v)). clear IHs1 IHs2. 
    intros. remember (split_xform x s1 (xcomp xinl f)) as e1. destruct e1.
    specialize (proj2 (join_xform_corr t_right0 t_right_xform0 t1 
                                       (xcomp (xcomp xinl xinr) f)
                                       s2 (xcomp (xcomp xinr xinr) f) str v)). 
    intros. remember (join_xform t_right0 t_right_xform0 t1 (xcomp (xcomp xinl xinr) f)
                                 s2 (xcomp (xcomp xinr xinr) f)) as e2. destruct e2.
    unfold in_triple_xform. simpl. crush.
    repeat in_regexp_inv. 
    assert (exists v', in_tree s1 str v' /\ List.In v (xinterp (xcomp xinl f) v')).
    econstructor ; split ; eauto. xinterp_simpl. auto. specialize (H1 H3).
    unfold in_triple_xform in H1. simpl in H1. destruct H1. left ; auto.
    destruct H1. right ; left. auto. right ; right. auto.
    right ; left. apply H2. right ; left. econstructor ; split ; eauto.
    xinterp_simpl. auto. right ; left. apply H2. right ; right. econstructor ; 
    split ; eauto. xinterp_simpl. auto.
    intros. specialize (proj2 (IHs2 (xcomp (xcomp xinr xinr) f) str v)).
    clear IHs1 IHs2. intros. remember (split_xform x s2 (xcomp (xcomp xinr xinr) f)) as e1.
    destruct e1. specialize (proj2 (join_xform_corr s1 (xcomp xinl f) t1
                                                    (xcomp (xcomp xinl xinr) f)
                                                    t_left0 t_left_xform0 str v)). intro.
    remember (join_xform s1 (xcomp xinl f) t1 (xcomp (xcomp xinl xinr) f) t_left0
                         t_left_xform0) as e2.
    destruct e2. unfold in_triple_xform. simpl. unfold in_tree in H. crush.
    repeat in_regexp_inv. left. apply H1. left ; econstructor ; split ; eauto.
    xinterp_simpl ; auto. left ; apply H1. right ; left ; econstructor ; split ; eauto ; 
    xinterp_simpl ; auto. 
    assert (exists v', in_tree s2 str v' /\ List.In v (xinterp (xcomp (xcomp xinr xinr) f) v')).
    econstructor ; split ; eauto ; xinterp_simpl ; auto.
    specialize (H0 H3). unfold in_triple_xform in H0. simpl in H0. 
    destruct H0. left. apply H1. right ; right. crush.
    destruct H0 ; auto.
  Qed.

  Fixpoint union_xform_tree t (s1:Raw.tree) : (tree_type s1 ->> List_t t) -> 
                                      forall s2:Raw.tree, tree_type s2 ->> List_t t -> 
                                  { rs : Raw.tree & tree_type rs ->> List_t t } := 
    match s1 return 
          (tree_type s1 ->> List_t t) -> forall s2:Raw.tree, tree_type s2 ->> List_t t -> 
                              { rs : Raw.tree & tree_type rs ->> List_t t }
    with 
      | Raw.Leaf => fun _ s2 f2 => existT _ s2 f2
      | Raw.Node i l1 x1 r1 => 
        fun f1 s2 f2 => 
          match s2 return {rs:Raw.tree & tree_type rs ->> List_t t} with
              | Raw.Leaf => existT _ (Raw.Node i l1 x1 r1) f1
              | Raw.Node _ _ _ _ => 
                let (l2',fl2', opt, r2',fr2') := split_xform x1 s2 f2 in 
                let (l',fl') := union_xform_tree l1 (xcomp xinl f1) l2' fl2' in 
                let (r',fr') := union_xform_tree r1 (xcomp (xcomp xinr xinr) f1) r2' fr2'
                in let xf1 := xcomp (xcomp xinl xinr) f1 in
                   let xf := match opt with 
                               | None => xf1
                               | Some fother => xcomp (xpair xf1 fother) xapp
                             end in 
                join_xform l' fl' x1 xf r' fr'
          end
    end.

  Lemma union_xform_tree_erase t s1 : forall f1 s2 f2,
    projT1 (@union_xform_tree t s1 f1 s2 f2) = Raw.union s1 s2.
  Proof.
    induction s1 ; intros ; auto. 
    simpl. destruct s2. auto.
    remember (split_xform t1 (Raw.Node t2 s2_1 t3 s2_2) f2) as e1.
    destruct e1.
    remember (Raw.split t1 (Raw.Node t2 s2_1 t3 s2_2)) as e2.
    destruct e2.
    match goal with 
      | [ |- projT1 (match ?exp with | existT _ _ => _ end) = _ ] => 
        remember exp as e3 ; destruct e3
    end.
    match goal with 
      | [ |- projT1 (match ?exp with | existT _ _ => _ end) = _ ] => 
        remember exp as e4 ; destruct e4
    end.
    rewrite join_xform_erase.
    replace x with (projT1 (existT (fun rs => tree_type rs->>List_t t) x x0)) ; auto.
    rewrite Heqe3. rewrite IHs1_1.
    replace x1 with (projT1 (existT (fun rs => tree_type rs->>List_t t) x1 x2)) ; auto.
    rewrite Heqe4. rewrite IHs1_2.
    specialize (split_xform_erase t1 (Raw.Node t2 s2_1 t3 s2_2) f2).
    intros. rewrite H in Heqe2. 
    remember (split_xform t1 (Raw.Node t2 s2_1 t3 s2_2) f2) as e5.
    destruct e5. 
    injection Heqe1. intros ; subst. clear Heqe1. 
    destruct t_in2 ; injection Heqe2 ; intros ; subst ; auto.
  Qed.

  Lemma union_xform_tree_corr : 
    forall ty s1 f1 s2 f2 str v, 
      in_tree_xform (@union_xform_tree ty s1 f1 s2 f2) str v <->
      in_tree_xform (existT _ s1 f1) str v \/ in_tree_xform (existT _ s2 f2) str v.
  Proof.
    induction s1.
    intros. simpl. crush. destruct x. 
    intros. destruct s2. simpl. crush. destruct x.
    unfold union_xform_tree. fold union_xform_tree.
    generalize (split_xform_corr t1 (Raw.Node t2 s2_1 t3 s2_2) f2 str v).
    intro. remember (split_xform t1 (Raw.Node t2 s2_1 t3 s2_2) f2) as e.
    destruct e. unfold in_triple_xform in H. simpl in H.
    specialize (IHs1_1 (xcomp xinl f1) t_left0 t_left_xform0 str v).
    remember (union_xform_tree s1_1 (xcomp xinl f1) t_left0 t_left_xform0) as e1.
    destruct e1.
    specialize (IHs1_2 (xcomp (xcomp xinr xinr) f1) t_right0 t_right_xform0 str v).
    remember (union_xform_tree s1_2 (xcomp (xcomp xinr xinr) f1) t_right0 
                               t_right_xform0) as e2.
    destruct e2. 
    match goal with 
      | [ |- in_tree_xform (join_xform ?x ?x0 ?t1 ?e ?x1 ?x2) ?str ?v <-> _ ] => 
        generalize (join_xform_corr x x0 t1 e x1 x2 str v) ; intro
    end.
    split ; intro.
    specialize (proj1 H0 H1). clear H0 H1. intro.
    destruct H0.
    specialize (proj1 IHs1_1 H0). intro. simpl in *. unfold in_tree in *. simpl in *.
    crush. xinterp_simpl. left ; econstructor ; crush.
    destruct H0. destruct t_in0. simpl in *. unfold in_tree. simpl in *.
    crush. xinterp_simpl. generalize (in_app_or _ _ _ H6).  crush.
    left ; econstructor ; crush.
    assert (exists v', in_regexp t1 str v' /\ List.In v (xinterp x3 v')).
    crush. specialize (H (@or_intror _ _ (@or_intror _ _ H8))). unfold in_tree in H.
    crush. left. crush. unfold in_tree ; crush. xinterp_simpl. crush.
    specialize (proj1 IHs1_2 H0). intro. destruct H1. left. 
    simpl in * ; unfold in_tree in * ; crush. xinterp_simpl ; crush. clear Heqe Heqe2 Heqe1.
    specialize (proj1 H (@or_intror _ _ (@or_introl _ _ H1))). clear H H1. intro. 
    right ; auto. clear Heqe Heqe1 Heqe2.
    apply H0. clear H0. 
    destruct H1.
      simpl in *. unfold in_tree in *. crush. repeat in_regexp_inv.
      assert (exists v', in_tree s1_1 str v' /\ List.In v (xinterp (xcomp xinl f1) v')).
      econstructor ; split ; eauto. xinterp_simpl. auto.
      specialize (H5 (@or_introl _ _ H7)). left ; auto. right ; left.
      econstructor ; split ; eauto. destruct t_in0. xinterp_simpl.
      apply in_or_app. auto. xinterp_simpl. auto.
      right ; right ; apply H3. left. econstructor ; split ; eauto ; xinterp_simpl ; auto.

      specialize (proj2 H H0). clear H H0. intros. destruct H.
      specialize (proj2 IHs1_1 (@or_intror _ _ H)). clear IHs1_1 H. intro. auto.
      destruct H. specialize (proj2 IHs1_2 (@or_intror _ _ H)). clear IHs1_2 H. auto.
      destruct t_in0 ; [idtac | crush]. right ; left. crush.
      econstructor ; split ; eauto. xinterp_simpl. apply in_or_app. auto.
  Qed.

  (* should rewrite using explicit code -- hard to work with it this way... *)
  Definition add_xform (ty:type)(x:regexp)(fx:regexp_type x->>List_t ty)
             (rs:rs_xf_pair ty) : rs_xf_pair ty.
    destruct rs as [s fs].
    destruct s as [t ok].
    remember (add_xform_tree x fx t fs) as p.
    destruct p as [t' ft'].
    assert (Raw.Ok t').
    replace t' with (projT1 (existT (fun rs => tree_type rs ->> List_t ty) t' ft')).
    rewrite Heqp. rewrite add_xform_tree_erase.
    apply (Raw.add_ok _ ok). auto.
    remember ({|this := t' ; is_ok := H|}) as s'.
    eapply (existT (fun rs => re_set_type rs ->> List_t ty) s').
    rewrite Heqs'. apply ft'.
  Defined.

  Lemma add_xform_erase ty x fx rs : 
    projT1 (@add_xform ty x fx rs) = add x (projT1 rs).
  Proof.
    unfold add_xform.
    destruct rs as [s fs].
    destruct s as [t ok].
    generalize (eq_ind_r (fun s => Raw.Ok (projT1 s))
                         (eq_ind_r (fun t0 => Raw.Ok t0)
                                   (Raw.add_ok x ok)
                                   (add_xform_tree_erase t x fx fs))).
    remember (add_xform_tree x fx t fs) as p.
    destruct p as [t' ft'].
    unfold add. simpl.
    intros.
    generalize (o (existT (fun rs => tree_type rs ->> List_t ty) t' ft') eq_refl).
    simpl. 
    replace (t') 
    with (projT1 (existT (fun rs => tree_type rs ->> List_t ty) t' ft')) ; auto.
    rewrite Heqp. rewrite add_xform_tree_erase. intros.
    rewrite (proof_irrelevance _ o0 (Raw.add_ok x ok)). auto.
  Qed.

  Lemma add_xform_corr ty x fx rs str v : 
    in_re_set_xform (@add_xform ty x fx rs) str v <-> 
    in_re_xform (existT _ x fx) str v \/ in_re_set_xform rs str v.
  Proof.
    destruct rs as [s fs]. destruct s as [t ok]. unfold in_re_set_xform.
    unfold add_xform. simpl. unfold eq_rec_r, eq_rec, eq_rect. simpl.
    generalize (eq_ind_r (fun s => Raw.Ok (projT1 s)) 
                         (eq_ind_r (fun t0 => Raw.Ok t0) (Raw.add_ok x ok)
                                   (add_xform_tree_erase t x fx fs))).
    generalize (add_xform_tree_corr t fs x fx str v).
    remember (add_xform_tree x fx t fs) as p. intros.
    destruct p. unfold re_set_type. simpl. unfold in_re_set. simpl.
    apply H.
  Qed.

  Definition union_xform (ty:type) (rs1 rs2 : rs_xf_pair ty) : rs_xf_pair ty.
    destruct rs1 as [s1 f1].
    destruct rs2 as [s2 f2].
    destruct s1 as [t1 okt1].
    destruct s2 as [t2 okt2].
    remember (union_xform_tree t1 f1 t2 f2) as p.
    destruct p as [t0 f0].
    assert (H: Raw.Ok t0).
    replace t0 with (projT1 (existT (fun rs => tree_type rs ->> List_t ty) t0 f0)) ; auto.
    rewrite Heqp. rewrite union_xform_tree_erase.
    apply (Raw.union_ok okt1 okt2).
    remember ({|this := t0 ; is_ok := H|}) as s'.
    apply (existT (fun rs => re_set_type rs ->> List_t ty) s').
    rewrite Heqs'.
    apply f0.
  Defined.

  Lemma union_xform_erase ty rs1 rs2 : 
    projT1 (@union_xform ty rs1 rs2) = union (projT1 rs1) (projT1 rs2).
  Proof.
    unfold union_xform. 
    destruct rs1 as [s1 f1].
    destruct rs2 as [s2 f2].
    destruct s1 as [t1 okt1].
    destruct s2 as [t2 okt2]. simpl.
    generalize (eq_ind_r (fun s => 
                            Raw.Ok (projT1 s))
                         (eq_ind_r (fun t3 => Raw.Ok t3)
                                   (Raw.union_ok okt1 okt2)
                                   (union_xform_tree_erase t1 f1 t2 f2))).
    remember (union_xform_tree t1 f1 t2 f2) as p.
    destruct p. simpl. 
    unfold union. simpl. intro.
    generalize (o (existT (fun rs => tree_type rs ->> List_t ty) x x0) eq_refl).
    clear o. simpl. 
    replace (x) with (projT1 (existT (fun rs => tree_type rs ->> List_t ty) x x0)) ; auto.
    rewrite Heqp. rewrite union_xform_tree_erase. intros.
    rewrite (proof_irrelevance _ o (Raw.union_ok okt1 okt2)). auto.
  Qed.

  Lemma union_xform_corr ty rs1 rs2 str v : 
    in_re_set_xform (@union_xform ty rs1 rs2) str v <-> 
    in_re_set_xform rs1 str v \/ in_re_set_xform rs2 str v.
  Proof.
    destruct rs1 as [s1 f1].
    destruct rs2 as [s2 f2].
    destruct s1 as [t1 okt1].
    destruct s2 as [t2 okt2]. simpl. 
    generalize (eq_ind_r
                    (fun s : {rs : Raw.tree & tree_type rs ->> List_t ty} =>
                     Raw.Ok (projT1 s))
                    (eq_ind_r (fun t3 : Raw.tree => Raw.Ok t3)
                       (Raw.union_ok (s1:=t1) (s2:=t2) okt1 okt2)
                       (union_xform_tree_erase t1 f1 t2 f2))).
    generalize (union_xform_tree_corr t1 f1 t2 f2 str v).
    remember (union_xform_tree t1 f1 t2 f2) as p. intros. 
    destruct p. simpl. unfold re_set_type, in_re_set. simpl.
    unfold eq_rec_r, eq_rec, eq_rect. simpl. apply H.
  Qed.

  Section FOLD_TREE_XFORM.
    Variable ty : type.
    Variable A : Type.
    Variable f : forall r, regexp_type r ->> ty -> A -> A.
    Fixpoint fold_tree_xform (s:Raw.tree) : (tree_type s ->> ty) -> A -> A := 
      match s return tree_type s ->> ty -> A -> A with
        | Raw.Leaf => fun _ v => v
        | Raw.Node _ l x r => 
          fun fs v => fold_tree_xform r (xcomp (xcomp xinr xinr) fs) 
                                     (f x (xcomp (xcomp xinl xinr) fs) 
                                           (fold_tree_xform l (xcomp xinl fs) v))
      end.
  End FOLD_TREE_XFORM.

  Definition map_tree_xform ty 
             (s:Raw.tree) 
             (fs:tree_type s ->> List_t ty) 
             (g:forall r:regexp, regexp_type r ->> List_t ty -> 
                                 {r' : regexp & regexp_type r' ->> List_t ty}) :
             { s' : Raw.tree & tree_type s' ->> List_t ty } := 
    fold_tree_xform (fun r fr (sx : {s':Raw.tree & tree_type s' ->> List_t ty}) => 
                       let (r',fr') := g r fr in
                       let (s',fs') := sx in 
                       add_xform_tree r' fr' s fs) s fs 
                    (existT _ Raw.Leaf xzero).

(* Raw.fold = 
fix fold (A : Type) (f : Raw.elt -> A -> A) (t : Raw.tree) 
         (base : A) {struct t} : A :=
  match t with
  | Raw.Leaf => base
  | Raw.Node _ l x r => fold A f r (f x (fold A f l base))
  end
     : forall A : Type, (Raw.elt -> A -> A) -> Raw.tree -> A -> A
*)
  (* Lemma map_tree_xform_unfold ty g i l v r fs :  *)
  (*   (@map_tree_xform ty (Raw.Node i l v r) fs g) =  *)
  (*   let (s1,f1) := @map_tree_xform ty l (xcomp xinl fs) g in  *)
  (*   let (v',fv') := g v (xcomp (xcomp xinl xinr) fs) in *)
  (*   let (s2,f2) := add_xform_tree v' fv' s1 f1 in  *)
    

  (* Lemma map_tree_xform_erase ty g1 g2 :  *)
  (*   (forall r (f:regexp_type r ->> List_t ty), projT1 (g1 r f) = g2 r) ->  *)
  (*   forall s fs,  *)
  (*   projT1 (@map_tree_xform ty s fs g1) =  *)
  (*   Raw.fold (fun r s' => Raw.add (g2 r) s') s Raw.Leaf. *)
  (* Proof. *)
  (*   intro H. induction s ; intro. auto. simpl. *)
  (*   unfold map_tree_xform.  *)
  
  (* Definition cat_re_xform :  *)
  (*   forall ty, rs_xf_pair (List_t ty) ->  *)
  (*              forall r:regexp, rs_xf_pair (Pair_t ty (regexp_type r)). *)


End RESETXFORM.

(* Module RR : WSets := RESet. *)
