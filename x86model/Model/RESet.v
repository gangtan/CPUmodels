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

  Definition rs_xf_pair (ty:type) := {rs : t & re_set_type rs ->> ty }.

  (* the following type for union_xofrm is motivated by the case of doing
     partial derivatives over r1+r2
        pdrv(a, r1+r2) =
          let (rs1, f1) = pdrv(a, r1) in
          let (rs2, f2) = pdrv(a, r2) in
            union_xform (rs1, f1) (rs2, f2)
  *)
  Parameter union_xform: forall ty1,
    rs_xf_pair (List_t ty1) -> rs_xf_pair (List_t ty1) -> rs_xf_pair (List_t ty1).
  (* note: def equality may not be necessary here *)
  Parameter union_xform_erase: forall ty1 rx1 rx2,
    projT1 (@union_xform ty1 rx1 rx2) = union (projT1 rx1) (projT1 rx2).

  Parameter empty_xform: forall ty, rs_xf_pair ty.
  Parameter empty_xform_erase: forall ty, projT1 (@empty_xform ty) = empty.

  Parameter singleton_xform: forall r:regexp, rs_xf_pair (regexp_type r).
  Parameter singleton_xform_erase: forall r, 
    projT1 (@singleton_xform r) = (singleton r).


  (* note: the following operation is motivated by the case of doing
     partial derives over "r1 cat r2" when r1 is not nullable.
        pdrv(a, r1 r2) =
          let (rs1, f1) := pdrv (a, r1) in
            cat_re_xform (rs1, f1) r2
  *)
  Parameter cat_re_xform: forall ty,
    rs_xf_pair ty -> forall r:regexp, rs_xf_pair (Pair_t ty (regexp_type r)).
  (* can also state a erasure lemma, need to bring the set_cat_re definition,
     which is in NewRecognizer.v *)

End RESetXform.

Module RESet := MSetAVL.Make REOrderedType.
Module RESETXFORM <: RESetXform.
  Include RESet.  

  Fixpoint tree_type (t:Raw.tree) : type := 
    match t with 
      | Raw.Leaf => Void_t
      | Raw.Node i lft r rgt => 
        Sum_t (tree_type lft) (Sum_t (regexp_type r) (tree_type rgt))
    end.

  Definition re_set_type (rs : t) : type := tree_type (this rs). 
  
  Definition rs_xf_pair (ty:type) := {rs : t & re_set_type rs ->> ty }.

  Definition empty_xform (ty:type) : rs_xf_pair ty := 
    existT _ empty xzero.
  
  Lemma empty_xform_erase : forall ty, projT1 (@empty_xform ty) = empty.
    auto.
  Qed.

  Definition singleton_xform (r:regexp) : rs_xf_pair (regexp_type r) := 
    existT _ (singleton r) (xmatch xzero (xmatch xid xzero)).

  Lemma singleton_xform_erase : forall r, projT1 (@singleton_xform r) = (singleton r).
    auto.
  Qed.

  Open Scope Z_scope.

  (* These definitions parallel those in the Raw module, but add in an xform. *)
  Definition create_xform t (l:Raw.tree) (fl : tree_type l ->> t)
                            (x:regexp) (fx : regexp_type x ->> t)
                            (r:Raw.tree) (fr : tree_type r ->> t) : 
    { s : Raw.tree & tree_type s ->> t } := 
    existT _ (Raw.Node (Int.Z_as_Int.plus (Int.Z_as_Int.max (Raw.height l) 
                                                            (Raw.height r)) 1)
                       l x r) (xmatch fl (xmatch fx fr)).

  Lemma create_xform_erase : 
    forall t l fl x fx r fr, projT1 (@create_xform t l fl x fx r fr) = Raw.create l x r.
    auto.
  Qed.

  Definition assert_false_xform := create_xform.

  Lemma assert_false_xform_erase : 
    forall t l fl x fx r fr, projT1 (@assert_false_xform t l fl x fx r fr) = 
                             Raw.assert_false l x r.
    auto.
  Qed.

  Definition bal_xform t (l:Raw.tree) (fl : tree_type l ->> List_t t)
                         (x:regexp) (fx : regexp_type x ->> List_t t)
                         (r:Raw.tree) (fr : tree_type r ->> List_t t) : 
                         {s : Raw.tree & tree_type s ->> List_t t} := 
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
    fold tree_type in IHs1. rewrite <- Heqe1 in IHs1. rewrite <- IHs1. auto.
    specialize (IHs2 x f1 (xcomp (xcomp xinr xinr) f)).
    fold tree_type in IHs2.
    match goal with 
      | [ |- projT1 (match ?e with | existT _ _ => _ end) = _ ] => remember e as e1
    end.
    destruct e1. rewrite bal_xform_erase. rewrite <- IHs2. auto.
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

  (* should rewrite using explicit code -- hard to work with it this way... *)
  Definition add_xform (ty:type)(x:regexp)(fx:regexp_type x->>List_t ty)
             (rs:rs_xf_pair (List_t ty)) : rs_xf_pair (List_t ty).
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

  Definition union_xform (ty:type) (rs1 rs2 : rs_xf_pair (List_t ty)) : 
    rs_xf_pair (List_t ty).
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

  (* An iterator for the trees -- extracts the elements and the appropriate
     transform.  Don't need this now, but I've left it in. *)
  Section ITER_TREE.
    Parameter T : type.
    Parameter A : Type.
    Parameter comb : forall r, regexp_type r ->> T -> A -> A.
    Fixpoint iter_tree_xform (s:Raw.tree) : (tree_type s ->> T) -> A -> A := 
      match s return tree_type s ->> T -> A -> A with
        | Raw.Leaf => fun _ v => v
        | Raw.Node _ l x r => 
          fun f v => iter_tree_xform r (xcomp (xcomp xinr xinr) f) 
                                     (comb x (xcomp (xcomp xinl xinr) f) 
                                           (iter_tree_xform l (xcomp xinl f) v))
      end.
  End ITER_TREE.

Print Raw.union.
Print Raw.split.
Print Raw.triple.
Print Raw.join.
End RESETXFORM.

(* Module RR : WSets := RESet. *)
