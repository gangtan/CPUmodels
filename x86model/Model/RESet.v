Require Import MSets.MSetInterface.
Require Import MSets.MSetProperties.
Require Import MSets.MSetAVL.

Require Import Structures.OrdersAlt.

Require Import Xform.
Require Import Regexp.

Require Import CommonTacs.

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

  Lemma bal_erase : 
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
    destruct e1. rewrite bal_erase. 
    fold tree_type in IHs1. rewrite <- Heqe1 in IHs1. rewrite <- IHs1. auto.
    specialize (IHs2 x f1 (xcomp (xcomp xinr xinr) f)).
    fold tree_type in IHs2.
    match goal with 
      | [ |- projT1 (match ?e with | existT _ _ => _ end) = _ ] => remember e as e1
    end.
    destruct e1. rewrite bal_erase. rewrite <- IHs2. auto.
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

(*
Record triple : Type := mktriple
  { t_left : Raw.t;  t_in : bool;  t_right : Raw.t }

Raw.split = 
fix split (x : REOrderedTypeAlt.t) (s : Raw.tree) {struct s} : Raw.triple :=
  match s with
  | Raw.Leaf =>
      {|
      Raw.t_left := Raw.Leaf;
      Raw.t_in := false;
      Raw.t_right := Raw.Leaf |}
  | Raw.Node _ l y r =>
      match REOrderedTypeAlt.compare x y with
      | Eq => {| Raw.t_left := l; Raw.t_in := true; Raw.t_right := r |}
      | Lt =>
          let (ll, b, rl) := split x l in
          {|
          Raw.t_left := ll;
          Raw.t_in := b;
          Raw.t_right := Raw.join rl y r |}
      | Gt =>
          let (rl, b, rr) := split x r in
          {|
          Raw.t_left := Raw.join l y rl;
          Raw.t_in := b;
          Raw.t_right := rr |}
      end
  end

Raw.union = 
fix union (s1 s2 : Raw.tree) {struct s1} : Raw.tree :=
  match s1 with
  | Raw.Leaf => s2
  | Raw.Node _ l1 x1 r1 =>
      match s2 with
      | Raw.Leaf => s1
      | Raw.Node _ _ _ _ =>
          let (l2', _, r2') := Raw.split x1 s2 in
          Raw.join (union l1 l2') x1 (union r1 r2')
      end
  end
*)

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
