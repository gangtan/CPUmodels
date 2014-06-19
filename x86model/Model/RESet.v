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

  Definition rx_equal ty (rx1 rx2: rs_xf_pair ty) := 
    forall s v, in_re_set_xform rx1 s v <-> in_re_set_xform rx2 s v.

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

  Parameter add_xform: 
    forall ty (rex: re_xf_pair ty) (rx: rs_xf_pair ty), rs_xf_pair ty.
  Parameter add_xform_erase: 
    forall ty (rex:re_xf_pair ty) rx,
      projT1 (add_xform rex rx) = add (projT1 rex) (projT1 rx).
  Parameter add_xform_corr: 
    forall ty (rex:re_xf_pair ty) rx s v,
      in_re_set_xform (add_xform rex rx) s v <->
      in_re_xform rex s v \/ in_re_set_xform rx s v.

  Parameter fold_xform: 
    forall (ty:type) (A:Type) (comb: re_xf_pair ty -> A -> A),
      (rs_xf_pair ty) -> A -> A.
  Parameter fold_xform_erase : forall ty1 ty2
     (comb1:re_xf_pair ty1 -> rs_xf_pair ty2 -> rs_xf_pair ty2)
     (comb2:regexp -> t -> t) rx ini_rx,
     (forall rex rx, projT1 (comb1 rex rx) = comb2 (projT1 rex) (projT1 rx)) -> 
     projT1 (fold_xform comb1 rx ini_rx) = fold comb2 (projT1 rx) (projT1 ini_rx).
  Parameter fold_xform_rec :
    forall (ty : type) (A : Type)     (* output type *)
           (P : rs_xf_pair ty -> A -> Prop)  (* predicate *)
           (f : re_xf_pair ty -> A -> A),    (* function we are folding *)
      (forall rx1 rx2 : rs_xf_pair ty,  (* predicate holds on equivalent sets *)
         rx_equal rx1 rx2 -> forall a : A, P rx1 a -> P rx2 a) ->
      (* predicate extends when we add something using the function *)
      (forall (rex : re_xf_pair ty) (rx : rs_xf_pair ty) (a : A),
         P rx a -> P (add_xform rex rx) (f rex a)) ->
      forall (rx : rs_xf_pair ty) (accum : A),
        (* predicate holds on empty set and initial accumulator *)
        P (empty_xform ty) accum -> 
        P rx (fold_xform f rx accum).

  Definition set_cat_re (s:t) (r:regexp): t := 
    match r with
      | Eps => s (* not stricitly necessary; an optimization *)
      | Zero => empty
      | _ => fold (fun r1 s' => add (Cat r1 r) s') s empty
                        (* Note : will need to show that this is the same as
                          RESF.map (re_set_build_map (fun r1 => Cat r1 r)) s *)
   end.

  Parameter cat_re_xform: forall ty,
    rs_xf_pair ty -> 
    forall r:regexp, rs_xf_pair (Pair_t ty (regexp_type r)).
  Parameter cat_re_xform_erase: forall t rx1 r,
    projT1 (@cat_re_xform t rx1 r) = set_cat_re (projT1 rx1) r.
  Parameter cat_re_xform_corr: forall ty (rx:rs_xf_pair ty) r str v,
    in_re_set_xform (cat_re_xform rx r) str v <->
    exists str1 str2 v1 v2, str = str1++str2 /\ v=(v1,v2) /\
      in_re_set_xform rx str1 v1 /\ in_regexp r str2 v2.

  Parameter equal_xform : forall (s1 s2:t), 
    (Equal s1 s2) -> (re_set_type s1 ->> re_set_type s2).
  Parameter equal_xform_corr : 
    forall s1 s2 (H: Equal s1 s2) str v,
    in_re_set s1 str v <-> 
    in_re_set s2 str (xinterp (@equal_xform s1 s2 H) v).

  Parameter Equal_sym : forall s1 s2, Equal s1 s2 -> Equal s2 s1.

  Parameter equal_iso : forall (s1 s2:t) (H:Equal s1 s2) v, 
    (xinterp (equal_xform (Equal_sym H)) (xinterp (equal_xform H) v)) = v.

  Parameter equal_xform_corr2 : 
    forall rs1 rs2 (H:Equal rs1 rs2) ty (f:re_set_type rs1 ->> List_t ty) str v, 
      in_re_set_xform (existT _ rs1 f) str v <->
      in_re_set_xform (existT _ rs2 (xcomp (equal_xform (Equal_sym H)) f)) str v.

  Parameter re_set_extract_nil: forall s, list (interp (re_set_type s)).
  Parameter re_set_extract_nil_corr : 
    forall s (v : interp (re_set_type s)),
           in_re_set s nil v <-> List.In v (re_set_extract_nil s).
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

  Fixpoint tree_extract_nil (t:Raw.tree) : list (interp (tree_type t)) := 
    match t as t return list (interp (tree_type t)) with 
      | Raw.Leaf => nil
      | Raw.Node _ l x r => 
        let vl := tree_extract_nil l in 
        let vx := regexp_extract_nil x in 
              let vr := tree_extract_nil r in 
              (List.map (fun x => inl x) vl) ++ 
              (List.map (fun x => inr (inl x)) vx) ++ 
              (List.map (fun x => inr (inr x)) vr) 
    end.

  Lemma regexp_extract_nil_corr1 r str v : 
    in_regexp r str v -> str = nil -> List.In v (regexp_extract_nil r).
  Proof.
    induction 1 ; crush. generalize (app_eq_nil _ _ H3). crush.
    apply in_prod ; auto. rewrite in_app. left. rewrite in_map_iff. crush.
    rewrite in_app. right. rewrite in_map_iff. crush.
    generalize (app_eq_nil _ _ H4). crush.
  Qed.

  Lemma regexp_extract_nil_corr2 :
    forall r v, 
      List.In v (regexp_extract_nil r) -> in_regexp r nil v.
  Proof.
    induction r ; crush. destruct v. rewrite in_prod_iff in H. crush.
    rewrite in_app in H ; destruct H ; rewrite in_map_iff in H ; crush.
  Qed.

  Lemma tree_extract_nil_corr : forall tr v,
    in_tree tr nil v <-> List.In v (tree_extract_nil tr).
  Proof.
    unfold in_tree.
    induction tr ; simpl. intro ; destruct v.
    intro. destruct v as [v | [v | v]]. split. intro. 
    in_regexp_inv. injection H0 ; crush. rewrite in_app. left.
    eapply in_map. apply (proj1 (IHtr1 x)). auto.
    rewrite in_app. intros. destruct H. rewrite (in_map_iff) in H.
    crush. injection H ; crush. generalize (proj2 (IHtr1 v)). crush.
    rewrite in_app in H. destruct H. rewrite in_map_iff in H.
    crush. rewrite in_map_iff in H. crush.
    split. intros. in_regexp_inv. in_regexp_inv. injection H0 ; crush.
    rewrite in_app. right. rewrite in_app. left. rewrite in_map_iff. 
    econstructor ; crush. eapply regexp_extract_nil_corr1 ; eauto.
    rewrite in_app. rewrite in_app. repeat rewrite in_map_iff. crush.
    inversion H ; crush. eapply InAlt_r. eapply InAlt_l. 
    eapply regexp_extract_nil_corr2. eauto. eauto. auto.
    repeat rewrite in_app. repeat rewrite in_map_iff. crush.
    repeat in_regexp_inv. injection H0 ; crush. right ; right. 
    exists x0. split ; auto. eapply IHtr2. eauto.
    injection H ; crush. eapply InAlt_r ; eauto. eapply InAlt_r ; eauto.
    eapply IHtr2. auto.
  Qed.

  Definition re_set_extract_nil (s:t) : list (interp (re_set_type s)).
    destruct s. unfold re_set_type. apply tree_extract_nil.
  Defined.

  Lemma re_set_extract_nil_corr (s:t) (v:interp (re_set_type s)) :
    in_re_set s nil v <-> List.In v (re_set_extract_nil s).
  Proof.
    destruct s. simpl. unfold in_re_set. simpl. apply tree_extract_nil_corr.
  Qed.

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
                             (x:regexp) (fx : regexp_type x ->> List_t ty)                             (r:Raw.tree) (fr : tree_type r ->> List_t ty) : 
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
(* *)
(*     | [|- context[xinterp xcross _]] => rewrite xcross_corr; simpl *)
(*     | [H:context[xinterp xcross _] |- _] =>  *)
(*       rewrite xcross_corr in H; simpl in H *)
(* *)
    | [|- context [xinterp xapp (_,_)]] => rewrite xapp_corr; simpl
    | [H:context [xinterp xapp (_,_)] |- _] =>
      rewrite xapp_corr in H; simpl in H
    | [|- context [xinterp (xmap _) ?V]] =>
      rewrite (@xmap_corr _ _ _ V); simpl
    | [H:context [xinterp (xmap _) ?V] |- _] =>
      rewrite (@xmap_corr _ _ _ V) in H; simpl in H
(* *)
(*     | [|- context[xinterp xflatten _]] => rewrite xflatten_corr2; simpl *)
(*     | [H:context[xinterp xflatten _] |- _] =>  *)
(*       rewrite xflatten_corr2 in H; simpl in H *)
(* *)
  end.

  Lemma in_not_leaf : forall (r:regexp), Raw.In r Raw.Leaf -> False.
  Proof.
    unfold Raw.In. intros. inversion H.
  Qed.

   Lemma ok_left i (t1 t2:Raw.tree) (x:regexp) (ok : Raw.Ok (Raw.Node i t1 x t2)) : 
     Raw.Ok t1.
   Proof.
     unfold Raw.Ok in *. inversion ok. subst ; auto.
   Qed.     

   Lemma ok_right i (t1 t2:Raw.tree) (x:regexp) (ok : Raw.Ok (Raw.Node i t1 x t2)) : 
     Raw.Ok t2.
   Proof.
     unfold Raw.Ok in *. inversion ok. subst ; auto.
   Qed.

  Lemma in_left r i t1 t2 x :
        Raw.In r (Raw.Node i t1 x t2) ->
        (Raw.Ok (Raw.Node i t1 x t2)) -> 
        (REOrderedTypeAlt.compare r x = Lt) -> 
        Raw.In r t1.
  Proof.
    unfold Raw.In, Raw.Ok. intros.  
    inversion H ; inversion H0 ; subst ; clear H H0 ; try congruence.
    assert False ; [idtac | contradiction].
    specialize (H14 r H3). simpl in *. rewrite REOrderedTypeAlt.compare_sym in H14.
    rewrite H1 in H14. simpl in *. discriminate.
  Qed.    

  Lemma in_right r i t1 t2 x : 
        Raw.In r (Raw.Node i t1 x t2) ->
        (Raw.Ok (Raw.Node i t1 x t2)) -> 
        (REOrderedTypeAlt.compare r x = Gt) -> 
        Raw.In r t2.
  Proof.
    unfold Raw.In, Raw.Ok. intros.  
    inversion H ; inversion H0 ; subst ; clear H H0 ; try congruence.
    assert False ; [idtac | contradiction].
    specialize (H13 r H3). simpl in *. congruence.
  Qed.    

  Lemma cmp_leib : forall r1 r2, REOrderedTypeAlt.compare r1 r2 = Eq -> r1 = r2.
    apply compare_re_eq_leibniz.
  Qed.

  Lemma subset_corr t1 t2 : (Raw.Ok t1) -> (Raw.Ok t2) ->
    (Raw.subset t1 t2 = true <-> forall r, Raw.In r t1 -> Raw.In r t2).
  Proof.
    apply Raw.subset_spec.
  Qed.    

  Lemma subset_node i t_left r t_right t2 : 
    Raw.Ok (Raw.Node i t_left r t_right) ->
    Raw.Ok t2 ->
    Raw.subset (Raw.Node i t_left r t_right) t2 = true -> 
    Raw.subset t_left t2 = true /\ Raw.In r t2 /\ Raw.subset t_right t2 = true.
  Proof.
    intros. 
    generalize (ok_left H) (ok_right H). 
    rewrite subset_corr in H1 ; auto.
    intros ; split.
    rewrite subset_corr ; auto. intros. apply H1. eapply Raw.InLeft. auto.
    split. apply H1. econstructor. apply Raw.MX.compare_refl.
    rewrite subset_corr ; auto. intros. apply H1. eapply Raw.InRight. auto.
  Qed.

  (* Given a proof that r is in the tree t, extract an xform from
     regexp_type r to tree_type t. *)
  Fixpoint find_xform (t:Raw.tree) (r:regexp) : 
    Raw.Ok t -> Raw.In r t -> xform (regexp_type r) (tree_type t) := 
    match t as t' 
          return Raw.Ok t' -> Raw.In r t' -> xform (regexp_type r) (tree_type t') with
      | Raw.Leaf => fun Htok Hin => False_rect _ (in_not_leaf Hin)
      | Raw.Node _ ltree r' rtree => 
        fun Htok Hin => 
          match REOrderedTypeAlt.compare r r' as p 
                return (REOrderedTypeAlt.compare r r' = p) -> _
          with 
            | Eq => fun H3 => 
                      eq_rec_r
                        (fun r0 : regexp =>
                           regexp_type r0 ->> Sum_t (tree_type ltree) 
                                       (Sum_t (regexp_type r') (tree_type rtree)))
                            (xcomp xinl xinr) (cmp_leib r r' H3)
            | Lt => fun H2 => 
                      let x := find_xform (ok_left Htok) (in_left Hin Htok H2) 
                          in xcomp x xinl
            | Gt => fun H4 => 
                      let x := find_xform (ok_right Htok) (in_right Hin Htok H4)
                      in xcomp x (xcomp xinr xinr)
          end eq_refl
    end.

  Lemma find_xform_corr (r:regexp) (t:Raw.tree) : 
    forall (okt:Raw.Ok t) (Hinr:Raw.In r t)
        (str : list char_t )(v : interp (tree_type t)),
    (exists v', in_regexp r str v' /\ v = xinterp (@find_xform t r okt Hinr) v') 
    -> in_tree t str v.
  Proof.
    induction t ; crush. unfold Raw.In in Hinr. inversion Hinr.
    generalize (cmp_leib r t3).
    generalize (in_right Hinr okt).
    generalize (in_left Hinr okt).
    generalize (REOrderedTypeAlt.compare r t3).
    destruct c ; intros. generalize (e eq_refl). intros ; subst.
    unfold eq_rec_r, eq_rec, eq_rect, eq_sym. unfold in_tree. simpl ; eauto.
    specialize (IHt1 (ok_left okt) (i eq_refl) str). clear IHt2 i0 e.
    assert (exists v, in_tree t2 str v). econstructor. eapply IHt1.
    econstructor. eauto. crush. unfold in_tree in *. xinterp_simpl. crush. 
    clear IHt1 i e. specialize (IHt2 (ok_right okt) (i0 eq_refl) str). 
    unfold in_tree in *. simpl. eapply InAlt_r. eapply InAlt_r. eauto.
    eauto. xinterp_simpl. auto.
  Qed.

  (* Given trees t1 and r2 such that (subset t1 t2) produce a transform of the type
     tree_type t1 ->> tree_type t2. *)
  Fixpoint inject_xform_tree (t1 : Raw.tree) (t2 : Raw.tree) : 
         (Raw.Ok t1) -> (Raw.Ok t2) -> 
         (Raw.subset t1 t2 = true) -> (tree_type t1 ->> tree_type t2) := 
    match t1 as t1' return 
         (Raw.Ok t1') -> (Raw.Ok t2) -> 
         (Raw.subset t1' t2 = true) -> (tree_type t1' ->> tree_type t2)
    with 
      | Raw.Leaf => fun _ _ _ => xzero
      | Raw.Node _ t_left r t_right => 
        fun t1ok t2ok Hsub => 
          (xmatch (inject_xform_tree (ok_left t1ok) t2ok 
                                     (proj1 (subset_node t1ok t2ok Hsub)))
                  (xmatch 
                     (find_xform t2ok (proj1 (proj2 (subset_node t1ok t2ok Hsub))))
                     (inject_xform_tree (ok_right t1ok) t2ok 
                                        (proj2 (proj2 (subset_node t1ok t2ok Hsub))))))
    end.

  (* Prove that [inject_xform_tree] preserves the [in_tree] relation.  One
     direction is easy, but the other is not. *)
  Lemma inject_xform_tree_corr1 : 
    forall t1 t2 okt1 okt2 Hsub str v,
      in_tree t1 str v -> 
      in_tree t2 str (xinterp (@inject_xform_tree t1 t2 okt1 okt2 Hsub) v).
  Proof.
    induction t1 ; intros. destruct v. 
    unfold in_tree in *. simpl. 
    specialize (IHt1_1 _ (ok_left okt1) okt2 (proj1 (subset_node okt1 okt2 Hsub)) str).
    specialize (IHt1_2 _ (ok_right okt1) okt2 (proj2 (proj2 (subset_node okt1 okt2 Hsub)))
                       str).
    simpl in H. generalize (inv_alt H). clear H. intro. destruct H. clear IHt1_2.
    destruct H as [v1 [H1 H2]]. subst. xinterp_simpl. eapply IHt1_1 ; auto.
    destruct H as [v2 [H H2]] ; subst.
    generalize (inv_alt H) ; clear H ; intros ; subst. destruct H ;
    destruct H as [v1 [H1 H2]] ; subst. xinterp_simpl.
    apply (find_xform_corr okt2 (proj1 (proj2 (subset_node okt1 okt2 Hsub)))). eauto.
    xinterp_simpl. apply IHt1_2. auto.
  Qed.
  
  Definition inject_xform (s1 s2 : RESet.t) : 
    (RESet.subset s1 s2 = true) -> (re_set_type s1 ->> re_set_type s2).
  Proof.
    destruct s1 as [t1 okt1].
    destruct s2 as [t2 okt2]. unfold RESet.subset, re_set_type. simpl. 
    apply (inject_xform_tree okt1 okt2).
  Defined.

  Definition inject_xform_corr1 s1 s2 (Hsub : RESet.subset s1 s2 = true) str v : 
    in_re_set s1 str v -> 
    in_re_set s2 str (xinterp (inject_xform s1 s2 Hsub) v).
  Proof.    
    destruct s1 as [t1 okt1].
    destruct s2 as [t2 okt2]. 
    unfold RESet.subset, re_set_type, in_re_set in *. simpl in *.
    apply inject_xform_tree_corr1 ; auto.
  Qed.

  Definition equal_xform s1 s2 (H : RESet.Equal s1 s2) : re_set_type s1 ->> re_set_type s2.
    assert (RESet.subset s1 s2 = true).
    rewrite (RESet.subset_spec). intro. apply (proj1 (H a)). 
    apply (@inject_xform s1 s2 H0).
  Defined.

  Lemma Equal_sym s1 s2 : RESet.Equal s1 s2 -> RESet.Equal s2 s1.
  Proof.
    unfold RESet.Equal. crush. rewrite <- H. auto.
  Qed.
  
  Lemma Subset_node i t11 x t12 t2 : 
    Raw.Subset (Raw.Node i t11 x t12) t2 -> 
    Raw.Subset t11 t2 /\ Raw.In x t2 /\ Raw.Subset t12 t2.
  Proof.
    unfold Raw.Subset. intros. split. intros. apply H. eapply Raw.InLeft ; auto.
    split. apply H. eapply Raw.IsRoot. apply Raw.MX.compare_refl.
    intros. apply H. eapply Raw.InRight ; eauto.
  Qed.

  (* A [ctxt] is a tree with a single hole. *)
  Inductive ctxt := 
    | Hole : ctxt
    | LeftNode : Int.Z_as_Int.t -> ctxt -> REOrderedTypeAlt.t -> Raw.tree -> ctxt
    | RightNode : Int.Z_as_Int.t -> Raw.tree -> REOrderedTypeAlt.t -> ctxt -> ctxt.

  (* Filling a context's hole with a tree *)
  Fixpoint fill (c:ctxt) (t0:Raw.tree) {struct c} : Raw.tree := 
    match c with 
      | Hole => t0
      | LeftNode i c' x r => Raw.Node i (fill c' t0) x r
      | RightNode i l x c' => Raw.Node i l x (fill c' t0)
    end.

  (* fill a context's hole with another context *)
  Fixpoint fill_ctxt (c1 c2:ctxt) : ctxt := 
    match c1 with 
      | Hole => c2
      | LeftNode i c x r => LeftNode i (fill_ctxt c c2) x r
      | RightNode i l x c => RightNode i l x (fill_ctxt c c2)
    end.

  Lemma fill_ctxt_left c i l x r : 
    (fill c (Raw.Node i l x r)) = fill (fill_ctxt c (LeftNode i Hole x r)) l.
  Proof.
    induction c ; crush.
  Qed.

  Lemma fill_ctxt_right (c:ctxt) i (l:Raw.tree) x (r:Raw.tree) : 
    (fill c (Raw.Node i l x r)) = fill (fill_ctxt c (RightNode i l x Hole)) r.
  Proof.
    induction c ; crush.
  Qed.

  (* Used to simplify some casting. *)
  Lemma tree_eq t1 t2 : t1 = t2 -> tree_type t1 = tree_type t2.
    intros ; subst. auto.
  Defined.

  Lemma subset_ctxt c i l x r t : 
    Raw.Subset (fill c (Raw.Node i l x r)) t -> 
    Raw.Subset l t /\ Raw.In x t /\ Raw.Subset r t.
  Proof. 
    induction c ; simpl ; intros. apply (Subset_node H).
    apply IHc. generalize (Subset_node H). crush.
    apply IHc. generalize (Subset_node H). crush.
  Qed.

  Lemma subset_fill_left {c i l x r t2} : 
    Raw.Subset (fill c (Raw.Node i l x r)) t2 -> 
    Raw.Subset (fill (fill_ctxt c (LeftNode i Hole x r)) l) t2.
  Proof.
    rewrite <- fill_ctxt_left. auto.
  Qed.

  Lemma subset_fill_right {c i l x r t2} : 
    Raw.Subset (fill c (Raw.Node i l x r)) t2 -> 
    Raw.Subset (fill (fill_ctxt c (RightNode i l x Hole)) r) t2.
  Proof.
    rewrite <- fill_ctxt_right. auto.
  Qed.

  Lemma ok_fill_left {c i l x r} : 
    Raw.Ok (fill c (Raw.Node i l x r)) -> 
    Raw.Ok (fill (fill_ctxt c (LeftNode i Hole x r)) l).
  Proof.
    rewrite <- fill_ctxt_left. auto.
  Qed.

  Lemma ok_fill_right {c i l x r} : 
    Raw.Ok (fill c (Raw.Node i l x r)) -> 
    Raw.Ok (fill (fill_ctxt c (RightNode i l x Hole)) r).
  Proof.
    rewrite <- fill_ctxt_right. auto.
  Qed.

  Lemma fill_in {c i l x r t2} : 
    Raw.Subset (fill c (Raw.Node i l x r)) t2 -> Raw.In x t2.
  Proof.
    intro.
    generalize (subset_ctxt _ _ _ _ _ H). crush.
  Qed.

  Definition cast {t1 t2:Type} : (t1 = t2) -> t1 -> t2.
    intro ; subst. apply (fun x => x).
  Defined.

  Definition interp_eq {t1 t2} : t1 = t2 -> interp t1 = interp t2.
    intros. subst. auto.
  Defined.

  Lemma in_ctxt {i l x r c t} : 
    Raw.Ok t -> 
    t = fill c (Raw.Node i l x r) -> 
    Raw.In x t.
  Proof.
    intros. subst.
    induction c ; simpl ; intros. eapply Raw.IsRoot. apply Raw.MX.compare_refl.
    inversion H. subst. eapply Raw.InLeft. eapply IHc. auto.
    inversion H. subst. eapply Raw.InRight. eapply IHc. auto.
  Qed.

  Lemma lt_trans_sub_node {y i l x r} : 
    Raw.Ok (Raw.Node i l x r) -> 
    Raw.lt_tree y (Raw.Node i l x r) -> Raw.lt_tree y l.
  Proof.
    intros. inversion H ; subst ; clear H. eapply Raw.lt_tree_trans ; eauto.
    remember_rev (REOrderedTypeAlt.compare x y) as c ; destruct c ; auto.
    generalize (cmp_leib _ _ Hc) ; intros ; subst.
    contradiction (Raw.lt_tree_not_in y (Raw.Node i l y r)). econstructor.
    eapply Raw.MX.compare_refl.
    specialize (H0 x). simpl in *. rewrite H0 in Hc ; auto. econstructor.
    eapply Raw.MX.compare_refl.
  Qed.

  Lemma lt_fill {i l x r y c} : 
    Raw.Ok (fill c (Raw.Node i l x r)) -> 
    Raw.lt_tree y (fill c (Raw.Node i l x r)) -> 
    REOrderedTypeAlt.compare x y = Lt.
  Proof.
    intros. apply (H0 x). eapply in_ctxt. auto. eauto.
  Qed.

  Lemma ok_fill_left_lt {i l x r c j y r'} : 
    Raw.Ok (Raw.Node j (fill c (Raw.Node i l x r)) y r') -> 
    REOrderedTypeAlt.compare x y = Lt.
  Proof. 
    intros. inversion H. subst. eapply lt_fill ; eauto.
  Qed.

  Lemma gt_fill {i l x r y c} : 
    Raw.Ok (fill c (Raw.Node i l x r)) -> 
    Raw.gt_tree y (fill c (Raw.Node i l x r)) -> 
    REOrderedTypeAlt.compare x y = Gt.
  Proof.
    intros. specialize (H0 x). simpl in H0. 
    specialize (H0 (@in_ctxt i l x r c _ H eq_refl)). 
    rewrite (REOrderedTypeAlt.compare_sym). rewrite H0 ; auto.
  Qed.

  Lemma ok_fill_right_gt {i l x r c j l' y} : 
    Raw.Ok (Raw.Node j l' y (fill c (Raw.Node i l x r))) -> 
    REOrderedTypeAlt.compare x y = Gt.
  Proof.
    intros. inversion H ; subst ; clear H. eapply gt_fill ; eauto.
  Qed.

  Lemma in_find_form x str vx t2 (t2ok : Raw.Ok t2) (Hin : Raw.In x t2) : 
    in_tree t2 str (xinterp (find_xform t2ok Hin) vx) -> 
    in_regexp x str vx.
  Proof.
    unfold in_tree. induction t2. simpl. intros. in_regexp_inv.
    rename t0 into i. rename t1 into y.
    inversion Hin. subst. simpl.
    (* IsRoot *)
    generalize (cmp_leib x y). generalize (in_left Hin t2ok).
    generalize (in_right Hin t2ok). rewrite H0. intros.
    assert (x = y) ; auto. subst.
    rewrite (@proof_irrelevance _ (e eq_refl) eq_refl) in H. 
    unfold eq_rec_r, eq_rec, eq_rect, eq_sym in H. xinterp_simpl ; simpl in H.
    in_regexp_inv. in_regexp_inv. 
    (* InLeft *)
    subst. simpl. specialize (IHt2_1 (ok_left t2ok)). clear IHt2_2.
    generalize (cmp_leib x y) (in_left Hin t2ok) (in_right Hin t2ok).
    assert (REOrderedTypeAlt.compare x y = Lt).
    clear IHt2_1 ; inversion t2ok ; subst ; clear t2ok. clear Hin.
    remember_rev (REOrderedTypeAlt.compare x y) as c. destruct c ; auto.
    generalize (cmp_leib _ _ Hc) ; intros ; subst. 
    contradiction (Raw.lt_tree_not_in y t2_1).
    contradiction (Raw.lt_tree_not_in x t2_1). eapply Raw.lt_tree_trans ; eauto.
    rewrite REOrderedTypeAlt.compare_sym. rewrite Hc. auto. rewrite H. intros.
    xinterp_simpl. in_regexp_inv. injection H2 ; intros ; subst. clear H2.
    eauto. 
    (* InRight *)
    subst. simpl. specialize (IHt2_2 (ok_right t2ok)). clear IHt2_1.
    generalize (cmp_leib x y) (in_left Hin t2ok) (in_right Hin t2ok).
    assert (REOrderedTypeAlt.compare x y = Gt). 
    clear IHt2_2 ; inversion t2ok ; subst ; clear t2ok ; clear Hin.
    remember_rev (REOrderedTypeAlt.compare x y) as c ; destruct c ; auto.
    generalize (cmp_leib _ _ Hc) ; intros ; subst.
    contradiction (Raw.gt_tree_not_in y t2_2) ; auto.
    contradiction (Raw.gt_tree_not_in x t2_2). eapply Raw.gt_tree_trans ; auto. eauto.
    auto. rewrite H. intros. xinterp_simpl. in_regexp_inv.
    injection H2 ; intros ; subst ; clear H2. in_regexp_inv.
    injection H2 ; intros ; subst ; clear H2. eauto.
  Qed.                                                

  (* This is the key lemma for showing that [inject_xform_tree] preserves
   * the [in_tree] relation.  If [t1] and [t2] are equivalent trees, and
   * [in_tree t2 str (xinterp (inject_xform_tree t1 t2) v)] holds, then
   * we know that (a) there is some [x] in both [t1] and [t2] and a [vx] 
   * such that [in_tree x str vx], (b) [t1 = fill C [Node l x r]] for
   * some context [C] and trees [l] and [r], and (c) [v] can be obtained
   * by mapping [vx] into [t1] by calling [find_xform].
   *)
  Lemma inject_deconstruct t2 (okt2:Raw.Ok t2) str : 
    forall t1 (okt1:Raw.Ok t1) (Hsub1:Raw.subset t1 t2 = true) (v:interp (tree_type t1)),
    in_tree t2 str (xinterp (inject_xform_tree okt1 okt2 Hsub1) v) -> 
    exists i1, exists l1, exists x, exists r1, exists vx, exists c1,
    exists (H: t1 = fill c1 (Raw.Node i1 l1 x r1)), 
      in_regexp x str vx /\
      v = xinterp (find_xform okt1 (in_ctxt okt1 H)) vx.
  Proof.
    Opaque Raw.subset. unfold in_tree.
    induction t1 ; intros. destruct v. 
    specialize (IHt1_1 (ok_left okt1) (proj1 (subset_node okt1 okt2 Hsub1))).
    specialize (IHt1_2 (ok_right okt1) (proj2 (proj2 (subset_node okt1 okt2 Hsub1)))).
    simpl in H. destruct v as [v | v]. 
    clear IHt1_2. assert (in_regexp (tree_to_regexp t2) str
                           ((xinterp (inject_xform_tree (ok_left okt1) okt2
                             (proj1 (subset_node okt1 okt2 Hsub1)))) v)).
    xinterp_simpl  ; auto. clear H.
    specialize (IHt1_1 v H0). clear H0.
    destruct IHt1_1 as [i1 [l1 [x [r1 [vx [c1 [H1 [H2 H3]]]]]]]].
    exists i1. exists l1. exists x. exists r1. exists vx. 
    exists (LeftNode t0 c1 t1 t1_2). 
    assert (Raw.Node t0 t1_1 t1 t1_2 = fill (LeftNode t0 c1 t1 t1_2) (Raw.Node i1 l1 x r1)).
    subst ; auto. exists H. split. auto.
    generalize (in_ctxt okt1 H). intro H0. clear H. subst.
    simpl. generalize (cmp_leib x t1). generalize (in_left H0 okt1).
    generalize (in_right H0 okt1). rename t1 into y. rename t0 into j.
    rewrite (ok_fill_left_lt okt1).
    intros. xinterp_simpl. 
    rewrite (@proof_irrelevance _ (in_ctxt (ok_left okt1) eq_refl) (i0 eq_refl)). auto.
    destruct v as [vx | v].
    clear IHt1_1 IHt1_2. rename t0 into i. rename t1 into x.
    xinterp_simpl. simpl in H. xinterp_simpl. simpl in H. 
    exists i. exists t1_1. exists x. exists t1_2. exists vx. exists Hole.
    exists eq_refl. split. 
    apply (@in_find_form x str vx t2 okt2 _ H).
    generalize (cmp_leib x x).
    generalize (@in_left x i t1_1 t1_2 x 
                         (@in_ctxt i t1_1 x t1_2 Hole (Raw.Node i t1_1 x t1_2)
                                   okt1 (@eq_refl Raw.tree (Raw.Node i t1_1 x t1_2)))).
    generalize (@in_right x i t1_1 t1_2 x
                     (@in_ctxt i t1_1 x t1_2 Hole (Raw.Node i t1_1 x t1_2)
                        okt1 (@eq_refl Raw.tree (Raw.Node i t1_1 x t1_2)))).
    rewrite (Raw.MX.compare_refl x). intros. 
    rewrite (@proof_irrelevance _ (e eq_refl) eq_refl). 
    unfold eq_rec_r, eq_rec, eq_rect, eq_sym. xinterp_simpl. auto.
    clear IHt1_1. assert (in_regexp (tree_to_regexp t2) str
                          (xinterp (inject_xform_tree (ok_right okt1) okt2
                           (proj2 (proj2 (subset_node okt1 okt2 Hsub1)))) v)).
    xinterp_simpl. simpl in H. xinterp_simpl. simpl in H. auto. clear H.
    specialize (IHt1_2 v H0). clear H0.
    destruct IHt1_2 as [i1 [l1 [x [r1 [vx [c1 [H1 [H2 H3]]]]]]]].
    exists i1. exists l1. exists x. exists r1. exists vx.
    exists (RightNode t0 t1_1 t1 c1). subst. 
    assert (Raw.Node t0 t1_1 t1 (fill c1 (Raw.Node i1 l1 x r1)) =
         fill (RightNode t0 t1_1 t1 c1) (Raw.Node i1 l1 x r1)). subst ; auto.
    exists H. split ; auto.
    simpl. generalize (cmp_leib x t1) (in_left (in_ctxt okt1 H) okt1).
    generalize (in_right (in_ctxt okt1 H) okt1).
    rewrite (ok_fill_right_gt okt1). intros ; xinterp_simpl.
    rewrite (@proof_irrelevance _ (in_ctxt (ok_right okt1) eq_refl) (i eq_refl)).
    auto.
  Qed.

  (* The other half showing that [inject_xform_tree] preserves the [in_tree]
   * relation. *)
  Lemma inject_xform_tree_corr2 : 
    forall t1 (okt1:Raw.Ok t1) t2 (okt2:Raw.Ok t2) 
           Hsub1 (Hsub2:Raw.subset t2 t1 = true) str v,
      in_tree t2 str (xinterp (inject_xform_tree okt1 okt2 Hsub1) v) ->
      in_tree t1 str v.
  Proof.
    intros. 
    specialize (@inject_deconstruct t2 okt2 str t1 okt1 Hsub1 v H).
    intros. destruct H0 as [i [l [x [r [vx [c [H1 [H2 H3]]]]]]]].
    clear H. subst. generalize c okt1 ; clear c okt1 Hsub1 Hsub2 okt2.
    induction c ; intro okt1. simpl.
    generalize (cmp_leib x x). 
    generalize (@in_left x i l r x
                     (@in_ctxt i l x r Hole (Raw.Node i l x r) okt1
                        (@eq_refl Raw.tree (Raw.Node i l x r)))).   
    generalize (@in_right x i l r x
                     (@in_ctxt i l x r Hole (Raw.Node i l x r) okt1
                        (@eq_refl Raw.tree (Raw.Node i l x r)))).
    rewrite Raw.MX.compare_refl. intros. rewrite (@proof_irrelevance _ (e eq_refl) eq_refl).
    unfold eq_rec_r, eq_rec, eq_rect, eq_sym. xinterp_simpl. unfold in_tree. 
    simpl. eauto.
    simpl. rename t0 into j. rename t1 into y.
    generalize (cmp_leib x y). 
    generalize (@in_left x j (fill c (Raw.Node i l x r)) t3 y
                     (@in_ctxt i l x r (LeftNode j c y t3)
                        (Raw.Node j (fill c (Raw.Node i l x r)) y t3) okt1
                        (@eq_refl Raw.tree
                           (Raw.Node j (fill c (Raw.Node i l x r)) y t3)))
                     okt1).
    generalize (@in_right x j (fill c (Raw.Node i l x r)) t3 y
                     (@in_ctxt i l x r (LeftNode j c y t3)
                        (Raw.Node j (fill c (Raw.Node i l x r)) y t3) okt1
                        (@eq_refl Raw.tree
                           (Raw.Node j (fill c (Raw.Node i l x r)) y t3)))
                     okt1).
    rewrite (ok_fill_left_lt okt1). intros.
    specialize (IHc (ok_left okt1)). unfold in_tree in *.
    eapply InAlt_l. fold tree_to_regexp. eapply IHc.
    rewrite (@proof_irrelevance _ (i1 eq_refl) 
                                (in_ctxt (ok_left okt1) eq_refl)).
    xinterp_simpl. auto.
    simpl. generalize (cmp_leib x t3). 
    generalize (@in_left x t0 t1 (fill c (Raw.Node i l x r)) t3
                     (@in_ctxt i l x r (RightNode t0 t1 t3 c)
                        (Raw.Node t0 t1 t3 (fill c (Raw.Node i l x r))) okt1
                        (@eq_refl Raw.tree
                           (Raw.Node t0 t1 t3 (fill c (Raw.Node i l x r)))))
                     okt1).
    generalize (@in_right x t0 t1 (fill c (Raw.Node i l x r)) t3
                     (@in_ctxt i l x r (RightNode t0 t1 t3 c)
                        (Raw.Node t0 t1 t3 (fill c (Raw.Node i l x r))) okt1
                        (@eq_refl Raw.tree
                           (Raw.Node t0 t1 t3 (fill c (Raw.Node i l x r)))))
                     okt1).
    rewrite (ok_fill_right_gt okt1). intros. 
    specialize (IHc (ok_right okt1)). unfold in_tree in *.
    eapply InAlt_r. eapply InAlt_r. fold tree_to_regexp. eapply IHc.
    eauto. rewrite (@proof_irrelevance _ (i0 eq_refl)
                                       (in_ctxt (ok_right okt1) eq_refl)). 
    xinterp_simpl. auto.
  Qed.   

  Lemma inject_xform_tree_corr : 
    forall t1 t2 okt1 okt2 Hsub1 (Hsub2:Raw.subset t2 t1 = true) str v, 
       in_tree t1 str v <-> 
       in_tree t2 str (xinterp (@inject_xform_tree t1 t2 okt1 okt2 Hsub1) v).
  Proof.
    intros ; split. apply inject_xform_tree_corr1. apply inject_xform_tree_corr2. auto.
  Qed.

  Lemma inject_deconstruct2 :
    forall t1 (okt1:Raw.Ok t1) (v:interp (tree_type t1)),
    exists i1, exists l1, exists x, exists r1, exists vx, exists c1,
    exists (H: t1 = fill c1 (Raw.Node i1 l1 x r1)), 
      v = xinterp (find_xform okt1 (in_ctxt okt1 H)) vx.
  Proof.
    Opaque Raw.subset.
    induction t1 ; simpl ; intros. destruct v.
    intros.
    specialize (IHt1_1 (ok_left okt1)).
    specialize (IHt1_2 (ok_right okt1)). 
    destruct v as [vl | [vx | vr]].
    (* v = inl vl *)
    clear IHt1_2. specialize (IHt1_1 vl). 
    destruct IHt1_1 as [i1 [l1 [x [r1 [vx [c1 [H1 H3]]]]]]].
    exists i1. exists l1. exists x. exists r1. exists vx.
    exists (LeftNode t0 c1 t1 t1_2). 
    assert (Raw.Node t0 t1_1 t1 t1_2 = fill (LeftNode t0 c1 t1 t1_2) (Raw.Node i1 l1 x r1)).
    subst ; auto. exists H. generalize (in_ctxt okt1 H). clear H. subst ; simpl. intro.
    generalize (cmp_leib x t1). generalize (in_left i okt1). generalize (in_right i okt1).
    clear i. rewrite (ok_fill_left_lt okt1). intros. xinterp_simpl.
    rewrite (@proof_irrelevance _ (in_ctxt (ok_left okt1) eq_refl) (i0 eq_refl)). auto.
    (* v = inr (inl vx) *)
    clear IHt1_1 IHt1_2. rename t0 into i. rename t1 into x.
    exists i. exists t1_1. exists x. exists t1_2. exists vx. exists Hole. 
    exists eq_refl. generalize (cmp_leib x x).
    generalize (@in_left x i t1_1 t1_2 x 
                         (@in_ctxt i t1_1 x t1_2 Hole (Raw.Node i t1_1 x t1_2)
                                   okt1 (@eq_refl Raw.tree (Raw.Node i t1_1 x t1_2)))).
    generalize (@in_right x i t1_1 t1_2 x
                     (@in_ctxt i t1_1 x t1_2 Hole (Raw.Node i t1_1 x t1_2)
                        okt1 (@eq_refl Raw.tree (Raw.Node i t1_1 x t1_2)))).
    rewrite (Raw.MX.compare_refl x). intros.
    rewrite (@proof_irrelevance _ (e eq_refl) eq_refl). 
    unfold eq_rec_r, eq_rec, eq_rect, eq_sym. xinterp_simpl. auto.
    (* v = inr (inr vr) *)
    clear IHt1_1. specialize (IHt1_2 vr).
    destruct IHt1_2 as [i1 [l1 [x [r1 [vx [c1 [H1 H2]]]]]]].
    exists i1. exists l1. exists x. exists r1. exists vx. exists (RightNode t0 t1_1 t1 c1).
    assert (Raw.Node t0 t1_1 t1 t1_2 = 
            fill (RightNode t0 t1_1 t1 c1) (Raw.Node i1 l1 x r1)).
    subst. auto. exists H.
    generalize (cmp_leib x t1).
    generalize (in_left (in_ctxt okt1 H) okt1).
    generalize (in_right (in_ctxt okt1 H) okt1). clear H. subst.
    rewrite (ok_fill_right_gt okt1). intros.
    xinterp_simpl.
    rewrite (@proof_irrelevance _ (in_ctxt (ok_right okt1) eq_refl) (i eq_refl)). auto.
  Qed.

(*
  Lemma find_xform_injective : 
    forall x1 x2 t1 (okt1: Raw.Ok t1) (Hin1:Raw.In x1 t1) (Hin2:Raw.In x2 t1) v1 v2,
      (xinterp (find_xform okt1 Hin1) v1 = xinterp (find_xform okt1 Hin2) v2) -> 
      v1 = v2.
  Proof.
    induction t1. simpl. intros. inversion Hin1.
    simpl. intros okt1 Hin1 Hin2 v1 v2. 
    rewrite (@proof_irrelevance _ Hin2 Hin1).
    generalize (cmp_leib x t1).
    generalize (in_left Hin1 okt1) (in_right Hin1 okt1).
    remember (REOrderedTypeAlt.compare x t1) as cmp.
    destruct cmp. intros.
    assert (x = t1) ; auto ; subst. 
    rewrite (@proof_irrelevance _ (e eq_refl) eq_refl) in H.
    unfold eq_rec_r, eq_rec, eq_rect, eq_sym in H. xinterp_simpl.
    congruence.
    intros. xinterp_simpl. injection H ; intros ; clear H.
    apply (IHt1_1 _ _ _ _ _ H0).
    intros. xinterp_simpl. injection H ; intros ; clear H.
    apply (IHt1_2 _ _ _ _ _ H0).
  Qed.
*)

  Lemma inject_is_find_xform : 
    forall i1 l1 x r1 (okt1 : Raw.Ok (Raw.Node i1 l1 x r1)) (vx:interp (regexp_type x))
           t2 (okt2: Raw.Ok t2) (Hsub : Raw.subset t2 (Raw.Node i1 l1 x r1) = true) 
           (Hin : Raw.In x t2), 
      xinterp (inject_xform_tree okt2 okt1 Hsub) 
              (xinterp (find_xform okt2 Hin) vx) = inr (inl vx).
  Proof.
    induction t2 ; simpl ; intros. inversion Hin.
    xinterp_simpl. 
    generalize (cmp_leib x t1). generalize (cmp_leib t1 x).
    generalize (in_left Hin okt2) (in_right Hin okt2)
               (proj1 (subset_node okt2 okt1 Hsub))
               (in_left (proj1 (proj2 (subset_node okt2 okt1 Hsub))) okt1)
               (in_right (proj1 (proj2 (subset_node okt2 okt1 Hsub))) okt1)
               (proj2 (proj2 (subset_node okt2 okt1 Hsub))).
    rewrite (REOrderedTypeAlt.compare_sym x t1).
    remember_rev (REOrderedTypeAlt.compare x t1) as cmp.
    destruct cmp ; simpl ; intros.
    (* cmp = Eq *)
    assert (x = t1) ; auto ; subst. rewrite (@proof_irrelevance _ (e2 eq_refl) eq_refl).
    rewrite (@proof_irrelevance _ (e1 eq_refl) eq_refl).
    unfold eq_rec_r, eq_rec, eq_rect, eq_sym. xinterp_simpl. auto.
    (* cmp = Lt *)
    xinterp_simpl. eapply IHt2_1.
    (* cmp = Gt *)
    xinterp_simpl. eapply IHt2_2.
  Qed.

  Lemma fill_is_in {c i l x r t} : 
    fill c (Raw.Node i l x r) = t -> 
    Raw.In x t.
  Proof.
    intro ; subst.
    apply (@fill_in c i l x r (fill c (Raw.Node i l x r))). 
    intro. auto.
  Qed.

  Fixpoint find_subtree' (t1:Raw.tree) (c1:ctxt) {struct c1} : 
    tree_type t1 ->> tree_type (fill c1 t1) := 
      match c1 as c1 return tree_type t1 ->> tree_type (fill c1 t1)
      with 
        | Hole => xid
        | LeftNode i c1' x r => 
          xcomp (find_subtree' t1 c1') xinl
        | RightNode i l x c1' => 
          xcomp (find_subtree' t1 c1') (xcomp xinr xinr)
      end.

  Definition find_subtree t t1 c1 (H:fill c1 t1 = t) : tree_type t1 ->> tree_type t := 
    xcoerce (find_subtree' t1 c1) eq_refl (tree_eq H).

  Lemma in_gives_ctxt :
    forall x t1,
      Raw.In x t1 ->
      exists c, exists i, exists l, exists r, 
         fill c (Raw.Node i l x r) = t1.
  Proof.                                                
    induction t1 ; simpl ; intros ; inversion H ; subst.
    assert (t1 = x). rewrite (cmp_leib x t1 H1). auto. subst. clear H1.
    exists Hole. repeat econstructor ; eauto.
    specialize (IHt1_1 H1). crush. 
    exists (LeftNode t0 x0 t1 t1_2). simpl. repeat econstructor ; eauto.
    specialize (IHt1_2 H1). crush.
    exists (RightNode t0 t1_1 t1 x0). simpl. repeat econstructor ; eauto.
  Qed.

  Lemma inject_find_is_find : 
    forall x vx i1 l1 r1 i2 l2 r2 c2 (okt2:Raw.Ok (fill c2 (Raw.Node i2 l2 x r2)))
      c1 (okt1 :Raw.Ok (fill c1 (Raw.Node i1 l1 x r1))) Hsub1,
    (xinterp (inject_xform_tree okt1 okt2 Hsub1)
             (xinterp (find_xform okt1 (in_ctxt okt1 eq_refl)) vx) = 
     xinterp (find_xform okt2 (in_ctxt okt2 eq_refl)) vx).
  Proof.
    induction c1 ; simpl ; intros.
    (* c1 = Hole *)
    generalize (cmp_leib x x).
    generalize (@in_left x i1 l1 r1 x
                        (@in_ctxt i1 l1 x r1 Hole (Raw.Node i1 l1 x r1) okt1
                           (@eq_refl Raw.tree (Raw.Node i1 l1 x r1))) okt1)
               (@in_right x i1 l1 r1 x
                          (@in_ctxt i1 l1 x r1 Hole (Raw.Node i1 l1 x r1) okt1
                                    (@eq_refl Raw.tree (Raw.Node i1 l1 x r1))) okt1).
    generalize (proj1 (subset_node okt1 okt2 Hsub1))
               (proj2 (proj2 (subset_node okt1 okt2 Hsub1)))
               (proj1 (proj2 (subset_node okt1 okt2 Hsub1))).

    rewrite Raw.MX.compare_refl. intros.
    rewrite (@proof_irrelevance _ (e1 eq_refl) eq_refl).
    xinterp_simpl. 
    rewrite (@proof_irrelevance _ i 
              (@in_ctxt i2 l2 x r2 c2 (fill c2 (Raw.Node i2 l2 x r2)) okt2
                (@eq_refl Raw.tree (fill c2 (Raw.Node i2 l2 x r2))))). auto.
    (* c1 = LeftNode *)
    xinterp_simpl.
    generalize (cmp_leib x t1).
    generalize (@in_left x t0 (fill c1 (Raw.Node i1 l1 x r1)) t2 t1
                      (@in_ctxt i1 l1 x r1 (LeftNode t0 c1 t1 t2)
                         (Raw.Node t0 (fill c1 (Raw.Node i1 l1 x r1)) t1 t2)
                         okt1
                         (@eq_refl Raw.tree
                            (Raw.Node t0 (fill c1 (Raw.Node i1 l1 x r1)) t1 t2))) okt1).
    generalize (@in_right x t0 (fill c1 (Raw.Node i1 l1 x r1)) t2 t1
                      (@in_ctxt i1 l1 x r1 (LeftNode t0 c1 t1 t2)
                         (Raw.Node t0 (fill c1 (Raw.Node i1 l1 x r1)) t1 t2)
                         okt1
                         (@eq_refl Raw.tree
                            (Raw.Node t0 (fill c1 (Raw.Node i1 l1 x r1)) t1 t2))) okt1).
    generalize (proj1 (subset_node okt1 okt2 Hsub1))
               (proj2 (proj2 (subset_node okt1 okt2 Hsub1)))
               (proj1 (proj2 (subset_node okt1 okt2 Hsub1))).
    remember_rev (REOrderedTypeAlt.compare x t1) as cmp.
    destruct cmp.
      (* cmp = Eq -- contradiction *)
      assert False. assert (t1 = x). symmetry. apply (cmp_leib _ _ Hcmp). subst.
      clear Hcmp IHc1. inversion okt1. subst.
      apply (Raw.lt_tree_not_in x (fill c1 (Raw.Node i1 l1 x r1))) ; auto.
      apply (fill_is_in eq_refl). contradiction.
      (* cmp = Lt *)
      intros. xinterp_simpl. specialize (IHc1 (ok_left okt1) e).
      rewrite (@proof_irrelevance _ (in_ctxt (ok_left okt1) eq_refl) (i3 eq_refl)) in IHc1.
      auto.
      (* cmp = Gt -- contradiction *)
      assert False. inversion okt1. subst.
      apply (Raw.lt_tree_not_in x (fill c1 (Raw.Node i1 l1 x r1))).
      eapply Raw.lt_tree_trans ; eauto. rewrite (REOrderedTypeAlt.compare_sym).
      rewrite Hcmp. auto. apply (fill_is_in eq_refl). contradiction.
   (* c1 = RightNode *)
   xinterp_simpl.
   generalize (cmp_leib x t2).
   generalize (@in_left x t0 t1 (fill c1 (Raw.Node i1 l1 x r1)) t2
                      (@in_ctxt i1 l1 x r1 (RightNode t0 t1 t2 c1)
                         (Raw.Node t0 t1 t2 (fill c1 (Raw.Node i1 l1 x r1)))
                         okt1
                         (@eq_refl Raw.tree
                            (Raw.Node t0 t1 t2 (fill c1 (Raw.Node i1 l1 x r1))))) okt1).
   generalize (@in_right x t0 t1 (fill c1 (Raw.Node i1 l1 x r1)) t2
                      (@in_ctxt i1 l1 x r1 (RightNode t0 t1 t2 c1)
                         (Raw.Node t0 t1 t2 (fill c1 (Raw.Node i1 l1 x r1)))
                         okt1
                         (@eq_refl Raw.tree
                            (Raw.Node t0 t1 t2 (fill c1 (Raw.Node i1 l1 x r1))))) okt1).
   generalize (proj1 (subset_node okt1 okt2 Hsub1))
               (proj2 (proj2 (subset_node okt1 okt2 Hsub1)))
               (proj1 (proj2 (subset_node okt1 okt2 Hsub1))).
    remember_rev (REOrderedTypeAlt.compare x t2) as cmp.
    destruct cmp.
      (* cmp = Eq -- contradiction *)
      assert False. assert (t2 = x). symmetry. apply (cmp_leib _ _ Hcmp). subst.
      clear Hcmp IHc1. inversion okt1. subst.
      apply (Raw.gt_tree_not_in x (fill c1 (Raw.Node i1 l1 x r1))) ; auto.
      apply (fill_is_in eq_refl). contradiction.
      (* cmp = Lt -- contradiction *)
      assert False. inversion okt1. subst.
      apply (Raw.gt_tree_not_in x (fill c1 (Raw.Node i1 l1 x r1))).
      eapply Raw.gt_tree_trans ; eauto. apply (fill_is_in eq_refl). contradiction.
      (* cmp = Gt *)
      intros. xinterp_simpl. specialize (IHc1 (ok_right okt1) e0).
      rewrite (@proof_irrelevance _ (in_ctxt (ok_right okt1) eq_refl) (i0 eq_refl)) in IHc1.
      auto.
  Qed.

  Lemma inject_tree_iso : 
    forall t1 (okt1:Raw.Ok t1) t2 (okt2:Raw.Ok t2) Hsub1 Hsub2 (v:interp (tree_type t1)), 
      xinterp (inject_xform_tree okt2 okt1 Hsub2)
         (xinterp (inject_xform_tree okt1 okt2 Hsub1) v) = v.
  Proof.
    intros.
    generalize (@inject_deconstruct2 t1 okt1 v).
    intros. destruct H as [i1 [l1 [x [r1 [vx [c1 [H1 H2]]]]]]]. 
    assert (Raw.In x t2).
    rewrite (Raw.subset_spec) in Hsub1 ; auto. apply (Hsub1 x). subst.
    apply (fill_is_in eq_refl). 
    specialize (in_gives_ctxt H). intros.
    destruct H0 as [c2 [i2 [l2 [r2 H0]]]].  subst.
    rewrite inject_find_is_find. rewrite inject_find_is_find. auto.
  Qed.

  Lemma xcoerce_refl t1 t2 (x:t1 ->> t2) : 
    xcoerce x eq_refl eq_refl = x.
  Proof.
    auto.
  Qed.

  Lemma xcoerce_cod : 
    forall t1 t2 t3 (x:t1 ->> t2) (H:t2 = t3) (v:interp t1),
      xinterp (xcoerce x eq_refl H) v = 
      cast (interp_eq H) (xinterp x v).
  Proof.
    intros. subst. rewrite xcoerce_refl. auto.
  Qed.

  Lemma equal_iso s1 s2 (H:Equal s1 s2) v : 
    (xinterp (equal_xform (Equal_sym H)) 
      (xinterp (equal_xform H) v)) = v.
  Proof.
    destruct s1 as [t1 okt1].
    destruct s2 as [t2 okt2].
    unfold equal_xform. simpl. apply inject_tree_iso.
  Qed.    

  (* Lift up from trees to sets *)
  Lemma equal_xform_corr : 
    forall s1 s2 (H:Equal s1 s2) str v,
      in_re_set s1 str v <-> in_re_set s2 str (xinterp (@equal_xform s1 s2 H) v).
  Proof.
    destruct s1 as [s1 okt1]. 
    destruct s2 as [s2 okt2]. 
    unfold Equal, in_re_set, equal_xform, inject_xform. simpl.
    intros. apply inject_xform_tree_corr. rewrite (Raw.subset_spec) ; auto.
    intro. intro. specialize (H a). tauto.
  Qed.

  Lemma equal_xform_corr2 rs1 rs2 (H:Equal rs1 rs2)
     ty (f:re_set_type rs1 ->> List_t ty) str v:
    in_re_set_xform (existT _ rs1 f) str v <->
    in_re_set_xform
      (existT _ rs2 (xcomp (equal_xform (Equal_sym H)) f)) str v.
  Proof.
    specialize (equal_xform_corr H str). unfold in_re_set_xform.
    crush. generalize (proj1 (H0 x) H1). intro. econstructor ; split ; eauto.
    xinterp_simpl. rewrite equal_iso. auto.
    generalize (proj2 (H0 (xinterp (equal_xform (Equal_sym H)) x))).
    generalize (Equal_sym H). intro. 
    rewrite (@proof_irrelevance _ H (Equal_sym e)). rewrite equal_iso.
    intro. specialize (H3 H1). econstructor ; split ; eauto.
    xinterp_simpl. rewrite (@proof_irrelevance _ e (Equal_sym H)). auto.
  Qed.

  (* Now we must lift up the underlying set operations to operations over
     a pair of a set and a transform, whose domain is taken from the type
     of the set. *)

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
  Definition add_xform (ty:type) (refx : re_xf_pair ty)
             (rs:rs_xf_pair ty) : rs_xf_pair ty.
    destruct refx as [x fx].
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

  Lemma add_xform_erase ty rex rs : 
    projT1 (@add_xform ty rex rs) = add (projT1 rex) (projT1 rs).
  Proof.
    unfold add_xform.
    destruct rex as [x fx].
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

  Lemma add_xform_corr ty rex rs str v : 
    in_re_set_xform (@add_xform ty rex rs) str v <-> 
    in_re_xform rex str v \/ in_re_set_xform rs str v.
  Proof.
    destruct rex as [x fx].
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
    Variable f : re_xf_pair ty -> A -> A.
    Fixpoint fold_tree_xform (s:Raw.tree) : (tree_type s ->> List_t ty) -> A -> A :=
      match s return tree_type s ->> List_t ty -> A -> A with
        | Raw.Leaf => fun _ v => v
        | Raw.Node _ l x r => 
          fun fs v => 
            fold_tree_xform r (xcomp (xcomp xinr xinr) fs)
                            (f (existT _ x (xcomp (xcomp xinl xinr) fs))
                               (fold_tree_xform l (xcomp xinl fs) v))
      end.
  End FOLD_TREE_XFORM.

  Section FOLD_TREE_XFORM_ERASE.
    Variable ty1 : type.
    Variable ty2 : type.
    Variable comb1 : re_xf_pair ty1 -> rs_xf_pair ty2 -> rs_xf_pair ty2.
    Variable comb2 : regexp -> RESet.t -> RESet.t.
    Variable H : forall rex rx, projT1 (comb1 rex rx) = comb2 (projT1 rex) (projT1 rx).

    Lemma fold_tree_xform_erase : 
      forall rx f ini_rx, 
        projT1 (fold_tree_xform comb1 rx f ini_rx) = 
        Raw.fold comb2 rx (projT1 ini_rx).
    Proof.
      induction rx. auto. intros.
      simpl. rewrite IHrx2. rewrite H. simpl. rewrite IHrx1. auto.
    Qed.
  End FOLD_TREE_XFORM_ERASE.

  Definition fold_xform ty (A:Type) (comb : re_xf_pair ty -> A -> A) 
             (rx : rs_xf_pair ty) (a:A) : A :=
    let (s1, f1) := rx in
    match s1 as s1' return (re_set_type s1' ->> List_t ty -> A) with
      | {| this := t1; is_ok := okt1 |} =>
        fun f2 : re_set_type {| this := t1; is_ok := okt1 |} ->> List_t ty =>
          fold_tree_xform comb t1 f2 a
    end f1.

   Lemma fold_xform_erase : forall ty1 ty2
     (comb1:re_xf_pair ty1 -> rs_xf_pair ty2 -> rs_xf_pair ty2)
     (comb2:regexp -> RESet.t -> RESet.t) rx ini_rx,
     (forall rex rx, projT1 (comb1 rex rx) = comb2 (projT1 rex) (projT1 rx)) -> 
     projT1 (fold_xform comb1 rx ini_rx) = RESet.fold comb2 (projT1 rx) (projT1 ini_rx).
  Proof.
    intros.
    destruct rx. simpl. destruct x. 
    unfold RESet.fold. simpl. destruct ini_rx.
    rewrite (@fold_tree_xform_erase ty1 ty2 comb1 comb2 H). auto.
  Qed.

  Definition map_xform ty1 ty2 (f : re_xf_pair ty1 -> re_xf_pair ty2) (s:rs_xf_pair ty1) : 
    rs_xf_pair ty2 := 
    fold_xform (fun x => add_xform (f x)) s (empty_xform ty2).

  Lemma map_xform_erase : 
    forall ty1 ty2 (f : re_xf_pair ty1 -> re_xf_pair ty2) 
              (f' : regexp -> regexp) (s : rs_xf_pair ty1), 
      (forall rx, projT1 (f rx) = f' (projT1 rx)) -> 
      projT1(map_xform f s) = 
      RESet.fold (fun x => RESet.add (f' x)) (projT1 s) RESet.empty.
   Proof.
     intros.
     unfold map_xform. apply fold_xform_erase. intros. 
     rewrite add_xform_erase. rewrite H. auto.
   Qed.    

   Definition set_cat_re (s:RESet.t) (r:regexp): RESet.t := 
     match r with
       | Eps => s (* not stricitly necessary; an optimization *)
       | Zero => RESet.empty
       | _ => RESet.fold (fun r1 s' => RESet.add (Cat r1 r) s') s RESet.empty
                         (* Note : will need to show that this is the same as
                            RESF.map (re_set_build_map (fun r1 => Cat r1 r)) s *)
     end.
         
   Definition simple_cat_re_xform ty (s:rs_xf_pair ty) (r:regexp) : 
     rs_xf_pair (Pair_t ty (regexp_type r)) := 
     map_xform 
       (fun xf => let (x,f) := xf in 
                  existT _ (Cat x r)
                         (xcomp (xpair xsnd (xcomp xfst f)) (xmapenv (xpair xsnd xfst))))
       s.

   Definition cat_re_xform ty (s : rs_xf_pair ty) (r:regexp) : 
     rs_xf_pair (Pair_t ty (regexp_type r)) := 
     match r as r' return rs_xf_pair (Pair_t ty (regexp_type r')) with
       | Eps => let (raw_set,f) := s in 
                (existT _ raw_set (xcomp f (xmap (xpair xid xunit))))
       | Zero => (existT _ RESet.empty xzero)
       | r' => simple_cat_re_xform s r'
     end.

   Lemma cat_re_xform_erase ty s r :  
     projT1 (@cat_re_xform ty s r) = set_cat_re (projT1 s) r.
   Proof.
     destruct s. destruct r ; auto ; unfold cat_re_xform ; 
     apply map_xform_erase ; destruct rx ; auto.
   Qed.

   Definition rx_equal ty (rx1 rx2: rs_xf_pair ty) := 
     forall s v, in_re_set_xform rx1 s v <-> in_re_set_xform rx2 s v.

   Definition tx_equal ty (tx1 tx2: tree_xf_pair ty) := 
     forall s v, in_tree_xform tx1 s v <-> in_tree_xform tx2 s v.

   Lemma tree_disj i (t1 t2:Raw.tree) (x:regexp) (ok : Raw.Ok (Raw.Node i t1 x t2)) :
     forall r, (Raw.In r t1 -> ~Raw.In r t2 /\ r <> x) /\ 
               (Raw.In r t2 -> ~Raw.In r t1 /\ r <> x).
   Proof.
     inversion ok. subst. intro. 
     specialize (H5 r). specialize (H6 r). simpl in *.
     remember (REOrderedTypeAlt.compare r x) as c ; destruct c ; split ; intros ;
     match goal with 
         | [ H1 : ?P1 -> _, H2 : ?P1 |- _ ] => specialize (H1 H2) ; try discriminate
     end.
     generalize (REOrderedTypeAlt.compare_sym x r) ; unfold CompOpp. rewrite H6.
     rewrite <- Heqc. intros ; discriminate. split. intro. specialize (H6 H0).
     generalize (REOrderedTypeAlt.compare_sym r x). unfold CompOpp. rewrite H6.
     rewrite <- Heqc. intros ; discriminate. intro. subst.
     rewrite (Raw.MX.compare_refl x) in Heqc. discriminate.
     generalize (REOrderedTypeAlt.compare_sym r x). unfold CompOpp. rewrite H6.
     rewrite <- Heqc. intro ; discriminate.
     split. intro. specialize (H5 H0). discriminate.
     intro ; subst. rewrite (Raw.MX.compare_refl x) in Heqc. discriminate.
   Qed.

   Lemma in_tree_in_elem : 
     forall tree s v, 
       in_tree tree s v -> exists r, (Raw.In r tree /\ exists v', in_regexp r s v').
   Proof.
     induction tree ; simpl ; intros. destruct v.
     unfold in_tree in H. simpl in H. repeat in_regexp_inv. 
     specialize (IHtree1 _ _ H). crush. 
     econstructor. split. eapply Raw.InLeft ; eauto. eauto.
     econstructor. split ; eauto. eapply Raw.IsRoot. eapply Raw.MX.compare_refl.
     specialize (IHtree2 _ _ H). crush. 
     econstructor. split. eapply Raw.InRight ; eauto. eauto.
   Qed.


   Section FOLD_TREE_REC.
     Variable ty : type.
     Variable A : Type.
     Variable P : rs_xf_pair ty -> A -> Prop.
     Variable f : re_xf_pair ty -> A -> A.
     Variable P_resp_equiv : 
       forall rx1 rx2, rx_equal rx1 rx2 -> forall (a:A), P rx1 a -> P rx2 a.
     Variable P_extends : 
       forall rx rs a, P rs a -> P (add_xform rx rs) (f rx a).

     Lemma fold_tree_rec' : 
       forall (tree : Raw.tree)
              (tree_xf : tree_type tree ->> List_t ty)
              (accum_set : rs_xf_pair ty)
              (accum : A)
              (Inv : P accum_set accum),
         P (fold_tree_xform (fun x => add_xform x) tree tree_xf accum_set)
           (fold_tree_xform f tree tree_xf accum).
     Proof.
      induction tree ; intros.
      (* base case *)
      auto.
       (* inductive case *)
      specialize (IHtree1 (xcomp xinl tree_xf) accum_set accum Inv). 
      generalize (P_extends (existT _ t1 (xcomp (xcomp xinl xinr) tree_xf)) IHtree1).
      clear IHtree1. intro H.
      specialize (IHtree2 (xcomp (xcomp xinr xinr) tree_xf) _ _ H).
      assert (rx_equal (fold_tree_xform (fun x => add_xform x) tree2 
                                        (xcomp (xcomp xinr xinr) tree_xf)
                                        (add_xform 
                                           (existT _ t1 (xcomp (xcomp xinl xinr) tree_xf))
                                           (fold_tree_xform (fun x => add_xform x)
                                                            tree1 (xcomp xinl tree_xf)
                                                            accum_set)))
                       (fold_tree_xform (fun x => add_xform x) 
                                        (Raw.Node t0 tree1 t1 tree2) tree_xf accum_set)).
      intro ; intro. clear IHtree2 H.
      assert (@fold_tree_xform ty _ (fun x => add_xform x)
                              (Raw.Node t0 tree1 t1 tree2) = 
              fun fs v => 
                fold_tree_xform (fun x => add_xform x)
                  tree2 (xcomp (xcomp xinr xinr) fs)
                                (add_xform (existT _ t1 (xcomp (xcomp xinl xinr) fs))
                                           (fold_tree_xform (fun x => add_xform x)
                                                            tree1 (xcomp xinl fs) v))).
      auto. rewrite H. split ; auto.
      apply (P_resp_equiv H0 IHtree2).
    Qed.

    Lemma fold_tree_rec : 
      forall (tree : Raw.tree)
             (tree_xf : tree_type tree ->> List_t ty)
             (tree_ok : Raw.Ok tree)
             (accum : A)
             (Inv : P (empty_xform ty) accum),
             P (existT _ {| this := tree ; is_ok := tree_ok|} tree_xf)
             (fold_tree_xform f tree tree_xf accum).
    Proof.
      intros.
      specialize (fold_tree_rec' tree tree_xf Inv).
      apply P_resp_equiv. clear A P f P_resp_equiv P_extends accum Inv.
      unfold rx_equal. 
      assert (forall s str v, 
                in_re_set_xform s str v <-> 
                (in_re_set_xform s str v \/ in_re_set_xform (empty_xform ty) str v)).
      intros ; split ; auto. intros. destruct H ; auto. 
      contradiction (empty_xform_corr H). intros.
      symmetry. rewrite H. clear H. generalize (empty_xform ty). 
      induction tree. 
      (* Base case *)
      crush. unfold in_re_set in H. unfold in_tree in H. simpl in H. in_regexp_inv.
      (* Inductive case *)
      intro.
      specialize (IHtree1 (xcomp xinl tree_xf) (ok_left tree_ok)).
      specialize (IHtree2 (xcomp (xcomp xinr xinr) tree_xf) (ok_right tree_ok)).
      unfold fold_tree_xform. 
      rewrite <- IHtree2. rewrite add_xform_corr. rewrite <- IHtree1.
      clear IHtree1 IHtree2. unfold in_re_set_xform, in_re_set, re_set_type, in_tree.
      crush. in_regexp_inv. right ; right. left. econstructor ; split ; eauto.
      xinterp_simpl. auto. in_regexp_inv. right ; left ; econstructor ; split ; eauto.
      xinterp_simpl. auto. left ; econstructor ; split ; eauto. xinterp_simpl ; auto.
      xinterp_simpl. left ; eauto. xinterp_simpl. left ; eauto. xinterp_simpl ; eauto.
   Qed.

   Lemma fold_xform_rec : 
     forall (rs : rs_xf_pair ty) (accum : A),
       P (empty_xform ty) accum -> P rs (fold_xform f rs accum).
     Proof.
       intros. unfold fold_xform. destruct rs as [s x]. 
       destruct s as [t okt]. unfold re_set_type in x. simpl in x.
       apply (fold_tree_rec). auto.
     Qed.
  End FOLD_TREE_REC.

  Lemma cat_re_xform_corr' : 
     forall ty (s : rs_xf_pair ty) r str (v : interp ty * interp (regexp_type r)), 
       in_re_set_xform (simple_cat_re_xform s r) str v <-> 
       exists str1 str2 v1 v2, str = str1 ++ str2 /\ v = (v1,v2) /\ 
                           in_re_set_xform s str1 v1 /\ in_regexp r str2 v2.
   Proof.
     Opaque add_xform xpair xcomp.
     unfold simple_cat_re_xform. unfold map_xform. fold regexp_type.
     intros. apply fold_xform_rec.
     intros. split. intros. specialize (proj1 H0 H1). clear H0 H1. crush.
     repeat econstructor. specialize (H x x1). crush. auto.
     crush. apply H2. repeat econstructor. specialize (H x x1) ; crush. auto.

     intros. rewrite add_xform_corr. destruct rx. crush. in_regexp_inv.
     xinterp_simpl. rewrite xmapenv_corr in H2. fold interp in H2. 
     match goal with 
         | [ H : List.In _ (map ?e _) |- _ ] => 
           replace e with (fun x : interp ty => (x,x5)) in H
     end. Focus 2. apply extensionality. intro ; xinterp_simpl ; auto.
     simpl in H2. assert (exists v1, v = (v1,x5) /\ List.In v1 (xinterp x0 x4)).
     generalize H2. generalize (xinterp x0 x4). induction i ; crush.
     specialize (IHi H4). crush. crush.
     repeat econstructor ; eauto. apply add_xform_corr. left. crush.
     specialize (H H1). crush. repeat econstructor ; eauto. apply add_xform_corr.
     right ; crush. rewrite add_xform_corr in H1. crush. left.
     exists (x5,x4). crush. xinterp_simpl. rewrite xmapenv_corr. fold interp. simpl.
     replace (fun x6 : interp ty => xinterp (xpair xsnd xfst) (x4,x6)) with 
     (fun x6 : interp ty => (x6,x4)). Focus 2. apply extensionality.
     intro. xinterp_simpl. auto. generalize (xinterp x0 x5) H3.
     induction i ; crush. right. apply H0. repeat econstructor. auto. auto.
     unfold in_re_set_xform. simpl. crush. destruct x. destruct x3.
  Qed.

  Lemma cat_re_xform_corr : 
    forall ty (s : rs_xf_pair ty) r str (v : interp ty * interp (regexp_type r)), 
       in_re_set_xform (cat_re_xform s r) str v <-> 
       exists str1 str2 v1 v2, str = str1 ++ str2 /\ v = (v1,v2) /\ 
                           in_re_set_xform s str1 v1 /\ in_regexp r str2 v2.
  Proof.
    intros.
    generalize (cat_re_xform_corr' s r str v). intros.
    destruct r ; auto ; clear H ; simpl in *. destruct s. crush.
    xinterp_simpl. destruct v. destruct u. assert (List.In i (xinterp x0 x1)).
    generalize (xinterp x0 x1) H0 . induction i0 ; crush. xinterp_simpl.
    crush. repeat econstructor ; eauto. rewrite <- app_nil_end. auto.
    in_regexp_inv. exists x5. split ; auto. generalize H1. xinterp_simpl.
    generalize (xinterp x0 x5). induction i ; crush.
    destruct v. destruct v.
  Qed. 

End RESETXFORM.

(* Module RR : WSets := RESet. *) 
