Require Import List.
Require Import Bool.
Require Import Char.
Require Import Xform.
Require Import CommonTacs.

Set Implicit Arguments.

Inductive astgram : Set := 
| aAny : astgram
| aEps : astgram
| aZero : astgram
| aChar : char_t -> astgram
| aCat : astgram -> astgram -> astgram
| aAlt : astgram -> astgram -> astgram
| aStar : astgram -> astgram.

Fixpoint astgram_cmp (a1 a2:astgram) : comparison := 
  match a1, a2 with 
    | aEps, aEps => Eq
    | aEps, _ => Lt
    | _, aEps => Gt
    | aZero, aZero => Eq
    | aZero, _ => Lt
    | _, aZero => Gt
    | aAny, aAny => Eq
    | aAny, _ => Lt
    | _, aAny => Gt
    | aChar c1, aChar c2 => char_cmp c1 c2
    | aChar _, _ => Lt
    | _ , aChar _ => Gt
    | aCat a1 a2, aCat a3 a4 => 
      match astgram_cmp a1 a3 with 
        | Eq => astgram_cmp a2 a4
        | Lt => Lt
        | Gt => Gt
      end
    | aCat _ _, _ => Lt
    | _, aCat _ _ => Gt
    | aAlt a1 a2, aAlt a3 a4 => 
      match astgram_cmp a1 a3 with 
        | Eq => astgram_cmp a2 a4
        | Lt => Lt
        | Gt => Gt
      end
    | aAlt _ _, _ => Lt
    | _, aAlt _ _ => Gt
    | aStar a1, aStar a3 => astgram_cmp a1 a3
  end.

Lemma astgram_eq_corr a1 : forall a2:astgram,
  astgram_cmp a1 a2 = Eq -> a1 = a2.
Proof.
  induction a1 ; induction a2 ; simpl ; auto ; intros ; 
  try discriminate ; try (rewrite (char_eq_leibniz c c0) ; auto) ; 
  try (specialize (IHa1_1 a2_1) ; specialize (IHa1_2 a2_2) ;
  destruct (astgram_cmp a1_1 a2_1) ; try discriminate ; rewrite IHa1_1 ; auto ;
  rewrite IHa1_2 ; auto). erewrite IHa1 ; eauto.
Qed.    

Lemma astgram_cmp_sym : forall a1 a2, astgram_cmp a2 a1 = CompOpp (astgram_cmp a1 a2).
Proof.
  induction a1 ; destruct a2 ; auto ; simpl. apply CharOrderedTypeAlt.compare_sym.
  repeat rewrite IHa1_1. repeat rewrite IHa1_2. destruct (astgram_cmp a1_1 a2_1) ; auto.
  repeat rewrite IHa1_1. repeat rewrite IHa1_2. destruct (astgram_cmp a1_1 a2_1) ; auto.
  rewrite IHa1. auto.
Qed.

Lemma astgram_cmp_trans : 
  forall cmp a1 a2 a3,
    astgram_cmp a1 a2 = cmp -> 
    astgram_cmp a2 a3 = cmp -> astgram_cmp a1 a3 = cmp.
Proof.
  Local Ltac trans_simp := 
    match goal with 
      | [ H: astgram_cmp ?a1 ?a2 = Eq |- _ ] => apply astgram_eq_corr in H ; subst a2
    end.
  intros cmp a1. generalize cmp. clear cmp.
  induction a1 ; destruct a2 ; intros  ; destruct a3 ; simpl in *; 
  intros ; try congruence ; eauto.
  Case "aChar".
    eapply CharOrderedTypeAlt.compare_trans ; eauto. 
  Case "aCat".
    remember_rev (astgram_cmp a1_1 a2_1) as cmp1.
    remember_rev (astgram_cmp a2_1 a3_1) as cmp2.
    destruct cmp1; destruct cmp2 ; try (repeat trans_simp ; crush ; fail).
    assert (H10:astgram_cmp a1_1 a3_1 = Eq) by eauto. rewrite H10. eauto.
    assert (H10:astgram_cmp a1_1 a3_1 = Lt) by eauto. rewrite H10. eauto.
    assert (H10:astgram_cmp a1_1 a3_1 = Gt) by eauto. rewrite H10. eauto.
  case "aAlt".
    remember_rev (astgram_cmp a1_1 a2_1) as cmp1.
    remember_rev (astgram_cmp a2_1 a3_1) as cmp2.
    destruct cmp1; destruct cmp2 ; try (repeat trans_simp ; crush ; fail).
    assert (H10:astgram_cmp a1_1 a3_1 = Eq) by eauto. rewrite H10. eauto.
    assert (H10:astgram_cmp a1_1 a3_1 = Lt) by eauto. rewrite H10. eauto.
    assert (H10:astgram_cmp a1_1 a3_1 = Gt) by eauto. rewrite H10. eauto.
Qed.

(** Compute the return [type] of an [astgram]. *)
Fixpoint astgram_type (pg : astgram) : type := 
  match pg with 
    | aEps => Unit_t
    | aZero => Void_t
    | aChar _ => Char_t
    | aAny => Char_t
    | aCat pg1 pg2 => Pair_t (astgram_type pg1) (astgram_type pg2)
    | aAlt pg1 pg2 => Sum_t (astgram_type pg1) (astgram_type pg2)
    | aStar pg => List_t (astgram_type pg)
  end.

Inductive in_astgram : forall a, list char_t -> interp (astgram_type a) -> Prop :=
| InaEps : forall s v, s = nil -> v = tt -> in_astgram aEps s v
| InaChar : forall c s v, s = c::nil -> v = c -> in_astgram (aChar c) s v
| InaAny : forall c s v, s = c::nil -> v = c -> in_astgram aAny s v
| InaCat : 
    forall a1 a2 s1 s2 v1 v2 s v,
      in_astgram a1 s1 v1 -> in_astgram a2 s2 v2 -> s = s1 ++ s2 -> v = (v1,v2) -> 
      in_astgram (aCat a1 a2) s v
| InaAlt_l : 
    forall a1 a2 s v1 v, 
      in_astgram a1 s v1 -> v = inl _ v1 -> in_astgram (aAlt a1 a2) s v
| InaAlt_r : 
    forall a1 a2 s v2 v, 
      in_astgram a2 s v2 -> v = inr _ v2 -> in_astgram (aAlt a1 a2) s v
| InaStar_eps : forall a s v, s = nil -> v = nil -> in_astgram (aStar a) s v
| InaStar_cons : 
    forall a s1 v1 s2 v2 s v,
      in_astgram a s1 v1 -> in_astgram (aStar a) s2 v2 -> 
      s1 <> nil -> s = s1 ++ s2 -> v = v1::v2 -> in_astgram (aStar a) s v.
Hint Constructors in_astgram.

Definition af_pair (t:type) := {a : astgram & astgram_type a ->> t }.
Definition af (t:type) (a:astgram) (f:astgram_type a ->> t) : af_pair t := 
  existT _ a f.

Definition in_af t (e: af_pair (List_t t)) cs v := 
  match e with 
    | existT ag x => exists v', in_astgram ag cs v' /\ In v (xinterp x v')
  end.

Definition xsingle {t1 t2:type} : (t1 ->> t2) -> t1 ->> List_t t2 := 
  fun f => xcons f xempty.

Section BALANCE.
  Variable A : Type.
  Variable B : Type.
  Variable node : B -> B -> B.
  Variable singleton : A -> B.
  Variable emp : B.

  Fixpoint merge_adj (xs:list B) : list B := 
    match xs with 
      | nil => nil
      | x::nil => x::nil
      | x::y::rest => (node x y)::(merge_adj rest)
    end.

  Require Import Recdef Omega.

  Lemma balance_lt (l:list B) (x b:B) : length (merge_adj (x::b::l)) < length (x::b::l).
  Proof.
    assert ((forall b,length (merge_adj (b::l)) <= length (b::l)) /\ 
            (forall x b, length (merge_adj (x::b::l)) < length (x::b::l))).
    intros ; subst. 
    induction l ; intros ; split ; auto. destruct IHl. intro. specialize (H0 b0 a).
    omega. intros. simpl. destruct IHl. specialize (H a). simpl in H. omega.
    destruct H. eapply H0.
  Qed.

  Function balance' (xs:list B) {measure length xs} : B := 
  match xs with 
    | nil => emp
    | x::nil => x
    | xs' => balance' (merge_adj xs')
  end.
  intros ; subst ; eapply balance_lt. 
  Defined.

  Definition balance (xs:list A) : B := 
    balance' (List.map singleton xs).
End BALANCE.

Fixpoint sum_type (ags : list astgram) : type := 
  match ags with 
    | nil => Void_t
    | a::rest => Sum_t (astgram_type a) (sum_type rest)
  end.

Fixpoint prod_type (ags : list astgram) : type := 
  match ags with 
    | nil => Unit_t
    | a::rest => Pair_t (astgram_type a) (prod_type rest)
  end.

Definition af_sum t := {ags : list astgram & sum_type ags ->> t}.
Definition afsl {t} (ags : list astgram) (f : sum_type ags ->> t) : 
  af_sum t := existT _ ags f.
Definition af_prod t := {ags : list astgram & prod_type ags ->> t}.
Definition afpl {t} (ags : list astgram) (f : prod_type ags ->> t) : 
  af_prod t := existT _ ags f.

Fixpoint append_cat (p1s p2s:list astgram) : 
  af_prod (List_t (Pair_t (prod_type p1s) (prod_type p2s))) := 
  match p1s return af_prod (List_t (Pair_t (prod_type p1s) (prod_type p2s))) with 
    | nil => afpl p2s (xsingle (xpair xunit xid))
    | p::p1s' => 
      let (ps, f) := append_cat p1s' p2s in 
      afpl (p::ps) 
           (xcomp (xpair xfst (xcomp xsnd f)) 
                  (xmapenv (xpair (xpair xfst (xcomp xsnd xfst)) (xcomp xsnd xsnd))))
  end. 

Definition re_cat' : forall (ps:list astgram), af_pair (prod_type ps).
  refine (fix re_cat' (ps:list astgram) : af_pair (prod_type ps) := 
            match ps as ps' return af_pair (prod_type ps') with 
              | nil => af aEps xid
              | p::ps' => 
                match ps' as qs return (qs = ps') -> af_pair (prod_type (p::qs)) with
                  | nil => fun _ => af p (xpair xid xunit)
                  | qs => 
                    match re_cat' ps' return (qs = ps') -> af_pair (prod_type (p::qs)) with 
                      | existT a f => fun H => af (aCat p a) _
                    end
                end eq_refl
            end). simpl.
refine (xcoerce (xpair xfst (xcomp xsnd f)) eq_refl _).
rewrite <- H. auto.
Defined.
 
Fixpoint merge_pairs_dep (al : list astgram) : af_sum (sum_type al) := 
  match al return af_sum (sum_type al) with
    | nil => afsl nil xid
    | a1::al' => 
      match al' return af_sum (sum_type (a1::al')) with
        | nil => afsl (a1::nil) xid
        | a2::al'' => 
          let (b, f) := merge_pairs_dep al'' in 
          afsl ((aAlt a1 a2)::b) 
               (xmatch (xmatch xinl (xcomp xinl xinr)) (xcomp f (xcomp xinr xinr)))
      end
  end.

Definition get_sum_list {t} (af : af_sum t) : list astgram := 
  let (al,_) := af in al.

Lemma dep_balance_lt : forall (l:list astgram) (a1 a2:astgram),
  length (get_sum_list (merge_pairs_dep (a1::a2::l))) < length (a1::a2::l).
Proof.
  assert (forall l, (get_sum_list (merge_pairs_dep l)) = (merge_adj aAlt l) /\
                    forall a, (get_sum_list (merge_pairs_dep (a::l))) = 
                              (merge_adj aAlt (a::l))).
  induction l ; auto. destruct IHl ; split ; auto. simpl. 
  unfold get_sum_list in H. destruct (merge_pairs_dep l). simpl. subst. auto.
  intros. specialize (H (a1::a2::l)). destruct H. rewrite H. apply balance_lt.
Qed.

Function re_alt' (ps:list astgram) {measure length ps} : af_pair (sum_type ps) := 
  match ps return af_pair (sum_type ps) with 
    | nil => af aZero xid
    | x::nil => af x xinl
    | ps' => let (xs,f) := merge_pairs_dep ps' in
             let (a,g) := re_alt' xs in 
             af a (xcomp g f)
  end.
  intros ; subst. specialize (dep_balance_lt l0 x a). rewrite teq1. simpl. auto.
Defined.

(*  
Definition re_alt' : forall (ps:list astgram), af_pair (sum_type ps).
  refine (fix re_alt' (ps:list astgram) : af_pair (sum_type ps) := 
            match ps as ps' return af_pair (sum_type ps') with 
              | nil => af aZero xid
              | p::ps' => 
                match ps' as qs return (qs = ps') -> af_pair (sum_type (p::qs)) with
                  | nil => fun _ => af p xinl
                  | qs => 
                    match re_alt' ps' return (qs = ps') -> af_pair (sum_type (p::qs)) with 
                      | existT a f => fun H => af (aAlt p a) _
                    end
                end eq_refl
            end).
  subst. rewrite H. simpl. refine (xmatch xinl (xcomp f xinr)).
Defined.
*)

Definition re_cat {t} (ps : list astgram) (f: prod_type ps ->> t) : af_pair t := 
  let (a,g) := re_cat' ps in af a (xcomp g f).

Definition re_alt {t} (ps : list astgram) (f: sum_type ps ->> t) : af_pair t := 
  let (a,g) := re_alt' ps in af a (xcomp g f).

Definition merge_alt : forall (p1s p2s: list astgram),
                         af_sum (List_t (Sum_t (sum_type p1s) (sum_type p2s))).
refine (fix merge_alt (p1s : list astgram) : 
          forall p2s, af_sum (List_t (Sum_t (sum_type p1s) (sum_type p2s))) := 
          match p1s return 
                forall p2s, af_sum (List_t (Sum_t (sum_type p1s) (sum_type p2s))) with
            | nil => fun p2s => afsl p2s (xsingle xinr)
            | p1::p1s' => 
              fix merge_alt_aux (p2s:list astgram) : 
                af_sum (List_t (Sum_t (sum_type (p1::p1s')) (sum_type p2s))) := 
              match p2s as p2s' return 
                    af_sum (List_t (Sum_t (sum_type (p1::p1s')) (sum_type p2s'))) with
                | nil => afsl (p1::p1s') (xsingle xinl)
                | p2::p2s' => 
                  match astgram_cmp p1 p2 as x return
                        (astgram_cmp p1 p2 = x) -> 
                        af_sum (List_t (Sum_t (sum_type (p1::p1s')) (sum_type (p2::p2s'))))
                  with 
                    | Eq => 
                      fun H => 
                        let (ps, f) := merge_alt p1s' p2s' in 
                        afsl (p1::ps) _ 
                    | Lt => 
                      fun H => 
                        let (ps, f) := merge_alt p1s' (p2::p2s') in 
                        afsl (p1::ps) 
                             (xmatch (xsingle (xcomp xinl xinl))
                                     (xcomp f (xmap (xmatch (xcomp xinr xinl) xinr))))
                    | Gt => 
                      fun H => 
                        let (ps,f) := merge_alt_aux p2s' in 
                        afsl (p2::ps) 
                             (xmatch (xsingle (xcomp xinl xinr))
                                     (xcomp f (xmap (xmatch xinl (xcomp xinr xinr)))))
                  end eq_refl
              end
          end) ; simpl.
rewrite ((astgram_eq_corr p1 p2) H) ;
refine (xmatch (xcons (xcomp xinl xinl)
                      (xcons (xcomp xinl xinr) xempty)) 
               (xcomp f (xmap (xmatch (xcomp xinr xinl) (xcomp xinr xinr))))).
Defined.

Fixpoint flatten_alt (a : astgram) : af_sum (List_t (astgram_type a)) :=
  match a return af_sum (List_t (astgram_type a)) with 
    | aAlt a1 a2 => 
      let (p1s,f1s) := flatten_alt a1 in 
      let (p2s,f2s) := flatten_alt a2 in 
      let (a',f) := merge_alt p1s p2s in
      afsl a' (xcomp f (xcomp (xmap (xmatch (xcomp f1s (xmap xinl)) 
                                            (xcomp f2s (xmap xinr)))) xflatten))
    | aZero => afsl nil (xsingle xid)
    | a' => afsl (a'::nil) (xmatch (xsingle xid) xzero) 
  end.

Fixpoint flatten_cat (a:astgram) : af_prod (List_t (astgram_type a)) := 
  match a return af_prod (List_t (astgram_type a)) with
    | aEps => afpl nil (xsingle xid)
    | aCat a1 a2 => 
      let (p1s,f1s) := flatten_cat a1 in 
      let (p2s,f2s) := flatten_cat a2 in 
      let (ps, f) := append_cat p1s p2s in 
      afpl ps (xcomp f (xcomp (xcomp (xmap (xpair (xcomp xfst f1s) 
                                                  (xcomp xsnd f2s))) 
                                     (xmap xcross)) xflatten))
    | a' => afpl (a'::nil) (xsingle xfst)
  end.

Fixpoint opt_ag (a:astgram) : af_pair (List_t (astgram_type a)) := 
  match a with 
    | aAlt a1 a2 => 
      let (a1', f1) := opt_ag a1 in 
      let (a2', f2) := opt_ag a2 in 
      let (p1s, f1s) := flatten_alt a1' in 
      let (p2s, f2s) := flatten_alt a2' in 
      let (p, f) := merge_alt p1s p2s in 
      re_alt p 
             (xcomp f (xcomp 
                         (xmap (xmatch (xcomp (xthen f1s f1) (xmap xinl)) 
                                       (xcomp (xthen f2s f2) (xmap xinr)))) xflatten))
    | aCat a1 a2 => 
      let (a1', f1) := opt_ag a1 in 
      let (a2', f2) := opt_ag a2 in 
      match a1' return af_pair (List_t (astgram_type (aCat a1 a2))) with
        | aZero => af aZero xzero
        | b1 => 
          match a2' return af_pair (List_t (astgram_type (aCat a1 a2))) with
            | aZero => af aZero xzero
            | b2 => 
              let (p1s, f1s) := flatten_cat b1 in
              let (p2s, f2s) := flatten_cat b2 in 
              let (p, f) := append_cat p1s p2s in
              re_cat p 
                     (xcomp f (xcomp (xmap (xpair (xcomp xfst (xthen f1s f1)) 
                                                  (xcomp xsnd (xthen f2s f2))))
                                     (xcomp (xmap xcross) xflatten)))
            end
      end
    | aStar a1 => 
      let (a', f) := opt_ag a1 in 
      match a' return astgram_type a' ->> List_t (astgram_type a1) -> 
                      af_pair (List_t (astgram_type (aStar a1)))
      with 
        | aZero => fun _ => af aEps (xsingle xempty)
        | aStar a'' => fun f1 => af (aStar a'') 
                                    (xcomp f1 (xcons xid (xcons xempty xempty)))
        | a'' => fun f1 => af (aStar a'') (xmap f1)
      end f
    | a' => af a' (xsingle xid)
  end.

Definition opt_af {t} (a:astgram) (f:astgram_type a ->> List_t t):af_pair (List_t t) :=
  let (a',f1) := opt_ag a in 
  af a' (xopt (xthen f1 f)).

Fixpoint null_and_split (a:astgram): af_pair (List_t (astgram_type a)) := 
  match a return af_pair (List_t (astgram_type a)) with 
    | aEps => af aEps (xsingle xid)
    | aZero => af aZero xempty
    | aChar c => af aZero xempty
    | aAny => af aZero xempty
    | aAlt a11 a12 => 
      let (a11', f1) := null_and_split a11 in 
      let (a12', f2) := null_and_split a12 in 
      opt_af (aAlt a11' a12') 
             (xmatch  (xcomp f1 (xmap xinl)) (xcomp f2 (xmap xinr)))
    | aCat a11 a12 => 
      let (a11', f1) := null_and_split a11 in 
      match a11' with 
        | aZero => af aZero xempty
        | a11'' => 
          let (a12', f2) := null_and_split a12 in 
          opt_af (aCat a11'' a12') 
                 (xcomp (xpair (xcomp xfst f1) (xcomp xsnd f2)) xcross)
      end
    | aStar a11 => af aEps (xsingle xempty)
  end.

Fixpoint deriv_and_split (a:astgram) (c:char_t) : af_pair (List_t (astgram_type a)) :=
  match a return af_pair (List_t (astgram_type a)) with 
    | aEps => af aZero xempty
    | aZero => af aZero xempty
    | aChar c' => 
      match char_cmp c c' with 
          | Eq => af aEps (xsingle (xchar c))
          | _ => af aZero xempty
      end
    | aAny => af aEps (xsingle (xchar c))
    | aAlt ag11 ag12 => 
      let (ag11', f1) := deriv_and_split ag11 c in 
      let (ag12', f2) := deriv_and_split ag12 c in 
      opt_af (aAlt ag11' ag12') 
             (xmatch (xcomp f1 (xmap xinl)) (xcomp f2 (xmap xinr)))
    | aCat ag11 ag12 => 
      let (ag11', f1) := deriv_and_split ag11 c in 
      let (ag_left, f_left) := opt_ag (aCat ag11' ag12) in
      let (ag11null', fnull) := null_and_split ag11 in 
      match ag11null' with 
        | aZero => 
          opt_af ag_left 
                 (xcomp f_left (xcomp (xmap (xcrossmap f1 (xsingle xid))) xflatten))
        | ag11null => 
          let (ag12', f2) := deriv_and_split ag12 c in 
          let (ag_right, f_right) := opt_ag (aCat ag11null ag12') in
          opt_af (aAlt ag_left ag_right) 
                 (xmatch 
                    (xcomp f_left (xcomp (xmap (xcrossmap f1 (xsingle xid))) xflatten))
                    (xcomp f_right (xcomp (xmap (xcrossmap fnull f2)) xflatten)))
      end 
    | aStar ag0 => 
      let (ag0', f) := deriv_and_split ag0 c in 
      opt_af (aCat ag0' (aStar ag0)) 
             (xcomp (xpair xsnd (xcomp xfst f)) (xmapenv (xcons xsnd xfst)))
  end.

Definition cross_prod t1 t2 (xs:list t1) (ys:list t2) : list (t1 * t2) := 
  (fold_right (fun v a => (map (fun w => (v,w)) ys) ++ a) nil xs).

Fixpoint astgram_extract_nil (a:astgram) : list (interp (astgram_type a)) := 
  match a return list (interp (astgram_type a)) with
    | aEps => tt::nil
    | aZero => nil
    | aChar _ => nil
    | aAny => nil
    | aCat ag1 ag2 => cross_prod (astgram_extract_nil ag1) (astgram_extract_nil ag2)
    | aAlt ag1 ag2 => 
      (List.map (fun x => inl _ x) (astgram_extract_nil ag1)) ++ 
      (List.map (fun x => inr _ x) (astgram_extract_nil ag2))
    | aStar ag => nil::nil
  end.

Fixpoint derivs_and_split (a:astgram) (cs:list char_t) : 
  af_pair (List_t (astgram_type a)) :=
  match cs with 
    | nil => af a (xsingle xid)
    | c::cs' => let (a1, x1) := deriv_and_split a c in 
                let (a2, x2) := derivs_and_split a1 cs' in 
                af a2 (xthen x2 x1)
  end.


(*********************************************)
(* Proofs                                    *)
(*********************************************)
Fixpoint mrg_alt (p1s : list astgram) : list astgram -> list astgram := 
  match p1s with 
    | nil => fun p2s => p2s
    | p1::p1s' => 
      (fix mrg_alt_aux (p2s:list astgram) : list astgram := 
         match p2s with 
           | nil => p1::p1s'
           | p2::p2s' => 
             match astgram_cmp p1 p2 with 
               | Eq => let ps := mrg_alt p1s' p2s' in p1::ps
               | Lt => let ps := mrg_alt p1s' (p2::p2s') in (p1::ps)
               | Gt => let ps := mrg_alt_aux p2s' in (p2::ps)
             end
         end)
  end.

Lemma mrg_alt_corr p1s : forall p2s,
  match merge_alt p1s p2s with 
      | existT ps _ => ps = mrg_alt p1s p2s
  end.
Proof.
  induction p1s ; [simpl ; auto | idtac]. 
  induction p2s ; [simpl ; auto | idtac]. 
  simpl. generalize (astgram_eq_corr a a0). generalize (astgram_cmp a a0) as c.
  destruct c  ; intros. 
  specialize (IHp1s p2s). destruct (merge_alt p1s p2s). simpl. congruence.
  specialize (IHp1s (a0::p2s)).
  destruct (merge_alt p1s (a0::p2s)). simpl. congruence. simpl in *.
  match goal with 
      | [ H : match ?e1 with | existT _ _ => _ end |- _] => remember e1 
  end.
  destruct a1. simpl. congruence.
Qed.
                          
Fixpoint flat_alt (a:astgram) : list astgram := 
  match a with 
    | aAlt a1 a2 => 
      let p1s := flat_alt a1 in 
      let p2s := flat_alt a2 in 
      mrg_alt p1s p2s
    | aZero => nil
    | a' => (a'::nil)
  end.

Lemma flat_alt_corr : 
  forall a, 
    match flatten_alt a with 
      | existT ps _ => ps = flat_alt a
    end.
Proof.
  induction a ; simpl ; auto.
  destruct (flatten_alt a1). destruct (flatten_alt a2). 
  generalize (mrg_alt_corr x x1). destruct (merge_alt x x1). 
  intros ; simpl. congruence.
Qed.

Fixpoint flat_cat (a:astgram) : list astgram := 
  match a with 
    | aCat a1 a2 => 
      let p1s := flat_cat a1 in 
      let p2s := flat_cat a2 in 
      p1s ++ p2s
    | aEps => nil
    | a' => (a'::nil)
  end.

Lemma append_cat_corr : 
  forall (as1 as2:list astgram),
    match append_cat as1 as2 with
      | existT ps _ => ps = as1 ++ as2
    end.
Proof.
  induction as1. simpl ; auto. simpl. intros. specialize (IHas1 as2).
  destruct (append_cat as1 as2). simpl. congruence.
Qed.

Lemma flat_cat_corr (a:astgram) :
  match flatten_cat a with 
      | existT ps _ => ps = flat_cat a
  end.
Proof.
  induction a ; simpl ; auto. destruct (flatten_cat a1). destruct (flatten_cat a2). 
  generalize (append_cat_corr x x1). destruct (append_cat x x1). intros. simpl.
  congruence.
Qed.

Fixpoint recat (ps:list astgram) : astgram := 
  match ps with 
    | nil => aEps
    | p::nil => p
    | p::ps' => aCat p (recat ps')
  end.

Definition realt (ps:list astgram) : astgram := 
  balance aAlt (fun x => x) aZero ps.

Lemma recat_corr ps : 
  match re_cat' ps with 
    | existT ps1 _ => ps1 = recat ps
  end.
Proof. 
  induction ps ; simpl ; auto. destruct ps. simpl ; auto.
  destruct (re_cat' (a0::ps)). simpl in *. congruence.
Qed.

Lemma merge_adj_corr' n : 
  forall zs, length zs < n -> 
  match merge_pairs_dep zs with 
      | existT ys _ => ys = merge_adj aAlt zs
  end.
Proof. 
  induction n ; simpl ; intros. omega.
  destruct zs. simpl ; auto. simpl in *. assert (length zs < n). omega.
  destruct zs ; simpl ; auto. simpl in *. assert (length zs < n). omega. 
  specialize (IHn _ H1). destruct (merge_pairs_dep zs). simpl. congruence.
Qed.

Lemma merge_adj_corr zs : 
  match merge_pairs_dep zs with
      | existT ys _ => ys = merge_adj aAlt zs
  end.
Proof.
  assert (length zs < S(length zs)). omega. eapply merge_adj_corr' ; eauto.
Qed.

Lemma map_id {A} (xs:list A) : 
  List.map (fun x => x) xs = xs.
Proof.
  induction xs ; simpl ; auto ; rewrite IHxs ; auto.
Qed.

Lemma realt_corr' n : 
  forall ps, length ps < n -> 
  match re_alt' ps with 
      | existT ps1 _ => ps1 = realt ps
  end.
Proof.
 induction n ; simpl ; intros. omega.
 destruct ps ; simpl ; auto. destruct ps. simpl ; auto. 
 rewrite re_alt'_equation. unfold realt. unfold balance.
 rewrite balance'_equation. rewrite map_id.
 generalize (merge_adj_corr (a::a0::ps)).
 destruct (merge_pairs_dep (a::a0::ps)). intros ; subst.
 assert (length (merge_adj aAlt (a::a0::ps)) < n). generalize (balance_lt aAlt ps a a0).
 simpl in *. intros ; omega. specialize (IHn _ H0).
 destruct (re_alt' (merge_adj aAlt (a::a0::ps))). subst. simpl. unfold realt.
 unfold balance. rewrite map_id. auto.
Qed.

Lemma realt_corr ps : 
  match re_alt' ps with 
    | existT ps1 _ => ps1 = realt ps
  end.
Proof.
  eapply (@realt_corr' (S (length ps))). omega.
Qed.

Definition appcat (p1s p2s:list astgram) := p1s ++ p2s.

Lemma appcat_corr p1s : 
  forall p2s, match append_cat p1s p2s with
                | existT ps _ => ps = appcat p1s p2s
              end.
Proof.
  induction p1s ; simpl ; auto. intro. specialize (IHp1s p2s). 
  destruct (append_cat p1s p2s). simpl ; congruence.
Qed.

Fixpoint opt_a (a:astgram) : astgram := 
  match a with 
    | aAlt a1 a2 => 
      let a1' := opt_a a1 in 
      let a2' := opt_a a2 in
      let p1s := flat_alt a1' in 
      let p2s := flat_alt a2' in 
      let p := mrg_alt p1s p2s in
      balance aAlt (fun x => x) aZero p
    | aCat a1 a2 => 
      let a1' := opt_a a1 in 
      let a2' := opt_a a2 in 
      match a1' with 
        | aZero => aZero
        | b1 => 
          match a2' with 
              | aZero => aZero 
              | b2 => 
                let p1s := flat_cat b1 in 
                let p2s := flat_cat b2 in 
                let p := appcat p1s p2s in 
                recat p
          end
      end
    | aStar a1 => 
      let a1' := opt_a a1 in 
      match a1' with 
        | aZero => aEps
        | aStar a'' => aStar a''
        | a'' => aStar a''
      end
    | a' => a'
  end.

Lemma opt_a_corr : 
  forall a, match opt_ag a with 
              | existT a' _ => a' = opt_a a
            end.
Proof.
  induction a ; simpl ; auto. destruct (opt_ag a1) ; destruct (opt_ag a2) ; simpl. 
  rewrite <- IHa1 ; rewrite <- IHa2.
  generalize (flat_cat_corr x) (flat_cat_corr x1). destruct (flatten_cat x) ; 
  destruct (flatten_cat x1). intros. rewrite <- H ; rewrite <- H0.
  generalize (appcat_corr x3 x5). destruct (append_cat x3 x5). intro. rewrite <- H1.
  generalize (recat_corr x7). unfold re_cat. destruct (re_cat' x7). intros. rewrite <- H2.
  destruct x ; destruct x1 ; simpl ; auto.
  destruct (opt_ag a1) ; destruct (opt_ag a2) ; simpl ; rewrite <- IHa1 ; rewrite <- IHa2.
  generalize (flat_alt_corr x) (flat_alt_corr x1) ; destruct (flatten_alt x) ; 
  destruct (flatten_alt x1) ; intros. rewrite <- H ; rewrite <- H0.
  generalize (mrg_alt_corr x3 x5). destruct (merge_alt x3 x5) ; intros. rewrite <- H1.
  generalize (realt_corr x7). unfold re_alt. destruct (re_alt' x7). intros. simpl.
  rewrite H2. auto.
  destruct (opt_ag a) ; simpl. rewrite <- IHa. destruct x ; simpl ; auto.
Qed.


Fixpoint list_all {A} (P:A -> Prop) (xs: list A) : Prop := 
  match xs with 
    | nil => True
    | h::t => P h /\ list_all P t
  end.

Lemma list_all_app {A} (P:A->Prop) (xs ys:list A) :
  list_all P xs -> list_all P ys -> list_all P (xs ++ ys).
Proof.
  induction xs ; auto. simpl. intros. destruct H. split ; auto.
Qed.

Lemma list_all_imp {A} (P1:A->Prop) (P2:A->Prop) : 
  (forall x, P1 x -> P2 x) -> forall xs, list_all P1 xs -> list_all P2 xs.
Proof.
  intro ; induction xs ; crush.
Qed.

Fixpoint increasing (xs:list astgram) : Prop := 
  match xs with 
    | nil => True
    | x::xs => increasing xs /\ list_all (fun y => astgram_cmp x y = Lt) xs
  end.

Fixpoint wf_astgram (a:astgram) : Prop := 
  match a with 
    | aAlt a1 a2 =>
      a1 <> aZero /\ a2 <> aZero /\ 
      wf_astgram a1 /\ wf_astgram a2 /\ increasing (flat_alt a1 ++ flat_alt a2)
    | aCat a1 a2 => 
      (match a1 with aEps => False | aCat _ _ => False | aZero => False | _ => True end) /\
      (match a2 with aEps => False | aZero => False | _ => True end) /\
      wf_astgram a1 /\ wf_astgram a2
    | aStar a1 => 
      (match a1 with aZero => False | aStar _ => False | _ => True end) /\ wf_astgram a1
    | _ => True
  end.

Ltac mycrush := 
  simpl in * ; 
  match goal with 
    | [ H : _ /\ _ |- _ ] => destruct H ; crush
    | [ H : False |- _ ] => contradiction H
    | [ |- forall _,_ ] => intro ; crush
    | [ |- _ /\ _ ] => split ; crush
    | [ |- _ <> _ ] => discriminate
    | _ => eauto
  end.

Lemma recat_wf (xs:list astgram) : 
  list_all (fun x => wf_astgram x /\ 
                     match x with aEps => False | aZero => False | aCat _ _ => False
                               | _ => True
                     end) xs -> wf_astgram (recat xs).
Proof.
  induction xs ; crush. specialize (IHxs H0). destruct xs ; auto. repeat split ; auto.
  simpl in *. destruct xs ; auto. destruct H0. destruct H0. destruct a0 ; auto.
Qed.

Lemma flat_cat_wf (a:astgram) : 
  a <> aZero -> 
  wf_astgram a -> 
  list_all (fun x : astgram =>
      wf_astgram x /\
      match x with
      | aAny => True
      | aEps => False
      | aZero => False
      | aChar _ => True
      | aCat _ _ => False
      | aAlt _ _ => True
      | aStar _ => True
      end) (flat_cat a).
Proof.
  induction a ; crush. assert (a1 <> aZero). destruct a1 ; try congruence.
  specialize (IHa1 H4 H2). assert (a2 <> aZero). destruct a2 ; try congruence.
  specialize (IHa2 H5 H3). apply list_all_app; auto.
Qed.

Definition notadd (a:astgram) : Prop := 
  match a with
      | aZero => False
      | aAlt _ _ => False
      | _ => True
  end.

Lemma mrg_alt_wf (a1s:list astgram) : 
  list_all notadd a1s -> increasing a1s -> list_all wf_astgram a1s ->
  forall a2s, 
    list_all notadd a2s -> increasing a2s -> list_all wf_astgram a2s ->
    list_all notadd (mrg_alt a1s a2s) /\ increasing (mrg_alt a1s a2s) /\ 
    list_all wf_astgram (mrg_alt a1s a2s) /\
    forall a, list_all (fun y => astgram_cmp a y = Lt) a1s -> 
              list_all (fun y => astgram_cmp a y = Lt) a2s -> 
              list_all (fun y => astgram_cmp a y = Lt) (mrg_alt a1s a2s).
Proof.
  induction a1s. simpl ; intros ; split ; auto. 
  simpl. intros. destruct H. destruct H0. destruct H1. 
  induction a2s. crush.
  simpl in *. destruct H2. destruct H3. destruct H4. specialize (IHa2s H8 H3 H10).
  specialize (IHa1s H5 H0 H7). remember (astgram_cmp a a0) as e.
  destruct e. 
  Case "Eq".
    clear IHa2s. specialize (IHa1s _ H8 H3 H10) ; crush. apply H14 ; auto.
    rewrite (astgram_eq_corr _ _ (eq_sym Heqe)). auto.
  Case "Lt".
    clear IHa2s. specialize (IHa1s (a0::a2s) (conj H2 H8) (conj H3 H9) (conj H4 H10)).
    crush. rewrite <- Heqe. apply H14 ; crush. rewrite <- Heqe. 
    apply (@list_all_imp _ (fun y => astgram_cmp a0 y = Lt)) ; auto. intros.
    eapply astgram_cmp_trans. eauto. auto.
  Case "Gt".
    clear IHa1s. assert (astgram_cmp a0 a = Lt). rewrite (astgram_cmp_sym a a0).
    rewrite <- Heqe ; auto. crush. apply H15 ; crush.
    apply (@list_all_imp _ (fun y => astgram_cmp a y = Lt)) ; auto. intros.
    eapply astgram_cmp_trans ; eauto.
Qed.

Lemma flat_alt_wf (a:astgram) : 
  wf_astgram a -> 
  list_all notadd (flat_alt a) /\ increasing (flat_alt a) /\ list_all wf_astgram (flat_alt a).
Proof.
  induction a ; try (crush ; fail). simpl ; intros. destruct H as [H [H1 [H2 [H3 H4]]]].
  specialize (IHa1 H2). specialize (IHa2 H3). destruct IHa1 as [H5 [H6 H7]].
  destruct IHa2 as [H8 [H9 H10]].
  generalize (mrg_alt_wf _ H5 H6 H7 _ H8 H9 H10). crush.
Qed.

Lemma merge_adj_nz' (n:nat) : 
  forall l, length l < n -> list_all (fun x => x <> aZero) l -> 
            list_all (fun x => x <> aZero) (merge_adj aAlt l).
Proof.
  induction n ; crush. destruct l ; crush. destruct l ; crush.
  apply IHn; crush.
Qed.

Lemma merge_adj_nz l : list_all (fun x => x <> aZero) l -> 
                       list_all (fun x => x <> aZero) (merge_adj aAlt l).
Proof.
  apply (@merge_adj_nz' (S (length l))) ; crush.
Qed.

Lemma app_list_all {A} (P:A->Prop) (xs ys:list A) : 
  list_all P (xs ++ ys) -> list_all P xs /\ list_all P ys.
Proof.
  induction xs. crush. simpl. intros. destruct H. specialize (IHxs H0). crush.
Qed.

Lemma increasing_app : 
  forall (l1 l2:list astgram),
    increasing (l1 ++ l2) -> increasing l1 /\ increasing l2.
Proof.
  induction l1 ; crush. destruct (IHl1 _ H) ; auto. apply (proj1 (app_list_all _ _ _ H0)).
  apply (proj2 (IHl1 _ H)).
Qed.

Lemma inc_mrg_alt : 
  forall as1 as2, 
    increasing (as1 ++ as2) ->
    (mrg_alt as1 as2) = as1 ++ as2.
Proof.
  induction as1 ; crush. generalize H H0 ; clear H H0. induction as2. crush. 
  rewrite <- app_nil_end. auto. intros. generalize (app_list_all _ _ _ H0). crush.
Qed.

Lemma fold_flat_merge' n : 
  forall l, length l < n -> 
  increasing (fold_right (fun a xs => flat_alt a ++ xs) nil l) -> 
  (fold_right (fun a xs => flat_alt a ++ xs) nil l) = 
  (fold_right (fun a xs => flat_alt a ++ xs) nil (merge_adj aAlt l)).
Proof.
  induction n ; crush. destruct l ; crush. destruct l ; crush. rewrite <- app_ass in H0.
  generalize (increasing_app _ _ H0). intro H1 ; destruct H1.
  rewrite IHn ; auto. rewrite inc_mrg_alt. rewrite <- app_ass. auto. auto. omega.
Qed.

Lemma fold_flat_merge l : 
  increasing (fold_right (fun a xs => flat_alt a ++ xs) nil l) -> 
  (fold_right (fun a xs => flat_alt a ++ xs) nil l) = 
  (fold_right (fun a xs => flat_alt a ++ xs) nil (merge_adj aAlt l)).
Proof.
  apply (@fold_flat_merge' (S (length l))) ; crush.
Qed.

Lemma merge_adj_wf' n : 
  forall l, length l < n -> 
            list_all wf_astgram l -> 
            list_all (fun x => x <> aZero) l -> 
            increasing (fold_right (fun a xs => flat_alt a ++ xs) nil l) -> 
            list_all wf_astgram (merge_adj aAlt l).
Proof.
  induction n ; crush. destruct l ; crush. destruct l ; crush.
  rewrite <- app_ass in H2. apply (proj1 (increasing_app _ _ H2)).
  apply IHn ; crush. rewrite <- app_ass in H2. apply (proj2 (increasing_app _ _ H2)).
Qed.

Lemma merge_adj_wf l : 
  list_all wf_astgram l -> 
  list_all (fun x => x <> aZero) l -> 
  increasing (fold_right (fun a xs => flat_alt a ++ xs) nil l) -> 
  list_all wf_astgram (merge_adj aAlt l).
Proof.
  apply (@merge_adj_wf' (S (length l))) ; crush.
Qed.

Lemma balance_wf' (n:nat) : 
  forall (l:list astgram),
    length l < n -> list_all (fun x => x <> aZero) l -> 
    list_all wf_astgram l -> 
    increasing (fold_right (fun a xs => (flat_alt a) ++ xs) nil l) -> 
    wf_astgram (balance' aAlt aZero l).
Proof.
  induction n ; crush. rewrite balance'_equation. destruct l ; crush.
  destruct l ; crush. rewrite <- app_ass in H2. generalize (increasing_app _ _ H2). crush.
  apply IHn. generalize (balance_lt aAlt l a a0). simpl in *. omega.
  crush. apply merge_adj_nz ; crush. simpl. crush. 
  apply merge_adj_wf ; crush. simpl. rewrite inc_mrg_alt ; crush. 
  rewrite <- fold_flat_merge ; auto. 
Qed.

Lemma balance_wf l : 
  list_all (fun x => x <> aZero) l -> 
    list_all wf_astgram l -> 
    increasing (fold_right (fun a xs => (flat_alt a) ++ xs) nil l) -> 
    wf_astgram (balance' aAlt aZero l).
Proof.
  apply (@balance_wf' (S (length l))) ; crush.
Qed.

Lemma mrg_alt_nz l1 : 
  list_all notadd l1 -> 
  forall l2, list_all notadd l2 -> list_all notadd (mrg_alt l1 l2).
Proof.
  induction l1 ; crush ;induction l2 ; crush ; destruct (astgram_cmp a a0) ; crush. 
  apply IHl1 ; crush.
Qed.

Lemma fold_flat l : 
  increasing l -> list_all notadd l -> 
  fold_right (fun a xs => flat_alt a ++ xs) nil l = l.
Proof.
  induction l ; crush. assert (flat_alt a = (a::nil)). destruct a ; crush.
  rewrite H3. crush.
Qed.

Lemma opt_wf (a:astgram) : wf_astgram (opt_a a).
Proof.
  induction a ; try (crush ; fail).
  Case "aCat".
    assert (opt_a a1 = aZero \/ opt_a a1 <> aZero). 
    destruct (opt_a a1) ; try (right ; discriminate) ; left ; auto. destruct H. 
    simpl ; rewrite H ; simpl ; auto. 
    assert (opt_a a2 = aZero \/ opt_a a2 <> aZero).
    destruct (opt_a a2) ; try (right ; discriminate) ; left ; auto. destruct H0.
    simpl ; rewrite H0 ; destruct (opt_a a1) ; simpl ; auto.
    replace (opt_a (aCat a1 a2)) with 
    (recat (appcat (flat_cat (opt_a a1))(flat_cat (opt_a a2))));
      [idtac | simpl ; destruct (opt_a a1) ; destruct (opt_a a2) ; auto ; congruence]. 
    apply recat_wf. unfold appcat. apply list_all_app. apply (flat_cat_wf H IHa1).
    apply (flat_cat_wf H0 IHa2). simpl.
  Case "aAlt".
    generalize (flat_alt_wf _ IHa1) (flat_alt_wf _ IHa2) ; crush. unfold balance.
    rewrite map_id. specialize (mrg_alt_wf _ H H3 H4 _ H0 H1 H2). crush. 
    apply balance_wf ; crush. apply (list_all_imp notadd). destruct x ; crush. 
    apply mrg_alt_nz ; auto. rewrite fold_flat ; crush.
  Case "aStar".
    simpl. destruct (opt_a a) ; crush.
Qed.

Lemma notadd_flat (a:astgram) : 
  wf_astgram a -> list_all notadd (flat_alt a).
Proof.
  induction a ; crush. apply mrg_alt_nz ; crush.
Qed.

Lemma flat_balance' n : 
  forall l, 
    length l < n -> 
    list_all (fun x => x <> aZero) l -> 
    list_all wf_astgram l -> increasing l ->
    flat_alt (balance' aAlt aZero l) = fold_right (fun a x => flat_alt a ++ x) nil l.
Proof.
  induction n; crush. 
  destruct l ; crush ; destruct l. destruct a; crush.
  apply app_nil_end. rewrite balance'_equation. generalize (balance_lt aAlt l a a0).
  intros. rewrite IHn.  Focus 2. crush.
crush. 
  rewrite inc_mrg_alt ; crush. rewrite <- fold_flat_merge. auto.




Lemma flat_balance' (a1 a2:astgram) : 
  wf_astgram a1 -> wf_astgram a2 -> 
  flat_alt (balance' aAlt aZero (mrg_alt (flat_alt a1) (flat_alt a2))) = 
  mrg_alt (flat_alt a1) (flat_alt a2).
Proof. 
  intros. 
  assert (list_all (fun x => x <> aZero) (mrg_alt (flat_alt a1) (flat_alt a2))).
  apply (list_all_imp notadd). destruct x ; crush.
  apply mrg_alt_nz. apply (notadd_flat a1 H). apply (notadd_flat a2 H0).
  generalize H1 ; clear H1. generalize (mrg_alt (flat_alt a1) (flat_alt a2)). 
  clear a1 a2 H H0.
  assert (forall n, forall l, length l < n -> list_all (fun x => x <> aZero) l -> 
                              flat_alt (balance' aAlt aZero l) = l).
  induction n; crush. destruct l ; crush. destruct l ; crush.
  destruct a ; crush. rewrite balance'_equation. simpl. rewrite IHn ; crush.
*)


Lemma opt_alt_assoc (a1 a2 a3:astgram) : 
  opt_a (aAlt a1 (aAlt a2 a3)) = opt_a (aAlt (aAlt a1 a2) a3).
Proof.
  intros. 
  generalize (opt_wf a1) (opt_wf a2) (opt_wf a3) 
             (opt_wf (aAlt a1 (aAlt a2 a3))) (opt_wf (aAlt (aAlt a1 a2) a3)).
  simpl. generalize (opt_a a1) (opt_a a2) (opt_a a3). clear a1 a2 a3. 
  intros a1 a2 a3 H1 H2 H3 H4 H5.
  unfold balance. repeat rewrite map_id.


SearchAbout (notadd (flat_alt _)).
  generalize (fun p1 p2 => mrg_alt_nz (flat_alt a1) p1 (flat_alt a2) p2).
  remember (mrg_alt (flat_alt a1) (flat_alt a2)) as e.
  SearchAbout (mrg_alt _ _).



  unfold balance. repeat rewrite map_id.
  Lemma flat_balance' n : 
    forall l, length l < n -> 
              list_all wf_astgram l -> 
              list_all (fun x => x <> aZero) l -> 
              flat_alt (balance' aAlt aZero l) = l.
  Proof.
    induction n ; crush ; destruct l ; crush. rewrite balance'_equation.
    destruct l ; crush. destruct a ; crush.
    
    
SearchAbout mrg_alt.

Lemma flatten_re_alt : 
  forall (ps1 ps : list astgram), 
    length ps <= length ps1 -> 
    list_all not_sum ps ->
    match re_alt' ps with 
      | existT a _ => match flatten_alt a with
                        | existT ps' _ => ps = ps'
                      end
    end.
Proof.  
  induction ps1. simpl. intros. destruct ps. simpl. auto.
  simpl in *. omega. destruct ps. simpl ; auto. rewrite re_alt'_equation. 
  destruct ps. simpl. intros. destruct H0. apply (flatten_not_sum a0 H0). 
  intros. destruct H0 as [H0 [H1 H2]]. assert (length ps <= length ps1). 
  simpl in H. omega. specialize (IHps1 _ H3 H2). simpl (merge_pairs_dep _).

Definition alts := List.fold_right aAlt aZero.
Definition cats := List.fold_right aCat aEps.
Definition ff := aChar false.
Definition tt := aChar true.

Fixpoint xopt' {t1 t2} (n:nat) (x:t1->>t2) : t1->>t2 := 
  match n with 
    | 0 => x
    | S m => xopt' m (xopt x)
  end.

Definition foo g n := 
  match deriv_and_split g false with 
      | existT a x => 
        let y := xopt' n x in 
        (a, show_xform y, xform_count y)
  end.

Definition xs : list astgram :=
  (cats (ff::ff::ff::ff::nil))::
  (cats (ff::tt::ff::tt::nil))::
        (cats (tt::ff::tt::ff::nil))::
        (cats (ff::nil))::
        (cats (ff::tt::nil))::
        (cats (ff::tt::tt::nil))::
        (cats (ff::tt::tt::tt::nil))::
        (cats (ff::tt::tt::tt::tt::nil))::
        (cats (ff::tt::tt::tt::tt::tt::nil))::
        (cats (ff::tt::tt::tt::tt::tt::tt::nil))::
        (cats (ff::tt::tt::tt::tt::tt::tt::tt::nil))::
        nil.

Definition g := balance aAlt (fun x => x) aZero xs.

Time Eval vm_compute in foo g 20.

