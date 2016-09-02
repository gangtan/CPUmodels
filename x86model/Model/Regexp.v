Require Import Coq.Structures.OrdersAlt.
Require Import CommonTacs.
Require Import Xform.
Require Import ParserArg.
Import X86_PARSER_ARG.

Set Implicit Arguments.

Inductive regexp : Set := 
| rEps : regexp
| rZero : regexp
| rChar : char_p -> regexp
| rAny : regexp
| rCat : regexp -> regexp -> regexp
| rAlt : regexp -> regexp -> regexp
| rStar : regexp -> regexp.

(** Compute the return [xtype] of an [regexp]. *)
Fixpoint regexp_type (pg : regexp) : xtype := 
  match pg with 
    | rEps => xUnit_t
    | rZero => xVoid_t
    | rChar _ => xChar_t
    | rAny => xChar_t
    | rCat pg1 pg2 => xPair_t (regexp_type pg1) (regexp_type pg2)
    | rAlt pg1 pg2 => xSum_t (regexp_type pg1) (regexp_type pg2)
    | rStar pg => xList_t (regexp_type pg)
  end.

Inductive in_regexp : forall a, list char_p -> xt_interp (regexp_type a) -> Prop :=
| InrEps : forall s v, s = nil -> v = tt -> in_regexp rEps s v
| InrChar : forall c s v, s = c::nil -> v = c -> in_regexp (rChar c) s v
| InrAny : forall c s v, s = c::nil -> v = c -> in_regexp rAny s v
| InrCat : 
    forall a1 a2 s1 s2 v1 v2 s v,
      in_regexp a1 s1 v1 -> in_regexp a2 s2 v2 -> s = s1 ++ s2 -> v = (v1,v2) -> 
      in_regexp (rCat a1 a2) s v
| InrAlt_l : 
    forall a1 a2 s v1 v, 
      in_regexp a1 s v1 -> v = inl _ v1 -> in_regexp (rAlt a1 a2) s v
| InrAlt_r : 
    forall a1 a2 s v2 v, 
      in_regexp a2 s v2 -> v = inr _ v2 -> in_regexp (rAlt a1 a2) s v
| InrStar_eps : forall a s v, s = nil -> v = nil -> in_regexp (rStar a) s v
| InrStar_cons : 
    forall a s1 v1 s2 v2 s v,
      in_regexp a s1 v1 -> in_regexp (rStar a) s2 v2 -> 
      s1 <> nil -> s = s1 ++ s2 -> v = v1::v2 -> in_regexp (rStar a) s v.
Hint Constructors in_regexp.

(** * Inversion principles for [regexp]s. *)

Lemma inv_eps : forall s v, in_regexp rEps s v -> s = nil /\ v = tt.
Proof. intros. inversion H. crush. Qed.

Lemma inv_zero : forall s v, in_regexp rZero s v -> False.
Proof. intros. inversion H. Qed.

Lemma inv_char : forall c s v, in_regexp (rChar c) s v -> s = c::nil /\ v = c.
Proof.  intros. inversion H. subst. crush. Qed.

Lemma inv_any : forall s v, in_regexp rAny s v -> s = v::nil.
Proof.  intros. inversion H. crush. Qed.

Lemma inv_cat : forall r1 r2 s v, in_regexp (rCat r1 r2) s v -> 
  exists s1, exists s2, exists v1, exists v2, 
    in_regexp r1 s1 v1 /\ in_regexp r2 s2 v2 /\ s = s1++s2 /\ v = (v1,v2).
Proof.
  intros ; inversion H ; subst ; crush. exists s1. exists s2. exists v1. exists v2.
  auto.
Qed.

Lemma inv_cat_nil : forall r1 r2 v, in_regexp (rCat r1 r2) nil v -> 
  exists v1, exists v2, in_regexp r1 nil v1 /\ in_regexp r2 nil v2 /\ v = (v1,v2).
Proof. intros. apply inv_cat in H.
  destruct H as [s1 [s2 [v1 [v2 H1]]]].
  sim. exists v1, v2.
  symmetry in H1. apply app_eq_nil in H1.
  crush.
Qed.

Lemma inv_alt : forall r1 r2 s v, in_regexp (rAlt r1 r2) s v -> 
  (exists v1, in_regexp r1 s v1 /\ v = inl _ v1) \/
  (exists v2, in_regexp r2 s v2 /\ v = inr _ v2) .
Proof. intros ; inversion H ; subst ; crush. Qed.

Lemma inv_star: forall r s v, in_regexp (rStar r) s v -> 
  (s = nil /\ v = nil) \/
  (exists s1 s2 v1 v2, 
     in_regexp r s1 v1 /\ in_regexp (rStar r) s2 v2 /\
     s1 <> nil /\ s = s1++s2 /\ v=v1::v2).
Proof. intros. inversion H; try crush. 
  right. exists s1, s2, v1, v2. crush.
Qed.

Lemma inv_star_nil: forall r v, in_regexp (rStar r) nil v -> v = nil.
Proof. intros. apply inv_star in H.
  destruct H. crush.
  sim. destruct x; crush.
Qed.

(** Inversion tactic for [regexp]. *)
Ltac in_regexp_inv := 
  match goal with 
    | [ H: in_regexp rZero _ _ |- _ ] => contradiction (inv_zero H)
    | [ H : in_regexp rEps _ _ |- _ ] => 
      generalize (inv_eps H) ; clear H ; crush
    | [ H : in_regexp (rChar _) _ _ |- _] => 
      generalize (inv_char H) ; clear H ; crush
    | [ H : in_regexp rAny _ _ |- _] => 
      generalize (inv_any H) ; clear H ; crush
    | [ H : in_regexp (rCat _ _) nil _ |- _] => 
      generalize (inv_cat_nil H) ; clear H ; crush
    | [ H : in_regexp (rCat _ _) _ _ |- _] => 
      generalize (inv_cat H) ; clear H ; crush
    | [ H : in_regexp (rAlt _ _) _ _ |- _] => 
      generalize (inv_alt H) ; clear H ;  crush
    | [ H : in_regexp (rStar _) nil _ |- _] => 
      generalize (inv_star_nil H) ; clear H ;  crush
    | [ H : in_regexp (rStar _) _ _ |- _] => 
      generalize (inv_star H) ; clear H ;  crush
  end.

(** This function computes the list of all values v, such that 
    [in_regexp nil v] holds. *)
Fixpoint regexp_extract_nil (r:regexp) : list (xt_interp (regexp_type r)) := 
  match r return list (xt_interp (regexp_type r)) with
    | rEps => tt::nil
    | rZero => nil
    | rChar _ => nil
    | rAny => nil
    | rCat ag1 ag2 => list_prod (regexp_extract_nil ag1) (regexp_extract_nil ag2)
    | rAlt ag1 ag2 => 
      (List.map (fun x => inl _ x) (regexp_extract_nil ag1)) ++ 
      (List.map (fun x => inr _ x) (regexp_extract_nil ag2))
    | rStar ag => nil::nil
  end.

(** Nullable (r) returns true iff r can match the empty string *)
Fixpoint regexp_nullable (r:regexp) : bool :=
  match r with
    | rZero | rChar _ | rAny => false
    | rEps => true
    | rCat r1 r2 => regexp_nullable r1 && regexp_nullable r2
    | rAlt r1 r2 => regexp_nullable r1 || regexp_nullable r2
    | rStar r1 => true
  end.

Fixpoint regexp_always_rejects (r:regexp) : bool :=
  match r with
    | rEps => false
    | rChar _ => false
    | rAny => false
    | rZero => true
    | rAlt r1 r2 => regexp_always_rejects r1 && regexp_always_rejects r2
    | rCat r1 r2 => regexp_always_rejects r1 || regexp_always_rejects r2
    | rStar _ => false
  end.

(** * Ordering for regexps *)

(** Use lexicographic ordering when ordering two regexps. *)
Fixpoint compare_re (r1 r2:regexp) : comparison := 
  match r1 with
    | rEps => match r2 with
                | rEps => Eq
                | _ => Lt
              end
    | rZero => match r2 with
                 | rEps => Gt
                 | rZero => Eq
                 | _ => Lt
               end
    | rChar c1 => 
      match r2 with
        | rEps | rZero => Gt
        | rChar c2 => char_cmp c1 c2
        | _ => Lt
      end
    | rAny => match r2 with
                | rEps | rZero | rChar _ => Gt
                | rAny => Eq
                | _ => Lt
              end
    | rCat r11 r12 =>
      match r2 with
        | rEps | rZero | rChar _ | rAny => Gt
        | rCat r21 r22 =>
          let cp := compare_re r11 r21 in
          match cp with
            | Eq => compare_re r12 r22
            | _ => cp
          end
        | _ => Lt
      end
    | rAlt r11 r12 =>
      match r2 with
        | rEps | rZero | rChar _ | rAny | rCat _ _ => Gt
        | rAlt r21 r22 =>
          let cp := compare_re r11 r21 in
          match cp with
            | Eq => compare_re r12 r22
            | _ => cp
          end
        | _ => Lt
      end
    | rStar r11 => 
      match r2 with
        | rEps | rZero | rChar _ | rAny | rCat _ _ | rAlt _ _ => Gt
        | rStar r21 => compare_re r11 r21
      end
  end.

Lemma compare_re_eq_leibniz: 
  forall r1 r2, compare_re r1 r2 = Eq -> r1 = r2.
Proof. induction r1; try (destruct r2; simpl; congruence; fail). 
       Case "rChar".
       destruct r2; simpl; try congruence. intros.
       rewrite (char_eq_leibniz c c0) ; auto.
       Case "rCat".
       destruct r2; simpl; try congruence.
       remember_rev (compare_re r1_1 r2_1) as cmp.
       destruct cmp; crush_hyp.
       Case "rAlt".
       destruct r2; simpl; try congruence.
       remember_rev (compare_re r1_1 r2_1) as cmp.
       destruct cmp; crush_hyp.
       Case "rStar".
       destruct r2; simpl; try congruence.
       crush_hyp.
Qed.

Module REOrderedTypeAlt <: OrderedTypeAlt.
  Definition t:=regexp.
  Definition compare := compare_re.

  Lemma compare_sym : forall r1 r2, compare r2 r1 = CompOpp (compare r1 r2).
  Proof. induction r1; try (destruct r2; trivial; fail).
    Case "rChar".
      destruct r2; trivial. 
      generalize (CharOrderedTypeAlt.compare_sym c c0). simpl. auto.
    Case "rCat".
      destruct r2; trivial. simpl.
        rewrite (IHr1_1 r2_1). destruct (compare r1_1 r2_1); simpl; eauto.
    Case "rAlt".
      destruct r2; trivial. simpl.
        rewrite (IHr1_1 r2_1). destruct (compare r1_1 r2_1); simpl; eauto.
    Case "rStar".
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
    Case "rChar".
      destruct r2; destruct r3; simpl; try congruence.
      apply (CharOrderedTypeAlt.compare_trans).
    Case "rCat".
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
    Case "rAlt".
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
    Case "rStar".  
      destruct r2; destruct r3; simpl; (congruence || eauto).
  Qed.

End REOrderedTypeAlt.

Module REOrderedType := OT_from_Alt REOrderedTypeAlt.
