Require Import List.
Require Export Char.
Require Import Xform.
Require Import CommonTacs.
Require Import Structures.OrdersAlt.

Inductive regexp : Set := 
| Eps : regexp
| Zero : regexp
| Char : char_t -> regexp
| Any : regexp
| Cat : regexp -> regexp -> regexp
| Alt : regexp -> regexp -> regexp
| Star : regexp -> regexp.

(** Compute the return [type] of an [regexp]. *)
Fixpoint regexp_type (pg : regexp) : type := 
  match pg with 
    | Eps => Unit_t
    | Zero => Void_t
    | Char _ => Char_t
    | Any => Char_t
    | Cat pg1 pg2 => Pair_t (regexp_type pg1) (regexp_type pg2)
    | Alt pg1 pg2 => Sum_t (regexp_type pg1) (regexp_type pg2)
    | Star pg => List_t (regexp_type pg)
  end.

Inductive in_regexp : forall a, list char_t -> interp (regexp_type a) -> Prop :=
| InEps : forall s v, s = nil -> v = tt -> in_regexp Eps s v
| InChar : forall c s v, s = c::nil -> v = c -> in_regexp (Char c) s v
| InAny : forall c s v, s = c::nil -> v = c -> in_regexp Any s v
| InCat : 
    forall a1 a2 s1 s2 v1 v2 s v,
      in_regexp a1 s1 v1 -> in_regexp a2 s2 v2 -> s = s1 ++ s2 -> v = (v1,v2) -> 
      in_regexp (Cat a1 a2) s v
| InAlt_l : 
    forall a1 a2 s v1 v, 
      in_regexp a1 s v1 -> v = inl _ v1 -> in_regexp (Alt a1 a2) s v
| InAlt_r : 
    forall a1 a2 s v2 v, 
      in_regexp a2 s v2 -> v = inr _ v2 -> in_regexp (Alt a1 a2) s v
| InStar_eps : forall a s v, s = nil -> v = nil -> in_regexp (Star a) s v
| InStar_cons : 
    forall a s1 v1 s2 v2 s v,
      in_regexp a s1 v1 -> in_regexp (Star a) s2 v2 -> 
      s1 <> nil -> s = s1 ++ s2 -> v = v1::v2 -> in_regexp (Star a) s v.
Hint Constructors in_regexp.

(** * Ordering for regexps *)

(** Use lexicographic ordering when ordering two regexps. *)
Fixpoint compare_re (r1 r2:regexp) : comparison := 
  match r1 with
    | Eps => match r2 with
                | Eps => Eq
                | _ => Lt
              end
    | Zero => match r2 with
                 | Eps => Gt
                 | Zero => Eq
                 | _ => Lt
               end
    | Char c1 => 
      match r2 with
        | Eps | Zero => Gt
        | Char c2 => char_cmp c1 c2
        | _ => Lt
      end
    | Any => match r2 with
                | Eps | Zero | Char _ => Gt
                | Any => Eq
                | _ => Lt
              end
    | Cat r11 r12 =>
      match r2 with
        | Eps | Zero | Char _ | Any => Gt
        | Cat r21 r22 =>
          let cp := compare_re r11 r21 in
          match cp with
            | Eq => compare_re r12 r22
            | _ => cp
          end
        | _ => Lt
      end
    | Alt r11 r12 =>
      match r2 with
        | Eps | Zero | Char _ | Any | Cat _ _ => Gt
        | Alt r21 r22 =>
          let cp := compare_re r11 r21 in
          match cp with
            | Eq => compare_re r12 r22
            | _ => cp
          end
        | _ => Lt
      end
    | Star r11 => 
      match r2 with
        | Eps | Zero | Char _ | Any | Cat _ _ | Alt _ _ => Gt
        | Star r21 => compare_re r11 r21
      end
  end.

Lemma compare_re_eq_leibniz: 
  forall r1 r2, compare_re r1 r2 = Eq -> r1 = r2.
Proof. induction r1; try (destruct r2; simpl; congruence; fail). 
       Case "aChar".
       destruct r2; simpl; try congruence. intros.
       rewrite (char_eq_leibniz c c0) ; auto.
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
      destruct r2; trivial. 
      generalize (CharOrderedTypeAlt.compare_sym c c0). simpl. auto.
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
      apply (CharOrderedTypeAlt.compare_trans).
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

