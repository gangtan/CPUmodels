Require Import Bits.

Definition char_t : Set := bool.
Definition char_cmp (c1 c2:char_t) : comparison := 
  match c1, c2 with 
    | false, true => Lt
    | true, false => Gt
    | _, _ => Eq
  end.
Lemma char_eq_leibniz : 
  forall c1 c2, char_cmp c1 c2 = Eq -> c1 = c2.
Proof.
  destruct c1 ; destruct c2 ; intros  ; auto ; discriminate.
Qed.
Require Import Coq.Structures.OrdersAlt.
Module CharOrderedTypeAlt <: OrderedTypeAlt.
  Definition t : Type := char_t.
  Definition compare : t -> t -> comparison := char_cmp.

  Lemma compare_sym : forall (c1 c2 : t), compare c2 c1 = CompOpp (compare c1 c2).
  Proof.
    destruct c1 ; destruct c2 ; auto.
  Qed.

  Lemma compare_trans : 
    forall cmp c1 c2 c3, compare c1 c2 = cmp  -> compare c2 c3 = cmp -> compare c1 c3 = cmp.
  Proof.
    destruct c1 ; destruct c2 ; destruct c3 ; simpl ; intros ; subst ; auto ; discriminate.
  Qed.
End CharOrderedTypeAlt.

Module CharOrderedType := OT_from_Alt CharOrderedTypeAlt.
                         
Require Import String.
Open Scope string_scope.
Definition show_char (c:char_t) : string := 
  match c with 
    | true => "1"
    | false => "0"
  end.

