Require Import Coq.Program.Equality.
Require Import Coqlib.
Require Import List.
Require Import Bool.
Require Import Char.
Set Implicit Arguments.

Inductive void : Type := .

(** Syntax for the types returned by a grammar *)
Inductive type : Type := 
| Unit_t : type
| Char_t : type
| Void_t : type
| Pair_t : type -> type -> type
| Sum_t : type -> type -> type
| List_t : type -> type.
  
Definition type_dec : forall (t1 t2:type), {t1=t2} + {t1<>t2}.
  decide equality.
Defined.
  
(** Interpret the type syntax as a Coq type. *)
Fixpoint interp (t:type) : Type := 
  match t with 
    | Unit_t => unit
    | Char_t => char_t
    | Void_t => void
    | Pair_t t1 t2 => (interp t1) * (interp t2)
    | Sum_t t1 t2 => (interp t1) + (interp t2)
    | List_t t1 => list (interp t1)
  end%type.

(** Syntax for transforms (functions) that map from one type to
      another.  This little first-order language uses a variable-
      free representation (similar to sequents) to avoid messing with
      issues around lambda representations. *)
Reserved Notation "t1 ->> t2" (left associativity, at level 69, t2 at next level).
Inductive xform : type -> type -> Type := 
| Xid    : forall {t}, t ->> t
| Xzero  : forall {t}, Void_t ->> t
| Xcomp  : forall {t1 t2 t3}, (t1 ->> t2) -> (t2 ->> t3) -> (t1 ->> t3)
| Xchar  : forall {t}, char_t -> t ->> Char_t
| Xunit  : forall {t}, t ->> Unit_t
| Xempty : forall {t1 t2}, t1 ->> List_t t2 
| Xpair  : forall {t t1 t2}, (t ->> t1) -> (t ->> t2) -> (t ->> Pair_t t1 t2)
| Xfst   : forall {t1 t2}, (Pair_t t1 t2) ->> t1
| Xsnd   : forall {t1 t2}, (Pair_t t1 t2) ->> t2
| Xinl   : forall {t1 t2}, t1 ->> (Sum_t t1 t2)
| Xinr   : forall {t1 t2}, t2 ->> (Sum_t t1 t2)    
| Xmatch : forall {t t1 t2},  (t1 ->> t) -> (t2 ->> t) -> (Sum_t t1 t2 ->> t)
| Xcons  : forall {t1 t2}, (t1 ->> t2) -> (t1 ->> List_t t2) -> (t1 ->> List_t t2)
| Xfoldr : forall {t1 t2 t3}, 
             (Pair_t t1 t2 ->> t2) -> (t3 ->> t2) -> (t3 ->> List_t t1) -> t3 ->> t2
where "t1 ->> t2" := (xform t1 t2).

(** Interpret the transform syntax as a Coq function.  Note that 
      this is really a "compiler" of sorts in that we are able to
      translate all of the sub-terms at compile-time, so we don't
      pay the pattern-match cost at run-time.
 *)      
Fixpoint xinterp {t1 t2} (x: t1 ->> t2) : interp t1 -> interp t2 := 
  match x in t1 ->> t2 return interp t1 -> interp t2 with 
    | Xid t => fun (x:interp t) => x
    | Xzero t => fun (x:interp Void_t) => match x with end
    | Xcomp ta tb tc f1 f2 => 
      let f1' := xinterp f1 in 
      let f2' := xinterp f2 in 
      fun x => f2' (f1' x)
    | Xchar t c => fun (x:interp t) => c
    | Xunit t => fun (x:interp t) => tt
    | Xempty ta tb => fun (x:interp ta) => (@nil (interp tb))
    | Xpair ta tb tc f1 f2 => 
      let f1' := xinterp f1 in 
      let f2' := xinterp f2 in 
      fun x => (f1' x, f2' x)
    | Xfst ta tb => @fst _ _
    | Xsnd ta tb => @snd _ _
    | Xinl ta tb => @inl _ (interp tb)
    | Xinr ta tb => @inr (interp ta) _
    | Xmatch ta tb tc f1 f2 => 
      let f1' := xinterp f1 in 
      let f2' := xinterp f2 in 
      fun x => 
        match x with 
          | inl x1 => f1' x1 
          | inr x2 => f2' x2 
        end
    | Xcons ta tb f1 f2 => 
      let f1' := xinterp f1 in 
      let f2' := xinterp f2 in 
      fun (x:interp ta) => (f1' x)::(f2' x)
    | Xfoldr ta tb tc f1 f2 f3 =>
      let f1' := xinterp f1 in 
      let f2' := xinterp f2 in 
      let f3' := xinterp f3 in
      fun x => List.fold_right (fun a b => f1' (a,b)) (f2' x) (f3' x)
  end.

(** * Optimize an [xform]. *)

(* Here are the optimizations we do on transforms.  I'm using ";" to
     abbreviate composition, and the other abbreviations should be obvious.
     Our primary goal is to get rid of obvious reductions like constructing
     a pair, and then immediately projecting out the first component.  Along
     the way, we effectively get rid of composition (similar to cut-elimination)
     so that as many of the reductions fire as possible.  We also do some 
     "eta-like" reductions (e.g., (fst,snd) = id), but not all of those that
     are possible yet.  

     id ; f => f
     zero ; f => zero

     f ; id => f
     f ; (f1 ; f2) => (f ; f1) ; f2
     f ; char c => char c
     f ; unit => unit
     f ; empty => empty
     f ; (g1, g2) => (f;g1, f;g2)
     f ; g1::g2 => (f;g1)::(f;g2)
     f ; foldr g1 g2 g3 => foldr g1 (f ; g2) (f ; g3)

     (f1,f2) ; fst => f1
     (f1,f2) ; snd => f2
     inl ; match f1 f2 => f1
     inr ; match f1 f2 => f2 
     foldr f1 f2 empty => f2
     foldr f1 f2 (f3::f4) => (f3, foldr f1 f2 f4) ; f1

     foldr f1 f2 zero => zero
     foldr f1 zero f3 => zero
     pair zero f => zero
     pair f zero => f
     cons zero f => zero
     cons f zero => zero

     (fst, snd) => id
     match inl inr => id

     I'd like to add support for the "eta" rule for lists:
       foldr (fst::snd) empty f => f
     but haven't bothered to yet.

     Finally, it may be necessary to call the rewriting multiple times
     to get a normal form, since I wasn't able to make all of the 
     reductions mutually recursive as they need to be.
   *)

(** Need some explicit casting to get things to type-check. *)
Definition xcoerce t1 t2 t3 t4 (x:xform t1 t2) : t1 = t3 -> t2 = t4 -> xform t3 t4.
  intros. subst. apply x.
Defined.

(** A note:  It would be much more natural to index [grammar] and [xform] by 
    the corresponding Coq [Type]s instead of my own internal [type] syntax,
    which then has to be interpreted.  In particular, I could get rid of
    the need to use [Extraction Implicit] which is a bit of a hack for 
    getting rid of the [type]s in the extracted code.  However, I wouldn't
    be able to prove these crucial injectivity properties of sums and
    products. *)
Definition eq_pair_fst t1 t2 t3 t4 : (Pair_t t1 t2 = Pair_t t3 t4) -> t3 = t1.
  intros ; injection H. intros. apply (eq_sym H1).
Defined.
Definition eq_pair_snd t1 t2 t3 t4 : (Pair_t t1 t2 = Pair_t t3 t4) -> t4 = t2.
  intros ; injection H. intros. apply (eq_sym H0).
Defined.
Definition eq_sum_fst t1 t2 t3 t4 : (Sum_t t1 t2 = Sum_t t3 t4) -> t3 = t1.
  intros ; injection H. intros. apply (eq_sym H1).
Defined.
Definition eq_sum_snd t1 t2 t3 t4 : (Sum_t t1 t2 = Sum_t t3 t4) -> t4 = t2.
  intros ; injection H. intros. apply (eq_sym H0).
Defined.
Definition list_t_eq : forall t1 t2, (List_t t1 = List_t t2) -> t2 = t1.
  intros. injection H. intro. apply (eq_sym H0).
Defined.
Definition pair_eq_snd t1 t2 t3 t4 : Pair_t t3 t4 = Pair_t t1 t2 -> 
                                     Pair_t t1 t2 = Pair_t t1 t4.
Proof. intros. injection H. intros ; subst. auto.
Defined.
Definition pair_eq_fst t1 t2 t3 : t1 = t2 -> Pair_t t1 t3 = Pair_t t2 t3.
Proof. intro. subst. auto. Defined.  
Definition sum_eq tf th td tc : Sum_t tf th = Sum_t td tc -> Sum_t td th = Sum_t td tc.
  intro. injection H. intros. subst. auto.
Defined.  
Lemma two_pair {w tb tc u2 u3} : 
  (w = Pair_t tb tc) -> (w = Pair_t u2 u3) -> Pair_t tb tc = Pair_t tb u3.
  intros. subst. injection H0. intros ; subst. auto.
Defined.

(** Define some "smart" constructors for transforms that do the reductions
      as we build them. *)

Definition xid {t} : t ->> t := Xid.
Definition xzero {t} : Void_t ->> t := Xzero.
Definition xchar {t} (c:char_t) : t ->> Char_t := Xchar c.
Definition xunit {t} : t ->> Unit_t := Xunit.
Definition xempty {t1 t2} : t1 ->> List_t t2 := Xempty.
Definition xinl {t1 t2} : t1 ->> Sum_t t1 t2 := Xinl.
Definition xinr {t1 t2} : t2 ->> Sum_t t1 t2 := Xinr.
Definition xfst {t1 t2} : Pair_t t1 t2 ->> t1 := Xfst.
Definition xsnd {t1 t2} : Pair_t t1 t2 ->> t2 := Xsnd.

(** These next two functions reduce [Xpair Xfst Xsnd] to [Xid].  
    It's incredibly tedious to propagate the right types and equations around, 
    so I had to break it into two functions. *)
Definition xpair_fst ta tc (x2:ta->>tc):forall t1 t2, 
  (ta = Pair_t t1 t2) -> ta ->>(Pair_t t1 tc) := 
  match x2 in ta->>tc return forall t1 t2,ta=Pair_t t1 t2 -> ta->>(Pair_t t1 tc) with
    | Xsnd t3 t4 => fun t1 t2 H => xcoerce Xid (eq_sym H) (pair_eq_snd H)
    | Xzero _ => fun t1 t2 H => Xzero
    | x2 => fun t1 t2 H => Xpair (xcoerce Xfst (eq_sym H) (eq_refl _)) x2
  end.

Definition xpair_r ta tb tc (x2:ta ->> tc) : (ta ->> tb) -> ta ->> (Pair_t tb tc) := 
  match x2 in ta ->> tc return ta->>tb -> ta->>(Pair_t tb tc) with
    | Xzero _ => fun x1 => Xzero
    | x2 => fun x1 => Xpair x1 x2
  end.

Definition xpair ta tb tc (x1:ta ->> tb) (x2:ta ->> tc) : ta ->> (Pair_t tb tc) := 
 match x1 in ta ->> tb return ta->>tc -> ta->>(Pair_t tb tc) with
   | Xfst t1 t2 => fun x2 => xpair_fst x2 (eq_refl _)
   | Xzero t => fun x2 => Xzero
   | x1 => fun x2 => xpair_r x2 x1 
  end x2.

(** The [xpair] optimization preserves meaning. *)
Lemma xpair_r_corr ta tb tc (x2:ta ->> tc) (x1:ta->>tb) v : 
  xinterp (xpair_r x2 x1) v = xinterp (Xpair x1 x2) v.
Proof.
  destruct x2 ; simpl in * ; auto. destruct v.
Qed.

Lemma xpair_corr ta tb tc (x1:ta->>tb) (x2:ta->>tc) v : 
  xinterp (xpair x1 x2) v = xinterp (Xpair x1 x2) v.
Proof.
  Ltac xpair_corr_simp := 
    match goal with | [ H : void |- _ ] => destruct H | _ => auto end.  
  destruct x1 ; simpl in * ; auto ; intros ; xpair_corr_simp ; 
  dependent destruction x2 ; simpl in * ; xpair_corr_simp.
  destruct v. auto.
Qed.

Definition xmatch_inl :forall t1 t2 tb tc (x2:tb->>tc),
  (tc=Sum_t t1 t2) -> Sum_t t1 tb ->> Sum_t t1 t2.
refine (fun t1 t2 tb tc x2 => 
  match x2 in tb->>tc return (tc=Sum_t t1 t2) -> Sum_t t1 tb ->> Sum_t t1 t2 with
    | Xinr t1' t2' => fun H => xcoerce Xid _ H
    | x2' => fun H => Xmatch Xinl (xcoerce x2' (eq_refl _) H)
  end
). injection H ; intros ; subst. auto.
Defined.

Definition xmatch_empty {tb t} (x2:tb->>t) : 
  forall {t1 t2}, (t = List_t t2) -> Sum_t t1 tb ->> List_t t2 := 
  match x2 in tb->>t return forall {t1 t2}, (t = List_t t2) -> Sum_t t1 tb ->> List_t t2
  with 
    | Xempty td te => fun t1 t2 H => Xempty
    | x2' => fun t1 t2 H => (Xmatch Xempty (xcoerce x2' eq_refl H))
  end.

(** This function and the two above implement the reduction
    [match x with inl a => inl a | inr b => inr b end = id]. *)
Definition xmatch ta tb tc (x1:ta->>tc) (x2:tb->>tc) : Sum_t ta tb ->> tc := 
  match x1 in ta->>tc return tb->>tc -> Sum_t ta tb ->> tc with
    | Xinl t1 t2 => fun x2' => xmatch_inl x2' (eq_refl _)
    | Xempty t1 t2 => fun x2' => xmatch_empty x2' (eq_refl _)
    | x1' => Xmatch x1'
  end x2.

(** Correctness of eta-reduction for sums. *)
Lemma xmatch_corr ta tb tc (x1:ta->>tc) (x2:tb->>tc) v : 
  xinterp (xmatch x1 x2) v = xinterp (Xmatch x1 x2) v.
Proof.
  destruct x1 ; simpl ; auto ; intros; dependent destruction x2 ; simpl ; destruct v ; 
  auto.
Qed.

(** These next few functions implement specific reductions for when a particular
    combinator is composed with another.  
*)
(** (f1, f2) o id = (f1, f2)
    (f1, f2) o (char c) = char c
    (f1, f2) o unit = unit
    (f1, f2) o empty = empty
    (f1, f2) o fst = f1
    (f1, f2) o snd = f2
    (f1, f2) o (g1, g2) = ((f1, f2) o g1, (f1, f2) o g2)
*)
Fixpoint xcomp_pair t21 t22 (x2:t21 ->> t22) : 
  forall ta tb tc (x11:ta->>tb) (x12:ta->>tc), (Pair_t tb tc = t21) -> ta ->> t22 := 
    match x2 in t21 ->> t22 return
      forall ta tb tc (x11:ta->>tb) (x12:ta->>tc), (Pair_t tb tc = t21) -> ta ->> t22 with
      | Xid t => fun ta tb tc x11 x12 H => xcoerce (Xpair x11 x12) (eq_refl _) H
      | Xchar t c => fun ta tb tc x11 x12 H => Xchar c
      | Xunit t => fun ta tb tc x11 x12 H => Xunit 
      | Xempty t1 t2 => fun ta tb tc x11 x12 H => Xempty 
      | Xfst te tf =>
        fun ta tb tc x11 x12 H => xcoerce x11 (eq_refl _) (eq_pair_fst (eq_sym H))
      | Xsnd te tf => 
        fun ta tb tc x11 x12 H => xcoerce x12 (eq_refl _) (eq_pair_snd (eq_sym H))
      | Xpair u1 u2 u3 x21 x22 => 
        fun ta tb tc x11 x12 H => 
          xpair (xcomp_pair x21 x11 x12 H) (xcomp_pair x22 x11 x12 H)
      | x2' => 
        fun ta tb tc x11 x12 H => 
          Xcomp (xpair x11 x12) (xcoerce x2' (eq_sym H) (eq_refl _))
    end.

(** [xcomp_pair] is correct. *)
Lemma xcomp_pair_corr : 
  forall t21 t22 (x2:t21->>t22) ta tb tc (x11:ta->>tb) (x12:ta->>tc) H v, 
  xinterp (xcomp_pair x2 x11 x12 H) v = 
  xinterp (Xcomp (Xpair x11 x12) (xcoerce x2 (eq_sym H) (eq_refl _))) v.
Proof.
  induction x2 ; simpl ; intros ; subst ; simpl ; auto ; try discriminate ; 
  try rewrite xpair_corr ; simpl ; auto. rewrite IHx2_1. rewrite IHx2_2.
  auto. injection H ; intros ; subst. rewrite (proof_irrelevance _ H (eq_refl _)).
  auto. injection H ; intros ; subst ; rewrite (proof_irrelevance _ H (eq_refl _)). auto.
Qed.

(**  inl o id = inl
     inl o (char c) = char c
     inl o unit = unit
     inl o empty = empty
     inl o (match f1 f2) = f1 
*)
Definition xcomp_inl t21 t22 (x2:t21 ->> t22) : 
  forall ta tb, (Sum_t ta tb = t21) -> ta ->> t22 :=
    match x2 in t21->>t22 return 
      forall ta tb, (Sum_t ta tb = t21) -> ta ->> t22 with
      | Xid t => fun ta tb H => xcoerce Xinl (eq_refl _) H 
      | Xchar t c => fun ta tb H => Xchar c
      | Xunit t => fun ta tb H => Xunit 
      | Xempty t1 t2 => fun ta tb H => Xempty 
      | Xmatch td te tf x21 x22 => 
        fun ta tb H => xcoerce x21 (eq_sum_fst H) (eq_refl _)
      | x2' => 
        fun ta tb H => Xcomp Xinl (xcoerce x2' (eq_sym H) (eq_refl _))
    end.

(** [xcomp_inl] is correct *)
Lemma xcomp_inl_corr t21 t22 (x2:t21->>t22) ta tb (H:Sum_t ta tb = t21) v: 
  xinterp (xcomp_inl x2 H) v = 
  xinterp (Xcomp Xinl (xcoerce x2 (eq_sym H) (eq_refl _))) v.
Proof.
  destruct x2 ; simpl ; intros ; subst ; simpl ; auto. injection H ; intros ; subst.
  rewrite (proof_irrelevance _ H (eq_refl _)). auto.
Qed.

(**  inr o id = inr f
     inr o (char c) = char c
     inr o unit = unit
     inr o empty = empty
     inr o (match f1 f2) = f2
*)
Definition xcomp_inr t21 t22 (x2:t21 ->> t22) : 
  forall ta tb, (Sum_t ta tb = t21) -> tb ->> t22 :=
    match x2 in t21->>t22 return 
      forall ta tb, (Sum_t ta tb = t21) -> tb ->> t22 with
      | Xid t => fun ta tb H => xcoerce Xinr (eq_refl _) H 
      | Xchar t c => fun ta tb H => Xchar c
      | Xunit t => fun ta tb H => Xunit 
      | Xempty t1 t2 => fun ta tb H => Xempty 
      | Xmatch td te tf x21 x22 => 
        fun ta tb H => xcoerce x22 (eq_sum_snd H) (eq_refl _)
      | x2' => 
        fun ta tb H => Xcomp Xinr (xcoerce x2' (eq_sym H) (eq_refl _))
    end.

(** [xcomp_inr] is correct. *)
Lemma xcomp_inr_corr t21 t22 (x2:t21->>t22) ta tb (H:Sum_t ta tb = t21) v: 
  xinterp (xcomp_inr x2 H) v = 
  xinterp (Xcomp Xinr (xcoerce x2 (eq_sym H) (eq_refl _))) v.
Proof.
  destruct x2 ; simpl ; intros ; subst ; simpl ; auto. injection H ; intros ; subst.
  rewrite (proof_irrelevance _ H (eq_refl _)). auto.
Qed.

(** empty o id = id
    empty o (char c) = char c
    empty o unit = unit
    empty o empty = empty
    empty o (map f) = empty
*)
Definition xcomp_empty t21 t22 (x2:t21 ->> t22) : 
  forall ta tb, (List_t tb = t21) -> ta ->> t22 := 
    match x2 in t21 ->> t22 return forall ta tb, (List_t tb = t21) -> ta ->> t22 with
      | Xid t => fun ta tb H => xcoerce Xempty (eq_refl _) H
      | Xchar t c => fun ta tb H => Xchar c
      | Xunit t => fun ta tb H => Xunit 
      | Xempty t1 t2 => fun ta tb H => Xempty
      | x2' => fun ta tb H => Xcomp Xempty (xcoerce x2' (eq_sym H) (eq_refl _))
    end.

(** [xcomp_empty] is correct. *)
Lemma xcomp_empty_corr t21 t22 (x2:t21->>t22) ta tb (H:List_t tb = t21) v : 
  xinterp (xcomp_empty x2 ta H) v = 
  xinterp (Xcomp Xempty (xcoerce x2 (eq_sym H) (eq_refl _))) v.
Proof.
  destruct x2 ; simpl ; intros ; subst ; simpl ; auto. 
Qed.

Definition xcons' t1 t (x2:t1->>t) : 
  forall t2, (t = List_t t2) -> (t1->>t2) -> (t1 ->> List_t t2) := 
  match x2 in t1->>t return forall t2, (t = List_t t2) -> (t1->>t2) -> (t1 ->> List_t t2)
  with
    | Xzero _ => fun t2 H x1 => Xzero 
    | x2' => fun t2 H x1 => Xcons x1 (xcoerce x2' eq_refl H)
  end.

Lemma xcons'_corr t1 t (x2:t1->>t) : 
  forall t2 (H:t=List_t t2) x1 v, 
    xinterp (xcons' x2 H x1) v = xinterp (Xcons x1 (xcoerce x2 eq_refl H)) v.
Proof.
  induction x2 ; intros ; auto. destruct v.
Qed.

Definition xcons t1 t2 (x1:t1->>t2) : (t1 ->> List_t t2) -> (t1 ->> List_t t2) := 
  match x1 in t1->>t2 return (t1 ->> List_t t2) -> (t1 ->> List_t t2) with
    | Xzero _ => fun _ => Xzero
    | x1' => fun x2 => xcons' x2 eq_refl x1'
  end.

Lemma xcons_corr t1 t2 (x1:t1->>t2) (x2:t1 ->> List_t t2) v : 
  xinterp (xcons x1 x2) v = xinterp (Xcons x1 x2) v.
Proof.
  induction x1 ; try apply xcons'_corr. destruct v.
Qed.

(** (cons f1 f2) o id = (cons f1 f2)
    (cons f1 f2) o (char c) = char c
    (cons f1 f2) o unit = unit
    (cons f1 f2) o empty = empty
    (cons f1 f2) o (map f) = cons (f1 o f) (f2 o (map f))
*)
Definition xcomp_cons t21 t22 (x2:t21 ->> t22) : 
  forall ta tb (x11:ta->>tb) (x12:ta->>List_t tb), (List_t tb = t21) -> ta ->> t22 := 
    match x2 in t21 ->> t22 return
      forall ta tb (x11:ta->>tb) (x12:ta->>List_t tb), (List_t tb = t21) -> ta ->> t22 with
      | Xid t => fun ta tb x11 x12 H => xcoerce (Xcons x11 x12) (eq_refl _) H
      | Xchar t c => fun ta tb x11 x12 H => Xchar c
      | Xunit t => fun ta tb x11 x12 H => Xunit 
      | Xempty tc td => fun ta tb x11 x12 H => Xempty
      | x2' => fun ta tb x11 x21 H => 
        Xcomp (xcons x11 x21) (xcoerce x2' (eq_sym H) (eq_refl _))
    end.

(** [xcomp_cons] is correct. *)
Lemma xcomp_cons_corr t21 t22 (x2:t21->>t22) ta tb (x11:ta->>tb) (x12:ta->>List_t tb) H v: 
  xinterp (xcomp_cons x2 x11 x12 H) v = xinterp (Xcomp (Xcons x11 x12) (xcoerce x2 (eq_sym H) (eq_refl _))) v.
Proof.
  destruct x2 ; simpl ; intros ; subst ; try rewrite xcons_corr ; simpl ; auto. 
Qed.

(** foldr f1 f2 zero => zero
      foldr f1 f2 empty => f1
      foldr f1 f2 (fhd::ftl) => (fhd, foldr f1 f2 ftl) ; f2
 *)
Fixpoint xfoldr' {t3 u} (x3:t3->>u) {struct x3} :
  forall {t1 t2}, (u = List_t t1) -> (Pair_t t1 t2 ->> t2) -> (t3 ->> t2) -> t3 ->> t2 := 
  match x3 in t3->>u return 
        forall {t1 t2}, (u = List_t t1) -> (Pair_t t1 t2 ->> t2) -> (t3 ->> t2) -> t3 ->> t2
  with 
    | Xempty ta tb => fun t1 t2 H x1 x2 => x2
    | Xcons ta tb x31 x32 => 
      fun t1 t2 H x1 x2 => 
        (Xcomp (xpair (xcoerce x31 eq_refl (list_t_eq (eq_sym H))) 
                            (xfoldr' x32 eq_refl 
                                     (xcoerce x1 (pair_eq_fst _ (list_t_eq H)) eq_refl) x2))
                     x1)
    | Xzero _ => fun t1 t2 H x1 x2 => Xzero 
    | Xmatch ta tb tc x31 x32 => 
      fun t1 t2 H x1 x2 => Xmatch (xfoldr' x31 H x1 (Xcomp Xinl x2)) 
                                  (xfoldr' x32 H x1 (Xcomp Xinr x2))
    (* still missing the "eta" rule for xfoldr *)                                          
    | x3' => fun t1 t2 H x1 x2 => Xfoldr x1 x2 (xcoerce x3' eq_refl H)
  end.

Lemma xfoldr'_corr t3 u (x3:t3->>u) : 
  forall t1 t2 (H:u=List_t t1) (x1:Pair_t t1 t2->>t2) (x2:t3->>t2) (v:interp t3),
    xinterp (xfoldr' x3 H x1 x2) v = 
    xinterp (Xfoldr x1 x2 (xcoerce x3 eq_refl H)) v.
Proof.
  induction x3 ; intros ; auto ; try (destruct v ; fail). injection H ; intros ; 
  subst ; rewrite (proof_irrelevance _ H eq_refl) ; auto.
  subst. simpl. fold interp. destruct v. rewrite IHx3_1. auto.
  rewrite IHx3_2 ; auto. injection H ; intros ; subst. 
  rewrite (proof_irrelevance _ H eq_refl). simpl. fold interp. 
  rewrite xpair_corr. simpl. rewrite IHx3_2. auto.
Qed.  

Definition xfoldr {t1 t2 t3} 
           (x1:Pair_t t1 t2 ->> t2)(x2:t3 ->> t2)(x3:t3 ->> List_t t1) : t3 ->> t2 :=
  xfoldr' x3 eq_refl x1 x2.

Lemma xfoldr_corr t1 t2 t3 (x1:Pair_t t1 t2 ->>t2)(x2:t3->>t2)(x3:t3->>List_t t1) v :
  xinterp (xfoldr x1 x2 x3) v = xinterp (Xfoldr x1 x2 x3) v.
Proof.
  unfold xfoldr ; rewrite xfoldr'_corr ; auto.
Qed.

(** Cut eliminations on the right here:
     f o id = f
     f o (char c) = char c
     f o unit = unit
     f o empty = empty
*)
Fixpoint xcomp_r t21 t22 (x2:t21 ->> t22) : forall t11, t11 ->> t21 -> t11 ->> t22 :=
  match x2 in t21 ->> t22 return forall t11, t11 ->> t21 -> t11 ->> t22 with
    | Xid t => fun t1 x1 => x1
    | Xchar t c => fun t1 x1 => Xchar c
    | Xunit t => fun t1 x1 => Xunit
    | Xempty t1 t2 => fun t1 x1 => Xempty
    | Xpair t t21 t22 x21 x22 => fun t1 x1 => xpair (xcomp_r x21 x1) (xcomp_r x22 x1)
    | Xcons t1 t2 x21 x22 => fun t1 x1 => xcons (xcomp_r x21 x1) (xcomp_r x22 x1)
    | Xfoldr t2 t3 t4 x21 x22 x23 => fun t1 x1 => xfoldr x21 (xcomp_r x22 x1) (xcomp_r x23 x1)
    | x2' => fun t1 x1 => Xcomp x1 x2'
  end.

(** [xcomp_r] is correct. *)
Lemma xcomp_r_corr t21 t22 (x2:t21->>t22) t11 (x1:t11->>t21) v : 
  xinterp (xcomp_r x2 x1) v = xinterp (Xcomp x1 x2) v.
Proof.
  induction x2 ; simpl ; intros ; auto. 
  rewrite xpair_corr. simpl. rewrite IHx2_1. rewrite IHx2_2. auto.
  rewrite xcons_corr. simpl. rewrite IHx2_1. rewrite IHx2_2. auto. 
  rewrite xfoldr_corr. simpl. fold interp. rewrite IHx2_2. rewrite IHx2_3. auto. 
Qed.

(** Optimization for composition of combinators, takes advantage
    of all of the specialized functions above, plus a few more:
     id o f = f
     zero o f = zero
     (f1 o f2) o f3 = f1 o (f2 o f3)
     (match f1 f2) o f3 = match (f1 o f3) (f2 o f3)
     plus the reductions in the functions above
*)
Fixpoint xcomp t11 t12 (x1:t11 ->> t12) : forall t22, t12 ->> t22 -> t11 ->> t22 := 
    match x1 in t11 ->> t12 return forall t22, t12 ->> t22 -> t11 ->> t22 with
      | Xid _ => fun t22 x2 => x2
      | Xzero _ => fun t22 x2 => Xzero
      | Xcomp ta tb tc x11 x12 => 
        fun t22 x2 => xcomp x11 (xcomp x12 x2)
      | Xpair ta tb tc x11 x12 => 
        fun t22 x2 => xcomp_pair x2 x11 x12 (eq_refl _)
      | Xinl ta tb => fun t22 x2 => xcomp_inl x2 (eq_refl _)
      | Xinr ta tb => fun t22 x2 => xcomp_inr x2 (eq_refl _)
      | Xempty ta tb => fun t22 x2 => xcomp_empty x2 _ (eq_refl _)
      | Xcons ta tb x11 x12 => fun t22 x2 => xcomp_cons x2 x11 x12 (eq_refl _)
      | Xmatch ta tb tc x11 x12 => fun t22 x2 => xmatch (xcomp x11 x2) (xcomp x12 x2)
      | x1' => fun t22 x2 => xcomp_r x2 x1'
    end.

(** [xcomp] is correct. *)
Lemma xcomp_corr t1 t2 (x1:t1->>t2) t3 (x2:t2->>t3) v : 
  xinterp (xcomp x1 x2) v = xinterp (Xcomp x1 x2) v.
Proof.
  induction x1 ; simpl in * ; intros ; auto ; 
  match goal with 
    | [ v : void |- _ ] => destruct v
    | [ |- xinterp (xcomp_r ?x2 ?x1) ?v = _ ] => apply (xcomp_r_corr x2 x1 v)
    | _ => idtac
  end.
  rewrite <- IHx1_2. rewrite <- IHx1_1. auto.
  apply xcomp_empty_corr. apply xcomp_pair_corr.  apply xcomp_inl_corr.
  apply xcomp_inr_corr. destruct v ; auto. rewrite xmatch_corr ; simpl ; auto.
  rewrite xmatch_corr ; simpl ; auto.
  apply xcomp_cons_corr. 
Qed.

(** The [xcomp'] function is an extra loop to try to get more reductions
    to fire. *)
Fixpoint xcomp' tb tc (x2:tb->>tc) : forall ta, ta->>tb -> ta->>tc := 
  match x2 in tb->>tc return forall ta, ta->>tb -> ta->>tc with 
    | Xcomp td te tf x21 x22 => fun ta x1 => xcomp' x22 (xcomp' x21 x1)
    | Xpair td te tf x21 x22 => fun ta x1 => xpair (xcomp' x21 x1) (xcomp' x22 x1)
    | Xcons td te x21 x22 => fun ta x1 => xcons (xcomp' x21 x1) (xcomp' x22 x1)
    | Xfoldr td te tf x21 x22 x23 => fun ta x1 => xfoldr x21 (xcomp' x22 x1) (xcomp' x23 x1)
    | x2' => fun ta x1 => xcomp x1 x2'
  end.

Lemma xcomp'_corr tb tc (x2:tb->>tc) ta (x1:ta->>tb) v : 
  xinterp (xcomp' x2 x1) v = xinterp (Xcomp x1 x2) v.
Proof.
  induction x2 ; simpl ; intros ; auto ; try (rewrite xcomp_corr ; auto).
  rewrite IHx2_2. simpl. rewrite IHx2_1. auto. rewrite xpair_corr. simpl.
  rewrite IHx2_1. rewrite IHx2_2. auto. rewrite xcons_corr ; simpl ; 
  rewrite IHx2_1 ; rewrite IHx2_2 ; auto. 
  rewrite xfoldr_corr. simpl. rewrite IHx2_2. rewrite IHx2_3. auto.
Qed.

(** Optimize an [xform].  Most of the reductions are in the
    [Xcomp] (composition) case, though there are a couple of
    eta reductions for [Xpair] and [Xmatch] respectively. *)
Fixpoint xopt t1 t2 (x:t1 ->> t2) : t1 ->> t2 := 
  match x with
    | Xpair ta tb tc x1 x2 => xpair (xopt x1) (xopt x2)
    | Xmatch ta tb tc x1 x2 => xmatch (xopt x1) (xopt x2)
    | Xcomp ta tb tc x1 x2 => xcomp' (xopt x2) (xopt x1) 
    | Xcons ta tb x1 x2 => xcons (xopt x1) (xopt x2)
    | Xfoldr ta tb tc x1 x2 x3 => xfoldr (xopt x1) (xopt x2) (xopt x3)
    | x' => x'
  end.

(** [xopt] is correct. *)
Lemma xopt_corr t1 t2 (x:t1 ->> t2) : xinterp (xopt x) = xinterp x.
Proof.
  induction x ; simpl ; intros ; auto ; try (rewrite <- IHx ; auto) ; 
    try (rewrite <- IHx1 ; rewrite <- IHx2 ; auto) ; apply extensionality ; intros.
  apply xcomp'_corr. apply xpair_corr. apply xmatch_corr. apply xcons_corr.
  rewrite <- IHx3 ; apply xfoldr_corr. 
Qed.

(** Derived Transforms *)

(** Map a transform over a list. *)
Definition xmap {t1 t2} (f:t1 ->> t2) : List_t t1 ->> List_t t2 := 
  xopt (xfoldr (xcons (xcomp xfst f) xsnd) xempty xid).

Lemma xmap_corr t1 t2 (f:t1 ->> t2) (vs:interp (List_t t1)) : 
  xinterp (xmap f) = List.map (xinterp f).
Proof.
  eapply extensionality. intro x. unfold xmap. rewrite xopt_corr.
  induction x. auto. simpl. rewrite xcons_corr. simpl. rewrite xcomp_r_corr. simpl.
  rewrite <- IHx. auto.
Qed.

(** Append a pair of lists. *)
Definition xapp {t} : Pair_t (List_t t) (List_t t) ->> List_t t := 
  xopt (xfoldr (xcons xfst xsnd) xsnd xfst).

Lemma xapp_corr t (vs1 vs2: interp (List_t t)) : 
  xinterp xapp (vs1,vs2) = vs1 ++ vs2.
Proof.
  unfold xapp. rewrite xopt_corr.
  induction vs1. simpl. auto. simpl. rewrite <- IHvs1. auto.
Qed. 

(** Similar to Map but draws from the environment. *)
Definition xmapenv {t1 t2 t3} (f:Pair_t t1 t2 ->> t3) : Pair_t t1 (List_t t2)->>List_t t3 :=
  xopt (xcomp (xfoldr (xpair (xcomp xsnd xfst) 
                       (xcons (xcomp (xpair (xcomp xsnd xfst) xfst) f) 
                              (xcomp xsnd xsnd))) (xpair xfst xempty) xsnd) xsnd).

Lemma xmapenv_corr {t1 t2 t3} (f:Pair_t t1 t2->>t3) v : 
  xinterp (xmapenv f) v = List.map (fun x => xinterp f (fst v,x)) (snd v).
Proof.
  assert (xinterp (xmapenv f) v = 
          xinterp (Xcomp (Xfoldr (Xpair (Xcomp Xsnd Xfst)
                                        (Xcons (Xcomp (xpair (Xcomp Xsnd Xfst) Xfst) f)
                                               (Xcomp Xsnd Xsnd))) (Xpair Xfst Xempty) Xsnd)
                         Xsnd) v).
  unfold xmapenv. rewrite xopt_corr. rewrite xcomp_corr. 
  replace (xinterp
     (Xcomp
        (xfoldr
           (xpair (xcomp xsnd xfst)
              (xcons (xcomp (xpair (xcomp xsnd xfst) xfst) f)
                 (xcomp xsnd xsnd))) (xpair xfst xempty) xsnd) xsnd) v) with
  (snd ((xinterp (xfoldr (xpair (xcomp xsnd xfst)
              (xcons (xcomp (xpair (xcomp xsnd xfst) xfst) f)
                 (xcomp xsnd xsnd))) (xpair xfst xempty) xsnd) v))) ; auto.
  rewrite xfoldr_corr. 
  replace (xinterp
        (Xfoldr
           (xpair (xcomp xsnd xfst)
              (xcons (xcomp (xpair (xcomp xsnd xfst) xfst) f)
                 (xcomp xsnd xsnd))) (xpair xfst xempty) xsnd) v) with
  (List.fold_right 
     (fun a b => 
     (xinterp (xpair (xcomp xsnd xfst)
              (xcons (xcomp (xpair (xcomp xsnd xfst) xfst) f)
                 (xcomp xsnd xsnd)))) (a,b))
                   (xinterp (xpair xfst xempty) v) (xinterp xsnd v)) ; 
  auto ; fold interp. 
  rewrite xpair_corr. unfold xsnd, xfst.
  replace  (fun (a : interp t2) (b : interp t1 * list (interp t3)) =>
         xinterp
           (xpair (xcomp Xsnd Xfst)
              (xcons (xcomp (xpair (xcomp Xsnd Xfst) Xfst) f)
                 (xcomp Xsnd Xsnd))) (a, b))
  with (fun a b => 
          xinterp
           (Xpair (Xcomp Xsnd Xfst)
              (Xcons (Xcomp (Xpair (Xcomp Xsnd Xfst) Xfst) f)
                 (Xcomp Xsnd Xsnd))) (a, b)) ; fold interp.
  Focus 2. eapply extensionality. intro. eapply extensionality. intro.
  simpl. rewrite xpair_r_corr. simpl. rewrite xcons_corr. simpl. 
  rewrite xcomp_pair_corr. simpl. auto. auto.
  rewrite H. clear H. fold interp.
  destruct v. induction i0. auto.
  simpl in *. fold interp in *. rewrite IHi0.
  replace (fst
        (fold_right
           (fun (a0 : interp t2) (b : interp t1 * list (interp t3)) =>
            (fst b, xinterp f (fst b, a0) :: snd b)) 
           (i, nil) i0)) with i ; auto.
  clear IHi0. induction i0 ; auto.
Qed.

(** Flatten a list of lists. *)
Definition xflatten {t} : List_t (List_t t) ->> List_t t := 
  xopt (xfoldr xapp xempty xid).

Lemma xflatten_corr {t} (vs : interp (List_t (List_t t))) : 
  xinterp xflatten vs = 
  List.fold_right (fun a b => List.fold_right (fun x y => x::y) b a) nil vs.
Proof.
  unfold xflatten. rewrite xopt_corr.
  induction vs ; simpl ; fold interp in *; auto. 
Qed.

(** Compute the cross product of two lists.  For instance, the
      cross product of (1::2::nil, true::false::nil) is 
      (1,true)::(1,false)::(2,true)::(2,false)::nil.
 *)
Definition xcross {t1 t2} : Pair_t (List_t t1) (List_t t2) ->> List_t (Pair_t t1 t2) := 
  xopt (xcomp (xmapenv (xcomp (xpair xsnd xfst) (xmapenv (xpair xsnd xfst)))) xflatten).

(** Lift a continuation to work on a list of values, and then
      concatenate all of the results. *)
Definition xthen {t1 t2 t3} (f1: t1 ->> List_t t2) (f2: t2 ->> List_t t3) : 
  t1 ->> List_t t3 := 
  xopt (xcomp f1 (xcomp (xmap f2) xflatten)).

(** Like cross product, but parameterized by generators [f1] and [f2]. *)
Definition xcrossmap {t1 t2 t3 t4} (f1 : t1 ->> List_t t3) (f2 : t2 ->> List_t t4) : 
  (Pair_t t1 t2) ->> List_t (Pair_t t3 t4) := 
  xopt (xcomp (xpair (xcomp xfst f1) (xcomp xsnd f2)) xcross).

(** Some utilities for viewing and seeing the size of Xforms. *)

Require Import String.
Open Scope string_scope.
Definition emit (s:string) (a:list string) : list string := s :: a.
Definition seq {A} (c1 c2:A -> A)(a:A): A := 
  c2 (c1 a).
Notation "c1 ;; c2" := (seq c1 c2) (right associativity, at level 84).

Fixpoint show_xform' t1 t2 (x:t1->>t2) : list string -> list string := 
  match x with
    | Xid _ => emit "id"
    | Xzero _ => emit "Z"
    | Xcomp _ _ _ x1 x2 => 
      emit "(" ;; (show_xform' x1) ;; emit ";" ;; (show_xform' x2) ;; emit ")"
    | Xchar _ c => emit (show_char c)
    | Xunit _ => emit "U" 
    | Xempty _ _ => emit "[]"
    | Xpair _ _ _ x1 x2 => 
      emit "(" ;; (show_xform' x1) ;; emit "," ;; (show_xform' x2) ;; emit ")"
    | Xfst _ _ => emit "fst"
    | Xsnd _ _ => emit "snd"
    | Xinl _ _ => emit "inl"
    | Xinr _ _ => emit "inr"
    | Xmatch _ _ _  x1 x2 =>
      emit "[" ;; (show_xform' x1) ;; emit "|" ;; (show_xform' x2) ;; emit "]"
    | Xcons _ _ x1 x2 => 
      emit "(" ;; (show_xform' x1) ;; emit "::" ;; (show_xform' x2) ;; emit ")"
    | Xfoldr _ _ _ x1 x2 x3 => 
      emit "fold(" ;; (show_xform' x1) ;; emit "," ;; (show_xform' x2) ;; 
           emit "," ;; (show_xform' x3) ;; emit ")"
  end.

Definition show_xform t1 t2 (x:t1->>t2) : string := 
  let ss := List.rev (show_xform' x nil) in 
  List.fold_right (fun x y => x ++ y) "" ss.

Definition inc (n:nat) : nat := plus 1 n.

Fixpoint xform_count' t1 t2 (x:t1->>t2) : nat->nat := 
  match x with 
    | Xid _ => inc
    | Xzero _ => inc
    | Xcomp _ _ _ x1 x2 => inc ;; (xform_count' x1) ;; (xform_count' x2)
    | Xchar _ true => inc
    | Xchar _ false => inc
    | Xunit _ => inc
    | Xempty _ _ => inc
    | Xpair _ _ _ x1 x2 => inc ;; (xform_count' x1) ;; (xform_count' x2)
    | Xfst _ _ => inc
    | Xsnd _ _ => inc
    | Xinl _ _ => inc
    | Xinr _ _ => inc
    | Xmatch _ _ _ x1 x2 => inc ;; (xform_count' x1) ;; (xform_count' x2)
    | Xcons _ _ x1 x2 => inc ;; (xform_count' x1) ;; (xform_count' x2)
    | Xfoldr _ _ _ x1 x2 x3 => 
      inc ;; (xform_count' x1) ;; (xform_count' x2) ;; (xform_count' x3)
  end.

Definition xform_count t1 t2 (x:t1->>t2) : nat := xform_count' x 0.
