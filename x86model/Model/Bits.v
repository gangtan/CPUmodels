(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Formalizations of integers modulo $2^32$ #2<sup>32</sup>#. *)

(* JGM: modified once again to get rid of the module issue. *)
(* JGM: modified to abstract over the wordsize. *)
(* JDT: fixed the proofs so they work with abstract wordsize.
        note that rol_rol and rolm_rolm did not generalize to
        completely abstract wordsize. They still hold if wordsize
        is a power of two or if the arguments they take are small enough
        these weakened theorems are given as rol_rol_weak and 
        rol_rol_weak_2 (and similarly for rolm_rolm).  *) 
        


Require Import Coqlib.

Module Word.
  Section WORDSIZE.
  Variable wordsize_minus_one : nat.

  Definition wordsize : nat := S wordsize_minus_one.
(* Definition wordsize : nat := 32%nat. *)
Definition modulus : Z := two_power_nat wordsize.
Definition half_modulus : Z := modulus / 2.

(** * Comparisons *)

Inductive comparison : Type :=
  | Ceq : comparison               (**r same *)
  | Cne : comparison               (**r different *)
  | Clt : comparison               (**r less than *)
  | Cle : comparison               (**r less than or equal *)
  | Cgt : comparison               (**r greater than *)
  | Cge : comparison.              (**r greater than or equal *)

Definition negate_comparison (c: comparison): comparison :=
  match c with
  | Ceq => Cne
  | Cne => Ceq
  | Clt => Cge
  | Cle => Cgt
  | Cgt => Cle
  | Cge => Clt
  end.

Definition swap_comparison (c: comparison): comparison :=
  match c with
  | Ceq => Ceq
  | Cne => Cne
  | Clt => Cgt
  | Cle => Cge
  | Cgt => Clt
  | Cge => Cle
  end.

(** * Representation of machine integers *)

(** A machine integer (type [int]) is represented as a Coq arbitrary-precision
  integer (type [Z]) plus a proof that it is in the range 0 (included) to
  [modulus] (excluded. *)

Record int: Type := mkint { intval: Z; intrange: 0 <= intval < modulus }.
Implicit Arguments mkint [].

Definition max_unsigned : Z := modulus - 1.
Definition max_signed : Z := half_modulus - 1.
Definition min_signed : Z := - half_modulus.

(** The [unsigned] and [signed] functions return the Coq integer corresponding
  to the given machine integer, interpreted as unsigned or signed 
  respectively. *)

Definition unsigned (n: int) : Z := intval n.

Definition signed (n: int) : Z :=
  if zlt (unsigned n) half_modulus
  then unsigned n
  else unsigned n - modulus.

Lemma mod_in_range:
  forall x, 0 <= Zmod x modulus < modulus.
Proof.
  intro.
  exact (Z_mod_lt x modulus (two_power_nat_pos wordsize)).
Qed.

(** Conversely, [repr] takes a Coq integer and returns the corresponding
  machine integer.  The argument is treated modulo [modulus]. *)

Definition repr (x: Z) : int := 
  mkint (Zmod x modulus) (mod_in_range x).

Definition zero := repr 0.
Definition one  := repr 1.
Definition mone := repr (-1).

Lemma mkint_eq:
  forall x y Px Py, x = y -> mkint x Px = mkint y Py.
Proof.
  intros. subst y. 
  generalize (proof_irrelevance _ Px Py); intro.
  subst Py. reflexivity.
Qed.

Lemma eq_dec: forall (x y: int), {x = y} + {x <> y}.
Proof.
  intros. destruct x; destruct y. case (zeq intval0 intval1); intro.
  left. apply mkint_eq. auto.
  right. red; intro. injection H. exact n.
Qed.

(** * Arithmetic and logical operations over machine integers *)

Definition eq (x y: int) : bool := 
  if zeq (unsigned x) (unsigned y) then true else false.
Definition lt (x y: int) : bool :=
  if zlt (signed x) (signed y) then true else false.
Definition ltu (x y: int) : bool :=
  if zlt (unsigned x) (unsigned y) then true else false.
Definition lequ (x y : int) :  bool :=
  orb (ltu x y) (eq x y).

Definition neg (x: int) : int := repr (- unsigned x).

Definition zero_ext (n: Z) (x: int) : int :=
  repr (Zmod (unsigned x) (two_p n)).
Definition sign_ext (n: Z) (x: int) : int :=
  repr (let p := two_p n in
        let y := Zmod (unsigned x) p in
        if zlt y (two_p (n-1)) then y else y - p).

Definition add (x y: int) : int :=
  repr (unsigned x + unsigned y).
Definition sub (x y: int) : int :=
  repr (unsigned x - unsigned y).
Definition mul (x y: int) : int :=
  repr (unsigned x * unsigned y).

Definition Zdiv_round (x y: Z) : Z :=
  if zlt x 0 then
    if zlt y 0 then (-x) / (-y) else - ((-x) / y)
  else
    if zlt y 0 then -(x / (-y)) else x / y.

Definition Zmod_round (x y: Z) : Z :=
  x - (Zdiv_round x y) * y.

Definition divs (x y: int) : int :=
  repr (Zdiv_round (signed x) (signed y)).
Definition mods (x y: int) : int :=
  repr (Zmod_round (signed x) (signed y)).
Definition divu (x y: int) : int :=
  repr (unsigned x / unsigned y).
Definition modu (x y: int) : int :=
  repr (Zmod (unsigned x) (unsigned y)).

Definition bool_to_int (b : bool) :=
  match b with 
    | true => one
    | false => zero
  end.

Definition unsigned_overflow(o1 o2: Z) :=
 let res := o1 + o2 in 
 if Coqlib.zlt res modulus then 
   false
 else
   true.

Definition unsigned_overflow_with_carry(o1 o2: Z)(carry: bool) :=
 let c := bool_to_int(carry) in
 let res := o1 +  o2 + unsigned c in 
 if zle res max_unsigned then 
   false
 else
   true.

Definition signed_overflow (o1 o2: Z) :=
let res := o1 + o2 in
if (andb (zle res max_signed) (zle min_signed res)) then
  false
else
  true.

Definition signed_overflow_with_carry (o1 o2: Z)(carry: bool) :=
let c := bool_to_int(carry) in
let res := o1 + o2 + signed c in
if (andb (zle res max_signed) (zle min_signed res)) then
  false
else
  true.

Definition signed_overflow_with_borrow (o1 o2: Z)(borrow: bool) :=
let b := bool_to_int(borrow) in
let res := o1 + o2 - signed b in
if (andb (zle res max_signed) (zle min_signed res)) then
  false
else
  true.

Definition is_zero (i: int) : bool := eq i zero.
Definition is_signed (i: int) : bool := lt i zero.

(** For bitwise operations, we need to convert between Coq integers [Z]
  and their bit-level representations.  Bit-level representations are
  represented as characteristic functions, that is, functions [f]
  of type [nat -> bool] such that [f i] is the value of the [i]-th bit
  of the number.  The values of characteristic functions for [i] greater
  than 32 are ignored. *)

Definition Z_shift_add (b: bool) (x: Z) :=
  if b then 2 * x + 1 else 2 * x.

Definition Z_bin_decomp (x: Z) : bool * Z :=
  match x with
  | Z0 => (false, 0)
  | Zpos p =>
      match p with
      | xI q => (true, Zpos q)
      | xO q => (false, Zpos q)
      | xH => (true, 0)
      end
  | Zneg p =>
      match p with
      | xI q => (true, Zneg q - 1)
      | xO q => (false, Zneg q)
      | xH => (true, -1)
      end
  end.

Fixpoint bits_of_Z (n: nat) (x: Z) {struct n}: Z -> bool :=
  match n with
  | O =>
      (fun i: Z => false)
  | S m =>
      let (b, y) := Z_bin_decomp x in
      let f := bits_of_Z m y in
      (fun i: Z => if zeq i 0 then b else f (i - 1))
  end.

Fixpoint Z_of_bits (n: nat) (f: Z -> bool) {struct n}: Z :=
  match n with
  | O => 0
  | S m => Z_shift_add (f 0) (Z_of_bits m (fun i => f (i + 1)))
  end.

(** Bitwise logical ``and'', ``or'' and ``xor'' operations. *)

Definition bitwise_binop (f: bool -> bool -> bool) (x y: int) :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let fy := bits_of_Z wordsize (unsigned y) in
  repr (Z_of_bits wordsize (fun i => f (fx i) (fy i))).

Definition and (x y: int): int := bitwise_binop andb x y.
Definition or (x y: int): int := bitwise_binop orb x y.
Definition xor (x y: int) : int := bitwise_binop xorb x y.

Definition not (x: int) : int := xor x mone.

(** Shifts and rotates. *)

Definition shl (x y: int): int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let vy := unsigned y in
  repr (Z_of_bits wordsize (fun i => fx (i - vy))).

Definition shru (x y: int): int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let vy := unsigned y in
  repr (Z_of_bits wordsize (fun i => fx (i + vy))).

(** Arithmetic right shift is defined as signed division by a power of two.
  Two such shifts are defined: [shr] rounds towards minus infinity
  (standard behaviour for arithmetic right shift) and
  [shrx] rounds towards zero. *)

Definition shr (x y: int): int :=
  repr (signed x / two_p (unsigned y)).

Definition shrx (x y: int): int :=
  divs x (shl one y).

Definition shr_carry (x y: int) :=
  sub (shrx x y) (shr x y).

Definition rol (x y: int) : int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let vy := unsigned y in
  repr (Z_of_bits wordsize
         (fun i => fx (Zmod (i - vy) (Z_of_nat wordsize)))).

Definition ror (x y: int) : int :=
  let fx := bits_of_Z wordsize (unsigned x) in
  let vy := unsigned y in
  repr (Z_of_bits wordsize
         (fun i => fx (Zmod (i + vy) (Z_of_nat wordsize)))).

Definition rolm (x a m: int): int := and (rol x a) m.

(** Decomposition of a number as a sum of powers of two. *)

Fixpoint Z_one_bits (n: nat) (x: Z) (i: Z) {struct n}: list Z :=
  match n with
  | O => nil
  | S m =>
      let (b, y) := Z_bin_decomp x in
      if b then i :: Z_one_bits m y (i+1) else Z_one_bits m y (i+1)
  end.

Definition one_bits (x: int) : list int :=
  List.map repr (Z_one_bits wordsize (unsigned x) 0).

(** Recognition of powers of two. *)

Definition is_power2 (x: int) : option int :=
  match Z_one_bits wordsize (unsigned x) 0 with
  | i :: nil => Some (repr i)
  | _ => None
  end.

(** Recognition of integers that are acceptable as immediate operands
  to the [rlwim] PowerPC instruction.  These integers are of the form
  [000011110000] or [111100001111], that is, a run of one bits
  surrounded by zero bits, or conversely.  We recognize these integers by
  running the following automaton on the bits.  The accepting states are
  2, 3, 4, 5, and 6.
<<
               0          1          0
              / \        / \        / \
              \ /        \ /        \ /
        -0--> [1] --1--> [2] --0--> [3]
       /     
     [0]
       \
        -1--> [4] --0--> [5] --1--> [6]
              / \        / \        / \
              \ /        \ /        \ /
               1          0          1
>>
*)

Inductive rlw_state: Type :=
  | RLW_S0 : rlw_state
  | RLW_S1 : rlw_state
  | RLW_S2 : rlw_state
  | RLW_S3 : rlw_state
  | RLW_S4 : rlw_state
  | RLW_S5 : rlw_state
  | RLW_S6 : rlw_state
  | RLW_Sbad : rlw_state.

Definition rlw_transition (s: rlw_state) (b: bool) : rlw_state :=
  match s, b with
  | RLW_S0, false => RLW_S1
  | RLW_S0, true  => RLW_S4
  | RLW_S1, false => RLW_S1
  | RLW_S1, true  => RLW_S2
  | RLW_S2, false => RLW_S3
  | RLW_S2, true  => RLW_S2
  | RLW_S3, false => RLW_S3
  | RLW_S3, true  => RLW_Sbad
  | RLW_S4, false => RLW_S5
  | RLW_S4, true  => RLW_S4
  | RLW_S5, false => RLW_S5
  | RLW_S5, true  => RLW_S6
  | RLW_S6, false => RLW_Sbad
  | RLW_S6, true  => RLW_S6
  | RLW_Sbad, _ => RLW_Sbad
  end.

Definition rlw_accepting (s: rlw_state) : bool :=
  match s with
  | RLW_S0 => false
  | RLW_S1 => false
  | RLW_S2 => true
  | RLW_S3 => true
  | RLW_S4 => true
  | RLW_S5 => true
  | RLW_S6 => true
  | RLW_Sbad => false
  end.

Fixpoint is_rlw_mask_rec (n: nat) (s: rlw_state) (x: Z) {struct n} : bool :=
  match n with
  | O =>
      rlw_accepting s
  | S m =>
      let (b, y) := Z_bin_decomp x in
      is_rlw_mask_rec m (rlw_transition s b) y
  end.

Definition is_rlw_mask (x: int) : bool :=
  is_rlw_mask_rec wordsize RLW_S0 (unsigned x).

(** Comparisons. *)

Definition cmp (c: comparison) (x y: int) : bool :=
  match c with
  | Ceq => eq x y
  | Cne => negb (eq x y)
  | Clt => lt x y
  | Cle => negb (lt y x)
  | Cgt => lt y x
  | Cge => negb (lt x y)
  end.

Definition cmpu (c: comparison) (x y: int) : bool :=
  match c with
  | Ceq => eq x y
  | Cne => negb (eq x y)
  | Clt => ltu x y
  | Cle => negb (ltu y x)
  | Cgt => ltu y x
  | Cge => negb (ltu x y)
  end.

Definition is_false (x: int) : Prop := x = zero.
Definition is_true  (x: int) : Prop := x <> zero.
Definition notbool  (x: int) : int  := if eq x zero then one else zero.

(** * Properties of integers and integer arithmetic *)

(** ** Properties of equality *)

Lemma one_is_1: (1 mod modulus = 1).
    unfold Zmod in |- *.  unfold modulus. unfold wordsize. 
    auto with *.  auto. induction wordsize_minus_one. compute. auto.  auto with *. 
Qed.

Theorem one_not_zero: one <> zero.
Proof.
  intros. unfold one, zero, repr. 
  assert (0 mod modulus = 0). auto with *. 
  assert (1 mod modulus = 1). apply one_is_1. congruence.
Qed.


Theorem int_eq_sym:
  forall x y, eq x y = eq y x.
Proof.
  intros; unfold eq. case (zeq (unsigned x) (unsigned y)); intro.
  rewrite e. rewrite zeq_true. auto.
  rewrite zeq_false. auto. auto.
Qed.

Theorem eq_spec: forall (x y: int), if eq x y then x = y else x <> y.
Proof.
  intros; unfold eq. case (eq_dec x y); intro.
  subst y. rewrite zeq_true. auto.
  rewrite zeq_false. auto. 
  destruct x; destruct y.
  simpl. red; intro. elim n. apply mkint_eq. auto.
Qed.

Theorem int_eq_refl: forall x, eq x x = true.
Proof.
  intros. generalize (eq_spec x x); case (eq x x); intros; congruence.
Qed.

Theorem eq_false: forall x y, x <> y -> eq x y = false.
Proof.
  intros. generalize (eq_spec x y); case (eq x y); intros; congruence.
Qed.

Lemma int_eq_inv : forall x y, eq x y = true -> unsigned x = unsigned y.
Proof. unfold eq; intros. 
  destruct (zeq (unsigned x) (unsigned y)); [trivial|discriminate].
Qed.

Lemma unsigned_eq_eq :
  forall i1 i2, unsigned i1 = unsigned i2 -> i1 = i2.
Proof. intros. destruct i1; destruct i2. simpl in H.
  apply mkint_eq. trivial.
Qed.

Theorem unsigned_range:
  forall i, 0 <= unsigned i < modulus.
Proof.
  destruct i; simpl. auto.
Qed.
Hint Resolve unsigned_range: ints.

Theorem unsigned_range_2:
  forall i, 0 <= unsigned i <= max_unsigned.
Proof.
  intro; unfold max_unsigned. 
  generalize (unsigned_range i). omega.
Qed.
Hint Resolve unsigned_range_2: ints.

Lemma int_eq_true_iff2 :
  forall i1 i2, eq i1 i2 = true <-> i1 = i2.
Proof. intros; split.
  intro H. generalize (eq_spec i1 i2). rewrite H. trivial.
  intro H. rewrite H. apply int_eq_refl. 
Qed.

Lemma int_eq_true_iff :
  forall i1 i2, eq i1 i2 = true <-> unsigned i1 = unsigned i2.
Proof. intros; split. 
  intro H. apply int_eq_true_iff2 in H. rewrite H; trivial.
  intro H. unfold eq. rewrite H. apply Coqlib.zeq_true.
Qed.

Lemma int_eq_unsigned :
  forall i1 i2, i1 = i2 <-> unsigned i1 = unsigned i2.
Proof. intros; split. congruence.
  intro. apply int_eq_true_iff2. apply int_eq_true_iff. trivial.
Qed.

Lemma int_eq_false_iff2 :
  forall i1 i2, eq i1 i2 = false <-> i1 <> i2.
Proof. intros; split.
  intro H. intro Hc. apply int_eq_true_iff2 in Hc. 
    rewrite Hc in H. discriminate.
  intro H. remember (eq i1 i2) as e.
    destruct e. apply eq_sym in Heqe.
    generalize (eq_spec i1 i2). rewrite Heqe. congruence.
    trivial.
Qed.

Lemma int_eq_false_iff :
  forall i1 i2, eq i1 i2 = false <-> unsigned i1 <> unsigned i2.
Proof. intros; split.
  intro H. intro Hc. apply int_eq_false_iff2 in H. 
    apply unsigned_eq_eq in Hc. contradiction.
  intro H. apply int_eq_false_iff2. congruence.
Qed.

(** ** Properties of ordering *)
Lemma int_lt_inv : 
  forall i1 i2, lt i1 i2 = true -> signed i1 < signed i2.
Proof. unfold lt; intros.
  destruct (zlt (signed i1) (signed i2)). trivial. discriminate.
Qed.

Lemma int_ltu_inv:
  forall x y, ltu x y = true -> 0 <= unsigned x < unsigned y.
Proof.
  unfold ltu; intros. destruct (zlt (unsigned x) (unsigned y)).
  split; auto. generalize (unsigned_range x); omega.
  discriminate.
Qed.

Lemma int_ltu_true_iff :
  forall i1 i2, ltu i1 i2 = true <-> (unsigned i1 < unsigned i2)%Z.
Proof. intros. split. apply int_ltu_inv.
  intro H. unfold ltu. 
    destruct (zlt (unsigned i1) (unsigned i2)). trivial. 
    Coqlib.omegaContradiction.
Qed.

Lemma int_ltu_false_iff :
  forall i1 i2, ltu i1 i2 = false <-> (unsigned i1 >= unsigned i2)%Z.
Proof. intros. 
  split; unfold ltu; destruct (Coqlib.zlt (unsigned i1) (unsigned i2)); 
    congruence.
Qed.

Lemma int_lt_trans : 
  forall (i1 i2 i3:int), lt i1 i2 = true -> lt i2 i3 = true -> lt i1 i3 = true.
Proof. unfold lt. intros i1 i2 i3 H1 H2.
  apply int_lt_inv in H1. apply int_lt_inv in H2.
  apply zlt_true.
  apply Zlt_trans with (m:=signed i2); trivial.
Qed.

Lemma int_ltu_trans : 
  forall (i1 i2 i3:int), 
    ltu i1 i2 = true -> ltu i2 i3 = true -> ltu i1 i3 = true.
Proof. unfold ltu. intros i1 i2 i3 H1 H2.
  apply int_ltu_inv in H1. apply int_ltu_inv in H2.
  apply zlt_true. omega.
Qed.

Lemma int_eq_ltu_trans :
  forall (i1 i2 i3:int), 
    eq i1 i2 = true -> ltu i2 i3 = true -> ltu i1 i3 = true.
Proof. intros i1 i2 i3 H1 H2. 
  apply int_eq_inv in H1. apply int_ltu_inv in H2. apply zlt_true. omega.
Qed.

Lemma int_lequ_true_iff :
  forall i1 i2, lequ i1 i2 = true <-> unsigned i1 <= unsigned i2.
Proof. unfold lequ. intros; split; intros.
  destruct (Bool.orb_true_elim _ _ H).
    cut (unsigned i1 < unsigned i2). omega. apply (int_ltu_true_iff). trivial.
    cut (unsigned i1 = unsigned i2). omega. apply (int_eq_true_iff). trivial.
  apply Zle_lt_or_eq in H. destruct H.
    apply int_ltu_true_iff in H. rewrite H. trivial.
    apply int_eq_true_iff in H. rewrite H. apply Bool.orb_true_r.
Qed.

Lemma int_lequ_false_iff :
  forall i1 i2, lequ i1 i2 = false <-> unsigned i1 > unsigned i2.
Proof. intros; split.
  intros. unfold lequ in H.
    destruct (Bool.orb_false_elim _ _ H).
    apply int_ltu_false_iff in H0. apply int_eq_false_iff in H1. omega.
  intros. 
    assert (ltu i1 i2 = false). apply int_ltu_false_iff. omega.
    assert (eq i1 i2 = false). apply int_eq_false_iff. omega.
    unfold lequ. apply Bool.orb_false_intro; assumption.
Qed.

Lemma int_lequ_refl : forall x, lequ x x = true.
Proof. unfold lequ. intros. rewrite int_eq_refl. rewrite orb_true_r. trivial. Qed.

Lemma int_lequ_trans : forall x y z, 
  lequ x y = true -> lequ y z = true -> lequ x z = true.
Proof. intros. apply int_lequ_true_iff in H. apply int_lequ_true_iff in H0.
  apply int_lequ_true_iff. omega.
Qed.

Lemma int_lequ_zero : forall x, lequ zero x = true.
Proof. intros. apply int_lequ_true_iff.
  unfold zero. change (unsigned (repr 0)) with 0.
  generalize (unsigned_range x). omega. 
Qed.

(** ** Modulo arithmetic *)

(** We define and state properties of equality and arithmetic modulo a
  positive integer. *)

Section EQ_MODULO.

Variable modul: Z.
Hypothesis modul_pos: modul > 0.

Definition eqmod (x y: Z) : Prop := exists k, x = k * modul + y.

Lemma eqmod_refl: forall x, eqmod x x.
Proof.
  intros; red. exists 0. omega.
Qed.

Lemma eqmod_refl2: forall x y, x = y -> eqmod x y.
Proof.
  intros. subst y. apply eqmod_refl.
Qed.

Lemma eqmod_sym: forall x y, eqmod x y -> eqmod y x.
Proof.
  intros x y [k EQ]; red. exists (-k). subst x. ring.
Qed.

Lemma eqmod_trans: forall x y z, eqmod x y -> eqmod y z -> eqmod x z.
Proof.
  intros x y z [k1 EQ1] [k2 EQ2]; red.
  exists (k1 + k2). subst x; subst y. ring.
Qed.

Lemma eqmod_small_eq:
  forall x y, eqmod x y -> 0 <= x < modul -> 0 <= y < modul -> x = y.
Proof.
  intros x y [k EQ] I1 I2.
  generalize (Zdiv_unique _ _ _ _ EQ I2). intro.
  rewrite (Zdiv_small x modul I1) in H. subst k. omega.
Qed.

Lemma eqmod_mod_eq:
  forall x y, eqmod x y -> x mod modul = y mod modul.
Proof.
  intros x y [k EQ]. subst x. 
  rewrite Zplus_comm. apply Z_mod_plus. auto.
Qed.

Lemma eqmod_mod:
  forall x, eqmod x (x mod modul).
Proof.
  intros; red. exists (x / modul). 
  rewrite Zmult_comm. apply Z_div_mod_eq. auto.
Qed.

Lemma eqmod_add:
  forall a b c d, eqmod a b -> eqmod c d -> eqmod (a + c) (b + d).
Proof.
  intros a b c d [k1 EQ1] [k2 EQ2]; red.
  subst a; subst c. exists (k1 + k2). ring.
Qed.

Lemma eqmod_neg:
  forall x y, eqmod x y -> eqmod (-x) (-y).
Proof.
  intros x y [k EQ]; red. exists (-k). rewrite EQ. ring. 
Qed.

Lemma eqmod_sub:
  forall a b c d, eqmod a b -> eqmod c d -> eqmod (a - c) (b - d).
Proof.
  intros a b c d [k1 EQ1] [k2 EQ2]; red.
  subst a; subst c. exists (k1 - k2). ring.
Qed.

Lemma eqmod_mult:
  forall a b c d, eqmod a c -> eqmod b d -> eqmod (a * b) (c * d).
Proof.
  intros a b c d [k1 EQ1] [k2 EQ2]; red.
  subst a; subst b.
  exists (k1 * k2 * modul + c * k2 + k1 * d).
  ring.
Qed.

End EQ_MODULO.

(** We then specialize these definitions to equality modulo 
  $2^32$ #2<sup>32</sup>#. *)

(** Or rather, $2^wordsize$ #2<sup>wordsize</sup>#. *)

Lemma modulus_pos:
  modulus > 0.
Proof.
  unfold modulus. 
  generalize wordsize.
  induction n ; simpl. unfold two_power_nat. unfold shift_nat. simpl. 
  omega.
  apply two_power_nat_pos. 
Qed.
Hint Resolve modulus_pos: ints.

Definition eqm := eqmod modulus.

Lemma eqm_refl: forall x, eqm x x.
Proof (eqmod_refl modulus).
Hint Resolve eqm_refl: ints.

Lemma eqm_refl2:
  forall x y, x = y -> eqm x y.
Proof (eqmod_refl2 modulus).
Hint Resolve eqm_refl2: ints.

Lemma eqm_sym: forall x y, eqm x y -> eqm y x.
Proof (@eqmod_sym modulus).
Hint Resolve eqm_sym: ints.

Lemma eqm_trans: forall x y z, eqm x y -> eqm y z -> eqm x z.
Proof (@eqmod_trans modulus).
Hint Resolve eqm_trans: ints.

Lemma eqm_samerepr: forall x y, eqm x y -> repr x = repr y.
Proof.
  intros. unfold repr. apply mkint_eq. 
  apply eqmod_mod_eq. auto with ints. exact H.
Qed.

Lemma eqm_small_eq:
  forall x y, eqm x y -> 0 <= x < modulus -> 0 <= y < modulus -> x = y.
Proof (@eqmod_small_eq modulus).
Hint Resolve eqm_small_eq: ints.

Lemma eqm_add:
  forall a b c d, eqm a b -> eqm c d -> eqm (a + c) (b + d).
Proof (@eqmod_add modulus).
Hint Resolve eqm_add: ints.

Lemma eqm_neg:
  forall x y, eqm x y -> eqm (-x) (-y).
Proof (@eqmod_neg modulus).
Hint Resolve eqm_neg: ints.

Lemma eqm_sub:
  forall a b c d, eqm a b -> eqm c d -> eqm (a - c) (b - d).
Proof (@eqmod_sub modulus).
Hint Resolve eqm_sub: ints.

Lemma eqm_mult:
  forall a b c d, eqm a c -> eqm b d -> eqm (a * b) (c * d).
Proof (@eqmod_mult modulus).
Hint Resolve eqm_mult: ints.

(** ** Properties of the coercions between [Z] and [int] *)

Lemma eqm_unsigned_repr:
  forall z, eqm z (unsigned (repr z)).
Proof.
  unfold eqm, repr, unsigned; intros; simpl.
  apply eqmod_mod. auto with ints.
Qed.
Hint Resolve eqm_unsigned_repr: ints.

Lemma eqm_unsigned_repr_l:
  forall a b, eqm a b -> eqm (unsigned (repr a)) b.
Proof.
  intros. apply eqm_trans with a. 
  apply eqm_sym. apply eqm_unsigned_repr. auto.
Qed.
Hint Resolve eqm_unsigned_repr_l: ints.

Lemma eqm_unsigned_repr_r:
  forall a b, eqm a b -> eqm a (unsigned (repr b)).
Proof.
  intros. apply eqm_trans with b. auto.
  apply eqm_unsigned_repr. 
Qed.
Hint Resolve eqm_unsigned_repr_r: ints.

Lemma eqm_signed_unsigned:
  forall x, eqm (signed x) (unsigned x).
Proof.
  intro; red; unfold signed. set (y := unsigned x).
  case (zlt y half_modulus); intro.
  apply eqmod_refl. red; exists (-1); ring. 
Qed.

Lemma two_power_nat_monotone: forall n, two_power_nat n < two_power_nat (S n).
  intros. induction n. compute. trivial. assert (two_power_nat (S (S n)) = 2 * two_power_nat (S n)). auto. rewrite H. auto.
Qed.

Lemma min_signed_lt_0:  min_signed < 0.
  intros. unfold min_signed, half_modulus, modulus, wordsize. 
  assert ((two_power_nat (S wordsize_minus_one) / 2) = (two_power_nat wordsize_minus_one)).
  rewrite two_power_nat_S. rewrite Zmult_comm. rewrite Z_div_mult. trivial.
  exact modulus_pos.
  assert (two_power_nat wordsize_minus_one > 0). apply two_power_nat_pos. omega.
Qed.
Hint Resolve min_signed_lt_0: ints.

Theorem signed_range:
  forall i, min_signed <= signed i <= max_signed.
Proof.
  intros. unfold signed. 
  generalize (unsigned_range i). set (n := unsigned i). intros.
  case (zlt n half_modulus); intro.
  assert (min_signed < 0).  
    apply min_signed_lt_0. 
  assert (min_signed < n) by auto with *. 
  unfold max_signed.  auto with *. 
  assert (2 *half_modulus = modulus). 
    unfold half_modulus. unfold modulus.
    unfold wordsize. rewrite two_power_nat_S. 
    replace (2 * two_power_nat wordsize_minus_one)
      with (two_power_nat wordsize_minus_one * 2) by auto with *.
  rewrite Z_div_mult. omega.
    exact modulus_pos.
  replace modulus with (2 * half_modulus).
  replace modulus with (2 * half_modulus) in H. 
  unfold min_signed, max_signed. auto with zarith. 
Qed.

Theorem repr_unsigned:
  forall i, repr (unsigned i) = i.
Proof.
  destruct i; simpl. unfold repr. apply mkint_eq.
  apply Zmod_small. auto.
Qed.
Hint Resolve repr_unsigned: ints.

Lemma repr_signed:
  forall i, repr (signed i) = i.
Proof.
  intros. transitivity (repr (unsigned i)). 
  apply eqm_samerepr. apply eqm_signed_unsigned. auto with ints.
Qed.
Hint Resolve repr_unsigned: ints.

Theorem unsigned_repr:
  forall z, 0 <= z <= max_unsigned -> unsigned (repr z) = z.
Proof.
  intros. unfold repr, unsigned; simpl. 
  apply Zmod_small. unfold max_unsigned in H. omega.
Qed.
Hint Resolve unsigned_repr: ints.

Lemma unsigned_repr2:
  forall z, 0 <= z < modulus -> unsigned (repr z) = z.
Proof. intros. apply unsigned_repr. unfold max_unsigned; omega.
Qed.

Lemma unsigned_one: unsigned one = 1.
Proof. unfold one.
    rewrite unsigned_repr. trivial.
    unfold max_unsigned, modulus. unfold wordsize.
    rewrite two_power_nat_S. assert (two_power_nat wordsize_minus_one > 0).
    apply two_power_nat_pos.
    omega.
Qed.

Theorem signed_repr:
  forall z, min_signed <= z <= max_signed -> signed (repr z) = z.
Proof.
  intros. unfold signed. case (zle 0 z); intro.
  replace (unsigned (repr z)) with z.
  rewrite zlt_true. auto. unfold max_signed in H. omega.
  symmetry. apply unsigned_repr. 
  split. auto. apply Zle_trans with max_signed. tauto.
  unfold max_signed. unfold max_unsigned. unfold half_modulus.
  assert (modulus / 2 < modulus). 
  apply Z_div_lt. auto with *. apply modulus_pos. auto with *.  
  pose (z' := z + modulus).
  replace (repr z) with (repr z').
  replace (unsigned (repr z')) with z'.
  rewrite zlt_false. unfold z'. omega.
  unfold z'. unfold min_signed in H. 
  unfold half_modulus. unfold half_modulus in H. 
  assert (z+modulus >= -(modulus/2) + modulus). 
    auto with *. 
  assert (-(modulus / 2) + modulus >= modulus / 2).
    unfold modulus. 
    unfold wordsize.
    rewrite two_power_nat_S. rewrite Zmult_comm. rewrite Z_div_mult.
    assert (two_power_nat (S wordsize_minus_one) >= 
      2 * two_power_nat wordsize_minus_one). 
      replace (2 * two_power_nat wordsize_minus_one) 
        with (two_power_nat (S wordsize_minus_one)) by auto. 
      auto with *. 
    auto with *. 
  auto with *.
  auto with zarith.
  change modulus with (2*  half_modulus). 
  symmetry. apply unsigned_repr.
  unfold z', max_unsigned. unfold min_signed, max_signed in H. 
  unfold modulus. unfold half_modulus in H. unfold modulus in H. 
  assert (0 <= - (two_power_nat wordsize / 2) + two_power_nat wordsize). 
    unfold wordsize. 
    rewrite two_power_nat_S. rewrite Zmult_comm. rewrite Z_div_mult.
    replace (two_power_nat (S wordsize_minus_one)) 
      with (2* two_power_nat wordsize_minus_one) by auto. 
    replace (- two_power_nat wordsize_minus_one + 
      2 * two_power_nat wordsize_minus_one) 
      with (two_power_nat wordsize_minus_one) by omega. 
    assert (two_power_nat wordsize_minus_one > 0). apply two_power_nat_pos.
      auto with *. 
    auto with *. omega. 
  apply eqm_samerepr. unfold z'; red. exists 1. omega.
Qed.

(** ** Properties of addition *)

Theorem add_unsigned: forall x y, add x y = repr (unsigned x + unsigned y).
Proof. intros; reflexivity.
Qed.

Theorem add_signed: forall x y, add x y = repr (signed x + signed y).
Proof. 
  intros. rewrite add_unsigned. apply eqm_samerepr.
  apply eqm_add; apply eqm_sym; apply eqm_signed_unsigned.
Qed.

Theorem add_commut: forall x y, add x y = add y x.
Proof. intros; unfold add. decEq. omega. Qed.

Theorem add_zero: forall x, add x zero = x.
Proof. 
  intros; unfold add, zero. change (unsigned (repr 0)) with 0.
  rewrite Zplus_0_r. apply repr_unsigned.
Qed.

Lemma zero_add : forall i, add zero i = i.
Proof. intros; rewrite add_commut. apply add_zero. Qed.

Theorem add_assoc: forall x y z, add (add x y) z = add x (add y z).
Proof.
  intros; unfold add.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_samerepr. 
  apply eqm_trans with ((x' + y') + z').
  auto with ints.
  rewrite <- Zplus_assoc. auto with ints.
Qed.

Theorem add_permut: forall x y z, add x (add y z) = add y (add x z).
Proof.
  intros. rewrite (add_commut y z). rewrite <- add_assoc. apply add_commut. 
Qed.

Theorem add_neg_zero: forall x, add x (neg x) = zero.
Proof.
  intros; unfold add, neg, zero. apply eqm_samerepr.
  replace 0 with (unsigned x + (- (unsigned x))).
  auto with ints. omega.
Qed.

Lemma add_repr :
  forall z1 z2:Z, add (repr z1) (repr z2) = repr (z1 + z2).
Proof. intros z1 z2; rewrite add_unsigned. simpl.
  unfold repr. apply mkint_eq.
  apply eq_sym. apply Zplus_mod.
Qed.

(** ** Properties of negation *)

Theorem neg_repr: forall z, neg (repr z) = repr (-z).
Proof.
  intros; unfold neg. apply eqm_samerepr. auto with ints.
Qed.

Theorem neg_zero: neg zero = zero.
Proof.
  unfold neg, zero. compute. apply mkint_eq. auto.
Qed.

Theorem neg_involutive: forall x, neg (neg x) = x.
Proof.
  intros; unfold neg. transitivity (repr (unsigned x)).
  apply eqm_samerepr. apply eqm_trans with (- (- (unsigned x))).
  apply eqm_neg. apply eqm_unsigned_repr_l. apply eqm_refl. 
  apply eqm_refl2. omega. apply repr_unsigned.
Qed. 

Theorem neg_add_distr: forall x y, neg(add x y) = add (neg x) (neg y).
Proof.
  intros; unfold neg, add. apply eqm_samerepr.
  apply eqm_trans with (- (unsigned x + unsigned y)).
  auto with ints.
  replace (- (unsigned x + unsigned y))
     with ((- unsigned x) + (- unsigned y)).
  auto with ints. omega.
Qed.

(** ** Properties of subtraction *)

Theorem sub_zero_l: forall x, sub x zero = x.
Proof.
  intros; unfold sub. change (unsigned zero) with 0.
  replace (unsigned x - 0) with (unsigned x). apply repr_unsigned.
  omega.
Qed.

Theorem sub_zero_r: forall x, sub zero x = neg x.
Proof.
  intros; unfold sub, neg. change (unsigned zero) with 0.
  replace (0 - unsigned x) with (- unsigned x). auto.
  omega.
Qed.

Theorem sub_add_opp: forall x y, sub x y = add x (neg y).
Proof.
  intros; unfold sub, add, neg.
  replace (unsigned x - unsigned y)
     with (unsigned x + (- unsigned y)).
  apply eqm_samerepr. auto with ints. omega.
Qed.

Theorem sub_idem: forall x, sub x x = zero.
Proof.
  intros; unfold sub. replace (unsigned x - unsigned x) with 0.
  reflexivity. omega.
Qed.

Theorem sub_add_l: forall x y z, sub (add x y) z = add (sub x z) y.
Proof.
  intros. repeat rewrite sub_add_opp. 
  repeat rewrite add_assoc. decEq. apply add_commut.
Qed.

Theorem sub_add_r: forall x y z, sub x (add y z) = add (sub x z) (neg y).
Proof.
  intros. repeat rewrite sub_add_opp.
  rewrite neg_add_distr. rewrite add_permut. apply add_commut.
Qed.

Theorem sub_shifted:
  forall x y z,
  sub (add x z) (add y z) = sub x y.
Proof.
  intros. rewrite sub_add_opp. rewrite neg_add_distr.
  rewrite add_assoc. 
  rewrite (add_commut (neg y) (neg z)).
  rewrite <- (add_assoc z). rewrite add_neg_zero.
  rewrite (add_commut zero). rewrite add_zero.
  symmetry. apply sub_add_opp.
Qed.

Lemma sub_repr :
  forall z1 z2:Z, sub (repr z1) (repr z2) = repr (z1 - z2).
Proof. intros z1 z2. rewrite sub_add_opp. rewrite neg_repr. rewrite add_repr.
  assert (z1 + (- z2) = z1 - z2)%Z. ring. congruence.
Qed.

Lemma add_sub_assoc :
  forall i1 i2 i3, sub (add i1 i2) i3 = add i1 (sub i2 i3).
Proof. intros; rewrite sub_add_opp; rewrite sub_add_opp.
  rewrite add_assoc. trivial.
Qed.

(** ** Properties of multiplication *)

Theorem mul_commut: forall x y, mul x y = mul y x.
Proof.
  intros; unfold mul. decEq. ring. 
Qed.

Theorem mul_zero: forall x, mul x zero = zero.
Proof.
  intros; unfold mul. change (unsigned zero) with 0.
  unfold zero. decEq. ring.
Qed.

Theorem mul_one: forall x, mul x one = x.
Proof.
  intros; unfold mul. rewrite unsigned_one.
  transitivity (repr (unsigned x)). decEq. ring.
  apply repr_unsigned.
Qed.

Theorem mul_assoc: forall x y z, mul (mul x y) z = mul x (mul y z).
Proof.
  intros; unfold mul.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_samerepr. apply eqm_trans with ((x' * y') * z').
  auto with ints.
  rewrite <- Zmult_assoc. auto with ints.
Qed.

Theorem mul_add_distr_l:
  forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Proof.
  intros; unfold mul, add.
  apply eqm_samerepr.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_trans with ((x' + y') * z').
  auto with ints.
  replace ((x' + y') * z') with (x' * z' + y' * z').
  auto with ints.
  ring.
Qed.

Theorem mul_signed:
  forall x y, mul x y = repr (signed x * signed y).
Proof.
  intros; unfold mul. apply eqm_samerepr.
  apply eqm_mult; apply eqm_sym; apply eqm_signed_unsigned.
Qed.

Theorem mul_add_distr_r:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Proof.
  intros. rewrite mul_commut. rewrite mul_add_distr_l. 
  decEq; apply mul_commut.
Qed. 

Theorem neg_mul_distr_l: 
  forall x y, neg(mul x y) = mul (neg x) y.
Proof.
  intros. unfold mul, neg.
  set (x' := unsigned x).  set (y' := unsigned y).
  apply eqm_samerepr. apply eqm_trans with (- (x' * y')).
  auto with ints.
  replace (- (x' * y')) with ((-x') * y') by ring.
  auto with ints.
Qed.

Theorem neg_mul_distr_r:
   forall x y, neg(mul x y) = mul x (neg y).
Proof.
  intros. rewrite (mul_commut x y). rewrite (mul_commut x (neg y)).
  apply neg_mul_distr_l. 
Qed.

(** ** Properties of binary decompositions *)

Lemma Z_bin_decomp_when_zero : forall z b, 
  Z_bin_decomp z = (false,b) -> z = 2*b.
Proof. intros. destruct z. simpl in H.  inv H. trivial.
  destruct p; simpl in H; try congruence.
    inv H. trivial.
  destruct p; simpl in H; try congruence.
    inv H. trivial.
Qed.

Lemma Z_shift_add_bin_decomp:
  forall x,
  Z_shift_add (fst (Z_bin_decomp x)) (snd (Z_bin_decomp x)) = x.
Proof.
  destruct x; simpl.
  auto.
  destruct p; reflexivity.
  destruct p; try reflexivity. simpl. 
  assert (forall z, 2 * (z + 1) - 1 = 2 * z + 1). intro; omega.
  generalize (H (Zpos p)); simpl. congruence.
Qed.

Lemma Z_shift_add_inj:
  forall b1 x1 b2 x2,
  Z_shift_add b1 x1 = Z_shift_add b2 x2 -> b1 = b2 /\ x1 = x2.
Proof.
  intros until x2.
  unfold Z_shift_add.
  destruct b1; destruct b2; intros;
  ((split; [reflexivity|omega]) || omegaContradiction).
Qed.

Opaque Zmult.

Lemma Z_bin_decomp_2xm1:
  forall x, Z_bin_decomp (2 * x - 1) = (true, x - 1).
Proof.
  intros. caseEq (Z_bin_decomp (2 * x - 1)). intros b y EQ.
  generalize (Z_shift_add_bin_decomp (2 * x - 1)).
  rewrite EQ; simpl.
  replace (2 * x - 1) with (Z_shift_add true (x - 1)).
  intro. elim (Z_shift_add_inj _ _ _ _ H); intros.
  congruence. unfold Z_shift_add. omega.
Qed.

Lemma Z_of_bits_exten:
  forall n f1 f2,
  (forall z, 0 <= z < Z_of_nat n -> f1 z = f2 z) ->
  Z_of_bits n f1 = Z_of_bits n f2.
Proof.
  induction n; intros.
  reflexivity.
  simpl. rewrite inj_S in H. decEq. apply H. omega. 
  apply IHn. intros; apply H. omega.
Qed.

Lemma Z_of_bits_of_Z:
  forall x, eqm (Z_of_bits wordsize (bits_of_Z wordsize x)) x.
Proof.
  assert (forall n x, exists k,
    Z_of_bits n (bits_of_Z n x) = k * two_power_nat n + x).
  induction n; intros.
  rewrite two_power_nat_O. simpl. exists (-x). omega.
  rewrite two_power_nat_S. simpl.
  caseEq (Z_bin_decomp x). intros b y ZBD. simpl. 
  replace (Z_of_bits n (fun i => if zeq (i + 1) 0 then b else bits_of_Z n y (i + 1 - 1)))
     with (Z_of_bits n (bits_of_Z n y)).
  elim (IHn y). intros k1 EQ1. rewrite EQ1.
  rewrite <- (Z_shift_add_bin_decomp x). 
  rewrite ZBD. simpl. 
  exists k1.
  case b; unfold Z_shift_add; ring.
  apply Z_of_bits_exten. intros.
  rewrite zeq_false. decEq. omega. omega. 
  intro. exact (H wordsize x).
Qed.

Lemma bits_of_Z_zero:
  forall n x, bits_of_Z n 0 x = false.
Proof.
  induction n; simpl; intros.
  auto.
  case (zeq x 0); intro. auto. auto.
Qed.

Lemma bits_of_Z_mone:
  forall n x,
  0 <= x < Z_of_nat n -> 
  bits_of_Z n (two_power_nat n - 1) x = true.
Proof.
  induction n; intros.
  simpl in H. omegaContradiction.
  unfold bits_of_Z; fold bits_of_Z.
  rewrite two_power_nat_S. rewrite Z_bin_decomp_2xm1.
  rewrite inj_S in H. case (zeq x 0); intro. auto.
  apply IHn. omega. 
Qed.

Lemma Z_bin_decomp_shift_add:
  forall b x, Z_bin_decomp (Z_shift_add b x) = (b, x).
Proof.
  intros. caseEq (Z_bin_decomp (Z_shift_add b x)); intros b' x' EQ.
  generalize (Z_shift_add_bin_decomp (Z_shift_add b x)).
  rewrite EQ; simpl fst; simpl snd. intro.
  elim (Z_shift_add_inj _ _ _ _ H); intros.
  congruence.
Qed.

Lemma bits_of_Z_of_bits:
  forall n f i,
  0 <= i < Z_of_nat n ->
  bits_of_Z n (Z_of_bits n f) i = f i.
Proof.
  induction n; intros; simpl.
  simpl in H. omegaContradiction.
  rewrite Z_bin_decomp_shift_add.
  case (zeq i 0); intro.
  congruence.
  rewrite IHn. decEq. omega. rewrite inj_S in H. omega.
Qed.  

Lemma Z_of_bits_range:
  forall f, 0 <= Z_of_bits wordsize f < modulus.
Proof.
  unfold max_unsigned, modulus.
  generalize wordsize. induction n; simpl; intros.
  rewrite two_power_nat_O. omega.
  rewrite two_power_nat_S. generalize (IHn (fun i => f (i + 1))).
  set (x := Z_of_bits n (fun i => f (i + 1))).
  intro. destruct (f 0); unfold Z_shift_add; omega.
Qed.
Hint Resolve Z_of_bits_range: ints.

Lemma Z_of_bits_range_2:
  forall f, 0 <= Z_of_bits wordsize f <= max_unsigned.
Proof.
  intros. unfold max_unsigned.
  generalize (Z_of_bits_range f). omega.
Qed.
Hint Resolve Z_of_bits_range_2: ints.

Lemma bits_of_Z_below:
  forall n x i, i < 0 -> bits_of_Z n x i = false.
Proof.
  induction n; simpl; intros.
  reflexivity.
  destruct (Z_bin_decomp x). rewrite zeq_false. apply IHn.
  omega. omega.
Qed.

Lemma bits_of_Z_above:
  forall n x i, i >= Z_of_nat n -> bits_of_Z n x i = false.
Proof.
  induction n; intros; simpl.
  reflexivity.
  destruct (Z_bin_decomp x). rewrite zeq_false. apply IHn.
  rewrite inj_S in H. omega. rewrite inj_S in H. omega.
Qed.

Lemma bits_of_Z_of_bits':
  forall n f i,
  bits_of_Z n (Z_of_bits n f) i =
  if zlt i 0 then false 
  else if zle (Z_of_nat n) i then false
  else f i.
Proof.
  intros. 
  destruct (zlt i 0). apply bits_of_Z_below; auto.
  destruct (zle (Z_of_nat n) i). apply bits_of_Z_above. omega.
  apply bits_of_Z_of_bits. omega.
Qed. 

Lemma last_bit_zero_imp_mult2 : forall n z,
  bits_of_Z (S n) z 0 = false -> 
    exists z', z = 2*z' /\ 
    forall (k:Z), bits_of_Z (S n) z (k + 1) = bits_of_Z n z' k.
Proof. intros. simpl in H.
  remember (Z_bin_decomp z) as d.
  destruct d. simpl in H. subst b.
  apply eq_sym in Heqd.
  exists z0. split.  apply Z_bin_decomp_when_zero in Heqd. trivial.
    intros. simpl. rewrite Heqd.
    destruct (zeq (k+1) 0). assert (k=-1) by omega. subst k.
      apply eq_sym. apply bits_of_Z_below. omega.
      replace (k+1-1) with k by omega. trivial.
Qed.

Lemma bits_of_Z_inc_width : forall n m k z,
  k < Z_of_nat n <= Z_of_nat m -> bits_of_Z n z k = bits_of_Z m z k.
Proof. induction n; intros. 
  simpl in H. rewrite bits_of_Z_below by omega. 
    rewrite bits_of_Z_below by omega. trivial.
  assert (n < m)%nat.
    destruct H. apply inj_le_rev in H0. omega.
  rewrite (S_pred m n) by assumption.
  destruct (Ztrichotomy k 0).
    rewrite bits_of_Z_below by assumption.
    rewrite bits_of_Z_below by assumption. trivial.
    simpl. destruct (Z_bin_decomp z).
    destruct H1. subst k. simpl. trivial.
      rewrite zeq_false by omega.
      rewrite zeq_false by omega.
      apply IHn. split. 
        rewrite inj_S in H. omega.
        destruct H. apply inj_le_rev in H2. apply inj_le. omega.
Qed.


Opaque Zmult.

Lemma Z_of_bits_excl:
  forall n f g h,
  (forall i, 0 <= i < Z_of_nat n -> f i && g i = false) ->
  (forall i, 0 <= i < Z_of_nat n -> f i || g i = h i) ->
  Z_of_bits n f + Z_of_bits n g = Z_of_bits n h.
Proof.
  induction n.
  intros; reflexivity.
  intros. simpl. rewrite inj_S in H. rewrite inj_S in H0.
  rewrite <- (IHn (fun i => f(i+1)) (fun i => g(i+1)) (fun i => h(i+1))).
  assert (0 <= 0 < Zsucc(Z_of_nat n)). omega.
  unfold Z_shift_add.
  rewrite <- H0; auto.
  set (F := Z_of_bits n (fun i => f(i + 1))).
  set (G := Z_of_bits n (fun i => g(i + 1))).
  caseEq (f 0); intros; caseEq (g 0); intros; simpl.
  generalize (H 0 H1). rewrite H2; rewrite H3. simpl. intros; discriminate.
  omega. omega. omega.
  intros; apply H. omega.
  intros; apply H0. omega.
Qed.

(** ** Properties of bitwise and, or, xor *)

Lemma bitwise_binop_commut:
  forall f,
  (forall a b, f a b = f b a) ->
  forall x y,
  bitwise_binop f x y = bitwise_binop f y x.
Proof.
  unfold bitwise_binop; intros.
  decEq. apply Z_of_bits_exten; intros. auto.
Qed.

Lemma bitwise_binop_assoc:
  forall f,
  (forall a b c, f a (f b c) = f (f a b) c) ->
  forall x y z,
  bitwise_binop f (bitwise_binop f x y) z =
  bitwise_binop f x (bitwise_binop f y z).
Proof.
  unfold bitwise_binop; intros.
  repeat rewrite unsigned_repr; auto with ints.
  decEq. apply Z_of_bits_exten; intros.
  repeat (rewrite bits_of_Z_of_bits; auto).
Qed.

Lemma bitwise_binop_idem:
  forall f,
  (forall a, f a a = a) ->
  forall x,
  bitwise_binop f x x = x.
Proof.
  unfold bitwise_binop; intros.
  transitivity (repr (Z_of_bits wordsize (bits_of_Z wordsize (unsigned x)))).
  decEq. apply Z_of_bits_exten; intros. auto.
  transitivity (repr (unsigned x)).
  apply eqm_samerepr. apply Z_of_bits_of_Z. apply repr_unsigned.
Qed.

Theorem and_commut: forall x y, and x y = and y x.
Proof (bitwise_binop_commut andb andb_comm).

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
Proof (bitwise_binop_assoc andb andb_assoc).

Lemma Z_of_bits_of_Z_lt_modulus:
  forall x, 0 <= x < modulus -> (Z_of_bits wordsize (bits_of_Z wordsize x)) = x.
  intros. 
  assert (eqm (Z_of_bits wordsize (bits_of_Z wordsize x)) x). apply Z_of_bits_of_Z.
  unfold eqm in H0. unfold eqmod in H0. elim H0. intros.
  assert (0 <= Z_of_bits wordsize (bits_of_Z wordsize 0) < modulus). apply Z_of_bits_range.
  auto with ints.
Qed.

Theorem and_zero: forall x, and x zero = zero.
Proof.
  unfold and, bitwise_binop, zero; intros.
  transitivity (repr (Z_of_bits wordsize (bits_of_Z wordsize 0))).
  decEq. apply Z_of_bits_exten. intros.
  change (unsigned (repr 0)) with 0.
  rewrite bits_of_Z_zero. apply andb_b_false. decEq. apply Z_of_bits_of_Z_lt_modulus.
  assert (modulus > 0). exact modulus_pos. auto with *. 
Qed.

Lemma mone_max_unsigned:
  mone = repr max_unsigned.
Proof.
  unfold mone. apply eqm_samerepr. exists (-1).
  unfold max_unsigned. omega.
Qed.

Theorem and_mone: forall x, and x mone = x.
Proof.
  unfold and, bitwise_binop; intros. 
  rewrite mone_max_unsigned. unfold max_unsigned, modulus.
  transitivity (repr (Z_of_bits wordsize (bits_of_Z wordsize (unsigned x)))).
  decEq. apply Z_of_bits_exten. intros.
  rewrite unsigned_repr. rewrite bits_of_Z_mone. 
  apply andb_b_true. omega. unfold max_unsigned. fold modulus.
  assert (modulus > 0). auto with *. auto with *. 
  transitivity (repr (unsigned x)). 
  apply eqm_samerepr. apply Z_of_bits_of_Z.
  apply repr_unsigned.
Qed.

Theorem and_idem: forall x, and x x = x.
Proof.
  assert (forall b, b && b = b).
    destruct b; reflexivity.
  exact (bitwise_binop_idem andb H).
Qed.

Theorem or_commut: forall x y, or x y = or y x.
Proof (bitwise_binop_commut orb orb_comm).

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
Proof (bitwise_binop_assoc orb orb_assoc).


Theorem or_zero: forall x, or x zero = x.
Proof.
  unfold or, bitwise_binop, zero; intros. 
  transitivity (repr (Z_of_bits wordsize (bits_of_Z wordsize (unsigned x)))).
  decEq. apply Z_of_bits_exten. intros.
  change (unsigned (repr 0)) with 0.
  rewrite bits_of_Z_zero. apply orb_b_false.
  transitivity (repr (unsigned x)); auto with ints.
  apply eqm_samerepr. apply Z_of_bits_of_Z.
Qed.

Theorem or_mone: forall x, or x mone = mone.
Proof.
  rewrite mone_max_unsigned. 
  unfold or, bitwise_binop; intros.
  decEq. 
  transitivity (Z_of_bits wordsize (bits_of_Z wordsize max_unsigned)).
  apply Z_of_bits_exten. intros.
  assert (unsigned (repr max_unsigned) = max_unsigned).
  apply unsigned_repr. unfold max_unsigned. assert (modulus > 0). exact modulus_pos.
  auto with *.
  auto with *. rewrite H0.
  unfold max_unsigned, modulus. rewrite bits_of_Z_mone; auto.
  apply orb_b_true. 
  apply Z_of_bits_of_Z_lt_modulus.
  unfold max_unsigned. assert (modulus > 0).  auto with *. auto with *. 
Qed.

Theorem or_idem: forall x, or x x = x.
Proof.
  assert (forall b, b || b = b).
    destruct b; reflexivity.
  exact (bitwise_binop_idem orb H).
Qed.

Theorem and_or_distrib:
  forall x y z,
  and x (or y z) = or (and x y) (and x z).
Proof.
  intros; unfold and, or, bitwise_binop.
  decEq. repeat rewrite unsigned_repr; auto with ints.
  apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; auto.
  apply demorgan1.
Qed.  

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof (bitwise_binop_commut xorb xorb_comm).

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
Proof.
  assert (forall a b c, xorb a (xorb b c) = xorb (xorb a b) c).
  symmetry. apply xorb_assoc.
  exact (bitwise_binop_assoc xorb H).
Qed.


Theorem xor_zero: forall x, xor x zero = x.
Proof.
  unfold xor, bitwise_binop, zero; intros. 
  transitivity (repr (Z_of_bits wordsize (bits_of_Z wordsize (unsigned x)))).
  decEq. apply Z_of_bits_exten. intros.
  change (unsigned (repr 0)) with 0.
  rewrite bits_of_Z_zero. apply xorb_false.
  transitivity (repr (unsigned x)); auto with ints.
  apply eqm_samerepr. apply Z_of_bits_of_Z.
Qed.

Theorem xor_zero_one: xor zero one = one.
Proof. assert (xor zero one = xor one zero). apply xor_commut. rewrite H. apply xor_zero.
Qed.

Theorem one_lteq_max_unsigned: 1 <= max_unsigned.
Proof. unfold max_unsigned. unfold modulus. unfold wordsize. rewrite two_power_nat_S.
       assert (two_power_nat wordsize_minus_one > 0). apply two_power_nat_pos. omega.
Qed.

Theorem xor_x_x: forall x, xor x x = zero.
Proof. intros. unfold xor. unfold bitwise_binop.
  assert (Z_of_bits wordsize ((fun i : Z =>
         xorb (bits_of_Z wordsize (unsigned x) i)
           (bits_of_Z wordsize (unsigned x) i))) =
    Z_of_bits wordsize (fun i : Z => false)).
  apply Z_of_bits_exten. intros.  apply xorb_nilpotent.
  rewrite H. 
  assert (Z_of_bits wordsize (fun _ : Z=> false) = 
          (Z_of_bits wordsize (bits_of_Z wordsize 0))). 
  apply Z_of_bits_exten. intros. symmetry.
  apply bits_of_Z_zero. rewrite H0. 
  unfold zero. decEq. apply Z_of_bits_of_Z_lt_modulus.
  assert (modulus > 0). auto with *. auto with *.
Qed.

Theorem xor_one_one: xor one one = zero.
Proof. apply xor_x_x.
Qed.

Theorem and_xor_distrib:
  forall x y z,
  and x (xor y z) = xor (and x y) (and x z).
Proof.
  intros; unfold and, xor, bitwise_binop.
  decEq. repeat rewrite unsigned_repr; auto with ints.
  apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; auto.
  assert (forall a b c, a && (xorb b c) = xorb (a && b) (a && c)).
    destruct a; destruct b; destruct c; reflexivity.
  auto.
Qed.  

Theorem not_involutive:
  forall (x: int), not (not x) = x.
Proof.
  intros. unfold not. rewrite xor_assoc. 
  assert (xor mone mone = zero). apply xor_x_x.
  rewrite H. rewrite xor_zero. auto.
Qed.

(** ** Proofs by reflexion *)

(** To prove equalities involving shifts and rotates, we need to
  show complicated integer equalities involving one integer variable
  that ranges between 0 and 31.  Rather than proving these equalities,
  we ask Coq to check them by computing the 32 values of the 
  left and right-hand sides and checking that they are equal.
  This is an instance of proving by reflection. *)

Section REFLECTION.

Variables (f g: int -> int).

Fixpoint check_equal_on_range (n: nat) : bool :=
  match n with
  | O => true
  | S n => if eq (f (repr (Z_of_nat n))) (g (repr (Z_of_nat n)))
           then check_equal_on_range n
           else false
  end.

Lemma check_equal_on_range_correct:
  forall n, 
  check_equal_on_range n = true ->
  forall z, 0 <= z < Z_of_nat n -> f (repr z) = g (repr z).
Proof.
  induction n.
  simpl; intros;  omegaContradiction.
  simpl check_equal_on_range.
  set (fn := f (repr (Z_of_nat n))).
  set (gn := g (repr (Z_of_nat n))).
  generalize (eq_spec fn gn).
  case (eq fn gn); intros.
  rewrite inj_S in H1. 
  assert (0 <= z < Z_of_nat n \/ z = Z_of_nat n). omega.
  elim H2; intro.
  apply IHn. auto. auto.
  subst z; auto. 
  discriminate. 
Qed.

Lemma equal_on_range:
  check_equal_on_range wordsize = true ->
  forall n, 0 <= unsigned n < Z_of_nat wordsize ->
  f n = g n.
Proof.
  intros. replace n with (repr (unsigned n)). 
  apply check_equal_on_range_correct with wordsize; auto.
  apply repr_unsigned.
Qed.

End REFLECTION.

(** ** Properties of shifts and rotates *)

Lemma Z_of_bits_shift:
  forall n f,
  exists k,
  Z_of_bits n (fun i => f (i - 1)) =
    k * two_power_nat n + Z_shift_add (f (-1)) (Z_of_bits n f).
Proof.
  induction n; intros.
  simpl. rewrite two_power_nat_O. unfold Z_shift_add.
  exists (if f (-1) then (-1) else 0).
  destruct (f (-1)); omega.
  rewrite two_power_nat_S. simpl. 
  elim (IHn (fun i => f (i + 1))). intros k' EQ.
  replace (Z_of_bits n (fun i => f (i - 1 + 1)))
     with (Z_of_bits n (fun i => f (i + 1 - 1))) in EQ.
  rewrite EQ.
  change (-1 + 1) with 0.
  exists k'.
  unfold Z_shift_add; destruct (f (-1)); destruct (f 0); ring.
  apply Z_of_bits_exten; intros.
  decEq. omega.
Qed.

Lemma Z_of_bits_shifts:
  forall m f,
  0 <= m ->
  (forall i, i < 0 -> f i = false) ->
  eqm (Z_of_bits wordsize (fun i => f (i - m)))
      (two_p m * Z_of_bits wordsize f).
Proof.
  intros. pattern m. apply natlike_ind.
  apply eqm_refl2. transitivity (Z_of_bits wordsize f).
  apply Z_of_bits_exten; intros. decEq. omega.
  simpl two_p. omega.
  intros. rewrite two_p_S; auto.
  set (f' := fun i => f (i - x)).
  apply eqm_trans with (Z_of_bits wordsize (fun i => f' (i - 1))).
  apply eqm_refl2. apply Z_of_bits_exten; intros.
  unfold f'. decEq. omega.
  apply eqm_trans with (Z_shift_add (f' (-1)) (Z_of_bits wordsize f')).
  exact (Z_of_bits_shift wordsize f').
  unfold f'. unfold Z_shift_add. rewrite H0. 
  rewrite <- Zmult_assoc. apply eqm_mult. apply eqm_refl.
  apply H2. omega. assumption.
Qed.

Lemma shl_mul_two_p:
  forall x y,
  shl x y = mul x (repr (two_p (unsigned y))).
Proof.
  intros. unfold shl, mul. 
  apply eqm_samerepr. 
  eapply eqm_trans.
  apply Z_of_bits_shifts.
  generalize (unsigned_range y). omega.
  intros; apply bits_of_Z_below; auto.
  rewrite Zmult_comm. apply eqm_mult.
  apply Z_of_bits_of_Z. apply eqm_unsigned_repr.
Qed.


Theorem shl_zero: forall x, shl x zero = x.
Proof.
  intros. rewrite shl_mul_two_p. 
  change (repr (two_p (unsigned zero))) with one.
  apply mul_one.
Qed.



Theorem shl_mul:
  forall x y,
  shl x y = mul x (shl one y).
Proof.
  intros. 
  assert (shl one y = repr (two_p (unsigned y))).
  rewrite shl_mul_two_p. rewrite mul_commut. rewrite mul_one. auto.
  rewrite H. apply shl_mul_two_p.
Qed.

Lemma two_power_nat_increases: forall n, Z_of_nat n <= two_power_nat n -1.
Proof.
  intros.
  induction n. change (Z_of_nat 0) with 0. change (two_power_nat 0) with 1.
  auto with *. rewrite two_power_nat_S. rewrite inj_S.
  change (Zsucc (Z_of_nat n)) with (Z_of_nat n + 1).
  auto with *.
Qed.

Theorem shl_rolm:
  forall x n,
  ltu n (repr (Z_of_nat wordsize)) = true ->
  shl x n = rolm x n (shl mone n).
Proof.
  intros x n. unfold ltu. 
  rewrite unsigned_repr. case (zlt (unsigned n) (Z_of_nat wordsize)); intros LT XX.
  unfold shl, rolm, rol, and, bitwise_binop.
  decEq. apply Z_of_bits_exten; intros.
  repeat rewrite unsigned_repr; auto with ints.
  repeat rewrite bits_of_Z_of_bits; auto. 
  case (zlt z (unsigned n)); intro LT2.
  assert (z - unsigned n < 0). omega.
  rewrite (@bits_of_Z_below wordsize (unsigned x) _ H0).
  rewrite (@bits_of_Z_below wordsize (unsigned mone) _ H0).
  symmetry. apply andb_b_false. 
  assert (z - unsigned n < Z_of_nat wordsize).
    generalize (unsigned_range n). omega. 
  replace (unsigned mone) with (two_power_nat wordsize - 1).
  rewrite bits_of_Z_mone. rewrite andb_b_true. decEq.
  rewrite Zmod_small. auto. omega. omega. 
  rewrite mone_max_unsigned. unfold max_unsigned, modulus.
  symmetry. apply unsigned_repr. fold modulus. unfold max_unsigned.
  assert (modulus > 0). auto with *. auto with *.
  discriminate. unfold max_unsigned, modulus.
  assert (Z_of_nat wordsize <= two_power_nat wordsize - 1). apply two_power_nat_increases.  
  auto with *.
Qed.

Lemma bitwise_binop_shl:
  forall f x y n,
  f false false = false ->
  bitwise_binop f (shl x n) (shl y n) = shl (bitwise_binop f x y) n.
Proof.
  intros. unfold bitwise_binop, shl.
  decEq. repeat rewrite unsigned_repr; auto with ints.
  apply Z_of_bits_exten; intros.
  case (zlt (z - unsigned n) 0); intro.
  transitivity false. repeat rewrite bits_of_Z_of_bits; auto.
  repeat rewrite bits_of_Z_below; auto.
  rewrite bits_of_Z_below; auto.
  repeat rewrite bits_of_Z_of_bits; auto.
  generalize (unsigned_range n). omega.
Qed.

Lemma and_shl:
  forall x y n,
  and (shl x n) (shl y n) = shl (and x y) n.
Proof.
  unfold and; intros. apply bitwise_binop_shl. reflexivity.
Qed.

Lemma unsigned_repr_wordsize: unsigned (repr (Z_of_nat wordsize)) = Z_of_nat wordsize.
Proof.
  apply unsigned_repr. assert (Z_of_nat wordsize <= max_unsigned).
  unfold max_unsigned, modulus. apply two_power_nat_increases. auto with *.
Qed.

Lemma two_power_nat_increases2: forall n:nat, 2 * (Z_of_nat n - 1) < two_power_nat n - 1.
intros. assert (n = 0 \/ n = 1 \/ n >= 2)%nat.
omega. 
  destruct H. rewrite H. simpl. auto with *. trivial.
  destruct H. rewrite H. change (Z_of_nat 1) with 1. change (2 * (1-1)) with 0.
    change (two_power_nat 1) with 2. auto with *. 
  assert (forall n, 2 * (Z_of_nat (n + 2) -1) < two_power_nat (n + 2) - 1).  
  intros. induction n0. 
     change (two_power_nat (0 + 2)) with 4. change (Z_of_nat (0 + 2)) with 2. auto with *. 
  rewrite inj_plus. assert (S n0 = n0 + 1)%nat. omega. rewrite H0.
  change (Z_of_nat 2) with 2. 
  assert (2 * (Z_of_nat (n0 + 1) + 2 -1) = 2 * Z_of_nat (n0 + 1) + 2). omega. rewrite H1.
  assert ( (n0 + 1 + 2)%nat = (S (n0 + 2))). omega. 
  rewrite H2. rewrite two_power_nat_S. 
  assert (2 * Z_of_nat 1 <= two_power_nat (n0 + 2)).
  replace (n0 + 2)%nat with (S (S n0)). 
  rewrite two_power_nat_S. rewrite two_power_nat_S. 
  change (Z_of_nat 1) with 1. assert (two_power_nat n0 > 0). apply two_power_nat_pos. omega.
  omega. assert (Z_of_nat (n0 + 2) - 1 = Z_of_nat (n0 + 1)). 
  rewrite inj_plus. rewrite inj_plus. simpl. omega. rewrite H4 in IHn0.   omega. 
  set (x := (n -2)%nat).
  assert (n = (x+2)%nat). unfold x. auto with *. rewrite H1. apply H0. 
Qed.

Theorem shl_shl:
  forall x y z,
  ltu y (repr (Z_of_nat wordsize)) = true -> 
  ltu z (repr (Z_of_nat wordsize)) = true ->
  ltu (add y z) (repr (Z_of_nat wordsize)) = true ->
  shl (shl x y) z = shl x (add y z).
Proof.
  intros. unfold shl, add.
  generalize (int_ltu_inv _ _ H). 
  generalize (int_ltu_inv _ _ H0).
  rewrite unsigned_repr_wordsize.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  intros.
  repeat rewrite unsigned_repr.
  decEq. apply Z_of_bits_exten. intros n R.
  rewrite bits_of_Z_of_bits'. 
  destruct (zlt (n - z') 0).
  symmetry. apply bits_of_Z_below. omega.
  destruct (zle (Z_of_nat wordsize) (n - z')).
  symmetry. apply bits_of_Z_below. omega.
  decEq. omega.
  assert (2 * (Z_of_nat wordsize - 1) < max_unsigned).
  apply two_power_nat_increases2. omega.  apply Z_of_bits_range_2. 
Qed.

Theorem shru_shru:
  forall x y z,
  ltu y (repr (Z_of_nat wordsize)) = true -> 
  ltu z (repr (Z_of_nat wordsize)) = true ->
  ltu (add y z) (repr (Z_of_nat wordsize)) = true ->
  shru (shru x y) z = shru x (add y z).
Proof.
  intros. unfold shru, add.
  generalize (int_ltu_inv _ _ H). 
  generalize (int_ltu_inv _ _ H0).
  rewrite unsigned_repr_wordsize.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  intros.
  repeat rewrite unsigned_repr.
  decEq. apply Z_of_bits_exten. intros n R.
  rewrite bits_of_Z_of_bits'. 
  destruct (zlt (n + z') 0). omegaContradiction.
  destruct (zle (Z_of_nat wordsize) (n + z')).
  symmetry. apply bits_of_Z_above. omega.
  decEq. omega.
  assert (2 * (Z_of_nat wordsize - 1) < max_unsigned). apply two_power_nat_increases2. 
  omega.
  apply Z_of_bits_range_2.
Qed.

Theorem shru_rolm:
  forall x n,
  ltu n (repr (Z_of_nat wordsize)) = true ->
  shru x n = rolm x (sub (repr (Z_of_nat wordsize)) n) (shru mone n).
Proof.
  intros x n. unfold ltu. 
  rewrite unsigned_repr_wordsize. 
  case (zlt (unsigned n) (Z_of_nat wordsize)); intros LT XX.
  unfold shru, rolm, rol, and, bitwise_binop.
  decEq. apply Z_of_bits_exten; intros.
  repeat rewrite unsigned_repr; auto with ints.
  repeat rewrite bits_of_Z_of_bits; auto. 
  unfold sub. 
  rewrite unsigned_repr_wordsize.
  rewrite unsigned_repr. 
  case (zlt (z + unsigned n) (Z_of_nat wordsize)); intro LT2.
  replace (unsigned mone) with (two_power_nat wordsize - 1).
  rewrite bits_of_Z_mone. rewrite andb_b_true.
  decEq. 
  replace (z - (Z_of_nat wordsize - unsigned n))
     with ((z + unsigned n) + (-1) * Z_of_nat wordsize).
  rewrite Z_mod_plus. symmetry. apply Zmod_small.
  generalize (unsigned_range n). omega. omega. omega.  
  generalize (unsigned_range n). omega.  
  change (two_power_nat wordsize - 1) with max_unsigned. rewrite mone_max_unsigned.
  rewrite unsigned_repr. trivial. unfold max_unsigned.
  assert (0 <= modulus - 1). unfold modulus. assert (two_power_nat wordsize > 0). 
  apply two_power_nat_pos. auto with *. auto with *.
  rewrite (@bits_of_Z_above wordsize (unsigned x) _ LT2).
  rewrite (@bits_of_Z_above wordsize (unsigned mone) _ LT2).
  symmetry. apply andb_b_false.
  split. omega. apply Zle_trans with (Z_of_nat wordsize).
  generalize (unsigned_range n); omega. unfold max_unsigned, modulus. 
  apply two_power_nat_increases. apply eq_true_false_abs in XX. elim XX. trivial.
Qed.

Lemma bitwise_binop_shru:
  forall f x y n,
  f false false = false ->
  bitwise_binop f (shru x n) (shru y n) = shru (bitwise_binop f x y) n.
Proof.
  intros. unfold bitwise_binop, shru.
  decEq. repeat rewrite unsigned_repr; auto with ints.
  apply Z_of_bits_exten; intros.
  case (zlt (z + unsigned n) (Z_of_nat wordsize)); intro.
  repeat rewrite bits_of_Z_of_bits; auto.
  generalize (unsigned_range n); omega.
  transitivity false. repeat rewrite bits_of_Z_of_bits; auto.
  repeat rewrite bits_of_Z_above; auto.
  rewrite bits_of_Z_above; auto.
Qed.

Lemma and_shru:
  forall x y n,
  and (shru x n) (shru y n) = shru (and x y) n.
Proof.
  unfold and; intros. apply bitwise_binop_shru. reflexivity.
Qed.


(* The following is basically the same as Zdiv_interval_2 as found in Coqlib.v
   but the version in that file has the condition hi > 0, which seems needlessly strong
   There seems to be a different version of Coqlib.v that has hi >= 0, as we do here,
   but I didn't want to just change it and potentially break some other dependency. -JDT *)

Lemma Zdiv_interval_3:
  forall lo hi a b,
  lo <= a <= hi -> lo <= 0 -> hi >= 0 -> b > 0 ->
  lo <= a/b <= hi.
Proof.
  intros.
  assert (lo <= a / b < hi+1).
  apply Zdiv_interval_1. omega. omega. auto.
  assert (lo * b <= lo * 1). apply Zmult_le_compat_l_neg. omega. omega. 
  replace (lo * 1) with lo in H3 by ring.
  assert ((hi + 1) * 1 <= (hi + 1) * b). apply Zmult_le_compat_l. omega. omega.
  replace ((hi + 1) * 1) with (hi + 1) in H4 by ring.
  omega.
  omega.
Qed.

Theorem shr_shr:
  forall x y z,
  ltu y (repr (Z_of_nat wordsize)) = true -> 
  ltu z (repr (Z_of_nat wordsize)) = true ->
  ltu (add y z) (repr (Z_of_nat wordsize)) = true ->
  shr (shr x y) z = shr x (add y z).
Proof.
  intros. unfold shr, add.
  generalize (int_ltu_inv _ _ H). 
  generalize (int_ltu_inv _ _ H0).
  rewrite unsigned_repr_wordsize.
  set (x' := signed x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  intros.
  rewrite unsigned_repr.
  rewrite two_p_is_exp. 
  rewrite signed_repr.
  decEq. apply Zdiv_Zdiv. apply two_p_gt_ZERO. omega. apply two_p_gt_ZERO. omega.
  apply Zdiv_interval_3. unfold x'; apply signed_range. assert (min_signed < 0).
  apply min_signed_lt_0. omega. unfold max_signed, half_modulus, modulus.
  unfold wordsize. rewrite two_power_nat_S. rewrite Zmult_comm.
  rewrite Z_div_mult. assert (two_power_nat wordsize_minus_one > 0). 
  apply two_power_nat_pos. omega. omega. apply two_p_gt_ZERO. omega. omega. omega. 
  assert (2 * (Z_of_nat wordsize - 1) < max_unsigned). unfold max_unsigned, modulus. 
  apply two_power_nat_increases2. omega.
Qed.

Theorem rol_zero:
  forall x,
  rol x zero = x.
Proof.
  intros. unfold rol.
  transitivity (repr (Z_of_bits wordsize (bits_of_Z wordsize (unsigned x)))).
  decEq. apply Z_of_bits_exten; intros. assert (z - unsigned zero = z).
  unfold unsigned, zero. simpl. assert (0 mod modulus = 0). simple apply refl_equal. 
  rewrite H0.
  auto with *. rewrite H0. assert (z mod Z_of_nat wordsize = z). apply Zmod_small.
  apply H. rewrite H1. trivial. 
  transitivity (repr (unsigned x)). 
  decEq. apply eqm_small_eq. apply Z_of_bits_of_Z.
  auto with ints. auto with ints. auto with ints.
Qed.

Lemma bitwise_binop_rol:
  forall f x y n,
  bitwise_binop f (rol x n) (rol y n) = rol (bitwise_binop f x y) n.
Proof.
  intros. unfold bitwise_binop, rol.
  decEq. repeat (rewrite unsigned_repr; auto with ints).
  apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; auto.
  apply Z_mod_lt. auto with ints. 
Qed.


Theorem rol_and:
  forall x y n,
  rol (and x y) n = and (rol x n) (rol y n).
Proof.
  intros. symmetry. unfold and. apply bitwise_binop_rol.
Qed.

Lemma two_power_nat_div: forall y x,
  (y <= x)%nat -> two_power_nat x / two_power_nat y = two_power_nat (x - y).
Proof.
  induction y; intros. change (two_power_nat 0) with 1.
  replace (x-0)%nat with x. auto with zarith. omega. 
  assert (x > 0)%nat. omega. set (n := (x - 1)%nat ). assert (x = (S n)).
  unfold n. omega. rewrite H1. repeat rewrite two_power_nat_S.
  rewrite Zdiv_mult_cancel_l. replace (S n - S y)%nat with (n - y)%nat.
  rewrite IHy. trivial. omega. omega. omega.  
Qed.

Lemma two_power_nat_divide:
  forall x y : nat,
    (x <= y)%nat -> Zdivide (two_power_nat x) (two_power_nat y).
Proof. induction x; intros. 
  rewrite two_power_nat_O. apply Zone_divide.
  assert (y > 0)%nat. omega. set (n := (y - 1)%nat). 
  assert (y = (S n)). unfold n. omega. rewrite H1. 
  repeat rewrite two_power_nat_S.
  apply Zmult_divide_compat_l.
  apply IHx. omega.
Qed.

Lemma eqmod_two_power_nat: 
  forall W a, (exists k, two_power_nat k = W) -> 
     W < modulus ->
    (eqmod W a (unsigned (repr a))).
Proof.
  intros.
    elim (eqm_unsigned_repr a). intros k EQ.
    elim H. intros.
    red. exists (k * (modulus / W)).
    replace (k * (modulus / W) * W) with (k * modulus). auto. 
    unfold modulus. elim H. intros. rewrite <-H1.
    assert (x <= wordsize \/ x > wordsize)%nat. omega.
    elim H3; intros. rewrite two_power_nat_div. symmetry.
    rewrite two_power_nat_two_p. rewrite two_power_nat_two_p.
    rewrite <-Zmult_assoc. rewrite <-two_p_is_exp.
    replace (Z_of_nat (wordsize - x) + Z_of_nat x) with (Z_of_nat wordsize).
    rewrite <-two_power_nat_two_p. trivial. rewrite <-inj_plus. 
    replace (wordsize - x + x)%nat with (wordsize)%nat. trivial. omega.
    omega. apply Zle_0_nat. exact H4.
    assert (two_power_nat wordsize <= two_power_nat x).
    repeat rewrite two_power_nat_two_p. apply two_p_monotone. auto with zarith.
    assert (Z_of_nat wordsize <= two_power_nat wordsize - 1).
    apply two_power_nat_increases. unfold modulus in H0. omegaContradiction.
Qed.

(* This is not true for arbitrary wordsize. It works if
   wordsize is a power of two or n + m < max_unsigned. See below. -JDT *)
(*
Theorem rol_rol:
  forall x n m,
  rol (rol x n) m = rol x (modu (add n m) (repr (Z_of_nat wordsize))).
Proof.
  intros. unfold rol. decEq.
  repeat (rewrite unsigned_repr; auto with ints).
  apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; auto.
  decEq. unfold modu, add. 
  set (W := Z_of_nat wordsize).
  set (M := unsigned m); set (N := unsigned n).
  assert (W > 0). compute; auto.
  assert (forall a, eqmod W a (unsigned (repr a))).
    intro. elim (eqm_unsigned_repr a). intros k EQ.
    red. exists (k * (modulus / W)). 
    replace (k * (modulus / W) * W) with (k * modulus). auto.
    rewrite <- Zmult_assoc. reflexivity.
  apply eqmod_mod_eq. auto.
  change (unsigned (repr W)) with W.
  apply eqmod_trans with (z - (N + M) mod W).
  apply eqmod_trans with ((z - M) - N).
  apply eqmod_sub. apply eqmod_sym. apply eqmod_mod. auto.
  apply eqmod_refl. 
  replace (z - M - N) with (z - (N + M)).
  apply eqmod_sub. apply eqmod_refl. apply eqmod_mod. auto.
  omega.
  apply eqmod_sub. apply eqmod_refl. 
  eapply eqmod_trans; [idtac|apply H1].
  eapply eqmod_trans; [idtac|apply eqmod_mod].
  apply eqmod_sym. eapply eqmod_trans; [idtac|apply eqmod_mod].
  apply eqmod_sym. apply H1. auto. auto. 
  apply Z_mod_lt. compute; auto.
Qed.
*) 

Theorem rol_rol_weak:
  forall x n m,
  (exists k, two_power_nat k = Z_of_nat wordsize) -> 
  rol (rol x n) m = rol x (modu (add n m) (repr (Z_of_nat wordsize))).
Proof.
  intros. unfold rol. decEq.
  repeat (rewrite unsigned_repr; auto with ints).
  apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; auto.
  decEq. unfold modu, add. 
  set (W := Z_of_nat wordsize).
  set (M := unsigned m); set (N := unsigned n).
  assert (W > 0). unfold W. omega.
  assert (W <= modulus - 1) as L0. 
   unfold W, modulus. apply two_power_nat_increases.
  apply eqmod_mod_eq. auto.
  unfold W. rewrite unsigned_repr_wordsize. fold W.
  apply eqmod_trans with (z - (N + M) mod W).
  apply eqmod_trans with ((z - M) - N).
  apply eqmod_sub. apply eqmod_sym. apply eqmod_mod. auto.
  apply eqmod_refl. 
  replace (z - M - N) with (z - (N + M)).
  apply eqmod_sub. apply eqmod_refl. apply eqmod_mod. auto.
  omega.
  apply eqmod_sub. apply eqmod_refl. 
  eapply eqmod_trans; [idtac|apply eqmod_two_power_nat].
  eapply eqmod_trans; [idtac|apply eqmod_mod].
  apply eqmod_sym. eapply eqmod_trans; [idtac|apply eqmod_mod].
  apply eqmod_sym. apply eqmod_two_power_nat. auto. auto.
  omega. exact H1. exact H1. exact H. omega.
  apply Z_mod_lt. omega. 
Qed.

Theorem rol_rol_weak_2:
  forall x n m,
  unsigned n + unsigned m <= max_unsigned -> 
  rol (rol x n) m = rol x (modu (add n m) (repr (Z_of_nat wordsize))).
Proof.
  intros. 
  assert (0 <= unsigned n + unsigned m <= max_unsigned) as L1.
  split.
  assert (0 <= unsigned n < modulus). apply unsigned_range. 
  assert (0 <= unsigned m < modulus). apply unsigned_range.
  omega. exact H.
  unfold rol. decEq.
  repeat (rewrite unsigned_repr; auto with ints).
  apply Z_of_bits_exten; intros.
  repeat rewrite bits_of_Z_of_bits; auto.
  decEq. unfold modu, add. 
  set (W := Z_of_nat wordsize).
  set (M := unsigned m); set (N := unsigned n).
  assert (W > 0). unfold W. omega.
  assert (W <= modulus - 1) as L0. 
   unfold W, modulus. apply two_power_nat_increases.
  repeat rewrite unsigned_repr. rewrite Zminus_mod_idemp_l.
  rewrite Zminus_mod_idemp_r. replace (z - (N + M)) with (z - M - N).
  trivial. omega. unfold W, max_unsigned, modulus. auto with *.
  exact L1.
  assert (0 <= (N + M) mod W < W). apply Z_mod_lt. exact H1.
  unfold max_unsigned. auto with zarith. unfold max_unsigned. auto with zarith.
  exact L1. apply Z_mod_lt. auto with zarith. 
Qed.

Theorem rolm_zero:
  forall x m,
  rolm x zero m = and x m.
Proof.
  intros. unfold rolm. rewrite rol_zero. auto.
Qed.

(*
Theorem rolm_rolm:
  forall x n1 m1 n2 m2,
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (modu (add n1 n2) (repr (Z_of_nat wordsize)))
           (and (rol m1 n2) m2).
Proof.
  intros.
  unfold rolm. rewrite rol_and. rewrite and_assoc. 
  rewrite rol_rol. reflexivity.
Qed.
*)

Theorem rolm_rolm_weak:
  forall x n1 m1 n2 m2,
  (exists k, two_power_nat k = Z_of_nat wordsize) -> 
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (modu (add n1 n2) (repr (Z_of_nat wordsize)))
           (and (rol m1 n2) m2).
Proof.
  intros.
  unfold rolm. rewrite rol_and. rewrite and_assoc. 
  rewrite rol_rol_weak. trivial. exact H.
Qed.


Theorem rolm_rolm_weak_2:
  forall x n1 m1 n2 m2,
  unsigned n1 + unsigned n2 <= max_unsigned ->
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (modu (add n1 n2) (repr (Z_of_nat wordsize)))
           (and (rol m1 n2) m2).
Proof.
  intros.
  unfold rolm. rewrite rol_and. rewrite and_assoc. 
  rewrite rol_rol_weak_2. trivial. exact H.
Qed.


Theorem rol_or:
  forall x y n,
  rol (or x y) n = or (rol x n) (rol y n).
Proof.
  intros. symmetry. unfold or. apply bitwise_binop_rol.
Qed.


Theorem or_rolm:
  forall x n m1 m2,
  or (rolm x n m1) (rolm x n m2) = rolm x n (or m1 m2).
Proof.
  intros; unfold rolm. symmetry. apply and_or_distrib. 
Qed.

Theorem ror_rol:
  forall x y,
  ltu y (repr (Z_of_nat wordsize)) = true ->
  ror x y = rol x (sub (repr (Z_of_nat wordsize)) y).
Proof.
  intros. unfold ror, rol, sub.
  generalize (int_ltu_inv _ _ H).
  rewrite unsigned_repr_wordsize.
  change (unsigned (repr (Z_of_nat wordsize))) with (Z_of_nat wordsize).
  intro. rewrite unsigned_repr.
  decEq. apply Z_of_bits_exten. intros. decEq.
  apply eqmod_mod_eq. omega. 
  exists 1. omega.
  assert (Z_of_nat wordsize <= max_unsigned). unfold max_unsigned, modulus.
  apply two_power_nat_increases. omega.
Qed.

Lemma max_unsigned_geq_zero: 0 <= max_unsigned.
Proof. 
  unfold max_unsigned, modulus. assert (two_power_nat wordsize > 0).
  apply two_power_nat_pos. omega.
Qed.
Hint Resolve max_unsigned_geq_zero: ints.

Remark or_shl_shru_masks_helper:
  forall x,
  forall shift,
  forall z, 
    0 <= shift < Z_of_nat wordsize ->
    0 <= z < Z_of_nat wordsize -> z >= shift ->
    bits_of_Z wordsize
      (unsigned (shl x (repr shift))) z = bits_of_Z wordsize (unsigned x) (z - shift).
Proof.
  intros. unfold shl. rewrite unsigned_repr. rewrite bits_of_Z_of_bits. 
  rewrite unsigned_repr. trivial. assert (Z_of_nat wordsize <= max_unsigned). 
  unfold max_unsigned, modulus. apply two_power_nat_increases.  omega. 
  auto with *. apply Z_of_bits_range_2.
Qed.

Remark or_shl_shru_masks_helper2:
  forall shift,
  forall z,
    0 <= shift < Z_of_nat wordsize ->
    0 <= z < Z_of_nat wordsize -> z >= shift ->
    bits_of_Z wordsize
      (unsigned (shl mone (repr shift))) z = true.
Proof.
  intros. rewrite or_shl_shru_masks_helper. unfold wordsize. 
  replace (unsigned mone) with (two_power_nat wordsize - 1).
  rewrite bits_of_Z_mone. trivial. omega. rewrite mone_max_unsigned. rewrite unsigned_repr. 
  auto with *. auto with *.  exact H. exact H0. exact H1.
Qed. 

Remark or_shl_shru_masks_helper3:
  forall logn,
  forall z,
    0 <= unsigned logn < Z_of_nat wordsize ->
    0 <= z < Z_of_nat wordsize -> z >= Z_of_nat wordsize - unsigned logn ->
    bits_of_Z wordsize
      (unsigned (shl mone (sub (repr (Z_of_nat wordsize)) logn))) z = true.
Proof.
  intros.
  set (shift := unsigned (sub (repr (Z_of_nat wordsize)) logn)).
  assert (z >= shift). unfold shift. unfold sub. rewrite unsigned_repr_wordsize. 
  rewrite unsigned_repr. exact H1. split. omega.
  assert (Z_of_nat wordsize <= max_unsigned). unfold max_unsigned, modulus.
  apply two_power_nat_increases. omega. apply or_shl_shru_masks_helper2.
  rewrite unsigned_repr_wordsize. omega. exact H0. rewrite unsigned_repr_wordsize.
  exact H1.
Qed.

Remark or_shl_shru_masks_helper4:
  forall logn,
  forall z,
    0 <= unsigned logn < Z_of_nat wordsize ->
    0 <= z < Z_of_nat wordsize -> z < Z_of_nat wordsize - unsigned logn ->
    bits_of_Z wordsize (unsigned (shru mone logn)) z = true.
Proof.
  intros.
  cut (bits_of_Z wordsize (unsigned (shru mone logn)) z = 
    bits_of_Z wordsize (unsigned mone) (z + unsigned logn)).
  intros. rewrite H2. replace (unsigned mone) with (two_power_nat wordsize - 1).
  rewrite bits_of_Z_mone. trivial. 
  split.   omega. omega. rewrite mone_max_unsigned.
  rewrite unsigned_repr. unfold max_unsigned, modulus. trivial. auto with *. 
  unfold shru. rewrite unsigned_repr. rewrite bits_of_Z_of_bits. trivial.
  exact H0. apply Z_of_bits_range_2.
Qed.

Remark or_shl_shru_masks:
  forall logn, 0 <= unsigned logn < Z_of_nat wordsize ->
  or (shl mone (sub (repr (Z_of_nat wordsize)) logn)) (shru mone logn) = mone.
Proof.
  rewrite mone_max_unsigned. 
  unfold or, bitwise_binop; intros.
  decEq. 
  transitivity (Z_of_bits wordsize (bits_of_Z wordsize max_unsigned)).
  apply Z_of_bits_exten. intros.
  rewrite bits_of_Z_mone.
  assert (z < Z_of_nat wordsize - unsigned logn \/ z >= Z_of_nat wordsize - unsigned logn).
  omega.
  rewrite <-mone_max_unsigned.
  destruct H1.
  rewrite or_shl_shru_masks_helper4.
  apply orb_b_true. exact H. exact H0. exact H1.
  rewrite or_shl_shru_masks_helper3.
  apply orb_true_b. exact H. exact H0. exact H1.
  exact H0.
  apply Z_of_bits_of_Z_lt_modulus. split. 
  auto with ints. unfold max_unsigned.  omega.
Qed.


Theorem or_ror:
  forall x y z,
  ltu y (repr (Z_of_nat wordsize)) = true ->
  ltu z (repr (Z_of_nat wordsize)) = true ->
  add y z = repr (Z_of_nat wordsize) ->
  ror x z = or (shl x y) (shru x z).
Proof.
  intros.
  generalize (int_ltu_inv _ _ H).
  generalize (int_ltu_inv _ _ H0).
  rewrite unsigned_repr_wordsize.
  intros.
  rewrite ror_rol; auto.
  rewrite shl_rolm; auto.
  rewrite shru_rolm; auto.
  replace y with (sub (repr (Z_of_nat wordsize)) z).
  rewrite or_rolm.
  rewrite or_shl_shru_masks; auto.
  unfold rolm. rewrite and_mone. auto.
  rewrite <- H1. rewrite sub_add_opp. rewrite add_assoc. 
  rewrite <- sub_add_opp. rewrite sub_idem. apply add_zero. 
Qed.

Remark shru_shl_and_1:
  forall y,
  0 <= unsigned y < Z_of_nat wordsize ->
  modu (add y (sub (repr (Z_of_nat wordsize)) y)) (repr (Z_of_nat wordsize)) = zero.
Proof.
  intros.
  unfold modu. unfold zero. decEq. rewrite unsigned_repr_wordsize.
  unfold sub. rewrite unsigned_repr_wordsize.
  replace (unsigned (add y (repr (Z_of_nat wordsize - unsigned y)))) with
      (Z_of_nat wordsize).
  apply Z_mod_same_full. 
  unfold add.
  assert (Z_of_nat wordsize <= max_unsigned). unfold max_unsigned, modulus.
  apply two_power_nat_increases.
  assert (0 <= Z_of_nat wordsize - unsigned y <= max_unsigned).
  split. omega. omega.
  rewrite unsigned_repr. rewrite unsigned_repr. omega. exact H1.
  rewrite unsigned_repr. omega. exact H1.
Qed.

Remark shru_shl_and_2_helper1:
  forall n, forall i, forall y,
  0 <= unsigned y < Z_of_nat n ->
  0 <= i < Z_of_nat n -unsigned y ->
  bits_of_Z n ((two_p (Z_of_nat n -unsigned y)) -1) i = true.
Proof.
  induction n; intros.
  simpl in H. omegaContradiction.
  rewrite inj_S in H. change (Zsucc (Z_of_nat n)) with (Z_of_nat n + 1) in H.
  assert (unsigned y < Z_of_nat n \/ unsigned y = Z_of_nat n).
  omega.
  destruct H1.
  unfold bits_of_Z; fold bits_of_Z.
  replace (Z_of_nat (S n) - unsigned y) with (Zsucc (Z_of_nat n - unsigned y)).
  rewrite two_p_S. rewrite Z_bin_decomp_2xm1.
  case (zeq i 0); intro. trivial.
  apply IHn. omega. rewrite inj_S in H0.  omega. omega.
  rewrite inj_S. omega.
  assert (Z_of_nat (S n) - unsigned y = 1).
  rewrite inj_S. omega. rewrite H2 in H0. rewrite H2.
  assert (i = 0). omega. simpl. rewrite H3. apply zeq_true.
Qed.

Remark shru_shl_and_2_helper2:
  forall n, forall i, forall y,
  0 <= unsigned y <= Z_of_nat n ->
  i >= Z_of_nat n -unsigned y ->
  bits_of_Z n ((two_p (Z_of_nat n -unsigned y)) -1) i = false.
Proof.
  induction n; intros.
  simpl in H. assert (unsigned y = 0). omega. rewrite H1.  
  simpl. trivial.
  rewrite inj_S in H, H0. change (Zsucc (Z_of_nat n)) with (Z_of_nat n + 1) in H.
  change (Zsucc (Z_of_nat n)) with (Z_of_nat n + 1) in H0.
  assert (unsigned y <= Z_of_nat n \/ unsigned y = Z_of_nat n + 1).
  omega.
  destruct H1.
  unfold bits_of_Z; fold bits_of_Z.
  replace (Z_of_nat (S n) - unsigned y) with (Zsucc (Z_of_nat n - unsigned y)).
  rewrite two_p_S. rewrite Z_bin_decomp_2xm1.
  case (zeq i 0); intro.
  assert (i > 0). omega. omegaContradiction.
  apply IHn. omega. omega. omega. 
  rewrite inj_S. omega.
  assert (Z_of_nat (S n) - unsigned y = 0).
  rewrite inj_S. omega. rewrite H2. 
  apply bits_of_Z_zero.
Qed.

Remark shru_shl_and_2:
  forall y,
  0 <= unsigned y < Z_of_nat wordsize ->
  and (rol (shl mone y) (sub (repr (Z_of_nat wordsize)) y)) (shru mone y) =
  repr (two_p (Z_of_nat wordsize - unsigned y) - 1).
Proof.
  intros.
  unfold and. unfold bitwise_binop.
  transitivity (repr (Z_of_bits wordsize
     (bits_of_Z wordsize (two_p (Z_of_nat wordsize - unsigned y) -1)))).
  decEq.
  apply Z_of_bits_exten. intros.
  assert (z < Z_of_nat wordsize - unsigned y \/ z >= Z_of_nat wordsize - unsigned y).
  omega.
  elim H1; intros.
  rewrite shru_shl_and_2_helper1.
  assert ((bits_of_Z wordsize (unsigned (shru mone y)) z) = true).
  apply or_shl_shru_masks_helper4. exact H. exact H0. exact H2. rewrite H3. 
  assert ((bits_of_Z wordsize
     (unsigned (rol (shl mone y) (sub (repr (Z_of_nat wordsize)) y))) z) = true).
  unfold rol. rewrite unsigned_repr. rewrite bits_of_Z_of_bits.
  assert (unsigned (sub (repr (Z_of_nat wordsize)) y) = Z_of_nat wordsize - unsigned y).
  unfold sub. rewrite unsigned_repr_wordsize.
  rewrite unsigned_repr. trivial. split. omega. 
  assert (Z_of_nat wordsize <= max_unsigned). 
  unfold max_unsigned, modulus. apply two_power_nat_increases. omega.
  rewrite H4. 
  replace (z - (Z_of_nat wordsize - unsigned y)) 
    with (z + (unsigned y - Z_of_nat wordsize)).
  rewrite Zplus_mod. rewrite Zminus_mod. rewrite Z_mod_same_full.
  repeat rewrite Zmod_small. replace (z + (unsigned y - 0)) with (z + unsigned y).
   unfold shl. rewrite unsigned_repr. rewrite bits_of_Z_of_bits.
   replace (z + unsigned y - unsigned y) with z. rewrite mone_max_unsigned.
   rewrite unsigned_repr. unfold max_unsigned.
   apply bits_of_Z_mone.
   exact H0. auto with *.
   omega. omega. apply Z_of_bits_range_2. omega. exact H. omega. exact H.
   exact H0. omega. exact H. omega. exact H. exact H0. omega. exact H0. 
   apply Z_of_bits_range_2.
   unfold max_unsigned. rewrite H4. auto with *. exact H. omega.
   rewrite shru_shl_and_2_helper2.
   assert (bits_of_Z wordsize (unsigned (shru mone y)) z = false).
   unfold shru. rewrite unsigned_repr. rewrite bits_of_Z_of_bits. apply bits_of_Z_above.
   omega. exact H0. apply Z_of_bits_range_2. 
   rewrite H3. apply andb_false_r.
   omega. exact H2.
   decEq. apply Z_of_bits_of_Z_lt_modulus. 
   split. assert (two_p (Z_of_nat wordsize - unsigned y) > 0). apply two_p_gt_ZERO.  
   omega. omega. unfold modulus. 
   assert (two_p (Z_of_nat wordsize - unsigned y) <= two_power_nat wordsize).
   rewrite two_power_nat_two_p. apply two_p_monotone. omega. omega. 
Qed.

Theorem shru_shl_and:
  forall x y,
  ltu y (repr (Z_of_nat wordsize)) = true ->
  shru (shl x y) y = and x (repr (two_p (Z_of_nat wordsize - unsigned y) - 1)).
Proof.
  intros.
  generalize (int_ltu_inv _ _ H). intros.
  rewrite unsigned_repr_wordsize in H0.
  assert (0 <= two_p (Z_of_nat wordsize - unsigned y) - 1 <= max_unsigned).
  unfold max_unsigned. unfold modulus. rewrite two_power_nat_two_p.
  assert (two_p (Z_of_nat wordsize - unsigned y) <= two_p (Z_of_nat wordsize)).
  apply two_p_monotone. omega.
  assert (two_p (Z_of_nat wordsize - unsigned y) > 0). apply two_p_gt_ZERO. 
  omega. omega. 
  unfold shru, and, bitwise_binop.
  decEq. apply Z_of_bits_exten. intros.
  assert (0 <= z < Z_of_nat wordsize - unsigned y \/ z >= Z_of_nat wordsize - unsigned y). 
  omega.
  elim H3; intros; unfold shl; repeat rewrite unsigned_repr. 
  rewrite shru_shl_and_2_helper1.
  rewrite andb_true_r. rewrite bits_of_Z_of_bits.
  replace (z + unsigned y - unsigned y) with z. trivial.
  omega. omega. exact H0. exact H4. exact H1. apply Z_of_bits_range_2. 
  rewrite shru_shl_and_2_helper2. rewrite andb_false_r. apply bits_of_Z_above. 
  omega. omega. exact H4. exact H1. apply Z_of_bits_range_2.
Qed.

(** ** Relation between shifts and powers of 2 *)

Fixpoint powerserie (l: list Z): Z :=
  match l with
  | nil => 0
  | x :: xs => two_p x + powerserie xs
  end.

Lemma Z_bin_decomp_range:
  forall x n,
  0 <= x < 2 * n -> 0 <= snd (Z_bin_decomp x) < n.
Proof.
  intros. rewrite <- (Z_shift_add_bin_decomp x) in H.
  unfold Z_shift_add in H. destruct (fst (Z_bin_decomp x)); omega.
Qed.

Lemma Z_one_bits_powerserie:
  forall x, 0 <= x < modulus -> x = powerserie (Z_one_bits wordsize x 0).
Proof.
  assert (forall n x i, 
    0 <= i ->
    0 <= x < two_power_nat n ->
    x * two_p i = powerserie (Z_one_bits n x i)).
  induction n; intros.
  simpl. rewrite two_power_nat_O in H0. 
  assert (x = 0). omega. subst x. omega.
  rewrite two_power_nat_S in H0. simpl Z_one_bits.
  generalize (Z_shift_add_bin_decomp x).
  generalize (@Z_bin_decomp_range x _ H0).
  case (Z_bin_decomp x). simpl. intros b y RANGE SHADD. 
  subst x. unfold Z_shift_add.
  destruct b. simpl powerserie. rewrite <- IHn. 
  rewrite two_p_is_exp. change (two_p 1) with 2. ring.
  auto. omega. omega. auto.
  rewrite <- IHn. 
  rewrite two_p_is_exp. change (two_p 1) with 2. ring.
  auto. omega. omega. auto.
  intros. rewrite <- H. change (two_p 0) with 1. omega.
  omega. exact H0.
Qed.

Lemma Z_one_bits_range:
  forall x i, In i (Z_one_bits wordsize x 0) -> 0 <= i < Z_of_nat wordsize.
Proof.
  assert (forall n x i j,
    In j (Z_one_bits n x i) -> i <= j < i + Z_of_nat n).
  induction n; simpl In.
  intros; elim H.
  intros x i j. destruct (Z_bin_decomp x). case b.
  rewrite inj_S. simpl. intros [A|B]. subst j. omega.
  generalize (IHn _ _ _ B). omega.
  intros B. rewrite inj_S. generalize (IHn _ _ _ B). omega.
  intros. generalize (H wordsize x 0 i H0). omega.
Qed.

Lemma is_power2_rng:
  forall n logn,
  is_power2 n = Some logn ->
  0 <= unsigned logn < Z_of_nat wordsize.
Proof.
  intros n logn. unfold is_power2.
  generalize (Z_one_bits_range (unsigned n)).
  destruct (Z_one_bits wordsize (unsigned n) 0).
  intros; discriminate.
  destruct l.
  intros. injection H0; intro; subst logn; clear H0.
  assert (0 <= z < Z_of_nat wordsize).
  apply H. auto with coqlib.
  rewrite unsigned_repr. auto.
  assert (Z_of_nat wordsize <= max_unsigned). unfold max_unsigned, modulus.
  apply two_power_nat_increases.
  omega.
  intros; discriminate.
Qed.

Theorem is_power2_range:
  forall n logn,
  is_power2 n = Some logn -> ltu logn (repr (Z_of_nat wordsize)) = true.
Proof.
  intros. unfold ltu.
  rewrite unsigned_repr_wordsize.
  generalize (@is_power2_rng _ _ H). 
  case (zlt (unsigned logn) (Z_of_nat wordsize)); intros.
  auto. omegaContradiction. 
Qed. 

Lemma is_power2_correct:
  forall n logn,
  is_power2 n = Some logn ->
  unsigned n = two_p (unsigned logn).
Proof.
  intros n logn. unfold is_power2.
  generalize (@Z_one_bits_powerserie (unsigned n) (unsigned_range n)).
  generalize (Z_one_bits_range (unsigned n)).
  destruct (Z_one_bits wordsize (unsigned n) 0).
  intros; discriminate.
  destruct l.
  intros. simpl in H0. injection H1; intros; subst logn; clear H1.
  rewrite unsigned_repr. replace (two_p z) with (two_p z + 0).
  auto. omega. elim (H z); intros. 
  assert (Z_of_nat wordsize <= max_unsigned). unfold max_unsigned, modulus. 
  apply two_power_nat_increases.
  omega. auto with coqlib. 
  intros; discriminate.
Qed.

Remark two_p_range:
  forall n,
  0 <= n < Z_of_nat wordsize ->
  0 <= two_p n <= max_unsigned.
Proof.
  intros. split.
  assert (two_p n > 0). apply two_p_gt_ZERO. omega. omega.
  assert (two_p n <= two_p (Z_of_nat wordsize - 1)). apply two_p_monotone. omega.
  eapply Zle_trans. eauto. unfold max_unsigned. unfold modulus. unfold wordsize. 
  rewrite two_power_nat_two_p. rewrite inj_S. 
  change (Zsucc (Z_of_nat wordsize_minus_one)) with (Z_of_nat wordsize_minus_one + 1). 
  replace (Z_of_nat wordsize_minus_one + 1 -1) with (Z_of_nat wordsize_minus_one).
  change (Z_of_nat wordsize_minus_one + 1) with (Zsucc (Z_of_nat wordsize_minus_one)).
  rewrite two_p_S. assert (two_p (Z_of_nat wordsize_minus_one) > 0). apply two_p_gt_ZERO.
  apply Zle_0_nat.
  auto with *.
  apply Zle_0_nat.
  omega.
Qed.

Remark Z_one_bits_zero:
  forall n i, Z_one_bits n 0 i = nil.
Proof.
  induction n; intros; simpl; auto.
Qed.

Remark Z_one_bits_two_p:
  forall n x i,
  0 <= x < Z_of_nat n ->
  Z_one_bits n (two_p x) i = (i + x) :: nil.
Proof.
  induction n; intros; simpl. simpl in H. omegaContradiction.
  rewrite inj_S in H. 
  assert (x = 0 \/ 0 < x) by omega. destruct H0.
  subst x; simpl. decEq. omega. apply Z_one_bits_zero.
  replace (two_p x) with (Z_shift_add false (two_p (x-1))).
  rewrite Z_bin_decomp_shift_add.
  replace (i + x) with ((i + 1) + (x - 1)) by omega. 
  apply IHn. omega.
  unfold Z_shift_add. rewrite <- two_p_S. decEq; omega. omega.
Qed.


Lemma is_power2_two_p:
  forall n, 0 <= n < Z_of_nat wordsize ->
  is_power2 (repr (two_p n)) = Some (repr n).
Proof.
  intros. unfold is_power2. rewrite unsigned_repr. 
  rewrite Z_one_bits_two_p. auto. auto.
  apply two_p_range. auto.
Qed.


Theorem mul_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  mul x n = shl x logn.
Proof.
  intros. generalize (@is_power2_correct n logn H); intro.
  rewrite shl_mul_two_p. rewrite <- H0. rewrite repr_unsigned.
  auto.
Qed.


Lemma Z_of_bits_shift_rev:
  forall n f,
  (forall i, i >= Z_of_nat n -> f i = false) ->
  Z_of_bits n f = Z_shift_add (f 0) (Z_of_bits n (fun i => f(i + 1))).
Proof.
  induction n; intros.
  simpl. rewrite H. reflexivity. unfold Z_of_nat. omega.
  simpl. rewrite (IHn (fun i => f (i + 1))).
  reflexivity. 
  intros. apply H. rewrite inj_S. omega.
Qed.

Lemma Z_of_bits_shifts_rev:
  forall m f,
  0 <= m ->
  (forall i, i >= Z_of_nat wordsize -> f i = false) ->
  exists k,
  Z_of_bits wordsize f = k + two_p m * Z_of_bits wordsize (fun i => f(i + m))
  /\ 0 <= k < two_p m.
Proof.
  intros. pattern m. apply natlike_ind.
  exists 0. change (two_p 0) with 1. split.
  transitivity (Z_of_bits wordsize (fun i => f (i + 0))).
  apply Z_of_bits_exten. intros. decEq. omega.
  omega. omega.
  intros x POSx [k [EQ1 RANGE1]].
  set (f' := fun i => f (i + x)) in *.
  assert (forall i, i >= Z_of_nat wordsize -> f' i = false).
  intros. unfold f'. apply H0. omega.  
  generalize (Z_of_bits_shift_rev wordsize f' H1). intro.
  rewrite EQ1. rewrite H2. 
  set (z := Z_of_bits wordsize (fun i => f (i + Zsucc x))).
  replace (Z_of_bits wordsize (fun i => f' (i + 1))) with z.
  rewrite two_p_S.
  case (f' 0); unfold Z_shift_add.
  exists (k + two_p x). split. ring. omega. 
  exists k. split. ring. omega.
  auto. 
  unfold z. apply Z_of_bits_exten; intros. unfold f'.
  decEq. omega. 
  auto.
Qed.

Lemma shru_div_two_p:
  forall x y,
  shru x y = repr (unsigned x / two_p (unsigned y)).
Proof.
  intros. unfold shru. 
  set (x' := unsigned x). set (y' := unsigned y).
  elim (@Z_of_bits_shifts_rev y' (bits_of_Z wordsize x')).
  intros k [EQ RANGE].
  replace (Z_of_bits wordsize (bits_of_Z wordsize x')) with x' in EQ.
  rewrite Zplus_comm in EQ. rewrite Zmult_comm in EQ.
  generalize (Zdiv_unique _ _ _ _ EQ RANGE). intros.
  rewrite H. auto.
  apply eqm_small_eq. apply eqm_sym. apply Z_of_bits_of_Z. 
  unfold x'. apply unsigned_range. 
  auto with ints.
  generalize (unsigned_range y). unfold y'. omega.
  intros. apply bits_of_Z_above. auto.
Qed.

Theorem shru_zero:
  forall x, shru x zero = x.
Proof.
  intros. rewrite shru_div_two_p. change (two_p (unsigned zero)) with 1.
  transitivity (repr (unsigned x)). decEq. apply Zdiv_unique with 0.
  omega. omega. auto with ints.
Qed.

Theorem shr_zero:
  forall x, shr x zero = x.
Proof.
  intros. unfold shr. change (two_p (unsigned zero)) with 1.
  replace (signed x / 1) with (signed x).
  apply repr_signed.
  symmetry. apply Zdiv_unique with 0. omega. omega. 
Qed.


Theorem divu_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  divu x n = shru x logn.
Proof.
  intros. generalize (@is_power2_correct n logn H). intro.
  symmetry. unfold divu. rewrite H0. apply shru_div_two_p.
Qed.


Lemma modu_divu_Euclid:
  forall x y, y <> zero -> x = add (mul (divu x y) y) (modu x y).
Proof.
  intros. unfold add, mul, divu, modu.
  transitivity (repr (unsigned x)). auto with ints. 
  apply eqm_samerepr. 
  set (x' := unsigned x). set (y' := unsigned y).
  apply eqm_trans with ((x' / y') * y' + x' mod y').
  apply eqm_refl2. rewrite Zmult_comm. apply Z_div_mod_eq.
  generalize (unsigned_range y); intro.
  assert (unsigned y <> 0). red; intro. 
  elim H. rewrite <- (repr_unsigned y). unfold zero. congruence.
  unfold y'. omega.
  auto with ints.
Qed.

Theorem modu_divu:
  forall x y, y <> zero -> modu x y = sub x (mul (divu x y) y).
Proof.
  intros. 
  assert (forall a b c, a = add b c -> c = sub a b).
  intros. subst a. rewrite sub_add_l. rewrite sub_idem.
  rewrite add_commut. rewrite add_zero. auto.
  apply H0. apply modu_divu_Euclid. auto.
Qed.

Theorem mods_divs:
  forall x y, mods x y = sub x (mul (divs x y) y).
Proof.
  intros; unfold mods, sub, mul, divs.
  apply eqm_samerepr.
  unfold Zmod_round.
  apply eqm_sub. apply eqm_signed_unsigned. 
  apply eqm_unsigned_repr_r. 
  apply eqm_mult. auto with ints. apply eqm_signed_unsigned.
Qed.


Theorem divs_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  divs x n = shrx x logn.
Proof.
  intros. generalize (@is_power2_correct _ _ H); intro.
  unfold shrx. rewrite shl_mul_two_p.
  rewrite mul_commut. rewrite mul_one.
  rewrite <- H0. rewrite repr_unsigned. auto.
Qed.

Theorem shrx_carry:
  forall x y,
  add (shr x y) (shr_carry x y) = shrx x y.
Proof.
  intros. unfold shr_carry. 
  rewrite sub_add_opp. rewrite add_permut. 
  rewrite add_neg_zero. apply add_zero.
Qed.

Lemma Zdiv_round_Zdiv:
  forall x y,
  y > 0 ->
  Zdiv_round x y = if zlt x 0 then (x + y - 1) / y else x / y.
Proof.
  intros. unfold Zdiv_round.
  destruct (zlt x 0). 
  rewrite zlt_false; try omega.
  generalize (Z_div_mod_eq (-x) y H).
  generalize (Z_mod_lt (-x) y H).
  set (q := (-x) / y). set (r := (-x) mod y). intros.
  symmetry.
  apply Zdiv_unique with (y - r - 1).
  replace x with (- (y * q) - r) by omega.
  replace (-(y * q)) with ((-q) * y) by ring.
  omega.
  omega.
  apply zlt_false. omega.
Qed.

Lemma shrx_shr_trivial_case:
  forall x y,
  (wordsize_minus_one = 0)%nat ->
  ltu y (repr (Z_of_nat wordsize - 1)) = true ->
  shrx x y =
  shr (if lt x zero then add x (sub (shl one y) one) else x) y.
Proof.
  intros.
  unfold shrx, divs, shr. decEq.
  exploit int_ltu_inv; eauto. 
  replace (unsigned (repr (Z_of_nat wordsize - 1))) with (Z_of_nat wordsize - 1).
  set (uy := unsigned y).
  unfold wordsize in H0. rewrite H in H0. simpl in H0. 
  assert (0 <= unsigned y < unsigned (repr 0)). apply int_ltu_inv. exact H0.
  rewrite unsigned_repr in H1.
  assert (unsigned y = 0). omega. intuition. 
  assert (max_unsigned > 0). auto with *. omega. rewrite unsigned_repr. trivial.
  split. unfold wordsize. rewrite inj_S. auto with *. 
  assert (Z_of_nat wordsize <= max_unsigned). unfold max_unsigned, modulus.
  apply two_power_nat_increases. omega.
Qed.

Theorem shrx_shr:
  forall x y,
  ltu y (repr (Z_of_nat wordsize - 1)) = true ->
  shrx x y =
  shr (if lt x zero then add x (sub (shl one y) one) else x) y.
Proof.
  assert (wordsize_minus_one = 0 \/ wordsize_minus_one > 0)%nat.
  omega. destruct H. intros. apply shrx_shr_trivial_case. exact H. exact H0.
  intros. unfold shrx, divs, shr. decEq.
  exploit int_ltu_inv; eauto. 
  replace (unsigned (repr (Z_of_nat wordsize - 1))) with (Z_of_nat wordsize - 1).
  set (uy := unsigned y).
  intro RANGE.
  assert (shl one y = repr (two_p uy)).
    transitivity (mul one (repr (two_p uy))).
    symmetry. apply mul_pow2. replace y with (repr uy). 
    apply is_power2_two_p. omega. unfold uy. apply repr_unsigned.
    rewrite mul_commut. apply mul_one.
  assert (two_p uy > 0). apply two_p_gt_ZERO. omega.
  assert (two_p uy <= two_p (Z_of_nat wordsize - 2)).
    apply two_p_monotone. omega.
  assert (two_p (Z_of_nat wordsize - 2) <= max_unsigned).
    assert (two_p (Z_of_nat wordsize - 1) <= max_unsigned).
    unfold max_unsigned, modulus, wordsize.
    set (wmo := wordsize_minus_one).
    rewrite inj_S. change (Zsucc (Z_of_nat wmo)) with (Z_of_nat wmo + 1).
    replace (Z_of_nat wmo + 1 -1) with (Z_of_nat wmo).
    rewrite <-two_power_nat_two_p. rewrite two_power_nat_S.
    assert (two_power_nat wmo > 0). apply two_power_nat_pos. omega. omega. 
    assert (two_p (Z_of_nat wordsize -2) <= two_p (Z_of_nat wordsize - 1)).
    apply two_p_monotone. omega. omega. 
  assert (unsigned (shl one y) = two_p uy).
    rewrite H1. apply unsigned_repr.
    assert (two_p (Z_of_nat wordsize - 2) <= max_unsigned).
    assert (two_p (Z_of_nat wordsize - 1) <= max_unsigned).
    unfold max_unsigned, modulus, wordsize.
    set (wmo := wordsize_minus_one).
    rewrite inj_S. change (Zsucc (Z_of_nat wmo)) with (Z_of_nat wmo + 1).
    replace (Z_of_nat wmo + 1 -1) with (Z_of_nat wmo).
    rewrite <-two_power_nat_two_p. rewrite two_power_nat_S.
    assert (two_power_nat wmo > 0). apply two_power_nat_pos. omega. omega. 
    assert (two_p (Z_of_nat wordsize -2) <= two_p (Z_of_nat wordsize - 1)).
    apply two_p_monotone. omega. omega. 
    omega.
  assert (two_p (Z_of_nat wordsize - 2) <= max_signed).
    unfold max_signed, half_modulus, modulus, wordsize. 
    set (wmo := wordsize_minus_one).
    rewrite inj_S. change (Zsucc (Z_of_nat wmo)) with (Z_of_nat wmo + 1).
    replace (Z_of_nat wmo + 1 -1) with (Z_of_nat wmo).
    set (wmo_pred := (wordsize_minus_one -1)%nat).
    assert (wmo = S (wmo_pred)). unfold wmo_pred, wmo. omega.
    replace (Z_of_nat wmo + 1 -2) with (Z_of_nat (wmo_pred)).
    rewrite <-two_power_nat_two_p. rewrite two_power_nat_S.
    assert (two_power_nat wmo > 0). apply two_power_nat_pos. 
    rewrite Zmult_comm. rewrite Z_div_mult.
    rewrite H6. rewrite two_power_nat_S. assert (two_power_nat wmo_pred > 0).
    apply two_power_nat_pos. omega. omega. omega. omega.
  assert (signed (shl one y) = two_p uy).
    rewrite H1. apply signed_repr. 
    split. apply Zle_trans with 0. assert (min_signed < 0). auto with ints.
    omega. omega. omega.
  rewrite H7. 
  rewrite Zdiv_round_Zdiv; auto.
  unfold lt. replace (signed zero) with 0. 
  destruct (zlt (signed x) 0); auto.
  rewrite add_signed.
  assert (unsigned one = 1).  apply unsigned_one.
    
  assert (signed (sub (shl one y) one) = two_p uy - 1).
    unfold sub. rewrite <-H7. rewrite signed_repr. 
    replace (unsigned one) with 1. omega.
    rewrite H8.
    split. apply Zle_trans with 0. assert (min_signed < 0). 
    apply min_signed_lt_0. auto with *. 
    rewrite H5. omega. rewrite H5. omega. rewrite H9. 
  rewrite signed_repr. decEq. omega.
  generalize (signed_range x). intros. 
  assert (two_p uy - 1 <= max_signed). omega. omega. unfold zero.
  rewrite signed_repr. trivial.
  assert (min_signed < 0). apply min_signed_lt_0. auto with *.
  rewrite unsigned_repr. trivial.
  assert (Z_of_nat wordsize <= max_unsigned). unfold max_unsigned, modulus.
  apply two_power_nat_increases.
  split. unfold wordsize. rewrite inj_S.
  change (Zsucc (Z_of_nat wordsize_minus_one)) with (Z_of_nat wordsize_minus_one + 1).
  replace (Z_of_nat wordsize_minus_one + 1 -1) with (Z_of_nat wordsize_minus_one).
  auto with *. omega. omega.
Qed.

Lemma add_and:
  forall x y z,
  and y z = zero ->
  add (and x y) (and x z) = and x (or y z).
Proof.
  intros. unfold add, and, bitwise_binop. 
  decEq.
  repeat rewrite unsigned_repr; auto with ints.
  apply Z_of_bits_excl; intros.
  assert (forall a b c, a && b && (a && c) = a && (b && c)).
    destruct a; destruct b; destruct c; reflexivity.
  rewrite H1. 
  replace (bits_of_Z wordsize (unsigned y) i &&
           bits_of_Z wordsize (unsigned z) i)
     with (bits_of_Z wordsize (unsigned (and y z)) i).
  rewrite H. change (unsigned zero) with 0. 
  rewrite bits_of_Z_zero. apply andb_b_false.
  unfold and, bitwise_binop. 
  rewrite unsigned_repr; auto with ints. rewrite bits_of_Z_of_bits. 
  reflexivity. auto. 
  rewrite <- demorgan1.
  unfold or, bitwise_binop. 
  rewrite unsigned_repr; auto with ints. rewrite bits_of_Z_of_bits; auto.
Qed.

Remark modu_and_masks_1:
  forall logn, 0 <= unsigned logn < Z_of_nat wordsize ->
  rol (shru mone logn) logn = shl mone logn.
Proof.
  assert (0 < Z_of_nat wordsize). unfold wordsize. rewrite inj_S. omega.
  intros. 
  unfold rol, shru, shl. decEq. apply Z_of_bits_exten. intros.
  rewrite unsigned_repr. rewrite bits_of_Z_of_bits.
  assert (unsigned logn = unsigned logn mod Z_of_nat wordsize).
  rewrite Zmod_small. trivial. exact H0. set (W:= Z_of_nat wordsize).
  assert ((z - unsigned logn) < 0 \/ (z - unsigned logn) >= 0).
  omega. 
  elim H3; intros. rewrite bits_of_Z_above. rewrite bits_of_Z_below. trivial.
  exact H4. assert ((z - unsigned logn) mod W >= W - unsigned logn).
  assert (z - unsigned logn = - (unsigned logn - z)). omega. rewrite H5.
  rewrite Z_mod_nz_opp_full. rewrite Zmod_small.
  omega. split. auto with zarith. unfold W. auto with zarith. 
  rewrite Zmod_eq. assert (unsigned logn - z < W) as L1. unfold W. auto with zarith. 
  assert ((unsigned logn - z) / W < 1) as L2. apply Zdiv_lt_upper_bound. auto with zarith. 
  unfold W. auto with zarith. auto with zarith. 
  assert (0 <= (unsigned logn - z) / W) as L3. apply Zdiv_le_lower_bound. auto with zarith.
  unfold W. auto with zarith. auto with zarith.
  assert ((unsigned logn - z) / W = 0) as L4. auto with zarith. rewrite L4. auto with *.
  unfold W. auto with zarith. fold W. omega.
  assert (((z - unsigned logn) mod W + unsigned logn) = 
    ((z - unsigned logn) mod W + unsigned logn) mod W). symmetry.
  rewrite Zmod_small. trivial. rewrite Zmod_small. unfold W. omega.
  unfold W. omega. rewrite H5. rewrite Zplus_mod_idemp_l.
  replace (z - unsigned logn + unsigned logn) with z. rewrite Zmod_small. 
  rewrite mone_max_unsigned. rewrite unsigned_repr. unfold max_unsigned, modulus.
  repeat rewrite bits_of_Z_mone. trivial. omega. exact H1. auto with *.
  unfold W. exact H1. omega.
  apply Z_mod_lt. exact modulus_pos.
  apply Z_of_bits_range_2.
Qed.

Remark modu_and_masks_2:
  forall logn, 0 <= unsigned logn < Z_of_nat wordsize ->
  and (shl mone logn) (sub (repr (two_p (unsigned logn))) one) = zero.
Proof.
  intros. 
  assert (0 <= 1 <= max_unsigned) as L0.
  split. exact max_unsigned_geq_zero.
  unfold max_unsigned, modulus, wordsize. rewrite two_power_nat_S.
  assert (two_power_nat wordsize_minus_one > 0). apply two_power_nat_pos. 
  omega. 
  assert (two_p (unsigned logn) > 0) as L1. apply two_p_gt_ZERO. apply H.
  assert (0 <= two_p (unsigned logn) <= max_unsigned) as L2.
  split. auto with zarith.
  unfold max_unsigned, modulus, wordsize. 
  rewrite two_power_nat_two_p. rewrite inj_S. rewrite two_p_S.
  assert (two_p (unsigned logn) <= two_p (Z_of_nat wordsize_minus_one)).
  apply two_p_monotone. unfold wordsize in H. rewrite inj_S in H. auto with zarith. 
  omega. auto with zarith.
  unfold and, shl, sub. unfold bitwise_binop. unfold zero. decEq.
  transitivity (Z_of_bits wordsize (bits_of_Z wordsize 0)).
  apply Z_of_bits_exten. intros. rewrite bits_of_Z_zero. unfold one.
  repeat rewrite unsigned_repr. 
  set (y := Z_of_nat wordsize - unsigned logn).
  assert (unsigned logn = Z_of_nat wordsize - y). unfold y. omega.
  rewrite H1.
  assert (y = unsigned (repr y)). rewrite unsigned_repr.  trivial.
  assert (Z_of_nat wordsize <= max_unsigned). unfold max_unsigned, modulus.
  apply two_power_nat_increases. omega.
  rewrite H2.
  assert (z < Z_of_nat wordsize - y \/ z >= Z_of_nat wordsize - y). omega.
  elim H3; intros.
  rewrite bits_of_Z_of_bits.
  rewrite mone_max_unsigned. rewrite unsigned_repr. unfold max_unsigned, modulus.
  rewrite bits_of_Z_below. apply andb_false_l. rewrite <-H2. omega. auto with *.
  exact H0.
  rewrite shru_shl_and_2_helper2. apply andb_false_r. rewrite <-H2. omega.
  rewrite <-H2. exact H4.
  exact L0. exact L2. omega. exact L0. exact L2. apply Z_of_bits_range_2.
  apply Z_of_bits_of_Z_lt_modulus. unfold modulus. split. auto with zarith. 
  assert (two_power_nat wordsize > 0). 
  apply two_power_nat_pos. omega. 
Qed.

Remark modu_and_masks_3:
  forall logn, 0 <= unsigned logn < Z_of_nat wordsize ->
  or (shl mone logn) (sub (repr (two_p (unsigned logn))) one) = mone.
Proof.
  intros.
  assert (0 <= 1 <= max_unsigned) as L0.
  split. exact max_unsigned_geq_zero.
  unfold max_unsigned, modulus, wordsize. rewrite two_power_nat_S.
  assert (two_power_nat wordsize_minus_one > 0). apply two_power_nat_pos. 
  omega. 
  assert (two_p (unsigned logn) > 0) as L1. apply two_p_gt_ZERO. apply H.
  assert (0 <= two_p (unsigned logn) <= max_unsigned) as L2.
  split. auto with zarith.
  unfold max_unsigned, modulus, wordsize. 
  rewrite two_power_nat_two_p. rewrite inj_S. rewrite two_p_S.
  assert (two_p (unsigned logn) <= two_p (Z_of_nat wordsize_minus_one)).
  apply two_p_monotone. unfold wordsize in H. rewrite inj_S in H. auto with zarith. 
  omega. auto with zarith.
  unfold or, shl, sub, bitwise_binop. symmetry. rewrite mone_max_unsigned. symmetry.
  decEq. transitivity (Z_of_bits wordsize (bits_of_Z wordsize max_unsigned)).
  apply Z_of_bits_exten. intros. rewrite bits_of_Z_mone.
  repeat rewrite unsigned_repr. rewrite bits_of_Z_of_bits.
  set (y := Z_of_nat wordsize - unsigned logn).
  assert (unsigned logn = Z_of_nat wordsize - y). unfold y. omega.
  rewrite H1.
  assert (z < Z_of_nat wordsize - y \/ z >= Z_of_nat wordsize - y). omega.
  elim H2; intros. unfold one. rewrite unsigned_repr.
  assert (y = unsigned (repr y)). rewrite unsigned_repr.  trivial.
  assert (Z_of_nat wordsize <= max_unsigned). unfold max_unsigned, modulus.
  apply two_power_nat_increases. omega. rewrite H4.
  rewrite shru_shl_and_2_helper1. apply orb_true_r.
  rewrite <-H4. unfold y. omega. omega. exact L0.
  unfold max_unsigned. unfold modulus. rewrite bits_of_Z_mone. apply orb_true_l.
  omega. exact H0. exact L2. unfold one. rewrite unsigned_repr. omega. exact L0.
  apply L2. auto with *. apply Z_of_bits_range_2. auto with *. exact H0.
  rewrite Z_of_bits_of_Z_lt_modulus. trivial. split. auto with ints. 
  unfold max_unsigned. auto with zarith.
Qed.

Theorem modu_and:
  forall x n logn,
  is_power2 n = Some logn ->
  modu x n = and x (sub n one).
Proof.
  assert (Z_of_nat wordsize <= max_unsigned) as L0. unfold max_unsigned, modulus.
  apply two_power_nat_increases.
  intros. generalize (@is_power2_correct _ _ H); intro.
  generalize (@is_power2_rng _ _ H); intro.
  assert (n <> zero). 
    red; intro. subst n. change (unsigned zero) with 0 in H0.
    assert (two_p (unsigned logn) > 0). apply two_p_gt_ZERO. omega.
    omegaContradiction.
  generalize (@modu_divu_Euclid x n H2); intro.
  assert (forall a b c, add a b = add a c -> b = c).
    intros. assert (sub (add a b) a = sub (add a c) a). congruence.
    repeat rewrite sub_add_l in H5. repeat rewrite sub_idem in H5.
    rewrite add_commut in H5; rewrite add_zero in H5.
    rewrite add_commut in H5; rewrite add_zero in H5.
    auto.
  apply H4 with (mul (divu x n) n).
  rewrite <- H3. 
  rewrite (@divu_pow2 x n logn H). 
  rewrite (@mul_pow2 (shru x logn) n logn H). 
  rewrite shru_rolm. rewrite shl_rolm. rewrite rolm_rolm_weak_2.
  rewrite sub_add_opp. rewrite add_assoc. 
  replace (add (neg logn) logn) with zero.
  rewrite add_zero.
  replace (modu (repr (Z_of_nat wordsize)) (repr (Z_of_nat wordsize)))
    with zero.
  rewrite rolm_zero. 
  symmetry.
  replace n with (repr (two_p (unsigned logn))).
  rewrite modu_and_masks_1; auto.
  rewrite and_idem.
  rewrite add_and. rewrite modu_and_masks_3; auto. apply and_mone.
  apply modu_and_masks_2; auto.
  transitivity (repr (unsigned n)). decEq. auto. auto with ints.
  unfold modu. repeat rewrite unsigned_repr_wordsize. rewrite Z_mod_same_full.
  fold zero. trivial.
  rewrite add_commut. rewrite add_neg_zero. auto.
  unfold sub. rewrite unsigned_repr_wordsize. rewrite unsigned_repr.
  omega. omega.
  unfold ltu. apply zlt_true. rewrite unsigned_repr_wordsize. apply H1.
  unfold ltu. apply zlt_true. rewrite unsigned_repr_wordsize. apply H1.
Qed.

(** ** Properties of integer zero extension and sign extension. *)

Section EXTENSIONS.

Variable n: Z.
Hypothesis RANGE: 0 < n < Z_of_nat wordsize.

Remark two_p_n_pos:
  two_p n > 0.
Proof. apply two_p_gt_ZERO. omega. Qed.


Remark two_p_n_range:
  0 <= two_p n <= max_unsigned.
Proof. apply two_p_range. omega. Qed.

Remark two_p_n_range':
  two_p n <= max_signed + 1.
Proof. 
  assert (two_p n <= two_p (Z_of_nat wordsize - 1)).
  apply two_p_monotone. omega. 
  assert (two_p (Z_of_nat wordsize - 1) = max_signed + 1).
  unfold max_signed, half_modulus, modulus, wordsize. 
  rewrite two_power_nat_S. rewrite Zmult_comm. rewrite Z_div_mult.
  rewrite inj_S.
  rewrite two_power_nat_two_p.
  change (Zsucc (Z_of_nat wordsize_minus_one)) with (Z_of_nat wordsize_minus_one + 1). 
  replace (Z_of_nat wordsize_minus_one + 1 -1) with (Z_of_nat wordsize_minus_one). 
  omega. omega. omega. rewrite <-H0.
  exact H.
Qed.



Remark unsigned_repr_two_p:
  unsigned (repr (two_p n)) = two_p n.
Proof.
  apply unsigned_repr. apply two_p_n_range. 
Qed.



Theorem zero_ext_and:
  forall x, zero_ext n x = and x (repr (two_p n - 1)).
Proof.
  intros; unfold zero_ext.
  assert (is_power2 (repr (two_p n)) = Some (repr n)).
    apply is_power2_two_p. omega.
  generalize (@modu_and x _ _ H).
  unfold modu. rewrite unsigned_repr_two_p. intro. rewrite H0. 
  decEq. unfold sub. decEq. rewrite unsigned_repr_two_p.
  rewrite unsigned_one. trivial.
Qed.


Theorem zero_ext_idem:
  forall x, zero_ext n (zero_ext n x) = zero_ext n x.
Proof.
  intros. repeat rewrite zero_ext_and. 
  rewrite and_assoc. rewrite and_idem. auto.
Qed.


Lemma eqm_eqmod_two_p:
  forall a b, eqm a b -> eqmod (two_p n) a b.
Proof.
  intros a b [k EQ].
  exists (k * two_p (Z_of_nat wordsize - n)).
  rewrite EQ. decEq. rewrite <- Zmult_assoc. decEq.
  rewrite <- two_p_is_exp. unfold modulus. rewrite two_power_nat_two_p.
  decEq. omega. omega. omega.
Qed.

Lemma sign_ext_charact:
  forall x y,
  -(two_p (n-1)) <= signed y < two_p (n-1) ->
  eqmod (two_p n) (unsigned x) (signed y) ->
  sign_ext n x = y.
Proof.
  intros. unfold sign_ext. set (x' := unsigned x) in *.
  destruct H0 as [k EQ].
  assert (two_p n = 2 * two_p (n - 1)). rewrite <- two_p_S. decEq. omega. omega.
  assert (signed y >= 0 \/ signed y < 0) by omega. destruct H1.
  assert (x' mod two_p n = signed y).
  apply Zmod_unique with k; auto. omega.
  rewrite zlt_true. rewrite H2. apply repr_signed. omega.
  assert (x' mod two_p n = signed y + two_p n).
  apply Zmod_unique with (k-1). rewrite EQ. ring. omega. 
  rewrite zlt_false. replace (x' mod two_p n - two_p n) with (signed y) by omega.
  apply repr_signed.
  omega.
Qed.

Lemma zero_ext_eqmod_two_p:
  forall x y,
  eqmod (two_p n) (unsigned x) (unsigned y) -> zero_ext n x = zero_ext n y.
Proof.
  intros. unfold zero_ext. decEq. apply eqmod_mod_eq. apply two_p_n_pos. auto.
Qed.

Lemma sign_ext_eqmod_two_p:
  forall x y,
  eqmod (two_p n) (unsigned x) (unsigned y) -> sign_ext n x = sign_ext n y.
Proof.
  intros. unfold sign_ext. 
  assert (unsigned x mod two_p n = unsigned y mod two_p n). 
  apply eqmod_mod_eq. apply two_p_n_pos. auto. 
  rewrite H0. auto.
Qed.

Lemma eqmod_two_p_zero_ext:
  forall x, eqmod (two_p n) (unsigned x) (unsigned (zero_ext n x)).
Proof.
  intros. unfold zero_ext. 
  apply eqmod_trans with (unsigned x mod two_p n).
  apply eqmod_mod. apply two_p_n_pos.
  apply eqm_eqmod_two_p. apply eqm_unsigned_repr. 
Qed.

Lemma eqmod_two_p_sign_ext:
  forall x, eqmod (two_p n) (unsigned x) (unsigned (sign_ext n x)).
Proof.
  intros. unfold sign_ext. destruct (zlt (unsigned x mod two_p n) (two_p (n-1))).
  apply eqmod_trans with (unsigned x mod two_p n).
  apply eqmod_mod. apply two_p_n_pos.
  apply eqm_eqmod_two_p. apply eqm_unsigned_repr. 
  apply eqmod_trans with (unsigned x mod two_p n).
  apply eqmod_mod. apply two_p_n_pos.
  apply eqmod_trans with (unsigned x mod two_p n - 0).
  apply eqmod_refl2. omega.
  apply eqmod_trans with (unsigned x mod two_p n - two_p n).
  apply eqmod_sub. apply eqmod_refl. exists (-1). ring.
  apply eqm_eqmod_two_p. apply eqm_unsigned_repr. 
Qed.

Theorem sign_ext_idem:
  forall x, sign_ext n (sign_ext n x) = sign_ext n x.
Proof.
  intros. apply sign_ext_eqmod_two_p. 
  apply eqmod_sym. apply eqmod_two_p_sign_ext.
Qed.

Theorem sign_ext_zero_ext:
  forall x, sign_ext n (zero_ext n x) = sign_ext n x.
Proof.
  intros. apply sign_ext_eqmod_two_p.
  apply eqmod_sym. apply eqmod_two_p_zero_ext.
Qed.

Theorem zero_ext_sign_ext:
  forall x, zero_ext n (sign_ext n x) = zero_ext n x.
Proof.
  intros. apply zero_ext_eqmod_two_p.
  apply eqmod_sym. apply eqmod_two_p_sign_ext.
Qed.

Theorem sign_ext_equal_if_zero_equal:
  forall x y,
  zero_ext n x = zero_ext n y ->
  sign_ext n x = sign_ext n y.
Proof.
  intros. rewrite <- (sign_ext_zero_ext x).
  rewrite <- (sign_ext_zero_ext y). congruence.
Qed.

Lemma eqmod_mult_div:
  forall n1 n2 x y,
  0 <= n1 -> 0 <= n2 ->
  eqmod (two_p (n1+n2)) (two_p n1 * x) y ->
  eqmod (two_p n2) x (y / two_p n1).
Proof.
  intros. rewrite two_p_is_exp in H1; auto. 
  destruct H1 as [k EQ]. exists k.
  change x with (0 / two_p n1 + x). rewrite <- Z_div_plus.
  replace (0 + x * two_p n1) with (two_p n1 * x) by ring.
  rewrite EQ. 
  replace (k * (two_p n1 * two_p n2) + y) with (y + (k * two_p n2) * two_p n1) by ring.
  rewrite Z_div_plus. ring. 
  apply two_p_gt_ZERO; auto.
  apply two_p_gt_ZERO; auto.
Qed.

Theorem sign_ext_shr_shl:
  forall x, 
  let y := repr (Z_of_nat wordsize - n) in
  sign_ext n x = shr (shl x y) y.
Proof.
  intros.
  assert (unsigned y = Z_of_nat wordsize - n).
    unfold y. apply unsigned_repr. 
    assert (Z_of_nat wordsize <= max_unsigned). 
    unfold max_unsigned, modulus. apply two_power_nat_increases. omega.
  apply sign_ext_charact.
  (* inequalities *)
  assert (two_power_nat wordsize_minus_one > 0). apply two_power_nat_pos.
  unfold shr. rewrite H. 
  set (z := signed (shl x y)).
  rewrite signed_repr. 
  apply Zdiv_interval_1.
  assert (two_p (n - 1) > 0). apply two_p_gt_ZERO. omega. omega.
  apply two_p_gt_ZERO. omega.
  apply two_p_gt_ZERO. omega.
  replace ((- two_p (n-1)) * two_p (Z_of_nat wordsize - n))
     with (- (two_p (n-1) * two_p (Z_of_nat wordsize - n))) by ring.
  rewrite <- two_p_is_exp.
  replace (n - 1 + (Z_of_nat wordsize - n)) with (Z_of_nat wordsize - 1) by omega.
  assert (min_signed <= z < max_signed + 1).
  generalize (signed_range (shl x y)). unfold z. omega. unfold wordsize.
  rewrite inj_S. set (wmo:= wordsize_minus_one). 
  change (Zsucc (Z_of_nat wmo)) with (Z_of_nat wmo + 1).
  replace (Z_of_nat wmo + 1 -1) with (Z_of_nat wmo).
  rewrite <-two_power_nat_two_p. 
  assert (- two_power_nat wmo = min_signed). unfold min_signed, half_modulus, modulus, wordsize. fold wmo. rewrite two_power_nat_S. 
  rewrite Zmult_comm. rewrite Z_div_mult. auto with *.
  omega. 
  assert (max_signed + 1 = two_power_nat wmo). 
  unfold max_signed, half_modulus, modulus, wordsize. fold wmo.
  rewrite two_power_nat_S. rewrite Zmult_comm. rewrite Z_div_mult.  omega.
  omega. auto with *. omega. omega. omega. 
  apply Zdiv_interval_3. unfold z. apply signed_range. assert (min_signed < 0). 
  auto with ints. omega. unfold max_signed, half_modulus, modulus, wordsize. 
  rewrite two_power_nat_S. rewrite Zmult_comm. rewrite Z_div_mult. auto with *.
auto with *. auto with *. 
  (* eqmod *)
  unfold shr. rewrite H. 
  apply eqmod_trans with (signed (shl x y) / two_p (Z_of_nat wordsize - n)).
  apply eqmod_mult_div. omega. omega. 
  replace (Z_of_nat wordsize - n + n) with (Z_of_nat wordsize) by omega.
  replace (eqmod (two_p (Z_of_nat wordsize))
     (two_p (Z_of_nat wordsize - n) * unsigned x) (signed (shl x y)))
  with (eqm (two_p (Z_of_nat wordsize - n) * unsigned x) (signed (shl x y))).
  rewrite shl_mul_two_p. unfold mul. rewrite H. 
  apply eqm_sym. eapply eqm_trans. apply eqm_signed_unsigned. 
  apply eqm_unsigned_repr_l. rewrite (Zmult_comm (unsigned x)). 
  apply eqm_mult. apply eqm_sym. apply eqm_unsigned_repr. apply eqm_refl. unfold eqm.
  unfold modulus. rewrite two_power_nat_two_p. trivial.
  apply eqm_eqmod_two_p. apply eqm_sym. eapply eqm_trans.
  apply eqm_signed_unsigned. apply eqm_sym. apply eqm_unsigned_repr. 
Qed.


Theorem zero_ext_shru_shl:
  forall x, 
  let y := repr (Z_of_nat wordsize - n) in
  zero_ext n x = shru (shl x y) y.
Proof.
  intros.
  assert (unsigned y = Z_of_nat wordsize - n).
    unfold y. apply unsigned_repr. 
    assert (Z_of_nat wordsize <= max_unsigned).  unfold max_unsigned, modulus.
    apply two_power_nat_increases.
    omega.
  rewrite zero_ext_and. symmetry. 
  replace n with (Z_of_nat wordsize - unsigned y).
  apply shru_shl_and. unfold ltu. apply zlt_true.
  rewrite H. rewrite unsigned_repr_wordsize.
  omega. omega.
Qed.

End EXTENSIONS.

(** ** Properties of [one_bits] (decomposition in sum of powers of two) *)

Opaque Z_one_bits. (* Otherwise, next Qed blows up! *)

Theorem one_bits_range:
  forall x i, In i (one_bits x) -> ltu i (repr (Z_of_nat wordsize)) = true.
Proof.
  intros. unfold one_bits in H.
  elim (list_in_map_inv _ _ _ H). intros i0 [EQ IN].
  subst i. unfold ltu. apply zlt_true. 
  generalize (Z_one_bits_range _ _ IN). intros.
  rewrite unsigned_repr. rewrite unsigned_repr_wordsize.
     intuition congruence. assert (Z_of_nat wordsize <= max_unsigned).
     unfold max_unsigned, modulus. apply two_power_nat_increases. omega.
Qed.

Fixpoint int_of_one_bits (l: list int) : int :=
  match l with
  | nil => zero
  | a :: b => add (shl one a) (int_of_one_bits b)
  end.


Theorem one_bits_decomp:
  forall x, x = int_of_one_bits (one_bits x).
Proof.
  intros. 
  transitivity (repr (powerserie (Z_one_bits wordsize (unsigned x) 0))).
  transitivity (repr (unsigned x)).
  auto with ints. decEq. apply Z_one_bits_powerserie.
  auto with ints.
  unfold one_bits. 
  generalize (Z_one_bits_range (unsigned x)).
  generalize (Z_one_bits wordsize (unsigned x) 0).
  induction l.
  intros; reflexivity.
  intros; simpl. rewrite <- IHl. unfold add. apply eqm_samerepr.
  apply eqm_add. rewrite shl_mul_two_p. rewrite mul_commut. 
  rewrite mul_one. apply eqm_unsigned_repr_r. 
  rewrite unsigned_repr. auto with ints.
  generalize (H a (in_eq _ _)). 
  assert (Z_of_nat wordsize <= max_unsigned).
  unfold max_unsigned, modulus. apply two_power_nat_increases. omega. 
  auto with ints.
  intros; apply H; auto with coqlib.
Qed.

(** ** Properties of comparisons *)

Theorem negate_cmp:
  forall c x y, cmp (negate_comparison c) x y = negb (cmp c x y).
Proof.
  intros. destruct c; simpl; try rewrite negb_elim; auto.
Qed.

Theorem negate_cmpu:
  forall c x y, cmpu (negate_comparison c) x y = negb (cmpu c x y).
Proof.
  intros. destruct c; simpl; try rewrite negb_elim; auto.
Qed.

Theorem swap_cmp:
  forall c x y, cmp (swap_comparison c) x y = cmp c y x.
Proof.
  intros. destruct c; simpl; auto. apply int_eq_sym. decEq. apply int_eq_sym.
Qed.

Theorem swap_cmpu:
  forall c x y, cmpu (swap_comparison c) x y = cmpu c y x.
Proof.
  intros. destruct c; simpl; auto. apply int_eq_sym. decEq. apply int_eq_sym.
Qed.

Lemma translate_eq:
  forall x y d,
  eq (add x d) (add y d) = eq x y.
Proof.
  intros. unfold eq. case (zeq (unsigned x) (unsigned y)); intro.
  unfold add. rewrite e. apply zeq_true.
  apply zeq_false. unfold add. red; intro. apply n. 
  apply eqm_small_eq; auto with ints.
  replace (unsigned x) with ((unsigned x + unsigned d) - unsigned d).
  replace (unsigned y) with ((unsigned y + unsigned d) - unsigned d).
  apply eqm_sub. apply eqm_trans with (unsigned (repr (unsigned x + unsigned d))).
  eauto with ints. apply eqm_trans with (unsigned (repr (unsigned y + unsigned d))).
  eauto with ints. eauto with ints. eauto with ints.
  omega. omega.
Qed.


Lemma translate_lt:
  forall x y d,
  min_signed <= signed x + signed d <= max_signed ->
  min_signed <= signed y + signed d <= max_signed ->
  lt (add x d) (add y d) = lt x y.
Proof.
  intros. repeat rewrite add_signed. unfold lt.
  repeat rewrite signed_repr; auto. case (zlt (signed x) (signed y)); intro.
  apply zlt_true. omega.
  apply zlt_false. omega.
Qed.



Theorem translate_cmp:
  forall c x y d,
  min_signed <= signed x + signed d <= max_signed ->
  min_signed <= signed y + signed d <= max_signed ->
  cmp c (add x d) (add y d) = cmp c x y.
Proof.
  intros. unfold cmp.
  rewrite translate_eq. repeat rewrite translate_lt; auto.
Qed.  



Theorem notbool_isfalse_istrue:
  forall x, is_false x -> is_true (notbool x).
Proof.
  unfold is_false, is_true, notbool; intros; subst x. 
  simpl. apply one_not_zero. 
Qed.


Theorem notbool_istrue_isfalse:
  forall x, is_true x -> is_false (notbool x).
Proof.
  unfold is_false, is_true, notbool; intros.
  generalize (eq_spec x zero). case (eq x zero); intro.
  contradiction. auto.
Qed.


Theorem shru_lt_zero:
  forall x,
  shru x (repr (Z_of_nat wordsize - 1)) = if lt x zero then one else zero.
Proof.
  intros. rewrite shru_div_two_p. 
  replace (two_p (unsigned (repr (Z_of_nat wordsize - 1))))
    with half_modulus.
  generalize (unsigned_range x); intro. 
  unfold lt. replace (signed zero) with 0. unfold signed. 
  destruct (zlt (unsigned x) half_modulus).
  rewrite zlt_false.
  replace (unsigned x / half_modulus) with 0. reflexivity. 
  symmetry. apply Zdiv_unique with (unsigned x). ring. omega. omega.
  rewrite zlt_true. 
  replace (unsigned x / half_modulus) with 1. reflexivity.
  symmetry. apply Zdiv_unique with (unsigned x - half_modulus). ring. 
  replace modulus with (2 * half_modulus) in H. omega.
  unfold half_modulus, modulus, wordsize. rewrite two_power_nat_S.
  replace (2 * two_power_nat wordsize_minus_one)
    with (two_power_nat wordsize_minus_one * 2).
  rewrite Z_div_mult. rewrite Zmult_comm. trivial. omega. rewrite Zmult_comm.
  trivial. omega. unfold zero. unfold signed. rewrite unsigned_repr. rewrite zlt_true.
  trivial. unfold half_modulus, modulus, wordsize. rewrite two_power_nat_S.
  rewrite Zmult_comm. rewrite Z_div_mult. assert (two_power_nat wordsize_minus_one > 0).  
  apply two_power_nat_pos. auto with *. omega.
  assert (max_unsigned > 0). auto with *. omega.
  unfold wordsize. rewrite inj_S. set (wmo := wordsize_minus_one). 
  change (Zsucc (Z_of_nat wmo)) with (Z_of_nat wmo + 1). 
  replace (Z_of_nat wmo + 1 -1) with (Z_of_nat wmo).
  rewrite unsigned_repr. unfold half_modulus, modulus, wordsize. fold wmo.
  rewrite two_power_nat_S. rewrite Zmult_comm. rewrite Z_div_mult.
  rewrite two_power_nat_two_p. trivial. omega. unfold max_unsigned, modulus.
  unfold wordsize. fold wmo. rewrite two_power_nat_S. 
  assert (Z_of_nat wmo <= two_power_nat wmo -1). apply two_power_nat_increases.
  omega. omega.
Qed.

(** * Def and properties of low_bits_zero *)
Definition low_bits_zero (x z:Z) := 
  forall i:Z, 0 <= i < z -> bits_of_Z wordsize x i = false.

Lemma shl_low_bits_zero : forall (z:Z) (x:int),
  z <= Z_of_nat wordsize -> low_bits_zero (unsigned (shl x (repr z))) z.
Proof. unfold low_bits_zero; intros. unfold shl.
  rewrite unsigned_repr2 by (apply Z_of_bits_range).
  rewrite bits_of_Z_of_bits.  
  rewrite bits_of_Z_below. trivial.
  rewrite unsigned_repr2. omega. 
  assert (Z_of_nat wordsize < modulus).
    unfold modulus. generalize (two_power_nat_increases wordsize). omega.
  omega. omega.
Qed.

Lemma and_low_bits_zero : forall z v1 v2,
  z <= Z_of_nat wordsize -> low_bits_zero (unsigned v2) z
    -> low_bits_zero (unsigned (and v1 v2)) z.
Proof. unfold low_bits_zero; intros. unfold and, bitwise_binop.
  rewrite unsigned_repr2 by (apply Z_of_bits_range).
  rewrite bits_of_Z_of_bits by omega.
  rewrite H0 by omega.
  apply andb_false_r.
Qed.

Lemma low_bits_zero_multiple : forall (k:nat) (z:Z),
  (k <= wordsize)%nat -> low_bits_zero z (Z_of_nat k)
    -> Zmod z (two_power_nat k) = 0.
Proof. induction k; intros.
  rewrite two_power_nat_O. rewrite Zmod_1_r. trivial.
  assert (bits_of_Z wordsize z 0 = false).
    apply H0. split. omega. 
    change 0 with (Z_of_nat 0)%nat. apply inj_lt; omega.
  unfold wordsize in H1.  apply last_bit_zero_imp_mult2 in H1.
  destruct H1 as [z' [H2 H4]].
  assert (low_bits_zero z' (Z_of_nat k)).
    unfold low_bits_zero; intros.
    rewrite <- (bits_of_Z_inc_width wordsize_minus_one wordsize).
    rewrite <- H4. apply H0. rewrite inj_S. omega.
    unfold wordsize in *.
    split. apply inj_le in H. rewrite inj_S in H. rewrite inj_S in H. omega. 
      rewrite inj_S. omega.
  apply IHk in H1. 
    apply Zmod_divides. generalize (two_power_nat_pos (S k)); omega.
    apply Zmod_divides in H1. destruct H1 as [c H1]. subst z'.
    rewrite Zmult_assoc in H2.
    rewrite <- two_power_nat_S in H2. exists c. trivial.
    generalize (two_power_nat_pos k); omega.
    omega.
Qed.

Lemma Z_bin_decomp_when_double: forall z z1,
  z = 2 * z1 -> Z_bin_decomp z = (false, z1).
Proof. intros.
  assert (z = Z_shift_add false z1). simpl. destruct z1; trivial.
  rewrite H0. apply Z_bin_decomp_shift_add.
Qed.

Lemma multiple_low_bits_zero : forall(k:nat) (z:Z),
  (k <= wordsize)%nat -> Zmod z (two_power_nat k) = 0
    -> low_bits_zero z (Z_of_nat k).
Proof. induction k. unfold low_bits_zero.  
  intros. contradict H1. simpl. omega.
  intros.
    assert (z = (two_power_nat (S k)) * (z / (two_power_nat (S k)))). 
      rewrite (Z_div_exact_full_2 z (two_power_nat (S k))) at 1. trivial.
      generalize (two_power_nat_pos (S k)). omega.
      assumption.
    assert (z = 2 * (two_power_nat k * (z / (two_power_nat (k+1))))).
      rewrite H1 at 1.
      rewrite two_power_nat_S at 1.
      replace (k+1)%nat with (S k). ring.
      omega.
    unfold low_bits_zero. intros.
    destruct H3.
    apply Zle_lt_or_eq in H3.
    assert (Z_bin_decomp z = (false, two_power_nat k * (z / two_power_nat (k+1)))).
      eapply Z_bin_decomp_when_double; eassumption.
    simpl. rewrite H5.
    destruct H3.
      assert (0 <= i-1 < Z_of_nat k). rewrite inj_S in H4. omega.
      assert (2 * (two_power_nat k * (z / two_power_nat (k + 1))) =
              (two_power_nat k * (2 * (z / two_power_nat (k + 1)))))
        by ring.
      rewrite zeq_false by omega.
      assert (low_bits_zero (two_power_nat k * (z / two_power_nat (k + 1)))
                (Z_of_nat k)).
        eapply IHk. omega.
          rewrite Zmult_comm. apply Z_mod_mult.
      assert (k <= wordsize_minus_one)%nat.
        unfold wordsize in H. omega.
      assert (i - 1 < Z_of_nat wordsize_minus_one <= Z_of_nat wordsize).
        unfold wordsize. split. omega. 
        apply inj_le. omega.
      erewrite (bits_of_Z_inc_width wordsize_minus_one) by eassumption.
      apply H8. omega.
    subst i. trivial.
Qed.

Lemma WordRing: ring_theory zero one add mul sub neg Logic.eq.
  constructor.
  apply zero_add.
  apply add_commut.
  intros.
    rewrite add_assoc. trivial.
  intros.
    rewrite mul_commut. apply mul_one.
  apply mul_commut.
  intros.
    rewrite mul_assoc. trivial.
  apply mul_add_distr_l.
  apply sub_add_opp.
  intros.
    rewrite <-sub_add_opp. apply sub_idem.
Qed.

Add Ring WordRing: WordRing.

End WORDSIZE.




Implicit Arguments add [wordsize_minus_one].
Implicit Arguments sub [wordsize_minus_one].
Implicit Arguments mul [wordsize_minus_one].
Implicit Arguments divs [wordsize_minus_one].
Implicit Arguments mods [wordsize_minus_one].
Implicit Arguments divu [wordsize_minus_one].
Implicit Arguments modu [wordsize_minus_one].
Implicit Arguments is_zero [wordsize_minus_one].
Implicit Arguments is_signed [wordsize_minus_one].
Implicit Arguments and [wordsize_minus_one].
Implicit Arguments or [wordsize_minus_one].
Implicit Arguments xor [wordsize_minus_one].
Implicit Arguments not [wordsize_minus_one].
Implicit Arguments shl [wordsize_minus_one].
Implicit Arguments shru [wordsize_minus_one].
Implicit Arguments shr [wordsize_minus_one].
Implicit Arguments shrx [wordsize_minus_one].
Implicit Arguments shr_carry [wordsize_minus_one].
Implicit Arguments rol [wordsize_minus_one].
Implicit Arguments ror [wordsize_minus_one].
Implicit Arguments rolm [wordsize_minus_one].
Implicit Arguments one_bits [wordsize_minus_one].
Implicit Arguments is_power2 [wordsize_minus_one].
Implicit Arguments cmp [wordsize_minus_one].
Implicit Arguments cmpu [wordsize_minus_one].
Implicit Arguments is_false [wordsize_minus_one].
Implicit Arguments is_true [wordsize_minus_one].
Implicit Arguments notbool [wordsize_minus_one].
Implicit Arguments repr [wordsize_minus_one].
Implicit Arguments unsigned [wordsize_minus_one].
Implicit Arguments signed [wordsize_minus_one].
Implicit Arguments unsigned_range [wordsize_minus_one].
Implicit Arguments zero [wordsize_minus_one].
Implicit Arguments one [wordsize_minus_one].
Implicit Arguments eq_dec [wordsize_minus_one].
Implicit Arguments lequ [wordsize_minus_one].
Implicit Arguments eq [wordsize_minus_one].
Implicit Arguments lt [wordsize_minus_one].
Implicit Arguments ltu [wordsize_minus_one].
Implicit Arguments and [wordsize_minus_one].
Implicit Arguments or [wordsize_minus_one].
Implicit Arguments xor [wordsize_minus_one].
Implicit Arguments unsigned_overflow [wordsize_minus_one].
Implicit Arguments signed_overflow [wordsize_minus_one].
Implicit Arguments unsigned_overflow_with_carry [wordsize_minus_one].
Implicit Arguments signed_overflow_with_carry [wordsize_minus_one].
Implicit Arguments bool_to_int [wordsize_minus_one].
Implicit Arguments neg [wordsize_minus_one].
End Word.

Definition int1 := Word.int 0.
Definition int4 := Word.int 3.
Definition int8 := Word.int 7.  
Definition int16 := Word.int 15.
Definition int32 := Word.int 31. 
Definition int64 := Word.int 63.


(** * Tactics for int *)

(** Convert operations on int32 to operations on Z *)
Hint Rewrite Word.int_eq_true_iff Word.int_eq_false_iff Word.int_eq_unsigned 
  Word.int_ltu_true_iff Word.int_ltu_false_iff
  Word.int_lequ_true_iff Word.int_lequ_false_iff : int_to_Z.
Ltac int_to_Z_tac :=  autorewrite with int_to_Z in *.


(** * Showing int32 is an ordered type *)

Require Import Coq.Structures.OrderedType.

(* Parameterize the following module by a size module would be ok for
   defining an OrderedType, but somehow omega won't fail for some simple
   situtions *)
Module Int32_OT <: OrderedType.

  Definition t := Word.int 31.
  Definition eq (x y: t) := Word.eq  x y = true.

  Lemma eq_refl : forall x : t, eq x x.
  Proof. unfold eq. apply Word.int_eq_refl. Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. unfold eq. intros. rewrite Word.int_eq_sym. trivial. Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. unfold eq. intros. int_to_Z_tac. omega. Qed.

  Definition lt (x y:t) := Word.ltu x y = true.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. unfold lt. intros. int_to_Z_tac. omega. Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. unfold lt, eq. intros. intro Hc. int_to_Z_tac.  omega. Qed.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof. unfold lt, eq; intros.
    destruct (Ztrichotomy_inf (Word.unsigned x)  (Word.unsigned y))
      as [[H|H]|H].
      apply LT. int_to_Z_tac. omega.
      apply EQ. int_to_Z_tac. omega.
      apply GT. int_to_Z_tac. omega.
  Qed.

  Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
    intros. case_eq (Word.eq x y); intros.
      left. unfold eq; int_to_Z_tac. omega.
      right. unfold eq; int_to_Z_tac. omega.
  Defined.
End Int32_OT.