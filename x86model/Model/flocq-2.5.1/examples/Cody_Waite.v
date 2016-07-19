Require Import Reals Fcore.
Require Import Gappa.Gappa_tactic Interval.Interval_tactic.

Open Scope R_scope.

Notation pow2 := (bpow radix2).
Definition mul x y := (round radix2 (FLT_exp (-1074) 53) ZnearestE (x * y)).
Definition sub x y := (round radix2 (FLT_exp (-1074) 53) ZnearestE (x - y)).

Definition Log2h := 3048493539143 * pow2 (-42).
Definition Log2l := 544487923021427 * pow2 (-93).
Definition InvLog2 := 3248660424278399 * pow2 (-51).

Lemma argument_reduction :
  forall x : R,
  generic_format radix2 (FLT_exp (-1074) 53) x ->
  Rabs x <= 710 ->
  let k := round radix2 (FIX_exp 0) ZnearestE (mul x InvLog2) in
  let tf := sub (sub x (mul k Log2h)) (mul k Log2l) in
  let te := x - k * ln 2 in
  Rabs tf <= 355 / 1024 /\
  Rabs (tf - te) <= 65537 * pow2 (-71).
Proof with auto with typeclass_instances.
intros x Fx Bx k tf te.
assert (Rabs x <= 5/16 \/ 5/16 <= Rabs x <= 710) as [Bx'|Bx'] by gappa.
- assert (k = 0).
    clear -Bx'.
    refine (let H := _ in Rle_antisym _ _ (proj2 H) (proj1 H)).
    unfold k, mul, InvLog2, Log2h ; gappa.
  unfold tf, te, mul, sub.
  rewrite H.
  rewrite 2!Rmult_0_l.
  rewrite round_0...
  rewrite Rmult_0_l.
  rewrite 2!Rminus_0_r.
  rewrite 2!round_generic with (2 := Fx)...
  gappa.
- assert (Hl: - 1 * pow2 (-102) <= Log2l - (ln 2 - Log2h) <= 0).
    unfold Log2l, Log2h ; simpl bpow ;
    interval with (i_prec 110).
  assert (Ax: x = x * InvLog2 * (1 / InvLog2)).
    field.
    unfold InvLog2 ; simpl ; interval.
  unfold te.
  replace (x - k * ln 2) with (x - k * Log2h - k * (ln 2 - Log2h)) by ring.
  revert Hl Ax.
  unfold tf, te, k, sub, mul, InvLog2, Log2h, Log2l ; gappa.
Qed.
