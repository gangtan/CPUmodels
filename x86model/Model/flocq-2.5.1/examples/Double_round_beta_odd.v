(** * Conditions for innocuous double rounding. *)

Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_generic_fmt.
Require Import Fcalc_ops.
Require Import Fcore_ulp.

Require Import Fappli_double_round.

Require Import Psatz.

Open Scope R_scope.

Section Double_round_beta_odd.

Variable beta : radix.
Notation bpow e := (bpow beta e).
Notation ln_beta x := (ln_beta beta x).

(** A little tactic to simplify terms of the form [bpow a * bpow b]. *)
Ltac bpow_simplify :=
  (* bpow ex * bpow ey ~~> bpow (ex + ey) *)
  repeat
    match goal with
      | |- context [(Fcore_Raux.bpow _ _ * Fcore_Raux.bpow _ _)] =>
        rewrite <- bpow_plus
      | |- context [(?X1 * Fcore_Raux.bpow _ _ * Fcore_Raux.bpow _ _)] =>
        rewrite (Rmult_assoc X1); rewrite <- bpow_plus
      | |- context [(?X1 * (?X2 * Fcore_Raux.bpow _ _) * Fcore_Raux.bpow _ _)] =>
        rewrite <- (Rmult_assoc X1 X2); rewrite (Rmult_assoc (X1 * X2));
        rewrite <- bpow_plus
    end;
  (* ring_simplify arguments of bpow *)
  repeat
    match goal with
      | |- context [(Fcore_Raux.bpow _ ?X)] =>
        progress ring_simplify X
    end;
  (* bpow 0 ~~> 1 *)
  change (Fcore_Raux.bpow _ 0) with 1;
  repeat
    match goal with
      | |- context [(_ * 1)] =>
        rewrite Rmult_1_r
    end.

Hypothesis Obeta : exists n, (beta = 2 * n + 1 :> Z)%Z.

Lemma midpoint_beta_odd_remains_pos :
  forall x,
  0 < x ->
  forall (ex1 ex2 : Z),
  (ex2 <= ex1)%Z ->
  x = Z2R (Zfloor (x * bpow (- ex1))) * bpow ex1 ->
  exists x',
    0 < x'
    /\ (ln_beta x' = ln_beta x :> Z)
    /\ x' = Z2R (Zfloor (x' * bpow (- ex2))) * bpow ex2
    /\ x + / 2 * bpow ex1 = x' + / 2 * bpow ex2.
Proof.
intros x Px ex1 ex2 Hf2.
set (z := (ex1 - ex2)%Z).
assert (Hz : Z_of_nat (Zabs_nat z) = z).
{ rewrite Zabs2Nat.id_abs.
  rewrite <- cond_Zopp_Zlt_bool; unfold cond_Zopp.
  assert (H : (z <? 0)%Z = false); [|now rewrite H].
  apply Zlt_bool_false; unfold z; omega. }
revert Hz.
generalize (Zabs_nat z); intro n.
unfold z; clear z; revert ex1 ex2 Hf2.
induction n.
- simpl.
  intros ex1 ex2 _ Hf1 Fx.
  exists x.
  assert (H : ex2 = ex1) by omega.
  split; [|split; [|split]].
  + exact Px.
  + reflexivity.
  + revert Fx; unfold generic_format, F2R, scaled_mantissa, canonic_exp; simpl.
    now rewrite H.
  + now unfold ulp, canonic_exp; rewrite H.
- intros ex1 ex2 Hf2 HSn Fx.
  destruct Obeta as (nb,Hb).
  assert (Hbeta : (2 <= beta)%Z).
  { destruct beta as (beta_val,beta_prop).
    now apply Zle_bool_imp_le. }
  assert (Nnnb : (1 <= nb)%Z) by omega.
  assert (Hf1 : (ex1 = ex2 + Z.of_nat n + 1 :> Z)%Z); [|clear HSn].
  { rewrite <- Zplus_assoc.
    replace (_ + 1)%Z with (Z.of_nat (S n)); [omega|].
    simpl.
    now rewrite Zpos_P_of_succ_nat. }
  assert (Hf2' : (ex2 + 1 <= ex1)%Z).
  { rewrite Hf1.
    rewrite <- Zplus_assoc.
    apply Zplus_le_compat_l.
    rewrite <- (Zplus_0_l 1) at 1; apply Zplus_le_compat_r.
    apply Zle_0_nat. }
  assert (Hd1 : Z.of_nat n = (ex1 - (ex2 + 1))%Z);
    [now rewrite Hf1; ring|].
  set (ex2' := (ex2 + 1)%Z).
  destruct (IHn ex1 ex2' Hf2' Hd1 Fx)
    as (x',(Px',(Hlx',(Fx',Hx')))); clear Hd1 IHn.
  set (u := bpow ex2).
  exists (x' + Z2R nb * u).
  split; [|split; [|split]].
  + apply (Rlt_le_trans _ _ _ Px').
    rewrite <- (Rplus_0_r x') at 1; apply Rplus_le_compat_l.
    apply Rmult_le_pos.
    * change 0 with (Z2R 0); apply Z2R_le; omega.
    * now apply bpow_ge_0.
  + rewrite <- Hlx'.
    apply (ln_beta_plus_eps beta (fun e => (e - (ln_beta x' - ex2'))%Z));
      [| |split].
    * exact Px'.
    * unfold generic_format, F2R, scaled_mantissa, canonic_exp; simpl.
      bpow_simplify.
      rewrite Ztrunc_floor; [exact Fx'|].
      now apply Rmult_le_pos; [apply Rlt_le|apply bpow_ge_0].
    * apply Rmult_le_pos; [|now apply bpow_ge_0].
      change 0 with (Z2R 0); apply Z2R_le; omega.
    * rewrite ulp_neq_0;[idtac| now apply Rgt_not_eq].
      unfold u, ex2', canonic_exp; bpow_simplify.
      rewrite Zplus_comm; rewrite bpow_plus.
      apply Rmult_lt_compat_r; [now apply bpow_gt_0|].
      rewrite bpow_1.
      apply Z2R_lt; omega.
  + rewrite Fx' at 1.
    unfold ex2' at 2.
    rewrite Zplus_comm; rewrite bpow_plus; fold u.
    rewrite <- Rmult_assoc; rewrite <- Rmult_plus_distr_r.
    apply Rmult_eq_compat_r.
    replace (Z2R _) with (x' * bpow (- ex2'));
      [|now apply (Rmult_eq_reg_r (bpow ex2'));
         [|now apply Rgt_not_eq; apply bpow_gt_0]; bpow_simplify].
    rewrite Rmult_plus_distr_r.
    unfold u, ex2'; bpow_simplify.
    rewrite Fx' at 2; unfold ex2'; bpow_simplify.
    rewrite bpow_1; rewrite <- Z2R_mult; rewrite <- Z2R_plus.
    rewrite Zfloor_Z2R.
    rewrite Z2R_plus.
    apply f_equal2; [|reflexivity].
    replace (- ex2 - 1)%Z with (- ex2')%Z; [|now unfold ex2'; ring].
    rewrite Fx' at 1; unfold ex2'; bpow_simplify.
    now rewrite Z2R_mult; rewrite <- bpow_1.
  + rewrite Hx'.
    rewrite Rplus_assoc; apply Rplus_eq_compat_l.
    rewrite <- Rmult_plus_distr_r.
    unfold ex2'; rewrite Zplus_comm; rewrite bpow_plus.
    rewrite <- Rmult_assoc; apply Rmult_eq_compat_r.
    rewrite (Rmult_eq_reg_l 2 _ (Z2R nb + / 2)); [reflexivity| |lra].
    field_simplify; apply Rmult_eq_compat_r.
    rewrite bpow_1; change 2 with (Z2R 2); change 1 with (Z2R 1).
    now rewrite <- Z2R_mult; rewrite <- Z2R_plus; apply f_equal.
Qed.

Lemma midpoint_beta_odd_remains :
  forall x,
  0 <= x ->
  forall (ex1 ex2 : Z),
  (ex2 <= ex1)%Z ->
  x = Z2R (Zfloor (x * bpow (- ex1))) * bpow ex1 ->
  exists x',
    0 <= x'
    /\ x' = Z2R (Zfloor (x' * bpow (- ex2))) * bpow ex2
    /\ x + / 2 * bpow ex1 = x' + / 2 * bpow ex2.
Proof.
intros x Px ex1 ex2 Hf2 Hx.
set (x1 := x + bpow ex1).
assert (Px1 : 0 < x1).
{ apply (Rle_lt_trans _ _ _ Px).
  rewrite <- (Rplus_0_r x); apply Rplus_lt_compat_l, bpow_gt_0. }
destruct (midpoint_beta_odd_remains_pos x1 Px1 ex1 ex2 Hf2)
  as (x',(Hx'1,(Hx'2,(Hx'3,Hx'4)))).
{ unfold x1 at 2.
  rewrite Rmult_plus_distr_r, Hx; bpow_simplify.
  change 1 with (Z2R 1); rewrite <- Z2R_plus.
  now rewrite Zfloor_Z2R, Z2R_plus, Rmult_plus_distr_r, Rmult_1_l, <- Hx. }
assert (Hx' : x' = x1 + / 2 * bpow ex1 - / 2 * bpow ex2).
{ rewrite Hx'4; ring. }
exists (x' - bpow ex1); split; [|split].
- rewrite Hx'; unfold x1; ring_simplify.
  replace (_ - _) with (x + (/ 2 * (bpow ex1 - bpow ex2))) by ring.
  apply Rplus_le_le_0_compat; [exact Px|]; apply Rmult_le_pos; [lra|].
  now apply Rle_0_minus, bpow_le.
- rewrite Rmult_minus_distr_r; rewrite Hx'3 at 2; bpow_simplify.
  rewrite <- (Z2R_Zpower beta (ex1 - ex2)); [|now apply Zle_minus_le_0].
  rewrite <- Z2R_minus, Zfloor_Z2R, Z2R_minus.
  rewrite (Z2R_Zpower beta (ex1 - ex2)); [|now apply Zle_minus_le_0].
  rewrite Rmult_minus_distr_r; bpow_simplify.
  now rewrite Hx'3 at 1.
- rewrite Hx'; unfold x1; ring.
Qed.

Lemma neq_midpoint_beta_odd_aux1 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (ln_beta x) <= fexp1 (ln_beta x))%Z ->
  midp beta fexp1 x - / 2 * ulp beta fexp2 x <= x < midp beta fexp1 x ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hx.
unfold midp in Hx.
rewrite 2!ulp_neq_0 in Hx; try now apply Rgt_not_eq.
unfold double_round_eq.
set (ex1 := fexp1 (ln_beta x)).
set (ex2 := fexp2 (ln_beta x)).
set (rx1 := round beta fexp1 Zfloor x).
assert (Prx1 : 0 <= rx1).
{ rewrite <- (round_0 beta fexp1 Zfloor).
  now apply round_le; [exact Vfexp1|apply valid_rnd_DN|apply Rlt_le]. }
assert (Hrx1 : rx1 = Z2R (Zfloor (rx1 * bpow (- ex1))) * bpow ex1).
{ unfold rx1 at 2; unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
  unfold ex1; bpow_simplify.
  now rewrite Zfloor_Z2R. }
destruct (midpoint_beta_odd_remains rx1 Prx1 ex1 ex2 Hf2f1 Hrx1)
  as (rx2,(Nnrx2, (Hrx2, Hrx12))).
assert (Hx' : rx2 <= x < rx2 + / 2 * bpow ex2).
{ split.
  - replace rx2 with (rx2 + / 2 * bpow ex2 - / 2 * bpow ex2) by ring.
    rewrite <- Hrx12; apply Hx.
  - rewrite <- Hrx12; apply Hx. }
assert (Hr2 : round beta fexp2 (Znearest choice2) x = rx2).
{ unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
  apply (Rmult_eq_reg_r (bpow (- fexp2 (ln_beta x))));
    [|now apply Rgt_not_eq, Rlt_gt, bpow_gt_0].
  bpow_simplify.
  rewrite (Znearest_imp _ _ (Zfloor (rx2 * bpow (- ex2)))).
  - now rewrite Hrx2 at 2; unfold ex2; bpow_simplify.
  - apply Rabs_lt; split.
    + apply Rlt_le_trans with 0; [lra|].
      apply Rle_0_minus.
      apply (Rmult_le_reg_r (bpow ex2)); [now apply bpow_gt_0|].
      fold ex2; bpow_simplify.
      now rewrite <- Hrx2.
    + apply (Rmult_lt_reg_r (bpow (fexp2 (ln_beta x)))); [now apply bpow_gt_0|].
      rewrite Rmult_minus_distr_r; fold ex2; bpow_simplify.
      rewrite <- Hrx2.
      now apply (Rplus_lt_reg_l rx2); ring_simplify. }
rewrite Hr2.
assert (Hrx2' : rx1 <= rx2 < rx1 + / 2 * bpow ex1).
{ split.
  - apply (Rplus_le_reg_r (/ 2 * bpow ex1)).
    rewrite Hrx12.
    apply Rplus_le_compat_l.
    apply Rmult_le_compat_l; [lra|].
    now apply bpow_le.
  - apply (Rle_lt_trans _ _ _ (proj1 Hx') (proj2 Hx)). }
assert (Hrx2r : rx2 = round beta fexp2 Zfloor x).
{ unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
  fold ex2; rewrite Hrx2.
  apply Rmult_eq_compat_r, f_equal.
  apply eq_sym, Zfloor_imp; split.
  - apply (Rle_trans _ _ _ (Zfloor_lb _)).
    now apply Rmult_le_compat_r; [apply bpow_ge_0|].
  - apply (Rmult_lt_reg_r (bpow ex2)); [now apply bpow_gt_0|]; bpow_simplify.
    rewrite Z2R_plus, Rmult_plus_distr_r, <- Hrx2.
    apply (Rlt_le_trans _ _ _ (proj2 Hx')).
    apply Rplus_le_compat_l, Rmult_le_compat_r; [apply bpow_ge_0|simpl; lra]. }
destruct (Rle_or_lt rx2 0) as [Nprx2|Prx2].
{ (* rx2 = 0 *)
  assert (Zrx2 : rx2 = 0); [now apply Rle_antisym|].
  rewrite Zrx2, round_0; [|now apply valid_rnd_N].
  unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
  apply (Rmult_eq_reg_r (bpow (- fexp1 (ln_beta x))));
    [|now apply Rgt_not_eq, bpow_gt_0]; rewrite Rmult_0_l; bpow_simplify.
  change 0 with (Z2R 0); apply f_equal, eq_sym, Znearest_imp.
  apply Rabs_lt; simpl; unfold Rminus; rewrite Ropp_0, Rplus_0_r.
  split.
  - apply Rlt_trans with 0; [lra|].
    now apply Rmult_lt_0_compat; [|apply bpow_gt_0].
  - apply (Rmult_lt_reg_r (bpow (fexp1 (ln_beta x)))); [now apply bpow_gt_0|].
    bpow_simplify.
    rewrite Zrx2, Rplus_0_l in Hx'.
    apply (Rlt_le_trans _ _ _ (proj2 Hx')), Rmult_le_compat_l; [lra|].
    now apply bpow_le. }
(* 0 < rx2 *)
assert (Hl2 : ln_beta rx2 = ln_beta x :> Z).
{ now rewrite Hrx2r; apply ln_beta_DN; [|rewrite <- Hrx2r]. }
assert (Hr12 : round beta fexp1 (Znearest choice1) rx2 = rx1).
{ unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
  rewrite Hl2; fold ex1.
  apply (Rmult_eq_reg_r (bpow (- ex1)));
    [|now apply Rgt_not_eq, bpow_gt_0]; bpow_simplify.
  unfold rx1, round, F2R, scaled_mantissa, canonic_exp; simpl.
  fold ex1; bpow_simplify.
  apply f_equal, Znearest_imp.
  apply Rabs_lt; split.
  - apply Rlt_le_trans with 0; [lra|apply Rle_0_minus].
    now apply (Rmult_le_reg_r (bpow ex1)); bpow_simplify; [apply bpow_gt_0|].
  - apply (Rmult_lt_reg_r (bpow ex1)); [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r; bpow_simplify.
    change (Z2R _ * _) with rx1.
    apply (Rplus_lt_reg_r rx1); ring_simplify.
    apply (Rlt_le_trans _ _ _ (proj2 Hrx2')), Rplus_le_compat_l.
    now apply Rmult_le_compat_l; [lra|right]. }
rewrite Hr12.
unfold rx1, round, F2R, scaled_mantissa, canonic_exp; simpl; fold ex1.
apply Rmult_eq_compat_r, f_equal, eq_sym, Znearest_imp, Rabs_lt; split.
- apply Rlt_le_trans with 0; [lra|]; apply Rle_0_minus, Zfloor_lb.
- apply (Rmult_lt_reg_r (bpow ex1)); [now apply bpow_gt_0|].
  rewrite Rmult_minus_distr_r; bpow_simplify.
  change (Z2R _ * _) with rx1.
  now apply (Rplus_lt_reg_l rx1); ring_simplify.
Qed.

Lemma neq_midpoint_beta_odd_aux2 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (ln_beta x) < fexp1 (ln_beta x))%Z ->
  midp beta fexp1 x < x <= midp beta fexp1 x + / 2 * ulp beta fexp2 x ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hx.
unfold midp in Hx.
rewrite 2!ulp_neq_0 in Hx; try now apply Rgt_not_eq.
unfold double_round_eq.
set (ex1 := fexp1 (ln_beta x)).
set (ex2 := fexp2 (ln_beta x)).
set (rx1 := round beta fexp1 Zfloor x).
assert (Hbeta : (2 <= beta)%Z).
{ destruct beta as (beta_val,beta_prop).
  now apply Zle_bool_imp_le. }
destruct (generic_format_EM beta fexp2 x) as [F2x|NF2x].
{ (* generic_format beta fexp2 x *)
  now rewrite (round_generic _ fexp2); [|apply valid_rnd_N|]. }
(* ~ generic_format beta fexp2 x *)
assert (Nnrx1 : 0 <= rx1).
{ rewrite <- (round_0 beta fexp1 Zfloor).
  now apply round_le; [exact Vfexp1|apply valid_rnd_DN|apply Rlt_le]. }
assert (Hrx1 : rx1 = Z2R (Zfloor (rx1 * bpow (- ex1))) * bpow ex1).
{ unfold rx1 at 2; unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
  unfold ex1; bpow_simplify.
  now rewrite Zfloor_Z2R. }
set (rx1c := round beta fexp1 Zceil x).
assert (Hf2f1' : (fexp2 (ln_beta x) <= fexp1 (ln_beta x))%Z) by omega.
assert (NF1x : ~ generic_format beta fexp1 x).
{ now intro H; apply NF2x, (generic_inclusion_ln_beta _ fexp1). }
assert (Hrx1c : rx1c = rx1 + ulp beta fexp1 x).
{ now apply round_UP_DN_ulp. }
rewrite ulp_neq_0 in Hrx1c; try now apply Rgt_not_eq.
destruct (midpoint_beta_odd_remains rx1 Nnrx1 ex1 ex2 Hf2f1' Hrx1)
  as (rx2,(Nnrx2, (Hrx2, Hrx12))).
set (rx2c := rx2 + bpow (fexp2 (ln_beta x))).
assert (Hx' : rx2c - / 2 * bpow ex2 < x <= rx2c).
{ unfold rx2c, canonic_exp; fold ex1; fold ex2; split.
  - replace (_ - _) with (rx2 + / 2 * bpow ex2) by field.
    rewrite <- Hrx12; apply Hx.
  - replace (_ + _) with (rx2 + / 2 * bpow ex2 + / 2 * bpow ex2) by field.
    rewrite <- Hrx12; apply Hx. }
assert (Hrx2c : rx2c = Z2R (Zfloor (rx2c * bpow (- ex2))) * bpow ex2).
{ unfold rx2c, ulp, canonic_exp; fold ex2; rewrite Rmult_plus_distr_r.
  bpow_simplify.
  rewrite Hrx2 at 2; bpow_simplify.
  change 1 with (Z2R 1); rewrite <- Z2R_plus, Zfloor_Z2R, Z2R_plus; simpl.
  now rewrite Rmult_plus_distr_r; apply f_equal2; [|now rewrite Rmult_1_l]. }
assert (Prx2c : 0 < rx2c).
{ now apply Rplus_le_lt_0_compat; [|apply bpow_gt_0]. }
assert (Hr2 : round beta fexp2 (Znearest choice2) x = rx2c).
{ unfold round, F2R, scaled_mantissa, canonic_exp; simpl; fold ex2.
  apply (Rmult_eq_reg_r (bpow (- ex2))); [|now apply Rgt_not_eq, bpow_gt_0].
  bpow_simplify.
  rewrite (Znearest_imp _ _ (Zfloor (rx2c * bpow (- ex2)))).
  - now apply (Rmult_eq_reg_r (bpow ex2)); bpow_simplify;
    [apply eq_sym|apply Rgt_not_eq, bpow_gt_0].
  - apply Rabs_lt; split.
    + apply (Rmult_lt_reg_r (bpow ex2)); [now apply bpow_gt_0|].
      rewrite Rmult_minus_distr_r; bpow_simplify.
      rewrite <- Hrx2c.
      now apply (Rplus_lt_reg_l rx2c); ring_simplify.
    + apply Rle_lt_trans with 0; [|lra].
      apply Rle_minus.
      apply (Rmult_le_reg_r (bpow ex2)); [now apply bpow_gt_0|]; bpow_simplify.
      now rewrite <- Hrx2c. }
rewrite Hr2.
assert (Hrx2' : rx1c - / 2 * bpow ex1 < rx2c <= rx1c).
{ split.
  - rewrite Hrx1c; unfold ulp, canonic_exp; fold ex1.
    replace (_ - _) with (rx1 + / 2 * bpow ex1) by field.
    apply (Rlt_le_trans _ _ _ (proj1 Hx) (proj2 Hx')).
  - apply (Rplus_le_reg_r (- / 2 * bpow ex2)).
    unfold rx2c, ulp, canonic_exp; fold ex2.
    replace (_ + _) with (rx2 + / 2 * bpow ex2) by field.
    rewrite <- Hrx12.
    rewrite Hrx1c, Rplus_assoc; apply Rplus_le_compat_l.
    unfold ulp, canonic_exp; fold ex1.
    apply (Rplus_le_reg_r (- / 2 * bpow ex1)); field_simplify.
    unfold Rdiv; apply Rmult_le_compat_r; [lra|].
    now apply Rle_0_minus, bpow_le. }
assert (Hr1 : round beta fexp1 (Znearest choice1) x = rx1c).
{ unfold rx1c, round, F2R, scaled_mantissa, canonic_exp; simpl; fold ex1.
  apply Rmult_eq_compat_r, f_equal, Znearest_imp, Rabs_lt; split.
  - apply (Rmult_lt_reg_r (bpow ex1)); [now apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r; bpow_simplify.
    change (Z2R _ * _) with rx1c.
    apply (Rplus_lt_reg_l rx1c); ring_simplify.
    rewrite Hrx1c; unfold ulp, canonic_exp; fold ex1.
    now replace (_ - _) with (rx1 + / 2 * bpow ex1) by field.
  - apply Rlt_le_trans with 0; [|lra]; apply Rlt_minus.
    apply (Rmult_lt_reg_r (bpow ex1)); [now apply bpow_gt_0|]; bpow_simplify.
    assert (H : x <= rx1c); [now apply round_UP_pt|].
    destruct H as [H|H]; [exact H|].
    casetype False; apply NF1x.
    unfold generic_format, F2R, scaled_mantissa, canonic_exp; simpl; fold ex1.
    rewrite Ztrunc_floor;
      [|now apply Rmult_le_pos;[apply Rlt_le|apply bpow_ge_0]].
    rewrite H at 2.
    unfold rx1c, round, F2R, scaled_mantissa, canonic_exp; simpl; fold ex1.
    now bpow_simplify; rewrite Zfloor_Z2R; rewrite H at 1. }
rewrite Hr1.
destruct (Rle_or_lt rx1 0) as [Nprx1|Prx1].
{ (* rx1 = 0 *)
  assert (Zrx1 : rx1 = 0); [now apply Rle_antisym|].
  rewrite Hrx1c, Zrx1, Rplus_0_l.
  unfold rx2c, ulp, canonic_exp; fold ex1; fold ex2.
  replace (_ + _) with (rx2 + / 2 * bpow ex2 + / 2 * bpow ex2) by field.
  rewrite <- Hrx12, Zrx1, Rplus_0_l.
  assert (Ph12 : 0 < / 2 * bpow ex1 + / 2 * bpow ex2).
  { now apply Rplus_lt_0_compat;
    (apply Rmult_lt_0_compat; [lra|apply bpow_gt_0]). }
  assert (Hf1 : (fexp1 (ln_beta x) <= ln_beta x)%Z).
  { apply ln_beta_ge_bpow.
    rewrite Rabs_right; [|now apply Rle_ge, Rlt_le].
    apply Rle_trans with (/ 2 * bpow ex1).
    - unfold Zminus; rewrite bpow_plus, Rmult_comm.
      fold ex1; apply Rmult_le_compat_r; [now apply bpow_ge_0|].
      rewrite bpow_opp; apply Rinv_le; [lra|].
      simpl; unfold Z.pow_pos; simpl; rewrite Zmult_1_r.
      now change 2 with (Z2R 2); apply Z2R_le.
    - apply Rlt_le.
      now rewrite <- (Rplus_0_l (_ * _)), <- Zrx1. }
  assert (Hl1 : ln_beta (/ 2 * bpow ex1 + / 2 * bpow ex2) = ln_beta x :> Z).
  { apply ln_beta_unique; split.
    - rewrite Rabs_right; [|now apply Rle_ge, Rlt_le].
      apply Rle_trans with x.
      + destruct (ln_beta x) as (ex, Hex); simpl.
        now rewrite <- (Rabs_right x);
          [apply Hex, Rgt_not_eq|apply Rle_ge, Rlt_le].
      + rewrite <- (Rplus_0_l (_ * _)), <- Zrx1.
        apply Hx.
    - rewrite Rabs_right; [|now apply Rle_ge, Rlt_le].
      apply Rlt_le_trans with (bpow ex1); [|now apply bpow_le].
      rewrite <- (Rmult_1_l (bpow ex1)) at 2.
      replace (1 * bpow ex1) with (/ 2 * bpow ex1 + / 2 * bpow ex1) by field.
      now apply Rplus_lt_compat_l, Rmult_lt_compat_l; [lra|apply bpow_lt]. }
  unfold round, F2R, scaled_mantissa, canonic_exp; simpl; rewrite Hl1.
  fold ex1; apply (Rmult_eq_reg_r (bpow (- ex1)));
    [|now apply Rgt_not_eq, bpow_gt_0]; bpow_simplify.
  change 1 with (Z2R 1); apply f_equal, Znearest_imp; simpl.
  apply Rabs_lt; simpl; split.
  - apply (Rplus_lt_reg_r 1); replace (- _ + _) with (/ 2) by field.
    ring_simplify; apply (Rmult_lt_reg_r (bpow ex1)); [now apply bpow_gt_0|].
    rewrite Rmult_plus_distr_r; bpow_simplify.
    rewrite <- (Rplus_0_r (_ * _)) at 1; apply Rplus_lt_compat_l.
    apply Rmult_lt_0_compat; [lra|apply bpow_gt_0].
  - apply (Rplus_lt_reg_r 1); ring_simplify.
    apply (Rmult_lt_reg_r (bpow ex1)); [now apply bpow_gt_0|].
    do 2 rewrite Rmult_plus_distr_r; bpow_simplify.
    now apply Rplus_lt_compat_l, Rmult_lt_compat;
      [lra|apply bpow_ge_0|lra|apply bpow_lt]. }
(* 0 < rx1 *)
assert (Hl1 : ln_beta rx1 = ln_beta x :> Z).
{ now apply ln_beta_DN. }
assert (Hl2 : ln_beta rx2c = ln_beta x :> Z).
{ apply ln_beta_unique; rewrite Rabs_right; [|now apply Rle_ge, Rlt_le].
  replace rx2c with (rx1 + (/ 2 * bpow ex1 + / 2 * bpow ex2));
    [|now rewrite <- Rplus_assoc, Hrx12;
       replace (_ + _) with (rx2 + bpow ex2) by field].
  split.
  - rewrite <- Rplus_assoc.
    apply Rle_trans with x; [|now apply Hx].
    apply Rge_le; rewrite <- (Rabs_right x) at 1; [|now apply Rle_ge, Rlt_le];
    apply Rle_ge; destruct (ln_beta x) as (ex,Hex); simpl; apply Hex.
    now apply Rgt_not_eq.
  - apply Rlt_le_trans with (rx1 + bpow ex1).
    + apply Rplus_lt_compat_l.
      rewrite <- (Rmult_1_l (bpow ex1)) at 2.
      replace (1 * bpow ex1) with (/ 2 * bpow ex1 + / 2 * bpow ex1) by field.
      now apply Rplus_lt_compat_l, Rmult_lt_compat_l; [lra|apply bpow_lt].
    + unfold ex1; rewrite <- Hl1.
      fold (canonic_exp beta fexp1 rx1); rewrite <- ulp_neq_0; try now apply Rgt_not_eq.
      apply id_p_ulp_le_bpow; [exact Prx1| |].
      * now apply generic_format_round; [|apply valid_rnd_DN].
      * destruct (ln_beta rx1) as (erx1, Herx1); simpl.
        rewrite <- (Rabs_right rx1) at 1; [|now apply Rle_ge, Rlt_le].
        now apply Herx1, Rgt_not_eq. }
unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
rewrite Hl2; fold ex1.
apply (Rmult_eq_reg_r (bpow (- ex1)));
  [|now apply Rgt_not_eq, bpow_gt_0]; bpow_simplify.
rewrite Hrx1c, Rmult_plus_distr_r.
unfold rx1, round, F2R, scaled_mantissa, ulp, canonic_exp; simpl; fold ex1.
bpow_simplify.
change 1 with (Z2R 1); rewrite <- Z2R_plus; apply f_equal, Znearest_imp.
apply Rabs_lt; split.
- rewrite Z2R_plus; simpl; apply (Rplus_lt_reg_r 1); ring_simplify.
  replace (- _ + _) with (/ 2) by field.
  apply (Rmult_lt_reg_r (bpow ex1)); [now apply bpow_gt_0|].
  rewrite Rmult_minus_distr_r; bpow_simplify.
  change (Z2R _ * _) with rx1.
  apply (Rplus_lt_reg_l rx1); ring_simplify.
  apply Rlt_le_trans with x; [apply Hx|apply Hx'].
- apply (Rmult_lt_reg_r (bpow ex1)); [now apply bpow_gt_0|].
  rewrite Rmult_minus_distr_r; bpow_simplify.
  rewrite Z2R_plus, Rmult_plus_distr_r; simpl; rewrite Rmult_1_l.
  change (Z2R _ * _ + _) with (rx1 + bpow (canonic_exp beta fexp1 x)).
  rewrite <- Hrx1c; lra.
Qed.

(* neq_midpoint_beta_odd_aux{1,2} together *)
Lemma neq_midpoint_beta_odd_aux3 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (ln_beta x) <= fexp1 (ln_beta x))%Z ->
  (fexp1 (ln_beta x) <= ln_beta x)%Z ->
  x <> midp beta fexp1 x ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hf1 Hx.
destruct (generic_format_EM beta fexp2 x) as [F2x|NF2x].
{ (* generic_format beta fexp2 x *)
  unfold double_round_eq.
  now rewrite (round_generic _ fexp2); [|apply valid_rnd_N|]. }
(* ~ generic_format beta fexp2 x *)
assert (NF1x : ~ generic_format beta fexp1 x).
{ now intro H; apply NF2x, (generic_inclusion_ln_beta _ fexp1). }
destruct (Rle_or_lt x (midp beta fexp1 x)) as [H1|H1].
- (* x < midp fexp1 x *)
  assert (H1' : x < midp beta fexp1 x) by lra.
  destruct (Rlt_or_le x (midp beta fexp1 x - / 2 * ulp beta fexp2 x))
    as [H2|H2].
  + (* x < midp fexp1 x - / 2 * ulp beta fexp2 x *)
    now apply double_round_lt_mid.
  + (* midp fexp1 x - / 2 * ulp beta fexp2 x <= x *)
    now apply neq_midpoint_beta_odd_aux1; [| | | |split].
- (* midp fexp1 x < x *)
  assert (Hm : midp' beta fexp1 x = midp beta fexp1 x).
  { now unfold midp', midp; rewrite round_UP_DN_ulp; [field|]. }
  destruct (Zle_or_lt (fexp1 (ln_beta x)) (fexp2 (ln_beta x))) as [H3|H3].
  + (* fexp2 (ln_beta x) = fexp1 (ln_beta x) *)
    assert (H3' : fexp2 (ln_beta x) = fexp1 (ln_beta x));
    [now apply Zle_antisym|].
    now apply double_round_gt_mid_same_place; [| | |rewrite Hm].
  + (* fexp2 (ln_beta x) < fexp1 (ln_beta x) *)
    destruct (Rlt_or_le (midp beta fexp1 x + / 2 * ulp beta fexp2 x) x)
      as [H2|H2].
    * (* midp fexp1 x + / 2 * ulp beta fexp2 x < x *)
      now apply double_round_gt_mid_further_place; [| | |omega| |rewrite Hm].
    * (* x <= midp fexp1 x + / 2 * ulp beta fexp2 x *)    
      now apply neq_midpoint_beta_odd_aux2; [| | | |split].
Qed.

(* neq_midpoint_beta_odd_aux3 without the hypothesis
   fexp1 (ln_beta x) <= ln_beta x *)
Lemma neq_midpoint_beta_odd :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  forall x,
  0 < x ->
  (fexp2 (ln_beta x) <= fexp1 (ln_beta x))%Z ->
  x <> midp beta fexp1 x ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 x Px Hf2f1 Hx.
destruct (Zle_or_lt (fexp1 (ln_beta x)) (ln_beta x)) as [H1|H1].
{ (* fexp1 (ln_beta x) <= ln_beta x *)
  now apply neq_midpoint_beta_odd_aux3. }
(* ln_beta x < fexp1 (ln_beta x) *)
unfold double_round_eq.
revert Hf2f1 Hx H1.
destruct (ln_beta x) as (ex,Hex); simpl.
specialize (Hex (Rgt_not_eq _ _ Px)).
intros Hf2f1 Hx H1.
rewrite Rabs_right in Hex; [|now apply Rle_ge, Rlt_le].
rewrite (round_N_really_small_pos _ fexp1 _ x ex Hex H1).
destruct (Zle_or_lt (fexp1 ex) (fexp2 ex)) as [H2|H2].
- (* fexp1 ex = fexp2 ex *)
  replace (fexp1 ex) with (fexp2 ex) in H1; [|now apply Zle_antisym].
  rewrite (round_N_really_small_pos _ fexp2 _ x ex Hex H1).
  now rewrite round_0; [|apply valid_rnd_N].
- (* fexp2 (ln_beta x) < fexp1 (ln_beta x) *)
  set (r2 := round beta fexp2 (Znearest choice2) x).
  destruct (Req_dec r2 0) as [Zr2|Nzr2].
  { (* r2 = 0 *)
    now rewrite Zr2, round_0; [|apply valid_rnd_N]. }
  (* r2 <> 0 *)
  assert (B1 : Rabs (r2 - x) <= / 2 * ulp beta fexp2 x);
    [now apply error_le_half_ulp|].
  rewrite ulp_neq_0 in B1; try now apply Rgt_not_eq.
  unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
  apply (Rmult_eq_reg_r (bpow (- fexp1 (ln_beta r2))));
    [|now apply Rgt_not_eq, bpow_gt_0].
  rewrite Rmult_0_l; bpow_simplify.
  change 0 with (Z2R 0); apply f_equal, Znearest_imp.
  simpl; unfold Rminus; rewrite Ropp_0, Rplus_0_r.
  rewrite Rabs_mult, (Rabs_right (bpow _)); [|now apply Rle_ge, bpow_ge_0].
  apply (Rmult_lt_reg_r (bpow (fexp1 (ln_beta r2)))); [now apply bpow_gt_0|].
  bpow_simplify.
  replace r2 with (r2 - x + x) by ring.
  apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)).
  apply Rlt_le_trans with (/ 2 * bpow (canonic_exp beta fexp2 x) + bpow ex);
    [now apply Rplus_le_lt_compat;
      [|rewrite Rabs_right; [|apply Rle_ge, Rlt_le]]|].
  replace (_ - _ + _) with r2 by ring.
  assert (Hbeta : (2 <= beta)%Z).
  { destruct beta as (beta_val,beta_prop).
    now apply Zle_bool_imp_le. }
  assert (Hex' : ln_beta x = ex :> Z).
  { now apply ln_beta_unique;
    rewrite Rabs_right; [|apply Rle_ge, Rlt_le]. }
  assert (Hl2 : (ln_beta r2 <= fexp1 ex)%Z).
  { apply (ln_beta_le_bpow _ _ _ Nzr2).
    replace r2 with (r2 - x + x) by ring.
    apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)).
    apply Rlt_le_trans with (/ 2 * bpow (canonic_exp beta fexp2 x) + bpow ex);
      [now apply Rplus_le_lt_compat;
        [|rewrite Rabs_right; [|apply Rle_ge, Rlt_le]]|].
    apply Rle_trans with (2 * bpow (fexp1 ex - 1)).
    - rewrite Rmult_plus_distr_r, Rmult_1_l.
      apply Rplus_le_compat; [|now apply bpow_le; omega].
      apply Rle_trans with (bpow (fexp2 ex)); [|now apply bpow_le; omega].
      rewrite <- (Rmult_1_l (bpow (fexp2 _))); unfold canonic_exp.
      rewrite Hex'; apply Rmult_le_compat_r; [apply bpow_ge_0|lra].
    - rewrite <- (Rmult_1_l (bpow (fexp1 _))).
      unfold Zminus; rewrite Zplus_comm, bpow_plus, <- Rmult_assoc.
      apply Rmult_le_compat_r; [now apply bpow_ge_0|].
      apply (Rmult_le_reg_r (bpow 1)); [now apply bpow_gt_0|].
      rewrite Rmult_1_l; bpow_simplify.
      simpl; unfold Z.pow_pos; simpl; rewrite Zmult_1_r.
      now change 2 with (Z2R 2); apply Z2R_le. }
  assert (Hf1r2 : fexp1 (ln_beta r2) = fexp1 ex).
  { now apply (proj2 (Vfexp1 ex)); [omega|]. }
  rewrite Hf1r2.
  replace (bpow ex) with (/ 2 * (2 * bpow ex)) by field.
  rewrite <- Rmult_plus_distr_l; apply Rmult_le_compat_l; [lra|].
  apply Rle_trans with (3 * bpow (fexp1 ex - 1)).
  + rewrite (Rmult_plus_distr_r _ 2); rewrite Rmult_1_l; apply Rplus_le_compat.
    * apply bpow_le; unfold canonic_exp; rewrite Hex'; omega.
    * apply Rmult_le_compat_l; [lra|]; apply bpow_le; omega.
  + rewrite <- (Rmult_1_l (bpow (fexp1 _))).
    unfold Zminus; rewrite Zplus_comm, bpow_plus, <- Rmult_assoc.
    apply Rmult_le_compat_r; [now apply bpow_ge_0|].
    apply (Rmult_le_reg_r (bpow 1)); [now apply bpow_gt_0|].
    rewrite Rmult_1_l; bpow_simplify.
    simpl; unfold Z.pow_pos; simpl; rewrite Zmult_1_r.
    change 3 with (Z2R 3); apply Z2R_le.
    destruct (Zle_or_lt beta 2) as [Hb2|Hb2]; [|omega].
    assert (Hbeta' : beta = 2%Z :> Z); [now apply Zle_antisym|].
    casetype False.
    rewrite <- Zodd_ex_iff in Obeta.
    apply (Zodd_not_Zeven _ Obeta).
    now rewrite Hbeta'.
Qed.

(* argh: was 0 <= Z2R mx. This becomes incorrect in FLX with the new ulp. *)
Lemma float_neq_midpoint_beta_odd :
  forall (mx ex : Z),
  forall (fexp : Z -> Z),
  0 < Z2R mx ->
  Z2R mx * bpow ex <> midp beta fexp (Z2R mx * bpow ex).
Proof.
intros mx ex fexp Hmx.
unfold midp; rewrite ulp_neq_0.
unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
set (exf := fexp (ln_beta (Z2R mx * bpow ex))).
set (mxf := Zfloor (Z2R mx * bpow ex * bpow (- exf))).
destruct (Zle_or_lt exf ex) as [Hm|Hm].
- (* exf <= ex *)
  replace ex with (ex - exf + exf)%Z by ring.
  rewrite bpow_plus.
  intro H.
  apply (Rplus_eq_compat_l (- Z2R mxf * bpow exf)) in H.
  revert H.
  rewrite <- Rmult_assoc, <- Rmult_plus_distr_r.
  rewrite <- (Z2R_Zpower _ (_ - _)); [|now apply Zle_minus_le_0].
  intro H.
  ring_simplify in H.
  rewrite <- Rmult_plus_distr_r in H.
  rewrite <- Z2R_opp, <- Z2R_mult, <- Z2R_plus, Rmult_comm in H.
  apply Rmult_eq_reg_l in H; [|now apply Rgt_not_eq, bpow_gt_0].
  apply (Rmult_eq_compat_l 2) in H.
  revert H.
  change 2 with (Z2R 2) at 1; rewrite <- Z2R_mult, Rinv_r; [|lra].
  change 1 with (Z2R 1); apply Z2R_neq.
  intro H.
  apply (Zodd_not_Zeven 1); [now simpl|].
  rewrite <- H.
  now apply Zeven_mult_Zeven_l.
- assert (Hm' : (ex <= exf)%Z) by omega.
  assert (Nnmxy : 0 <= Z2R mxf * bpow exf).
  { apply Rmult_le_pos; [|now apply bpow_ge_0].
    change 0 with (Z2R 0); apply Z2R_le; unfold mxf.
    apply Zfloor_lub; simpl.
    apply Rmult_le_pos; [|now apply bpow_ge_0].
    now apply Rmult_le_pos; [now left|apply bpow_ge_0]. }
  destruct (midpoint_beta_odd_remains _ Nnmxy _ _ Hm')
    as (x',(_,(Hx',Hxx'))).
  { now bpow_simplify; rewrite Zfloor_Z2R. }
  rewrite Hxx', Hx'.
  set (mx' := Zfloor (x' * bpow (- ex))).
  intro H.
  apply (Rplus_eq_compat_l (- Z2R mx' * bpow ex)) in H.
  revert H.
  rewrite <- Rmult_plus_distr_r.
  intro H.
  ring_simplify in H.
  rewrite <- Rmult_plus_distr_r in H.
  rewrite <- Z2R_opp, <- Z2R_plus, Rmult_comm in H.
  apply Rmult_eq_reg_l in H; [|now apply Rgt_not_eq, bpow_gt_0].
  apply (Rmult_eq_compat_l 2) in H.
  revert H.
  change 2 with (Z2R 2) at 1; rewrite <- Z2R_mult, Rinv_r; [|lra].
  change 1 with (Z2R 1); apply Z2R_neq.
  intro H.
  apply (Zodd_not_Zeven 1); [now simpl|].
  rewrite <- H.
  now apply Zeven_mult_Zeven_l.
- apply Rmult_integral_contrapositive_currified.
  now apply Rgt_not_eq, Rlt_gt.
  apply Rgt_not_eq, bpow_gt_0.
Qed.

Section Double_round_mult_beta_odd.

Lemma double_round_mult_beta_odd_aux1 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (forall ex, (fexp2 ex <= fexp1 ex)%Z) ->
  forall x y,
  0 < x -> 0 < y ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 (x * y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hfexp x y Px Py Fx Fy.
apply neq_midpoint_beta_odd; try assumption.
- now apply Rmult_lt_0_compat.
- apply Hfexp.
- intro Hxy.
  revert Fx Fy.
  unfold generic_format, F2R, scaled_mantissa, canonic_exp; simpl.
  set (mx := Ztrunc (x * bpow (- fexp1 (ln_beta x)))).
  set (my := Ztrunc (y * bpow (- fexp1 (ln_beta y)))).
  set (ex := ln_beta x).
  set (ey := ln_beta y).
  intros Fx Fy.
  revert Hxy.
  rewrite Fx, Fy.
  replace (_ * _)
  with (Z2R mx * Z2R my * bpow (fexp1 ex) * bpow (fexp1 ey)) by ring.
  rewrite <- Z2R_mult, Rmult_assoc, <- bpow_plus.
  apply float_neq_midpoint_beta_odd.
  apply (Rmult_lt_reg_r (bpow (fexp1 ex))); [now apply bpow_gt_0|].
  apply (Rmult_lt_reg_r (bpow (fexp1 ey))); [now apply bpow_gt_0|].
  do 2 rewrite Rmult_0_l.
  rewrite Z2R_mult;
    replace (_ * _)
    with (Z2R mx * bpow (fexp1 ex) * (Z2R my * bpow (fexp1 ey))) by ring.
  rewrite <- Fx, <- Fy.
  now apply Rmult_lt_0_compat.
Qed.

Lemma double_round_mult_beta_odd_aux2 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (forall ex, (fexp2 ex <= fexp1 ex)%Z) ->
  forall x y,
  0 <= x -> 0 <= y ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 (x * y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hfexp x y Nnx Nny Fx Fy.
destruct (Req_dec x 0) as [Zx|Nzx].
- (* x = 0 *)
  unfold double_round_eq.
  now rewrite Zx, Rmult_0_l, round_0; [|apply valid_rnd_N].
- (* 0 < x *)
  assert (Px : 0 < x); [lra|].
  destruct (Req_dec y 0) as [Zy|Nzy].
  + (* y = 0 *)
    unfold double_round_eq.
    now rewrite Zy, Rmult_0_r, round_0; [|apply valid_rnd_N].
  + (* 0 < y *)
    assert (Py : 0 < y); [lra|].
    now apply double_round_mult_beta_odd_aux1.
Qed.

Lemma double_round_mult_beta_odd :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (forall ex, (fexp2 ex <= fexp1 ex)%Z) ->
  forall x y,
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 (x * y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Fx Fy.
unfold double_round_eq.
destruct (Rlt_or_le x 0) as [Sx|Sx]; destruct (Rlt_or_le y 0) as [Sy|Sy].
- (* x < 0, y < 0 *)
  replace (x * y) with ((- x) * (- y)); [|ring].
  assert (Px : 0 <= - x); [lra|].
  assert (Py : 0 <= - y); [lra|].
  apply generic_format_opp in Fx.
  apply generic_format_opp in Fy.
  now apply double_round_mult_beta_odd_aux2.
- (* x < 0, 0 <= y *)
  replace (x * y) with (- ((- x) * y)); [|ring].
  assert (Px : 0 <= - x); [lra|].
  apply generic_format_opp in Fx.
  do 3 rewrite round_N_opp.
  apply Ropp_eq_compat.
  now apply double_round_mult_beta_odd_aux2.
- (* 0 <= x, y < 0 *)
  replace (x * y) with (- (x * (- y))); [|ring].
  assert (Py : 0 <= - y); [lra|].
  apply generic_format_opp in Fy.
  do 3 rewrite round_N_opp.
  apply Ropp_eq_compat.
  now apply double_round_mult_beta_odd_aux2.
- (* 0 <= x, 0 <= y *)
  now apply double_round_mult_beta_odd_aux2.
Qed.

Section Double_round_mult_beta_odd_FLX.

Require Import Fcore_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem double_round_mult_beta_odd_FLX :
  forall choice1 choice2,
  (prec <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  double_round_eq beta (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x * y).
Proof.
intros choice1 choice2 Hprec x y Fx Fy.
apply double_round_mult_beta_odd.
- now apply FLX_exp_valid.
- now apply FLX_exp_valid.
- intro ex; unfold FLX_exp; omega.
- now apply generic_format_FLX.
- now apply generic_format_FLX.
Qed.

End Double_round_mult_beta_odd_FLX.

Section Double_round_mult_beta_odd_FLT.

Require Import Fcore_FLX.
Require Import Fcore_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem double_round_mult_beta_odd_FLT :
  forall choice1 choice2,
  (emin' <= emin)%Z -> (prec <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  double_round_eq beta (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x * y).
Proof.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply double_round_mult_beta_odd.
- now apply FLT_exp_valid.
- now apply FLT_exp_valid.
- intro ex; unfold FLT_exp.
  generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  omega.
- now apply generic_format_FLT.
- now apply generic_format_FLT.
Qed.

End Double_round_mult_beta_odd_FLT.

Section Double_round_mult_beta_odd_FTZ.

Require Import Fcore_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem double_round_mult_beta_odd_FTZ :
  forall choice1 choice2,
  (emin' + prec' <= emin + prec)%Z -> (prec <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  double_round_eq beta (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x * y).
Proof.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply double_round_mult_beta_odd.
- now apply FTZ_exp_valid.
- now apply FTZ_exp_valid.
- intro ex; unfold FTZ_exp.
  unfold Prec_gt_0 in prec_gt_0_.
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ex - prec) emin);
  omega.
- now apply generic_format_FTZ.
- now apply generic_format_FTZ.
Qed.

End Double_round_mult_beta_odd_FTZ.

End Double_round_mult_beta_odd.

Section Double_round_plus_beta_odd.

Lemma double_round_plus_beta_odd_aux1 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (forall ex, (fexp2 ex <= fexp1 ex)%Z) ->
  forall x y,
  0 < x -> 0 < y ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 (x + y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hfexp x y Px Py Fx Fy.
apply neq_midpoint_beta_odd; try assumption.
- now apply Rplus_lt_0_compat.
- apply Hfexp.
- intro Hxy.
  revert Fx Fy.
  unfold generic_format, F2R, scaled_mantissa, canonic_exp; simpl.
  set (mx := Ztrunc (x * bpow (- fexp1 (ln_beta x)))).
  set (my := Ztrunc (y * bpow (- fexp1 (ln_beta y)))).
  set (ex := ln_beta x).
  set (ey := ln_beta y).
  intros Fx Fy.
  revert Hxy.
  rewrite Fx, Fy.
  destruct (Zle_or_lt (fexp1 ex) (fexp1 ey)) as [Hexy|Hexy].
  + replace (fexp1 ey) with (fexp1 ey - fexp1 ex + fexp1 ex)%Z by ring.
    rewrite bpow_plus, <- Rmult_assoc, <- Rmult_plus_distr_r.
    rewrite <- Z2R_Zpower; [|now apply Zle_minus_le_0].
    rewrite <- Z2R_mult, <- Z2R_plus.
    apply float_neq_midpoint_beta_odd.
    apply (Rmult_lt_reg_r (bpow (fexp1 ex))); [now apply bpow_gt_0|].
    rewrite Z2R_plus, Z2R_mult, Z2R_Zpower; [|now apply Zle_minus_le_0].
    rewrite Rmult_0_l, Rmult_plus_distr_r; bpow_simplify.
    rewrite <- Fx, <- Fy.
    now apply Rplus_lt_0_compat.
  + replace (fexp1 ex) with (fexp1 ex - fexp1 ey + fexp1 ey)%Z by ring.
    rewrite bpow_plus, <- Rmult_assoc, <- Rmult_plus_distr_r.
    rewrite <- Z2R_Zpower; [|omega].
    rewrite <- Z2R_mult, <- Z2R_plus.
    apply float_neq_midpoint_beta_odd.
    apply (Rmult_lt_reg_r (bpow (fexp1 ey))); [now apply bpow_gt_0|].
    rewrite Z2R_plus, Z2R_mult, Z2R_Zpower; [|omega].
    rewrite Rmult_0_l, Rmult_plus_distr_r; bpow_simplify.
    rewrite <- Fx, <- Fy.
    now apply Rplus_lt_0_compat.
Qed.

Lemma double_round_plus_beta_odd_aux2 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (forall ex, (fexp2 ex <= fexp1 ex)%Z) ->
  forall x y,
  0 <= x -> 0 <= y ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 (x + y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hfexp x y Nnx Nny Fx Fy.
destruct (Req_dec x 0) as [Zx|Nzx]; destruct (Req_dec y 0) as [Zy|Nzy].
- (* x = 0, y = 0 *)
  unfold double_round_eq.
  now rewrite Zx, Zy, Rplus_0_l, round_0; [|apply valid_rnd_N].
- (* x = 0, 0 < y *)
  assert (Py : 0 < y); [lra|].
  rewrite Zx, Rplus_0_l.
  apply (neq_midpoint_beta_odd _ _ Vfexp1 Vfexp2 _ _ _ Py (Hfexp _)).
  rewrite Fy; unfold F2R, scaled_mantissa; simpl.
  apply float_neq_midpoint_beta_odd.
  apply Rmult_lt_reg_r with (bpow (canonic_exp beta fexp1 y)).
  apply bpow_gt_0.
  rewrite Rmult_0_l.
  apply Rlt_le_trans with (1:=Py).
  right; rewrite Fy at 1; unfold F2R, scaled_mantissa; now simpl.
- (* 0 < x, y = 0 *)
  assert (Px : 0 < x); [lra|].
  rewrite Zy, Rplus_0_r.
  apply (neq_midpoint_beta_odd _ _ Vfexp1 Vfexp2 _ _ _ Px (Hfexp _)).
  rewrite Fx; unfold F2R, scaled_mantissa; simpl.
  apply float_neq_midpoint_beta_odd.
  apply Rmult_lt_reg_r with (bpow (canonic_exp beta fexp1 x)).
  apply bpow_gt_0.
  rewrite Rmult_0_l.
  apply Rlt_le_trans with (1:=Px).
  right; rewrite Fx at 1; unfold F2R, scaled_mantissa; now simpl.
- (* 0 < x, 0 < y *)
  assert (Px : 0 < x); [lra|].
  assert (Py : 0 < y); [lra|].
  now apply double_round_plus_beta_odd_aux1.
Qed.

Lemma double_round_minus_beta_odd_aux1 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (forall ex, (fexp2 ex <= fexp1 ex)%Z) ->
  forall x y,
  0 < x -> 0 < y -> y < x ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 (x - y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hfexp x y Px Py Hxy Fx Fy.
apply neq_midpoint_beta_odd; try assumption.
- now apply Rlt_Rminus.
- apply Hfexp.
- intro Hxy'.
  revert Fx Fy.
  unfold generic_format, F2R, scaled_mantissa, canonic_exp; simpl.
  set (mx := Ztrunc (x * bpow (- fexp1 (ln_beta x)))).
  set (my := Ztrunc (y * bpow (- fexp1 (ln_beta y)))).
  set (ex := ln_beta x).
  set (ey := ln_beta y).
  intros Fx Fy.
  revert Hxy'.
  rewrite Fx, Fy.
  destruct (Zle_or_lt (fexp1 ex) (fexp1 ey)) as [Hexy|Hexy].
  + replace (fexp1 ey) with (fexp1 ey - fexp1 ex + fexp1 ex)%Z by ring.
    rewrite bpow_plus, <- Rmult_assoc, <- Rmult_minus_distr_r.
    rewrite <- Z2R_Zpower; [|now apply Zle_minus_le_0].
    rewrite <- Z2R_mult, <- Z2R_minus.
    apply float_neq_midpoint_beta_odd.
    apply (Rmult_lt_reg_r (bpow (fexp1 ex))); [now apply bpow_gt_0|].
    rewrite Z2R_minus, Z2R_mult, Z2R_Zpower; [|now apply Zle_minus_le_0].
    rewrite Rmult_0_l, Rmult_minus_distr_r; bpow_simplify.
    rewrite <- Fx, <- Fy.
    now apply Rlt_Rminus.
  + replace (fexp1 ex) with (fexp1 ex - fexp1 ey + fexp1 ey)%Z by ring.
    rewrite bpow_plus, <- Rmult_assoc, <- Rmult_minus_distr_r.
    rewrite <- Z2R_Zpower; [|omega].
    rewrite <- Z2R_mult, <- Z2R_minus.
    apply float_neq_midpoint_beta_odd.
    apply (Rmult_lt_reg_r (bpow (fexp1 ey))); [now apply bpow_gt_0|].
    rewrite Z2R_minus, Z2R_mult, Z2R_Zpower; [|omega].
    rewrite Rmult_0_l, Rmult_minus_distr_r; bpow_simplify.
    rewrite <- Fx, <- Fy.
    now apply Rlt_Rminus.
Qed.

Lemma double_round_minus_beta_odd_aux2 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (forall ex, (fexp2 ex <= fexp1 ex)%Z) ->
  forall x y,
  0 <= x -> 0 <= y ->
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 (x - y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hfexp x y Nnx Nny Fx Fy.
destruct (Req_dec x 0) as [Zx|Nzx]; destruct (Req_dec y 0) as [Zy|Nzy].
- (* x = 0, y = 0 *)
  unfold double_round_eq.
  unfold Rminus.
  now rewrite Zx, Zy, Rplus_0_l, Ropp_0, round_0; [|apply valid_rnd_N].
- (* x = 0, 0 < y *)
  assert (Py : 0 < y); [lra|].
  unfold Rminus; rewrite Zx, Rplus_0_l.
  unfold double_round_eq; do 3 rewrite round_N_opp; apply f_equal.
  apply (neq_midpoint_beta_odd _ _ Vfexp1 Vfexp2 _ _ _ Py (Hfexp _)).
  rewrite Fy; unfold F2R, scaled_mantissa; simpl.
  apply float_neq_midpoint_beta_odd.
  apply Rmult_lt_reg_r with (bpow (canonic_exp beta fexp1 y)).
  apply bpow_gt_0.
  rewrite Rmult_0_l; apply Rlt_le_trans with (1:=Py).
  right; rewrite Fy at 1; unfold F2R, scaled_mantissa; now simpl.
- (* 0 < x, y = 0 *)
  assert (Px : 0 < x); [lra|].
  unfold Rminus; rewrite Zy, Ropp_0, Rplus_0_r.
  apply (neq_midpoint_beta_odd _ _ Vfexp1 Vfexp2 _ _ _ Px (Hfexp _)).
  rewrite Fx; unfold F2R, scaled_mantissa; simpl.
  apply float_neq_midpoint_beta_odd.
  apply Rmult_lt_reg_r with (bpow (canonic_exp beta fexp1 x)).
  apply bpow_gt_0.
  rewrite Rmult_0_l; apply Rlt_le_trans with (1:=Px).
  right; rewrite Fx at 1; unfold F2R, scaled_mantissa; now simpl.
- (* 0 < x, 0 < y *)
  assert (Px : 0 < x); [lra|].
  assert (Py : 0 < y); [lra|].
  destruct (Rtotal_order x y) as [Hxy|[Hxy|Hxy]].
  + replace (x - y) with (- (y - x)) by ring.
    unfold double_round_eq; do 3 rewrite round_N_opp; apply f_equal.
    now apply double_round_minus_beta_odd_aux1.
  + unfold double_round_eq.
    now rewrite (Rminus_diag_eq _ _ Hxy), round_0; [|apply valid_rnd_N].
  + now apply double_round_minus_beta_odd_aux1.
Qed.

Lemma double_round_plus_beta_odd :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (forall ex, (fexp2 ex <= fexp1 ex)%Z) ->
  forall x y,
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 (x + y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Fx Fy.
unfold double_round_eq.
destruct (Rlt_or_le x 0) as [Sx|Sx]; destruct (Rlt_or_le y 0) as [Sy|Sy].
- (* x < 0, y < 0 *)
  replace (x + y) with (- ((- x) + (- y))); [|ring].
  assert (Px : 0 <= - x); [lra|].
  assert (Py : 0 <= - y); [lra|].
  do 3 rewrite round_N_opp; apply f_equal.
  apply generic_format_opp in Fx.
  apply generic_format_opp in Fy.
  now apply double_round_plus_beta_odd_aux2.
- (* x < 0, 0 <= y *)
  replace (x + y) with (- ((- x) - y)); [|ring].
  assert (Px : 0 <= - x); [lra|].
  apply generic_format_opp in Fx.
  do 3 rewrite round_N_opp; apply f_equal.
  now apply double_round_minus_beta_odd_aux2.
- (* 0 <= x, y < 0 *)
  replace (x + y) with (x - (- y)); [|ring].
  assert (Py : 0 <= - y); [lra|].
  apply generic_format_opp in Fy.
  now apply double_round_minus_beta_odd_aux2.
- (* 0 <= x, 0 <= y *)
  now apply double_round_plus_beta_odd_aux2.
Qed.

Lemma double_round_minus_beta_odd :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (forall ex, (fexp2 ex <= fexp1 ex)%Z) ->
  forall x y,
  generic_format beta fexp1 x -> generic_format beta fexp1 y ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 (x - y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x y Fx Fy.
apply generic_format_opp in Fy.
now apply double_round_plus_beta_odd.
Qed.

Section Double_round_plus_beta_odd_FLX.

Require Import Fcore_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem double_round_plus_beta_odd_FLX :
  forall choice1 choice2,
  (prec <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  double_round_eq beta (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x + y).
Proof.
intros choice1 choice2 Hprec x y Fx Fy.
apply double_round_plus_beta_odd.
- now apply FLX_exp_valid.
- now apply FLX_exp_valid.
- intro ex; unfold FLX_exp; omega.
- now apply generic_format_FLX.
- now apply generic_format_FLX.
Qed.

Theorem double_round_minus_beta_odd_FLX :
  forall choice1 choice2,
  (prec <= prec')%Z ->
  forall x y,
  FLX_format beta prec x -> FLX_format beta prec y ->
  double_round_eq beta (FLX_exp prec) (FLX_exp prec') choice1 choice2 (x - y).
Proof.
intros choice1 choice2 Hprec x y Fx Fy.
apply double_round_minus_beta_odd.
- now apply FLX_exp_valid.
- now apply FLX_exp_valid.
- intro ex; unfold FLX_exp; omega.
- now apply generic_format_FLX.
- now apply generic_format_FLX.
Qed.

End Double_round_plus_beta_odd_FLX.

Section Double_round_plus_beta_odd_FLT.

Require Import Fcore_FLX.
Require Import Fcore_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem double_round_plus_beta_odd_FLT :
  forall choice1 choice2,
  (emin' <= emin)%Z -> (prec <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  double_round_eq beta (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x + y).
Proof.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply double_round_plus_beta_odd.
- now apply FLT_exp_valid.
- now apply FLT_exp_valid.
- intro ex; unfold FLT_exp.
  generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  omega.
- now apply generic_format_FLT.
- now apply generic_format_FLT.
Qed.

Theorem double_round_minus_beta_odd_FLT :
  forall choice1 choice2,
  (emin' <= emin)%Z -> (prec <= prec')%Z ->
  forall x y,
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  double_round_eq beta (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (x - y).
Proof.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply double_round_minus_beta_odd.
- now apply FLT_exp_valid.
- now apply FLT_exp_valid.
- intro ex; unfold FLT_exp.
  generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  omega.
- now apply generic_format_FLT.
- now apply generic_format_FLT.
Qed.

End Double_round_plus_beta_odd_FLT.

Section Double_round_plus_beta_odd_FTZ.

Require Import Fcore_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem double_round_plus_beta_odd_FTZ :
  forall choice1 choice2,
  (emin' + prec' <= emin + prec)%Z -> (prec <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  double_round_eq beta (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x + y).
Proof.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply double_round_plus_beta_odd.
- now apply FTZ_exp_valid.
- now apply FTZ_exp_valid.
- intro ex; unfold FTZ_exp.
  unfold Prec_gt_0 in prec_gt_0_.
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ex - prec) emin);
  omega.
- now apply generic_format_FTZ.
- now apply generic_format_FTZ.
Qed.

Theorem double_round_minus_beta_odd_FTZ :
  forall choice1 choice2,
  (emin' + prec' <= emin + prec)%Z -> (prec <= prec')%Z ->
  forall x y,
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  double_round_eq beta (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (x - y).
Proof.
intros choice1 choice2 Hemin Hprec x y Fx Fy.
apply double_round_minus_beta_odd.
- now apply FTZ_exp_valid.
- now apply FTZ_exp_valid.
- intro ex; unfold FTZ_exp.
  unfold Prec_gt_0 in prec_gt_0_.
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ex - prec) emin);
  omega.
- now apply generic_format_FTZ.
- now apply generic_format_FTZ.
Qed.

End Double_round_plus_beta_odd_FTZ.

End Double_round_plus_beta_odd.

Section Double_round_sqrt_beta_odd.

(* argh: was forall x, but 0 may be a midpoint now *)
Lemma sqrt_neq_midpoint :
  forall fexp : Z -> Z, Valid_exp fexp ->
  forall x, 0 < x ->
  generic_format beta fexp x ->
  sqrt x <> midp beta fexp (sqrt x).
Proof.
intros fexp Vfexp x Px Fx.
(*destruct (Rle_or_lt x 0) as [Npx|Px].
{ (* x <= 0 *)
  rewrite (sqrt_neg _ Npx).
  unfold midp; rewrite round_0; [|apply valid_rnd_DN]; rewrite Rplus_0_l.
  intro H.
  apply (Rmult_eq_compat_l 2) in H; field_simplify in H.
  unfold Rdiv in H; rewrite Rinv_1 in H; do 2 rewrite Rmult_1_r in H.
  apply eq_sym in H.
  revert H; apply Rgt_not_eq; apply bpow_gt_0. } *)
(* 0 < x *)
unfold midp.
set (r := round beta fexp Zfloor (sqrt x)).
revert Fx.
rewrite ulp_neq_0.
2: now apply Rgt_not_eq, sqrt_lt_R0.
unfold generic_format, round, F2R, scaled_mantissa, canonic_exp; simpl.
set (m := Ztrunc (x * bpow (- fexp (ln_beta x)))).
intro Fx.
assert (Nnr : 0 <= r).
{ unfold r; rewrite <- (round_0 beta fexp Zfloor); apply round_le.
  - exact Vfexp.
  - apply valid_rnd_DN.
  - apply sqrt_ge_0. }
set (exsx := fexp (ln_beta (sqrt x))).
set (exx := (fexp (ln_beta x))).
destruct (Req_dec r 0) as [Zr|Nzr].
{ (* r = 0 *)
  rewrite Zr.
  destruct (Zle_or_lt exx (2 * exsx)) as [H1|H1].
  - (* exx <= 2 * exsx *)
    set (ex2 := Zfloor (Z2R exx / 2)).
    assert (H1' : (ex2 <= exsx)%Z).
    { apply le_Z2R.
      apply (Rle_trans _ _ _ (Zfloor_lb _)).
      apply (Rmult_le_reg_l 2); [lra|].
      replace (_ * (_ / _)) with (Z2R exx) by field.
      now change 2 with (Z2R 2); rewrite <- Z2R_mult; apply Z2R_le. }
    assert (H1'' : (2 * ex2 <= exx)%Z).
    { apply le_Z2R, (Rmult_le_reg_r (/ 2)); [lra|].
      rewrite Zmult_comm, Z2R_mult, Rmult_assoc; simpl.
      rewrite Rinv_r; [|lra]; rewrite Rmult_1_r.
      apply Zfloor_lb. }
    destruct (midpoint_beta_odd_remains _ (Rle_refl 0) _ _ H1')
      as (x',(Nnx',(Fx',Hx'))).
    { rewrite Rmult_0_l.
      now change 0 with (Z2R 0); rewrite Zfloor_Z2R; simpl; rewrite Rmult_0_l. }
    rewrite Hx'.
    intro H.
    assert (H' := H).
    apply (Rmult_eq_compat_l (sqrt x)) in H.
    rewrite H' in H at 3.
    clear H'.
    revert H.
    rewrite sqrt_def; [|now apply Rlt_le].
    replace (_ * _)
    with (x' * x' + x' * bpow ex2 + / 4 * bpow ex2 * bpow ex2) by field.
    rewrite Fx; fold exx.
    revert Fx'; set (m' := Zfloor ((x' * bpow (- ex2)))); intro Fx'.
    rewrite Fx'.
    replace (_ + Z2R m' * _ * _)
    with ((Z2R m' * Z2R m' + Z2R m') * (bpow ex2 * bpow ex2)) by ring.
    rewrite (Rmult_assoc (/ 4)), <- Rmult_plus_distr_r.
    bpow_simplify.
    intro H; apply (Rmult_eq_compat_r (bpow (- 2 * ex2))) in H; revert H.
    bpow_simplify.
    rewrite <- Z2R_Zpower; [|now apply Zle_minus_le_0].
    do 2 rewrite <- Z2R_mult; rewrite <- Z2R_plus.
    intro H.
    apply (Rplus_eq_compat_l (- Z2R (m' * m' + m'))) in H.
    ring_simplify in H.
    rewrite <- Z2R_opp, <- Z2R_plus in H.
    apply (Rmult_eq_compat_l 4) in H.
    revert H.
    change 4 with (Z2R 4) at 1; rewrite <- Z2R_mult, Rinv_r; [|lra].
    change 1 with (Z2R 1); apply Z2R_neq.
    intro H.
    apply (Zodd_not_Zeven 1); [now simpl|].
    rewrite <- H.
    now apply Zeven_mult_Zeven_l.
  - (* 2 * exsx < exx *)
    rewrite Rplus_0_l.
    intro H.
    assert (H' := H).
    apply (Rmult_eq_compat_l (sqrt x)) in H.
    rewrite H' in H at 3.
    clear H'.
    revert H.
    rewrite sqrt_def; [|now apply Rlt_le].
    replace (_ * _)
    with (/ 4 * bpow exsx * bpow exsx) by field.
    rewrite Fx; fold exx.
    bpow_simplify.
    intro H; apply (Rmult_eq_compat_r (bpow (- 2 * exsx))) in H; revert H.
    bpow_simplify.
    rewrite <- Z2R_Zpower; [|now apply Zle_minus_le_0; omega].
    rewrite <- Z2R_mult.
    intro H.
    apply (Rmult_eq_compat_l 4) in H.
    revert H.
    change 4 with (Z2R 4) at 1; rewrite <- Z2R_mult, Rinv_r; [|lra].
    change 1 with (Z2R 1); apply Z2R_neq.
    intro H.
    apply (Zodd_not_Zeven 1); [now simpl|].
    rewrite <- H.
    now apply Zeven_mult_Zeven_l. }
(* 0 < r *)    
assert (Pr : 0 < r) by lra.
destruct (Zle_or_lt exx (2 * exsx)) as [H1|H1].
- (* exx <= 2 * exsx *)
  set (ex2 := Zfloor (Z2R exx / 2)).
  assert (H1' : (ex2 <= exsx)%Z).
  { apply le_Z2R.
    apply (Rle_trans _ _ _ (Zfloor_lb _)).
    apply (Rmult_le_reg_l 2); [lra|].
    replace (_ * (_ / _)) with (Z2R exx) by field.
    now change 2 with (Z2R 2); rewrite <- Z2R_mult; apply Z2R_le. }
  assert (H1'' : (2 * ex2 <= exx)%Z).
  { apply le_Z2R, (Rmult_le_reg_r (/ 2)); [lra|].
    rewrite Zmult_comm, Z2R_mult, Rmult_assoc; simpl.
    rewrite Rinv_r; [|lra]; rewrite Rmult_1_r.
    apply Zfloor_lb. }
  destruct (midpoint_beta_odd_remains_pos _ Pr _ _ H1')
    as (x',(Px',(Lx',(Fx',Hx')))).
  { unfold r at 2, round, F2R, scaled_mantissa, canonic_exp; simpl.
    fold exsx; bpow_simplify.
    now rewrite Zfloor_Z2R. }
  rewrite Hx'.
  intro H.
  assert (H' := H).
  apply (Rmult_eq_compat_l (sqrt x)) in H.
  rewrite H' in H at 3.
  clear H'.
  revert H.
  rewrite sqrt_def; [|now apply Rlt_le].
  replace (_ * _)
  with (x' * x' + x' * bpow ex2 + / 4 * bpow ex2 * bpow ex2) by field.
  rewrite Fx; fold exx.
  revert Fx'; set (m' := Zfloor ((x' * bpow (- ex2)))); intro Fx'.
  rewrite Fx'.
  replace (_ + Z2R m' * _ * _)
  with ((Z2R m' * Z2R m' + Z2R m') * (bpow ex2 * bpow ex2)) by ring.
  rewrite (Rmult_assoc (/ 4)), <- Rmult_plus_distr_r.
  bpow_simplify.
  intro H; apply (Rmult_eq_compat_r (bpow (- 2 * ex2))) in H; revert H.
  bpow_simplify.
  rewrite <- Z2R_Zpower; [|now apply Zle_minus_le_0].
  do 2 rewrite <- Z2R_mult; rewrite <- Z2R_plus.
  intro H.
  apply (Rplus_eq_compat_l (- Z2R (m' * m' + m'))) in H.
  ring_simplify in H.
  rewrite <- Z2R_opp, <- Z2R_plus in H.
  apply (Rmult_eq_compat_l 4) in H.
  revert H.
  change 4 with (Z2R 4) at 1; rewrite <- Z2R_mult, Rinv_r; [|lra].
  change 1 with (Z2R 1); apply Z2R_neq.
  intro H.
  apply (Zodd_not_Zeven 1); [now simpl|].
  rewrite <- H.
  now apply Zeven_mult_Zeven_l.
- (* 2 * exsx < exx *)
  intro H.
  assert (H' := H).
  apply (Rmult_eq_compat_l (sqrt x)) in H.
  rewrite H' in H at 3.
  clear H'.
  revert H.
  rewrite sqrt_def; [|now apply Rlt_le].
  replace (_ * _)
  with (r * r + r * bpow exsx + / 4 * bpow exsx * bpow exsx) by field.
  rewrite Fx; fold exx.
  set (mr := Zfloor (sqrt x * bpow (- exsx))).
  assert (Hr : r = Z2R mr * bpow exsx); [now simpl|].
  rewrite Hr.
  replace (_ + _)
  with ((Z2R mr * Z2R mr + Z2R mr + / 4) * bpow exsx * bpow exsx) by ring.
  bpow_simplify.
  intro H; apply (Rmult_eq_compat_r (bpow (- 2 * exsx))) in H; revert H.
  bpow_simplify.
  rewrite <- Z2R_Zpower; [|now apply Zle_minus_le_0; omega].
  do 2 rewrite <- Z2R_mult; rewrite <- Z2R_plus.
  intro H.
  apply (Rplus_eq_compat_l (- Z2R (mr * mr + mr))) in H.
  ring_simplify in H.
  rewrite <- Z2R_opp, <- Z2R_plus in H.
  apply (Rmult_eq_compat_l 4) in H.
  revert H.
  change 4 with (Z2R 4) at 1; rewrite <- Z2R_mult, Rinv_r; [|lra].
  change 1 with (Z2R 1); apply Z2R_neq.
  intro H.
  apply (Zodd_not_Zeven 1); [now simpl|].
  rewrite <- H.
  now apply Zeven_mult_Zeven_l.
Qed.

Lemma double_round_sqrt_beta_odd :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall (choice1 choice2 : Z -> bool),
  (forall ex, (fexp2 ex <= fexp1 ex)%Z) ->
  forall x,
  generic_format beta fexp1 x ->
  double_round_eq beta fexp1 fexp2 choice1 choice2 (sqrt x).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2 Hexp x Fx.
destruct (Rle_or_lt x 0) as [Npx|Px].
{ (* x <= 0 *)
  unfold double_round_eq.
  rewrite (sqrt_neg _ Npx).
  now rewrite round_0; [|apply valid_rnd_N]. }
assert (Psx := sqrt_lt_R0 _ Px).
specialize (Hexp (ln_beta (sqrt x))).
apply (neq_midpoint_beta_odd _ _ _ _ _ _ _ Psx Hexp).
now apply sqrt_neq_midpoint.
Qed.

Section Double_round_sqrt_beta_odd_FLX.

Require Import Fcore_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem double_round_sqrt_beta_odd_FLX :
  forall choice1 choice2,
  (prec <= prec')%Z ->
  forall x,
  FLX_format beta prec x ->
  double_round_eq beta (FLX_exp prec) (FLX_exp prec') choice1 choice2 (sqrt x).
Proof.
intros choice1 choice2 Hprec x Fx.
apply double_round_sqrt_beta_odd.
- now apply FLX_exp_valid.
- now apply FLX_exp_valid.
- intro ex; unfold FLX_exp; omega.
- now apply generic_format_FLX.
Qed.

End Double_round_sqrt_beta_odd_FLX.

Section Double_round_sqrt_beta_odd_FLT.

Require Import Fcore_FLX.
Require Import Fcore_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem double_round_sqrt_beta_odd_FLT :
  forall choice1 choice2,
  (emin' <= emin)%Z -> (prec <= prec')%Z ->
  forall x,
  FLT_format beta emin prec x ->
  double_round_eq beta (FLT_exp emin prec) (FLT_exp emin' prec')
                  choice1 choice2 (sqrt x).
Proof.
intros choice1 choice2 Hemin Hprec x Fx.
apply double_round_sqrt_beta_odd.
- now apply FLT_exp_valid.
- now apply FLT_exp_valid.
- intro ex; unfold FLT_exp.
  generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  omega.
- now apply generic_format_FLT.
Qed.

End Double_round_sqrt_beta_odd_FLT.

Section Double_round_sqrt_beta_odd_FTZ.

Require Import Fcore_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem double_round_sqrt_beta_odd_FTZ :
  forall choice1 choice2,
  (emin' + prec' <= emin + prec)%Z -> (prec <= prec')%Z ->
  forall x,
  FTZ_format beta emin prec x ->
  double_round_eq beta (FTZ_exp emin prec) (FTZ_exp emin' prec')
                  choice1 choice2 (sqrt x).
Proof.
intros choice1 choice2 Hemin Hprec x Fx.
apply double_round_sqrt_beta_odd.
- now apply FTZ_exp_valid.
- now apply FTZ_exp_valid.
- intro ex; unfold FTZ_exp.
  unfold Prec_gt_0 in prec_gt_0_.
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ex - prec) emin);
  omega.
- now apply generic_format_FTZ.
Qed.

End Double_round_sqrt_beta_odd_FTZ.

End Double_round_sqrt_beta_odd.

Section Double_round_div_beta_odd_rna.

Lemma double_round_eq_mid_beta_odd_rna_aux1 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall x,
  0 < x ->
  (fexp2 (ln_beta x) <= fexp1 (ln_beta x) - 1)%Z ->
  (fexp1 (ln_beta x) <= ln_beta x)%Z ->
  x = midp beta fexp1 x ->
  round beta fexp1 ZnearestA (round beta fexp2 ZnearestA x)
  = round beta fexp1 ZnearestA x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 x Px Hf2 Hf1.
unfold midp.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
set (rd := round beta fexp1 Zfloor x).
set (u := bpow (fexp1 (ln_beta x))).
intro Xmid.
apply (Rplus_eq_compat_l (- rd)) in Xmid; ring_simplify in Xmid.
rewrite Rplus_comm in Xmid; fold (x - rd) in Xmid.
assert (Xmid' : x = rd + / 2 * u);
[now apply (Rplus_eq_reg_r (- rd)); ring_simplify|].
destruct (Req_dec rd 0) as [Zrd|Nzrd].
- (* rd = 0 *)
  set (rd1 := round beta fexp1 ZnearestA x).
  rewrite Zrd in Xmid'; rewrite Rplus_0_l in Xmid'.
  rewrite Xmid'.
  replace u with (Z2R beta * bpow (fexp1 (ln_beta x) - 1));
    [|now rewrite <- bpow_1; unfold u, ulp, canonic_exp; bpow_simplify].
  rewrite <- Rmult_assoc.
  elim Obeta; intros m Hm.
  rewrite Hm.
  rewrite Z2R_plus; rewrite Z2R_mult.
  rewrite Rmult_plus_distr_l; rewrite <- Rmult_assoc; simpl.
  replace (/ 2 * 2) with 1 by field; rewrite Rmult_1_l; rewrite Rmult_1_r.
  rewrite Rmult_plus_distr_r.
  set (x'' := Z2R m * bpow (fexp1 (ln_beta x) - 1)).
  assert (Hbeta : (2 <= beta)%Z).
  { destruct beta as (beta_val,beta_prop).
    now apply Zle_bool_imp_le. }
  assert (Pm : (1 <= m)%Z) by omega.
  assert (Px'' : 0 < x'').
  { unfold x''.
    apply Rmult_lt_0_compat.
    - change 0 with (Z2R 0); apply Z2R_lt; omega.
    - now apply bpow_gt_0. }
  assert (Hx'' : x'' =
                 Z2R (Zfloor (x'' * bpow (- (fexp1 (ln_beta x) - 1)))) *
                 bpow (fexp1 (ln_beta x) - 1)).
  { unfold x''; bpow_simplify.
    now rewrite Zfloor_Z2R. }
  destruct (midpoint_beta_odd_remains_pos x'' Px'' (fexp1 (ln_beta x) - 1)
                                          (fexp2 (ln_beta x)) Hf2 Hx'')
    as (x2,(Hx2_0,(Hx2_1,(Hx2_2,Hx2_3)))).
  rewrite Hx2_3.
  assert (Hlx : ln_beta x = fexp1 (ln_beta x) :> Z).
  { apply ln_beta_unique; split.
    - apply Rabs_ge; right.
      apply Rle_trans with (/2 * u); [|now rewrite Xmid'; apply Rle_refl].
      unfold Zminus; rewrite Zplus_comm; rewrite bpow_plus.
      rewrite bpow_opp; rewrite bpow_1.
      apply Rmult_le_compat.
      + apply Rlt_le; apply Rinv_0_lt_compat.
        change 0 with (Z2R 0); apply Z2R_lt; omega.
      + apply bpow_ge_0.
      + apply Rinv_le; [lra|].
        now change 2 with (Z2R 2); apply Z2R_le.
      + unfold u, ulp, canonic_exp; apply Rle_refl.
    - rewrite Rabs_right; [|now apply Rle_ge; apply Rlt_le].
      rewrite Xmid' at 1.
      unfold u, ulp, canonic_exp.
      rewrite <- Rmult_1_l.
      apply Rmult_lt_compat_r; [|lra].
      apply bpow_gt_0. }
  assert (Hlx'' : ln_beta x'' = ln_beta x :> Z).
  { apply ln_beta_unique; split.
    - apply Rabs_ge; right.
      unfold x''; rewrite <- Hlx.
      rewrite <- (Rmult_1_l (bpow _)) at 1.
      apply Rmult_le_compat_r.
      + apply bpow_ge_0.
      + now change 1 with (Z2R 1); apply Z2R_le.
    - rewrite Rabs_right; [|now apply Rle_ge; apply Rlt_le].
      unfold x''; rewrite <- Hlx.
      unfold Zminus; rewrite Zplus_comm; rewrite bpow_plus;
      rewrite <- Rmult_assoc.
      rewrite <- Rmult_1_l; apply Rmult_lt_compat_r; [now apply bpow_gt_0|].
      apply (Rmult_lt_reg_r (bpow 1)); bpow_simplify; rewrite bpow_1.
      + change 0 with (Z2R 0); apply Z2R_lt; omega.
      + rewrite Rmult_1_l; apply Z2R_lt.
        omega. }
  assert (Hl2 : ln_beta (x2 + / 2 * bpow (fexp2 (ln_beta x)))
                = ln_beta x2 :> Z).
  { apply (ln_beta_plus_eps beta fexp2); [| |split].
    - exact Hx2_0.
    - unfold generic_format, F2R, scaled_mantissa, canonic_exp; simpl.
      rewrite Hx2_1, Hlx'', Ztrunc_floor; [exact Hx2_2|].
      now apply Rmult_le_pos; [apply Rlt_le|apply bpow_ge_0].
    - apply Rmult_le_pos; [lra|apply bpow_ge_0].
    - rewrite ulp_neq_0; try now apply Rgt_not_eq.
      unfold canonic_exp; rewrite Hx2_1; rewrite Hlx''.
      rewrite <- Rmult_1_l; apply Rmult_lt_compat_r; [|lra].
      apply bpow_gt_0. }
  unfold round at 2, F2R, scaled_mantissa, canonic_exp; simpl.
  rewrite Hl2; rewrite Hx2_1; rewrite Hlx''.
  rewrite Rmult_plus_distr_r; bpow_simplify.
  rewrite Hx2_2; bpow_simplify.
  assert (Hfl : (Zfloor (Z2R (Zfloor (x2 * bpow (- fexp2 (ln_beta x))))
                         + / 2)
                 = Zfloor (x2 * bpow (- fexp2 (ln_beta x))))%Z).
  { apply Zfloor_imp; split.
    - rewrite <- (Rplus_0_r (Z2R _)) at 1.
      apply Rplus_le_compat_l; lra.
    - rewrite Z2R_plus.
      apply Rplus_lt_compat_l; simpl; lra. }
  unfold Znearest at 2.
  rewrite Hfl; replace (_ + / 2 - _) with (/ 2) by ring.
  rewrite Rcompare_Eq; [|reflexivity].
  assert (H : (0 <=? Zfloor (x2 * bpow (- fexp2 (ln_beta x))))%Z = true);
    [|rewrite H; simpl; clear H].
  { apply Zle_bool_true.
    apply le_Z2R; simpl.
    apply (Rmult_le_reg_r (bpow (fexp2 (ln_beta x))));
      [now apply bpow_gt_0|rewrite Rmult_0_l].
    now rewrite <- Hx2_2; apply Rlt_le. }
  assert (Hce : (Zceil (Z2R (Zfloor (x2 * bpow (- fexp2 (ln_beta x))))
                        + / 2)
                 = Zfloor (x2 * bpow (- fexp2 (ln_beta x))) + 1)%Z).
  { apply Zceil_imp; split.
    - unfold Zminus; rewrite <- Zplus_assoc; rewrite Z2R_plus.
      apply Rplus_lt_compat_l; simpl; lra.
    - rewrite Z2R_plus.
      apply Rplus_le_compat_l; simpl; lra. }
  rewrite Hce.
  rewrite Z2R_plus; rewrite Rmult_plus_distr_r; simpl.
  rewrite <- Hx2_2; rewrite Rmult_1_l.
  replace (x2 + _) with (x2 + / 2 * bpow (fexp2 (ln_beta x))
                         + / 2 * bpow (fexp2 (ln_beta x))) by field.
  rewrite <- Hx2_3; unfold x''.
  rewrite <- Rmult_plus_distr_r.
  replace (Z2R m) with (/ 2 * (2 * Z2R m)) by field.
  rewrite <- (Rmult_1_r (/ 2)) at 2; rewrite <- Rmult_plus_distr_l.
  change 2 with (Z2R 2) at 2; rewrite <- Z2R_mult.
  change 1 with (Z2R 1) at 3; rewrite <- Z2R_plus.
  rewrite <- Hm.
  unfold Zminus; rewrite Zplus_comm; rewrite bpow_plus.
  rewrite <- Rmult_assoc; rewrite (Rmult_assoc (/ 2)).
  rewrite <- bpow_1; bpow_simplify.
  replace (/ 2 * _) with x.
  set (rd2 := round beta fexp1 ZnearestA
                    (x + / 2 * bpow (fexp2 (ln_beta x)))).
  unfold rd1; rewrite Xmid'.
  unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
  replace (fexp1 _) with (fexp1 (ln_beta x)); [|now rewrite Xmid'].
  unfold u, ulp, canonic_exp; bpow_simplify.
  unfold Znearest.
  assert (Zfh : (Zfloor (/ 2) = 0)%Z);
    [now apply Zfloor_imp; split; simpl; lra|].
  rewrite Zfh; simpl.
  unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r.
  rewrite Rcompare_Eq; [|reflexivity]; simpl.
  assert (Zch : (Zceil (/ 2) = 1)%Z);
    [now apply Zceil_imp; split; simpl; lra|].
  rewrite Zch; simpl; rewrite Rmult_1_l.
  unfold rd2; clear rd2.
  assert (Hlx' : ln_beta (x + / 2 * bpow (fexp2 (ln_beta x)))
                 = fexp1 (ln_beta x) :> Z).
  { apply ln_beta_unique; split.
    - apply Rabs_ge; right.
      apply Rle_trans with (/2 * u).
      + unfold Zminus; rewrite Zplus_comm; rewrite bpow_plus.
        rewrite bpow_opp; rewrite bpow_1.
        apply Rmult_le_compat.
        * apply Rlt_le; apply Rinv_0_lt_compat.
          change 0 with (Z2R 0); apply Z2R_lt; omega.
        * apply bpow_ge_0.
        * apply Rinv_le; [lra|].
          now change 2 with (Z2R 2); apply Z2R_le.
        * unfold u, ulp, canonic_exp; apply Rle_refl.
      + rewrite <- (Rplus_0_r (/ 2 * u)).
        rewrite Xmid'.
        apply Rplus_le_compat_l.
        apply Rmult_le_pos; [lra|].
        apply bpow_ge_0.
    - rewrite Rabs_right.
      + rewrite Xmid' at 1.
        rewrite <- Rmult_plus_distr_l.
        apply Rlt_le_trans with (/ 2 * (2 * u)).
        * apply Rmult_lt_compat_l; [lra|].
          rewrite Rmult_plus_distr_r; rewrite Rmult_1_l.
          apply Rplus_lt_compat_l.
          unfold u, ulp, canonic_exp; apply bpow_lt.
          omega.
        * replace (/ 2 * _) with u by field.
          unfold u, ulp, canonic_exp; apply Rle_refl.
      + apply Rle_ge.
        apply Rplus_le_le_0_compat.
        * now apply Rlt_le.
        * apply Rmult_le_pos; [lra|].
          apply bpow_ge_0. }
  unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
  rewrite Hlx'.
  do 2 rewrite <- Hlx.
  rewrite <- Rmult_1_l; apply Rmult_eq_compat_r.
  unfold Znearest.
  assert (Hfl' : (Zfloor ((x + / 2 * bpow (fexp2 (ln_beta x)))
                          * bpow (- ln_beta x)) = 0)%Z).
  { apply Zfloor_imp; split; simpl.
    - apply (Rmult_le_reg_r (bpow (ln_beta x))); [now apply bpow_gt_0|].
      rewrite Rmult_0_l; bpow_simplify.
      apply Rplus_le_le_0_compat.
      + now apply Rlt_le.
      + apply Rmult_le_pos; [lra|].
        apply bpow_ge_0. 
    - apply (Rmult_lt_reg_r (bpow (ln_beta x))); [now apply bpow_gt_0|].
      rewrite Rmult_1_l; bpow_simplify.
      apply Rlt_le_trans with (/ 2 * (2 * u)).
      * rewrite Xmid' at 1.
        rewrite <- Rmult_plus_distr_l.
        apply Rmult_lt_compat_l; [lra|].
        rewrite Rmult_plus_distr_r; rewrite Rmult_1_l.
        apply Rplus_lt_compat_l.
        unfold u, ulp, canonic_exp; apply bpow_lt.
        omega.
      * replace (/ 2 * _) with u by field.
        unfold u, ulp, canonic_exp; rewrite <- Hlx; apply Rle_refl. }
  rewrite Hfl'; simpl; unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r.
  assert (H : Rcompare ((x + / 2 * bpow (fexp2 (ln_beta x)))
                        * bpow (- ln_beta x)) (/ 2) = Gt);
    [|rewrite H; clear H; simpl].
  { apply Rcompare_Gt.
    apply (Rmult_lt_reg_r (bpow (ln_beta x))); [now apply bpow_gt_0|].
    bpow_simplify.
    rewrite Hlx at 1; change (bpow (fexp1 _)) with u.
    rewrite <- Xmid'.
    rewrite <- (Rplus_0_r x) at 1.
    apply Rplus_lt_compat_l.
    apply Rmult_lt_0_compat; [lra|].
    apply bpow_gt_0. }
  change 1 with (Z2R 1); apply f_equal; apply Zceil_imp; simpl; split.
  + apply Rmult_lt_0_compat; [|now apply bpow_gt_0].
    apply Rplus_lt_0_compat; [exact Px|].
    apply Rmult_lt_0_compat; [lra|].
    apply bpow_gt_0.
  + apply (Rmult_le_reg_r (bpow (ln_beta x))); [now apply bpow_gt_0|].
    rewrite Rmult_1_l; bpow_simplify.
    rewrite Xmid' at 1; rewrite <- Rmult_plus_distr_l.
    apply (Rmult_le_reg_l 2); [lra|].
    rewrite <- Rmult_assoc; replace (2 * _) with 1 by field;
    rewrite Rmult_1_l.
    rewrite Rmult_plus_distr_r; rewrite Rmult_1_l.
    unfold u, ulp, canonic_exp; rewrite <- Hlx.
    apply Rplus_le_compat_l; apply bpow_le; omega.
- (* rd <> 0 *)
  assert (Prd : 0 < rd).
  { assert (H : 0 <= rd); [|lra].
    rewrite <- (round_0 beta fexp1 Zfloor); unfold rd.
    apply round_le.
    - exact Vfexp1.
    - apply valid_rnd_DN.
    - now apply Rlt_le. }
  assert (Hlr : ln_beta x = ln_beta rd :> Z).
  { apply eq_sym.
      apply ln_beta_DN; [exact Vfexp1|].
      exact Prd. }
  destruct (midpoint_beta_odd_remains_pos rd Prd (fexp1 (ln_beta x))
                                          (fexp2 (ln_beta x)))
    as (x2,(Hx2_0,(Hx2_1,(Hx2_2,Hx2_3)))); [omega| |].
  { rewrite Hlr.
    rewrite <- Ztrunc_floor.
    - apply generic_format_round; [exact Vfexp1|].
      apply valid_rnd_DN. 
    - now apply Rmult_le_pos; [apply Rlt_le|apply bpow_ge_0]. }
  change (bpow (fexp1 _)) with u in Hx2_3.
  rewrite <- Xmid' in Hx2_3.
  set (rd1 := round beta fexp1 ZnearestA x).
  rewrite Hx2_3.
  unfold round at 2, F2R, scaled_mantissa, canonic_exp; simpl.
  rewrite <- Hx2_3.
  assert (Hfl : Z2R (Zfloor (x * bpow (- fexp2 (ln_beta x))))
                = x2 * bpow (- fexp2 (ln_beta x))).
  { rewrite Hx2_3 at 1.
    rewrite Rmult_plus_distr_r; bpow_simplify.
    rewrite Hx2_2; bpow_simplify.
    apply f_equal.
    apply Zfloor_imp; split.
    - rewrite <- (Rplus_0_r (Z2R _)) at 1.
      apply Rplus_le_compat_l; lra.
    - rewrite Z2R_plus; simpl.
      apply Rplus_lt_compat_l; lra. }
  unfold Znearest at 2.
  rewrite Hfl.
  replace (x * _ - x2 * _) with (/ 2);
    [|now rewrite Hx2_3 at 1; rewrite Rmult_plus_distr_r; bpow_simplify; ring].
  rewrite Rcompare_Eq; [|reflexivity].
  rewrite Zle_bool_true;
    [|now apply le_Z2R; simpl; rewrite Hfl; apply Rmult_le_pos;
      [apply Rlt_le|apply bpow_ge_0]].
  assert (Hce : Z2R (Zceil (x * bpow (- fexp2 (ln_beta x))))
                * bpow (fexp2 (ln_beta x))
                = x2 + bpow (fexp2 (ln_beta x))).
  { apply (Rmult_eq_reg_r (bpow (- fexp2 (ln_beta x))));
    [|now apply Rgt_not_eq; apply bpow_gt_0].
    rewrite Rmult_plus_distr_r; bpow_simplify.
    rewrite Hx2_2; bpow_simplify.
    change 1 with (Z2R 1); rewrite <- Z2R_plus; apply f_equal.
    rewrite Hx2_3 at 1.
    rewrite Rmult_plus_distr_r; bpow_simplify.
    rewrite Hx2_2 at 1; bpow_simplify.
    set (x2b := Zfloor (x2 * bpow (- fexp2 (ln_beta x)))).
    apply Zceil_imp; split.
    - replace (_ - _)%Z with x2b by ring.
      rewrite <- (Rplus_0_r (Z2R _)) at 1; apply Rplus_lt_compat_l; lra.
    - rewrite Z2R_plus; simpl; apply Rplus_le_compat_l; lra. }
  rewrite Hce.
  unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
  set (f1 := fexp1 (ln_beta x)).
  set (f2 := fexp2 (ln_beta x)).
  assert (Hx2b2 : x2 + bpow f2 = x + / 2 * bpow f2).
  { apply (Rplus_eq_reg_r (- / 2 * bpow f2)); field_simplify.
    unfold Rdiv; apply Rmult_eq_compat_r.
    now rewrite Hx2_3; field_simplify. }
  assert (Hl2 : ln_beta (x2 + bpow f2) = ln_beta x :> Z).
  { rewrite Hx2b2.
    rewrite Hlr; rewrite Xmid'.
    rewrite Rplus_assoc.
    apply (ln_beta_plus_eps beta fexp1 rd Prd); [|split].
    - apply generic_format_round; [exact Vfexp1|apply valid_rnd_DN].
    - apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [lra|apply bpow_ge_0]).
    - rewrite <- Rmult_plus_distr_l.
      apply (Rmult_lt_reg_l 2); [lra|].
      rewrite <- Rmult_assoc; replace (2 * / 2) with 1 by field;
      rewrite Rmult_1_l.
      rewrite ulp_neq_0; trivial.
      unfold canonic_exp; rewrite <- Hlr; change (bpow (fexp1 _)) with u.
      rewrite Rmult_plus_distr_r; rewrite Rmult_1_l.
      apply Rplus_lt_compat_l; unfold u, ulp, canonic_exp, f2; apply bpow_lt.
      omega. }
  rewrite Hl2.
  rewrite Hx2b2.
  rewrite Xmid' at 1; rewrite Rplus_assoc.
  fold f1.
  assert (Hrd : rd * bpow (- f1) = Z2R (Zfloor (x * bpow (- f1)))).
  { unfold rd, round, F2R, scaled_mantissa, canonic_exp; simpl.
    now fold f1; bpow_simplify. }
  assert (Hfld : Z2R (Zfloor ((rd + (/ 2 * u + / 2 * bpow f2)) * bpow (- f1)))
                 = rd * bpow (- f1)).
  { rewrite Rmult_plus_distr_r; rewrite Hrd.
    apply f_equal.
    apply Zfloor_imp; split.
    - rewrite <- (Rplus_0_r (Z2R _)) at 1; apply Rplus_le_compat_l.
      apply Rmult_le_pos; [|now apply bpow_ge_0].
      apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [lra|apply bpow_ge_0]).
    - rewrite Z2R_plus; apply Rplus_lt_compat_l; simpl.
      apply (Rmult_lt_reg_r (bpow (f1))); [now apply bpow_gt_0|];
      rewrite Rmult_1_l; bpow_simplify.
      rewrite <- Rmult_plus_distr_l.
      apply (Rmult_lt_reg_l 2); [lra|]; rewrite <- Rmult_assoc.
      replace (2 * / 2) with 1 by field; rewrite Rmult_1_l.
      change (bpow f1) with u.
      rewrite Rmult_plus_distr_r; rewrite Rmult_1_l; apply Rplus_lt_compat_l.
      unfold f2, u, ulp, canonic_exp; apply bpow_lt; omega. }
  unfold Znearest.
  rewrite Hfld.
  replace (_ - rd * bpow _) with (/ 2 * (u + bpow f2) * bpow (- f1)) by ring.
  assert (H : / 2 < / 2 * (u + bpow f2) * bpow (- f1)).
  { unfold u, ulp, canonic_exp; fold f1.
    rewrite Rmult_assoc.
    rewrite <- (Rmult_1_r (/ 2)) at 1; apply Rmult_lt_compat_l; [lra|].
    rewrite Rmult_plus_distr_r; bpow_simplify.
    rewrite <- (Rplus_0_r 1) at 1; apply Rplus_lt_compat_l.
    apply bpow_gt_0. }
  rewrite Rcompare_Gt; [clear H|exact H].
  unfold rd1, round, F2R, scaled_mantissa, canonic_exp; simpl; fold f1.
  apply Rmult_eq_compat_r; apply f_equal.
  unfold Znearest.
  rewrite <- Hrd.
  rewrite <- Rmult_minus_distr_r.
  replace (x - rd) with (/ 2 * u).
  rewrite Rmult_assoc; unfold u, ulp, canonic_exp; fold f1; bpow_simplify.
  rewrite Rcompare_Eq; [|reflexivity].
  rewrite Zle_bool_true;
    [|now apply Zfloor_lub; simpl; apply Rmult_le_pos;
      [apply Rlt_le|apply bpow_ge_0]].
  rewrite Xmid'; do 3 rewrite Rmult_plus_distr_r.
  rewrite Hrd.
  bpow_simplify.
  apply eq_trans with (Zfloor (x *  bpow (- f1)) + 1)%Z; [|apply eq_sym];
  apply Zceil_imp; split.
  + unfold Zminus; rewrite <- Zplus_assoc; rewrite Z2R_plus.
    replace (1 + _)%Z with Z0 by ring; simpl; apply Rplus_lt_compat_l.
    apply Rplus_lt_0_compat; [lra|].
    apply Rmult_lt_0_compat; [lra|apply bpow_gt_0].
  + rewrite Z2R_plus; apply Rplus_le_compat_l; simpl.
    apply (Rplus_le_reg_r (- / 2)); ring_simplify.
    apply (Rmult_le_reg_l (/ 2)); [lra|].
    field_simplify; unfold Rdiv; apply Rmult_le_compat_r; [lra|].
    change 1 with (bpow 0); apply bpow_le; unfold f1, f2; omega.
  + unfold Zminus; rewrite <- Zplus_assoc; rewrite Z2R_plus.
    replace (1 + _)%Z with Z0 by ring; simpl; apply Rplus_lt_compat_l.
    apply Rmult_lt_0_compat; [|now apply bpow_gt_0].
    apply Rmult_lt_0_compat; [lra|apply bpow_gt_0].
  + rewrite Z2R_plus; apply Rplus_le_compat_l; simpl.
    unfold u, ulp, canonic_exp; fold f1; bpow_simplify; lra.
Qed.      

Lemma double_round_eq_mid_beta_odd_rna_aux2 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall x,
  0 < x ->
  (fexp2 (ln_beta x) = fexp1 (ln_beta x))%Z ->
  (fexp1 (ln_beta x) <= ln_beta x)%Z ->
  x = midp beta fexp1 x ->
  round beta fexp1 ZnearestA (round beta fexp2 ZnearestA x)
  = round beta fexp1 ZnearestA x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 x Px Hf2 Hf1 Xmid.
assert (H : round beta fexp2 ZnearestA x = round beta fexp1 ZnearestA x).
{ unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
  now rewrite Hf2. }
rewrite round_generic.
- exact H.
- apply valid_rnd_N.
- now rewrite H; apply generic_format_round; [|apply valid_rnd_N].
Qed.

(* double_round_eq_mid_beta_odd_rna_aux{1,2} together *)
Lemma double_round_eq_mid_beta_odd_rna_aux3 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall x,
  0 < x ->
  (fexp2 (ln_beta x) <= fexp1 (ln_beta x))%Z ->
  (fexp1 (ln_beta x) <= ln_beta x)%Z ->
  x = midp beta fexp1 x ->
  round beta fexp1 ZnearestA (round beta fexp2 ZnearestA x)
  = round beta fexp1 ZnearestA x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 x Px Hf2 Hf1 Xmid.
destruct (Zle_or_lt (fexp2 (ln_beta x)) (fexp1 (ln_beta x) - 1)) as [H1|H1].
- now apply double_round_eq_mid_beta_odd_rna_aux1.
- assert (H : fexp2 (ln_beta x) = fexp1 (ln_beta x)) by omega.
  now apply double_round_eq_mid_beta_odd_rna_aux2.
Qed.

(* double_round_eq_mid_beta_odd_rna_aux3 without the hypothesis
   fexp1 (ln_beta x) <= ln_beta x *)
Lemma double_round_eq_mid_beta_odd_rna_aux4 :
  forall (fexp1 fexp2 : Z -> Z),
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  forall x,
  0 < x ->
  (fexp2 (ln_beta x) <= fexp1 (ln_beta x))%Z ->
  x = midp beta fexp1 x ->
  round beta fexp1 ZnearestA (round beta fexp2 ZnearestA x)
  = round beta fexp1 ZnearestA x.
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 x Px Hf2 Xmid.
destruct (Zle_or_lt (fexp1 (ln_beta x)) (ln_beta x)) as [H1|H1].
{ (* fexp1 (ln_beta x) <= ln_beta x *)
  now apply double_round_eq_mid_beta_odd_rna_aux3. }
(* ln_beta x < fexp1 (ln_beta x) *)
revert Hf2 H1.
destruct (ln_beta x) as (ex,Hex); simpl.
specialize (Hex (Rgt_not_eq _ _ Px)).
intros Hf2 H1.
rewrite Rabs_right in Hex; [|now apply Rle_ge, Rlt_le].
rewrite (round_N_really_small_pos _ fexp1 _ x ex Hex H1).
destruct (Zle_or_lt (fexp1 ex) (fexp2 ex)) as [H2|H2].
- (* fexp1 ex = fexp2 ex *)
  replace (fexp1 ex) with (fexp2 ex) in H1; [|now apply Zle_antisym].
  rewrite (round_N_really_small_pos _ fexp2 _ x ex Hex H1).
  now rewrite round_0; [|apply valid_rnd_N].
- (* fexp2 (ln_beta x) < fexp1 (ln_beta x) *)
  set (r2 := round beta fexp2 ZnearestA x).
  destruct (Req_dec r2 0) as [Zr2|Nzr2].
  { (* r2 = 0 *)
    now rewrite Zr2, round_0; [|apply valid_rnd_N]. }
  (* r2 <> 0 *)
  assert (B1 : Rabs (r2 - x) <= / 2 * ulp beta fexp2 x);
    [now apply error_le_half_ulp|].
  unfold round, F2R, scaled_mantissa, canonic_exp; simpl.
  apply (Rmult_eq_reg_r (bpow (- fexp1 (ln_beta r2))));
    [|now apply Rgt_not_eq, bpow_gt_0].
  rewrite Rmult_0_l; bpow_simplify.
  change 0 with (Z2R 0); apply f_equal, Znearest_imp.
  simpl; unfold Rminus; rewrite Ropp_0, Rplus_0_r.
  rewrite Rabs_mult, (Rabs_right (bpow _)); [|now apply Rle_ge, bpow_ge_0].
  apply (Rmult_lt_reg_r (bpow (fexp1 (ln_beta r2)))); [now apply bpow_gt_0|].
  bpow_simplify.
  replace r2 with (r2 - x + x) by ring.
  apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)).
  apply Rlt_le_trans with (/ 2 * ulp beta fexp2 x + bpow ex);
    [now apply Rplus_le_lt_compat;
      [|rewrite Rabs_right; [|apply Rle_ge, Rlt_le]]|].
  replace (_ - _ + _) with r2 by ring.
  assert (Hbeta : (2 <= beta)%Z).
  { destruct beta as (beta_val,beta_prop).
    now apply Zle_bool_imp_le. }
  assert (Hex' : ln_beta x = ex :> Z).
  { now apply ln_beta_unique;
    rewrite Rabs_right; [|apply Rle_ge, Rlt_le]. }
  assert (Hl2 : (ln_beta r2 <= fexp1 ex)%Z).
  { apply (ln_beta_le_bpow _ _ _ Nzr2).
    replace r2 with (r2 - x + x) by ring.
    apply (Rle_lt_trans _ _ _ (Rabs_triang _ _)).
    apply Rlt_le_trans with (/ 2 * ulp beta fexp2 x + bpow ex);
      [now apply Rplus_le_lt_compat;
        [|rewrite Rabs_right; [|apply Rle_ge, Rlt_le]]|].
    apply Rle_trans with (2 * bpow (fexp1 ex - 1)).
    - rewrite Rmult_plus_distr_r, Rmult_1_l.
      apply Rplus_le_compat; [|now apply bpow_le; omega].
      apply Rle_trans with (bpow (fexp2 ex)); [|now apply bpow_le; omega].
      rewrite <- (Rmult_1_l (bpow _)).
      rewrite ulp_neq_0; try now apply Rgt_not_eq.
      unfold canonic_exp.
      rewrite Hex'; apply Rmult_le_compat_r; [apply bpow_ge_0|lra].
    - rewrite <- (Rmult_1_l (bpow (fexp1 _))).
      unfold Zminus; rewrite Zplus_comm, bpow_plus, <- Rmult_assoc.
      apply Rmult_le_compat_r; [now apply bpow_ge_0|].
      apply (Rmult_le_reg_r (bpow 1)); [now apply bpow_gt_0|].
      rewrite Rmult_1_l; bpow_simplify.
      simpl; unfold Z.pow_pos; simpl; rewrite Zmult_1_r.
      now change 2 with (Z2R 2); apply Z2R_le. }
  assert (Hf1r2 : fexp1 (ln_beta r2) = fexp1 ex).
  { now apply (proj2 (Vfexp1 ex)); [omega|]. }
  rewrite Hf1r2.
  replace (bpow ex) with (/ 2 * (2 * bpow ex)) by field.
  rewrite <- Rmult_plus_distr_l; apply Rmult_le_compat_l; [lra|].
  apply Rle_trans with (3 * bpow (fexp1 ex - 1)).
  + rewrite (Rmult_plus_distr_r _ 2); rewrite Rmult_1_l; apply Rplus_le_compat.
    * rewrite ulp_neq_0; try now apply Rgt_not_eq.
      apply bpow_le; unfold canonic_exp; rewrite Hex'; omega.
    * apply Rmult_le_compat_l; [lra|]; apply bpow_le; omega.
  + rewrite <- (Rmult_1_l (bpow (fexp1 _))).
    unfold Zminus; rewrite Zplus_comm, bpow_plus, <- Rmult_assoc.
    apply Rmult_le_compat_r; [now apply bpow_ge_0|].
    apply (Rmult_le_reg_r (bpow 1)); [now apply bpow_gt_0|].
    rewrite Rmult_1_l; bpow_simplify.
    simpl; unfold Z.pow_pos; simpl; rewrite Zmult_1_r.
    change 3 with (Z2R 3); apply Z2R_le.
    destruct (Zle_or_lt beta 2) as [Hb2|Hb2]; [|omega].
    assert (Hbeta' : beta = 2%Z :> Z); [now apply Zle_antisym|].
    casetype False.
    rewrite <- Zodd_ex_iff in Obeta.
    apply (Zodd_not_Zeven _ Obeta).
    now rewrite Hbeta'.
Qed.

Lemma double_round_div_beta_odd_rna_aux :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  (forall ex, (fexp2 ex <= fexp1 ex)%Z) ->
  forall x y,
  0 < x -> 0 < y ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round beta fexp1 ZnearestA (round beta fexp2 ZnearestA (x / y))
  = round beta fexp1 ZnearestA (x / y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 Hexp x y Px Py Fx Fy.
assert (Pxy : 0 < x / y).
{ now unfold Rdiv; apply Rmult_lt_0_compat; [|apply Rinv_0_lt_compat]. }
specialize (Hexp (ln_beta (x / y))).
destruct (Req_dec (x / y) (midp beta fexp1 (x / y))) as [Mid|Nmid].
- now apply double_round_eq_mid_beta_odd_rna_aux4.
- now apply neq_midpoint_beta_odd.
Qed.

Lemma double_round_div_beta_odd_rna :
  forall fexp1 fexp2 : Z -> Z,
  Valid_exp fexp1 -> Valid_exp fexp2 ->
  (forall ex, (fexp2 ex <= fexp1 ex)%Z) ->
  forall x y,
  y <> 0 ->
  generic_format beta fexp1 x ->
  generic_format beta fexp1 y ->
  round beta fexp1 ZnearestA (round beta fexp2 ZnearestA (x / y))
  = round beta fexp1 ZnearestA (x / y).
Proof.
intros fexp1 fexp2 Vfexp1 Vfexp2 Hexp x y Nzy Fx Fy.
destruct (Rtotal_order x 0) as [Nx|[Zx|Px]].
- (* x < 0 *)
  destruct (Rtotal_order y 0) as [Ny|[Zy|Py]].
  + (* y < 0 *)
    rewrite <- (Ropp_involutive x).
    rewrite <- (Ropp_involutive y).
    rewrite Ropp_div.
    unfold Rdiv; rewrite <- Ropp_inv_permute; [|lra].
    rewrite Ropp_mult_distr_r_reverse.
    rewrite Ropp_involutive.
    fold ((- x) / (- y)).
    apply Ropp_lt_contravar in Nx.
    apply Ropp_lt_contravar in Ny.
    rewrite Ropp_0 in Nx, Ny.
    apply generic_format_opp in Fx.
    apply generic_format_opp in Fy.
    now apply double_round_div_beta_odd_rna_aux.
  + (* y = 0 *)
    now casetype False; apply Nzy.
  + (* y > 0 *)
    rewrite <- (Ropp_involutive x).
    rewrite Ropp_div.
    do 3 rewrite round_NA_opp.
    apply Ropp_eq_compat.
    apply Ropp_lt_contravar in Nx.
    rewrite Ropp_0 in Nx.
    apply generic_format_opp in Fx.
    now apply double_round_div_beta_odd_rna_aux.
- (* x = 0 *)
  rewrite Zx.
  unfold Rdiv; rewrite Rmult_0_l.
  now rewrite round_0; [|apply valid_rnd_N].
- (* x > 0 *)
  destruct (Rtotal_order y 0) as [Ny|[Zy|Py]].
  + (* y < 0 *)
    rewrite <- (Ropp_involutive y).
    unfold Rdiv; rewrite <- Ropp_inv_permute; [|lra].
    rewrite Ropp_mult_distr_r_reverse.
    do 3 rewrite round_NA_opp.
    apply Ropp_eq_compat.
    apply Ropp_lt_contravar in Ny.
    rewrite Ropp_0 in Ny.
    apply generic_format_opp in Fy.
    now apply double_round_div_beta_odd_rna_aux.
  + (* y = 0 *)
    now casetype False; apply Nzy.
  + (* y > 0 *)
    now apply double_round_div_beta_odd_rna_aux.
Qed.

Section Double_round_div_beta_odd_rna_FLX.

Require Import Fcore_FLX.

Variable prec : Z.
Variable prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem double_round_div_rna_FLX :
  (prec <= prec')%Z ->
  forall x y,
  y <> 0 ->
  FLX_format beta prec x -> FLX_format beta prec y ->
  round beta (FLX_exp prec) ZnearestA
        (round beta (FLX_exp prec') ZnearestA (x / y))
  = round beta (FLX_exp prec) ZnearestA (x / y).
Proof.
intros Hprec x y Nzy Fx Fy.
apply double_round_div_beta_odd_rna.
- now apply FLX_exp_valid.
- now apply FLX_exp_valid.
- intro ex; unfold FLX_exp; omega.
- exact Nzy.
- now apply generic_format_FLX.
- now apply generic_format_FLX.
Qed.

End Double_round_div_beta_odd_rna_FLX.

Section Double_round_div_beta_odd_rna_FLT.

Require Import Fcore_FLX.
Require Import Fcore_FLT.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem double_round_div_rna_FLT :
  (emin' <= emin)%Z ->
  (prec <= prec')%Z ->
  forall x y,
  y <> 0 ->
  FLT_format beta emin prec x -> FLT_format beta emin prec y ->
  round beta (FLT_exp emin prec) ZnearestA
        (round beta (FLT_exp emin' prec') ZnearestA (x / y))
  = round beta (FLT_exp emin prec) ZnearestA (x / y).
Proof.
intros Hemin Hprec x y Nzy Fx Fy.
apply double_round_div_beta_odd_rna.
- now apply FLT_exp_valid.
- now apply FLT_exp_valid.
- intro ex; unfold FLT_exp.
  generalize (Zmax_spec (ex - prec) emin).
  generalize (Zmax_spec (ex - prec') emin').
  omega.
- exact Nzy.
- now apply generic_format_FLT.
- now apply generic_format_FLT.
Qed.

End Double_round_div_beta_odd_rna_FLT.

Section Double_round_div_beta_odd_rna_FTZ.

Require Import Fcore_FLX.
Require Import Fcore_FTZ.

Variable emin prec : Z.
Variable emin' prec' : Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.
Context { prec_gt_0_' : Prec_gt_0 prec' }.

Theorem double_round_div_rna_FTZ :
  (emin' + prec' <= emin + prec)%Z ->
  (prec <= prec')%Z ->
  forall x y,
  y <> 0 ->
  FTZ_format beta emin prec x -> FTZ_format beta emin prec y ->
  round beta (FTZ_exp emin prec) ZnearestA
        (round beta (FTZ_exp emin' prec') ZnearestA (x / y))
  = round beta (FTZ_exp emin prec) ZnearestA (x / y).
Proof.
intros Hemin Hprec x y Nzy Fx Fy.
apply double_round_div_beta_odd_rna.
- now apply FTZ_exp_valid.
- now apply FTZ_exp_valid.
- intro ex; unfold FTZ_exp.
  unfold Prec_gt_0 in prec_gt_0_.
  destruct (Z.ltb_spec (ex - prec') emin');
  destruct (Z.ltb_spec (ex - prec) emin);
  omega.
- exact Nzy.
- now apply generic_format_FTZ.
- now apply generic_format_FTZ.
Qed.

End Double_round_div_beta_odd_rna_FTZ.

End Double_round_div_beta_odd_rna.

End Double_round_beta_odd.
