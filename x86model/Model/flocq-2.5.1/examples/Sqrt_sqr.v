Require Import Fcore.
Require Import Interval.Interval_tactic.

Section Sec1.

Open Scope R_scope.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Variable choice1 : Z -> bool.
Variable choice2 : Z -> bool.
Variable choice3 : Z -> bool.

Notation format := (generic_format beta (FLX_exp prec)).
Notation round_flx1 :=(round beta (FLX_exp prec) (Znearest choice1)).
Notation round_flx2 :=(round beta (FLX_exp prec) (Znearest choice2)).
Notation round_flx3 :=(round beta (FLX_exp prec) (Znearest choice3)).
Notation ulp_flx :=(ulp beta (FLX_exp prec)).
Notation pred_flx := (pred beta (FLX_exp prec)).

Hypothesis pGt1: (1 < prec)%Z.

Variables x:R.
Hypothesis xPos: 0 < x.
Hypothesis Fx: format x.

Let y:=round_flx1(x*x).
Let z:=round_flx2(sqrt y).


Theorem round_flx_sqr_sqrt_middle: x = sqrt (Z2R beta) * bpow (ln_beta beta x - 1) -> z=x.
Proof with auto with typeclass_instances.
intros Hx.
unfold z, y.
replace (round_flx1 (x * x)) with (bpow (2*ln_beta beta x -1)).
replace (sqrt (bpow (2 * ln_beta beta x - 1))) with x.
apply round_generic...
apply sym_eq, sqrt_lem_1.
apply bpow_ge_0.
now left.
rewrite Hx at 1.
rewrite Rmult_comm; rewrite Hx at 1.
apply trans_eq with ((sqrt (Z2R beta)*sqrt (Z2R beta)) * (bpow (ln_beta beta x-1)*bpow (ln_beta beta x-1))).
ring.
rewrite <- bpow_plus, sqrt_def, <- bpow_1, <- bpow_plus.
apply f_equal; ring.
left; apply radix_pos.
replace (x*x) with (bpow (2 * ln_beta beta x - 1)).
apply sym_eq, round_generic...
apply generic_format_bpow.
unfold FLX_exp; omega.
apply sym_eq; rewrite Hx at 1.
rewrite Rmult_comm; rewrite Hx at 1.
apply trans_eq with ((sqrt (Z2R beta)*sqrt (Z2R beta)) * (bpow (ln_beta beta x-1)*bpow (ln_beta beta x-1))).
ring.
rewrite <- bpow_plus, sqrt_def, <- bpow_1, <- bpow_plus.
apply f_equal; ring.
left; apply radix_pos.
Qed.

Theorem round_flx_sqr_sqrt_le: (beta <= 4)%Z -> z <= x.
Proof with auto with typeclass_instances.
intros Hb.
case (Req_dec x (sqrt (Z2R beta) * bpow (ln_beta beta x - 1))).
intros L; right; now apply round_flx_sqr_sqrt_middle.
intros Hx'.
assert (0 < x*x) by now apply Rmult_lt_0_compat.
assert (0 <= 1 + ulp_flx (x * x) / 2 / (x * x)).
rewrite <- (Rplus_0_l 0).
apply Rplus_le_compat; auto with real.
unfold Rdiv; apply Rmult_le_pos.
apply Rmult_le_pos; auto with real; apply ulp_ge_0.
left; auto with real.
assert (0 <= 1 + ulp_flx x / 2 / x).
rewrite <- (Rplus_0_l 0).
apply Rplus_le_compat; auto with real.
unfold Rdiv; apply Rmult_le_pos.
apply Rmult_le_pos; auto with real; apply ulp_ge_0.
left; auto with real.
(* *)
apply round_N_le_midp; try assumption...
apply Rlt_le_trans with (x*(1+ulp_flx x / 2 / x)).
2: right; rewrite succ_eq_pos; try now left.
2: field; auto with real.
apply Rle_lt_trans with (sqrt ((x*x)*(1+ulp_flx (x*x)/2/(x*x)))).
apply sqrt_le_1_alt.
apply Rplus_le_reg_l with (-x*x).
apply Rle_trans with (y-x*x);[right; ring|idtac].
apply Rle_trans with (/2*ulp_flx (x*x));[idtac|right; field; auto with real].
apply Rle_trans with (1:=RRle_abs _).
apply error_le_half_ulp...
rewrite sqrt_mult; auto with real.
rewrite sqrt_square; auto with real.
apply Rmult_lt_compat_l.
assumption.
rewrite <- (sqrt_square (1 + ulp_flx x / 2 / x)); try assumption.
apply sqrt_lt_1_alt.
split; try assumption.
apply Rmult_lt_reg_l with (2*x*x).
rewrite Rmult_assoc; apply Rmult_lt_0_compat; auto with real.
apply Rplus_lt_reg_r with (-2*x*x - ulp_flx x*ulp_flx x/2).
apply Rle_lt_trans with (ulp_flx (x*x) - ulp_flx x*ulp_flx x/2).
right; field.
auto with real.
apply Rlt_le_trans with (2*x*ulp_flx x).
2: right; field; auto with real.
apply Rle_lt_trans with (ulp_flx (x * x) + ulp_flx x * ulp_flx x / 2).
apply Rplus_le_compat_l.
apply Rplus_le_reg_r with (ulp_flx x * ulp_flx x / 2).
apply Rle_trans with 0;[right; ring|idtac].
apply Rle_trans with (ulp_flx x * ulp_flx x).
apply Rmult_le_pos; apply ulp_ge_0.
right; field.
rewrite 2!ulp_neq_0.
2: now apply Rgt_not_eq.
2: now apply Rgt_not_eq.
unfold canonic_exp, FLX_exp.
destruct (ln_beta beta x) as (e,He).
simpl.
assert (bpow (e - 1) <= x < bpow e).
rewrite <- (Rabs_right x).
apply He; auto with real.
apply Rle_ge; auto with real.
rewrite <- bpow_plus.
case (Rle_or_lt x (sqrt (Z2R (radix_val beta))*bpow (e-1))); intros Hx.
(* . *)
destruct Hx.
replace (ln_beta beta (x * x)-prec)%Z with (2*e-1-prec)%Z.
apply Rlt_le_trans with (bpow (2 * e - 1 - prec) + bpow (2*e - 1 - prec) / 2).
apply Rplus_lt_compat_l.
unfold Rdiv; apply Rmult_lt_compat_r.
auto with real.
apply bpow_lt.
omega.
apply Rle_trans with (2*bpow (2 * e - 1 - prec)).
apply Rle_trans with (3/2*bpow (2 * e - 1 - prec)).
right; field.
apply Rmult_le_compat_r.
apply bpow_ge_0.
interval.
rewrite Rmult_assoc; apply Rmult_le_compat_l.
auto with real.
apply Rle_trans with (bpow (e-1)*bpow (e - prec)).
rewrite <- bpow_plus.
apply bpow_le.
omega.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply H2.
apply f_equal with (f:= fun z => (z-prec)%Z).
apply sym_eq, ln_beta_unique.
rewrite Rabs_right.
split.
apply Rle_trans with (bpow (e-1)*bpow (e-1)).
rewrite <- bpow_plus.
right; apply f_equal; ring.
apply Rmult_le_compat; try apply H2; try apply bpow_ge_0.
apply Rlt_le_trans with ((sqrt (Z2R beta)*bpow (e-1))*(sqrt (Z2R beta)*bpow (e-1))).
apply Rmult_le_0_lt_compat; try apply H3; now left.
apply Rle_trans with ((sqrt (Z2R beta)*sqrt (Z2R beta)) * (bpow (e-1)*bpow (e-1))).
right; ring.
rewrite <- bpow_plus, sqrt_def, <- bpow_1, <- bpow_plus.
right; apply f_equal; ring.
left; apply radix_pos.
apply Rle_ge; auto with real.
(* . *)
simpl in Hx'; contradict H3; assumption.
(* . *)
replace (ln_beta beta (x * x)-prec)%Z with (2*e-prec)%Z.
case (Zle_lt_or_eq _ _ Hb); clear Hb; intros Hb.
(* .. *)
apply Rle_lt_trans with (2*(sqrt (Z2R beta) * bpow (e - 1))* bpow (e - prec)).
2: apply Rmult_lt_compat_r.
2: apply bpow_gt_0.
2: apply Rmult_lt_compat_l; try assumption.
2: auto with real.
apply Rle_trans with ((2 * sqrt (Z2R beta)) * bpow (2*e - 1- prec)).
2: replace (2*e)%Z with (e+e)%Z by ring; unfold Zminus.
2: repeat rewrite bpow_plus; right; ring.
apply Rle_trans with ((Z2R beta + /4)*bpow (2 * e - 1 - prec)).
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
rewrite <- bpow_1, <- bpow_plus.
right; apply f_equal; ring.
apply Rmult_le_reg_l with 4%R.
apply Rmult_lt_0_compat; auto with real.
apply Rle_trans with (2*bpow (e - prec + (e - prec))).
right; field.
apply Rle_trans with (bpow (2 * e - 1 - prec)).
2: right; field.
apply Rle_trans with (bpow (1+(e - prec + (e - prec)))).
rewrite (bpow_plus _ 1%Z).
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite bpow_1.
replace 2%R with (Z2R 2) by reflexivity; apply Z2R_le.
generalize (radix_gt_1 beta).
omega.
apply bpow_le.
omega.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert ((radix_val beta = 2%Z)%Z \/ radix_val beta = 3)%Z.
assert (1 < radix_val beta)%Z by apply radix_gt_1.
omega.
destruct H3; rewrite H3; simpl; interval.
(* .. *)
apply Rlt_le_trans with (2 * (2*bpow (e - 1)+bpow (e-prec)) * bpow (e - prec)).
apply Rlt_le_trans with (4* bpow (e - 1)* bpow (e - prec)
  + bpow (e - prec) * bpow (e - prec)*2).
2: right; ring.
replace (4 * bpow (e - 1) * bpow (e - prec)) with (bpow (2 * e - prec)).
apply Rplus_lt_compat_l.
rewrite <- bpow_plus.
unfold Rdiv; apply Rmult_lt_compat_l.
apply bpow_gt_0.
interval.
replace 4 with (bpow 1).
repeat rewrite <- bpow_plus.
apply f_equal; ring.
rewrite bpow_1, Hb; reflexivity.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rmult_le_compat_l.
auto with real.
apply Rle_trans with (2 * bpow (e - 1) + ulp_flx (2 * bpow (e - 1))).
apply Rplus_le_compat_l.
rewrite ulp_neq_0.
2: apply Rmult_integral_contrapositive_currified; apply Rgt_not_eq.
2: apply Rlt_0_2.
2: apply bpow_gt_0.
unfold canonic_exp, FLX_exp.
right; apply f_equal.
apply f_equal2; try reflexivity.
apply sym_eq, ln_beta_unique.
rewrite Rabs_right.
split.
rewrite <- (Rmult_1_l (bpow (e-1))) at 1.
apply Rmult_le_compat_r.
apply bpow_ge_0.
auto with real.
apply Rlt_le_trans with (Z2R beta*bpow (e - 1)).
apply Rmult_lt_compat_r.
apply bpow_gt_0.
rewrite Hb; simpl; interval.
rewrite <- bpow_1, <- bpow_plus.
right; apply f_equal; ring.
apply Rle_ge, Rmult_le_pos.
auto with real.
apply bpow_ge_0.
rewrite <- succ_eq_pos.
apply succ_le_lt...
apply generic_format_FLX.
exists (Float beta 2 (e-1)).
simpl; split.
unfold F2R; now simpl.
apply Zlt_le_trans with (4^1)%Z.
simpl; unfold Z.pow_pos; simpl; omega.
rewrite Hb.
apply Interval_missing.Zpower_le_exp_compat; omega.
apply Rle_lt_trans with (2:=Hx).
replace (sqrt (Z2R beta)) with 2%R.
now right.
rewrite Hb; simpl.
apply sym_eq, sqrt_square; auto with real.
apply Rmult_le_pos.
now auto with real.
apply bpow_ge_0.
apply f_equal with (f:= fun z => (z-prec)%Z).
apply sym_eq, ln_beta_unique.
rewrite Rabs_right.
split.
apply Rle_trans with ((sqrt (Z2R beta)*bpow (e-1))*(sqrt (Z2R beta)*bpow (e-1))).
apply Rle_trans with ((sqrt (Z2R beta)*sqrt (Z2R beta)) * (bpow (e-1)*bpow (e-1))).
2: right; ring.
rewrite <- bpow_plus, sqrt_def, <- bpow_1, <- bpow_plus.
right; apply f_equal; ring.
left; apply radix_pos.
apply Rmult_le_compat.
apply Rmult_le_pos; try apply sqrt_pos; apply bpow_ge_0.
apply Rmult_le_pos; try apply sqrt_pos; apply bpow_ge_0.
now left.
now left.
apply Rlt_le_trans with (bpow (e)*bpow (e)).
2: rewrite <- bpow_plus.
2: right; apply f_equal; ring.
apply Rmult_le_0_lt_compat; try apply H2.
now left.
now left.
apply Rle_ge; auto with real.
Qed.

Lemma ulp_sqr_ulp_lt: forall u, 0 < u ->
  (u < sqrt (Z2R (radix_val beta)) * bpow (ln_beta beta u-1)) ->
  ulp_flx (u * u) + ulp_flx u * ulp_flx u / 2 < 2 * u * ulp_flx u.
Proof with auto with typeclass_instances.
intros u Hu.
rewrite 2!ulp_neq_0.
2: now apply Rgt_not_eq.
2: now apply Rgt_not_eq, Rmult_lt_0_compat.
unfold canonic_exp, FLX_exp.
(* *)
destruct (ln_beta beta u) as (e,He); simpl.
intros Cu.
assert (He2:(bpow (e - 1) <= u < bpow e)).
rewrite <- (Rabs_right u).
apply He; auto with real.
apply Rle_ge; now left.
clear He.
destruct (ln_beta beta (u*u)) as (i,Hi); simpl.
assert (Hi2:(bpow (i - 1) <= u*u < bpow i)).
rewrite <- (Rabs_right (u*u)).
apply Hi; auto with real.
apply Rle_ge; apply Rmult_le_pos; auto with real.
clear Hi.
assert (i=2*e-1)%Z.
assert (2*e-2 < i /\ i-1 < 2*e-1)%Z;[idtac|omega].
split;apply lt_bpow with beta.
apply Rle_lt_trans with (2:=proj2 Hi2).
replace (2*e-2)%Z with ((e-1)+(e-1))%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat; try apply bpow_ge_0; apply He2.
apply Rle_lt_trans with (1:=proj1 Hi2).
apply Rlt_le_trans with  ((sqrt (Z2R beta) * bpow (e - 1))*(sqrt (Z2R beta) * bpow (e - 1))).
apply Rlt_trans with ((sqrt (Z2R beta) * bpow (e - 1))*u).
now apply Rmult_lt_compat_r.
apply Rmult_lt_compat_l.
apply Rlt_trans with (1:=Hu); assumption.
assumption.
right; apply trans_eq with ((sqrt (Z2R beta) * sqrt (Z2R beta)) *(bpow (e - 1) * bpow (e - 1)));[ring|idtac].
rewrite <- bpow_plus.
rewrite sqrt_sqrt.
replace (Z2R beta) with (bpow 1).
rewrite <- bpow_plus.
apply f_equal; ring.
apply bpow_1.
generalize (radix_gt_0 beta); intros.
replace 0 with (Z2R 0) by reflexivity; left; now apply Z2R_lt.
rewrite H.
apply Rlt_le_trans with (2 * bpow (e-1) * bpow (e - prec)).
rewrite Rmult_assoc, Rmult_plus_distr_r, Rmult_1_l.
rewrite <- 2!bpow_plus.
replace (e - 1 + (e - prec))%Z with (2 * e - 1 - prec)%Z by ring.
apply Rplus_lt_compat_l.
apply Rmult_lt_reg_l with 2%R; auto with real.
apply Rle_lt_trans with (bpow (e - prec + (e - prec))).
right; field.
apply Rlt_le_trans with (1*bpow (2 * e - 1 - prec)).
rewrite Rmult_1_l; apply bpow_lt.
omega.
apply Rmult_le_compat_r; auto with real.
apply bpow_ge_0.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rmult_le_compat_l; auto with real.
apply He2.
Qed.

Theorem round_flx_sqr_sqrt_exact_case1:
  (x < sqrt (Z2R (radix_val beta)) * bpow (ln_beta beta x-1)) ->
    z = x.
Proof with auto with typeclass_instances.
intros Cu.
case (Req_dec x (bpow (ln_beta beta x - 1))); intros Hx.
(* *)
unfold z, y.
rewrite Hx, <- bpow_plus.
rewrite (round_generic _ _ _ (bpow (ln_beta beta x - 1 + (ln_beta beta x - 1))))...
replace (sqrt (bpow (ln_beta beta x - 1 + (ln_beta beta x - 1)))) with (bpow (ln_beta beta x - 1 )).
apply round_generic...
apply generic_format_bpow.
unfold FLX_exp; auto with zarith.
apply sym_eq, sqrt_lem_1; try apply bpow_ge_0.
apply sym_eq, bpow_plus.
apply generic_format_bpow.
unfold FLX_exp; auto with zarith.
(* *)
assert (0 < x*x) by now apply Rmult_lt_0_compat.
assert (0 <= 1 - ulp_flx x / 2 / x).
apply Rplus_le_reg_l with (ulp_flx x / 2 / x); ring_simplify.
apply Rmult_le_reg_l with 2; auto with real.
apply Rmult_le_reg_l with x; auto with real.
apply Rle_trans with (ulp_flx x).
right; field; auto with real.
apply Rle_trans with x.
apply ulp_le_id; auto.
rewrite Rmult_1_r, <- (Rplus_0_l x) at 1.
rewrite Rmult_plus_distr_l, Rmult_1_r; auto with real.
assert (0 <= 1 - ulp_flx (x * x) / 2 / (x * x)).
apply Rplus_le_reg_l with (ulp_flx (x*x) / 2 / (x*x)); ring_simplify.
apply Rmult_le_reg_l with 2; auto with real.
apply Rmult_le_reg_l with (x*x); auto with real.
apply Rle_trans with (ulp_flx (x*x)).
right; field; auto with real.
apply Rle_trans with (x*x).
rewrite ulp_neq_0; try now apply Rgt_not_eq.
unfold canonic_exp, FLX_exp.
destruct (ln_beta beta (x*x)) as (e,He); simpl.
apply Rle_trans with (bpow (e-1)).
apply bpow_le; auto with zarith.
rewrite <- (Rabs_right (x*x)).
apply He; auto with real.
apply Rle_ge; auto with real.
rewrite Rmult_1_r, <- (Rplus_0_l (x*x)) at 1.
rewrite Rmult_plus_distr_l, Rmult_1_r; auto with real.
assert (0 <= 1 + ulp_flx x / 2 / x).
rewrite <- (Rplus_0_l 0).
apply Rplus_le_compat; auto with real.
unfold Rdiv; apply Rmult_le_pos.
apply Rmult_le_pos; auto with real; apply ulp_ge_0.
left; auto with real.
assert (0 <= 1 + ulp_flx (x * x) / 2 / (x * x)).
rewrite <- (Rplus_0_l 0).
apply Rplus_le_compat; auto with real.
unfold Rdiv; apply Rmult_le_pos.
apply Rmult_le_pos; auto with real; apply ulp_ge_0.
left; auto with real.
(* *)
apply sym_eq, Rle_antisym.
(* . *)
apply round_N_ge_midp; try assumption...
apply Rle_lt_trans with (x*(1-ulp_flx x / 2 / x)).
rewrite pred_eq_pos;[idtac|now left].
unfold pred_pos; rewrite Req_bool_false; trivial.
right; field; auto with real.
apply Rlt_le_trans with (sqrt ((x*x)*(1-ulp_flx (x*x)/2/(x*x)))).
rewrite sqrt_mult; auto with real.
rewrite sqrt_square; auto with real.
apply Rmult_lt_compat_l.
assumption.
rewrite <- (sqrt_square (1 - ulp_flx x / 2 / x)); try assumption.
apply sqrt_lt_1_alt.
split.
apply Rmult_le_pos; assumption.
apply Rmult_lt_reg_l with (2*x*x).
rewrite Rmult_assoc; apply Rmult_lt_0_compat; auto with real.
apply Rplus_lt_reg_r with (-2*x*x+2*x*ulp_flx x+ ulp_flx(x*x)).
apply Rle_lt_trans with (ulp_flx (x*x) + ulp_flx (x)*ulp_flx (x)/2).
right; field.
auto with real.
apply Rlt_le_trans with (2*x*ulp_flx x).
2: right; field; auto with real.
apply ulp_sqr_ulp_lt; auto.
apply sqrt_le_1_alt.
apply Rplus_le_reg_l with (-y+ulp_flx (x * x)/2).
apply Rle_trans with (-(y-x*x));[right; field; auto with real|idtac].
apply Rle_trans with (/2*ulp_flx (x*x));[idtac|right; field; auto with real].
apply Rle_trans with (1:=RRle_abs _).
rewrite Rabs_Ropp.
apply error_le_half_ulp...
(* . *)
apply round_N_le_midp; try assumption...
apply Rlt_le_trans with (x*(1+ulp_flx x / 2 / x)).
2: rewrite succ_eq_pos; try now left.
2: right; field; auto with real.
apply Rle_lt_trans with (sqrt ((x*x)*(1+ulp_flx (x*x)/2/(x*x)))).
apply sqrt_le_1_alt.
apply Rplus_le_reg_l with (-x*x).
apply Rle_trans with (y-x*x);[right; ring|idtac].
apply Rle_trans with (/2*ulp_flx (x*x));[idtac|right; field; auto with real].
apply Rle_trans with (1:=RRle_abs _).
apply error_le_half_ulp...
rewrite sqrt_mult; auto with real.
rewrite sqrt_square; auto with real.
apply Rmult_lt_compat_l.
assumption.
rewrite <- (sqrt_square (1 + ulp_flx x / 2 / x)); try assumption.
apply sqrt_lt_1_alt.
split; try assumption.
apply Rmult_lt_reg_l with (2*x*x).
rewrite Rmult_assoc; apply Rmult_lt_0_compat; auto with real.
apply Rplus_lt_reg_r with (-2*x*x - ulp_flx x*ulp_flx x/2).
apply Rle_lt_trans with (ulp_flx (x*x) - ulp_flx x*ulp_flx x/2).
right; field.
auto with real.
apply Rlt_le_trans with (2*x*ulp_flx x).
2: right; field; auto with real.
apply Rle_lt_trans with (ulp_flx (x * x) + ulp_flx x * ulp_flx x / 2).
2: apply ulp_sqr_ulp_lt; auto.
apply Rplus_le_compat_l.
apply Rplus_le_reg_r with (ulp_flx x * ulp_flx x / 2).
apply Rle_trans with 0;[right; ring|idtac].
apply Rle_trans with (ulp_flx x * ulp_flx x).
apply Rmult_le_pos; apply ulp_ge_0.
right; field.
Qed.

Theorem round_flx_sqr_sqrt_aux2: forall n,
 (0 <= n)%Z ->
 (2*Z2R n * bpow (prec-1) * ulp_flx x * (1+bpow (1-prec)/2) < x) ->
  round_flx3(x/(x-Z2R n*ulp_flx x)) <= 1.
Proof with auto with typeclass_instances.
intros n Hnp Hn.
apply round_N_le_midp...
replace 1 with (bpow 0) by reflexivity.
apply generic_format_bpow.
unfold FLX_exp; omega.
assert (0 < x - Z2R n*ulp_flx x).
apply Rplus_lt_reg_r with (Z2R n*ulp_flx x); ring_simplify.
apply Rle_lt_trans with (2:=Hn).
apply Rle_trans with (Z2R n*(ulp_flx x*((1*1)*(1+0))));[right; ring|idtac].
apply Rle_trans with (Z2R n*(ulp_flx x*(2*bpow (prec - 1)* (1 + bpow (1 - prec) / 2))));[idtac|right; ring].
apply Rmult_le_compat_l.
replace 0 with (Z2R 0) by reflexivity.
now apply Z2R_le.
apply Rmult_le_compat_l.
unfold ulp; apply ulp_ge_0.
apply Rmult_le_compat.
rewrite Rmult_1_l; apply Rle_0_1.
rewrite Rplus_0_r; apply Rle_0_1.
apply Rmult_le_compat; try apply Rle_0_1.
auto with real.
replace 1 with (bpow 0) by reflexivity.
apply bpow_le.
omega.
apply Rplus_le_compat_l.
unfold Rdiv; apply Rmult_le_pos.
apply bpow_ge_0.
auto with real.
apply Rmult_lt_reg_r with (x - Z2R n*ulp_flx x).
assumption.
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
2: auto with real.
apply Rplus_lt_reg_r with (-x+Z2R n*ulp_flx x + Z2R n*ulp_flx x* ulp_flx 1 * / 2); ring_simplify.
apply Rmult_lt_reg_l with (2*/ulp_flx 1).
apply Rmult_lt_0_compat.
auto with real.
apply Rinv_0_lt_compat.
rewrite ulp_neq_0; try apply bpow_gt_0.
apply Rgt_not_eq, Rlt_0_1.
apply Rlt_le_trans with x.
apply Rle_lt_trans with (2:=Hn).
replace  (ulp_flx 1) with (bpow (1-prec)).
rewrite <- bpow_opp.
replace ((-(1-prec)))%Z with (prec -1)%Z by ring.
right; unfold Rdiv; ring.
replace 1 with (bpow 0) by reflexivity.
rewrite ulp_bpow.
apply f_equal; unfold FLX_exp; omega.
rewrite succ_eq_pos.
right; field.
apply Rgt_not_eq.
rewrite ulp_neq_0; try apply bpow_gt_0.
apply Rgt_not_eq, Rlt_0_1.
apply Rle_0_1.
Qed.

End Sec1.

Section Sec2.

Open Scope R_scope.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Variable choice1 : Z -> bool.
Variable choice2 : Z -> bool.

Notation format := (generic_format beta (FLX_exp prec)).
Notation round_flx1 :=(round beta (FLX_exp prec) (Znearest choice1)).
Notation round_flx2 :=(round beta (FLX_exp prec) (Znearest choice2)).
Notation ulp_flx :=(ulp beta (FLX_exp prec)).
Notation pred_flx := (pred beta (FLX_exp prec)).

Hypothesis pGt1: (1 < prec)%Z.

Variables x:R.
Hypothesis xPos: 0 < x.
Hypothesis Fx: format x.
Hypothesis Hx: (sqrt (Z2R (radix_val beta)) * bpow (ln_beta beta x-1) < x).

Variable k:Z.
Hypothesis kpos: (0 <= k)%Z.
Hypothesis kLe: (k < radix_val beta)%Z.
Hypothesis kradix2 : (k = 0)%Z  \/  (2 < radix_val beta)%Z.

Let y:=round_flx1(x*x).
Let z:=round_flx2(sqrt y).
Let xk :=  x-Z2R k*ulp_flx x.

Lemma xkgt:  bpow (ln_beta beta x - 1) < xk.
Proof.
unfold xk.
case kradix2.
intros V; rewrite V; simpl; ring_simplify.
apply Rle_lt_trans with (2:=Hx).
rewrite <- (Rmult_1_l (bpow (ln_beta beta x - 1))) at 1.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert (2 <= beta)%Z.
clear; destruct beta as (v, Hr); simpl.
now apply Zle_bool_imp_le.
apply Z2R_le in H.
simpl in H; interval.
intros Hb.
apply Rle_lt_trans with (sqrt (Z2R beta) * bpow (ln_beta beta x - 1)
    - Z2R k * ulp_flx x).
rewrite ulp_neq_0; try now apply Rgt_not_eq.
unfold canonic_exp, FLX_exp.
apply Rle_trans with (bpow (ln_beta beta x - 1)
   *(sqrt (Z2R beta) -Z2R k * bpow (1-prec))).
rewrite <- (Rmult_1_r (bpow (ln_beta beta x - 1))) at 1.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply Rplus_le_reg_l with (Z2R k * bpow (1 - prec)).
apply Rle_trans with ((1-/Z2R beta) * bpow (2 - prec)+1).
apply Rplus_le_compat_r.
apply Rle_trans with (((1-/Z2R beta)*Z2R beta) * bpow (1 - prec)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rle_trans with (Z2R (beta-1)).
apply Z2R_le.
omega.
rewrite Z2R_minus; right.
simpl; field.
apply Rgt_not_eq, Rlt_gt.
replace 0 with (Z2R 0) by reflexivity.
apply Z2R_lt, radix_gt_0.
right; rewrite Rmult_assoc; apply f_equal.
rewrite <- bpow_1, <- bpow_plus.
apply f_equal; ring.
ring_simplify (Z2R k * bpow (1 - prec) + (sqrt (Z2R beta) - Z2R k * bpow (1 - prec))).
assert (H':(3 <= beta)%Z) by omega.
apply Z2R_le in H'; simpl in H'.
assert (H'':(1 <= Z2R beta)).
apply Rle_trans with (2:=H').
apply Rplus_le_reg_l with (-1); ring_simplify.
auto with real.
(* because p=2 is possible *)
case (Zle_lt_or_eq 3 beta).
omega.
intros H1; assert (H1':(4 <= beta)%Z) by omega.
apply Z2R_le in H1'; simpl in H1'.
apply Rle_trans with (1*1 +1).
apply Rplus_le_compat_r.
apply Rmult_le_compat.
apply Rplus_le_reg_l with (/Z2R beta); ring_simplify.
rewrite <- Rinv_1.
apply Rle_Rinv.
apply Rlt_0_1.
apply Rlt_le_trans with (2:=H''); auto with real.
exact H''.
apply bpow_ge_0.
apply Rplus_le_reg_l with (/Z2R beta-1); ring_simplify.
left; apply Rinv_0_lt_compat.
apply Rlt_le_trans with (2:=H''); auto with real.
apply Rle_trans with (bpow 0).
apply bpow_le.
omega.
right; reflexivity.
interval.
intros Hb'.
apply Rle_trans with ((1 - / Z2R beta) *1 +1).
apply Rplus_le_compat_r.
apply Rmult_le_compat_l.
apply Rplus_le_reg_l with (/Z2R beta); ring_simplify.
rewrite <- Rinv_1.
apply Rle_Rinv.
apply Rlt_0_1.
apply Rlt_le_trans with (2:=H''); auto with real.
exact H''.
apply Rle_trans with (bpow 0).
apply bpow_le.
omega.
right; reflexivity.
rewrite <- Hb'; simpl; interval.
right; ring_simplify.
apply f_equal.
apply trans_eq with (Z2R k *(bpow (ln_beta beta x - 1) * bpow (1 - prec))).
ring.
apply f_equal.
rewrite <- bpow_plus.
apply f_equal.
ring.
apply Rplus_lt_compat_r.
assumption.
Qed.

Lemma xklt: xk < bpow (ln_beta beta x).
Proof.
apply Rle_lt_trans with x.
apply Rplus_le_reg_l with (-xk); unfold xk; ring_simplify.
apply Rmult_le_pos.
replace 0 with (Z2R 0) by reflexivity.
apply Z2R_le, kpos.
apply ulp_ge_0.
apply Rle_lt_trans with (1:=RRle_abs _).
apply bpow_ln_beta_gt.
Qed.

Lemma xkpos: 0  < xk.
Proof.
apply Rle_lt_trans with (2:=xkgt).
apply bpow_ge_0.
Qed.

Lemma format_xminusk: format xk.
Proof with auto with typeclass_instances.
apply generic_format_FLX.
unfold generic_format in Fx.
exists  (Float beta (Ztrunc (scaled_mantissa beta (FLX_exp prec) x) - k)
                    (canonic_exp beta (FLX_exp prec) x)).
split.
unfold xk; rewrite Fx at 1; unfold F2R; simpl.
rewrite Z2R_minus; ring_simplify.
apply f_equal.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
apply Rmult_comm; apply f_equal.
simpl.
rewrite Z.abs_eq.
apply Zle_lt_trans with (Ztrunc (scaled_mantissa beta (FLX_exp prec) x) - 0)%Z.
apply Zplus_le_compat_l.
omega.
rewrite Zminus_0_r.
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow (canonic_exp beta (FLX_exp prec) x)).
apply bpow_gt_0.
apply Rle_lt_trans with x.
rewrite Fx at 3.
right; unfold F2R; reflexivity.
rewrite Z2R_Zpower.
rewrite <- bpow_plus.
unfold canonic_exp, FLX_exp.
replace  (prec + (ln_beta beta x - prec))%Z with (ln_beta beta x+0)%Z by ring.
rewrite Zplus_0_r.
apply Rle_lt_trans with (Rabs x).
apply RRle_abs.
apply bpow_ln_beta_gt...
omega.
apply le_Z2R.
apply Rmult_le_reg_r with (bpow (canonic_exp beta (FLX_exp prec) x)).
apply bpow_gt_0.
rewrite Rmult_0_l.
apply Rle_trans with xk.
left; apply xkpos.
right; unfold xk; rewrite Fx at 1; unfold F2R; simpl; rewrite Z2R_minus; ring_simplify.
apply f_equal.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
apply Rmult_comm; apply f_equal.
Qed.

Theorem round_flx_sqr_sqrt_aux1:
  (/ 2 * bpow (ln_beta beta x) <
      (2 * Z2R k + 1) * x -
           (Z2R k + / 2) * (Z2R k + / 2) * bpow (ln_beta beta x - prec)) ->
  xk <= z.
Proof with auto with typeclass_instances.
intros V.
apply round_N_ge_midp...
apply format_xminusk.
assert (Z:(ln_beta_val beta xk (ln_beta beta xk) = ln_beta beta x)%Z).
apply ln_beta_unique.
rewrite Rabs_right; try split.
left; now apply xkgt.
now apply xklt.
apply Rle_ge; left; now apply xkpos.
apply Rle_lt_trans with (x - Z2R k * ulp_flx x - ulp_flx x / 2).
rewrite pred_eq_pos.
2: left; apply xkpos.
unfold pred_pos; rewrite Req_bool_false.
2: apply Rgt_not_eq, Rlt_gt.
2: apply Rle_lt_trans with (2:=xkgt).
2: right; apply f_equal, f_equal2...
replace (ulp_flx xk) with (ulp_flx x).
unfold xk; right; field.
rewrite 2!ulp_neq_0; try apply Rgt_not_eq; try assumption.
unfold canonic_exp; now rewrite Z.
apply xkpos.
apply Rle_lt_trans with (x-(Z2R k+/2)*ulp_flx x).
right; unfold Rdiv; ring.
assert (0 <= x - (Z2R k + / 2) * ulp_flx x).
apply Rplus_le_reg_l with (/2*ulp_flx x).
rewrite Rplus_0_r.
apply Rle_trans with xk.
apply Rle_trans with (1*bpow (ln_beta beta x - 1)).
apply Rmult_le_compat.
auto with real.
apply ulp_ge_0.
interval.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
unfold canonic_exp, FLX_exp.
apply bpow_le; omega.
rewrite Rmult_1_l.
left; apply xkgt.
unfold xk; right; ring.
rewrite <- (sqrt_square (x - (Z2R k + / 2) * ulp_flx x)).
2: assumption.
apply sqrt_lt_1_alt.
split.
apply Rmult_le_pos; assumption.
apply Rlt_le_trans with (x*x - /2*bpow (2 * ln_beta beta x  - prec)).
rewrite ulp_neq_0; try now apply Rgt_not_eq.
unfold canonic_exp, FLX_exp.
apply Rplus_lt_reg_r with (-x*x).
apply Rle_lt_trans with
  (- (bpow (ln_beta beta x - prec)*((2*Z2R k +1)*x -
            (Z2R k + / 2)*  (Z2R k + / 2) * bpow (ln_beta beta x - prec)))).
right; field.
apply Rlt_le_trans with (- (bpow (ln_beta beta x - prec)*
    (/2*bpow (ln_beta beta x)))).
apply Ropp_lt_contravar.
apply Rmult_lt_compat_l.
apply bpow_gt_0.
exact V.
right; apply trans_eq with
  ((-/2)*(bpow (ln_beta beta x - prec)*bpow (ln_beta beta x))).
ring.
rewrite <- bpow_plus.
apply trans_eq with
  ((-/2)*bpow (2 * ln_beta beta x - prec)).
apply f_equal.
apply f_equal; ring.
ring.
apply Rplus_le_reg_l with (-y+/2*bpow (2 * ln_beta beta x  - prec)).
ring_simplify.
apply Rle_trans with (-(y-x*x)).
right; ring.
apply Rle_trans with (1:=RRle_abs _).
rewrite Rabs_Ropp.
apply Rle_trans with (1:=error_le_half_ulp _ _ _ _)...
apply Rmult_le_compat_l.
left; auto with real.
rewrite ulp_neq_0.
2: apply Rmult_integral_contrapositive_currified; now apply Rgt_not_eq.
unfold canonic_exp, FLX_exp.
apply bpow_le.
apply Zplus_le_compat_r.
apply ln_beta_le_bpow.
auto with real.
rewrite Rabs_mult.
replace (2*ln_beta beta x)%Z with (ln_beta beta x+ln_beta beta x)%Z by ring.
rewrite bpow_plus.
apply Rmult_le_0_lt_compat; try apply Rabs_pos; apply bpow_ln_beta_gt.
Qed.


Theorem round_flx_sqr_sqrt_aux1_simpl:
  (/ 2 * bpow (ln_beta beta x) + bpow (2+ln_beta beta x - prec) <= (2 * Z2R k + 1) * x)
  -> xk <= z.
Proof.
intros H; apply round_flx_sqr_sqrt_aux1.
apply Rplus_lt_reg_r with (bpow (2 + ln_beta beta x - prec)).
apply Rle_lt_trans with (1:=H).
apply Rplus_lt_reg_r with (-(2 * Z2R k + 1) * x + (Z2R k + / 2) * (Z2R k + / 2) * bpow (ln_beta beta x - prec)).
apply Rle_lt_trans with (((Z2R k + / 2) * (Z2R k + / 2) )* bpow (ln_beta beta x - prec)).
right; ring.
apply Rlt_le_trans with (bpow (2 + ln_beta beta x - prec)).
2: right; ring.
unfold Zminus; rewrite <- Zplus_assoc.
rewrite bpow_plus with (e1:=2%Z).
apply Rmult_lt_compat_r.
apply bpow_gt_0.
simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r, Z2R_mult.
assert (Z2R k + /2 < Z2R beta).
apply Rle_lt_trans with (Z2R (beta -1) + /2).
apply Rplus_le_compat_r.
apply Z2R_le.
omega.
rewrite Z2R_minus; simpl.
apply Rplus_lt_reg_r with (-Z2R beta + /2).
field_simplify.
unfold Rdiv; apply Rmult_lt_compat_r.
apply Rinv_0_lt_compat, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
exact Rlt_0_1.
assert (0 <= Z2R k + / 2).
replace 0 with (Z2R 0+0) by (simpl; ring); apply Rplus_le_compat.
apply Z2R_le, kpos.
apply Rlt_le, Rinv_0_lt_compat, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
now apply Rmult_le_0_lt_compat.
Qed.




End Sec2.

Section Sec3.

Open Scope R_scope.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Variable choice1 : Z -> bool.
Variable choice2 : Z -> bool.
Variable choice3 : Z -> bool.

Notation format := (generic_format beta (FLX_exp prec)).
Notation round_flx1 :=(round beta (FLX_exp prec) (Znearest choice1)).
Notation round_flx2 :=(round beta (FLX_exp prec) (Znearest choice2)).
Notation round_flx3 :=(round beta (FLX_exp prec) (Znearest choice3)).
Notation ulp_flx :=(ulp beta (FLX_exp prec)).
Notation pred_flx := (pred beta (FLX_exp prec)).

Hypothesis pGt2: (2 < prec)%Z.

Hypothesis pGt1: (1 < prec)%Z.

Variables x:R.
Hypothesis xPos: 0 < x.
Hypothesis Fx: format x.
Hypothesis Hx: (sqrt (Z2R (radix_val beta)) * bpow (ln_beta beta x-1) < x).

Let y:=round_flx1(x*x).
Let z:=round_flx2(sqrt y).

Theorem round_flx_sqr_sqrt_exact_aux: (radix_val beta <= 4)%Z ->
    z=x.
Proof with auto with typeclass_instances.
intros Hb.
apply Rle_antisym.
(* . *)
apply round_flx_sqr_sqrt_le...
(* . *)
assert (((radix_val beta = 2)%Z \/ (radix_val beta=3)%Z) \/ (radix_val beta=4)%Z).
generalize (radix_gt_1 beta); omega.
destruct H.
(* .. radix is 2 or 3 *)
apply Rle_trans with (x-Z2R 0 * ulp_flx x).
right; simpl; ring.
apply round_flx_sqr_sqrt_aux1...
omega.
apply radix_gt_0.
apply Rlt_le_trans with (x-/4*bpow (ln_beta beta x - prec)).
2: right; simpl; field.
apply Rle_lt_trans with (sqrt (Z2R beta) * bpow (ln_beta beta x - 1)
   - / 4 * bpow (ln_beta beta x - prec)).
2: apply Rplus_lt_compat_r; assumption.
apply Rle_trans with ((Z2R beta / 2)*bpow (ln_beta beta x-1)).
replace (bpow (ln_beta beta x)) with (bpow (1+(ln_beta beta x-1))).
rewrite bpow_plus, bpow_1.
right; unfold Rdiv; ring.
apply f_equal; ring.
apply Rle_trans with ((sqrt (Z2R beta) - /4* / Z2R beta)
    * bpow (ln_beta beta x-1)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
destruct H; rewrite H; simpl; interval.
rewrite Rmult_minus_distr_r.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
rewrite Rmult_assoc; apply Rmult_le_compat_l.
left; apply Rinv_0_lt_compat, Rmult_lt_0_compat; auto with real.
apply Rle_trans with (bpow (-1+(ln_beta beta x - 1))).
apply bpow_le; omega.
rewrite bpow_plus.
right; apply f_equal2; try reflexivity.
rewrite <- bpow_1, <- bpow_opp.
apply f_equal; reflexivity.
(* .. radix is 4 *)
assert (2 * bpow (ln_beta beta x - 1) < x).
apply Rle_lt_trans with (2:=Hx).
right; apply f_equal2; try reflexivity.
rewrite H; simpl.
apply sym_eq, sqrt_square; auto with real.
(* ... *)
assert ((2 * bpow (ln_beta beta x - 1)+1*bpow (ln_beta beta x - prec)) <= x).
assert (0 < 2 * bpow (ln_beta beta x - 1)).
apply Rmult_lt_0_compat.
auto with real.
apply bpow_gt_0.
assert (bpow (ln_beta beta x - prec)=ulp_flx (2 * bpow (ln_beta beta x - 1))).
rewrite ulp_neq_0; try now apply Rgt_not_eq.
unfold canonic_exp, FLX_exp.
apply f_equal.
apply f_equal2; try reflexivity.
apply sym_eq, ln_beta_unique.
rewrite Rabs_right.
2: apply Rle_ge; left; assumption.
split.
apply Rle_trans with (1*bpow (ln_beta beta x - 1)).
right; ring.
apply Rmult_le_compat_r.
apply bpow_ge_0.
auto with real.
apply Rlt_le_trans with (4*bpow (ln_beta beta x - 1)).
apply Rmult_lt_compat_r.
apply bpow_gt_0.
interval.
replace 4 with (Z2R 4) by reflexivity.
rewrite <- H, <- bpow_1, <- bpow_plus.
right; apply f_equal; ring.
rewrite H2, Rmult_1_l.
rewrite <- succ_eq_pos;[idtac|now left].
apply succ_le_lt...
apply generic_format_FLX.
exists (Float beta 2 (ln_beta beta x -1)).
simpl; split.
unfold F2R; simpl; ring.
rewrite H; apply Zlt_le_trans with (4^1)%Z.
simpl; unfold Z.pow_pos; simpl; omega.
apply Interval_missing.Zpower_le_exp_compat; omega.
(* ... *)
apply Rle_trans with (x-Z2R 0 * ulp_flx x).
right; simpl; ring.
apply round_flx_sqr_sqrt_aux1...
omega.
apply radix_gt_0.
apply Rlt_le_trans with (x-/4*bpow (ln_beta beta x - prec)).
2: right; simpl; field.
apply Rlt_le_trans with ( (2* bpow (ln_beta beta x - 1) +  1 * bpow (ln_beta beta x - prec))
   - / 4 * bpow (ln_beta beta x - prec)).
2: apply Rplus_le_compat_r; assumption.
apply Rlt_le_trans with ((/2 + (1-/4)*bpow (-prec))
    * bpow (ln_beta beta x)).
apply Rmult_lt_compat_r.
apply bpow_gt_0.
apply Rle_lt_trans with (/2+0);[right; ring|idtac].
apply Rplus_lt_compat_l.
apply Rmult_lt_0_compat.
interval.
apply bpow_gt_0.
unfold Zminus; repeat rewrite bpow_plus.
replace (bpow (- (1))) with (/4).
right; field.
rewrite bpow_opp, bpow_1, H; reflexivity.
Qed.


Let k:=(Zceil (x*bpow (1-ln_beta beta x)/(2+bpow (1-prec))) -1)%Z.

Lemma kpos: (0 <= k)%Z.
assert (0 < x*bpow (1-ln_beta beta x)/(2+bpow (1-prec))).
apply Fourier_util.Rlt_mult_inv_pos.
apply Rmult_lt_0_compat.
assumption.
apply bpow_gt_0.
rewrite Rplus_comm, <-Rplus_assoc; apply Rle_lt_0_plus_1, Rlt_le, Rle_lt_0_plus_1.
apply bpow_ge_0.
assert (0 < Zceil (x * bpow (1 - ln_beta beta x) / (2+bpow (1-prec))))%Z.
apply lt_Z2R; simpl (Z2R 0).
apply Rlt_le_trans with (1:=H).
apply Zceil_ub.
unfold k; omega.
Qed.

Lemma kLe: (k < radix_val beta)%Z.
cut (Zceil (x * bpow (1 - ln_beta beta x) / (2+bpow (1-prec))) <= beta)%Z.
unfold k; omega.
apply Zceil_glb.
apply Rle_trans with (bpow 1 / 1).
unfold Rdiv; apply Rmult_le_compat.
apply Rmult_le_pos; try apply bpow_ge_0; now left.
apply Rlt_le, Rinv_0_lt_compat.
rewrite Rplus_comm, <-Rplus_assoc; apply Rle_lt_0_plus_1, Rlt_le, Rle_lt_0_plus_1.
apply bpow_ge_0.
apply Rle_trans with (bpow (ln_beta beta x)*bpow (1 - ln_beta beta x)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rle_trans with (1:=RRle_abs _).
left; apply bpow_ln_beta_gt.
rewrite <- bpow_plus.
apply bpow_le; omega.
apply Rinv_le.
exact Rlt_0_1.
apply Rplus_le_reg_l with (-1); ring_simplify.
apply Rlt_le, Rle_lt_0_plus_1, bpow_ge_0.
rewrite bpow_1; right; field.
Qed.

Lemma kLe2: (k <= Zceil (Z2R(radix_val beta)/ 2) -1)%Z.
cut (Zceil (x * bpow (1 - ln_beta beta x) / (2+bpow (1-prec)))
   <= Zceil (Z2R(radix_val beta)/ 2))%Z.
unfold k; omega.
apply Zceil_glb.
apply Rle_trans with (bpow 1 / 2).
unfold Rdiv; apply Rmult_le_compat.
apply Rmult_le_pos.
now left.
apply bpow_ge_0.
apply Rlt_le, Rinv_0_lt_compat.
rewrite Rplus_comm, <-Rplus_assoc.
apply Rle_lt_0_plus_1, Rlt_le, Rle_lt_0_plus_1, bpow_ge_0.
apply Rle_trans with (bpow (ln_beta beta x)*bpow (1 - ln_beta beta x)).
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rle_trans with (1:=RRle_abs _).
left; apply bpow_ln_beta_gt.
rewrite <- bpow_plus.
apply bpow_le; omega.
apply Rinv_le.
apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rplus_le_reg_l with (-2); ring_simplify.
apply bpow_ge_0.
rewrite bpow_1.
apply Zceil_ub.
Qed.



Lemma round_flx_sqr_sqrt_snd_deg: 
  (((radix_val beta=5)%Z /\ (3 < prec)%Z) \/ (5 < radix_val beta)%Z) ->
    sqrt (Z2R beta) + / 4 * bpow (3 - prec) <=
      Z2R beta * (2 - bpow (1 - prec)) / (2 * (2 + bpow (1 - prec))).
Proof.
intros H; destruct H.
(* radix=5 *)
destruct H as (H1,H2).
apply Rle_trans with (sqrt (Z2R beta) + / (4 *Z2R (beta))).
apply Rplus_le_compat_l.
rewrite (Rinv_mult_distr 4).
apply Rmult_le_compat_l.
apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rle_trans with (bpow (-(1))).
apply bpow_le; omega.
right; rewrite bpow_opp.
apply f_equal, bpow_1.
apply Rgt_not_eq, Rmult_lt_0_compat; apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rgt_not_eq, radix_pos.
apply Rle_trans with (Z2R beta * (2-/(Z2R beta*Z2R beta)) / (2* (2 + /(Z2R beta*Z2R beta)))).
rewrite H1;simpl; interval.
unfold Rdiv; rewrite 2!Rmult_assoc.
apply Rmult_le_compat_l.
left; apply radix_pos.
apply Rmult_le_compat.
rewrite H1; simpl; interval.
rewrite H1; simpl; interval.
apply Rplus_le_reg_l with (-2); ring_simplify.
apply Ropp_le_contravar.
apply Rle_trans with (bpow (-(2))).
apply bpow_le; omega.
right; rewrite bpow_opp.
apply f_equal; simpl; unfold Z.pow_pos; simpl.
rewrite <- Z2R_mult; apply f_equal; ring.
apply Rinv_le.
apply Rmult_lt_0_compat.
apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
rewrite Rplus_comm, <- Rplus_assoc.
apply Rle_lt_0_plus_1, Rlt_le,Rle_lt_0_plus_1, bpow_ge_0.
apply Rmult_le_compat_l.
apply Rlt_le,Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rplus_le_compat_l.
apply Rle_trans with (bpow (-(2))).
apply bpow_le; omega.
right; rewrite bpow_opp.
apply f_equal; simpl; unfold Z.pow_pos; simpl.
rewrite <- Z2R_mult; apply f_equal; ring.
(* radix > 5 *)
apply Rle_trans with (sqrt (Z2R beta) + /4*1).
apply Rplus_le_compat_l.
apply Rmult_le_compat_l.
apply Rlt_le, Rinv_0_lt_compat,  Rmult_lt_0_compat; apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rle_trans with (bpow 0).
apply bpow_le; omega.
right; reflexivity.
rewrite Rmult_1_r.
assert (6 <= Z2R beta).
replace 6 with (Z2R 6) by reflexivity.
apply Z2R_le; omega.
apply Rle_trans with (Z2R beta*(12/25)).
apply Rplus_le_reg_l with (-sqrt (Z2R beta)); ring_simplify.
apply Rle_trans with (Z2R beta*(12/25-/sqrt(Z2R beta))).
apply Rle_trans with (Z2R beta*(71/1000)).
apply Rle_trans with (Z2R 6*(71/1000)).
simpl; interval.
apply Rmult_le_compat_r.
interval.
apply Z2R_le; omega.
apply Rmult_le_compat_l.
left; apply radix_pos.
interval.
assert (sqrt (Z2R beta) <> 0).
apply Rgt_not_eq.
apply sqrt_lt_R0, radix_pos.
apply Rplus_le_reg_l with (-12/25*Z2R beta).
unfold Rdiv; ring_simplify.
right; rewrite Ropp_mult_distr_l_reverse; apply f_equal.
apply Rmult_eq_reg_l with (sqrt (Z2R beta)); trivial.
apply trans_eq with (Z2R beta).
field; trivial.
apply sym_eq, sqrt_sqrt.
left; apply radix_pos.
unfold Rdiv; rewrite (Rmult_assoc _ (2 - bpow (1 - prec))).
apply Rmult_le_compat_l.
left; apply radix_pos.
assert (0 <= bpow (1-prec) <= 1/32).
split.
apply bpow_ge_0.
apply Rle_trans with (bpow (-(2))).
apply bpow_le.
omega.
rewrite bpow_opp.
simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r.
apply Rle_trans with (/Z2R (6*6)).
apply Rinv_le.
simpl; interval.
apply Z2R_le.
apply Zmult_le_compat; omega.
simpl; interval.
interval.
Qed.



Theorem round_flx_sqr_sqrt_aux: (4 < radix_val beta)%Z ->
 ((radix_val beta=5)%Z -> (3 < prec)%Z) ->
 (sqrt (Z2R (radix_val beta)) * bpow (ln_beta beta x-1) < x) ->
  round_flx3(x/z) <= 1.
Proof with auto with typeclass_instances.
intros Hbeta Hprec5 H1.
apply Rle_trans with (round_flx3 (x/(x-Z2R k*ulp_flx x))).
apply round_le...
unfold Rdiv; apply Rmult_le_compat_l.
now left.
apply Rinv_le.
apply xkpos; try assumption.
apply kLe.
right; omega.
(* *)
apply round_flx_sqr_sqrt_aux1...
apply kpos.
apply kLe.
right; omega.
apply Rplus_lt_reg_l with ((Z2R k + / 2) * (Z2R k + / 2) * bpow (ln_beta beta x - prec)).
apply Rlt_le_trans with ((2 * Z2R k + 1) * x).
2: right; ring.
apply Rle_lt_trans with
 (/4*bpow (2+(ln_beta beta x - prec)) + / 2 * bpow (ln_beta beta x)).
apply Rplus_le_compat_r.
rewrite bpow_plus, <- Rmult_assoc.
apply Rmult_le_compat_r.
apply bpow_ge_0.
assert (0 <= Z2R k + / 2).
replace 0 with (Z2R 0+0) by (simpl;ring); apply Rplus_le_compat.
apply Z2R_le, kpos.
apply Rlt_le, Rinv_0_lt_compat, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
assert (Z2R k + / 2 <= Z2R beta / 2).
apply Rle_trans with ((Z2R (Zceil (Z2R beta / 2) - 1)) + /2).
apply Rplus_le_compat_r.
apply Z2R_le, kLe2.
rewrite Z2R_minus; simpl.
generalize (beta); intros n.
case (Zeven_odd_dec n); intros V.
apply Zeven_ex_iff in V; destruct V as (m, Hm).
rewrite Hm, Z2R_mult.
replace (Z2R 2*Z2R m/2) with (Z2R m).
rewrite Zceil_Z2R.
apply Rplus_le_reg_l with (-Z2R m + /2).
field_simplify.
unfold Rdiv; apply Rmult_le_compat_r.
apply Rlt_le, Rinv_0_lt_compat.
apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rlt_le, Rlt_0_1.
simpl; field.
apply Zodd_ex_iff in V; destruct V as (m, Hm).
rewrite Hm, Z2R_plus, Z2R_mult.
replace ((Z2R 2*Z2R m+Z2R 1)/2) with (Z2R m+/2).
replace (Zceil (Z2R m + / 2)) with (m+1)%Z.
rewrite Z2R_plus; simpl; right; field.
apply sym_eq, Zceil_imp.
split.
ring_simplify (m+1-1)%Z.
apply Rplus_lt_reg_r with (-Z2R m).
ring_simplify.
apply Rinv_0_lt_compat.
apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
rewrite Z2R_plus; apply Rplus_le_compat_l.
apply Rplus_le_reg_l with (-/2).
simpl; field_simplify.
unfold Rdiv; apply Rmult_le_compat_r.
apply Rlt_le, Rinv_0_lt_compat.
apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rlt_le, Rlt_0_1.
simpl; field.
apply Rle_trans with ((Z2R beta / 2)*(Z2R beta / 2)).
now apply Rmult_le_compat.
simpl; unfold Z.pow_pos; simpl.
rewrite Zmult_1_r, Z2R_mult.
right; field.
generalize kpos; unfold k; intros Y.
destruct (ln_beta beta x) as (e,He).
simpl (ln_beta_val beta x (Build_ln_beta_prop beta x e He)) in *.
apply Rle_lt_trans with (bpow (e-1)*(/4*bpow (3-prec) + (Z2R beta) / 2)).
rewrite (Rmult_plus_distr_l (bpow (e-1))).
apply Rplus_le_compat.
rewrite (Rmult_comm (bpow (e-1))).
rewrite Rmult_assoc; apply Rmult_le_compat_l.
apply Rlt_le, Rinv_0_lt_compat.
apply Rmult_lt_0_compat; apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
rewrite <- bpow_plus.
right; apply f_equal; ring.
unfold Zminus; rewrite bpow_plus, bpow_opp, bpow_1.
right; field.
apply Rgt_not_eq, radix_pos.
apply Rle_lt_trans with
   ((2 * (x * bpow (1 - e) / (2+bpow (1-prec)) - 1) + 1) *
    (sqrt (Z2R beta) * bpow (e - 1))).
apply Rle_trans with (bpow (e - 1)*((2 * (x * bpow (1 - e) / (2+bpow (1-prec)) - 1) + 1) *
   sqrt (Z2R beta))).
2: right; ring.
apply Rmult_le_compat_l.
apply bpow_ge_0.
apply Rplus_le_reg_l with (-(Z2R beta/2)+sqrt (Z2R beta)).
ring_simplify.
apply Rle_trans with  (Z2R beta *(2-bpow(1-prec))/ (2*(2+bpow (1-prec)))).
apply round_flx_sqr_sqrt_snd_deg.
case (Zle_lt_or_eq 5 (radix_val beta)).
omega.
intros G; now right.
intros G; left; split.
now rewrite G.
apply Hprec5; now rewrite G.
apply Rle_trans with (- (Z2R beta / 2) + Z2R (beta)*2/(2+bpow (1-prec))).
right; field.
apply Rgt_not_eq.
rewrite Rplus_comm, <- Rplus_assoc.
apply Rle_lt_0_plus_1, Rlt_le, Rle_lt_0_plus_1, bpow_ge_0.
apply Rplus_le_compat_l.
apply Rle_trans with (2*sqrt (Z2R beta) * ((sqrt (Z2R beta) * bpow (e - 1))*bpow (1 - e) /(2+bpow (1-prec)))).
apply Rle_trans with ((sqrt (Z2R beta) * sqrt (Z2R beta))
   * ((bpow (e - 1) * bpow (1 - e))) *(2/(2+bpow (1-prec)))).
2: right; field.
rewrite <- bpow_plus.
rewrite sqrt_sqrt.
ring_simplify (e-1+(1-e))%Z.
simpl; unfold Rdiv; right; simpl; ring.
left; apply radix_pos.
apply Rgt_not_eq; rewrite Rplus_comm, <- Rplus_assoc.
apply Rle_lt_0_plus_1, Rlt_le, Rle_lt_0_plus_1, bpow_ge_0.
apply Rmult_le_compat_l.
apply Rmult_le_pos.
apply Rlt_le, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply sqrt_pos.
apply Rmult_le_compat_r.
apply Rlt_le, Rinv_0_lt_compat.
rewrite Rplus_comm, <- Rplus_assoc.
apply Rle_lt_0_plus_1, Rlt_le, Rle_lt_0_plus_1, bpow_ge_0.
apply Rmult_le_compat_r.
apply bpow_ge_0.
now left.
apply Rle_lt_trans with
  ((2 * Z2R (Zceil (x * bpow (1 - e) / (2+bpow (1-prec))) - 1) + 1)*
    (sqrt (Z2R beta) * bpow (e - 1))).
apply Rmult_le_compat_r.
apply Rmult_le_pos.
apply sqrt_pos.
apply bpow_ge_0.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l.
apply Rlt_le, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
rewrite Z2R_minus; simpl (Z2R 1).
apply Rplus_le_compat_r.
apply Zceil_ub.
apply Rmult_lt_compat_l.
apply Rle_lt_0_plus_1.
apply Rmult_le_pos.
apply Rlt_le, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
replace 0 with (Z2R 0) by reflexivity.
apply Z2R_le, Y.
assumption.
(* *)
apply round_flx_sqr_sqrt_aux2...
apply kpos.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
unfold k, canonic_exp, FLX_exp.
destruct (ln_beta beta x) as (e,He).
simpl (ln_beta_val beta x (Build_ln_beta_prop beta x e He)) in *.
apply Rle_lt_trans with (2 * Z2R (Zceil (x * bpow (1 - e) / (2+bpow (1-prec))) - 1) *
(bpow (prec - 1) * bpow (e - prec)) * (1 + bpow (1 - prec) / 2)).
right; ring.
rewrite <- bpow_plus.
apply Rlt_le_trans with (2 * (x * bpow (1 - e) / (2+bpow (1-prec))) *
bpow (prec - 1 + (e - prec)) * (1 + bpow (1 - prec) / 2)).
apply Rmult_lt_compat_r.
rewrite Rplus_comm; apply Rle_lt_0_plus_1.
unfold Rdiv; apply Rmult_le_pos.
apply bpow_ge_0.
apply Rlt_le, Rinv_0_lt_compat, Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
apply Rmult_lt_compat_l.
apply Rle_lt_0_plus_1, Rlt_le, Rlt_0_1.
generalize ((x * bpow (1 - e) / (2+bpow (1-prec)))).
intros r; case (Req_dec (Z2R (Zfloor r)) r).
intros V; rewrite <- V; rewrite  Zceil_Z2R.
apply Z2R_lt; omega.
intros V; rewrite (Zceil_floor_neq _ V).
ring_simplify (Zfloor r+1-1)%Z.
case (Zfloor_lb r); try trivial.
intros W; now contradict W.
apply Rle_trans with (x*(bpow (1 - e)*bpow (prec - 1 + (e - prec)))*
   (2*(1 + bpow (1 - prec) / 2)/(2+bpow (1-prec)))).
right; unfold Rdiv; ring.
rewrite <- bpow_plus.
ring_simplify (1 - e + (prec - 1 + (e - prec)))%Z.
simpl (bpow 0); rewrite Rmult_1_r.
right; field.
apply Rgt_not_eq.
rewrite Rplus_comm, <- Rplus_assoc; apply Rle_lt_0_plus_1.
apply Rlt_le, Rle_lt_0_plus_1, bpow_ge_0.
Qed.

End Sec3.

Section Sec4.

Open Scope R_scope.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Variable choice1 : Z -> bool.
Variable choice2 : Z -> bool.
Variable choice3 : Z -> bool.
Variable choice4 : Z -> bool.
Variable choice5 : Z -> bool.

Notation format := (generic_format beta (FLX_exp prec)).
Notation round_flx1 :=(round beta (FLX_exp prec) (Znearest choice1)).
Notation round_flx2 :=(round beta (FLX_exp prec) (Znearest choice2)).
Notation round_flx3 :=(round beta (FLX_exp prec) (Znearest choice3)).
Notation round_flx4 :=(round beta (FLX_exp prec) (Znearest choice4)).
Notation round_flx5 :=(round beta (FLX_exp prec) (Znearest choice5)).

Hypothesis pGt1: (2 < prec)%Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.

Theorem round_flx_sqr_sqrt_exact_pos:
  forall x, 0 < x -> format x -> (radix_val beta <= 4)%Z ->
  round_flx2(sqrt (round_flx1(x*x))) = x.
Proof with auto with typeclass_instances.
intros x Hx Fx Hradix.
case (Rle_or_lt x (sqrt (Z2R beta) * bpow (ln_beta beta x - 1))).
intros H1; destruct H1.
apply round_flx_sqr_sqrt_exact_case1...
omega.
apply round_flx_sqr_sqrt_middle...
omega.
intros H1.
apply round_flx_sqr_sqrt_exact_aux...
omega.
Qed.

Theorem round_flx_sqr_sqrt_exact:
  forall x, format x -> (beta <= 4)%Z ->
  round_flx2(sqrt (round_flx1(x*x))) = Rabs x.
Proof with auto with typeclass_instances.
intros x Fx Hradix.
case (Rle_or_lt 0 x) as [H1|H1].
destruct H1.
rewrite Rabs_right;[idtac|apply Rle_ge; now left].
now apply round_flx_sqr_sqrt_exact_pos.
rewrite <- H, Rabs_R0, Rmult_0_l.
rewrite round_0...
rewrite sqrt_0.
apply round_0...
replace (x*x) with ((-x)*(-x)) by ring.
rewrite Rabs_left1; auto with real.
apply round_flx_sqr_sqrt_exact_pos; trivial.
auto with real.
now apply generic_format_opp.
Qed.

Hypothesis pradix5: (radix_val beta=5)%Z -> (3 < prec)%Z.

Theorem round_flx_sqr_sqrt_pos:
  forall x, format x -> 0 < x -> (4 < radix_val beta)%Z ->
  ((radix_val beta=5)%Z -> (3 < prec)%Z) ->
  round_flx3(x/round_flx2(sqrt (round_flx1(x*x)))) <= 1.
Proof with auto with typeclass_instances.
intros x Fx Hx Hr1 Hr2.
case (Rle_or_lt x (sqrt (Z2R beta) * bpow (ln_beta beta x - 1))); intros H1.
replace (round_flx2 (sqrt (round_flx1 (x * x)))) with x.
replace (x/x) with 1;[idtac|field; auto with real].
right; apply round_generic...
replace 1 with (bpow 0) by reflexivity.
apply generic_format_bpow.
unfold FLX_exp; auto with zarith.
destruct H1.
rewrite round_flx_sqr_sqrt_exact_case1...
omega.
rewrite round_flx_sqr_sqrt_middle...
omega.
apply round_flx_sqr_sqrt_aux...
omega.
Qed.

Theorem sqrt_sqr_pos: forall x y:R, format x -> 0 <= x ->
    0 <= round_flx3 (x / round_flx2(sqrt (round_flx4(round_flx1(x*x)+round_flx5(y*y))))) <= 1.
Proof with auto with typeclass_instances.
intros x y Fx Hx.
case Hx; intros Hx'.
assert (round_flx2 (sqrt (round_flx1 (x * x))) <=
        round_flx2 (sqrt (round_flx4 (round_flx1 (x * x) + round_flx5 (y * y))))).
apply round_le...
apply sqrt_le_1_alt.
apply round_ge_generic...
apply generic_format_round...
apply Rplus_le_reg_l with (-(round_flx1 (x*x))); ring_simplify.
rewrite <- round_0 with beta (FLX_exp prec) (Znearest choice5)...
apply round_le...
apply Rle_trans with (Rsqr y);[auto with real|right ; unfold Rsqr; ring].
assert (0 < round_flx2 (sqrt (round_flx1 (x * x)))).
destruct (ln_beta beta x) as (e,He).
apply Rlt_le_trans with (bpow (e-1)).
apply bpow_gt_0.
apply round_ge_generic...
apply generic_format_bpow.
unfold FLX_exp; auto with zarith.
rewrite <- (sqrt_sqrt (bpow (e-1))).
2: apply bpow_ge_0.
rewrite <- sqrt_mult; try apply bpow_ge_0.
apply sqrt_le_1_alt.
rewrite <- bpow_plus.
apply round_ge_generic...
apply generic_format_bpow.
unfold FLX_exp; auto with zarith.
rewrite bpow_plus.
rewrite Rabs_right in He by now apply Rle_ge.
apply Rmult_le_compat; try apply bpow_ge_0; apply He; auto with real.
split.
(* *)
replace 0 with (round_flx3 0).
apply round_le...
unfold Rdiv; apply Rmult_le_pos; try assumption.
left; apply Rinv_0_lt_compat.
apply Rlt_le_trans with (1:=H0); exact H.
apply round_0...
(* *)
apply Rle_trans with
  (round_flx3 (x / round_flx2 (sqrt (round_flx1 (x * x))))).
apply round_le...
unfold Rdiv; apply Rmult_le_compat_l; try exact Hx.
apply Rinv_le; assumption.
case (Zle_or_lt (radix_val beta) 4); intros Hradix.
rewrite round_flx_sqr_sqrt_exact; try assumption.
rewrite Rabs_right.
2: now apply Rle_ge.
replace (x/x) with 1;[idtac|field; auto with real].
right; apply round_generic...
replace 1 with (bpow 0) by reflexivity.
apply generic_format_bpow.
unfold FLX_exp; auto with zarith.
now apply round_flx_sqr_sqrt_pos.
unfold Rdiv; rewrite <- Hx', Rmult_0_l.
rewrite round_0...
auto with real.
Qed.

End Sec4.

Section Sec5.

Open Scope R_scope.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable prec : Z.
Variable choice1 : Z -> bool.
Variable choice2 : Z -> bool.
Variable choice3 : Z -> bool.
Variable choice4 : Z -> bool.
Variable choice5 : Z -> bool.

Notation format := (generic_format beta (FLX_exp prec)).
Notation round_flx1 :=(round beta (FLX_exp prec) (Znearest choice1)).
Notation round_flx2 :=(round beta (FLX_exp prec) (Znearest choice2)).
Notation round_flx3 :=(round beta (FLX_exp prec) (Znearest choice3)).
Notation round_flx4 :=(round beta (FLX_exp prec) (Znearest choice4)).
Notation round_flx5 :=(round beta (FLX_exp prec) (Znearest choice5)).

Hypothesis pGt1: (2 < prec)%Z.

Hypothesis pradix5: (radix_val beta=5)%Z -> (3 < prec)%Z.

Theorem sqrt_sqr: forall x y:R, format x ->
   -1 <=  round_flx1 (x / round_flx2(sqrt (round_flx3(round_flx4(x*x)+round_flx5(y*y))))) <= 1.
Proof with auto with typeclass_instances.
intros x y Fx.
case (Rle_or_lt 0 x); intros Hx.
split.
apply Rle_trans with 0.
auto with real.
apply sqrt_sqr_pos...
unfold Prec_gt_0; omega.
apply sqrt_sqr_pos...
unfold Prec_gt_0; omega.
replace
 (x / round_flx2 (sqrt (round_flx3 (round_flx4 (x * x) + round_flx5 (y * y))))) with
 (-(((-x) / round_flx2 (sqrt (round_flx3 (round_flx4 ((-x) * (-x)) + round_flx5 (y * y))))))).
rewrite round_N_opp.
split.
apply Ropp_le_contravar.
apply sqrt_sqr_pos...
unfold Prec_gt_0; omega.
now apply generic_format_opp.
auto with real.
apply Rle_trans with (-0).
apply Ropp_le_contravar.
apply sqrt_sqr_pos...
unfold Prec_gt_0; omega.
now apply generic_format_opp.
auto with real.
rewrite Ropp_0; auto with real.
unfold Rdiv; rewrite Ropp_mult_distr_l_reverse, Ropp_involutive.
repeat apply f_equal; apply f_equal2; apply f_equal; ring.
Qed.

End Sec5.
