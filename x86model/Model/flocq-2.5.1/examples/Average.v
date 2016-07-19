Require Import Fcore.
Require Import Fprop_plus_error.
Require Import Fourier.

Open Scope R_scope.

Section av1.


Lemma Rmin_Rmax_overflow: forall x y z M, Rabs x <= M -> Rabs y <= M ->
        Rmin x y <= z <= Rmax x y -> Rabs z <= M.
Proof.
intros x y z M Hx Hy H.
case (Rle_or_lt 0 z); intros Hz.
rewrite Rabs_right.
apply Rle_trans with (1:=proj2 H).
generalize (proj2 H).
apply Rmax_case_strong.
intros; apply Rle_trans with (2:=Hx).
apply RRle_abs.
intros; apply Rle_trans with (2:=Hy).
apply RRle_abs.
now apply Rle_ge.
rewrite Rabs_left; try assumption.
apply Rle_trans with (Rmax (-x) (-y)).
rewrite Rmax_opp.
apply Ropp_le_contravar, H.
apply Rmax_case_strong.
intros; apply Rle_trans with (2:=Hx).
rewrite <- Rabs_Ropp.
apply RRle_abs.
intros; apply Rle_trans with (2:=Hy).
rewrite <- Rabs_Ropp.
apply RRle_abs.
Qed.


Definition radix2 := Build_radix 2 (refl_equal true).
Notation bpow e := (bpow radix2 e).

Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE). 
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).
Notation cexp := (canonic_exp radix2 (FLT_exp emin prec)).
Notation pred_flt := (pred radix2 (FLT_exp emin prec)).

Lemma FLT_format_double: forall u, format u -> format (2*u).
Proof with auto with typeclass_instances.
intros u Fu.
apply generic_format_FLT.
apply FLT_format_generic in Fu...
destruct Fu as (uf, (H1,(H2,H3))).
exists (Float radix2 (Fnum uf) (Fexp uf+1)).
split.
rewrite H1; unfold F2R; simpl.
rewrite bpow_plus, bpow_1.
simpl;ring.
split.
now simpl.
simpl; apply Zle_trans with (1:=H3).
omega.
Qed.


Lemma FLT_format_half: forall u, 
   format u -> bpow (prec+emin) <= Rabs u -> format (u/2).
Proof with auto with typeclass_instances.
intros u Fu H.
apply FLT_format_generic in Fu...
destruct Fu as ((n,e),(H1,(H2,H3))).
simpl in H1, H2, H3.
apply generic_format_FLT.
exists (Float radix2 n (e-1)).
split; simpl.
rewrite H1; unfold F2R; simpl.
unfold Zminus; rewrite bpow_plus.
simpl; unfold Rdiv; ring.
split;[assumption|idtac].
assert (prec + emin < prec +e)%Z;[idtac|omega].
apply lt_bpow with radix2.
apply Rle_lt_trans with (1:=H).
rewrite H1; unfold F2R; simpl.
rewrite Rabs_mult; rewrite (Rabs_right (bpow e)).
2: apply Rle_ge, bpow_ge_0.
rewrite bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
rewrite <- Z2R_abs.
rewrite <- Z2R_Zpower.
now apply Z2R_lt.
unfold Prec_gt_0 in prec_gt_0_; omega.
Qed.


Lemma FLT_round_half: forall z, bpow (prec+emin) <= Rabs z -> 
   round_flt (z/2)= round_flt z /2.
Proof with auto with typeclass_instances.
intros z Hz.
apply Rmult_eq_reg_l with 2.
2: apply sym_not_eq; auto with real.
apply trans_eq with (round_flt z).
2: field.
assert (z <> 0)%R.
intros K; contradict Hz.
rewrite K, Rabs_R0; apply Rlt_not_le.
apply bpow_gt_0.
assert (cexp (z/2) = cexp z -1)%Z.
assert (prec+emin < ln_beta radix2 z)%Z.
apply lt_bpow with radix2.
destruct ln_beta as (e,He); simpl.
apply Rle_lt_trans with (1:=Hz).
now apply He.
unfold canonic_exp, FLT_exp.
replace ((ln_beta radix2 (z/2))-prec)%Z with ((ln_beta radix2 z -1) -prec)%Z.
rewrite Z.max_l; try omega.
rewrite Z.max_l; try omega.
apply Zplus_eq_compat; try reflexivity.
apply sym_eq, ln_beta_unique.
destruct (ln_beta radix2 z) as (e,He); simpl.
unfold Rdiv; rewrite Rabs_mult.
rewrite (Rabs_right (/2)).
split.
apply Rmult_le_reg_l with (bpow 1).
apply bpow_gt_0.
rewrite <- bpow_plus.
replace (1+(e-1-1))%Z with (e-1)%Z by ring.
apply Rle_trans with (Rabs z).
now apply He.
right; simpl; field.
apply Rmult_lt_reg_l with (bpow 1).
apply bpow_gt_0.
rewrite <- bpow_plus.
replace (1+(e-1))%Z with e by ring.
apply Rle_lt_trans with (Rabs z).
right; simpl; field.
now apply He.
apply Rle_ge; auto with real.
unfold round, scaled_mantissa, F2R.
rewrite H0; simpl.
rewrite Rmult_comm, Rmult_assoc.
apply f_equal2.
apply f_equal, f_equal.
replace (-(cexp z -1))%Z with (-cexp z +1)%Z by ring.
rewrite bpow_plus.
simpl; field.
unfold Zminus; rewrite bpow_plus.
simpl; field.
Qed. 



Lemma FLT_ulp_le_id: forall u, bpow emin <= u -> ulp_flt u <= u.
Proof with auto with typeclass_instances.
intros u H.
rewrite ulp_neq_0.
2: apply Rgt_not_eq, Rlt_le_trans with (2:=H), bpow_gt_0.
case (Rle_or_lt (bpow (emin+prec-1)) u); intros Hu.
unfold ulp; rewrite canonic_exp_FLT_FLX.
unfold canonic_exp, FLX_exp.
destruct (ln_beta radix2 u) as (e,He); simpl.
apply Rle_trans with (bpow (e-1)).
apply bpow_le.
unfold Prec_gt_0 in prec_gt_0_; omega.
rewrite <- (Rabs_right u).
apply He.
apply Rgt_not_eq, Rlt_gt.
apply Rlt_le_trans with (2:=Hu).
apply bpow_gt_0.
apply Rle_ge, Rle_trans with (2:=Hu), bpow_ge_0.
rewrite Rabs_right.
assumption.
apply Rle_ge, Rle_trans with (2:=Hu), bpow_ge_0.
unfold ulp; rewrite canonic_exp_FLT_FIX.
apply H.
apply Rgt_not_eq, Rlt_gt.
apply Rlt_le_trans with (2:=H).
apply bpow_gt_0.
rewrite Rabs_right.
apply Rlt_le_trans with (1:=Hu).
apply bpow_le; omega.
apply Rle_ge, Rle_trans with (2:=H), bpow_ge_0.
Qed.



Lemma FLT_ulp_double: forall u, ulp_flt (2*u) <= 2*ulp_flt(u).
intros u.
case (Req_bool_spec u 0); intros Hu'.
rewrite Hu', Rmult_0_r.
rewrite <- (Rmult_1_l (ulp_flt 0)) at 1.
apply Rmult_le_compat_r.
apply ulp_ge_0.
left; apply Rlt_plus_1.
rewrite 2!ulp_neq_0; trivial.
2: apply Rmult_integral_contrapositive_currified; trivial.
2: apply Rgt_not_eq; apply Rlt_trans with (1:=Rlt_plus_1 _).
2: rewrite Rplus_0_l; apply Rlt_plus_1.
pattern 2 at 2; replace 2 with (bpow 1) by reflexivity.
rewrite <- bpow_plus.
apply bpow_le.
case (Rle_or_lt (bpow (emin+prec-1)) (Rabs u)); intros Hu.
(* *)
rewrite canonic_exp_FLT_FLX.
rewrite canonic_exp_FLT_FLX; trivial.
unfold canonic_exp, FLX_exp.
replace 2 with (bpow 1) by reflexivity.
rewrite Rmult_comm, ln_beta_mult_bpow.
omega.
intros H; contradict Hu.
apply Rlt_not_le; rewrite H, Rabs_R0.
apply bpow_gt_0.
apply Rle_trans with (1:=Hu).
rewrite Rabs_mult.
pattern (Rabs u) at 1; rewrite <- (Rmult_1_l (Rabs u)).
apply Rmult_le_compat_r.
apply Rabs_pos.
rewrite Rabs_right.
now auto with real.
apply Rle_ge; now auto with real.
(* *)
case (Req_dec u 0); intros K.
rewrite K, Rmult_0_r.
omega.
rewrite canonic_exp_FLT_FIX.
rewrite canonic_exp_FLT_FIX; trivial.
unfold FIX_exp, canonic_exp; omega.
apply Rlt_le_trans with (1:=Hu).
apply bpow_le; omega.
apply Rmult_integral_contrapositive_currified; trivial.
apply Rgt_not_eq, Rlt_gt; now auto with real.
rewrite Rabs_mult.
rewrite Rabs_right.
2: apply Rle_ge; now auto with real.
apply Rlt_le_trans with (2*bpow (emin + prec - 1)).
apply Rmult_lt_compat_l.
now auto with real.
assumption.
replace 2 with (bpow 1) by reflexivity.
rewrite <- bpow_plus.
apply bpow_le; omega.
Qed.


Lemma round_plus_small_id_aux: forall f h, format f -> (bpow (prec+emin) <= f) -> 0 < f 
   -> Rabs h <= /4* ulp_flt f -> round_flt (f+h) = f.
Proof with auto with typeclass_instances.
intros f h Ff H1 H2 Hh.
case (Rle_or_lt 0 h); intros H3;[destruct H3|idtac].
(* 0 < h *)
rewrite Rabs_right in Hh.
2: now apply Rle_ge, Rlt_le.
apply round_N_eq_DN_pt with (f+ ulp_flt f)...
pattern f at 2; rewrite <- (round_DN_plus_eps_pos radix2 (FLT_exp emin prec) f) with (eps:=h); try assumption.
apply round_DN_pt...
now left.
split.
now left.
apply Rle_lt_trans with (1:=Hh).
rewrite <- (Rmult_1_l (ulp_flt f)) at 2.
apply Rmult_lt_compat_r.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
apply bpow_gt_0.
fourier.
rewrite <- (round_UP_plus_eps_pos radix2 (FLT_exp emin prec) f) with (eps:=h); try assumption.
apply round_UP_pt...
now left.
split; trivial.
apply Rle_trans with (1:=Hh).
rewrite <- (Rmult_1_l (ulp_flt f)) at 2.
apply Rmult_le_compat_r.
apply ulp_ge_0.
fourier.
apply Rplus_lt_reg_l with (-f); ring_simplify.
apply Rlt_le_trans with (/2*ulp_flt f).
2: right; field.
apply Rle_lt_trans with (1:=Hh).
apply Rmult_lt_compat_r.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
apply bpow_gt_0.
fourier.
(* h = 0 *)
rewrite <- H, Rplus_0_r.
apply round_generic...
(* h < 0 *)
(*  - assertions *)
rewrite Rabs_left in Hh; try assumption.
assert (0 < pred_flt f).
apply Rlt_le_trans with (bpow emin).
apply bpow_gt_0.
apply le_pred_lt...
apply FLT_format_bpow...
omega.
apply Rlt_le_trans with (2:=H1).
apply bpow_lt.
unfold Prec_gt_0 in prec_gt_0_; omega.
assert (M:(prec + emin +1 <= ln_beta radix2 f)%Z).
apply ln_beta_ge_bpow.
replace (prec+emin+1-1)%Z with (prec+emin)%Z by ring.
rewrite Rabs_right; try assumption.
apply Rle_ge; now left.
assert (T1:(ulp_flt (pred_flt f) = ulp_flt f) 
     \/ ( ulp_flt (pred_flt f) = /2* ulp_flt f 
               /\ f = bpow (ln_beta radix2 f -1))).
generalize H; rewrite pred_eq_pos; [idtac|now left].
unfold pred_pos; case Req_bool_spec; intros K HH.
(**)
right; split; try assumption.
rewrite ulp_neq_0;[idtac|now apply Rgt_not_eq].
apply trans_eq with (bpow (ln_beta radix2 f- prec -1)).
apply f_equal.
unfold canonic_exp.
apply trans_eq with (FLT_exp emin prec (ln_beta radix2 f -1)%Z).
apply f_equal.
unfold FLT_exp.
rewrite Z.max_l.
2: omega.
apply ln_beta_unique.
rewrite Rabs_right.
split.
apply Rplus_le_reg_l with (bpow (ln_beta radix2 f -1-prec)).
ring_simplify.
apply Rle_trans with (bpow (ln_beta radix2 f - 1 - 1) + bpow (ln_beta radix2 f - 1 - 1)).
apply Rplus_le_compat_r.
apply bpow_le.
unfold Prec_gt_0 in prec_gt_0_; omega.
apply Rle_trans with (bpow 1*bpow (ln_beta radix2 f - 1 - 1)).
simpl; right; ring.
rewrite <- bpow_plus.
apply Rle_trans with (bpow (ln_beta radix2 f -1)).
apply bpow_le; omega.
rewrite <- K; now right.
rewrite <- K.
apply Rplus_lt_reg_l with (-f+bpow (ln_beta radix2 f-1-prec)); ring_simplify.
apply bpow_gt_0.
apply Rle_ge.
rewrite K at 1.
apply Rplus_le_reg_l with (bpow (ln_beta radix2 f - 1 - prec)).
ring_simplify.
apply bpow_le.
unfold Prec_gt_0 in prec_gt_0_; omega.
unfold FLT_exp.
rewrite Z.max_l;[ring|omega].
replace (/2) with (bpow (-1)) by reflexivity.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
rewrite <- bpow_plus.
apply f_equal.
unfold canonic_exp, FLT_exp.
rewrite Z.max_l;[ring|omega].
(**)
left.
assert (bpow (ln_beta radix2 f -1) < f).
destruct (ln_beta radix2 f); simpl in *.
destruct a.
now apply Rgt_not_eq.
rewrite Rabs_right in H0.
destruct H0; try assumption.
contradict H0.
now apply sym_not_eq.
apply Rle_ge; now left.
assert (bpow (ln_beta radix2 f -1) + ulp_flt (bpow (ln_beta radix2 f-1)) <= f).
rewrite <- succ_eq_pos;[idtac|apply bpow_ge_0].
apply succ_le_lt...
apply FLT_format_bpow...
unfold Prec_gt_0 in prec_gt_0_;omega.
rewrite ulp_bpow in H4.
unfold FLT_exp in H4.
rewrite Z.max_l in H4.
2: omega.
replace (ln_beta radix2 f - 1 + 1 - prec)%Z with  (ln_beta radix2 f - prec)%Z in H4 by ring.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
rewrite ulp_neq_0 at 2; try now apply Rgt_not_eq.
unfold canonic_exp.
apply f_equal; apply f_equal.
replace (ulp_flt f) with (bpow (ln_beta radix2 f -prec)).
apply ln_beta_unique.
rewrite Rabs_right.
split.
apply Rplus_le_reg_l with (bpow (ln_beta radix2 f -prec)).
ring_simplify.
apply Rle_trans with (2:=H4); right; ring.
apply Rlt_trans with f.
apply Rplus_lt_reg_l with (-f+bpow (ln_beta radix2 f - prec)).
ring_simplify.
apply bpow_gt_0.
apply Rle_lt_trans with (1:=RRle_abs _).
apply bpow_ln_beta_gt.
apply Rle_ge.
apply Rplus_le_reg_l with (bpow (ln_beta radix2 f - prec)).
ring_simplify.
left; apply Rle_lt_trans with (2:=H0).
apply bpow_le.
unfold Prec_gt_0 in prec_gt_0_;omega.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
unfold canonic_exp, FLT_exp.
rewrite Z.max_l.
reflexivity.
omega.
assert (T: (ulp_flt (pred_flt f) = ulp_flt f \/ 
              (ulp_flt (pred_flt f) = / 2 * ulp_flt f /\ - h < / 4 * ulp_flt f))
         \/ (ulp_flt (pred_flt f) = / 2 * ulp_flt f /\
              f = bpow (ln_beta radix2 f - 1) /\
              - h = / 4 * ulp_flt f) ).
destruct T1.
left; now left.
case Hh; intros P.
left; right.
split; try apply H0; assumption.
right.
split; try split; try apply H0; assumption.
clear T1.
(*  - end of assertions *)
destruct T.
(* normal case *)
apply round_N_eq_UP_pt with (pred_flt f)...
rewrite <- (round_DN_minus_eps_pos radix2 (FLT_exp emin prec) f) with (eps:=-h); try assumption.
replace (f--h) with (f+h) by ring.
apply round_DN_pt...
split.
auto with real.
apply Rle_trans with (1:=Hh).
apply Rle_trans with (/2*ulp_flt f).
apply Rmult_le_compat_r.
apply ulp_ge_0.
fourier.
case H0.
intros Y; rewrite Y.
rewrite <- (Rmult_1_l (ulp_flt f)) at 2.
apply Rmult_le_compat_r.
apply ulp_ge_0.
fourier.
intros Y; rewrite (proj1 Y); now right.
replace (f+h) with (pred_flt f + (f-pred_flt f+h)) by ring.
pattern f at 4; rewrite <- (round_UP_pred_plus_eps_pos radix2 (FLT_exp emin prec) f) with (eps:=(f - pred_flt f + h)); try assumption.
apply round_UP_pt...
replace (f-pred_flt f) with (ulp_flt (pred_flt f)).
split.
apply Rplus_lt_reg_l with (-h); ring_simplify.
case H0; [intros Y|intros (Y1,Y2)].
apply Rle_lt_trans with (1:=Hh).
rewrite Y.
rewrite <- (Rmult_1_l (ulp_flt f)) at 2.
apply Rmult_lt_compat_r.
rewrite ulp_neq_0;[apply bpow_gt_0|now apply Rgt_not_eq].
fourier.
apply Rlt_le_trans with (1:=Y2).
rewrite Y1.
apply Rmult_le_compat_r.
apply ulp_ge_0.
fourier.
apply Rplus_le_reg_l with (-ulp_flt (pred_flt f)); ring_simplify.
now left.
rewrite pred_eq_pos; try now left.
pattern f at 2; rewrite <- (pred_pos_plus_ulp radix2 (FLT_exp emin prec) f)...
ring.
apply Rplus_lt_reg_l with (-f); ring_simplify.
apply Rle_lt_trans with (-(/2 * ulp_flt (pred_flt f))).
right.
apply trans_eq with ((pred_flt f - f) / 2).
field.
rewrite pred_eq_pos; try now left.
pattern f at 2; rewrite <- (pred_pos_plus_ulp radix2 (FLT_exp emin prec) f)...
field.
replace h with (--h) by ring.
apply Ropp_lt_contravar.
case H0;[intros Y|intros (Y1,Y2)].
apply Rle_lt_trans with (1:=Hh).
rewrite Y.
apply Rmult_lt_compat_r.
rewrite ulp_neq_0; try apply bpow_gt_0; now apply Rgt_not_eq.
fourier.
apply Rlt_le_trans with (1:=Y2).
rewrite Y1.
right; field.
(* complex case: even choosing *)
elim H0; intros  T1 (T2,T3); clear H0.
assert (pred_flt f = bpow (ln_beta radix2 f - 1) - bpow (ln_beta radix2 f - 1 -prec)).
rewrite pred_eq_pos; try now left.
unfold pred_pos; case Req_bool_spec.
intros _; rewrite <- T2.
apply f_equal, f_equal.
unfold FLT_exp.
rewrite Z.max_l.
ring.
omega.
intros Y; now contradict T2.
assert (round radix2 (FLT_exp emin prec) Zfloor (f+h) = pred_flt f).
replace (f+h) with (f-(-h)) by ring.
apply round_DN_minus_eps_pos...
split.
auto with real.
rewrite T3, T1.
apply Rmult_le_compat_r.
apply ulp_ge_0.
fourier.
assert (round radix2 (FLT_exp emin prec) Zceil (f+h) = f).
replace (f+h) with (pred_flt f + /2*ulp_flt (pred_flt f)).
apply round_UP_pred_plus_eps_pos...
split.
apply Rmult_lt_0_compat.
fourier.
rewrite ulp_neq_0; try now apply Rgt_not_eq.
apply bpow_gt_0.
rewrite <- (Rmult_1_l (ulp_flt (pred_flt f))) at 2.
apply Rmult_le_compat_r.
apply ulp_ge_0.
fourier.
rewrite T1, H0, <- T2.
replace h with (--h) by ring; rewrite T3.
replace (bpow (ln_beta radix2 f - 1 - prec)) with (/2*ulp_flt f).
field.
replace (/2) with (bpow (-1)) by reflexivity.
rewrite T2 at 1.
rewrite ulp_bpow, <- bpow_plus.
apply f_equal; unfold FLT_exp.
rewrite Z.max_l.
ring.
omega.
assert ((Zeven (Zfloor (scaled_mantissa radix2 (FLT_exp emin prec) (f + h)))) = false).
replace (Zfloor (scaled_mantissa radix2 (FLT_exp emin prec) (f + h)))
   with (Zpower radix2 prec -1)%Z.
unfold Zminus; rewrite Zeven_plus.
rewrite Zeven_opp.
rewrite Zeven_Zpower.
reflexivity.
unfold Prec_gt_0 in prec_gt_0_; omega.
apply eq_Z2R.
rewrite <- scaled_mantissa_DN...
2: rewrite H4; assumption.
rewrite H4.
unfold scaled_mantissa.
rewrite bpow_opp.
rewrite <- ulp_neq_0; try now apply Rgt_not_eq.
rewrite T1.
rewrite Rinv_mult_distr.
2: apply Rgt_not_eq; fourier.
2: apply Rgt_not_eq; rewrite ulp_neq_0; try apply bpow_gt_0.
2: now apply Rgt_not_eq.
rewrite Rinv_involutive.
2: apply Rgt_not_eq; fourier.
rewrite T2 at 2.
rewrite ulp_bpow.
rewrite <- bpow_opp.
unfold FLT_exp at 2.
rewrite Z.max_l.
2: omega.
replace 2 with (bpow 1) by reflexivity.
rewrite <- bpow_plus.
rewrite H0.
rewrite Rmult_minus_distr_r, <- 2!bpow_plus.
rewrite Z2R_minus.
apply f_equal2.
rewrite Z2R_Zpower.
apply f_equal.
ring.
unfold Prec_gt_0 in prec_gt_0_; omega.
apply trans_eq with (bpow 0).
reflexivity.
apply f_equal.
ring.
rewrite round_N_middle.
rewrite H5.
rewrite H6.
reflexivity.
rewrite H5, H4.
pattern f at 1; rewrite <- (pred_pos_plus_ulp radix2 (FLT_exp emin prec) f); try assumption.
ring_simplify.
rewrite <- pred_eq_pos;[idtac|now left].
rewrite T1.
replace h with (--h) by ring.
rewrite T3.
field.
Qed.

Lemma round_plus_small_id: forall f h, format f -> (bpow (prec+emin) <= Rabs f)  
   -> Rabs h <= /4* ulp_flt f -> round_flt (f+h) = f.
intros f h Ff H1 H2.
case (Rle_or_lt 0 f); intros V.
case V; clear V; intros V.
apply round_plus_small_id_aux; try assumption.
rewrite Rabs_right in H1; try assumption.
apply Rle_ge; now left.
contradict H1.
rewrite <- V, Rabs_R0.
apply Rlt_not_le, bpow_gt_0.
rewrite <- (Ropp_involutive f), <- (Ropp_involutive h).
replace (--f + --h) with (-(-f+-h)) by ring.
rewrite round_NE_opp.
apply f_equal.
apply round_plus_small_id_aux.
now apply generic_format_opp.
rewrite Rabs_left in H1; try assumption.
auto with real.
now rewrite Rabs_Ropp, ulp_opp.
Qed.



Definition average1 (x y : R) :=round_flt(round_flt(x+y)/2).

Variables x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

Let a:=(x+y)/2.
Let av:=average1 x y.

Lemma average1_correct: av = round_flt a.
Proof with auto with typeclass_instances.
case (Rle_or_lt (bpow (prec + emin)) (Rabs (x+y))).
(* normal case: division by 2 is exact *)
intros H.
unfold av,a,average1.
rewrite round_generic...
now apply sym_eq, FLT_round_half.
apply FLT_format_half.
apply generic_format_round...
apply abs_round_ge_generic...
apply FLT_format_bpow...
unfold Prec_gt_0 in prec_gt_0_; omega.
(* subnormal case: addition is exact, but division by 2 is not *)
intros H.
unfold av, average1.
replace (round_flt (x + y)) with (x+y).
reflexivity.
apply sym_eq, round_generic...
apply FLT_format_plus_small...
left; assumption.
Qed.



Lemma average1_symmetry: forall u v, average1 u v = average1 v u.
Proof.
intros u v; unfold average1.
rewrite Rplus_comm; reflexivity.
Qed.

Lemma average1_symmetry_Ropp: forall u v, average1 (-u) (-v) = - average1 u v.
Proof.
intros u v; unfold average1.
replace (-u+-v) with (-(u+v)) by ring.
rewrite round_NE_opp.
replace (- round_flt (u + v) / 2) with (- (round_flt (u + v) / 2)) by (unfold Rdiv; ring).
now rewrite round_NE_opp.
Qed.

Lemma average1_same_sign_1: 0 <= a -> 0 <= av.
Proof with auto with typeclass_instances.
intros H.
rewrite average1_correct.
apply round_ge_generic...
apply generic_format_0.
Qed.

Lemma average1_same_sign_2: a <= 0-> av <= 0.
Proof with auto with typeclass_instances.
intros H.
rewrite average1_correct.
apply round_le_generic...
apply generic_format_0.
Qed.

Lemma average1_between: Rmin x y <= av <= Rmax x y.
Proof with auto with typeclass_instances.
rewrite average1_correct.
split.
apply round_ge_generic...
now apply P_Rmin.
apply Rmult_le_reg_l with 2.
auto with real.
rewrite Rmult_plus_distr_r, Rmult_1_l.
apply Rle_trans with (x+y);[idtac|right;unfold a; field].
apply Rplus_le_compat.
apply Rmin_l.
apply Rmin_r.
(* *)
apply round_le_generic...
now apply Rmax_case.
apply Rmult_le_reg_l with 2.
auto with real.
apply Rle_trans with (x+y);[right;unfold a; field|idtac].
rewrite Rmult_plus_distr_r, Rmult_1_l.
apply Rplus_le_compat.
apply Rmax_l.
apply Rmax_r.
Qed.


Lemma average1_zero: a = 0 -> av = 0.
Proof with auto with typeclass_instances.
intros H1; rewrite average1_correct, H1.
rewrite round_0...
Qed.



Lemma average1_no_underflow: (bpow emin) <= Rabs a -> av <> 0.
Proof with auto with typeclass_instances.
intros H.
(* *)
cut (bpow emin <= Rabs av).
intros H1 H2.
rewrite H2 in H1; rewrite Rabs_R0 in H1.
contradict H1.
apply Rlt_not_le.
apply bpow_gt_0.
(* *)
rewrite average1_correct.
apply abs_round_ge_generic...
apply FLT_format_bpow...
omega.
Qed.


Lemma average1_correct_weak1: Rabs (av -a) <= /2*ulp_flt a.
Proof with auto with typeclass_instances.
rewrite average1_correct.
apply error_le_half_ulp...
Qed.

Lemma average1_correct_weak2: Rabs (av -a) <= 3/2*ulp_flt a.
Proof with auto with typeclass_instances.
apply Rle_trans with (1:=average1_correct_weak1).
apply Rmult_le_compat_r.
unfold ulp; apply ulp_ge_0.
apply Rle_trans with (1/2); unfold Rdiv.
right; ring.
apply Rmult_le_compat_r.
now auto with real.
apply Rplus_le_reg_l with (-1); ring_simplify.
now auto with real.
Qed.



(* Hypothesis diff_sign: (0 <= x /\ y <= 0) \/ (x <= 0 /\ 0 <= y).
  is useless for properties: only useful for preventing overflow *)





Definition average2 (x y : R) :=round_flt(round_flt(x/2) + round_flt(y/2)).

Let av2:=average2 x y.


Lemma average2_correct: bpow (emin +prec+prec+1) <= Rabs x -> av2 = round_flt a.
Proof with auto with typeclass_instances.
intros Hx.
assert (G:(0 < prec)%Z).
unfold Prec_gt_0 in prec_gt_0_; assumption.
unfold av2, average2.
replace (round_flt (x/2)) with (x/2).
2: apply sym_eq, round_generic...
2: apply FLT_format_half; try assumption.
2: apply Rle_trans with (2:=Hx).
2: apply bpow_le; omega.
case (Rle_or_lt (bpow (prec + emin)) (Rabs y)).
(* y is big enough so that y/2 is correct *)
intros Hy.
replace (round_flt (y/2)) with (y/2).
apply f_equal; unfold a; field.
apply sym_eq, round_generic...
apply FLT_format_half; assumption.
(* y is a subnormal, then it is too small to impact the result *)
intros Hy.
assert (format (x/2)).
apply FLT_format_half.
assumption.
apply Rle_trans with (2:=Hx).
apply bpow_le.
omega.
assert (bpow (prec+emin) <= Rabs (x/2)).
apply Rmult_le_reg_l with (bpow 1).
apply bpow_gt_0.
rewrite <- bpow_plus.
apply Rle_trans with (Rabs x).
apply Rle_trans with (2:=Hx).
apply bpow_le.
omega.
rewrite <- (Rabs_right (bpow 1)).
rewrite <- Rabs_mult.
right; apply f_equal.
simpl; field.
apply Rle_ge, bpow_ge_0.
assert (K1: Rabs (y / 2) <= bpow (prec+emin-1)).
unfold Rdiv; rewrite Rabs_mult.
unfold Zminus; rewrite bpow_plus.
simpl; rewrite (Rabs_right (/2)).
apply Rmult_le_compat_r.
fourier.
now left.
fourier.
assert (K2:bpow (prec+emin-1) <= / 4 * ulp_flt (x / 2)).
assert (Z: x/2 <> 0).
intros K; contradict H0.
rewrite K, Rabs_R0.
apply Rlt_not_le, bpow_gt_0.
rewrite ulp_neq_0; trivial.
replace (/4) with (bpow (-2)) by reflexivity.
rewrite <- bpow_plus.
apply bpow_le.
unfold canonic_exp, FLT_exp.
assert (emin+prec+prec+1 -1 < ln_beta radix2 (x/2))%Z.
destruct (ln_beta radix2 (x/2)) as (e,He).
simpl.
apply lt_bpow with radix2.
apply Rle_lt_trans with (Rabs (x/2)).
unfold Rdiv; rewrite Rabs_mult.
unfold Zminus; rewrite bpow_plus.
simpl; rewrite (Rabs_right (/2)).
apply Rmult_le_compat_r.
fourier.
exact Hx.
fourier.
apply He; trivial.
rewrite Z.max_l.
omega.
omega.
(* . *)
apply trans_eq with (x/2).
apply round_plus_small_id; try assumption.
apply Rle_trans with (2:=K2).
apply abs_round_le_generic...
apply FLT_format_bpow...
omega.
unfold a; apply sym_eq.
replace ((x+y)/2) with (x/2+y/2) by field.
apply round_plus_small_id; try assumption.
now apply Rle_trans with (2:=K2).
Qed.



End av1.

Section av3.

Notation bpow e := (bpow radix2 e).

Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE). 
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).
Notation cexp := (canonic_exp radix2 (FLT_exp emin prec)).

Definition average3 (x y : R) :=round_flt(x+round_flt(round_flt(y-x)/2)).

Variables x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

Let a:=(x+y)/2.
Let av:=average3 x y.


Lemma average3_symmetry_Ropp: forall u v, average3 (-u) (-v) = - average3 u v.
intros u v; unfold average3.
replace (-v--u) with (-(v-u)) by ring.
rewrite round_NE_opp.
replace (- round_flt (v-u) / 2) with (- (round_flt (v-u) / 2)) by (unfold Rdiv; ring).
rewrite round_NE_opp.
replace (- u + - round_flt (round_flt (v - u) / 2)) with
   (-(u+round_flt (round_flt (v - u) / 2))) by ring.
apply round_NE_opp.
Qed.


Lemma average3_same_sign_1: 0 <= a -> 0 <= av.
Proof with auto with typeclass_instances.
intros H.
apply round_ge_generic...
apply generic_format_0.
apply Rplus_le_reg_l with (-x).
ring_simplify.
apply round_ge_generic...
now apply generic_format_opp.
apply Rmult_le_reg_l with 2.
auto with real.
apply Rle_trans with (-(2*x)).
right; ring.
apply Rle_trans with (round_flt (y - x)).
2: right; field.
apply round_ge_generic...
apply generic_format_opp.
now apply FLT_format_double...
apply Rplus_le_reg_l with (2*x).
apply Rmult_le_reg_r with (/2).
auto with real.
apply Rle_trans with 0;[right; ring|idtac].
apply Rle_trans with (1:=H).
right; unfold a, Rdiv; ring.
Qed.

Lemma average3_same_sign_2: a <= 0-> av <= 0.
Proof with auto with typeclass_instances.
intros H.
apply round_le_generic...
apply generic_format_0.
apply Rplus_le_reg_l with (-x).
ring_simplify.
apply round_le_generic...
now apply generic_format_opp.
apply Rmult_le_reg_l with 2.
auto with real.
apply Rle_trans with (-(2*x)).
2: right; ring.
apply Rle_trans with (round_flt (y - x)).
right; field.
apply round_le_generic...
apply generic_format_opp.
now apply FLT_format_double...
apply Rplus_le_reg_l with (2*x).
apply Rmult_le_reg_r with (/2).
auto with real.
apply Rle_trans with 0;[idtac|right; ring].
apply Rle_trans with (2:=H).
right; unfold a, Rdiv; ring.
Qed.




Lemma average3_between_aux: forall u v, format u -> format v -> u <= v ->
    u <= average3 u v <= v.
Proof with auto with typeclass_instances.
clear Fx Fy a av x y.
intros x y Fx Fy M.
split.
(* . *)
apply round_ge_generic...
apply Rplus_le_reg_l with (-x).
ring_simplify.
apply round_ge_generic...
apply generic_format_0.
unfold Rdiv; apply Rmult_le_pos.
apply round_ge_generic...
apply generic_format_0.
apply Rplus_le_reg_l with x.
now ring_simplify.
auto with real.
(* . *)
apply round_le_generic...
assert (H:(0 <= round radix2 (FLT_exp emin prec) Zfloor (y-x))).
apply round_ge_generic...
apply generic_format_0.
apply Rplus_le_reg_l with x.
now ring_simplify.
destruct H as [H|H].
(* .. *)
pattern y at 2; replace y with (x + (y-x)) by ring.
apply Rplus_le_compat_l.
case (generic_format_EM radix2 (FLT_exp emin prec) (y-x)); intros K.
apply round_le_generic...
rewrite round_generic...
apply Rmult_le_reg_l with 2.
auto with real.
apply Rplus_le_reg_l with (2*x-y).
apply Rle_trans with x.
right; field.
apply Rle_trans with (1:=M).
right; field.
apply Rle_trans with (round radix2 (FLT_exp emin prec) Zfloor (y - x)).
apply round_le_generic...
apply generic_format_round...
apply Rmult_le_reg_l with 2.
auto with real.
apply Rle_trans with (round_flt (y - x)).
right; field.
case (round_DN_or_UP radix2 (FLT_exp emin prec) ZnearestE (y-x));
   intros H1; rewrite H1.
apply Rplus_le_reg_l with (-round radix2 (FLT_exp emin prec) Zfloor (y - x)).
ring_simplify.
now left.
rewrite round_UP_DN_ulp.
apply Rplus_le_reg_l with (-round radix2 (FLT_exp emin prec) Zfloor (y - x)); ring_simplify.
apply round_DN_pt...
apply generic_format_ulp...
case (Rle_or_lt (bpow (emin + prec - 1))  (y-x)); intros P.
apply FLT_ulp_le_id...
apply Rle_trans with (2:=P).
apply bpow_le; unfold Prec_gt_0 in prec_gt_0_; omega.
contradict K.
apply FLT_format_plus_small...
now apply generic_format_opp.
rewrite Rabs_right.
apply Rle_trans with (bpow (emin+prec-1)).
left; exact P.
apply bpow_le; omega.
apply Rle_ge; apply Rplus_le_reg_l with x; now ring_simplify.
assumption.
apply round_DN_pt...
(* .. *)
case M; intros H1.
2: rewrite H1; replace (y-y) with 0 by ring.
2: rewrite round_0...
2: unfold Rdiv; rewrite Rmult_0_l.
2: rewrite round_0...
2: right; ring.
apply Rle_trans with (x+0).
2: rewrite Rplus_0_r; assumption.
apply Rplus_le_compat_l.
replace 0 with (round_flt (bpow emin/2)).
apply round_le...
unfold Rdiv; apply Rmult_le_compat_r.
auto with real.
apply round_le_generic...
apply FLT_format_bpow...
omega.
case (Rle_or_lt (y-x) (bpow emin)); trivial.
intros H2.
contradict H.
apply Rlt_not_eq.
apply Rlt_le_trans with (bpow emin).
apply bpow_gt_0.
apply round_DN_pt...
apply FLT_format_bpow...
omega.
now left.
replace (bpow emin /2) with (bpow (emin-1)).
unfold round, scaled_mantissa, canonic_exp, FLT_exp.
rewrite ln_beta_bpow.
replace (emin - 1 + 1 - prec)%Z with (emin-prec)%Z by ring.
rewrite Z.max_r.
2: unfold Prec_gt_0 in prec_gt_0_; omega.
rewrite <- bpow_plus.
replace (emin-1+-emin)%Z with (-1)%Z by ring.
replace (ZnearestE (bpow (-1))) with 0%Z.
unfold F2R; simpl; ring.
simpl; unfold Znearest.
replace (Zfloor (/2)) with 0%Z.
rewrite Rcompare_Eq.
reflexivity.
simpl; ring.
apply sym_eq, Zfloor_imp.
simpl; split.
auto with real.
apply Rmult_lt_reg_l with 2.
auto with real.
apply Rle_lt_trans with 1.
right; field.
rewrite Rmult_1_r.
auto with real.
unfold Zminus; rewrite bpow_plus.
reflexivity.
Qed.

Lemma average3_between: Rmin x y <= av <= Rmax x y.
Proof with auto with typeclass_instances.
case (Rle_or_lt x y); intros M.
(* x <= y *)
rewrite Rmin_left; try exact M.
rewrite Rmax_right; try exact M.
now apply average3_between_aux.
(* y < x *)
rewrite Rmin_right; try now left.
rewrite Rmax_left; try now left.
unfold av; rewrite <- (Ropp_involutive x); rewrite <- (Ropp_involutive y).
rewrite average3_symmetry_Ropp.
split; apply Ropp_le_contravar.
apply average3_between_aux.
now apply generic_format_opp.
now apply generic_format_opp.
apply Ropp_le_contravar; now left.
apply average3_between_aux.
now apply generic_format_opp.
now apply generic_format_opp.
apply Ropp_le_contravar; now left.
Qed.


Lemma average3_zero: a = 0 -> av = 0.
Proof with auto with typeclass_instances.
intros H.
assert (y=-x).
apply Rplus_eq_reg_l with x.
apply Rmult_eq_reg_r with (/2).
apply trans_eq with a.
reflexivity.
rewrite H; ring.
apply Rgt_not_eq, Rlt_gt.
auto with real.
unfold av, average3.
rewrite H0.
replace (-x-x) with (-(2*x)) by ring.
rewrite round_generic with (x:=(-(2*x)))...
replace (-(2*x)/2) with (-x) by field.
rewrite round_generic with (x:=-x)...
replace (x+-x) with 0 by ring.
apply round_0...
now apply generic_format_opp.
apply generic_format_opp.
now apply FLT_format_double.
Qed.


Lemma average3_no_underflow_aux_aux: forall z:Z, (0 < z)%Z -> 
    (ZnearestE (Z2R z / 2) < z)%Z.
Proof.
intros z H1.
case (Zle_lt_or_eq 1 z); [omega|intros H2|intros H2].
apply lt_Z2R.
apply Rplus_lt_reg_r with (- ((Z2R z)/2)).
apply Rle_lt_trans with (-(((Z2R z) /2) - Z2R (ZnearestE (Z2R z / 2)))).
right; ring.
apply Rle_lt_trans with (1:= RRle_abs _).
rewrite Rabs_Ropp.
apply Rle_lt_trans with (1:=Znearest_N (fun x => negb (Zeven x)) _).
apply Rle_lt_trans with (1*/2);[right; ring|idtac].
apply Rlt_le_trans with ((Z2R z)*/2);[idtac|right; field].
apply Rmult_lt_compat_r.
auto with real.
replace 1 with (Z2R 1) by reflexivity.
now apply Z2R_lt.
rewrite <- H2.
unfold Znearest; simpl.
replace (Zfloor (1 / 2)) with 0%Z.
rewrite Rcompare_Eq.
simpl; omega.
simpl; field.
unfold Rdiv; rewrite Rmult_1_l.
apply sym_eq, Zfloor_imp.
simpl; split.
auto with real.
apply Rmult_lt_reg_l with 2.
auto with real.
apply Rle_lt_trans with 1.
right; field.
rewrite Rmult_1_r.
auto with real.
Qed.


Lemma average3_no_underflow_aux1: forall f, format f -> 0 < f ->
  f <= round_flt (f/2) -> False.
Proof with auto with typeclass_instances.
intros f Ff Hf1 Hf2.
apply FLT_format_generic in Ff...
destruct Ff as (g, (H1,(H2,H3))).
case (Zle_lt_or_eq emin (Fexp g)); try exact H3; intros H4.
contradict Hf2.
apply Rlt_not_le.
rewrite round_generic...
apply Rplus_lt_reg_l with (-(f/2)).
apply Rle_lt_trans with 0;[right; ring|idtac].
apply Rlt_le_trans with (f*/2);[idtac|right;field].
apply Rmult_lt_0_compat; try assumption.
auto with real.
apply generic_format_FLT.
exists (Float radix2 (Fnum g) (Fexp g-1)).
split.
rewrite H1; unfold F2R; simpl.
unfold Zminus; rewrite bpow_plus.
simpl; field.
split.
now simpl.
simpl; omega.
contradict Hf2; apply Rlt_not_le.
unfold round, scaled_mantissa.
replace (cexp (f/2)) with emin.
rewrite H1; unfold F2R; simpl.
rewrite <- H4.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
apply Z2R_lt.
replace (Z2R (Fnum g) * bpow emin / 2 * bpow (- emin)) with (Z2R (Fnum g) /2).
apply average3_no_underflow_aux_aux.
apply lt_Z2R.
apply Rmult_lt_reg_r with (bpow (Fexp g)).
apply bpow_gt_0.
rewrite Rmult_0_l.
apply Rlt_le_trans with (1:=Hf1).
right; rewrite H1; reflexivity.
unfold Rdiv; apply trans_eq with (Z2R (Fnum g) * / 2 * (bpow (- emin)*bpow emin)).
rewrite <- bpow_plus.
ring_simplify (-emin+emin)%Z.
simpl; ring.
ring.
apply sym_eq, canonic_exp_FLT_FIX.
apply Rgt_not_eq, Rlt_gt.
unfold Rdiv; apply Rmult_lt_0_compat; try assumption.
auto with real.
rewrite H1; unfold F2R, Rdiv; simpl.
replace (/2) with (bpow (-1)) by reflexivity.
rewrite Rmult_assoc, <- bpow_plus.
rewrite Rabs_mult.
rewrite (Rabs_right (bpow _)).
2: apply Rle_ge, bpow_ge_0.
rewrite (Zplus_comm emin _).
rewrite (bpow_plus _ prec _).
apply Rmult_lt_compat.
apply Rabs_pos.
apply bpow_ge_0.
rewrite <- Z2R_Zpower, <- Z2R_abs.
now apply Z2R_lt.
unfold Prec_gt_0 in prec_gt_0_; omega.
rewrite <- H4; apply bpow_lt.
omega.
Qed.


Lemma average3_no_underflow_aux2: forall u v, format u -> format v -> 
    (0 <= u /\ 0 <= v) \/ (u <= 0 /\ v <= 0) ->
    u <= v ->
   (bpow emin) <= Rabs ((u+v)/2) -> average3 u v <> 0.
Proof with auto with typeclass_instances.
clear Fx Fy a av x y; intros x y Fx Fy same_sign xLey H; unfold average3.
intros J.
apply round_plus_eq_zero in J...
2: apply generic_format_round...
assert (H1:x <= 0).
apply Rplus_le_reg_r with (round_flt (round_flt (y - x) / 2)).
rewrite J, Rplus_0_l.
apply round_ge_generic...
apply generic_format_0.
unfold Rdiv; apply Rmult_le_pos.
apply round_ge_generic...
apply generic_format_0.
apply Rplus_le_reg_l with x; now ring_simplify.
auto with real.
destruct H1 as [H1|H1].
(* *)
destruct same_sign as [(H2,H3)|(_,H2)].
contradict H2; now apply Rlt_not_le.
apply average3_no_underflow_aux1 with (-x).
now apply generic_format_opp.
rewrite <- Ropp_0; now apply Ropp_lt_contravar.
apply Rle_trans with (round_flt (round_flt (y - x) / 2)).
apply Rplus_le_reg_l with x.
rewrite J; right; ring.
apply round_le...
unfold Rdiv; apply Rmult_le_compat_r.
auto with real.
apply round_le_generic...
now apply generic_format_opp.
apply Rplus_le_reg_l with x.
now ring_simplify.
(* *)
rewrite H1 in J, H.
rewrite Rplus_0_l in H.
contradict J; apply Rgt_not_eq, Rlt_gt.
rewrite Rplus_0_l.
unfold Rminus; rewrite Ropp_0, Rplus_0_r.
rewrite round_generic with (x:=y)...
apply Rlt_le_trans with (bpow emin).
apply bpow_gt_0.
apply round_ge_generic...
apply FLT_format_bpow...
omega.
apply Rle_trans with (1:=H).
right; apply Rabs_right.
apply Rle_ge; unfold Rdiv; apply Rmult_le_pos.
rewrite <- H1; assumption.
auto with real.
Qed.

Lemma average3_no_underflow_aux3: forall u v, format u -> format v -> 
    (0 <= u /\ 0 <= v) \/ (u <= 0 /\ v <= 0) ->
   (bpow emin) <= Rabs ((u+v)/2) -> average3 u v <> 0.
Proof with auto with typeclass_instances.
clear Fx Fy a av x y; intros x y Fx Fy.
intros same_sign H.
case (Rle_or_lt x y); intros H1.
now apply average3_no_underflow_aux2.
rewrite <- (Ropp_involutive x); rewrite <- (Ropp_involutive y).
rewrite average3_symmetry_Ropp.
apply Ropp_neq_0_compat.
apply average3_no_underflow_aux2.
now apply generic_format_opp.
now apply generic_format_opp.
rewrite <- Ropp_0; case same_sign; intros (T1,T2).
right; split; now apply Ropp_le_contravar.
left; split; now apply Ropp_le_contravar.
apply Ropp_le_contravar; now left.
apply Rle_trans with (1:=H).
rewrite <- Rabs_Ropp.
right; apply f_equal.
unfold Rdiv; ring.
Qed.


Lemma average3_no_underflow: 
  (0 <= x /\ 0 <= y) \/ (x <= 0 /\ y <= 0) ->
  (bpow emin) <= Rabs a -> av <> 0.
Proof with auto with typeclass_instances.
intros; now apply average3_no_underflow_aux3.
Qed.



Lemma average3_correct_aux: forall u v, format u -> format v -> u <= v ->
     (0 <= u /\ 0 <= v) \/ (u <= 0 /\ v <= 0) ->
     0 < Rabs ((u+v)/2) < bpow emin ->
     Rabs (average3 u v -((u+v)/2)) <= 3/2 * ulp_flt ((u+v)/2).
Proof with auto with typeclass_instances.
clear Fx Fy x y a av.
intros u v Fu Fv uLev same_sign.
pose (b:=(u+v)/2); fold b.
(* mostly forward proof *)
intros (H1,H2).
apply generic_format_FIX_FLT,FIX_format_generic in Fu.
apply generic_format_FIX_FLT,FIX_format_generic in Fv.
destruct Fu as ((nu,eu),(J1,J2)).
destruct Fv as ((nv,ev),(J3,J4)); simpl in J2, J4.
(* b is bpow emin /2 *)
assert (b = Z2R (nu+nv) * bpow (emin-1)).
unfold b; rewrite J1, J3; unfold F2R; rewrite J2,J4; simpl.
unfold Zminus; rewrite bpow_plus, Z2R_plus; simpl; field.
assert (Z.abs (nu+nv) = 1)%Z.
assert (0 < Z.abs (nu+nv) < 2)%Z;[idtac|omega].
split; apply lt_Z2R; simpl; rewrite Z2R_abs; 
 apply Rmult_lt_reg_l with (bpow (emin-1)); try apply bpow_gt_0.
rewrite Rmult_0_r.
apply Rlt_le_trans with (1:=H1).
right; rewrite H, Rabs_mult.
rewrite (Rabs_right (bpow (emin -1))).
ring.
apply Rle_ge, bpow_ge_0.
apply Rle_lt_trans with (Rabs b).
right; rewrite H, Rabs_mult.
rewrite (Rabs_right (bpow (emin -1))).
ring.
apply Rle_ge, bpow_ge_0.
apply Rlt_le_trans with (1:=H2).
right; unfold Zminus; rewrite bpow_plus.
simpl; field.
(* only 2 possible values for u and v *)
assert (((nu=0)/\ (nv=1)) \/ ((nu=-1)/\(nv=0)))%Z.
assert (nu <= nv)%Z.
apply le_Z2R.
apply Rmult_le_reg_r with (bpow emin).
apply bpow_gt_0.
apply Rle_trans with u.
right; rewrite J1,J2; reflexivity.
apply Rle_trans with (1:=uLev).
right; rewrite J3,J4; reflexivity.
case same_sign; intros (L1,L2).
rewrite J1 in L1; apply Fnum_ge_0_compat in L1; simpl in L1.
rewrite J3 in L2; apply Fnum_ge_0_compat in L2; simpl in L2.
left.
rewrite Z.abs_eq in H0.
omega.
omega.
rewrite J1 in L1; apply Fnum_le_0_compat in L1; simpl in L1.
rewrite J3 in L2; apply Fnum_le_0_compat in L2; simpl in L2.
right.
rewrite Z.abs_neq in H0.
omega.
omega.
(* look into the 2 possible cases *)
assert (G1:(round_flt (bpow emin/2) = 0)).
replace (bpow emin /2) with (bpow (emin-1)).
unfold round, scaled_mantissa.
rewrite canonic_exp_FLT_FIX.
unfold canonic_exp, FIX_exp; simpl.
rewrite <- bpow_plus.
replace (bpow (emin - 1 + - emin)) with (/2).
replace (ZnearestE (/ 2)) with 0%Z.
unfold F2R; simpl; ring.
unfold Znearest.
replace (Zfloor (/2)) with 0%Z.
rewrite Rcompare_Eq.
reflexivity.
simpl; ring.
apply sym_eq, Zfloor_imp.
simpl; split.
auto with real.
apply Rmult_lt_reg_l with 2.
auto with real.
apply Rle_lt_trans with 1.
right; field.
rewrite Rmult_1_r.
auto with real.
ring_simplify (emin-1+-emin)%Z; reflexivity.
apply Rgt_not_eq, Rlt_gt, bpow_gt_0.
rewrite Rabs_right.
apply bpow_lt.
unfold Prec_gt_0 in prec_gt_0_; omega.
apply Rle_ge, bpow_ge_0.
unfold Zminus; rewrite bpow_plus.
reflexivity.
case H3; intros (T1,T2).
unfold b, average3.
rewrite J1,J3,J2,J4,T1,T2; unfold F2R; simpl.
rewrite Rmult_0_l, Rmult_1_l, 2!Rplus_0_l.
unfold Rminus; rewrite Ropp_0, Rplus_0_r.
rewrite (round_generic _ _ _ (bpow (emin)))...
2: apply FLT_format_bpow...
2: omega.
rewrite G1.
rewrite round_0...
rewrite Rplus_0_l, Rabs_Ropp.
rewrite Rabs_right.
2: apply Rle_ge, Rmult_le_pos.
2: apply bpow_ge_0.
2: now auto with real.
apply Rle_trans with ((3*ulp_flt (bpow emin / 2))/2);[idtac|right; unfold Rdiv; ring].
unfold Rdiv; apply Rmult_le_compat_r.
now auto with real.
apply Rle_trans with (3*bpow emin).
apply Rle_trans with (1*bpow emin).
right; ring.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rplus_le_reg_l with (-1); ring_simplify.
now auto with real.
apply Rmult_le_compat_l.
apply Fourier_util.Rle_zero_pos_plus1.
now auto with real.
rewrite ulp_neq_0.
2: apply Rmult_integral_contrapositive_currified.
2: apply Rgt_not_eq, bpow_gt_0.
2: apply Rinv_neq_0_compat, Rgt_not_eq; fourier.
apply bpow_le.
unfold canonic_exp, FLT_exp.
apply Z.le_max_r.
unfold b, average3.
rewrite J1,J3,J2,J4,T1,T2; unfold F2R; simpl.
rewrite Rmult_0_l, Rplus_0_r.
replace (0 - -1 * bpow emin) with (bpow emin) by ring.
rewrite (round_generic _ _ _ (bpow (emin)))...
2: apply FLT_format_bpow...
2: omega.
rewrite G1.
replace (-1 * bpow emin + 0) with (-bpow emin) by ring.
rewrite round_generic...
2: apply generic_format_opp.
2: apply FLT_format_bpow...
2: omega.
replace (- bpow emin - -1 * bpow emin / 2) with (-((bpow emin)/2)) by field.
rewrite Rabs_Ropp.
rewrite Rabs_right.
replace (-1 * bpow emin / 2) with (-((bpow emin/2))) by field.
rewrite ulp_opp.
apply Rle_trans with ((3*ulp_flt (bpow emin / 2))/2);[idtac|right; unfold Rdiv; ring].
unfold Rdiv; apply Rmult_le_compat_r.
now auto with real.
apply Rle_trans with (3*bpow emin).
apply Rle_trans with (1*bpow emin).
right; ring.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rplus_le_reg_l with (-1); ring_simplify.
now auto with real.
apply Rmult_le_compat_l.
apply Fourier_util.Rle_zero_pos_plus1.
now auto with real.
rewrite ulp_neq_0.
2: apply Rmult_integral_contrapositive_currified.
2: apply Rgt_not_eq, bpow_gt_0.
2: apply Rinv_neq_0_compat, Rgt_not_eq; fourier.
apply bpow_le.
unfold canonic_exp, FLT_exp.
apply Z.le_max_r.
apply Rle_ge, Rmult_le_pos.
apply bpow_ge_0.
now auto with real.
Qed.



Lemma average3_correct_aux2: forall u v, format u -> format v -> u <= v ->
     (0 <= u /\ 0 <= v) \/ (u <= 0 /\ v <= 0) ->
     Rabs (average3 u v -((u+v)/2)) <= 3/2 * ulp_flt ((u+v)/2).
Proof with auto with typeclass_instances.
clear Fx Fy a av x y.
intros u v Fu Fv uLev same_sign.
pose (b:=(u+v)/2); fold b.
assert (T: forall z, Rabs (2*z) = 2* Rabs z).
intros z; rewrite Rabs_mult.
rewrite Rabs_right; try reflexivity.
apply Rle_ge; now auto with real.
destruct uLev as [uLtv|uEqv].
(* when u < v *)
assert (B: u <= v) by now left.
assert (K1: b <> 0).
apply Rmult_integral_contrapositive_currified.
2: apply Rgt_not_eq, Rlt_gt; now auto with real.
intros L; case same_sign; intros (L1,L2).
absurd (0 <= u); try assumption.
apply Rlt_not_le.
apply Rlt_le_trans with v; try assumption.
apply Rplus_le_reg_l with u.
rewrite L, Rplus_0_r; assumption.
absurd (v <= 0); try assumption.
apply Rlt_not_le.
apply Rle_lt_trans with u; try assumption.
apply Rplus_le_reg_r with v.
rewrite L, Rplus_0_l; assumption.
(* . initial lemma *)
assert (Y:(Rabs (round_flt (v - u) - (v-u)) <= ulp_flt b)).
apply Rle_trans with (/2*ulp_flt (v-u)).
apply error_le_half_ulp...
apply Rmult_le_reg_l with 2.
now auto with real.
rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l.
2: apply Rgt_not_eq, Rlt_gt; now auto with real.
apply Rle_trans with (ulp_flt (2*b)).
case same_sign; intros (T1,T2).
apply ulp_le_pos...
apply Rplus_le_reg_l with u; ring_simplify; assumption.
apply Rle_trans with (2*(b-u)).
right; unfold b; field.
apply Rmult_le_compat_l.
now auto with real.
apply Rplus_le_reg_l with (-b+u); ring_simplify; assumption.
rewrite <- (ulp_opp _ _ (2*b)).
apply ulp_le_pos...
apply Rplus_le_reg_l with u; ring_simplify; assumption.
apply Rle_trans with (2*(v-b)).
right; unfold b; field.
apply Rle_trans with (2*(-b));[idtac|right; ring].
apply Rmult_le_compat_l.
now auto with real.
apply Rplus_le_reg_l with b; ring_simplify; assumption.
rewrite 2!ulp_neq_0; trivial.
2: apply Rmult_integral_contrapositive_currified; trivial.
2: apply Rgt_not_eq; fourier.
replace 2 with (bpow 1) by reflexivity.
rewrite <- bpow_plus.
apply bpow_le.
unfold canonic_exp, FLT_exp.
rewrite Rmult_comm, ln_beta_mult_bpow; trivial.
rewrite <- Z.add_max_distr_l.
replace (ln_beta radix2 b + 1 - prec)%Z with (1 + (ln_beta radix2 b - prec))%Z by ring.
apply Z.max_le_compat_l.
omega.
(* . splitting case of av=0 *)
case (Rle_or_lt (bpow emin) (Rabs b)); intros D.
(* . main proof *)
unfold average3.
case (Rle_or_lt (bpow (prec+emin)) (v-u)); intros H1.
(* .. v-u is big enough: division by 2 is exact *)
cut (round_flt (round_flt (v - u) / 2) = round_flt (v - u) / 2).
intros Z; rewrite Z.
replace (round_flt (u + round_flt (v - u) / 2) - b) with
   ((round_flt (u + round_flt (v - u) / 2) - (u + round_flt (v - u) / 2)) +/2*(round_flt (v - u)-(v-u))).
2: unfold b; field.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with (ulp_flt b+/2*ulp_flt b);[idtac|right; field].
apply Rplus_le_compat.
apply Rle_trans with (/2*ulp_flt (u + round_flt (v - u) / 2)).
apply error_le_half_ulp...
apply Rmult_le_reg_l with 2.
auto with real.
rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l.
2: apply Rgt_not_eq, Rlt_gt; now auto with real.
apply Rle_trans with (2:=FLT_ulp_double _ _ _).
apply ulp_le...
replace (u + round_flt (v - u) / 2) with (b+/2*(round_flt (v - u) - (v - u))).
2: unfold b; field.
rewrite (T b).
rewrite Rmult_plus_distr_r, Rmult_1_l.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rplus_le_compat_l.
rewrite Rabs_mult.
rewrite Rabs_right.
2: apply Rle_ge; now auto with real.
apply Rmult_le_reg_l with 2.
now auto with real.
rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l.
2: apply Rgt_not_eq, Rlt_gt; now auto with real.
apply Rle_trans with (1:=Y).
apply Rle_trans with (ulp_flt (2*b)).
apply ulp_le...
rewrite <- (Rmult_1_l (Rabs b)).
rewrite (T b).
apply Rmult_le_compat_r.
apply Rabs_pos.
now auto with real.
rewrite <- (T b).
rewrite <- ulp_abs.
apply FLT_ulp_le_id...
assert (H:generic_format radix2 (FIX_exp emin) (2*b)).
replace (2*b) with (u+v).
2: unfold b; field.
apply generic_format_FIX_FLT,FIX_format_generic in Fu.
apply generic_format_FIX_FLT,FIX_format_generic in Fv.
destruct Fu as (fu,(J1,J2)).
destruct Fv as (fv,(J3,J4)).
apply generic_format_FIX.
exists (Float radix2 (Fnum fu+Fnum fv) emin).
split;[idtac|reflexivity].
rewrite J1,J3; unfold F2R; simpl.
rewrite J2,J4, Z2R_plus; ring.
apply FIX_format_generic in H.
destruct H as ((n,e),(J1,J2)).
rewrite J1; unfold F2R; rewrite J2.
simpl; rewrite Rabs_mult.
pattern (bpow emin) at 1; rewrite <- (Rmult_1_l (bpow emin)).
rewrite (Rabs_right (bpow emin)).
2: apply Rle_ge, bpow_ge_0.
apply Rmult_le_compat_r.
apply bpow_ge_0.
rewrite <- Z2R_abs.
replace 1 with (Z2R 1) by reflexivity.
apply Z2R_le.
assert (0 < Z.abs n)%Z;[idtac|omega].
apply Z.abs_pos.
intros M; apply K1.
apply Rmult_eq_reg_l with 2.
2: apply Rgt_not_eq, Rlt_gt; now auto with real.
rewrite Rmult_0_r, J1,M; unfold F2R; simpl; ring.
rewrite Rabs_mult.
rewrite Rabs_right.
2: apply Rle_ge; auto with real.
apply Rmult_le_compat_l.
now auto with real.
exact Y.
apply round_generic...
apply FLT_format_half...
apply generic_format_round...
apply abs_round_ge_generic...
apply FLT_format_bpow...
unfold Prec_gt_0 in prec_gt_0_; omega.
rewrite Rabs_right; try assumption.
apply Rle_ge; left; apply Rplus_lt_reg_l with u; now ring_simplify.
(* .. v-u is small: subtraction is exact *)
cut ((round_flt (v - u)= (v-u))).
intros Z; rewrite Z.
replace (u + round_flt ((v-u) / 2)) with (b+((round_flt ((v-u) / 2) - (v-u)/2))).
2: unfold b; field.
pose (eps:=(round_flt ((v - u) / 2) - (v - u) / 2)%R); fold eps.
assert (Rabs eps <= /2*bpow emin).
unfold eps.
apply Rle_trans with (1:=error_le_half_ulp _ _ _ _)...
right; apply f_equal.
apply ulp_FLT_small...
rewrite Zplus_comm; apply Rle_lt_trans with (2:=H1).
rewrite Rabs_right.
apply Rmult_le_reg_l with 2.
now auto with real.
apply Rplus_le_reg_l with (-v+2*u).
apply Rle_trans with u.
right; field.
left; now ring_simplify.
apply Rle_ge, Rmult_le_pos.
apply Rplus_le_reg_l with u; now ring_simplify.
now auto with real.
replace (round_flt (b + eps) - b) with ((round_flt (b+eps) -(b+eps)) + eps) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with (/2*ulp_flt (b+eps) + /2*bpow emin).
apply Rplus_le_compat.
apply error_le_half_ulp...
assumption.
apply Rmult_le_reg_l with 2.
now auto with real.
apply Rle_trans with (ulp_flt (b + eps)+bpow emin).
right; field.
apply Rle_trans with (2*ulp_flt b + ulp_flt b).
2: right; field.
apply Rplus_le_compat.
apply Rle_trans with (2:=FLT_ulp_double _ _ _).
apply ulp_le...
rewrite (T b).
rewrite Rmult_plus_distr_r, Rmult_1_l.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rplus_le_compat_l.
apply Rle_trans with (2:=D).
rewrite <- (Rmult_1_l (bpow emin)).
apply Rle_trans with (1:=H).
apply Rmult_le_compat_r.
apply bpow_ge_0.
pattern 1 at 3; rewrite <- Rinv_1.
apply Rinv_le; now auto with real.
rewrite <- ulp_FLT_small with radix2 emin prec 0...
apply ulp_ge_ulp_0...
rewrite Rabs_R0; apply bpow_gt_0.
apply round_generic...
apply FLT_format_plus_small...
now apply generic_format_opp.
rewrite Rabs_right.
now left.
apply Rle_ge, Rplus_le_reg_l with u; now ring_simplify.
(* . when b = bpow emin /2 *)
apply average3_correct_aux; trivial.
split; trivial.
now apply Rabs_pos_lt.
(* . x = y *)
unfold average3,b.
rewrite uEqv.
replace (v-v) with 0 by ring.
rewrite round_0...
unfold Rdiv; rewrite Rmult_0_l.
rewrite round_0...
rewrite Rplus_0_r.
rewrite round_generic...
replace ((v+v)*/2) with v by field.
replace (v-v) with 0 by ring.
rewrite Rabs_R0.
apply Rmult_le_pos.
apply Rmult_le_pos.
apply Fourier_util.Rle_zero_pos_plus1; now auto with real.
now auto with real.
apply ulp_ge_0.
Qed.



(* tight example x=1/2 and y=2^p-1: error is 5/4 ulp *) 

Lemma average3_correct: (0 <= x /\ 0 <= y) \/ (x <= 0 /\ y <= 0) ->
     Rabs (av-a) <= 3/2 * ulp_flt a.
Proof with auto with typeclass_instances.
intros same_sign; case (Rle_or_lt x y); intros H.
now apply average3_correct_aux2.
unfold av, a.
rewrite <- (Ropp_involutive x), <- (Ropp_involutive y).
rewrite average3_symmetry_Ropp.
rewrite <- Rabs_Ropp.
replace (- (- average3 (- x) (- y) - (- - x + - - y) / 2)) with
   (average3 (-x) (-y) - ((-x+-y)/2)).
2: unfold Rdiv; ring.
apply Rle_trans with (3 / 2 * ulp_flt ((- x + - y) / 2)).
apply average3_correct_aux2.
now apply generic_format_opp.
now apply generic_format_opp.
apply Ropp_le_contravar; now left.
rewrite <- Ropp_0; case same_sign; intros (T1,T2).
right; split; now apply Ropp_le_contravar.
left; split; now apply Ropp_le_contravar.
right; apply f_equal.
rewrite <- ulp_opp.
apply f_equal.
unfold Rdiv; ring.
Qed.


(* Lemma average3_symmetry: forall u v, average3 u v = average3 v u.
   is false *)


End av3.





Section average.

Notation bpow e := (bpow radix2 e).

Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE). 
Notation ulp_flt :=(ulp radix2 (FLT_exp emin prec)).
Notation cexp := (canonic_exp radix2 (FLT_exp emin prec)).

Definition average (x y : R) := 
   let samesign :=  match (Rle_bool 0 x), (Rle_bool 0 y) with
        true  , true   => true
      | false , false => true
      | _,_ => false
   end in
     if samesign then 
       match (Rle_bool (Rabs x) (Rabs y)) with
            true => average3 emin prec x y
          | false => average3 emin prec y x
        end
      else average1 emin prec x y.

Variables x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

Let a:=(x+y)/2.
Let av:=average x y.

Lemma average_symmetry: forall u v, average u v = average v u.
Proof.
intros u v; unfold average.
case (Rle_bool_spec 0 u); case (Rle_bool_spec 0 v); intros.
rewrite 2!Rabs_right; try apply Rle_ge; try assumption.
case (Rle_bool_spec u v); case (Rle_bool_spec v u); trivial.
intros; replace u with v; trivial; auto with real.
intros H1 H2; contradict H1; auto with real.
apply average1_symmetry.
apply average1_symmetry.
rewrite 2!Rabs_left; try assumption.
case (Rle_bool_spec (-u) (-v)); case (Rle_bool_spec (-v) (-u)); trivial.
intros; replace u with v; trivial; auto with real.
intros H1 H2; contradict H1; auto with real.
Qed.

Lemma average_symmetry_Ropp: forall u v, format u -> format v -> 
  average (-u) (-v) = - average u v.
Proof with auto with typeclass_instances.
(* first: nonnegative u *)
assert (forall u v, 0 <= u -> format u -> format v -> 
  average (-u) (-v) = - average u v).
intros u v Hu Fu Fv; unfold average.
rewrite 2!Rabs_Ropp.
destruct Hu as [Hu|Hu].
 (* 0 < u *)
 rewrite Rle_bool_false.
 2: apply Ropp_lt_cancel.
 2: now rewrite Ropp_involutive, Ropp_0.
 rewrite (Rle_bool_true 0 u); [idtac|now left].
 rewrite Rabs_right.
 2: apply Rle_ge; now left.
 destruct (total_order_T 0 v) as [Hv|Hv];[destruct Hv as [Hv|Hv] |idtac].
 (* . 0 < u and 0 < v *)
   rewrite Rle_bool_false.
   2: apply Ropp_lt_cancel.
   2: now rewrite Ropp_involutive, Ropp_0.
   rewrite (Rle_bool_true 0 v); [idtac|now left].
   rewrite Rabs_right.
   2: apply Rle_ge; now left.
   case (Rle_bool_spec u v);intros.
   apply average3_symmetry_Ropp.
   apply average3_symmetry_Ropp.
 (* . 0 < u and v = 0 *)
   rewrite <- Hv, Ropp_0, Rabs_R0.
   rewrite Rle_bool_true ;[idtac|now right].
   rewrite Rle_bool_false; try exact Hu.
   unfold average1, average3.
   unfold Rminus; rewrite Ropp_0, Rplus_0_l, 2!Rplus_0_r.
   rewrite (round_generic _ _ _ u); trivial.
   rewrite (round_generic _ _ _ (-u)).
   2: now apply generic_format_opp.
   rewrite <- round_NE_opp.
   rewrite <- round_NE_opp.
   rewrite (round_generic _ _ _ (round_flt (-(u/2)))).
   apply f_equal; field.
   apply generic_format_round...
 (* . 0 < u and v < 0 *)
   rewrite Rabs_left; trivial.
   rewrite Rle_bool_true.
   rewrite Rle_bool_false; trivial.
   apply average1_symmetry_Ropp.
   rewrite <- Ropp_0; apply Ropp_le_contravar.
   now left.
 (* u = 0 *)
   rewrite <- Hu, Ropp_0, Rabs_R0.
   rewrite Rle_bool_true.
   2: now right.
   rewrite (Rle_bool_true 0 (Rabs v)).
   2: apply Rabs_pos.
   destruct (total_order_T 0 v) as [Hv|Hv];[destruct Hv as [Hv|Hv] |idtac].
   (* . u=0 and 0 < v *)
   rewrite Rle_bool_false.
   rewrite Rle_bool_true.
   unfold average1, average3.
   unfold Rminus; rewrite Ropp_0, 2!Rplus_0_l, Rplus_0_r.
   rewrite (round_generic _ _ _ v); trivial.
   rewrite (round_generic _ _ _ (-v)).
   2: now apply generic_format_opp.
   rewrite <- round_NE_opp.
   rewrite <- round_NE_opp.
   rewrite (round_generic _ _ _ (round_flt (-(v/2)))).
   apply f_equal; field.
   apply generic_format_round...
   now left.
   rewrite <- Ropp_0; now apply Ropp_lt_contravar.
  (* . u=0 and v=0 *)
   rewrite <- Hv, Ropp_0.
   rewrite Rle_bool_true.
   2: now right.
   unfold average3.
   replace (0-0) with 0 by ring; rewrite round_0...
   unfold Rdiv; rewrite Rmult_0_l, round_0, Rplus_0_l...
  rewrite round_0...
  ring.
  (* . u=0 and v < 0 *)
  rewrite Rle_bool_true.
  rewrite Rle_bool_false.
   unfold average1, average3.
   unfold Rminus; rewrite Ropp_0, 2!Rplus_0_l, Rplus_0_r.
   rewrite (round_generic _ _ _ v); trivial.
   rewrite (round_generic _ _ _ (-v)).
   2: now apply generic_format_opp.
   rewrite <- round_NE_opp.
   rewrite (round_generic _ _ _ (round_flt (-v/2))).
   apply f_equal; field.
   apply generic_format_round...
   exact Hv.
   rewrite <- Ropp_0; apply Ropp_le_contravar; now left.
(* any u *)
intros u v Fu Fv.
case (Rle_or_lt 0 u).
intros Hu; now apply H.
intros Hu.
apply trans_eq with (- average (--u) (--v)).
rewrite (H (-u) (-v)).
ring.
rewrite <- Ropp_0; apply Ropp_le_contravar; now left.
apply generic_format_opp...
apply generic_format_opp...
apply f_equal, f_equal2; ring.
Qed.


Lemma average_same_sign_1: 0 <= a -> 0 <= av.
Proof with auto with typeclass_instances.
intros H; unfold av, average.
case (Rle_bool_spec 0 x); case (Rle_bool_spec 0 y); intros.
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_same_sign_1...
apply average3_same_sign_1...
now rewrite Rplus_comm.
apply average1_same_sign_1...
apply average1_same_sign_1...
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_same_sign_1...
apply average3_same_sign_1...
now rewrite Rplus_comm.
Qed.

Lemma average_same_sign_2: a <= 0-> av <= 0.
Proof with auto with typeclass_instances.
intros H; unfold av, average.
case (Rle_bool_spec 0 x); case (Rle_bool_spec 0 y); intros.
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_same_sign_2...
apply average3_same_sign_2...
now rewrite Rplus_comm.
apply average1_same_sign_2...
apply average1_same_sign_2...
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_same_sign_2...
apply average3_same_sign_2...
now rewrite Rplus_comm.
Qed.

Lemma average_correct: Rabs (av -a) <= 3/2 * ulp_flt a.
Proof with auto with typeclass_instances.
unfold av,a,average.
case (Rle_bool_spec 0 x); case (Rle_bool_spec 0 y); intros.
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_correct...
rewrite Rplus_comm.
apply average3_correct...
apply average1_correct_weak2...
apply average1_correct_weak2...
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_correct...
right; split; now left.
rewrite Rplus_comm.
apply average3_correct...
right; split; now left.
Qed.

Lemma average_between: Rmin x y <= av <= Rmax x y.
Proof with auto with typeclass_instances.
unfold av,a,average.
case (Rle_bool_spec 0 x); case (Rle_bool_spec 0 y); intros.
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_between...
rewrite Rmin_comm, Rmax_comm.
apply average3_between...
apply average1_between...
apply average1_between...
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_between...
rewrite Rmin_comm, Rmax_comm.
apply average3_between...
Qed.


Lemma average_zero: a = 0 -> av = 0.
Proof with auto with typeclass_instances.
unfold av,a,average.
case (Rle_bool_spec 0 x); case (Rle_bool_spec 0 y); intros.
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_zero...
apply average3_zero...
now rewrite Rplus_comm.
apply average1_zero...
apply average1_zero...
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_zero...
apply average3_zero...
now rewrite Rplus_comm.
Qed.


Lemma average_no_underflow: (bpow emin) <= Rabs a -> av <> 0.
Proof with auto with typeclass_instances.
unfold av,a,average.
case (Rle_bool_spec 0 x); case (Rle_bool_spec 0 y); intros.
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_no_underflow...
apply average3_no_underflow...
now rewrite Rplus_comm.
apply average1_no_underflow...
apply average1_no_underflow...
case (Rle_bool_spec (Rabs x) (Rabs y)); intros.
apply average3_no_underflow...
right; split; now left.
apply average3_no_underflow...
right; split; now left.
now rewrite Rplus_comm.
Qed.



End average.
