Require Import Fcore.
Require Import Fcalc_bracket Fcalc_round Fcalc_ops Fcalc_div Fcalc_sqrt.

Section Compute.

Variable beta : radix.

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.

Variable prec : Z.
Hypothesis Hprec : (0 < prec)%Z.
Hypothesis fexp_prec :
  forall e, (e - prec <= fexp e)%Z.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Variable choice : bool -> Z -> location -> Z.
Hypothesis rnd_choice :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  rnd x = cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l).

Lemma Rsgn_F2R :
  forall m e,
  Rlt_bool (F2R (Float beta m e)) 0 = Zlt_bool m 0.
Proof.
intros m e.
case Zlt_bool_spec ; intros H.
apply Rlt_bool_true.
now apply F2R_lt_0_compat.
apply Rlt_bool_false.
now apply F2R_ge_0_compat.
Qed.

Definition plus (x y : float beta) :=
  let (m, e) := Fplus beta x y in
  let s := Zlt_bool m 0 in
  let '(m', e', l) := truncate beta fexp (Zabs m, e, loc_Exact) in
  Float beta (cond_Zopp s (choice s m' l)) e'.

Theorem plus_correct :
  forall x y : float beta,
  round beta fexp rnd (F2R x + F2R y) = F2R (plus x y).
Proof.
intros x y.
unfold plus.
rewrite <- F2R_plus.
destruct (Fplus beta x y) as [m e].
rewrite (round_trunc_sign_any_correct beta fexp rnd choice rnd_choice _ (Zabs m) e loc_Exact).
3: now right.
destruct truncate as [[m' e'] l'].
apply (f_equal (fun s => F2R (Float beta (cond_Zopp s (choice s _ _)) _))).
apply Rsgn_F2R.
apply inbetween_Exact.
apply sym_eq, F2R_Zabs.
Qed.

Definition mult (x y : float beta) :=
  let (m, e) := Fmult beta x y in
  let s := Zlt_bool m 0 in
  let '(m', e', l) := truncate beta fexp (Zabs m, e, loc_Exact) in
  Float beta (cond_Zopp s (choice s m' l)) e'.

Theorem mult_correct :
  forall x y : float beta,
  round beta fexp rnd (F2R x * F2R y) = F2R (mult x y).
Proof.
intros x y.
unfold mult.
rewrite <- F2R_mult.
destruct (Fmult beta x y) as [m e].
rewrite (round_trunc_sign_any_correct beta fexp rnd choice rnd_choice _ (Zabs m) e loc_Exact).
3: now right.
destruct truncate as [[m' e'] l'].
apply (f_equal (fun s => F2R (Float beta (cond_Zopp s (choice s _ _)) _))).
apply Rsgn_F2R.
apply inbetween_Exact.
apply sym_eq, F2R_Zabs.
Qed.

Definition sqrt (x : float beta) :=
  let (m, e) := x in
  if Zlt_bool 0 m then
    let '(m', e', l) := truncate beta fexp (Fsqrt_core beta prec m e) in
    Float beta (choice false m' l) e'
  else Float beta 0 0.

Theorem sqrt_correct :
  forall x : float beta,
  round beta fexp rnd (R_sqrt.sqrt (F2R x)) = F2R (sqrt x).
Proof.
intros [m e].
unfold sqrt.
case Zlt_bool_spec ; intros Hm.
generalize (Fsqrt_core_correct beta prec m e Hm).
destruct Fsqrt_core as [[m' e'] l].
intros [Hs1 Hs2].
rewrite (round_trunc_sign_any_correct beta fexp rnd choice rnd_choice _ m' e' l).
destruct truncate as [[m'' e''] l'].
now rewrite Rlt_bool_false by apply sqrt_ge_0.
now rewrite Rabs_pos_eq by apply sqrt_ge_0.
left.
apply Zle_trans with (2 := fexp_prec _).
clear -Hs1 ; omega.
destruct (Req_dec (F2R (Float beta m e)) 0) as [Hz|Hz].
rewrite Hz, sqrt_0, F2R_0.
now apply round_0.
unfold R_sqrt.sqrt.
destruct Rcase_abs as [H|H].
rewrite F2R_0.
now apply round_0.
destruct H as [H|H].
elim Rgt_not_le with (1 := H).
now apply F2R_le_0_compat.
now elim Hz.
Qed.

Lemma Rsgn_div :
  forall x y : R,
  x <> R0 -> y <> R0 ->
  Rlt_bool (x / y) 0 = xorb (Rlt_bool x 0) (Rlt_bool y 0).
Proof.
intros x y Hx0 Hy0.
unfold Rdiv.
case (Rlt_bool_spec x) ; intros Hx ;
  case (Rlt_bool_spec y) ; intros Hy.
apply Rlt_bool_false.
rewrite <- Rmult_opp_opp.
apply Rlt_le, Rmult_lt_0_compat.
now apply Ropp_gt_lt_0_contravar.
apply Ropp_gt_lt_0_contravar.
now apply Rinv_lt_0_compat.
apply Rlt_bool_true.
apply Ropp_lt_cancel.
rewrite Ropp_0, <- Ropp_mult_distr_l_reverse.
apply Rmult_lt_0_compat.
now apply Ropp_gt_lt_0_contravar.
apply Rinv_0_lt_compat.
destruct Hy as [Hy|Hy].
easy.
now elim Hy0.
apply Rlt_bool_true.
apply Ropp_lt_cancel.
rewrite Ropp_0, <- Ropp_mult_distr_r_reverse.
apply Rmult_lt_0_compat.
destruct Hx as [Hx|Hx].
easy.
now elim Hx0.
apply Ropp_gt_lt_0_contravar.
now apply Rinv_lt_0_compat.
apply Rlt_bool_false.
apply Rlt_le, Rmult_lt_0_compat.
destruct Hx as [Hx|Hx].
easy.
now elim Hx0.
apply Rinv_0_lt_compat.
destruct Hy as [Hy|Hy].
easy.
now elim Hy0.
Qed.

Definition div (x y : float beta) :=
  let (mx, ex) := x in
  let (my, ey) := y in
  if Zeq_bool mx 0 then Float beta 0 0
  else
    let '(m, e, l) := truncate beta fexp (Fdiv_core beta prec (Zabs mx) ex (Zabs my) ey) in
    let s := xorb (Zlt_bool mx 0) (Zlt_bool my 0) in
    Float beta (cond_Zopp s (choice s m l)) e.

Theorem div_correct :
  forall x y : float beta,
  F2R y <> R0 ->
  round beta fexp rnd (F2R x / F2R y) = F2R (div x y).
Proof.
intros [mx ex] [my ey] Hy.
unfold div.
case Zeq_bool_spec ; intros Hm.
rewrite Hm, 2!F2R_0.
unfold Rdiv.
rewrite Rmult_0_l.
now apply round_0.
assert (Hx: (0 < Zabs mx)%Z) by now apply Z.abs_pos.
assert (Hy': (0 < Zabs my)%Z).
  apply Z.abs_pos.
  contradict Hy.
  rewrite Hy.
  apply F2R_0.
generalize (Fdiv_core_correct beta prec (Zabs mx) ex (Zabs my) ey Hprec Hx Hy').
destruct Fdiv_core as [[m e] l].
intros [Hs1 Hs2].
rewrite (round_trunc_sign_any_correct beta fexp rnd choice rnd_choice _ m e l).
destruct truncate as [[m' e'] l'].
apply (f_equal (fun s => F2R (Float beta (cond_Zopp s (choice s _ _)) _))).
rewrite Rsgn_div.
apply f_equal2 ; apply Rsgn_F2R.
contradict Hm.
apply F2R_eq_0_reg with (1 := Hm).
exact Hy.
unfold Rdiv.
rewrite Rabs_mult, Rabs_Rinv.
rewrite <- 2!F2R_Zabs.
exact Hs2.
exact Hy.
left.
apply Zle_trans with (2 := fexp_prec _).
clear -Hs1 ; omega.
Qed.

End Compute.

Goal
  let beta := Build_radix 5 (eq_refl true) in
  let prec := 3%Z in
  forall c1 c2 mx,
  let x := F2R (Float beta mx 0) in
  (0 <= mx < 125)%Z ->
  let rnd c := round beta (FLX_exp prec) (Znearest c) in
  rnd c1 (R_sqrt.sqrt (rnd c2 (x * x)%R)) = x.
Proof with auto with typeclass_instances.
intros beta prec c1 c2 mx x Hm rnd.
assert (Hprec: Prec_gt_0 prec) by easy.
unfold x, rnd.
set (r c (s : bool) m l := cond_incr (round_N (if s then negb (c (- (m + 1))%Z) else c m) l) m).
rewrite mult_correct with (choice := r c2)...
2: intros x' m l H ; now apply inbetween_int_N_sign.
rewrite sqrt_correct with (prec := prec) (choice := r c1)...
2: intros e ; apply Zle_refl.
2: intros x' m l H ; now apply inbetween_int_N_sign.
apply Rminus_diag_uniq.
rewrite <- F2R_minus.
set (f mx := let x := Float beta mx 0 in Fminus beta
  (sqrt beta (FLX_exp prec) prec (r c1) (mult beta (FLX_exp prec) (r c2) x x)) x).
fold (f mx).
assert (Fnum (f mx) = Z0).
clear x.
revert mx Hm.
set (g := fix g m := match m with O => true | S m => match Fnum (f (Z_of_nat m)) with Z0 => g m | _ => false end end).
assert (g 125 = true) by now vm_compute.
revert H.
clearbody f.
clear.
change 125%Z with (Z_of_nat 125).
induction (125).
intros _ mx [H1 H2].
elim (Zlt_irrefl 0).
now apply Zle_lt_trans with mx.
simpl g.
rewrite inj_S.
intros H mx [H1 H2].
apply Zlt_succ_le in H2.
destruct (Zle_lt_or_eq _ _ H2) as [H3|H3].
destruct (Fnum (f (Z.of_nat n))) ; try easy.
now apply IHn ; try split.
rewrite H3.
now destruct (Fnum (f (Z.of_nat n))).
destruct (f mx).
simpl in H.
rewrite H.
apply F2R_0.
Qed.
