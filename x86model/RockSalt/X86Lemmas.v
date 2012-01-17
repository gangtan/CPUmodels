(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)


(** X86Lemmas.v. This file holds lemmas about X86 instructions *)

Require Import Tacs.
Require Import ZArith.
Require Import List.
Require Import Coqlib.
Require Import Bits.
Require Import X86Syntax.
Require Import X86Semantics.
Require Import Monad.
Require Import Int32.
Require Import Eqdep.
Require Import VerifierDFA.
Close Scope char_scope.

Import X86_RTL.
Import X86_MACHINE.
Import X86_Decode.

Local Open Scope monad_scope.


Notation SegStart s seg := (seg_regs_starts (rtl_mach_state s) seg).
Notation SegLimit s seg := (seg_regs_limits (rtl_mach_state s) seg).
Notation PC s := (pc_reg (rtl_mach_state s)).

Notation CStart s := (seg_regs_starts (rtl_mach_state s) CS).
Notation CLimit s := (seg_regs_limits (rtl_mach_state s) CS).
Notation DStart s := (seg_regs_starts (rtl_mach_state s) DS).
Notation DLimit s := (seg_regs_limits (rtl_mach_state s) DS).
Notation SStart s := (seg_regs_starts (rtl_mach_state s) SS).
Notation SLimit s := (seg_regs_limits (rtl_mach_state s) SS).
Notation GStart s := (seg_regs_starts (rtl_mach_state s) GS).
Notation GLimit s := (seg_regs_limits (rtl_mach_state s) GS).
Notation EStart s := (seg_regs_starts (rtl_mach_state s) ES).
Notation ELimit s := (seg_regs_limits (rtl_mach_state s) ES).

(** * Lemmas and tactics for eliminating and introducing a RTL monad *)

Lemma rtl_bind_okay_elim:
  forall (A B:Type) (c1:RTL A) (f: A -> RTL B) (s1 s2:rtl_state) (v:B),
    Bind _ c1 f s1 = (Okay_ans v, s2)
      -> exists s1': rtl_state, exists v':A,
            c1 s1 = (Okay_ans v', s1') /\ f v' s1' = (Okay_ans v, s2).
Proof. intros. unfold Bind, RTL_monad in H. 
  destruct (c1 s1) as [r s1']. destruct r as [ | | v']; try discriminate.
  exists s1'; exists v'. tauto.
Qed.

Lemma rtl_bind_okay_intro :
  forall (A B:Type) (c1:RTL A) (f: A -> RTL B) (s1 s2 s1':rtl_state)
    (v':A) (v:B),
    c1 s1 = (Okay_ans v', s1') -> f v' s1' = (Okay_ans v, s2)
      -> Bind _ c1 f s1 = (Okay_ans v, s2).
Proof. intros. unfold Bind, RTL_monad. rewrite H. trivial. Qed.

Lemma rtl_bind_safefail_intro1 :
  forall (A B:Type) (c1:RTL A) (f: A -> RTL B) (s1 s2 s1':rtl_state)
    (v':A),
    c1 s1 = (Okay_ans v', s1') -> f v' s1' = (SafeFail_ans _, s2)
      -> Bind _ c1 f s1 = (SafeFail_ans _, s2).
Proof. intros. unfold Bind, RTL_monad. rewrite H. trivial. Qed.

Lemma rtl_bind_fail_elim :
  forall (A B:Type) (c1:RTL A) (f: A -> RTL B) (s1 s2:rtl_state),
    Bind _ c1 f s1 = (Fail_ans _, s2)
      -> (c1 s1) = (Fail_ans _, s2) \/
         (exists s1': rtl_state, exists v':A,
            c1 s1 = (Okay_ans v', s1') /\ f v' s1' = (Fail_ans _, s2)).
Proof. intros. unfold Bind, RTL_monad in H. 
  destruct (c1 s1) as [r s1']. destruct r as [ | | v']; try discriminate.
    prover.
    right. exists s1', v'. prover.
Qed.

(** Find a (v <- op1; op2) s = (Okay_ans v', s') in the context; break
 ** it using rtl_bind_okay_elim; introduce the intermediate state 
 ** and value into the context; try the input tactic *)
Ltac rtl_okay_break := 
  match goal with
    | [H: Bind _ _ _ ?s = (Okay_ans ?v', ?s') |- _]  => 
      apply rtl_bind_okay_elim in H; 
      let H1 := fresh "H" in let s' := fresh "s" in let v' := fresh "v" in 
        destruct H as [s' [v' [H1 H]]]
  end.

(** Find a (v <- op1; op2) s = Failed in the context; break
 ** it using rtl_bind_fail_elim to destruct the goal into two cases *)
Ltac rtl_fail_break := 
  match goal with
    | [H: Bind _ _ _ ?s = (Fail_ans _, _) |- _]  => 
      apply rtl_bind_fail_elim in H;
      destruct H as [H|H];
      [idtac|
        let H1 := fresh "H" in let s' := fresh "s" in let v' := fresh "v" in 
        destruct H as [s' [v' [H1 H]]]]
  end.

(* Destruct the head in a match clause *)
Ltac extended_destruct_head c := 
  match c with
    | context[if ?X then _ else _] => destruct X
    | context[match ?X with Some _ => _ | None => _  end] => destruct X
    | context[match ?X with (_, _)  => _ end] => destruct X
    | context[match ?X with nil => _ | cons _ _ => _ end] => destruct X
    | context[match ?X with O => _ | S _ => _  end] => destruct X
    | context[match ?X with 0%Z => _ | Zpos _  => _ | Zneg _ => _ end] => destruct X
    | context[match ?X with Imm_op _ => _ | Reg_op _ => _ 
         | Address_op _ => _ | Offset_op _ => _ end] => destruct X
    | context[match ?X with Reg_ri _ => _ | Imm_ri _ => _ end] => destruct X
    | context[match ?X with | EAX => _ | EBX => _ | ECX => _ | EDX => _ 
         | ESP => _ | EBP => _ | ESI => _ | EDI => _ end] => destruct X
    | context[match ?X with lock => _ | rep => _ | repn => _ end] => destruct X
    | context[match ?X with O_ct => _ | NO_ct => _ | B_ct => _ | NB_ct => _
         | E_ct => _ | NE_ct => _ | BE_ct => _ | NBE_ct => _
         | S_ct => _ | NS_ct => _ | P_ct => _ | NP_ct => _
         | L_ct => _ | NL_ct => _ | LE_ct => _ | NLE_ct => _ end] => destruct X
    | _ => fail
  end.

(** * Lemmas and tactics for simplifying a RTL computation*)

Lemma update_env1: forall s r1 r2 v env,
  r1 <> r2 -> (update_env r1 v env) s r2 = env s r2.
Proof.
    intros s r1 r2 v env.
    intros neq.
    unfold update_env.
    destruct eq_nat_dec.
      unfold eq_rec_r.
      unfold eq_rec.
      unfold eq_rect.
      rewrite (UIP_refl _ _ _).
      destruct (eq_pseudo_reg r1 r2).
      rewrite e0 in neq.
      intuition.
      trivial.
    trivial.
Qed.

Lemma update_env2: forall s1 s2 (r1: pseudo_reg s1) (r2: pseudo_reg s2) v env,
  s1 <> s2 -> (update_env r1 v env) s2 r2 = env s2 r2.
Proof.
    intros s1 s2 r1 r2 v env neq.
    unfold update_env.
    destruct eq_nat_dec.
    rewrite e in neq.
    intuition.
    trivial.
Qed.

Lemma update_env3: forall s r1 v env,
  (update_env r1 v env) s r1 = v.
Proof.
    intros s r1 v env.
    unfold update_env.
    destruct eq_nat_dec.
      unfold eq_rec_r.
      unfold eq_rec.
      unfold eq_rect.
      rewrite (UIP_refl _ _ _).
      destruct (eq_pseudo_reg r1 r1).
      trivial. intuition. intuition.
Qed.

Lemma update_env4: forall s s2 (r1: pseudo_reg s) r2 v0 v1 env,
  (update_env r1 v1 (update_env r1 v0 env)) s2 r2 = (update_env r1 v1 env) s2 r2.
Proof.
    intros.
    destruct (eq_nat_dec s s2); intros.
    subst.
    unfold update_env.
    destruct (eq_pseudo_reg r1 r2).
    subst.
    destruct eq_nat_dec.
      unfold eq_rec_r.
      unfold eq_rec.
      unfold eq_rect.
      rewrite (UIP_refl _ _ _).
      destruct (eq_pseudo_reg r2 r2).
      trivial. intuition. intuition.
    destruct eq_nat_dec.
      unfold eq_rec_r.
      unfold eq_rec.
      unfold eq_rect.
      rewrite (UIP_refl _ _ _).
      destruct (eq_pseudo_reg r1 r2).
      trivial. trivial. trivial.
    rewrite update_env2.
    unfold update_env.
    destruct eq_nat_dec.
    intuition. trivial. trivial.
Qed.

Ltac size_compare_tac := unfold RTL.size1, RTL.size32; omega.

Hint Rewrite update_env3 : rtl_rewrite_db.
Hint Rewrite update_env2 using size_compare_tac : rtl_rewrite_db.
Hint Rewrite update_env1 using (congruence || (injection; omega)) : rtl_rewrite_db.

Lemma update_env5: forall sz1 sz2 idx1 idx2 v env,
  idx1 <> idx2
    -> (update_env (ps_reg sz1 idx1) v env) sz2 (ps_reg sz2 idx2)
         = env sz2 (ps_reg sz2 idx2).
Proof. intros. generalize (eq_nat_dec sz1 sz2); intros.
  destruct H0. rewrite <- e. autorewrite with rtl_rewrite_db. trivial.
    autorewrite with rtl_rewrite_db. trivial.
Qed.        

Hint Rewrite update_env5 using omega : rtl_rewrite_db.


Lemma one_plus_rewrite_2 : forall x, x + 1 + 1 =  x + 2.
Proof. intros. ring. Qed.
Lemma one_plus_rewrite_3 : forall x, x + 1 + 1 + 1 = x + 3.
Proof. intros. ring. Qed.
Lemma one_plus_rewrite_4 : forall x, x + 1 + 1 + 1 + 1 = x + 4.
Proof. intros. ring. Qed.
Hint Rewrite one_plus_rewrite_2 one_plus_rewrite_3 
  one_plus_rewrite_4 : rtl_rewrite_db.

Ltac simpl_rtl := autorewrite with rtl_rewrite_db in *.

(** * Lemmas about basic operations that are used to define
    * instruction semantics. Conventions used in lemmas are explained
      below:
      
      (1) Lemmas ending with "_equation" are for instructions that
      always suceed and return the identical state when given an
      initial state; * in addtion, the values they return are
      easy to write down.
      
      (2) Lemmas ending with "_exists" are for instructions that
      always succeed and return the same state. But the return
      values are not easy to write down; so we use an existential
      in the lemmas.
 *)

Lemma in_seg_bounds_equation : forall seg a s,
  in_seg_bounds seg a s =
    (Okay_ans (int32_lequ_bool a (seg_regs_limits (rtl_mach_state s) seg)), s).
Proof. intros. trivial. Qed.

Lemma in_seg_bounds_rng_equation : forall s sreg a offset,
  in_seg_bounds_rng sreg a offset s = 
    (Okay_ans (andb (int32_lequ_bool a (a +32 offset))
      (int32_lequ_bool (a +32 offset) (seg_regs_limits (rtl_mach_state s) sreg))), s).
Proof. trivial. Qed.

(*
Lemma fetch_n_exists : forall (n:nat) (pc:int32) (s:rtl_state),
  exists bytes, fetch_n_rtl n pc s = (Okay_ans bytes, s).
Proof. unfold fetch_n_rtl. intros. exists (fetch_n n pc s). trivial. Qed.
*)

Ltac rtl_comp_elim_exist H lm name:=
  let Ht := fresh "Ht" in
    destruct lm as [name Ht];
    unfold Bind at 1 in H; unfold RTL_monad at 1 in H;
    rewrite Ht in H.

Ltac rtl_comp_elim_L1 :=
  let unfold_rtl_monad H := 
    unfold Bind at 1 in H; unfold RTL_monad at 1 in H
  in match goal with
    | [H: Return ?v ?s = _ |- _] =>
      compute [Return Bind RTL_monad] in H
    | [H: SafeFail _ _ = _ |- _] =>
      compute [SafeFail] in H
    | [H: set_ps _ _ _ = _ |- _] =>
      compute [set_ps] in H
    | [H: Bind _ (get_ps _) _ _ = _ |- _] =>
      unfold_rtl_monad H; compute [get_ps] in H
    | [H: Bind _ (set_ps _ _) _ _ = _ |- _] =>
      unfold_rtl_monad H; compute [set_ps] in H
    | [H: Bind _ (get_loc _) _ _ = _ |- _] =>
      unfold_rtl_monad H; compute [get_loc get_location] in H
    | [H: Bind _ (in_seg_bounds _ _) _ _ = _ |- _] =>
      unfold_rtl_monad H; rewrite in_seg_bounds_equation in H
    | [H: Bind _ (in_seg_bounds_rng _ _ _) _ _ = _ |- _] =>
      unfold_rtl_monad H; rewrite in_seg_bounds_rng_equation in H
    | [H: Bind _ flush_env _ _ = _ |- _] =>
      unfold_rtl_monad H; compute [flush_env] in H
    | [H: Bind _ (Return _) _ _ = _ |- _] =>
      unfold_rtl_monad H; compute [Return Bind RTL_monad] in H
(*
    | [H: Bind _ (fetch_n_rtl ?n ?pc) _ ?s = _ |- _] =>
      let name := fresh "bytes" in
        rtl_comp_elim_exist H (fetch_n_exists n pc s) name *)
  end.

(*
Lemma effective_addr_exists : forall (a:address) (s:mach_state),
  exists w:int32, effective_addr a s = Succ (s, w).
Proof. unfold effective_addr; intros.
  repeat destruct_head;
  eexists; repeat mach_succ_intro_L1; simpl; trivial.
Qed.

Ltac mach_comp_elim_L2 :=
   match goal with
    | [H: Bind _ (effective_addr ?a) _ ?s = _ |- _] =>
      let name := fresh "w" in
        mach_comp_elim_exist H (effective_addr_exists a s) name
   end.
*)

Ltac rtl_comp_elim :=  rtl_comp_elim_L1.

Ltac rtl_invert := 
  let tac1 H := 
    match type of H with
      | (Okay_ans ?v, ?s) = (Okay_ans ?v', ?s') =>
        inversion H; subst s'; try (subst v'); clear H
      | (SafeFail_ans _, _) = (Okay_ans _, _) => inversion H
      | (Fail_ans _, _) = (Okay_ans _, _) => inversion H
    end
  in appHyps tac1.

Ltac rtl_okay_elim :=  rtl_comp_elim || rtl_invert || rtl_okay_break.

Ltac removeUnit :=
  repeat (match goal with
            | [v:unit |- _] => destruct v
          end).

Ltac rtl_okay_intro_L1 :=
  match goal with
    | [|- Bind _ (get_loc (seg_reg_start_loc _)) _ _ = (Okay_ans _, _) ] =>
      eapply rtl_bind_okay_intro; [compute [get_loc]; trivial | idtac]
    | [|- Bind _ (get_byte _) _ _ = (Okay_ans _, _) ] =>
      eapply rtl_bind_okay_intro; [compute [get_byte]; trivial | idtac]
    | [|- Bind _ (in_seg_bounds_rng _ _ _) _ _ = (Okay_ans _, _)] =>
      eapply rtl_bind_okay_intro; 
      [apply in_seg_bounds_rng_equation | idtac]
  end.

Ltac rtl_okay_intro := rtl_okay_intro_L1.

(** * Lemmas and tactics for eliminating and introducing a conversion monad *)
Lemma conv_bind_elim :
  forall (A B:Type) (cv1:Conv A) (f: A -> Conv B) (cs1 cs2:conv_state) (v:B),
    Bind _ cv1 f cs1 = (v, cs2)
      -> exists cs1': conv_state, exists v':A,
            cv1 cs1 = (v', cs1') /\ f v' cs1' = (v, cs2).
Proof. unfold Bind, Conv_monad. intros.
  destruct (cv1 cs1) as [v' cs1'].
  exists cs1', v'. prover.
Qed.

Ltac conv_break := 
  match goal with
    | [H: Bind _ _ _ ?cs = (?v', ?cs') |- _]  => 
      apply conv_bind_elim in H;
      let H1 := fresh "H" in let cs1 := fresh "cs" in let v1 := fresh "v" in 
        destruct H as [cs1 [v1 [H1 H]]]
  end.

(** * Lemmas about RTL_step_list *)

Lemma RTL_step_list_app : forall rl1 rl2, 
  RTL_step_list (rl1 ++ rl2)  = (RTL_step_list rl1;; RTL_step_list rl2).
Proof. induction rl1 as [ | i rl1]; intros.
  Case "rt1=nil". simpl app. 
    assert (RTL_step_list nil = ret tt) by trivial.
    rewrite H. rewrite ret_left_unit. trivial.
  Case "i::rt1". simpl app.
    unfold RTL_step_list at 1. fold RTL_step_list. 
    unfold RTL_step_list at 2. fold RTL_step_list.
    rewrite IHrl1.
    rewrite bind_assoc. trivial.
Qed.

Lemma RTL_step_list_cons : forall i rl,
  RTL_step_list (i :: rl)  = (interp_rtl i;; RTL_step_list rl).
Proof. trivial. Qed.

Lemma RTL_step_list_nil : RTL_step_list nil  = ret tt.
Proof. trivial. Qed.

Hint Rewrite RTL_step_list_app RTL_step_list_cons RTL_step_list_nil : step_list_db.


(** * The following sets up the general framework for proving properties of
   instruction semantics:
   (1) Module type RTL_STATE_REL provides the abstraction of a relation between 
       two RTL states, e.g., the two states have the same segment registers.
   (2) Module type RTL_Prop provides the abstraction of a property about
       RTL computations.
   (3) Functor RTL_Prop takes a RTL_STATE_REL module and lifts the 
       relation to a property about RTL compuation.
   (4) Functor Conv_Prop takes a RTL_Prop module and lifts the 
       property to a property about conversion.
*)

Module Type RTL_STATE_REL.
  (* A binary relation that relates two RTL states *)
  Parameter brel : rtl_state -> rtl_state -> Prop.
  (* The relation is reflexive and transitive *)
  Axiom brel_refl : forall s, brel s s.
  Axiom brel_trans : forall s1 s2 s3, brel s1 s2 -> brel s2 s3 -> brel s1 s3.
End RTL_STATE_REL.

Module Type RTL_PROP.
  (* A property about RTL compuation *)
  Parameter rtl_prop : forall (A:Type), RTL A -> Prop.
  
  Axiom bind_sat_prop : forall (A B:Type) (c1:RTL A) (f:A -> RTL B), 
    rtl_prop _ c1 -> (forall a:A, rtl_prop _ (f a))
      -> rtl_prop _ (Bind _ c1 f).
  Axiom ret_sat_prop : forall (A:Type) (a:A), rtl_prop _ (Return a).
End RTL_PROP.

Module RTL_Prop (R:RTL_STATE_REL) <: RTL_PROP.

  (* Lift the relation to a property on a RTL computation *)
  Definition rtl_prop (A:Type) (c:RTL A) := 
    forall s s' v', c s = (Okay_ans v', s') -> R.brel s s'.
  Implicit Arguments rtl_prop [A].

  (* To prove "Bind _ c1 f" satisfies a RTL-computation property, it is
     sufficient to show c1 satifies it, and f satifies it for any result
     of c1 *)
  Lemma bind_sat_prop : forall (A B:Type) (c1:RTL A) (f:A -> RTL B), 
    rtl_prop c1 -> (forall a:A, rtl_prop (f a))
      -> rtl_prop (Bind _ c1 f).
  Proof. unfold rtl_prop. intros.
    rtl_okay_break.
    apply R.brel_trans with (s2:= s0); eauto.
  Qed.

  Lemma ret_sat_prop : forall (A:Type) (a:A), rtl_prop (Return a).
  Proof. unfold rtl_prop. intros. inversion H; subst.
    apply R.brel_refl.
  Qed.

  Lemma fail_sat_prop : forall (A:Type), rtl_prop (Fail A).
  Proof. unfold rtl_prop. intros. inversion H. Qed.

  Lemma safe_fail_sat_prop : forall (A:Type), rtl_prop (SafeFail A).
  Proof. unfold rtl_prop. intros. inversion H. Qed.

End RTL_Prop.  

Module Conv_Prop (RP: RTL_PROP).
  Import RP.
  Implicit Arguments rtl_prop [A].

  (* Lift a property about a RTL computation to a property about conversion from
   an x86 instruction to a list of RTL instructions. It says that
   if the computation for the input RTL-instruction list satifies the
   property, and after conversion the output RTL-instruction list also
   satisifies the property *)
  Definition conv_prop (A:Type) (cv:Conv A) := 
    forall cs (v:A) cs',
      cv cs = (v, cs')
        -> rtl_prop (RTL_step_list (List.rev (c_rev_i cs)))
        -> rtl_prop (RTL_step_list (List.rev (c_rev_i cs'))).
  Implicit Arguments conv_prop [A].

  Lemma conv_to_rtl_prop: forall cv,
    conv_prop cv -> rtl_prop (RTL_step_list (runConv cv)).
  Proof. unfold conv_prop, runConv. intros.
    remember_rev (cv {|c_rev_i := nil; c_next:=0|}) as cva.
    destruct cva.
    apply H in Hcva. prover. 
      compute [c_rev_i rev RTL_step_list]. apply ret_sat_prop.
  Qed.

  Lemma bind_sat_conv_prop : forall (A B:Type) (cv: Conv A) (f:A -> Conv B),
    conv_prop cv -> (forall a:A, conv_prop (f a)) -> conv_prop (Bind _ cv f).
  Proof. unfold conv_prop. intros.
    conv_break. eauto.
  Qed.

  Lemma ret_sat_conv_prop : forall (A:Type) (r:A), 
    conv_prop (ret r).
  Proof. unfold conv_prop. intros. prover. Qed.

  Lemma emit_sat_conv_prop : forall i,
    rtl_prop (interp_rtl i) -> conv_prop (emit i).
  Proof. unfold conv_prop, EMIT. intros.
    prover. autorewrite with step_list_db.
    apply bind_sat_prop. assumption.
      intros. apply bind_sat_prop. assumption.
      intros. apply ret_sat_prop.
  Qed.

  Lemma fresh_sat_conv_prop : 
    forall (s:nat) (almost_i: pseudo_reg s -> rtl_instr),
      (forall r, rtl_prop (interp_rtl (almost_i r)))
        -> conv_prop (fresh almost_i).
  Proof. unfold conv_prop, fresh. intros.
    prover. autorewrite with step_list_db. 
    apply bind_sat_prop. assumption.
      intros. apply bind_sat_prop. apply H.
      intros. apply ret_sat_prop.
  Qed.

End Conv_Prop.  

Ltac conv_backward :=
  match goal with
    | [H: ?cv ?cs = (_, ?cs'),
       H1: RTL_step_list (rev (c_rev_i ?cs')) ?s = (Okay_ans _, ?s') 
       |- _]
      => inv H; simpl in H1; autorewrite with step_list_db in H1;
         repeat rtl_okay_break
  end.
  
(** * Lemmas about that instructions that preserve the state *)

Module Same_RTL_State_Rel <: RTL_STATE_REL.
  Definition brel (s1 s2 : rtl_state) := s1 = s2.

  Lemma brel_refl : forall s, brel s s.
  Proof. unfold brel. trivial. Qed.

  Lemma brel_trans : forall s1 s2 s3, brel s1 s2 -> brel s2 s3 -> brel s1 s3.
  Proof. unfold brel. prover. Qed.
End Same_RTL_State_Rel.

Module Same_RTL_State := RTL_Prop Same_RTL_State_Rel.
Notation same_rtl_state := Same_RTL_State.rtl_prop.

(* rtl_prop_unfold_db is an unfold database when we develop lemmas about 
   RTL instructions *)
Hint Unfold same_rtl_state Same_RTL_State_Rel.brel : rtl_prop_unfold_db.

Hint Immediate Same_RTL_State.ret_sat_prop : same_rtl_state_db.
Hint Immediate Same_RTL_State.fail_sat_prop : same_rtl_state_db.
Hint Immediate Same_RTL_State.safe_fail_sat_prop : same_rtl_state_db.

(* the ordering of matches is important for the following tactic *)
Ltac same_rtl_state_tac := 
  repeat (match goal with
            | [|- same_rtl_state (Bind _ _ _)] => 
              apply Same_RTL_State.bind_sat_prop; [idtac | intros]
            | [|- same_rtl_state ?c] => extended_destruct_head c
            | [|- same_rtl_state _] => auto with same_rtl_state_db
          end).

(** * Lemmas about that instructions that preserve the machine state,
   which is the set of registers in x86 *)
Module Same_Mach_State_Rel <: RTL_STATE_REL.
  Definition brel (s1 s2 : rtl_state) := 
    rtl_mach_state s1 = rtl_mach_state s2.

  Lemma brel_refl : forall s, brel s s.
  Proof. unfold brel. trivial. Qed.

  Lemma brel_trans : forall s1 s2 s3, brel s1 s2 -> brel s2 s3 -> brel s1 s3.
  Proof. unfold brel. prover. Qed.
End Same_Mach_State_Rel.

Module Same_Mach_State := RTL_Prop Same_Mach_State_Rel.
Notation same_mach_state := Same_Mach_State.rtl_prop.

Hint Unfold same_mach_state Same_Mach_State_Rel.brel : rtl_prop_unfold_db.

Ltac same_mach_state_tac := 
  compute [interp_rtl]; fold interp_rtl;
  repeat (match goal with
            | [|- same_mach_state (Bind _ _ _)] => 
              apply Same_Mach_State.bind_sat_prop; [idtac | intros]
            | [|- same_mach_state ?c] => extended_destruct_head c
            | [|- same_mach_state _] => auto with same_mach_state_db
          end).

Hint Immediate Same_Mach_State.ret_sat_prop : same_mach_state_db.
Hint Immediate Same_Mach_State.fail_sat_prop : same_mach_state_db.
Hint Immediate Same_Mach_State.safe_fail_sat_prop : same_mach_state_db.

Lemma same_rtl_state_same_mach_state : forall (A:Type) (c:RTL A), 
  same_rtl_state c -> same_mach_state c.
Proof. unfold same_mach_state, Same_Mach_State_Rel.brel.
  unfold same_rtl_state, Same_RTL_State_Rel.brel.
  intros. apply H in H0. subst s'. 
  trivial.
Qed.

Local Ltac rtl_prover := 
  autounfold with rtl_prop_unfold_db ; simpl; 
  unfold flush_env, set_ps, get_ps, set_byte, get_byte, set_loc, get_loc, 
    choose_bits;
  prover.

Lemma flush_env_same_mach_state : same_mach_state flush_env.
Proof. rtl_prover. Qed.

Lemma set_ps_same_mach_state : forall s (r:pseudo_reg s) v,
  same_mach_state (set_ps r v).
Proof. rtl_prover. Qed.

Lemma set_byte_same_mach_state : forall addr v,
  same_mach_state (set_byte addr v).
Proof. rtl_prover. Qed.

Lemma get_ps_same_mach_state : forall s (r:pseudo_reg s),
  same_mach_state (get_ps r).
Proof. rtl_prover. Qed.

Lemma get_loc_same_mach_state : forall s (l:location s),
  same_mach_state (get_loc l).
Proof. rtl_prover. Qed.

Lemma get_byte_same_mach_state : forall addr,
  same_mach_state (get_byte addr).
Proof. rtl_prover. Qed.

Lemma choose_bits_same_mach_state : forall s, 
  same_mach_state (choose_bits s).
Proof. rtl_prover. Qed.

Hint Extern 0 (same_mach_state flush_env)
  => apply flush_env_same_mach_state : same_mach_state_db.
Hint Immediate set_ps_same_mach_state
  set_byte_same_mach_state get_ps_same_mach_state get_loc_same_mach_state
  get_byte_same_mach_state choose_bits_same_mach_state
  : same_mach_state_db.

(** * Lemmas about when a machine computation does not change seg registers *)

Module Same_Seg_Regs_Rel <: RTL_STATE_REL.
  Definition brel (s1 s2 : rtl_state) := 
    seg_regs_starts (rtl_mach_state s1) = seg_regs_starts (rtl_mach_state s2) /\
    seg_regs_limits (rtl_mach_state s1) = seg_regs_limits (rtl_mach_state s2).
  
  Lemma brel_refl : forall s, brel s s.
  Proof. unfold brel; intros. tauto. Qed.

  Lemma brel_trans : forall s1 s2 s3, brel s1 s2 -> brel s2 s3 -> brel s1 s3.
  Proof. unfold brel. prover. Qed.
End Same_Seg_Regs_Rel.

Module Same_Seg_Regs := RTL_Prop Same_Seg_Regs_Rel.
Notation same_seg_regs := Same_Seg_Regs.rtl_prop.

Hint Unfold same_seg_regs Same_Seg_Regs_Rel.brel : rtl_prop_unfold_db.

Ltac same_seg_regs_one_tac := 
  match goal with
    | [|- same_seg_regs (Bind _ _ _)] => 
      apply Same_Seg_Regs.bind_sat_prop; [idtac | intros]
    | [|- same_seg_regs ?c] => extended_destruct_head c
    | [|- same_seg_regs _] => auto with same_seg_regs_db
  end.

Ltac same_seg_regs_tac := 
  compute [interp_rtl]; fold interp_rtl;
  repeat same_seg_regs_one_tac.

Hint Immediate Same_Seg_Regs.ret_sat_prop : same_seg_regs_db.
Hint Immediate Same_Seg_Regs.fail_sat_prop : same_seg_regs_db.
Hint Immediate Same_Seg_Regs.safe_fail_sat_prop : same_seg_regs_db.

Lemma same_mach_state_same_seg_regs : forall (A:Type) (c:RTL A), 
  same_mach_state c -> same_seg_regs c.
Proof. autounfold with rtl_prop_unfold_db.
  intros.  generalize (H s s' v'). prover.
Qed.

(* Try same_mach_state_db *)
Hint Extern 2 (same_seg_regs _) =>
  apply same_mach_state_same_seg_regs; auto with same_mach_state_db
  : same_seg_regs_db.

Lemma same_rtl_state_same_seg_regs : forall (A:Type) (c:RTL A), 
  same_rtl_state c -> same_seg_regs c.
Proof. autounfold with rtl_prop_unfold_db.
  intros. apply H in H0. subst s'.  prover.
Qed.

(* Try same_rtl_state_db *)
Hint Extern 2 (same_seg_regs _) =>
  apply same_rtl_state_same_seg_regs; auto with same_rtl_state_db
  : same_seg_regs_db.


Definition is_seg_reg_loc (s:nat) (l:loc s) :=
  match l with
    | seg_reg_start_loc seg => true
    | seg_reg_limit_loc seg => true
    | _ => false
  end.

Lemma set_loc_same_seg_regs : forall s (l:location s) v,
  is_seg_reg_loc _ l = false -> same_seg_regs (set_loc l v).
Proof. autounfold with rtl_prop_unfold_db.  unfold set_loc. intros. 
  inversion_clear H0. simpl.
  destruct l; prover.
Qed.  

Hint Resolve set_loc_same_seg_regs : same_seg_regs_db.

(** * Lemmas about when a machine computation does not change the pc reg *)

Module Same_PC_Rel <: RTL_STATE_REL.
  Definition brel (s1 s2 : rtl_state) := 
    pc_reg (rtl_mach_state s1) = pc_reg (rtl_mach_state s2).

  Lemma brel_refl : forall s, brel s s.
  Proof. unfold brel; intros. tauto. Qed.

  Lemma brel_trans : forall s1 s2 s3, brel s1 s2 -> brel s2 s3 -> brel s1 s3.
  Proof. unfold brel. prover. Qed.
End Same_PC_Rel.

Module Same_PC := RTL_Prop Same_PC_Rel.
Notation same_pc := Same_PC.rtl_prop.

Hint Unfold same_pc Same_PC_Rel.brel : rtl_prop_unfold_db.

Ltac same_pc_tac := 
  compute [interp_rtl]; fold interp_rtl;
  repeat (match goal with
            | [|- same_pc (Bind _ _ _)] => 
              apply Same_PC.bind_sat_prop; [idtac | intros]
            | [|- same_pc ?c] => extended_destruct_head c
            | [|- same_pc _] => auto with same_pc_db
          end).

Hint Immediate Same_PC.ret_sat_prop : same_pc_db.
Hint Immediate Same_PC.fail_sat_prop : same_pc_db.
Hint Immediate Same_PC.safe_fail_sat_prop : same_pc_db.

Lemma same_mach_state_same_pc : forall (A:Type) (c:RTL A), 
  same_mach_state c -> same_pc c.
Proof. autounfold with rtl_prop_unfold_db.
  intros.  generalize (H s s' v'). prover.
Qed.

(* Try same_mach_state_db *)
Hint Extern 2 (same_pc _) =>
  apply same_mach_state_same_pc; auto with same_mach_state_db
  : same_pc_db.

Definition is_pc_loc (s:nat) (l:loc s) :=
  match l with
    | pc_loc => true
    | _ => false
  end.

Lemma set_loc_same_pc : forall s (l:location s) v,
  is_pc_loc _ l = false -> same_pc (set_loc l v).
Proof. autounfold with rtl_prop_unfold_db.  unfold set_loc. intros. 
  inversion_clear H0. simpl.
  destruct l; prover.
Qed.  

Hint Resolve set_loc_same_pc : same_pc_db.

(** * Lemmas about when a machine computation preserves the memory *)
Module Same_Mem_Rel <: RTL_STATE_REL.
  Definition brel (s1 s2 : rtl_state) := rtl_memory s1 = rtl_memory s2.

  Lemma brel_refl : forall s, brel s s.
  Proof. unfold brel; intros. tauto. Qed.

  Lemma brel_trans : forall s1 s2 s3, brel s1 s2 -> brel s2 s3 -> brel s1 s3.
  Proof. unfold brel. prover. Qed.
End Same_Mem_Rel.

Module Same_Mem := RTL_Prop Same_Mem_Rel.
Notation same_mem := Same_Mem.rtl_prop.

Hint Unfold same_mem Same_Mem_Rel.brel : rtl_prop_unfold_db.

Ltac same_mem_tac := 
  compute [interp_rtl]; fold interp_rtl;
  repeat (match goal with
            | [|- same_mem (Bind _ _ _)] => 
              apply Same_Mem.bind_sat_prop; [idtac | intros]
            | [|- same_mem ?c] => extended_destruct_head c
            | [|- same_mem _] => auto with same_mem_db
          end).

Lemma same_rtl_state_same_mem : forall (A:Type) (c:RTL A), 
  same_rtl_state c -> same_mem c.
Proof. autounfold with rtl_prop_unfold_db.
  intros. apply H in H0. subst s'. trivial. 
Qed.

(* Try same_rtl_state_db *)
Hint Extern 2 (same_mem _) =>
  apply same_rtl_state_same_mem; auto with same_rtl_state_db
  : same_mem_db.

Lemma flush_env_same_mem : same_mem flush_env.
Proof. rtl_prover. Qed.

Lemma set_ps_same_mem : forall s (r:pseudo_reg s) v,
  same_mem (set_ps r v).
Proof. rtl_prover. Qed.

Lemma get_ps_same_mem : forall s (r:pseudo_reg s),
  same_mem (get_ps r).
Proof. rtl_prover. Qed.

Lemma get_loc_same_mem : forall s (l:location s),
  same_mem (get_loc l).
Proof. rtl_prover. Qed.

Lemma set_loc_same_mem : forall s (l:location s) v,
  same_mem (set_loc l v).
Proof. rtl_prover. Qed.

Lemma get_byte_same_mem : forall addr,
  same_mem (get_byte addr).
Proof. rtl_prover. Qed.

Lemma choose_bits_same_mem : forall s, 
  same_mem (choose_bits s).
Proof. rtl_prover. Qed.


Hint Extern 0 (same_mem flush_env)
  => apply flush_env_same_mem : same_mem_db.
Hint Immediate set_ps_same_mem
  get_ps_same_mem get_loc_same_mem set_loc_same_mem
  get_byte_same_mem choose_bits_same_mem
  : same_mem_db.

(** * Lemmas about agree_over and agree_outside *)
Definition agree_over_addr_region (r:Int32Ensemble) (s s':rtl_state) : Prop :=
  forall l:int32, Ensembles.In _ r l -> 
     AddrMap.get l (rtl_memory s) = AddrMap.get l (rtl_memory s').

Definition agree_outside_addr_region (r:Int32Ensemble) (s s':rtl_state) :=
  forall l:int32, ~ (Ensembles.In _ r l) -> 
     AddrMap.get l (rtl_memory s) = AddrMap.get l (rtl_memory s').

Lemma agree_over_addr_region_e : forall r s s' l,
  agree_over_addr_region r s s' -> Ensembles.In _ r l
    -> AddrMap.get l (rtl_memory s) = AddrMap.get l (rtl_memory s').
Proof. prover. Qed.

Lemma agree_outsie_addr_region_e : forall r s s' l,
  agree_outside_addr_region r s s' -> ~ Ensembles.In _ r l
    -> AddrMap.get l (rtl_memory s) = AddrMap.get l (rtl_memory s').
Proof. prover. Qed.

Lemma agree_over_addr_region_refl : forall r s,
  agree_over_addr_region r s s.
Proof. prover. Qed.

Lemma agree_over_addr_region_trans : forall r s1 s2 s3,
  agree_over_addr_region r s1 s2 -> agree_over_addr_region r s2 s3
    -> agree_over_addr_region r s1 s3.
Proof. unfold agree_over_addr_region. intros.
  generalize (H l) (H0 l). prover.
Qed.

Lemma agree_over_outside : forall s1 s2 r r',
  Ensembles.Disjoint _ r r' -> agree_outside_addr_region r' s1 s2
    -> agree_over_addr_region r s1 s2.
Proof. unfold agree_outside_addr_region, agree_over_addr_region.
  intros.
  assert (~ Ensembles.In _ r' l).
    intro. destruct H. 
    cut (Ensembles.In _ (Ensembles.Intersection _ r r') l). (apply H).
    apply Ensembles.Intersection_intro; assumption.
  auto.
Qed.
  
Lemma agree_outside_addr_region_refl : forall s r,
  agree_outside_addr_region r s s.
Proof. prover. Qed.

Lemma agree_outside_addr_region_trans : forall s1 s2 s3 r,
  agree_outside_addr_region r s1 s2
    -> agree_outside_addr_region r s2 s3
    -> agree_outside_addr_region r s1 s3.
Proof. unfold agree_outside_addr_region. intros.
  generalize (H l) (H0 l). prover.
Qed.

Lemma same_mem_agree_outside : forall s s' r,
  rtl_memory s = rtl_memory s' -> agree_outside_addr_region r s s'.
Proof. intros. unfold agree_outside_addr_region. intros. congruence. Qed.


(** * Lemmas about when a machine computation preserves the memory region 
   outside of a segment. This property needs to be parametrized over the
   segment register. ML's module system, however, can only parametrize
   over modules. 
*)
Definition segAddrs (seg:segment_register) (s:rtl_state) : Int32Ensemble :=
  let m := rtl_mach_state s in
    addrRegion (seg_regs_starts m seg) (seg_regs_limits m seg).

(* Without the first two conditions, it would no be transitive *)
Definition agree_outside_seg (seg:segment_register) (A:Type) (c:RTL A) :=
  forall s s' v', c s = (Okay_ans v', s') -> 
    SegStart s seg = SegStart s' seg /\
    SegLimit s seg = SegLimit s' seg /\
    agree_outside_addr_region (segAddrs seg s) s s'.
Implicit Arguments agree_outside_seg [A].

Lemma bind_agree_outside_seg :
  forall (seg:segment_register) (A B:Type) (c1:RTL A) (f: A -> RTL B),
    agree_outside_seg seg c1
      -> (forall a:A, agree_outside_seg seg (f a))
      -> agree_outside_seg seg (Bind _ c1 f).
Proof. unfold agree_outside_seg. intros.
  rtl_okay_break.
  apply H in H2. apply H0 in H1.
  assert (segAddrs seg s = segAddrs seg s0) as H10.
    unfold segAddrs. prover.
  rewrite H10 in *.
  split. prover. split. prover.
  eapply agree_outside_addr_region_trans with (s2:= s0); prover.
Qed.

Ltac agree_outside_seg_one_tac := 
  match goal with
    | [|- agree_outside_seg _ (Bind _ _ _)] => 
      apply bind_agree_outside_seg; [idtac | intros]
    | [|- agree_outside_seg _ ?c] => extended_destruct_head c
    | [|- agree_outside_seg _ _]
      => auto with agree_outside_seg_db
  end.

Ltac agree_outside_seg_tac := 
  compute [interp_rtl]; fold interp_rtl;
  repeat agree_outside_seg_one_tac.

Lemma same_mem_agree_outside_seg : forall seg (A:Type) (c:RTL A), 
  same_mem c -> same_seg_regs c -> agree_outside_seg seg c.
Proof. unfold same_mem, same_seg_regs, agree_outside_seg.
  unfold Same_Mem_Rel.brel, Same_Seg_Regs_Rel.brel.
  intros. generalize (H _ _ _ H1). generalize (H0 _ _ _ H1).
  prover.
Qed.

(* Try same_mem *)
Hint Extern 2 (agree_outside_seg _ _) =>
  apply same_mem_agree_outside_seg; 
    [auto with same_mem_db | auto with same_seg_regs_db]
    : agree_outside_seg_db.

(*
Lemma set_mem32_agree_outside_data_seg : forall a w,
  agree_outside_data_seg (set_mem32 a w).
Proof. unfold set_mem32, agree_outside_data_seg;  intros.
  mach_succ_elim.
  remember_destruct_head in H as Hin; try discriminate.
  mach_succ_elim.
  split. intros l Hnotin.
  assert (in_seg_bounds_rng DS a (repr 3) s = Succ (s, true)) as H4.
    rewrite in_seg_bounds_rng_equation. 
    rewrite HHin. trivial.
  assert (l <> add (seg_regs_starts s DS) a) as H6.
    rewrite <- (add32_zero_r a). rewrite <-Word.add_assoc.
    set_mem32_aux_tac1 Hnotin s.
  assert (l <> seg_regs_starts s DS +32 a +32_p 1) as H8.
    set_mem32_aux_tac1 Hnotin s.
  assert (l <> seg_regs_starts s DS +32 a +32_p 2) as H10.
    set_mem32_aux_tac1 Hnotin s.
  assert (l <> seg_regs_starts s DS +32 a +32_p 3) as H12.
    set_mem32_aux_tac1 Hnotin s.
  repeat (rtl_okay_break set_mem32_aux_tac2 || appHyps set_mem32_aux_tac2).
  trivial.
Qed.
Hint Resolve set_mem32_agree_outside_data_seg : agree_outside_data_seg_db.

Lemma set_addr32_agree_outside_data_seg : forall a w,
  agree_outside_data_seg (set_addr32 a w).
Proof. unfold set_addr32; intros. agree_outside_data_seg_tac. Qed.
Hint Resolve set_addr32_agree_outside_data_seg : agree_outside_data_seg_db.

Lemma set_op32_agree_outside_data_seg : forall op w,
  agree_outside_data_seg (set_op32 op w).
Proof. unfold set_op32; intros.
  destruct op; agree_outside_data_seg_tac. 
Qed.
Hint Resolve set_op32_agree_outside_data_seg : agree_outside_data_seg_db.

Lemma logical_op_agree_outside_data_seg : forall f w op1 op2,
  agree_outside_data_seg (step_logical_op f w op1 op2).
Proof. unfold step_logical_op; intros. agree_outside_data_seg_tac. Qed.

Lemma ADD_agree_outside_data_seg : forall w op1 op2,
  agree_outside_data_seg (step_ADD w op1 op2).
Proof. unfold step_ADD; intros. agree_outside_data_seg_tac. Qed.
*)

(** * Lemmas about same_regs *)
(*
Definition same_regs (A:Type) (c:Mach A) := 
  forall s s' v', c s = Succ (s', v') -> gp_regs s = gp_regs s'.
Implicit Arguments same_regs [A].

Lemma Bind_same_regs: forall (A B:Type) (c1:Mach A) (f:A -> Mach B), 
  same_regs c1 -> (forall a:A, same_regs (f a)) -> same_regs (Bind _ c1 f).
Proof. unfold same_regs. intros. 
  unfold Bind, Mach_monad in H1. 
  remember_rev (c1 s) as r.
  destruct r as [(s0,v) | |]; try discriminate.
  generalize (H s s0 v Hr) (H0 v s0 s' v' H1); intros.
  apply eq_trans with (y:= gp_regs s0); assumption.
Qed.

Lemma same_rtl_state_same_regs : forall (A:Type) (c:Mach A), 
  same_rtl_state c -> same_regs c.
Proof. unfold same_rtl_state, same_regs; intros. apply H in H0. subst s'. trivial.
Qed.

Ltac same_regs_prim_tac := 
  auto with same_regs_db ||
  (apply same_rtl_state_same_regs; auto with same_rtl_state_db; fail).

Ltac same_regs_bind_tac := 
  apply Bind_same_regs; [idtac | intros].

Ltac same_regs_tac := 
  repeat (match goal with 
            | [|- same_regs ?c] => 
              destruct_tac c same_regs_bind_tac same_regs_prim_tac
          end).

Lemma set_pc_same_regs : forall pc, same_regs (set_pc pc).
Proof. unfold set_pc, same_regs; intros; destruct s'; inv H; trivial. Qed.

Lemma set_mem_same_regs : forall a v, same_regs (set_mem a v).
Proof. unfold set_pc, same_regs; intros; destruct s'; inv H; trivial. Qed.

Lemma set_flag_same_regs : forall fl w, same_regs (set_flag fl w).
Proof. unfold set_flag, same_regs; intros; destruct s'; inv H; trivial. Qed.

Lemma set_oracle_same_regs : forall w, same_regs (set_oracle w).
Proof. unfold set_oracle, same_regs; intros; destruct s'; inv H; trivial. Qed.

Hint Resolve set_pc_same_regs set_mem_same_regs set_flag_same_regs
  set_oracle_same_regs : same_regs_db.

Lemma set_mem32_same_regs : forall a w, same_regs (set_mem32 a w).
Proof. unfold set_mem32; intros. same_regs_tac. Qed.
Hint Resolve set_mem32_same_regs : same_regs_db.

Lemma set_addr32_same_regs : forall a v, same_regs (set_addr32 a v).
Proof. unfold set_addr32; intros. same_regs_tac. Qed.

Lemma next_oracle_bit_same_regs: same_regs next_oracle_bit.
Proof. unfold next_oracle_bit; intros. same_regs_tac. Qed.

Hint Resolve set_addr32_same_regs next_oracle_bit_same_regs : same_regs_db.
*)

(** * Lemmas about same_regs_but *)

(** r is not the same as op *)
Definition reg_eq_operand (r:register) (op:operand) : bool := 
  match op with
    | Reg_op r' => register_eq_dec r' r
    | _ => false
  end.

(** s and s' have the same register values except for the possible 
    register in op *)
(*
Definition state_same_regs_but (s:mach_state) (s':mach_state)
  (op:operand) : Prop := 
  forall r:register, reg_eq_operand r op = false -> gp_regs s r = gp_regs s' r.

Lemma state_same_regs_but_refl : forall s op, state_same_regs_but s s op.
Proof. unfold state_same_regs_but; intros. trivial. Qed.

Lemma state_same_regs_but_trans : forall s1 s2 s3 op, 
  state_same_regs_but s1 s2 op -> state_same_regs_but s2 s3 op
    -> state_same_regs_but s1 s3 op.
Proof. unfold state_same_regs_but; intros. eauto using eq_trans. Qed.

Definition same_regs_but (A:Type) (op:operand) (c:Mach A) := 
  forall s s' v', c s = Succ (s', v') -> state_same_regs_but s s' op.
Implicit Arguments same_regs_but [A].


Lemma Bind_same_regs_but: forall (A B:Type) (op:operand)
  (c1:Mach A) (f:A -> Mach B), 
  same_regs_but op c1 -> (forall a:A, same_regs_but op (f a))
    -> same_regs_but op (Bind _ c1 f).
Proof. unfold same_regs_but. intros. 
  unfold Bind, Mach_monad in H1. 
  remember_rev (c1 s) as r.
  destruct r as [(s0,v) | |]; try discriminate.
  generalize (H s s0 v Hr) (H0 v s0 s' v' H1); intros.
  eauto using state_same_regs_but_trans.
Qed.

Lemma same_rtl_state_same_regs_but : forall (A:Type) (op:operand) (c:Mach A), 
  same_rtl_state c -> same_regs_but op c.
Proof. unfold same_rtl_state, same_regs_but; intros. apply H in H0. subst s'. 
  apply state_same_regs_but_refl.
Qed.

Lemma same_regs_same_regs_but : forall (A:Type) (op:operand) (c:Mach A),
  same_regs c -> same_regs_but op c.
Proof. unfold same_regs, same_regs_but, state_same_regs_but; intros.
  erewrite H by eassumption. trivial.
Qed.

Ltac same_regs_but_prim_tac := 
  auto with same_regs_but_db ||
  (* try same_rtl_state *)
  (apply same_rtl_state_same_regs_but; auto with same_rtl_state_db; fail) ||
  (* try same_regs *)
  (apply same_regs_same_regs_but; auto with same_regs_db; fail).

Ltac same_regs_but_bind_tac := 
  apply Bind_same_regs_but; [idtac | intros].

Ltac same_regs_but_tac := 
  repeat (match goal with 
            | [|- same_regs_but _ ?c] => 
              destruct_tac c same_regs_but_bind_tac same_regs_but_prim_tac
          end).

Lemma set_reg_same_regs_but : forall r v, 
  same_regs_but (Reg_op r) (set_reg r v).
Proof. unfold set_reg, same_regs_but, state_same_regs_but; intros.
  unfold reg_eq_operand in H0.
  destruct register_eq_dec; try discriminate.
  destruct s'. inv H. simpl.
  unfold update, X86Semantics.eq_dec.
  destruct EqDec_register.
  destruct (eq_dec0 r r0); try congruence.
Qed.

Lemma set_op32_same_regs_but : forall op v, same_regs_but op (set_op32 op v).
Proof. unfold set_op32, same_regs_but, state_same_regs_but; intros.
  destruct op; try discriminate.
    apply set_reg_same_regs_but in H. auto.
    erewrite (set_addr32_same_regs). trivial. eassumption.
Qed.

Hint Resolve set_reg_same_regs_but set_op32_same_regs_but : same_regs_but_db.

Lemma ADD_same_regs_but : forall w op1 op2, 
  same_regs_but op1 (step_ADD w op1 op2).
Proof. unfold step_ADD; intros. same_regs_but_tac. Qed.

Lemma logical_op_same_regs_but : forall f w op1 op2, 
  same_regs_but op1 (step_logical_op f w op1 op2).
Proof. unfold step_logical_op; intros. same_regs_but_tac. Qed.
*)


(** * Lemmas about no_fail *)

Definition no_fail (A:Type) (c:RTL A) := 
  forall s s', c s <> (Fail_ans _, s').
Implicit Arguments no_fail [A].

Lemma bind_no_fail: forall (A B:Type) (c1:RTL A) (f:A -> RTL B), 
  no_fail c1 -> (forall a:A, no_fail (f a)) -> no_fail (Bind _ c1 f).
Proof. unfold no_fail. intros. intro Hc.
  apply rtl_bind_fail_elim in Hc. 
  destruct Hc. contradict H1. apply H. 
  destruct H1 as [s1' [v' [H2 H4]]]. contradict H4. apply H0.
Qed.

Ltac no_fail_one_tac := 
    match goal with
      | [|- no_fail (Bind _ _ _)] => 
        apply bind_no_fail; [idtac | intros]
      | [|- no_fail ?c] => extended_destruct_head c
      | [|- no_fail _] => auto with no_fail_db
    end.

Ltac no_fail_tac := 
  compute [interp_rtl]; fold interp_rtl;
  repeat no_fail_one_tac.

Lemma ret_no_fail : forall (A:Type) (a:A), no_fail (Return a).
Proof. discriminate. Qed.

Lemma safefail_no_fail : forall (A:Type), no_fail (SafeFail A).
Proof. discriminate. Qed.

Hint Resolve ret_no_fail safefail_no_fail : no_fail_db.

Lemma flush_env_no_fail : no_fail flush_env.
Proof. rtl_prover. Qed.

Lemma get_ps_no_fail : forall s (r:pseudo_reg s),
  no_fail (get_ps r).
Proof. rtl_prover. Qed.

Lemma set_ps_no_fail : forall s (r:pseudo_reg s) v,
  no_fail (set_ps r v).
Proof. rtl_prover. Qed.

Lemma get_byte_no_fail : forall addr,
  no_fail (get_byte addr).
Proof. rtl_prover. Qed.

Lemma set_byte_no_fail : forall addr v,
  no_fail (set_byte addr v).
Proof. rtl_prover. Qed.

Lemma get_loc_no_fail : forall s (l:location s),
  no_fail (get_loc l).
Proof. rtl_prover. Qed.

Lemma set_loc_no_fail : forall s (l:location s) v,
  no_fail (set_loc l v).
Proof. rtl_prover. Qed.

Lemma choose_bits_no_fail : forall s, 
  no_fail (choose_bits s).
Proof. rtl_prover. Qed.

Hint Extern 0 (no_fail flush_env) => apply flush_env_no_fail : no_fail_db.
Hint Immediate set_ps_no_fail set_byte_no_fail get_ps_no_fail 
  get_loc_no_fail set_loc_no_fail
  get_byte_no_fail choose_bits_no_fail
  : no_fail_db.

(** * Lemmas about inBoundCodeAddr *)

Definition inBoundCodeAddr (pc:int32) (s:rtl_state) := 
  pc <=32 CLimit s.

Lemma step_fail_pc_inBound : forall s s',
  step s = (Fail_ans unit, s') -> inBoundCodeAddr (PC s) s.
Proof. unfold step. intros.
  rtl_comp_elim_L1.
  do 2 rtl_comp_elim_L1.
  remember_destruct_head in H as irng.
    clear H. unfold inBoundCodeAddr. prover.
    discriminate.
Qed.

Lemma step_immed_pc_inBound : forall s s',
  s ==> s' -> inBoundCodeAddr (PC s) s.
Proof. unfold step_immed, step. intros.
  do 3 rtl_okay_elim.
  remember_destruct_head in H as irng.
    clear H.
    unfold inBoundCodeAddr. prover.
    discriminate.
Qed.

(*
Lemma inBoundCodeAddr_equiv : forall s s' pc,
  state_same_seg_regs s s' -> inBoundCodeAddr pc s -> inBoundCodeAddr pc s'.
Proof. unfold inBoundCodeAddr; intros. destruct H. congruence. Qed.
*)

(** * Lemmas about fetch_n *)
Lemma fetch_n_length : forall n pc s,
  length (fetch_n n pc s) = n.
Proof. induction n; prover. Qed.

Lemma fetch_n_sound : forall n pc s bytes k,
  fetch_n n pc s = bytes
    -> (0 <= k < n)%nat
    -> nth k bytes zero = (AddrMap.get (pc +32_n k) (rtl_memory s)).
Proof. induction n.
  Case "n=0". prover.
  Case "S n". intros.
    assert (k = 0 \/ k > 0)%nat as H10.
      generalize (le_lt_or_eq 0 k); prover.
    simpl in H; subst bytes.
    destruct H10.
    SCase "k=0". 
      subst k. rewrite add32_zero_r. prover.
    SCase "k>0".
      assert (0 <= k-1 < n)%nat by omega.
      rewrite cons_nth by assumption.
      erewrite IHn by trivial.
      unfold "+32". rewrite add_assoc. rewrite add_repr.
      assert (1 + Z_of_nat (k-1) = Z_of_nat k).
        rewrite inj_minus1 by omega. ring.
      prover.
Qed.    

(** * upd_get lemmas *)
(*
Lemma set_pc_pc_reg : forall s s' v' pc,
  set_pc pc s = Succ (s', v') -> pc_reg s' = pc.
Proof. intros. unfold set_pc in H. inv H. simpl. trivial. Qed.

Lemma set_reg_get_dest : forall s s' v v' r,
  set_reg r v s = Succ (s', v') -> gp_regs s' r = v.
Proof. unfold set_reg; intros. destruct s'; inv H. simpl.
  unfold update. unfold X86Semantics.eq_dec, EqDec_register.
  destruct (register_eq_dec r r); congruence.
Qed.
*)

(** * An unfolding database for proving properties of conversions *)

Hint Unfold load_Z load_int arith test load_reg set_reg cast_u cast_s
  get_seg_start get_seg_limit read_byte write_byte get_flag set_flag
  get_pc set_pc copy_ps : conv_unfold_db.

(** * The property that if a conversion returns a pseudo register, its
   index is less than the index of the current conversion state *)
Definition conv_index_increase (A:Type) (cv:Conv A) :=
  forall cs v' cs',
    cv cs = (v', cs') -> c_next cs < c_next cs'.
Implicit Arguments conv_index_increase [A].

Ltac conv_index_increase_tac := 
  autounfold with conv_unfold_db;
  repeat (match goal with
            | [|- conv_index_increase ?c] => extended_destruct_head c
            | [|- conv_index_increase _]
              => auto 10 with conv_index_increase_db
          end).

Lemma bind_conv_index_increase :
  forall s (A:Type) (c1:Conv A) (f: A -> Conv (pseudo_reg s)),
    conv_index_increase c1
      -> (forall a:A, conv_index_increase (f a))
      -> conv_index_increase (Bind _ c1 f).
Proof. unfold conv_index_increase. intros.
  conv_break. eapply H in H2. eapply H0 in H1. omega.
Qed.
Hint Extern 1 (conv_index_increase (Bind _ ?c1 ?f)) =>
  apply (bind_conv_index_increase _ _ c1 f); [idtac | intros]
    : conv_index_increase_db.

Lemma fresh_conv_index_increase : 
  forall s (almost_i: pseudo_reg s -> rtl_instr),
    conv_index_increase (fresh almost_i).
Proof. unfold conv_index_increase, fresh. prover. Qed.
Hint Immediate fresh_conv_index_increase : conv_index_increase_db.

Lemma compute_parity_aux_index_increase : forall n s (op1:pseudo_reg s) op2,
  conv_index_increase (compute_parity_aux op1 op2 n).
Proof. induction n; intros.
  simpl. conv_index_increase_tac.
  unfold compute_parity_aux. fold (@compute_parity_aux s).
  conv_index_increase_tac.
Qed.

Definition conv_index_monotone s (cv:Conv (pseudo_reg s)) :=
  forall cs idx cs',
    cv cs = (ps_reg s idx, cs') -> idx < c_next cs'.
Implicit Arguments conv_index_monotone [s].

Ltac conv_index_monotone_tac := 
  autounfold with conv_unfold_db;
  repeat (match goal with
            | [|- conv_index_monotone ?c] => extended_destruct_head c
            | [|- conv_index_monotone _]
              => auto 10 with conv_index_monotone_db
          end).

Lemma bind_conv_index_monotone_1 :
  forall s (A:Type) (c1:Conv A) (f: A -> Conv (pseudo_reg s)),
    (forall a:A, conv_index_monotone (f a))
      -> conv_index_monotone (Bind _ c1 f).
Proof. unfold conv_index_monotone. intros.
  conv_break. eauto.
Qed.
Hint Extern 1 (conv_index_monotone (Bind _ ?c1 ?f)) =>
  apply (bind_conv_index_monotone_1 _ _ c1 f); intros
    : conv_index_monotone_db.

Lemma fresh_conv_index_monotone : 
  forall s (almost_i: pseudo_reg s -> rtl_instr),
    conv_index_monotone (fresh almost_i).
Proof. unfold conv_index_monotone, fresh. prover. Qed.
Hint Immediate fresh_conv_index_monotone : conv_index_monotone_db.

Lemma fresh_pr_monotone : forall s (almost_i:pseudo_reg s -> rtl_instr) cs v' cs',
  fresh almost_i cs = (v', cs') -> c_next cs < c_next cs'.
Proof. unfold fresh. intros. prover. Qed.

(** * Lemmas about a conversion preserves the property of same_seg_regs *)

Module Conv_Same_Seg_Regs := Conv_Prop (Same_Seg_Regs).
Notation conv_same_seg_regs := Conv_Same_Seg_Regs.conv_prop.

Hint Extern 1 (conv_same_seg_regs (emit _)) => 
  apply Conv_Same_Seg_Regs.emit_sat_conv_prop; same_seg_regs_tac : conv_same_seg_regs_db.

Hint Extern 1 (conv_same_seg_regs (fresh _)) => 
  apply Conv_Same_Seg_Regs.fresh_sat_conv_prop; intros; same_seg_regs_tac :
  conv_same_seg_regs_db.

Hint Resolve Conv_Same_Seg_Regs.ret_sat_conv_prop 
  : conv_same_seg_regs_db.

Ltac conv_same_seg_regs_tac := 
  repeat autounfold with conv_unfold_db;
  repeat (match goal with
            | [|- conv_same_seg_regs (Bind _ _ _)] => 
              apply Conv_Same_Seg_Regs.bind_sat_conv_prop; [idtac | intros]
            | [|- conv_same_seg_regs ?c] => extended_destruct_head c
            | [|- conv_same_seg_regs _] => auto with conv_same_seg_regs_db
          end).

(** ** Lemmas for many conversion primitives can be proved by simply unfolding
   their definitions and use the above conv_same_seg_regs_tac. However, there
   are two cases when we want to state a separate lemma about a conversion
   primitive and check the lemma into the hint databse:
   (1) Some lemmas need manual intervention to prove, for example, 
       induction-based proofs.
   (2) If a primitive is used quite often in definitions, it is good to
       state a separate lemma for it; after it is declared in the hint db, 
       it provides a shortcut in the proof search;
       for instance, lemmas about iload_op8, iload_op16, iload_32 and load_op
       are added for this reason. Those could be proved by just unfolding them. 
       But in conv_DIV for example, if we did that, the amount of time to prove
       conv_same_seg_regs (conv_DIV ...) would be an order of magnitiude more.
 *)

Lemma load_mem_n_same_seg_regs : forall seg addr n,
  conv_same_seg_regs (load_mem_n seg addr n).
Proof. unfold load_mem_n, lmem, add_and_check_segment.
  induction n. 
    conv_same_seg_regs_tac.
    fold load_mem_n in *. conv_same_seg_regs_tac.
Qed.

Hint Extern 1 (conv_same_seg_regs (load_mem_n _ _ ?X))
  =>  apply load_mem_n_same_seg_regs with (n:=X)
  : conv_same_seg_regs_db.

Lemma set_mem_n_same_seg_regs : forall n seg (v:pseudo_reg (8*(n+1)-1)) addr,
  conv_same_seg_regs (set_mem_n seg v addr).
Proof. unfold set_mem_n, smem, add_and_check_segment.
  induction n; intros. 
    conv_same_seg_regs_tac.
    fold (@set_mem_n n) in *. conv_same_seg_regs_tac.
Qed.

Hint Immediate set_mem_n_same_seg_regs : conv_same_seg_regs_db.

Lemma iload_op8_same_seg_regs : forall seg op,
  conv_same_seg_regs (iload_op8 seg op).
Proof. unfold iload_op8, load_mem8, compute_addr. intros. 
  conv_same_seg_regs_tac.
Qed.  

Lemma iload_op16_same_seg_regs : forall seg op,
  conv_same_seg_regs (iload_op16 seg op).
Proof. unfold iload_op16, load_mem16, compute_addr. intros. 
  conv_same_seg_regs_tac.
Qed.  

Lemma iload_op32_same_seg_regs : forall seg op,
  conv_same_seg_regs (iload_op32 seg op).
Proof. unfold iload_op32, load_mem32, compute_addr. intros. 
  conv_same_seg_regs_tac.
Qed.  

Hint Immediate iload_op8_same_seg_regs iload_op16_same_seg_regs
  iload_op32_same_seg_regs : conv_same_seg_regs_db.

Lemma load_op_same_seg_regs : forall p w rseg op,
  conv_same_seg_regs (load_op p w rseg op).
Proof. unfold load_op. intros. conv_same_seg_regs_tac. Qed.

Hint Immediate load_op_same_seg_regs : conv_same_seg_regs_db.

Lemma set_reg_same_seg_regs : forall p r,
  conv_same_seg_regs (set_reg p r).
Proof. unfold set_reg. intros. apply Conv_Same_Seg_Regs.emit_sat_conv_prop.
  unfold same_seg_regs, Same_Seg_Regs_Rel.brel. simpl. unfold set_loc. intros.
  prover.
Qed.

Hint Immediate set_reg_same_seg_regs : conv_same_seg_regs_db.

Lemma set_op_same_seg_regs : forall p w seg r op,
  conv_same_seg_regs (set_op p w seg r op).
Proof. unfold set_op, iset_op32, iset_op16, iset_op8.
  unfold set_mem32, set_mem16, set_mem8, compute_addr. intros.
  destruct (op_override p); destruct w;
  conv_same_seg_regs_tac.
Qed.

Hint Immediate set_op_same_seg_regs : conv_same_seg_regs_db.

Lemma conv_BS_aux_same_seg_regs : forall s d n (op:pseudo_reg s),
  conv_same_seg_regs (conv_BS_aux d n op).
Proof. unfold conv_BS_aux.  
  induction n; intros; conv_same_seg_regs_tac.
Qed.

Lemma compute_parity_aux_same_seg_regs : forall s (op1:pseudo_reg s) op2 n,
  conv_same_seg_regs (compute_parity_aux op1 op2 n).
Proof. induction n. simpl. conv_same_seg_regs_tac.
  unfold compute_parity_aux. fold (@compute_parity_aux s).
  conv_same_seg_regs_tac.
Qed.

Hint Immediate conv_BS_aux_same_seg_regs compute_parity_aux_same_seg_regs :
  conv_same_seg_regs_db.

(** * Lemmas about a conversion preserves the property of same_mem *)
(* this property does not seem useful. remove it? *)

Module Conv_Same_Mem := Conv_Prop (Same_Mem).
Notation conv_same_mem := Conv_Same_Mem.conv_prop.

Ltac conv_same_mem_tac := 
  repeat autounfold with conv_unfold_db;
  repeat (match goal with
            | [|- conv_same_mem (Bind _ _ _)] => 
              apply Conv_Same_Mem.bind_sat_conv_prop; [idtac | intros]
            | [|- conv_same_mem ?c] => extended_destruct_head c
            | [|- conv_same_mem _] => auto with conv_same_mem_db
          end).

Hint Extern 1 (conv_same_mem (emit _)) => 
  apply Conv_Same_Mem.emit_sat_conv_prop; same_mem_tac : conv_same_mem_db.

Hint Extern 1 (conv_same_mem (fresh _)) => 
  apply Conv_Same_Mem.fresh_sat_conv_prop; intros; same_mem_tac :
  conv_same_mem_db.

Hint Resolve Conv_Same_Mem.ret_sat_conv_prop 
  : conv_same_mem_db.

Lemma load_mem_n_same_mem : forall seg addr n,
  conv_same_mem (load_mem_n seg addr n).
Proof. unfold load_mem_n, lmem, add_and_check_segment.
  induction n.
    conv_same_mem_tac.
    fold load_mem_n in *. conv_same_mem_tac.
Qed.

Hint Extern 1 (conv_same_mem (load_mem_n _ _ ?X))
  =>  apply load_mem_n_same_mem with (n:=X) : conv_same_mem_db.

Lemma iload_op32_same_mem : forall seg op,
  conv_same_mem (iload_op32 seg op).
Proof. unfold iload_op32, load_mem32, compute_addr. intros. 
  conv_same_mem_tac.
Qed.  

Hint Immediate iload_op32_same_mem : conv_same_mem_db.

(** * Lemmas about a conversion preserves the property of
   agree_outside_data_seg *)
Definition conv_agree_outside_seg (seg:segment_register) (A:Type) (cv:Conv A) :=
  forall cs (v:A) cs',
    cv cs = (v, cs')
      -> agree_outside_seg seg (RTL_step_list (List.rev (c_rev_i cs)))
      -> agree_outside_seg seg (RTL_step_list (List.rev (c_rev_i cs'))).
Implicit Arguments conv_agree_outside_seg [A].

Lemma conv_agree_outside_seg_e : forall (A:Type) seg (cv:Conv A) cs v cs',
  cv cs = (v, cs')
    -> conv_agree_outside_seg seg cv
    -> agree_outside_seg seg (RTL_step_list (List.rev (c_rev_i cs)))
    -> agree_outside_seg seg (RTL_step_list (List.rev (c_rev_i cs'))).
Proof. unfold conv_agree_outside_seg. eauto. Qed.

Lemma conv_to_rtl_aos: forall seg cv,
  conv_agree_outside_seg seg cv
    -> agree_outside_seg seg (RTL_step_list (runConv cv)).
Proof. unfold conv_agree_outside_seg, runConv. intros.
  remember_rev (cv {| c_rev_i := nil; c_next := 0 |}) as cva.
  destruct cva.
  apply H in Hcva. prover. 
    compute [c_rev_i rev RTL_step_list].
    agree_outside_seg_tac.
Qed.

Lemma bind_conv_aos : forall seg (A B:Type) (cv: Conv A) (f:A -> Conv B),
  conv_agree_outside_seg seg cv
    -> (forall a:A, conv_agree_outside_seg seg (f a))
    -> conv_agree_outside_seg seg (Bind _ cv f).
Proof. unfold conv_agree_outside_seg. intros.
  conv_break. eauto.
Qed.

Lemma emit_conv_aos : forall seg i,
  agree_outside_seg seg (interp_rtl i)
    -> conv_agree_outside_seg seg (emit i).
Proof. unfold conv_agree_outside_seg, EMIT. intros.
  prover. autorewrite with step_list_db.
  agree_outside_seg_tac.
Qed.

Hint Extern 1 (conv_agree_outside_seg _ (emit _)) => 
  apply emit_conv_aos; agree_outside_seg_tac
    : conv_agree_outside_seg_db.

Lemma fresh_conv_aos : 
  forall seg (s:nat) (almost_i: pseudo_reg s -> rtl_instr),
    (forall r, agree_outside_seg seg (interp_rtl (almost_i r)))
      -> conv_agree_outside_seg seg (fresh almost_i).
Proof. unfold conv_agree_outside_seg, fresh. intros.
  prover. autorewrite with step_list_db. 
  agree_outside_seg_tac.
Qed.

Hint Extern 1 (conv_agree_outside_seg _ (fresh _)) => 
  apply fresh_conv_aos; intros; agree_outside_seg_tac :
  conv_agree_outside_seg_db.

Lemma ret_conv_aos : forall seg (A:Type) (r:A), 
  conv_agree_outside_seg seg (ret r).
Proof. unfold conv_agree_outside_seg. prover. Qed.

Hint Resolve ret_conv_aos : conv_agree_outside_seg_db.

Ltac conv_agree_outside_seg_one_tac :=
  match goal with
    | [|- conv_agree_outside_seg _ (Bind _ _ _)] => 
      apply bind_conv_aos; [idtac | intros]
    | [|- conv_agree_outside_seg _ ?c] => extended_destruct_head c
    | [|- conv_agree_outside_seg _ _]
      => auto with conv_agree_outside_seg_db
  end.

Ltac conv_agree_outside_seg_tac := 
  repeat autounfold with conv_unfold_db;
  repeat conv_agree_outside_seg_one_tac.

(*
Lemma safe_fail_if_sound : forall op r1 r2 cs v cs' s v' s',
  safe_fail_if op r1 r2 cs = Some (v, cs')
    -> RTL_step_list (List.rev (c_rev_i cs')) s = (Okay_ans v', s')
    -> interp_test op (rtl_env s' r1) (rtl_env s' r2) <> one.
Proof. unfold safe_fail_if. intros. 
  simpl in H. inversion H; subst; clear H.
  simpl in H0.
  autorewrite with step_list_db in H0.
  compute [interp_rtl] in H0.
  repeat rtl_okay_elim. removeUnit.
  simpl in H1.
  remember_destruct_head in H1 as chk.
    Case "test succeeds". rtl_okay_elim.
    Case "test fails". rtl_okay_elim.
      simpl. simpl_rtl.
      apply int_eq_false_iff2 in Hchk. 
      assumption.
Qed.
*)

Lemma add_and_check_safe : forall seg addr cs r cs' s v' s',
  add_and_check_segment seg addr cs = (r, cs') 
    -> addr <> ps_reg RTL.size32 (c_next cs)
    -> addr <> ps_reg RTL.size32 (c_next cs + 1)
    -> addr <> ps_reg  RTL.size32 (c_next cs + 2)
    -> RTL_step_list (List.rev (c_rev_i cs')) s = (Okay_ans v', s')
    -> Ensembles.In _ (segAddrs seg s') (rtl_env s' r).
Proof. intros.
  unfold add_and_check_segment in H. 
  simpl in H. simpl_rtl.
  inv H. simpl in H3.
  autorewrite with step_list_db in H3.
  repeat rtl_okay_elim. removeUnit.
  simpl in H4.
  remember_destruct_head in H4 as chk.
  Case "test succeeds". repeat rtl_okay_elim.
  Case "test fails".
    unfold segAddrs. 
    simpl in *. repeat rtl_okay_elim. simpl in *. simpl_rtl.
    unfold Ensembles.In, addrRegion.
    exists (rtl_env s0 addr).
    split. trivial.
      apply int_eq_false_iff2 in Hchk.
      compute [interp_test] in Hchk.
      remember_destruct_head in Hchk as ltu; try congruence.
      all_to_Z_tac. apply Zge_le. assumption.
Qed.

Lemma smem_agree_outside_seg : forall seg v addr cs r cs',
  smem seg v addr cs = (r, cs')
    -> addr <> ps_reg RTL.size32 (c_next cs)
    -> addr <> ps_reg RTL.size32 (c_next cs + 1)
    -> addr <> ps_reg RTL.size32 (c_next cs + 2)
    -> agree_outside_seg seg (RTL_step_list (List.rev (c_rev_i cs)))
    -> agree_outside_seg seg (RTL_step_list (List.rev (c_rev_i cs'))).
Proof. unfold smem. intros.
  conv_break.
  compute [write_byte EMIT] in H.
  inversion H; subst; clear H.
  simpl. autorewrite with step_list_db.
  assert (conv_agree_outside_seg seg (add_and_check_segment seg addr))
    as H10.
    unfold add_and_check_segment.
    conv_agree_outside_seg_tac.
  unfold agree_outside_seg. intros.
  repeat rtl_okay_elim. removeUnit.
  assert (Ensembles.In _ (segAddrs seg s0) (rtl_env s0 v0)) as H12.
    eapply add_and_check_safe; eassumption.
  apply H10 in H4. apply H4 in H3. apply H3 in H5.
  assert (segAddrs seg s = segAddrs seg s0) as H14.
    unfold segAddrs. prover.
  rewrite <- H14 in H12.
  assert (SegStart s0 seg = SegStart s1 seg /\
          SegLimit s0 seg = SegLimit s1 seg).
    simpl in H6. compute [set_byte] in H6.
    inversion H6; clear H6. subst s1.
    prover.
  assert (agree_outside_addr_region (segAddrs seg s) s0 s1).
    unfold agree_outside_addr_region; intros.
    simpl in H6. compute [set_byte] in H6. 
    inversion H6; clear H6; subst s1.
    simpl in *.
    rewrite AddrMap.gso by prover. trivial.
  split. prover. split. prover.
    apply agree_outside_addr_region_trans with (s2:=s0); prover.
Qed.

  
Lemma smem_agree_outside_seg_2 : forall seg v addr_id cs r cs',
  smem seg v (ps_reg _ addr_id) cs = (r, cs')
    -> addr_id < c_next cs
    -> agree_outside_seg seg (RTL_step_list (List.rev (c_rev_i cs)))
    -> agree_outside_seg seg (RTL_step_list (List.rev (c_rev_i cs'))).
Proof. intros. eapply smem_agree_outside_seg; 
  (eassumption || intro H5; inversion H5; omega).
Qed.

Ltac conv_backward_aos :=
  match goal with
    [H: ?cv ?cs = (_, ?cs') |- 
      agree_outside_seg _ (RTL_step_list (rev (c_rev_i ?cs')))]
      => eapply conv_agree_outside_seg_e; 
        [eassumption | conv_agree_outside_seg_tac | idtac]
  end.

Lemma set_mem_n_aos :
  forall n seg (v:pseudo_reg (8*(n+1)-1)) addr_id cs r cs',
    set_mem_n seg v (ps_reg _ addr_id) cs = (r, cs')
      -> addr_id < c_next cs
      -> agree_outside_seg seg (RTL_step_list (List.rev (c_rev_i cs)))
      -> agree_outside_seg seg (RTL_step_list (List.rev (c_rev_i cs'))).
Proof. induction n; intros.
  Case "n=0". simpl in H. eapply smem_agree_outside_seg_2; eassumption.
  Case "S n".
    unfold set_mem_n in H.
    fold (@set_mem_n n) in H. 
    repeat conv_break. removeUnit.
    destruct v6 as [pr6].
    eapply smem_agree_outside_seg_2.
      eassumption.
      eapply fresh_conv_index_monotone. eassumption.
      do 5 conv_backward_aos.
      eapply IHn. eassumption. 
        apply fresh_pr_monotone in H2. omega.
        conv_backward_aos. assumption.
Qed.


Lemma set_mem_n_aos_2 :
  forall n seg (v:pseudo_reg (8*(n+1)-1)) cv,
    conv_index_monotone cv
      -> conv_agree_outside_seg seg cv
      -> conv_agree_outside_seg seg (addr <- cv; set_mem_n seg v addr).
Proof. unfold conv_agree_outside_seg. intros.
  conv_break. destruct v1.
  eapply set_mem_n_aos. eassumption.
    eauto. eauto.
Qed.

Lemma set_mem_n_aos_3 :
  forall n seg (v:pseudo_reg (8*(n+1)-1)) cv 
     (A:Type) (f: pseudo_reg RTL.size32 -> Conv A),
    conv_index_monotone cv
      -> conv_agree_outside_seg seg cv
      -> (forall addr, conv_agree_outside_seg seg (f addr))
      -> conv_agree_outside_seg seg (addr <- cv; set_mem_n seg v addr;; f addr).
Proof. unfold conv_agree_outside_seg. intros.
  do 2 conv_break. removeUnit. destruct v1.
  eapply H1. eassumption.
  eapply set_mem_n_aos. eassumption.
    eauto. eauto.
Qed.

(** ** a little prover for showing two segment registers are the same *)
Definition seg_eq (seg1 seg2 : segment_register) := seg1 = seg2.

Lemma seg_eq_refl : forall seg, seg_eq seg seg. 
Proof. prover. Qed.

Hint Resolve seg_eq_refl : conv_agree_outside_seg_db.

Lemma iset_op32_aos : forall seg1 seg2 pre op,
  seg_eq seg1 seg2 -> conv_agree_outside_seg seg1 (iset_op32 seg2 pre op).
Proof. unfold seg_eq, iset_op32, compute_addr, set_mem32. 
  intros. subst.
  destruct op. 
    conv_agree_outside_seg_tac.
    conv_agree_outside_seg_tac.
    apply set_mem_n_aos_2; [conv_index_monotone_tac | conv_agree_outside_seg_tac].
    apply set_mem_n_aos_2; [conv_index_monotone_tac | conv_agree_outside_seg_tac].
Qed.

Lemma iset_op16_aos : forall seg1 seg2 pre op,
  seg_eq seg1 seg2 -> conv_agree_outside_seg seg1 (iset_op16 seg2 pre op).
Proof. unfold seg_eq, iset_op16, compute_addr. intros. subst.
  destruct op.
    conv_agree_outside_seg_tac.
    conv_agree_outside_seg_tac.
    apply set_mem_n_aos_2; [conv_index_monotone_tac | conv_agree_outside_seg_tac].
    apply set_mem_n_aos_2; [conv_index_monotone_tac | conv_agree_outside_seg_tac].
Qed.

Lemma iset_op8_aos : forall seg1 seg2 pre op,
  seg_eq seg1 seg2 -> conv_agree_outside_seg seg1 (iset_op8 seg2 pre op).
Proof. unfold seg_eq, iset_op8, compute_addr. intros. subst.
  destruct op.
    conv_agree_outside_seg_tac.
    conv_agree_outside_seg_tac.
    apply set_mem_n_aos_2; [conv_index_monotone_tac | conv_agree_outside_seg_tac].
    apply set_mem_n_aos_2; [conv_index_monotone_tac | conv_agree_outside_seg_tac].
Qed.

Hint Resolve iset_op32_aos iset_op16_aos iset_op8_aos
  : conv_agree_outside_seg_db.

Lemma set_op_aos : forall seg1 seg2 pre w r op,
  seg_eq seg1 seg2 
    -> conv_agree_outside_seg seg1 (set_op pre w seg2 r op).
Proof. unfold seg_eq, set_op. intros. subst.
  destruct (op_override pre); destruct w;
  conv_agree_outside_seg_tac.
Qed.

Hint Resolve set_op_aos : conv_agree_outside_seg_db.



Lemma iset_op8_reg_op_aos : forall seg1 seg2 pre reg,
  conv_agree_outside_seg seg1 (iset_op8 seg2 pre (Reg_op reg)).
Proof. unfold seg_eq, iset_op8, compute_addr. intros. subst.
  conv_agree_outside_seg_tac.
Qed.

Lemma iset_op16_reg_op_aos : forall seg1 seg2 pre reg,
  conv_agree_outside_seg seg1 (iset_op16 seg2 pre (Reg_op reg)).
Proof. unfold seg_eq, iset_op16, compute_addr. intros. subst.
  conv_agree_outside_seg_tac.
Qed.

Lemma iset_op32_reg_op_aos : forall seg1 seg2 pre reg,
  conv_agree_outside_seg seg1 (iset_op32 seg2 pre (Reg_op reg)).
Proof. unfold seg_eq, iset_op32, compute_addr, set_mem32. intros. 
  conv_agree_outside_seg_tac.
Qed.

Hint Resolve iset_op8_reg_op_aos iset_op16_reg_op_aos iset_op32_reg_op_aos
  : conv_agree_outside_seg_db.

Lemma set_op_reg_op_aos : forall seg1 seg2 pre w r reg,
  conv_agree_outside_seg seg1 (set_op pre w seg2 r (Reg_op reg)).
Proof. unfold seg_eq, set_op. intros. subst.
  destruct (op_override pre); destruct w;
  conv_agree_outside_seg_tac.
Qed.

Hint Resolve set_op_reg_op_aos : conv_agree_outside_seg_db.

Lemma load_mem_n_aos : forall seg1 seg2 addr n,
  conv_agree_outside_seg seg1 (load_mem_n seg2 addr n).
Proof. unfold load_mem_n, lmem, add_and_check_segment.
  induction n. 
    conv_agree_outside_seg_tac.
    fold load_mem_n in *. conv_agree_outside_seg_tac.
Qed.

(* I have to do the following seems because of dependent types *)
Hint Extern 1 (conv_agree_outside_seg _ (load_mem_n _ _ ?X))
  =>  apply load_mem_n_aos with (n:=X)
  : conv_agree_outside_seg_db.

Lemma iload_op8_aos : forall seg1 seg op,
  conv_agree_outside_seg seg1 (iload_op8 seg op).
Proof. unfold iload_op8, load_mem8, compute_addr. intros. 
  conv_agree_outside_seg_tac.
Qed.  

Lemma iload_op16_aos : forall seg1 seg op,
  conv_agree_outside_seg seg1 (iload_op16 seg op).
Proof. unfold iload_op16, load_mem16, compute_addr. intros. 
  conv_agree_outside_seg_tac.
Qed.  

Lemma iload_op32_aos : forall seg1 seg op,
  conv_agree_outside_seg seg1 (iload_op32 seg op).
Proof. unfold iload_op32, load_mem32, compute_addr. intros. 
  conv_agree_outside_seg_tac.
Qed.  

Hint Immediate iload_op8_aos iload_op16_aos iload_op32_aos
  : conv_agree_outside_seg_db.

Lemma load_op_aos : forall seg1 p w seg2 op,
  conv_agree_outside_seg seg1 (load_op p w seg2 op).
Proof. unfold load_op. intros. conv_agree_outside_seg_tac. Qed.

Hint Immediate load_op_aos : conv_agree_outside_seg_db.

Lemma set_Bit_mem_aos : forall seg pre w op addr poff bitval,
  seg_eq seg (get_segment_op pre DS op)
    -> conv_agree_outside_seg seg (set_Bit_mem pre w op addr poff bitval).
Proof. unfold set_Bit_mem, modify_Bit, set_mem, 
         load_mem, load_mem32, load_mem16, load_mem8, not, set_mem8,
         set_mem16, set_mem32. intros.
  unfold seg_eq in *. subst seg.
  do 2 (conv_agree_outside_seg_one_tac; [conv_agree_outside_seg_tac | idtac]).
  destruct (op_override pre); destruct w;
    (apply set_mem_n_aos_2; [conv_index_monotone_tac | conv_agree_outside_seg_tac]).
Qed.

Lemma conv_BS_aux_aos : forall seg s d n (op:pseudo_reg s),
  conv_agree_outside_seg seg (conv_BS_aux d n op).
Proof. unfold conv_BS_aux.  
  induction n; intros; conv_agree_outside_seg_tac.
Qed.

Lemma compute_parity_aux_aos : 
  forall seg s (op1:pseudo_reg s) op2 n,
    conv_agree_outside_seg seg (compute_parity_aux op1 op2 n).
Proof. induction n. simpl. conv_agree_outside_seg_tac.
  unfold compute_parity_aux. fold (@compute_parity_aux s).
  conv_agree_outside_seg_tac.
Qed.

Hint Resolve set_Bit_mem_aos compute_parity_aux_aos conv_BS_aux_aos 
  : conv_agree_outside_seg_db.

(** * Lemmas about a conversion preserves the property of same_pc *)

Module Conv_Same_PC := Conv_Prop (Same_PC).
Notation conv_same_pc := Conv_Same_PC.conv_prop.

Hint Extern 1 (conv_same_pc (emit _)) => 
  apply Conv_Same_PC.emit_sat_conv_prop; same_pc_tac : conv_same_pc_db.

Hint Extern 1 (conv_same_pc (fresh _)) => 
  apply Conv_Same_PC.fresh_sat_conv_prop; intros; same_pc_tac :
  conv_same_pc_db.

Hint Resolve Conv_Same_PC.ret_sat_conv_prop 
  : conv_same_pc_db.

Ltac conv_same_pc_tac := 
  repeat autounfold with conv_unfold_db;
  repeat (match goal with
            | [|- conv_same_pc (Bind _ _ _)] => 
              apply Conv_Same_PC.bind_sat_conv_prop; [idtac | intros]
            | [|- conv_same_pc ?c] => extended_destruct_head c
            | [|- conv_same_pc _] => auto with conv_same_pc_db
          end).

Lemma conv_same_pc_e : forall (A:Type) (cv:Conv A) cs v cs',
  cv cs = (v, cs')
    -> conv_same_pc cv
    -> same_pc (RTL_step_list (List.rev (c_rev_i cs)))
    -> same_pc (RTL_step_list (List.rev (c_rev_i cs'))).
Proof. unfold conv_same_pc. eauto. Qed.

Ltac conv_backward_same_pc :=
  match goal with
    [H: ?cv ?cs = (_, ?cs') |- 
      same_pc (RTL_step_list (rev (c_rev_i ?cs')))]
    => eapply conv_same_pc_e;
       [eassumption | conv_same_pc_tac | idtac]
  end.

Lemma load_mem_n_same_pc : forall seg addr n,
  conv_same_pc (load_mem_n seg addr n).
Proof. unfold load_mem_n, lmem, add_and_check_segment.
  induction n. 
    conv_same_pc_tac.
    fold load_mem_n in *. conv_same_pc_tac.
Qed.

Hint Extern 1 (conv_same_pc (load_mem_n _ _ ?X))
  =>  apply load_mem_n_same_pc with (n:=X) : conv_same_pc_db.

Lemma set_mem_n_same_pc : forall n seg (v:pseudo_reg (8*(n+1)-1)) addr,
  conv_same_pc (set_mem_n seg v addr).
Proof. unfold set_mem_n, smem, add_and_check_segment.
  induction n; intros. 
    conv_same_pc_tac.
    fold (@set_mem_n n) in *. conv_same_pc_tac.
Qed.

Hint Immediate set_mem_n_same_pc : conv_same_pc_db.

Lemma iload_op8_same_pc : forall seg op,
  conv_same_pc (iload_op8 seg op).
Proof. unfold iload_op8, load_mem8, compute_addr. intros. 
  conv_same_pc_tac.
Qed.  

Lemma iload_op16_same_pc : forall seg op,
  conv_same_pc (iload_op16 seg op).
Proof. unfold iload_op16, load_mem16, compute_addr. intros. 
  conv_same_pc_tac.
Qed.  

Lemma iload_op32_same_pc : forall seg op,
  conv_same_pc (iload_op32 seg op).
Proof. unfold iload_op32, load_mem32, compute_addr. intros. 
  conv_same_pc_tac.
Qed.  

Hint Immediate iload_op8_same_pc iload_op16_same_pc
  iload_op32_same_pc : conv_same_pc_db.

Lemma load_op_same_pc : forall p w rseg op,
  conv_same_pc (load_op p w rseg op).
Proof. unfold load_op. intros. conv_same_pc_tac. Qed.

Hint Immediate load_op_same_pc : conv_same_pc_db.

Lemma set_reg_same_pc : forall p r,
  conv_same_pc (set_reg p r).
Proof. unfold set_reg. intros. apply Conv_Same_PC.emit_sat_conv_prop.
  unfold same_pc, Same_PC_Rel.brel. simpl. unfold set_loc. intros.
  prover.
Qed.

Hint Immediate set_reg_same_pc : conv_same_pc_db.

Lemma set_op_same_pc : forall p w seg r op,
  conv_same_pc (set_op p w seg r op).
Proof. unfold set_op, iset_op32, iset_op16, iset_op8.
  unfold set_mem32, set_mem16, set_mem8, compute_addr. intros.
  destruct (op_override p); destruct w;
  conv_same_pc_tac.
Qed.

Hint Immediate set_op_same_pc : conv_same_pc_db.

Lemma conv_BS_aux_same_pc : forall s d n (op:pseudo_reg s),
  conv_same_pc (conv_BS_aux d n op).
Proof. unfold conv_BS_aux.  
  induction n; intros; conv_same_pc_tac.
Qed.

Lemma compute_parity_aux_same_pc : forall s (op1:pseudo_reg s) op2 n,
  conv_same_pc (compute_parity_aux op1 op2 n).
Proof. induction n. simpl. conv_same_pc_tac.
  unfold compute_parity_aux. fold (@compute_parity_aux s).
  conv_same_pc_tac.
Qed.

Hint Immediate conv_BS_aux_same_pc compute_parity_aux_same_pc :
  conv_same_pc_db.

(** * Lemmas about the property that conversions preserve the 
   same_mach_state property *)
Module Conv_Same_Mach_State := Conv_Prop (Same_Mach_State).
Notation conv_same_mach_state := Conv_Same_Mach_State.conv_prop.

Hint Extern 1 (conv_same_mach_state (emit _)) => 
  apply Conv_Same_Mach_State.emit_sat_conv_prop; same_mach_state_tac
    : conv_same_mach_state_db.

Hint Extern 1 (conv_same_mach_state (fresh _)) => 
  apply Conv_Same_Mach_State.fresh_sat_conv_prop; intros; same_mach_state_tac :
  conv_same_mach_state_db.

Hint Resolve Conv_Same_Mach_State.ret_sat_conv_prop 
  : conv_same_mach_state_db.

Ltac conv_same_mach_state_tac := 
  repeat autounfold with conv_unfold_db;
  repeat (match goal with
            | [|- conv_same_mach_state (Bind _ _ _)] => 
              apply Conv_Same_Mach_State.bind_sat_conv_prop; [idtac | intros]
            | [|- conv_same_mach_state ?c] => extended_destruct_head c
            | [|- conv_same_mach_state _] => auto with conv_same_mach_state_db
          end).

Lemma conv_same_mach_state_e : forall (A:Type) (cv:Conv A) cs v cs',
  cv cs = (v, cs')
    -> conv_same_mach_state cv
    -> same_mach_state (RTL_step_list (List.rev (c_rev_i cs)))
    -> same_mach_state (RTL_step_list (List.rev (c_rev_i cs'))).
Proof. unfold conv_same_mach_state. eauto. Qed.

Ltac conv_backward_sms :=
  match goal with
    [H: ?cv ?cs = (_, ?cs') |- 
      same_mach_state (RTL_step_list (rev (c_rev_i ?cs')))]
      => eapply conv_same_mach_state_e;
        [eassumption | conv_same_mach_state_tac | idtac]
  end.

Lemma set_mem_n_same_mach_state : forall n seg (v:pseudo_reg (8*(n+1)-1)) addr,
  conv_same_mach_state (set_mem_n seg v addr).
Proof. unfold set_mem_n, smem, add_and_check_segment.
  induction n; intros. 
    conv_same_mach_state_tac.
    fold (@set_mem_n n) in *. conv_same_mach_state_tac.
Qed.

Hint Immediate set_mem_n_same_mach_state : conv_same_mach_state_db.



(** * Lemmas about the property that conversions preserve the no_fail property *)
Definition conv_no_fail (A:Type) (cv:Conv A) :=
  forall cs (v:A) cs',
    cv cs = (v, cs')
      -> no_fail (RTL_step_list (List.rev (c_rev_i cs)))
      -> no_fail (RTL_step_list (List.rev (c_rev_i cs'))).
Implicit Arguments conv_no_fail [A].

Lemma conv_to_rtl_no_fail: forall cv,
    conv_no_fail cv ->  no_fail (RTL_step_list (runConv cv)).
Proof. unfold conv_no_fail, runConv. intros.
  remember_rev (cv {| c_rev_i := nil; c_next := 0 |}) as cva.
  destruct cva.
  apply H in Hcva. prover. 
    compute [c_rev_i rev RTL_step_list].
    no_fail_tac.
Qed.

Lemma bind_conv_no_fail : forall (A B:Type) (cv: Conv A) (f:A -> Conv B),
  conv_no_fail cv
    -> (forall a:A, conv_no_fail (f a))
    -> conv_no_fail (Bind _ cv f).
Proof. unfold conv_no_fail. intros.
  conv_break. eauto.
Qed.

Lemma emit_conv_no_fail : forall i,
  no_fail (interp_rtl i) -> conv_no_fail (emit i).
Proof. unfold conv_no_fail, EMIT. intros.
  prover. autorewrite with step_list_db.
  no_fail_tac.
Qed.

Hint Extern 1 (conv_no_fail (emit _)) => 
  apply emit_conv_no_fail; no_fail_tac : conv_no_fail_db.

Lemma fresh_conv_no_fail : 
  forall (s:nat) (almost_i: pseudo_reg s -> rtl_instr),
    (forall r, no_fail (interp_rtl (almost_i r)))
      -> conv_no_fail (fresh almost_i).
Proof. unfold conv_no_fail, fresh. intros.
  prover. autorewrite with step_list_db. 
  no_fail_tac.
Qed.

Hint Extern 1 (conv_no_fail (fresh _)) => 
  apply fresh_conv_no_fail; intros; no_fail_tac : conv_no_fail_db.

Lemma ret_conv_no_fail : forall (A:Type) (r:A), conv_no_fail (ret r).
Proof. unfold conv_no_fail. prover. Qed.

Hint Resolve ret_conv_no_fail : conv_no_fail_db.

Ltac conv_no_fail_tac := 
  repeat autounfold with conv_unfold_db;
  repeat (match goal with
            | [H: no_imm_op (Imm_op _) = true |- conv_no_fail _]
                => discriminate H
            | [|- conv_no_fail (Bind _ _ _)] => 
              apply bind_conv_no_fail; [idtac | intros]
            | [|- conv_no_fail ?c] => extended_destruct_head c
            | [|- conv_no_fail _] => auto with conv_no_fail_db
          end).


Lemma load_mem_n_no_fail : forall seg addr n,
  conv_no_fail (load_mem_n seg addr n).
Proof. unfold load_mem_n, lmem, add_and_check_segment.
  induction n. 
    conv_no_fail_tac.
    fold load_mem_n in *. conv_no_fail_tac.
Qed.

Hint Extern 1 (conv_no_fail (load_mem_n _ _ ?X))
  =>  apply load_mem_n_no_fail with (n:=X) : conv_no_fail_db.

Lemma set_mem_n_no_fail : forall n seg (v:pseudo_reg (8*(n+1)-1)) addr,
  conv_no_fail (set_mem_n seg v addr).
Proof. unfold set_mem_n, smem, add_and_check_segment.
  induction n; intros. 
    conv_no_fail_tac.
    fold (@set_mem_n n) in *. conv_no_fail_tac.
Qed.

Hint Immediate set_mem_n_no_fail : conv_no_fail_db.

Lemma iload_op8_no_fail : forall seg op,
  conv_no_fail (iload_op8 seg op).
Proof. unfold iload_op8, load_mem8, compute_addr. intros. 
  conv_no_fail_tac.
Qed.  

Lemma iload_op16_no_fail : forall seg op,
  conv_no_fail (iload_op16 seg op).
Proof. unfold iload_op16, load_mem16, compute_addr. intros. 
  conv_no_fail_tac.
Qed.  

Lemma iload_op32_no_fail : forall seg op,
  conv_no_fail (iload_op32 seg op).
Proof. unfold iload_op32, load_mem32, compute_addr. intros. 
  conv_no_fail_tac.
Qed.  

Hint Immediate iload_op8_no_fail iload_op16_no_fail
  iload_op32_no_fail : conv_no_fail_db.

Lemma load_op_no_fail : forall p w rseg op,
  conv_no_fail (load_op p w rseg op).
Proof. unfold load_op. intros. conv_no_fail_tac. Qed.

Hint Immediate load_op_no_fail : conv_no_fail_db.

Lemma set_reg_no_fail : forall p r,
  conv_no_fail (set_reg p r).
Proof. unfold set_reg. intros. conv_no_fail_tac. Qed.

Hint Immediate set_reg_no_fail : conv_no_fail_db.

Lemma iset_op8_no_fail : forall seg r op,
  no_imm_op op = true -> conv_no_fail (iset_op8 seg r op).
Proof. unfold iset_op8, compute_addr, set_mem8. intros.
  destruct op; conv_no_fail_tac. 
Qed.

Lemma iset_op16_no_fail : forall seg r op,
  no_imm_op op = true -> conv_no_fail (iset_op16 seg r op).
Proof. unfold iset_op16, compute_addr, set_mem16. intros.
  destruct op; conv_no_fail_tac.
Qed.

Lemma iset_op32_no_fail : forall seg r op,
  no_imm_op op = true -> conv_no_fail (iset_op32 seg r op).
Proof. unfold iset_op32, compute_addr, set_mem32. intros.
  destruct op; conv_no_fail_tac.
Qed.

Hint Resolve iset_op8_no_fail iset_op16_no_fail iset_op32_no_fail
  : conv_no_fail_db.
 
Lemma set_op_no_fail : forall p w seg r op,
  no_imm_op op = true -> conv_no_fail (set_op p w seg r op).
Proof. unfold set_op. intros. conv_no_fail_tac. Qed.

Hint Resolve set_op_no_fail : conv_no_fail_db.

Lemma conv_BS_aux_no_fail : forall s d n (op:pseudo_reg s),
  conv_no_fail (conv_BS_aux d n op).
Proof. unfold conv_BS_aux.  
  induction n; intros; conv_no_fail_tac.
Qed.

Lemma compute_parity_aux_no_fail : forall s (op1:pseudo_reg s) op2 n,
  conv_no_fail (compute_parity_aux op1 op2 n).
Proof. induction n. simpl. conv_no_fail_tac.
  unfold compute_parity_aux. fold (@compute_parity_aux s).
  conv_no_fail_tac.
Qed.

Hint Immediate conv_BS_aux_no_fail compute_parity_aux_no_fail :
  conv_no_fail_db.


(** * A tactic that is the aggregate of all instruction properties *)

(* In this unfolding tactic, note that I didn't unfold load_op and set_op as lemmas
   about them should already be in the hint databases *)
Ltac unfold_instr_conv_tac :=
  unfold conv_AND, conv_OR, conv_XOR, conv_TEST, conv_logical_op, 
    conv_XADD, conv_NOT, conv_ADD, conv_MOV, conv_Jcc, conv_JMP, 
    conv_ADC, conv_CDQ, conv_BSWAP,
    conv_CMPXCHG, conv_CMP, conv_CMPS, conv_CMOV,
    conv_SUB, conv_NEG, conv_SUB_CMP_generic, conv_CWDE,
    conv_DIV, conv_IDIV, conv_MUL, conv_IMUL, conv_INC, conv_LEA,
    conv_BSF, conv_BSR, conv_BS, 
    conv_MOVSX, conv_MOVZX, conv_MOV_extend, conv_XCHG,
    conv_LEAVE, conv_POPA, conv_POP, 
    conv_PUSHA, conv_SAR, conv_SBB,
    conv_SETcc, conv_SHL, conv_SHLD, conv_SHR, conv_SHRD, conv_RCL, conv_RCR, 
    conv_ROL, conv_ROR, conv_shift, 
    conv_CLD, conv_HLT, conv_STOS, conv_CLC, conv_CMC,
    conv_MOVS, conv_BT, conv_LAHF, conv_SAHF, conv_STC, conv_STD,
    conv_AAA_AAS, conv_AAD, conv_AAM, conv_DAA_DAS, conv_DEC,
    conv_POP_pseudo,
    testcarryAdd, testcarrySub,
    extract_and_set, get_and_place,
    get_AL, get_AH, set_AL, set_AH, ifset,
    string_op_reg_shift, get_Bit, fbit, set_Bit, modify_Bit,
    compute_parity, undef_flag,
    load_mem, load_mem8, load_mem16, load_mem32, set_mem32,
    compute_addr, compute_cc, not.

Ltac extra_unfold_conv_tac :=
  unfold conv_CALL, conv_PUSH, conv_PUSH_pseudo, set_Bit_mem, 
    iset_op8, iset_op16, iset_op32, set_mem, set_mem8, set_mem16, set_mem32; 
    unfold_instr_conv_tac.

Ltac no_fail_extra_unfold_tac := 
  unfold conv_CALL, conv_PUSH, conv_PUSH_pseudo, set_Bit_mem, 
    set_mem, set_mem8, set_mem16; unfold_instr_conv_tac.

Ltac prove_instr := 
  match goal with
    | [|- same_seg_regs (RTL_step_list (runConv ?CV))]
      => apply Conv_Same_Seg_Regs.conv_to_rtl_prop with (cv:=CV);
           unfold_instr_conv_tac; extra_unfold_conv_tac; conv_same_seg_regs_tac
    | [|- same_pc (RTL_step_list (runConv ?CV))]
      => apply Conv_Same_PC.conv_to_rtl_prop with (cv:=CV);
           unfold_instr_conv_tac; extra_unfold_conv_tac; conv_same_pc_tac
    | [|- same_mem (RTL_step_list (runConv ?CV))]
      => apply Conv_Same_Mem.conv_to_rtl_prop with (cv:=CV);
           unfold_instr_conv_tac; extra_unfold_conv_tac; conv_same_mem_tac
    | [|- agree_outside_seg _ (RTL_step_list (runConv ?CV))]
      => apply conv_to_rtl_aos with (cv:=CV);
         unfold_instr_conv_tac; conv_agree_outside_seg_tac
    | [|- no_fail (RTL_step_list (runConv ?CV))]
      => apply conv_to_rtl_no_fail with (cv:=CV);
           unfold_instr_conv_tac; no_fail_extra_unfold_tac; conv_no_fail_tac
  end.

(* Desmonstration of how to use prove_instr *)
Lemma POP_aoss : forall lr b1 b2 op,
  agree_outside_seg SS 
    (RTL_step_list (runConv (conv_POP (mkPrefix lr None b1 b2) op))).
Proof. intros. prove_instr. Qed.

Lemma ADD_no_fail : forall pre w op1 op2,
  no_imm_op op1 = true
    -> no_fail (RTL_step_list (runConv (conv_ADD pre w op1 op2))).
Proof. intros. prove_instr. Qed.

(** * Properties of non_cflow_instr, dir_cflow_instr, and nacl_jmp *)

(** ** Showing that non_cflow_instr preserves the same seg registers *)
(* For some reason,  if I prove the following lemma with 
   pre=emptyPrefix, the QED will take forever if I don't set
   Opaque conv_BSWAP. Opaque conv_POP. *)
Lemma nci_same_seg_regs: forall ins pre,
  non_cflow_instr pre ins = true
    -> same_seg_regs (RTL_step_list (instr_to_rtl pre ins)).
(* Admitted. *)
Proof. intros. 
  destruct ins; 
  unfold instr_to_rtl, check_prefix in *;
    (discriminate H || (prove_instr; fail) || idtac).
Qed.

Hint Resolve nci_same_seg_regs : same_seg_regs_db.

(** ** Showing that non_cflow_instr modifies only DS, SS, ES segments *)
Lemma PUSH_aos : forall pre w op,
  conv_agree_outside_seg SS (conv_PUSH pre w op).
Proof. unfold conv_PUSH, set_mem, set_mem32, set_mem16, set_mem8. 
  intros.
  do 3 (apply bind_conv_aos; [conv_agree_outside_seg_tac | intros]).
  destruct (op_override pre); destruct w;
    (apply set_mem_n_aos_3; 
      [conv_index_monotone_tac | conv_agree_outside_seg_tac
        | intros; conv_agree_outside_seg_tac]).
Qed.

Lemma PUSH_pseudo_aos : forall pre w op,
  conv_agree_outside_seg SS (conv_PUSH_pseudo pre w op).
Proof. unfold conv_PUSH_pseudo, set_mem, set_mem32, set_mem16, set_mem8. 
  intros.
  do 2 (apply bind_conv_aos; [conv_agree_outside_seg_tac | intros]).
  destruct (op_override pre); destruct w;
    (apply set_mem_n_aos_3; 
      [conv_index_monotone_tac | conv_agree_outside_seg_tac
        | intros; conv_agree_outside_seg_tac]).
Qed.

Hint Resolve PUSH_aos PUSH_pseudo_aos : conv_agree_outside_seg_db.

Lemma only_op_override_seg_eq : forall pre seg,
  only_op_override pre = true -> seg_eq seg (get_segment pre seg).
Proof. unfold only_op_override, get_segment. intros.
  destruct (lock_rep pre); destruct (seg_override pre); prover.
Qed.

Lemma only_lock_or_rep_seg_eq : forall pre seg,
  only_lock_or_rep pre = true -> seg_eq seg (get_segment pre seg).
Proof. unfold only_lock_or_rep, get_segment. intros.
  destruct (lock_rep pre); destruct (seg_override pre).
    destruct l; prover.
    destruct l; prover.
    prover. prover.
Qed.

Lemma only_gs_seq_override_seg_eq : forall pre seg,
  only_gs_seg_override pre = true -> 
    (seg_eq seg (get_segment pre seg) \/ seg_eq GS (get_segment pre seg)).
Proof. unfold only_gs_seg_override, get_segment. intros.
  destruct (lock_rep pre). discriminate.
  destruct (seg_override pre). right. destruct s; prover.
  destruct op_override. discriminate.
  destruct (addr_override pre). discriminate.
    left. apply seg_eq_refl.
Qed.  

Lemma either_prefix_seg_eq : forall pre seg,
  either_prefix pre = true -> 
    seg_eq seg (get_segment pre seg) \/ seg_eq GS (get_segment pre seg).
Proof. unfold either_prefix. intros.
  bool_elim_tac. auto using only_op_override_seg_eq.
    auto using only_gs_seq_override_seg_eq.
Qed.

Hint Resolve only_op_override_seg_eq only_lock_or_rep_seg_eq
  only_gs_seq_override_seg_eq either_prefix_seg_eq : conv_agree_outside_seg_db.

Lemma only_op_override_get_segment_op2 : forall pre seg op1 op2,
  only_op_override pre = true
    -> seg_eq seg (get_segment_op2 pre seg op1 op2) \/
       seg_eq SS (get_segment_op2 pre seg op1 op2).
Proof. unfold only_op_override, get_segment_op2. intros. 
  do 2 (destruct_head in H; try discriminate).
  destruct_head. right; prover.
  destruct_head. right; prover. left; prover.
Qed.

Lemma only_lock_or_rep_get_segment_op2 : forall pre seg op1 op2,
  only_lock_or_rep pre = true
    -> seg_eq seg (get_segment_op2 pre seg op1 op2) \/
       seg_eq SS (get_segment_op2 pre seg op1 op2).
Proof. unfold only_lock_or_rep, get_segment_op2. intros.
  destruct (lock_rep pre).
  destruct l; try congruence.
    do 3 (destruct_head in H; try discriminate).
      destruct_head. right; prover.
      destruct_head; prover.
    do 3 (destruct_head in H; try discriminate).
      destruct_head. prover.
      destruct_head; prover.
Qed.    

Lemma only_gs_seq_override_get_segment_op2 : forall pre seg op1 op2,
  only_gs_seg_override pre = true -> 
    (seg_eq seg (get_segment_op2 pre seg op1 op2) \/
     seg_eq SS (get_segment_op2 pre seg op1 op2) \/
     seg_eq GS (get_segment_op2 pre seg op1 op2)).
Proof. unfold only_gs_seg_override, get_segment_op2. intros.
  destruct_head in H; try discriminate.
  destruct (seg_override pre). destruct s; prover.
  destruct (op_override pre); try discriminate.
  destruct (addr_override pre); try discriminate.
  destruct_head. prover.
  destruct_head; prover.
Qed.  

Lemma either_prefix_get_segment_op2 : forall pre seg op1 op2,
  either_prefix pre = true
    -> seg_eq seg (get_segment_op2 pre seg op1 op2) \/
       seg_eq SS (get_segment_op2 pre seg op1 op2) \/
       seg_eq GS (get_segment_op2 pre seg op1 op2).
Proof. unfold either_prefix. intros. bool_elim_tac.
  use_lemma only_op_override_get_segment_op2 by eassumption.
    destruct H0; eauto.
  use_lemma only_gs_seq_override_get_segment_op2 by eassumption.
    destruct H0. eauto. destruct H0; eauto.
Qed.

Lemma only_op_override_get_segment_op : forall pre seg op1,
  only_op_override pre = true
    -> seg_eq seg (get_segment_op pre seg op1) \/
       seg_eq SS (get_segment_op pre seg op1).
Proof. unfold only_op_override, get_segment_op. intros. 
  do 2 (destruct_head in H; try discriminate).
  destruct_head. right; prover.
    left; prover. 
Qed.

Lemma only_lock_or_rep_get_segment_op : forall pre seg op1,
  only_lock_or_rep pre = true
    -> seg_eq seg (get_segment_op pre seg op1) \/
       seg_eq SS (get_segment_op pre seg op1).
Proof. unfold only_lock_or_rep, get_segment_op. intros. 
  destruct (lock_rep pre).
  destruct l; try congruence.
  do 3 (destruct_head in H; try discriminate).
    destruct_head; prover.
  do 3 (destruct_head in H; try discriminate).
    destruct_head; prover.
Qed.

Lemma only_gs_seq_override_get_segment_op : forall pre seg op1,
  only_gs_seg_override pre = true -> 
    (seg_eq seg (get_segment_op pre seg op1) \/
     seg_eq SS (get_segment_op pre seg op1) \/
     seg_eq GS (get_segment_op pre seg op1)).
Proof. unfold only_gs_seg_override, get_segment_op. intros.
  destruct_head in H; try discriminate.
  destruct (seg_override pre). destruct s; prover.
  destruct (op_override pre); try discriminate.
  destruct (addr_override pre); try discriminate.
  destruct_head; prover.
Qed.  

Lemma either_prefix_get_segment_op : forall pre seg op1,
  either_prefix pre = true
    -> seg_eq seg (get_segment_op pre seg op1) \/
       seg_eq SS (get_segment_op pre seg op1) \/
       seg_eq GS (get_segment_op pre seg op1).
Proof. unfold either_prefix. intros. bool_elim_tac.
  use_lemma only_op_override_get_segment_op by eassumption.
    destruct H0; eauto.
  use_lemma only_gs_seq_override_get_segment_op by eassumption.
    destruct H0. eauto. destruct H0; eauto.
Qed.

(* This is only for demonstration purpose *)
Lemma ADD_aos : forall pre w op1 op2,
  either_prefix pre = true
    -> agree_outside_seg DS (RTL_step_list (runConv (conv_ADD pre w op1 op2))) \/
       agree_outside_seg SS (RTL_step_list (runConv (conv_ADD pre w op1 op2))) \/
       agree_outside_seg GS (RTL_step_list (runConv (conv_ADD pre w op1 op2))).
Proof. intros. 
  assert (H10: seg_eq DS (get_segment_op2 pre DS op1 op2) \/
               seg_eq SS (get_segment_op2 pre DS op1 op2) \/
               seg_eq GS (get_segment_op2 pre DS op1 op2)).
    apply either_prefix_get_segment_op2; assumption.
  destruct H10 as [H10|[H10|H10]]. 
    left. prove_instr.
    right. left. prove_instr.
    right. right. prove_instr.
Qed.

Ltac get_segment_aos_tac := 
  match goal with
    | [H:either_prefix _ = true |- _]
      => apply either_prefix_seg_eq with (seg:=DS) in H;
         destruct H; [left; prove_instr | right; right; left; prove_instr]
  end.

Ltac aos_case_tac H :=
  destruct H; 
    [left; prove_instr | 
      (destruct H; [right; left; prove_instr | right; right; left; prove_instr])].

Ltac get_segment_op2_aos_tac opx opy := 
    match goal with 
      | [H: either_prefix ?PRE = true |- _] =>
        dupHyp H;
        apply either_prefix_get_segment_op2 with 
          (seg:=DS) (op1:=opx) (op2:=opy) in H;
        aos_case_tac H
      | [H: only_gs_seg_override ?PRE = true |- _] => 
        dupHyp H;
        apply only_gs_seq_override_get_segment_op2 with 
          (seg:=DS) (op1:=opx) (op2:=opy) in H;
        aos_case_tac H
      | [H: only_lock_or_rep ?PRE = true |- _] =>
        dupHyp H;
        apply only_lock_or_rep_get_segment_op2 with 
          (seg:=DS) (op1:=opx) (op2:=opy) in H;
        destruct H; [left; prove_instr | right; left; prove_instr]
    end.

Ltac get_segment_op_aos_tac opx := 
    match goal with 
      | [H: either_prefix ?PRE = true |- _] =>
        dupHyp H;
        apply either_prefix_get_segment_op with 
          (seg:=DS) (op1:=opx) in H;
        aos_case_tac H
      | [H: only_gs_seg_override ?PRE = true |- _] => 
        dupHyp H;
        apply only_gs_seq_override_get_segment_op with 
          (seg:=DS) (op1:=opx) in H;
        aos_case_tac H
      | [H: only_lock_or_rep ?PRE = true |- _] =>
        dupHyp H;
        apply only_lock_or_rep_get_segment_op with 
          (seg:=DS) (op1:=opx) in H;
        destruct H; [left; prove_instr | right; left; prove_instr]
    end.

Lemma nci_aos :forall ins pre,
  non_cflow_instr pre ins = true
    -> (agree_outside_seg DS (RTL_step_list (instr_to_rtl pre ins)) \/
        agree_outside_seg SS (RTL_step_list (instr_to_rtl pre ins)) \/
        agree_outside_seg GS (RTL_step_list (instr_to_rtl pre ins)) \/
        agree_outside_seg ES (RTL_step_list (instr_to_rtl pre ins))).
(* Admitted. *)
Proof. intros.
  destruct ins; 
  unfold instr_to_rtl, check_prefix in *; simpl in H; bool_elim_tac;
    try (discriminate H || left; prove_instr; fail).

  (* ADC *)
  get_segment_op2_aos_tac op1 op2.
  (* ADD *)
  get_segment_op2_aos_tac op1 op2.
  (* AND *)
  get_segment_op2_aos_tac op1 op2.
  (* BSF *)
  get_segment_op2_aos_tac op1 op2.
  (* BSR *)
  get_segment_op2_aos_tac op1 op2.
  (* BT *)
  get_segment_op_aos_tac op1.
  (* BT *)
  get_segment_op_aos_tac op1.
  (* BT *)
  get_segment_op_aos_tac op1.
  (* BT *)
  get_segment_op_aos_tac op1.
  (* CMOV *)
  get_segment_op2_aos_tac op1 op2.
  (* CMPXCHG *)
  get_segment_op2_aos_tac op1 op2.
  (* DEC *)
  get_segment_op_aos_tac op1.
  (* IMUL *)
  destruct opopt as [o|];
    [get_segment_op2_aos_tac op1 o | get_segment_op_aos_tac op1].
  (* INC *)
  get_segment_op_aos_tac op1.
  (* LEA *)
  destruct op2; try discriminate. bool_elim_tac.
  get_segment_op_aos_tac op1.
  (* MOV *)
  get_segment_op2_aos_tac op1 op2.
  (* MOVS *)
  right; right; right; prove_instr.
  (* MOVSX *)
  get_segment_op2_aos_tac op1 op2.
  (* MOVZX *)
  get_segment_op2_aos_tac op1 op2.
  (* NEG *)
  get_segment_op_aos_tac op.
  (* NOT *)
  get_segment_op_aos_tac op.
  (* OR *)
  get_segment_op2_aos_tac op1 op2.
  (* POP *)
  right; left; prove_instr.
  (* POPA *)
  right; left; prove_instr.
  (* PUSHA *)
  right; left; prove_instr.
  (* RCL *)
  get_segment_op_aos_tac op1.
  (* RCR *)
  get_segment_op_aos_tac op1.
  (* ROL *)
  get_segment_op_aos_tac op1.
  (* ROR *)
  get_segment_op_aos_tac op1.
  (* SAR *)
  get_segment_op_aos_tac op1.
  (* SBB *)
  get_segment_op2_aos_tac op1 op2.
  (* SETcc *)
  get_segment_op_aos_tac op1.
  (* SHL *)
  get_segment_op_aos_tac op1.
  (* SHLD *)
  get_segment_op_aos_tac op1.
  (* SHR *)
  get_segment_op_aos_tac op1.
  (* SHRD *)
  get_segment_op_aos_tac op1.
  (* STOS *)
  right; right; right; prove_instr.
  (* SUB *)
  get_segment_op2_aos_tac op1 op2.
  (* XADD *)
  get_segment_op2_aos_tac op1 op2.
  (* XCHG *)
  get_segment_op2_aos_tac op1 op2.
  (* XOR *)
  get_segment_op2_aos_tac op1 op2.
Qed.
 
(** ** Showing that non_cflow_instr does not modify the PC *)

Lemma nci_same_pc: forall ins pre,
  non_cflow_instr pre ins = true
    -> same_pc (RTL_step_list (instr_to_rtl pre ins)).
(* Admitted. *)
Proof. intros.
  destruct ins; 
  unfold instr_to_rtl, check_prefix in *;
    (discriminate H || prove_instr).
Qed.

(** ** Showing that dir_cflow_instr does not modify segment registers *)

Lemma dci_same_seg_regs: forall ins pre,
  dir_cflow_instr pre ins = true
    -> same_seg_regs (RTL_step_list (instr_to_rtl pre ins)).
Proof. intros. 
  destruct ins; 
  unfold instr_to_rtl, check_prefix in *;
    (discriminate H || prove_instr).
Qed. 

Hint Resolve dci_same_seg_regs : same_seg_regs_db.

(** ** Showing that dir_cflow_instr only modify SS memory
       (only the call instruction will modify that) *)

Lemma CALL_aoss : forall pre near absolute op sel,
  conv_agree_outside_seg SS (conv_CALL pre near absolute op sel).
Proof. unfold conv_CALL, set_mem32. intros.
  do 3 (conv_agree_outside_seg_one_tac; [conv_agree_outside_seg_tac | idtac]).
  apply set_mem_n_aos_3.
    conv_index_monotone_tac.
    conv_agree_outside_seg_tac.
    intros. unfold conv_JMP. conv_agree_outside_seg_tac.
Qed.  

Hint Resolve CALL_aoss : conv_agree_outside_seg_db.

Lemma dci_aoss :forall ins pre, 
  dir_cflow_instr pre ins = true
    -> agree_outside_seg SS (RTL_step_list (instr_to_rtl pre ins)).
Proof. intros. 
  destruct ins; 
  unfold instr_to_rtl, check_prefix in *;
    (discriminate H || prove_instr).
Qed.

(** ** Showing that non_cflow_instr and dir_cflow_instr does not fail *)

Lemma check_prefix_no_fail_1 : forall pre,
  only_op_override pre = true -> conv_no_fail (check_prefix pre).
Proof. unfold check_prefix. intros.
  unfold only_op_override in H.
  remember_destruct_head in H as lrp; try discriminate.
  remember_destruct_head in H as sp; try discriminate.
  remember_destruct_head in H as aop; try discriminate.
  conv_no_fail_tac.
Qed.

Lemma check_prefix_no_fail_2 : forall pre,
  only_lock_or_rep pre = true -> conv_no_fail (check_prefix pre).
Proof. unfold check_prefix. intros.
  unfold only_lock_or_rep in H.
  destruct (lock_rep pre); try congruence.
  destruct l; try congruence.
  do 3 (destruct_head in H; try congruence).
    conv_no_fail_tac.
  do 3 (destruct_head in H; try congruence).
    conv_no_fail_tac.
Qed.

Lemma check_prefix_no_fail_3 : forall pre,
  only_gs_seg_override pre = true -> conv_no_fail (check_prefix pre).
Proof. unfold check_prefix. intros.
  unfold only_gs_seg_override in H.
  remember_destruct_head in H as sp; try discriminate.
  destruct (seg_override pre).
    destruct s; try discriminate.
    do 2 (remember_destruct_head in H as op; try discriminate).
    conv_no_fail_tac.
    do 2 (remember_destruct_head in H as op; try discriminate).
    conv_no_fail_tac.
Qed.

Lemma check_prefix_no_fail_4 : forall pre,
  either_prefix pre = true -> conv_no_fail (check_prefix pre).
Proof. unfold either_prefix. intros. 
  bool_elim_tac. auto using check_prefix_no_fail_1.
    auto using check_prefix_no_fail_3.
Qed.

Lemma check_prefix_no_fail_5 : forall pre,
  no_prefix pre = true -> conv_no_fail (check_prefix pre).
Proof. unfold no_prefix, check_prefix. intros. 
  do 4 (destruct_head in H; try discriminate).
  conv_no_fail_tac.
Qed.

Hint Resolve check_prefix_no_fail_1 check_prefix_no_fail_2 
  check_prefix_no_fail_3 check_prefix_no_fail_4 
  check_prefix_no_fail_5 : conv_no_fail_db.
  
Lemma nci_no_fail : forall ins pre,
  non_cflow_instr pre ins = true
    -> no_fail (RTL_step_list (instr_to_rtl pre ins)).
(* Admitted. *)
Proof. intros. 
  destruct ins; 
  simpl in H; bool_elim_tac;
  (discriminate H || (unfold instr_to_rtl in *; prove_instr; fail) || idtac).

  (* LEA *)
  unfold instr_to_rtl in *;
  destruct op2; try discriminate.
  bool_elim_tac.  
  match goal with
    | [|- no_fail (RTL_step_list (runConv ?CV))]
      => apply conv_to_rtl_no_fail with (cv:=CV);
         unfold_instr_conv_tac; no_fail_extra_unfold_tac; conv_no_fail_tac
  end.
Qed.

Lemma dci_CALL_pre : forall pre near absolute op1 sel,
  dir_cflow_instr pre (CALL near absolute op1 sel) = true
    -> no_prefix pre = true.
Proof. intros. simpl in H.
  repeat (destruct_head in H; try discriminate).
  destruct op1; try discriminate.
  destruct op1; try discriminate.
  trivial.
Qed.

Lemma dci_JMP_pre : forall pre near absolute op1 sel,
  dir_cflow_instr pre (JMP near absolute op1 sel) = true
    -> no_prefix pre = true.
Proof. intros. simpl in H.
  repeat (destruct_head in H; try discriminate).
  destruct op1; try discriminate.
  destruct op1; try discriminate.
  trivial.
Qed.

Lemma dci_no_fail : forall ins pre, 
  dir_cflow_instr pre ins = true
    -> no_fail (RTL_step_list (instr_to_rtl pre ins)).
Proof. intros. 
  destruct ins; unfold instr_to_rtl in *; try discriminate H.
  Case "Call".
    destruct near. eapply dci_CALL_pre in H. prove_instr. 
    discriminate.
  Case "Jcc". prove_instr.
  Case "JMP".
    destruct near. eapply dci_JMP_pre in H. prove_instr.
      discriminate.
Qed.


