(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

(** X86Lemmas.v. This file holds lemmas about X86 instructions *)

(* Require Import Tacs. *)
Require Import CommonTacs.
Require Import ZArith.
Require Import List.
Require Import Coqlib.
Require Import Bits.
Require Import Decode.
Require Import X86Semantics.
Require Import Monad.
Require Import Int32.
Require Import Eqdep.
Require Import VerifierDFA.
Close Scope char_scope.

Import X86_PARSER.
Import X86_RTL.
Import X86_MACHINE.
Import X86_Compile.

Local Open Scope monad_scope.
Set Implicit Arguments.


Notation get_core_state s := (core (rtl_mach_state s)).

Notation SegStart s seg := (seg_regs_starts (get_core_state s) seg).
Notation SegLimit s seg := (seg_regs_limits (get_core_state s) seg).
Notation PC s := (pc_reg (get_core_state s)).

Notation CStart s := (seg_regs_starts (get_core_state s) CS).
Notation CLimit s := (seg_regs_limits (get_core_state s) CS).
Notation DStart s := (seg_regs_starts (get_core_state s) DS).
Notation DLimit s := (seg_regs_limits (get_core_state s) DS).
Notation SStart s := (seg_regs_starts (get_core_state s) SS).
Notation SLimit s := (seg_regs_limits (get_core_state s) SS).
Notation GStart s := (seg_regs_starts (get_core_state s) GS).
Notation GLimit s := (seg_regs_limits (get_core_state s) GS).
Notation EStart s := (seg_regs_starts (get_core_state s) ES).
Notation ELimit s := (seg_regs_limits (get_core_state s) ES).

(** * Reification of RTL computations *)
Section REIFY_RTL_COMP.

  Local Set Implicit Arguments.

  Inductive rtl_comp : Type -> Type :=
  | rc_ret  (T:Type) (a:T) : rtl_comp T
  | rc_fail (T:Type) : rtl_comp T
  | rc_trap (T:Type) : rtl_comp T
  | rc_get_loc n (l:location n) : rtl_comp (int n)
  | rc_set_loc n (l:location n) (v:int n) : rtl_comp unit
  | rc_get_array n1 n2 (a:array n1 n2) (i:int n1) : rtl_comp (int n2)
  | rc_set_array n1 n2 (a:array n1 n2) (i:int n1) (v:int n2) : rtl_comp unit
  | rc_get_byte (addr:int size_addr) : rtl_comp (int size8)
  | rc_set_byte (addr:int size_addr) (v:int size8) : rtl_comp unit
  | rc_get_random (n:nat) : rtl_comp (int n)
  | rc_advance_oracle : rtl_comp unit
  | rc_interp_rtl_exp n (e:rtl_exp n) : rtl_comp (int n).

  Definition  rtl_comp_denote T (c: rtl_comp T) : RTL T := 
    match c with
      | rc_ret _ a => ret a
      | rc_fail _ => Fail _
      | rc_trap _ => Trap _
      | rc_get_loc _ l => get_loc l
      | rc_set_loc _ l v => set_loc l v
      | rc_get_array _ _ a i => get_array a i
      | rc_set_array _ _ a i v => set_array a i v
      | rc_get_byte addr => get_byte addr
      | rc_set_byte addr v => set_byte addr v
      | rc_get_random n => get_random n
      | rc_advance_oracle => advance_oracle
      | rc_interp_rtl_exp _ e => interp_rtl_exp_comp e
    end.

End REIFY_RTL_COMP.

Ltac reify_rtl_comp c := 
  match c with
    | Return ?A => constr:(rc_ret A)
    | Fail ?T => constr:(rc_fail T)
    | Trap ?T => constr:(rc_trap T)
    | get_loc ?L => constr:(rc_get_loc L)
    | set_loc ?L ?V => constr:(rc_set_loc L V)
    | get_array ?A ?I => constr:(rc_get_array A I)
    | set_array ?A ?I ?V => constr:(rc_set_array A I V)
    | get_byte ?A => constr:(rc_get_byte A)
    | set_byte ?A ?V => constr:(rc_set_byte A V)
    | get_random ?N => constr:(rc_get_random N)
    | advance_oracle => constr:(rc_advance_oracle)
    | interp_rtl_exp_comp ?E => constr:(rc_interp_rtl_exp E)
  end.

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

Lemma rtl_bind_trap_intro1 :
  forall (A B:Type) (c1:RTL A) (f: A -> RTL B) (s1 s2 s1':rtl_state)
    (v':A),
    c1 s1 = (Okay_ans v', s1') -> f v' s1' = (Trap_ans _, s2)
      -> Bind _ c1 f s1 = (Trap_ans _, s2).
Proof. intros. unfold Bind, RTL_monad. rewrite H. trivial. Qed.

Lemma rtl_bind_fail_elim :
  forall (A B:Type) (c1:RTL A) (f: A -> RTL B) (s1 s2:rtl_state),
    Bind _ c1 f s1 = (Fail_ans _, s2)
      -> (c1 s1) = (Fail_ans _, s2) \/
         (exists s1': rtl_state, exists v':A,
            c1 s1 = (Okay_ans v', s1') /\ f v' s1' = (Fail_ans _, s2)).
Proof. intros. unfold Bind, RTL_monad in H.
  destruct (c1 s1) as [r s1']. destruct r as [ | | v']; try discriminate.
    crush. right. crush.
Qed.

(** Find a (v <- op1; op2) s = (Okay_ans v', s') in the context; break it
    using rtl_bind_okay_elim; introduce the intermediate state and value
    into the context; try the input tactic *)
Ltac rtl_okay_break := 
  match goal with
    | [H: Bind _ _ _ ?s = (Okay_ans ?v', ?s') |- _]  => 
      apply rtl_bind_okay_elim in H; 
      let H1 := fresh "H" in let s' := fresh "s" in let v' := fresh "v" in 
        destruct H as [s' [v' [H1 H]]]
  end.

(** Find a (v <- op1; op2) s = Failed in the context; break
    it using rtl_bind_fail_elim to destruct the goal into two cases *)
Ltac rtl_fail_break := 
  match goal with
    | [H: Bind _ _ _ ?s = (Fail_ans _, _) |- _]  => 
      apply rtl_bind_fail_elim in H;
      destruct H as [H|H];
      [idtac|
        let H1 := fresh "H" in let s' := fresh "s" in let v' := fresh "v" in 
        destruct H as [s' [v' [H1 H]]]]
  end.

(** Destruct the head in a match clause *)
Ltac extended_destruct_head c := 
  match c with
    | context[if ?X then _ else _] => destruct X
    | context[match ?X with Some _ => _ | None => _  end] => destruct X
    | context[match ?X with (_, _)  => _ end] => destruct X
    | context[match ?X with nil => _ | Datatypes.cons _ _ => _ end] => destruct X
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

(** * Lemmas about basic operations of instruction semantics.

      Conventions used in lemmas are explained below:
      - Lemmas ending with "_equation" are for instructions that
      always suceed and return the identical state when given an
      initial state; * in addtion, the values they return are
      easy to write down.
      - Lemmas ending with "_exists" are for instructions that
      always succeed and return the same state. But the return
      values are not easy to write down; so we use an existential
      in the lemmas.
 *)

Lemma in_seg_bounds_equation : forall seg a s,
  in_seg_bounds seg a s =
    (Okay_ans (int32_lequ_bool a (SegLimit s seg)), s).
Proof. intros. trivial. Qed.

Lemma in_seg_bounds_rng_equation : forall s sreg a offset,
  in_seg_bounds_rng sreg a offset s = 
    (Okay_ans (andb (int32_lequ_bool a (a +32 offset))
      (int32_lequ_bool (a +32 offset) (SegLimit s sreg))), s).
Proof. trivial. Qed.

(*
Lemma fetch_n_exists : forall (n:nat) (pc:int32) (s:rtl_state),
  exists bytes, fetch_n_rtl n pc s = (Okay_ans bytes, s).
Proof. unfold fetch_n_rtl. intros. exists (fetch_n n pc s). trivial. Qed.
*)

Ltac rtl_comp_elim_L1 :=
  let unfold_rtl_monad H :=
    unfold Bind at 1 in H; unfold RTL_monad at 1 in H
  in match goal with
    | [H: Return ?v ?s = _ |- _] =>
      compute [Return Bind RTL_monad] in H
    | [H: Trap _ _ = _ |- _] =>
      compute [Trap] in H
    | [H: interp_rtl_exp_comp _ _ = _ |- _] => inv H
    | [H: interp_rtl ?I _ = _ |- _] => 
      match I with
        | set_loc_rtl _ _ _ => compute [interp_rtl] in H
        | set_array_rtl _ _ _ _ _ => compute [interp_rtl] in H
        | set_byte_rtl _ _ => compute [interp_rtl] in H
        | advance_oracle_rtl => compute [interp_rtl] in H
        | if_rtl _ _ => compute [interp_rtl] in H
        | error_rtl => compute [interp_rtl] in H
        | trap_rtl => compute [interp_rtl] in H
      end
    | [H: Bind _ (get_loc _) _ _ = _ |- _] =>
      unfold_rtl_monad H; compute [get_loc get_location] in H
    | [H: Bind _ (in_seg_bounds _ _) _ _ = _ |- _] =>
      unfold_rtl_monad H; rewrite in_seg_bounds_equation in H
    | [H: Bind _ (in_seg_bounds_rng _ _ _) _ _ = _ |- _] =>
      unfold_rtl_monad H; rewrite in_seg_bounds_rng_equation in H
    | [H: Bind _ (Return _) _ _ = _ |- _] =>
      unfold_rtl_monad H; compute [Return Bind RTL_monad] in H
(* *)
(*     | [H: Bind _ (fetch_n_rtl ?n ?pc) _ ?s = _ |- _] => *)
(*       let name := fresh "bytes" in *)
(*         rtl_comp_elim_exist H (fetch_n_exists n pc s) name *)
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
      | (Trap_ans _, _) = (Okay_ans _, _) => inversion H
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
  destruct_head in H. crush.
Qed.

(* todo: remove *)
(* Ltac conv_break :=  *)
(*   match goal with *)
(*     | [H: Bind _ _ _ ?cs = (?v', ?cs') |- _]  =>  *)
(*       apply conv_bind_elim in H; *)
(*       let H1 := fresh "H" in let cs1 := fresh "cs" in let v1 := fresh "v" in  *)
(*         destruct H as [cs1 [v1 [H1 H]]] *)
(*   end. *)

Ltac conv_elim := 
  unfold write_byte in *;
  match goal with
      | [H: (emit _ ) ?CS = _ |- _] => 
        match type of CS with 
          | conv_state => compute [EMIT] in H; inversion H; subst; clear H
        end
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

(** * A general framework for proving properties of instructions:

   - Module type [RTL_STATE_REL] provides the abstraction of a relation 
     between two RTL states, e.g., the two states have the same segment 
     registers.
   - Module type [RTL_PROP] provides the abstraction of a property about
     RTL computations.
   - Functor [RTL_Prop] takes a [RTL_STATE_REL] module and lifts the 
     relation to a property about RTL compuations.
   - Functor [Conv_Prop] takes a [RTL_Prop] module and lifts the 
     property to a property about RTL conversions.
*)

Module Type RTL_STATE_REL.
  (** A binary relation that relates two RTL states *)
  Parameter brel : rtl_state -> rtl_state -> Prop.
  (** The relation is reflexive and transitive *)
  Axiom brel_refl : forall s, brel s s.
  Axiom brel_trans : forall s1 s2 s3, brel s1 s2 -> brel s2 s3 -> brel s1 s3.
End RTL_STATE_REL.

Module Type RTL_PROP.
  (** A property about RTL compuation *)
  Parameter rtl_prop : forall (A:Type), RTL A -> Prop.

  Axiom bind_sat_prop : forall (A B:Type) (c1:RTL A) (f:A -> RTL B), 
    rtl_prop c1 -> (forall a:A, rtl_prop (f a))
      -> rtl_prop (Bind _ c1 f).
  Axiom ret_sat_prop : forall (A:Type) (a:A), rtl_prop (Return a).

End RTL_PROP.

Module RTL_Prop (R:RTL_STATE_REL) <: RTL_PROP.

  (** Lift the relation to a property on a RTL computation *)
  Definition rtl_prop (A:Type) (c:RTL A) := 
    forall s s' v', c s = (Okay_ans v', s') -> R.brel s s'.

  (** To prove "Bind _ c1 f" satisfies a RTL-computation property, it is
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

  Lemma trap_sat_prop : forall (A:Type), rtl_prop (Trap A).
  Proof. unfold rtl_prop. intros. inversion H. Qed.

End RTL_Prop.

Module Conv_Prop (RP: RTL_PROP).
  Import RP.

  (** Lift a property about a RTL computation to a property about a
   conversion from an x86 instruction to a list of RTL instructions. It
   says that if the computation for the input RTL-instruction list satifies
   the property, and after conversion the output RTL-instruction list also
   satisifies the property. *)
  Definition conv_prop (A:Type) (cv:Conv A) := 
    forall cs (v:A) cs',
      cv cs = (v, cs')
        -> rtl_prop (RTL_step_list (List.rev (c_rev_i cs)))
        -> rtl_prop (RTL_step_list (List.rev (c_rev_i cs'))).

  Lemma conv_to_rtl_prop: forall cv,
    conv_prop cv -> rtl_prop (RTL_step_list (runConv cv)).
  Proof. unfold conv_prop, runConv. intros.
    remember_rev (cv {|c_rev_i := nil|}) as cva.
    destruct cva.
    apply H in Hcva. crush.
      compute [c_rev_i rev RTL_step_list]. apply ret_sat_prop.
  Qed.

  Lemma bind_sat_conv_prop : forall (A B:Type) (cv: Conv A) (f:A -> Conv B),
    conv_prop cv -> (forall a:A, conv_prop (f a)) -> conv_prop (Bind _ cv f).
  Proof. unfold conv_prop. intros. conv_elim. eauto. Qed.

  Lemma ret_sat_conv_prop : forall (A:Type) (r:A), 
    conv_prop (ret r).
  Proof. unfold conv_prop. crush. Qed.

  Lemma emit_sat_conv_prop : forall i,
    rtl_prop (interp_rtl i) -> conv_prop (emit i).
  Proof. unfold conv_prop, EMIT. intros.
    crush. autorewrite with step_list_db.
    apply bind_sat_prop. assumption.
      intros. apply bind_sat_prop. assumption.
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

(** * Properties about RTL computations *)

(** ** Property that an RTL computation preserves [rtl_state] *)

Module Same_RTL_State_Rel <: RTL_STATE_REL.
  Definition brel (s1 s2 : rtl_state) := s1 = s2.

  Lemma brel_refl : forall s, brel s s.
  Proof. unfold brel. trivial. Qed.

  Lemma brel_trans : forall s1 s2 s3, brel s1 s2 -> brel s2 s3 -> brel s1 s3.
  Proof. unfold brel. crush. Qed.
End Same_RTL_State_Rel.

Module Same_RTL_State := RTL_Prop Same_RTL_State_Rel.
Notation same_rtl_state := Same_RTL_State.rtl_prop.

(* rtl_prop_unfold_db is an unfold database when we develop lemmas about  *)
(* RTL instructions *)
Hint Unfold same_rtl_state Same_RTL_State_Rel.brel : rtl_prop_unfold_db.

Local Ltac rtl_prop_prover :=
  autounfold with rtl_prop_unfold_db ; simpl;
  unfold set_byte, get_byte, set_loc, get_loc, set_array, get_array, 
    get_random, advance_oracle, interp_rtl_exp_comp, Fail, Trap;
  crush.

(* the ordering of matches is important for the following tactic *)
Ltac same_rtl_state_tac :=
  repeat (match goal with
            | [|- same_rtl_state (Bind _ _ _)] =>
              apply Same_RTL_State.bind_sat_prop; [idtac | intros]
            | [|- same_rtl_state ?c] => extended_destruct_head c
            | [|- same_rtl_state _] => auto with same_rtl_state_db
          end).

(** A decision procedure for checking if a RTL computation does not
    change the rtl state *)
Definition check_same_rtl_state T (rc:rtl_comp T) : bool := 
  match rc with
    | rc_ret _ _ | rc_fail _ | rc_trap _ | rc_get_loc _ _ 
    | rc_get_array _ _ _ _ 
    | rc_get_byte _ | rc_get_random _  
    | rc_interp_rtl_exp _ _ => true
    | _ => false
  end.

Lemma check_same_rtl_state_sound : forall T (rc: rtl_comp T),
  check_same_rtl_state rc = true -> same_rtl_state (rtl_comp_denote rc).
Proof. destruct rc; try (discriminate H || rtl_prop_prover; fail). Qed.

(* A reflection based tactic to check if a basic rtl computation satisfies
   [same_rtl_state]. Not stricitly necessary here; alternatively, we can
   also put in lemmas about those rcl computations into the hint database;
   but that requires we state those lemmas explicitly.  *)
Hint Extern 2 (same_rtl_state ?C) =>
  let rc:= reify_rtl_comp C in
  change (same_rtl_state (rtl_comp_denote rc));
  apply check_same_rtl_state_sound; trivial : same_rtl_state_db.

(** ** Property that an RTL computation preserves [rtl_mach_state] *)
Module Same_Mach_State_Rel <: RTL_STATE_REL.
  Definition brel (s1 s2 : rtl_state) :=
    rtl_mach_state s1 = rtl_mach_state s2.

  Lemma brel_refl : forall s, brel s s.
  Proof. unfold brel. trivial. Qed.

  Lemma brel_trans : forall s1 s2 s3, brel s1 s2 -> brel s2 s3 -> brel s1 s3.
  Proof. unfold brel. crush. Qed.
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

Definition check_same_mach_state T (rc:rtl_comp T) : bool := 
  match rc with
    | rc_ret _ _ | rc_fail _ | rc_trap _ | rc_get_loc _ _ 
    | rc_get_array _ _ _ _ 
    | rc_get_byte _ | rc_set_byte _ _ | rc_get_random _ 
    | rc_advance_oracle
    | rc_interp_rtl_exp _ _ => true
    | _ => false
  end.

Lemma check_same_mach_state_sound : forall T (rc: rtl_comp T),
  check_same_mach_state rc = true -> same_mach_state (rtl_comp_denote rc).
Proof. destruct rc; try (discriminate H || rtl_prop_prover; fail). Qed.

Hint Extern 2 (same_mach_state ?C) =>
  let rc:= reify_rtl_comp C in
  change (same_mach_state (rtl_comp_denote rc));
  apply check_same_mach_state_sound; trivial : same_mach_state_db.

Lemma same_rtl_state_same_mach_state : forall (A:Type) (c:RTL A),
  same_rtl_state c -> same_mach_state c.
Proof. unfold same_mach_state, Same_Mach_State_Rel.brel.
  unfold same_rtl_state, Same_RTL_State_Rel.brel.
  intros. apply H in H0. subst s'.
  trivial.
Qed.

(** ** Property that an RTL computation preserves the core state *)
Module Same_Core_State_Rel <: RTL_STATE_REL.
  Definition brel (s1 s2 : rtl_state) :=
    core (rtl_mach_state s1) = core (rtl_mach_state s2).

  Lemma brel_refl : forall s, brel s s.
  Proof. unfold brel. trivial. Qed.

  Lemma brel_trans : forall s1 s2 s3, brel s1 s2 -> brel s2 s3 -> brel s1 s3.
  Proof. unfold brel. crush. Qed.
End Same_Core_State_Rel.

Module Same_Core_State := RTL_Prop Same_Core_State_Rel.
Notation same_core_state := Same_Core_State.rtl_prop.

Hint Unfold same_core_state Same_Core_State_Rel.brel : rtl_prop_unfold_db.

Ltac same_core_state_tac :=
  compute [interp_rtl]; fold interp_rtl;
  repeat (match goal with
            | [|- same_core_state (Bind _ _ _)] =>
              apply Same_Core_State.bind_sat_prop; [idtac | intros]
            | [|- same_core_state ?c] => extended_destruct_head c
            | [|- same_core_state _] => auto with same_core_state_db
          end).

Definition check_same_core_state T (rc:rtl_comp T) : bool := 
  match rc with
    | rc_ret _ _ | rc_fail _ | rc_trap _ | rc_get_loc _ _ 
    | rc_get_array _ _ _ _ | rc_set_array _ _ _ _ _
    | rc_get_byte _ | rc_set_byte _ _
    | rc_get_random _ | rc_advance_oracle
    | rc_interp_rtl_exp _ _ => true
    | _ => false
  end.

Lemma same_mach_state_same_core_state : forall (A:Type) (c:RTL A),
  same_mach_state c -> same_core_state c.
Proof. autounfold with rtl_prop_unfold_db. crush_hyp. Qed.

Lemma check_same_core_state_sound : forall T (rc: rtl_comp T),
  check_same_core_state rc = true -> same_core_state (rtl_comp_denote rc).
Proof. 
  intros; destruct rc; simpl; try (discriminate H || rtl_prop_prover; fail). 
  destruct a; rtl_prop_prover.  
Qed.

Hint Extern 2 (same_core_state ?C) =>
  let rc:= reify_rtl_comp C in
  change (same_core_state (rtl_comp_denote rc));
  apply check_same_core_state_sound; trivial : same_core_state_db.

(** ** Property that an RTL computation preserves values in seg registers *)

Module Same_Seg_Regs_Rel <: RTL_STATE_REL.
  Definition brel (s1 s2 : rtl_state) :=
    seg_regs_starts (get_core_state s1) = seg_regs_starts (get_core_state s2) /\
    seg_regs_limits (get_core_state s1) = seg_regs_limits (get_core_state s2).
  
  Lemma brel_refl : forall s, brel s s.
  Proof. unfold brel; intros. tauto. Qed.

  Lemma brel_trans : forall s1 s2 s3, brel s1 s2 -> brel s2 s3 -> brel s1 s3.
  Proof. unfold brel. crush. Qed.
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

Lemma same_core_state_same_seg_regs : forall (A:Type) (c:RTL A),
  same_core_state c -> same_seg_regs c.
Proof. autounfold with rtl_prop_unfold_db. crush_hyp. Qed.

Lemma same_mach_state_same_seg_regs : forall (A:Type) (c:RTL A),
  same_mach_state c -> same_seg_regs c.
Proof. autounfold with rtl_prop_unfold_db. crush_hyp.
Qed.

Lemma same_rtl_state_same_seg_regs : forall (A:Type) (c:RTL A),
  same_rtl_state c -> same_seg_regs c.
Proof. autounfold with rtl_prop_unfold_db. crush_hyp. Qed.

Definition is_seg_reg_loc (s:nat) (l:loc s) :=
  match l with
    | seg_reg_start_loc seg => true
    | seg_reg_limit_loc seg => true
    | _ => false
  end.

Lemma set_loc_same_seg_regs : forall s (l:location s) v,
  is_seg_reg_loc l = false -> same_seg_regs (set_loc l v).
Proof. autounfold with rtl_prop_unfold_db.  unfold set_loc.
  intros; destruct l; crush.
Qed.

Definition check_same_seg_regs T (rc:rtl_comp T) : bool := 
  match rc with
    | rc_ret _ _ | rc_fail _ | rc_trap _ | rc_get_loc _ _ 
    | rc_get_array _ _ _ _ | rc_set_array _ _ _ _ _
    | rc_get_byte _ | rc_set_byte _ _
    | rc_get_random _ | rc_advance_oracle
    | rc_interp_rtl_exp _ _ => true
    | rc_set_loc _ l _ => negb (is_seg_reg_loc l)
  end.

Lemma check_same_seg_regs_sound : forall T (rc: rtl_comp T),
  check_same_seg_regs rc = true -> same_seg_regs (rtl_comp_denote rc).
Proof. destruct rc; intros; try (discriminate H || rtl_prop_prover; fail).
  simpl in H; bool_elim_tac; simpl; auto using set_loc_same_seg_regs.
  apply same_core_state_same_seg_regs; simpl; auto with same_core_state_db.
Qed.

(* try the decision procedure on basic rtl computations *)
Hint Extern 2 (same_seg_regs ?C) =>
  let rc:= reify_rtl_comp C in
  change (same_seg_regs (rtl_comp_denote rc));
  apply check_same_seg_regs_sound; trivial : same_seg_regs_db.

(** ** Property that an RTL computation does not change the pc register *)

Module Same_PC_Rel <: RTL_STATE_REL.
  Definition brel (s1 s2 : rtl_state) := 
    pc_reg (get_core_state s1) = pc_reg (get_core_state s2).

  Lemma brel_refl : forall s, brel s s.
  Proof. unfold brel; intros. tauto. Qed.

  Lemma brel_trans : forall s1 s2 s3, brel s1 s2 -> brel s2 s3 -> brel s1 s3.
  Proof. unfold brel. crush. Qed.
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

Definition is_pc_loc (s:nat) (l:loc s) :=
  match l with
    | pc_loc => true
    | _ => false
  end.

Definition check_same_pc T (rc:rtl_comp T) : bool := 
  match rc with
    | rc_ret _ _ | rc_fail _ | rc_trap _ | rc_get_loc _ _ 
    | rc_get_array _ _ _ _ 
    | rc_get_byte _ | rc_set_byte _ _
    | rc_get_random _ | rc_advance_oracle
    | rc_interp_rtl_exp _ _ => true
    | rc_set_loc _ l _ => negb (is_pc_loc l)
    | _ => false
  end.

Lemma set_loc_same_pc : forall s (l:location s) v,
  is_pc_loc l = false -> same_pc (set_loc l v).
Proof. autounfold with rtl_prop_unfold_db.  unfold set_loc. intros. 
  destruct l; crush.
Qed.  

Lemma same_mach_state_same_pc : forall (A:Type) (c:RTL A), 
  same_mach_state c -> same_pc c.
Proof. autounfold with rtl_prop_unfold_db. crush_hyp. Qed.

Lemma check_same_pc_sound : forall T (rc: rtl_comp T),
  check_same_pc rc = true -> same_pc (rtl_comp_denote rc).
Proof. intros; destruct rc; try (discriminate H || rtl_prop_prover; fail). 
  simpl in H; bool_elim_tac; simpl; auto using set_loc_same_pc.
Qed.

Hint Extern 2 (same_pc ?C) =>
  let rc:= reify_rtl_comp C in
  change (same_pc (rtl_comp_denote rc));
  apply check_same_pc_sound; trivial : same_pc_db.


(** ** Property that an RTL computation preserves the memory *)
Module Same_Mem_Rel <: RTL_STATE_REL.
  Definition brel (s1 s2 : rtl_state) := rtl_memory s1 = rtl_memory s2.

  Lemma brel_refl : forall s, brel s s.
  Proof. unfold brel; intros. tauto. Qed.

  Lemma brel_trans : forall s1 s2 s3, brel s1 s2 -> brel s2 s3 -> brel s1 s3.
  Proof. unfold brel. crush. Qed.
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

Definition check_same_mem T (rc:rtl_comp T) : bool := 
  match rc with
    | rc_ret _ _ | rc_fail _ | rc_trap _
    | rc_get_loc _ _  | rc_set_loc _ _ _
    | rc_get_array _ _ _ _ | rc_set_array _ _ _ _ _
    | rc_get_byte _ 
    | rc_get_random _ | rc_advance_oracle
    | rc_interp_rtl_exp _ _ => true
    | _ => false
  end.

Lemma same_rtl_state_same_mem : forall (A:Type) (c:RTL A), 
  same_rtl_state c -> same_mem c.
Proof. autounfold with rtl_prop_unfold_db.
  intros. apply H in H0. subst s'. trivial. 
Qed.

Lemma check_same_mem_sound : forall T (rc: rtl_comp T),
  check_same_mem rc = true -> same_mem (rtl_comp_denote rc).
Proof. 
  intros; destruct rc; try (discriminate H || rtl_prop_prover; fail). 
Qed.

Hint Extern 2 (same_mem ?C) =>
  let rc:= reify_rtl_comp C in
  change (same_mem (rtl_comp_denote rc));
  apply check_same_mem_sound; trivial : same_mem_db.

(** ** A state relation about agreeing over/outside a memory region *)
Definition agree_over_addr_region (r:Int32Ensemble) (s s':rtl_state) : Prop :=
  forall l:int32, Ensembles.In _ r l -> 
     AddrMap.get l (rtl_memory s) = AddrMap.get l (rtl_memory s').

Definition agree_outside_addr_region (r:Int32Ensemble) (s s':rtl_state) :=
  forall l:int32, ~ (Ensembles.In _ r l) -> 
     AddrMap.get l (rtl_memory s) = AddrMap.get l (rtl_memory s').

Lemma agree_over_addr_region_e : forall r s s' l,
  agree_over_addr_region r s s' -> Ensembles.In _ r l
    -> AddrMap.get l (rtl_memory s) = AddrMap.get l (rtl_memory s').
Proof. crush. Qed.

Lemma agree_outsie_addr_region_e : forall r s s' l,
  agree_outside_addr_region r s s' -> ~ Ensembles.In _ r l
    -> AddrMap.get l (rtl_memory s) = AddrMap.get l (rtl_memory s').
Proof. crush. Qed.

Lemma agree_over_addr_region_refl : forall r s,
  agree_over_addr_region r s s.
Proof. crush. Qed.

Lemma agree_over_addr_region_trans : forall r s1 s2 s3,
  agree_over_addr_region r s1 s2 -> agree_over_addr_region r s2 s3
    -> agree_over_addr_region r s1 s3.
Proof. unfold agree_over_addr_region. intros. crush. Qed.

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
Proof. crush. Qed.

Lemma agree_outside_addr_region_trans : forall s1 s2 s3 r,
  agree_outside_addr_region r s1 s2
    -> agree_outside_addr_region r s2 s3
    -> agree_outside_addr_region r s1 s3.
Proof. unfold agree_outside_addr_region. intros. crush. Qed.

Lemma same_mem_agree_outside : forall s s' r,
  rtl_memory s = rtl_memory s' -> agree_outside_addr_region r s s'.
Proof. intros. unfold agree_outside_addr_region. intros. congruence. Qed.

(** ** Property that an RTL computation preserves memory outside of a segment.
   This property needs to be parametrized over the segment register. ML's
   module system, however, can only parametrize over modules.  *)

Definition segAddrs (seg:segment_register) (s:rtl_state) : Int32Ensemble :=
  addrRegion (SegStart s seg) (SegLimit s seg).

(* Without the first two conditions, it would no be transitive *)
Definition agree_outside_seg (seg:segment_register) (A:Type) (c:RTL A) :=
  forall s s' v', c s = (Okay_ans v', s') -> 
    SegStart s seg = SegStart s' seg /\
    SegLimit s seg = SegLimit s' seg /\
    agree_outside_addr_region (segAddrs seg s) s s'.

Lemma bind_agree_outside_seg :
  forall (seg:segment_register) (A B:Type) (c1:RTL A) (f: A -> RTL B),
    agree_outside_seg seg c1
      -> (forall a:A, agree_outside_seg seg (f a))
      -> agree_outside_seg seg (Bind _ c1 f).
Proof. unfold agree_outside_seg. intros.
  rtl_okay_break.
  apply H in H2. apply H0 in H1.
  assert (segAddrs seg s = segAddrs seg s0) as H10.
    unfold segAddrs. crush.
  rewrite H10 in *.
  split. crush. split. crush.
  eapply agree_outside_addr_region_trans with (s2:= s0); crush.
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
  crush.
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

(*
(** ** Lemmas about same_regs *)
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

(*
(** ** Lemmas about same_regs_but *)

(** r is not the same as op *)
Definition reg_eq_operand (r:register) (op:operand) : bool := 
  match op with
    | Reg_op r' => register_eq_dec r' r
    | _ => false
  end.

(** s and s' have the same register values except for the possible 
    register in op *)
*)
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


(** ** Property that an RTL computation does not raise an error *)

Definition no_fail (A:Type) (c:RTL A) := 
  forall s s', c s <> (Fail_ans _, s').

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

Definition check_no_fail T (rc:rtl_comp T) : bool := 
  match rc with
    | rc_ret _ _ | rc_trap _
    | rc_get_loc _ _  | rc_set_loc _ _ _
    | rc_get_array _ _ _ _ | rc_set_array _ _ _ _ _
    | rc_get_byte _ | rc_set_byte _ _ 
    | rc_get_random _ | rc_advance_oracle
    | rc_interp_rtl_exp _ _  => true
    | _ => false
  end.

Lemma check_no_fail_sound : forall T (rc: rtl_comp T),
  check_no_fail rc = true -> no_fail (rtl_comp_denote rc).
Proof. intros; destruct rc; try (discriminate || rtl_prop_prover; fail). Qed.

Hint Extern 2 (no_fail ?C) =>
  let rc:= reify_rtl_comp C in
  change (no_fail (rtl_comp_denote rc));
  apply check_no_fail_sound; trivial : no_fail_db.

(** ** Lemmas about inBoundCodeAddr *)

Definition inBoundCodeAddr (pc:int32) (s:rtl_state) := 
  pc <=32 CLimit s.

Lemma step_fail_pc_inBound : forall s s',
  step s = (Fail_ans unit, s') -> inBoundCodeAddr (PC s) s.
Proof. unfold step. intros.
  do 2 rtl_comp_elim_L1.
  remember_destruct_head in H as irng.
    clear H. unfold inBoundCodeAddr. crush.
    discriminate.
Qed.

Lemma step_immed_pc_inBound : forall s s',
  s ==> s' -> inBoundCodeAddr (PC s) s.
Proof. unfold step_immed, step. intros.
  do 2 rtl_okay_elim.
  remember_destruct_head in H as irng.
    clear H.
    unfold inBoundCodeAddr. crush.
    discriminate.
Qed.

(*
Lemma inBoundCodeAddr_equiv : forall s s' pc,
  state_same_seg_regs s s' -> inBoundCodeAddr pc s -> inBoundCodeAddr pc s'.
Proof. unfold inBoundCodeAddr; intros. destruct H. congruence. Qed.
*)

(** ** Lemmas about fetch_n *)
Lemma fetch_n_length : forall n pc s,
  length (fetch_n n pc s) = n.
Proof. induction n; crush. Qed.

Lemma fetch_n_sound : forall n pc s bytes k,
  fetch_n n pc s = bytes
    -> (0 <= k < n)%nat
    -> nth k bytes zero = (AddrMap.get (pc +32_n k) (rtl_memory s)).
Proof. induction n.
  Case "n=0". crush.
  Case "S n". intros.
    assert (k = 0 \/ k > 0)%nat as H10.
      generalize (le_lt_or_eq 0 k); crush.
    simpl in H; subst bytes.
    destruct H10.
    SCase "k=0". 
      subst k. rewrite add32_zero_r. crush.
    SCase "k>0".
      assert (0 <= k-1 < n)%nat by omega.
      rewrite cons_nth by assumption.
      erewrite IHn by trivial.
      unfold "+32". rewrite add_assoc. rewrite add_repr.
      assert (1 + Z_of_nat (k-1) = Z_of_nat k).
        rewrite inj_minus1 by omega. ring.
      crush.
Qed.    

(*
(** * upd_get lemmas *)
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

(** * Proving properties about RTL conversions *)

(** ** An unfolding database for proving properties of RTL conversions *)

Hint Unfold load_Z load_int arith test load_reg set_reg cast_u cast_s
  get_seg_start get_seg_limit read_byte write_byte get_flag set_flag
  get_pc set_pc copy_ps read_loc write_loc if_exp raise_error raise_trap 
  no_op choose if_trap:
  conv_unfold_db.

(** ** Property that a conversion preserves [same_seg_regs] *)

Module Conv_Same_Seg_Regs := Conv_Prop Same_Seg_Regs.
Notation conv_same_seg_regs := Conv_Same_Seg_Regs.conv_prop.

Hint Extern 1 (conv_same_seg_regs (emit _)) => 
  apply Conv_Same_Seg_Regs.emit_sat_conv_prop; same_seg_regs_tac : conv_same_seg_regs_db.

Hint Resolve Conv_Same_Seg_Regs.ret_sat_conv_prop : conv_same_seg_regs_db.

Ltac conv_same_seg_regs_tac := 
  repeat autounfold with conv_unfold_db;
  repeat (match goal with
            | [|- conv_same_seg_regs (Bind _ _ _)] => 
              apply Conv_Same_Seg_Regs.bind_sat_conv_prop; [idtac | intros]
            | [|- conv_same_seg_regs ?c] => extended_destruct_head c
            | [|- conv_same_seg_regs _] => auto with conv_same_seg_regs_db
          end).


(** Lemmas for many conversion primitives can be proved by simply unfolding
   their definitions and use the above conv_same_seg_regs_tac. However, there
   are two cases when we want to state a separate lemma about a conversion
   primitive and check the lemma into the hint databse:
   - Some lemmas need manual intervention to prove, for example, 
       induction-based proofs.
   - If a primitive is used quite often in definitions, it is good to
       state a separate lemma for it; after it is declared in the hint db, 
       it provides a shortcut in the proof search;
       for instance, lemmas about iload_op8, iload_op16, iload_32 and load_op
       are added for this reason. Those could be proved by just unfolding them. 
       But in conv_DIV for example, if we did that, the amount of time to prove
       conv_same_seg_regs (conv_DIV ...) would be an order of magnitiude more.
 *)

Lemma load_mem_n_same_seg_regs : forall seg addr n,
  conv_same_seg_regs (load_mem_n seg addr n).
Proof. unfold load_mem_n, lmem, add_and_check_segment, if_trap.
  induction n. 
    conv_same_seg_regs_tac.
    fold load_mem_n in *. conv_same_seg_regs_tac.
Qed.

Hint Extern 1 (conv_same_seg_regs (load_mem_n _ _ ?X))
  =>  apply load_mem_n_same_seg_regs with (n:=X)
  : conv_same_seg_regs_db.

Lemma set_mem_n_same_seg_regs : forall n seg (v:rtl_exp (8*(n+1)-1)) addr,
  conv_same_seg_regs (set_mem_n seg v addr).
Proof. unfold set_mem_n, smem, add_and_check_segment, if_trap.
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


Lemma set_op_same_seg_regs : forall p w seg r op,
  conv_same_seg_regs (set_op p w seg r op).
Proof. unfold set_op, iset_op32, iset_op16, iset_op8.
  unfold set_mem32, set_mem16, set_mem8, compute_addr, raise_error.
  intros.
  destruct (op_override p); destruct w;
  conv_same_seg_regs_tac.
Qed.

Hint Immediate set_op_same_seg_regs : conv_same_seg_regs_db.

Lemma conv_BS_aux_same_seg_regs : forall s d n (op:rtl_exp s),
  conv_same_seg_regs (conv_BS_aux d n op).
Proof. unfold conv_BS_aux.  
  induction n; intros; conv_same_seg_regs_tac.
Qed.

Lemma compute_parity_aux_same_seg_regs : forall s (op1:rtl_exp s) op2 n,
  conv_same_seg_regs (compute_parity_aux op1 op2 n).
Proof. induction n. simpl. conv_same_seg_regs_tac.
  unfold compute_parity_aux. fold (@compute_parity_aux s).
  conv_same_seg_regs_tac.
Qed.

Hint Immediate conv_BS_aux_same_seg_regs compute_parity_aux_same_seg_regs :
  conv_same_seg_regs_db.

(** ** Property that a conversion preserves [same_mem] *)

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

(** ** Properthat that a conversion preserves [agree_outside_data_seg] *)
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
  remember_rev (cv {| c_rev_i := nil |}) as cva.
  destruct cva.
  apply H in Hcva. crush.
    compute [c_rev_i rev RTL_step_list].
    agree_outside_seg_tac.
Qed.

Lemma bind_conv_aos : forall seg (A B:Type) (cv: Conv A) (f:A -> Conv B),
  conv_agree_outside_seg seg cv
    -> (forall a:A, conv_agree_outside_seg seg (f a))
    -> conv_agree_outside_seg seg (Bind _ cv f).
Proof. unfold conv_agree_outside_seg. intros. conv_elim. eauto. Qed.

Lemma emit_conv_aos : forall seg i,
  agree_outside_seg seg (interp_rtl i)
    -> conv_agree_outside_seg seg (emit i).
Proof. unfold conv_agree_outside_seg, EMIT. intros.
  crush. autorewrite with step_list_db.
  agree_outside_seg_tac.
Qed.

Hint Extern 1 (conv_agree_outside_seg _ (emit _)) => 
  apply emit_conv_aos; agree_outside_seg_tac
    : conv_agree_outside_seg_db.

Lemma ret_conv_aos : forall seg (A:Type) (r:A), 
  conv_agree_outside_seg seg (ret r).
Proof. unfold conv_agree_outside_seg. crush. Qed.

Hint Resolve ret_conv_aos : conv_agree_outside_seg_db.

Ltac conv_agree_outside_seg_one_tac :=
  match goal with
    | [|- conv_agree_outside_seg _ (Bind _ _ _)] => 
      apply bind_conv_aos; [idtac | intros]
    | [|- conv_agree_outside_seg _ ?c] => extended_destruct_head c
    | [|- conv_agree_outside_seg _ _]
      => eauto with conv_agree_outside_seg_db
  end.

Ltac conv_agree_outside_seg_tac := 
  repeat autounfold with conv_unfold_db;
  repeat conv_agree_outside_seg_one_tac.

Lemma add_and_check_safe : forall seg addr cs r cs' s v' s', 
  add_and_check_segment seg addr cs = (r, cs')
    -> RTL_step_list (List.rev (c_rev_i cs')) s = (Okay_ans v', s')
    -> Ensembles.In _ (segAddrs seg s') (interp_rtl_exp r s').
Proof. intros.
  unfold add_and_check_segment in H.
  conv_backward.
  repeat rtl_okay_elim. removeUnit.
  remember_destruct_head in H1 as chk.
  Case "test fails". discriminate.
  Case "test succeeds".
    repeat rtl_okay_elim.
    unfold segAddrs, Ensembles.In, addrRegion.
    exists (interp_rtl_exp addr s2).
    split. trivial.
      apply int_eq_false_iff2 in Hchk.
      compute [interp_test] in Hchk.
      remember_destruct_head in Hchk as ltu; try congruence.
      all_to_Z_tac. apply Zge_le. assumption.
Qed.


Lemma smem_aos : forall seg v addr,
  conv_agree_outside_seg seg (smem seg v addr).
Proof. unfold smem, conv_agree_outside_seg. intros.
  repeat conv_elim.
  simpl. autorewrite with step_list_db.
  assert (conv_agree_outside_seg seg (add_and_check_segment seg addr))
    as H10.
    unfold add_and_check_segment.
    conv_agree_outside_seg_tac.
  unfold agree_outside_seg. intros.
  repeat rtl_okay_elim. simpl. removeUnit. 
  unfold conv_agree_outside_seg in H10. 
  use_lemma H10 by eassumption.
  unfold agree_outside_seg in H.
  use_lemma H by eassumption.
  assert (Ensembles.In _ (segAddrs seg s0) (interp_rtl_exp v1 s0)) as H12.
    eapply add_and_check_safe; eassumption.
  assert (segAddrs seg s0 = segAddrs seg s) as H14.
    unfold segAddrs. 
    crush.
  rewrite H14 in H12.
  assert (SegStart s0 seg = SegStart s1 seg /\
          SegLimit s0 seg = SegLimit s1 seg).
    inv H3. simpl. crush.
  assert (agree_outside_addr_region (segAddrs seg s) s0 s1).
    unfold agree_outside_addr_region; intros.
    unfold set_byte in H3. crush.
    rewrite AddrMap.gso; [trivial | contradict H12; subst; trivial].
  crush.
    apply agree_outside_addr_region_trans with (s2:=s0); crush.
Qed.

Hint Resolve smem_aos : conv_agree_outside_seg_db.

Ltac conv_backward_aos :=
  match goal with
    [H: ?cv ?cs = (_, ?cs') |- 
      agree_outside_seg _ (RTL_step_list (rev (c_rev_i ?cs')))]
      => eapply conv_agree_outside_seg_e; 
        [eassumption | conv_agree_outside_seg_tac | idtac]
  end.

Lemma set_mem_n_aos :
  forall n seg (v:rtl_exp (8*(n+1)-1)) addr,
    conv_agree_outside_seg seg (@set_mem_n n seg v addr).
Proof. induction n; intros.
  Case "n=0". simpl. conv_agree_outside_seg_tac.
  Case "S n". unfold set_mem_n. fold (@ set_mem_n n).
    conv_agree_outside_seg_tac.
Qed.
Hint Resolve set_mem_n_aos : conv_agree_outside_seg_db.

Definition seg_eq (seg1 seg2 : segment_register) := seg1 = seg2.

Lemma seg_eq_refl : forall seg, seg_eq seg seg. 
Proof. crush. Qed.

Hint Resolve seg_eq_refl : conv_agree_outside_seg_db.

Lemma iset_op32_aos : forall seg1 seg2 pre op,
  seg_eq seg1 seg2 -> conv_agree_outside_seg seg1 (iset_op32 seg2 pre op).
Proof. unfold seg_eq, iset_op32, compute_addr, set_mem32. 
  intros. subst.
  destruct op; conv_agree_outside_seg_tac.
Qed.

Lemma iset_op16_aos : forall seg1 seg2 pre op,
  seg_eq seg1 seg2 -> conv_agree_outside_seg seg1 (iset_op16 seg2 pre op).
Proof. unfold seg_eq, iset_op16, compute_addr, set_mem16. intros. subst.
  destruct op; conv_agree_outside_seg_tac.
Qed.

Lemma iset_op8_aos : forall seg1 seg2 pre op,
  seg_eq seg1 seg2 -> conv_agree_outside_seg seg1 (iset_op8 seg2 pre op).
Proof. unfold seg_eq, iset_op8, compute_addr. intros. subst.
  destruct op; conv_agree_outside_seg_tac.
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
  destruct (op_override pre); destruct w; conv_agree_outside_seg_tac.
Qed.

Lemma conv_BS_aux_aos : forall seg s d n (op:rtl_exp s),
  conv_agree_outside_seg seg (conv_BS_aux d n op).
Proof. unfold conv_BS_aux.  
  induction n; intros; conv_agree_outside_seg_tac.
Qed.

Lemma compute_parity_aux_aos : 
  forall seg s (op1:rtl_exp s) op2 n,
    conv_agree_outside_seg seg (compute_parity_aux op1 op2 n).
Proof. induction n. simpl. conv_agree_outside_seg_tac.
  unfold compute_parity_aux. fold (@compute_parity_aux s).
  conv_agree_outside_seg_tac.
Qed.

Hint Resolve set_Bit_mem_aos compute_parity_aux_aos conv_BS_aux_aos 
  : conv_agree_outside_seg_db.


(** ** Property that a conversion preserves [same_pc] *)

Module Conv_Same_PC := Conv_Prop Same_PC.
Notation conv_same_pc := Conv_Same_PC.conv_prop.

Hint Extern 1 (conv_same_pc (emit _)) =>
  apply Conv_Same_PC.emit_sat_conv_prop; same_pc_tac : conv_same_pc_db.

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

Lemma load_mem_n_same_pc : forall seg addr n,
  conv_same_pc (load_mem_n seg addr n).
Proof. unfold load_mem_n, lmem, add_and_check_segment.
  induction n; conv_same_pc_tac.
Qed.

Hint Extern 1 (conv_same_pc (load_mem_n _ _ ?X))
  =>  apply load_mem_n_same_pc with (n:=X) : conv_same_pc_db.

Lemma set_mem_n_same_pc : forall n seg (v:rtl_exp (8*(n+1)-1)) addr,
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
  crush.
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

Lemma conv_BS_aux_same_pc : forall s d n (op:rtl_exp s),
  conv_same_pc (conv_BS_aux d n op).
Proof. unfold conv_BS_aux.  
  induction n; intros; conv_same_pc_tac.
Qed.

Lemma compute_parity_aux_same_pc : forall s (op1:rtl_exp s) op2 n,
  conv_same_pc (compute_parity_aux op1 op2 n).
Proof. induction n. simpl. conv_same_pc_tac.
  unfold compute_parity_aux. fold (@compute_parity_aux s).
  conv_same_pc_tac.
Qed.

Hint Immediate conv_BS_aux_same_pc compute_parity_aux_same_pc :
  conv_same_pc_db.


(** ** Property that conversions preserve [same_mach_state] *)

Module Conv_Same_Mach_State := Conv_Prop (Same_Mach_State).
Notation conv_same_mach_state := Conv_Same_Mach_State.conv_prop.

Hint Extern 1 (conv_same_mach_state (emit _)) => 
  apply Conv_Same_Mach_State.emit_sat_conv_prop; same_mach_state_tac
    : conv_same_mach_state_db.

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

Lemma set_mem_n_same_mach_state : forall n seg (v:rtl_exp (8*(n+1)-1)) addr,
  conv_same_mach_state (set_mem_n seg v addr).
Proof. unfold set_mem_n, smem, add_and_check_segment.
  induction n; intros. 
    conv_same_mach_state_tac.
    fold (@set_mem_n n) in *. conv_same_mach_state_tac.
Qed.

Hint Immediate set_mem_n_same_mach_state : conv_same_mach_state_db.

(** ** Property that conversions [no_fail] *)
Definition conv_no_fail (A:Type) (cv:Conv A) :=
  forall cs (v:A) cs',
    cv cs = (v, cs')
      -> no_fail (RTL_step_list (List.rev (c_rev_i cs)))
      -> no_fail (RTL_step_list (List.rev (c_rev_i cs'))).
Implicit Arguments conv_no_fail [A].

Lemma conv_to_rtl_no_fail: forall cv,
    conv_no_fail cv ->  no_fail (RTL_step_list (runConv cv)).
Proof. unfold conv_no_fail, runConv. intros.
  remember_rev (cv {| c_rev_i := nil |}) as cva.
  destruct cva.
  apply H in Hcva. crush.
    compute [c_rev_i rev RTL_step_list].
    no_fail_tac.
Qed.

Lemma bind_conv_no_fail : forall (A B:Type) (cv: Conv A) (f:A -> Conv B),
  conv_no_fail cv
    -> (forall a:A, conv_no_fail (f a))
    -> conv_no_fail (Bind _ cv f).
Proof. unfold conv_no_fail. intros.
  conv_elim. eauto.
Qed.

Lemma emit_conv_no_fail : forall i,
  no_fail (interp_rtl i) -> conv_no_fail (emit i).
Proof. unfold conv_no_fail, EMIT. intros.
  crush. autorewrite with step_list_db.
  no_fail_tac.
Qed.

Hint Extern 1 (conv_no_fail (emit _)) => 
  apply emit_conv_no_fail; no_fail_tac : conv_no_fail_db.

Lemma ret_conv_no_fail : forall (A:Type) (r:A), conv_no_fail (ret r).
Proof. unfold conv_no_fail. crush. Qed.

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

Lemma set_mem_n_no_fail : forall n seg (v:rtl_exp (8*(n+1)-1)) addr,
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

Lemma conv_BS_aux_no_fail : forall s d n (op:rtl_exp s),
  conv_no_fail (conv_BS_aux d n op).
Proof. unfold conv_BS_aux.  
  induction n; intros; conv_no_fail_tac.
Qed.

Lemma compute_parity_aux_no_fail : forall s (op1:rtl_exp s) op2 n,
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
    conv_PUSHA, conv_PUSH, conv_PUSH_pseudo, conv_SAR, conv_SBB,
    conv_SETcc, conv_SHL, conv_SHLD, conv_SHR, conv_SHRD, conv_RCL, conv_RCR, 
    conv_ROL, conv_ROR, conv_shift, 
    conv_CLD, conv_HLT, conv_STOS, conv_CLC, conv_CMC,
    conv_MOVS, conv_BT, conv_LAHF, conv_SAHF, conv_STC, conv_STD,
    conv_AAA_AAS, conv_AAD, conv_AAM, conv_DAA_DAS, conv_DEC,
    conv_POP_pseudo,
    conv_CALL, conv_JMP,
    testcarryAdd, testcarrySub,
    extract_and_set, get_and_place,
    get_AL, get_AH, set_AL, set_AH, 
    string_op_reg_shift, if_set_loc, get_Bit, fbit, set_Bit, modify_Bit,
    compute_parity, undef_flag,
    load_mem, load_mem8, load_mem16, load_mem32,
    set_mem, set_mem8, set_mem16, set_mem32,
    compute_addr, compute_cc, not.

Ltac extra_unfold_conv_tac :=
  unfold set_Bit_mem, iset_op8, iset_op16, iset_op32; 
    unfold_instr_conv_tac.

Ltac no_fail_extra_unfold_tac := 
  unfold conv_CALL, conv_PUSH, set_Bit_mem, 
    set_mem, set_mem8, set_mem16; unfold_instr_conv_tac.

Ltac unfold_prefix_filters_tac := 
 unfold no_prefix, lock_or_gs_or_op, only_gs_seg_override, lock_or_gs_without_op,
   only_seg_or_op, rep_or_repn_or_gs_or_op_prefix, rep_or_gs_or_op_prefix in *.


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
           unfold_prefix_filters_tac; unfold_instr_conv_tac; 
           no_fail_extra_unfold_tac; conv_no_fail_tac
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

(** ** Showing that non_cflow_instr preserves memory outside of DS, SS, GS,
  ES segments *)

Lemma filter_prefix_only_seg_get_segment : 
  forall pre seg lrs_filter op_filter cs_filter,
    filter_prefix lrs_filter ft_only_gs_seg op_filter cs_filter pre = true
      -> seg_eq seg (get_segment pre seg) \/ seg_eq GS (get_segment pre seg).
Proof. unfold filter_prefix, get_segment, ft_only_gs_seg; intros.
  bool_elim_tac. destruct (seg_override pre). 
    destruct s; crush. right; crush.
    left; crush.
Qed.

Lemma filter_prefix_only_seg_get_segment_op : 
  forall pre seg lrs_filter op_filter cs_filter op,
    filter_prefix lrs_filter ft_only_gs_seg op_filter cs_filter pre = true
      -> seg_eq seg (get_segment_op pre seg op) \/ 
         seg_eq GS (get_segment_op pre seg op) \/
         seg_eq SS (get_segment_op pre seg op).
Proof. unfold filter_prefix, get_segment_op, ft_only_gs_seg; intros.
  bool_elim_tac. destruct (seg_override pre). 
    destruct s; crush. right; left; crush.
    destruct_head. right; right; crush.
    left; crush.
Qed.

Lemma filter_prefix_only_seg_get_segment_op2 : 
  forall pre seg lrs_filter op_filter cs_filter op1 op2,
    filter_prefix lrs_filter ft_only_gs_seg op_filter cs_filter pre = true
      -> seg_eq seg (get_segment_op2 pre seg op1 op2) \/ 
         seg_eq GS (get_segment_op2 pre seg op1 op2) \/
         seg_eq SS (get_segment_op2 pre seg op1 op2).
Proof. unfold filter_prefix, get_segment_op2, ft_only_gs_seg; intros.
  bool_elim_tac. destruct (seg_override pre). 
    destruct s; crush. right; left; crush.
    destruct_head. right; right; crush.
    destruct_head. right; right; crush.
    left; crush.
Qed.

Ltac aos_helper_tac := 
  repeat match goal with
           | [H: seg_eq _ _ \/ _ |- _] => destruct H
           | [H: seg_eq ?Seg _ |- agree_outside_seg ?Seg _ \/ _ ] => left
           | [ |- agree_outside_seg _ _ \/ _ ] => right
           | [ |- agree_outside_seg ?Seg _ ] => prove_instr
         end.

Ltac aos_tac := 
  unfold_prefix_filters_tac;
  unfold_instr_conv_tac; 
  match goal with
    | [ H: filter_prefix _ ft_only_gs_seg _ _ _ = true |-
        context[get_segment_op ?Pre ?Seg _]] => 
      eapply filter_prefix_only_seg_get_segment_op
      with (seg:=Seg) (pre:=Pre)  in H
    | [ H: filter_prefix _ ft_only_gs_seg _ _ _ = true |-
        context[get_segment_op2 ?Pre ?Seg _ _]] => 
      eapply filter_prefix_only_seg_get_segment_op2 
      with (seg:=Seg) (pre:=Pre) in H
    | [ H: filter_prefix _ ft_only_gs_seg _ _ _ = true |-
        context[get_segment ?Pre ?Seg]] => 
      apply filter_prefix_only_seg_get_segment
      with (seg:=Seg) (pre:=Pre) in H
  end;
  aos_helper_tac.

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
    try (discriminate H || (left; prove_instr; fail) || (aos_tac; fail)).

  (* IMUL *)
  destruct opopt as [o|]. aos_tac.
  unfold only_seg_or_op in H.
  eapply filter_prefix_only_seg_get_segment_op
  with (seg:=DS) (pre:=pre) (op:=op1) in H.
  aos_helper_tac.

  (* LEA *)
  destruct op2; try discriminate. 
  bool_elim_tac. aos_tac.

  (* MOVS *)
  right; right; right; prove_instr.

  (* POP *)
  right; left; prove_instr.

  (* PUSH *)
  right; left; prove_instr.

  (* PUSHA *)
  right; left; prove_instr.
  (* STOS *)
  right; right; right; prove_instr.
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
Lemma dci_aoss :forall ins pre, 
  dir_cflow_instr pre ins = true
    -> agree_outside_seg SS (RTL_step_list (instr_to_rtl pre ins)).
Proof. intros. 
  destruct ins; 
  unfold instr_to_rtl, check_prefix in *;
    (discriminate H || prove_instr).
Qed.

(** ** Showing that non_cflow_instr and dir_cflow_instr does not fail *)

Lemma filter_prefix_no_fail :
  forall pre lrs_filter seg_filter op_filter,
    filter_prefix lrs_filter seg_filter op_filter ft_bool_no pre = true
    -> conv_no_fail (check_prefix pre).
Proof. unfold filter_prefix, ft_bool_no, check_prefix; intros. 
  bool_elim_tac. rewrite H0. conv_no_fail_tac.
Qed.  

Hint Extern 1 (conv_no_fail (check_prefix ?Pre)) =>
  match goal with
    | [H: filter_prefix _ _ _ ft_bool_no Pre = true |- _] => 
      eapply filter_prefix_no_fail; eassumption
  end : conv_no_fail_db.

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
  bool_elim_tac. prove_instr.
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
  Case "Jcc".  simpl in H. prove_instr.
  Case "JMP".
    destruct near. eapply dci_JMP_pre in H. prove_instr.
      discriminate.
Qed.



(** * Reification of RTL conversions 

   It converts rtl conversions in higher-order syntax to first-order terms
   with variables indexed by types of those variables so that we can write
   coq functions on rtl conversions. Unfortunately, this mechanism is not
   used in the following code because it turns of this reflection-based
   proof is slower than the tacticis-based approach. I left the code
   here as an interesting example of how to reify high-order Coq terms
   to first-order syntax.
*)
Section REIFIED_RTL_CONV.
  Local Set Implicit Arguments.

  (** Types of return values of rtl conversions; cover only unit and the
     rtl_exp types. *)
  Inductive ty : Set :=
  | ct_unit : ty     (* unit type *)
  | ct_rtl_exp : forall s:nat, ty.  (* [rtl_exp s] type *)

  Definition ty_denote (t:ty) :=
    match t with
      | ct_unit => unit
      | ct_rtl_exp s => rtl_exp s
    end.

  (** The reified syntax of rtl conversions is parameterized by a type
   environment, which remembers tye types of free varialbes. Types of
   variables are of the form "rtl_exp n"; we remember only those natural
   numbers. *)
  Definition tyenv := list nat.

  Fixpoint tyenv_denote (te: tyenv) := 
    match te with
      | nil => unit
      | n :: te' => (rtl_exp n * tyenv_denote te')%type
    end.

  Inductive member (n:nat) : tyenv -> Type := 
  | lfirst : forall te, member n (n :: te)
  | lnext : forall te n', member n te -> member n (n' :: te).

  Section REIFIED_RTL_EXP.

    Variable te: tyenv.

    (** RTL expressions with unbound variables, indexed by the type of the
        expression. *)
    Inductive open_rtl_exp : nat -> Type := 
    (* variables *)
    | ore_var n (m: member n te) :  open_rtl_exp n
    | ore_arith n (b:bit_vector_op) (oe1 oe2:open_rtl_exp n) : open_rtl_exp n
    | ore_test n (top:test_op) (oe1 oe2:open_rtl_exp n) : open_rtl_exp size1
    | ore_if n (cond: open_rtl_exp size1) (oe1 oe2: open_rtl_exp n) :
          open_rtl_exp n
    | ore_cast_s n1 n2 (oe: open_rtl_exp n1) : open_rtl_exp n2
    | ore_cast_u n1 n2 (oe: open_rtl_exp n1) : open_rtl_exp n2
    | ore_imm n : int n -> open_rtl_exp n
    | ore_get_loc n (l:location n) : open_rtl_exp n
    | ore_get_array l n (a:array l n) (idx: open_rtl_exp l) : open_rtl_exp n
    | ore_get_byte (addr: open_rtl_exp size_addr) : open_rtl_exp size8
    | ore_get_random n : open_rtl_exp n
    | ore_farith (ew mw: positive) (hyp: float_width_hyp ew mw)
                 (fop: float_arith_op) (rounding: open_rtl_exp size2) :
          let len := (nat_of_P ew + nat_of_P mw)%nat in
          open_rtl_exp len -> open_rtl_exp len -> open_rtl_exp len
    | ore_fcast (ew1 mw1 ew2 mw2:positive) 
          (hyp1: float_width_hyp ew1 mw1) (hyp2: float_width_hyp ew2 mw2)
          (rounding: open_rtl_exp size2) :
          open_rtl_exp (nat_of_P ew1 + nat_of_P mw1)%nat ->
          open_rtl_exp (nat_of_P ew2 + nat_of_P mw2)%nat.

  End REIFIED_RTL_EXP.

  (* Tricky to get this right, fighting the type checker all the time;
     illustrate all the pain of doing dependent types in Coq:( *)
  Fixpoint get_from_env te n : 
    tyenv_denote te -> member n te -> ty_denote (ct_rtl_exp n) :=
    match te return tyenv_denote te -> member n te
                    -> ty_denote (ct_rtl_exp n) with
      | nil => fun env mem => 
        match mem in member _ te' return (match te' with
                                            | nil => ty_denote (ct_rtl_exp n)
                                            | _ => unit
                                          end) with
          | lfirst _ => tt
          | lnext _ _ _ => tt
        end
      | n' :: te' => 
        fun env mem =>
          match mem in member _ te1 return (match te1 with
                                              | nil => Empty_set
                                              | n'' :: te'' =>
                                                tyenv_denote (n'' :: te'')
                                                -> (tyenv_denote te''
                                                    -> member n te''
                                                    -> ty_denote 
                                                         (ct_rtl_exp n))
                                                -> ty_denote (ct_rtl_exp n)
                                            end) with
          | lfirst _ => fun env _ => fst env
          | lnext x ts2 mem' => fun env get_ty' => 
                                get_ty' (snd env) mem'
        end env (@get_from_env te' n)
    end.

  (** Denotation of [open_rtl_exp] *)
  Fixpoint ore_denote (te: tyenv) n (env: tyenv_denote te)
             (oe: open_rtl_exp te n) : ty_denote (ct_rtl_exp n) :=
    match oe with
      | ore_var n mem => get_from_env env mem
      | ore_arith _ b oe1 oe2 => 
        arith_rtl_exp b (ore_denote env oe1) (ore_denote env oe2)
      | ore_test _ top oe1 oe2 =>
        test_rtl_exp top (ore_denote env oe1) (ore_denote env oe2)
      | ore_if _ cond oe1 oe2 =>
        if_rtl_exp (ore_denote env cond)
                   (ore_denote env oe1) (ore_denote env oe2)
      | ore_cast_s _ n2 oe =>
        cast_s_rtl_exp n2 (ore_denote env oe)
      | ore_cast_u _ n2 oe =>
        cast_u_rtl_exp n2 (ore_denote env oe)
      | ore_imm _ i => imm_rtl_exp i
      | ore_get_loc _ l => get_loc_rtl_exp l
      | ore_get_array _ _ a idx => get_array_rtl_exp a (ore_denote env idx)
      | ore_get_byte addr => get_byte_rtl_exp (ore_denote env addr)
      | ore_get_random n => get_random_rtl_exp n
      | ore_farith _ _ hyp fop rounding oe1 oe2 =>
        farith_rtl_exp hyp fop (ore_denote env rounding)
                       (ore_denote env oe1) (ore_denote env oe2)
      | ore_fcast _ _ _ _ hyp1 hyp2 rounding oe1 => 
        fcast_rtl_exp hyp1 hyp2 (ore_denote env rounding)
                       (ore_denote env oe1)
    end.

  (** Reified syntax of rtl conversions, indexed by the types of
     free variables and the return type *)
  Inductive open_conv (te: tyenv) : ty -> Type := 
    (* oc_seq is a special kind of bind in which oc1 returns unit *)
  | oc_seq t (oc1: open_conv te ct_unit) (oc2: open_conv te t) :
      open_conv te t
  | oc_bind_exp n t (oc:open_conv te (ct_rtl_exp n)) 
                (f:open_conv (n::te) t) : open_conv te t
  | oc_ret n (oe: open_rtl_exp te n) : open_conv te (ct_rtl_exp n)
  | oc_no_op : open_conv te ct_unit
  | oc_write_loc n (oe: open_rtl_exp te n) (l:loc n) : open_conv te ct_unit
  | oc_write_array l n (a:array l n) (idx: open_rtl_exp te l)
      (v: open_rtl_exp te n) : open_conv te ct_unit
  | oc_write_byte (v: open_rtl_exp te size8) (a: open_rtl_exp te size32) :
    open_conv te ct_unit
  | oc_if_trap (g: open_rtl_exp te size1) : open_conv te ct_unit
  | oc_if_set_loc (cond: open_rtl_exp te size1) n (oe: open_rtl_exp te n)
                  (l:loc n) : open_conv te ct_unit
  | oc_error : open_conv te ct_unit
  | oc_trap : open_conv te ct_unit
  | oc_load_op (pre:prefix) (w:bool) (seg:segment_register) (op:operand) :
      open_conv te (ct_rtl_exp (opsize (op_override pre) w))
  | oc_set_op (pre:prefix) (w:bool) (seg:segment_register) 
              (v: open_rtl_exp te (opsize (op_override pre) w))
              (op:operand) : open_conv te ct_unit
  | oc_iload_op8 (seg:segment_register) (op:operand) : 
      open_conv te (ct_rtl_exp size8)
  | oc_iset_op8 (seg:segment_register) (p: open_rtl_exp te size8)
                (op:operand) : open_conv te ct_unit
  (* compute_parity_aux *)
  | oc_cp_aux s (oe1: open_rtl_exp te s) (oe2: open_rtl_exp te size1) 
              (n:nat) : open_conv te (ct_rtl_exp size1)
  (* a catch-call clause; for debugging *)
  | oc_any t (c:tyenv_denote te -> Conv (ty_denote t)) : open_conv te t.
   
  (** Denotation of open_conv_denote *)
  Fixpoint oc_denote (te:tyenv) (t:ty) (env:tyenv_denote te)
           (oc:open_conv te t) : Conv (ty_denote t) := 
    match oc in open_conv _ t' return Conv (ty_denote t') with
      | oc_seq _ oc1 oc2 => 
        Bind _ (oc_denote env oc1) (fun _ => oc_denote env oc2)
      | oc_bind_exp n _ oc1 ocf =>
        Bind _ (oc_denote env oc1) 
             (fun x => @oc_denote (n::te) _ (x,env) ocf)
      | oc_ret _ oe => ret (ore_denote env oe)
      | oc_no_op => ret tt
      | oc_write_loc n oe l => write_loc (ore_denote env oe) l
      | oc_write_array _ _ arr idx v => 
        write_array arr (ore_denote env idx) (ore_denote env v)
      | oc_write_byte v addr => 
        write_byte (ore_denote env v) (ore_denote env addr)
      | oc_if_trap g => if_trap (ore_denote env g)
      | oc_if_set_loc cond _ oe l => 
        if_set_loc (ore_denote env cond) (ore_denote env oe) l
      | oc_error => raise_error
      | oc_trap => raise_trap
      | oc_load_op pre w seg op => load_op pre w seg op
      | oc_set_op pre w seg ov op => 
        set_op pre w seg (ore_denote env ov) op
      | oc_iload_op8 seg op => iload_op8 seg op
      | oc_iset_op8 seg p op => iset_op8 seg (ore_denote env p) op
      | oc_cp_aux _ oe1 oe2 n => 
        compute_parity_aux (ore_denote env oe1) (ore_denote env oe2) n
      | oc_any _ c => c env
    end.

End REIFIED_RTL_CONV.

(** ** Tactics for converting RTL conversions to terms in open_conv syntax
*)

Ltac ty_reify tp := 
  match tp with 
    | unit => ct_unit
    | rtl_exp ?s => constr:(ct_rtl_exp s)
    | _ => fail "ty_reify failed!"
  end.

Ltac member_pf ts fe := 
  match ts with
    | ?t' :: ?ts' =>
      match fe with
        | fun env => env => constr:(lfirst t' ts')
        | fun env => snd (@?fe' env) => 
          let mem := member_pf ts' fe' in
          constr:(lnext t' mem)
      end
    | _ => fail "member_pf failed!"
  end.

(** Reify higher-order rtl expressions to first-order syntax. All
   expressions of the form [fun env => ...], where env is the value
   environment and of type [tyenv_denote te]. [fst env] is converted
   [ore_var lfirst]; [fst (snd env)] is converted to [ore_var (lnext
   lfirst)]; [fst (snd (snd env))] is converted to [ore_var (lnext (lnext
   lfirst))] *)
Ltac reify_rtl_exp te e := 
  match e with
    | fun env:_ => fst (@?FE env)=> 
      let mem := member_pf te FE in
      constr:(ore_var mem)
    | fun env => imm_rtl_exp ?I =>
      constr:(ore_imm te I)
    | fun env => arith_rtl_exp ?Bop (@?E1 env) (@?E2 env) =>
      let oe1 := reify_rtl_exp te E1 in
      let oe2 := reify_rtl_exp te E2 in
      constr:(ore_arith Bop oe1 oe2)
    | fun env => test_rtl_exp ?Top (@?E1 env) (@?E2 env) =>
      let oe1 := reify_rtl_exp te E1 in
      let oe2 := reify_rtl_exp te E2 in
      constr:(ore_test Top oe1 oe2)
    | fun env => if_rtl_exp (@?C env) (@?E1 env) (@?E2 env) =>
      let oc := reify_rtl_exp te C in
      let oe1 := reify_rtl_exp te E1 in
      let oe2 := reify_rtl_exp te E2 in
      constr:(ore_if oc oe1 oe2)
    | fun env => cast_s_rtl_exp ?N2 (@?E env) =>
      let oe := reify_rtl_exp te E in
      constr:(ore_cast_s N2 oe)
    | fun env => cast_u_rtl_exp ?N2 (@?E env) =>
      let oe := reify_rtl_exp te E in
      constr:(ore_cast_u N2 oe)
    | fun env => get_loc_rtl_exp ?L => constr:(ore_get_loc te L)
    | fun env => get_array_rtl_exp ?A (@?Idx env) =>
      let oi := reify_rtl_exp te Idx in
      constr:(ore_get_array A oi)
    | fun env => get_byte_rtl_exp (@?Addr env) =>
      let oa := reify_rtl_exp te Addr in
      constr:(ore_get_byte oa)
    | fun env => get_random_rtl_exp ?N => constr:(ore_get_random te N)
    | fun env => farith_rtl_exp ?Hyp ?Fop (@?R env) (@?E1 env) (@?E2 env)  => 
      let or := reify_rtl_exp te R in
      let oe1 := reify_rtl_exp te E1 in
      let oe2 := reify_rtl_exp te E2 in
      constr:(ore_farith Hyp Fop or oe1 oe2)
    | fun env => fcast_rtl_exp ?Hyp1 ?Hyp2 (@?R env) (@?E env) => 
      let or := reify_rtl_exp te R in
      let oe := reify_rtl_exp te E in
      constr:(ore_fcast Hyp1 Hyp2 or oe)
  end.

(* Goal False. *)
(* Unset Ltac Debug. *)
(* let s := reify_rtl_exp (size8 :: size8 :: nil) *)
(*           (fun env: (rtl_exp size8)*(rtl_exp size8*unit) => *)
(*              arith_rtl_exp and_op (fst env) (fst (snd env))) *)
(* in pose s. *)

(** Reify higher-order rtl conversions to first-order syntax; te is the type
   enviroment (list of types of free variables in conversion cv) *)
Ltac reify_rtl_conv te cv := 
  match eval cbv beta iota zeta in cv with
    | fun (env: ?T) => Bind _ (@?C env) (fun (y:?S) => @?F env y) =>
      let oc := reify_rtl_conv te C in
      let t:= ty_reify S in
      match t with
        | ct_unit =>
          let of := reify_rtl_conv te (fun p:T => F p tt) in
          constr:(oc_seq oc of)
        | ct_rtl_exp ?N=> 
          let of := 
              reify_rtl_conv (N::te) (fun p:S*T => F (snd p) (fst p)) in
          constr:(oc_bind_exp oc of)
      end
        
    | fun (env: ?T) => Return (@?E env) =>
      let oe := reify_rtl_exp te E in
      constr:(oc_ret oe)

    | fun (env: ?T) => no_op =>
      constr:(oc_no_op te)

    | fun (env: ?T) => write_loc (@?E env) ?L =>
      let oe := reify_rtl_exp te E in
      constr:(oc_write_loc oe L)

    | fun (env: ?T) => raise_error =>
      constr:(oc_error te)

    | fun (env: ?T) => load_op ?Pre ?W ?Seg ?Op =>
      constr:(oc_load_op te Pre W Seg Op)

    | fun (env: ?T) => set_op ?Pre ?W ?Seg (@?V env) ?Op =>
      let ov := reify_rtl_exp te V in
      constr:(oc_set_op Pre W Seg ov Op)

    | fun (env: ?T) => iload_op8 ?Seg ?Op =>
      constr:(oc_iload_op8 te Seg Op)

    | fun (env: ?T) => iset_op8 ?Seg (@?P env) ?Op =>
      let p := reify_rtl_exp te P in
      constr:(oc_iset_op8 Seg p Op)

    | fun (env: ?T) => compute_parity_aux (@?E1 env) (@?E2 env) ?N =>
      let oe1 := reify_rtl_exp te E1 in
      let oe2 := reify_rtl_exp te E2 in
      constr:(oc_cp_aux oe1 oe2 N)

    | fun (env: ?T) => @?C env =>
      match type of C with
        | _ -> Conv ?T' =>
          let t' := ty_reify T' in
          constr:(oc_any te t' C)
      end
  end.

(* testing *)
(* Set Printing Depth 100. *)
(* Goal conv_AAA_AAS add_op = conv_AAA_AAS sub_op. *)
(* Proof. *)
(*   unfold conv_AAA_AAS, load_Z, undef_flag, get_flag, set_flag, *)
(*     get_AH, get_AL, copy_ps, set_AL, set_AH, load_int, read_loc, *)
(*     arith, test, cast_u, cast_s, if_exp, choose. *)
(*   (* arith, test, copy_ps. *) *)
(*   Unset Ltac Debug. *)
(*   Time match goal with *)
(*           | [|- ?X = ?Y] => *)
(*             let l:= reify_rtl_conv (@nil nat) (fun _:unit => X) in *)
(*             let r:= reify_rtl_conv (@nil nat) (fun _:unit => Y) in *)
(*             change (@oc_denote (@nil nat) _ tt l= *)
(*                     @oc_denote (@nil nat) _ tt r) *)
(*        end. *)

(* Goal False. *)
(* Unset Ltac Debug. *)
(* let s := reify_rtl_conv (@nil nat) *)
(*           (fun _:unit => pal <- iload_op8 DS (Reg_op EAX); *)
(*            ret arith_rtl_exp and_op pal pal) in *)
(* pose s. *)

(* Goal load_Z size8 9 = load_Z size8 9. *)
(* Proof.  unfold load_Z, load_int. *)
(*         Unset Ltac Debug. *)
(*         match goal with *)
(*           | [|- ?X = ?Y] => *)
(*             let l:= reify_rtl_conv (@nil nat) (fun _:unit => X) in *)
(*             let r:= reify_rtl_conv (@nil nat) (fun _:unit => Y) in *)
(*             change (@oc_denote (@nil nat) _ tt l=@oc_denote (@nil nat) _ tt r) *)
(*         end. *)

