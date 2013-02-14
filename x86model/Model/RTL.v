(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

Require Import List.
Require Import Bits.
Require Import ZArith.
Require Import Parser.
Require Import String.
Require Import Monad.
Require Import Maps.
Require Import X86Syntax.
Require Import Eqdep.
Require Import Flocq.Appli.Fappli_IEEE_bits.
Require Import Flocq.Appli.Fappli_IEEE.
Set Implicit Arguments.
Unset Automatic Introduction.


Definition size1 := 0.
Definition size2 := 1.
Definition size3 := 2.
Definition size4 := 3.
Definition size8 := 7.
Definition size16 := 15.
Definition size32 := 31.
Definition size64 := 63.
Definition size80 := 79.
Definition int n := Word.int n.

Module Type MACHINE_SIG.
  (** We abstract over locations which include things like registers, flags, the pc, 
      segment registers, etc.  Our only assumption is that updates to distinct locations
      commute. *)
  Variable location : nat -> Set.  (* registers, flags, etc. *)

  (** We also abstract over the size of memory, by parameterizing the RTLs over the
      number of bits in addresses. *)
  Variable size_addr : nat.  (* number of bits in a memory adress minus one *)

  (** We assume some type for the machine state *)
  Variable mach_state : Type.
  (** And operations for reading/writing locations *)
  Variable get_location : forall s, location s -> mach_state -> Word.int s.
  Variable set_location : forall s, location s -> Word.int s -> mach_state -> mach_state.
End MACHINE_SIG.

(** Generic register-transfer language *)    
Module RTL(M : MACHINE_SIG).
  Import M.
  Local Open Scope Z_scope.
  Module AddrIndexed.
    Definition t := int size_addr.
    Definition index(i:int size_addr) : positive := ZIndexed.index (Word.unsigned i).
    Lemma index_inj : forall (x y : int size_addr), index x = index y -> x = y.
    Proof.
      unfold index. destruct x; destruct y ; simpl ; intros.
      generalize intrange intrange0. clear intrange intrange0.
      rewrite (ZIndexed.index_inj intval intval0 H). intros.
      rewrite (Coqlib.proof_irrelevance _ intrange intrange0). auto.
    Qed.
    Definition eq := @Word.eq_dec size_addr.
  End AddrIndexed.
  Module AddrMap := IMap(AddrIndexed).

  (** RTL instructions form a RISC-like core language that operate over pseudo-registers.
      We assume that we're working under an environment that holds an infinite number of
      pseudo registers for each bit-vector size of interest.  The instructions include
      arithmetic operations over bitvectors, test instructions, a primitive conditional
      instruction, signed and unsigned conversions of bitvectors from one size to another,
      the ability to read/write locations in the machine state, the ability to read/write
      locations in memory, the ability to non-deterministically choose a bit-vector, 
      and an error. *)
  Inductive bit_vector_op : Set := 
    add_op | sub_op | mul_op | divs_op | divu_op | modu_op | mods_op
  | and_op | or_op | xor_op | shl_op | shr_op | shru_op | ror_op | rol_op.

  Inductive float_arith_op : Set :=
    fadd_op | fsub_op | fmul_op | fdiv_op.

  Inductive test_op : Set := eq_op | lt_op | ltu_op.

  (* Constraints on mantissa and exponent widths of floating-point numbers *)
  Definition float_width_hyp (mw ew:positive) :=
    Zpos mw + 1 < 2 ^ (Zpos ew - 1).

  Definition rounding_mode := Flocq.Appli.Fappli_IEEE.mode.

  Inductive rtl_exp : nat -> Type := 
  | arith_rtl_exp : forall s (b:bit_vector_op)(e1 e2:rtl_exp s), rtl_exp s
  | test_rtl_exp : forall s (top:test_op)(e1 e2:rtl_exp s), rtl_exp size1
  | if_rtl_exp : forall s (cond:rtl_exp size1) (e1 e2: rtl_exp s), rtl_exp s
  | cast_s_rtl_exp : forall s1 s2 (e:rtl_exp s1), rtl_exp s2
  | cast_u_rtl_exp : forall s1 s2 (e:rtl_exp s1), rtl_exp s2
  | imm_rtl_exp : forall s, int s -> rtl_exp s
  | get_loc_rtl_exp : forall s (l:location s), rtl_exp s
  | get_byte_rtl_exp : forall (addr:rtl_exp size_addr),  rtl_exp size8
  | farith_rtl_exp : (* floating-point arithmetics *)
    forall (mw ew:positive),
      let len := (1 + nat_of_P mw + nat_of_P ew)%nat in
        float_width_hyp mw ew ->
        float_arith_op -> rounding_mode ->
        rtl_exp len -> rtl_exp len -> rtl_exp len
  | fcast_rtl_exp : (* cast between floats of different precisions *)
    forall (mw1 ew1 mw2 ew2:positive),
      float_width_hyp mw1 ew1 -> float_width_hyp mw2 ew2 -> rounding_mode ->
      rtl_exp (1 + nat_of_P mw1 + nat_of_P ew1)%nat ->
      rtl_exp (1 + nat_of_P mw2 + nat_of_P ew2)%nat
  | choose_rtl_exp : forall s, rtl_exp s.

  Inductive rtl_instr : Type :=
  | set_loc_rtl : forall s (e:rtl_exp s) (l:location s), rtl_instr
  | set_byte_rtl: forall (e:rtl_exp size8)(addr:rtl_exp size_addr), rtl_instr
  | if_rtl : rtl_exp size1 -> rtl_instr -> rtl_instr
  | error_rtl : rtl_instr
  | trap_rtl : rtl_instr.


  (** Next, we give meaning to RTL instructions as transformers over a machine state *)

  Record oracle := { 
    oracle_bits : forall s, Z -> int s ; 
    oracle_offset : Z
  }.

  Record rtl_state := { 
    rtl_oracle : oracle ; 
    rtl_mach_state : mach_state ; 
    rtl_memory : AddrMap.t int8
  }. 

  Inductive RTL_ans(A:Type) : Type := 
  | Fail_ans : RTL_ans A
  | Trap_ans : RTL_ans A
  | Okay_ans : A -> RTL_ans A.

  Definition RTL(T:Type) := rtl_state -> (RTL_ans T * rtl_state).

  Instance RTL_monad : Monad RTL := { 
    Return := fun A (x:A) (rs:rtl_state) => (Okay_ans x, rs) ;
    Bind := fun A B (c:RTL A) (f:A -> RTL B) (rs:rtl_state) => 
      match c rs with
        | (Okay_ans v, rs') => f v rs'
        | (Fail_ans, rs') => (Fail_ans _, rs')
        | (SafeFail_ans, rs') => (Trap_ans _, rs')
      end
  }.
  intros ; apply Coqlib.extensionality. auto.
  intros ; apply Coqlib.extensionality. intros. destruct (c x) ; auto. destruct r ; auto.
  intros ; apply Coqlib.extensionality. intros. destruct (f x) ; auto.
    destruct r ; auto.
  Defined.

  Definition Fail T : RTL T := fun rs => (Fail_ans T,rs).
  Definition Trap T : RTL T := fun rs => (Trap_ans T,rs).

  Definition set_loc s (l:location s) (v:int s) : RTL unit := 
    fun rs => (Okay_ans tt, {| rtl_oracle := rtl_oracle rs ; 
                           rtl_mach_state := set_location l v (rtl_mach_state rs) ; 
                           rtl_memory := rtl_memory rs |}).
  Definition set_byte (addr:int size_addr) (v:int size8) : RTL unit := 
    fun rs => (Okay_ans tt, {| rtl_oracle := rtl_oracle rs ; 
                           rtl_mach_state := rtl_mach_state rs ;
                           rtl_memory := AddrMap.set addr v (rtl_memory rs) |}).

  Definition get_loc s (l:location s) : RTL (int s) :=
    fun rs => (Okay_ans (get_location l (rtl_mach_state rs)), rs).
  Definition get_byte (addr:int size_addr) : RTL (int size8) := 
    fun rs => (Okay_ans (AddrMap.get addr (rtl_memory rs)), rs).

  Definition choose_bits (s:nat) : RTL (int s) :=
    fun rs =>
      let o := rtl_oracle rs in
      let o' := {| oracle_bits := oracle_bits o; oracle_offset := oracle_offset o + 1 |} in
        (Okay_ans (oracle_bits o s (oracle_offset o)),
          {| rtl_oracle := o' ;
             rtl_mach_state := rtl_mach_state rs ;
             rtl_memory := rtl_memory rs |}).

  Definition interp_arith s (b:bit_vector_op)(v1 v2:int s) : int s := 
    match b with 
      | add_op => Word.add v1 v2
      | sub_op => Word.sub v1 v2
      | mul_op => Word.mul v1 v2
      | divs_op => Word.divs v1 v2
      | divu_op => Word.divu v1 v2
      | modu_op => Word.modu v1 v2
      | mods_op => Word.mods v1 v2
      | and_op => Word.and v1 v2
      | or_op => Word.or v1 v2
      | xor_op => Word.xor v1 v2
      | shl_op => Word.shl v1 v2
      | shr_op => Word.shr v1 v2
      | shru_op => Word.shru v1 v2
      | ror_op => Word.ror v1 v2
      | rol_op => Word.rol v1 v2
    end.

  Definition interp_test s (t:test_op)(v1 v2:int s) : int size1 := 
    if (match t with 
      | eq_op => Word.eq v1 v2 
      | lt_op => Word.lt v1 v2
      | ltu_op => Word.ltu v1 v2
        end) then Word.one else Word.zero.

  Lemma prec_gt_0 : forall mw:positive, 0 < Zpos mw + 1.
  Proof. intros. generalize (Pos2Z.is_pos mw). omega. Qed.

  Definition interp_farith (mw ew:positive) (hyp: float_width_hyp mw ew)
    (fop:float_arith_op) (rm: rounding_mode)
    (v1 v2: int (1 + nat_of_P mw + nat_of_P ew)) :
    int (1 + nat_of_P mw + nat_of_P ew) :=
    let prec := Zpos mw + 1 in
    let emax := Zpower 2 (Zpos ew - 1) in
    let bf_of_bits := binary_float_of_bits (Zpos mw) (Zpos ew) 
      (Pos2Z.is_pos mw) (Pos2Z.is_pos ew) hyp in
    let bf1 := bf_of_bits (Word.unsigned v1) in
    let bf2 := bf_of_bits (Word.unsigned v2) in
    let res := 
      match fop with
        | fadd_op => Bplus prec emax (prec_gt_0 mw) hyp rm bf1 bf2 
        | fsub_op => Bminus prec emax (prec_gt_0 mw) hyp rm bf1 bf2 
        | fmul_op => Bmult prec emax (prec_gt_0 mw) hyp rm bf1 bf2 
        | fdiv_op => Bdiv prec emax (prec_gt_0 mw) hyp rm bf1 bf2 
      end
    in
    Word.repr (bits_of_binary_float (Zpos mw) (Zpos ew) res).

  Definition cond_Zopp (b : bool) m := if b then Zopp m else m.

  Definition binary_float_cast (prec1 emax1 prec2 emax2:Z) 
    (H1: 0 < prec2)  (H2: prec2 < emax2)
    (rm: rounding_mode)
    (bf: binary_float prec1 emax1)
        : binary_float prec2 emax2 :=
    match bf with
      | B754_nan => B754_nan _ _
      | B754_zero sign => B754_zero _ _ sign
      | B754_infinity sign => B754_infinity _ _ sign
      | B754_finite sign mant ep _  => 
        binary_normalize prec2 emax2 H1 H2 rm (cond_Zopp sign (Zpos mant)) ep true
    end.

  Definition interp_fcast (mw1 ew1 mw2 ew2:positive)
     (hyp1: float_width_hyp mw1 ew1) (hyp2: float_width_hyp mw2 ew2)
     (rm:rounding_mode) (v: int (1 + nat_of_P mw1 + nat_of_P ew1)) :
     int (1 + nat_of_P mw2 + nat_of_P ew2) :=
     let bf_of_bits := binary_float_of_bits (Zpos mw1) (Zpos ew1)
       (Pos2Z.is_pos mw1) (Pos2Z.is_pos ew1) hyp1 in
     let bf := bf_of_bits (Word.unsigned v) in
     let bf' := binary_float_cast (prec_gt_0 mw2) hyp2 rm bf in
       Word.repr (bits_of_binary_float (Zpos mw2) (Zpos ew2) bf').

  Local Open Scope monad_scope.

  Fixpoint interp_rtl_exp s (e:rtl_exp s) : RTL (int s) := 
    match e with 
      | arith_rtl_exp _ b e1 e2 =>
        v1 <- interp_rtl_exp e1; v2 <- interp_rtl_exp e2; ret (interp_arith b v1 v2)
      | test_rtl_exp _ t e1 e2 => 
        v1 <- interp_rtl_exp e1; v2 <- interp_rtl_exp e2; ret (interp_test t v1 v2)
      | if_rtl_exp _ cd e1 e2 =>
        v <- interp_rtl_exp cd;
        if (Word.eq v Word.one) then interp_rtl_exp e1
          else interp_rtl_exp e2
      | cast_s_rtl_exp _ _ e =>
        v <- interp_rtl_exp e; ret (Word.repr (Word.signed v))
      | cast_u_rtl_exp _ _ e => 
        v <- interp_rtl_exp e; ret (Word.repr (Word.unsigned v))
      | imm_rtl_exp _ v => ret v
      | get_loc_rtl_exp _ l => get_loc l
      | get_byte_rtl_exp addr => 
        v <- interp_rtl_exp addr; get_byte v
      | farith_rtl_exp _ _ hyp fop rm e1 e2 =>
        v1 <- interp_rtl_exp e1; v2 <- interp_rtl_exp e2; ret (interp_farith hyp fop rm v1 v2)
      | fcast_rtl_exp _ _ _ _ hyp1 hyp2 rm e =>
        v <- interp_rtl_exp e; ret (interp_fcast hyp1 hyp2 rm v)
      | choose_rtl_exp _ => choose_bits _
    end.


  Fixpoint interp_rtl (instr:rtl_instr) : RTL unit := 
    match instr with 
      | set_loc_rtl _ e l => 
        v <- interp_rtl_exp e; set_loc l v
      | set_byte_rtl e addr => 
        v <- interp_rtl_exp e; a <- interp_rtl_exp addr; set_byte a v
      | if_rtl r i => 
        v <- interp_rtl_exp r ; if (Word.eq v Word.one) then interp_rtl i else ret tt
      | error_rtl => Fail unit
      | trap_rtl => Trap unit
    end.

  (** We collect all of the information for an instruction into a record
      satisfying this interface. *)
  Record instruction := { 
    instr_assembly : string ;  (* for printing/debugging *)
    instr_rtl : list rtl_instr (* semantics as RTL instructions *)
  }.
End RTL.

