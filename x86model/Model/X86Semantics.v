(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.
Require ExtrOcamlZBigInt. 
Require Import List.
Require Import Bits.
Require Import ZArith.
Require Import Parser.
Require Import Decode.  
Require Import String.
Require Import Monad.
Require Import Maps.
Require Import X86Syntax.
Require Import RTL.

Set Implicit Arguments.
Unset Automatic Introduction.

Module X86_MACHINE.
  Local Open Scope Z_scope.
  Local Open Scope string_scope.

  Definition size_addr := size32.  
  Inductive flag : Set := ID | VIP | VIF | AC | VM | RF | NT | IOPL | OF | DF 
  | IF_flag | TF | SF | ZF | AF | PF | CF.

  Definition flag_eq_dec : forall(f1 f2:flag), {f1=f2}+{f1<>f2}.
    intros ; decide equality. Defined.

  Inductive loc : nat -> Set := 
  | reg_loc : register -> loc size32
  | seg_reg_start_loc : segment_register -> loc size32
  | seg_reg_limit_loc : segment_register -> loc size32
  | flag_loc : flag -> loc size1
  | control_register_loc : control_register -> loc size32
  | debug_register_loc : debug_register -> loc size32
  | pc_loc : loc size32
  (*Floating-Point locations *)
  | fpu_reg_loc : fpu_register -> loc size80
  | fpu_lastOperPtr_loc : fp_lastOperandPtr_register -> loc size64
  | fpu_st_loc : fp_status_register -> loc size3
  | fpu_cntrl_loc : fp_control_register -> loc size3
  | fpu_tag_loc : fpu_tagWords -> loc size2.
  Definition location := loc.

  Definition fmap (A B:Type) := A -> B.
  Definition upd A (eq_dec:forall (x y:A),{x=y}+{x<>y}) B (f:fmap A B) (x:A) (v:B) : 
    fmap A B := fun y => if eq_dec x y then v else f y.
  Definition look A B (f:fmap A B) (x:A) : B := f x.

  Record mach := { 
    gp_regs : fmap register int32 ;
    seg_regs_starts : fmap segment_register int32 ; 
    seg_regs_limits : fmap segment_register int32 ; 
    flags_reg : fmap flag int1 ; 
    control_regs : fmap control_register int32 ; 
    debug_regs : fmap debug_register int32 ; 
    pc_reg : int size32 ;
    fpu_regs : fmap fpu_register int80 ;
    fpu_lastOperPtr : fmap fp_lastOperandPtr_register int64 ;
    fpu_status : fmap fp_status_register int3 ;
    fpu_control : fmap fp_control_register int3 ;
    fpu_tags : fmap fpu_tagWords int2
    
  }.
  Definition mach_state := mach.

  Definition get_location s (l:loc s) (m:mach_state) : int s := 
    match l in loc s' return int s' with 
      | reg_loc r => look (gp_regs m) r
      | seg_reg_start_loc r => look (seg_regs_starts m) r
      | seg_reg_limit_loc r => look (seg_regs_limits m) r
      | flag_loc f => look (flags_reg m) f
      | control_register_loc r => look (control_regs m) r
      | debug_register_loc r => look (debug_regs m) r
      | pc_loc => pc_reg m
      | fpu_reg_loc r => look (fpu_regs m) r
      | fpu_lastOperPtr_loc r=> look (fpu_lastOperPtr m) r
      | fpu_st_loc r=> look (fpu_status m) r
      | fpu_cntrl_loc r=> look (fpu_control m) r
      | fpu_tag_loc r=> look (fpu_tags m) r
    end.

  Definition set_gp_regs r v m := 
    {| gp_regs := upd register_eq_dec (gp_regs m) r v ; 
       fpu_regs := fpu_regs m ;
       seg_regs_starts := seg_regs_starts m ; 
       seg_regs_limits := seg_regs_limits m ;
       flags_reg := flags_reg m ;
       control_regs := control_regs m; 
       debug_regs := debug_regs m; 
       pc_reg := pc_reg m;
       fpu_lastOperPtr := fpu_lastOperPtr m ;
       fpu_status := fpu_status m ;
       fpu_control := fpu_control m ;
       fpu_tags := fpu_tags m 
       
    |}.

  Definition set_seg_regs_starts r v m := 
    {| gp_regs := gp_regs m ;
       fpu_regs := fpu_regs m ;
       seg_regs_starts := upd segment_register_eq_dec (seg_regs_starts m) r v ; 
       seg_regs_limits := seg_regs_limits m ;
       flags_reg := flags_reg m ;
       control_regs := control_regs m; 
       debug_regs := debug_regs m; 
       pc_reg := pc_reg m ;
       fpu_lastOperPtr := fpu_lastOperPtr m ;
       fpu_status := fpu_status m ;
       fpu_control := fpu_control m ;
       fpu_tags := fpu_tags m 
    |}.

  Definition set_seg_regs_limits r v m := 
    {| gp_regs := gp_regs m ;
       fpu_regs := fpu_regs m ;
       seg_regs_starts := seg_regs_starts m ;
       seg_regs_limits := upd segment_register_eq_dec (seg_regs_limits m) r v ; 
       flags_reg := flags_reg m ;
       control_regs := control_regs m; 
       debug_regs := debug_regs m; 
       pc_reg := pc_reg m ;
       fpu_lastOperPtr := fpu_lastOperPtr m ;
       fpu_status := fpu_status m ;
       fpu_control := fpu_control m ;
       fpu_tags := fpu_tags m 
    |}.

  Definition set_flags_reg r v m := 
    {| gp_regs := gp_regs m ;
       fpu_regs := fpu_regs m ;
       seg_regs_starts := seg_regs_starts m ;
       seg_regs_limits := seg_regs_limits m ;
       flags_reg := upd flag_eq_dec (flags_reg m) r v ;
       control_regs := control_regs m; 
       debug_regs := debug_regs m; 
       pc_reg := pc_reg m ;
       fpu_lastOperPtr := fpu_lastOperPtr m ;
       fpu_status := fpu_status m ;
       fpu_control := fpu_control m ;
       fpu_tags := fpu_tags m 
    |}.

  Definition set_control_regs r v m := 
    {| gp_regs := gp_regs m ;
       fpu_regs := fpu_regs m ;
       seg_regs_starts := seg_regs_starts m ;
       seg_regs_limits := seg_regs_limits m ;
       flags_reg := flags_reg m ; 
       control_regs := upd control_register_eq_dec (control_regs m) r v ;
       debug_regs := debug_regs m; 
       pc_reg := pc_reg m ;
       fpu_lastOperPtr := fpu_lastOperPtr m ;
       fpu_status := fpu_status m ;
       fpu_control := fpu_control m ;
       fpu_tags := fpu_tags m 
    |}.

  Definition set_debug_regs r v m := 
    {| gp_regs := gp_regs m ;
       fpu_regs := fpu_regs m ;
       seg_regs_starts := seg_regs_starts m ;
       seg_regs_limits := seg_regs_limits m ;
       flags_reg := flags_reg m ; 
       control_regs := control_regs m ;
       debug_regs := upd debug_register_eq_dec (debug_regs m) r v ;
       pc_reg := pc_reg m ;
       fpu_lastOperPtr := fpu_lastOperPtr m ;
       fpu_status := fpu_status m ;
       fpu_control := fpu_control m ;
       fpu_tags := fpu_tags m 
    |}.

  Definition set_pc v m := 
    {| gp_regs := gp_regs m ;
       fpu_regs := fpu_regs m ;
       seg_regs_starts := seg_regs_starts m ;
       seg_regs_limits := seg_regs_limits m ;
       flags_reg := flags_reg m ; 
       control_regs := control_regs m ;
       debug_regs := debug_regs m ; 
       pc_reg := v ;
       fpu_lastOperPtr := fpu_lastOperPtr m ;
       fpu_status := fpu_status m ;
       fpu_control := fpu_control m ;
       fpu_tags := fpu_tags m 
    |}.

  Definition set_fpu_regs r v m := 
    {| gp_regs := gp_regs m ;
       fpu_regs := upd fpu_register_eq_dec (fpu_regs m) r v ;
       seg_regs_starts := seg_regs_starts m ; 
       seg_regs_limits := seg_regs_limits m ;
       flags_reg := flags_reg m ;
       control_regs := control_regs m; 
       debug_regs := debug_regs m; 
       pc_reg := pc_reg m ;
       fpu_lastOperPtr := fpu_lastOperPtr m ;
       fpu_status := fpu_status m ;
       fpu_control := fpu_control m ;
       fpu_tags := fpu_tags m 
    |}.

  Definition set_fpu_lastOper r v m :=
   {|  gp_regs := gp_regs m ;
       fpu_regs := fpu_regs m ;
       seg_regs_starts := seg_regs_starts m ;
       seg_regs_limits := seg_regs_limits m ;
       flags_reg := flags_reg m ; 
       control_regs := control_regs m ;
       debug_regs := debug_regs m ; 
       pc_reg := pc_reg m ;
       fpu_lastOperPtr := upd fp_lastOperandPtr_register_eq_dec (fpu_lastOperPtr m) r v ;
       fpu_status := fpu_status m ;
       fpu_control := fpu_control m ;
       fpu_tags := fpu_tags m 
    |}.

  Definition set_fpu_status r v m :=
  {|   gp_regs := gp_regs m ;
       fpu_regs := fpu_regs m ;
       seg_regs_starts := seg_regs_starts m ;
       seg_regs_limits := seg_regs_limits m ;
       flags_reg := flags_reg m ; 
       control_regs := control_regs m ;
       debug_regs := debug_regs m ; 
       pc_reg := pc_reg m ;
       fpu_lastOperPtr := fpu_lastOperPtr m ;
       fpu_status := upd fp_status_register_eq_dec (fpu_status m) r v ;
       fpu_control := fpu_control m ;
       fpu_tags := fpu_tags m 
    |}.
  Definition set_fpu_control r v m :=
  {|   gp_regs := gp_regs m ;
       fpu_regs := fpu_regs m ;
       seg_regs_starts := seg_regs_starts m ;
       seg_regs_limits := seg_regs_limits m ;
       flags_reg := flags_reg m ; 
       control_regs := control_regs m ;
       debug_regs := debug_regs m ; 
       pc_reg := pc_reg m ;
       fpu_lastOperPtr := fpu_lastOperPtr m ;
       fpu_status := fpu_status m ;
       fpu_control := upd fp_control_register_eq_dec (fpu_control m) r v ;
       fpu_tags := fpu_tags m 
    |}.
  Definition set_fpu_tags r v m:=
  {|   gp_regs := gp_regs m ;
       fpu_regs := fpu_regs m ;
       seg_regs_starts := seg_regs_starts m ;
       seg_regs_limits := seg_regs_limits m ;
       flags_reg := flags_reg m ; 
       control_regs := control_regs m ;
       debug_regs := debug_regs m ; 
       pc_reg := pc_reg m ;
       fpu_lastOperPtr := fpu_lastOperPtr m ;
       fpu_status := fpu_status m ;
       fpu_control := fpu_control m ;
       fpu_tags := upd fp_tagWords_eq_dec (fpu_tags m) r v 
    |}.

  Definition set_location s (l:loc s) (v:int s) m := 
    match l in loc s' return int s' -> mach_state with 
      | reg_loc r => fun v => set_gp_regs r v m
      | seg_reg_start_loc r => fun v => set_seg_regs_starts r v m
      | seg_reg_limit_loc r => fun v => set_seg_regs_limits r v m
      | flag_loc f => fun v => set_flags_reg f v m
      | control_register_loc r => fun v => set_control_regs r v m
      | debug_register_loc r => fun v => set_debug_regs r v m
      | pc_loc => fun v => set_pc v m
      | fpu_reg_loc r => fun v => set_fpu_regs r v m
      | fpu_lastOperPtr_loc r => fun v => set_fpu_lastOper r v m 
      | fpu_st_loc r=> fun v => set_fpu_status r v m
      | fpu_cntrl_loc r=> fun v => set_fpu_control r v m
      | fpu_tag_loc r=> fun v => set_fpu_tags r v m
    end v.

End X86_MACHINE.

Module X86_RTL := RTL.RTL(X86_MACHINE).

Require Import List.

Module X86_Decode.
  Import X86_MACHINE.
  Import X86_RTL.
  Local Open Scope monad_scope.

  Record conv_state := { c_rev_i :list rtl_instr ; c_next : Z }.
  Definition Conv(T:Type) := conv_state -> T * conv_state.
  Instance Conv_monad : Monad Conv := {
    Return := fun A (x:A) (s:conv_state) => (x,s) ; 
    Bind := fun A B (c:Conv A) (f:A -> Conv B) (s:conv_state) => 
      let (v,s') := c s in f v s'
  }.
  intros ; apply Coqlib.extensionality ; auto.
  intros ; apply Coqlib.extensionality ; intros. destruct (c x). auto.
  intros ; apply Coqlib.extensionality ; intros. destruct (f x) ; auto. 
  Defined.
  Definition runConv (c:Conv unit) : (list rtl_instr) := 
    match c {|c_rev_i := nil ; c_next:=0|} with 
      | (_, c') => (List.rev (c_rev_i c'))
    end.
  Definition EMIT(i:rtl_instr) : Conv unit := 
    fun s => (tt,{|c_rev_i := i::(c_rev_i s) ; c_next := c_next s|}).
  Notation "'emit' i" := (EMIT i) (at level 75) : monad_scope.
  Definition fresh s (almost_i : pseudo_reg s -> rtl_instr) : Conv (pseudo_reg s) := 
    fun ts => let r := c_next ts in 
              let ts' := {|c_rev_i := (almost_i (ps_reg s r))::c_rev_i ts ; 
                           c_next := r + 1|} in 
                (ps_reg s r, ts').

  Definition load_Z s (i:Z) := fresh (load_imm_rtl (@Word.repr s i)).
  Definition load_int s (i:int s) := fresh (load_imm_rtl i).
  Definition arith s b (r1 r2:pseudo_reg s) := fresh (arith_rtl b r1 r2).
  Definition test s t (r1 r2:pseudo_reg s) := fresh (test_rtl t r1 r2).
  Definition load_reg (r:register) := fresh (get_loc_rtl (reg_loc r)).
  Definition set_reg (p:pseudo_reg size32) (r:register) := 
    emit set_loc_rtl p (reg_loc r).
  Definition load_fpu_reg (f_r : fpu_register) := fresh (get_loc_rtl (fpu_reg_loc f_r)).
  Definition set_fpu_reg (p: pseudo_reg size80) (f_r: fpu_register) :=
    emit set_loc_rtl p (fpu_reg_loc f_r).
  Definition cast_u s1 s2 (r:pseudo_reg s1) := fresh (@cast_u_rtl s1 s2 r).
  Definition cast_s s1 s2 (r:pseudo_reg s1) := fresh (@cast_s_rtl s1 s2 r).
  Definition get_seg_start (s:segment_register) := 
    fresh (get_loc_rtl (seg_reg_start_loc s)).
  Definition get_seg_limit (s:segment_register) := 
    fresh (get_loc_rtl (seg_reg_limit_loc s)).
  Definition read_byte (a:pseudo_reg size32) := fresh (get_byte_rtl a).
  Definition write_byte (v:pseudo_reg size8) (a:pseudo_reg size32) := 
    emit set_byte_rtl v a.
  Definition get_flag fl := fresh (get_loc_rtl (flag_loc fl)).
  Definition set_flag fl (r: pseudo_reg size1) := emit set_loc_rtl r (flag_loc fl). 
  Definition set_fpu_status fp_s (p: pseudo_reg size3) := emit set_loc_rtl p (fpu_st_loc fp_s).
  Definition get_fpu_status fp_s := fresh (get_loc_rtl (fpu_st_loc fp_s)).
  Definition set_fpu_tags tag_s (p: pseudo_reg size2) := emit set_loc_rtl p (fpu_tag_loc tag_s).
  Definition get_fpu_tags tag_s := fresh (get_loc_rtl (fpu_tag_loc tag_s)).
  Definition set_fpu_control cntrl_s (p: pseudo_reg size3) := emit set_loc_rtl p (fpu_cntrl_loc cntrl_s).
  Definition get_fpu_control cntrl_s := fresh (get_loc_rtl (fpu_cntrl_loc cntrl_s)).

  Definition get_pc := fresh (get_loc_rtl pc_loc).
  Definition set_pc v := emit set_loc_rtl v pc_loc.
  Definition not {s} (p: pseudo_reg s) : Conv (pseudo_reg s) :=
    mask <- load_Z s (Word.max_unsigned s);
    arith xor_op p mask.
  Definition undef_flag (f: flag) :=
    ps <- fresh (@choose_rtl size1);
    set_flag f ps.

  Definition int_to_fpu_reg_aux (sum : Z) : fpu_register := 
     match sum with
     | 0%Z => ST0
     | 1%Z => ST1
     | 2%Z => ST2
     | 3%Z => ST3
     | 4%Z => ST4
     | 5%Z => ST5
     | 6%Z => ST6   
     | _   => ST7 
     end.

  (*Returns an fpu register at position index, where top is the current stack top *)
  Definition int_to_fpu_reg (top index : pseudo_reg size3) : fpu_register := 
     let (t) := top in
     let (i) := index in
     let ind := Zmod (t + i) 8 in
     int_to_fpu_reg_aux ind.

  Definition fpu_from_int (fpu_index : int3) (top : pseudo_reg size3) : fpu_register := 
     let intv := Word.intval size3 fpu_index in
     int_to_fpu_reg top (ps_reg size3 intv).

  (* Copy the contents of rs to a new pseudo register *)
  Definition copy_ps s (rs:pseudo_reg s) := fresh (@cast_u_rtl s s rs).

  Definition scale_to_int32 (s:scale) : int32 :=
    Word.repr match s with | Scale1 => 1 | Scale2 => 2 | Scale4 => 4 | Scale8 => 8 end.

  (* compute an effective address *)
  Definition compute_addr(a:address) : Conv (pseudo_reg size32) := 
    let disp := addrDisp a in 
      match addrBase a, addrIndex a with 
        | None, None => load_int disp 
        | Some r, None => 
          p1 <- load_reg r ; p2 <- load_int disp ; arith add_op p1 p2
        | Some r1, Some (s, r2) =>
          b <- load_reg r1;
          i <- load_reg r2;
          s <- load_int (scale_to_int32 s);
          p0 <- arith mul_op i s;
          p1 <- arith add_op b p0;
          disp <- load_int disp;
          arith add_op p1 disp
        | None, Some (s, r) => 
          i <- load_reg r;
          s <- load_int (scale_to_int32 s);
          disp <- load_int disp;
          p0 <- arith mul_op i s;
          arith add_op disp p0
      end.

  (* check that the addr is not greater the segment_limit, and then 
     add the specified segment base *)
  Definition add_and_check_segment (seg:segment_register) (a:pseudo_reg size32) : 
    Conv (pseudo_reg size32) := 
    p1 <- get_seg_start seg ; 
    p2 <- arith add_op p1 a ;
    p3 <- get_seg_limit seg ;
    guard <- test ltu_op p3 a;
    emit if_rtl guard safe_fail_rtl;;
    ret p2.

  (* load a byte from memory, taking into account the specified segment *)
  Definition lmem (seg:segment_register) (a:pseudo_reg size32) : Conv (pseudo_reg size8):=
    p <- add_and_check_segment seg a ; 
    read_byte p.

  (* store a byte to memory, taking into account the specified segment *)
  Definition smem (seg:segment_register) (v:pseudo_reg size8) (a:pseudo_reg size32) :
    Conv unit := 
    p <- add_and_check_segment seg a ; 
    write_byte v p.

  (* load an n-byte vector from memory -- takes into account the segment *)
  Program Fixpoint load_mem_n (seg:segment_register) (addr:pseudo_reg size32)
    (nbytes_minus_one:nat) : Conv (pseudo_reg ((nbytes_minus_one+1) * 8 -1)%nat) := 
    match nbytes_minus_one with 
      | 0 => lmem seg addr
      | S n => 
        rec <- load_mem_n seg addr n ; 
        count <- load_Z size32 (Z_of_nat (S n)) ; 
        p3 <- arith add_op addr count ;
        nb <- lmem seg p3 ; 
        p5 <- cast_u ((nbytes_minus_one + 1)*8-1)%nat rec ; 
        p6 <- cast_u ((nbytes_minus_one + 1)*8-1)%nat nb ;
        p7 <- load_Z _ (Z_of_nat (S n) * 8) ;
        p8 <- arith shl_op p6 p7 ;
        arith or_op p5 p8
    end.

  Definition load_mem80 (seg : segment_register)(addr:pseudo_reg size32) := 
    load_mem_n seg addr 9.

  Definition load_mem64 (seg : segment_register) (addr: pseudo_reg size32) := 
    load_mem_n seg addr 7.

  Definition load_mem32 (seg:segment_register) (addr:pseudo_reg size32) := 
    load_mem_n seg addr 3.

  (*Definition load_mem32 (seg: segment_register) (addr: pseudo_reg size32) :=
    b0 <- lmem seg addr;
    one <- load_Z size32 1;
    addr1 <- arith add_op addr one;
    b1 <- lmem seg addr1;
    addr2 <- arith add_op addr1 one;
    b2 <- lmem seg addr2;
    addr3 <- arith add_op addr2 one;
    b3 <- lmem seg addr3;

    w0 <- cast_u size32 b0;
    w1 <- cast_u size32 b1;
    w2 <- cast_u size32 b2;
    w3 <- cast_u size32 b3;
    eight <- load_Z size32 8;
    r0 <- arith shl_op w3 eight;
    r1 <- arith or_op r0 w2;
    r2 <- arith shl_op r1 eight;
    r3 <- arith or_op r2 w1;
    r4 <- arith shl_op r3 eight;
    arith or_op r4 w0.*)
    

  Definition load_mem16 (seg:segment_register) (addr:pseudo_reg size32) := 
    load_mem_n seg addr 1.
  Definition load_mem8 (seg:segment_register) (addr:pseudo_reg size32) := 
    load_mem_n seg addr 0.

  (* given a prefix and w bit, return the size of the operand *)
  Definition opsize override w :=
    match override, w with
      | _, false => size8
      | true, _ => size16
      | _,_ => size32
    end.

  Definition load_mem p w (seg:segment_register) (op:pseudo_reg size32) : 
    Conv (pseudo_reg (opsize (op_override p) w)) :=
    match (op_override p) as b,w return
      Conv (pseudo_reg (opsize b w)) with
      | true, true => load_mem16 seg op
      | true, false => load_mem8 seg op
      | false, true => load_mem32 seg op
      | false, false => load_mem8 seg op
    end.

  Definition iload_op32 (seg:segment_register) (op:operand) : Conv (pseudo_reg size32) :=
    match op with 
      | Imm_op i => load_int i
      | Reg_op r => load_reg r
      | Address_op a => p1 <- compute_addr a ; load_mem32 seg p1
      | Offset_op off => p1 <- load_int off;
                          load_mem32 seg p1
    end.

  Definition iload_op16 (seg:segment_register) (op:operand) : Conv (pseudo_reg size16) :=
    match op with 
      | Imm_op i => tmp <- load_int i;
                    cast_u size16 tmp
      | Reg_op r => tmp <- load_reg r;
                    cast_u size16 tmp
      | Address_op a => p1 <- compute_addr a ; load_mem16 seg p1
      | Offset_op off => p1 <- load_int off;
                          load_mem16 seg p1
    end.

  (* This is a little strange because actually for example, ESP here should refer
     to AH, EBP to CH, ESI to DH, and EDI to BH *) 

  Definition iload_op8 (seg:segment_register) (op:operand) : Conv (pseudo_reg size8) :=
    match op with 
      | Imm_op i => tmp <- load_int i;
                    cast_u size8 tmp
      | Reg_op r =>
         tmp <- load_reg (match r with
                            | EAX => EAX
                            | ECX => ECX
                            | EDX => EDX
                            | EBX => EBX
                            | ESP => EAX
                            | EBP => ECX
                            | ESI => EDX
                            | EDI => EBX
                          end);
         (match r with
            | EAX | ECX | EDX | EBX => cast_u size8 tmp
            | _ =>  eight <- load_Z size32 8;
                    tmp2 <- arith shru_op tmp eight;
                    cast_u size8 tmp2
          end)
      | Address_op a => p1 <- compute_addr a ; load_mem8 seg p1
      | Offset_op off =>  p1 <- load_int off;
                          load_mem8 seg p1
    end.

  (* set memory with an n-byte vector *)
  Program Fixpoint set_mem_n {t} (seg:segment_register)
    (v: pseudo_reg (8*(t+1)-1)%nat) (addr : pseudo_reg size32) : Conv unit := 
    match t with 
      | 0 => smem seg v addr
      | S u => 
        p1 <- cast_u (8*(u+1)-1)%nat v ; 
        set_mem_n seg p1 addr ;; 
        p2 <- load_Z (8*(t+1)-1)%nat (Z_of_nat  ((S u) * 8)) ; 
        p3 <- arith shru_op v p2 ;
        p4 <- cast_u size8 p3 ; 
        p5 <- load_Z size32 (Z_of_nat (S u)) ; 
        p6 <- arith add_op p5 addr ;
        smem seg p4 p6
    end.


  Definition set_mem80 (seg: segment_register) (v: pseudo_reg size80) (a: pseudo_reg size32) : Conv unit :=
    @set_mem_n 9 seg v a.  

  Definition set_mem64 (seg : segment_register) (v : pseudo_reg size64) (a : pseudo_reg size32) : Conv unit := 
    @set_mem_n 7 seg v a.

  Definition set_mem32 (seg:segment_register) (v a:pseudo_reg size32) : Conv unit :=
    @set_mem_n 3 seg v a.

  (*Definition set_mem32 (seg: segment_register) (v a: pseudo_reg size32) : Conv unit := 
    b0 <- cast_u size8 v;
    smem seg b0 a;;
    eight <- load_Z size32 8;
    one <- load_Z size32 1;
    v1 <- arith shru_op v eight;
    b1 <- cast_u size8 v1;
    addr1 <- arith add_op a one;
    smem seg b1 addr1;;
    v2 <- arith shru_op v1 eight;
    b2 <- cast_u size8 v2;
    addr2 <- arith add_op addr1 one;
    smem seg b2 addr2;;
    v3 <- arith shru_op v2 eight;
    b3 <- cast_u size8 v3;
    addr3 <- arith add_op addr2 one;
    smem seg b3 addr3.*)
    

  Definition set_mem16 (seg:segment_register) (v: pseudo_reg size16)
    (a:pseudo_reg size32) : Conv unit :=
      @set_mem_n 1 seg v a.

  Definition set_mem8 (seg:segment_register) (v: pseudo_reg size8) 
    (a:pseudo_reg size32) : Conv unit :=
      @set_mem_n 0 seg v a.

 Definition set_mem p w (seg:segment_register) : pseudo_reg (opsize (op_override p) w) ->
    pseudo_reg size32 -> 
    Conv unit :=
    match (op_override p) as b,w return
      pseudo_reg (opsize b w) -> pseudo_reg size32 -> Conv unit with
      | true, true => set_mem16 seg
      | true, false => set_mem8 seg
      | false, true => set_mem32 seg
      | false, false => set_mem8 seg
    end.
  (* update an operand *)
  Definition iset_op80 (seg:segment_register) (p:pseudo_reg size80) (op:operand) :
    Conv unit := 
    match op with 
      | Imm_op _ => emit error_rtl
      | Reg_op r => tmp <- cast_u size32 p;
                    set_reg tmp r
      | Address_op a => addr <- compute_addr a ; tmp <- cast_u size32 p;
                        set_mem32 seg tmp addr
      | Offset_op off => addr <- load_int off; tmp <- cast_u size32 p;
                        set_mem32 seg tmp addr
    end.

  Definition iset_op32 (seg:segment_register) (p:pseudo_reg size32) (op:operand) :
    Conv unit := 
    match op with 
      | Imm_op _ => emit error_rtl
      | Reg_op r => set_reg p r
      | Address_op a => addr <- compute_addr a ; set_mem32 seg p addr
      | Offset_op off => addr <- load_int off;
                           set_mem32 seg p addr
    end.

  Definition iset_op16 (seg:segment_register) (p:pseudo_reg size16) (op:operand) :
    Conv unit := 
    match op with 
      | Imm_op _ => emit error_rtl
      | Reg_op r => tmp <- load_reg r;
                    mask <- load_int (Word.mone size32);
                    sixteen <- load_Z size32 16;
                    mask2 <- arith shl_op mask sixteen ;
                    tmp2  <- arith and_op mask2 tmp;
                    p32 <- cast_u size32 p;
                    tmp3 <- arith or_op tmp2 p32;
                    set_reg tmp3 r
      | Address_op a => addr <- compute_addr a ; set_mem16 seg p addr
      | Offset_op off => addr <- load_int off;
                           set_mem16 seg p addr
    end.

  Definition iset_op8 (seg:segment_register) (p:pseudo_reg size8) (op:operand) :
    Conv unit := 
    match op with 
      | Imm_op _ => emit error_rtl
      | Reg_op r => tmp0 <- load_reg 
                         (match r with
                            | EAX => EAX
                            | ECX => ECX
                            | EDX => EDX
                            | EBX => EBX
                            | ESP => EAX
                            | EBP => ECX
                            | ESI => EDX
                            | EDI => EBX
                          end);
                    shift <- load_Z size32
                             (match r with
                                | EAX | ECX | EDX | EBX => 0
                                | _ => 8
                              end);
                    mone <- load_int (Word.mone size32);
                    mask0 <-load_Z size32 255;
                    mask1 <- arith shl_op mask0 shift;
                    mask2 <- arith xor_op mask1 mone;
                    tmp1 <- arith and_op tmp0 mask2;
                    pext <- cast_u size32 p;
                    pext_shift <- arith shl_op pext shift;
                    res <- arith or_op tmp1 pext_shift;
                    set_reg res
                         (match r with
                            | EAX => EAX
                            | ECX => ECX
                            | EDX => EDX
                            | EBX => EBX
                            | ESP => EAX
                            | EBP => ECX
                            | ESI => EDX
                            | EDI => EBX
                          end)
      | Address_op a => addr <- compute_addr a ; set_mem8 seg p addr
      | Offset_op off => addr <- load_int off;
                           set_mem8 seg p addr
    end.
  (* given a prefix and w bit, return the appropriate load function for the
     corresponding operand size *)
  Definition load_op p w (seg:segment_register) (op:operand)
    : Conv (pseudo_reg (opsize (op_override p) w)) :=
    match op_override p as b, w return 
      Conv (pseudo_reg (opsize b w)) with
      | true, true => iload_op16 seg op
      | true, false => iload_op8 seg op
      | false, true => iload_op32 seg op
      | false, false => iload_op8 seg op
    end.

  Definition set_op p w (seg:segment_register) :
     pseudo_reg (opsize (op_override p) w) -> operand -> Conv unit :=
    match op_override p as b, w 
      return pseudo_reg (opsize b w) -> operand -> Conv unit with
      | true, true => iset_op16 seg 
      | true, false => iset_op8 seg
      | false, true => iset_op32 seg 
      | false, false => iset_op8 seg
    end.
  
  (* given a prefix, get the override segment and if none is specified return def *)
  Definition get_segment (p:prefix) (def:segment_register) : segment_register := 
    match seg_override p with 
      | Some s => s 
      | None => def
    end.

  Definition op_contains_stack (op:operand) : bool :=
    match op with
      |Address_op a =>
        match (addrBase a) with
          |Some EBP => true
          |Some ESP => true
          | _ => false
        end
      | _ => false
    end.

  (*The default segment when an operand uses ESP or EBP as a base address
     is the SS segment*)
  Definition get_segment_op (p:prefix) (def:segment_register) (op:operand)
    : segment_register := 
    match seg_override p with 
      | Some s => s 
      | None => 
        match (op_contains_stack op) with
          | true => SS
          | false => def
        end
    end.
  Definition get_segment_op2 (p:prefix) (def:segment_register) (op1:operand)
    (op2: operand) : segment_register := 
    match seg_override p with 
      | Some s => s 
      | None => 
        match (op_contains_stack op1,op_contains_stack op2) with
          | (true,_) => SS
          | (_,true) => SS
          | (false,false) => def
        end
    end.

  Definition compute_cc (ct: condition_type) : Conv (pseudo_reg size1) :=
    match ct with
      | O_ct => get_flag OF
      | NO_ct => p <- get_flag OF;
        not p
      | B_ct => get_flag CF
      | NB_ct => p <- get_flag CF;
        not p
      | E_ct => get_flag ZF
      | NE_ct => p <- get_flag ZF;
        not p
      | BE_ct => cf <- get_flag CF;
        zf <- get_flag ZF;
        arith or_op cf zf
      | NBE_ct => cf <- get_flag CF;
        zf <- get_flag ZF;
        p <- arith or_op cf zf;
        not p
      | S_ct => get_flag SF
      | NS_ct => p <- get_flag SF;
        not p
      | P_ct => get_flag PF
      | NP_ct => p <- get_flag PF;
        not p
      | L_ct => sf <- get_flag SF;
        of <- get_flag OF;
        arith xor_op sf of
      | NL_ct => sf <- get_flag SF;
        of <- get_flag OF;
        p <- arith xor_op sf of;
        not p
      | LE_ct => zf <- get_flag ZF;
        of <- get_flag OF;
        sf <- get_flag SF;
        p <- arith xor_op of sf;
        arith or_op zf p
      | NLE_ct => zf <- get_flag ZF;
        of <- get_flag OF;
        sf <- get_flag SF;
        p0 <- arith xor_op of sf;
        p1 <- arith or_op zf p0;
        not p1
    end.

  Fixpoint compute_parity_aux {s} op1 (op2 : pseudo_reg size1) (n: nat) :
    Conv (pseudo_reg size1) :=
    match n with
      | O => @load_Z size1 0
      | S m =>
        op2 <- compute_parity_aux op1 op2 m;
        one <- load_Z s 1;
        op1 <- arith shru_op op1 one; 
        r <- cast_u size1 op1;
        @arith size1 xor_op r op2
    end.
  
  Definition compute_parity {s} op : Conv (pseudo_reg size1) := 
    r1 <- load_Z size1 0;
    one <- load_Z size1 1;
    p <- @compute_parity_aux s op r1 8; (* ACHTUNG *)
    arith xor_op p one.

  (**********************************************)
  (*   Conversion functions for instructions    *)
  (**********************************************)

  (************************)
  (* Arith ops            *)
  (************************)
  Definition conv_INC (pre:prefix) (w: bool) (op:operand) : Conv unit :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    let seg := get_segment_op pre DS op in 
        p0 <- load seg op ; 
        p1 <- load_Z _ 1 ; 
        p2 <- arith add_op p0 p1 ; 
        set seg p2 op;;

        (* Note that CF is NOT changed by INC *)

        zero <- load_Z _ 0;
        ofp <- test lt_op p2 p0;
        set_flag OF ofp;;

        zfp <- test eq_op p2 zero;
        set_flag ZF zfp;;

        sfp <- test lt_op p2 zero;
        set_flag SF sfp;;

        pfp <- compute_parity p2;
        set_flag PF pfp;;

        n0 <- cast_u size4 p0;
        n1 <- load_Z size4 1;
        n2 <- arith add_op n0 n1;
        afp <- test ltu_op n2 n0;
        set_flag AF afp.

  Definition conv_DEC (pre: prefix) (w: bool) (op: operand) : Conv unit :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    let seg := get_segment_op pre DS op in
        p0 <- load seg op;
        p1 <- load_Z _ 1;
        p2 <- arith sub_op p0 p1;
        set seg p2 op;;

        (* Note that CF is NOT changed by DEC *)
        zero <- load_Z _ 0;
        ofp <- test lt_op p0 p2; 
        set_flag OF ofp;;

        zfp <- test eq_op p2 zero;
        set_flag ZF zfp;;
        
        sfp <- test lt_op p2 zero;
        set_flag SF sfp;;

        pfp <- compute_parity p2;
        set_flag PF pfp;;

        n0 <- cast_u size4 p0;
        n1 <- load_Z size4 1;
        n2 <- arith sub_op n0 n1;
        afp <- test ltu_op n0 n2;
        set_flag AF afp.

  Definition conv_ADC (pre: prefix) (w: bool) (op1 op2: operand) : Conv unit :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    let seg := get_segment_op2 pre DS op1 op2 in
        (* RTL for useful constants *)
        zero <- load_Z _ 0;
        up <- load_Z _ 1;

        (* RTL for op1 *)
        p0 <- load seg op1;
        p1 <- load seg op2;
        cf1 <- get_flag CF;
        cfext <- cast_u _ cf1; 
        p2 <- arith add_op p0 p1;
        p2 <- arith add_op p2 cfext;
        set seg p2 op1;;        

        (* RTL for OF *)
        b0 <- test lt_op zero p0;
        b1 <- test lt_op zero p1;
        b2 <- test lt_op zero p2;
        b3 <- @arith size1 xor_op b0 b1;
        b3 <- @arith size1 xor_op up b3;
        b4 <- @arith size1 xor_op b0 b2;
        b4 <- @arith size1 and_op b3 b4;
        set_flag OF b4;;

        (* RTL for CF *)
        b0 <- test ltu_op p2 p0;
        b1 <- test ltu_op p2 p1;
        b0 <- @arith size1 or_op b0 b1;
        set_flag CF b0;;

        (* RTL for ZF *)
        b0 <- test eq_op p2 zero;
        set_flag ZF b0;;

        (* RTL for SF *)
        b0 <- test lt_op p2 zero;
        set_flag SF b0;;

        (* RTL for PF *)
        b0 <- compute_parity p2;
        set_flag PF b0;;

        (* RTL for AF *)
        n0 <- cast_u size4 p0;
        n1 <- cast_u size4 p1;
        cf4 <- cast_u size4 cf1;
        n2 <- @arith size4 add_op n0 n1;
        n2 <- @arith size4 add_op n2 cf4;
        b0 <- test ltu_op n2 n0;
        b1 <- test ltu_op n2 n1;
        b0 <- @arith size1 or_op b0 b1;
        set_flag AF b0.

Definition conv_STC: Conv unit :=
  one <- load_Z size1 1;
  set_flag CF one.

Definition conv_STD: Conv unit :=
  one <- load_Z size1 1;
  set_flag DF one. 

Definition conv_CLC: Conv unit :=
  zero <- load_Z size1 0;
  set_flag CF zero.

Definition conv_CLD: Conv unit :=
  zero <- load_Z size1 0;
  set_flag DF zero.

Definition conv_CMC: Conv unit :=
  zero <- load_Z size1 0;
  p1 <- get_flag CF;
  p0 <- test eq_op zero p1;
  set_flag CF p0.

Definition conv_LAHF: Conv unit :=
  dst <- load_Z size8 0;

  fl <- get_flag SF;
  pos <- load_Z size8 7;
  byt <- cast_u size8 fl;  
  tmp <- @arith size8 shl_op byt pos;  
  dst <- @arith size8 or_op dst tmp; 

  fl <- get_flag ZF;
  pos <- load_Z size8 6;
  byt <- cast_u size8 fl;  
  tmp <- @arith size8 shl_op byt pos;  
  dst <- @arith size8 or_op dst tmp; 

  fl <- get_flag AF;
  pos <- load_Z size8 4;
  byt <- cast_u size8 fl;  
  tmp <- @arith size8 shl_op byt pos;  
  dst <- @arith size8 or_op dst tmp; 

  fl <- get_flag PF;
  pos <- load_Z size8 2;
  byt <- cast_u size8 fl;  
  tmp <- @arith size8 shl_op byt pos;  
  dst <- @arith size8 or_op dst tmp; 

  fl <- get_flag CF;
  pos <- load_Z size8 0;
  byt <- cast_u size8 fl;  
  tmp <- @arith size8 shl_op byt pos;  
  dst <- @arith size8 or_op dst tmp; 

  fl <- load_Z size8 1;
  pos <- load_Z size8 1;
  byt <- cast_u size8 fl;  
  tmp <- @arith size8 shl_op byt pos;  
  dst <- @arith size8 or_op dst tmp; 

  iset_op8 DS dst (Reg_op ESP).

Definition conv_SAHF: Conv unit :=
  one <- load_Z size8 1;
  ah <- iload_op8 DS (Reg_op ESP);

  pos <- load_Z size8 7;
  tmp <- @arith size8 shr_op ah pos;
  tmp <- @arith size8 and_op tmp one;
  b <- test eq_op one tmp;
  set_flag SF b;;

  pos <- load_Z size8 6;
  tmp <- @arith size8 shr_op ah pos;
  tmp <- @arith size8 and_op tmp one;
  b <- test eq_op one tmp;
  set_flag ZF b;;

  pos <- load_Z size8 4;
  tmp <- @arith size8 shr_op ah pos;
  tmp <- @arith size8 and_op tmp one;
  b <- test eq_op one tmp;
  set_flag AF b;;

  pos <- load_Z size8 2;
  tmp <- @arith size8 shr_op ah pos;
  tmp <- @arith size8 and_op tmp one;
  b <- test eq_op one tmp;
  set_flag PF b;;

  pos <- load_Z size8 0;
  tmp <- @arith size8 shr_op ah pos;
  tmp <- @arith size8 and_op tmp one;
  b <- test eq_op one tmp;
  set_flag CF b. 


  Definition conv_ADD (pre: prefix) (w: bool) (op1 op2: operand) : Conv unit :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    let seg := get_segment_op2 pre DS op1 op2 in
        (* RTL for useful constants *)
        zero <- load_Z _ 0;
        up <- load_Z size1 1;

        (* RTL for op1 *)
        p0 <- load seg op1;
        p1 <- load seg op2;
        p2 <- arith add_op p0 p1;
        set seg p2 op1;;        

        (* RTL for OF *)
        b0 <- test lt_op zero p0;
        b1 <- test lt_op zero p1;
        b2 <- test lt_op zero p2;
        b3 <- @arith size1 xor_op b0 b1;
        b3 <- @arith size1 xor_op up b3;
        b4 <- @arith size1 xor_op b0 b2;
        b4 <- @arith size1 and_op b3 b4;
        set_flag OF b4;;

        (* RTL for CF *)
        b0 <- test ltu_op p2 p0;
        b1 <- test ltu_op p2 p1;
        b0 <- @arith size1 or_op b0 b1;
        set_flag CF b0;;

        (* RTL for ZF *)
        b0 <- test eq_op p2 zero;
        set_flag ZF b0;;

        (* RTL for SF *)
        b0 <- test lt_op p2 zero;
        set_flag SF b0;;

        (* RTL for PF *)
        b0 <- compute_parity p2;
        set_flag PF b0;;

        (* RTL for AF *)
        n0 <- cast_u size4 p0;
        n1 <- cast_u size4 p1;
        n2 <- @arith size4 add_op n0 n1;
        b0 <- test ltu_op n2 n0;
        b1 <- test ltu_op n2 n1;
        b0 <- @arith size1 or_op b0 b1;
        set_flag AF b0.


  (* If e is true, then this is sub, otherwise it's cmp 
     Dest is equal to op1 for the case of SUB,
     but it's equal to op2 for the case of NEG
     
     We use segdest, seg1, seg2 to specify which segment
     registers to use for the destination, op1, and op2.
     This is because for CMPS, only the first operand's 
     segment can be overriden. 
  *) 

  Definition conv_SUB_CMP_generic (e: bool) (pre: prefix) (w: bool) (dest: operand) (op1 op2: operand) 
    (segdest seg1 seg2: segment_register) :=
    let load := load_op pre w in 
    let set := set_op pre w in 
        (* RTL for useful constants *)
        zero <- load_Z _ 0;
        up <- load_Z size1 1;

        (* RTL for op1 *)
        p0 <- load seg1 op1;
        p1 <- load seg2 op2;
        p2 <- arith sub_op p0 p1;

        (* RTL for OF *)
        negp1 <- arith sub_op zero p1;
        b0 <- test lt_op zero p0;
        b1 <- test lt_op zero negp1;
        b2 <- test lt_op zero p2;
        b3 <- @arith size1 xor_op b0 b1;
        b3 <- @arith size1 xor_op up b3;
        b4 <- @arith size1 xor_op b0 b2;
        b4 <- @arith size1 and_op b3 b4;
        set_flag OF b4;;

        (* RTL for CF *)
        b0 <- test ltu_op p0 p1;
        set_flag CF b0;;

        (* RTL for ZF *)
        b0 <- test eq_op p2 zero;
        set_flag ZF b0;;

        (* RTL for SF *)
        b0 <- test lt_op p2 zero;
        set_flag SF b0;;

        (* RTL for PF *)
        b0 <- compute_parity p2;
        set_flag PF b0;;

        (* RTL for AF *)
        n0 <- cast_u size4 p0;
        n1 <- cast_u size4 p1;
        b0 <- test ltu_op p0 p1;
        set_flag AF b0;;

        if e then
          set segdest p2 dest
        else 
          ret tt.

  Definition conv_CMP (pre: prefix) (w: bool) (op1 op2: operand) :=
    let seg := get_segment_op2 pre DS op1 op2 in
    conv_SUB_CMP_generic false pre w op1 op1 op2 seg seg seg.
  Definition conv_SUB (pre: prefix) (w: bool) (op1 op2: operand) :=
    let seg := get_segment_op2 pre DS op1 op2 in
    conv_SUB_CMP_generic true pre w op1 op1 op2 seg seg seg.
  Definition conv_NEG (pre: prefix) (w: bool) (op1: operand) :=
    let seg := get_segment_op pre DS op1 in
    conv_SUB_CMP_generic true pre w op1 (Imm_op Word.zero) op1 seg seg seg.

  Definition conv_SBB (pre: prefix) (w: bool) (op1 op2: operand) :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    let seg := get_segment_op2 pre DS op1 op2 in
        (* RTL for useful constants *)
        zero <- load_Z _ 0;
        up <- load_Z size1 1;
        
        old_cf <- get_flag CF;
        old_cf_ext <- cast_u _ old_cf;
        (* RTL for op1 *)
        p0 <- load seg op1;
        p1 <- load seg op2;
        p2_0 <- arith sub_op p0 p1;
        p2 <- arith sub_op p2_0 old_cf_ext;

        (* RTL for OF *)
        negp1 <- arith sub_op zero p1;
        b0 <- test lt_op zero p0;
        b1 <- test lt_op zero negp1;
        b2 <- test lt_op zero p2;
        b3 <- @arith size1 xor_op b0 b1;
        b3 <- @arith size1 xor_op up b3;
        b4 <- @arith size1 xor_op b0 b2;
        b4 <- @arith size1 and_op b3 b4;
        set_flag OF b4;;

        (* RTL for CF *)
        b0' <- test ltu_op p0 p1;
        b0'' <- test eq_op p0 p1;
        b0 <- arith or_op b0' b0'';
        set_flag CF b0;;

        (* RTL for ZF *)
        b0 <- test eq_op p2 zero;
        set_flag ZF b0;;

        (* RTL for SF *)
        b0 <- test lt_op p2 zero;
        set_flag SF b0;;

        (* RTL for PF *)
        b0 <- compute_parity p2;
        set_flag PF b0;;

        (* RTL for AF *)
        n0 <- cast_u size4 p0;
        n1 <- cast_u size4 p1;
        b0' <- test ltu_op p0 p1;
        b0'' <- test eq_op p0 p1;
        b0 <- arith or_op b0' b0'';
        set_flag AF b0;;
        set seg p2 op1.

  (* I tried refactoring this so that it was smaller, but the way I did
     it caused type-checking to seem to go on FOREVER - maybe someone more 
     clever can figure out how to clean this up *)

  Definition conv_DIV (pre: prefix) (w: bool) (op: operand) :=
    let seg := get_segment_op pre DS op in
      undef_flag CF;;
      undef_flag OF;;
      undef_flag SF;;
      undef_flag ZF;;
      undef_flag AF;;
      undef_flag PF;;
      match op_override pre, w with
        | _, false => dividend <- iload_op16 seg (Reg_op EAX);
                      divisor <- iload_op8 seg op;
                      zero <- load_Z _ 0;
                      divide_by_zero <- test eq_op zero divisor;
                      emit if_rtl divide_by_zero safe_fail_rtl;;
                      divisor_ext <- cast_u _ divisor;
                      quotient <- arith divu_op dividend divisor_ext;
                      max_quotient <- load_Z _ 255;
                      div_error <- test ltu_op max_quotient quotient;
                      emit if_rtl div_error safe_fail_rtl;;
                      remainder <- arith modu_op dividend divisor_ext;
                      quotient_trunc <- cast_u _ quotient;
                      remainder_trunc <- cast_u _ remainder;
                      iset_op8 seg quotient_trunc (Reg_op EAX);;
                      iset_op8 seg remainder_trunc (Reg_op ESP) (* This is AH *)
       | true, true => dividend_lower <- iload_op16 seg (Reg_op EAX);
                       dividend_upper <- iload_op16 seg (Reg_op EDX);
                       dividend0 <- cast_u size32 dividend_upper;
                       sixteen <- load_Z size32 16;
                       dividend1 <- arith shl_op dividend0 sixteen;
                       dividend_lower_ext <- cast_u size32 dividend_lower;
                       dividend <- arith or_op dividend1 dividend_lower_ext;
                       divisor <- iload_op16 seg op;
                       zero <- load_Z _ 0;
                       divide_by_zero <- test eq_op zero divisor;
                       emit if_rtl divide_by_zero safe_fail_rtl;;
                       divisor_ext <- cast_u _ divisor;
                       quotient <- arith divu_op dividend divisor_ext;
                       max_quotient <- load_Z _ 65535;
                       div_error <- test ltu_op max_quotient quotient;
                       emit if_rtl div_error safe_fail_rtl;;
                       remainder <- arith modu_op dividend divisor_ext;
                       quotient_trunc <- cast_u _ quotient;
                       remainder_trunc <- cast_u _ remainder;
                       iset_op16 seg quotient_trunc (Reg_op EAX);;
                       iset_op16 seg remainder_trunc (Reg_op EDX) 
       | false, true => dividend_lower <- iload_op32 seg (Reg_op EAX);
                       dividend_upper <- iload_op32 seg (Reg_op EDX);
                       dividend0 <- cast_u 63 dividend_upper;
                       thirtytwo <- load_Z 63 32;
                       dividend1 <- arith shl_op dividend0 thirtytwo;
                       dividend_lower_ext <- cast_u _ dividend_lower;
                       dividend <- arith or_op dividend1 dividend_lower_ext;
                       divisor <- iload_op32 seg op;
                       zero <- load_Z _ 0;
                       divide_by_zero <- test eq_op zero divisor;
                       emit if_rtl divide_by_zero safe_fail_rtl;;
                       divisor_ext <- cast_u _ divisor;
                       quotient <- arith divu_op dividend divisor_ext;
                       max_quotient <- load_Z _ 4294967295;
                       div_error <- test ltu_op max_quotient quotient;
                       emit if_rtl div_error safe_fail_rtl;;
                       remainder <- arith modu_op dividend divisor_ext;
                       quotient_trunc <- cast_u _ quotient;
                       remainder_trunc <- cast_u _ remainder;
                       iset_op32 seg quotient_trunc (Reg_op EAX);;
                       iset_op32 seg remainder_trunc (Reg_op EDX) 
     end.

  Definition conv_IDIV (pre: prefix) (w: bool) (op: operand) :=
    let seg := get_segment_op pre DS op in
      undef_flag CF;;
      undef_flag OF;;
      undef_flag SF;;
      undef_flag ZF;;
      undef_flag AF;;
      undef_flag PF;;
      match op_override pre, w with
        | _, false => dividend <- iload_op16 seg (Reg_op EAX);
                      divisor <- iload_op8 seg op;
                      zero <- load_Z _ 0;
                      divide_by_zero <- test eq_op zero divisor;
                      emit if_rtl divide_by_zero safe_fail_rtl;;
                      divisor_ext <- cast_s _ divisor;
                      quotient <- arith divs_op dividend divisor_ext;
                      max_quotient <- load_Z _ 127;
                      min_quotient <- load_Z _ (-128);
                      div_error0 <- test lt_op max_quotient quotient;
                      div_error1 <- test lt_op quotient min_quotient;
                      div_error <- arith or_op div_error0 div_error1;
                      emit if_rtl div_error safe_fail_rtl;;
                      remainder <- arith mods_op dividend divisor_ext;
                      quotient_trunc <- cast_s _ quotient;
                      remainder_trunc <- cast_s _ remainder;
                      iset_op8 seg quotient_trunc (Reg_op EAX);;
                      iset_op8 seg remainder_trunc (Reg_op ESP) (* This is AH *)
       | true, true => dividend_lower <- iload_op16 seg (Reg_op EAX);
                       dividend_upper <- iload_op16 seg (Reg_op EDX);
                       dividend0 <- cast_s size32 dividend_upper;
                       sixteen <- load_Z size32 16;
                       dividend1 <- arith shl_op dividend0 sixteen;
                       dividend_lower_ext <- cast_s size32 dividend_lower;
                       dividend <- arith or_op dividend1 dividend_lower_ext;
                       divisor <- iload_op16 seg op;
                       zero <- load_Z _ 0;
                       divide_by_zero <- test eq_op zero divisor;
                       emit if_rtl divide_by_zero safe_fail_rtl;;
                       divisor_ext <- cast_s _ divisor;
                       quotient <- arith divs_op dividend divisor_ext;
                       max_quotient <- load_Z _ 32767;
                       min_quotient <- load_Z _ (-32768);
                       div_error0 <- test lt_op max_quotient quotient;
                       div_error1 <- test lt_op quotient min_quotient;
                       div_error <- arith or_op div_error0 div_error1;
                       emit if_rtl div_error safe_fail_rtl;;
                       remainder <- arith mods_op dividend divisor_ext;
                       quotient_trunc <- cast_s _ quotient;
                       remainder_trunc <- cast_s _ remainder;
                       iset_op16 seg quotient_trunc (Reg_op EAX);;
                       iset_op16 seg remainder_trunc (Reg_op EDX) 
       | false, true => dividend_lower <- iload_op32 seg (Reg_op EAX);
                       dividend_upper <- iload_op32 seg (Reg_op EDX);
                       dividend0 <- cast_s 63 dividend_upper;
                       thirtytwo <- load_Z 63 32;
                       dividend1 <- arith shl_op dividend0 thirtytwo;
                       dividend_lower_ext <- cast_s _ dividend_lower;
                       dividend <- arith or_op dividend1 dividend_lower_ext;
                       divisor <- iload_op32 seg op;
                       zero <- load_Z _ 0;
                       divide_by_zero <- test eq_op zero divisor;
                       emit if_rtl divide_by_zero safe_fail_rtl;;
                       divisor_ext <- cast_s _ divisor;
                       quotient <- arith divs_op dividend divisor_ext;
                       max_quotient <- load_Z _ 2147483647;
                       min_quotient <- load_Z _ (-2147483648);
                       div_error0 <- test lt_op max_quotient quotient;
                       div_error1 <- test lt_op quotient min_quotient;
                       div_error <- arith or_op div_error0 div_error1;
                       emit if_rtl div_error safe_fail_rtl;;
                       remainder <- arith mods_op dividend divisor_ext;
                       quotient_trunc <- cast_s _ quotient;
                       remainder_trunc <- cast_s _ remainder;
                       iset_op32 seg quotient_trunc (Reg_op EAX);;
                       iset_op32 seg remainder_trunc (Reg_op EDX) 
     end.

  Program Definition conv_IMUL (pre: prefix) (w: bool) (op1: operand) 
    (opopt2: option operand) (iopt: option int32) :=
    undef_flag SF;;
    undef_flag ZF;;
    undef_flag AF;;
    undef_flag PF;;
    (match opopt2 with | None => let load := load_op pre w in
                let seg := get_segment_op pre DS op1 in
                 p1 <- load seg (Reg_op EAX);
                 p2 <- load seg op1;
                 p1ext <- cast_s (2*((opsize (op_override pre) w)+1)-1) p1;
                 p2ext <- cast_s (2*((opsize (op_override pre) w)+1)-1) p2;
                 res <- arith mul_op p1ext p2ext;
                 lowerhalf <- cast_s (opsize (op_override pre) w) res;
                 shift <- load_Z _ (Z_of_nat (opsize (op_override pre) w + 1));
                 res_shifted <- arith shr_op res shift;
                 upperhalf <- cast_s (opsize (op_override pre) w) res_shifted;
                 zero <- load_Z _  0;
                 max <- load_Z _ (Word.max_unsigned (opsize (op_override pre) w));
                 b0 <- test eq_op upperhalf zero;
                 b1 <- test eq_op upperhalf max;
                 b2 <- arith or_op b0 b1;
                 flag <- not b2;
                 set_flag CF flag;;
                 set_flag OF flag;;
                 match (op_override pre), w with
                   | _, false => iset_op16 seg res (Reg_op EAX) 
                   | _, true =>  let set := set_op pre w in
                                    set seg lowerhalf (Reg_op EAX);;
                                    set seg upperhalf (Reg_op EDX)
                 end
      | Some op2 => 
        match iopt with
          | None => let load := load_op pre w in
                    let set := set_op pre w in
                    let seg := get_segment_op2 pre DS op1 op2 in
                      p1 <- load seg op1;
                      p2 <- load seg op2;
                      p1ext <- cast_s (2*((opsize (op_override pre) w)+1)-1) p1;
                      p2ext <- cast_s (2*((opsize (op_override pre) w)+1)-1) p2;
                      res <- arith mul_op p1ext p2ext;
                      lowerhalf <- cast_s (opsize (op_override pre) w) res;
                      reextend <- cast_s (2*((opsize (op_override pre) w)+1)-1) lowerhalf;
                      b0 <- test eq_op reextend res;
                      flag <- not b0;
                      set_flag CF flag;;
                      set_flag OF flag;;
                      set seg lowerhalf op1
          |Some imm3  =>  let load := load_op pre w in
                    let set := set_op pre w in
                    let seg := get_segment_op2 pre DS op1 op2 in
                      p1 <- load seg op2;
                      p2 <- load_int imm3;
                      p1ext <- cast_s (2*((opsize (op_override pre) w)+1)-1) p1;
                      p2ext <- cast_s (2*((opsize (op_override pre) w)+1)-1) p2;
                      res <- arith mul_op p1ext p2ext;
                      lowerhalf <- cast_s (opsize (op_override pre) w) res;
                      reextend <- cast_s (2*((opsize (op_override pre) w)+1)-1) lowerhalf;
                      b0 <- test eq_op reextend res;
                      flag <- not b0;
                      set_flag CF flag;;
                      set_flag OF flag;;
                      set seg lowerhalf op1
        end
    end).
    Obligation 1. unfold opsize. 
      destruct (op_override pre); simpl; auto. Defined.



  Definition conv_MUL (pre: prefix) (w: bool) (op: operand) :=
    let seg := get_segment_op pre DS op in
    undef_flag SF;;
    undef_flag ZF;;
    undef_flag AF;;
    undef_flag PF;;
    match op_override pre, w with
      | _, false => p1 <- iload_op8 seg op;
                    p2 <- iload_op8 seg (Reg_op EAX);
                    p1ext <- cast_u size16 p1;
                    p2ext <- cast_u size16 p2;
                    res <- arith mul_op p1ext p2ext;
                    iset_op16 seg res (Reg_op EAX);;
                    max <- load_Z _ 255;
                    cf_test <- test ltu_op max res;
                    set_flag CF cf_test;;
                    set_flag OF cf_test
      | true, true => p1 <- iload_op16 seg op;
                    p2 <- iload_op16 seg (Reg_op EAX);
                    p1ext <- cast_u size32 p1;
                    p2ext <- cast_u size32 p2;
                    res <- arith mul_op p1ext p2ext;
                    res_lower <- cast_u size16 res;
                    sixteen <- load_Z size32 16;
                    res_shifted <- arith shru_op res sixteen;
                    res_upper <- cast_u size16 res_shifted;
                    iset_op16 seg res_lower (Reg_op EAX);;
                    iset_op16 seg res_upper (Reg_op EDX);;
                    zero <- load_Z size16 0;
                    cf_test <- test ltu_op zero res_upper;
                    set_flag CF cf_test;;
                    set_flag OF cf_test
      | false, true => p1 <- iload_op32 seg op;
                    p2 <- iload_op32 seg (Reg_op EAX);
                    p1ext <- cast_u 63 p1;
                    p2ext <- cast_u 63 p2;
                    res <- arith mul_op p1ext p2ext;
                    res_lower <- cast_u size32 res;
                    thirtytwo <- load_Z 63 32;
                    res_shifted <- arith shru_op res thirtytwo;
                    res_upper <- cast_u size32 res_shifted;
                    iset_op32 seg res_lower (Reg_op EAX);;
                    iset_op32 seg res_upper (Reg_op EDX);;
                    zero <- load_Z size32 0;
                    cf_test <- test ltu_op zero res_upper;
                    set_flag CF cf_test;;
                    set_flag OF cf_test
   end.

  Definition conv_shift shift (pre: prefix) (w: bool) (op1: operand) (op2: reg_or_immed) :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    let seg := get_segment_op pre DS op1 in
      (* These aren't actually undef'd, but they're sqirrely
         so for now I'll just overapproximate *)
      undef_flag OF;;
      undef_flag CF;;
      undef_flag SF;;
      undef_flag ZF;;
      undef_flag PF;;
      undef_flag AF;;
      p1 <- load seg op1;
      p2 <- (match op2 with
              | Reg_ri r => iload_op8 seg (Reg_op r) 
              | Imm_ri i => load_int i
             end);
      mask <- load_Z _ 31;
      p2 <- arith and_op p2 mask;
      p2cast <- cast_u (opsize (op_override pre) w) p2;
      p3 <- arith shift p1 p2cast;
      set seg p3 op1.
               
  Definition conv_SHL pre w op1 op2 := conv_shift shl_op pre w op1 op2.
  Definition conv_SAR pre w op1 op2 := conv_shift shr_op pre w op1 op2.
  Definition conv_SHR pre w op1 op2 := conv_shift shru_op pre w op1 op2.

  Definition conv_ROR pre w op1 op2 := conv_shift ror_op pre w op1 op2. 
  Definition conv_ROL pre w op1 op2 := conv_shift rol_op pre w op1 op2.

  (* Need to be careful about op1 size. *)

  Definition conv_RCL pre w op1 op2 :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    let seg := get_segment_op pre DS op1 in

    p1 <- load seg op1;
    p2 <- (match op2 with
              | Reg_ri r => iload_op8 seg (Reg_op r) 
              | Imm_ri i => load_int i
                   end);
    mask <- load_Z size8 31;
    p2 <- arith and_op p2 mask;
    (match opsize (op_override pre) w with
       | 7  => modmask <- load_Z _ 9;
               p2 <- arith modu_op p2 modmask;
               ret tt
       | 15 => modmask <- load_Z _ 17;
               p2 <- arith modu_op p2 modmask;
               ret tt
       | _  => ret tt
     end);;
    p2cast <- cast_u ((opsize (op_override pre) w) + 1) p2;
    
    tmp <- cast_u ((opsize (op_override pre) w) + 1) p1;
    cf <- get_flag CF;
    cf <- cast_u ((opsize (op_override pre) w) + 1) cf;
    tt <- load_Z _ (Z_of_nat ((opsize (op_override pre) w) + 1));
    cf <- arith shl_op cf tt;
    tmp <- arith or_op tmp cf;
    tmp <- arith rol_op tmp p2cast; 
    
    p3 <- cast_u (opsize (op_override pre) w) tmp;
    cf <- arith shr_op tmp tt;
    cf <- cast_u size1 cf;
    undef_flag OF;;
    set_flag CF cf;;
    set seg p3 op1.

  Definition conv_RCR pre w op1 op2 :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    let seg := get_segment_op pre DS op1 in
    p1 <- load seg op1;
    p2 <- (match op2 with
              | Reg_ri r => iload_op8 seg (Reg_op r) 
              | Imm_ri i => load_int i
                   end);   
    mask <- load_Z size8 31;
    p2 <- arith and_op p2 mask;
    (match opsize (op_override pre) w with
       | 7  => modmask <- load_Z _ 9;
               p2 <- arith modu_op p2 modmask;
               ret tt
       | 15 => modmask <- load_Z _ 17;
               p2 <- arith modu_op p2 modmask;
               ret tt
       | _  => ret tt
     end);;
   p2cast <- cast_u ((opsize (op_override pre) w) + 1) p2;

    oneshift <- load_Z _ 1;

    tmp <- cast_u ((opsize (op_override pre) w) + 1) p1;
    tmp <- arith shl_op tmp oneshift;
    cf <- get_flag CF;
    cf <- cast_u ((opsize (op_override pre) w) + 1) cf;
    tmp <- arith or_op tmp cf;
    tmp <- arith ror_op tmp p2cast;
    
    cf <- cast_u size1 tmp;
    p3 <- arith shr_op tmp oneshift;
    p3 <- cast_u ((opsize (op_override pre) w)) p3;
    undef_flag OF;;
    set_flag CF cf;;
    set seg p3 op1.

  Definition conv_SHLD pre (op1: operand) (r: register) ri :=
    let load := load_op pre true in
    let set := set_op pre true in
    let seg := get_segment_op pre DS op1 in
      count <- (match ri with
              | Reg_ri r => iload_op8 seg (Reg_op r) 
              | Imm_ri i => load_int i
             end);
      thirtytwo <- load_Z _ 32;
      count <- arith modu_op count thirtytwo;
      (* These aren't actually always undef'd, but they're sqirrely
         so for now I'll just overapproximate *)
      undef_flag CF;;
      undef_flag SF;;
      undef_flag ZF;;
      undef_flag PF;;
      undef_flag AF;;
      p1 <- load seg op1;
      p2 <- load seg (Reg_op r);
      shiftup <- (match (op_override pre) with
                    | true => load_Z 63 16
                    | false => load_Z 63 32
                  end);
      wide_p1 <- cast_u 63 p1;
      wide_p1 <- arith shl_op wide_p1 shiftup;
      wide_p2 <- cast_u 63 p2;
      combined <- arith or_op wide_p1 wide_p2;
      wide_count <- cast_u 63 count;
      shifted <- arith shl_op combined wide_count;
      shifted <- arith shru_op shifted shiftup;
      newdest <- cast_u _ shifted;
      maxcount <- (match (op_override pre) with
                    | true => load_Z size8 16
                    | false => load_Z size8 32
                  end);
      guard1 <- test ltu_op maxcount count;
      guard2 <- test eq_op maxcount count;
      guard <- arith or_op guard1 guard2;
      emit (if_rtl guard (choose_rtl newdest));;
      set seg newdest op1.

  Definition conv_SHRD pre (op1: operand) (r: register) ri :=
    let load := load_op pre true in
    let set := set_op pre true in
    let seg := get_segment_op pre DS op1 in
      count <- (match ri with
              | Reg_ri r => iload_op8 seg (Reg_op r) 
              | Imm_ri i => load_int i
             end);
      thirtytwo <- load_Z _ 32;
      count <- arith modu_op count thirtytwo;
      (* These aren't actually always undef'd, but they're sqirrely
         so for now I'll just overapproximate *)
      undef_flag CF;;
      undef_flag SF;;
      undef_flag ZF;;
      undef_flag PF;;
      undef_flag AF;;
      p1 <- load seg op1;
      p2 <- load seg (Reg_op r);
      wide_p1 <- cast_u 63 p1;
      shiftup <- (match (op_override pre) with
                    | true => load_Z 63 16
                    | false => load_Z 63 32
                  end);
      wide_p2 <- cast_u 63 p2;
      wide_p2 <- arith shl_op wide_p2 shiftup;
      combined <- arith or_op wide_p1 wide_p2;
      wide_count <- cast_u 63 count;
      shifted <- arith shru_op combined wide_count;
      newdest <- cast_u _ shifted;
      maxcount <- (match (op_override pre) with
                    | true => load_Z size8 16
                    | false => load_Z size8 32
                  end);
      guard1 <- test ltu_op maxcount count;
      guard2 <- test eq_op maxcount count;
      guard <- arith or_op guard1 guard2;
      emit (if_rtl guard (choose_rtl newdest));;
      set seg newdest op1.
  (************************)
  (* Binary Coded Dec Ops *)
  (************************)

  (* The semantics for these operations are described using slightly different pseudocode in the
     old and new intel manuals, although they are operationally equivalent. These definitions
     are structured based on the new manual, so it may look strange when compared with the old
     manual *)

  Definition get_AH : Conv (pseudo_reg size8) :=
    iload_op8 DS (Reg_op ESP)
  .
  Definition set_AH v: Conv unit :=
    iset_op8 DS v (Reg_op ESP) 
  .
  Definition get_AL : Conv (pseudo_reg size8) :=
    iload_op8 DS (Reg_op EAX)
  .
  Definition set_AL v: Conv unit :=
    iset_op8 DS v (Reg_op EAX) 
  .
  Definition ifset s cond (rd:pseudo_reg s) (rs:pseudo_reg s) : Conv unit :=
    emit (if_rtl cond (cast_u_rtl rs rd))
.
  Definition conv_AAA_AAS (op1: bit_vector_op) : Conv unit :=
    pnine <- load_Z size8 9;
    p0Fmask <- load_Z size8 15;
    paf <- get_flag AF;
    pal <- get_AL;
    digit1 <- arith and_op pal p0Fmask;
    cond1 <- test lt_op pnine digit1;
    cond <- arith or_op cond1 paf;

    pah <- get_AH;
    (*Else branch*)
    pfalse <- load_Z size1 0;
    v_ah <- copy_ps pah;
    v_af <- copy_ps pfalse;
    v_cf <- copy_ps pfalse;
    v_al <- arith and_op pal p0Fmask;
    
    (*If branch*)
    psix <- load_Z size8 6;
    pone <- load_Z size8 1;
    ptrue <- load_Z size1 1;
    pal_c <- arith op1 pal psix;
    pal_cmask <- arith and_op pal_c p0Fmask;
    ifset cond v_al pal_cmask;;
    
    pah <- get_AH;
    pah_c <- arith op1 pah pone;
    ifset cond v_ah pah_c;;
    ifset cond v_af ptrue;;
    ifset cond v_cf ptrue;;
    
    (*Set final values*)
    set_AL v_al;;
    set_AH v_ah;;
    set_flag AF v_af;;
    set_flag CF v_cf;;

    undef_flag OF;;
    undef_flag SF;;
    undef_flag ZF;;
    undef_flag PF
    .
  Definition conv_AAD : Conv unit :=
    pal <- get_AL;
    pah <- get_AH;
    pten <- load_Z size8 10;
    pFF <- load_Z size8 255;
    pzero <- load_Z size8 0;

    tensval <- arith mul_op pah pten;
    pal_c <- arith add_op pal tensval;
    pal_cmask <- arith and_op pal_c pFF;
    set_AL pal_cmask;;
    set_AH pzero;;

    b0 <- test eq_op pal_cmask pzero;
    set_flag ZF b0;;
    b1 <- test lt_op pal_cmask pzero;
    set_flag SF b1;;
    b2 <- compute_parity pal_cmask;
    set_flag PF b2;;
    undef_flag OF;;
    undef_flag AF;;
    undef_flag CF
    .

  Definition conv_AAM : Conv unit :=
    pal <- get_AL;
    pten <- load_Z size8 10;
    digit1 <- arith divu_op pal pten;
    digit2 <- arith modu_op pal pten;
    set_AH digit1;;
    set_AL digit2;;

    pzero <- load_Z size8 0;
    b0 <- test eq_op digit2 pzero;
    set_flag ZF b0;;
    b1 <- test lt_op digit2 pzero;
    set_flag SF b1;;
    b2 <- compute_parity digit2;
    set_flag PF b2;;
    undef_flag OF;;
    undef_flag AF;;
    undef_flag CF
    .

  Definition testcarryAdd s (p1:pseudo_reg s) p2 p3 : Conv (pseudo_reg size1) :=
    b0 <-test ltu_op p3 p1;
    b1 <-test ltu_op p3 p2;
    arith or_op b0 b1.

  Definition testcarrySub s (p1:pseudo_reg s) p2 (p3:pseudo_reg s) : Conv (pseudo_reg size1) :=
    test ltu_op p1 p2.

  (*Use oracle for now*)
  Definition conv_DAA_DAS (op1: bit_vector_op) 
    (tester: (pseudo_reg size8) -> (pseudo_reg size8) -> (pseudo_reg size8) ->
      Conv (pseudo_reg size1)) : Conv unit :=
    pal <- fresh (@choose_rtl size8);
    set_AL pal;;
    undef_flag CF;;
    undef_flag AF;;
    undef_flag SF;;
    undef_flag ZF;;
    undef_flag PF;;
    undef_flag OF
  .
(*
  Definition conv_DAA_DAS (op1: bit_vector_op) tester: Conv unit :=
    pal <- get_AL;
    pcf <- get_flag CF;
    ptrue <- load_Z size1 1;
    pfalse <- load_Z size1 0;
    set_flag CF pfalse;;

    pnine <- load_Z size8 9;
    p0Fmask <- load_Z size8 15;
    palmask <- arith and_op pal p0Fmask;
    cond1 <- test lt_op pnine palmask;
    paf <- get_flag AF;
    cond <- arith or_op cond1 paf;

    v_cf <- load_Z size1 0;
    (*First outer if*)
      (*Else*)
      v_al <- copy_ps pal;
      v_af <- load_Z size1 0;
      (*If*)
      psix <- load_Z size8 6;
      pal_c <- arith op1 pal psix;
      ifset cond v_al pal_c;;
      ifset cond v_af ptrue;;

      (*Annoying test for carry flag*)
      b2 <- tester pal psix pal_c;
      newc <- arith or_op pcf b2;
      ifset cond v_cf newc;;
    (*End first outer if*)
      
    pninenine <- load_Z size8 153 (*0x99*);
    cond1' <- test lt_op pninenine pal;
    cond' <- arith or_op cond1' pcf;
    ncond' <- not cond';
    (*Second outer if*)
      (*Else*)
      ifset ncond' v_cf pfalse;;
      (*If*)
      psixty <- load_Z size8 96; (*0x60*)
      pal2_c <- arith op1 v_al psixty;
      ifset cond' v_al pal2_c;;
      ifset cond' v_cf ptrue;;
    (*End second outer if*)
    
    (*Set final values*)
    (*v_al, v_cf, v_af*)
    set_AL v_al;;
    set_flag CF v_cf;;
    set_flag AF v_af;;
    pzero <- load_Z size8 0;
    b0 <- test eq_op v_al pzero;
    set_flag ZF b0;;
    b1 <- test lt_op v_al pzero;
    set_flag SF b1;;
    b2 <- compute_parity v_al;
    set_flag PF b2;;
    undef_flag OF
.
    
*)
    
  (************************)
  (* Logical Ops          *)
  (************************)

  Definition conv_logical_op (do_effect: bool) (b: bit_vector_op) (pre: prefix) 
    (w: bool) (op1 op2: operand) : Conv unit :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    let seg := get_segment_op2 pre DS op1 op2 in
        p0 <- load seg op1;
        p1 <- load seg op2;
        p2 <- arith b p0 p1;
        zero <- load_Z _ 0;
        zfp <- test eq_op zero p2;
        sfp <- test lt_op p2 zero;
        pfp <- compute_parity p2;
        zero1 <- load_Z size1 0;
        set_flag OF zero1 ;;
        set_flag CF zero1 ;;
        set_flag ZF zfp   ;;
        set_flag SF sfp ;;
        set_flag PF pfp ;;
        undef_flag AF;;
        if do_effect then
          set seg p2 op1
        else
          ret tt.
  
  Definition conv_AND p w op1 op2 := conv_logical_op true and_op p w op1 op2.
  Definition conv_OR p w op1 op2 := conv_logical_op true or_op p w op1 op2.
  Definition conv_XOR p w op1 op2 := conv_logical_op true xor_op p w op1 op2.

  (* This is like AND except you don't actually write the result in op1 *)
  Definition conv_TEST p w op1 op2 := conv_logical_op false and_op p w op1 op2.

  (* This is different than the others because it doesn't affect any
     flags *)

  Definition conv_NOT (pre: prefix) (w: bool) (op: operand) : Conv unit :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    let seg := get_segment_op pre DS op in
        p0 <- load seg op;
        max_unsigned <- load_Z _ (Word.max_unsigned size32);
        p1 <- arith xor_op p0 max_unsigned;
        set seg p1 op.

  (************************)
  (* Stack Ops            *)
  (************************)

  Definition conv_POP (pre: prefix) (op: operand) :=
    (*Segment cannot be overriden*)
    let seg := SS in 
    let set := set_op pre true seg in
    let loadmem := load_mem pre true seg in 
    let espoffset := match (op_override pre) with
                       | true => 2%Z
                       | false => 4%Z
                     end in
      oldesp <- load_reg ESP;
      value <- loadmem oldesp;
      offset <- load_Z size32 espoffset;
      newesp <- arith add_op oldesp offset;
      set_reg newesp ESP;;
      set value op
      .
  Definition conv_POPA (pre:prefix) :=
    let espoffset := match (op_override pre) with
                       | true => 2%Z
                       | false => 4%Z
                     end in
    let poprtl r := conv_POP pre (Reg_op r) in
    poprtl EDI;;
    poprtl ESI;;
    poprtl EBP;;
    oldesp <- load_reg ESP;
    offset <- load_Z size32 espoffset;
    newesp <- arith add_op oldesp offset;
    set_reg newesp ESP;;
    poprtl EBX;;
    poprtl EDX;;
    poprtl ECX;;
    poprtl EAX.

  Definition conv_PUSH (pre: prefix) (w: bool) (op: operand) :=
    let seg := SS in
    let load := load_op pre true seg in
    let setmem := set_mem pre true seg in
    let espoffset := match op_override pre,w return Z with 
                       | true,_ => 2%Z
                       | false,_ => 4%Z
                     end in
    p0 <- load op;
    oldesp <- load_reg ESP;
    offset <- load_Z size32 espoffset;
    newesp <- arith sub_op oldesp offset;
    setmem p0 newesp;;
    set_reg newesp ESP
    .

  Definition conv_PUSH_pseudo (pre:prefix) (w:bool) 
    pr  := (* (pr: pseudo_reg (opsize (op_override pre) w)) *)
    let seg := SS in
    let setmem := set_mem pre w seg in
    let espoffset := match op_override pre,w return Z with 
                       | _,false => 1%Z
                       | true,true => 2%Z
                       | false,true => 4%Z
                     end in
    oldesp <- load_reg ESP;
    offset <- load_Z size32 espoffset;
    newesp <- arith sub_op oldesp offset;
    setmem pr newesp;;
    set_reg newesp ESP
    .

(*
    let seg := get_segment pre SS in
      if w then
        p0 <- iload_op32 seg op;
        oldesp <- load_reg ESP;
        four <- load_Z size32 4;
        newesp <- arith sub_op oldesp four;
        set_mem32 seg p0 newesp;;
        set_reg newesp ESP
      else
        b0 <- iload_op8 seg op;
        oldesp <- load_reg ESP;
        one <- load_Z size32 1;
        newesp <- arith sub_op oldesp one;
        set_mem8 seg b0 newesp;;
        set_reg newesp ESP.
*)

Definition conv_PUSHA (pre:prefix) :=
    let load := load_op pre true SS in
    let pushrtl r := conv_PUSH pre true (Reg_op r) in
    oldesp <- load (Reg_op ESP);
    pushrtl EAX;;
    pushrtl ECX;;
    pushrtl EDX;;
    pushrtl EBX;;
    conv_PUSH_pseudo pre true oldesp;;
    pushrtl EBP;;
    pushrtl ESI;;
    pushrtl EDI
.


Definition get_and_place T dst pos fl: Conv (pseudo_reg T) :=
  fl <- get_flag fl;
  pos <- load_Z _ pos;
  byt <- cast_u _ fl;  
  tmp <- @arith _ shl_op byt pos;  
  dst <- @arith _ or_op dst tmp;
  Return dst.
(*
This is not quite right. Plus those more sketchy flags
are not being modeled yet since they're more systemszy.

Definition conv_PUSHF pre :=
  dst <- load_Z (opsize (op_override pre) true) 0;

  dst <- get_and_place dst 21 ID;
  dst <- get_and_place dst 20 VIP;
  dst <- get_and_place dst 19 VIF;  
  dst <- get_and_place dst 18 AC;
  dst <- get_and_place dst 17 VM;
  dst <- get_and_place dst 16 RF;
  dst <- get_and_place dst 14 NT;
(*  get_and_place dst 13 12 IOPL; *)
  dst <- get_and_place dst 11 OF;
  dst <- get_and_place dst 10 DF;
  dst <- get_and_place dst 9 IF_flag;
  dst <- get_and_place dst 8 TF;
  dst <- get_and_place dst 7 SF;
  dst <- get_and_place dst 6 ZF;
  dst <- get_and_place dst 4 AF;
  dst <- get_and_place dst 2 PF;
  dst <- get_and_place dst 0 CF;
  conv_PUSH_pseudo pre true dst.  
*)

Definition conv_POP_pseudo (pre: prefix) :=
(*Segment cannot be overriden*)
  let seg := SS in 
    let set := set_op pre true seg in
      let loadmem := load_mem pre true seg in 
        let espoffset := match (op_override pre) with
                           | true => 2%Z
                           | false => 4%Z
                         end in
        oldesp <- load_reg ESP;
        value <- loadmem oldesp;
        offset <- load_Z size32 espoffset;
        newesp <- arith add_op oldesp offset;
        set_reg newesp ESP;;
        Return value.

Definition extract_and_set T value pos fl: Conv unit :=
  one <- load_Z T 1;
  pos <- load_Z _ pos;
  tmp <- @arith _ shr_op value pos;
  tmp <- @arith _ and_op tmp one;
  b <- test eq_op one tmp;
  set_flag fl b.
(*
This is not quite right.
Definition conv_POPF pre :=
  v <- conv_POP_pseudo pre;

  @extract_and_set ((opsize (op_override pre) true)) v 21 ID;;
  extract_and_set v 20 VIP;;
  extract_and_set v 19 VIF;; 
  extract_and_set v 18 AC;;
  extract_and_set v 17 VM;;
  extract_and_set v 16 RF;;
  extract_and_set v 14 NT;;
(*  extract_and_set dst 13 12 IOPL; *)
  extract_and_set v 11 OF;;
  extract_and_set v 10 DF;;
  extract_and_set v 9 IF_flag;;
  extract_and_set v 8 TF;;
  extract_and_set v 7 SF;;
  extract_and_set v 6 ZF;;
  extract_and_set v 4 AF;;
  extract_and_set v 2 PF;;
  extract_and_set v 0 CF.
*)

  (************************)
  (* Control-Flow Ops     *)
  (************************)

  Definition conv_JMP (pre: prefix) (near absolute: bool) (op: operand)
    (sel: option selector) :=
    let seg := get_segment_op pre DS op in
      if near then
        disp <- iload_op32 seg op;
        base <- (match absolute with
                   | true => load_Z size32 0
                   | false => get_pc
                 end);
        newpc <- arith add_op base disp;
        set_pc newpc
      else
        emit error_rtl.

  Definition conv_Jcc (pre: prefix) (ct: condition_type) (disp: int32) : Conv unit :=
    guard <- compute_cc ct;
    oldpc <- get_pc;
    pdisp <- load_int disp;
    newpc <- arith add_op oldpc pdisp;
    emit if_rtl guard (set_loc_rtl newpc pc_loc).

  Definition conv_CALL (pre: prefix) (near absolute: bool) (op: operand)
    (sel: option selector) :=
      oldpc <- get_pc;
      oldesp <- load_reg ESP;
      four <- load_Z size32 4;
      newesp <- arith sub_op oldesp four;
      set_mem32 SS oldpc newesp;;
      set_reg newesp ESP;;
      conv_JMP pre near absolute op sel.
  
  Definition conv_RET (pre: prefix) (same_segment: bool) (disp: option int16) :=
      if same_segment then
        oldesp <- load_reg ESP;
        value <- load_mem32 SS oldesp;
        four <- load_Z size32 4;
        newesp <- arith add_op oldesp four;
        (match disp with
           | None => set_reg newesp ESP
           | Some imm => imm0 <- load_int imm;
             imm <- cast_u size32 imm0;
             newesp2 <- arith add_op newesp imm;
             set_reg newesp2 ESP
         end);;
        set_pc value
      else
        emit error_rtl.
  
  Definition conv_LEAVE pre := 
    ebp_val <- load_reg EBP;
    set_reg ebp_val ESP;;
    conv_POP pre (Reg_op EBP).

  Definition conv_LOOP pre (flagged:bool) (testz:bool) (disp:int8):=
    ptrue <- load_Z size1 1;
    p0 <- load_reg ECX;
    p1 <- load_Z _ 1;
    p2 <- arith sub_op p0 p1;
    set_reg p2 ECX;;
    pzero <- load_Z _ 0;
    pcz <- test eq_op p2 pzero;
    pcnz <- arith xor_op pcz ptrue;
    pzf <- get_flag ZF;
    pnzf <- arith xor_op pzf ptrue;
    bcond <- 
    (match flagged with
       | true =>
         (match testz with
            | true => (arith and_op pzf pcnz)
            | false => (arith and_op pnzf pcnz)
          end)
       | false => arith or_op pcnz pcnz
     end);
    eip0 <- get_pc;
    doffset0 <- load_int disp;
    doffset1 <- cast_s size32 doffset0;
    eip1 <- arith add_op eip0 doffset1;
    eipmask <-
    (match (op_override pre) with
       |true => load_Z size32 65536%Z (*0000FFFF*)
       |false => load_Z size32 (-1%Z)
     end);
    eip2 <- arith and_op eip1 eipmask;
    emit (if_rtl bcond (set_loc_rtl eip2 pc_loc))
    .

  (************************)
  (* Misc Ops             *)
  (************************)

  (* Unfortunately this is kind of "dumb", because we can't short-circuit
     once we find the msb/lsb *)

  Fixpoint conv_BS_aux {s} (d: bool) (n: nat) (op: pseudo_reg s) : Conv (pseudo_reg s) :=
    let curr_int := (match d with
                       | true => @Word.repr s (BinInt.Z_of_nat (s-n)) 
                       | false => @Word.repr s (BinInt.Z_of_nat n) 
                     end) in
    match n with
      | O => load_int curr_int
      | S n' => bcount <- load_int curr_int;
        rec <- conv_BS_aux d n' op;
        ps <- arith shru_op op bcount;
        curr_bit <- cast_u size1 ps;
        emit if_rtl curr_bit (load_imm_rtl curr_int rec);;
        ret rec
    end.

  Definition conv_BS (d: bool) (pre: prefix) (op1 op2: operand) :=
    let seg := get_segment_op2 pre DS op1 op2 in
      undef_flag AF;;
      undef_flag CF;;
      undef_flag SF;;
      undef_flag OF;;
      undef_flag PF;;
      des <- iload_op32 seg op1;
      src <- iload_op32 seg op2;
      zero <- load_Z size32 0;
      zf <- test eq_op src zero;
      set_flag ZF zf;;
      res <- conv_BS_aux d size32 src;
      emit (if_rtl zf (choose_rtl res));;
      iset_op32 seg res op1.

  Definition conv_BSF p op1 op2 := conv_BS true p op1 op2.
  Definition conv_BSR p op1 op2 := conv_BS false p op1 op2.
  
  Definition get_Bit {s: nat} (pb: pseudo_reg s) (poff: pseudo_reg s) : 
    Conv (pseudo_reg size1) :=
    omask <- load_Z s 1;
    shr_pb <- arith shr_op pb poff;
    mask_pb <- arith and_op shr_pb omask;
    tb <- cast_u size1 mask_pb;
    ret tb.

  Definition modify_Bit {s} (value: pseudo_reg s) (poff: pseudo_reg s)
    (bitval: pseudo_reg size1): Conv (pseudo_reg s) :=
    obit <- load_Z _ 1;
    one_shifted <- arith shl_op obit poff;
    inv_one_shifted <- not one_shifted;
    bitvalword <- cast_u _ bitval;
    bit_shifted <- arith shl_op bitvalword poff;
    newval <- arith and_op value inv_one_shifted;
    arith or_op newval bit_shifted.

  (*Set a bit given a word referenced by an operand*)
  Definition set_Bit (pre:prefix) (w:bool)
    (op:operand) (poff: pseudo_reg (opsize (op_override pre) w)) 
    (bitval: pseudo_reg size1):
    Conv unit :=
    let seg := get_segment_op pre DS op in
    let load := load_op pre w seg in
    let set := set_op pre w seg in
    value <- load op;
    newvalue <- modify_Bit value poff bitval;
    set newvalue op.

  (*Set a bit given a word referenced by a raw address*)
  Definition set_Bit_mem (pre:prefix) (w:bool)
    (op:operand) (addr:pseudo_reg size32) (poff: pseudo_reg (opsize (op_override pre) w)) 
    (bitval: pseudo_reg size1):
    Conv unit :=
    let seg := get_segment_op pre DS op in
    let load := load_mem pre w seg in
    let set := set_mem pre w seg in
    value <- load addr;
    newvalue <- modify_Bit value poff bitval;
    (* adding copy_ps makes the proof much easier since it meets the pattern 
             "addr <- v; set_mem_n ... addr" *)
    newaddr <- copy_ps addr; 
    set newvalue newaddr.

  (* id, comp, set, or reset on a single bit, depending on the params*)
  Definition fbit (param1: bool) (param2: bool) (v: pseudo_reg size1):
    Conv (pseudo_reg size1) :=
    pone <- load_Z size1 1;
    pzero <- load_Z size1 0;
    match param1, param2 with
      | true, true => ret pone
      | true, false => ret pzero
      | false, true => ret v
      | false, false => v1 <- (not v); ret v1
    end.

  (*tt: set, tf: clear, ft: id, ff: complement*)
  Definition conv_BT (param1: bool) (param2: bool)
    (pre: prefix) (op1 : operand) (regimm: operand) :=
    let seg := get_segment_op pre DS op1 in
    let load := load_op pre true seg in
    let lmem := load_mem pre true seg in
    let opsz := opsize (op_override pre) true in
    undef_flag OF;;
    undef_flag SF;;
    undef_flag AF;;
    undef_flag PF;;
    pi <- load regimm;
    popsz <- load_Z opsz (BinInt.Z_of_nat opsz + 1);
    rawoffset <- 
      (match regimm with
         | Imm_op i =>
           arith modu_op pi popsz
         | _ => copy_ps pi
       end
      );
    popsz_bytes <- load_Z size32 ((BinInt.Z_of_nat (opsz + 1))/8);
    pzero <- load_Z opsz 0;
    pneg1 <- load_Z size32 (-1)%Z;
    (*for factoring out what we do when we access mem*)
    (*psaddr is the base word address*)
    let btmem psaddr := 
        bitoffset <- arith mods_op rawoffset popsz;
        wordoffset' <- arith divs_op rawoffset popsz;
        (*Important to preserve sign here*)
        wordoffset <- cast_s size32 wordoffset';
        (*if the offset is negative, we need to the word offset needs to
           be shifted one more down, and the offset needs to be made positive *)
        isneg <- test lt_op bitoffset pzero;
        (*nbitoffset:size_opsz and nwordoffset:size32 are final signed values*)
        nbitoffset <- copy_ps bitoffset;
        nwordoffset <- copy_ps wordoffset;
        (*If the bitoffset was lt zero, we need to adjust values to make them positive*)
        negbitoffset <- arith add_op popsz bitoffset;
        negwordoffset <- arith add_op pneg1 wordoffset;
        emit (if_rtl isneg (cast_u_rtl negbitoffset nbitoffset));;
        emit (if_rtl isneg (cast_u_rtl negwordoffset nwordoffset));;
        newaddrdelta <- arith mul_op nwordoffset popsz_bytes;
        newaddr <- arith add_op newaddrdelta psaddr;
        
        value <- lmem newaddr;
        bt <- get_Bit value nbitoffset;
        set_flag CF bt;;
        newbt <- fbit param1 param2 bt;
        set_Bit_mem pre true op1 newaddr nbitoffset newbt in
    match op1 with
      | Imm_op _ => emit error_rtl
      | Reg_op r1 =>
        value <- load (Reg_op r1);
        bitoffset <- arith modu_op rawoffset popsz;
        bt <- get_Bit value bitoffset;
        set_flag CF bt;;
        newbt <- fbit param1 param2 bt;
        set_Bit pre true op1 bitoffset newbt
      | Address_op a => 
        psaddr <- compute_addr a;
        btmem psaddr
      | Offset_op ioff => 
        psaddr <- load_int ioff;
        btmem psaddr
    end
.
    
  Definition conv_BSWAP (pre: prefix) (r: register) :=
    let seg := get_segment pre DS in
      eight <- load_Z size32 8;
      ps0 <- load_reg r;
      b0 <- cast_u size8 ps0;

      ps1 <- arith shru_op ps0 eight;
      b1 <- cast_u size8 ps1;
      w1 <- cast_u size32 b1;

      ps2 <- arith shru_op ps1 eight;
      b2 <- cast_u size8 ps2;
      w2 <- cast_u size32 b2;

      ps3 <- arith shru_op ps2 eight;
      b3 <- cast_u size8 ps3;
      w3 <- cast_u size32 b3;

      res0 <- cast_u size32 b0;
      res1 <- arith shl_op res0 eight;
      res2 <- arith add_op res1 w1;
      res3 <- arith shl_op res2 eight;
      res4 <- arith add_op res3 w2;
      res5 <- arith shl_op res4 eight;
      res6 <- arith add_op res5 w3;
      set_reg res6 r.

  Definition conv_CWDE (pre: prefix) :=
    let seg := get_segment pre DS in
      match op_override pre with
        | true =>  p1 <- iload_op8 seg (Reg_op EAX);
                   p2 <- cast_s size16 p1;
                   iset_op16 seg p2 (Reg_op EAX)
        | false => p1 <- iload_op16 seg (Reg_op EAX);
                   p2 <- cast_s size32 p1;
                   iset_op32 seg p2 (Reg_op EAX)
      end.

  Definition conv_CDQ (pre: prefix) :=
    let seg := get_segment pre DS in
      match op_override pre with
        | true =>  p1 <- iload_op16 seg (Reg_op EAX);
                   p2 <- cast_s size32 p1;
                   p2_bottom <- cast_s size16 p2;
                   sixteen <- load_Z _ 16;
                   p2_top0 <- arith shr_op p2 sixteen;
                   p2_top <- cast_s size16 p2_top0;
                   iset_op16 seg p2_bottom (Reg_op EAX);;
                   iset_op16 seg p2_top (Reg_op EDX)
        | false =>  p1 <- iload_op32 seg (Reg_op EAX);
                   p2 <- cast_s 63 p1;
                   p2_bottom <- cast_s size32 p2;
                   thirtytwo <- load_Z _ 32;
                   p2_top0 <- arith shr_op p2 thirtytwo;
                   p2_top <- cast_s size32 p2_top0;
                   iset_op32 seg p2_bottom (Reg_op EAX);;
                   iset_op32 seg p2_top (Reg_op EDX)
      end.
          

  Definition conv_MOV (pre: prefix) (w: bool) (op1 op2: operand) : Conv unit :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    let seg := get_segment_op2 pre DS op1 op2 in
        res <- load seg op2;
        set seg res op1.

  (* Note that cmov does not have a byte mode - however we use it as a pseudo-instruction
     to simplify some of the other instructions (e.g. CMPXCHG *)

  Definition conv_CMOV (pre: prefix) (w: bool) (cc: condition_type) (op1 op2: operand) : Conv unit :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    let seg := get_segment_op2 pre DS op1 op2 in
        tmp <- load seg op1;
        src <- load seg op2;
        cc <- compute_cc cc;
        emit (if_rtl cc (cast_u_rtl src tmp));;
        set seg tmp op1.

  Definition conv_MOV_extend (extend_op: forall s1 s2: nat, pseudo_reg s1 
    -> Conv (pseudo_reg s2)) (pre: prefix) (w: bool) (op1 op2: operand) : Conv unit :=
    let seg := get_segment_op2 pre DS op1 op2 in
    match op_override pre, w with
      (* It's not really clear what should be done true, true here. It's not in the table,
         but it seems to be a valid instruction. It would correspond to sign/zero
         extending a 16 bit value to a 16 bit value... ie just moving *)
      | true, true =>  p1 <- iload_op16 seg op2;
                       iset_op16 seg p1 op1
      | false, true => p1 <- iload_op16 seg op2;
                       p2 <- extend_op _ _ p1;
                       iset_op32 seg p2 op1
      | true, false => p1 <- iload_op8 seg op2;
                       p2 <- extend_op _ _ p1;
                       iset_op16 seg p2 op1
      | false, false => p1 <- iload_op8 seg op2;
                        p2 <- extend_op _ _ p1;
                        iset_op32 seg p2 op1
    end.

  Definition conv_MOVZX pre w op1 op2 := conv_MOV_extend cast_u pre w op1 op2.
  Definition conv_MOVSX pre w op1 op2 := conv_MOV_extend cast_s pre w op1 op2.

  Definition conv_XCHG (pre: prefix) (w: bool) (op1 op2: operand) : Conv unit :=
    let load := load_op pre w in
    let set := set_op pre w in
    let seg := get_segment_op2 pre DS op1 op2 in
        p1 <- load seg op1;
        p2 <- load seg op2;
        set seg p2 op1;;
        set seg p1 op2.

  Definition conv_XADD (pre: prefix) (w: bool) (op1 op2: operand) : Conv unit :=
    conv_XCHG pre w op1 op2;;
    conv_ADD pre w op1 op2.

  (* This actually has some interesting properties for concurrency stuff
     but for us this doesn't matter yet *)
  Definition conv_CMPXCHG (pre: prefix) (w: bool) (op1 op2: operand) : Conv unit :=
    (* The ZF flag will be set by the CMP to be zero if EAX = op1 *)
    conv_CMP pre w (Reg_op EAX) op1;;
    conv_CMOV pre w (E_ct) op1 op2;;
    conv_CMOV pre w (NE_ct) (Reg_op EAX) op1.

  (* This handles shifting the ESI/EDI stuff by the correct offset
     and in the appopriate direction for the string ops *) 
 
  Definition string_op_reg_shift reg pre w : Conv unit :=
    offset <- load_Z _  
                   (match op_override pre, w with
                      | _, false => 1
                      | true, true => 2
                      | false, true => 4
                    end);
    df <- get_flag DF;
    old_reg <- iload_op32 DS (Reg_op reg);
    new_reg1 <- arith add_op old_reg offset;
    new_reg2 <- arith sub_op old_reg offset;
    emit set_loc_rtl new_reg1 (reg_loc reg);;
    emit if_rtl df (set_loc_rtl new_reg2 (reg_loc reg)).

  (*
  Definition string_op_reg_shift pre w : Conv unit :=
    offset <- load_Z _  
                   (match op_override pre, w with
                      | _, false => 1
                      | true, true => 2
                      | false, true => 4
                    end);
    df <- get_flag DF;
    old_esi <- iload_op32 DS (Reg_op ESI);
    old_edi <- iload_op32 DS (Reg_op EDI);

    new_esi1 <- arith add_op old_esi offset;
    new_esi2 <- arith sub_op old_esi offset;

    new_edi1 <- arith add_op old_edi offset;
    new_edi2 <- arith sub_op old_edi offset;
   
    emit set_loc_rtl new_esi1 (reg_loc ESI);;
    emit if_rtl df (set_loc_rtl new_esi2 (reg_loc ESI));;

    emit set_loc_rtl new_edi1 (reg_loc EDI);;
    emit if_rtl df (set_loc_rtl new_edi2 (reg_loc EDI)).
  *)

  (* As usual we assume AddrSize = 32 bits *)
  Definition conv_MOVS pre w : Conv unit :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    (* The dest segment has to be ES, but the source can
       be overriden (DS by default)
    *)
    let seg_load := get_segment pre DS in 
    p1 <- load seg_load (Address_op (mkAddress Word.zero (Some ESI) None));
    set ES p1 (Address_op (mkAddress Word.zero (Some EDI) None));;
    string_op_reg_shift EDI pre w;;
    string_op_reg_shift ESI pre w.

  Definition conv_STOS pre w : Conv unit :=
    let load := load_op pre w in 
    let set := set_op pre w in 
    p1 <- load DS (Reg_op EAX);
    set ES p1 (Address_op (mkAddress Word.zero (Some EDI) None));;
    string_op_reg_shift EDI pre w.

  Definition conv_CMPS pre w : Conv unit :=
    let seg1 := get_segment pre DS in 
    let op1 := (Address_op (mkAddress Word.zero (Some ESI) None)) in
    let op2 := (Address_op (mkAddress Word.zero (Some EDI) None)) in
    conv_SUB_CMP_generic false pre w op1 op2 op2 
      seg1 seg1 ES;;
    string_op_reg_shift EDI pre w;;
    string_op_reg_shift ESI pre w.
 
  Definition conv_LEA (pre: prefix) (op1 op2: operand) :=
    let seg := get_segment_op pre DS op1 in
      match op2 with
        | Address_op a =>
          r <- compute_addr a;
          iset_op32 seg r op1
        | _ => emit error_rtl
      end.

  Definition conv_HLT (pre:prefix) := 
    emit safe_fail_rtl.

  Definition conv_SETcc (pre: prefix) (ct: condition_type) (op: operand) := 
    let seg := get_segment_op pre DS op in
      ccval <- compute_cc ct;
      ccext <- cast_u size8 ccval;
      iset_op8 seg ccext op.
      
  (* Just a filter for some prefix stuff we're not really handling yet.
     In the future this should go away. *)
  Definition check_prefix (p: prefix) := 
    (match op_override p, addr_override p with
       | false, false => ret tt
       | true, false => ret tt
       | _, _ => emit error_rtl
     end).

  (*
  Definition conv_REP_generic (zfval: option Z) (oldpc_val: Word.int size32) :=
    oldecx <- load_reg ECX;
    one <- load_Z _ 1;
    newecx <- arith sub_op oldecx one;
    emit set_loc_rtl newecx (reg_loc ECX);;
    zero <- load_Z _ 0;
    oldpc <- load_int oldpc_val;
    op_guard <- test eq_op newecx zero;
    guard <- not op_guard;
    emit if_rtl guard (set_loc_rtl oldpc pc_loc);;
    match zfval with
      | None => ret tt
      | Some z => v <- load_Z _ z;
                  zf <- get_flag ZF;
                  op_guard2 <- test eq_op zf v;
                  guard2 <- not op_guard2;
                  emit if_rtl guard2 (set_loc_rtl oldpc pc_loc)
    end.     

  Definition conv_REP := conv_REP_generic None.
  Definition conv_REPE := conv_REP_generic (Some 0%Z).
  Definition conv_REPNE := conv_REP_generic (Some 1%Z).

  Definition conv_lock_rep (pre: prefix) (i: instr) :=
      match lock_rep pre with 
        | Some lock | None => ret tt
        | Some rep => match i with
                        | MOVS _ => conv_REP oldpc
                        | LODS _ => conv_REP oldpc
                        | CMPS _ => conv_REPE oldpc
                        | STOS _ => conv_REP oldpc
                        | _ => emit error_rtl
                      end
        | _ => emit error_rtl
      end.
  *)


(************************)
(* Floating-Point Ops   *)
(************************)

(*
    Uses Flocq library for conversion functions.
    Things to check : 
                      -DS segment register used for all memory-related conversions
                      -Values of floating-point constants may be off (had a hard time finding them)
                      -Will include more comprehensive handling of errors and exceptions in next update. For now, 
                       emit error_rtl is used in most exception cases.

    By : Mark Kogan (mak215@lehigh.edu)
*)
Section X86FloatSemantics.

    Require Import Flocq.Appli.Fappli_IEEE.
    Require Import Flocq.Appli.Fappli_IEEE_bits.
    Require Import Flocq.Core.Fcore.
    Require Import FloatingAux.

(*Floating-Point Constants. For pi, e, 0.0, +1.0, and -1.0 I found the double-extended precision bit-values but
  for other constants I only found double-precision using this site: 
  http://www.binaryconvert.com/result_double.html?decimal=046051048049048050057057057053055 
*)

(*Start of floating-point conversion functions *)

  Definition int_to_bin32 (i : Word.int size32) : binary32 := b32_of_bits (Word.intval size32 i).
  Definition bin32_to_int (b : binary32) : Word.int size32 := Word.repr (bits_of_b32 b).

  Definition int_to_bin64 (i : Word.int size64) : binary64 := b64_of_bits (Word.intval size64 i).
  Definition bin64_to_int (b : binary64) : Word.int size64 := Word.repr (bits_of_b64 b).

  Definition int_to_de_float (i : Word.int size80) : de_float := de_float_of_bits (Word.intval size80 i).
  Definition de_float_to_int (b : de_float) : Word.int size80 := Word.repr (bits_of_de_float b).

  Definition string_to_de_float (s : string) := let intval := Word.string_to_int size80 s in int_to_de_float intval.
  Definition s2bf (s : string) := string_to_de_float s.

  (*These values may not be correct - have to check against C's floating-point constants or something *)
  Definition pos1 :=      s2bf "00111111111111110000000000000000000000000000000000000000000000000000000000000000".
  Definition neg1 :=      s2bf "10111111111111110000000000000000000000000000000000000000000000000000000000000000".
  Definition pi :=        s2bf "00000000000000011001001000011111101101010100010001000010110100011000010001101010".
  Definition e :=         s2bf "00000000000000010101101111110000101010001011000101000101011101101001010100110110".
  Definition pos_zero :=  s2bf "00000000000000000000000000000000000000000000000000000000000000000000000000000000".
  Definition log2_10 :=   s2bf "01111111111111111010100100110100111100001001011111011000001000110111000000000000".
  Definition log10_2 :=   s2bf "00111111110100000011010001000001001101010000101010010110000010011000000000000000".
  Definition ln_2  :=     s2bf "00111111111000000110001011100100001011111110111111111011101100111100000000000000".
  Definition log2_e :=    s2bf "00111111111110000111000101010100011101100101001100110010010001011110000000000000".
 
   (* Definition pos1_fl := de_float_of_bits   *)
   (*   (Zpos 0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0). *)
   (* Definition neg1_fl := de_float_of_bits  *)
   (*   (Zpos 1~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).  *)
   (* Definition pi_fl := de_float__of_bits  *)
   (*   (Zpos 0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0~1~0~0~1~0~0~0~0~1~1~1~1~1~1~0~1~1~0~1~0~1~0~1~0~0~0~1~0~0~0~1~0~0~0~0~1~0~1~1~0~1~0~0~0~1~1~0~0~0~0~1~0~0~0~1~1~0~1~0~1~0).  *)
   (* Definition e_fl := de_float_of_bits  *)
   (*   (Zpos 0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1~0~1~1~0~1~1~1~1~1~1~0~0~0~0~1~0~1~0~1~0~0~0~1~0~1~1~0~0~0~1~0~1~0~0~0~1~0~1~0~1~1~1~0~1~1~0~1~0~0~1~0~1~0~1~0~0~1~1~0~1~1~0).  *)
   (* Definition pos_zero_fl := de_float_of_bits  *)
   (*   (Zpos 0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).  *)
   (* Definition log2_10_fl := de_float_of_bits  *)
   (*   (Zpos 0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0~1~0~0~1~0~0~1~1~0~1~0~0~1~1~1~1~0~0~0~0~1~0~0~1~0~1~1~1~1~1~0~1~1~0~0~0~0~0~1~0~0~0~1~1~0~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0).  *)
   (* Definition log10_2_fl := de_float_of_bits  *)
   (*   (Zpos 0~0~1~1~1~1~1~1~1~1~0~1~0~0~0~0~0~0~1~1~0~1~0~0~0~1~0~0~0~0~0~1~0~0~1~1~0~1~0~1~0~0~0~0~1~0~1~0~1~0~0~1~0~1~1~0~0~0~0~0~1~0~0~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).  *)
   (* Definition ln_2_fl  := de_float_of_bits  *)
   (*   (Zpos 0~0~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~1~1~0~0~0~1~0~1~1~1~0~0~1~0~0~0~0~1~0~1~1~1~1~1~1~1~0~1~1~1~1~1~1~1~1~1~0~1~1~1~0~1~1~0~0~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0).  *)
   (* Definition log2_e_fl := de_float_of_bits  *)
   (*   (Zpos 0~0~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~1~1~1~0~0~0~1~0~1~0~1~0~1~0~0~0~1~1~1~0~1~1~0~0~1~0~1~0~0~1~1~0~0~1~1~0~0~1~0~0~1~0~0~0~1~0~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0). *)

  (* Get normal de_float representation to determine sign, then make mantissa the val of i and subtract
     most significant 1 to denormalize, then make exponent the number of significant bits of i. Then combine everything *)
  Definition integer_to_de_float (i : Word.int size80) : de_float := 
     let bin := int_to_de_float i in
     match bin with 
     | B754_zero s => B754_zero _ _ s
     | B754_infinity s => B754_infinity _ _ s
     | B754_nan => B754_nan _ _
     | B754_finite s m e _ => 
         let mant_val := Word.intval size80 i in
         let (rec, shifted_m) := shr (Build_shr_record mant_val false false) mant_val 1 in
         let exp_val := Z_of_nat size80 in  (*This probably needs to be replaced with the number of significant bits of i *)
         let joined := join_bits 64 16384 s (shifted_m - 1) exp_val in
         de_float_of_bits joined 
     end.
  
  Definition conv_FCLEX :=
    clear <- load_Z size3 0;
    set_fpu_status Pe clear;;
    set_fpu_status Ue clear;;
    set_fpu_status Oe clear;;
    set_fpu_status Ze clear;;
    set_fpu_status De clear;;
    set_fpu_status Ie clear;;

    clear0 <- cast_u size3 clear;
    set_fpu_control Pm clear0;;
    set_fpu_control Um clear0;;
    set_fpu_control Om clear0;;
    set_fpu_control Zm clear0;;
    set_fpu_control Dm clear0;;
    set_fpu_control Im clear0.

  (*Top may have to be 0 *)
  Definition init_top := sev <- load_Z size3 7; set_fpu_status Top sev.

  Definition set_CC_unordered := 
   onee <- load_Z size3 1;
   set_fpu_status C3 onee;; set_fpu_status C2 onee;; set_fpu_status C0 onee.

  Definition init_tags :=
    empty <- load_Z size2 3;
    set_fpu_tags Tag0 empty;;
    set_fpu_tags Tag1 empty;;
    set_fpu_tags Tag2 empty;;
    set_fpu_tags Tag3 empty;;
    set_fpu_tags Tag4 empty;;
    set_fpu_tags Tag5 empty;;
    set_fpu_tags Tag6 empty;;
    set_fpu_tags Tag7 empty.

  Definition conv_FINIT := 
     init_top;;
     set_CC_unordered;;
     conv_FCLEX;;
     init_tags. (*Probably init more stuff *)

 (*load val into an fpu-register stack where the top reg is stacktop and num is the number of registers from the top 
    where it is located, i.e num is i in st(i). *) 
  Definition set_stack_i (val : pseudo_reg size80) (top index : pseudo_reg size3): Conv unit := 
     set_fpu_reg val (int_to_fpu_reg top index).

 (*return the val of an fpu register where the top reg is stacktop and num is the number of registers from the top 
    where it is located, i.e num is i in st(i). *) 
  Definition load_from_stack_i (top index: pseudo_reg size3) : Conv (pseudo_reg size80) := 
     load_fpu_reg (int_to_fpu_reg top index).

  (*index is the tag index to update (corresponding to a given fpu stack register) and tagval is either 00, 01, 10, or 11, depending on 
    the value of st(index) 
  *)
  Definition update_tag (index : pseudo_reg size3) (tagval: pseudo_reg size2) :=
     zero <- load_Z size3 0;
     one <- load_Z size3 1;
     two <- load_Z size3 2;
     three <- load_Z size3 3;
     four <- load_Z size3 4;
     five <- load_Z size3 5;
     six <- load_Z size3 6;
     seven <- load_Z size3 7;
     
     t0 <- test eq_op index zero;
     t1 <- test eq_op index one;
     t2 <- test eq_op index two;
     t3 <- test eq_op index three;
     t4 <- test eq_op index four;
     t5 <- test eq_op index five;
     t6 <- test eq_op index six;
     t7 <- test eq_op index seven;
     
     emit if_rtl t0 (set_loc_rtl tagval (fpu_tag_loc Tag0));;
     emit if_rtl t1 (set_loc_rtl tagval (fpu_tag_loc Tag1));;
     emit if_rtl t2 (set_loc_rtl tagval (fpu_tag_loc Tag2));;
     emit if_rtl t3 (set_loc_rtl tagval (fpu_tag_loc Tag3));;
     emit if_rtl t4 (set_loc_rtl tagval (fpu_tag_loc Tag4));;
     emit if_rtl t5 (set_loc_rtl tagval (fpu_tag_loc Tag5));;
     emit if_rtl t6 (set_loc_rtl tagval (fpu_tag_loc Tag6));;
     emit if_rtl t7 (set_loc_rtl tagval (fpu_tag_loc Tag7)).

  (*Wraps around to 7 if current top is 0 *)
  Definition dec_stack (size : nat) := 
     t <- get_fpu_status Top;
     topp <- cast_u size t;
     z <- load_Z size 0;
     
     let (t) := topp in
     if (Zeq_bool t 0) then
         sev <- load_Z size3 7;
         set_fpu_status Top sev
     else
         one <- load_Z size 1;
         u <- arith sub_op topp one;
         upd <- cast_u size3 u;
         set_fpu_status Top upd.

  (*Wraps around to 0 if current top is 7 *)
  Definition inc_stack (size : nat) := 
     t <- get_fpu_status Top;
     topp <- cast_u size t;
     
     let (t) := topp in
     if (Zeq_bool t 7) then
        z <- load_Z size3 0;
        set_fpu_status Top z
     else
        one <- load_Z size 1;
        u <- arith add_op topp one;
        updd <- cast_u size3 u;
        set_fpu_status Top updd.

  Definition conv_FDECSTP := dec_stack size3.
  Definition conv_FINCSTP := inc_stack size3.

  Definition get_stacktop := topp <- get_fpu_status Top; castt <- cast_u size3 topp; Return castt.

  Definition psreg_to_int n (p : pseudo_reg n) : Word.int n := 
     let (val) := p in
     Word.repr val.

  Definition int_to_psreg n (i : Word.int n) : pseudo_reg n := 
     let val := Word.intval n i in
     ps_reg n val.


  Definition conv_FLD (op: fp_operand) := 
     topp <- get_stacktop;
     zero <- load_Z size3 0;
     match op with
     | FPS_op reg =>
       val <- load_fpu_reg (fpu_from_int reg topp);
       conv_FDECSTP;; 
       set_stack_i val topp zero
     | FPM16_op _ => emit error_rtl (* todo: fix this *)
     | FPM32_op a =>  
        addr <- compute_addr a; 
        val <- load_mem32 DS addr;
        conv_FDECSTP;;
        let int_val := psreg_to_int val in
        let b32_val := int_to_bin32 int_val in
        let conv_val := de_float_of_b32 b32_val in

        let ps_reg_val := int_to_psreg (de_float_to_int conv_val) in
        set_stack_i ps_reg_val topp zero
     | FPM64_op a =>
        addr <- compute_addr a; 
        val <- load_mem64 DS addr;
        conv_FDECSTP;;
        let int_val := psreg_to_int val in
        let b64_val := int_to_bin64 int_val in
        let conv_val := de_float_of_b64 b64_val in

        let ps_reg_val := int_to_psreg (de_float_to_int conv_val) in
        set_stack_i ps_reg_val topp zero
     | FPM80_op a =>
        addr <- compute_addr a; 
        val <- load_mem80 DS addr;
        conv_FDECSTP;;
        let int_val := psreg_to_int val in
        let b80_val := int_to_de_float int_val in

        let ps_reg_val := int_to_psreg (de_float_to_int b80_val) in
        set_stack_i ps_reg_val topp zero
     end.


  (*TODO: Include handling of invalid-operation exception (look at FST/FSTP instruction in manual) *)
  Definition conv_FST (op: fp_operand) := 
    topp <- get_stacktop;
    zero <- load_Z size3 0;
    top_val <- load_from_stack_i topp zero;
    
    match op with 
    | FPS_op reg =>    (*Copy st(0) to st(i) *)
      set_fpu_reg top_val (fpu_from_int reg topp)
    | FPM16_op a =>  emit error_rtl
    | FPM32_op a =>      (*Copy st(0) to memory *)
      addr <- compute_addr a;
      let int_val := psreg_to_int top_val in
      let b80_val := int_to_de_float int_val in
      let conv_val := b32_of_de_float b80_val in
      let psreg_val := int_to_psreg (bin32_to_int conv_val) in

      set_mem32 DS psreg_val addr
    | FPM64_op a =>
      addr <- compute_addr a;
      let int_val := psreg_to_int top_val in
      let f_val := int_to_de_float int_val in
      let conv_val := b64_of_de_float f_val in
      let psreg_val := int_to_psreg (bin64_to_int conv_val) in

      set_mem64 DS psreg_val addr
    | FPM80_op a =>
      addr <- compute_addr a;
      let int_val := psreg_to_int top_val in
      let b80_val := int_to_de_float int_val in
      let psreg_val := int_to_psreg (de_float_to_int b80_val) in

      set_mem80 DS psreg_val addr 
    end.

  Definition conv_FSTP (op: fp_operand) := 
    conv_FST op;;
    topp <- get_stacktop;
    empty <- load_Z size2 3;
    update_tag topp empty;;
    conv_FINCSTP.

  Definition conv_load_fpconstant (b: de_float) : Conv unit := 
     val <- load_int (de_float_to_int b);
     onee <- load_Z size3 1;
     top <- get_stacktop;
     decrval <- arith sub_op top onee;
     tagval <- load_Z size3 0;
     set_stack_i val decrval tagval;;
     tag_c <- cast_u size2 tagval;
     update_tag decrval tag_c.

  Definition conv_FLDZ : Conv unit := conv_load_fpconstant pos_zero.
  Definition conv_FLD1 : Conv unit := conv_load_fpconstant pos1.
  Definition conv_FLDPI : Conv unit := conv_load_fpconstant pi.
  Definition conv_FLDL2T : Conv unit := conv_load_fpconstant log2_10.
  Definition conv_FLDL2E : Conv unit := conv_load_fpconstant log2_e.
  Definition conv_FLDLG2 : Conv unit :=conv_load_fpconstant log10_2.
  Definition conv_FLDLN2 : Conv unit := conv_load_fpconstant ln_2.


  (* mode_UP seems to be the fastest computation-wise *)
  Definition add_to_stacktop80 (sec : pseudo_reg size80) :=
     zero <- load_Z size3 0;
     topp <- get_stacktop;
     stacktop_val <- load_from_stack_i topp zero;

     let(st0val) := stacktop_val in
     let first_val := int_to_de_float (Word.repr st0val) in

     let (stIval) := sec in
     let sec_val := int_to_de_float (Word.repr stIval) in
       
     let sum := de_float_plus mode_UP first_val sec_val in
     let sum_int := de_float_to_int sum in 
     let sum_val := ps_reg size80 (Word.intval size80 sum_int) in
     Return sum_val.  

  Definition sub_from_stacktop80 (sec : pseudo_reg size80) (order: bool) := 
    zero <- load_Z size3 0;
     topp <- get_stacktop;
     stacktop_val <- load_from_stack_i topp zero;

     let(st0val) := stacktop_val in
     let first_val := int_to_de_float (Word.repr st0val) in

     let (stIval) := sec in
     let sec_val := int_to_de_float (Word.repr stIval) in
       
     match order with 
     | true =>  
     	let sub := de_float_minus mode_UP first_val sec_val in
     	let sub_int := de_float_to_int sub in 
     	let sub_val := ps_reg size80 (Word.intval size80 sub_int) in
     	Return sub_val

     | false =>
	let sub := de_float_minus mode_UP sec_val first_val in
     	let sub_int := de_float_to_int sub in 
     	let sub_val := ps_reg size80 (Word.intval size80 sub_int) in
     	Return sub_val
     end.

  Definition mult_stacktop80 (sec : pseudo_reg size80) := 
     zero <- load_Z size3 0;
     topp <- get_stacktop;
     stacktop_val <- load_from_stack_i topp zero;

     let(st0val) := stacktop_val in
     let first_val := int_to_de_float (Word.repr st0val) in

     let (stIval) := sec in
     let sec_val := int_to_de_float (Word.repr stIval) in
       
     let mult := de_float_mult mode_UP first_val sec_val in
     let mult_int := de_float_to_int mult in 
     let mult_val := ps_reg size80 (Word.intval size80 mult_int) in
     Return mult_val. 

  Definition div_stacktop80 (sec : pseudo_reg size80) (order : bool) :=
     zero <- load_Z size3 0;
     topp <- get_stacktop;
     stacktop_val <- load_from_stack_i topp zero;

     let(st0val) := stacktop_val in
     let first_val := int_to_de_float (Word.repr st0val) in

     let (stIval) := sec in
     let sec_val := int_to_de_float (Word.repr stIval) in
     
     match order with 
     | true =>  
     	let div := de_float_div mode_UP first_val sec_val in
     	let div_int := de_float_to_int div in 
     	let div_val := ps_reg size80 (Word.intval size80 div_int) in
     	Return div_val

     | false =>
	let div := de_float_div mode_UP sec_val first_val in
     	let div_int := de_float_to_int div in 
     	let div_val := ps_reg size80 (Word.intval size80 div_int) in
     	Return div_val
     end.

  Definition sqrt_stacktop80 := 
     zero <- load_Z size3 0;
     topp <- get_stacktop;
     stacktop_val <- load_from_stack_i topp zero;

     let(st0val) := stacktop_val in
     let first_val := int_to_de_float (Word.repr st0val) in
       
     let rt := de_float_sqrt mode_UP first_val in
     let rt_int := de_float_to_int rt in 
     let rt_val := ps_reg size80 (Word.intval size80 rt_int) in
     Return rt_val.

  Definition sub80_topfirst (sec : pseudo_reg size80):= sub_from_stacktop80 sec true.
  Definition div80_topfirst (sec : pseudo_reg size80) := div_stacktop80 sec true. 
  Definition sub80_toplast (sec : pseudo_reg size80) := sub_from_stacktop80 sec false.
  Definition div80_toplast (sec : pseudo_reg size80) := div_stacktop80 sec false.  

  (*Performs a simple arithmetic operation on st(0) and st(i) and stores the result in one of those registers *)  
  Definition conv_simple_arith (d : bool) (st_i : fp_operand)
                               (operation : pseudo_reg size80-> Conv (pseudo_reg size80)) := 
     topp <- get_stacktop;
     zero <- load_Z size3 0;
     match st_i with 
     | FPS_op r => 
        next_val <- load_fpu_reg (fpu_from_int r topp);
        curr_val <- operation next_val;
        
        match d with 
        | false => set_stack_i curr_val topp zero  (*load sum into stacktop *) 
        | true => set_fpu_reg curr_val (fpu_from_int r topp)  (*load sum into st(i) *)
        end

     | FPM32_op a =>
        addr <- compute_addr a; 
        val <- load_mem32 DS addr;

        let int_val := psreg_to_int val in
        let b32_val := int_to_bin32 int_val in
        let conv_val := de_float_of_b32 b32_val in
        let ps_reg_sti := int_to_psreg (de_float_to_int conv_val) in
        
        curr_val <- operation ps_reg_sti;
        set_stack_i curr_val topp zero (*add from memory to stacktop *)
     | FPM64_op a =>
        addr <- compute_addr a; 
        val <- load_mem64 DS addr;

        let int_val := psreg_to_int val in
        let b64_val := int_to_bin64 int_val in
        let conv_val := de_float_of_b64 b64_val in
        let ps_reg_sti := int_to_psreg (de_float_to_int conv_val) in
        
        curr_val <- operation ps_reg_sti;
        set_stack_i curr_val topp zero (*add from memory to stacktop *)
     | _ => emit error_rtl
     end.

  (* " The FADDP instructions perform the additional operation of popping the FPU register 
       stack after storing the result. To pop the register stack, the processor marks the 
       ST(0) register as empty and increments the stack pointer (TOP) by 1. 
       (The nooperand version of the floating-point add instructions always results in the register 
       stack being popped" (FADD description in manual) *)
  Definition conv_simple_arith_and_pop (st_i : fp_operand)
	(operation : pseudo_reg size80 -> Conv (pseudo_reg size80))
     : Conv unit := 
     toploc <- get_stacktop;
     empty <- load_Z size2 3;
     update_tag toploc empty;;
     conv_simple_arith false st_i operation;;
     conv_FINCSTP.

  Definition conv_FSUB_or_FDIV_aux (op1 op2 : fp_operand) (order : bool)
	   (operation : pseudo_reg size80 -> bool -> Conv (pseudo_reg size80)) := 
     topp <- get_stacktop;
     zero <- load_Z size3 0;
     match op1, op2 with 
     | FPS_op zerr, FPM32_op a =>
	addr <- compute_addr a; 
        val <- load_mem32 DS addr;

        let int_val := psreg_to_int val in
        let b32_val := int_to_bin32 int_val in
        let conv_val := de_float_of_b32 b32_val in
        let ps_reg_sti := int_to_psreg (de_float_to_int conv_val) in
        
        curr_val <- operation ps_reg_sti order;
        set_stack_i curr_val topp zero 

     | FPS_op zerr, FPM64_op a =>
	addr <- compute_addr a; 
        val <- load_mem64 DS addr;

        let int_val := psreg_to_int val in
        let b64_val := int_to_bin64 int_val in
        let conv_val := de_float_of_b64 b64_val in
        let ps_reg_sti := int_to_psreg (de_float_to_int conv_val) in
        
        curr_val <- operation ps_reg_sti order;
        set_stack_i curr_val topp zero

     | FPS_op a, FPS_op b =>
	let reg_Z := Word.intval size3 a in
	match reg_Z with 
	| 0%Z =>   (* Means st(0) <- st(0) - st(i) *) 
	  sub_arg <- load_from_stack_i topp (int_to_psreg b);
	  diff <- operation sub_arg order;
	  set_stack_i diff topp zero 
	| _ =>     (* st(i) <- st(0) - st(i)   Here a is stI*)
          let ps_a := int_to_psreg a in
          sub_arg <- load_from_stack_i topp ps_a;
	  diff <- operation sub_arg order;
	  set_stack_i diff topp ps_a
        end 
     | _, _ => emit error_rtl
     end.


  Definition conv_FADD (d :bool) (st_i: fp_operand) : Conv unit := conv_simple_arith d st_i add_to_stacktop80.
  Definition conv_FSUB (op1 op2 : fp_operand) : Conv unit := conv_FSUB_or_FDIV_aux op1 op2 true sub_from_stacktop80.
  Definition conv_FMUL (d : bool) (st_i : fp_operand) : Conv unit := conv_simple_arith d st_i mult_stacktop80.
  Definition conv_FDIV (op1 op2 : fp_operand) : Conv unit := conv_FSUB_or_FDIV_aux op1 op2 true div_stacktop80.

  Definition conv_FADDP (st_i : fp_operand) : Conv unit := conv_simple_arith_and_pop st_i add_to_stacktop80.
  Definition conv_FSUBP (st_i : fp_operand) : Conv unit := conv_simple_arith_and_pop st_i sub80_topfirst.
  Definition conv_FMULP (st_i : fp_operand) : Conv unit := conv_simple_arith_and_pop st_i mult_stacktop80.
  Definition conv_FDIVP (st_i : fp_operand) : Conv unit := conv_simple_arith_and_pop st_i div80_topfirst.

  Definition conv_FSUBR (op1 op2 : fp_operand) : Conv unit := conv_FSUB_or_FDIV_aux op1 op2 false sub_from_stacktop80.
  Definition conv_FDIVR (op1 op2 : fp_operand) : Conv unit := conv_FSUB_or_FDIV_aux op1 op2 false div_stacktop80.


  Definition conv_FSUBRP (st_i : fp_operand) : Conv unit := conv_simple_arith_and_pop st_i sub80_toplast.
  Definition conv_FDIVRP (st_i : fp_operand) : Conv unit := conv_simple_arith_and_pop st_i div80_toplast.

(*  
  Definition conv_simple_integer_arith (st_i : operand) 
        (operation : pseudo_reg size80 -> Conv (pseudo_reg size80)) : Conv unit := 
     match st_i with 
     | Address_op addr =>
     (* let (d, b, i) := addr in  eventually going to have to figure out how to differentiate between size16 and size32 memory *)
       a <- compute_addr addr;
       loadaddr <- load_mem32 SS a;
       let (lval) := loadaddr in
       let intlval := Word.repr lval in
       let val := integer_to_bin80 intlval in
       int_operation (ps_reg size80 (bits_of_b80 val)) At 
     end.
*)

(* Floating-point Comparisons *)
(* gtan: cannot use Rcompare here, no Ocaml code can be extracted *)
(* Definition float_compare (a b : binary80) :=  *)
(*    let aR := B2R 64 16384 a in *)
(*    let bR := B2R 64 16384 b in *)
(*    Rcompare aR bR. *)

(* Set appropriate CC flags that indicate the result of the comparison *)
Definition set_CC_flags (comp : comparison) : Conv unit := 
    zero <- load_Z size3 0;
    onee <- load_Z size3 1;
    match comp with 
    | Lt => set_fpu_status C3 zero;; set_fpu_status C2 zero;; set_fpu_status C0 onee
    | Gt => set_fpu_status C3 zero;; set_fpu_status C2 zero;; set_fpu_status C0 zero
    | Eq => set_fpu_status C3 onee;; set_fpu_status C2 zero;; set_fpu_status C0 zero
    end.

(* Definition conv_FCOM (op1: option fp_operand) :=  *)
(*      topp <- get_stacktop; *)
(*      zero <- load_Z size3 0; *)
(*      onee <- load_Z size3 1; *)
(*      st0 <- load_from_stack_i topp zero; *)
(*      let (st0val) := st0 in *)
(*      let binst0 := b80_of_bits st0val in *)
(*      match op1 with  *)
(*      | None => (* Compare st(0) to st(1) *) *)
(* 	 st1 <- load_from_stack_i topp onee; *)
(*          let (st1val) := st1 in *)
(*          let compval := float_compare binst0 (b80_of_bits st1val) in *)
(*          set_CC_flags compval *)
         	 
(*      | Some op1 => *)
(* 	match op1 with *)
(* 	| FPS_op r => *)
(*             stI <- load_fpu_reg (fpu_from_int r topp); *)
(*             let (stIval) := stI in *)
(*             let compval := float_compare binst0 (b80_of_bits stIval) in *)
(*             set_CC_flags compval *)

(* 	| FPM32_op adr =>  *)
(*             addr <- compute_addr adr;  *)
(*             val <- load_mem32 DS addr; *)

(*             let int_val := psreg_to_int val in *)
(*             let b32_val := int_to_bin32 int_val in *)
(*             let conv_val := b32_to_b80 b32_val in *)
(*             let psreg_stI := int_to_psreg (bin80_to_int conv_val) in *)
(*             let (stIval) := psreg_stI in *)
(*             let compval := float_compare binst0 (b80_of_bits stIval) in *)
(*             set_CC_flags compval *)
(*         | FPM64_op adr => *)
(*             addr <- compute_addr adr;  *)
(*             val <- load_mem64 DS addr; *)

(*             let int_val := psreg_to_int val in *)
(*             let b64_val := int_to_bin64 int_val in *)
(*             let conv_val := b64_to_b80 b64_val in *)
(*             let psreg_stI := int_to_psreg (bin80_to_int conv_val) in *)
(*             let (stIval) := psreg_stI in *)
(*             let compval := float_compare binst0 (b80_of_bits stIval) in *)
(*             set_CC_flags compval *)
(* 	| _ => set_CC_unordered *)
(* 	end *)
(*      end. *)

(* Definition conv_FCOMP (op1 : option fp_operand) :=  *)
(*     conv_FCOM op1;; *)
(*     toploc <- get_stacktop; *)
(*     empty <- load_Z size2 3; *)
(*     update_tag toploc empty;; *)
(*     conv_FINCSTP. *)

(* Definition conv_FCOMPP :=  *)
(*     conv_FCOMP (None);; *)
   
(*     toploc <- get_stacktop; *)
(*     empty <- load_Z size2 3; *)
(*     update_tag toploc empty;; *)
(*     conv_FINCSTP. *)

End X86FloatSemantics.

  Definition instr_to_rtl (pre: prefix) (i: instr) :=
    runConv 
    (check_prefix pre;;
     match i with
         | AND w op1 op2 => conv_AND pre w op1 op2
         | OR w op1 op2 => conv_OR pre w op1 op2
         | XOR w op1 op2 => conv_XOR pre w op1 op2
         | TEST w op1 op2 => conv_TEST pre w op1 op2
         | NOT w op1 => conv_NOT pre w op1
         | INC w op1 => conv_INC pre w op1
         | DEC w op1 => conv_DEC pre w op1
         | ADD w op1 op2 => conv_ADD pre w op1 op2
         | ADC w op1 op2 => conv_ADC pre w op1 op2
         | CMP w op1 op2 => conv_CMP pre w op1 op2
         | SUB w op1 op2 => conv_SUB pre w op1 op2
         | SBB w op1 op2 => conv_SBB pre w op1 op2
         | NEG w op1 => conv_NEG pre w op1 
         | DIV w op => conv_DIV pre w op
         | AAA => conv_AAA_AAS add_op
         | AAS => conv_AAA_AAS sub_op
         | AAD => conv_AAD
         | AAM => conv_AAM
         | DAA => conv_DAA_DAS (add_op) (@testcarryAdd size8)
         | DAS => conv_DAA_DAS (sub_op) (@testcarrySub size8)
         | HLT => conv_HLT pre
         | IDIV w op => conv_IDIV pre w op
         | IMUL w op1 op2 i => conv_IMUL pre w op1 op2 i
         | MUL w op  => conv_MUL pre w op
         | SHL w op1 op2 => conv_SHL pre w op1 op2
         | SHR w op1 op2 => conv_SHR pre w op1 op2
         | SHLD op1 op2 ri => conv_SHLD pre op1 op2 ri
         | SHRD op1 op2 ri => conv_SHRD pre op1 op2 ri
         | SAR w op1 op2 => conv_SAR pre w op1 op2
         | BSR op1 op2 => conv_BSR pre op1 op2
         | BSF op1 op2 => conv_BSF pre op1 op2
         | BT op1 op2 => conv_BT false true pre op1 op2
         | BTC op1 op2 => conv_BT false false pre op1 op2
         | BTS op1 op2 => conv_BT true true pre op1 op2
         | BTR op1 op2 => conv_BT true false pre op1 op2
         | BSWAP r => conv_BSWAP pre r
         | CWDE => conv_CWDE pre
         | CDQ => conv_CDQ pre
         | MOV w op1 op2 => conv_MOV pre w op1 op2 
         | CMOVcc ct op1 op2 => conv_CMOV pre true ct op1 op2 
         | MOVZX w op1 op2 => conv_MOVZX pre w op1 op2 
         | MOVSX w op1 op2 => conv_MOVSX pre w op1 op2 
         | XCHG w op1 op2 => conv_XCHG pre w op1 op2 
         | XADD w op1 op2 => conv_XADD pre w op1 op2 
         | CLC => conv_CLC
         | CLD => conv_CLD
         | STD => conv_STD
         | STC => conv_STC
         | MOVS w => conv_MOVS pre w
         | CMPXCHG w op1 op2 => conv_CMPXCHG pre w op1 op2
         | CMPS w => conv_CMPS pre w
         | STOS w => conv_STOS pre w
         | LEA op1 op2 => conv_LEA pre op1 op2
         | SETcc ct op => conv_SETcc pre ct op
         | CALL near abs op1 sel => conv_CALL pre near abs op1 sel
         | LEAVE => conv_LEAVE pre
         | POP op => conv_POP pre op
         | POPA => conv_POPA pre
         | PUSH w op => conv_PUSH pre w op
         | PUSHA => conv_PUSHA pre
         | RET ss disp => conv_RET pre ss disp
         | ROL w op1 op2 => conv_ROL pre w op1 op2
         | ROR w op1 op2 => conv_ROR pre w op1 op2
         | RCL w op1 op2 => conv_RCL pre w op1 op2  
         | RCR w op1 op2 => conv_RCR pre w op1 op2  
         | LAHF => conv_LAHF
         | SAHF => conv_SAHF
         | CMC => conv_CMC
         | JMP near abs op1 sel => conv_JMP pre near abs op1 sel
         | Jcc ct disp => conv_Jcc pre ct disp 
         | LOOP disp => conv_LOOP pre false false disp
         | LOOPZ disp => conv_LOOP pre true true disp
         | LOOPNZ disp => conv_LOOP pre true false disp
         | NOP _ => ret tt
         (*Floating-point conversions*)
    (*     | F2XM1 => conv_F2XM1 pre
         | FABS => conv_FABS *)
         | FADD d op1 => conv_FADD d op1
         | FADDP op1 => conv_FADDP op1  
    (*     | FBLD op1 => conv_FBLD pre op1
         | FBSTP op1 => conv_FBSTP pre op1
         | FCHS => conv_FCHS
         | FCLEX => conv_FCLEX      *)
         (* | FCOM op1 => conv_FCOM op1 *)
         (* | FCOMP op1 => conv_FCOMP op1 *)
         (* | FCOMPP => conv_FCOMPP *)
   (*      | FCOMIP op1 => conv_FCOMIP pre op1
         | FCOS => conv_FCOS       *)
         | FDECSTP => conv_FDECSTP
           (* gtan: comment out FDIV case for now as I have changed the syntax of FDIV *)
         (* | FDIV a b c d => conv_FDIV a b c d *)
         | FDIVP op1 => conv_FDIVP op1
      (*   | FDIVR : conv_FDIVR pre d r1 r2 op1
         | FDIVRP : conv_FDIVRP pre op1
         | FFREE : conv_FFREE pre op1
         | FIADD : conv_FIADD pre op1
         | FICOM : conv_FICOM pre op1
         | FICOMP : conv_FICOMP pre op1
         | FIDIV : conv_FIDIV pre op1
         | FIDIVR : conv_FIDIVR pre op1
         | FILD : conv_FILD pre op1
         | FIMUL : conv_FIMUL pre op1
         | FINCSTP : conv_FINCSTP
         | FINIT : conv_FINIT
         | FIST : conv_FIST
         | FISTP : conv_FISTP
         | FISUB : conv_FISUB
         | FISUBR : conv_FISUBR    *)
         | FLD a => conv_FLD a
         | FLD1 => conv_FLD1
       (*  | FLDCW : conv_FLDCW
         | FLDENV : conv_FLDENV  *)
         | FLDL2E => conv_FLDL2E
         | FLDL2T => conv_FLDL2T
         | FLDLG2 => conv_FLDLG2
         | FLDLN2 => conv_FLDLN2
         | FLDPI => conv_FLDPI
         | FLDZ => conv_FLDZ
         | FMUL d op1 => conv_FMUL d op1
         | FMULP op1 => conv_FMULP op1
       (*  | FNOP : conv_FNOP
         | FNSTCW => conv_FNSTCW
         | FPATAN : conv_FPATAN
         | FPREM : conv_FPREM
         | FPREM1 : conv_FPREM1
         | FPTAN : conv_FPTAN
         | FRNDINT : conv_FRNDINT
         | FRSTOR : conv_FRSTOR pre op1
         | FSAVE : conv_FSAVE pre op1
         | FSCALE : conv_FSCALE
         | FSIN : conv_FSIN
         | FSINCOS : conv_FSINCOS
         | FSQRT : conv_FSQRT
         | FST : conv_FST pre op1
         | FSTCW : conv_FSTCW pre op1
         | FSTENV : conv_FSTENV pre op1
         | FSTP : conv_FSTP pre op1
         | FSTSW : conv_FSTSW pre op1     *)
           (* gtan: comment out FSUB case for now as I have changed its syntax *)
         (* | FSUB d r1 r2 op1 => conv_FSUB d r1 r2 op1 *)
         | FSUBP op1 => conv_FSUBP op1
       (*  | FSUBR : conv_FSUBR pre d r1 r2 op1
         | FSUBRP : conv_FSUBRP pre op1
         | FTST : conv_FTST
         | FUCOM : conv_FUCOM pre op1
         | FUCOMP : conv_FUCOMP pre op1
         | FUCOMPP : conv_FUCOMPP
         | FUCOMI : conv_FUCOMI pre op1
         | FUCOMIP : conv_FUCOMIP pre op1
         | FXAM : conv_FXAM
         | FXCH : conv_FXCH pre op1
         | FXTRACT : conv_FXTRACT
         | FYL2X : conv_FYL2X
         | FYL2XP1 : conv_FYL2XP1
         | FWAIT : conv_FWAIT     *)
         | _ => emit error_rtl 
    end
    ).

End X86_Decode.

Local Open Scope Z_scope.
Local Open Scope monad_scope.
Import X86_Decode.
Import X86_RTL.
Import X86_MACHINE.

Definition in_seg_bounds (s: segment_register) (o1: int32) : RTL bool :=
  seg_limit <- get_loc (seg_reg_limit_loc s);
  ret (Word.lequ o1 seg_limit).

Definition in_seg_bounds_rng (s: segment_register) (o1: int32) 
  (offset: int32) : RTL bool :=
  seg_limit <- get_loc (seg_reg_limit_loc s);
  let o2 := Word.add o1 offset in
  ret (andb (Word.lequ o1 o2)
            (Word.lequ o2 seg_limit)).

(** fetch n bytes starting from the given location. *)
Fixpoint fetch_n (n:nat) (loc:int32) (r:rtl_state) : list int8 := 
  match n with 
    | 0%nat => nil
    | S m => 
      AddrMap.get loc (rtl_memory r) :: 
        fetch_n m (Word.add loc (Word.repr 1)) r
  end.

(** Go into a loop trying to parse an instruction.  We iterate at most [n] times,
    and at least once.  This returns the first successful match of the parser
    as well as the length (in bytes) of the matched instruction.  Right now, 
    [n] is set to 15 but it should probably be calculated as the longest possible
    match for the instruction parsers.  The advantage of this routine over the
    previous one is two-fold -- first, we are guaranteed that the parser only
    succeeds when we pass in bytes.  Second, we only fetch bytes that are
    needed, so we don't have to worry about running out side a segment just
    to support parsing.
*)
Fixpoint parse_instr_aux
  (n:nat) (loc:int32) (len:positive) (ps:Decode.X86_PARSER.instParserState) : 
  RTL ((prefix * instr) * positive) := 
  match n with 
    | 0%nat => Fail _ 
    | S m => b <- get_byte loc ; 
             match Decode.X86_PARSER.parse_byte ps b with 
               | (ps', nil) => 
                 parse_instr_aux m (Word.add loc (Word.repr 1)) (len + 1) ps'
               | (_, v::_) => ret (v,len)
             end
  end.

Definition parse_instr (pc:int32) : RTL ((prefix * instr) * positive) :=
  seg_start <- get_loc (seg_reg_start_loc CS);
  (* add the PC to it *)
  let real_pc := Word.add seg_start pc in
    parse_instr_aux 15 real_pc 1 Decode.X86_PARSER.initial_parser_state.

(** Fetch an instruction at the location given by the program counter.  Return
    the abstract syntax for the instruction, along with a count in bytes for 
    how big the instruction is.  We fail if the bits do not parse, or have more
    than one parse.  We should fail if these locations aren't mapped, but we'll
    deal with that later. *)
Definition fetch_instruction (pc:int32) : RTL ((prefix * instr) * positive) :=
  [pi, len] <- parse_instr pc;
  in_bounds_rng <- in_seg_bounds_rng CS pc (Word.repr (Zpos len - 1));
  if (in_bounds_rng) then ret (pi,len)
  else SafeFail _.

Fixpoint RTL_step_list l :=
  match l with
    | nil => ret tt
    | i::l' => interp_rtl i;; RTL_step_list l'
  end.

Definition check_rep_instr (ins:instr) : RTL unit :=
  match ins with
    | MOVS _ | STOS _ | CMPS _ => ret tt
    | _ => Fail _
  end.

Definition run_rep 
  (pre:prefix) (ins: instr) (default_new_pc : int32) : RTL unit := 
  check_rep_instr ins;;
  ecx <- get_loc (reg_loc ECX);
  if (Word.eq ecx Word.zero) then set_loc pc_loc default_new_pc
    else 
      set_loc (reg_loc ECX) (Word.sub ecx Word.one);;
      RTL_step_list (X86_Decode.instr_to_rtl pre ins);;
      ecx' <- get_loc (reg_loc ECX);
      (if (Word.eq ecx' Word.zero) then 
        set_loc pc_loc default_new_pc
        else ret tt);;
       (* For CMPS we also need to break from the loop if ZF = 0 *)
      match ins with
        | CMPS _ =>
          zf <- get_loc (flag_loc ZF);
          if (Word.eq zf Word.zero) then set_loc pc_loc default_new_pc
          else ret tt
        | _ => ret tt
      end.

Definition step : RTL unit := 
  flush_env;;
  pc <- get_loc pc_loc ; 
  (* check if pc is in the code region; 
     different from the range checks in fetch_instruction; 
     this check makes sure the machine safely fails when pc is 
     out of bounds so that there is no need to fetch an instruction *)
  pc_in_bounds <- in_seg_bounds CS pc;
  if (pc_in_bounds) then 
    [pi,length] <- fetch_instruction pc ; 
    let (pre, instr) := pi in
    let default_new_pc := Word.add pc (Word.repr (Zpos length)) in
      match lock_rep pre with
        | Some rep (* We'll only allow rep, not lock or repn *) =>
          run_rep pre instr default_new_pc
        | None => set_loc pc_loc default_new_pc;; 
                  RTL_step_list (X86_Decode.instr_to_rtl pre instr)
        | _ => Fail _ 
      end
  else SafeFail _.

Definition step_immed (m1 m2: rtl_state) : Prop := step m1 = (Okay_ans tt, m2).
Notation "m1 ==> m2" := (step_immed m1 m2).
Require Import Relation_Operators.
Definition steps := clos_refl_trans rtl_state step_immed.
Notation "m1 '==>*' m2" := (steps m1 m2) (at level 55, m2 at next level).
