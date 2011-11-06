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
Require Import MIPSSyntax.
Require Import RTL.
Set Implicit Arguments.
Unset Automatic Introduction.

Module MIPS_MACHINE.
  Local Open Scope Z_scope.
  Local Open Scope string_scope.

  Definition size_addr := size32.

  Inductive loc : nat -> Set := 
  | reg_loc : register -> loc size32
  | hi_loc : loc size32
  | lo_loc : loc size32
  | pc_loc : loc size32
    (*Whether or not the next instruction is executed as a branch delay*)
  | bdelay_active_loc : loc size1
    (*The pc to go to after the branch delay*)
  | bdelay_pc_loc : loc size32
.

  Definition location := loc.

  Definition fmap (A B:Type) := A -> B.
  Definition upd A (eq_dec:forall (x y:A),{x=y}+{x<>y}) B (f:fmap A B) (x:A) (v:B) : 
    fmap A B := fun y => if eq_dec x y then v else f y.
  Definition look A B (f:fmap A B) (x:A) : B := f x.

  Record mach := { 
    gp_regs : fmap register int32 ; 
    hi_reg : int32;
    lo_reg : int32;
    pc_reg : int32;
    bdelay_active_f : int1;
    bdelay_pc_reg : int32
  }.
  Definition mach_state := mach.

  Definition get_location s (l:loc s) (m:mach_state) : int s := 
    match l in loc s' return int s' with 
      | reg_loc r => 
        match r with 
          | Reg 0 => Word.zero
          | _ => look (gp_regs m) r
        end
      | hi_loc => hi_reg m
      | lo_loc => lo_reg m
      | pc_loc => pc_reg m
      | bdelay_active_loc => bdelay_active_f m
      | bdelay_pc_loc => bdelay_pc_reg m
    end.

  Definition set_gp_regs r v m := 
    {| gp_regs := 
       match r with 
         | Reg 0 => gp_regs m
         | _ => upd register_eq_dec (gp_regs m) r v  
       end;
       hi_reg := hi_reg m;
       lo_reg := lo_reg m;
       pc_reg := pc_reg m;
       bdelay_active_f := bdelay_active_f m;
       bdelay_pc_reg := bdelay_pc_reg m
    |}.
  Definition set_pc v m := 
    {| gp_regs := gp_regs m ;
       hi_reg := hi_reg m;
       lo_reg := lo_reg m;
       pc_reg := v;
       bdelay_active_f := bdelay_active_f m;
       bdelay_pc_reg := bdelay_pc_reg m
    |}.
 
  Definition set_hi v m := 
    {| gp_regs := gp_regs m ;
       hi_reg := v;
       lo_reg := lo_reg m;
       pc_reg := pc_reg m;
       bdelay_active_f := bdelay_active_f m;
       bdelay_pc_reg := bdelay_pc_reg m
    |}.

  Definition set_lo v m := 
    {| gp_regs := gp_regs m ;
       hi_reg := hi_reg m;
       lo_reg := v;
       pc_reg := pc_reg m;
       bdelay_active_f := bdelay_active_f m;
       bdelay_pc_reg := bdelay_pc_reg m
    |}.

  Definition set_bdelay v m := 
    {| gp_regs := gp_regs m ;
       hi_reg := hi_reg m;
       lo_reg := lo_reg m;
       pc_reg := pc_reg m;
       bdelay_active_f := bdelay_active_f m;
       bdelay_pc_reg := v
    |}.

  Definition set_bdelay_f v m := 
    {| gp_regs := gp_regs m ;
       hi_reg := hi_reg m;
       lo_reg := lo_reg m;
       pc_reg := pc_reg m;
       bdelay_active_f := v;
       bdelay_pc_reg := bdelay_pc_reg m
    |}.
  Definition set_location s (l:loc s) (v:int s) m := 
    match l in loc s' return int s' -> mach_state with 
      | reg_loc r => fun v => set_gp_regs r v m
      | hi_loc => fun v => set_hi v m
      | lo_loc => fun v => set_lo v m
      | pc_loc => fun v => set_pc v m
      | bdelay_active_loc => fun v => set_bdelay_f v m
      | bdelay_pc_loc => fun v => set_bdelay v m
    end v.
End MIPS_MACHINE.

Module MIPS_RTL := RTL.RTL(MIPS_MACHINE).

Module MIPS_Decode.
  Import MIPS_MACHINE.
  Import MIPS_RTL.
  Local Open Scope monad_scope.
  Record conv_state := { c_rev_i : list rtl_instr ; c_next : Z }.
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
  Definition cast_u s1 s2 (r:pseudo_reg s1) := fresh (@cast_u_rtl s1 s2 r).
  Definition cast_s s1 s2 (r:pseudo_reg s1) := fresh (@cast_s_rtl s1 s2 r).
  Definition read_byte (a:pseudo_reg size32) := fresh (get_byte_rtl a).
  Definition write_byte (v:pseudo_reg size8) (a:pseudo_reg size32) := 
    emit set_byte_rtl v a.

  Definition get_pc := fresh (get_loc_rtl pc_loc).
  Definition set_pc v := emit set_loc_rtl v pc_loc.

  Definition get_hi := fresh (get_loc_rtl hi_loc).
  Definition get_lo := fresh (get_loc_rtl lo_loc).
  Definition set_hi v := emit set_loc_rtl v hi_loc.
  Definition set_lo v := emit set_loc_rtl v lo_loc.

  Definition get_bdelayf := fresh (get_loc_rtl bdelay_active_loc).
  Definition get_bdelaypc := fresh (get_loc_rtl bdelay_pc_loc).
  (*Helper functions for setting the pc in a branch delayed way with / without a 
     conditional flag*)
  Definition set_bdelay_cond f v :=
    ttrue <- load_int Word.one;
    (emit (if_rtl f (set_loc_rtl ttrue bdelay_active_loc));;
      emit (if_rtl f (set_loc_rtl v bdelay_pc_loc))).
  Definition set_bdelay v:= 
    ttrue <- load_int Word.one;
    (emit (set_loc_rtl ttrue bdelay_active_loc);;
      emit (set_loc_rtl v bdelay_pc_loc)).
  Definition clear_bdelay :=
    tzero <- load_int Word.zero;
    tfalse <- load_int Word.zero;
    emit (set_loc_rtl tfalse bdelay_active_loc);;
    emit (set_loc_rtl tzero bdelay_pc_loc).
  (*If a delay is present, set the pc. Always clear the delay*)
  (*This check should be done before every non-cflow instruction*)
  Definition bd_prologue :=
    bdf <- get_bdelayf;
    bdpc <- get_bdelaypc;
    emit (if_rtl bdf (set_loc_rtl bdpc pc_loc));;
    clear_bdelay
  .
    (*If a delay is present for a control flow instruction, undefined behavior*)
  Definition bd_prologue_cf :=
    bdf <- get_bdelayf;
    emit (if_rtl bdf (error_rtl))
  .
 

  Definition not {s} (p: pseudo_reg s) : Conv (pseudo_reg s) :=
    mask <- load_Z s (Word.max_unsigned s);
    arith xor_op p mask.

  Definition bnot (p: pseudo_reg size1) : Conv (pseudo_reg size1) :=
    pone <- load_Z size1 1%Z;
    arith xor_op pone p.
  Definition neg {s} (p: pseudo_reg s) : Conv (pseudo_reg s) :=
    pzero <- load_Z s 0%Z;
    arith sub_op pzero p.
  Definition undef s :=
    fresh (@choose_rtl s)
.

  (* Copy the contents of rs to a new pseudo register *)
  Definition copy_ps s (rs:pseudo_reg s) := fresh (@cast_u_rtl s s rs).

  Definition onemaskl s n : Conv (pseudo_reg s) :=
    numshift <- load_Z s ((Z_of_nat s)+1-n);
    mask <- load_Z s (Word.max_unsigned s);
    maskr <- arith shr_op mask numshift;
    arith shl_op maskr numshift
    .
    
  (* compute an effective address *)
  Definition compute_addr(r:register) (i:int16) : Conv (pseudo_reg size32) := 
    b <- load_reg r;
    disp16 <- load_int i;
    disp32 <- cast_s size32 disp16;
    arith add_op b disp32
  .

  (* load a byte from memory, taking into account the specified segment *)
  Definition lmem (a:pseudo_reg size32) : Conv (pseudo_reg size8):=
    read_byte a.

  (* store a byte to memory, taking into account the specified segment *)
  Definition smem (v:pseudo_reg size8) (a:pseudo_reg size32) :
    Conv unit := 
    write_byte v a.

  (* load an n-byte vector from memory -- takes into account the segment *)
  Program Fixpoint load_mem_n (addr:pseudo_reg size32)
    (nbytes_minus_one:nat) : Conv (pseudo_reg ((nbytes_minus_one+1) * 8 -1)%nat) := 
    match nbytes_minus_one with 
      | 0 => lmem addr
      | S n => 
        rec <- load_mem_n addr n ; 
        count <- load_Z size32 (Z_of_nat (S n)) ; 
        p3 <- arith add_op addr count ;
        nb <- lmem p3 ; 
        p5 <- cast_u ((nbytes_minus_one + 1)*8-1)%nat rec ; 
        p6 <- cast_u ((nbytes_minus_one + 1)*8-1)%nat nb ;
        p7 <- load_Z _ (Z_of_nat (S n) * 8) ;
        p8 <- arith shl_op p6 p7 ;
        arith or_op p5 p8
    end.

  Definition load_mem32 (addr:pseudo_reg size32) := 
    load_mem_n addr 3.
  Definition load_mem16 (addr:pseudo_reg size32) := 
    load_mem_n addr 1.
  Definition load_mem8 (addr:pseudo_reg size32) := 
    load_mem_n addr 0.
  (* set memory with an n-byte vector *)
  Program Fixpoint set_mem_n {t}
    (v: pseudo_reg (8*(t+1)-1)%nat) (addr : pseudo_reg size32) : Conv unit := 
    match t with 
      | 0 => smem v addr
      | S u => 
        p1 <- cast_u (8*(u+1)-1)%nat v ; 
        set_mem_n p1 addr ;; 
        p2 <- load_Z (8*(t+1)-1)%nat (Z_of_nat  ((S u) * 8)) ; 
        p3 <- arith shru_op v p2 ;
        p4 <- cast_u size8 p3 ; 
        p5 <- load_Z size32 (Z_of_nat (S u)) ; 
        p6 <- arith add_op p5 addr ;
        smem p4 p6
    end.

  Definition set_mem32  (v a:pseudo_reg size32) : Conv unit :=
    @set_mem_n 3 v a.
  Definition set_mem16  (v: pseudo_reg size16)
    (a:pseudo_reg size32) : Conv unit :=
      @set_mem_n 1 v a.
  Definition set_mem8  (v: pseudo_reg size8) 
    (a:pseudo_reg size32) : Conv unit :=
      @set_mem_n 0 v a.
  (**********************************************)
  (*   Conversion functions for instructions    *)
  (**********************************************)

  (************************)
  (* Arith ops            *)
  (************************)

  Definition OF_check_add (a1:pseudo_reg size32) a2 sum : Conv unit :=
        zero <- load_Z _ 0;
        sign1 <- test lt_op zero a1;
        sign2 <- test lt_op zero a2;
        signsum <- test lt_op zero sum;
        sign_op_eq <- test eq_op sign1 sign2;
        sign_res_neq <- @arith size1 xor_op sign1 signsum;
        of_flag <- @arith size1 and_op sign_op_eq sign_res_neq;
        (*Throw an exception if there was an overflow*)
        emit if_rtl of_flag safe_fail_rtl
        .
  Definition OF_check_sub (a1:pseudo_reg size32) a2 diff : Conv unit :=
        zero <- load_Z _ 0;
        sign1 <- test lt_op zero a1;
        sign2 <- test lt_op zero a2;
        signdiff <- test lt_op zero diff;
        sign_op_neq <- arith xor_op sign1 sign2;
        sign_res_neq <- @arith size1 xor_op sign1 signdiff;
        of_flag <- @arith size1 and_op sign_op_neq sign_res_neq;
        (*Throw an exception if there was an overflow*)
        emit if_rtl of_flag safe_fail_rtl
        .
  Definition conv_ADD (rop: roperand) : Conv unit :=
    match rop with
      | Rop rs rt rd _ =>
        a1 <- load_reg rs;
        a2 <- load_reg rt;
        sum <- arith add_op a1 a2;
        OF_check_add a1 a2 sum;;
        set_reg sum rd
    end.
  Definition conv_ADDU (rop: roperand) : Conv unit :=
    match rop with
      | Rop rs rt rd _ =>
        a1 <- load_reg rs;
        a2 <- load_reg rt;
        sum <- arith add_op a1 a2;
        set_reg sum rd
    end.

  Definition conv_SUB (rop:roperand) : Conv unit :=
    match rop with | Rop rs rt rd _ =>
      a1 <- load_reg rs;
      a2 <- load_reg rt;
      diff <- arith sub_op a1 a2;
      OF_check_sub a1 a2 diff;;
      set_reg diff rd
    end.
  

  Definition conv_SUBU (rop:roperand) : Conv unit :=
    match rop with | Rop rs rt rd _ =>
      a1 <- load_reg rs;
      a2 <- load_reg rt;
      diff <- arith sub_op a1 a2;
      set_reg diff rd
    end.
  
  Definition conv_ADDIs (sign:bool) (iop: ioperand) : Conv unit :=
    match iop with
      | Iop rs rt i =>
        a1 <- load_reg rs;
        pi <- load_int i;
        a2 <- cast_s size32 pi;
        sum <- arith add_op a1 a2;
        match sign with 
          | true =>
            OF_check_add a1 a2 sum;;
            set_reg sum rt
          | false =>
            set_reg sum rt
        end
    end.
  Definition conv_ADDI := conv_ADDIs true.
  Definition conv_ADDIU := conv_ADDIs false.
  
  Definition conv_MUL (rop: roperand) : Conv unit :=
    match rop with | Rop rs rt rd _  =>
      a1 <- load_reg rs;
      a2 <- load_reg rt;
      prod <- arith mul_op a1 a2;
      set_reg prod rd;;
      rand1 <- undef size32;
      set_hi rand1;;
      rand2 <- undef size32;
      set_lo rand2
    end.
  Definition conv_MULTs caster (rop: roperand) : Conv unit :=
    match rop with | Rop rs rt _ _ =>
      a1 <- load_reg rs;
      a2 <- load_reg rt;
      a1e <- caster a1;
      a2e <- caster a2;
      prod <- arith mul_op a1e a2e;
      prodlo <- cast_u size32 prod;
      p32 <- load_Z 63 32;
      prods <- arith shru_op prod p32;
      prodhi <- cast_u size32 prods;
      set_hi prodhi;;
      set_lo prodlo
    end.
  Definition conv_MULT (rop:roperand) : Conv unit := conv_MULTs (cast_s 63) rop.
  Definition conv_MULTU (rop:roperand) : Conv unit := conv_MULTs (cast_u 63) rop.

  (*How is the signed modulus taken?*)
  Definition conv_DIVs (divop:bit_vector_op) (modop:bit_vector_op) (rop: roperand) : Conv unit :=
    match rop with | Rop rs rt _ _ =>
      a1 <- load_reg rs;
      a2 <- load_reg rt;
      pzero <- load_Z size32 0;
      divbyzero <- test eq_op a2 pzero;
      emit (if_rtl divbyzero error_rtl);;
      quo <- arith divop a1 a2;
      rem <- arith modop a1 a2;
      set_lo quo;;
      set_hi rem
    end.
  Definition conv_DIV := conv_DIVs divs_op mods_op.
  Definition conv_DIVU := conv_DIVs divu_op modu_op.

  Definition conv_MFHI (rop: roperand) : Conv unit :=
    match rop with | Rop _ _ rd _ =>
      hi <- get_hi;
      set_reg hi rd
    end.
  Definition conv_MFLO (rop: roperand) : Conv unit :=
    match rop with | Rop _ _ rd _ =>
      lo <- get_lo;
      set_reg lo rd
    end.
  Definition conv_LUI (iop:ioperand) : Conv unit :=
    match iop with | Iop _ rt i =>
      pi <- load_int i;
      a1 <- cast_u size32 pi;
      p16 <- load_Z size32 16;
      a1s <- arith shl_op a1 p16;
      set_reg a1s rt
    end.
  (*-----Logical Ops-------*)
  Definition conv_log (op1: bit_vector_op) (rop: roperand) : Conv unit :=
    match rop with
      | Rop rs rt rd _ =>
        a1 <- load_reg rs;
        a2 <- load_reg rt;
        a3 <- arith op1 a1 a2;
        set_reg a3 rd
    end.
  Definition conv_AND := conv_log and_op.
  Definition conv_OR := conv_log or_op.
  Definition conv_XOR := conv_log xor_op.
  Definition conv_NOR (rop: roperand) : Conv unit :=
    match rop with | Rop rs rt rd _ => 
      a1 <- load_reg rs;
      a2 <- load_reg rt;
      v_or <- arith or_op a1 a2;
      v_nor <- not v_or;
      set_reg v_nor rd
    end.

  Definition conv_logi (op1: bit_vector_op) (iop:ioperand): Conv unit :=
    match iop with
      | Iop rs rt i =>
        a1 <- load_reg rs;
        pi <- load_int i;
        a2 <- cast_u size32 pi;
        a3 <- arith op1 a1 a2;
        set_reg a3 rt
    end.
  Definition conv_ANDI := conv_logi and_op.
  Definition conv_ORI := conv_logi or_op.
  Definition conv_XORI := conv_logi xor_op.

  Definition conv_sh (op1: bit_vector_op) (rop: roperand) : Conv unit :=
    match rop with | Rop _ rt rd sa =>
      a1 <- load_reg rt;
      si <- load_int sa;
      a2 <- cast_u size32 si;
      a1s <- arith op1 a1 a2;
      set_reg a1s rd
    end.
  Definition conv_SLL := conv_sh shl_op.
  Definition conv_SRA := conv_sh shr_op.
  Definition conv_SRL := conv_sh shru_op.

  Definition conv_shv (op1: bit_vector_op) (rop: roperand) : Conv unit :=
    match rop with | Rop rs rt rd _ =>
      a1 <- load_reg rt;
      a2 <- load_reg rs;
      shamt5 <- cast_u 4 a2;
      shamt <- cast_u size32 shamt5;
      a3 <- arith op1 a1 shamt;
      set_reg a3 rd
    end.
  Definition conv_SLLV := conv_shv shl_op.
  Definition conv_SRAV := conv_shv shru_op.
  Definition conv_SRLV := conv_shv shr_op.

  Definition conv_set (op1:test_op) (rop: roperand) : Conv unit :=
    match rop with | Rop rs rt rd _ =>
      pone <- load_Z size32 1;
      pzero <- load_Z size32 0;
      a1 <- load_reg rs;
      a2 <- load_reg rt;
      cond <- test op1 a1 a2;
      v_rd <- copy_ps pzero;
      emit (if_rtl cond (cast_u_rtl pone v_rd));;
      set_reg v_rd rd
    end.
      
  Definition conv_SLT := conv_set lt_op.
  Definition conv_SLTU := conv_set ltu_op.


  Definition conv_seti caster (op1:test_op) (iop: ioperand) : Conv unit :=
    match iop with | Iop rs rt i =>
      pone <- load_Z size32 1;
      pzero <- load_Z size32 0;
      a1 <- load_reg rs;
      a2 <- load_int i;
      a2c <- caster a2;
      cond <- test op1 a1 a2c;
      v_rd <- copy_ps pzero;
      emit (if_rtl cond (cast_u_rtl pone v_rd));;
      set_reg v_rd rt
    end.
  Definition conv_SLTI := conv_seti (cast_s size32) (lt_op).
  Definition conv_SLTIU := conv_seti (cast_u size32) (ltu_op).
      

  Definition conv_SEB (rop:roperand) : Conv unit :=
    match rop with | Rop _ rt rd _ =>
      a1 <- load_reg rt;
      a1b <- cast_u size8 a1;
      a1bc <- cast_s size32 a1b;
      set_reg a1bc rd
    end.
  Definition conv_SEH (rop:roperand) : Conv unit :=
    match rop with | Rop _ rt rd _ =>
      a1 <- load_reg rt;
      a1h <- cast_u size16 a1;
      a1hc <- cast_s size32 a1h;
      set_reg a1hc rd
    end.

  (*--------------------*)
  (* Memory Ops         *)
  (*--------------------*)

  Definition testparity (p:Z) (v:pseudo_reg size32) : Conv (pseudo_reg size1) :=
    pval <- load_Z size32 p;
    rem <- arith modu_op v pval;
    pzero <- load_Z size32 0;
    test eq_op rem pzero.

  Definition conv_L_tlc s
    (tester:pseudo_reg size32 -> Conv (pseudo_reg size1))
    (loader:pseudo_reg size32 -> Conv (pseudo_reg s))
    (caster:pseudo_reg s -> Conv (pseudo_reg size32))
      (iop: ioperand) : Conv unit :=
    match iop with
      | Iop rs rt i =>
        addr <- compute_addr rs i;
        addrgood <- tester addr;
        addrerrorf <- bnot addrgood;
        emit (if_rtl addrerrorf error_rtl);;
        membyte <- loader addr;
        m_extend <- caster membyte;
        set_reg m_extend rt
    end.

  Definition conv_LB (iop:ioperand) := 
    conv_L_tlc (testparity 1) (load_mem8) (cast_s size32) iop.
  Definition conv_LBU (iop:ioperand) := 
    conv_L_tlc (testparity 1) (load_mem8) (cast_u size32) iop.
  
  Definition conv_LH (iop:ioperand) := 
    conv_L_tlc (testparity 2) (load_mem16) (cast_s size32) iop.
  Definition conv_LHU (iop:ioperand) := 
    conv_L_tlc (testparity 2) (load_mem16) (cast_u size32) iop.
  
  Definition conv_LW (iop:ioperand) := 
    conv_L_tlc (testparity 4) (load_mem32) (cast_u size32) iop.
  
  Definition conv_S_tlc s
    (tester:pseudo_reg size32 -> Conv (pseudo_reg size1))
    (saver:pseudo_reg s -> pseudo_reg size32 -> Conv unit)
    (caster:pseudo_reg size32 -> Conv (pseudo_reg s))
      (iop: ioperand) : Conv unit :=
    match iop with
      | Iop rs rt i =>
        addr <- compute_addr rs i;
        addrgood <- tester addr;
        addrerrorf <- bnot addrgood;
        emit (if_rtl addrerrorf error_rtl);;

        rval <- load_reg rt;
        rvalc <- caster rval;
        saver rvalc addr
    end.


  Definition conv_SB (iop:ioperand) := 
    conv_S_tlc (testparity 1) (@set_mem8) (cast_u size8) iop.
  Definition conv_SH (iop:ioperand) := 
    conv_S_tlc (testparity 2) (@set_mem16) (cast_u size16) iop.
  Definition conv_SW (iop:ioperand) := 
    conv_S_tlc (testparity 4) (@set_mem32) (cast_u size32) iop.
  (*--------------------*)
  (* Control Flow Ops   *)
  (*--------------------*)


  (*Shift and cast ints into the actual memory offset*)
  Definition int2moffset_u s (i: int s) : Conv (pseudo_reg size32) :=
    ibits <- load_int i;
    ioffset <- cast_u size32 ibits;
    ptwo <- load_Z size32 2;
    ishifted <- arith shl_op ioffset ptwo;
    ret ishifted.
    
  Definition int2moffset_s s (i: int s) : Conv (pseudo_reg size32) :=
    ibits <- load_int i;
    ioffset <- cast_s size32 ibits;
    ptwo <- load_Z size32 2;
    ishifted <- arith shl_op ioffset ptwo;
    ret ishifted.
    
  (*pc is incremented before execution*)
  (*pc isn't actually set until next step, so we set the branch delay state of the machine here*)
  Definition conv_Jl (linkflag: bool) (jop: joperand) : Conv unit :=
    match jop with
      | Jop i =>
        curpc <- get_pc;
        pcmask <- onemaskl size32 4;
        pcmasked <- arith and_op curpc pcmask;
        ioffset <- int2moffset_u i;
        newpc <- arith or_op pcmasked ioffset;
        match (linkflag) with
          | false => 
            set_bdelay newpc
          | true => 
            pfour <- load_Z size32 4;
            pc4 <- arith add_op curpc pfour;
            set_reg pc4 (Reg 31);;
            set_bdelay newpc
        end
    end.

  Definition conv_J (jop: joperand) : Conv unit := conv_Jl false jop.
  Definition conv_JAL (jop: joperand) : Conv unit := conv_Jl true jop.
  
  Definition conv_JRl (linkflag: bool) (rop:roperand) : Conv unit :=
    match rop with | Rop rs _ rd _ =>
      if (register_eq_dec rs rd) then (emit error_rtl) else(
        curpc <- get_pc;
        newpc <- load_reg rs;
        match (linkflag) with
          |true =>
            pfour <- load_Z size32 4;
            retpc <- arith add_op curpc pfour;
            set_reg retpc rd;;
            set_bdelay newpc
          |false=>
            set_bdelay newpc
        end
      )
    end.
  Definition conv_JALR (rop:roperand) : Conv unit := conv_JRl true rop.
  Definition conv_JR (rop:roperand) : Conv unit := conv_JRl false rop.

  Definition b_getnewpc s (i: int s) : Conv (pseudo_reg size32) :=
    curpc <- get_pc;
    ioffset <- int2moffset_s i;
    arith add_op curpc ioffset
  .
  Inductive condition2 : Set :=
  | Eq_cond : condition2
  | Ne_cond : condition2
    .
  Inductive condition1 : Set :=
  | Gez_cond : condition1
  | Gtz_cond : condition1
  | Lez_cond : condition1
  | Ltz_cond : condition1
    .
  Definition conv_cond1 s (c:condition1) (a:pseudo_reg s) : Conv (pseudo_reg size1) :=
    pzero <- load_Z s 0%Z;
    match c with
      | Gez_cond => 
        condf1 <- test lt_op pzero a;
        condf2 <- test eq_op pzero a;
        arith or_op condf1 condf2
      | Gtz_cond =>
        test lt_op pzero a
      | Lez_cond =>
        condf1 <- test lt_op a pzero;
        condf2 <- test eq_op a pzero;
        arith or_op condf1 condf2
      | Ltz_cond =>
        test lt_op a pzero
    end.
  Definition conv_cond2 s (c:condition2) (a1:pseudo_reg s) (a2:pseudo_reg s) :
    Conv (pseudo_reg size1) :=
    match c with
      | Eq_cond => test eq_op a1 a2
      | Ne_cond => condf1 <- test eq_op a1 a2; bnot condf1
    end.

  (*Two argument comparison branches*)
  Definition conv_Bcond2 (c:condition2) (iop:ioperand) : Conv unit :=
    match iop with | Iop rs rt i =>
      newpc <- b_getnewpc i;
      a1 <- load_reg rs;
      a2 <- load_reg rt;
      condf <- conv_cond2 c a1 a2;
      set_bdelay_cond condf newpc
    end.
  Definition conv_BEQ (iop:ioperand) : Conv unit := conv_Bcond2 Eq_cond iop.
  Definition conv_BNE (iop:ioperand) : Conv unit := conv_Bcond2 Ne_cond iop.

  (*Single argument comparison branches*)
  Definition conv_Bcond1 (c:condition1) (iop:ioperand) : Conv unit :=
    match iop with | Iop rs _ i =>
      newpc <- b_getnewpc i;
      a1 <- load_reg rs;
      condf <- conv_cond1 c a1;
      set_bdelay_cond condf newpc
    end.

  Definition conv_Bcondl1 (c:condition1) (iop:ioperand) : Conv unit :=
    match iop with | Iop rs _ i =>
      curpc <- get_pc;
      pfour <- load_Z size32 4;
      retpc <- arith add_op curpc pfour;
      set_reg retpc (Reg 31);;
      newpc <- b_getnewpc i;
      a1 <- load_reg rs;
      condf <- conv_cond1 c a1;
      set_bdelay_cond condf newpc
    end.
  Definition conv_BGEZ (iop:ioperand) : Conv unit := conv_Bcond1 Gez_cond iop.
  Definition conv_BGEZAL := conv_Bcondl1 Gez_cond.
  Definition conv_BGTZ (iop:ioperand) : Conv unit := conv_Bcond1 Gtz_cond iop.
  Definition conv_BLEZ (iop:ioperand) : Conv unit := conv_Bcond1 Lez_cond iop.
  Definition conv_BLTZ (iop:ioperand) : Conv unit := conv_Bcond1 Ltz_cond iop.
  Definition conv_BLTZAL := conv_Bcondl1 Ltz_cond.
  (*---------End specific instruction implementations--------------*)

  (*Predicate to distinguish between control flow and noncflow instructions*)
  Definition iscflow (i:instr ) : bool:=
    match i with
      | BEQ _ | BGEZ _ | BGTZ _ | BLEZ _ | BLTZ _ | BNE _  => true
      | J _ | JAL _ | JALR _ | JR _ => true
      | _  => false
    end.

  Definition incr_pc : Conv unit :=
    pwsize <- load_Z size32 (4%Z);
    curpc <- get_pc;
    newpc <- arith add_op curpc pwsize;
    set_pc newpc
    .
    
  (*Main translation function*)
  Definition instr_to_rtl (i: instr) :=
    runConv (
      (*Increment the PC before executing any instruction.*)
      incr_pc;;
      (*Different preprocessing behaviors are needed to deal with branch delayed instructions*)
      match (iscflow i) with
        | true => bd_prologue_cf
        | false => bd_prologue
      end;;
      match i with
        | ADD rop => conv_ADD rop
        | ADDI iop => conv_ADDI iop
        | ADDIU iop => conv_ADDIU iop
        | ADDU rop => conv_ADDU rop
        | AND rop => conv_AND rop
        | ANDI iop => conv_ANDI iop
        | BEQ iop => conv_BEQ iop
        | BGEZ iop => conv_BGEZ iop
        | BGEZAL iop => conv_BGEZAL iop
        | BGTZ iop => conv_BGTZ iop
        | BLEZ iop => conv_BLEZ iop
        | BLTZ iop => conv_BLTZ iop
        | BLTZAL iop => conv_BLTZAL iop
        | BNE iop => conv_BNE iop
        | DIV rop => conv_DIV rop
        | DIVU rop => conv_DIVU rop
        | J jop => conv_J jop
        | JAL jop => conv_J jop
        | JALR rop => conv_JALR rop
        | JR rop => conv_JR rop
        | LB iop => conv_LB iop
        | LBU iop => conv_LBU iop
        | LH iop => conv_LH iop
        | LHU iop => conv_LHU iop
        | LUI iop => conv_LUI iop
        | LW iop => conv_LW iop
        | MFHI rop => conv_MFHI rop
        | MFLO rop => conv_MFLO rop
        | MUL rop => conv_MUL rop
        | MULT rop => conv_MULT rop
        | MULTU rop => conv_MULTU rop
        | NOR rop => conv_NOR rop
        | OR rop => conv_OR rop
        | ORI iop => conv_ORI iop
        | SB iop => conv_SB iop
        | SEB rop => conv_SEB rop
        | SEH rop => conv_SEH rop
        | SH iop => conv_SH iop
        | SLL rop => conv_SLL rop
        | SLLV rop => conv_SLLV rop
        | SLT rop => conv_SLT rop
        | SLTI iop => conv_SLTI iop
        | SLTIU iop => conv_SLTIU iop
        | SLTU rop => conv_SLTU rop
        | SRA rop => conv_SRA rop
        | SRAV rop => conv_SRAV rop
        | SRL rop => conv_SRL rop
        | SRLV rop => conv_SRLV rop
        | SUB rop => conv_SUB rop
        | SUBU rop => conv_SUBU rop
        | SW iop => conv_SW iop
        | XOR rop => conv_XOR rop
        | XORI iop => conv_XORI iop
      end
    ).

End MIPS_Decode.

Local Open Scope Z_scope.
Local Open Scope monad_scope.
Import MIPS_Decode.
Import MIPS_RTL.
Import MIPS_MACHINE.

Fixpoint RTL_step_list l :=
  match l with
    | nil => ret tt
    | i::l' => interp_rtl i;; RTL_step_list l'
  end.

Definition step_ins inst: RTL unit := 
  flush_env;;
  RTL_step_list (MIPS_Decode.instr_to_rtl inst)
.

