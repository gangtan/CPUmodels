(* Tests contributed by Konstantin Weitz *)
Require Import X86Semantics.
Import X86_RTL.
Import X86_Compile.
Import X86_MACHINE.
Require Import Maps.
Require Import Bits.
Require Import List.
Require Import Coq.PArith.BinPos.
Require Import Bool.
Import ListNotations.
Import PTree.
Import Pos.
Import BinNums.
Import Word.

Arguments Word.mone {_}.

(* Notation "# n" := (mkint _ n _)(at level 45). *)

Section InitState.
Variable eax ebx ecx : int32.

Definition empty_mem : AddrMap.t int8 := (Word.zero, PTree.empty _).
Definition empty_seg : fmap segment_register int32 := (fun seg => Word.zero).
Definition empty_flags : fmap flag int1 := fun f => Word.zero.
Definition init_pc : int32 := Word.zero.
Definition init_reg : fmap register int32 := 
  fun reg => match reg with 
               EAX => eax
             | EBX => ebx
             | ECX => ecx
             | _ => Word.zero end.

Definition empty_oracle : oracle.
  refine {|
    oracle_bits := (fun a b => Word.zero);
    oracle_offset := 0
  |}.
Defined.

Definition init_machine : core_state. 
  refine {|
    gp_regs := init_reg;
    seg_regs_starts := empty_seg;
    seg_regs_limits := (fun seg_reg => Word.mone);
    flags_reg := empty_flags;
    control_regs := (fun c => Word.zero);
    debug_regs :=  (fun d => Word.zero);
    pc_reg := init_pc
  |}.
Defined.

Definition empty_fpu_machine : fpu_state.
refine {|
  fpu_data_regs := (fun fpr => Word.zero);
  fpu_status := Word.zero;
  fpu_control := Word.zero;
  fpu_tags := (fun t => Word.zero);
  fpu_lastInstrPtr := Word.zero;
  fpu_lastDataPtr := Word.zero;
  fpu_lastOpcode := Word.zero
|}.
Defined.

Definition init_full_machine : mach_state.
  refine {|
   core := init_machine;
   fpu := empty_fpu_machine
  |}.
Defined.

Definition init_rtl_state : rtl_state.
  refine {|
    rtl_oracle := empty_oracle;
    rtl_env := empty_env;
    rtl_mach_state := init_full_machine;
    rtl_memory := empty_mem
  |}.
Defined.

Definition no_prefix : prefix := mkPrefix None None false false.

Definition run (i:instr) :=
  RTL_step_list (instr_to_rtl no_prefix i) init_rtl_state.

Definition gpr (s:@RTL_ans unit * rtl_state) :=
  gp_regs (core (rtl_mach_state (snd s))).

Definition flag (s:@RTL_ans unit * rtl_state) :=
  flags_reg (core (rtl_mach_state (snd s))).

End InitState.

Module Test_XOR.
  Definition i:instr := XOR true (Reg_op EAX) (Reg_op EBX).

  (* Compute (instr_to_rtl no_prefix i). *)
  (* Compute (gpr (run one zero zero i) EAX). *)

  (* PF should be zero since (gpr (run one zero zero i) EAX) is 1,
     which has an odd number of bits *)
  Example ex1: (flag (run one zero zero i) PF) = zero.
  Proof. reflexivity. Qed.

End Test_XOR.

Module Test_Add.
  Definition i:instr := ADD true (Reg_op EAX) (Reg_op EBX).

  (* Compute (gpr  (run one mone zero i) EAX). *)

  (* ZF should be one, since (gpr  (run one mone zero i) EAX)
     returns zero *)
  Example ex1: (flag (run one mone zero i) ZF) = one.
  Proof. reflexivity. Qed.

End Test_Add.

Module Test_Adc.
  Definition i:instr := 
    ADC true (Reg_op (EBX)) (Reg_op (ECX)).

  Example ex1: (gpr (run zero (repr 2146959366) (repr 2148007937) i) EBX)
              = repr 7.
  Proof. reflexivity. Qed.

End Test_Adc.

Module Test_Sbb.
  Definition i:instr := SBB true (Reg_op (EBX)) (Reg_op (ECX)).

  Example ex1: (gpr (run zero (repr 3221249032) (repr 3221249032) i) EBX)
              = repr 0.
  Proof. reflexivity. Qed.

  Example ex2: (flag (run zero (repr 3221249032) (repr 3221249032) i) ZF)
              = repr 1.
  Proof. reflexivity. Qed.

  Example ex3: (flag (run zero (repr 3221249032) (repr 3221249032) i) PF)
              = repr 1.
  Proof. reflexivity. Qed.

  Example ex4: (flag (run zero (repr 3221249032) (repr 3221249032) i) SF)
              = repr 0.
  Proof. reflexivity. Qed.

  Example ex5: (flag (run zero (repr 3221249032) (repr 3221249032) i) CF)
              = repr 0.
  Proof. reflexivity. Qed.

  (* this fails for now *)
  (* Example ex6: (flag (run zero (repr 2147483712) (repr 2147483648) i) OF) *)
  (*             = repr 0. *)
  (* Proof. reflexivity. Qed. *)

End Test_Sbb.

Module Test_Xadd.
  Definition i:instr := XADD true (Reg_op (EBX)) (Reg_op (ECX)).

  Example ex1: (flag (run zero (repr 1608135424) (repr 2759947009) i) OF)
              = repr 0.
  Proof. reflexivity. Qed.

  Example ex2: intval 31 (gpr (run zero (repr 1608135424) (repr 2759947009) i) EBX)
              = intval 31 (repr 73115137).
  Proof. reflexivity. Qed.

End Test_Xadd.

Module Test_Mul.
  Definition i:instr := MUL true (Reg_op (EBX)).

  Example ex1: (gpr (run (repr 2233468006) (repr 1546826500) zero i) EDX)
               =  (repr 804380396).
  Proof. reflexivity. Qed.

End Test_Mul.

Module Test_Imul.
  Definition i:instr := IMUL true (Reg_op (EBX)) (None) (None).

  Example ex1: (gpr (run (repr 633430437) (repr 2147483231) zero i) EDX)
               =  (repr 316715156).
  Proof. reflexivity. Qed.

  (* SF is undefined according to manual *)
  (* Example ex2: (flag (run (repr 633430437) (repr 2147483231) zero i) SF) *)
  (*              =  (repr 1). *)
  (* Proof. reflexivity. Qed. *)


End Test_Imul.

Module SubOverflow.
  Definition i:instr := SUB true (Reg_op EAX) (Reg_op EBX).

  (* the overflow flags is not set, even though the result overflowed to -3 *)
  Compute (gpr  (run (repr 2147483645) (repr 2147483648) zero i) EAX).
  Compute (flag (run (repr 2147483645) (repr 2147483648) zero i) OF).
End SubOverflow.

