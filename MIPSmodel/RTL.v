Require Import List.
Require Import Bits.
Require Import ZArith.
Require Import Parser.
Require Import String.
Require Import Monad.
Require Import Maps.
Require Import MIPSSyntax.
Require Import Eqdep.
Set Implicit Arguments.
Unset Automatic Introduction.

Definition size1 := 0.
Definition size4 := 3.
Definition size8 := 7.
Definition size16 := 15.
Definition size32 := 31.
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

  Inductive test_op : Set := eq_op | lt_op | ltu_op.

  Inductive pseudo_reg (s:nat) : Set := 
  | ps_reg : Z -> pseudo_reg s.

  Inductive rtl_instr : Set := 
  | arith_rtl : forall s (b:bit_vector_op)(r1 r2:pseudo_reg s)(rd:pseudo_reg s), rtl_instr
  | test_rtl : forall s (top:test_op)(r1 r2:pseudo_reg s)(rd:pseudo_reg size1), rtl_instr
  | if_rtl : pseudo_reg size1 -> rtl_instr -> rtl_instr
  | cast_s_rtl : forall s1 s2 (r1:pseudo_reg s1) (rd:pseudo_reg s2),  rtl_instr
  | cast_u_rtl : forall s1 s2 (r1:pseudo_reg s1) (rd:pseudo_reg s2),  rtl_instr
  | load_imm_rtl : forall s (i:int s) (rd:pseudo_reg s),  rtl_instr
  | set_loc_rtl : forall s (rs:pseudo_reg s) (l:location s), rtl_instr
  | get_loc_rtl : forall s (l:location s) (rd:pseudo_reg s), rtl_instr
  | set_byte_rtl: forall (rs:pseudo_reg size8)(addr:pseudo_reg size_addr), rtl_instr
  | get_byte_rtl: forall (addr:pseudo_reg size_addr)(rd:pseudo_reg size8), rtl_instr
  | choose_rtl : forall s (rd:pseudo_reg s), rtl_instr
  | error_rtl : rtl_instr
  | safe_fail_rtl : rtl_instr.

  (** Next, we give meaning to RTL instructions as transformers over an
      environment for pseudo-registers and a machine state. *)
  Definition pseudo_env := forall s, pseudo_reg s -> int s.
  Definition empty_env : pseudo_env := fun s _ => Word.zero.
  Definition eq_pseudo_reg s : forall (r1 r2:pseudo_reg s), {r1 = r2} + {r1 <> r2}.
    intros. destruct r1. destruct r2. destruct (Z_eq_dec z z0). subst. left. auto.
    right. intro. apply n. congruence.
  Defined.
  Definition update_env s (r:pseudo_reg s) (v:int s) (env:pseudo_env) : pseudo_env.
    intros s r v env s' r'.
    destruct (eq_nat_dec s s'). subst. destruct (eq_pseudo_reg r r'). subst. apply v.
    apply (env s' r').
    apply (env s' r').
  Defined.


  Record oracle := { 
    oracle_bits : forall s, Z -> int s ; 
    oracle_offset : Z
  }.

  Record rtl_state := { 
    rtl_oracle : oracle ; 
    rtl_env : pseudo_env ; 
    rtl_mach_state : mach_state ; 
    rtl_memory : AddrMap.t int8
  }. 

  Inductive RTL_ans(A:Type) : Type := 
  | Fail_ans : RTL_ans A
  | SafeFail_ans : RTL_ans A
  | Okay_ans : A -> RTL_ans A.

  Definition RTL(T:Type) := rtl_state -> (RTL_ans T * rtl_state).

  Instance RTL_monad : Monad RTL := { 
    Return := fun A (x:A) (rs:rtl_state) => (Okay_ans x, rs) ;
    Bind := fun A B (c:RTL A) (f:A -> RTL B) (rs:rtl_state) => 
      match c rs with
        | (Okay_ans v, rs') => f v rs'
        | (Fail_ans, rs') => (Fail_ans _, rs')
        | (SafeFail_ans, rs') => (SafeFail_ans _, rs')
      end
  }.
  intros ; apply Coqlib.extensionality. auto.
  intros ; apply Coqlib.extensionality. intros. destruct (c x) ; auto. destruct r ; auto.
  intros ; apply Coqlib.extensionality. intros. destruct (f x) ; auto.
    destruct r ; auto.
  Defined.

  Definition Fail T : RTL T := fun rs => (Fail_ans T,rs).
  Definition SafeFail T : RTL T := fun rs => (SafeFail_ans T,rs).

  Definition flush_env : RTL unit :=
    fun rs => (Okay_ans tt, {| rtl_oracle := rtl_oracle rs ; 
                           rtl_env := empty_env;
                           rtl_mach_state := rtl_mach_state rs ; 
                           rtl_memory := rtl_memory rs |}).
  Definition set_ps s (r:pseudo_reg s) (v:int s) : RTL unit := 
    fun rs => (Okay_ans tt, {| rtl_oracle := rtl_oracle rs ; 
                           rtl_env := update_env r v (rtl_env rs) ;
                           rtl_mach_state := rtl_mach_state rs ; 
                           rtl_memory := rtl_memory rs |}).
  Definition set_loc s (l:location s) (v:int s) : RTL unit := 
    fun rs => (Okay_ans tt, {| rtl_oracle := rtl_oracle rs ; 
                           rtl_env := rtl_env rs ; 
                           rtl_mach_state := set_location l v (rtl_mach_state rs) ; 
                           rtl_memory := rtl_memory rs |}).
  Definition set_byte (addr:int size_addr) (v:int size8) : RTL unit := 
    fun rs => (Okay_ans tt, {| rtl_oracle := rtl_oracle rs ; 
                           rtl_env := rtl_env rs ; 
                           rtl_mach_state := rtl_mach_state rs ;
                           rtl_memory := AddrMap.set addr v (rtl_memory rs) |}).
  Definition get_ps s (r:pseudo_reg s) : RTL (int s) := 
    fun rs => (Okay_ans (rtl_env rs r), rs).
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
             rtl_env := rtl_env rs ; 
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

  Local Open Scope monad_scope.

  Fixpoint interp_rtl (instr:rtl_instr) : RTL unit := 
    match instr with 
      | arith_rtl s b r1 r2 rd => 
        v1 <- get_ps r1 ; v2 <- get_ps r2 ; set_ps rd (interp_arith b v1 v2)
      | test_rtl s t r1 r2 rd => 
        v1 <- get_ps r1 ; v2 <- get_ps r2 ; set_ps rd (interp_test t v1 v2)
      | if_rtl r i => 
        v <- get_ps r ; if (Word.eq v Word.one) then interp_rtl i else ret tt
      | cast_s_rtl s1 s2 rs rd => 
        v <- get_ps rs ; 
        set_ps rd (Word.repr (Word.signed v))
      | cast_u_rtl s1 s2 rs rd => 
        v <- get_ps rs ; 
        set_ps rd (Word.repr (Word.unsigned v))
      | load_imm_rtl s i rd => set_ps rd i
      | set_loc_rtl s rs l => v <- get_ps rs ; set_loc l v
      | get_loc_rtl s l rd => v <- get_loc l ; set_ps rd v
      | set_byte_rtl rs addr => v <- get_ps rs ; a <- get_ps addr ; set_byte a v
      | get_byte_rtl addr rd => a <- get_ps addr ; v <- get_byte a ; set_ps rd v
      | choose_rtl s rd => v <- choose_bits s ; set_ps rd v
      | error_rtl => Fail unit
      | safe_fail_rtl => SafeFail unit
    end.

  (** We collect all of the information for an instruction into a record
      satisfying this interface. *)
  Record instruction := { 
    instr_assembly : string ;  (* for printing/debugging *)
    instr_rtl : list rtl_instr (* semantics as RTL instructions *)
  }.
End RTL.

