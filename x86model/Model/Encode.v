(* This file encodes Intel IA32 (x86) 32-bit instructions into 
 * their binary form. *)

Require Import X86Syntax.
Require Import String.
Require Import Coqlib.
Require Import Bits.
Require Import Ascii.
Require Import Monad.
Local Open Scope monad_scope.

(* an encoding monad *)
Definition Enc (T:Type) := option T.

Instance EncodingMonad : Monad Enc := { 
  Return := fun A x => Some x ; 
  Bind := fun A B c f => match c with | None => None | Some v => f v end 
}.
auto. destruct c ; auto. intros. destruct f ; auto.
Defined.

Definition invalid (T:Type) : Enc T := @None T.
Implicit Arguments invalid [T].


Inductive op_size : Set := OpSize8 | OpSize16 | OpSize32.

(* Recursive function that converts a string consisiting of 
 * 1's and 0's to list of booleans respresenting 1's and 0's. *)
Fixpoint s2bl (s:string) : list bool :=
  match s with
    | EmptyString => nil
    | String a s =>
      (if ascii_dec a "0"%char then false else true)::(s2bl s)
  end.


(* Recursive Definition converts a list of booleans representing 
 * 1's and 0's back to the string containing the vaulues.*)
Fixpoint lb2bits (lb : list bool) : string :=
  match lb with
    | nil => EmptyString
    | x :: m => 
      match x with
        | true => append "1" (lb2bits m)
        | false => append "0" (lb2bits m)
      end
  end.

(* testing if a signed 32-bit immediate can be represented in a byte;
   that is, if it's within [-128,127] *)
Definition repr_in_signed_byte (imm:int32) :=
  andb (Word.lt imm (Word.repr 128)) (Word.lt (Word.repr (-129)) imm).

(* Definition matches a register with a list of booleans that 
 * represents its bit encoding. *)
Definition enc_reg r : list bool :=
  match r with
    | EAX => s2bl "000"
    | ECX => s2bl "001"
    | EDX => s2bl "010"
    | EBX => s2bl "011"
    | ESP => s2bl "100"
    | EBP => s2bl "101"
    | ESI => s2bl "110"
    | EDI => s2bl "111"
  end.

(* Definition matches a debuging register to a list of 
 * booleans representing its bit encoding.*)
Definition enc_debug_reg dr : list bool :=
  match dr with
    | DR0 => s2bl "000"
    | DR1 => s2bl "001"
    | DR2 => s2bl "010"
    | DR3 => s2bl "011"
    | DR6 => s2bl "110"
    | DR7 => s2bl "111"
  end.

(* Definition matches a control register to a list of booleans 
 * that represents it bit encodings. *)
Definition enc_control_reg cr : list bool:=
  match cr with
    | CR0 => s2bl "000"
    | CR2 => s2bl "010"
    | CR3 => s2bl "011"
    | CR4 => s2bl "100"
  end.

(*Definition matches a segment register to its bit encoding 
 * when only 2 bits are needed. *)
Definition enc_sreg2 sr : Enc (list bool) :=
  match sr with
    | ES => ret (s2bl "00")
    | CS => ret (s2bl "01")
    | SS => ret (s2bl "10")
    | DS => ret (s2bl "11")
    | _ => invalid
  end.

(* Definition matches a segment register to its bit encoding
 * when 3 bits are needed. *)
Definition enc_sreg3 sr : list bool :=
  match sr with
    | ES => s2bl "000"
    | CS => s2bl "001"
    | SS => s2bl "010"
    | DS => s2bl "011"
    | FS => s2bl "100"
    | GS => s2bl "101"
  end.

(* Definitions matches a segment register to the register that shares 
 * the same 3 bit encoding. Used when a segment register needs to be 
 * encoded by the definition enc_modrm. *)
Definition sreg3_2_reg sr : register :=
  match sr with
    | ES => EAX
    | CS => ECX
    | SS => EDX
    | DS => EBX
    | FS => ESP
    | GS => EBP
  end.

(* Definition matches a condition type to a list of booleans 
 * representing its bit encoding.*)
Definition enc_condition_type ct : list bool :=
match ct with
| O_ct => s2bl "0000"(* overflow *)
| NO_ct => s2bl "0001" (* not overflow *)
| B_ct => s2bl "0010" (* below, not above or equal *)
| NB_ct => s2bl "0011" (* not below, above or equal *)
| E_ct => s2bl "0100" (* equal, zero *)
| NE_ct => s2bl "0101" (* not equal, not zero *)
| BE_ct => s2bl "0110" (* below or equal, not above *)
| NBE_ct => s2bl "0111" (* not below or equal, above *)
| S_ct => s2bl "1000" (* sign *)
| NS_ct => s2bl "1001" (* not sign *)
| P_ct => s2bl "1010" (* parity, parity even *)
| NP_ct => s2bl "1011" (* not parity, parity odd *)
| L_ct => s2bl "1100"  (* less than, not greater than or equal to *)
| NL_ct => s2bl "1101" (* not less than, greater than or equal to *)
| LE_ct => s2bl "1110" (* less than or equal to, not greater than *)
| NLE_ct => s2bl "1111"
end.

(* Definition encodes the scale in address operands as a list of 
 * booleans represents the bits*)
Definition enc_scale (sc: scale) :=
  match sc with
    | Scale1 => s2bl "00"
    | Scale2 => s2bl "01"
    | Scale4 => s2bl "10"
    | Scale8 => s2bl "11"
  end.

(* encoding an SIB byte *)
Definition enc_SIB (bs:register) (idxopt: option (scale * register)) :=
  match bs, idxopt with
    | ESP, None => ret (s2bl "00" ++ s2bl "100" ++ s2bl "100")
    | _, Some (sc,idx) =>
      match idx with
        | ESP => invalid
        | _ => ret (enc_scale sc ++ enc_reg idx ++ enc_reg bs)
      end
    | _, _ => invalid
  end.

(* Definition enc_SIB (sc:scale) (idx base: register) := *)
(*   enc_scale sc ++ enc_reg idx ++ enc_reg base. *)

(* converting a sz-bit integer to a list of bool of length n *)
Definition int_explode (sz:nat) (i:Word.int sz) (n:nat) : list bool :=
  let bs := Word.bits_of_Z (S sz) (Word.unsigned i) in
  let fix int_explode_aux (n:nat) :=
    match n with
      | O => nil
      | S m => bs (Z_of_nat m) :: int_explode_aux m
    end
    in int_explode_aux n.
Implicit Arguments int_explode [sz].

Definition enc_byte (sz:nat) (i:Word.int sz) : list bool :=
  int_explode i 8.
Implicit Arguments enc_byte [sz].

(* little endian encoding of half word *)
Definition enc_halfword (sz:nat) (i:Word.int sz) : list bool :=
  let b0 := Word.and (Word.shru i (Word.repr 8)) (Word.repr 255) in
  let b1 := Word.and i (Word.repr 255) in
  let hw := Word.or (Word.shl b1 (Word.repr 8)) b0 in
    int_explode hw 16.
Implicit Arguments enc_halfword [sz].

Definition enc_word (sz:nat) (i:Word.int sz) : list bool :=
  let b3 := Word.and i (Word.repr 255) in
  let b2 := Word.and (Word.shru i (Word.repr 8)) (Word.repr 255) in
  let b1 := Word.and (Word.shru i (Word.repr 16)) (Word.repr 255) in
  let b0 := Word.shru i (Word.repr 24) in
  let w1 := Word.shl b1 (Word.repr 8) in
  let w2 := Word.shl b2 (Word.repr 16) in
  let w3 := Word.shl b3 (Word.repr 24) in
  let hw := Word.or w3 (Word.or w2 (Word.or w1 b0)) in
    int_explode hw 32.
Implicit Arguments enc_word [sz].

(* encoding the modrm byte given the encoding of the reg field *)
Definition enc_modrm_gen (reg: list bool) (op2 : operand): Enc (list bool) := 
  match op2 with
    | Reg_op r2 => ret (s2bl "11" ++ reg ++ enc_reg r2)
    | Address_op {| addrDisp:=disp; addrBase:=None; addrIndex:=None |} =>
      ret (s2bl "00" ++ reg ++ s2bl "101" ++ enc_word disp)
    | Address_op {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=idxopt |} =>
      let enc_r_or_m :=
        match bs, idxopt with
          | ESP, _  (* special case: when base is ESP, need a SIB byte *)
          | _, Some _ =>
            l <- enc_SIB bs idxopt; ret (s2bl "100" ++ l)
          | _, None => ret (enc_reg bs)
        end in
        r_or_m <- enc_r_or_m;
        let enc_disp_idxopt := 
          if (repr_in_signed_byte disp) then
            ret (s2bl "01" ++ reg ++ r_or_m ++ enc_byte disp)
            else ret (s2bl "10" ++ reg ++ r_or_m ++ enc_word disp)
        in
        (* alternate encoding: even if disp can be in a byte, we can always
           use the encoding of disp32[reg] *)
        match bs with
          | EBP => (* when base is EBP, cannot use the 00 mod *)
            enc_disp_idxopt
          | _ => 
            if (Word.eq disp Word.zero) then ret (s2bl "00" ++ reg ++ r_or_m)
              else enc_disp_idxopt
        end
    | Address_op {| addrDisp:=disp; addrBase:=None; addrIndex:=Some(sc,idx) |} =>
      (* special case: disp32[index*scale] *)
      ret (s2bl "00" ++ reg ++ s2bl "100" ++
           enc_scale sc ++ enc_reg idx ++ s2bl "101" ++ enc_word disp)
    | _ => invalid
  end.

(* encoding two operands: op1, op2;
   op1 should always be a register operand; 
   instructions whose op1 is not a reg but op2 is a reg should call enc_modrm op2 op1 *)
Definition enc_modrm (op1 op2: operand): Enc (list bool) :=
   match op1 with
    | Reg_op r1 => enc_modrm_gen (enc_reg r1) op2
    | _ => invalid
  end.

(* similar to enc_modrm except that the reg field is fixed to a 
   particular bit pattern *)
Definition enc_modrm_2 (bs:string) op2 : Enc (list bool) :=
  enc_modrm_gen (s2bl bs) op2.

(* Definition encodes an immediate operand to a list of booleans 
 * representing the bits*)
Definition enc_imm (op_override w: bool) (i1 : int32) : list bool :=
  match op_override, w with
    | _, false => enc_byte i1
    | false, true => enc_word i1
    | true, true => enc_halfword i1
  end.

(* Definition encodes the w/s operand as a list of booleans representing its bit. *)
Definition enc_bit (b : bool) : list bool :=
  match b with 
    | true => s2bl "1"
    | false => s2bl "0"
  end.

(* the encoding of the directionality bit *)
Definition enc_dbit (d:bool) := d :: nil.

(* Definition handles logic and arithmetic instructions that share similar
   bit patterns depending on the operands of the instruction. 
   op1 is the destination *)
Definition enc_logic_or_arith 
  (lb1: string) (* first 5 bits for most cases *)
  (lb2 : string) (* when first 5 bits are 10000, lb2 is the extra opcode in
                    the reg field of the modrm byte *)
  (op_override :bool) (w: bool) (op1 op2 : operand) : Enc (list bool) :=
match op1, op2 with
  | Reg_op r1, Reg_op r2 => 
    (* alternate encoding: set the d bit 0 and call enc_modrm op2 op1 *)
    l1 <- enc_modrm op1 op2; 
    ret (s2bl lb1 ++ s2bl "0" ++ enc_dbit true ++ enc_bit w ++ l1)
  | Reg_op r1, Address_op a1 => 
    l1 <- enc_modrm op1 op2; 
    ret (s2bl lb1 ++ s2bl "0" ++ enc_dbit true ++ enc_bit w ++ l1)
  | Address_op a1, Reg_op r1 => 
    l1 <- enc_modrm op2 op1; 
    ret (s2bl lb1 ++  s2bl "0" ++ enc_dbit false ++ enc_bit w ++ l1)
  | Reg_op EAX, Imm_op i1 => 
    (* alternate encoding possible; see the case of _, Immop i1 *)
    ret (s2bl lb1 ++ s2bl "10" ++ enc_bit w ++ enc_imm op_override w i1)
  | _, Imm_op i1 =>
    match op_override, w with
      | _ , false => 
        l1 <- enc_modrm_2 lb2 op1;
        ret (s2bl "10000000" ++ l1 ++ enc_byte i1)
      | false, true => 
        (* alternate encoding: even if i1 can be in a byte, 
           we can encode it as imm32 *)
        l1 <- enc_modrm_2 lb2 op1;
        if (repr_in_signed_byte i1) then
          ret (s2bl "10000011" ++ l1 ++ enc_byte i1)
          else ret (s2bl "10000001" ++ l1 ++ enc_word i1)
      | true, true => 
        (* alternate encoding: even if i1 can be in a byte, 
           we can encode it as imm32 *)
        l1 <- enc_modrm_2 lb2 op1;
        if (repr_in_signed_byte i1) then
          ret (s2bl "10000011" ++ l1 ++ enc_byte i1)
          else ret (s2bl "10000001" ++ l1 ++ enc_halfword i1)
    end
  | _, _ => invalid
end.

(* Definition handles bit scan instructions. Returns list of booleans 
 * representing the bit pattern of the instruction. *)
Definition enc_BitScan (op1 op2 : operand) (lb : list bool) : Enc (list bool) :=
  match op1, op2 with 
    | Reg_op r1, Reg_op r2 => ret (lb ++ s2bl "11" ++ enc_reg r1 ++ enc_reg r2)
    | Address_op a1, Reg_op r1 => l1 <- enc_modrm op2 op1; ret (lb ++ l1)
    | _, _ => invalid
  end.

(* Definition handles bit test instructions. Returns list of booleans 
 * representing the bit pattern of the instruction. *)
Definition enc_bit_test (lb1 lb2 : string) 
  (op1 op2 : operand) : Enc (list bool) :=
  match op1, op2  with
    | _, Imm_op i1 =>
      l1 <- enc_modrm_2 lb1 op1;
      ret (s2bl "0000111110111010" ++ l1 ++ enc_imm false false i1)
    | _, _ => 
      l1 <- enc_modrm op2 op1; 
      ret (s2bl "00001111"  ++ s2bl "101" ++ s2bl lb2 ++ s2bl "011" ++ l1)
  end.

(* Definition handles divide and multiply instructions. Returns list of booleans 
 * representing the bit pattern of the instruction. *)
Definition enc_div_mul (w : bool) (op1 : operand) (lb : string) : Enc (list bool) :=
  l1 <- enc_modrm_2 lb op1; 
  ret (s2bl "1111011" ++ enc_bit w ++ l1).

(* Definition handles shift and rotate instructions. Returns list of booleans 
 * representing the bit pattern of the instruction. *)
(* Since ri is not an optional operand the instance of the definition where r1 is 1 is treated as an immediate*)
Definition enc_Rotate (w:bool)(op1:operand)(ri:reg_or_immed) (r:register) : Enc (list bool) :=
  match ri with
   (* | Imm_ri (Word.int 1) => s2bl "1101000" ++ enc_bit w ++ enc_modrm (Reg_op r) op1*)
    | Reg_ri ECX => l1 <- enc_modrm (Reg_op r) op1; ret (s2bl "1101001" ++ enc_bit w ++ l1)
    | Imm_ri i1 => 
      l1 <- enc_modrm (Reg_op r) op1; 
      ret (s2bl "1100000" ++ enc_bit w ++ l1 ++ enc_byte i1)
    |  _ => invalid
  end.

(* Definition if passed a true returns a list containing a false bool, if passed false returns a list containing a true bool.*)
Definition enc_op_bool (same_segment : bool) : list bool :=
  match same_segment with
    | true => s2bl "0"
    | false => s2bl "1"
  end.


(******INSTRUCTION ENCODINGS START HERE*******)
(******INSTRUCTIONS LISTED IN ALPHABETICAL ORDER******)

Definition enc_AAA := ret (s2bl "00110111").
Definition enc_AAD := ret (s2bl "1101010100001010").
Definition enc_AAM := ret (s2bl "1101010000001010").
Definition enc_AAS := ret (s2bl "00111111").
Definition enc_ADC := enc_logic_or_arith "00010" "010".
Definition enc_ADD := enc_logic_or_arith "00000" "000".
Definition enc_AND := enc_logic_or_arith "00100" "100".
Definition enc_ARPL (op1 op2 : operand) : Enc (list bool) :=
match op1, op2 with
| Reg_op r1, Reg_op r2 => ret (s2bl "0110001111" ++ enc_reg r1 ++ enc_reg r2)
| Reg_op r1, Address_op a1 => l1 <- enc_modrm op1 op2; ret (s2bl "01100011" ++ l1)
| _ , _ => invalid
end.


Definition enc_BOUND (op1 op2 : operand) : Enc (list bool) :=
   l1 <- enc_modrm op1 op2; ret (s2bl "01100010" ++ l1).
Definition enc_BSF (op1 op2 : operand) : Enc (list bool) :=
   enc_BitScan op1 op2 (s2bl "0000111110111100").
Definition enc_BSR (op1 op2 : operand) : Enc (list bool) :=
   enc_BitScan op1 op2 (s2bl "0000111110111101").
Definition enc_BSWAP (r : register) := ret (s2bl "0000111111001" ++ enc_reg r).
Definition enc_BT := enc_bit_test "100" "00".
Definition enc_BTC := enc_bit_test "111" "11".
Definition enc_BTR := enc_bit_test "110" "10".
Definition enc_BTS := enc_bit_test "101" "01".

Definition enc_CALL (near absolute : bool) (op1 : operand) (sel : option selector)
  : Enc (list bool) :=
  match near, absolute with
    | true, false => 
      match op1 with
        | Imm_op i1 => ret (s2bl "11101000" ++ enc_word i1)
        | _ => invalid
      end
    | true, true => 
      l1 <- enc_modrm_2 "010" op1; ret (s2bl "11111111" ++ l1)
    | false, true => 
      match sel, op1 with
        | Some sel, Imm_op i1 =>
          ret (s2bl "10011010" ++ enc_word i1 ++ enc_halfword sel)
        | None, _ => 
          l1 <- enc_modrm_2 "011" op1; ret (s2bl "11111111" ++ l1)      
        | _,_ => invalid
      end
    | false, false => invalid
  end.

Definition enc_CDQ := ret (s2bl "10011001").
Definition enc_CLC := ret (s2bl "11111000").
Definition enc_CLD := ret (s2bl "11111100").
Definition enc_CLI := ret (s2bl "11111010").
Definition enc_CLTS := ret (s2bl "0000111100000110").
Definition enc_CMC := ret (s2bl "11110101").
Definition enc_CMOVcc (ct:condition_type)(op1 op2: operand) : Enc (list bool) :=
  l1 <- enc_modrm op1 op2; ret (s2bl "000011110100" ++ enc_condition_type ct ++ l1).
Definition enc_CMP := enc_logic_or_arith "00111" "111".
Definition enc_CMPS (w : bool) := ret (s2bl "1010011" ++ enc_bit w).
Definition enc_CMPXCHG (w : bool) (op1 op2 : operand) : Enc (list bool) :=
  match op1, op2 with
    | Reg_op r1, Reg_op r2 => 
      ret (s2bl "000011111011000" ++ enc_bit w ++ s2bl "11" ++ enc_reg r2 ++ enc_reg r1) 
    | Address_op a1, Reg_op r1 => 
      l1 <- enc_modrm op2 op1; ret (s2bl "000011111011000" ++ enc_bit w ++ l1)
    | _, _ => invalid
  end.
Definition enc_CPUID := ret (s2bl "0000111110100010").
Definition enc_CWDE := ret (s2bl "10011000").


Definition enc_DAA := ret (s2bl "00101111"). 
Definition enc_DAS := ret (s2bl "00101111").
(*DEC has alternate coding for a register operand that is ommited for now*)
Definition enc_DEC (w : bool) (op1 : operand) : Enc (list bool) :=
  match op1 with
    | Reg_op r => 
      ret (s2bl "1111111" ++ enc_bit w ++ s2bl "11001" ++ enc_reg r) (* There is an alternate encoding for a register operand for this instruction *)
    | Address_op a1 => l1 <- enc_modrm (Reg_op ECX) op1; ret (s2bl "1111111" ++ enc_bit w ++ l1)
    | _ => invalid
  end.
Definition enc_DIV (w : bool) (op1 : operand) : Enc (list bool) := 
  enc_div_mul w op1 "110".

Definition enc_HLT := ret (s2bl "11110100").


Definition enc_IDIV (w : bool) (op1 : operand) : Enc (list bool) := 
  enc_div_mul w op1 "111".

Definition enc_IMUL (op_override:bool)
  (w:bool) (op1:operand) (opopt: option operand) (iopt:option int32)
  : Enc (list bool) :=
  match opopt, iopt with
    | None, None => 
      l1 <- enc_modrm_2 "101" op1; 
      ret (s2bl "1111011" ++ enc_bit w ++ l1)
    | Some op2, None =>
      l1 <- enc_modrm op1 op2; ret (s2bl "0000111110101111" ++ l1)
    | Some op2, Some imm3 =>
      (* alternate encoding: even if imm3 can be in a byte, 
         we can use the case of 32-bit immediates *)
      if (repr_in_signed_byte imm3) then 
        l1 <- enc_modrm op1 op2; 
        ret (s2bl "01101011" ++ l1 ++ enc_imm false false imm3)
      else
        l1 <- enc_modrm op1 op2; 
        ret (s2bl "01101001" ++ l1 ++ enc_imm op_override true imm3)
    | _ , _ => invalid
  end.

Definition enc_IN (w:bool)(p: option port_number) : Enc (list bool) :=
  match p with
    | None => ret (s2bl "1110110" ++ enc_bit w)
    | Some imm8 => ret (s2bl "1110010" ++ enc_bit w ++ enc_byte imm8)
  end.
(*INC has alternate coding for a register operand that I ommited for now*)
Definition enc_INC (w : bool) (op1 : operand) : Enc (list bool) :=
  match op1 with
    | Reg_op r => ret (s2bl "1111111" ++ enc_bit w ++ s2bl "11000" ++ enc_reg r) (* There is an alternate encoding for a register operand for this instruction *)
    | Address_op a1 => l1 <- enc_modrm (Reg_op EAX) op1; ret (s2bl "1111111" ++ enc_bit w ++ l1)
    | _ => invalid
  end.
Definition enc_INS (w : bool) := ret (s2bl "0110110" ++ enc_bit w).
Definition enc_INT := ret (s2bl "11001100").
Definition enc_INTn (it:interrupt_type) := ret (s2bl "11001101" ++ enc_byte it).
Definition enc_INTO := ret (s2bl "11001110").
Definition enc_INVD := ret (s2bl "0000111100001000").
Definition enc_INVLPG (op1:operand) : Enc (list bool) := 
  l1 <- enc_modrm (Reg_op EDI) op1; ret (s2bl "0000111100000001" ++ l1).
Definition enc_IRET := ret (s2bl "11001111").


Definition enc_Jcc (ct:condition_type) (disp:int32) :=
  ret (s2bl "000011111000" ++ enc_condition_type ct ++ enc_word disp).
Definition enc_JCXZ (b:int8) :=
  ret (s2bl "11100011" ++ enc_byte b).

Definition enc_JMP (near:bool)(absolute:bool)(op1: operand)(sel:option selector)
  : Enc (list bool) :=
  match near, absolute with
    | true, false => 
      match op1 with
        | Imm_op i1 => 
          if (repr_in_signed_byte i1) then
            (* alternate encoding: can always use the word case to encode i1 *)
            ret (s2bl "11101011" ++ enc_byte i1)
          else ret (s2bl "11101001" ++ enc_word i1)
        | _ => invalid
      end
    | true, true => 
      l1 <- enc_modrm_2 "100" op1; ret (s2bl "11111111" ++ l1)
    | false, true => 
      match sel, op1 with
        | Some sel, Imm_op i1 =>
          ret (s2bl "11101010" ++ enc_word i1 ++ enc_halfword sel)
        | None, _ => 
          l1 <- enc_modrm_2 "101" op1; ret (s2bl "11111111" ++ l1)      
        | _,_ => invalid
      end
    | false, false => invalid
  end.

Definition enc_LAHF := ret (s2bl "10011111").
Definition enc_LAR (op1 op2:operand) : Enc (list bool) := 
  l1 <- enc_modrm op1 op2; ret (s2bl "0000111100000010" ++ l1).
Definition enc_LDS (op1 op2:operand) : Enc (list bool) :=
  l1 <- enc_modrm op1 op2; ret (s2bl "11000101" ++ l1).
Definition enc_LEA (op1 op2:operand) : Enc (list bool) := 
  l1 <- enc_modrm op1 op2; ret (s2bl "10001101" ++ l1).
Definition enc_LEAVE := ret (s2bl "11001001").
Definition enc_LES (op1 op2:operand) : Enc (list bool) := 
  l1 <- enc_modrm op1 op2; ret (s2bl "11000100" ++ l1).
Definition enc_LFS (op1 op2:operand) : Enc (list bool) := 
  l1 <- enc_modrm op1 op2; ret (s2bl "000011110110100" ++ l1).
Definition enc_LGDT (op1:operand) : Enc (list bool) := 
  l1 <- enc_modrm (Reg_op EDX) op1; ret (s2bl "0000111100000001" ++ l1).
Definition enc_LGS (op1 op2:operand) : Enc (list bool) := 
  l1 <- enc_modrm op1 op2; ret (s2bl"0000111110110101" ++ l1).
Definition enc_LIDT (op1:operand) : Enc (list bool) := 
  l1 <- enc_modrm (Reg_op EBX) op1; ret (s2bl "0000111100000001" ++ l1).
Definition enc_LLDT (op1 : operand) : Enc (list bool) := 
  match op1 with
    | Reg_op r1 => ret (s2bl "000011110000000011010"  ++ enc_reg r1)
    | Address_op a1 => l1 <- enc_modrm (Reg_op EDX) op1; ret (s2bl "000011110000000" ++ l1)
    | _ => invalid
  end.
Definition enc_LMSW (op1 : operand) : Enc (list bool) := 
  match op1 with
    | Reg_op r1 => ret (s2bl "000011110000000111110"  ++ enc_reg r1)
    | Address_op a1 => l1 <- enc_modrm (Reg_op ESI) op1; ret (s2bl "000011110000001" ++ l1)
    | _ => invalid
  end.
Definition enc_LODS (w : bool) := ret (s2bl "1010110" ++ enc_bit w).
Definition enc_LOOP (disp:int8) := ret (s2bl "11100010" ++ enc_byte disp).
Definition enc_LOOPNZ (disp:int8) := ret (s2bl "11100000" ++ enc_byte disp).
Definition enc_LOOPZ (disp:int8) := ret (s2bl "11100001" ++ enc_byte disp).
Definition enc_LSL (op1 op2:operand) : Enc (list bool) :=
  l1 <- enc_modrm op1 op2; ret (s2bl "0000111100000011" ++ l1).
Definition enc_LSS (op1 op2:operand) : Enc (list bool) :=
  l1 <- enc_modrm op1 op2; ret (s2bl "0000111110110010" ++ l1).
Definition enc_LTR (op1 : operand) : Enc (list bool) := 
  match op1 with
    | Reg_op r1 => ret (s2bl "000011110000000011011"  ++ enc_reg r1)
    | Address_op a1 => l1 <- enc_modrm (Reg_op EBX) op1; ret (s2bl "000011110000000" ++ l1)
    | _ => invalid
  end.

Definition enc_MOV (op_override w:bool) (op1 op2:operand) : Enc (list bool) := 
  match op1, op2 with
    | Reg_op _, Reg_op _ => 
      (* alternate encoding: set the d bit and reverse op1 and op2*)
      l1 <- enc_modrm op2 op1; ret (s2bl "1000100" ++ enc_bit w ++ l1)
    | Reg_op _, Address_op _ => 
      l1 <- enc_modrm op1 op2; ret (s2bl "1000101" ++ enc_bit w ++ l1)
    | Reg_op r1, Imm_op i1 => 
      (* alternate encoding: C6/C7 /0 *)
      ret (s2bl "1011" ++ enc_bit w ++ enc_reg r1 ++ enc_imm op_override w i1)
    | Reg_op EAX, Offset_op o1 => 
      ret (s2bl "1010000" ++ enc_bit w ++ enc_word o1)
    | Address_op _, Reg_op _ => 
      l1 <- enc_modrm op2 op1; ret (s2bl "1000100" ++ enc_bit w ++ l1)
    | Offset_op o1, Reg_op EAX => 
      ret (s2bl "1010001" ++ enc_bit w ++ enc_word o1)
    | Address_op a1, Imm_op i1 => 
      l1 <- enc_modrm_2 "000" op1; 
      ret (s2bl "1100011" ++ enc_bit w ++ l1 ++ enc_imm op_override w i1)
    | _, _ => invalid
  end.


Definition enc_MOVBE (op1 op2:operand) : Enc (list bool) :=  
  match op1, op2 with
    | Reg_op r1, Address_op a2 => l1 <- enc_modrm op1 op2; ret (s2bl "000011110011100011110000" ++ l1)
    | Address_op a1, Reg_op r2 => l1 <- enc_modrm op2 op1; ret (s2bl "000011110011100011110001" ++ l1)
    | _,_ => invalid
  end.
Definition enc_MOVCR (direction:bool)(cr:control_register)(r:register) := 
  ret (s2bl "00001111001000" ++ enc_bit direction ++ s2bl "011" ++ enc_control_reg cr ++ enc_reg r).
Definition enc_MOVDR (direction:bool)(dr:debug_register)(r:register) :=
  ret (s2bl "00001111001000" ++ enc_bit direction ++ s2bl "111" ++ enc_debug_reg dr ++ enc_reg r).
Definition enc_MOVS (w : bool) := ret (s2bl "1010010" ++ enc_bit w).
Definition enc_MOVSR (direction:bool)(sr:segment_register)(op1:operand) : Enc (list bool) := 
  l1 <- enc_modrm (Reg_op (sreg3_2_reg sr)) op1; 
  ret (s2bl "100011" ++ enc_bit direction ++ s2bl "0"  ++ l1).
Definition enc_MOVSX (w:bool)(op1 op2:operand) : Enc (list bool) := 
  l1 <- enc_modrm op1 op2; ret (s2bl "000011111011111" ++ enc_bit w ++ l1).
Definition enc_MOVZX (w:bool)(op1 op2:operand) : Enc (list bool) :=
  l1 <- enc_modrm op1 op2; ret (s2bl "000011111011011" ++ enc_bit w ++ l1).  
Definition enc_MUL (w : bool) (op1 : operand) : Enc (list bool) := 
  enc_div_mul w op1 "100".


Definition enc_NEG (w:bool)(op:operand) : Enc (list bool) := 
  l1 <- enc_modrm (Reg_op EBX) op;
  ret (s2bl "1111011" ++ enc_bit w ++ l1).
Definition enc_NOP (op_opt: option operand) : Enc (list bool) :=
  match op_opt with
    | None => ret (s2bl "10010000")
    | Some op_opt => l1 <- enc_modrm (Reg_op EAX) op_opt; ret (s2bl "0000111100011111" ++ l1)
  end.
Definition enc_NOT (w:bool)(op:operand) : Enc (list bool) := 
  l1 <- enc_modrm (Reg_op EDX) op; ret (s2bl "1111011" ++ enc_bit w ++ l1).


Definition enc_OR := enc_logic_or_arith "00001" "001".

Definition enc_OUT (w:bool)(p:option port_number) : Enc (list bool) :=
  match p with
    | None => ret (s2bl "1110111" ++ enc_bit w)
    | Some p => ret (s2bl "1110011" ++ enc_bit w ++ enc_byte p)
  end.
Definition enc_OUTS (w : bool) := ret (s2bl "0110111" ++ enc_bit w).


Definition enc_POP (op1:operand) : Enc (list bool) := 
  match op1 with
    | Reg_op r1 => 
      (* alternate encoding: "8F /0"   pop r/m32 *)
      ret (s2bl "01011" ++ enc_reg r1)
    | _ => 
      l1 <- enc_modrm_2 "000" op1; ret (s2bl "10001111" ++ l1)
  end. 
Definition enc_POPA := ret (s2bl "01100001").
Definition enc_POPF := ret (s2bl "10011101").
Definition enc_POPSR (sr:segment_register) : Enc (list bool) := 
  match sr with
    | DS => ret (s2bl "00011111")
    | ES => ret (s2bl "00000111")
    | SS => ret (s2bl "00010111")
    | FS => ret (s2bl "0000111110100001")
    | GS => ret (s2bl "0000111110101001")
    | _ => invalid
  end.
Definition enc_PUSH (w:bool)(op1:operand) : Enc (list bool) :=
  match w with
    | true =>
      match op1 with 
        | Reg_op r1 => 
          (* alternate encoding: "FF /6" PUSH r/m16 *)
          ret (s2bl "01010" ++ enc_reg r1)
        | Address_op a1 => 
          l1 <- enc_modrm_2 "110" op1; ret (s2bl "11111111"  ++ l1)
        | Imm_op i1 => 
          ret (s2bl "01101000" ++ enc_imm false true i1)
        | _ => invalid
      end
    | false => 
      match op1 with 
        | Imm_op i1 => ret (s2bl "01101010" ++ enc_imm false false i1)
        | _ => invalid
      end
  end.
Definition enc_PUSHA := ret (s2bl "10011101").
Definition enc_PUSHF := ret (s2bl "10011101").
Definition enc_PUSHSR (sr:segment_register) :=
  match sr with
    | CS => ret (s2bl "00001110")
    | DS => ret (s2bl "00011110")
    | ES => ret (s2bl "00000110")
    | SS => ret (s2bl "00010110")
    | FS => ret (s2bl "0000111110100000")
    | GS => ret (s2bl "0000111110101000")
  end.


Definition enc_RCL (w:bool) (op1:operand) (ri: reg_or_immed) : Enc (list bool) :=
  enc_Rotate w op1 ri EDX.
Definition enc_RCR (w:bool)(op1:operand)(ri:reg_or_immed) : Enc (list bool) :=
  enc_Rotate w op1 ri EBX.
Definition enc_RDMSR  := ret (s2bl "0000111100110010").
Definition enc_RDPMC  := ret (s2bl "0000111100110011").
Definition enc_RDTSC  := ret (s2bl "0000111100110001").
Definition enc_RDTSCP := ret (s2bl "000011110000000111111001").
Definition enc_RET (same_segment:bool)(disp:option int16) :=
  match disp with
    | None => ret (s2bl "1100" ++ enc_op_bool same_segment ++ s2bl "011")
    | Some disp => 
      ret (s2bl "1100" ++ enc_op_bool same_segment ++ s2bl "010" ++ enc_halfword disp)
  end.
Definition enc_ROL (w:bool)(op1:operand)(ri:reg_or_immed) : Enc (list bool) :=
  enc_Rotate w op1 ri EAX.
Definition enc_ROR (w:bool)(op1:operand)(ri:reg_or_immed) : Enc (list bool) :=
  enc_Rotate w op1 ri ECX.
Definition enc_RSM := ret (s2bl "0000111110101010").


Definition enc_SAHF := ret (s2bl "10011110").
Definition enc_SAR (w:bool)(op1:operand)(ri:reg_or_immed) : Enc (list bool) :=
  enc_Rotate w op1 ri EDI.
Definition enc_SBB := enc_logic_or_arith "00011" "011".
Definition enc_SCAS (w : bool) := ret (s2bl "1010111" ++ enc_bit w).
Definition enc_SETcc (ct:condition_type)(op1:operand) : Enc (list bool) :=
  l1 <- enc_modrm (Reg_op EAX) op1; ret (s2bl "000011111001" ++ enc_condition_type ct ++ l1).
Definition enc_SGDT (op1:operand) : Enc (list bool) := 
  l1 <- enc_modrm (Reg_op EAX) op1; ret (s2bl "0000111100000001" ++ l1).
Definition enc_SHL (w:bool)(op1:operand)(ri:reg_or_immed) : Enc (list bool) :=
  enc_Rotate w op1 ri ESP.
Definition enc_SHLD (op1:operand)(r:register)(ri:reg_or_immed) : Enc (list bool) :=
  match ri with
    | Imm_ri i1 => 
      l1 <- enc_modrm (Reg_op r) op1; ret (s2bl "0000111110100100" ++ l1 ++ enc_byte i1)
    | Reg_ri ECX => l1 <- enc_modrm (Reg_op r) op1; ret (s2bl "0000111110100101" ++ l1)
    | _ => invalid
  end.
Definition enc_SHR (w:bool)(op1:operand)(ri:reg_or_immed) : Enc (list bool) :=
  enc_Rotate w op1 ri EBP.
Definition enc_SHRD (op1:operand)(r:register)(ri:reg_or_immed) : Enc (list bool) :=
  match ri with
    | Imm_ri i1 => 
      l1 <- enc_modrm (Reg_op r) op1; ret (s2bl "0000111110101100" ++ l1 ++ enc_byte i1)
    | Reg_ri ECX => l1 <- enc_modrm (Reg_op r) op1; ret (s2bl "0000111110101101" ++ l1)
    | _ => invalid
  end.
Definition enc_SIDT (op1:operand) : Enc (list bool) := 
  l1 <- enc_modrm (Reg_op ECX) op1; ret (s2bl "0000111100000001" ++ l1).
Definition enc_SLDT (op1:operand) : Enc (list bool) := 
  l1 <- enc_modrm (Reg_op EAX) op1; ret (s2bl "0000111100000000" ++ l1).
Definition enc_SMSW (op1:operand) : Enc (list bool) := 
  l1 <- enc_modrm (Reg_op ESP) op1; ret (s2bl "0000111100000001" ++ l1).
Definition enc_STC := ret (s2bl "11111001").
Definition enc_STD := ret (s2bl "11111101").
Definition enc_STI := ret (s2bl "11111011").
Definition enc_STOS (w : bool) := ret (s2bl "1010101" ++ enc_bit w).
Definition enc_STR (op1:operand) : Enc (list bool) := 
  l1 <- enc_modrm (Reg_op ECX) op1; ret (s2bl "0000111100000000" ++ l1).
Definition enc_SUB := enc_logic_or_arith "00101" "101".

Definition enc_TEST (op_override w:bool)
  (op1 op2:operand) : Enc (list bool) :=
  match op1, op2 with
    | Reg_op EAX, Imm_op i
    | Imm_op i, Reg_op EAX =>
      ret (s2bl "1010100" ++ enc_bit w ++ enc_imm op_override w i)

    | op, Imm_op i
    | Imm_op i, op =>
      l1 <- enc_modrm_2 "000" op; 
      ret (s2bl "1111011" ++ enc_bit w ++ l1 ++ enc_imm op_override w i)

    | Reg_op r, op
    | op, Reg_op r =>
      l1 <- enc_modrm (Reg_op r) op; ret (s2bl "1000010"  ++ enc_bit w ++ l1)

    | _, _ => invalid
  end.

Definition enc_UD2 := ret (s2bl "0000FFFF00001011").

Definition enc_VERR (op1:operand) : Enc (list bool) :=
  l1 <- enc_modrm (Reg_op ESP) op1; ret (s2bl "0000111100000000" ++ l1).
Definition enc_VERW (op1:operand) : Enc (list bool) :=
  l1 <- enc_modrm (Reg_op EBP) op1; ret (s2bl "0000111100000000" ++ l1).


Definition enc_WBINVD := ret (s2bl "0000111100001001").
Definition enc_WRMSR := ret (s2bl "0000111100110000").


Definition enc_XADD (w:bool)(op1 op2:operand) : Enc (list bool) :=
  l1 <- enc_modrm op2 op1; ret (s2bl "000011111100000" ++ enc_bit w ++ l1).
Definition enc_XCHG (w:bool)(op1 op2:operand) : Enc (list bool) :=
  match op1, op2 with
    | Reg_op EAX, Reg_op r2 => ret (s2bl "10010" ++ enc_reg r2)
    | Reg_op r1, Reg_op EAX => ret (s2bl "10010" ++ enc_reg r1)
    | Reg_op r1, Reg_op r2 => 
      ret (s2bl "1000011" ++ enc_bit w ++ s2bl "11" ++ enc_reg r2 ++ enc_reg r1)
    | Reg_op r1, Address_op a2 => l1 <- enc_modrm op1 op2; ret (s2bl "1000011" ++ enc_bit w ++ l1)
    | Address_op a1, Reg_op r2 => l1 <- enc_modrm op2 op1; ret (s2bl "1000011" ++ enc_bit w ++ l1)
    |  _, _ => invalid
  end.
Definition enc_XLAT := ret (s2bl "11010111").
Definition enc_XOR := enc_logic_or_arith "00110" "110".


(******* Floating-point Definitions start here. *******)

(* Definition matches a floating-point register and returns a list of booleans that 
 * represents its bit encoding. *)
Definition enc_fpr r : list bool :=
  match r with
    | (ST0) => s2bl "000"
    | (ST1) => s2bl "001"
    | (ST2) => s2bl "010"
    | (ST3) => s2bl "011"
    | (ST4) => s2bl "100"
    | (ST5) => s2bl "101"
    | (ST6) => s2bl "110"
    | (ST7) => s2bl "111"
  end.

(* encoding the modrm byte for floating-point instructions, given the 3 bits for
   the opb field in the byte *)
Definition enc_fp_modrm (opb: list bool) (op2 : fp_operand) : Enc (list bool) :=
  match op2 with
    | FPS_op r2 => ret (s2bl "11" ++ opb ++ int_explode r2 3)

    | FPM32_op {| addrDisp:=disp; addrBase:=None; addrIndex:=None |}
    | FPM64_op {| addrDisp:=disp; addrBase:=None; addrIndex:=None |}
    | FPM80_op {| addrDisp:=disp; addrBase:=None; addrIndex:=None |} =>
      ret (s2bl "00" ++ opb ++ s2bl "101" ++ enc_word disp)

    | FPM32_op {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=idxopt |}
    | FPM64_op {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=idxopt |}
    | FPM80_op {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=idxopt |} =>
      let enc_r_or_m :=
        match bs, idxopt with
          | ESP, _  (* special case: when base is ESP, need a SIB byte *)
          | _, Some _ =>
            l <- enc_SIB bs idxopt; ret (s2bl "100" ++ l)
          | _, None => ret (enc_reg bs)
        end in
        r_or_m <- enc_r_or_m;
        let enc_disp_idxopt := 
          if (repr_in_signed_byte disp) then
            ret (s2bl "01" ++ opb ++ r_or_m ++ enc_byte disp)
            else ret (s2bl "10" ++ opb ++ r_or_m ++ enc_word disp)
        in
        (* alternate encoding: even if disp can be in a byte, we can always
           use the encoding of disp32[reg] *)
        match bs with
          | EBP => (* when base is EBP, cannot use the 00 mod *)
            enc_disp_idxopt
          | _ => 
            if (Word.eq disp Word.zero) then ret (s2bl "00" ++ opb ++ r_or_m)
              else enc_disp_idxopt
        end

    | FPM32_op {| addrDisp:=disp; addrBase:=None; addrIndex:=Some(sc,idx) |}
    | FPM64_op {| addrDisp:=disp; addrBase:=None; addrIndex:=Some(sc,idx) |}
    | FPM80_op {| addrDisp:=disp; addrBase:=None; addrIndex:=Some(sc,idx) |} =>
      (* special case: disp32[index*scale] *)
      ret (s2bl "00" ++ opb ++ s2bl "100" ++
           enc_scale sc ++ enc_reg idx ++ s2bl "101" ++ enc_word disp)

    (* | _ => invalid *)
  end.


(* A Helper function that deals with Instructions like FCOM, FCOMI, and others. Returns a 
list of booleans representing the bit pattern if the instruction is well formed. *)
Definition enc_comhelper (opb : list bool) (op2 : fp_operand) (lb : list bool) : Enc (list bool):=
  match op2 with
    | FPS_op i1 =>  ret (s2bl "110110001101" ++ lb  ++ int_explode i1 3)
    | FPM32_op fm1 => l1 <- enc_fp_modrm opb op2; ret (s2bl "11011000" ++ l1)
    | FPM64_op fm1 => l1 <- enc_fp_modrm opb op2; ret (s2bl "11011100" ++ l1)
    | _ => invalid
  end.

(* Definition encodes the floating-point register stack operands and returns the bit 
 pattern as a list of booleans.*) 
Definition enc_fp_int3 (op1 : fp_operand) : Enc (list bool) :=
  match op1 with
    | FPS_op i1 => ret (int_explode i1 3)
    | _ => invalid
  end.

(* Definition is a helper definition that encodes arithmetic instructions with two floating-point
   operands and returns their bit patterns represented as list booleans.
   In the case of "FPS_op i1, FPS_op i2", 
     * when m is true, then the sixth bit of the first byte should be
       the same as the fifth bit of the second byte.
     * when m is false, the two bits should be different.
 *)
Definition enc_fp_arith (m:bool) (lb opb: list bool)
  (op1 op2 : fp_operand) : Enc (list bool) :=
  match op1, op2 with 
    | FPS_op i1, FPS_op i2 => 
        if Word.eq i1 Word.zero then
          (* alternate encoding when i2 is also zero *)
          l1 <- enc_fp_int3 op2;
          let bm := if m then false else true in
            ret (s2bl "11011000" ++ s2bl "111" ++ lb ++ (bm :: l1))
        else if Word.eq i2 Word.zero then
          l1 <- enc_fp_int3 op1; 
          let bm := if m then true else false in
            ret (s2bl "11011100" ++ s2bl "111" ++ lb ++ (bm :: l1))
        else invalid
    | FPS_op i1, FPM32_op fa1 => 
        if Word.eq i1 Word.zero
          then l1 <- enc_fp_modrm opb op2; ret (s2bl "11011000" ++ l1)
          else invalid
    | FPS_op i1, FPM64_op fa1 => 
        if Word.eq i1 Word.zero 
          then l1 <- enc_fp_modrm opb op2; ret (s2bl "11011100" ++ l1)
          else invalid
    | _ , _ =>  invalid
  end.


(******* Floating-point Instructions ordered in ABC order *********)

(* 16-bit memory operands are also left out do to the fact that they are not properly
dealt with in the syntax yet.*)

(*
These few instructions commented here are not encoded due to the fact that they 
require operands that are not yet dealt with in the floating-point syntax.
| FSTENV : forall (op1: fp_operand), instr
| FSTSW : forall(op1: option fp_operand), instr
| FNSTCW : forall (op1: fp_operand), instr
 *)

Definition enc_F2XM1 := ret (s2bl "1101100111110000").
Definition enc_FABS := ret (s2bl "1101100111100001"). 
Definition enc_FADD (d: bool)(op1: fp_operand) : Enc (list bool) :=
  match op1 with 
    | FPS_op i1 =>
      ret (s2bl "11011"  ++ enc_bit d ++ s2bl "0011000"  ++ int_explode i1 3)
    | FPM32_op fm1 => 
      l1 <- enc_fp_modrm (s2bl "000") op1; ret (s2bl "11011000" ++ l1)
    | FPM64_op fm1 => 
      l1 <- enc_fp_modrm (s2bl "000") op1; ret (s2bl "11011100"  ++ l1)
    | _ => invalid
  end.

Definition enc_FADDP (op1: fp_operand) : Enc (list bool) := 
  l1 <- enc_fp_int3 op1; ret (s2bl "1101111011000" ++ l1).

Definition enc_FBLD (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "100") op1; ret (s2bl "11011111" ++ l1).
Definition enc_FBSTP (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "110") op1; ret (s2bl "11011111" ++ l1).
Definition enc_FCHS := ret (s2bl "1101100111100000"). 
Definition enc_FCLEX := ret (s2bl "1101101111100010").
Definition enc_FCOM (op1: option fp_operand) : Enc (list bool) :=
  match op1 with
    | Some fp1 => enc_comhelper (s2bl "010") fp1 (s2bl "0")
    | None => ret (s2bl "1101100011010001") 
  end.
Definition enc_FCOMP (op1: option fp_operand) : Enc (list bool) :=
  match op1 with
    | Some fp1 => enc_comhelper (s2bl "011") fp1 (s2bl "1")
    | None => ret (s2bl "1101100011011001")
  end.
Definition enc_FCOMPP := ret (s2bl "1101111011011001").
Definition enc_FCOMIP (op1: fp_operand) : Enc (list bool) := 
  l1 <- enc_fp_int3 op1; ret (s2bl "1101111111110" ++ l1).
Definition enc_FCOS := ret (s2bl "1101111011011001").
Definition enc_FDECSTP := ret (s2bl "1101111011011001").
Definition enc_FDIV := enc_fp_arith true (s2bl "1") (s2bl "110").
Definition enc_FDIVP (fp1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_int3 fp1; ret (s2bl "1101111011111" ++ l1).
Definition enc_FDIVR := enc_fp_arith false (s2bl "1") (s2bl "111").
Definition enc_FDIVRP (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_int3 op1; ret (s2bl "1101111011110" ++  l1).
Definition enc_FFREE (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_int3 op1; ret (s2bl "1101110111000" ++ l1).
Definition enc_FIADD (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "000") op1; ret (s2bl "11011010" ++ l1).
Definition enc_FICOM (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "010") op1; ret (s2bl "11011010" ++ l1).
Definition enc_FICOMP (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "011") op1; ret (s2bl "11011010" ++ l1).
Definition enc_FIDIV (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "110") op1; ret (s2bl "11011010" ++ l1).
Definition enc_FIDIVR (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "111") op1; ret (s2bl "11011010" ++ l1).
Definition enc_FILD (op1: fp_operand) : Enc (list bool) :=
  match op1 with
    | FPM32_op fp1 => 
      l1 <- enc_fp_modrm (s2bl "000") op1; ret (s2bl "11011011" ++ l1)
    | FPM64_op fp1 => 
      l1 <- enc_fp_modrm (s2bl "101") op1; ret (s2bl "11011111" ++ l1)
    | _ => invalid
  end.
Definition enc_FIMUL (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "001") op1; ret (s2bl "11011010" ++ l1).
Definition enc_FINCSTP := ret (s2bl "1101100111110111").
Definition enc_FINIT :=  ret (s2bl "100110111101101111100011").
Definition enc_FIST (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "010") op1; ret (s2bl "11011011" ++ l1).
Definition enc_FISTP (op1: fp_operand) : Enc (list bool) :=
  match op1 with
    | FPM32_op fp1 => 
      l1 <- enc_fp_modrm (s2bl "011") op1; ret (s2bl "11011011" ++ l1)
    | FPM64_op fp1 => 
      l1 <- enc_fp_modrm (s2bl "111") op1; ret (s2bl "11011111" ++ l1)
    | _ => invalid
  end.
Definition enc_FISUB (op1: fp_operand) : Enc (list bool) := 
  l1 <- enc_fp_modrm (s2bl "100") op1; ret (s2bl "11011010" ++ l1).
Definition enc_FISUBR (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "101") op1; ret (s2bl "11011010" ++ l1).
Definition enc_FLD (op1: fp_operand) : Enc (list bool) := 
  match op1 with 
    | FPS_op i1 =>  l1 <- enc_fp_int3 op1; ret (s2bl "1101100111000"  ++ l1)
    | FPM32_op fa1 => l1 <- enc_fp_modrm (s2bl "000") op1; ret (s2bl "11011001" ++ l1)
    | FPM64_op fa1 => l1 <- enc_fp_modrm (s2bl "000") op1; ret (s2bl "11011101" ++ l1)
    | FPM80_op fa1 => l1 <- enc_fp_modrm (s2bl "101") op1; ret (s2bl "11011011" ++ l1)
  end.
Definition enc_FLD1 := ret (s2bl "1101100111101000").
Definition enc_FLDCW (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "101") op1; ret (s2bl "11011001" ++ l1).
Definition enc_FLDENV (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "100") op1; ret (s2bl "11011001" ++ l1).
Definition enc_FLDL2E := ret (s2bl "1101100111101010").
Definition enc_FLDL2T := ret (s2bl "1101100111101001").
Definition enc_FLDLG2 := ret (s2bl "1101100111101100").
Definition enc_FLDLN2 := ret (s2bl "1101100111101101").
Definition enc_FLDPI := ret (s2bl "1101100111101011").
Definition enc_FLDZ := ret (s2bl "1101100111101110").
Definition enc_FMUL (d: bool) (op1: fp_operand) : Enc (list bool) :=
  match op1 with 
    | FPS_op i1 =>  
      l1 <- enc_fp_int3 op1; ret (s2bl "11011" ++ enc_bit d ++ s2bl "0011001"  ++ l1)
    | FPM32_op fa1 => 
      l1 <- enc_fp_modrm (s2bl "001") op1; ret (s2bl "11011000" ++ l1)
    | FPM64_op fa1 => 
      l1 <- enc_fp_modrm (s2bl "001") op1; ret (s2bl "11011100" ++ l1)
    | _ => invalid
  end.
Definition enc_FMULP (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_int3 op1; ret (s2bl "1101111011001" ++ l1).

Definition enc_FNSAVE (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "110") op1;
  ret (s2bl "11011101" ++ l1).
  
Definition enc_FNSTCW (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "111") op1;
  ret (s2bl "11011001" ++ l1).

Definition enc_FNOP := ret (s2bl "1101100111010000").
Definition enc_FPATAN := ret (s2bl "1101100111110011").
Definition enc_FPREM := ret (s2bl "1101100111111000").
Definition enc_FPREM1 := ret (s2bl "1101100111110101").
Definition enc_FPTAN := ret (s2bl "1101100111110010").
Definition enc_FRNDINT := ret (s2bl "1101100111111100").

Definition enc_FRSTOR (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "100") op1;
  ret (s2bl "11011101" ++ l1).

Definition enc_FSCALE := ret (s2bl "1101100111111101").
Definition enc_FSIN := ret (s2bl "1101100111111110").
Definition enc_FSINCOS := ret (s2bl "1101100111111011").
Definition enc_FSQRT := ret (s2bl "1101100111111010").
Definition enc_FST (op1: fp_operand) : Enc (list bool) :=
  match op1 with 
    | FPS_op i1 =>  l1 <- enc_fp_int3 op1; ret (s2bl "1101110111011"  ++ l1)
    | FPM32_op fa1 => l1 <- enc_fp_modrm (s2bl "010") op1; ret (s2bl "11011001" ++ l1)
    | FPM64_op fa1 => l1 <- enc_fp_modrm (s2bl "010") op1; ret (s2bl "11011101" ++ l1)
    | _ => invalid
  end.
Definition enc_FSTCW (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "111") op1; ret (s2bl "11011001" ++ l1).
Definition enc_FSTENV (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_modrm (s2bl "110") op1 ; ret (s2bl "11011001" ++ l1).
Definition enc_FSTP (op1: fp_operand) : Enc (list bool) :=
  match op1 with 
    | FPS_op fr1 =>  l1 <- enc_fp_int3 op1; ret (s2bl "1101110111011"  ++ l1)
    | FPM32_op fa1 => l1 <- enc_fp_modrm (s2bl "011") op1; ret (s2bl "11011001" ++ l1)
    | FPM64_op fa1 => l1 <- enc_fp_modrm (s2bl "011") op1; ret (s2bl "11011101" ++ l1)
    | FPM80_op fa1 => l1 <- enc_fp_modrm (s2bl "111") op1; ret (s2bl "11011011" ++ l1)
  end.
Definition enc_FSTSW (op1: option fp_operand) : Enc (list bool) :=
  match op1 with
    | None => ret (s2bl "1101111111100000")
    | Some op1 => l1 <- enc_fp_modrm (s2bl "111") op1; ret (s2bl "11011101" ++ l1)
  end.
Definition enc_FSUB := enc_fp_arith true (s2bl "0") (s2bl "100") .
Definition enc_FSUBP (op1 : fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_int3 op1; ret (s2bl "1101111011101" ++ l1).
Definition enc_FSUBR := enc_fp_arith false (s2bl "0") (s2bl "101").
Definition enc_FSUBRP (op1: (*option*) fp_operand) : Enc (list bool):=
   l1 <- enc_fp_int3 op1; ret (s2bl "1101111011100" ++ l1).
Definition enc_FTST := ret (s2bl "1101100111100100").
Definition enc_FUCOM (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_int3 op1; ret (s2bl "1101110111100" ++ l1).
Definition enc_FUCOMI (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_int3 op1; ret (s2bl "1101101111101"  ++ l1).
Definition enc_FUCOMIP (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_int3 op1; ret (s2bl "1101111111101" ++ l1).
Definition enc_FUCOMP (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_int3 op1; ret (s2bl "1101110111101" ++ l1).
Definition enc_FUCOMPP := ret (s2bl "1101101011101001").
Definition enc_FWAIT := ret (s2bl "10011011").
Definition enc_FXAM := ret (s2bl "1101100111100101").
Definition enc_FXCH (op1: fp_operand) : Enc (list bool) :=
  l1 <- enc_fp_int3 op1; ret (s2bl "1101100111001" ++ l1).
Definition enc_FXTRACT := ret (s2bl "1101100111110100").
Definition enc_FYL2X := ret (s2bl "1101100111110001").
Definition enc_FYL2XP1 := ret (s2bl "1101100111111001").

  (*MMX encodings *)

  Definition enc_mmx_modrm_gen (mmx_reg: list bool) (op2: mmx_operand) : Enc (list bool) := 
  match op2 with
    | MMX_Reg_op r2 => ret (s2bl "11" ++ mmx_reg ++ enc_fpr r2)
    | MMX_Addr_op {| addrDisp:=disp; addrBase:=None; addrIndex:=None |} =>
      ret (s2bl "00" ++ mmx_reg ++ s2bl "101" ++ enc_word disp)
    | MMX_Addr_op {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=idxopt |} =>
      let enc_r_or_m :=
        match bs, idxopt with
          | ESP, _  (* special case: when base is ESP, need a SIB byte *)
          | _, Some _ =>
            l <- enc_SIB bs idxopt; ret (s2bl "100" ++ l) 
          | _, None => ret (enc_reg bs)
        end in
        r_or_m <- enc_r_or_m;
        (* alternate encoding: even if disp can be in a byte, we can always
           use the encoding of disp32[reg] *)
        if (Word.eq disp Word.zero) then ret (s2bl "00" ++ mmx_reg ++ r_or_m)
          else if (repr_in_signed_byte disp) then
            ret (s2bl "01" ++ mmx_reg ++ r_or_m ++ enc_byte disp)
            else ret (s2bl "10" ++ mmx_reg ++ r_or_m ++ enc_word disp)
    | MMX_Addr_op {| addrDisp:=disp; addrBase:=None; addrIndex:=Some(sc,idx) |} =>
      (* special case: disp32[index*scale] *)
      ret (s2bl "00" ++ mmx_reg ++ s2bl "100" ++
           enc_scale sc ++ enc_reg idx ++ s2bl "101" ++ enc_word disp)
    | _ => invalid
  end.

  Definition enc_mmx_modrm (op1 op2: mmx_operand) := 
  match op1 with 
  | MMX_Reg_op r1 => enc_mmx_modrm_gen (enc_fpr r1) op2
  | _ => invalid
  end.

  Definition enc_gg (gg: mmx_granularity) := 
  match gg with 
  | MMX_8  => s2bl "00"
  | MMX_16 => s2bl "01"
  | MMX_32 => s2bl "10"
  | MMX_64 => s2bl "11"
  end.

  Definition enc_EMMS := ret (s2bl "0000111101110111").

  Definition enc_MOVD (op1 op2: mmx_operand) := 
    match op1, op2 with 
    | GP_Reg_op r, MMX_Reg_op m =>
        ret (s2bl "000011110110111011" ++ (enc_reg r) ++ (enc_fpr m))(*reg to mmxreg*)
    | MMX_Reg_op m, GP_Reg_op r =>
        ret (s2bl "000011110111111011" ++ (enc_fpr m) ++ (enc_reg r))(*reg from mmxreg*)
    | MMX_Addr_op a, MMX_Reg_op m => 
	l1 <- enc_mmx_modrm op2 op1; ret (s2bl "0000111101101110" ++ l1) (*mem to mmxreg *)
    | MMX_Reg_op m, MMX_Addr_op a =>
	l1 <- enc_mmx_modrm op1 op2; ret (s2bl "0000111101111110" ++ l1) (*mem from mmxreg *)
    | _, _=> invalid
    end.

  Definition enc_MOVQ (op1 op2: mmx_operand) :=
    match op1, op2 with 
    | MMX_Addr_op a, MMX_Reg_op m => 
	l1 <- enc_mmx_modrm op2 op1; ret (s2bl "0000111101101111" ++ l1)
    | MMX_Reg_op m, MMX_Addr_op a =>
	l1 <- enc_mmx_modrm op1 op2; ret (s2bl "0000111101111111" ++ l1)
    | _, _ => invalid
    end.

  Definition enc_PACKSSDW (op1 op2: mmx_operand):= 
    match op1, op2 with 
    | MMX_Addr_op mem, MMX_Reg_op mmx =>
	l1<- enc_mmx_modrm op2 op1; ret (s2bl "000011110110101111" ++ l1)
    | _, _ => invalid
    end. 

  Definition enc_PACKSSWB (op1 op2: mmx_operand) := 
    match op1, op2 with 
    | MMX_Addr_op mem, MMX_Reg_op mmx =>
	l1<- enc_mmx_modrm op2 op1; ret (s2bl "0000111101100011" ++ l1)
    | _, _ => invalid
    end. 

  Definition enc_PACKUSWB (op1 op2: mmx_operand):= 
    match op1, op2 with 
    | MMX_Addr_op mem, MMX_Reg_op mmx =>
	l1<- enc_mmx_modrm op2 op1; ret (s2bl "0000111101100111" ++ l1)
    | _, _ => invalid
    end. 

  Definition enc_PADD (gg: mmx_granularity) (op1 op2: mmx_operand):= 
    match gg, op1, op2 with 
    | b, MMX_Addr_op mem, MMX_Reg_op mmx => 
        l1 <- enc_mmx_modrm op2 op1; ret (s2bl "00001111111111" ++ (enc_gg b) ++ l1)
    | _, _, _ => invalid
    end.

  Definition enc_PADDS (gg: mmx_granularity) (op1 op2: mmx_operand):= 
    match gg, op1, op2 with 
    | b, MMX_Addr_op mem, MMX_Reg_op mmx => 
        l1 <- enc_mmx_modrm op2 op1; ret (s2bl   "00001111111011" ++ (enc_gg b) ++ l1)
    | _, _, _ => invalid
    end.

  Definition enc_PADDUS (gg: mmx_granularity) (op1 op2: mmx_operand):= 
    match gg, op1, op2 with 
    | b, MMX_Addr_op mem, MMX_Reg_op mmx => 
        l1 <- enc_mmx_modrm op2 op1; ret (s2bl   "00001111110111" ++ (enc_gg b) ++ (s2bl "11") ++ l1)
    | _, _, _ => invalid
    end.

  Definition enc_PAND (op1 op2: mmx_operand):= 
    match op1, op2 with
    | MMX_Addr_op mem, MMX_Reg_op mmx =>
	l1<- enc_mmx_modrm op2 op1; ret (s2bl "0000111111011011" ++ l1)
    | _, _ => invalid
    end. 

  Definition enc_PANDN (op1 op2: mmx_operand):= 
    match op1, op2 with
    | MMX_Addr_op mem, MMX_Reg_op mmx =>
	l1<- enc_mmx_modrm op2 op1; ret (s2bl "0000111111011111" ++ l1)
    | _, _ => invalid
    end. 

  Definition enc_PCMPEQ (gg: mmx_granularity) (op1 op2: mmx_operand):=
    match gg, op1, op2 with
    | b, MMX_Addr_op mem, MMX_Reg_op mmx => 
        l1 <- enc_mmx_modrm op2 op1; ret (s2bl   "00001111011101" ++ (enc_gg b) ++ (s2bl "11") ++ l1)
    | _, _, _ => invalid
    end.

  Definition enc_PCMPGT (gg: mmx_granularity) (op1 op2: mmx_operand):= 
    match gg, op1, op2 with
    | b, MMX_Addr_op mem, MMX_Reg_op mmx => 
        l1 <- enc_mmx_modrm op2 op1; ret (s2bl   "00001111011001" ++ (enc_gg b) ++ (s2bl "11") ++ l1)
    | _, _, _ => invalid
    end.

  Definition enc_PMADDWD (op1 op2: mmx_operand):= 
    match op1, op2 with
    | MMX_Addr_op mem, MMX_Reg_op mmx =>
	l1<- enc_mmx_modrm op2 op1; ret (s2bl "0000111111110101" ++ l1)
    | _, _ => invalid
    end. 

  Definition enc_PMULHUW (op1 op2: mmx_operand):= 
    match op1, op2 with
    | MMX_Addr_op mem, MMX_Reg_op mmx =>
	l1<- enc_mmx_modrm op2 op1; ret (s2bl "0000111111100100" ++ l1)
    | _, _ => invalid
    end.

  Definition enc_PMULHW (op1 op2: mmx_operand):= 
    match op1, op2 with
    | MMX_Addr_op mem, MMX_Reg_op mmx =>
	l1<- enc_mmx_modrm op2 op1; ret (s2bl "0000111111100101" ++ l1)
    | _, _ => invalid
    end. 

  Definition enc_PMULLW (op1 op2: mmx_operand):= 
    match op1, op2 with
    | MMX_Addr_op mem, MMX_Reg_op mmx =>
	l1<- enc_mmx_modrm op2 op1; ret (s2bl "0000111111010101" ++ l1)
    | _, _ => invalid
    end. 

  Definition enc_POR (op1 op2: mmx_operand):= 
    match op1, op2 with
    | MMX_Addr_op mem, MMX_Reg_op mmx =>
	l1<- enc_mmx_modrm op2 op1; ret (s2bl "0000111111100101" ++ l1)
    | _, _ => invalid
    end.

  Definition enc_PSLL (gg: mmx_granularity) (op1 op2: mmx_operand):= 
    match gg, op1, op2 with
    | b, MMX_Addr_op mem, MMX_Reg_op mmx => 
        l1 <- enc_mmx_modrm op2 op1; ret (s2bl     "00001111111100" ++ (enc_gg b) ++ (s2bl "11") ++ l1)
    | b, MMX_Reg_op r, MMX_Imm_op imm => ret (s2bl "00001111111100" ++ (enc_gg b) ++ (s2bl "11110") ++ (enc_fpr r) ++ (enc_byte imm))
    | _, _, _ => invalid
    end.

  Definition enc_PSRA (gg: mmx_granularity) (op1 op2: mmx_operand):=
    match gg, op1, op2 with
    | b, MMX_Addr_op mem, MMX_Reg_op mmx => 
        l1 <- enc_mmx_modrm op2 op1; ret (s2bl   "00001111111000" ++ (enc_gg b) ++ (s2bl "11") ++ l1)
    | b, MMX_Reg_op r, MMX_Imm_op imm => ret (s2bl "00001111111000" ++ (enc_gg b) ++ (s2bl "11110") ++ (enc_fpr r) ++ (enc_byte imm))
    | _, _, _ => invalid
    end.

  Definition enc_PSRL (gg: mmx_granularity) (op1 op2: mmx_operand):= 
    match gg, op1, op2 with
    | b, MMX_Addr_op mem, MMX_Reg_op mmx => 
        l1 <- enc_mmx_modrm op2 op1; ret (s2bl   "00001111110100" ++ (enc_gg b) ++ (s2bl "11") ++ l1)
    | b, MMX_Reg_op r, MMX_Imm_op imm => ret (s2bl "00001111110100" ++ (enc_gg b) ++ (s2bl "11110") ++ (enc_fpr r) ++ (enc_byte imm))
    | _, _, _ => invalid
    end.

  Definition enc_PSUB (gg: mmx_granularity) (op1 op2: mmx_operand):= 
    match gg, op1, op2 with
    | b, MMX_Addr_op mem, MMX_Reg_op mmx => 
        l1 <- enc_mmx_modrm op2 op1; ret (s2bl   "00001111111110" ++ (enc_gg b) ++ l1)
    | _, _, _ => invalid
    end.

  Definition enc_PSUBS (gg: mmx_granularity) (op1 op2: mmx_operand):= 
    match gg, op1, op2 with
    | b, MMX_Addr_op mem, MMX_Reg_op mmx => 
        l1 <- enc_mmx_modrm op2 op1; ret (s2bl   "00001111111010" ++ (enc_gg b) ++ l1)
    | _, _, _ => invalid
    end.

  Definition enc_PSUBUS (gg: mmx_granularity) (op1 op2: mmx_operand):= 
    match gg, op1, op2 with
    | b, MMX_Addr_op mem, MMX_Reg_op mmx => 
        l1 <- enc_mmx_modrm op2 op1; ret (s2bl   "00001111110110" ++ (enc_gg b) ++ l1)
    | _, _, _ => invalid
    end.

  Definition enc_PUNPCKH (gg: mmx_granularity) (op1 op2: mmx_operand):= 
    match gg, op1, op2 with
    | b, MMX_Addr_op mem, MMX_Reg_op mmx => 
        l1 <- enc_mmx_modrm op2 op1; ret (s2bl   "00001111011010" ++ (enc_gg b) ++ l1)
    | _, _, _ => invalid
    end.

  Definition enc_PUNPCKL (gg: mmx_granularity) (op1 op2: mmx_operand):= 
    match gg, op1, op2 with
    | b, MMX_Addr_op mem, MMX_Reg_op mmx => 
        l1 <- enc_mmx_modrm op2 op1; ret (s2bl   "00001111011000" ++ (enc_gg b) ++ l1)
    | _, _, _ => invalid
    end.

  Definition enc_PXOR (op1 op2: mmx_operand):= 
    match op1, op2 with
    | MMX_Addr_op mem, MMX_Reg_op mmx =>
	l1<- enc_mmx_modrm op2 op1; ret (s2bl "0000111111101111" ++ l1)
    | _, _ => invalid
    end.
(*SSE Encodings*)
Definition enc_xmm_r r := 
  match r with 
  | XMM0 => s2bl "000"
  | XMM1 => s2bl "001"
  | XMM2 => s2bl "010"
  | XMM3 => s2bl "011"
  | XMM4 => s2bl "100" 
  | XMM5 => s2bl "101"
  | XMM6 => s2bl "110"
  | _    => s2bl "111"
  end.

Definition enc_xmm_modrm_gen (xmm_reg: list bool) (op2: sse_operand) : Enc (list bool) := 
  match op2 with
    | SSE_XMM_Reg_op r2 => ret (s2bl "11" ++ xmm_reg ++ enc_xmm_r r2)
    | SSE_Addr_op {| addrDisp:=disp; addrBase:=None; addrIndex:=None |} =>
      ret (s2bl "00" ++ xmm_reg ++ s2bl "101" ++ enc_word disp)
    | SSE_Addr_op {| addrDisp:=disp; addrBase:=Some bs; addrIndex:=idxopt |} =>
      let enc_r_or_m :=
        match bs, idxopt with
          | ESP, _  (* special case: when base is ESP, need a SIB byte *)
          | _, Some _ =>
            l <- enc_SIB bs idxopt; ret (s2bl "100" ++ l)
          | _, None => ret (enc_reg bs)
        end in
        r_or_m <- enc_r_or_m;
        (* alternate encoding: even if disp can be in a byte, we can always
           use the encoding of disp32[reg] *)
        if (Word.eq disp Word.zero) then ret (s2bl "00" ++ xmm_reg ++ r_or_m)
          else if (repr_in_signed_byte disp) then
            ret (s2bl "01" ++ xmm_reg ++ r_or_m ++ enc_byte disp)
            else ret (s2bl "10" ++ xmm_reg ++ r_or_m ++ enc_word disp)
    | SSE_Addr_op {| addrDisp:=disp; addrBase:=None; addrIndex:=Some(sc,idx) |} =>
      (* special case: disp32[index*scale] *)
      ret (s2bl "00" ++ xmm_reg ++ s2bl "100" ++
           enc_scale sc ++ enc_reg idx ++ s2bl "101" ++ enc_word disp)
    | _ => invalid
  end.

  Definition enc_xmm_modrm (op1 op2: sse_operand) := 
  match op1 with 
  | SSE_XMM_Reg_op r1 => enc_xmm_modrm_gen (enc_xmm_r r1) op2
  | _ => invalid
  end.

(*Also needs to be enc_mm_modrm and enc_r32_modrm for SSE encodings *)

Definition enc_prefix (pre:X86Syntax.prefix) : Enc (list bool) :=
  let lr := 
    match (lock_rep pre) with
      | Some lock => s2bl "11110000"
      | Some rep  => s2bl "11110011"
      | Some repn => s2bl "11110010"
      | None => s2bl ""
    end in
  let so := 
    match (seg_override pre) with
      | Some CS => s2bl "00101110"
      | Some SS => s2bl "00110110"
      | Some DS => s2bl "00111110"
      | Some ES => s2bl "00100110"
      | Some FS => s2bl "01100100"
      | Some GS => s2bl "01100101"
      | None => s2bl ""
    end in
  let oo := if (op_override pre) then s2bl "01100110" else s2bl "" in
  let ao := if (addr_override pre) then s2bl "01100111" else s2bl "" in
    ret (lr ++ so ++ oo ++ ao).

Definition enc_instr (pre:X86Syntax.prefix) (i:instr) : Enc (list bool) := 
  match i with
    | AAA => enc_AAA
    | AAD => enc_AAD
    | AAM => enc_AAM
    | AAS => enc_AAS
    | ADC w op1 op2 => enc_ADC (op_override pre) w op1 op2
    | ADD w op1 op2 => enc_ADD (op_override pre) w op1 op2
    | AND w op1 op2 => enc_AND (op_override pre) w op1 op2
    | ARPL op1 op2 => enc_ARPL op1 op2
    | BOUND op1 op2 => enc_BOUND op1 op2
    | BSF op1 op2 => enc_BSF op1 op2
    | BSR op1 op2 => enc_BSR op1 op2
    | BSWAP r => enc_BSWAP r
    | BT op1 op2 => enc_BT op1 op2
    | BTC op1 op2 => enc_BTC op1 op2 
    | BTR op1 op2 => enc_BTR op1 op2
    | BTS op1 op2 => enc_BTS op1 op2
    | CALL near abs op1 sel => enc_CALL near abs op1 sel
    | CDQ => enc_CDQ
    | CLC => enc_CLC
    | CLD => enc_CLD
    | CLI => enc_CLI
    | CLTS => enc_CLTS
    | CMC => enc_CMC
    | CMOVcc ct op1 op2 => enc_CMOVcc ct op1 op2
    | CMP w op1 op2 => enc_CMP (op_override pre) w op1 op2
    | CMPS w => enc_CMPS w
    | CMPXCHG w op1 op2 => enc_CMPXCHG w op1 op2
    | CPUID => enc_CPUID
    | CWDE => enc_CWDE
    | DAA => enc_DAA
    | DAS => enc_DAS
    | DEC w op1 => enc_DEC w op1
    | DIV w op1 => enc_DIV w op1

    | F2XM1 => enc_F2XM1
    | FABS => enc_FABS
    | FADD d op1 => enc_FADD d op1
    | FADDP op1 => enc_FADDP op1
    | FBLD op1 => enc_FADDP op1
    | FBSTP op1 => enc_FADDP op1
    | FCHS => enc_FCHS
    | FCLEX => enc_FCLEX
    | FCOM op1 => enc_FCOM op1
    | FCOMP op1 => enc_FCOMP op1
    | FCOMPP => enc_FCOMPP
    | FCOMIP op1 => enc_FCOMIP op1
    | FCOS => enc_FCOS
    | FDECSTP => enc_FDECSTP
    | FDIV op1 op2 => enc_FDIV op1 op2
    | FDIVP op1 => enc_FDIVP op1
    | FDIVR op1 op2 => enc_FDIVR op1 op2
    | FDIVRP op1 => enc_FDIVRP op1
    | FFREE op1 => enc_FFREE op1
    | FIADD op1 => enc_FIADD op1
    | FICOM op1 => enc_FICOM op1
    | FICOMP op1 => enc_FICOMP op1
    | FIDIV op1 => enc_FIDIV op1
    | FIDIVR op1 => enc_FIDIVR op1
    | FILD op1 => enc_FILD op1
    | FIMUL op1 => enc_FIMUL op1
    | FINCSTP => enc_FINCSTP
    | FINIT => enc_FINIT
    | FIST op1 => enc_FIST op1
    | FISTP op1 => enc_FISTP op1
    | FISUB op1 => enc_FISUB op1
    | FISUBR op1 => enc_FISUBR op1
    | FLD op1 => enc_FLD op1
    | FLD1 => enc_FLD1
    | FLDCW op1 => enc_FLDCW op1
    | FLDENV op1 => enc_FLDENV op1
    | FLDL2E => enc_FLDL2E
    | FLDL2T => enc_FLDL2T
    | FLDLG2 => enc_FLDLG2
    | FLDLN2 => enc_FLDLN2
    | FLDPI => enc_FLDPI
    | FLDZ => enc_FLDZ
    | FMUL d op1 => enc_FMUL d op1
    | FMULP op1 => enc_FMULP op1
    | FNOP => enc_FNOP
    | FNSAVE op1 => enc_FNSAVE op1
    | FNSTCW op1 => enc_FNSTCW op1
    | FPATAN => enc_FPATAN
    | FPREM => enc_FPREM
    | FPREM1 => enc_FPREM1
    | FPTAN => enc_FPATAN 
    | FRNDINT => enc_FRNDINT
    | FRSTOR op1 => enc_FRSTOR op1
    | FSCALE => enc_FSCALE
    | FSIN => enc_FSIN
    | FSINCOS => enc_FSINCOS
    | FSQRT => enc_FSQRT
    | FST op1 => enc_FST op1
    | FSTENV op1 => enc_FSTENV op1
    | FSTP op1 => enc_FSTP op1 
    | FSTSW op1 => enc_FSTSW op1
    | FSUB op1 op2 => enc_FSUB op1 op2
    | FSUBP op1 => enc_FSUBP op1
    | FSUBR op1 op2 => enc_FSUBR op1 op2
    | FSUBRP op1 => enc_FSUBRP op1
    | FTST => enc_FTST
    | FUCOM op1 => enc_FUCOM op1
    | FUCOMP op1 => enc_FUCOMP op1
    | FUCOMPP => enc_FUCOMPP
    | FUCOMI op1 => enc_FUCOMI op1
    | FUCOMIP op1 => enc_FUCOMIP op1
    | FXAM => enc_FXAM
    | FXCH op1 => enc_FXCH op1
    | FXTRACT => enc_FXTRACT
    | FYL2X => enc_FYL2X
    | FYL2XP1 => enc_FYL2XP1
    | FWAIT => enc_FWAIT

    | HLT => enc_HLT
    | IDIV w op1 => enc_IDIV w op1
    | IMUL w op1 opopt iopt => enc_IMUL (op_override pre) w op1 opopt iopt
    | IN w p => enc_IN w p
    | INC w op1 => enc_INC w op1
    | INS w => enc_INS w
    | INTn it => enc_INTn it
    | INT => enc_INT
    | INTO => enc_INTO
    | INVD => enc_INVD
    | INVLPG op1 => enc_INVLPG op1
    | IRET => enc_IRET
    | Jcc ct disp => enc_Jcc ct disp
    | JCXZ b => enc_JCXZ b
    | JMP near absolute op1 sel => enc_JMP near absolute op1 sel
    | LAHF => enc_LAHF
    | LAR op1 op2 => enc_LAR op1 op2
    | LDS op1 op2 => enc_LDS op1 op2
    | LEA op1 op2 => enc_LEA op1 op2
    | LEAVE => enc_LEAVE
    | LES op1 op2 => enc_LES op1 op2 
    | LFS op1 op2 => enc_LFS op1 op2 
    | LGDT op1 => enc_LGDT op1
    | LGS  op1 op2 => enc_LGS op1 op2
    | LIDT op1 => enc_LIDT op1
    | LLDT op1 => enc_LLDT op1
    | LMSW op1 => enc_LMSW op1 
    | LODS w => enc_LODS w
    | LOOP disp => enc_LOOP disp
    | LOOPZ disp => enc_LOOPZ disp
    | LOOPNZ disp => enc_LOOPNZ disp
    | LSL op1 op2 => enc_LSL op1 op2
    | LSS op1 op2 => enc_LSS op1 op2
    | LTR  op1 => enc_LTR op1
    | MOV w op1 op2 => enc_MOV (op_override pre) w op1 op2
    | MOVCR d cr r => enc_MOVCR d cr r
    | MOVDR d dr r => enc_MOVDR d dr r
    | MOVSR d sr op1 => enc_MOVSR d sr op1
    | MOVBE op1 op2 => enc_MOVBE op1 op2
    | MOVS w => enc_MOVS w
    | MOVSX w op1 op2 => enc_MOVSX w op1 op2
    | MOVZX w op1 op2 => enc_MOVZX w op1 op2
    | MUL w op1 => enc_MUL w op1
    | NEG  w op1 => enc_NEG w op1
    | NOP opopt => enc_NOP opopt
    | NOT w op1 => enc_NOT w op1
    | OR w op1 op2 => enc_OR (op_override pre) w op1 op2
    | OUT w p => enc_OUT w p
    | OUTS w => enc_OUTS w
    | POP op1 => enc_POP op1
    | POPSR sr => enc_POPSR sr
    | POPA => enc_POPA
    | POPF => enc_POPF
    | PUSH w op1 => enc_PUSH w op1
    | PUSHSR sr => enc_PUSHSR sr
    | PUSHA => enc_PUSHA
    | PUSHF => enc_PUSHF
    | RCL w op1 ri => enc_RCL w op1 ri
    | RCR w op1 ri => enc_RCR w op1 ri
    | RDMSR => enc_RDMSR
    | RDPMC => enc_RDPMC
    | RDTSC => enc_RDTSC
    | RDTSCP => enc_RDTSCP
    | RET ss disp => enc_RET ss disp
    | ROL w op1 ri => enc_ROL w op1 ri
    | ROR w op1 ri => enc_ROR w op1 ri
    | RSM => enc_RSM
    | SAHF => enc_SAHF
    | SAR w op1 ri => enc_SAR w op1 ri
    | SBB w op1 op2 => enc_SBB (op_override pre) w op1 op2
    | SCAS w => enc_SCAS w
    | SETcc ct op1 => enc_SETcc ct op1
    | SGDT op1 => enc_SGDT op1
    | SHL w op1 ri => enc_SHL w op1 ri
    | SHLD op1 r ri => enc_SHLD op1 r ri
    | SHR w op1 ri => enc_SHR w op1 ri
    | SHRD op1 r ri => enc_SHRD op1 r ri
    | SIDT op1 => enc_SIDT op1
    | SLDT op1 => enc_SLDT op1
    | SMSW op1 => enc_SMSW op1
    | STC => enc_STC
    | STD => enc_STD
    | STI => enc_STI
    | STOS w => enc_STOS w
    | STR op1 => enc_STR op1
    | SUB w op1 op2 => enc_SUB (op_override pre) w op1 op2
    | TEST w op1 op2 => enc_TEST (op_override pre) w op1 op2
    | UD2 => enc_UD2
    | VERR op1 => enc_VERR op1
    | VERW op1 => enc_VERW op1
    | WBINVD => enc_WBINVD
    | WRMSR => enc_WRMSR
    | XADD w op1 op2 => enc_XADD w op1 op2
    | XCHG w op1 op2 => enc_XCHG w op1 op2
    | XLAT => enc_XLAT
    | XOR w op1 op2 => enc_XOR (op_override pre) w op1 op2

    (*MMX encoding definitions *)
    | EMMS => enc_EMMS
    | MOVD op1 op2 => enc_MOVD op1 op2
    | MOVQ op1 op2 => enc_MOVQ op1 op2
    | PACKSSDW op1 op2 => enc_PACKSSDW op1 op2
    | PACKSSWB op1 op2 => enc_PACKSSWB op1 op2
    | PACKUSWB op1 op2 => enc_PACKUSWB op1 op2
    | PADD gg op1 op2 => enc_PADD gg op1 op2
    | PADDS gg op1 op2 => enc_PADDS gg op1 op2
    | PADDUS gg op1 op2 => enc_PADDUS gg op1 op2
    | PAND op1 op2 => enc_PAND op1 op2
    | PANDN op1 op2 => enc_PANDN op1 op2
    | PCMPEQ gg op1 op2 => enc_PCMPEQ gg op1 op2
    | PCMPGT gg op1 op2 => enc_PCMPGT gg op1 op2
    | PMADDWD op1 op2 => enc_PMADDWD op1 op2
    | PMULHUW op1 op2 => enc_PMULHUW op1 op2
    | PMULHW op1 op2 => enc_PMULHW op1 op2 
    | PMULLW op1 op2 => enc_PMULLW op1 op2
    | POR op1 op2 => enc_POR op1 op2
    | PSLL gg op1 op2 => enc_PSLL gg op1 op2
    | PSRA gg op1 op2 => enc_PSRA gg op1 op2
    | PSRL gg op1 op2 => enc_PSRL gg op1 op2
    | PSUB gg op1 op2 => enc_PSUB gg op1 op2
    | PSUBS gg op1 op2 => enc_PSUBS gg op1 op2
    | PSUBUS gg op1 op2 => enc_PSUBUS gg op1 op2
    | PUNPCKH gg op1 op2 => enc_PUNPCKH gg op1 op2
    | PUNPCKL gg op1 op2 => enc_PUNPCKL gg op1 op2
    | PXOR op1 op2 => enc_PXOR op1 op2

    (*SSE encoding definitions *)
    | _ => invalid
  end.

Definition enc_pre_instr pre ins : Enc (list bool) := 
  l1 <- enc_prefix pre;
  l2 <- enc_instr pre ins;
  ret (l1 ++ l2).

(* encode instrs and output a list of bytes *)
Definition enc_pre_instr_bytes pre ins : Enc (list Z) :=
  let to_bytes := 
    (fix to_bytes lbits n (acc:Z) res :=
      match lbits with
        | nil => if (Zeq_bool n 7) then ret res else invalid
        | b::lbits' => 
          let acc' := Word.Z_shift_add b acc in
            if (Zeq_bool n 0) then
              to_bytes lbits' 7 0 (acc'::res)
            else
              to_bytes lbits' (n-1) acc' res
      end)
  in
  lbits <- enc_pre_instr pre ins;
  lbytes <- to_bytes lbits 7 0 nil;
  ret (List.rev lbytes).

(*
 80483fd:	55                   	push   ebp
 80483fe:	89 e5                	mov    ebp,esp
*)

(* some simple testing *)
(* Definition emptyPrefix := mkPrefix None None false false. *)
(* Eval compute in (enc_pre_instr_bytes emptyPrefix (PUSH true (Reg_op EBP))). *)
(* Eval compute in (enc_pre_instr_bytes emptyPrefix (MOV true (Reg_op ESP) (Reg_op EBP))). *)
