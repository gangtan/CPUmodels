(* Copyright (c) 2010-2011.
   Greg Morrisett, Gang Tan, Joseph Tassarotti, Jean-Baptiste Tristan, Edward Gan.
   All rights reserved. *)

Require ExtrOcamlString.
Require ExtrOcamlNatBigInt.
Require ExtrOcamlZBigInt.
Require Import Coq.Init.Logic.
Require Import Bool.
Require Import List.
Require Import List.
Require Import Monad.
Require Import Parser.
Require Import ZArith.
Require Import String.
Require Import Ascii.
Unset Automatic Introduction.
Set Implicit Arguments.
Local Open Scope Z_scope.

(* These are all nearly cribbed from Decode.v, but 
   this way we eliminate some of the slowness of loading
   Decode.v and we get the freedome to redefine stuff like
   modrm so it won't try to address stuff we probably
   won't have readaccess to *)

(* a module for generating the parser for x86 instructions *)
Module X86_PARSER_ARG.
  Require Import X86Syntax.
  Require Import Bits.
  
  Definition char_p : Set := bool.
  Definition char_eq : forall (c1 c2:char_p), {c1=c2}+{c1<>c2} := bool_dec.
  Inductive type : Set := 
  | Int_t : type
  | Register_t : type
  | Byte_t : type
  | Half_t : type
  | Word_t : type
  | Scale_t : type
  | Condition_t : type
  | Operand_t : type
  | Instruction_t : type
  | Control_Register_t : type
  | Debug_Register_t : type
  | Segment_Register_t : type
  | Lock_or_Rep_t : type
  | Bool_t : type
  | Prefix_t : type
  | Option_t (t: type) : type
  (* Need pairs at this level if I want to have options of pairs*)
  | Pair_t (t1 t2: type) : type. 

  Definition tipe := type.
  Definition tipe_eq : forall (t1 t2:tipe), {t1=t2} + {t1<>t2}.
    intros ; decide equality.
  Defined.

  Fixpoint tipe_m (t:tipe) := 
    match t with 
      | Int_t => Z
      | Register_t => register
      | Byte_t => int8
      | Half_t => int16
      | Word_t => int32
      | Scale_t => scale
      | Condition_t => condition_type
      | Operand_t => operand
      | Instruction_t => instr
      | Control_Register_t => control_register
      | Debug_Register_t => debug_register
      | Segment_Register_t => segment_register
      | Lock_or_Rep_t => lock_or_rep
      | Bool_t => bool
      | Prefix_t => prefix
      | Option_t t => option (tipe_m t)
      | Pair_t t1 t2 => ((tipe_m t1) * (tipe_m t2))%type
    end.
End X86_PARSER_ARG.

Module X86_PARSER.
  Module X86_BASE_PARSER := Parser.Parser(X86_PARSER_ARG).
  Require Import X86Syntax.
  Require Import Bits.
  Import X86_PARSER_ARG.
  Import X86_BASE_PARSER.

  Definition option_t x := tipe_t (Option_t x).
  Definition int_t := tipe_t Int_t.
  Definition register_t := tipe_t Register_t.
  Definition byte_t := tipe_t Byte_t.
  Definition half_t := tipe_t Half_t.
  Definition word_t := tipe_t Word_t.
  Definition scale_t := tipe_t Scale_t.
  Definition condition_t := tipe_t Condition_t.
  Definition operand_t := tipe_t Operand_t.
  Definition instruction_t := tipe_t Instruction_t.
  Definition control_register_t := tipe_t Control_Register_t.
  Definition debug_register_t := tipe_t Debug_Register_t.
  Definition segment_register_t := tipe_t Segment_Register_t.
  Definition lock_or_rep_t := tipe_t Lock_or_Rep_t.
  Definition bool_t := tipe_t Bool_t.
  Definition prefix_t := tipe_t Prefix_t.
  (* combinators for building parsers *)
  Definition bit(x:bool) : parser char_t := Char_p x.
  Definition never t : parser t := Zero_p t.
  Definition always t (x:result_m t) : parser t := @Map_p unit_t t (fun (_:unit) => x) Eps_p.
  Definition alt t (p1 p2:parser t) : parser t := Alt_p p1 p2.
  Definition alts t (ps: list (parser t)) : parser t := List.fold_right (@alt t) (@never t) ps.
  Definition map t1 t2 (p:parser t1) (f:result_m t1 -> result_m t2) : parser t2 := 
    @Map_p t1 t2 f p.
  Implicit Arguments map [t1 t2].
  Definition seq t1 t2 (p1:parser t1) (p2:parser t2) : parser (pair_t t1 t2) := Cat_p p1 p2.
  Definition cons t (pair : result_m (pair_t t (list_t t))) : result_m (list_t t) := 
    (fst pair)::(snd pair).
  Definition seqs t (ps:list (parser t)) : parser (list_t t) := 
    List.fold_right (fun p1 p2 => map (seq p1 p2) (@cons t)) 
      (@always (list_t t) (@nil (result_m t))) ps.
  Fixpoint string_to_bool_list (s:string) : list bool := 
    match s with
      | EmptyString => nil
      | String a s => 
        (if ascii_dec a "0"%char then false else true)::(string_to_bool_list s)
    end.

  Fixpoint bits_n (n:nat) : result := 
    match n with 
      | 0%nat => unit_t
      | S n => pair_t char_t (bits_n n)
    end.
  Fixpoint field'(n:nat) : parser (bits_n n) := 
    match n with 
      | 0%nat => Eps_p
      | S n => Cat_p Any_p (field' n)
    end.
  Fixpoint bits2Z(n:nat)(a:Z) : result_m (bits_n n) -> result_m int_t := 
    match n with 
      | 0%nat => fun _ => a
      | S n => fun p => bits2Z n (2*a + (if (fst p) then 1 else 0)) (snd p)
    end.
  Definition bits2int(n:nat)(bs:result_m (bits_n n)) : result_m int_t := bits2Z n 0 bs.
  Fixpoint bits (x:string) : parser (bits_n (String.length x)) := 
    match x with 
      | EmptyString => Eps_p
      | String c s => 
        (Cat_p (Char_p (if ascii_dec c "0"%char then false else true)) (bits s))
    end.

  (* notation for building parsers *)
  Infix "|+|" := alt (right associativity, at level 80).
  Infix "$" := seq (right associativity, at level 70).
  Infix "@" := map (right associativity, at level 75).
  Notation "e %% t" := (e : result_m t) (at level 80).
  Definition bitsleft t (s:string)(p:parser t) : parser t := 
    bits s $ p @ (@snd _ _).
  Infix "$$" := bitsleft (right associativity, at level 70).

  Definition anybit : parser char_t := Any_p.
  Definition field(n:nat) := (field' n) @ (bits2int n).
  Definition byte := (field 8) @ (@Word.repr 7 : _ -> result_m byte_t).
 (* Definition halfword := (field 16) @ (@Word.repr 15 : _ -> result_m half_t).
  Definition word := (field 32) @ (@Word.repr 31 : _ -> result_m word_t). *)
  Definition halfword := (byte $ byte) @ ((fun p =>
      let b0 := Word.repr (Word.unsigned (fst p)) in
      let b1 := Word.repr (Word.unsigned (snd p)) in
        Word.or (Word.shl b1 (Word.repr 8)) b0): _ -> result_m half_t).
  Definition word := (byte $ byte $ byte $ byte) @
    ((fun p => 
        let b0 := zero_extend8_32 (fst p) in
        let b1 := zero_extend8_32 (fst (snd p)) in
        let b2 := zero_extend8_32 (fst (snd (snd p))) in
        let b3 := zero_extend8_32 (snd (snd (snd p))) in
         let w1 := Word.shl b1 (Word.repr 8) in
         let w2 := Word.shl b2 (Word.repr 16) in
         let w3 := Word.shl b3 (Word.repr 24) in
          Word.or w3 (Word.or w2 (Word.or w1 b0)))
    : _ -> result_m word_t).

  (*
  Definition scale_p := (field 2) @ (Z_to_scale : _ -> result_m scale_t).
  *)
  Definition scale_p := bits "00" @ (fun _ => (Z_to_scale 1) %% scale_t).

  Definition tttn := (field 4) @ (Z_to_condition_type : _ -> result_m condition_t).

  (* The goal here is to have ESP and EBP and EBX to try to be the ones used for
     memory accesses - why? ESP/EBP Theyare most likely to point to valid memory
     addresses. I include EBX since ESP/EBP have special other properties, due to
     being for the stack (the addressing modes are odd *)

  Definition reg_no_esp : parser register_t :=
     (bits "000" |+| bits "001" |+| bits "010" |+|
     bits "011" |+| (* bits "100" <- this is esp *)  bits "101" |+|
     bits "110" |+| bits "111") @ 
       ((fun bs => Z_to_register (bits2int 3 bs)) : _ -> result_m register_t).

  Definition reg_no_ebp : parser register_t :=
     (bits "000" |+| bits "001" |+| bits "010" |+|
     bits "011" |+|  bits "100"  (* |+| bits "101" <- this is ebp *) |+|
     bits "110" |+| bits "111") @ 
       ((fun bs => Z_to_register (bits2int 3 bs)) : _ -> result_m register_t).

  Definition si := 
   (* (scale_p $ (bits "011") @ (fun p => let (p1,p2) := p in (Some (p1, EBX) %% (option_t 
      (Pair_t Scale_t Register_t))))) |+|  *)
    (scale_p $ bits "100" @ (fun p => None %% (option_t
      (Pair_t Scale_t Register_t)))).

  Definition sialt := 
  (scale_p $ (bits "011") @ (fun p => let (p1,p2) := p in (Some (p1, EBX) %% (option_t 
      (Pair_t Scale_t Register_t))))).

  Definition esp_ebp_ebx : parser register_t :=
    (bits "100" @ (fun _ => ESP %% register_t)) |+|
    (bits "101" @ (fun _ => EBP %% register_t)) |+|
    (bits "011" @ (fun _ => EBX %% register_t)).

  Definition reg_no_ebx_esp_ebp : parser register_t :=
     (bits "000" |+| bits "001" |+| bits "010" |+|
     (* bits "011" |+|  bits "100" |+| bits "101" <- this is esp and ebp *) 
     bits "110" |+| bits "111") @ 
       ((fun bs => Z_to_register (bits2int 3 bs)) : _ -> result_m register_t).

  Definition reg := reg_no_ebx_esp_ebp. 

  Definition sib := si $ (esp_ebp_ebx).
     
  (* This is 32 bytes, but it's between
     FFFF FF00 and 0000 00FF *)
(*  Definition smallword := 
    ((byte $ ("0000" $$ "0000" $$ "0000" $$ "0000" $$ "0000" $$ bits "0000")) |+|
      (byte $ ("1111" $$ "1111" $$ "1111" $$ "1111" $$ "1111" $$ bits "1111"))) @ 
      ((fun p => let (p, _) := p in zero_extend8_32 p %% word_t)).
*)
    Definition smallword :=
      (byte $ byte $ "1100" $$ "0000" $$ "0000" $$ bits "0000") @ (fun p => let (p, _) := 
        p in zero_extend8_32 p %% word_t) .
 
  (* These next 4 parsers are used in the definition of the mod/rm parser *)
  Definition rm00 : parser operand_t := 
    ( 
      bits "011" 
      ) @ 
          (fun bs => Address_op (mkAddress (Word.repr 0) 
            (Some (Z_to_register(bits2int 3 bs))) None) %% operand_t)
      |+| bits "100" $ si $ bits "011" @ 
          (fun p => match p with
                      | (_,(si,base)) => 
                        Address_op (mkAddress (Word.repr 0) 
                          (Some EBX) si)
                    end : result_m operand_t)     
      |+| bits "100" $ sialt $ bits "101" $ smallword @
          (fun p => match p with
                      | (_,(si,(_, disp))) => 
                        Address_op (mkAddress disp
                          (None) si)
                    end : result_m operand_t)
      |+| bits "101" $ smallword @
          (fun p => match p with 
                      | (_, disp) => 
                        Address_op (mkAddress disp None None)
                    end %% operand_t).  

  Definition rm01 : parser operand_t := 
    ((    bits "011" 
      $ byte)) @ 
          (fun p => 
            match p with 
              | (bs, disp) =>
                Address_op (mkAddress (sign_extend8_32 disp) 
                  (Some (Z_to_register(bits2int 3 bs))) None)
            end %% operand_t)
      |+| bits "100" $ sib $ byte @ 
          (fun p => 
            match p with
              | (_,((si,base),disp)) => 
                Address_op (mkAddress (sign_extend8_32 disp) (Some base)
                  (si))
            end %% operand_t).

  Definition rm10 : parser operand_t := 
    ((    bits "011" 
      ) $ smallword) @ 
          (fun p => 
            match p with 
              | (bs, disp) =>
                Address_op (mkAddress disp (Some (Z_to_register(bits2int 3 bs))) None)
            end %% operand_t)
      |+|  bits "100" $ sib $ smallword @ 
          (fun p => 
            match p with
              | (_,((si,base),disp)) => 
                Address_op (mkAddress disp (Some base) si)
            end %% operand_t).
  
  Definition rm11 : parser operand_t := reg_no_ebx_esp_ebp
   @ (fun x => Reg_op x : result_m operand_t).

  Definition modrm : parser (pair_t operand_t operand_t) := 
    (     (bits "00" $ (reg_no_ebx_esp_ebp) $ rm00)
      |+| (bits "01" $ (reg_no_ebx_esp_ebp) $ rm01)
      |+| (bits "10" $ (reg_no_ebx_esp_ebp) $ rm10)
      |+| (bits "11" $ (reg_no_ebx_esp_ebp) $ rm11) ) @ 
          (fun p => match p with 
                      | (_, (r, op)) => (Reg_op r, op)
                    end %% (pair_t operand_t operand_t)).


  (* same as modrm but disallows the register case *)
  Definition modrm_noreg :=
  (     ("00" $$ reg_no_ebx_esp_ebp $ rm00)
    |+| ("01" $$ reg_no_ebx_esp_ebp $ rm01)
    |+| ("10" $$ reg_no_ebx_esp_ebp $ rm10)).

  (* Similar to mod/rm parser except that the register field is fixed to a
   * particular bit-pattern, and the pattern starting with "11" is excluded. *)
  Definition ext_op_modrm(bs:string) : parser operand_t := 
    (      (bits "00" $ bits bs $ rm00)
     |+|   (bits "01" $ bits bs $ rm01)
     |+|   (bits "10" $ bits bs $ rm10) ) @
           (fun p => match p with 
                       | (_,(_,op)) => op
                     end %% operand_t).

  Definition ext_op_modrm2(bs:string) : parser operand_t :=
    (      (bits "00" $ bits bs $ rm00)
     |+|   (bits "01" $ bits bs $ rm01)
     |+|   (bits "10" $ bits bs $ rm10)
     |+|   (bits "11" $ bits bs $ rm11) ) @
           (fun p => match p with 
                       | (_,(_,op)) => op
                     end %% operand_t).

  (* My convention is to have EBX be a shadow of ESP, so you will
     want to run this instruction before all of your fuzzed instructions
  *)
  Definition MOV_ESP_to_EBX :=
    "1000" $$ "1001" $$ "1110" $$ bits "0011" @ 
      (fun _ => MOV true (Reg_op EBX) (Reg_op ESP) %% instruction_t).

Definition register_to_Z (r: register) :=
  match r with
    | EAX => 0
    | ECX => 1
    | EDX => 2
    | EBX => 3
    | ESP => 4
    | EBP => 5
    | ESI => 6
    | EDI => 7
  end.

Definition register_to_bools (r: register) := 
  let bs := Word.bits_of_Z 3 (register_to_Z r) in
    (bs 2) :: (bs 1) :: (bs 0) :: nil.

Fixpoint bitslist (bs: list bool) : parser unit_t :=
  match bs with
    | nil => Eps_p
    | b::bs' => Cat_p (Char_p b) (bitslist bs') @ (fun _ => tt %% unit_t)
  end.

  Definition verysmallword :=
    (byte $ "0000" $$ "0000" $$ "0000" $$ "0000" $$ "0000" $$ bits "0000") @ (fun p => let (p, _) := 
      p in zero_extend8_32 p %% word_t) |+|
    (byte $ "1111" $$ "1111" $$ "1111" $$ "1111" $$ "1111" $$ bits "1111") @ (fun p => let (p, _) := 
      p in zero_extend8_32 p %% word_t) .

  Definition MOV_smallimm_to_reg (r: register) :=
   "1100" $$ "0111" $$ "11" $$ "000" $$ bitslist (register_to_bools r) 
    $ verysmallword @ (fun p => match p with | (_,w) => 
                              MOV true  (Reg_op r) (Imm_op w) end %% instruction_t).

  Definition load_all_reg_smallimm :=
    let m := MOV_smallimm_to_reg in
      m EAX $ m ECX $ m EDX $ m ESI $ m EDI.

  Definition NOP :=
    "1001" $$ bits "0000" @ (fun _ => XCHG true (Reg_op EAX) (Reg_op EAX) %% instruction_t).

End X86_PARSER.


Import X86_PARSER_ARG.
Import X86_PARSER.
Import X86_BASE_PARSER.

(* This is basically stolen from CheckDeterminsitic, but I don't
   include the And_r constructor... you can't fuzz that *)

Inductive rexp : Type :=
| Any_r : rexp
| Char_r : char_p -> rexp
| Eps_r : rexp
| Cat_r : rexp -> rexp -> rexp
| Zero_r : rexp
| Alt_r : rexp -> rexp -> rexp
| Star_r : rexp -> rexp.


(* It's just better to strip out all of these maps and types
   from the beginning *)

Fixpoint parser2rexp {t} (p:parser t) : rexp :=
  match p with
    | Any_p => Any_r
    | Char_p c => Char_r c
    | Eps_p => Eps_r
    | Cat_p t1 t2 r1 r2 => Cat_r (parser2rexp r1) (parser2rexp r2)
    | Zero_p t => Zero_r
    | Alt_p t r1 r2 => Alt_r (parser2rexp r1) (parser2rexp r2)
    | Star_p t r => Star_r (parser2rexp r)
    | Map_p t1 t2 f r => parser2rexp r
  end.

 Record oracle := {
    oracle_num : nat -> nat;
    oracle_offset : nat
  }.

 Open Scope nat_scope.

  Definition RandMonad := StateMonad (oracle).
  Definition choose : ST oracle nat :=
    fun s => ({| oracle_num := oracle_num s;
                 oracle_offset := S (oracle_offset s)|},
             (oracle_num s) (oracle_offset s)).

  Open Scope monad_scope.

  Definition test_oracle := {| oracle_num := fun x => 27; oracle_offset := 0|}.

  Fixpoint rep (r: rexp) (n: nat) :=
    match n with
      | O => Eps_r
      | S n' => Cat_r r (rep r n')
    end.

  Require Import Coq.Arith.MinMax.
  Fixpoint starheight (r: rexp) :=
    match r with
      | Star_r r => S (starheight r)
      | Cat_r r1 r2 => max (starheight r1) (starheight r2)
      | Alt_r r1 r2 => max (starheight r1) (starheight r2)
      | _ => O
    end%nat.

  Lemma rep_samestarheight: forall n r, (starheight (rep r n) <= starheight r)%nat.
    intros. induction n. simpl; omega.
    simpl. apply max_l in IHn. rewrite IHn; auto.
  Qed.

  Fixpoint height (r: rexp) :=
    match r with
      | Star_r r => S (height r)
      | Cat_r r1 r2 => S (max (height r1) (height r2))
      | Alt_r r1 r2 => S (max (height r1) (height r2))
      | _ => O
    end%nat.

  Require Import Coq.Program.Wf.

  Definition lte_prod (p1 p2: nat * nat) := 
    lt (fst p1) (fst p2) \/ (le (fst p1) (fst p2) /\ lt (snd p1) (snd p2)).

  Theorem lt_Acc: forall n, Acc lt n.
  Proof.
    intros. induction n.
    econstructor. intros. inversion H.
    econstructor. intros.
    case (le_lt_or_eq _ _ H).
    intros.
    eapply Acc_inv. apply IHn. omega.
    intros. inversion H0; subst; auto. 
  Qed.

  Theorem lte_prod_Acc : forall n m, Acc lte_prod (n, m).
  Proof.
    induction n; induction m.
    econstructor. intros.
    unfold lte_prod in *; destruct H. inversion H.
    destruct H. inversion H0.
    econstructor. intros.
    unfold lte_prod in H. destruct H; [inversion H | ].
    destruct H. simpl in *.
    case (le_lt_or_eq _ _ H0).
    intros. eapply IHm. unfold lte_prod. right. split. auto.
    simpl; omega.
    intros. inversion H1; subst; auto. assert (fst y = O) by omega. 
    rewrite surjective_pairing. rewrite H2 in *. auto. 
    econstructor.
    intros. unfold lte_prod in H. destruct H.
    simpl in H.
    case (le_lt_or_eq _ _ H). intros.
    eapply Acc_inv. apply (IHn (snd y)).
    unfold lte_prod. left.
    simpl. omega.
    intros. inversion H0. 
    rewrite surjective_pairing. subst. auto.
    destruct H.
    simpl in *. inversion H0. 
    econstructor. intros.
    unfold lte_prod in H. destruct H.
    simpl in *.
    case (le_lt_or_eq _ _ H). intros.
    eapply Acc_inv. apply IHm.
    unfold lte_prod; left. simpl; omega.
    intros. inversion H0. subst. rewrite surjective_pairing. apply IHn. 
    simpl in *; destruct H.
    case (le_lt_or_eq _ _ H). intros.
    eapply Acc_inv. apply (IHn (S m)).
    unfold lte_prod. right. split. simpl. omega. simpl. auto. 
    intros.
    case (le_lt_or_eq _ _ H0). intros.
    eapply Acc_inv. apply IHm. unfold lte_prod. right.
    split; auto. simpl. omega.
    intros. inversion H2.
    subst.
    rewrite surjective_pairing. rewrite H1 in *. auto. 
  Qed.

  Theorem lte_prod_wf : well_founded lte_prod.
  Proof.
    split.
    destruct a.
    apply lte_prod_Acc.
  Qed.


  (* This takes in a regular expression, and instantiates 
     every (Star_r R) with R^n for some random n. *)
  Program Fixpoint destarify (r: rexp) {measure (starheight r, height r) (lte_prod)} :=
    match r with
      | Cat_r r1 r2 => r1f <- destarify r1;
                       r2f <- destarify r2;
                       ret Cat_r r1f r2f
      | Alt_r r1 r2 => r1f <- destarify r1;
                       r2f <- destarify r2;
                       ret Alt_r r1f r2f
      | Star_r r => count <- choose;
                    destarify (rep r count)
      | _ => ret r
    end.
  Obligation 1.
    unfold lte_prod; simpl; right; split; auto with *. Defined.
  Obligation 2.
    unfold lte_prod; simpl; right; split; auto with *. Defined.
  Obligation 3.
    unfold lte_prod; simpl; right; split; auto with *. Defined.
  Obligation 4.
    unfold lte_prod; simpl; right; split; auto with *. Defined.
  Obligation 5.
    unfold lte_prod; simpl; left;
    specialize (rep_samestarheight count r0); intros; omega. Defined.
  Obligation 6.
    repeat split; intros; discriminate. Defined.
  Obligation 7.
    repeat split; intros; discriminate. Defined.
  Obligation 8.
    repeat split; intros; discriminate. Defined.
  Obligation 9.
    repeat split; intros; discriminate. Defined.
  Obligation 10.
    eapply measure_wf.
    eapply lte_prod_wf.
  Defined.

  Open Local Scope Z_scope.
  Fixpoint altlen (r: rexp) :=
    match r with
      | Alt_r r1 r2 => S (altlen r2)
      | _ => O
    end.
  
  Fixpoint altdepth (r: rexp) :=
    match r with
      | Alt_r r1 r2 => altdepth r1 + altdepth r2
      | _ => 1
    end%nat.

  Definition choose_lt (n: nat) :=
    c <- choose;
    ret Zabs_nat ((Z_of_nat c) mod (Z_of_nat n)).

  Definition prob_k_of_nat (k n: nat) :=
    c <- choose_lt n;
    if lt_dec c k then
      ret true
    else
      ret false.
  
  Eval compute in altdepth (Alt_r (Alt_r (Char_r true) (Char_r true)) (Char_r true)).

  Fixpoint choosealt (r: rexp) (choice: nat) :=
    match r with
      | Alt_r r1 r2 => choice <- prob_k_of_nat (altdepth r1) (altdepth r);
                       if choice then
                         ret r1
                       else 
                         ret r2
      | _ => ret r
   end.

  Program Fixpoint fuzz_aux (r: rexp) (altcount : option nat)  
    {measure (starheight r, height r) (lte_prod)}  :=
    match r with
      | Any_r => c1 <- choose;
                 ret (if Z_eq_dec 0 ((Z_of_nat c1) mod 2) then
                   true::nil
                 else
                   false::nil)
      | Char_r c => ret (c::nil)
      | Eps_r => ret (nil)
      | Zero_r => ret (nil)    (* So... this isn't quite right. *)
      | Cat_r p1 p2 => v1 <- fuzz_aux p1 None;
                       v2 <- fuzz_aux p2 None;
                       ret (v1 ++ v2)
      (* This is the tricky part. We don't want to choose between
         p1 and p2 with equal probability. Why? Usually when writing
         out parsers, we will do something like p1 |+| p2 |+| p3 |+| p4.
         This parenthesizes into p1 |+| (p2 |+| (p3 |+| p4)), so this
         naive thing will heavily bias p1, which is not what we usually want *)
(*      | Alt_r  p1 p2 => match altcount with
                          | Some n => if eq_nat_dec n O then
                                         fuzz_aux p1 None
                                      else
                                         fuzz_aux p2 (Some (n - 1))%nat
                          | None => let altlen := altlen (Alt_r p1 p2) in
                                     c1 <- choose;
                                     if Z_eq_dec 0 (Z_of_nat c1 mod (Z_of_nat (altlen + 1))) then
                                       fuzz_aux p1 None
                                     else
                                       fuzz_aux p2 (Some (Zabs_nat (Z_of_nat c1 mod (Z_of_nat altlen))))
                       
                        end*)
     (* | Alt_r p1 p2 => c <- choose;
                       let p := choosealt (Alt_r p1 p2) (Zabs_nat ((Z_of_nat c) 
                         mod (Z_of_nat (altlen (Alt_r p1 p2) + 1)))) in
                       fuzz_aux p None*)
      | Alt_r r1 r2 => choice <- prob_k_of_nat (altdepth r1) (altdepth r);
                       if choice then
                         fuzz_aux r1 None
                       else 
                         fuzz_aux r2 None
      | Star_r p => count <- choose;
                      fuzz_aux (rep p count) None
    end.
  Obligation 1.
    unfold lte_prod; simpl; right; split; auto with *. Qed.
  Obligation 2.
    unfold lte_prod; simpl; right; split; auto with *. Qed.
  Obligation 3. 
    unfold lte_prod; simpl; right; split; auto with *. Qed.
  Obligation 4.
    unfold lte_prod; simpl; right; split; auto with *. Qed.
  Obligation 5.
    unfold lte_prod; simpl; left.
    specialize (rep_samestarheight count p); intros; omega. Qed.
  Obligation 6.
    eapply measure_wf.
    eapply lte_prod_wf.
  Defined.

  Definition fuzz r := fuzz_aux r None.
  Definition fuzz_p {t} (p: parser t) := fuzz (parser2rexp p).
