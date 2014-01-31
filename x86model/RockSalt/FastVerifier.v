(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)


Require Import Coqlib.
Require Import Parser.
Require Import List.
Require Import Bits.
Require Import Decode.
Require Import X86Syntax.
Require Import Recognizer.
Require Import Int32.
Require Import VerifierDFA.

Import X86_PARSER_ARG.
Import X86_PARSER.
(* Import X86_BASE_PARSER. *)

Require Coq.MSets.MSetAVL.
Require Coq.Structures.OrdersAlt.
Require Coq.MSets.MSetFacts.
Module New_Int32_OT := (Coq.Structures.OrdersAlt.Update_OT Int32_OT).
Module Int32Set := Coq.MSets.MSetAVL.Make New_Int32_OT.

Definition n_shift_add (b: bool) (x: nat) :=
  (if b then 2 * x + 1 else 2 * x)%nat.

Open Scope Z_scope.

Fixpoint n_of_bits (n: nat) (f: Z -> bool) {struct n}: nat :=
  match n with
  | O => O
  | S m => n_shift_add (f 0) (n_of_bits m (fun i => f (i + 1)))
  end.

(* Maybe tokens as nats isn't best... *)
Definition byte2token (b: int8) : token_id := Zabs_nat (Word.unsigned b).
Definition token2byte (t: token_id) : int8 := Word.repr (Z_of_nat t).

Section BUILT_DFAS.

  (* In this section we will just assume the DFAs are all built;
     that is, non_cflow_dfa should be the result of "make_dfa non_cflow_parser" and
     similarly for dir_cflow_dfa and nacljmp_dfa *)
  Variable non_cflow_dfa : Recognizer.DFA.
  Variable dir_cflow_dfa : Recognizer.DFA.
  Variable nacljmp_dfa : Recognizer.DFA.

  Variable initial_state : ParseState_t.

  (* G.T.: may be a good idea to parametrize the DFA w.r.t. the ChunkSize;
     Google's verifier allows it either to be 16 or 32.
   Parameters logChunkSize:nat.
   Hypothesis logChunkSize_range : (0 < logChunkSize <= Word.wordsize 31)%nat.
  *)

  Fixpoint parseloop (ps: ParseState_t) (bytes:list int8) : 
    option ((prefix * instr) * list int8) := 
    match bytes with 
      | nil => None
      | b::bs => match parse_byte ps b with 
                   | (ps',nil) => parseloop ps' bs
                   | (_, v::_) => Some (v,bs)
                 end
    end.

  Definition extract_disp (bytes: list int8) :=
    match (parseloop initial_state bytes) with
      | Some ((_, JMP true false (Imm_op disp) None), _) => Some disp
      | Some ((_, Jcc ct disp), _) => Some disp
      | Some ((_, CALL true false (Imm_op disp) None), _) => Some disp
      | _ => None
    end.


  (* Note: it's important to specify the type of tokens as "list token_id", not
     "list nat", even though token_id is defined to be nat. If a proof environment
     has one value of type "list token_id" and the other of type "list nat", 
     proof scripts such as rewrite or omega may fail since token_id needs to
     be unfolded. *)
  Fixpoint process_buffer_aux (loc: int32) (n: nat) (tokens:list token_id) 
    (curr_res: Int32Set.t * Int32Set.t) :=
    let (start_instrs, check_list) := curr_res in
      match tokens with
        | nil => Some curr_res
        | _ => (* There are left over bytes in the buffer *)
          match n with
            | O => None 
            | S m =>
              match (dfa_recognize non_cflow_dfa tokens,
                dfa_recognize dir_cflow_dfa tokens,
                dfa_recognize nacljmp_dfa tokens) with
                | (Some (len, remaining), None, None) => 
                  process_buffer_aux (loc +32_n len) m remaining
                  (Int32Set.add loc start_instrs, check_list)

                | (None, Some (len, remaining), None) => 
                  match extract_disp (List.map token2byte (firstn len tokens)) with
                    | None => None
                    | Some disp => 
                      process_buffer_aux (loc +32_n len) m remaining 
                      (Int32Set.add loc start_instrs,
                        Int32Set.add (loc +32_n len +32 disp) check_list)
                  end
                | (Some res0, None, Some (len, remaining)) => 
                  process_buffer_aux (loc +32_n len) m remaining
                  (Int32Set.add loc start_instrs, check_list)
                | _ => None (* None of the DFAs matched or too many DFAs matched *)
              end
          end
      end.

  (* The idea here is, given a list of int8s representing the code,
     we call process_buffer_aux with n := length of the list;
     since each instruction is at least one byte long, this should
     be enough calls to process_buffer_aux to process everything in 
     the buffer, without us having to worry about termination proofs
     Note: one way to avoid the n is would be to show each dfa consumes
     at least one byte.
     *)
  Definition process_buffer (buffer: list int8) :=
    process_buffer_aux (Word.repr 0) (length buffer) (List.map byte2token buffer) 
     (Int32Set.empty, Int32Set.empty).

  Definition aligned_bool (a:int32):bool := 
    Zeq_bool (Zmod (unsigned a) chunkSize) 0.
  Definition aligned (a:int32) := aligned_bool a = true.

  (* This calls process_buffer. If that returns a None, then the
     program is not safe. If process_buffer returns a set of start
     addresses and known jump addresses, then we need to check that
     any address in the jump addresses which is not in the start addresses
     is aligned. This is done by taking the set difference of check_addrs
     and start_addrs, filtering check_addrs for all of the aligned addresses
     and then checking that the filtering process doesn't remove anything
     (Perhaps it's faster to do a filter on the negation of aligned_bool
     and then check that the result is empty).

     We also check that the number of aligned start_addrs
     is equal to the number of aligned addresses we should have if
     this code segment is loaded at an aligned address.

     The count of the number of aligned addresses could be done in the
     process_buffer loop, but I didn't want to complicate the logic
     there any more.  *)

  Require Import Recdef.
  Function checkAligned_aux (p: Int32Set.t * Z * nat) {measure snd p}
    : bool :=
  match p with
    | (_, 0%nat) => true
    | ((startAddrs, next), len) =>
      (Int32Set.mem (repr next) startAddrs &&
       checkAligned_aux (startAddrs, (next + chunkSize), 
                            (len - Zabs_nat chunkSize)%nat))
  end.
  intros. simpl. omega.
  Defined.                          

  (* checking that all aligned addresses between 0 and len is in startAddrs *)
  Definition checkAligned (startAddrs:Int32Set.t) (len: nat) :bool :=
    checkAligned_aux (startAddrs, 0, len).

  (* checking all jump targets are either in startAddrs or are aligned addresses *)
  Definition checkJmpTargets (jmpTargets startAddrs: Int32Set.t) := 
    let check_start_diff := Int32Set.diff jmpTargets startAddrs in
      Int32Set.for_all aligned_bool check_start_diff.
      
  Definition checkProgram (buffer: list int8) : (bool * Int32Set.t) :=
    match process_buffer buffer with
      | None => (false, Int32Set.empty)
      | Some (start_addrs, check_addrs) => 
        let check_start_diff := Int32Set.diff check_addrs start_addrs in
          (andb (checkAligned start_addrs (length buffer))
            (checkJmpTargets check_addrs start_addrs),
           start_addrs)
    end.

End BUILT_DFAS.

Definition ncflow := make_dfa non_cflow_grammar.
Definition dbranch := make_dfa (alts dir_cflow).
Definition ibranch := make_dfa (alts nacljmp_mask).

(*Extraction "fastverif.ml" checkProgram ncflow dbranch ibranch.*)
