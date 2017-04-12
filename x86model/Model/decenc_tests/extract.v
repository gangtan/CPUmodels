(* Extract an OCaml x86 model from the Coq x86 model *)

Require ExtrOcamlString.

(* Map nat to OCaml big_int *)
Require ExtrOcamlNatBigInt.

(* fix bug in Require ExtrOcamlNatBigInt: missing the outer parentheses *)
Extract Constant minus => "(fun n m -> Big.max Big.zero (Big.sub n m))".

(* Map Z and pos to OCaml big_int *)
Require ExtrOcamlZBigInt.

(* bypassing the extraction of opaque constants *)
Set Extraction AccessOpaque.

Extract Inductive sigT => "(*)"  [ "(,)" ].

Require Import X86Model.X86BG.
(* Require Import X86Model.Decode. *)
Require Import X86Model.Parser.
Require X86Model.X86Semantics.
Extraction Blacklist String List. 
Require Encode.

Set Extraction Optimize.
Set Extraction AutoInline.

(* without this, some files will use an extracted Nat module, which conflicts with
    Ocaml's default Nat module *)
Extraction Blacklist Nat.

(* Did not extract X86Semantics.step below since that would call
   build_dfa on the instruction grammar, which would take
   approximately 2 minutes.  One way of avoiding this is to change the
   definition of X86Semantics.step to be parameterized by a dfa
   builder, similar to how initial_parse_state' does it; that way, the
   client can supply a dfa builder that just deserializes the dfa from
   a file, isntead of building it from scratch. *)

Separate Extraction initial_parser_state parse_tokens
  vinitial_parser_state vparse_tokens
  initial_naive_parser_state naive_parse_token
  (* instruction_grammar *)
  instr_bigrammar BiGrammar.bigrammar_to_grammar
  X86Semantics.X86_Compile.instr_to_rtl
  Encode.x86_encode (* encoder from the bigrammar *)
  Encode.enc_pre_instr_bytes (* a manual encoder *)
  .

(* Separate Extraction initial_parser_state parse_tokens *)
(*   vinitial_parser_state vparse_tokens *)
(*   initial_naive_parser_state naive_parse_token *)
(*   instruction_grammar X86Semantics.X86_Compile.instr_to_rtl. *)

(* Separate Extraction build_dfa dfa_recognize par2rec X86_PARSER.instr_grammar. *)

(* Extraction "recognizer.ml" build_dfa dfa_recognize par2rec . *)
