(* Extract an OCaml decoder from the Coq x86 model *)

(* Map nat to OCaml big_int *)
Require ExtrOcamlNatBigInt.
(* Map Z and pos to OCaml big_int *)
Require ExtrOcamlZBigInt.

(* bypassing the extraction of opaque constants *)
Set Extraction AccessOpaque.

Extract Inductive sigT => "(*)"  [ "(,)" ].

Require Import Decode. 
Extraction Blacklist String List. 
Recursive Extraction Library Decode.

(* Require Import NewDecode.  *)
(* Recursive Extraction Library NewDecode. *)

Require Import Encode. 
Recursive Extraction Library Encode.

(* Require Import ElfDecode. 
Recursive Extraction Library ElfDecode.
*)
