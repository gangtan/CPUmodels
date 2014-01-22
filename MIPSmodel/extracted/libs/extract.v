Require Import X86Semantics.
Require Import Reals.
Extraction Blacklist String List.
Set Extraction AccessOpaque.
Extract Constant R => "unit".
Extract Constant Rplus => "let rec loop x y = loop x y in loop".
Extract Constant Rmult => "let rec loop x y = loop x y in loop".
Extract Constant Ropp => "let rec loop x = loop x in loop".
Extract Constant Rinv => "let rec loop x = loop x in loop".
Extract Constant total_order_T => "let rec loop x y = loop x y in loop".
Extract Constant R0 => "()".
Extract Constant R1 => "()".
(*Recursive Extraction Decode.X86_PARSER.opt_initial_decoder_state.*)
Recursive Extraction X86Semantics.step.
