Require Import X86Semantics.

(* Flocq defines functions that either return reals or take them as parameters.
   We don't use these, but when extracting, Coq will extract the
axiomatization of the Reals, which will result in unrealized axioms that will
raise exceptions. The following eliminates this problem. *)
   
Extract Inlined Constant Fappli_IEEE.FF2R => "fun _ _ -> assert false".
Extract Inlined Constant Fappli_IEEE.B2R => "fun _ _ _ -> assert false".
Extract Inlined Constant Fappli_IEEE.round_mode => "fun _ _ -> assert false".
Extract Inlined Constant Fcalc_bracket.inbetween_loc => "fun _ _ _ -> assert false".
Extract Inlined Constant Fcore_defs.F2R => "fun _ _ -> assert false".
Extract Inlined Constant Fcore_generic_fmt.canonic_exp => "fun _ _ _ => assert false".
Extract Inlined Constant Fcore_generic_fmt.scaled_mantissa => "fun _ _ _ => assert false".

Extraction Blacklist String List. 

Recursive Extraction Library X86Semantics.
