Require Import ParserArg.

(* Grammar should be parametrized by a PARSER_ARG module; however, that
   would impede code extraction because of a Coq bug.  Instead, we
   introduce a bunch of definitions below to achieve some separation as
   long as we never directly use definitions in X86_PARSER_ARG *)
Definition char_p := X86_PARSER_ARG.char_p.
Definition char_dec := X86_PARSER_ARG.char_dec.
Definition user_type := X86_PARSER_ARG.user_type.
Definition user_type_dec := X86_PARSER_ARG.user_type_dec.
Definition user_type_denote := X86_PARSER_ARG.user_type_denote.
Definition token_id := X86_PARSER_ARG.token_id.
Definition num_tokens := X86_PARSER_ARG.num_tokens.
Definition token_id_to_chars := X86_PARSER_ARG.token_id_to_chars.

(** The [type]s for our grammars. *)
Inductive type : Type := 
| Unit_t : type
| Char_t : type
| Void_t : type
| Pair_t : type -> type -> type
| Sum_t : type -> type -> type
| List_t : type -> type
| Option_t : type -> type
| User_t : user_type -> type.

(** [void] is an empty type. *)
Inductive void : Type := .

(** The interpretation of [type]s as Coq [Type]s. *)
Fixpoint interp (t:type) : Type := 
  match t with 
    | Unit_t => unit
    | Char_t => char_p
    | Void_t => void
    | Pair_t t1 t2 => (interp t1) * (interp t2)
    | Sum_t t1 t2 => (interp t1) + (interp t2)
    | List_t t => list (interp t)
    | Option_t t => option (interp t)
    | User_t t => user_type_denote t
  end%type.
