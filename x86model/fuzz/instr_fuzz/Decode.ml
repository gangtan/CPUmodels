open BinInt
open Bits
open Bool
open Datatypes
open List0
open Specif
open String0
open X86Syntax

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module X86_PARSER_ARG = 
 struct 
  type char_p = bool
  
  (** val char_eq : char_p -> char_p -> bool **)
  
  let char_eq =
    bool_dec
  
  type coq_type =
  | Int_t
  | Register_t
  | Byte_t
  | Half_t
  | Word_t
  | Double_Word_t
  | Ten_Byte_t
  | Scale_t
  | Condition_t
  | Address_t
  | Operand_t
  | Fpu_Register_t
  | Fp_Status_Register_t
  | Fp_Control_Register_t
  | Fp_TagWord_Register_t
  | Fp_LastOperPtr_Register_t
  | Fp_LastInstrPtr_Register_t
  | Fp_Opcode_Register_t
  | Fpu_TagWords_t
  | Fp_Debug_Register_t
  | Fp_Operand_t
  | MMX_Granularity_t
  | MMX_Register_t
  | MMX_Operand_t
  | SSE_Register_t
  | SSE_Operand_t
  | Instruction_t
  | Control_Register_t
  | Debug_Register_t
  | Segment_Register_t
  | Lock_or_Rep_t
  | Bool_t
  | Prefix_t
  | Option_t of coq_type
  | Pair_t of coq_type * coq_type
  
  (** val type_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> (coq_type -> 'a1 -> 'a1) -> (coq_type -> 'a1 ->
      coq_type -> 'a1 -> 'a1) -> coq_type -> 'a1 **)
  
  let rec type_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 = function
  | Int_t -> f
  | Register_t -> f0
  | Byte_t -> f1
  | Half_t -> f2
  | Word_t -> f3
  | Double_Word_t -> f4
  | Ten_Byte_t -> f5
  | Scale_t -> f6
  | Condition_t -> f7
  | Address_t -> f8
  | Operand_t -> f9
  | Fpu_Register_t -> f10
  | Fp_Status_Register_t -> f11
  | Fp_Control_Register_t -> f12
  | Fp_TagWord_Register_t -> f13
  | Fp_LastOperPtr_Register_t -> f14
  | Fp_LastInstrPtr_Register_t -> f15
  | Fp_Opcode_Register_t -> f16
  | Fpu_TagWords_t -> f17
  | Fp_Debug_Register_t -> f18
  | Fp_Operand_t -> f19
  | MMX_Granularity_t -> f20
  | MMX_Register_t -> f21
  | MMX_Operand_t -> f22
  | SSE_Register_t -> f23
  | SSE_Operand_t -> f24
  | Instruction_t -> f25
  | Control_Register_t -> f26
  | Debug_Register_t -> f27
  | Segment_Register_t -> f28
  | Lock_or_Rep_t -> f29
  | Bool_t -> f30
  | Prefix_t -> f31
  | Option_t t0 ->
    f32 t0
      (type_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        t0)
  | Pair_t (t1, t2) ->
    f33 t1
      (type_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        t1) t2
      (type_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        t2)
  
  (** val type_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> (coq_type -> 'a1 -> 'a1) -> (coq_type -> 'a1 ->
      coq_type -> 'a1 -> 'a1) -> coq_type -> 'a1 **)
  
  let rec type_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 = function
  | Int_t -> f
  | Register_t -> f0
  | Byte_t -> f1
  | Half_t -> f2
  | Word_t -> f3
  | Double_Word_t -> f4
  | Ten_Byte_t -> f5
  | Scale_t -> f6
  | Condition_t -> f7
  | Address_t -> f8
  | Operand_t -> f9
  | Fpu_Register_t -> f10
  | Fp_Status_Register_t -> f11
  | Fp_Control_Register_t -> f12
  | Fp_TagWord_Register_t -> f13
  | Fp_LastOperPtr_Register_t -> f14
  | Fp_LastInstrPtr_Register_t -> f15
  | Fp_Opcode_Register_t -> f16
  | Fpu_TagWords_t -> f17
  | Fp_Debug_Register_t -> f18
  | Fp_Operand_t -> f19
  | MMX_Granularity_t -> f20
  | MMX_Register_t -> f21
  | MMX_Operand_t -> f22
  | SSE_Register_t -> f23
  | SSE_Operand_t -> f24
  | Instruction_t -> f25
  | Control_Register_t -> f26
  | Debug_Register_t -> f27
  | Segment_Register_t -> f28
  | Lock_or_Rep_t -> f29
  | Bool_t -> f30
  | Prefix_t -> f31
  | Option_t t0 ->
    f32 t0
      (type_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        t0)
  | Pair_t (t1, t2) ->
    f33 t1
      (type_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        t1) t2
      (type_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
        t2)
  
  type tipe = coq_type
  
  (** val tipe_eq : tipe -> tipe -> bool **)
  
  let rec tipe_eq t t0 =
    match t with
    | Int_t ->
      (match t0 with
       | Int_t -> true
       | _ -> false)
    | Register_t ->
      (match t0 with
       | Register_t -> true
       | _ -> false)
    | Byte_t ->
      (match t0 with
       | Byte_t -> true
       | _ -> false)
    | Half_t ->
      (match t0 with
       | Half_t -> true
       | _ -> false)
    | Word_t ->
      (match t0 with
       | Word_t -> true
       | _ -> false)
    | Double_Word_t ->
      (match t0 with
       | Double_Word_t -> true
       | _ -> false)
    | Ten_Byte_t ->
      (match t0 with
       | Ten_Byte_t -> true
       | _ -> false)
    | Scale_t ->
      (match t0 with
       | Scale_t -> true
       | _ -> false)
    | Condition_t ->
      (match t0 with
       | Condition_t -> true
       | _ -> false)
    | Address_t ->
      (match t0 with
       | Address_t -> true
       | _ -> false)
    | Operand_t ->
      (match t0 with
       | Operand_t -> true
       | _ -> false)
    | Fpu_Register_t ->
      (match t0 with
       | Fpu_Register_t -> true
       | _ -> false)
    | Fp_Status_Register_t ->
      (match t0 with
       | Fp_Status_Register_t -> true
       | _ -> false)
    | Fp_Control_Register_t ->
      (match t0 with
       | Fp_Control_Register_t -> true
       | _ -> false)
    | Fp_TagWord_Register_t ->
      (match t0 with
       | Fp_TagWord_Register_t -> true
       | _ -> false)
    | Fp_LastOperPtr_Register_t ->
      (match t0 with
       | Fp_LastOperPtr_Register_t -> true
       | _ -> false)
    | Fp_LastInstrPtr_Register_t ->
      (match t0 with
       | Fp_LastInstrPtr_Register_t -> true
       | _ -> false)
    | Fp_Opcode_Register_t ->
      (match t0 with
       | Fp_Opcode_Register_t -> true
       | _ -> false)
    | Fpu_TagWords_t ->
      (match t0 with
       | Fpu_TagWords_t -> true
       | _ -> false)
    | Fp_Debug_Register_t ->
      (match t0 with
       | Fp_Debug_Register_t -> true
       | _ -> false)
    | Fp_Operand_t ->
      (match t0 with
       | Fp_Operand_t -> true
       | _ -> false)
    | MMX_Granularity_t ->
      (match t0 with
       | MMX_Granularity_t -> true
       | _ -> false)
    | MMX_Register_t ->
      (match t0 with
       | MMX_Register_t -> true
       | _ -> false)
    | MMX_Operand_t ->
      (match t0 with
       | MMX_Operand_t -> true
       | _ -> false)
    | SSE_Register_t ->
      (match t0 with
       | SSE_Register_t -> true
       | _ -> false)
    | SSE_Operand_t ->
      (match t0 with
       | SSE_Operand_t -> true
       | _ -> false)
    | Instruction_t ->
      (match t0 with
       | Instruction_t -> true
       | _ -> false)
    | Control_Register_t ->
      (match t0 with
       | Control_Register_t -> true
       | _ -> false)
    | Debug_Register_t ->
      (match t0 with
       | Debug_Register_t -> true
       | _ -> false)
    | Segment_Register_t ->
      (match t0 with
       | Segment_Register_t -> true
       | _ -> false)
    | Lock_or_Rep_t ->
      (match t0 with
       | Lock_or_Rep_t -> true
       | _ -> false)
    | Bool_t ->
      (match t0 with
       | Bool_t -> true
       | _ -> false)
    | Prefix_t ->
      (match t0 with
       | Prefix_t -> true
       | _ -> false)
    | Option_t t1 ->
      (match t0 with
       | Option_t t2 -> tipe_eq t1 t2
       | _ -> false)
    | Pair_t (t1, t2) ->
      (match t0 with
       | Pair_t (t4, t5) -> if tipe_eq t1 t4 then tipe_eq t2 t5 else false
       | _ -> false)
  
  type tipe_m = __
 end

module X86_PARSER = 
 struct 
  module X86_BASE_PARSER = Parser.Parser(X86_PARSER_ARG)
  
  (** val option_t : X86_PARSER_ARG.coq_type -> X86_BASE_PARSER.result **)
  
  let option_t x =
    X86_BASE_PARSER.Coq_tipe_t (X86_PARSER_ARG.Option_t x)
  
  (** val int_t : X86_BASE_PARSER.result **)
  
  let int_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Int_t
  
  (** val register_t : X86_BASE_PARSER.result **)
  
  let register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Register_t
  
  (** val byte_t : X86_BASE_PARSER.result **)
  
  let byte_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Byte_t
  
  (** val half_t : X86_BASE_PARSER.result **)
  
  let half_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Half_t
  
  (** val word_t : X86_BASE_PARSER.result **)
  
  let word_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Word_t
  
  (** val double_word_t : X86_BASE_PARSER.result **)
  
  let double_word_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Double_Word_t
  
  (** val ten_byte_t : X86_BASE_PARSER.result **)
  
  let ten_byte_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Ten_Byte_t
  
  (** val scale_t : X86_BASE_PARSER.result **)
  
  let scale_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Scale_t
  
  (** val condition_t : X86_BASE_PARSER.result **)
  
  let condition_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Condition_t
  
  (** val fpu_register_t : X86_BASE_PARSER.result **)
  
  let fpu_register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Fpu_Register_t
  
  (** val fp_status_register_t : X86_BASE_PARSER.result **)
  
  let fp_status_register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Fp_Status_Register_t
  
  (** val fp_control_register_t : X86_BASE_PARSER.result **)
  
  let fp_control_register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Fp_Control_Register_t
  
  (** val fp_tagWord_register_t : X86_BASE_PARSER.result **)
  
  let fp_tagWord_register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Fp_TagWord_Register_t
  
  (** val fp_lastOperPtr_register_t : X86_BASE_PARSER.result **)
  
  let fp_lastOperPtr_register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Fp_LastOperPtr_Register_t
  
  (** val fp_lastInstrPtr_register_t : X86_BASE_PARSER.result **)
  
  let fp_lastInstrPtr_register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Fp_LastInstrPtr_Register_t
  
  (** val fp_opcode_register_t : X86_BASE_PARSER.result **)
  
  let fp_opcode_register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Fp_Opcode_Register_t
  
  (** val fpu_tagWords_t : X86_BASE_PARSER.result **)
  
  let fpu_tagWords_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Fpu_TagWords_t
  
  (** val fp_debug_register_t : X86_BASE_PARSER.result **)
  
  let fp_debug_register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Fp_Debug_Register_t
  
  (** val mmx_granularity_t : X86_BASE_PARSER.result **)
  
  let mmx_granularity_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.MMX_Granularity_t
  
  (** val mmx_operand_t : X86_BASE_PARSER.result **)
  
  let mmx_operand_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.MMX_Operand_t
  
  (** val mmx_register_t : X86_BASE_PARSER.result **)
  
  let mmx_register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.MMX_Register_t
  
  (** val sse_operand_t : X86_BASE_PARSER.result **)
  
  let sse_operand_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.SSE_Operand_t
  
  (** val sse_register_t : X86_BASE_PARSER.result **)
  
  let sse_register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.SSE_Register_t
  
  (** val address_t : X86_BASE_PARSER.result **)
  
  let address_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Address_t
  
  (** val operand_t : X86_BASE_PARSER.result **)
  
  let operand_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Operand_t
  
  (** val fp_operand_t : X86_BASE_PARSER.result **)
  
  let fp_operand_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Fp_Operand_t
  
  (** val instruction_t : X86_BASE_PARSER.result **)
  
  let instruction_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Instruction_t
  
  (** val control_register_t : X86_BASE_PARSER.result **)
  
  let control_register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Control_Register_t
  
  (** val debug_register_t : X86_BASE_PARSER.result **)
  
  let debug_register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Debug_Register_t
  
  (** val segment_register_t : X86_BASE_PARSER.result **)
  
  let segment_register_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Segment_Register_t
  
  (** val lock_or_rep_t : X86_BASE_PARSER.result **)
  
  let lock_or_rep_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Lock_or_Rep_t
  
  (** val bool_t : X86_BASE_PARSER.result **)
  
  let bool_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Bool_t
  
  (** val prefix_t : X86_BASE_PARSER.result **)
  
  let prefix_t =
    X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Prefix_t
  
  (** val bit : bool -> X86_BASE_PARSER.coq_parser **)
  
  let bit x =
    X86_BASE_PARSER.Char_p x
  
  (** val never : X86_BASE_PARSER.result -> X86_BASE_PARSER.coq_parser **)
  
  let never t =
    X86_BASE_PARSER.Zero_p t
  
  (** val always :
      X86_BASE_PARSER.result -> X86_BASE_PARSER.result_m ->
      X86_BASE_PARSER.coq_parser **)
  
  let always t x =
    X86_BASE_PARSER.Map_p (X86_BASE_PARSER.Coq_unit_t, t, (fun x0 -> x),
      X86_BASE_PARSER.Eps_p)
  
  (** val alt :
      X86_BASE_PARSER.result -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser **)
  
  let alt t p1 p2 =
    X86_BASE_PARSER.Alt_p (t, p1, p2)
  
  (** val alts :
      X86_BASE_PARSER.result -> X86_BASE_PARSER.coq_parser list ->
      X86_BASE_PARSER.coq_parser **)
  
  let alts t ps =
    fold_right (alt t) (never t) ps
  
  (** val map :
      X86_BASE_PARSER.result -> X86_BASE_PARSER.result ->
      X86_BASE_PARSER.coq_parser -> (X86_BASE_PARSER.result_m ->
      X86_BASE_PARSER.result_m) -> X86_BASE_PARSER.coq_parser **)
  
  let map t1 t2 p f =
    X86_BASE_PARSER.Map_p (t1, t2, f, p)
  
  (** val seq :
      X86_BASE_PARSER.result -> X86_BASE_PARSER.result ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser **)
  
  let seq t1 t2 p1 p2 =
    X86_BASE_PARSER.Cat_p (t1, t2, p1, p2)
  
  (** val cons : X86_BASE_PARSER.result -> (__ * __ list) -> __ list **)
  
  let cons t pair =
    (fst pair) :: (snd pair)
  
  (** val seqs :
      X86_BASE_PARSER.result -> X86_BASE_PARSER.coq_parser list ->
      X86_BASE_PARSER.coq_parser **)
  
  let seqs t ps =
    fold_right (fun p1 p2 ->
      map (X86_BASE_PARSER.Coq_pair_t (t, (X86_BASE_PARSER.Coq_list_t t)))
        (X86_BASE_PARSER.Coq_list_t t)
        (seq t (X86_BASE_PARSER.Coq_list_t t) p1 p2) (Obj.magic (cons t)))
      (always (X86_BASE_PARSER.Coq_list_t t) (Obj.magic [])) ps
  
  (** val string_to_bool_list : char list -> bool list **)
  
  let rec string_to_bool_list = function
  | [] -> []
  | a::s0 -> (if (=) a '0' then false else true) :: (string_to_bool_list s0)
  
  (** val bits_n : Big.big_int -> X86_BASE_PARSER.result **)
  
  let rec bits_n n =
    Big.nat_case
      (fun _ ->
      X86_BASE_PARSER.Coq_unit_t)
      (fun n0 -> X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
      (bits_n n0)))
      n
  
  (** val field' : Big.big_int -> X86_BASE_PARSER.coq_parser **)
  
  let rec field' n =
    Big.nat_case
      (fun _ ->
      X86_BASE_PARSER.Eps_p)
      (fun n0 -> X86_BASE_PARSER.Cat_p (X86_BASE_PARSER.Coq_char_t,
      (bits_n n0), X86_BASE_PARSER.Any_p,
      (field' n0)))
      n
  
  (** val bits2Z :
      Big.big_int -> Big.big_int -> X86_BASE_PARSER.result_m ->
      X86_BASE_PARSER.result_m **)
  
  let rec bits2Z n a x =
    Big.nat_case
      (fun _ ->
      Obj.magic a)
      (fun n0 ->
      bits2Z n0
        (Z.add (Z.mul (Big.double Big.one) a)
          (if fst (Obj.magic x) then Big.one else Big.zero))
        (snd (Obj.magic x)))
      n
  
  (** val bits2int :
      Big.big_int -> X86_BASE_PARSER.result_m -> X86_BASE_PARSER.result_m **)
  
  let bits2int n bs =
    bits2Z n Big.zero bs
  
  (** val bits : char list -> X86_BASE_PARSER.coq_parser **)
  
  let rec bits = function
  | [] -> X86_BASE_PARSER.Eps_p
  | c::s ->
    X86_BASE_PARSER.Cat_p (X86_BASE_PARSER.Coq_char_t, (bits_n (length s)),
      (X86_BASE_PARSER.Char_p (if (=) c '0' then false else true)), (bits s))
  
  (** val bitsleft :
      X86_BASE_PARSER.result -> char list -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser **)
  
  let bitsleft t s p =
    map (X86_BASE_PARSER.Coq_pair_t ((bits_n (length s)), t)) t
      (seq (bits_n (length s)) t (bits s) p) (Obj.magic snd)
  
  (** val anybit : X86_BASE_PARSER.coq_parser **)
  
  let anybit =
    X86_BASE_PARSER.Any_p
  
  (** val field : Big.big_int -> X86_BASE_PARSER.coq_parser **)
  
  let field n =
    map (bits_n n) int_t (field' n) (bits2int n)
  
  (** val reg : X86_BASE_PARSER.coq_parser **)
  
  let reg =
    map int_t register_t (field (Big.succ (Big.succ (Big.succ Big.zero))))
      (Obj.magic coq_Z_to_register)
  
  (** val fpu_reg : X86_BASE_PARSER.coq_parser **)
  
  let fpu_reg =
    map int_t fpu_register_t
      (field (Big.succ (Big.succ (Big.succ Big.zero))))
      (Obj.magic (Word.repr (Big.succ (Big.succ Big.zero))))
  
  (** val mmx_reg : X86_BASE_PARSER.coq_parser **)
  
  let mmx_reg =
    map int_t mmx_register_t
      (field (Big.succ (Big.succ (Big.succ Big.zero))))
      (Obj.magic coq_Z_to_mmx_register)
  
  (** val sse_reg : X86_BASE_PARSER.coq_parser **)
  
  let sse_reg =
    map int_t sse_register_t
      (field (Big.succ (Big.succ (Big.succ Big.zero))))
      (Obj.magic coq_Z_to_sse_register)
  
  (** val byte : X86_BASE_PARSER.coq_parser **)
  
  let byte =
    map int_t byte_t
      (field (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
        (Big.succ (Big.succ Big.zero)))))))))
      (Obj.magic
        (Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ Big.zero)))))))))
  
  (** val halfword : X86_BASE_PARSER.coq_parser **)
  
  let halfword =
    map (X86_BASE_PARSER.Coq_pair_t (byte_t, byte_t)) half_t
      (seq byte_t byte_t byte byte) (fun p ->
      let b0 =
        Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ Big.zero)))))))))))))))
          (Word.unsigned (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ Big.zero))))))) (fst (Obj.magic p)))
      in
      let b1 =
        Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ Big.zero)))))))))))))))
          (Word.unsigned (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ Big.zero))))))) (snd (Obj.magic p)))
      in
      Obj.magic
        (Word.coq_or (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ Big.zero)))))))))))))))
          (Word.shl (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ Big.zero)))))))))))))))
            b1
            (Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
              (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
              (Big.succ (Big.succ (Big.succ (Big.succ Big.zero)))))))))))))))
              (Big.double (Big.double (Big.double Big.one))))) b0))
  
  (** val word : X86_BASE_PARSER.coq_parser **)
  
  let word =
    map (X86_BASE_PARSER.Coq_pair_t (byte_t, (X86_BASE_PARSER.Coq_pair_t
      (byte_t, (X86_BASE_PARSER.Coq_pair_t (byte_t, byte_t)))))) word_t
      (seq byte_t (X86_BASE_PARSER.Coq_pair_t (byte_t,
        (X86_BASE_PARSER.Coq_pair_t (byte_t, byte_t)))) byte
        (seq byte_t (X86_BASE_PARSER.Coq_pair_t (byte_t, byte_t)) byte
          (seq byte_t byte_t byte byte))) (fun p ->
      let b0 = zero_extend8_32 (fst (Obj.magic p)) in
      let b1 = zero_extend8_32 (fst (snd (Obj.magic p))) in
      let b2 = zero_extend8_32 (fst (snd (snd (Obj.magic p)))) in
      let b3 = zero_extend8_32 (snd (snd (snd (Obj.magic p)))) in
      let w1 =
        Word.shl (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ Big.zero))))))))))))))))))))))))))))))) b1
          (Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ Big.zero)))))))))))))))))))))))))))))))
            (Big.double (Big.double (Big.double Big.one))))
      in
      let w2 =
        Word.shl (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ Big.zero))))))))))))))))))))))))))))))) b2
          (Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ Big.zero)))))))))))))))))))))))))))))))
            (Big.double (Big.double (Big.double (Big.double Big.one)))))
      in
      let w3 =
        Word.shl (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ Big.zero))))))))))))))))))))))))))))))) b3
          (Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ Big.zero)))))))))))))))))))))))))))))))
            (Big.double (Big.double (Big.double (Big.doubleplusone
            Big.one)))))
      in
      Obj.magic
        (Word.coq_or (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ Big.zero))))))))))))))))))))))))))))))) w3
          (Word.coq_or (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ Big.zero))))))))))))))))))))))))))))))) w2
            (Word.coq_or (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
              (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
              (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
              (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
              (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
              (Big.succ (Big.succ Big.zero))))))))))))))))))))))))))))))) w1
              b0))))
  
  (** val scale_p : X86_BASE_PARSER.coq_parser **)
  
  let scale_p =
    map int_t scale_t (field (Big.succ (Big.succ Big.zero)))
      (Obj.magic coq_Z_to_scale)
  
  (** val tttn : X86_BASE_PARSER.coq_parser **)
  
  let tttn =
    map int_t condition_t
      (field (Big.succ (Big.succ (Big.succ (Big.succ Big.zero)))))
      (Obj.magic coq_Z_to_condition_type)
  
  (** val reg_no_esp : X86_BASE_PARSER.coq_parser **)
  
  let reg_no_esp =
    map (bits_n (length ('0'::('0'::('0'::[]))))) register_t
      (alt (bits_n (length ('0'::('0'::('0'::[])))))
        (bits ('0'::('0'::('0'::[]))))
        (alt (bits_n (length ('0'::('0'::('1'::[])))))
          (bits ('0'::('0'::('1'::[]))))
          (alt (bits_n (length ('0'::('1'::('0'::[])))))
            (bits ('0'::('1'::('0'::[]))))
            (alt (bits_n (length ('0'::('1'::('1'::[])))))
              (bits ('0'::('1'::('1'::[]))))
              (alt (bits_n (length ('1'::('0'::('1'::[])))))
                (bits ('1'::('0'::('1'::[]))))
                (alt (bits_n (length ('1'::('1'::('0'::[])))))
                  (bits ('1'::('1'::('0'::[]))))
                  (bits ('1'::('1'::('1'::[])))))))))) (fun bs ->
      Obj.magic
        (coq_Z_to_register
          (Obj.magic (bits2int (Big.succ (Big.succ (Big.succ Big.zero))) bs))))
  
  (** val reg_no_ebp : X86_BASE_PARSER.coq_parser **)
  
  let reg_no_ebp =
    map (bits_n (length ('0'::('0'::('0'::[]))))) register_t
      (alt (bits_n (length ('0'::('0'::('0'::[])))))
        (bits ('0'::('0'::('0'::[]))))
        (alt (bits_n (length ('0'::('0'::('1'::[])))))
          (bits ('0'::('0'::('1'::[]))))
          (alt (bits_n (length ('0'::('1'::('0'::[])))))
            (bits ('0'::('1'::('0'::[]))))
            (alt (bits_n (length ('0'::('1'::('1'::[])))))
              (bits ('0'::('1'::('1'::[]))))
              (alt (bits_n (length ('1'::('0'::('0'::[])))))
                (bits ('1'::('0'::('0'::[]))))
                (alt (bits_n (length ('1'::('1'::('0'::[])))))
                  (bits ('1'::('1'::('0'::[]))))
                  (bits ('1'::('1'::('1'::[])))))))))) (fun bs ->
      Obj.magic
        (coq_Z_to_register
          (Obj.magic (bits2int (Big.succ (Big.succ (Big.succ Big.zero))) bs))))
  
  (** val si : X86_BASE_PARSER.coq_parser **)
  
  let si =
    map (X86_BASE_PARSER.Coq_pair_t (scale_t, register_t))
      (option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
        X86_PARSER_ARG.Register_t))) (seq scale_t register_t scale_p reg)
      (fun p ->
      match snd (Obj.magic p) with
      | ESP -> Obj.magic None
      | _ -> Obj.magic (Some p))
  
  (** val sib : X86_BASE_PARSER.coq_parser **)
  
  let sib =
    seq
      (option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
        X86_PARSER_ARG.Register_t))) register_t si reg
  
  (** val rm00 : X86_BASE_PARSER.coq_parser **)
  
  let rm00 =
    alt address_t
      (map (bits_n (length ('0'::('0'::('0'::[]))))) address_t
        (alt (bits_n (length ('0'::('0'::('0'::[])))))
          (bits ('0'::('0'::('0'::[]))))
          (alt (bits_n (length ('0'::('0'::('1'::[])))))
            (bits ('0'::('0'::('1'::[]))))
            (alt (bits_n (length ('0'::('1'::('0'::[])))))
              (bits ('0'::('1'::('0'::[]))))
              (alt (bits_n (length ('0'::('1'::('1'::[])))))
                (bits ('0'::('1'::('1'::[]))))
                (alt (bits_n (length ('1'::('1'::('0'::[])))))
                  (bits ('1'::('1'::('0'::[]))))
                  (bits ('1'::('1'::('1'::[]))))))))) (fun bs ->
        Obj.magic { addrDisp =
          (Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ Big.zero)))))))))))))))))))))))))))))))
            Big.zero); addrBase = (Some
          (coq_Z_to_register
            (Obj.magic
              (bits2int (Big.succ (Big.succ (Big.succ Big.zero))) bs))));
          addrIndex = None }))
      (alt address_t
        (map (X86_BASE_PARSER.Coq_pair_t
          ((bits_n (length ('1'::('0'::('0'::[]))))),
          (X86_BASE_PARSER.Coq_pair_t
          ((option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
             X86_PARSER_ARG.Register_t))), register_t)))) address_t
          (seq (bits_n (length ('1'::('0'::('0'::[])))))
            (X86_BASE_PARSER.Coq_pair_t
            ((option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
               X86_PARSER_ARG.Register_t))), register_t))
            (bits ('1'::('0'::('0'::[]))))
            (seq
              (option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
                X86_PARSER_ARG.Register_t))) register_t si reg_no_ebp))
          (fun p ->
          let (r, r0) = Obj.magic p in
          let (si0, base) = r0 in
          Obj.magic { addrDisp =
            (Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
              (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
              (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
              (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
              (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
              (Big.succ (Big.succ Big.zero)))))))))))))))))))))))))))))))
              Big.zero); addrBase = (Some base); addrIndex = si0 }))
        (alt address_t
          (map (X86_BASE_PARSER.Coq_pair_t
            ((bits_n (length ('1'::('0'::('0'::[]))))),
            (X86_BASE_PARSER.Coq_pair_t
            ((option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
               X86_PARSER_ARG.Register_t))), (X86_BASE_PARSER.Coq_pair_t
            ((bits_n (length ('1'::('0'::('1'::[]))))), word_t))))))
            address_t
            (seq (bits_n (length ('1'::('0'::('0'::[])))))
              (X86_BASE_PARSER.Coq_pair_t
              ((option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
                 X86_PARSER_ARG.Register_t))), (X86_BASE_PARSER.Coq_pair_t
              ((bits_n (length ('1'::('0'::('1'::[]))))), word_t))))
              (bits ('1'::('0'::('0'::[]))))
              (seq
                (option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
                  X86_PARSER_ARG.Register_t))) (X86_BASE_PARSER.Coq_pair_t
                ((bits_n (length ('1'::('0'::('1'::[]))))), word_t)) si
                (seq (bits_n (length ('1'::('0'::('1'::[]))))) word_t
                  (bits ('1'::('0'::('1'::[])))) word))) (fun p ->
            let (r, r0) = Obj.magic p in
            let (si0, r1) = r0 in
            let (r2, disp) = r1 in
            Obj.magic { addrDisp = disp; addrBase = None; addrIndex = si0 }))
          (map (X86_BASE_PARSER.Coq_pair_t
            ((bits_n (length ('1'::('0'::('1'::[]))))), word_t)) address_t
            (seq (bits_n (length ('1'::('0'::('1'::[]))))) word_t
              (bits ('1'::('0'::('1'::[])))) word) (fun p ->
            let (r, disp) = Obj.magic p in
            Obj.magic { addrDisp = disp; addrBase = None; addrIndex = None }))))
  
  (** val rm01 : X86_BASE_PARSER.coq_parser **)
  
  let rm01 =
    alt address_t
      (map (X86_BASE_PARSER.Coq_pair_t
        ((bits_n (length ('0'::('0'::('0'::[]))))), byte_t)) address_t
        (seq (bits_n (length ('0'::('0'::('0'::[]))))) byte_t
          (alt (bits_n (length ('0'::('0'::('0'::[])))))
            (bits ('0'::('0'::('0'::[]))))
            (alt (bits_n (length ('0'::('0'::('1'::[])))))
              (bits ('0'::('0'::('1'::[]))))
              (alt (bits_n (length ('0'::('1'::('0'::[])))))
                (bits ('0'::('1'::('0'::[]))))
                (alt (bits_n (length ('0'::('1'::('1'::[])))))
                  (bits ('0'::('1'::('1'::[]))))
                  (alt (bits_n (length ('1'::('0'::('1'::[])))))
                    (bits ('1'::('0'::('1'::[]))))
                    (alt (bits_n (length ('1'::('1'::('0'::[])))))
                      (bits ('1'::('1'::('0'::[]))))
                      (bits ('1'::('1'::('1'::[])))))))))) byte) (fun p ->
        let (bs, disp) = Obj.magic p in
        Obj.magic { addrDisp = (sign_extend8_32 disp); addrBase = (Some
          (coq_Z_to_register
            (Obj.magic
              (bits2int (Big.succ (Big.succ (Big.succ Big.zero))) bs))));
          addrIndex = None }))
      (map (X86_BASE_PARSER.Coq_pair_t
        ((bits_n (length ('1'::('0'::('0'::[]))))),
        (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
        ((option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
           X86_PARSER_ARG.Register_t))), register_t)), byte_t)))) address_t
        (seq (bits_n (length ('1'::('0'::('0'::[])))))
          (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
          ((option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
             X86_PARSER_ARG.Register_t))), register_t)), byte_t))
          (bits ('1'::('0'::('0'::[]))))
          (seq (X86_BASE_PARSER.Coq_pair_t
            ((option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
               X86_PARSER_ARG.Register_t))), register_t)) byte_t sib byte))
        (fun p ->
        let (r, r0) = Obj.magic p in
        let (r1, disp) = r0 in
        let (si0, base) = r1 in
        Obj.magic { addrDisp = (sign_extend8_32 disp); addrBase = (Some
          base); addrIndex = si0 }))
  
  (** val rm10 : X86_BASE_PARSER.coq_parser **)
  
  let rm10 =
    alt address_t
      (map (X86_BASE_PARSER.Coq_pair_t
        ((bits_n (length ('0'::('0'::('0'::[]))))), word_t)) address_t
        (seq (bits_n (length ('0'::('0'::('0'::[]))))) word_t
          (alt (bits_n (length ('0'::('0'::('0'::[])))))
            (bits ('0'::('0'::('0'::[]))))
            (alt (bits_n (length ('0'::('0'::('1'::[])))))
              (bits ('0'::('0'::('1'::[]))))
              (alt (bits_n (length ('0'::('1'::('0'::[])))))
                (bits ('0'::('1'::('0'::[]))))
                (alt (bits_n (length ('0'::('1'::('1'::[])))))
                  (bits ('0'::('1'::('1'::[]))))
                  (alt (bits_n (length ('1'::('0'::('1'::[])))))
                    (bits ('1'::('0'::('1'::[]))))
                    (alt (bits_n (length ('1'::('1'::('0'::[])))))
                      (bits ('1'::('1'::('0'::[]))))
                      (bits ('1'::('1'::('1'::[])))))))))) word) (fun p ->
        let (bs, disp) = Obj.magic p in
        Obj.magic { addrDisp = disp; addrBase = (Some
          (coq_Z_to_register
            (Obj.magic
              (bits2int (Big.succ (Big.succ (Big.succ Big.zero))) bs))));
          addrIndex = None }))
      (map (X86_BASE_PARSER.Coq_pair_t
        ((bits_n (length ('1'::('0'::('0'::[]))))),
        (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
        ((option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
           X86_PARSER_ARG.Register_t))), register_t)), word_t)))) address_t
        (seq (bits_n (length ('1'::('0'::('0'::[])))))
          (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
          ((option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
             X86_PARSER_ARG.Register_t))), register_t)), word_t))
          (bits ('1'::('0'::('0'::[]))))
          (seq (X86_BASE_PARSER.Coq_pair_t
            ((option_t (X86_PARSER_ARG.Pair_t (X86_PARSER_ARG.Scale_t,
               X86_PARSER_ARG.Register_t))), register_t)) word_t sib word))
        (fun p ->
        let (r, r0) = Obj.magic p in
        let (r1, disp) = r0 in
        let (si0, base) = r1 in
        Obj.magic { addrDisp = disp; addrBase = (Some base); addrIndex =
          si0 }))
  
  (** val modrm_gen :
      X86_BASE_PARSER.result -> X86_BASE_PARSER.coq_parser -> (address ->
      X86_BASE_PARSER.result_m) -> X86_BASE_PARSER.coq_parser **)
  
  let modrm_gen res_t reg_p addr_op =
    alt (X86_BASE_PARSER.Coq_pair_t (res_t, res_t))
      (map (X86_BASE_PARSER.Coq_pair_t (res_t, address_t))
        (X86_BASE_PARSER.Coq_pair_t (res_t, res_t))
        (alt (X86_BASE_PARSER.Coq_pair_t (res_t, address_t))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (res_t, address_t))
            ('0'::('0'::[])) (seq res_t address_t reg_p rm00))
          (alt (X86_BASE_PARSER.Coq_pair_t (res_t, address_t))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (res_t, address_t))
              ('0'::('1'::[])) (seq res_t address_t reg_p rm01))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (res_t, address_t))
              ('1'::('0'::[])) (seq res_t address_t reg_p rm10)))) (fun p ->
        let (op1, addr) = Obj.magic p in Obj.magic (op1, (addr_op addr))))
      (map (X86_BASE_PARSER.Coq_pair_t (res_t, res_t))
        (X86_BASE_PARSER.Coq_pair_t (res_t, res_t))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (res_t, res_t))
          ('1'::('1'::[])) (seq res_t res_t reg_p reg_p)) (fun p ->
        let (op1, op2) = Obj.magic p in Obj.magic (op1, op2)))
  
  (** val reg_op : X86_BASE_PARSER.coq_parser **)
  
  let reg_op =
    map register_t operand_t reg (fun x -> Obj.magic (Reg_op (Obj.magic x)))
  
  (** val modrm : X86_BASE_PARSER.coq_parser **)
  
  let modrm =
    modrm_gen operand_t reg_op (Obj.magic (fun x -> Address_op x))
  
  (** val mmx_reg_op : X86_BASE_PARSER.coq_parser **)
  
  let mmx_reg_op =
    map mmx_register_t mmx_operand_t mmx_reg (fun r ->
      Obj.magic (MMX_Reg_op (Obj.magic r)))
  
  (** val modrm_mmx : X86_BASE_PARSER.coq_parser **)
  
  let modrm_mmx =
    modrm_gen mmx_operand_t mmx_reg_op (Obj.magic (fun x -> MMX_Addr_op x))
  
  (** val sse_reg_op : X86_BASE_PARSER.coq_parser **)
  
  let sse_reg_op =
    map sse_register_t sse_operand_t sse_reg (fun r ->
      Obj.magic (SSE_XMM_Reg_op (Obj.magic r)))
  
  (** val modrm_xmm : X86_BASE_PARSER.coq_parser **)
  
  let modrm_xmm =
    modrm_gen sse_operand_t sse_reg_op (Obj.magic (fun x -> SSE_Addr_op x))
  
  (** val modrm_mm : X86_BASE_PARSER.coq_parser **)
  
  let modrm_mm =
    modrm_gen sse_operand_t
      (map mmx_register_t sse_operand_t mmx_reg (fun r ->
        Obj.magic (SSE_MM_Reg_op (Obj.magic r))))
      (Obj.magic (fun x -> SSE_Addr_op x))
  
  (** val modrm_gen_noreg :
      X86_BASE_PARSER.result -> X86_BASE_PARSER.result ->
      X86_BASE_PARSER.coq_parser -> (address -> X86_BASE_PARSER.result_m) ->
      X86_BASE_PARSER.coq_parser **)
  
  let modrm_gen_noreg reg_t res_t reg_p addr_op =
    map (X86_BASE_PARSER.Coq_pair_t (reg_t, address_t))
      (X86_BASE_PARSER.Coq_pair_t (reg_t, res_t))
      (alt (X86_BASE_PARSER.Coq_pair_t (reg_t, address_t))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (reg_t, address_t))
          ('0'::('0'::[])) (seq reg_t address_t reg_p rm00))
        (alt (X86_BASE_PARSER.Coq_pair_t (reg_t, address_t))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (reg_t, address_t))
            ('0'::('1'::[])) (seq reg_t address_t reg_p rm01))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (reg_t, address_t))
            ('1'::('0'::[])) (seq reg_t address_t reg_p rm10)))) (fun p ->
      let (op1, addr) = Obj.magic p in Obj.magic (op1, (addr_op addr)))
  
  (** val modrm_noreg : X86_BASE_PARSER.coq_parser **)
  
  let modrm_noreg =
    modrm_gen_noreg register_t operand_t reg
      (Obj.magic (fun x -> Address_op x))
  
  (** val modrm_xmm_noreg : X86_BASE_PARSER.coq_parser **)
  
  let modrm_xmm_noreg =
    modrm_gen_noreg sse_operand_t sse_operand_t sse_reg_op
      (Obj.magic (fun x -> SSE_Addr_op x))
  
  (** val modrm_xmm_gp_noreg : X86_BASE_PARSER.coq_parser **)
  
  let modrm_xmm_gp_noreg =
    modrm_gen_noreg sse_operand_t sse_operand_t
      (map register_t sse_operand_t reg (fun r ->
        Obj.magic (SSE_GP_Reg_op (Obj.magic r))))
      (Obj.magic (fun x -> SSE_Addr_op x))
  
  (** val modrm_mm_noreg : X86_BASE_PARSER.coq_parser **)
  
  let modrm_mm_noreg =
    modrm_gen_noreg sse_operand_t sse_operand_t
      (map mmx_register_t sse_operand_t mmx_reg (fun r ->
        Obj.magic (SSE_MM_Reg_op (Obj.magic r))))
      (Obj.magic (fun x -> SSE_Addr_op x))
  
  (** val ext_op_modrm_gen :
      X86_BASE_PARSER.result -> (address -> X86_BASE_PARSER.result_m) ->
      char list -> X86_BASE_PARSER.coq_parser **)
  
  let ext_op_modrm_gen res_t addr_op bs =
    map (X86_BASE_PARSER.Coq_pair_t ((bits_n (length ('0'::('0'::[])))),
      (X86_BASE_PARSER.Coq_pair_t ((bits_n (length bs)), address_t)))) res_t
      (alt (X86_BASE_PARSER.Coq_pair_t ((bits_n (length ('0'::('0'::[])))),
        (X86_BASE_PARSER.Coq_pair_t ((bits_n (length bs)), address_t))))
        (seq (bits_n (length ('0'::('0'::[])))) (X86_BASE_PARSER.Coq_pair_t
          ((bits_n (length bs)), address_t)) (bits ('0'::('0'::[])))
          (seq (bits_n (length bs)) address_t (bits bs) rm00))
        (alt (X86_BASE_PARSER.Coq_pair_t ((bits_n (length ('0'::('1'::[])))),
          (X86_BASE_PARSER.Coq_pair_t ((bits_n (length bs)), address_t))))
          (seq (bits_n (length ('0'::('1'::[])))) (X86_BASE_PARSER.Coq_pair_t
            ((bits_n (length bs)), address_t)) (bits ('0'::('1'::[])))
            (seq (bits_n (length bs)) address_t (bits bs) rm01))
          (seq (bits_n (length ('1'::('0'::[])))) (X86_BASE_PARSER.Coq_pair_t
            ((bits_n (length bs)), address_t)) (bits ('1'::('0'::[])))
            (seq (bits_n (length bs)) address_t (bits bs) rm10)))) (fun p ->
      let (r, r0) = Obj.magic p in let (r1, addr) = r0 in addr_op addr)
  
  (** val ext_op_modrm : char list -> X86_BASE_PARSER.coq_parser **)
  
  let ext_op_modrm =
    ext_op_modrm_gen operand_t (Obj.magic (fun x -> Address_op x))
  
  (** val ext_op_modrm_sse : char list -> X86_BASE_PARSER.coq_parser **)
  
  let ext_op_modrm_sse =
    ext_op_modrm_gen sse_operand_t (Obj.magic (fun x -> SSE_Addr_op x))
  
  (** val ext_op_modrm_FPM16 : char list -> X86_BASE_PARSER.coq_parser **)
  
  let ext_op_modrm_FPM16 =
    ext_op_modrm_gen fp_operand_t (Obj.magic (fun x -> FPM16_op x))
  
  (** val ext_op_modrm_FPM32 : char list -> X86_BASE_PARSER.coq_parser **)
  
  let ext_op_modrm_FPM32 =
    ext_op_modrm_gen fp_operand_t (Obj.magic (fun x -> FPM32_op x))
  
  (** val ext_op_modrm_FPM64 : char list -> X86_BASE_PARSER.coq_parser **)
  
  let ext_op_modrm_FPM64 =
    ext_op_modrm_gen fp_operand_t (Obj.magic (fun x -> FPM64_op x))
  
  (** val ext_op_modrm_FPM80 : char list -> X86_BASE_PARSER.coq_parser **)
  
  let ext_op_modrm_FPM80 =
    ext_op_modrm_gen fp_operand_t (Obj.magic (fun x -> FPM80_op x))
  
  (** val ext_op_modrm2 : char list -> X86_BASE_PARSER.coq_parser **)
  
  let ext_op_modrm2 bs =
    alt operand_t
      (map (X86_BASE_PARSER.Coq_pair_t ((bits_n (length bs)), address_t))
        operand_t
        (alt (X86_BASE_PARSER.Coq_pair_t ((bits_n (length bs)), address_t))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t ((bits_n (length bs)),
            address_t)) ('0'::('0'::[]))
            (seq (bits_n (length bs)) address_t (bits bs) rm00))
          (alt (X86_BASE_PARSER.Coq_pair_t ((bits_n (length bs)), address_t))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t ((bits_n (length bs)),
              address_t)) ('0'::('1'::[]))
              (seq (bits_n (length bs)) address_t (bits bs) rm01))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t ((bits_n (length bs)),
              address_t)) ('1'::('0'::[]))
              (seq (bits_n (length bs)) address_t (bits bs) rm10))))
        (fun p ->
        let (r, addr) = Obj.magic p in Obj.magic (Address_op addr)))
      (map (X86_BASE_PARSER.Coq_pair_t ((bits_n (length bs)), operand_t))
        operand_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t ((bits_n (length bs)),
          operand_t)) ('1'::('1'::[]))
          (seq (bits_n (length bs)) operand_t (bits bs) reg_op)) (fun p ->
        let (r, op) = Obj.magic p in op))
  
  (** val coq_AAA_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_AAA_p =
    map
      (bits_n
        (length ('0'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::[]))))))))))
      instruction_t
      (bits ('0'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::[])))))))))
      (fun x -> Obj.magic AAA)
  
  (** val coq_AAD_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_AAD_p =
    map
      (bits_n
        (length
          ('1'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::[]))))))))))))))))))
      instruction_t
      (bits
        ('1'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::[])))))))))))))))))
      (fun x -> Obj.magic AAD)
  
  (** val coq_AAM_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_AAM_p =
    map
      (bits_n
        (length
          ('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::[]))))))))))))))))))
      instruction_t
      (bits
        ('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::[])))))))))))))))))
      (fun x -> Obj.magic AAM)
  
  (** val coq_AAS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_AAS_p =
    map
      (bits_n
        (length ('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::[]))))))))))
      instruction_t
      (bits ('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::[])))))))))
      (fun x -> Obj.magic AAS)
  
  (** val imm_op : bool -> X86_BASE_PARSER.coq_parser **)
  
  let imm_op = function
  | true ->
    map half_t operand_t halfword (fun w ->
      Obj.magic (Imm_op (sign_extend16_32 (Obj.magic w))))
  | false ->
    map word_t operand_t word (fun w -> Obj.magic (Imm_op (Obj.magic w)))
  
  (** val logic_or_arith_p :
      bool -> char list -> char list -> (bool -> operand -> operand -> instr)
      -> X86_BASE_PARSER.coq_parser **)
  
  let logic_or_arith_p opsize_override op1 op2 instCon =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)))))) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)))))) op1
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)))))) ('0'::[])
            (seq X86_BASE_PARSER.Coq_char_t (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, (X86_BASE_PARSER.Coq_pair_t
              (operand_t, operand_t)))) anybit
              (seq X86_BASE_PARSER.Coq_char_t (X86_BASE_PARSER.Coq_pair_t
                (operand_t, operand_t)) anybit modrm)))) (fun p ->
        let (d, r) = Obj.magic p in
        let (w, r0) = r in
        let (op3, op4) = r0 in
        if d
        then Obj.magic instCon w op3 op4
        else Obj.magic instCon w op4 op3))
      (alt instruction_t
        (map (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t)) instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
            ('1'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
              ('0'::('0'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                ('1'::('1'::[]))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                  op2 (seq register_t byte_t reg byte))))) (fun p ->
          let (r, imm) = Obj.magic p in
          Obj.magic instCon true (Reg_op r) (Imm_op (sign_extend8_32 imm))))
        (alt instruction_t
          (map (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
            instruction_t
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
              ('1'::('0'::('0'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                ('0'::('0'::('0'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                  ('1'::('1'::[]))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                    op2 (seq register_t byte_t reg byte))))) (fun p ->
            let (r, imm) = Obj.magic p in
            Obj.magic instCon false (Reg_op r) (Imm_op (zero_extend8_32 imm))))
          (alt instruction_t
            (map (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
              instruction_t
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
                ('1'::('0'::('0'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                  operand_t)) ('0'::('0'::('0'::('1'::[]))))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                    operand_t)) ('1'::('1'::[]))
                    (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                      operand_t)) op2
                      (seq register_t operand_t reg (imm_op opsize_override))))))
              (fun p ->
              let (r, imm) = Obj.magic p in
              Obj.magic instCon true (Reg_op r) imm))
            (alt instruction_t
              (map byte_t instruction_t
                (bitsleft byte_t op1
                  (bitsleft byte_t ('1'::('0'::('0'::[]))) byte)) (fun imm ->
                Obj.magic instCon false (Reg_op EAX) (Imm_op
                  (zero_extend8_32 (Obj.magic imm)))))
              (alt instruction_t
                (map operand_t instruction_t
                  (bitsleft operand_t op1
                    (bitsleft operand_t ('1'::('0'::('1'::[])))
                      (imm_op opsize_override))) (fun imm ->
                  Obj.magic instCon true (Reg_op EAX) imm))
                (alt instruction_t
                  (map (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
                    instruction_t
                    (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                      byte_t)) ('1'::('0'::('0'::('0'::[]))))
                      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                        byte_t)) ('0'::('0'::('0'::('0'::[]))))
                        (seq operand_t byte_t (ext_op_modrm op2) byte)))
                    (fun p ->
                    let (op, imm) = Obj.magic p in
                    Obj.magic instCon false op (Imm_op (zero_extend8_32 imm))))
                  (alt instruction_t
                    (map (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
                      instruction_t
                      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                        byte_t)) ('1'::('0'::('0'::('0'::[]))))
                        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                          byte_t)) ('0'::('0'::('1'::('1'::[]))))
                          (seq operand_t byte_t (ext_op_modrm op2) byte)))
                      (fun p ->
                      let (op, imm) = Obj.magic p in
                      Obj.magic instCon true op (Imm_op
                        (sign_extend8_32 imm))))
                    (map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                      instruction_t
                      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                        operand_t)) ('1'::('0'::('0'::('0'::[]))))
                        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                          operand_t)) ('0'::('0'::('0'::('1'::[]))))
                          (seq operand_t operand_t (ext_op_modrm op2)
                            (imm_op opsize_override)))) (fun p ->
                      let (op, imm) = Obj.magic p in
                      Obj.magic instCon true op imm)))))))))
  
  (** val coq_ADC_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_ADC_p s =
    logic_or_arith_p s ('0'::('0'::('0'::('1'::('0'::[])))))
      ('0'::('1'::('0'::[]))) (fun x x0 x1 -> ADC (x, x0, x1))
  
  (** val coq_ADD_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_ADD_p s =
    logic_or_arith_p s ('0'::('0'::('0'::('0'::('0'::[])))))
      ('0'::('0'::('0'::[]))) (fun x x0 x1 -> ADD (x, x0, x1))
  
  (** val coq_AND_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_AND_p s =
    logic_or_arith_p s ('0'::('0'::('1'::('0'::('0'::[])))))
      ('1'::('0'::('0'::[]))) (fun x x0 x1 -> AND (x, x0, x1))
  
  (** val coq_CMP_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_CMP_p s =
    logic_or_arith_p s ('0'::('0'::('1'::('1'::('1'::[])))))
      ('1'::('1'::('1'::[]))) (fun x x0 x1 -> CMP (x, x0, x1))
  
  (** val coq_OR_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_OR_p s =
    logic_or_arith_p s ('0'::('0'::('0'::('0'::('1'::[])))))
      ('0'::('0'::('1'::[]))) (fun x x0 x1 -> OR (x, x0, x1))
  
  (** val coq_SBB_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_SBB_p s =
    logic_or_arith_p s ('0'::('0'::('0'::('1'::('1'::[])))))
      ('0'::('1'::('1'::[]))) (fun x x0 x1 -> SBB (x, x0, x1))
  
  (** val coq_SUB_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_SUB_p s =
    logic_or_arith_p s ('0'::('0'::('1'::('0'::('1'::[])))))
      ('1'::('0'::('1'::[]))) (fun x x0 x1 -> SUB (x, x0, x1))
  
  (** val coq_XOR_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_XOR_p s =
    logic_or_arith_p s ('0'::('0'::('1'::('1'::('0'::[])))))
      ('1'::('1'::('0'::[]))) (fun x x0 x1 -> XOR (x, x0, x1))
  
  (** val coq_ARPL_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_ARPL_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('1'::('1'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('0'::('0'::('1'::('1'::[])))) modrm)) (fun p ->
      let (op1, op2) = Obj.magic p in Obj.magic (ARPL (op1, op2)))
  
  (** val coq_BOUND_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BOUND_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('1'::('1'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('0'::('0'::('1'::('0'::[])))) modrm)) (fun p ->
      let (op1, op2) = Obj.magic p in Obj.magic (BOUND (op1, op2)))
  
  (** val coq_BSF_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BSF_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('1'::('1'::('0'::('0'::[])))) modrm)))) (fun p ->
      let (op1, op2) = Obj.magic p in Obj.magic (BSF (op1, op2)))
  
  (** val coq_BSR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BSR_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('1'::('1'::('0'::('1'::[])))) modrm)))) (fun p ->
      let (op1, op2) = Obj.magic p in Obj.magic (BSR (op1, op2)))
  
  (** val coq_BSWAP_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BSWAP_p =
    map register_t instruction_t
      (bitsleft register_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft register_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft register_t ('1'::('1'::('0'::('0'::[]))))
            (bitsleft register_t ('1'::[]) reg)))) (fun x ->
      Obj.magic (BSWAP (Obj.magic x)))
  
  (** val bit_test_p :
      char list -> char list -> (operand -> operand -> instr) ->
      X86_BASE_PARSER.coq_parser **)
  
  let bit_test_p opcode1 opcode2 instr0 =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
              ('1'::('0'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                ('1'::('0'::('1'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                  ('1'::('1'::[]))
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))
                    opcode1 (seq register_t byte_t reg byte))))))) (fun p ->
        let (r, imm) = Obj.magic p in
        Obj.magic instr0 (Reg_op r) (Imm_op (zero_extend8_32 imm))))
      (alt instruction_t
        (map (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t)) instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
                ('1'::('0'::('1'::('1'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, byte_t))
                  ('1'::('0'::('1'::('0'::[]))))
                  (seq operand_t byte_t (ext_op_modrm opcode1) byte)))))
          (fun p ->
          let (op1, imm) = Obj.magic p in
          Obj.magic instr0 op1 (Imm_op (zero_extend8_32 imm))))
        (map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                ('1'::('0'::('1'::[])))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                  opcode2
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t,
                    operand_t)) ('0'::('1'::('1'::[]))) modrm))))) (fun p ->
          let (op2, op1) = Obj.magic p in Obj.magic instr0 op1 op2)))
  
  (** val coq_BT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BT_p =
    bit_test_p ('1'::('0'::('0'::[]))) ('0'::('0'::[])) (fun x x0 -> BT (x,
      x0))
  
  (** val coq_BTC_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BTC_p =
    bit_test_p ('1'::('1'::('1'::[]))) ('1'::('1'::[])) (fun x x0 -> BTC (x,
      x0))
  
  (** val coq_BTR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BTR_p =
    bit_test_p ('1'::('1'::('0'::[]))) ('1'::('0'::[])) (fun x x0 -> BTR (x,
      x0))
  
  (** val coq_BTS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_BTS_p =
    bit_test_p ('1'::('0'::('1'::[]))) ('0'::('1'::[])) (fun x x0 -> BTS (x,
      x0))
  
  (** val coq_CALL_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CALL_p =
    alt instruction_t
      (map word_t instruction_t
        (bitsleft word_t ('1'::('1'::('1'::('0'::[]))))
          (bitsleft word_t ('1'::('0'::('0'::('0'::[])))) word)) (fun w ->
        Obj.magic (CALL (true, false, (Imm_op (Obj.magic w)), None))))
      (alt instruction_t
        (map operand_t instruction_t
          (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
            (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
              (ext_op_modrm2 ('0'::('1'::('0'::[])))))) (fun op ->
          Obj.magic (CALL (true, true, (Obj.magic op), None))))
        (alt instruction_t
          (map (X86_BASE_PARSER.Coq_pair_t (half_t, word_t)) instruction_t
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (half_t, word_t))
              ('1'::('0'::('0'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (half_t, word_t))
                ('1'::('0'::('1'::('0'::[]))))
                (seq half_t word_t halfword word))) (fun p ->
            Obj.magic (CALL (false, true, (Imm_op (snd (Obj.magic p))), (Some
              (fst (Obj.magic p)))))))
          (map operand_t instruction_t
            (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
              (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
                (ext_op_modrm2 ('0'::('1'::('1'::[])))))) (fun op ->
            Obj.magic (CALL (false, true, (Obj.magic op), None))))))
  
  (** val coq_CDQ_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CDQ_p =
    map (bits_n (length ('1'::('0'::('0'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('0'::('1'::[]))))))
        ('1'::('0'::('0'::('1'::[])))) (bits ('1'::('0'::('0'::('1'::[]))))))
      (fun x -> Obj.magic CDQ)
  
  (** val coq_CLC_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CLC_p =
    map (bits_n (length ('1'::('0'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('1'::('0'::('0'::('0'::[]))))))
      (fun x -> Obj.magic CLC)
  
  (** val coq_CLD_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CLD_p =
    map (bits_n (length ('1'::('1'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('0'::('0'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('1'::('1'::('0'::('0'::[]))))))
      (fun x -> Obj.magic CLD)
  
  (** val coq_CLI_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CLI_p =
    map (bits_n (length ('1'::('0'::('1'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('1'::('0'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('1'::('0'::('1'::('0'::[]))))))
      (fun x -> Obj.magic CLI)
  
  (** val coq_CLTS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CLTS_p =
    map (bits_n (length ('0'::('1'::('1'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('1'::('1'::('0'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (bits_n (length ('0'::('1'::('1'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (bits_n (length ('0'::('1'::('1'::('0'::[]))))))
            ('0'::('0'::('0'::('0'::[]))))
            (bits ('0'::('1'::('1'::('0'::[])))))))) (fun x ->
      Obj.magic CLTS)
  
  (** val coq_CMC_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CMC_p =
    map (bits_n (length ('0'::('1'::('0'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('1'::('0'::('1'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('0'::('1'::('0'::('1'::[]))))))
      (fun x -> Obj.magic CMC)
  
  (** val coq_CMPS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CMPS_p =
    map X86_BASE_PARSER.Coq_char_t instruction_t
      (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('0'::('1'::('0'::[]))))
        (bitsleft X86_BASE_PARSER.Coq_char_t ('0'::('1'::('1'::[]))) anybit))
      (fun x -> Obj.magic (CMPS (Obj.magic x)))
  
  (** val coq_CMPXCHG_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CMPXCHG_p =
    map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
      (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)))) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, (X86_BASE_PARSER.Coq_pair_t
              (operand_t, operand_t)))) ('0'::('0'::('0'::[])))
              (seq X86_BASE_PARSER.Coq_char_t (X86_BASE_PARSER.Coq_pair_t
                (operand_t, operand_t)) anybit modrm))))) (fun p ->
      let (w, r) = Obj.magic p in
      let (op1, op2) = r in Obj.magic (CMPXCHG (w, op2, op1)))
  
  (** val coq_CPUID_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CPUID_p =
    map (bits_n (length ('0'::('0'::('1'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('0'::('1'::('0'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (bits_n (length ('0'::('0'::('1'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (bits_n (length ('0'::('0'::('1'::('0'::[]))))))
            ('1'::('0'::('1'::('0'::[]))))
            (bits ('0'::('0'::('1'::('0'::[])))))))) (fun x ->
      Obj.magic CPUID)
  
  (** val coq_CWDE_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CWDE_p =
    map (bits_n (length ('1'::('0'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
        ('1'::('0'::('0'::('1'::[])))) (bits ('1'::('0'::('0'::('0'::[]))))))
      (fun x -> Obj.magic CWDE)
  
  (** val coq_DAA_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_DAA_p =
    map (bits_n (length ('0'::('1'::('1'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('1'::('1'::('1'::[]))))))
        ('0'::('0'::('1'::('0'::[])))) (bits ('0'::('1'::('1'::('1'::[]))))))
      (fun x -> Obj.magic DAA)
  
  (** val coq_DAS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_DAS_p =
    map (bits_n (length ('1'::('1'::('1'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('1'::('1'::[]))))))
        ('0'::('0'::('1'::('0'::[])))) (bits ('1'::('1'::('1'::('1'::[]))))))
      (fun x -> Obj.magic DAS)
  
  (** val coq_DEC_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_DEC_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        register_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          register_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            register_t)) ('1'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t register_t anybit
              (bitsleft register_t ('1'::('1'::('0'::('0'::('1'::[]))))) reg))))
        (fun p ->
        let (w, r) = Obj.magic p in Obj.magic (DEC (w, (Reg_op r)))))
      (alt instruction_t
        (map register_t instruction_t
          (bitsleft register_t ('0'::('1'::('0'::('0'::[]))))
            (bitsleft register_t ('1'::[]) reg)) (fun r ->
          Obj.magic (DEC (true, (Reg_op (Obj.magic r))))))
        (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            operand_t)) ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, operand_t))
              ('1'::('1'::('1'::[])))
              (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
                (ext_op_modrm ('0'::('0'::('1'::[]))))))) (fun p ->
          let (w, op1) = Obj.magic p in Obj.magic (DEC (w, op1)))))
  
  (** val coq_DIV_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_DIV_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        register_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          register_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            register_t)) ('0'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t register_t anybit
              (bitsleft register_t ('1'::('1'::('1'::('1'::('0'::[]))))) reg))))
        (fun p ->
        let (w, r) = Obj.magic p in Obj.magic (DIV (w, (Reg_op r)))))
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        operand_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            operand_t)) ('0'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
              (ext_op_modrm ('1'::('1'::('0'::[]))))))) (fun p ->
        let (w, op1) = Obj.magic p in Obj.magic (DIV (w, op1))))
  
  (** val coq_HLT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_HLT_p =
    map (bits_n (length ('0'::('1'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('0'::('1'::('0'::('0'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('0'::('1'::('0'::('0'::[]))))))
      (fun x -> Obj.magic HLT)
  
  (** val coq_IDIV_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_IDIV_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        register_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          register_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            register_t)) ('0'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t register_t anybit
              (bitsleft register_t ('1'::('1'::('1'::('1'::('1'::[]))))) reg))))
        (fun p ->
        let (w, r) = Obj.magic p in Obj.magic (IDIV (w, (Reg_op r)))))
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        operand_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            operand_t)) ('0'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
              (ext_op_modrm ('1'::('1'::('1'::[]))))))) (fun p ->
        let (w, op1) = Obj.magic p in Obj.magic (IDIV (w, op1))))
  
  (** val coq_IMUL_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_IMUL_p opsize_override =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        operand_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            operand_t)) ('0'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
              (ext_op_modrm2 ('1'::('0'::('1'::[]))))))) (fun p ->
        let (w, op1) = Obj.magic p in Obj.magic (IMUL (w, op1, None, None))))
      (alt instruction_t
        (map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                ('1'::('0'::('1'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                  ('1'::('1'::('1'::('1'::[])))) modrm)))) (fun p ->
          let (op1, op2) = Obj.magic p in
          Obj.magic (IMUL (true, op1, (Some op2), None))))
        (alt instruction_t
          (map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
            (operand_t, operand_t)), byte_t)) instruction_t
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              ((X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)), byte_t))
              ('0'::('1'::('1'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t
                ((X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)),
                byte_t)) ('1'::('0'::('1'::('1'::[]))))
                (seq (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
                  byte_t modrm byte))) (fun p ->
            let (r, imm) = Obj.magic p in
            let (op1, op2) = r in
            Obj.magic (IMUL (true, op1, (Some op2), (Some
              (sign_extend8_32 imm))))))
          (if opsize_override
           then map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
                  (operand_t, operand_t)), half_t)) instruction_t
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t
                    ((X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)),
                    half_t)) ('0'::('1'::('1'::('0'::[]))))
                    (bitsleft (X86_BASE_PARSER.Coq_pair_t
                      ((X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)),
                      half_t)) ('1'::('0'::('0'::('1'::[]))))
                      (seq (X86_BASE_PARSER.Coq_pair_t (operand_t,
                        operand_t)) half_t modrm halfword))) (fun p ->
                  let (r, imm) = Obj.magic p in
                  let (op1, op2) = r in
                  Obj.magic (IMUL (true, op1, (Some op2), (Some
                    (sign_extend16_32 imm)))))
           else map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
                  (operand_t, operand_t)), word_t)) instruction_t
                  (bitsleft (X86_BASE_PARSER.Coq_pair_t
                    ((X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)),
                    word_t)) ('0'::('1'::('1'::('0'::[]))))
                    (bitsleft (X86_BASE_PARSER.Coq_pair_t
                      ((X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)),
                      word_t)) ('1'::('0'::('0'::('1'::[]))))
                      (seq (X86_BASE_PARSER.Coq_pair_t (operand_t,
                        operand_t)) word_t modrm word))) (fun p ->
                  let (r, imm) = Obj.magic p in
                  let (op1, op2) = r in
                  Obj.magic (IMUL (true, op1, (Some op2), (Some imm)))))))
  
  (** val coq_IN_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_IN_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t, byte_t))
        instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          byte_t)) ('1'::('1'::('1'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            byte_t)) ('0'::('1'::('0'::[])))
            (seq X86_BASE_PARSER.Coq_char_t byte_t anybit byte))) (fun p ->
        let (w, pt) = Obj.magic p in Obj.magic (IN (w, (Some pt)))))
      (map X86_BASE_PARSER.Coq_char_t instruction_t
        (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('1'::('1'::('0'::[]))))
          (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('1'::('0'::[])))
            anybit)) (fun w -> Obj.magic (IN ((Obj.magic w), None))))
  
  (** val coq_INC_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INC_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
        register_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          register_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            register_t)) ('1'::('1'::('1'::[])))
            (seq X86_BASE_PARSER.Coq_char_t register_t anybit
              (bitsleft register_t ('1'::('1'::('0'::('0'::('0'::[]))))) reg))))
        (fun p ->
        let (w, r) = Obj.magic p in Obj.magic (INC (w, (Reg_op r)))))
      (alt instruction_t
        (map register_t instruction_t
          (bitsleft register_t ('0'::('1'::('0'::('0'::[]))))
            (bitsleft register_t ('0'::[]) reg)) (fun r ->
          Obj.magic (INC (true, (Reg_op (Obj.magic r))))))
        (map (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
          operand_t)) instruction_t
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (X86_BASE_PARSER.Coq_char_t,
            operand_t)) ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t, operand_t))
              ('1'::('1'::('1'::[])))
              (seq X86_BASE_PARSER.Coq_char_t operand_t anybit
                (ext_op_modrm ('0'::('0'::('0'::[]))))))) (fun p ->
          let (w, op1) = Obj.magic p in Obj.magic (INC (w, op1)))))
  
  (** val coq_INS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INS_p =
    map X86_BASE_PARSER.Coq_char_t instruction_t
      (bitsleft X86_BASE_PARSER.Coq_char_t ('0'::('1'::('1'::('0'::[]))))
        (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('1'::('0'::[]))) anybit))
      (fun x -> Obj.magic (INS (Obj.magic x)))
  
  (** val coq_INTn_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INTn_p =
    map byte_t instruction_t
      (bitsleft byte_t ('1'::('1'::('0'::('0'::[]))))
        (bitsleft byte_t ('1'::('1'::('0'::('1'::[])))) byte)) (fun x ->
      Obj.magic (INTn (Obj.magic x)))
  
  (** val coq_INT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INT_p =
    map (bits_n (length ('1'::('1'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('0'::('0'::[]))))))
        ('1'::('1'::('0'::('0'::[])))) (bits ('1'::('1'::('0'::('0'::[]))))))
      (fun x -> Obj.magic INT)
  
  (** val coq_INTO_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INTO_p =
    map (bits_n (length ('1'::('1'::('1'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('1'::('0'::[]))))))
        ('1'::('1'::('0'::('0'::[])))) (bits ('1'::('1'::('1'::('0'::[]))))))
      (fun x -> Obj.magic INTO)
  
  (** val coq_INVD_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INVD_p =
    map (bits_n (length ('1'::('0'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
            ('0'::('0'::('0'::('0'::[]))))
            (bits ('1'::('0'::('0'::('0'::[])))))))) (fun x ->
      Obj.magic INVD)
  
  (** val coq_INVLPG_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_INVLPG_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('1'::[]))))
              (ext_op_modrm ('1'::('1'::('1'::[])))))))) (fun x ->
      Obj.magic (INVLPG (Obj.magic x)))
  
  (** val coq_IRET_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_IRET_p =
    map (bits_n (length ('1'::('1'::('1'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('1'::('1'::[]))))))
        ('1'::('1'::('0'::('0'::[])))) (bits ('1'::('1'::('1'::('1'::[]))))))
      (fun x -> Obj.magic IRET)
  
  (** val coq_Jcc_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_Jcc_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (condition_t, byte_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t, byte_t))
          ('0'::('1'::('1'::('1'::[])))) (seq condition_t byte_t tttn byte))
        (fun p ->
        let (ct, imm) = Obj.magic p in
        Obj.magic (Jcc (ct, (sign_extend8_32 imm)))))
      (map (X86_BASE_PARSER.Coq_pair_t (condition_t, word_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t, word_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t, word_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t, word_t))
              ('1'::('0'::('0'::('0'::[]))))
              (seq condition_t word_t tttn word)))) (fun p ->
        let (ct, imm) = Obj.magic p in Obj.magic (Jcc (ct, imm))))
  
  (** val coq_JCXZ_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_JCXZ_p =
    map byte_t instruction_t
      (bitsleft byte_t ('1'::('1'::('1'::('0'::[]))))
        (bitsleft byte_t ('0'::('0'::('1'::('1'::[])))) byte)) (fun x ->
      Obj.magic (JCXZ (Obj.magic x)))
  
  (** val coq_JMP_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_JMP_p =
    alt instruction_t
      (map byte_t instruction_t
        (bitsleft byte_t ('1'::('1'::('1'::('0'::[]))))
          (bitsleft byte_t ('1'::('0'::('1'::('1'::[])))) byte)) (fun b ->
        Obj.magic (JMP (true, false, (Imm_op
          (sign_extend8_32 (Obj.magic b))), None))))
      (alt instruction_t
        (map word_t instruction_t
          (bitsleft word_t ('1'::('1'::('1'::('0'::[]))))
            (bitsleft word_t ('1'::('0'::('0'::('1'::[])))) word)) (fun w ->
          Obj.magic (JMP (true, false, (Imm_op (Obj.magic w)), None))))
        (alt instruction_t
          (map operand_t instruction_t
            (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
              (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
                (ext_op_modrm2 ('1'::('0'::('0'::[])))))) (fun op ->
            Obj.magic (JMP (true, true, (Obj.magic op), None))))
          (alt instruction_t
            (map (X86_BASE_PARSER.Coq_pair_t (half_t, word_t)) instruction_t
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (half_t, word_t))
                ('1'::('1'::('1'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (half_t, word_t))
                  ('1'::('0'::('1'::('0'::[]))))
                  (seq half_t word_t halfword word))) (fun p ->
              Obj.magic (JMP (false, true, (Imm_op (snd (Obj.magic p))),
                (Some (fst (Obj.magic p)))))))
            (map operand_t instruction_t
              (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
                (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
                  (ext_op_modrm2 ('1'::('0'::('1'::[])))))) (fun op ->
              Obj.magic (JMP (false, true, (Obj.magic op), None)))))))
  
  (** val coq_LAHF_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LAHF_p =
    map (bits_n (length ('1'::('1'::('1'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('1'::('1'::('1'::[]))))))
        ('1'::('0'::('0'::('1'::[])))) (bits ('1'::('1'::('1'::('1'::[]))))))
      (fun x -> Obj.magic LAHF)
  
  (** val coq_LAR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LAR_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('0'::('0'::('1'::('0'::[])))) modrm)))) (fun p ->
      Obj.magic (LAR ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LDS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LDS_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('1'::('1'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('0'::('1'::('0'::('1'::[])))) modrm)) (fun p ->
      Obj.magic (LDS ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LEA_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LEA_p =
    map (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
        ('1'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, operand_t))
          ('1'::('1'::('0'::('1'::[])))) modrm_noreg)) (fun p ->
      Obj.magic (LEA ((Reg_op (fst (Obj.magic p))), (snd (Obj.magic p)))))
  
  (** val coq_LEAVE_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LEAVE_p =
    map (bits_n (length ('1'::('0'::('0'::('1'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('0'::('1'::[]))))))
        ('1'::('1'::('0'::('0'::[])))) (bits ('1'::('0'::('0'::('1'::[]))))))
      (fun x -> Obj.magic LEAVE)
  
  (** val coq_LES_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LES_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('1'::('1'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('0'::('1'::('0'::('0'::[])))) modrm)) (fun p ->
      Obj.magic (LES ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LFS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LFS_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('0'::('1'::('0'::('0'::[])))) modrm)))) (fun p ->
      Obj.magic (LFS ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LGDT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LGDT_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('1'::[]))))
              (ext_op_modrm ('0'::('1'::('0'::[])))))))) (fun x ->
      Obj.magic (LGDT (Obj.magic x)))
  
  (** val coq_LGS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LGS_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('0'::('1'::('0'::('1'::[])))) modrm)))) (fun p ->
      Obj.magic (LGS ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LIDT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LIDT_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('1'::[]))))
              (ext_op_modrm ('0'::('1'::('1'::[])))))))) (fun x ->
      Obj.magic (LIDT (Obj.magic x)))
  
  (** val coq_LLDT_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LLDT_p =
    alt instruction_t
      (map register_t instruction_t
        (bitsleft register_t ('0'::('0'::('0'::('0'::[]))))
          (bitsleft register_t ('1'::('1'::('1'::('1'::[]))))
            (bitsleft register_t ('0'::('0'::('0'::('0'::[]))))
              (bitsleft register_t ('0'::('0'::('0'::('0'::[]))))
                (bitsleft register_t ('1'::('1'::[]))
                  (bitsleft register_t ('0'::('1'::('0'::[]))) reg))))))
        (fun r -> Obj.magic (LLDT (Reg_op (Obj.magic r)))))
      (map operand_t instruction_t
        (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
          (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
              (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
                (ext_op_modrm ('0'::('1'::('0'::[])))))))) (fun x ->
        Obj.magic (LLDT (Obj.magic x))))
  
  (** val coq_LMSW_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LMSW_p =
    alt instruction_t
      (map register_t instruction_t
        (bitsleft register_t ('0'::('0'::('0'::('0'::[]))))
          (bitsleft register_t ('1'::('1'::('1'::('1'::[]))))
            (bitsleft register_t ('0'::('0'::('0'::('0'::[]))))
              (bitsleft register_t ('0'::('0'::('0'::('1'::[]))))
                (bitsleft register_t ('1'::('1'::[]))
                  (bitsleft register_t ('1'::('1'::('0'::[]))) reg))))))
        (fun r -> Obj.magic (LMSW (Reg_op (Obj.magic r)))))
      (map operand_t instruction_t
        (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
          (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
              (bitsleft operand_t ('0'::('0'::('0'::('1'::[]))))
                (bitsleft operand_t ('1'::('1'::[]))
                  (ext_op_modrm ('1'::('1'::('0'::[]))))))))) (fun x ->
        Obj.magic (LMSW (Obj.magic x))))
  
  (** val coq_LODS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LODS_p =
    map X86_BASE_PARSER.Coq_char_t instruction_t
      (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('0'::('1'::('0'::[]))))
        (bitsleft X86_BASE_PARSER.Coq_char_t ('1'::('1'::('0'::[]))) anybit))
      (fun x -> Obj.magic (LODS (Obj.magic x)))
  
  (** val coq_LOOP_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LOOP_p =
    map byte_t instruction_t
      (bitsleft byte_t ('1'::('1'::('1'::('0'::[]))))
        (bitsleft byte_t ('0'::('0'::('1'::('0'::[])))) byte)) (fun x ->
      Obj.magic (LOOP (Obj.magic x)))
  
  (** val coq_LOOPZ_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LOOPZ_p =
    map byte_t instruction_t
      (bitsleft byte_t ('1'::('1'::('1'::('0'::[]))))
        (bitsleft byte_t ('0'::('0'::('0'::('1'::[])))) byte)) (fun x ->
      Obj.magic (LOOPZ (Obj.magic x)))
  
  (** val coq_LOOPNZ_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LOOPNZ_p =
    map byte_t instruction_t
      (bitsleft byte_t ('1'::('1'::('1'::('0'::[]))))
        (bitsleft byte_t ('0'::('0'::('0'::('0'::[])))) byte)) (fun x ->
      Obj.magic (LOOPNZ (Obj.magic x)))
  
  (** val coq_LSL_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LSL_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('0'::('0'::('1'::('1'::[])))) modrm)))) (fun p ->
      Obj.magic (LSL ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LSS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LSS_p =
    map (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))
              ('0'::('0'::('1'::('0'::[])))) modrm)))) (fun p ->
      Obj.magic (LSS ((fst (Obj.magic p)), (snd (Obj.magic p)))))
  
  (** val coq_LTR_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_LTR_p =
    map operand_t instruction_t
      (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
            (bitsleft operand_t ('0'::('0'::('0'::('0'::[]))))
              (ext_op_modrm ('0'::('1'::('1'::[])))))))) (fun x ->
      Obj.magic (LTR (Obj.magic x)))
  
  (** val coq_CMOVcc_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_CMOVcc_p =
    map (X86_BASE_PARSER.Coq_pair_t (condition_t, (X86_BASE_PARSER.Coq_pair_t
      (operand_t, operand_t)))) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t,
        (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t,
          (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (condition_t,
            (X86_BASE_PARSER.Coq_pair_t (operand_t, operand_t))))
            ('0'::('1'::('0'::('0'::[]))))
            (seq condition_t (X86_BASE_PARSER.Coq_pair_t (operand_t,
              operand_t)) tttn modrm)))) (fun p ->
      let (tttn0, r) = Obj.magic p in
      let (op1, op2) = r in Obj.magic (CMOVcc (tttn0, op1, op2)))
  
  (** val coq_MOV_p : bool -> X86_BASE_PARSER.coq_parser **)
  
  let coq_MOV_p opsize_override =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t
        (operand_t,
        operand_t))))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          operand_t))))
          ('1'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            operand_t))))
            ('1'::('0'::('1'::[])))
            (seq
              X86_BASE_PARSER.Coq_char_t
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              operand_t))
              anybit
              modrm)))
        (fun p ->
        let (w,
             r) =
          Obj.magic
            p
        in
        let (op1,
             op2) =
          r
        in
        Obj.magic
          (MOV
          (w,
          op1,
          op2))))
      (alt
        instruction_t
        (map
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          operand_t))))
          instruction_t
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            operand_t))))
            ('1'::('0'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t,
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              operand_t))))
              ('1'::('0'::('0'::[])))
              (seq
                X86_BASE_PARSER.Coq_char_t
                (X86_BASE_PARSER.Coq_pair_t
                (operand_t,
                operand_t))
                anybit
                modrm)))
          (fun p ->
          let (w,
               r) =
            Obj.magic
              p
          in
          let (op1,
               op2) =
            r
          in
          Obj.magic
            (MOV
            (w,
            op2,
            op1))))
        (alt
          instruction_t
          (map
            (X86_BASE_PARSER.Coq_pair_t
            (register_t,
            operand_t))
            instruction_t
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (register_t,
              operand_t))
              ('1'::('1'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (register_t,
                operand_t))
                ('0'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (register_t,
                  operand_t))
                  ('1'::('1'::[]))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (register_t,
                    operand_t))
                    ('0'::('0'::('0'::[])))
                    (seq
                      register_t
                      operand_t
                      reg
                      (imm_op
                        opsize_override))))))
            (fun p ->
            let (r,
                 w) =
              Obj.magic
                p
            in
            Obj.magic
              (MOV
              (true,
              (Reg_op
              r),
              w))))
          (alt
            instruction_t
            (map
              (X86_BASE_PARSER.Coq_pair_t
              (register_t,
              byte_t))
              instruction_t
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (register_t,
                byte_t))
                ('1'::('1'::('0'::('0'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (register_t,
                  byte_t))
                  ('0'::('1'::('1'::('0'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (register_t,
                    byte_t))
                    ('1'::('1'::[]))
                    (bitsleft
                      (X86_BASE_PARSER.Coq_pair_t
                      (register_t,
                      byte_t))
                      ('0'::('0'::('0'::[])))
                      (seq
                        register_t
                        byte_t
                        reg
                        byte)))))
              (fun p ->
              let (r,
                   b) =
                Obj.magic
                  p
              in
              Obj.magic
                (MOV
                (false,
                (Reg_op
                r),
                (Imm_op
                (zero_extend8_32
                  b))))))
            (alt
              instruction_t
              (map
                (X86_BASE_PARSER.Coq_pair_t
                (register_t,
                operand_t))
                instruction_t
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (register_t,
                  operand_t))
                  ('1'::('0'::('1'::('1'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (register_t,
                    operand_t))
                    ('1'::[])
                    (seq
                      register_t
                      operand_t
                      reg
                      (imm_op
                        opsize_override))))
                (fun p ->
                let (r,
                     w) =
                  Obj.magic
                    p
                in
                Obj.magic
                  (MOV
                  (true,
                  (Reg_op
                  r),
                  w))))
              (alt
                instruction_t
                (map
                  (X86_BASE_PARSER.Coq_pair_t
                  (register_t,
                  byte_t))
                  instruction_t
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (register_t,
                    byte_t))
                    ('1'::('0'::('1'::('1'::[]))))
                    (bitsleft
                      (X86_BASE_PARSER.Coq_pair_t
                      (register_t,
                      byte_t))
                      ('0'::[])
                      (seq
                        register_t
                        byte_t
                        reg
                        byte)))
                  (fun p ->
                  let (r,
                       b) =
                    Obj.magic
                      p
                  in
                  Obj.magic
                    (MOV
                    (false,
                    (Reg_op
                    r),
                    (Imm_op
                    (zero_extend8_32
                      b))))))
                (alt
                  instruction_t
                  (map
                    (X86_BASE_PARSER.Coq_pair_t
                    (operand_t,
                    operand_t))
                    instruction_t
                    (bitsleft
                      (X86_BASE_PARSER.Coq_pair_t
                      (operand_t,
                      operand_t))
                      ('1'::('1'::('0'::('0'::[]))))
                      (bitsleft
                        (X86_BASE_PARSER.Coq_pair_t
                        (operand_t,
                        operand_t))
                        ('0'::('1'::('1'::('1'::[]))))
                        (seq
                          operand_t
                          operand_t
                          (ext_op_modrm
                            ('0'::('0'::('0'::[]))))
                          (imm_op
                            opsize_override))))
                    (fun p ->
                    let (op,
                         w) =
                      Obj.magic
                        p
                    in
                    Obj.magic
                      (MOV
                      (true,
                      op,
                      w))))
                  (alt
                    instruction_t
                    (map
                      (X86_BASE_PARSER.Coq_pair_t
                      (operand_t,
                      byte_t))
                      instruction_t
                      (bitsleft
                        (X86_BASE_PARSER.Coq_pair_t
                        (operand_t,
                        byte_t))
                        ('1'::('1'::('0'::('0'::[]))))
                        (bitsleft
                          (X86_BASE_PARSER.Coq_pair_t
                          (operand_t,
                          byte_t))
                          ('0'::('1'::('1'::('0'::[]))))
                          (seq
                            operand_t
                            byte_t
                            (ext_op_modrm
                              ('0'::('0'::('0'::[]))))
                            byte)))
                      (fun p ->
                      let (op,
                           b) =
                        Obj.magic
                          p
                      in
                      Obj.magic
                        (MOV
                        (false,
                        op,
                        (Imm_op
                        (zero_extend8_32
                          b))))))
                    (alt
                      instruction_t
                      (map
                        word_t
                        instruction_t
                        (bitsleft
                          word_t
                          ('1'::('0'::('1'::('0'::[]))))
                          (bitsleft
                            word_t
                            ('0'::('0'::('0'::('1'::[]))))
                            word))
                        (fun w ->
                        Obj.magic
                          (MOV
                          (true,
                          (Reg_op
                          EAX),
                          (Offset_op
                          (Obj.magic
                            w))))))
                      (alt
                        instruction_t
                        (map
                          word_t
                          instruction_t
                          (bitsleft
                            word_t
                            ('1'::('0'::('1'::('0'::[]))))
                            (bitsleft
                              word_t
                              ('0'::('0'::('0'::('0'::[]))))
                              word))
                          (fun w ->
                          Obj.magic
                            (MOV
                            (false,
                            (Reg_op
                            EAX),
                            (Offset_op
                            (Obj.magic
                              w))))))
                        (alt
                          instruction_t
                          (map
                            word_t
                            instruction_t
                            (bitsleft
                              word_t
                              ('1'::('0'::('1'::('0'::[]))))
                              (bitsleft
                                word_t
                                ('0'::('0'::('1'::('1'::[]))))
                                word))
                            (fun w ->
                            Obj.magic
                              (MOV
                              (true,
                              (Offset_op
                              (Obj.magic
                                w)),
                              (Reg_op
                              EAX)))))
                          (map
                            word_t
                            instruction_t
                            (bitsleft
                              word_t
                              ('1'::('0'::('1'::('0'::[]))))
                              (bitsleft
                                word_t
                                ('0'::('0'::('1'::('0'::[]))))
                                word))
                            (fun w ->
                            Obj.magic
                              (MOV
                              (false,
                              (Offset_op
                              (Obj.magic
                                w)),
                              (Reg_op
                              EAX)))))))))))))))
  
  (** val control_reg_p :
      X86_BASE_PARSER.coq_parser **)
  
  let control_reg_p =
    alt
      control_register_t
      (map
        (bits_n
          (length
            ('0'::('0'::('0'::[])))))
        control_register_t
        (bits
          ('0'::('0'::('0'::[]))))
        (fun x ->
        Obj.magic
          CR0))
      (alt
        control_register_t
        (map
          (bits_n
            (length
              ('0'::('1'::('0'::[])))))
          control_register_t
          (bits
            ('0'::('1'::('0'::[]))))
          (fun x ->
          Obj.magic
            CR2))
        (alt
          control_register_t
          (map
            (bits_n
              (length
                ('0'::('1'::('1'::[])))))
            control_register_t
            (bits
              ('0'::('1'::('1'::[]))))
            (fun x ->
            Obj.magic
              CR3))
          (map
            (bits_n
              (length
                ('1'::('0'::('0'::[])))))
            control_register_t
            (bits
              ('1'::('0'::('0'::[]))))
            (fun x ->
            Obj.magic
              CR4))))
  
  (** val coq_MOVCR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVCR_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (control_register_t,
        register_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (control_register_t,
          register_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (control_register_t,
            register_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (control_register_t,
              register_t))
              ('0'::('0'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (control_register_t,
                register_t))
                ('0'::('0'::('1'::('0'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (control_register_t,
                  register_t))
                  ('1'::('1'::[]))
                  (seq
                    control_register_t
                    register_t
                    control_reg_p
                    reg))))))
        (fun p ->
        Obj.magic
          (MOVCR
          (false,
          (fst
            (Obj.magic
              p)),
          (snd
            (Obj.magic
              p))))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (control_register_t,
        register_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (control_register_t,
          register_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (control_register_t,
            register_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (control_register_t,
              register_t))
              ('0'::('0'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (control_register_t,
                register_t))
                ('0'::('0'::('0'::('0'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (control_register_t,
                  register_t))
                  ('1'::('1'::[]))
                  (seq
                    control_register_t
                    register_t
                    control_reg_p
                    reg))))))
        (fun p ->
        Obj.magic
          (MOVCR
          (true,
          (fst
            (Obj.magic
              p)),
          (snd
            (Obj.magic
              p))))))
  
  (** val debug_reg_p :
      X86_BASE_PARSER.coq_parser **)
  
  let debug_reg_p =
    alt
      debug_register_t
      (map
        (bits_n
          (length
            ('0'::('0'::('0'::[])))))
        debug_register_t
        (bits
          ('0'::('0'::('0'::[]))))
        (fun x ->
        Obj.magic
          DR0))
      (alt
        debug_register_t
        (map
          (bits_n
            (length
              ('0'::('0'::('1'::[])))))
          debug_register_t
          (bits
            ('0'::('0'::('1'::[]))))
          (fun x ->
          Obj.magic
            DR1))
        (alt
          debug_register_t
          (map
            (bits_n
              (length
                ('0'::('1'::('0'::[])))))
            debug_register_t
            (bits
              ('0'::('1'::('0'::[]))))
            (fun x ->
            Obj.magic
              DR2))
          (alt
            debug_register_t
            (map
              (bits_n
                (length
                  ('0'::('1'::('1'::[])))))
              debug_register_t
              (bits
                ('0'::('1'::('1'::[]))))
              (fun x ->
              Obj.magic
                DR3))
            (alt
              debug_register_t
              (map
                (bits_n
                  (length
                    ('1'::('1'::('0'::[])))))
                debug_register_t
                (bits
                  ('1'::('1'::('0'::[]))))
                (fun x ->
                Obj.magic
                  DR6))
              (map
                (bits_n
                  (length
                    ('1'::('1'::('1'::[])))))
                debug_register_t
                (bits
                  ('1'::('1'::('1'::[]))))
                (fun x ->
                Obj.magic
                  DR7))))))
  
  (** val coq_MOVDR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVDR_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (debug_register_t,
        register_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (debug_register_t,
          register_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (debug_register_t,
            register_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (debug_register_t,
              register_t))
              ('0'::('0'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (debug_register_t,
                register_t))
                ('0'::('0'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (debug_register_t,
                  register_t))
                  ('1'::('1'::[]))
                  (seq
                    debug_register_t
                    register_t
                    debug_reg_p
                    reg))))))
        (fun p ->
        Obj.magic
          (MOVDR
          (false,
          (fst
            (Obj.magic
              p)),
          (snd
            (Obj.magic
              p))))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (debug_register_t,
        register_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (debug_register_t,
          register_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (debug_register_t,
            register_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (debug_register_t,
              register_t))
              ('0'::('0'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (debug_register_t,
                register_t))
                ('0'::('0'::('0'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (debug_register_t,
                  register_t))
                  ('1'::('1'::[]))
                  (seq
                    debug_register_t
                    register_t
                    debug_reg_p
                    reg))))))
        (fun p ->
        Obj.magic
          (MOVDR
          (true,
          (fst
            (Obj.magic
              p)),
          (snd
            (Obj.magic
              p))))))
  
  (** val segment_reg_p :
      X86_BASE_PARSER.coq_parser **)
  
  let segment_reg_p =
    alt
      segment_register_t
      (map
        (bits_n
          (length
            ('0'::('0'::('0'::[])))))
        segment_register_t
        (bits
          ('0'::('0'::('0'::[]))))
        (fun x ->
        Obj.magic
          ES))
      (alt
        segment_register_t
        (map
          (bits_n
            (length
              ('0'::('0'::('1'::[])))))
          segment_register_t
          (bits
            ('0'::('0'::('1'::[]))))
          (fun x ->
          Obj.magic
            CS))
        (alt
          segment_register_t
          (map
            (bits_n
              (length
                ('0'::('1'::('0'::[])))))
            segment_register_t
            (bits
              ('0'::('1'::('0'::[]))))
            (fun x ->
            Obj.magic
              SS))
          (alt
            segment_register_t
            (map
              (bits_n
                (length
                  ('0'::('1'::('1'::[])))))
              segment_register_t
              (bits
                ('0'::('1'::('1'::[]))))
              (fun x ->
              Obj.magic
                DS))
            (alt
              segment_register_t
              (map
                (bits_n
                  (length
                    ('1'::('0'::('0'::[])))))
                segment_register_t
                (bits
                  ('1'::('0'::('0'::[]))))
                (fun x ->
                Obj.magic
                  FS))
              (map
                (bits_n
                  (length
                    ('1'::('0'::('1'::[])))))
                segment_register_t
                (bits
                  ('1'::('0'::('1'::[]))))
                (fun x ->
                Obj.magic
                  GS))))))
  
  (** val seg_modrm :
      X86_BASE_PARSER.coq_parser **)
  
  let seg_modrm =
    alt
      (X86_BASE_PARSER.Coq_pair_t
      (segment_register_t,
      operand_t))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (segment_register_t,
        address_t))
        (X86_BASE_PARSER.Coq_pair_t
        (segment_register_t,
        operand_t))
        (alt
          (X86_BASE_PARSER.Coq_pair_t
          (segment_register_t,
          address_t))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (segment_register_t,
            address_t))
            ('0'::('0'::[]))
            (seq
              segment_register_t
              address_t
              segment_reg_p
              rm00))
          (alt
            (X86_BASE_PARSER.Coq_pair_t
            (segment_register_t,
            address_t))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (segment_register_t,
              address_t))
              ('0'::('1'::[]))
              (seq
                segment_register_t
                address_t
                segment_reg_p
                rm01))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (segment_register_t,
              address_t))
              ('1'::('0'::[]))
              (seq
                segment_register_t
                address_t
                segment_reg_p
                rm10))))
        (fun p ->
        let (sr,
             addr) =
          Obj.magic
            p
        in
        Obj.magic
          (sr,
          (Address_op
          addr))))
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (segment_register_t,
        operand_t))
        ('1'::('1'::[]))
        (seq
          segment_register_t
          operand_t
          segment_reg_p
          reg_op))
  
  (** val coq_MOVSR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVSR_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (segment_register_t,
        operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (segment_register_t,
          operand_t))
          ('1'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (segment_register_t,
            operand_t))
            ('1'::('1'::('1'::('0'::[]))))
            seg_modrm))
        (fun p ->
        Obj.magic
          (MOVSR
          (false,
          (fst
            (Obj.magic
              p)),
          (snd
            (Obj.magic
              p))))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (segment_register_t,
        operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (segment_register_t,
          operand_t))
          ('1'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (segment_register_t,
            operand_t))
            ('1'::('1'::('0'::('0'::[]))))
            seg_modrm))
        (fun p ->
        Obj.magic
          (MOVSR
          (true,
          (fst
            (Obj.magic
              p)),
          (snd
            (Obj.magic
              p))))))
  
  (** val coq_MOVBE_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVBE_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (operand_t,
        operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              operand_t))
              ('0'::('0'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (operand_t,
                operand_t))
                ('1'::('0'::('0'::('0'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (operand_t,
                  operand_t))
                  ('1'::('1'::('1'::('1'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (operand_t,
                    operand_t))
                    ('0'::('0'::('0'::('0'::[]))))
                    modrm))))))
        (fun p ->
        Obj.magic
          (MOVBE
          ((snd
             (Obj.magic
               p)),
          (fst
            (Obj.magic
              p))))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (operand_t,
        operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              operand_t))
              ('0'::('0'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (operand_t,
                operand_t))
                ('1'::('0'::('0'::('0'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (operand_t,
                  operand_t))
                  ('1'::('1'::('1'::('1'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (operand_t,
                    operand_t))
                    ('0'::('0'::('0'::('1'::[]))))
                    modrm))))))
        (fun p ->
        Obj.magic
          (MOVBE
          ((fst
             (Obj.magic
               p)),
          (snd
            (Obj.magic
              p))))))
  
  (** val coq_MOVS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVS_p =
    map
      X86_BASE_PARSER.Coq_char_t
      instruction_t
      (bitsleft
        X86_BASE_PARSER.Coq_char_t
        ('1'::('0'::('1'::('0'::[]))))
        (bitsleft
          X86_BASE_PARSER.Coq_char_t
          ('0'::('1'::('0'::[])))
          anybit))
      (fun x ->
      Obj.magic
        (MOVS
        (Obj.magic
          x)))
  
  (** val coq_MOVSX_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVSX_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (X86_BASE_PARSER.Coq_char_t,
      (X86_BASE_PARSER.Coq_pair_t
      (operand_t,
      operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t
        (operand_t,
        operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            operand_t))))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t,
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              operand_t))))
              ('1'::('1'::('1'::[])))
              (seq
                X86_BASE_PARSER.Coq_char_t
                (X86_BASE_PARSER.Coq_pair_t
                (operand_t,
                operand_t))
                anybit
                modrm)))))
      (fun p ->
      let (w,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (MOVSX
        (w,
        op1,
        op2)))
  
  (** val coq_MOVZX_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVZX_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (X86_BASE_PARSER.Coq_char_t,
      (X86_BASE_PARSER.Coq_pair_t
      (operand_t,
      operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t
        (operand_t,
        operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            operand_t))))
            ('1'::('0'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t,
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              operand_t))))
              ('0'::('1'::('1'::[])))
              (seq
                X86_BASE_PARSER.Coq_char_t
                (X86_BASE_PARSER.Coq_pair_t
                (operand_t,
                operand_t))
                anybit
                modrm)))))
      (fun p ->
      let (w,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (MOVZX
        (w,
        op1,
        op2)))
  
  (** val coq_MUL_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MUL_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (X86_BASE_PARSER.Coq_char_t,
      operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        operand_t))
        ('1'::('1'::('1'::('1'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          operand_t))
          ('0'::('1'::('1'::[])))
          (seq
            X86_BASE_PARSER.Coq_char_t
            operand_t
            anybit
            (ext_op_modrm2
              ('1'::('0'::('0'::[])))))))
      (fun p ->
      Obj.magic
        (MUL
        ((fst
           (Obj.magic
             p)),
        (snd
          (Obj.magic
            p)))))
  
  (** val coq_NEG_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_NEG_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (X86_BASE_PARSER.Coq_char_t,
      operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        operand_t))
        ('1'::('1'::('1'::('1'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          operand_t))
          ('0'::('1'::('1'::[])))
          (seq
            X86_BASE_PARSER.Coq_char_t
            operand_t
            anybit
            (ext_op_modrm2
              ('0'::('1'::('1'::[])))))))
      (fun p ->
      Obj.magic
        (NEG
        ((fst
           (Obj.magic
             p)),
        (snd
          (Obj.magic
            p)))))
  
  (** val coq_NOT_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_NOT_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (X86_BASE_PARSER.Coq_char_t,
      operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        operand_t))
        ('1'::('1'::('1'::('1'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          operand_t))
          ('0'::('1'::('1'::[])))
          (seq
            X86_BASE_PARSER.Coq_char_t
            operand_t
            anybit
            (ext_op_modrm2
              ('0'::('1'::('0'::[])))))))
      (fun p ->
      Obj.magic
        (NOT
        ((fst
           (Obj.magic
             p)),
        (snd
          (Obj.magic
            p)))))
  
  (** val coq_OUT_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_OUT_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        byte_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          byte_t))
          ('1'::('1'::('1'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            byte_t))
            ('0'::('1'::('1'::[])))
            (seq
              X86_BASE_PARSER.Coq_char_t
              byte_t
              anybit
              byte)))
        (fun p ->
        Obj.magic
          (OUT
          ((fst
             (Obj.magic
               p)),
          (Some
          (snd
            (Obj.magic
              p)))))))
      (map
        X86_BASE_PARSER.Coq_char_t
        instruction_t
        (bitsleft
          X86_BASE_PARSER.Coq_char_t
          ('1'::('1'::('1'::('0'::[]))))
          (bitsleft
            X86_BASE_PARSER.Coq_char_t
            ('1'::('1'::('1'::[])))
            anybit))
        (fun w ->
        Obj.magic
          (OUT
          ((Obj.magic
             w),
          None))))
  
  (** val coq_OUTS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_OUTS_p =
    map
      X86_BASE_PARSER.Coq_char_t
      instruction_t
      (bitsleft
        X86_BASE_PARSER.Coq_char_t
        ('0'::('1'::('1'::('0'::[]))))
        (bitsleft
          X86_BASE_PARSER.Coq_char_t
          ('1'::('1'::('1'::[])))
          anybit))
      (fun x ->
      Obj.magic
        (OUTS
        (Obj.magic
          x)))
  
  (** val coq_POP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_POP_p =
    alt
      instruction_t
      (map
        operand_t
        instruction_t
        (bitsleft
          operand_t
          ('1'::('0'::('0'::('0'::[]))))
          (bitsleft
            operand_t
            ('1'::('1'::('1'::('1'::[]))))
            (ext_op_modrm2
              ('0'::('0'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (POP
          (Obj.magic
            x))))
      (map
        register_t
        instruction_t
        (bitsleft
          register_t
          ('0'::('1'::('0'::('1'::[]))))
          (bitsleft
            register_t
            ('1'::[])
            reg))
        (fun r ->
        Obj.magic
          (POP
          (Reg_op
          (Obj.magic
            r)))))
  
  (** val coq_POPSR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_POPSR_p =
    alt
      instruction_t
      (map
        (bits_n
          (length
            ('1'::('1'::('1'::[])))))
        instruction_t
        (bitsleft
          (bits_n
            (length
              ('1'::('1'::('1'::[])))))
          ('0'::('0'::('0'::[])))
          (bitsleft
            (bits_n
              (length
                ('1'::('1'::('1'::[])))))
            ('0'::('0'::[]))
            (bits
              ('1'::('1'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (POPSR
          ES)))
      (alt
        instruction_t
        (map
          (bits_n
            (length
              ('1'::('1'::('1'::[])))))
          instruction_t
          (bitsleft
            (bits_n
              (length
                ('1'::('1'::('1'::[])))))
            ('0'::('0'::('0'::[])))
            (bitsleft
              (bits_n
                (length
                  ('1'::('1'::('1'::[])))))
              ('1'::('0'::[]))
              (bits
                ('1'::('1'::('1'::[]))))))
          (fun x ->
          Obj.magic
            (POPSR
            SS)))
        (alt
          instruction_t
          (map
            (bits_n
              (length
                ('1'::('1'::('1'::[])))))
            instruction_t
            (bitsleft
              (bits_n
                (length
                  ('1'::('1'::('1'::[])))))
              ('0'::('0'::('0'::[])))
              (bitsleft
                (bits_n
                  (length
                    ('1'::('1'::('1'::[])))))
                ('1'::('1'::[]))
                (bits
                  ('1'::('1'::('1'::[]))))))
            (fun x ->
            Obj.magic
              (POPSR
              DS)))
          (alt
            instruction_t
            (map
              (bits_n
                (length
                  ('0'::('0'::('1'::[])))))
              instruction_t
              (bitsleft
                (bits_n
                  (length
                    ('0'::('0'::('1'::[])))))
                ('0'::('0'::('0'::('0'::[]))))
                (bitsleft
                  (bits_n
                    (length
                      ('0'::('0'::('1'::[])))))
                  ('1'::('1'::('1'::('1'::[]))))
                  (bitsleft
                    (bits_n
                      (length
                        ('0'::('0'::('1'::[])))))
                    ('1'::('0'::[]))
                    (bitsleft
                      (bits_n
                        (length
                          ('0'::('0'::('1'::[])))))
                      ('1'::('0'::('0'::[])))
                      (bits
                        ('0'::('0'::('1'::[]))))))))
              (fun x ->
              Obj.magic
                (POPSR
                FS)))
            (map
              (bits_n
                (length
                  ('0'::('0'::('1'::[])))))
              instruction_t
              (bitsleft
                (bits_n
                  (length
                    ('0'::('0'::('1'::[])))))
                ('0'::('0'::('0'::('0'::[]))))
                (bitsleft
                  (bits_n
                    (length
                      ('0'::('0'::('1'::[])))))
                  ('1'::('1'::('1'::('1'::[]))))
                  (bitsleft
                    (bits_n
                      (length
                        ('0'::('0'::('1'::[])))))
                    ('1'::('0'::[]))
                    (bitsleft
                      (bits_n
                        (length
                          ('0'::('0'::('1'::[])))))
                      ('1'::('0'::('1'::[])))
                      (bits
                        ('0'::('0'::('1'::[]))))))))
              (fun x ->
              Obj.magic
                (POPSR
                GS))))))
  
  (** val coq_POPA_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_POPA_p =
    map
      (bits_n
        (length
          ('0'::('0'::('0'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('0'::('0'::('1'::[]))))))
        ('0'::('1'::('1'::('0'::[]))))
        (bits
          ('0'::('0'::('0'::('1'::[]))))))
      (fun x ->
      Obj.magic
        POPA)
  
  (** val coq_POPF_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_POPF_p =
    map
      (bits_n
        (length
          ('1'::('1'::('0'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('1'::('0'::('1'::[]))))))
        ('1'::('0'::('0'::('1'::[]))))
        (bits
          ('1'::('1'::('0'::('1'::[]))))))
      (fun x ->
      Obj.magic
        POPF)
  
  (** val coq_PUSH_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PUSH_p =
    alt
      instruction_t
      (map
        operand_t
        instruction_t
        (bitsleft
          operand_t
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            operand_t
            ('1'::('1'::('1'::('1'::[]))))
            (ext_op_modrm
              ('1'::('1'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (PUSH
          (true,
          (Obj.magic
            x)))))
      (alt
        instruction_t
        (map
          register_t
          instruction_t
          (bitsleft
            register_t
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              register_t
              ('0'::[])
              reg))
          (fun r ->
          Obj.magic
            (PUSH
            (true,
            (Reg_op
            (Obj.magic
              r))))))
        (alt
          instruction_t
          (map
            byte_t
            instruction_t
            (bitsleft
              byte_t
              ('0'::('1'::('1'::('0'::[]))))
              (bitsleft
                byte_t
                ('1'::('0'::('1'::('0'::[]))))
                byte))
            (fun b ->
            Obj.magic
              (PUSH
              (false,
              (Imm_op
              (sign_extend8_32
                (Obj.magic
                  b)))))))
          (map
            word_t
            instruction_t
            (bitsleft
              word_t
              ('0'::('1'::('1'::('0'::[]))))
              (bitsleft
                word_t
                ('1'::('0'::('0'::('0'::[]))))
                word))
            (fun w ->
            Obj.magic
              (PUSH
              (true,
              (Imm_op
              (Obj.magic
                w))))))))
  
  (** val segment_reg2_p :
      X86_BASE_PARSER.coq_parser **)
  
  let segment_reg2_p =
    alt
      segment_register_t
      (map
        (bits_n
          (length
            ('0'::('0'::[]))))
        segment_register_t
        (bits
          ('0'::('0'::[])))
        (fun x ->
        Obj.magic
          ES))
      (alt
        segment_register_t
        (map
          (bits_n
            (length
              ('0'::('1'::[]))))
          segment_register_t
          (bits
            ('0'::('1'::[])))
          (fun x ->
          Obj.magic
            CS))
        (alt
          segment_register_t
          (map
            (bits_n
              (length
                ('1'::('0'::[]))))
            segment_register_t
            (bits
              ('1'::('0'::[])))
            (fun x ->
            Obj.magic
              SS))
          (map
            (bits_n
              (length
                ('1'::('1'::[]))))
            segment_register_t
            (bits
              ('1'::('1'::[])))
            (fun x ->
            Obj.magic
              DS))))
  
  (** val coq_PUSHSR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PUSHSR_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (segment_register_t,
        (bits_n
          (length
            ('1'::('1'::('0'::[])))))))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (segment_register_t,
          (bits_n
            (length
              ('1'::('1'::('0'::[])))))))
          ('0'::('0'::('0'::[])))
          (seq
            segment_register_t
            (bits_n
              (length
                ('1'::('1'::('0'::[])))))
            segment_reg2_p
            (bits
              ('1'::('1'::('0'::[]))))))
        (fun p ->
        Obj.magic
          (PUSHSR
          (fst
            (Obj.magic
              p)))))
      (alt
        instruction_t
        (map
          (bits_n
            (length
              ('0'::('0'::('0'::[])))))
          instruction_t
          (bitsleft
            (bits_n
              (length
                ('0'::('0'::('0'::[])))))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (bits_n
                (length
                  ('0'::('0'::('0'::[])))))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (bits_n
                  (length
                    ('0'::('0'::('0'::[])))))
                ('1'::('0'::[]))
                (bitsleft
                  (bits_n
                    (length
                      ('0'::('0'::('0'::[])))))
                  ('1'::('0'::('0'::[])))
                  (bits
                    ('0'::('0'::('0'::[]))))))))
          (fun x ->
          Obj.magic
            (PUSHSR
            FS)))
        (map
          (bits_n
            (length
              ('0'::('0'::('0'::[])))))
          instruction_t
          (bitsleft
            (bits_n
              (length
                ('0'::('0'::('0'::[])))))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (bits_n
                (length
                  ('0'::('0'::('0'::[])))))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (bits_n
                  (length
                    ('0'::('0'::('0'::[])))))
                ('1'::('0'::[]))
                (bitsleft
                  (bits_n
                    (length
                      ('0'::('0'::('0'::[])))))
                  ('1'::('0'::('1'::[])))
                  (bits
                    ('0'::('0'::('0'::[]))))))))
          (fun x ->
          Obj.magic
            (PUSHSR
            GS))))
  
  (** val coq_PUSHA_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PUSHA_p =
    map
      (bits_n
        (length
          ('0'::('0'::('0'::('0'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('0'::('0'::('0'::[]))))))
        ('0'::('1'::('1'::('0'::[]))))
        (bits
          ('0'::('0'::('0'::('0'::[]))))))
      (fun x ->
      Obj.magic
        PUSHA)
  
  (** val coq_PUSHF_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PUSHF_p =
    map
      (bits_n
        (length
          ('1'::('1'::('0'::('0'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('1'::('0'::('0'::[]))))))
        ('1'::('0'::('0'::('1'::[]))))
        (bits
          ('1'::('1'::('0'::('0'::[]))))))
      (fun x ->
      Obj.magic
        PUSHF)
  
  (** val rotate_p :
      char list
      ->
      (bool
      ->
      operand
      ->
      reg_or_immed
      ->
      instr)
      ->
      X86_BASE_PARSER.coq_parser **)
  
  let rotate_p extop inst =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          operand_t))
          ('1'::('1'::('0'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            operand_t))
            ('0'::('0'::('0'::[])))
            (seq
              X86_BASE_PARSER.Coq_char_t
              operand_t
              anybit
              (ext_op_modrm2
                extop))))
        (fun p ->
        Obj.magic
          inst
          (fst
            (Obj.magic
              p))
          (snd
            (Obj.magic
              p))
          (Imm_ri
          (Word.repr
            (Big.succ
            (Big.succ
            (Big.succ
            (Big.succ
            (Big.succ
            (Big.succ
            (Big.succ
            Big.zero)))))))
            Big.one))))
      (alt
        instruction_t
        (map
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          operand_t))
          instruction_t
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            operand_t))
            ('1'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t,
              operand_t))
              ('0'::('0'::('1'::[])))
              (seq
                X86_BASE_PARSER.Coq_char_t
                operand_t
                anybit
                (ext_op_modrm2
                  extop))))
          (fun p ->
          Obj.magic
            inst
            (fst
              (Obj.magic
                p))
            (snd
              (Obj.magic
                p))
            (Reg_ri
            ECX)))
        (map
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          byte_t))))
          instruction_t
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            byte_t))))
            ('1'::('1'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t,
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              byte_t))))
              ('0'::('0'::('0'::[])))
              (seq
                X86_BASE_PARSER.Coq_char_t
                (X86_BASE_PARSER.Coq_pair_t
                (operand_t,
                byte_t))
                anybit
                (seq
                  operand_t
                  byte_t
                  (ext_op_modrm2
                    extop)
                  byte))))
          (fun p ->
          let (w,
               r) =
            Obj.magic
              p
          in
          let (op,
               b) =
            r
          in
          Obj.magic
            inst
            w
            op
            (Imm_ri
            b))))
  
  (** val coq_RCL_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_RCL_p =
    rotate_p
      ('0'::('1'::('0'::[])))
      (fun x x0 x1 ->
      RCL
      (x,
      x0,
      x1))
  
  (** val coq_RCR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_RCR_p =
    rotate_p
      ('0'::('1'::('1'::[])))
      (fun x x0 x1 ->
      RCR
      (x,
      x0,
      x1))
  
  (** val coq_RDMSR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_RDMSR_p =
    map
      (bits_n
        (length
          ('0'::('0'::('1'::('0'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('0'::('1'::('0'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (bits_n
            (length
              ('0'::('0'::('1'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (bits_n
              (length
                ('0'::('0'::('1'::('0'::[]))))))
            ('0'::('0'::('1'::('1'::[]))))
            (bits
              ('0'::('0'::('1'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        RDMSR)
  
  (** val coq_RDPMC_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_RDPMC_p =
    map
      (bits_n
        (length
          ('0'::('0'::('1'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('0'::('1'::('1'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (bits_n
            (length
              ('0'::('0'::('1'::('1'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (bits_n
              (length
                ('0'::('0'::('1'::('1'::[]))))))
            ('0'::('0'::('1'::('1'::[]))))
            (bits
              ('0'::('0'::('1'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        RDPMC)
  
  (** val coq_RDTSC_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_RDTSC_p =
    map
      (bits_n
        (length
          ('0'::('0'::('0'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('0'::('0'::('1'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (bits_n
            (length
              ('0'::('0'::('0'::('1'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (bits_n
              (length
                ('0'::('0'::('0'::('1'::[]))))))
            ('0'::('0'::('1'::('1'::[]))))
            (bits
              ('0'::('0'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        RDTSC)
  
  (** val coq_RDTSCP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_RDTSCP_p =
    map
      (bits_n
        (length
          ('1'::('0'::('0'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('0'::('1'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (bits_n
            (length
              ('1'::('0'::('0'::('1'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (bits_n
              (length
                ('1'::('0'::('0'::('1'::[]))))))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (bits_n
                (length
                  ('1'::('0'::('0'::('1'::[]))))))
              ('0'::('0'::('0'::('1'::[]))))
              (bitsleft
                (bits_n
                  (length
                    ('1'::('0'::('0'::('1'::[]))))))
                ('1'::('1'::('1'::('1'::[]))))
                (bits
                  ('1'::('0'::('0'::('1'::[]))))))))))
      (fun x ->
      Obj.magic
        RDTSCP)
  
  (** val coq_RET_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_RET_p =
    alt
      instruction_t
      (map
        (bits_n
          (length
            ('0'::('0'::('1'::('1'::[]))))))
        instruction_t
        (bitsleft
          (bits_n
            (length
              ('0'::('0'::('1'::('1'::[]))))))
          ('1'::('1'::('0'::('0'::[]))))
          (bits
            ('0'::('0'::('1'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (RET
          (true,
          None))))
      (alt
        instruction_t
        (map
          half_t
          instruction_t
          (bitsleft
            half_t
            ('1'::('1'::('0'::('0'::[]))))
            (bitsleft
              half_t
              ('0'::('0'::('1'::('0'::[]))))
              halfword))
          (fun h ->
          Obj.magic
            (RET
            (true,
            (Some
            (Obj.magic
              h))))))
        (alt
          instruction_t
          (map
            (bits_n
              (length
                ('1'::('0'::('1'::('1'::[]))))))
            instruction_t
            (bitsleft
              (bits_n
                (length
                  ('1'::('0'::('1'::('1'::[]))))))
              ('1'::('1'::('0'::('0'::[]))))
              (bits
                ('1'::('0'::('1'::('1'::[]))))))
            (fun x ->
            Obj.magic
              (RET
              (false,
              None))))
          (map
            half_t
            instruction_t
            (bitsleft
              half_t
              ('1'::('1'::('0'::('0'::[]))))
              (bitsleft
                half_t
                ('1'::('0'::('1'::('0'::[]))))
                halfword))
            (fun h ->
            Obj.magic
              (RET
              (false,
              (Some
              (Obj.magic
                h))))))))
  
  (** val coq_ROL_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_ROL_p =
    rotate_p
      ('0'::('0'::('0'::[])))
      (fun x x0 x1 ->
      ROL
      (x,
      x0,
      x1))
  
  (** val coq_ROR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_ROR_p =
    rotate_p
      ('0'::('0'::('1'::[])))
      (fun x x0 x1 ->
      ROR
      (x,
      x0,
      x1))
  
  (** val coq_RSM_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_RSM_p =
    map
      (bits_n
        (length
          ('1'::('0'::('1'::('0'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('1'::('0'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (bits_n
            (length
              ('1'::('0'::('1'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (bits_n
              (length
                ('1'::('0'::('1'::('0'::[]))))))
            ('1'::('0'::('1'::('0'::[]))))
            (bits
              ('1'::('0'::('1'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        RSM)
  
  (** val coq_SAHF_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SAHF_p =
    map
      (bits_n
        (length
          ('1'::('1'::('1'::('0'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('1'::('1'::('0'::[]))))))
        ('1'::('0'::('0'::('1'::[]))))
        (bits
          ('1'::('1'::('1'::('0'::[]))))))
      (fun x ->
      Obj.magic
        SAHF)
  
  (** val coq_SAR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SAR_p =
    rotate_p
      ('1'::('1'::('1'::[])))
      (fun x x0 x1 ->
      SAR
      (x,
      x0,
      x1))
  
  (** val coq_SCAS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SCAS_p =
    map
      X86_BASE_PARSER.Coq_char_t
      instruction_t
      (bitsleft
        X86_BASE_PARSER.Coq_char_t
        ('1'::('0'::('1'::('0'::[]))))
        (bitsleft
          X86_BASE_PARSER.Coq_char_t
          ('1'::('1'::('1'::[])))
          anybit))
      (fun x ->
      Obj.magic
        (SCAS
        (Obj.magic
          x)))
  
  (** val coq_SETcc_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SETcc_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (condition_t,
      (X86_BASE_PARSER.Coq_pair_t
      (operand_t,
      operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (condition_t,
        (X86_BASE_PARSER.Coq_pair_t
        (operand_t,
        operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (condition_t,
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (condition_t,
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            operand_t))))
            ('1'::('0'::('0'::('1'::[]))))
            (seq
              condition_t
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              operand_t))
              tttn
              modrm))))
      (fun p ->
      Obj.magic
        (SETcc
        ((fst
           (Obj.magic
             p)),
        (snd
          (snd
            (Obj.magic
              p))))))
  
  (** val coq_SGDT_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SGDT_p =
    map
      operand_t
      instruction_t
      (bitsleft
        operand_t
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          operand_t
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            operand_t
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              operand_t
              ('0'::('0'::('0'::('1'::[]))))
              (ext_op_modrm
                ('0'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        (SGDT
        (Obj.magic
          x)))
  
  (** val coq_SHL_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SHL_p =
    rotate_p
      ('1'::('0'::('0'::[])))
      (fun x x0 x1 ->
      SHL
      (x,
      x0,
      x1))
  
  (** val shiftdouble_p :
      char list
      ->
      (operand
      ->
      register
      ->
      reg_or_immed
      ->
      X86_BASE_PARSER.result_m)
      ->
      X86_BASE_PARSER.coq_parser **)
  
  let shiftdouble_p opcode inst =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (register_t,
        (X86_BASE_PARSER.Coq_pair_t
        (register_t,
        byte_t))))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (register_t,
          (X86_BASE_PARSER.Coq_pair_t
          (register_t,
          byte_t))))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (register_t,
            (X86_BASE_PARSER.Coq_pair_t
            (register_t,
            byte_t))))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (register_t,
              (X86_BASE_PARSER.Coq_pair_t
              (register_t,
              byte_t))))
              ('1'::('0'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (register_t,
                (X86_BASE_PARSER.Coq_pair_t
                (register_t,
                byte_t))))
                opcode
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (register_t,
                  (X86_BASE_PARSER.Coq_pair_t
                  (register_t,
                  byte_t))))
                  ('0'::('0'::[]))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (register_t,
                    (X86_BASE_PARSER.Coq_pair_t
                    (register_t,
                    byte_t))))
                    ('1'::('1'::[]))
                    (seq
                      register_t
                      (X86_BASE_PARSER.Coq_pair_t
                      (register_t,
                      byte_t))
                      reg
                      (seq
                        register_t
                        byte_t
                        reg
                        byte))))))))
        (fun p ->
        let (r2,
             r) =
          Obj.magic
            p
        in
        let (r1,
             b) =
          r
        in
        inst
          (Reg_op
          r1)
          r2
          (Imm_ri
          b)))
      (alt
        instruction_t
        (map
          (X86_BASE_PARSER.Coq_pair_t
          ((X86_BASE_PARSER.Coq_pair_t
          (register_t,
          operand_t)),
          byte_t))
          instruction_t
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            ((X86_BASE_PARSER.Coq_pair_t
            (register_t,
            operand_t)),
            byte_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              ((X86_BASE_PARSER.Coq_pair_t
              (register_t,
              operand_t)),
              byte_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                ((X86_BASE_PARSER.Coq_pair_t
                (register_t,
                operand_t)),
                byte_t))
                ('1'::('0'::('1'::('0'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  ((X86_BASE_PARSER.Coq_pair_t
                  (register_t,
                  operand_t)),
                  byte_t))
                  opcode
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    ((X86_BASE_PARSER.Coq_pair_t
                    (register_t,
                    operand_t)),
                    byte_t))
                    ('0'::('0'::[]))
                    (seq
                      (X86_BASE_PARSER.Coq_pair_t
                      (register_t,
                      operand_t))
                      byte_t
                      modrm_noreg
                      byte))))))
          (fun p ->
          let (r0,
               b) =
            Obj.magic
              p
          in
          let (r,
               op) =
            r0
          in
          inst
            op
            r
            (Imm_ri
            b)))
        (alt
          instruction_t
          (map
            (X86_BASE_PARSER.Coq_pair_t
            (register_t,
            register_t))
            instruction_t
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (register_t,
              register_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (register_t,
                register_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (register_t,
                  register_t))
                  ('1'::('0'::('1'::('0'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (register_t,
                    register_t))
                    opcode
                    (bitsleft
                      (X86_BASE_PARSER.Coq_pair_t
                      (register_t,
                      register_t))
                      ('0'::('1'::[]))
                      (bitsleft
                        (X86_BASE_PARSER.Coq_pair_t
                        (register_t,
                        register_t))
                        ('1'::('1'::[]))
                        (seq
                          register_t
                          register_t
                          reg
                          reg)))))))
            (fun p ->
            let (r2,
                 r1) =
              Obj.magic
                p
            in
            inst
              (Reg_op
              r1)
              r2
              (Reg_ri
              ECX)))
          (map
            (X86_BASE_PARSER.Coq_pair_t
            (register_t,
            operand_t))
            instruction_t
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (register_t,
              operand_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (register_t,
                operand_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (register_t,
                  operand_t))
                  ('1'::('0'::('1'::('0'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (register_t,
                    operand_t))
                    opcode
                    (bitsleft
                      (X86_BASE_PARSER.Coq_pair_t
                      (register_t,
                      operand_t))
                      ('0'::('1'::[]))
                      modrm_noreg)))))
            (fun p ->
            let (r,
                 op) =
              Obj.magic
                p
            in
            inst
              op
              r
              (Reg_ri
              ECX)))))
  
  (** val coq_SHLD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SHLD_p =
    shiftdouble_p
      ('0'::('1'::[]))
      (Obj.magic
        (fun x x0 x1 ->
        SHLD
        (x,
        x0,
        x1)))
  
  (** val coq_SHR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SHR_p =
    rotate_p
      ('1'::('0'::('1'::[])))
      (fun x x0 x1 ->
      SHR
      (x,
      x0,
      x1))
  
  (** val coq_SHRD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SHRD_p =
    shiftdouble_p
      ('1'::('1'::[]))
      (Obj.magic
        (fun x x0 x1 ->
        SHRD
        (x,
        x0,
        x1)))
  
  (** val coq_SIDT_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SIDT_p =
    map
      operand_t
      instruction_t
      (bitsleft
        operand_t
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          operand_t
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            operand_t
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              operand_t
              ('0'::('0'::('0'::('1'::[]))))
              (ext_op_modrm
                ('0'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        (SIDT
        (Obj.magic
          x)))
  
  (** val coq_SLDT_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SLDT_p =
    map
      operand_t
      instruction_t
      (bitsleft
        operand_t
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          operand_t
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            operand_t
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              operand_t
              ('0'::('0'::('0'::('0'::[]))))
              (ext_op_modrm
                ('0'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        (SLDT
        (Obj.magic
          x)))
  
  (** val coq_SMSW_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SMSW_p =
    map
      operand_t
      instruction_t
      (bitsleft
        operand_t
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          operand_t
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            operand_t
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              operand_t
              ('0'::('0'::('0'::('1'::[]))))
              (ext_op_modrm
                ('1'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        (SMSW
        (Obj.magic
          x)))
  
  (** val coq_STC_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_STC_p =
    map
      (bits_n
        (length
          ('1'::('0'::('0'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('0'::('1'::[]))))))
        ('1'::('1'::('1'::('1'::[]))))
        (bits
          ('1'::('0'::('0'::('1'::[]))))))
      (fun x ->
      Obj.magic
        STC)
  
  (** val coq_STD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_STD_p =
    map
      (bits_n
        (length
          ('1'::('1'::('0'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('1'::('0'::('1'::[]))))))
        ('1'::('1'::('1'::('1'::[]))))
        (bits
          ('1'::('1'::('0'::('1'::[]))))))
      (fun x ->
      Obj.magic
        STD)
  
  (** val coq_STI_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_STI_p =
    map
      (bits_n
        (length
          ('1'::('0'::('1'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('1'::('1'::[]))))))
        ('1'::('1'::('1'::('1'::[]))))
        (bits
          ('1'::('0'::('1'::('1'::[]))))))
      (fun x ->
      Obj.magic
        STI)
  
  (** val coq_STOS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_STOS_p =
    map
      X86_BASE_PARSER.Coq_char_t
      instruction_t
      (bitsleft
        X86_BASE_PARSER.Coq_char_t
        ('1'::('0'::('1'::('0'::[]))))
        (bitsleft
          X86_BASE_PARSER.Coq_char_t
          ('1'::('0'::('1'::[])))
          anybit))
      (fun x ->
      Obj.magic
        (STOS
        (Obj.magic
          x)))
  
  (** val coq_STR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_STR_p =
    map
      operand_t
      instruction_t
      (bitsleft
        operand_t
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          operand_t
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            operand_t
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              operand_t
              ('0'::('0'::('0'::('0'::[]))))
              (ext_op_modrm
                ('0'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        (STR
        (Obj.magic
          x)))
  
  (** val coq_TEST_p :
      bool
      ->
      X86_BASE_PARSER.coq_parser **)
  
  let coq_TEST_p opsize_override =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (operand_t,
        operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            operand_t))
            ('0'::('1'::('1'::('1'::[]))))
            (seq
              operand_t
              operand_t
              (ext_op_modrm2
                ('0'::('0'::('0'::[]))))
              (imm_op
                opsize_override))))
        (fun p ->
        Obj.magic
          (TEST
          (true,
          (fst
            (Obj.magic
              p)),
          (snd
            (Obj.magic
              p))))))
      (alt
        instruction_t
        (map
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          byte_t))
          instruction_t
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            byte_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              byte_t))
              ('0'::('1'::('1'::('0'::[]))))
              (seq
                operand_t
                byte_t
                (ext_op_modrm2
                  ('0'::('0'::('0'::[]))))
                byte)))
          (fun p ->
          Obj.magic
            (TEST
            (false,
            (fst
              (Obj.magic
                p)),
            (Imm_op
            (zero_extend8_32
              (snd
                (Obj.magic
                  p))))))))
        (alt
          instruction_t
          (map
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            operand_t))))
            instruction_t
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t,
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              operand_t))))
              ('1'::('0'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (X86_BASE_PARSER.Coq_char_t,
                (X86_BASE_PARSER.Coq_pair_t
                (operand_t,
                operand_t))))
                ('0'::('1'::('0'::[])))
                (seq
                  X86_BASE_PARSER.Coq_char_t
                  (X86_BASE_PARSER.Coq_pair_t
                  (operand_t,
                  operand_t))
                  anybit
                  modrm)))
            (fun p ->
            let (w,
                 r) =
              Obj.magic
                p
            in
            let (op1,
                 op2) =
              r
            in
            Obj.magic
              (TEST
              (w,
              op1,
              op2))))
          (alt
            instruction_t
            (map
              operand_t
              instruction_t
              (bitsleft
                operand_t
                ('1'::('0'::('1'::('0'::[]))))
                (bitsleft
                  operand_t
                  ('1'::('0'::('0'::('1'::[]))))
                  (imm_op
                    opsize_override)))
              (fun w ->
              Obj.magic
                (TEST
                (true,
                (Obj.magic
                  w),
                (Reg_op
                EAX)))))
            (map
              byte_t
              instruction_t
              (bitsleft
                byte_t
                ('1'::('0'::('1'::('0'::[]))))
                (bitsleft
                  byte_t
                  ('1'::('0'::('0'::('0'::[]))))
                  byte))
              (fun b ->
              Obj.magic
                (TEST
                (true,
                (Imm_op
                (zero_extend8_32
                  (Obj.magic
                    b))),
                (Reg_op
                EAX))))))))
  
  (** val coq_UD2_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_UD2_p =
    map
      (bits_n
        (length
          ('1'::('0'::('1'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('1'::('1'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (bits_n
            (length
              ('1'::('0'::('1'::('1'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (bits_n
              (length
                ('1'::('0'::('1'::('1'::[]))))))
            ('0'::('0'::('0'::('0'::[]))))
            (bits
              ('1'::('0'::('1'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        UD2)
  
  (** val coq_VERR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_VERR_p =
    map
      operand_t
      instruction_t
      (bitsleft
        operand_t
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          operand_t
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            operand_t
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              operand_t
              ('0'::('0'::('0'::('0'::[]))))
              (ext_op_modrm
                ('1'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        (VERR
        (Obj.magic
          x)))
  
  (** val coq_VERW_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_VERW_p =
    map
      operand_t
      instruction_t
      (bitsleft
        operand_t
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          operand_t
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            operand_t
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              operand_t
              ('0'::('0'::('0'::('0'::[]))))
              (ext_op_modrm
                ('1'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        (VERW
        (Obj.magic
          x)))
  
  (** val coq_WBINVD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_WBINVD_p =
    map
      (bits_n
        (length
          ('1'::('0'::('0'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('0'::('1'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (bits_n
            (length
              ('1'::('0'::('0'::('1'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (bits_n
              (length
                ('1'::('0'::('0'::('1'::[]))))))
            ('0'::('0'::('0'::('0'::[]))))
            (bits
              ('1'::('0'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        WBINVD)
  
  (** val coq_WRMSR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_WRMSR_p =
    map
      (bits_n
        (length
          ('0'::('0'::('0'::('0'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('0'::('0'::('0'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (bits_n
            (length
              ('0'::('0'::('0'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (bits_n
              (length
                ('0'::('0'::('0'::('0'::[]))))))
            ('0'::('0'::('1'::('1'::[]))))
            (bits
              ('0'::('0'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        WRMSR)
  
  (** val coq_XADD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_XADD_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (X86_BASE_PARSER.Coq_char_t,
      (X86_BASE_PARSER.Coq_pair_t
      (operand_t,
      operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t
        (operand_t,
        operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            operand_t))))
            ('1'::('1'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t,
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              operand_t))))
              ('0'::('0'::('0'::[])))
              (seq
                X86_BASE_PARSER.Coq_char_t
                (X86_BASE_PARSER.Coq_pair_t
                (operand_t,
                operand_t))
                anybit
                modrm)))))
      (fun p ->
      let (w,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (XADD
        (w,
        op2,
        op1)))
  
  (** val coq_XCHG_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_XCHG_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t
        (operand_t,
        operand_t))))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t
          (operand_t,
          operand_t))))
          ('1'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t
            (operand_t,
            operand_t))))
            ('0'::('1'::('1'::[])))
            (seq
              X86_BASE_PARSER.Coq_char_t
              (X86_BASE_PARSER.Coq_pair_t
              (operand_t,
              operand_t))
              anybit
              modrm)))
        (fun p ->
        let (w,
             r) =
          Obj.magic
            p
        in
        let (op1,
             op2) =
          r
        in
        Obj.magic
          (XCHG
          (w,
          op1,
          op2))))
      (map
        register_t
        instruction_t
        (bitsleft
          register_t
          ('1'::('0'::('0'::('1'::[]))))
          (bitsleft
            register_t
            ('0'::[])
            reg))
        (fun r ->
        Obj.magic
          (XCHG
          (true,
          (Reg_op
          EAX),
          (Reg_op
          (Obj.magic
            r))))))
  
  (** val coq_XLAT_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_XLAT_p =
    map
      (bits_n
        (length
          ('0'::('1'::('1'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('1'::('1'::('1'::[]))))))
        ('1'::('1'::('0'::('1'::[]))))
        (bits
          ('0'::('1'::('1'::('1'::[]))))))
      (fun x ->
      Obj.magic
        XLAT)
  
  (** val coq_F2XM1_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_F2XM1_p =
    map
      (bits_n
        (length
          ('1'::('0'::('0'::('0'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('0'::('0'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('0'::('0'::('0'::('0'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('1'::('0'::('0'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        F2XM1)
  
  (** val coq_FABS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FABS_p =
    map
      (bits_n
        (length
          ('0'::('0'::('0'::('0'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('0'::('0'::('0'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('0'::('0'::('0'::('1'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('0'::('0'::('0'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        FABS)
  
  (** val coq_FADD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FADD_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('0'::('0'::[])))
            (ext_op_modrm_FPM32
              ('0'::('0'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FADD
          (true,
          (Obj.magic
            x)))))
      (alt
        instruction_t
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('1'::('0'::('0'::[])))
              (ext_op_modrm_FPM64
                ('0'::('0'::('0'::[]))))))
          (fun x ->
          Obj.magic
            (FADD
            (true,
            (Obj.magic
              x)))))
        (map
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          fpu_register_t))
          instruction_t
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            fpu_register_t))
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (seq
              X86_BASE_PARSER.Coq_char_t
              fpu_register_t
              anybit
              (bitsleft
                fpu_register_t
                ('0'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))
                fpu_reg)))
          (fun p ->
          let (d,
               s) =
            Obj.magic
              p
          in
          Obj.magic
            (FADD
            (d,
            (FPS_op
            s))))))
  
  (** val coq_FADDP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FADDP_p =
    map
      fpu_register_t
      instruction_t
      (bitsleft
        fpu_register_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fpu_register_t
          ('1'::('1'::('0'::[])))
          (bitsleft
            fpu_register_t
            ('1'::('1'::('0'::('0'::('0'::[])))))
            fpu_reg)))
      (fun x ->
      Obj.magic
        (FADDP
        (FPS_op
        (Obj.magic
          x))))
  
  (** val coq_FBLD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FBLD_p =
    map
      fp_operand_t
      instruction_t
      (bitsleft
        fp_operand_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fp_operand_t
          ('1'::('1'::('1'::[])))
          (ext_op_modrm_FPM64
            ('1'::('0'::('0'::[]))))))
      (fun x ->
      Obj.magic
        (FBLD
        (Obj.magic
          x)))
  
  (** val coq_FBSTP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FBSTP_p =
    map
      fp_operand_t
      instruction_t
      (bitsleft
        fp_operand_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fp_operand_t
          ('1'::('1'::('1'::[])))
          (ext_op_modrm_FPM64
            ('1'::('1'::('0'::[]))))))
      (fun x ->
      Obj.magic
        (FBSTP
        (Obj.magic
          x)))
  
  (** val coq_FCHS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FCHS_p =
    map
      (bits_n
        (length
          ('0'::('0'::('0'::('0'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('0'::('0'::('0'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('0'::('0'::('0'::('0'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('0'::('0'::('0'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FCHS)
  
  (** val coq_FCLEX_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FCLEX_p =
    map
      (bits_n
        (length
          ('0'::('0'::('0'::('1'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('0'::('0'::('1'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('0'::('0'::('1'::('0'::[])))))))
          ('0'::('1'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('0'::('0'::('0'::('1'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FCLEX)
  
  (** val coq_FCMOVcc_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FCMOVcc_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (X86_BASE_PARSER.Coq_char_t,
      (X86_BASE_PARSER.Coq_pair_t
      (X86_BASE_PARSER.Coq_char_t,
      (X86_BASE_PARSER.Coq_pair_t
      (X86_BASE_PARSER.Coq_char_t,
      fpu_register_t))))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        (X86_BASE_PARSER.Coq_pair_t
        (X86_BASE_PARSER.Coq_char_t,
        fpu_register_t))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          fpu_register_t))))))
          ('0'::('1'::[]))
          (seq
            X86_BASE_PARSER.Coq_char_t
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            fpu_register_t))))
            anybit
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t,
              (X86_BASE_PARSER.Coq_pair_t
              (X86_BASE_PARSER.Coq_char_t,
              fpu_register_t))))
              ('1'::('1'::('0'::[])))
              (seq
                X86_BASE_PARSER.Coq_char_t
                (X86_BASE_PARSER.Coq_pair_t
                (X86_BASE_PARSER.Coq_char_t,
                fpu_register_t))
                anybit
                (seq
                  X86_BASE_PARSER.Coq_char_t
                  fpu_register_t
                  anybit
                  fpu_reg))))))
      (fun p ->
      let (b2,
           r) =
        Obj.magic
          p
      in
      let (b1,
           r0) =
        r
      in
      let (b0,
           s) =
        r0
      in
      let n =
        bits2int
          (Big.succ
          (Big.succ
          (Big.succ
          Big.zero)))
          (Obj.magic
            (b2,
            (b1,
            (b0,
            ()))))
      in
      Obj.magic
        (FCMOVcc
        ((coq_Z_to_fp_condition_type
           (Obj.magic
             n)),
        (FPS_op
        s))))
  
  (** val coq_FCOM_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FCOM_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('0'::('0'::[])))
            (ext_op_modrm_FPM32
              ('0'::('1'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FCOM
          (Some
          (Obj.magic
            x)))))
      (alt
        instruction_t
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('1'::('0'::('0'::[])))
              (ext_op_modrm_FPM64
                ('0'::('1'::('0'::[]))))))
          (fun x ->
          Obj.magic
            (FCOM
            (Some
            (Obj.magic
              x)))))
        (map
          fpu_register_t
          instruction_t
          (bitsleft
            fpu_register_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fpu_register_t
              ('0'::('0'::('0'::[])))
              (bitsleft
                fpu_register_t
                ('1'::('1'::('0'::('1'::('0'::[])))))
                fpu_reg)))
          (fun x ->
          Obj.magic
            (FCOM
            (Some
            (FPS_op
            (Obj.magic
              x)))))))
  
  (** val coq_FCOMP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FCOMP_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('0'::('0'::[])))
            (ext_op_modrm_FPM32
              ('0'::('1'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FCOMP
          (Some
          (Obj.magic
            x)))))
      (alt
        instruction_t
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('1'::('0'::('0'::[])))
              (ext_op_modrm_FPM64
                ('0'::('1'::('1'::[]))))))
          (fun x ->
          Obj.magic
            (FCOMP
            (Some
            (Obj.magic
              x)))))
        (map
          fpu_register_t
          instruction_t
          (bitsleft
            fpu_register_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fpu_register_t
              ('0'::('0'::('0'::[])))
              (bitsleft
                fpu_register_t
                ('1'::('1'::('0'::('1'::('1'::[])))))
                fpu_reg)))
          (fun x ->
          Obj.magic
            (FCOMP
            (Some
            (FPS_op
            (Obj.magic
              x)))))))
  
  (** val coq_FCOMPP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FCOMPP_p =
    map
      (bits_n
        (length
          ('0'::('0'::('1'::[])))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('0'::('1'::[])))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('0'::('1'::[])))))
          ('1'::('1'::('0'::[])))
          (bitsleft
            (bits_n
              (length
                ('0'::('0'::('1'::[])))))
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bits
              ('0'::('0'::('1'::[])))))))
      (fun x ->
      Obj.magic
        FCOMPP)
  
  (** val coq_FCOMIP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FCOMIP_p =
    map
      fpu_register_t
      instruction_t
      (bitsleft
        fpu_register_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fpu_register_t
          ('1'::('1'::('1'::[])))
          (bitsleft
            fpu_register_t
            ('1'::('1'::('1'::('1'::('0'::[])))))
            fpu_reg)))
      (fun x ->
      Obj.magic
        (FCOMIP
        (FPS_op
        (Obj.magic
          x))))
  
  (** val coq_FCOS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FCOS_p =
    map
      (bits_n
        (length
          ('1'::('1'::('1'::('1'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('1'::('1'::('1'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('1'::('1'::('1'::('1'::[])))))))
          ('0'::('0'::('1'::[])))
          (bitsleft
            (bits_n
              (length
                ('1'::('1'::('1'::('1'::('1'::[])))))))
            ('1'::('1'::('1'::[])))
            (bits
              ('1'::('1'::('1'::('1'::('1'::[])))))))))
      (fun x ->
      Obj.magic
        FCOS)
  
  (** val coq_FDECSTP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FDECSTP_p =
    map
      (bits_n
        (length
          ('1'::('0'::('1'::('1'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('1'::('1'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('0'::('1'::('1'::('0'::[])))))))
          ('0'::('0'::('1'::[])))
          (bitsleft
            (bits_n
              (length
                ('1'::('0'::('1'::('1'::('0'::[])))))))
            ('1'::('1'::('1'::[])))
            (bits
              ('1'::('0'::('1'::('1'::('0'::[])))))))))
      (fun x ->
      Obj.magic
        FDECSTP)
  
  (** val coq_FDIV_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FDIV_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('0'::('0'::[])))
            (ext_op_modrm_FPM32
              ('1'::('1'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FDIV
          ((FPS_op
          (Word.zero
            (Big.succ
            (Big.succ
            Big.zero)))),
          (Obj.magic
            x)))))
      (alt
        instruction_t
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('1'::('0'::('0'::[])))
              (ext_op_modrm_FPM64
                ('1'::('1'::('0'::[]))))))
          (fun x ->
          Obj.magic
            (FDIV
            ((FPS_op
            (Word.zero
              (Big.succ
              (Big.succ
              Big.zero)))),
            (Obj.magic
              x)))))
        (alt
          instruction_t
          (map
            fpu_register_t
            instruction_t
            (bitsleft
              fpu_register_t
              ('1'::('1'::('0'::('1'::('1'::[])))))
              (bitsleft
                fpu_register_t
                ('0'::[])
                (bitsleft
                  fpu_register_t
                  ('0'::('0'::[]))
                  (bitsleft
                    fpu_register_t
                    ('1'::('1'::('1'::('1'::[]))))
                    (bitsleft
                      fpu_register_t
                      ('0'::[])
                      fpu_reg)))))
            (fun i ->
            Obj.magic
              (FDIV
              ((FPS_op
              (Word.zero
                (Big.succ
                (Big.succ
                Big.zero)))),
              (FPS_op
              (Obj.magic
                i))))))
          (map
            fpu_register_t
            instruction_t
            (bitsleft
              fpu_register_t
              ('1'::('1'::('0'::('1'::('1'::[])))))
              (bitsleft
                fpu_register_t
                ('1'::[])
                (bitsleft
                  fpu_register_t
                  ('0'::('0'::[]))
                  (bitsleft
                    fpu_register_t
                    ('1'::('1'::('1'::[])))
                    (bitsleft
                      fpu_register_t
                      ('1'::[])
                      (bitsleft
                        fpu_register_t
                        ('1'::[])
                        fpu_reg))))))
            (fun i ->
            Obj.magic
              (FDIV
              ((FPS_op
              (Obj.magic
                i)),
              (FPS_op
              (Word.zero
                (Big.succ
                (Big.succ
                Big.zero))))))))))
  
  (** val coq_FDIVP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FDIVP_p =
    map
      fpu_register_t
      instruction_t
      (bitsleft
        fpu_register_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fpu_register_t
          ('1'::('1'::('0'::[])))
          (bitsleft
            fpu_register_t
            ('1'::('1'::('1'::('1'::('1'::[])))))
            fpu_reg)))
      (fun x ->
      Obj.magic
        (FDIVP
        (FPS_op
        (Obj.magic
          x))))
  
  (** val coq_FDIVR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FDIVR_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('0'::('0'::[])))
            (ext_op_modrm_FPM32
              ('1'::('1'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FDIVR
          ((FPS_op
          (Word.zero
            (Big.succ
            (Big.succ
            Big.zero)))),
          (Obj.magic
            x)))))
      (alt
        instruction_t
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('1'::('0'::('0'::[])))
              (ext_op_modrm_FPM64
                ('1'::('1'::('1'::[]))))))
          (fun x ->
          Obj.magic
            (FDIVR
            ((FPS_op
            (Word.zero
              (Big.succ
              (Big.succ
              Big.zero)))),
            (Obj.magic
              x)))))
        (alt
          instruction_t
          (map
            fpu_register_t
            instruction_t
            (bitsleft
              fpu_register_t
              ('1'::('1'::('0'::('1'::('1'::[])))))
              (bitsleft
                fpu_register_t
                ('0'::[])
                (bitsleft
                  fpu_register_t
                  ('0'::('0'::[]))
                  (bitsleft
                    fpu_register_t
                    ('1'::('1'::('1'::[])))
                    (bitsleft
                      fpu_register_t
                      ('1'::[])
                      (bitsleft
                        fpu_register_t
                        ('1'::[])
                        fpu_reg))))))
            (fun i ->
            Obj.magic
              (FDIVR
              ((FPS_op
              (Word.zero
                (Big.succ
                (Big.succ
                Big.zero)))),
              (FPS_op
              (Obj.magic
                i))))))
          (map
            fpu_register_t
            instruction_t
            (bitsleft
              fpu_register_t
              ('1'::('1'::('0'::('1'::('1'::[])))))
              (bitsleft
                fpu_register_t
                ('1'::[])
                (bitsleft
                  fpu_register_t
                  ('0'::('0'::[]))
                  (bitsleft
                    fpu_register_t
                    ('1'::('1'::('1'::[])))
                    (bitsleft
                      fpu_register_t
                      ('1'::[])
                      (bitsleft
                        fpu_register_t
                        ('0'::[])
                        fpu_reg))))))
            (fun i ->
            Obj.magic
              (FDIVR
              ((FPS_op
              (Obj.magic
                i)),
              (FPS_op
              (Word.zero
                (Big.succ
                (Big.succ
                Big.zero))))))))))
  
  (** val coq_FDIVRP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FDIVRP_p =
    map
      fpu_register_t
      instruction_t
      (bitsleft
        fpu_register_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fpu_register_t
          ('1'::('1'::('0'::[])))
          (bitsleft
            fpu_register_t
            ('1'::('1'::('1'::('1'::('0'::[])))))
            fpu_reg)))
      (fun x ->
      Obj.magic
        (FDIVRP
        (FPS_op
        (Obj.magic
          x))))
  
  (** val coq_FFREE_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FFREE_p =
    map
      fpu_register_t
      instruction_t
      (bitsleft
        fpu_register_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fpu_register_t
          ('1'::('0'::('1'::[])))
          (bitsleft
            fpu_register_t
            ('1'::('1'::('0'::('0'::('0'::[])))))
            fpu_reg)))
      (fun x ->
      Obj.magic
        (FFREE
        (FPS_op
        (Obj.magic
          x))))
  
  (** val coq_FIADD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FIADD_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::[])))
            (ext_op_modrm_FPM16
              ('0'::('0'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FIADD
          (Obj.magic
            x))))
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('1'::('0'::[])))
            (ext_op_modrm_FPM32
              ('0'::('0'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FIADD
          (Obj.magic
            x))))
  
  (** val coq_FICOM_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FICOM_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::[])))
            (ext_op_modrm_FPM16
              ('0'::('1'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FICOM
          (Obj.magic
            x))))
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('1'::('0'::[])))
            (ext_op_modrm_FPM32
              ('0'::('1'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FICOM
          (Obj.magic
            x))))
  
  (** val coq_FICOMP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FICOMP_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::[])))
            (ext_op_modrm_FPM16
              ('0'::('1'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FICOMP
          (Obj.magic
            x))))
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('1'::('0'::[])))
            (ext_op_modrm_FPM32
              ('0'::('1'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FICOMP
          (Obj.magic
            x))))
  
  (** val coq_FIDIV_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FIDIV_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::[])))
            (ext_op_modrm_FPM16
              ('1'::('1'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FIDIV
          (Obj.magic
            x))))
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('1'::('0'::[])))
            (ext_op_modrm_FPM32
              ('1'::('1'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FIDIV
          (Obj.magic
            x))))
  
  (** val coq_FIDIVR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FIDIVR_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::[])))
            (ext_op_modrm_FPM16
              ('1'::('1'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FIDIVR
          (Obj.magic
            x))))
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('1'::('0'::[])))
            (ext_op_modrm_FPM32
              ('1'::('1'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FIDIVR
          (Obj.magic
            x))))
  
  (** val coq_FILD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FILD_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('1'::('1'::('1'::[])))
            (ext_op_modrm_FPM16
              ('0'::('0'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FILD
          (Obj.magic
            x))))
      (alt
        instruction_t
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('0'::('1'::('1'::[])))
              (ext_op_modrm_FPM32
                ('0'::('0'::('0'::[]))))))
          (fun x ->
          Obj.magic
            (FILD
            (Obj.magic
              x))))
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('1'::('1'::('1'::[])))
              (ext_op_modrm_FPM64
                ('1'::('0'::('1'::[]))))))
          (fun x ->
          Obj.magic
            (FILD
            (Obj.magic
              x)))))
  
  (** val coq_FIMUL_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FIMUL_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::[])))
            (ext_op_modrm_FPM16
              ('0'::('0'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FIMUL
          (Obj.magic
            x))))
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('1'::('0'::[])))
            (ext_op_modrm_FPM32
              ('0'::('0'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FIMUL
          (Obj.magic
            x))))
  
  (** val coq_FINCSTP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FINCSTP_p =
    map
      (bits_n
        (length
          ('1'::('0'::('1'::('1'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('1'::('1'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('0'::('1'::('1'::('1'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('1'::('0'::('1'::('1'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        FINCSTP)
  
  (** val coq_FIST_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FIST_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('1'::('1'::('1'::[])))
            (ext_op_modrm_FPM16
              ('0'::('1'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FIST
          (Obj.magic
            x))))
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('1'::('1'::[])))
            (ext_op_modrm_FPM32
              ('0'::('1'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FIST
          (Obj.magic
            x))))
  
  (** val coq_FISTP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FISTP_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('1'::('1'::('1'::[])))
            (ext_op_modrm_FPM16
              ('0'::('1'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FISTP
          (Obj.magic
            x))))
      (alt
        instruction_t
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('0'::('1'::('1'::[])))
              (ext_op_modrm_FPM32
                ('0'::('1'::('1'::[]))))))
          (fun x ->
          Obj.magic
            (FISTP
            (Obj.magic
              x))))
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('1'::('1'::('1'::[])))
              (ext_op_modrm_FPM64
                ('1'::('1'::('1'::[]))))))
          (fun x ->
          Obj.magic
            (FISTP
            (Obj.magic
              x)))))
  
  (** val coq_FISUB_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FISUB_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::[])))
            (ext_op_modrm_FPM16
              ('1'::('0'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FISUB
          (Obj.magic
            x))))
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('1'::('0'::[])))
            (ext_op_modrm_FPM32
              ('1'::('0'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FISUB
          (Obj.magic
            x))))
  
  (** val coq_FISUBR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FISUBR_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::[])))
            (ext_op_modrm_FPM16
              ('1'::('0'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FISUBR
          (Obj.magic
            x))))
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('1'::('0'::[])))
            (ext_op_modrm_FPM32
              ('1'::('0'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FISUBR
          (Obj.magic
            x))))
  
  (** val coq_FLD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FLD_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('0'::('1'::[])))
            (ext_op_modrm_FPM32
              ('0'::('0'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FLD
          (Obj.magic
            x))))
      (alt
        instruction_t
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('1'::('0'::('1'::[])))
              (ext_op_modrm_FPM64
                ('0'::('0'::('0'::[]))))))
          (fun x ->
          Obj.magic
            (FLD
            (Obj.magic
              x))))
        (alt
          instruction_t
          (map
            fp_operand_t
            instruction_t
            (bitsleft
              fp_operand_t
              ('1'::('1'::('0'::('1'::('1'::[])))))
              (bitsleft
                fp_operand_t
                ('0'::('1'::('1'::[])))
                (ext_op_modrm_FPM80
                  ('1'::('0'::('1'::[]))))))
            (fun x ->
            Obj.magic
              (FLD
              (Obj.magic
                x))))
          (map
            fpu_register_t
            instruction_t
            (bitsleft
              fpu_register_t
              ('1'::('1'::('0'::('1'::('1'::[])))))
              (bitsleft
                fpu_register_t
                ('0'::('0'::('1'::[])))
                (bitsleft
                  fpu_register_t
                  ('1'::('1'::('0'::('0'::('0'::[])))))
                  fpu_reg)))
            (fun x ->
            Obj.magic
              (FLD
              (FPS_op
              (Obj.magic
                x)))))))
  
  (** val coq_FLD1_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FLD1_p =
    map
      (bits_n
        (length
          ('0'::('1'::('0'::('0'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('1'::('0'::('0'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('1'::('0'::('0'::('0'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('0'::('1'::('0'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FLD1)
  
  (** val coq_FLDCW_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FLDCW_p =
    map
      fp_operand_t
      instruction_t
      (bitsleft
        fp_operand_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fp_operand_t
          ('0'::('0'::('1'::[])))
          (ext_op_modrm_FPM32
            ('1'::('0'::('1'::[]))))))
      (fun x ->
      Obj.magic
        (FLDCW
        (Obj.magic
          x)))
  
  (** val coq_FLDENV_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FLDENV_p =
    map
      fp_operand_t
      instruction_t
      (bitsleft
        fp_operand_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fp_operand_t
          ('0'::('0'::('1'::[])))
          (ext_op_modrm_FPM32
            ('1'::('0'::('0'::[]))))))
      (fun x ->
      Obj.magic
        (FLDENV
        (Obj.magic
          x)))
  
  (** val coq_FLDL2E_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FLDL2E_p =
    map
      (bits_n
        (length
          ('0'::('1'::('0'::('1'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('1'::('0'::('1'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('1'::('0'::('1'::('0'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('0'::('1'::('0'::('1'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FLDL2E)
  
  (** val coq_FLDL2T_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FLDL2T_p =
    map
      (bits_n
        (length
          ('0'::('1'::('0'::('0'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('1'::('0'::('0'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('1'::('0'::('0'::('1'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('0'::('1'::('0'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        FLDL2T)
  
  (** val coq_FLDLG2_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FLDLG2_p =
    map
      (bits_n
        (length
          ('0'::('1'::('1'::('0'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('1'::('1'::('0'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('1'::('1'::('0'::('0'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('0'::('1'::('1'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FLDLG2)
  
  (** val coq_FLDLN2_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FLDLN2_p =
    map
      (bits_n
        (length
          ('0'::('1'::('1'::('0'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('1'::('1'::('0'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('1'::('1'::('0'::('1'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('0'::('1'::('1'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        FLDLN2)
  
  (** val coq_FLDPI_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FLDPI_p =
    map
      (bits_n
        (length
          ('0'::('1'::('0'::('1'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('1'::('0'::('1'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('1'::('0'::('1'::('1'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('0'::('1'::('0'::('1'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        FLDPI)
  
  (** val coq_FLDZ_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FLDZ_p =
    map
      (bits_n
        (length
          ('0'::('1'::('1'::('1'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('1'::('1'::('1'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('1'::('1'::('1'::('0'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('0'::('1'::('1'::('1'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FLDZ)
  
  (** val coq_FMUL_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FMUL_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('0'::('0'::[])))
            (ext_op_modrm_FPM32
              ('0'::('0'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FMUL
          (true,
          (Obj.magic
            x)))))
      (alt
        instruction_t
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('1'::('0'::('0'::[])))
              (ext_op_modrm_FPM64
                ('0'::('0'::('1'::[]))))))
          (fun x ->
          Obj.magic
            (FMUL
            (true,
            (Obj.magic
              x)))))
        (map
          (X86_BASE_PARSER.Coq_pair_t
          (X86_BASE_PARSER.Coq_char_t,
          fpu_register_t))
          instruction_t
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (X86_BASE_PARSER.Coq_char_t,
            fpu_register_t))
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (seq
              X86_BASE_PARSER.Coq_char_t
              fpu_register_t
              anybit
              (bitsleft
                fpu_register_t
                ('0'::('0'::[]))
                (bitsleft
                  fpu_register_t
                  ('1'::('1'::('0'::('0'::('1'::[])))))
                  fpu_reg))))
          (fun p ->
          let (d,
               s) =
            Obj.magic
              p
          in
          Obj.magic
            (FMUL
            (d,
            (FPS_op
            s))))))
  
  (** val coq_FMULP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FMULP_p =
    map
      fpu_register_t
      instruction_t
      (bitsleft
        fpu_register_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fpu_register_t
          ('1'::('1'::('0'::[])))
          (bitsleft
            fpu_register_t
            ('1'::('1'::('0'::('0'::('1'::[])))))
            fpu_reg)))
      (fun x ->
      Obj.magic
        (FMULP
        (FPS_op
        (Obj.magic
          x))))
  
  (** val coq_FNOP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FNOP_p =
    map
      (bits_n
        (length
          ('1'::('0'::('0'::('0'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('0'::('0'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('0'::('0'::('0'::('0'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('0'::[]))))))
          (bits
            ('1'::('0'::('0'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FNOP)
  
  (** val coq_FNSAVE_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FNSAVE_p =
    map
      fp_operand_t
      instruction_t
      (bitsleft
        fp_operand_t
        ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::[]))))))))
        (ext_op_modrm_FPM64
          ('1'::('1'::('0'::[])))))
      (fun x ->
      Obj.magic
        (FNSAVE
        (Obj.magic
          x)))
  
  (** val coq_FNSTCW_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FNSTCW_p =
    map
      fp_operand_t
      instruction_t
      (bitsleft
        fp_operand_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fp_operand_t
          ('0'::('0'::('1'::[])))
          (ext_op_modrm_FPM32
            ('1'::('1'::('1'::[]))))))
      (fun x ->
      Obj.magic
        (FNSTCW
        (Obj.magic
          x)))
  
  (** val coq_FNSTSW_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FNSTSW_p =
    alt
      instruction_t
      (map
        (bits_n
          (length
            ('0'::('0'::('0'::('0'::('0'::[])))))))
        instruction_t
        (bitsleft
          (bits_n
            (length
              ('0'::('0'::('0'::('0'::('0'::[])))))))
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            (bits_n
              (length
                ('0'::('0'::('0'::('0'::('0'::[])))))))
            ('1'::('1'::('1'::[])))
            (bitsleft
              (bits_n
                (length
                  ('0'::('0'::('0'::('0'::('0'::[])))))))
              ('1'::('1'::('1'::[])))
              (bits
                ('0'::('0'::('0'::('0'::('0'::[])))))))))
        (fun x ->
        Obj.magic
          (FNSTSW
          None)))
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('1'::('0'::('1'::[])))
            (ext_op_modrm_FPM32
              ('1'::('1'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FNSTSW
          (Some
          (Obj.magic
            x)))))
  
  (** val coq_FPATAN_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FPATAN_p =
    map
      (bits_n
        (length
          ('1'::('0'::('0'::('1'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('0'::('1'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('0'::('0'::('1'::('1'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('1'::('0'::('0'::('1'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        FPATAN)
  
  (** val coq_FPREM_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FPREM_p =
    map
      (bits_n
        (length
          ('1'::('1'::('0'::('0'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('1'::('0'::('0'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('1'::('0'::('0'::('0'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('1'::('1'::('0'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FPREM)
  
  (** val coq_FPREM1_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FPREM1_p =
    map
      (bits_n
        (length
          ('1'::('0'::('1'::('0'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('1'::('0'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('0'::('1'::('0'::('1'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('1'::('0'::('1'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        FPREM1)
  
  (** val coq_FPTAN_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FPTAN_p =
    map
      (bits_n
        (length
          ('1'::('0'::('0'::('1'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('0'::('1'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('0'::('0'::('1'::('0'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('1'::('0'::('0'::('1'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FPTAN)
  
  (** val coq_FRNDINT_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FRNDINT_p =
    map
      (bits_n
        (length
          ('1'::('1'::('1'::('0'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('1'::('1'::('0'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('1'::('1'::('0'::('0'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('1'::('1'::('1'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FRNDINT)
  
  (** val coq_FRSTOR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FRSTOR_p =
    map
      fp_operand_t
      instruction_t
      (bitsleft
        fp_operand_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fp_operand_t
          ('1'::('0'::('1'::[])))
          (ext_op_modrm_FPM32
            ('1'::('0'::('0'::[]))))))
      (fun x ->
      Obj.magic
        (FRSTOR
        (Obj.magic
          x)))
  
  (** val coq_FSCALE_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FSCALE_p =
    map
      (bits_n
        (length
          ('1'::('1'::('1'::('0'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('1'::('1'::('0'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('1'::('1'::('0'::('1'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('1'::('1'::('1'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        FSCALE)
  
  (** val coq_FSIN_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FSIN_p =
    map
      (bits_n
        (length
          ('1'::('1'::('1'::('1'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('1'::('1'::('1'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('1'::('1'::('1'::('0'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('1'::('1'::('1'::('1'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FSIN)
  
  (** val coq_FSINCOS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FSINCOS_p =
    map
      (bits_n
        (length
          ('1'::('1'::('0'::('1'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('1'::('0'::('1'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('1'::('0'::('1'::('1'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('1'::('1'::('0'::('1'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        FSINCOS)
  
  (** val coq_FSQRT_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FSQRT_p =
    map
      (bits_n
        (length
          ('1'::('1'::('0'::('1'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('1'::('0'::('1'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('1'::('0'::('1'::('0'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('1'::('1'::('0'::('1'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FSQRT)
  
  (** val coq_FST_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FST_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('0'::('1'::[])))
            (ext_op_modrm_FPM32
              ('0'::('1'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FST
          (Obj.magic
            x))))
      (alt
        instruction_t
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('1'::('0'::('1'::[])))
              (ext_op_modrm_FPM64
                ('0'::('1'::('0'::[]))))))
          (fun x ->
          Obj.magic
            (FST
            (Obj.magic
              x))))
        (map
          fpu_register_t
          instruction_t
          (bitsleft
            fpu_register_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fpu_register_t
              ('1'::('0'::('1'::[])))
              (bitsleft
                fpu_register_t
                ('1'::('1'::('0'::('1'::('0'::[])))))
                fpu_reg)))
          (fun x ->
          Obj.magic
            (FST
            (FPS_op
            (Obj.magic
              x))))))
  
  (** val coq_FSTENV_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FSTENV_p =
    map
      fp_operand_t
      instruction_t
      (bitsleft
        fp_operand_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fp_operand_t
          ('0'::('0'::('1'::[])))
          (ext_op_modrm_FPM32
            ('1'::('1'::('0'::[]))))))
      (fun x ->
      Obj.magic
        (FSTENV
        (Obj.magic
          x)))
  
  (** val coq_FSTP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FSTP_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('0'::('1'::[])))
            (ext_op_modrm_FPM32
              ('0'::('1'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FSTP
          (Obj.magic
            x))))
      (alt
        instruction_t
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('1'::('0'::('1'::[])))
              (ext_op_modrm_FPM64
                ('0'::('1'::('1'::[]))))))
          (fun x ->
          Obj.magic
            (FSTP
            (Obj.magic
              x))))
        (alt
          instruction_t
          (map
            fp_operand_t
            instruction_t
            (bitsleft
              fp_operand_t
              ('1'::('1'::('0'::('1'::('1'::[])))))
              (bitsleft
                fp_operand_t
                ('0'::('1'::('1'::[])))
                (ext_op_modrm_FPM80
                  ('1'::('1'::('1'::[]))))))
            (fun x ->
            Obj.magic
              (FSTP
              (Obj.magic
                x))))
          (map
            fpu_register_t
            instruction_t
            (bitsleft
              fpu_register_t
              ('1'::('1'::('0'::('1'::('1'::[])))))
              (bitsleft
                fpu_register_t
                ('1'::('0'::('1'::[])))
                (bitsleft
                  fpu_register_t
                  ('1'::('1'::('0'::('1'::('1'::[])))))
                  fpu_reg)))
            (fun x ->
            Obj.magic
              (FSTP
              (FPS_op
              (Obj.magic
                x)))))))
  
  (** val coq_FSUB_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FSUB_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('0'::('0'::[])))
            (ext_op_modrm_FPM32
              ('1'::('0'::('0'::[]))))))
        (fun x ->
        Obj.magic
          (FSUB
          ((FPS_op
          (Word.zero
            (Big.succ
            (Big.succ
            Big.zero)))),
          (Obj.magic
            x)))))
      (alt
        instruction_t
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('1'::('0'::('0'::[])))
              (ext_op_modrm_FPM64
                ('1'::('0'::('0'::[]))))))
          (fun x ->
          Obj.magic
            (FSUB
            ((FPS_op
            (Word.zero
              (Big.succ
              (Big.succ
              Big.zero)))),
            (Obj.magic
              x)))))
        (alt
          instruction_t
          (map
            fpu_register_t
            instruction_t
            (bitsleft
              fpu_register_t
              ('1'::('1'::('0'::('1'::('1'::[])))))
              (bitsleft
                fpu_register_t
                ('0'::[])
                (bitsleft
                  fpu_register_t
                  ('0'::('0'::[]))
                  (bitsleft
                    fpu_register_t
                    ('1'::('1'::('1'::[])))
                    (bitsleft
                      fpu_register_t
                      ('0'::[])
                      (bitsleft
                        fpu_register_t
                        ('0'::[])
                        fpu_reg))))))
            (fun i ->
            Obj.magic
              (FSUB
              ((FPS_op
              (Word.zero
                (Big.succ
                (Big.succ
                Big.zero)))),
              (FPS_op
              (Obj.magic
                i))))))
          (map
            fpu_register_t
            instruction_t
            (bitsleft
              fpu_register_t
              ('1'::('1'::('0'::('1'::('1'::[])))))
              (bitsleft
                fpu_register_t
                ('1'::[])
                (bitsleft
                  fpu_register_t
                  ('0'::('0'::[]))
                  (bitsleft
                    fpu_register_t
                    ('1'::('1'::('1'::[])))
                    (bitsleft
                      fpu_register_t
                      ('0'::[])
                      (bitsleft
                        fpu_register_t
                        ('1'::[])
                        fpu_reg))))))
            (fun i ->
            Obj.magic
              (FSUB
              ((FPS_op
              (Obj.magic
                i)),
              (FPS_op
              (Word.zero
                (Big.succ
                (Big.succ
                Big.zero))))))))))
  
  (** val coq_FSUBP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FSUBP_p =
    map
      fpu_register_t
      instruction_t
      (bitsleft
        fpu_register_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fpu_register_t
          ('1'::('1'::('0'::[])))
          (bitsleft
            fpu_register_t
            ('1'::('1'::('1'::('0'::('1'::[])))))
            fpu_reg)))
      (fun x ->
      Obj.magic
        (FSUBP
        (FPS_op
        (Obj.magic
          x))))
  
  (** val coq_FSUBR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FSUBR_p =
    alt
      instruction_t
      (map
        fp_operand_t
        instruction_t
        (bitsleft
          fp_operand_t
          ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft
            fp_operand_t
            ('0'::('0'::('0'::[])))
            (ext_op_modrm_FPM32
              ('1'::('0'::('1'::[]))))))
        (fun x ->
        Obj.magic
          (FSUBR
          ((FPS_op
          (Word.zero
            (Big.succ
            (Big.succ
            Big.zero)))),
          (Obj.magic
            x)))))
      (alt
        instruction_t
        (map
          fp_operand_t
          instruction_t
          (bitsleft
            fp_operand_t
            ('1'::('1'::('0'::('1'::('1'::[])))))
            (bitsleft
              fp_operand_t
              ('1'::('0'::('0'::[])))
              (ext_op_modrm_FPM64
                ('1'::('0'::('1'::[]))))))
          (fun x ->
          Obj.magic
            (FSUBR
            ((FPS_op
            (Word.zero
              (Big.succ
              (Big.succ
              Big.zero)))),
            (Obj.magic
              x)))))
        (alt
          instruction_t
          (map
            fpu_register_t
            instruction_t
            (bitsleft
              fpu_register_t
              ('1'::('1'::('0'::('1'::('1'::[])))))
              (bitsleft
                fpu_register_t
                ('0'::[])
                (bitsleft
                  fpu_register_t
                  ('0'::('0'::[]))
                  (bitsleft
                    fpu_register_t
                    ('1'::('1'::('1'::[])))
                    (bitsleft
                      fpu_register_t
                      ('0'::[])
                      (bitsleft
                        fpu_register_t
                        ('1'::[])
                        fpu_reg))))))
            (fun i ->
            Obj.magic
              (FSUBR
              ((FPS_op
              (Word.zero
                (Big.succ
                (Big.succ
                Big.zero)))),
              (FPS_op
              (Obj.magic
                i))))))
          (map
            fpu_register_t
            instruction_t
            (bitsleft
              fpu_register_t
              ('1'::('1'::('0'::('1'::('1'::[])))))
              (bitsleft
                fpu_register_t
                ('1'::[])
                (bitsleft
                  fpu_register_t
                  ('0'::('0'::[]))
                  (bitsleft
                    fpu_register_t
                    ('1'::('1'::('1'::[])))
                    (bitsleft
                      fpu_register_t
                      ('0'::[])
                      (bitsleft
                        fpu_register_t
                        ('0'::[])
                        fpu_reg))))))
            (fun i ->
            Obj.magic
              (FSUBR
              ((FPS_op
              (Obj.magic
                i)),
              (FPS_op
              (Word.zero
                (Big.succ
                (Big.succ
                Big.zero))))))))))
  
  (** val coq_FSUBRP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FSUBRP_p =
    map
      fpu_register_t
      instruction_t
      (bitsleft
        fpu_register_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fpu_register_t
          ('1'::('1'::('0'::[])))
          (bitsleft
            fpu_register_t
            ('1'::('1'::('1'::('0'::('0'::[])))))
            fpu_reg)))
      (fun x ->
      Obj.magic
        (FSUBRP
        (FPS_op
        (Obj.magic
          x))))
  
  (** val coq_FTST_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FTST_p =
    map
      (bits_n
        (length
          ('0'::('0'::('1'::('0'::('0'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('0'::('1'::('0'::('0'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('0'::('1'::('0'::('0'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('0'::('0'::('1'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FTST)
  
  (** val coq_FUCOM_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FUCOM_p =
    map
      fpu_register_t
      instruction_t
      (bitsleft
        fpu_register_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fpu_register_t
          ('1'::('0'::('1'::[])))
          (bitsleft
            fpu_register_t
            ('1'::('1'::('1'::('0'::('0'::[])))))
            fpu_reg)))
      (fun x ->
      Obj.magic
        (FUCOM
        (FPS_op
        (Obj.magic
          x))))
  
  (** val coq_FUCOMP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FUCOMP_p =
    map
      fpu_register_t
      instruction_t
      (bitsleft
        fpu_register_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fpu_register_t
          ('1'::('0'::('1'::[])))
          (bitsleft
            fpu_register_t
            ('1'::('1'::('1'::('0'::('1'::[])))))
            fpu_reg)))
      (fun x ->
      Obj.magic
        (FUCOMP
        (FPS_op
        (Obj.magic
          x))))
  
  (** val coq_FUCOMPP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FUCOMPP_p =
    map
      (bits_n
        (length
          ('0'::('1'::('0'::('0'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('1'::('0'::('0'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('1'::('0'::('0'::('1'::[])))))))
          ('0'::('1'::('0'::('1'::('1'::('1'::[]))))))
          (bits
            ('0'::('1'::('0'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        FUCOMPP)
  
  (** val coq_FUCOMI_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FUCOMI_p =
    map
      fpu_register_t
      instruction_t
      (bitsleft
        fpu_register_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fpu_register_t
          ('0'::('1'::('1'::[])))
          (bitsleft
            fpu_register_t
            ('1'::('1'::('1'::('0'::('1'::[])))))
            fpu_reg)))
      (fun x ->
      Obj.magic
        (FUCOMI
        (FPS_op
        (Obj.magic
          x))))
  
  (** val coq_FUCOMIP_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FUCOMIP_p =
    map
      fpu_register_t
      instruction_t
      (bitsleft
        fpu_register_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fpu_register_t
          ('1'::('1'::('1'::[])))
          (bitsleft
            fpu_register_t
            ('1'::('1'::('1'::('0'::('1'::[])))))
            fpu_reg)))
      (fun x ->
      Obj.magic
        (FUCOMIP
        (FPS_op
        (Obj.magic
          x))))
  
  (** val coq_FXAM_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FXAM_p =
    map
      (bits_n
        (length
          ('0'::('0'::('1'::('0'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('0'::('1'::('0'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('0'::('1'::('0'::('1'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('0'::('0'::('1'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        FXAM)
  
  (** val coq_FXCH_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FXCH_p =
    map
      fpu_register_t
      instruction_t
      (bitsleft
        fpu_register_t
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          fpu_register_t
          ('0'::('0'::('1'::[])))
          (bitsleft
            fpu_register_t
            ('1'::('1'::('0'::('0'::('1'::[])))))
            fpu_reg)))
      (fun x ->
      Obj.magic
        (FXCH
        (FPS_op
        (Obj.magic
          x))))
  
  (** val coq_FXTRACT_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FXTRACT_p =
    map
      (bits_n
        (length
          ('0'::('1'::('0'::('0'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('1'::('0'::('0'::[]))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('0'::('1'::('0'::('0'::[]))))))
          ('0'::('0'::('1'::[])))
          (bitsleft
            (bits_n
              (length
                ('0'::('1'::('0'::('0'::[]))))))
            ('1'::('1'::('1'::('1'::[]))))
            (bits
              ('0'::('1'::('0'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        FXTRACT)
  
  (** val coq_FYL2X_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FYL2X_p =
    map
      (bits_n
        (length
          ('1'::('0'::('0'::('0'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('0'::('0'::('0'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('0'::('0'::('0'::('1'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('1'::('0'::('0'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        FYL2X)
  
  (** val coq_FYL2XP1_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FYL2XP1_p =
    map
      (bits_n
        (length
          ('1'::('1'::('0'::('0'::('1'::[])))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('1'::('1'::('0'::('0'::('1'::[])))))))
        ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft
          (bits_n
            (length
              ('1'::('1'::('0'::('0'::('1'::[])))))))
          ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
          (bits
            ('1'::('1'::('0'::('0'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        FYL2XP1)
  
  (** val coq_FWAIT_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_FWAIT_p =
    map
      (bits_n
        (length
          ('1'::('0'::('0'::('1'::('1'::('0'::('1'::('1'::[]))))))))))
      instruction_t
      (bits
        ('1'::('0'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))
      (fun x ->
      Obj.magic
        FWAIT)
  
  (** val mmx_gg_p :
      bool
      ->
      bool
      ->
      bool
      ->
      bool
      ->
      X86_BASE_PARSER.coq_parser **)
  
  let mmx_gg_p byte0 twob fourb eightb =
    let byte_p =
      if byte0
      then map
             (bits_n
               (length
                 ('0'::('0'::[]))))
             mmx_granularity_t
             (bits
               ('0'::('0'::[])))
             (fun x ->
             Obj.magic
               MMX_8)
      else never
             mmx_granularity_t
    in
    let twobytes_p =
      if twob
      then map
             (bits_n
               (length
                 ('0'::('1'::[]))))
             mmx_granularity_t
             (bits
               ('0'::('1'::[])))
             (fun x ->
             Obj.magic
               MMX_16)
      else never
             mmx_granularity_t
    in
    let fourbytes_p =
      if fourb
      then map
             (bits_n
               (length
                 ('1'::('0'::[]))))
             mmx_granularity_t
             (bits
               ('1'::('0'::[])))
             (fun x ->
             Obj.magic
               MMX_32)
      else never
             mmx_granularity_t
    in
    let eightbytes_p =
      if eightb
      then map
             (bits_n
               (length
                 ('1'::('1'::[]))))
             mmx_granularity_t
             (bits
               ('1'::('1'::[])))
             (fun x ->
             Obj.magic
               MMX_64)
      else never
             mmx_granularity_t
    in
    alt
      mmx_granularity_t
      byte_p
      (alt
        mmx_granularity_t
        twobytes_p
        (alt
          mmx_granularity_t
          fourbytes_p
          eightbytes_p))
  
  (** val coq_EMMS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_EMMS_p =
    map
      (bits_n
        (length
          ('0'::('1'::('1'::('1'::[]))))))
      instruction_t
      (bitsleft
        (bits_n
          (length
            ('0'::('1'::('1'::('1'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (bits_n
            (length
              ('0'::('1'::('1'::('1'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (bits_n
              (length
                ('0'::('1'::('1'::('1'::[]))))))
            ('0'::('1'::('1'::('1'::[]))))
            (bits
              ('0'::('1'::('1'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        EMMS)
  
  (** val coq_MOVD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVD_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_register_t,
        register_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_register_t,
          register_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_register_t,
            register_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_register_t,
              register_t))
              ('0'::('1'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_register_t,
                register_t))
                ('1'::('1'::('1'::('0'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (mmx_register_t,
                  register_t))
                  ('1'::('1'::[]))
                  (seq
                    mmx_register_t
                    register_t
                    mmx_reg
                    reg))))))
        (fun p ->
        let (m,
             r) =
          Obj.magic
            p
        in
        Obj.magic
          (MOVD
          ((GP_Reg_op
          r),
          (MMX_Reg_op
          m)))))
      (alt
        instruction_t
        (map
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_register_t,
          register_t))
          instruction_t
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_register_t,
            register_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_register_t,
              register_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_register_t,
                register_t))
                ('0'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (mmx_register_t,
                  register_t))
                  ('1'::('1'::('1'::('0'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (mmx_register_t,
                    register_t))
                    ('1'::('1'::[]))
                    (seq
                      mmx_register_t
                      register_t
                      mmx_reg
                      reg))))))
          (fun p ->
          let (m,
               r) =
            Obj.magic
              p
          in
          Obj.magic
            (MOVD
            ((GP_Reg_op
            r),
            (MMX_Reg_op
            m)))))
        (alt
          instruction_t
          (map
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            instruction_t
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (mmx_operand_t,
                  mmx_operand_t))
                  ('0'::('1'::('1'::('0'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (mmx_operand_t,
                    mmx_operand_t))
                    ('1'::('1'::('1'::('0'::[]))))
                    modrm_mmx))))
            (fun p ->
            let (op1,
                 op2) =
              Obj.magic
                p
            in
            Obj.magic
              (MOVD
              (op1,
              op2))))
          (map
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            instruction_t
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (mmx_operand_t,
                  mmx_operand_t))
                  ('0'::('1'::('1'::('1'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (mmx_operand_t,
                    mmx_operand_t))
                    ('1'::('1'::('1'::('0'::[]))))
                    modrm_mmx))))
            (fun p ->
            let (mem,
                 mmx) =
              Obj.magic
                p
            in
            Obj.magic
              (MOVD
              (mmx,
              mem))))))
  
  (** val coq_MOVQ_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVQ_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('0'::('1'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                ('1'::('1'::('1'::('1'::[]))))
                modrm_mmx))))
        (fun p ->
        let (op1,
             op2) =
          Obj.magic
            p
        in
        Obj.magic
          (MOVQ
          (op1,
          op2))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('0'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                ('1'::('1'::('1'::('1'::[]))))
                modrm_mmx))))
        (fun p ->
        let (op1,
             op2) =
          Obj.magic
            p
        in
        Obj.magic
          (MOVQ
          (op2,
          op1))))
  
  (** val coq_PACKSSDW_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PACKSSDW_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            ('0'::('1'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('1'::('0'::('1'::('1'::[]))))
              modrm_mmx))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (PACKSSDW
        (op1,
        op2)))
  
  (** val coq_PACKSSWB_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PACKSSWB_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            ('0'::('1'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('0'::('0'::('1'::('1'::[]))))
              modrm_mmx))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (PACKSSWB
        (op1,
        op2)))
  
  (** val coq_PACKUSWB_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PACKUSWB_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            ('0'::('1'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('0'::('1'::('1'::('1'::[]))))
              modrm_mmx))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (PACKUSWB
        (op1,
        op2)))
  
  (** val coq_PADD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PADD_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_granularity_t,
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))))
              ('1'::('1'::[]))
              (seq
                mmx_granularity_t
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                (mmx_gg_p
                  true
                  true
                  true
                  false)
                modrm_mmx)))))
      (fun p ->
      let (gg,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (PADD
        (gg,
        op1,
        op2)))
  
  (** val coq_PADDS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PADDS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_granularity_t,
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))))
            ('1'::('1'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))))
              ('1'::('1'::[]))
              (seq
                mmx_granularity_t
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                (mmx_gg_p
                  true
                  true
                  false
                  false)
                modrm_mmx)))))
      (fun p ->
      let (gg,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (PADDS
        (gg,
        op1,
        op2)))
  
  (** val coq_PADDUS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PADDUS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_granularity_t,
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))))
            ('1'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))))
              ('1'::('1'::[]))
              (seq
                mmx_granularity_t
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                (mmx_gg_p
                  true
                  true
                  false
                  false)
                modrm_mmx)))))
      (fun p ->
      let (gg,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (PADDUS
        (gg,
        op1,
        op2)))
  
  (** val coq_PAND_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PAND_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            ('1'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('1'::('0'::('1'::('1'::[]))))
              modrm_mmx))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (PAND
        (op1,
        op2)))
  
  (** val coq_PANDN_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PANDN_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            ('1'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              modrm_mmx))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (PANDN
        (op1,
        op2)))
  
  (** val coq_PCMPEQ_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PCMPEQ_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_granularity_t,
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))))
            ('0'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))))
              ('0'::('1'::[]))
              (seq
                mmx_granularity_t
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                (mmx_gg_p
                  true
                  true
                  true
                  false)
                modrm_mmx)))))
      (fun p ->
      let (gg,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (PCMPEQ
        (gg,
        op1,
        op2)))
  
  (** val coq_PCMPGT_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PCMPGT_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_granularity_t,
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))))
            ('0'::('1'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))))
              ('0'::('1'::[]))
              (seq
                mmx_granularity_t
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                (mmx_gg_p
                  true
                  true
                  true
                  false)
                modrm_mmx)))))
      (fun p ->
      let (gg,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (PCMPGT
        (gg,
        op1,
        op2)))
  
  (** val coq_PMADDWD_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PMADDWD_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('0'::('1'::('0'::('1'::[]))))
              modrm_mmx))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (PMADDWD
        (op1,
        op2)))
  
  (** val coq_PMULHUW_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PMULHUW_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            ('1'::('1'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('0'::('1'::('0'::('0'::[]))))
              modrm_mmx))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (PMULHUW
        (op1,
        op2)))
  
  (** val coq_PMULHW_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PMULHW_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            ('1'::('1'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('0'::('1'::('0'::('1'::[]))))
              modrm_mmx))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (PMULHW
        (op1,
        op2)))
  
  (** val coq_PMULLW_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PMULLW_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            ('1'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('0'::('1'::('0'::('1'::[]))))
              modrm_mmx))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (PMULLW
        (op1,
        op2)))
  
  (** val coq_POR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_POR_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            ('1'::('1'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('1'::('0'::('1'::('1'::[]))))
              modrm_mmx))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (POR
        (op1,
        op2)))
  
  (** val coq_PSLL_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PSLL_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_granularity_t,
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))))
                ('0'::('0'::[]))
                (seq
                  mmx_granularity_t
                  (X86_BASE_PARSER.Coq_pair_t
                  (mmx_operand_t,
                  mmx_operand_t))
                  (mmx_gg_p
                    false
                    true
                    true
                    true)
                  modrm_mmx)))))
        (fun p ->
        let (gg,
             r) =
          Obj.magic
            p
        in
        let (op1,
             op2) =
          r
        in
        Obj.magic
          (PSLL
          (gg,
          op1,
          op2))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_register_t,
        byte_t))))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_register_t,
          byte_t))))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_register_t,
            byte_t))))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_register_t,
              byte_t))))
              ('0'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_granularity_t,
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_register_t,
                byte_t))))
                ('0'::('0'::[]))
                (seq
                  mmx_granularity_t
                  (X86_BASE_PARSER.Coq_pair_t
                  (mmx_register_t,
                  byte_t))
                  (mmx_gg_p
                    false
                    true
                    true
                    true)
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (mmx_register_t,
                    byte_t))
                    ('1'::('1'::('1'::('1'::('0'::[])))))
                    (seq
                      mmx_register_t
                      byte_t
                      mmx_reg
                      byte)))))))
        (fun p ->
        let (gg,
             r0) =
          Obj.magic
            p
        in
        let (r,
             imm) =
          r0
        in
        Obj.magic
          (PSLL
          (gg,
          (MMX_Reg_op
          r),
          (MMX_Imm_op
          (zero_extend8_32
            imm))))))
  
  (** val coq_PSRA_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PSRA_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))))
              ('1'::('1'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_granularity_t,
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))))
                ('0'::('0'::[]))
                (seq
                  mmx_granularity_t
                  (X86_BASE_PARSER.Coq_pair_t
                  (mmx_operand_t,
                  mmx_operand_t))
                  (mmx_gg_p
                    false
                    true
                    true
                    false)
                  modrm_mmx)))))
        (fun p ->
        let (gg,
             r) =
          Obj.magic
            p
        in
        let (op1,
             op2) =
          r
        in
        Obj.magic
          (PSRA
          (gg,
          op1,
          op2))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_register_t,
        byte_t))))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_register_t,
          byte_t))))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_register_t,
            byte_t))))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_register_t,
              byte_t))))
              ('0'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_granularity_t,
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_register_t,
                byte_t))))
                ('0'::('0'::[]))
                (seq
                  mmx_granularity_t
                  (X86_BASE_PARSER.Coq_pair_t
                  (mmx_register_t,
                  byte_t))
                  (mmx_gg_p
                    false
                    true
                    true
                    false)
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (mmx_register_t,
                    byte_t))
                    ('1'::('1'::('1'::('0'::('0'::[])))))
                    (seq
                      mmx_register_t
                      byte_t
                      mmx_reg
                      byte)))))))
        (fun p ->
        let (gg,
             r0) =
          Obj.magic
            p
        in
        let (r,
             imm) =
          r0
        in
        Obj.magic
          (PSRA
          (gg,
          (MMX_Reg_op
          r),
          (MMX_Imm_op
          (zero_extend8_32
            imm))))))
  
  (** val coq_PSRL_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PSRL_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))))
              ('1'::('1'::('0'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_granularity_t,
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))))
                ('0'::('0'::[]))
                (seq
                  mmx_granularity_t
                  (X86_BASE_PARSER.Coq_pair_t
                  (mmx_operand_t,
                  mmx_operand_t))
                  (mmx_gg_p
                    false
                    true
                    true
                    true)
                  modrm_mmx)))))
        (fun p ->
        let (gg,
             r) =
          Obj.magic
            p
        in
        let (op1,
             op2) =
          r
        in
        Obj.magic
          (PSRL
          (gg,
          op1,
          op2))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_register_t,
        byte_t))))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_register_t,
          byte_t))))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_register_t,
            byte_t))))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_register_t,
              byte_t))))
              ('0'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_granularity_t,
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_register_t,
                byte_t))))
                ('0'::('0'::[]))
                (seq
                  mmx_granularity_t
                  (X86_BASE_PARSER.Coq_pair_t
                  (mmx_register_t,
                  byte_t))
                  (mmx_gg_p
                    false
                    true
                    true
                    true)
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (mmx_register_t,
                    byte_t))
                    ('1'::('1'::('0'::('1'::('0'::[])))))
                    (seq
                      mmx_register_t
                      byte_t
                      mmx_reg
                      byte)))))))
        (fun p ->
        let (gg,
             r0) =
          Obj.magic
            p
        in
        let (r,
             imm) =
          r0
        in
        Obj.magic
          (PSRL
          (gg,
          (MMX_Reg_op
          r),
          (MMX_Imm_op
          (zero_extend8_32
            imm))))))
  
  (** val coq_PSUB_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PSUB_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_granularity_t,
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))))
              ('1'::('0'::[]))
              (seq
                mmx_granularity_t
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                (mmx_gg_p
                  true
                  true
                  true
                  false)
                modrm_mmx)))))
      (fun p ->
      let (gg,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (PSUB
        (gg,
        op1,
        op2)))
  
  (** val coq_PSUBS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PSUBS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_granularity_t,
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))))
            ('1'::('1'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))))
              ('1'::('0'::[]))
              (seq
                mmx_granularity_t
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                (mmx_gg_p
                  true
                  true
                  false
                  false)
                modrm_mmx)))))
      (fun p ->
      let (gg,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (PSUBS
        (gg,
        op1,
        op2)))
  
  (** val coq_PSUBUS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PSUBUS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_granularity_t,
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))))
            ('1'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))))
              ('1'::('0'::[]))
              (seq
                mmx_granularity_t
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                (mmx_gg_p
                  true
                  true
                  false
                  false)
                modrm_mmx)))))
      (fun p ->
      let (gg,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (PSUBUS
        (gg,
        op1,
        op2)))
  
  (** val coq_PUNPCKH_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PUNPCKH_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_granularity_t,
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))))
            ('0'::('1'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))))
              ('1'::('0'::[]))
              (seq
                mmx_granularity_t
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                (mmx_gg_p
                  true
                  true
                  true
                  false)
                modrm_mmx)))))
      (fun p ->
      let (gg,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (PUNPCKH
        (gg,
        op1,
        op2)))
  
  (** val coq_PUNPCKL_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PUNPCKL_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_granularity_t,
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_granularity_t,
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_granularity_t,
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_granularity_t,
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))))
            ('0'::('1'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_granularity_t,
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))))
              ('0'::('0'::[]))
              (seq
                mmx_granularity_t
                (X86_BASE_PARSER.Coq_pair_t
                (mmx_operand_t,
                mmx_operand_t))
                (mmx_gg_p
                  true
                  true
                  true
                  false)
                modrm_mmx)))))
      (fun p ->
      let (gg,
           r) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (PUNPCKL
        (gg,
        op1,
        op2)))
  
  (** val coq_PXOR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PXOR_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (mmx_operand_t,
      mmx_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (mmx_operand_t,
        mmx_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (mmx_operand_t,
          mmx_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (mmx_operand_t,
            mmx_operand_t))
            ('1'::('1'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (mmx_operand_t,
              mmx_operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              modrm_mmx))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (PXOR
        (op1,
        op2)))
  
  (** val coq_ADDPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_ADDPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('0'::('0'::('0'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (ADDPS
        (op1,
        op2)))
  
  (** val coq_ADDSS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_ADDSS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('1'::('1'::('1'::('1'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('1'::('0'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('1'::('0'::('0'::('0'::[]))))
                  modrm_xmm))))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (ADDSS
        (op1,
        op2)))
  
  (** val coq_ANDNPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_ANDNPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('1'::('0'::('1'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (ANDNPS
        (op1,
        op2)))
  
  (** val coq_ANDPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_ANDPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('1'::('0'::('0'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (ANDPS
        (op1,
        op2)))
  
  (** val coq_CMPPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_CMPPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      ((X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t)),
      byte_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        ((X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t)),
        byte_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          ((X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t)),
          byte_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            ((X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t)),
            byte_t))
            ('1'::('1'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              ((X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t)),
              byte_t))
              ('0'::('0'::('1'::('0'::[]))))
              (seq
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                byte_t
                modrm_xmm
                byte)))))
      (fun p ->
      let (r,
           imm) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (CMPPS
        (op1,
        op2,
        (SSE_Imm_op
        (zero_extend8_32
          imm)))))
  
  (** val coq_CMPSS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_CMPSS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      ((X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t)),
      byte_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        ((X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t)),
        byte_t))
        ('1'::('1'::('1'::('1'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          ((X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t)),
          byte_t))
          ('0'::('0'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            ((X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t)),
            byte_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              ((X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t)),
              byte_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                ((X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t)),
                byte_t))
                ('1'::('1'::('0'::('0'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  ((X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t)),
                  byte_t))
                  ('0'::('0'::('1'::('0'::[]))))
                  (seq
                    (X86_BASE_PARSER.Coq_pair_t
                    (sse_operand_t,
                    sse_operand_t))
                    byte_t
                    modrm_xmm
                    byte)))))))
      (fun p ->
      let (r,
           imm) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (CMPSS
        (op1,
        op2,
        (SSE_Imm_op
        (zero_extend8_32
          imm)))))
  
  (** val coq_COMISS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_COMISS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (COMISS
        (op1,
        op2)))
  
  (** val coq_CVTPI2PS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_CVTPI2PS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('0'::('1'::('0'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (CVTPI2PS
        (op1,
        op2)))
  
  (** val coq_CVTPS2PI_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_CVTPS2PI_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_register_t,
        mmx_register_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_register_t,
          mmx_register_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_register_t,
            mmx_register_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_register_t,
              mmx_register_t))
              ('0'::('0'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_register_t,
                mmx_register_t))
                ('1'::('1'::('0'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_register_t,
                  mmx_register_t))
                  ('1'::('1'::[]))
                  (seq
                    sse_register_t
                    mmx_register_t
                    sse_reg
                    mmx_reg))))))
        (fun p ->
        let (sr,
             mr) =
          Obj.magic
            p
        in
        Obj.magic
          (CVTPS2PI
          ((SSE_XMM_Reg_op
          sr),
          (SSE_MM_Reg_op
          mr)))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('1'::('1'::('0'::('1'::[]))))
                modrm_xmm_noreg))))
        (fun p ->
        let (xmm,
             mem) =
          Obj.magic
            p
        in
        Obj.magic
          (CVTPS2PI
          (xmm,
          mem))))
  
  (** val coq_CVTSI2SS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_CVTSI2SS_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_register_t,
        register_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_register_t,
          register_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_register_t,
            register_t))
            ('0'::('0'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_register_t,
              register_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_register_t,
                register_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_register_t,
                  register_t))
                  ('0'::('0'::('1'::('0'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (sse_register_t,
                    register_t))
                    ('1'::('0'::('1'::('0'::[]))))
                    (bitsleft
                      (X86_BASE_PARSER.Coq_pair_t
                      (sse_register_t,
                      register_t))
                      ('1'::('1'::[]))
                      (seq
                        sse_register_t
                        register_t
                        sse_reg
                        reg))))))))
        (fun p ->
        let (sr,
             r) =
          Obj.magic
            p
        in
        Obj.magic
          (CVTSI2SS
          ((SSE_XMM_Reg_op
          sr),
          (SSE_GP_Reg_op
          r)))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('0'::('0'::('1'::('0'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (sse_operand_t,
                    sse_operand_t))
                    ('1'::('0'::('1'::('0'::[]))))
                    modrm_xmm_noreg))))))
        (fun p ->
        let (xmm,
             mem) =
          Obj.magic
            p
        in
        Obj.magic
          (CVTSI2SS
          (xmm,
          mem))))
  
  (** val coq_CVTSS2SI_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_CVTSS2SI_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (register_t,
        sse_register_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (register_t,
          sse_register_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (register_t,
            sse_register_t))
            ('0'::('0'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (register_t,
              sse_register_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (register_t,
                sse_register_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (register_t,
                  sse_register_t))
                  ('0'::('0'::('1'::('0'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (register_t,
                    sse_register_t))
                    ('1'::('1'::('0'::('1'::[]))))
                    (bitsleft
                      (X86_BASE_PARSER.Coq_pair_t
                      (register_t,
                      sse_register_t))
                      ('1'::('1'::[]))
                      (seq
                        register_t
                        sse_register_t
                        reg
                        sse_reg))))))))
        (fun p ->
        let (r,
             sr) =
          Obj.magic
            p
        in
        Obj.magic
          (CVTSS2SI
          ((SSE_GP_Reg_op
          r),
          (SSE_XMM_Reg_op
          sr)))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('0'::('0'::('1'::('0'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (sse_operand_t,
                    sse_operand_t))
                    ('1'::('1'::('0'::('1'::[]))))
                    modrm_xmm_gp_noreg))))))
        (fun p ->
        let (op1,
             mem) =
          Obj.magic
            p
        in
        Obj.magic
          (CVTSS2SI
          (op1,
          mem))))
  
  (** val coq_CVTTPS2PI_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_CVTTPS2PI_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('0'::('0'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (CVTTPS2PI
        (op1,
        op2)))
  
  (** val coq_CVTTSS2SI_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_CVTTSS2SI_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (register_t,
        sse_register_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (register_t,
          sse_register_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (register_t,
            sse_register_t))
            ('0'::('0'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (register_t,
              sse_register_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (register_t,
                sse_register_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (register_t,
                  sse_register_t))
                  ('0'::('0'::('1'::('0'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (register_t,
                    sse_register_t))
                    ('1'::('1'::('0'::('0'::[]))))
                    (bitsleft
                      (X86_BASE_PARSER.Coq_pair_t
                      (register_t,
                      sse_register_t))
                      ('1'::('1'::[]))
                      (seq
                        register_t
                        sse_register_t
                        reg
                        sse_reg))))))))
        (fun p ->
        let (r,
             sr) =
          Obj.magic
            p
        in
        Obj.magic
          (CVTTSS2SI
          ((SSE_GP_Reg_op
          r),
          (SSE_XMM_Reg_op
          sr)))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('0'::('0'::('1'::('0'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (sse_operand_t,
                    sse_operand_t))
                    ('1'::('1'::('0'::('0'::[]))))
                    modrm_xmm_gp_noreg))))))
        (fun p ->
        let (op1,
             mem) =
          Obj.magic
            p
        in
        Obj.magic
          (CVTTSS2SI
          (op1,
          mem))))
  
  (** val coq_DIVPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_DIVPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('0'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (DIVPS
        (op1,
        op2)))
  
  (** val coq_DIVSS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_DIVSS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('1'::('1'::('1'::('1'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('1'::('0'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('1'::('1'::('1'::('0'::[]))))
                  modrm_xmm))))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (DIVSS
        (op1,
        op2)))
  
  (** val coq_LDMXCSR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_LDMXCSR_p =
    map
      sse_operand_t
      instruction_t
      (bitsleft
        sse_operand_t
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          sse_operand_t
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            sse_operand_t
            ('1'::('0'::('1'::('0'::[]))))
            (bitsleft
              sse_operand_t
              ('1'::('1'::('1'::('0'::[]))))
              (ext_op_modrm_sse
                ('0'::('1'::('0'::[]))))))))
      (fun x ->
      Obj.magic
        (LDMXCSR
        (Obj.magic
          x)))
  
  (** val coq_MAXPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MAXPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (MAXPS
        (op1,
        op2)))
  
  (** val coq_MAXSS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MAXSS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('1'::('1'::('1'::('1'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('1'::('0'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('1'::('1'::('1'::('1'::[]))))
                  modrm_xmm))))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (MAXSS
        (op1,
        op2)))
  
  (** val coq_MINPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MINPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('0'::('1'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (MINPS
        (op1,
        op2)))
  
  (** val coq_MINSS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MINSS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('1'::('1'::('1'::('1'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('1'::('0'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('1'::('1'::('0'::('1'::[]))))
                  modrm_xmm))))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (MINSS
        (op1,
        op2)))
  
  (** val coq_MOVAPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVAPS_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('1'::('0'::('0'::('0'::[]))))
                modrm_xmm))))
        (fun p ->
        let (op1,
             op2) =
          Obj.magic
            p
        in
        Obj.magic
          (MOVAPS
          (op1,
          op2))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('1'::('0'::('0'::('1'::[]))))
                modrm_xmm))))
        (fun p ->
        let (op1,
             op2) =
          Obj.magic
            p
        in
        Obj.magic
          (MOVAPS
          (op1,
          op2))))
  
  (** val coq_MOVHLPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVHLPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_register_t,
      sse_register_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_register_t,
        sse_register_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_register_t,
          sse_register_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_register_t,
            sse_register_t))
            ('0'::('0'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_register_t,
              sse_register_t))
              ('0'::('0'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_register_t,
                sse_register_t))
                ('1'::('1'::[]))
                (seq
                  sse_register_t
                  sse_register_t
                  sse_reg
                  sse_reg))))))
      (fun p ->
      let (sr1,
           sr2) =
        Obj.magic
          p
      in
      Obj.magic
        (MOVHLPS
        ((SSE_XMM_Reg_op
        sr1),
        (SSE_XMM_Reg_op
        sr2))))
  
  (** val coq_MOVHPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVHPS_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('0'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('1'::('1'::('0'::[]))))
                modrm_xmm_noreg))))
        (fun p ->
        let (op1,
             mem) =
          Obj.magic
            p
        in
        Obj.magic
          (MOVHPS
          (op1,
          mem))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('0'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('1'::('1'::('1'::[]))))
                modrm_xmm_noreg))))
        (fun p ->
        let (op1,
             mem) =
          Obj.magic
            p
        in
        Obj.magic
          (MOVHPS
          (mem,
          op1))))
  
  (** val coq_MOVLHPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVLHPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_register_t,
      sse_register_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_register_t,
        sse_register_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_register_t,
          sse_register_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_register_t,
            sse_register_t))
            ('0'::('0'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_register_t,
              sse_register_t))
              ('0'::('1'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_register_t,
                sse_register_t))
                ('1'::('1'::[]))
                (seq
                  sse_register_t
                  sse_register_t
                  sse_reg
                  sse_reg))))))
      (fun p ->
      let (sr1,
           sr2) =
        Obj.magic
          p
      in
      Obj.magic
        (MOVLHPS
        ((SSE_XMM_Reg_op
        sr1),
        (SSE_XMM_Reg_op
        sr2))))
  
  (** val coq_MOVLPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVLPS_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('0'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('0'::('1'::('0'::[]))))
                modrm_xmm_noreg))))
        (fun p ->
        let (op1,
             mem) =
          Obj.magic
            p
        in
        Obj.magic
          (MOVLPS
          (op1,
          mem))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('0'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('0'::('1'::('1'::[]))))
                modrm_xmm_noreg))))
        (fun p ->
        let (op1,
             mem) =
          Obj.magic
            p
        in
        Obj.magic
          (MOVLPS
          (mem,
          op1))))
  
  (** val coq_MOVMSKPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVMSKPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (register_t,
      sse_register_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (register_t,
        sse_register_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (register_t,
          sse_register_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (register_t,
            sse_register_t))
            ('0'::('0'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (register_t,
              sse_register_t))
              ('0'::('1'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (register_t,
                sse_register_t))
                ('1'::('1'::[]))
                (seq
                  register_t
                  sse_register_t
                  reg
                  sse_reg))))))
      (fun p ->
      let (r,
           sr) =
        Obj.magic
          p
      in
      Obj.magic
        (MOVMSKPS
        ((SSE_GP_Reg_op
        r),
        (SSE_XMM_Reg_op
        sr))))
  
  (** val coq_MOVSS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVSS_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('0'::('0'::('0'::('1'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (sse_operand_t,
                    sse_operand_t))
                    ('0'::('0'::('0'::('0'::[]))))
                    modrm_xmm))))))
        (fun p ->
        let (op1,
             op2) =
          Obj.magic
            p
        in
        Obj.magic
          (MOVSS
          (op1,
          op2))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('0'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('1'::('1'::('1'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('0'::('0'::('0'::('1'::[]))))
                  (bitsleft
                    (X86_BASE_PARSER.Coq_pair_t
                    (sse_operand_t,
                    sse_operand_t))
                    ('0'::('0'::('0'::('1'::[]))))
                    modrm_xmm))))))
        (fun p ->
        let (op1,
             op2) =
          Obj.magic
            p
        in
        Obj.magic
          (MOVSS
          (op2,
          op1))))
  
  (** val coq_MOVUPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVUPS_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('0'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('0'::('0'::('0'::[]))))
                modrm_xmm))))
        (fun p ->
        let (op1,
             op2) =
          Obj.magic
            p
        in
        Obj.magic
          (MOVUPS
          (op1,
          op2))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('0'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('0'::('0'::('1'::[]))))
                modrm_xmm))))
        (fun p ->
        let (op1,
             op2) =
          Obj.magic
            p
        in
        Obj.magic
          (MOVUPS
          (op2,
          op1))))
  
  (** val coq_MULPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MULPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('0'::('0'::('1'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (MULPS
        (op1,
        op2)))
  
  (** val coq_MULSS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_MULSS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('1'::('1'::('1'::('1'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('1'::('0'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('1'::('0'::('0'::('1'::[]))))
                  modrm_xmm))))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (MULSS
        (op1,
        op2)))
  
  (** val coq_ORPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_ORPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('1'::('1'::('0'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (ORPS
        (op1,
        op2)))
  
  (** val coq_RCPPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_RCPPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('1'::('1'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (RCPPS
        (op1,
        op2)))
  
  (** val coq_RCPSS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_RCPSS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('1'::('1'::('1'::('1'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('1'::('0'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('0'::('0'::('1'::('1'::[]))))
                  modrm_xmm))))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (RCPSS
        (op1,
        op2)))
  
  (** val coq_RSQRTPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_RSQRTPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('1'::('0'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (RSQRTPS
        (op1,
        op2)))
  
  (** val coq_RSQRTSS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_RSQRTSS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('1'::('1'::('1'::('1'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('1'::('0'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('0'::('0'::('1'::('0'::[]))))
                  modrm_xmm))))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (RSQRTSS
        (op1,
        op2)))
  
  (** val coq_SHUFPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SHUFPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      ((X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t)),
      byte_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        ((X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t)),
        byte_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          ((X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t)),
          byte_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            ((X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t)),
            byte_t))
            ('1'::('1'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              ((X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t)),
              byte_t))
              ('0'::('1'::('1'::('0'::[]))))
              (seq
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                byte_t
                modrm_xmm
                byte)))))
      (fun p ->
      let (r,
           imm) =
        Obj.magic
          p
      in
      let (op1,
           op2) =
        r
      in
      Obj.magic
        (SHUFPS
        (op1,
        op2,
        (SSE_Imm_op
        (zero_extend8_32
          imm)))))
  
  (** val coq_SQRTPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SQRTPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('0'::('0'::('1'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (SQRTPS
        (op1,
        op2)))
  
  (** val coq_SQRTSS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SQRTSS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('1'::('1'::('1'::('1'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('1'::('0'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('0'::('0'::('0'::('1'::[]))))
                  modrm_xmm))))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (SQRTSS
        (op1,
        op2)))
  
  (** val coq_STMXCSR_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_STMXCSR_p =
    map
      sse_operand_t
      instruction_t
      (bitsleft
        sse_operand_t
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          sse_operand_t
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            sse_operand_t
            ('1'::('0'::('1'::('0'::[]))))
            (bitsleft
              sse_operand_t
              ('1'::('1'::('1'::('0'::[]))))
              (ext_op_modrm_sse
                ('0'::('1'::('1'::[]))))))))
      (fun x ->
      Obj.magic
        (STMXCSR
        (Obj.magic
          x)))
  
  (** val coq_SUBPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SUBPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('0'::('0'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (SUBPS
        (op1,
        op2)))
  
  (** val coq_SUBSS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_SUBSS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('1'::('1'::('1'::('1'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('0'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('1'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('1'::('0'::('1'::[]))))
                (bitsleft
                  (X86_BASE_PARSER.Coq_pair_t
                  (sse_operand_t,
                  sse_operand_t))
                  ('1'::('1'::('0'::('0'::[]))))
                  modrm_xmm))))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (SUBSS
        (op1,
        op2)))
  
  (** val coq_UCOMISS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_UCOMISS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('1'::('0'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('0'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (UCOMISS
        (op1,
        op2)))
  
  (** val coq_UNPCKHPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_UNPCKHPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('1'::('0'::('1'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (UNPCKHPS
        (op1,
        op2)))
  
  (** val coq_UNPCKLPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_UNPCKLPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('0'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('1'::('0'::('0'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (UNPCKLPS
        (op1,
        op2)))
  
  (** val coq_XORPS_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_XORPS_p =
    map
      (X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t,
      sse_operand_t))
      instruction_t
      (bitsleft
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('0'::('1'::('0'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('0'::('1'::('1'::('1'::[]))))
              modrm_xmm))))
      (fun p ->
      let (op1,
           op2) =
        Obj.magic
          p
      in
      Obj.magic
        (XORPS
        (op1,
        op2)))
  
  (** val coq_PAVGB_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PAVGB_p =
    alt
      instruction_t
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('0'::('0'::('0'::[]))))
                modrm_mm))))
        (fun p ->
        let (op1,
             op2) =
          Obj.magic
            p
        in
        Obj.magic
          (PAVGB
          (op1,
          op2))))
      (map
        (X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t,
        sse_operand_t))
        instruction_t
        (bitsleft
          (X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t,
          sse_operand_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft
            (X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t,
            sse_operand_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft
              (X86_BASE_PARSER.Coq_pair_t
              (sse_operand_t,
              sse_operand_t))
              ('1'::('1'::('1'::('0'::[]))))
              (bitsleft
                (X86_BASE_PARSER.Coq_pair_t
                (sse_operand_t,
                sse_operand_t))
                ('0'::('0'::('1'::('1'::[]))))
                modrm_mm))))
        (fun p ->
        let (op1,
             op2) =
          Obj.magic
            p
        in
        Obj.magic
          (PAVGB
          (op2,
          op1))))
  
  (** val coq_PEXTRW_p :
      X86_BASE_PARSER.coq_parser **)
  
  let coq_PEXTRW_p =
    map (X86_BASE_PARSER.Coq_pair_t (register_t, (X86_BASE_PARSER.Coq_pair_t
      (mmx_register_t, byte_t)))) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
        (X86_BASE_PARSER.Coq_pair_t (mmx_register_t, byte_t))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
          (X86_BASE_PARSER.Coq_pair_t (mmx_register_t, byte_t))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
            (X86_BASE_PARSER.Coq_pair_t (mmx_register_t, byte_t))))
            ('1'::('1'::('0'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
              (X86_BASE_PARSER.Coq_pair_t (mmx_register_t, byte_t))))
              ('0'::('1'::('0'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                (X86_BASE_PARSER.Coq_pair_t (mmx_register_t, byte_t))))
                ('1'::('1'::[]))
                (seq register_t (X86_BASE_PARSER.Coq_pair_t (mmx_register_t,
                  byte_t)) reg (seq mmx_register_t byte_t mmx_reg byte)))))))
      (fun p ->
      let (r32, r) = Obj.magic p in
      let (mmx, imm) = r in
      Obj.magic (PEXTRW ((SSE_GP_Reg_op r32), (SSE_MM_Reg_op mmx),
        (SSE_Imm_op (zero_extend8_32 imm)))))
  
  (** val coq_PINSRW_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PINSRW_p =
    alt instruction_t
      (map (X86_BASE_PARSER.Coq_pair_t (mmx_register_t,
        (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t)))) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (mmx_register_t,
          (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (mmx_register_t,
            (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (mmx_register_t,
              (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))))
              ('1'::('1'::('0'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (mmx_register_t,
                (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))))
                ('0'::('1'::('0'::('0'::[]))))
                (bitsleft (X86_BASE_PARSER.Coq_pair_t (mmx_register_t,
                  (X86_BASE_PARSER.Coq_pair_t (register_t, byte_t))))
                  ('1'::('1'::[]))
                  (seq mmx_register_t (X86_BASE_PARSER.Coq_pair_t
                    (register_t, byte_t)) mmx_reg
                    (seq register_t byte_t reg byte))))))) (fun p ->
        let (mmx, r) = Obj.magic p in
        let (r32, imm) = r in
        Obj.magic (PINSRW ((SSE_MM_Reg_op mmx), (SSE_GP_Reg_op r32),
          (SSE_Imm_op (zero_extend8_32 imm))))))
      (map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t, sse_operand_t)), byte_t)) instruction_t
        (bitsleft (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t, sse_operand_t)), byte_t))
          ('0'::('0'::('0'::('0'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t, sse_operand_t)), byte_t))
            ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              ((X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t)),
              byte_t)) ('1'::('1'::('0'::('0'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t
                ((X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t)),
                byte_t)) ('0'::('1'::('0'::('0'::[]))))
                (seq (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
                  sse_operand_t)) byte_t modrm_mm_noreg byte))))) (fun p ->
        let (r, imm) = Obj.magic p in
        let (op1, mem) = r in
        Obj.magic (PINSRW (op1, mem, (SSE_Imm_op (zero_extend8_32 imm))))))
  
  (** val coq_PMAXSW_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PMAXSW_p =
    map (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
      instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
            sse_operand_t)) ('1'::('1'::('1'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
              sse_operand_t)) ('1'::('1'::('1'::('0'::[])))) modrm_mm))))
      (fun p ->
      let (op1, op2) = Obj.magic p in Obj.magic (PMAXSW (op1, op2)))
  
  (** val coq_PMAXUB_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PMAXUB_p =
    map (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
      instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
            sse_operand_t)) ('1'::('1'::('0'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
              sse_operand_t)) ('1'::('1'::('1'::('0'::[])))) modrm_mm))))
      (fun p ->
      let (op1, op2) = Obj.magic p in Obj.magic (PMAXUB (op1, op2)))
  
  (** val coq_PMINSW_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PMINSW_p =
    map (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
      instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
            sse_operand_t)) ('1'::('1'::('1'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
              sse_operand_t)) ('1'::('0'::('1'::('0'::[])))) modrm_mm))))
      (fun p ->
      let (op1, op2) = Obj.magic p in Obj.magic (PMINSW (op1, op2)))
  
  (** val coq_PMINUB_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PMINUB_p =
    map (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
      instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
            sse_operand_t)) ('1'::('1'::('0'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
              sse_operand_t)) ('1'::('0'::('1'::('0'::[])))) modrm_mm))))
      (fun p ->
      let (op1, op2) = Obj.magic p in Obj.magic (PMINUB (op1, op2)))
  
  (** val coq_PMOVMSKB_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PMOVMSKB_p =
    map (X86_BASE_PARSER.Coq_pair_t (register_t, mmx_register_t))
      instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, mmx_register_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, mmx_register_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t, mmx_register_t))
            ('1'::('1'::('0'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
              mmx_register_t)) ('0'::('1'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (register_t,
                mmx_register_t)) ('1'::('1'::[]))
                (seq register_t mmx_register_t reg mmx_reg)))))) (fun p ->
      let (r, mr) = Obj.magic p in
      Obj.magic (PMOVMSKB ((SSE_GP_Reg_op r), (SSE_MM_Reg_op mr))))
  
  (** val coq_PSADBW_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PSADBW_p =
    map (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
      instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
            sse_operand_t)) ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
              sse_operand_t)) ('0'::('1'::('1'::('0'::[])))) modrm_mm))))
      (fun p ->
      let (op1, op2) = Obj.magic p in Obj.magic (PSADBW (op1, op2)))
  
  (** val coq_PSHUFW_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PSHUFW_p =
    map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
      (sse_operand_t, sse_operand_t)), byte_t)) instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
        (sse_operand_t, sse_operand_t)), byte_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
          (sse_operand_t, sse_operand_t)), byte_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_pair_t
            (sse_operand_t, sse_operand_t)), byte_t))
            ('0'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t
              ((X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t)),
              byte_t)) ('0'::('0'::('0'::('0'::[]))))
              (seq (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
                sse_operand_t)) byte_t modrm_mm byte))))) (fun p ->
      let (r, imm) = Obj.magic p in
      let (op1, op2) = r in
      Obj.magic (PSHUFW (op1, op2, (SSE_Imm_op (zero_extend8_32 imm)))))
  
  (** val coq_MASKMOVQ_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_MASKMOVQ_p =
    map (X86_BASE_PARSER.Coq_pair_t (mmx_register_t, mmx_register_t))
      instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (mmx_register_t, mmx_register_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (mmx_register_t,
          mmx_register_t)) ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (mmx_register_t,
            mmx_register_t)) ('1'::('1'::('1'::('1'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (mmx_register_t,
              mmx_register_t)) ('0'::('1'::('1'::('1'::[]))))
              (bitsleft (X86_BASE_PARSER.Coq_pair_t (mmx_register_t,
                mmx_register_t)) ('1'::('1'::[]))
                (seq mmx_register_t mmx_register_t mmx_reg mmx_reg))))))
      (fun p ->
      let (mr1, mr2) = Obj.magic p in
      Obj.magic (MASKMOVQ ((SSE_MM_Reg_op mr1), (SSE_MM_Reg_op mr2))))
  
  (** val coq_MOVNTPS_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVNTPS_p =
    map (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
      instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
            sse_operand_t)) ('0'::('0'::('1'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
              sse_operand_t)) ('1'::('0'::('1'::('1'::[])))) modrm_xmm_noreg))))
      (fun p ->
      let (op1, mem) = Obj.magic p in Obj.magic (MOVNTPS (mem, op1)))
  
  (** val coq_MOVNTQ_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_MOVNTQ_p =
    map (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
      instruction_t
      (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t, sse_operand_t))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
            sse_operand_t)) ('1'::('1'::('1'::('0'::[]))))
            (bitsleft (X86_BASE_PARSER.Coq_pair_t (sse_operand_t,
              sse_operand_t)) ('0'::('1'::('1'::('1'::[])))) modrm_mm_noreg))))
      (fun p ->
      let (op1, mem) = Obj.magic p in Obj.magic (MOVNTQ (mem, op1)))
  
  (** val coq_PREFETCHT0_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PREFETCHT0_p =
    map sse_operand_t instruction_t
      (bitsleft sse_operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft sse_operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft sse_operand_t ('0'::('0'::('0'::('1'::[]))))
            (bitsleft sse_operand_t ('1'::('0'::('0'::('0'::[]))))
              (ext_op_modrm_sse ('0'::('0'::('1'::[])))))))) (fun x ->
      Obj.magic (PREFETCHT0 (Obj.magic x)))
  
  (** val coq_PREFETCHT1_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PREFETCHT1_p =
    map sse_operand_t instruction_t
      (bitsleft sse_operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft sse_operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft sse_operand_t ('0'::('0'::('0'::('1'::[]))))
            (bitsleft sse_operand_t ('1'::('0'::('0'::('0'::[]))))
              (ext_op_modrm_sse ('0'::('1'::('0'::[])))))))) (fun x ->
      Obj.magic (PREFETCHT1 (Obj.magic x)))
  
  (** val coq_PREFETCHT2_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PREFETCHT2_p =
    map sse_operand_t instruction_t
      (bitsleft sse_operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft sse_operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft sse_operand_t ('0'::('0'::('0'::('1'::[]))))
            (bitsleft sse_operand_t ('1'::('0'::('0'::('0'::[]))))
              (ext_op_modrm_sse ('0'::('1'::('1'::[])))))))) (fun x ->
      Obj.magic (PREFETCHT2 (Obj.magic x)))
  
  (** val coq_PREFETCHNTA_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_PREFETCHNTA_p =
    map sse_operand_t instruction_t
      (bitsleft sse_operand_t ('0'::('0'::('0'::('0'::[]))))
        (bitsleft sse_operand_t ('1'::('1'::('1'::('1'::[]))))
          (bitsleft sse_operand_t ('0'::('0'::('0'::('1'::[]))))
            (bitsleft sse_operand_t ('1'::('0'::('0'::('0'::[]))))
              (ext_op_modrm_sse ('0'::('0'::('0'::[])))))))) (fun x ->
      Obj.magic (PREFETCHNTA (Obj.magic x)))
  
  (** val coq_SFENCE_p : X86_BASE_PARSER.coq_parser **)
  
  let coq_SFENCE_p =
    map (bits_n (length ('1'::('0'::('0'::('0'::[])))))) instruction_t
      (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
        ('0'::('0'::('0'::('0'::[]))))
        (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
            ('1'::('0'::('1'::('0'::[]))))
            (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
              ('1'::('1'::('1'::('0'::[]))))
              (bitsleft (bits_n (length ('1'::('0'::('0'::('0'::[]))))))
                ('1'::('1'::('1'::('1'::[]))))
                (bits ('1'::('0'::('0'::('0'::[])))))))))) (fun x ->
      Obj.magic SFENCE)
  
  (** val list2pair_t :
      X86_BASE_PARSER.result list -> X86_BASE_PARSER.result **)
  
  let rec list2pair_t = function
  | [] -> X86_BASE_PARSER.Coq_unit_t
  | r :: l' ->
    (match l' with
     | [] -> X86_BASE_PARSER.Coq_pair_t (r, (list2pair_t l'))
     | r' :: l0 ->
       (match l0 with
        | [] -> X86_BASE_PARSER.Coq_pair_t (r, r')
        | r0 :: l1 -> X86_BASE_PARSER.Coq_pair_t (r, (list2pair_t l'))))
  
  (** val lock_p : X86_BASE_PARSER.coq_parser **)
  
  let lock_p =
    map (bits_n (length ('0'::('0'::('0'::('0'::[])))))) lock_or_rep_t
      (bitsleft (bits_n (length ('0'::('0'::('0'::('0'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('0'::('0'::('0'::('0'::[]))))))
      (fun x -> Obj.magic Coq_lock)
  
  (** val rep_or_repn_p : X86_BASE_PARSER.coq_parser **)
  
  let rep_or_repn_p =
    alt lock_or_rep_t
      (map (bits_n (length ('0'::('0'::('1'::('0'::[])))))) lock_or_rep_t
        (bitsleft (bits_n (length ('0'::('0'::('1'::('0'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bits ('0'::('0'::('1'::('0'::[])))))) (fun x ->
        Obj.magic Coq_repn))
      (map (bits_n (length ('0'::('0'::('1'::('1'::[])))))) lock_or_rep_t
        (bitsleft (bits_n (length ('0'::('0'::('1'::('1'::[]))))))
          ('1'::('1'::('1'::('1'::[]))))
          (bits ('0'::('0'::('1'::('1'::[])))))) (fun x ->
        Obj.magic Coq_rep))
  
  (** val rep_p : X86_BASE_PARSER.coq_parser **)
  
  let rep_p =
    map (bits_n (length ('0'::('0'::('1'::('1'::[])))))) lock_or_rep_t
      (bitsleft (bits_n (length ('0'::('0'::('1'::('1'::[]))))))
        ('1'::('1'::('1'::('1'::[])))) (bits ('0'::('0'::('1'::('1'::[]))))))
      (fun x -> Obj.magic Coq_rep)
  
  (** val lock_or_rep_p : X86_BASE_PARSER.coq_parser **)
  
  let lock_or_rep_p =
    bitsleft lock_or_rep_t ('1'::('1'::('1'::('1'::[]))))
      (alt lock_or_rep_t
        (map (bits_n (length ('0'::('0'::('0'::('0'::[])))))) lock_or_rep_t
          (bits ('0'::('0'::('0'::('0'::[]))))) (fun x ->
          Obj.magic Coq_lock))
        (alt lock_or_rep_t
          (map (bits_n (length ('0'::('0'::('1'::('0'::[])))))) lock_or_rep_t
            (bits ('0'::('0'::('1'::('0'::[]))))) (fun x ->
            Obj.magic Coq_repn))
          (map (bits_n (length ('0'::('0'::('1'::('1'::[])))))) lock_or_rep_t
            (bits ('0'::('0'::('1'::('1'::[]))))) (fun x ->
            Obj.magic Coq_rep))))
  
  (** val segment_override_p : X86_BASE_PARSER.coq_parser **)
  
  let segment_override_p =
    alt segment_register_t
      (map (bits_n (length ('1'::('1'::('1'::('0'::[]))))))
        segment_register_t
        (bitsleft (bits_n (length ('1'::('1'::('1'::('0'::[]))))))
          ('0'::('0'::('1'::('0'::[]))))
          (bits ('1'::('1'::('1'::('0'::[])))))) (fun x -> Obj.magic CS))
      (alt segment_register_t
        (map (bits_n (length ('0'::('1'::('1'::('0'::[]))))))
          segment_register_t
          (bitsleft (bits_n (length ('0'::('1'::('1'::('0'::[]))))))
            ('0'::('0'::('1'::('1'::[]))))
            (bits ('0'::('1'::('1'::('0'::[])))))) (fun x -> Obj.magic SS))
        (alt segment_register_t
          (map (bits_n (length ('1'::('1'::('1'::('0'::[]))))))
            segment_register_t
            (bitsleft (bits_n (length ('1'::('1'::('1'::('0'::[]))))))
              ('0'::('0'::('1'::('1'::[]))))
              (bits ('1'::('1'::('1'::('0'::[])))))) (fun x -> Obj.magic DS))
          (alt segment_register_t
            (map (bits_n (length ('0'::('1'::('1'::('0'::[]))))))
              segment_register_t
              (bitsleft (bits_n (length ('0'::('1'::('1'::('0'::[]))))))
                ('0'::('0'::('1'::('0'::[]))))
                (bits ('0'::('1'::('1'::('0'::[])))))) (fun x ->
              Obj.magic ES))
            (alt segment_register_t
              (map (bits_n (length ('0'::('1'::('0'::('0'::[]))))))
                segment_register_t
                (bitsleft (bits_n (length ('0'::('1'::('0'::('0'::[]))))))
                  ('0'::('1'::('1'::('0'::[]))))
                  (bits ('0'::('1'::('0'::('0'::[])))))) (fun x ->
                Obj.magic FS))
              (map (bits_n (length ('0'::('1'::('0'::('1'::[]))))))
                segment_register_t
                (bitsleft (bits_n (length ('0'::('1'::('0'::('1'::[]))))))
                  ('0'::('1'::('1'::('0'::[]))))
                  (bits ('0'::('1'::('0'::('1'::[])))))) (fun x ->
                Obj.magic GS))))))
  
  (** val op_override_p : X86_BASE_PARSER.coq_parser **)
  
  let op_override_p =
    map (bits_n (length ('0'::('1'::('1'::('0'::[])))))) bool_t
      (bitsleft (bits_n (length ('0'::('1'::('1'::('0'::[]))))))
        ('0'::('1'::('1'::('0'::[])))) (bits ('0'::('1'::('1'::('0'::[]))))))
      (fun x -> Obj.magic true)
  
  (** val addr_override_p : X86_BASE_PARSER.coq_parser **)
  
  let addr_override_p =
    map (bits_n (length ('0'::('1'::('1'::('1'::[])))))) bool_t
      (bitsleft (bits_n (length ('0'::('1'::('1'::('1'::[]))))))
        ('0'::('1'::('1'::('0'::[])))) (bits ('0'::('1'::('1'::('1'::[]))))))
      (fun x -> Obj.magic true)
  
  (** val perm2 :
      X86_BASE_PARSER.result -> X86_BASE_PARSER.result ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser **)
  
  let perm2 t1 t2 p1 p2 =
    alt (X86_BASE_PARSER.Coq_pair_t (t1, t2)) (seq t1 t2 p1 p2)
      (map (X86_BASE_PARSER.Coq_pair_t (t2, t1)) (X86_BASE_PARSER.Coq_pair_t
        (t1, t2)) (seq t2 t1 p2 p1) (fun p ->
        let (a, b) = Obj.magic p in Obj.magic (b, a)))
  
  (** val perm3 :
      X86_BASE_PARSER.result -> X86_BASE_PARSER.result ->
      X86_BASE_PARSER.result -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser **)
  
  let perm3 t1 t2 t3 p1 p2 p3 =
    let r_t = X86_BASE_PARSER.Coq_pair_t (t1, (X86_BASE_PARSER.Coq_pair_t
      (t2, t3)))
    in
    alt (X86_BASE_PARSER.Coq_pair_t (t1, (X86_BASE_PARSER.Coq_pair_t (t2,
      t3))))
      (seq t1 (X86_BASE_PARSER.Coq_pair_t (t2, t3)) p1 (perm2 t2 t3 p2 p3))
      (alt r_t
        (map (X86_BASE_PARSER.Coq_pair_t (t2, (X86_BASE_PARSER.Coq_pair_t
          (t1, t3)))) r_t
          (seq t2 (X86_BASE_PARSER.Coq_pair_t (t1, t3)) p2
            (perm2 t1 t3 p1 p3)) (fun p ->
          let (b, r) = Obj.magic p in let (a, c) = r in Obj.magic (a, (b, c))))
        (map (X86_BASE_PARSER.Coq_pair_t (t3, (X86_BASE_PARSER.Coq_pair_t
          (t1, t2)))) r_t
          (seq t3 (X86_BASE_PARSER.Coq_pair_t (t1, t2)) p3
            (perm2 t1 t2 p1 p2)) (fun p ->
          let (c, r) = Obj.magic p in let (a, b) = r in Obj.magic (a, (b, c)))))
  
  (** val perm4 :
      X86_BASE_PARSER.result -> X86_BASE_PARSER.result ->
      X86_BASE_PARSER.result -> X86_BASE_PARSER.result ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser **)
  
  let perm4 t1 t2 t3 t4 p1 p2 p3 p4 =
    let r_t = X86_BASE_PARSER.Coq_pair_t (t1, (X86_BASE_PARSER.Coq_pair_t
      (t2, (X86_BASE_PARSER.Coq_pair_t (t3, t4)))))
    in
    alt (X86_BASE_PARSER.Coq_pair_t (t1, (X86_BASE_PARSER.Coq_pair_t (t2,
      (X86_BASE_PARSER.Coq_pair_t (t3, t4))))))
      (seq t1 (X86_BASE_PARSER.Coq_pair_t (t2, (X86_BASE_PARSER.Coq_pair_t
        (t3, t4)))) p1 (perm3 t2 t3 t4 p2 p3 p4))
      (alt r_t
        (map (X86_BASE_PARSER.Coq_pair_t (t2, (X86_BASE_PARSER.Coq_pair_t
          (t1, (X86_BASE_PARSER.Coq_pair_t (t3, t4)))))) r_t
          (seq t2 (X86_BASE_PARSER.Coq_pair_t (t1,
            (X86_BASE_PARSER.Coq_pair_t (t3, t4)))) p2
            (perm3 t1 t3 t4 p1 p3 p4)) (fun p ->
          let (b, r) = Obj.magic p in
          let (a, r0) = r in let (c, d) = r0 in Obj.magic (a, (b, (c, d)))))
        (alt r_t
          (map (X86_BASE_PARSER.Coq_pair_t (t3, (X86_BASE_PARSER.Coq_pair_t
            (t1, (X86_BASE_PARSER.Coq_pair_t (t2, t4)))))) r_t
            (seq t3 (X86_BASE_PARSER.Coq_pair_t (t1,
              (X86_BASE_PARSER.Coq_pair_t (t2, t4)))) p3
              (perm3 t1 t2 t4 p1 p2 p4)) (fun p ->
            let (c, r) = Obj.magic p in
            let (a, r0) = r in let (b, d) = r0 in Obj.magic (a, (b, (c, d)))))
          (map (X86_BASE_PARSER.Coq_pair_t (t4, (X86_BASE_PARSER.Coq_pair_t
            (t1, (X86_BASE_PARSER.Coq_pair_t (t2, t3)))))) r_t
            (seq t4 (X86_BASE_PARSER.Coq_pair_t (t1,
              (X86_BASE_PARSER.Coq_pair_t (t2, t3)))) p4
              (perm3 t1 t2 t3 p1 p2 p3)) (fun p ->
            let (d, r) = Obj.magic p in
            let (a, r0) = r in let (b, c) = r0 in Obj.magic (a, (b, (c, d)))))))
  
  (** val option_perm :
      X86_PARSER_ARG.tipe -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser **)
  
  let option_perm t1 p1 =
    let r_t = option_t t1 in
    alt r_t
      (map X86_BASE_PARSER.Coq_unit_t r_t X86_BASE_PARSER.Eps_p (fun p ->
        Obj.magic None))
      (map (X86_BASE_PARSER.Coq_tipe_t t1) r_t p1 (fun p ->
        Obj.magic (Some p)))
  
  (** val option_perm2 :
      X86_PARSER_ARG.tipe -> X86_PARSER_ARG.tipe ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser **)
  
  let option_perm2 t1 t2 p1 p2 =
    let r_t = X86_BASE_PARSER.Coq_pair_t ((option_t t1), (option_t t2)) in
    alt r_t
      (map X86_BASE_PARSER.Coq_unit_t r_t X86_BASE_PARSER.Eps_p (fun p ->
        Obj.magic (None, None)))
      (alt r_t
        (map (X86_BASE_PARSER.Coq_tipe_t t1) r_t p1 (fun p ->
          Obj.magic ((Some p), None)))
        (alt r_t
          (map (X86_BASE_PARSER.Coq_tipe_t t2) r_t p2 (fun p ->
            Obj.magic (None, (Some p))))
          (map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_tipe_t t1),
            (X86_BASE_PARSER.Coq_tipe_t t2))) r_t
            (perm2 (X86_BASE_PARSER.Coq_tipe_t t1)
              (X86_BASE_PARSER.Coq_tipe_t t2) p1 p2) (fun p ->
            let (a, b) = Obj.magic p in Obj.magic ((Some a), (Some b))))))
  
  (** val option_perm3 :
      X86_PARSER_ARG.tipe -> X86_PARSER_ARG.tipe -> X86_PARSER_ARG.tipe ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser **)
  
  let option_perm3 t1 t2 t3 p1 p2 p3 =
    let r_t = X86_BASE_PARSER.Coq_pair_t ((option_t t1),
      (X86_BASE_PARSER.Coq_pair_t ((option_t t2), (option_t t3))))
    in
    alt r_t
      (map X86_BASE_PARSER.Coq_unit_t r_t X86_BASE_PARSER.Eps_p (fun p ->
        Obj.magic (None, (None, None))))
      (alt r_t
        (map (X86_BASE_PARSER.Coq_tipe_t t1) r_t p1 (fun p ->
          Obj.magic ((Some p), (None, None))))
        (alt r_t
          (map (X86_BASE_PARSER.Coq_tipe_t t2) r_t p2 (fun p ->
            Obj.magic (None, ((Some p), None))))
          (alt r_t
            (map (X86_BASE_PARSER.Coq_tipe_t t3) r_t p3 (fun p ->
              Obj.magic (None, (None, (Some p)))))
            (alt r_t
              (map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_tipe_t
                t1), (X86_BASE_PARSER.Coq_tipe_t t2))) r_t
                (perm2 (X86_BASE_PARSER.Coq_tipe_t t1)
                  (X86_BASE_PARSER.Coq_tipe_t t2) p1 p2) (fun p ->
                let (a, b) = Obj.magic p in
                Obj.magic ((Some a), ((Some b), None))))
              (alt r_t
                (map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_tipe_t
                  t1), (X86_BASE_PARSER.Coq_tipe_t t3))) r_t
                  (perm2 (X86_BASE_PARSER.Coq_tipe_t t1)
                    (X86_BASE_PARSER.Coq_tipe_t t3) p1 p3) (fun p ->
                  let (a, c) = Obj.magic p in
                  Obj.magic ((Some a), (None, (Some c)))))
                (alt r_t
                  (map (X86_BASE_PARSER.Coq_pair_t
                    ((X86_BASE_PARSER.Coq_tipe_t t2),
                    (X86_BASE_PARSER.Coq_tipe_t t3))) r_t
                    (perm2 (X86_BASE_PARSER.Coq_tipe_t t2)
                      (X86_BASE_PARSER.Coq_tipe_t t3) p2 p3) (fun p ->
                    let (b, c) = Obj.magic p in
                    Obj.magic (None, ((Some b), (Some c)))))
                  (map (X86_BASE_PARSER.Coq_pair_t
                    ((X86_BASE_PARSER.Coq_tipe_t t1),
                    (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_tipe_t
                    t2), (X86_BASE_PARSER.Coq_tipe_t t3))))) r_t
                    (perm3 (X86_BASE_PARSER.Coq_tipe_t t1)
                      (X86_BASE_PARSER.Coq_tipe_t t2)
                      (X86_BASE_PARSER.Coq_tipe_t t3) p1 p2 p3) (fun p ->
                    let (a, r) = Obj.magic p in
                    let (b, c) = r in
                    Obj.magic ((Some a), ((Some b), (Some c)))))))))))
  
  (** val option_perm2_variation :
      X86_PARSER_ARG.tipe -> X86_PARSER_ARG.tipe ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser **)
  
  let option_perm2_variation t1 t2 p1 p2 =
    let r_t = X86_BASE_PARSER.Coq_pair_t ((option_t t1),
      (X86_BASE_PARSER.Coq_tipe_t t2))
    in
    alt r_t
      (map (X86_BASE_PARSER.Coq_tipe_t t2) r_t p2 (fun p ->
        Obj.magic (None, p)))
      (map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_tipe_t t1),
        (X86_BASE_PARSER.Coq_tipe_t t2))) r_t
        (perm2 (X86_BASE_PARSER.Coq_tipe_t t1) (X86_BASE_PARSER.Coq_tipe_t
          t2) p1 p2) (fun p ->
        let (a, b) = Obj.magic p in Obj.magic ((Some a), b)))
  
  (** val option_perm3_variation :
      X86_PARSER_ARG.tipe -> X86_PARSER_ARG.tipe -> X86_PARSER_ARG.tipe ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser **)
  
  let option_perm3_variation t1 t2 t3 p1 p2 p3 =
    let r_t = X86_BASE_PARSER.Coq_pair_t ((option_t t1),
      (X86_BASE_PARSER.Coq_pair_t ((option_t t2), (X86_BASE_PARSER.Coq_tipe_t
      t3))))
    in
    alt r_t
      (map (X86_BASE_PARSER.Coq_tipe_t t3) r_t p3 (fun p ->
        Obj.magic (None, (None, p))))
      (alt r_t
        (map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_tipe_t t1),
          (X86_BASE_PARSER.Coq_tipe_t t3))) r_t
          (perm2 (X86_BASE_PARSER.Coq_tipe_t t1) (X86_BASE_PARSER.Coq_tipe_t
            t3) p1 p3) (fun p ->
          let (a, c) = Obj.magic p in Obj.magic ((Some a), (None, c))))
        (alt r_t
          (map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_tipe_t t2),
            (X86_BASE_PARSER.Coq_tipe_t t3))) r_t
            (perm2 (X86_BASE_PARSER.Coq_tipe_t t2)
              (X86_BASE_PARSER.Coq_tipe_t t3) p2 p3) (fun p ->
            let (b, c) = Obj.magic p in Obj.magic (None, ((Some b), c))))
          (map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_tipe_t t1),
            (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_tipe_t t2),
            (X86_BASE_PARSER.Coq_tipe_t t3))))) r_t
            (perm3 (X86_BASE_PARSER.Coq_tipe_t t1)
              (X86_BASE_PARSER.Coq_tipe_t t2) (X86_BASE_PARSER.Coq_tipe_t t3)
              p1 p2 p3) (fun p ->
            let (a, r) = Obj.magic p in
            let (b, c) = r in Obj.magic ((Some a), ((Some b), c))))))
  
  (** val option_perm4 :
      X86_PARSER_ARG.tipe -> X86_PARSER_ARG.tipe -> X86_PARSER_ARG.tipe ->
      X86_PARSER_ARG.tipe -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser ->
      X86_BASE_PARSER.coq_parser -> X86_BASE_PARSER.coq_parser **)
  
  let option_perm4 t1 t2 t3 t4 p1 p2 p3 p4 =
    let r_t = X86_BASE_PARSER.Coq_pair_t ((option_t t1),
      (X86_BASE_PARSER.Coq_pair_t ((option_t t2), (X86_BASE_PARSER.Coq_pair_t
      ((option_t t3), (option_t t4))))))
    in
    alt r_t
      (map X86_BASE_PARSER.Coq_unit_t r_t X86_BASE_PARSER.Eps_p (fun p ->
        Obj.magic (None, (None, (None, None)))))
      (alt r_t
        (map (X86_BASE_PARSER.Coq_tipe_t t1) r_t p1 (fun p ->
          Obj.magic ((Some p), (None, (None, None)))))
        (alt r_t
          (map (X86_BASE_PARSER.Coq_tipe_t t2) r_t p2 (fun p ->
            Obj.magic (None, ((Some p), (None, None)))))
          (alt r_t
            (map (X86_BASE_PARSER.Coq_tipe_t t3) r_t p3 (fun p ->
              Obj.magic (None, (None, ((Some p), None)))))
            (alt r_t
              (map (X86_BASE_PARSER.Coq_tipe_t t4) r_t p4 (fun p ->
                Obj.magic (None, (None, (None, (Some p))))))
              (alt r_t
                (map (X86_BASE_PARSER.Coq_pair_t ((X86_BASE_PARSER.Coq_tipe_t
                  t1), (X86_BASE_PARSER.Coq_tipe_t t2))) r_t
                  (perm2 (X86_BASE_PARSER.Coq_tipe_t t1)
                    (X86_BASE_PARSER.Coq_tipe_t t2) p1 p2) (fun p ->
                  let (a, b) = Obj.magic p in
                  Obj.magic ((Some a), ((Some b), (None, None)))))
                (alt r_t
                  (map (X86_BASE_PARSER.Coq_pair_t
                    ((X86_BASE_PARSER.Coq_tipe_t t1),
                    (X86_BASE_PARSER.Coq_tipe_t t3))) r_t
                    (perm2 (X86_BASE_PARSER.Coq_tipe_t t1)
                      (X86_BASE_PARSER.Coq_tipe_t t3) p1 p3) (fun p ->
                    let (a, c) = Obj.magic p in
                    Obj.magic ((Some a), (None, ((Some c), None)))))
                  (alt r_t
                    (map (X86_BASE_PARSER.Coq_pair_t
                      ((X86_BASE_PARSER.Coq_tipe_t t1),
                      (X86_BASE_PARSER.Coq_tipe_t t4))) r_t
                      (perm2 (X86_BASE_PARSER.Coq_tipe_t t1)
                        (X86_BASE_PARSER.Coq_tipe_t t4) p1 p4) (fun p ->
                      let (a, d) = Obj.magic p in
                      Obj.magic ((Some a), (None, (None, (Some d))))))
                    (alt r_t
                      (map (X86_BASE_PARSER.Coq_pair_t
                        ((X86_BASE_PARSER.Coq_tipe_t t2),
                        (X86_BASE_PARSER.Coq_tipe_t t3))) r_t
                        (perm2 (X86_BASE_PARSER.Coq_tipe_t t2)
                          (X86_BASE_PARSER.Coq_tipe_t t3) p2 p3) (fun p ->
                        let (b, c) = Obj.magic p in
                        Obj.magic (None, ((Some b), ((Some c), None)))))
                      (alt r_t
                        (map (X86_BASE_PARSER.Coq_pair_t
                          ((X86_BASE_PARSER.Coq_tipe_t t2),
                          (X86_BASE_PARSER.Coq_tipe_t t4))) r_t
                          (perm2 (X86_BASE_PARSER.Coq_tipe_t t2)
                            (X86_BASE_PARSER.Coq_tipe_t t4) p2 p4) (fun p ->
                          let (b, d) = Obj.magic p in
                          Obj.magic (None, ((Some b), (None, (Some d))))))
                        (alt r_t
                          (map (X86_BASE_PARSER.Coq_pair_t
                            ((X86_BASE_PARSER.Coq_tipe_t t3),
                            (X86_BASE_PARSER.Coq_tipe_t t4))) r_t
                            (perm2 (X86_BASE_PARSER.Coq_tipe_t t3)
                              (X86_BASE_PARSER.Coq_tipe_t t4) p3 p4)
                            (fun p ->
                            let (c, d) = Obj.magic p in
                            Obj.magic (None, (None, ((Some c), (Some d))))))
                          (alt r_t
                            (map (X86_BASE_PARSER.Coq_pair_t
                              ((X86_BASE_PARSER.Coq_tipe_t t1),
                              (X86_BASE_PARSER.Coq_pair_t
                              ((X86_BASE_PARSER.Coq_tipe_t t2),
                              (X86_BASE_PARSER.Coq_tipe_t t3))))) r_t
                              (perm3 (X86_BASE_PARSER.Coq_tipe_t t1)
                                (X86_BASE_PARSER.Coq_tipe_t t2)
                                (X86_BASE_PARSER.Coq_tipe_t t3) p1 p2 p3)
                              (fun p ->
                              let (a, r) = Obj.magic p in
                              let (b, c) = r in
                              Obj.magic ((Some a), ((Some b), ((Some c),
                                None)))))
                            (alt r_t
                              (map (X86_BASE_PARSER.Coq_pair_t
                                ((X86_BASE_PARSER.Coq_tipe_t t1),
                                (X86_BASE_PARSER.Coq_pair_t
                                ((X86_BASE_PARSER.Coq_tipe_t t3),
                                (X86_BASE_PARSER.Coq_tipe_t t4))))) r_t
                                (perm3 (X86_BASE_PARSER.Coq_tipe_t t1)
                                  (X86_BASE_PARSER.Coq_tipe_t t3)
                                  (X86_BASE_PARSER.Coq_tipe_t t4) p1 p3 p4)
                                (fun p ->
                                let (a, r) = Obj.magic p in
                                let (c, d) = r in
                                Obj.magic ((Some a), (None, ((Some c), (Some
                                  d))))))
                              (alt r_t
                                (map (X86_BASE_PARSER.Coq_pair_t
                                  ((X86_BASE_PARSER.Coq_tipe_t t1),
                                  (X86_BASE_PARSER.Coq_pair_t
                                  ((X86_BASE_PARSER.Coq_tipe_t t2),
                                  (X86_BASE_PARSER.Coq_tipe_t t4))))) r_t
                                  (perm3 (X86_BASE_PARSER.Coq_tipe_t t1)
                                    (X86_BASE_PARSER.Coq_tipe_t t2)
                                    (X86_BASE_PARSER.Coq_tipe_t t4) p1 p2 p4)
                                  (fun p ->
                                  let (a, r) = Obj.magic p in
                                  let (b, d) = r in
                                  Obj.magic ((Some a), ((Some b), (None,
                                    (Some d))))))
                                (alt r_t
                                  (map (X86_BASE_PARSER.Coq_pair_t
                                    ((X86_BASE_PARSER.Coq_tipe_t t2),
                                    (X86_BASE_PARSER.Coq_pair_t
                                    ((X86_BASE_PARSER.Coq_tipe_t t3),
                                    (X86_BASE_PARSER.Coq_tipe_t t4))))) r_t
                                    (perm3 (X86_BASE_PARSER.Coq_tipe_t t2)
                                      (X86_BASE_PARSER.Coq_tipe_t t3)
                                      (X86_BASE_PARSER.Coq_tipe_t t4) p2 p3
                                      p4) (fun p ->
                                    let (b, r) = Obj.magic p in
                                    let (c, d) = r in
                                    Obj.magic (None, ((Some b), ((Some c),
                                      (Some d))))))
                                  (map (X86_BASE_PARSER.Coq_pair_t
                                    ((X86_BASE_PARSER.Coq_tipe_t t1),
                                    (X86_BASE_PARSER.Coq_pair_t
                                    ((X86_BASE_PARSER.Coq_tipe_t t2),
                                    (X86_BASE_PARSER.Coq_pair_t
                                    ((X86_BASE_PARSER.Coq_tipe_t t3),
                                    (X86_BASE_PARSER.Coq_tipe_t t4))))))) r_t
                                    (perm4 (X86_BASE_PARSER.Coq_tipe_t t1)
                                      (X86_BASE_PARSER.Coq_tipe_t t2)
                                      (X86_BASE_PARSER.Coq_tipe_t t3)
                                      (X86_BASE_PARSER.Coq_tipe_t t4) p1 p2
                                      p3 p4) (fun p ->
                                    let (a, r) = Obj.magic p in
                                    let (b, r0) = r in
                                    let (c, d) = r0 in
                                    Obj.magic ((Some a), ((Some b), ((Some
                                      c), (Some d))))))))))))))))))))
  
  (** val opt2b : bool option -> bool -> bool **)
  
  let opt2b a default =
    match a with
    | Some b -> b
    | None -> default
  
  (** val prefix_parser_rep : X86_BASE_PARSER.coq_parser **)
  
  let prefix_parser_rep =
    map (X86_BASE_PARSER.Coq_pair_t ((option_t X86_PARSER_ARG.Lock_or_Rep_t),
      (X86_BASE_PARSER.Coq_pair_t
      ((option_t X86_PARSER_ARG.Segment_Register_t),
      (option_t X86_PARSER_ARG.Bool_t))))) prefix_t
      (option_perm3 X86_PARSER_ARG.Lock_or_Rep_t
        X86_PARSER_ARG.Segment_Register_t X86_PARSER_ARG.Bool_t rep_p
        segment_override_p op_override_p) (fun p ->
      let (l, r) = Obj.magic p in
      let (s, op) = r in
      Obj.magic { lock_rep = l; seg_override = s; op_override =
        (opt2b op false); addr_override = false })
  
  (** val instr_parsers_rep : X86_BASE_PARSER.coq_parser list **)
  
  let instr_parsers_rep =
    coq_INS_p :: (coq_OUTS_p :: (coq_MOVS_p :: (coq_LODS_p :: (coq_STOS_p :: (coq_RET_p :: [])))))
  
  (** val prefix_parser_rep_or_repn : X86_BASE_PARSER.coq_parser **)
  
  let prefix_parser_rep_or_repn =
    map (X86_BASE_PARSER.Coq_pair_t ((option_t X86_PARSER_ARG.Lock_or_Rep_t),
      (X86_BASE_PARSER.Coq_pair_t
      ((option_t X86_PARSER_ARG.Segment_Register_t),
      (option_t X86_PARSER_ARG.Bool_t))))) prefix_t
      (option_perm3 X86_PARSER_ARG.Lock_or_Rep_t
        X86_PARSER_ARG.Segment_Register_t X86_PARSER_ARG.Bool_t rep_or_repn_p
        segment_override_p op_override_p) (fun p ->
      let (l, r) = Obj.magic p in
      let (s, op) = r in
      Obj.magic { lock_rep = l; seg_override = s; op_override =
        (opt2b op false); addr_override = false })
  
  (** val instr_parsers_rep_or_repn : X86_BASE_PARSER.coq_parser list **)
  
  let instr_parsers_rep_or_repn =
    coq_CMPS_p :: (coq_SCAS_p :: [])
  
  (** val prefix_parser_lock_with_op_override :
      X86_BASE_PARSER.coq_parser **)
  
  let prefix_parser_lock_with_op_override =
    map (X86_BASE_PARSER.Coq_pair_t ((option_t X86_PARSER_ARG.Lock_or_Rep_t),
      (X86_BASE_PARSER.Coq_pair_t
      ((option_t X86_PARSER_ARG.Segment_Register_t),
      (X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Bool_t))))) prefix_t
      (option_perm3_variation X86_PARSER_ARG.Lock_or_Rep_t
        X86_PARSER_ARG.Segment_Register_t X86_PARSER_ARG.Bool_t lock_p
        segment_override_p op_override_p) (fun p ->
      let (l, r) = Obj.magic p in
      let (s, op) = r in
      Obj.magic { lock_rep = l; seg_override = s; op_override = op;
        addr_override = false })
  
  (** val instr_parsers_lock_with_op_override :
      X86_BASE_PARSER.coq_parser list **)
  
  let instr_parsers_lock_with_op_override =
    (coq_ADD_p true) :: ((coq_ADC_p true) :: ((coq_AND_p true) :: (coq_NEG_p :: (coq_NOT_p :: (
      (coq_OR_p true) :: ((coq_SBB_p true) :: ((coq_SUB_p true) :: ((coq_XOR_p
                                                                    true) :: (coq_XCHG_p :: [])))))))))
  
  (** val prefix_parser_lock_no_op_override : X86_BASE_PARSER.coq_parser **)
  
  let prefix_parser_lock_no_op_override =
    map (X86_BASE_PARSER.Coq_pair_t ((option_t X86_PARSER_ARG.Lock_or_Rep_t),
      (option_t X86_PARSER_ARG.Segment_Register_t))) prefix_t
      (option_perm2 X86_PARSER_ARG.Lock_or_Rep_t
        X86_PARSER_ARG.Segment_Register_t lock_p segment_override_p)
      (fun p ->
      let (l, s) = Obj.magic p in
      Obj.magic { lock_rep = l; seg_override = s; op_override = false;
        addr_override = false })
  
  (** val instr_parsers_lock_no_op_override :
      X86_BASE_PARSER.coq_parser list **)
  
  let instr_parsers_lock_no_op_override =
    (coq_ADD_p false) :: ((coq_ADC_p false) :: ((coq_AND_p false) :: (coq_BTC_p :: (coq_BTR_p :: (coq_BTS_p :: (coq_CMPXCHG_p :: (coq_DEC_p :: (coq_INC_p :: (coq_NEG_p :: (coq_NOT_p :: (
      (coq_OR_p false) :: ((coq_SBB_p false) :: ((coq_SUB_p false) :: (
      (coq_XOR_p false) :: (coq_XADD_p :: (coq_XCHG_p :: []))))))))))))))))
  
  (** val prefix_parser_seg_with_op_override : X86_BASE_PARSER.coq_parser **)
  
  let prefix_parser_seg_with_op_override =
    map (X86_BASE_PARSER.Coq_pair_t
      ((option_t X86_PARSER_ARG.Segment_Register_t),
      (X86_BASE_PARSER.Coq_tipe_t X86_PARSER_ARG.Bool_t))) prefix_t
      (option_perm2_variation X86_PARSER_ARG.Segment_Register_t
        X86_PARSER_ARG.Bool_t segment_override_p op_override_p) (fun p ->
      let (s, op) = Obj.magic p in
      Obj.magic { lock_rep = None; seg_override = s; op_override = op;
        addr_override = false })
  
  (** val instr_parsers_seg_with_op_override :
      X86_BASE_PARSER.coq_parser list **)
  
  let instr_parsers_seg_with_op_override =
    (coq_CMP_p true) :: ((coq_IMUL_p true) :: ((coq_MOV_p true) :: ((coq_TEST_p
                                                                    true) :: [])))
  
  (** val prefix_parser_seg_op_override : X86_BASE_PARSER.coq_parser **)
  
  let prefix_parser_seg_op_override =
    map (X86_BASE_PARSER.Coq_pair_t
      ((option_t X86_PARSER_ARG.Segment_Register_t),
      (option_t X86_PARSER_ARG.Bool_t))) prefix_t
      (option_perm2 X86_PARSER_ARG.Segment_Register_t X86_PARSER_ARG.Bool_t
        segment_override_p op_override_p) (fun p ->
      let (s, op) = Obj.magic p in
      Obj.magic { lock_rep = None; seg_override = s; op_override =
        (opt2b op false); addr_override = false })
  
  (** val instr_parsers_seg_op_override : X86_BASE_PARSER.coq_parser list **)
  
  let instr_parsers_seg_op_override =
    coq_CMOVcc_p :: (coq_ROL_p :: (coq_ROR_p :: (coq_SAR_p :: (coq_SHL_p :: (coq_SHLD_p :: (coq_SHR_p :: (coq_SHRD_p :: (coq_MOVSX_p :: (coq_MOVZX_p :: (coq_DIV_p :: (coq_IDIV_p :: (coq_CDQ_p :: (coq_CWDE_p :: (coq_MUL_p :: []))))))))))))))
  
  (** val prefix_parser_seg_override : X86_BASE_PARSER.coq_parser **)
  
  let prefix_parser_seg_override =
    map (option_t X86_PARSER_ARG.Segment_Register_t) prefix_t
      (option_perm X86_PARSER_ARG.Segment_Register_t segment_override_p)
      (fun s ->
      Obj.magic { lock_rep = None; seg_override = (Obj.magic s);
        op_override = false; addr_override = false })
  
  (** val instr_parsers_seg_override : X86_BASE_PARSER.coq_parser list **)
  
  let instr_parsers_seg_override =
    coq_AAA_p :: (coq_AAD_p :: (coq_AAM_p :: (coq_AAS_p :: ((coq_CMP_p false) :: (coq_ARPL_p :: (coq_BOUND_p :: (coq_BSF_p :: (coq_BSR_p :: (coq_BSWAP_p :: (coq_BT_p :: (coq_CALL_p :: (coq_CLC_p :: (coq_CLD_p :: (coq_CLI_p :: (coq_CMC_p :: (coq_CPUID_p :: (coq_DAA_p :: (coq_HLT_p :: (
      (coq_IMUL_p false) :: (coq_IN_p :: (coq_INTn_p :: (coq_INT_p :: (coq_INTO_p :: (coq_INVD_p :: (coq_INVLPG_p :: (coq_IRET_p :: (coq_Jcc_p :: (coq_JCXZ_p :: (coq_JMP_p :: (coq_LAHF_p :: (coq_LAR_p :: (coq_LDS_p :: (coq_LEA_p :: (coq_LEAVE_p :: (coq_LES_p :: (coq_LFS_p :: (coq_LGDT_p :: (coq_LGS_p :: (coq_LIDT_p :: (coq_LLDT_p :: (coq_LMSW_p :: (coq_LOOP_p :: (coq_LOOPZ_p :: (coq_LOOPNZ_p :: (coq_LSL_p :: (coq_LSS_p :: (coq_LTR_p :: (
      (coq_MOV_p false) :: (coq_MOVCR_p :: (coq_MOVDR_p :: (coq_MOVSR_p :: (coq_MOVBE_p :: (coq_OUT_p :: (coq_POP_p :: (coq_POPSR_p :: (coq_POPA_p :: (coq_POPF_p :: (coq_PUSH_p :: (coq_PUSHSR_p :: (coq_PUSHA_p :: (coq_PUSHF_p :: (coq_RCL_p :: (coq_RCR_p :: (coq_RDMSR_p :: (coq_RDPMC_p :: (coq_RDTSC_p :: (coq_RDTSCP_p :: (coq_RSM_p :: (coq_SAHF_p :: (coq_SETcc_p :: (coq_SGDT_p :: (coq_SIDT_p :: (coq_SLDT_p :: (coq_SMSW_p :: (coq_STC_p :: (coq_STD_p :: (coq_STI_p :: (coq_STR_p :: (
      (coq_TEST_p false) :: (coq_UD2_p :: (coq_VERR_p :: (coq_VERW_p :: (coq_WBINVD_p :: (coq_WRMSR_p :: (coq_XLAT_p :: (coq_F2XM1_p :: (coq_FABS_p :: (coq_FADD_p :: (coq_FADDP_p :: (coq_FBLD_p :: (coq_FBSTP_p :: (coq_FCHS_p :: (coq_FCLEX_p :: (coq_FCMOVcc_p :: (coq_FCOM_p :: (coq_FCOMP_p :: (coq_FCOMPP_p :: (coq_FCOMIP_p :: (coq_FCOS_p :: (coq_FDECSTP_p :: (coq_FDIV_p :: (coq_FDIVP_p :: (coq_FDIVR_p :: (coq_FDIVRP_p :: (coq_FFREE_p :: (coq_FIADD_p :: (coq_FICOM_p :: (coq_FICOMP_p :: (coq_FIDIV_p :: (coq_FIDIVR_p :: (coq_FILD_p :: (coq_FIMUL_p :: (coq_FINCSTP_p :: (coq_FIST_p :: (coq_FISTP_p :: (coq_FISUB_p :: (coq_FISUBR_p :: (coq_FLD_p :: (coq_FLD1_p :: (coq_FLDCW_p :: (coq_FLDENV_p :: (coq_FLDL2E_p :: (coq_FLDL2T_p :: (coq_FLDLG2_p :: (coq_FLDLN2_p :: (coq_FLDPI_p :: (coq_FLDZ_p :: (coq_FMUL_p :: (coq_FMULP_p :: (coq_FNOP_p :: (coq_FNSAVE_p :: (coq_FNSTCW_p :: (coq_FNSTSW_p :: (coq_FPATAN_p :: (coq_FPREM_p :: (coq_FPREM1_p :: (coq_FPTAN_p :: (coq_FRNDINT_p :: (coq_FRSTOR_p :: (coq_FSCALE_p :: (coq_FSIN_p :: (coq_FSINCOS_p :: (coq_FSQRT_p :: (coq_FST_p :: (coq_FSTENV_p :: (coq_FSTP_p :: (coq_FSUB_p :: (coq_FSUBP_p :: (coq_FSUBR_p :: (coq_FSUBRP_p :: (coq_FTST_p :: (coq_FUCOM_p :: (coq_FUCOMP_p :: (coq_FUCOMPP_p :: (coq_FUCOMI_p :: (coq_FUCOMIP_p :: (coq_FXAM_p :: (coq_FXCH_p :: (coq_FXTRACT_p :: (coq_FYL2X_p :: (coq_FYL2XP1_p :: (coq_FWAIT_p :: (coq_EMMS_p :: (coq_MOVD_p :: (coq_MOVQ_p :: (coq_PACKSSDW_p :: (coq_PACKSSWB_p :: (coq_PACKUSWB_p :: (coq_PADD_p :: (coq_PADDS_p :: (coq_PADDUS_p :: (coq_PAND_p :: (coq_PANDN_p :: (coq_PCMPEQ_p :: (coq_PCMPGT_p :: (coq_PMADDWD_p :: (coq_PMULHUW_p :: (coq_PMULHW_p :: (coq_PMULLW_p :: (coq_POR_p :: (coq_PSLL_p :: (coq_PSRA_p :: (coq_PSRL_p :: (coq_PSUB_p :: (coq_PSUBS_p :: (coq_PSUBUS_p :: (coq_PUNPCKH_p :: (coq_PUNPCKL_p :: (coq_PXOR_p :: (coq_ADDPS_p :: (coq_ADDSS_p :: (coq_ANDNPS_p :: (coq_ANDPS_p :: (coq_CMPPS_p :: (coq_CMPSS_p :: (coq_COMISS_p :: (coq_CVTPI2PS_p :: (coq_CVTPS2PI_p :: (coq_CVTSI2SS_p :: (coq_CVTSS2SI_p :: (coq_CVTTPS2PI_p :: (coq_CVTTSS2SI_p :: (coq_DIVPS_p :: (coq_DIVSS_p :: (coq_LDMXCSR_p :: (coq_MAXPS_p :: (coq_MAXSS_p :: (coq_MINPS_p :: (coq_MINSS_p :: (coq_MOVAPS_p :: (coq_MOVHLPS_p :: (coq_MOVLPS_p :: (coq_MOVMSKPS_p :: (coq_MOVSS_p :: (coq_MOVUPS_p :: (coq_MULPS_p :: (coq_MULSS_p :: (coq_ORPS_p :: (coq_RCPPS_p :: (coq_RCPSS_p :: (coq_RSQRTPS_p :: (coq_RSQRTSS_p :: (coq_SHUFPS_p :: (coq_SQRTPS_p :: (coq_SQRTSS_p :: (coq_STMXCSR_p :: (coq_SUBPS_p :: (coq_SUBSS_p :: (coq_UCOMISS_p :: (coq_UNPCKHPS_p :: (coq_UNPCKLPS_p :: (coq_XORPS_p :: (coq_PAVGB_p :: (coq_PEXTRW_p :: (coq_PINSRW_p :: (coq_PMAXSW_p :: (coq_PMAXUB_p :: (coq_PMINSW_p :: (coq_PMINUB_p :: (coq_PMOVMSKB_p :: (coq_PSADBW_p :: (coq_PSHUFW_p :: (coq_MASKMOVQ_p :: (coq_MOVNTPS_p :: (coq_MOVNTQ_p :: (coq_PREFETCHT0_p :: (coq_PREFETCHT1_p :: (coq_PREFETCHT2_p :: (coq_PREFETCHNTA_p :: (coq_SFENCE_p :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  
  (** val instruction_parser_list : X86_BASE_PARSER.coq_parser list **)
  
  let instruction_parser_list =
    app
      (List0.map (fun p -> seq prefix_t instruction_t prefix_parser_rep p)
        instr_parsers_rep)
      (app
        (List0.map (fun p ->
          seq prefix_t instruction_t prefix_parser_rep_or_repn p)
          instr_parsers_rep_or_repn)
        (app
          (List0.map (fun p ->
            seq prefix_t instruction_t prefix_parser_lock_with_op_override p)
            instr_parsers_lock_with_op_override)
          (app
            (List0.map (fun p ->
              seq prefix_t instruction_t prefix_parser_lock_no_op_override p)
              instr_parsers_lock_no_op_override)
            (app
              (List0.map (fun p ->
                seq prefix_t instruction_t prefix_parser_seg_with_op_override
                  p) instr_parsers_seg_with_op_override)
              (app
                (List0.map (fun p ->
                  seq prefix_t instruction_t prefix_parser_seg_op_override p)
                  instr_parsers_seg_op_override)
                (List0.map (fun p ->
                  seq prefix_t instruction_t prefix_parser_seg_override p)
                  instr_parsers_seg_override))))))
  
  (** val instruction_parser : X86_BASE_PARSER.coq_parser **)
  
  let instruction_parser =
    alts (X86_BASE_PARSER.Coq_pair_t (prefix_t, instruction_t))
      instruction_parser_list
  
  (** val instruction_regexp_pair :
      X86_BASE_PARSER.regexp * X86_BASE_PARSER.ctxt_t **)
  
  let instruction_regexp_pair =
    X86_BASE_PARSER.parser2regexp (X86_BASE_PARSER.Coq_pair_t (prefix_t,
      instruction_t)) instruction_parser
  
  type instParserState = { inst_ctxt : X86_BASE_PARSER.ctxt_t;
                           inst_regexp : X86_BASE_PARSER.regexp }
  
  (** val instParserState_rect :
      (X86_BASE_PARSER.ctxt_t -> X86_BASE_PARSER.regexp -> __ -> 'a1) ->
      instParserState -> 'a1 **)
  
  let instParserState_rect f i =
    let { inst_ctxt = x; inst_regexp = x0 } = i in f x x0 __
  
  (** val instParserState_rec :
      (X86_BASE_PARSER.ctxt_t -> X86_BASE_PARSER.regexp -> __ -> 'a1) ->
      instParserState -> 'a1 **)
  
  let instParserState_rec f i =
    let { inst_ctxt = x; inst_regexp = x0 } = i in f x x0 __
  
  (** val inst_ctxt : instParserState -> X86_BASE_PARSER.ctxt_t **)
  
  let inst_ctxt x = x.inst_ctxt
  
  (** val inst_regexp : instParserState -> X86_BASE_PARSER.regexp **)
  
  let inst_regexp x = x.inst_regexp
  
  (** val initial_parser_state : instParserState **)
  
  let initial_parser_state =
    { inst_ctxt = (snd instruction_regexp_pair); inst_regexp =
      (fst instruction_regexp_pair) }
  
  (** val byte_explode : int8 -> bool list **)
  
  let byte_explode b =
    let bs =
      Word.bits_of_Z (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
        (Big.succ (Big.succ (Big.succ Big.zero))))))))
        (Word.unsigned (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
          (Big.succ (Big.succ Big.zero))))))) b)
    in
    (bs (Big.doubleplusone (Big.doubleplusone Big.one))) :: ((bs (Big.double
                                                               (Big.doubleplusone
                                                               Big.one))) :: (
    (bs (Big.doubleplusone (Big.double Big.one))) :: ((bs (Big.double
                                                        (Big.double
                                                        Big.one))) :: (
    (bs (Big.doubleplusone Big.one)) :: ((bs (Big.double Big.one)) :: (
    (bs Big.one) :: ((bs Big.zero) :: [])))))))
  
  (** val parse_byte :
      instParserState -> int8 -> instParserState * (prefix * instr) list **)
  
  let parse_byte ps b =
    let cs = byte_explode b in
    let r' =
      X86_BASE_PARSER.deriv_parse' (X86_BASE_PARSER.Coq_pair_t (prefix_t,
        instruction_t)) ps.inst_regexp cs
    in
    ({ inst_ctxt = ps.inst_ctxt; inst_regexp = r' },
    (Obj.magic
      (X86_BASE_PARSER.apply_null ps.inst_ctxt (X86_BASE_PARSER.Coq_pair_t
        (prefix_t, instruction_t)) r')))
 end

