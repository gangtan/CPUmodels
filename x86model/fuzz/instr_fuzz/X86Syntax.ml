open Bits

(** val zero_extend8_32 : int8 -> int32 **)

let zero_extend8_32 w =
  Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ
    Big.zero)))))))))))))))))))))))))))))))
    (Word.unsigned (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ Big.zero))))))) w)

(** val sign_extend8_32 : int8 -> int32 **)

let sign_extend8_32 w =
  Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ
    Big.zero)))))))))))))))))))))))))))))))
    (Word.signed (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ Big.zero))))))) w)

(** val zero_extend16_32 : int16 -> int32 **)

let zero_extend16_32 w =
  Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ
    Big.zero)))))))))))))))))))))))))))))))
    (Word.unsigned (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ Big.zero))))))))))))))) w)

(** val sign_extend16_32 : int16 -> int32 **)

let sign_extend16_32 w =
  Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ
    Big.zero)))))))))))))))))))))))))))))))
    (Word.signed (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ Big.zero))))))))))))))) w)

type port_number = int8

type interrupt_type = int8

type selector = int16

type register =
| EAX
| ECX
| EDX
| EBX
| ESP
| EBP
| ESI
| EDI

(** val register_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> register -> 'a1 **)

let register_rect f f0 f1 f2 f3 f4 f5 f6 = function
| EAX -> f
| ECX -> f0
| EDX -> f1
| EBX -> f2
| ESP -> f3
| EBP -> f4
| ESI -> f5
| EDI -> f6

(** val register_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> register -> 'a1 **)

let register_rec f f0 f1 f2 f3 f4 f5 f6 = function
| EAX -> f
| ECX -> f0
| EDX -> f1
| EBX -> f2
| ESP -> f3
| EBP -> f4
| ESI -> f5
| EDI -> f6

(** val register_eq_dec : register -> register -> bool **)

let register_eq_dec x y =
  match x with
  | EAX ->
    (match y with
     | EAX -> true
     | _ -> false)
  | ECX ->
    (match y with
     | ECX -> true
     | _ -> false)
  | EDX ->
    (match y with
     | EDX -> true
     | _ -> false)
  | EBX ->
    (match y with
     | EBX -> true
     | _ -> false)
  | ESP ->
    (match y with
     | ESP -> true
     | _ -> false)
  | EBP ->
    (match y with
     | EBP -> true
     | _ -> false)
  | ESI ->
    (match y with
     | ESI -> true
     | _ -> false)
  | EDI ->
    (match y with
     | EDI -> true
     | _ -> false)

(** val coq_Z_to_register : Big.big_int -> register **)

let coq_Z_to_register n =
  Big.z_case
    (fun _ ->
    EAX)
    (fun p ->
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        EDI)
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          EDI)
          (fun p2 ->
          EDI)
          (fun _ ->
          EBP)
          p1)
        (fun _ ->
        EBX)
        p0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          EDI)
          (fun p2 ->
          EDI)
          (fun _ ->
          ESI)
          p1)
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          EDI)
          (fun p2 ->
          EDI)
          (fun _ ->
          ESP)
          p1)
        (fun _ ->
        EDX)
        p0)
      (fun _ ->
      ECX)
      p)
    (fun p ->
    EDI)
    n

type scale =
| Scale1
| Scale2
| Scale4
| Scale8

(** val scale_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> scale -> 'a1 **)

let scale_rect f f0 f1 f2 = function
| Scale1 -> f
| Scale2 -> f0
| Scale4 -> f1
| Scale8 -> f2

(** val scale_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> scale -> 'a1 **)

let scale_rec f f0 f1 f2 = function
| Scale1 -> f
| Scale2 -> f0
| Scale4 -> f1
| Scale8 -> f2

(** val scale_eq_dec : scale -> scale -> bool **)

let scale_eq_dec x y =
  match x with
  | Scale1 ->
    (match y with
     | Scale1 -> true
     | _ -> false)
  | Scale2 ->
    (match y with
     | Scale2 -> true
     | _ -> false)
  | Scale4 ->
    (match y with
     | Scale4 -> true
     | _ -> false)
  | Scale8 ->
    (match y with
     | Scale8 -> true
     | _ -> false)

(** val coq_Z_to_scale : Big.big_int -> scale **)

let coq_Z_to_scale n =
  Big.z_case
    (fun _ ->
    Scale1)
    (fun p ->
    Big.positive_case
      (fun p0 ->
      Scale8)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        Scale8)
        (fun p1 ->
        Scale8)
        (fun _ ->
        Scale4)
        p0)
      (fun _ ->
      Scale2)
      p)
    (fun p ->
    Scale8)
    n

type segment_register =
| ES
| CS
| SS
| DS
| FS
| GS

(** val segment_register_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> segment_register -> 'a1 **)

let segment_register_rect f f0 f1 f2 f3 f4 = function
| ES -> f
| CS -> f0
| SS -> f1
| DS -> f2
| FS -> f3
| GS -> f4

(** val segment_register_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> segment_register -> 'a1 **)

let segment_register_rec f f0 f1 f2 f3 f4 = function
| ES -> f
| CS -> f0
| SS -> f1
| DS -> f2
| FS -> f3
| GS -> f4

(** val segment_register_eq_dec :
    segment_register -> segment_register -> bool **)

let segment_register_eq_dec x y =
  match x with
  | ES ->
    (match y with
     | ES -> true
     | _ -> false)
  | CS ->
    (match y with
     | CS -> true
     | _ -> false)
  | SS ->
    (match y with
     | SS -> true
     | _ -> false)
  | DS ->
    (match y with
     | DS -> true
     | _ -> false)
  | FS ->
    (match y with
     | FS -> true
     | _ -> false)
  | GS ->
    (match y with
     | GS -> true
     | _ -> false)

type control_register =
| CR0
| CR2
| CR3
| CR4

(** val control_register_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> control_register -> 'a1 **)

let control_register_rect f f0 f1 f2 = function
| CR0 -> f
| CR2 -> f0
| CR3 -> f1
| CR4 -> f2

(** val control_register_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> control_register -> 'a1 **)

let control_register_rec f f0 f1 f2 = function
| CR0 -> f
| CR2 -> f0
| CR3 -> f1
| CR4 -> f2

(** val control_register_eq_dec :
    control_register -> control_register -> bool **)

let control_register_eq_dec x y =
  match x with
  | CR0 ->
    (match y with
     | CR0 -> true
     | _ -> false)
  | CR2 ->
    (match y with
     | CR2 -> true
     | _ -> false)
  | CR3 ->
    (match y with
     | CR3 -> true
     | _ -> false)
  | CR4 ->
    (match y with
     | CR4 -> true
     | _ -> false)

type debug_register =
| DR0
| DR1
| DR2
| DR3
| DR6
| DR7

(** val debug_register_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> debug_register -> 'a1 **)

let debug_register_rect f f0 f1 f2 f3 f4 = function
| DR0 -> f
| DR1 -> f0
| DR2 -> f1
| DR3 -> f2
| DR6 -> f3
| DR7 -> f4

(** val debug_register_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> debug_register -> 'a1 **)

let debug_register_rec f f0 f1 f2 f3 f4 = function
| DR0 -> f
| DR1 -> f0
| DR2 -> f1
| DR3 -> f2
| DR6 -> f3
| DR7 -> f4

(** val debug_register_eq_dec : debug_register -> debug_register -> bool **)

let debug_register_eq_dec x y =
  match x with
  | DR0 ->
    (match y with
     | DR0 -> true
     | _ -> false)
  | DR1 ->
    (match y with
     | DR1 -> true
     | _ -> false)
  | DR2 ->
    (match y with
     | DR2 -> true
     | _ -> false)
  | DR3 ->
    (match y with
     | DR3 -> true
     | _ -> false)
  | DR6 ->
    (match y with
     | DR6 -> true
     | _ -> false)
  | DR7 ->
    (match y with
     | DR7 -> true
     | _ -> false)

type address = { addrDisp : int32; addrBase : register option;
                 addrIndex : (scale * register) option }

(** val address_rect :
    (int32 -> register option -> (scale * register) option -> 'a1) -> address
    -> 'a1 **)

let address_rect f a =
  let { addrDisp = x; addrBase = x0; addrIndex = x1 } = a in f x x0 x1

(** val address_rec :
    (int32 -> register option -> (scale * register) option -> 'a1) -> address
    -> 'a1 **)

let address_rec f a =
  let { addrDisp = x; addrBase = x0; addrIndex = x1 } = a in f x x0 x1

(** val addrDisp : address -> int32 **)

let addrDisp x = x.addrDisp

(** val addrBase : address -> register option **)

let addrBase x = x.addrBase

(** val addrIndex : address -> (scale * register) option **)

let addrIndex x = x.addrIndex

type operand =
| Imm_op of int32
| Reg_op of register
| Address_op of address
| Offset_op of int32

(** val operand_rect :
    (int32 -> 'a1) -> (register -> 'a1) -> (address -> 'a1) -> (int32 -> 'a1)
    -> operand -> 'a1 **)

let operand_rect f f0 f1 f2 = function
| Imm_op x -> f x
| Reg_op x -> f0 x
| Address_op x -> f1 x
| Offset_op x -> f2 x

(** val operand_rec :
    (int32 -> 'a1) -> (register -> 'a1) -> (address -> 'a1) -> (int32 -> 'a1)
    -> operand -> 'a1 **)

let operand_rec f f0 f1 f2 = function
| Imm_op x -> f x
| Reg_op x -> f0 x
| Address_op x -> f1 x
| Offset_op x -> f2 x

type reg_or_immed =
| Reg_ri of register
| Imm_ri of int8

(** val reg_or_immed_rect :
    (register -> 'a1) -> (int8 -> 'a1) -> reg_or_immed -> 'a1 **)

let reg_or_immed_rect f f0 = function
| Reg_ri x -> f x
| Imm_ri x -> f0 x

(** val reg_or_immed_rec :
    (register -> 'a1) -> (int8 -> 'a1) -> reg_or_immed -> 'a1 **)

let reg_or_immed_rec f f0 = function
| Reg_ri x -> f x
| Imm_ri x -> f0 x

type condition_type =
| O_ct
| NO_ct
| B_ct
| NB_ct
| E_ct
| NE_ct
| BE_ct
| NBE_ct
| S_ct
| NS_ct
| P_ct
| NP_ct
| L_ct
| NL_ct
| LE_ct
| NLE_ct

(** val condition_type_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> condition_type -> 'a1 **)

let condition_type_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
| O_ct -> f
| NO_ct -> f0
| B_ct -> f1
| NB_ct -> f2
| E_ct -> f3
| NE_ct -> f4
| BE_ct -> f5
| NBE_ct -> f6
| S_ct -> f7
| NS_ct -> f8
| P_ct -> f9
| NP_ct -> f10
| L_ct -> f11
| NL_ct -> f12
| LE_ct -> f13
| NLE_ct -> f14

(** val condition_type_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> condition_type -> 'a1 **)

let condition_type_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
| O_ct -> f
| NO_ct -> f0
| B_ct -> f1
| NB_ct -> f2
| E_ct -> f3
| NE_ct -> f4
| BE_ct -> f5
| NBE_ct -> f6
| S_ct -> f7
| NS_ct -> f8
| P_ct -> f9
| NP_ct -> f10
| L_ct -> f11
| NL_ct -> f12
| LE_ct -> f13
| NLE_ct -> f14

(** val condition_type_eq_dec : condition_type -> condition_type -> bool **)

let condition_type_eq_dec x y =
  match x with
  | O_ct ->
    (match y with
     | O_ct -> true
     | _ -> false)
  | NO_ct ->
    (match y with
     | NO_ct -> true
     | _ -> false)
  | B_ct ->
    (match y with
     | B_ct -> true
     | _ -> false)
  | NB_ct ->
    (match y with
     | NB_ct -> true
     | _ -> false)
  | E_ct ->
    (match y with
     | E_ct -> true
     | _ -> false)
  | NE_ct ->
    (match y with
     | NE_ct -> true
     | _ -> false)
  | BE_ct ->
    (match y with
     | BE_ct -> true
     | _ -> false)
  | NBE_ct ->
    (match y with
     | NBE_ct -> true
     | _ -> false)
  | S_ct ->
    (match y with
     | S_ct -> true
     | _ -> false)
  | NS_ct ->
    (match y with
     | NS_ct -> true
     | _ -> false)
  | P_ct ->
    (match y with
     | P_ct -> true
     | _ -> false)
  | NP_ct ->
    (match y with
     | NP_ct -> true
     | _ -> false)
  | L_ct ->
    (match y with
     | L_ct -> true
     | _ -> false)
  | NL_ct ->
    (match y with
     | NL_ct -> true
     | _ -> false)
  | LE_ct ->
    (match y with
     | LE_ct -> true
     | _ -> false)
  | NLE_ct ->
    (match y with
     | NLE_ct -> true
     | _ -> false)

(** val coq_Z_to_condition_type : Big.big_int -> condition_type **)

let coq_Z_to_condition_type n =
  Big.z_case
    (fun _ ->
    O_ct)
    (fun p ->
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          NLE_ct)
          (fun p2 ->
          Big.positive_case
            (fun p3 ->
            NLE_ct)
            (fun p3 ->
            NLE_ct)
            (fun _ ->
            NP_ct)
            p2)
          (fun _ ->
          NBE_ct)
          p1)
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          Big.positive_case
            (fun p3 ->
            NLE_ct)
            (fun p3 ->
            NLE_ct)
            (fun _ ->
            NL_ct)
            p2)
          (fun p2 ->
          Big.positive_case
            (fun p3 ->
            NLE_ct)
            (fun p3 ->
            NLE_ct)
            (fun _ ->
            NS_ct)
            p2)
          (fun _ ->
          NE_ct)
          p1)
        (fun _ ->
        NB_ct)
        p0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          Big.positive_case
            (fun p3 ->
            NLE_ct)
            (fun p3 ->
            NLE_ct)
            (fun _ ->
            LE_ct)
            p2)
          (fun p2 ->
          Big.positive_case
            (fun p3 ->
            NLE_ct)
            (fun p3 ->
            NLE_ct)
            (fun _ ->
            P_ct)
            p2)
          (fun _ ->
          BE_ct)
          p1)
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          Big.positive_case
            (fun p3 ->
            NLE_ct)
            (fun p3 ->
            NLE_ct)
            (fun _ ->
            L_ct)
            p2)
          (fun p2 ->
          Big.positive_case
            (fun p3 ->
            NLE_ct)
            (fun p3 ->
            NLE_ct)
            (fun _ ->
            S_ct)
            p2)
          (fun _ ->
          E_ct)
          p1)
        (fun _ ->
        B_ct)
        p0)
      (fun _ ->
      NO_ct)
      p)
    (fun p ->
    NLE_ct)
    n

type fpu_register =
| ST7
| ST6
| ST5
| ST4
| ST3
| ST2
| ST1
| ST0

(** val fpu_register_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fpu_register ->
    'a1 **)

let fpu_register_rect f f0 f1 f2 f3 f4 f5 f6 = function
| ST7 -> f
| ST6 -> f0
| ST5 -> f1
| ST4 -> f2
| ST3 -> f3
| ST2 -> f4
| ST1 -> f5
| ST0 -> f6

(** val fpu_register_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fpu_register ->
    'a1 **)

let fpu_register_rec f f0 f1 f2 f3 f4 f5 f6 = function
| ST7 -> f
| ST6 -> f0
| ST5 -> f1
| ST4 -> f2
| ST3 -> f3
| ST2 -> f4
| ST1 -> f5
| ST0 -> f6

(** val fpu_register_eq_dec : fpu_register -> fpu_register -> bool **)

let fpu_register_eq_dec x y =
  match x with
  | ST7 ->
    (match y with
     | ST7 -> true
     | _ -> false)
  | ST6 ->
    (match y with
     | ST6 -> true
     | _ -> false)
  | ST5 ->
    (match y with
     | ST5 -> true
     | _ -> false)
  | ST4 ->
    (match y with
     | ST4 -> true
     | _ -> false)
  | ST3 ->
    (match y with
     | ST3 -> true
     | _ -> false)
  | ST2 ->
    (match y with
     | ST2 -> true
     | _ -> false)
  | ST1 ->
    (match y with
     | ST1 -> true
     | _ -> false)
  | ST0 ->
    (match y with
     | ST0 -> true
     | _ -> false)

type fp_debug_register =
| Coq_eMF
| Coq_eDB
| Coq_eBP
| Coq_eUD
| Coq_eNM
| Coq_eDF
| Coq_eSS
| Coq_eGP
| Coq_ePF
| Coq_eAC
| Coq_eMC

(** val fp_debug_register_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> fp_debug_register -> 'a1 **)

let fp_debug_register_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
| Coq_eMF -> f
| Coq_eDB -> f0
| Coq_eBP -> f1
| Coq_eUD -> f2
| Coq_eNM -> f3
| Coq_eDF -> f4
| Coq_eSS -> f5
| Coq_eGP -> f6
| Coq_ePF -> f7
| Coq_eAC -> f8
| Coq_eMC -> f9

(** val fp_debug_register_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> fp_debug_register -> 'a1 **)

let fp_debug_register_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
| Coq_eMF -> f
| Coq_eDB -> f0
| Coq_eBP -> f1
| Coq_eUD -> f2
| Coq_eNM -> f3
| Coq_eDF -> f4
| Coq_eSS -> f5
| Coq_eGP -> f6
| Coq_ePF -> f7
| Coq_eAC -> f8
| Coq_eMC -> f9

(** val fp_debug_register_eq_dec :
    fp_debug_register -> fp_debug_register -> bool **)

let fp_debug_register_eq_dec x y =
  match x with
  | Coq_eMF ->
    (match y with
     | Coq_eMF -> true
     | _ -> false)
  | Coq_eDB ->
    (match y with
     | Coq_eDB -> true
     | _ -> false)
  | Coq_eBP ->
    (match y with
     | Coq_eBP -> true
     | _ -> false)
  | Coq_eUD ->
    (match y with
     | Coq_eUD -> true
     | _ -> false)
  | Coq_eNM ->
    (match y with
     | Coq_eNM -> true
     | _ -> false)
  | Coq_eDF ->
    (match y with
     | Coq_eDF -> true
     | _ -> false)
  | Coq_eSS ->
    (match y with
     | Coq_eSS -> true
     | _ -> false)
  | Coq_eGP ->
    (match y with
     | Coq_eGP -> true
     | _ -> false)
  | Coq_ePF ->
    (match y with
     | Coq_ePF -> true
     | _ -> false)
  | Coq_eAC ->
    (match y with
     | Coq_eAC -> true
     | _ -> false)
  | Coq_eMC ->
    (match y with
     | Coq_eMC -> true
     | _ -> false)

type fp_status_register =
| Busy
| C3
| Top
| C2
| C1
| C0
| Es
| Sf
| Pe
| Ue
| Oe
| Ze
| De
| Ie

(** val fp_status_register_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> fp_status_register -> 'a1 **)

let fp_status_register_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
| Busy -> f
| C3 -> f0
| Top -> f1
| C2 -> f2
| C1 -> f3
| C0 -> f4
| Es -> f5
| Sf -> f6
| Pe -> f7
| Ue -> f8
| Oe -> f9
| Ze -> f10
| De -> f11
| Ie -> f12

(** val fp_status_register_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> fp_status_register -> 'a1 **)

let fp_status_register_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
| Busy -> f
| C3 -> f0
| Top -> f1
| C2 -> f2
| C1 -> f3
| C0 -> f4
| Es -> f5
| Sf -> f6
| Pe -> f7
| Ue -> f8
| Oe -> f9
| Ze -> f10
| De -> f11
| Ie -> f12

(** val fp_status_register_eq_dec :
    fp_status_register -> fp_status_register -> bool **)

let fp_status_register_eq_dec x y =
  match x with
  | Busy ->
    (match y with
     | Busy -> true
     | _ -> false)
  | C3 ->
    (match y with
     | C3 -> true
     | _ -> false)
  | Top ->
    (match y with
     | Top -> true
     | _ -> false)
  | C2 ->
    (match y with
     | C2 -> true
     | _ -> false)
  | C1 ->
    (match y with
     | C1 -> true
     | _ -> false)
  | C0 ->
    (match y with
     | C0 -> true
     | _ -> false)
  | Es ->
    (match y with
     | Es -> true
     | _ -> false)
  | Sf ->
    (match y with
     | Sf -> true
     | _ -> false)
  | Pe ->
    (match y with
     | Pe -> true
     | _ -> false)
  | Ue ->
    (match y with
     | Ue -> true
     | _ -> false)
  | Oe ->
    (match y with
     | Oe -> true
     | _ -> false)
  | Ze ->
    (match y with
     | Ze -> true
     | _ -> false)
  | De ->
    (match y with
     | De -> true
     | _ -> false)
  | Ie ->
    (match y with
     | Ie -> true
     | _ -> false)

type fp_control_register =
| Res15
| Res14
| Res13
| Res7
| Res6
| IC
| RC
| PC
| Pm
| Um
| Om
| Zm
| Dm
| Im

(** val fp_control_register_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> fp_control_register -> 'a1 **)

let fp_control_register_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
| Res15 -> f
| Res14 -> f0
| Res13 -> f1
| Res7 -> f2
| Res6 -> f3
| IC -> f4
| RC -> f5
| PC -> f6
| Pm -> f7
| Um -> f8
| Om -> f9
| Zm -> f10
| Dm -> f11
| Im -> f12

(** val fp_control_register_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> fp_control_register -> 'a1 **)

let fp_control_register_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
| Res15 -> f
| Res14 -> f0
| Res13 -> f1
| Res7 -> f2
| Res6 -> f3
| IC -> f4
| RC -> f5
| PC -> f6
| Pm -> f7
| Um -> f8
| Om -> f9
| Zm -> f10
| Dm -> f11
| Im -> f12

(** val fp_control_register_eq_dec :
    fp_control_register -> fp_control_register -> bool **)

let fp_control_register_eq_dec x y =
  match x with
  | Res15 ->
    (match y with
     | Res15 -> true
     | _ -> false)
  | Res14 ->
    (match y with
     | Res14 -> true
     | _ -> false)
  | Res13 ->
    (match y with
     | Res13 -> true
     | _ -> false)
  | Res7 ->
    (match y with
     | Res7 -> true
     | _ -> false)
  | Res6 ->
    (match y with
     | Res6 -> true
     | _ -> false)
  | IC ->
    (match y with
     | IC -> true
     | _ -> false)
  | RC ->
    (match y with
     | RC -> true
     | _ -> false)
  | PC ->
    (match y with
     | PC -> true
     | _ -> false)
  | Pm ->
    (match y with
     | Pm -> true
     | _ -> false)
  | Um ->
    (match y with
     | Um -> true
     | _ -> false)
  | Om ->
    (match y with
     | Om -> true
     | _ -> false)
  | Zm ->
    (match y with
     | Zm -> true
     | _ -> false)
  | Dm ->
    (match y with
     | Dm -> true
     | _ -> false)
  | Im ->
    (match y with
     | Im -> true
     | _ -> false)

type fp_tagWord_register =
| Coq_valid
| Coq_zero
| Coq_special
| Coq_empty

(** val fp_tagWord_register_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> fp_tagWord_register -> 'a1 **)

let fp_tagWord_register_rect f f0 f1 f2 = function
| Coq_valid -> f
| Coq_zero -> f0
| Coq_special -> f1
| Coq_empty -> f2

(** val fp_tagWord_register_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> fp_tagWord_register -> 'a1 **)

let fp_tagWord_register_rec f f0 f1 f2 = function
| Coq_valid -> f
| Coq_zero -> f0
| Coq_special -> f1
| Coq_empty -> f2

(** val fp_tagWord_register_eq_dec :
    fp_tagWord_register -> fp_tagWord_register -> bool **)

let fp_tagWord_register_eq_dec x y =
  match x with
  | Coq_valid ->
    (match y with
     | Coq_valid -> true
     | _ -> false)
  | Coq_zero ->
    (match y with
     | Coq_zero -> true
     | _ -> false)
  | Coq_special ->
    (match y with
     | Coq_special -> true
     | _ -> false)
  | Coq_empty ->
    (match y with
     | Coq_empty -> true
     | _ -> false)

(** val coq_Z_to_fp_tagWord_register : Big.big_int -> fp_tagWord_register **)

let coq_Z_to_fp_tagWord_register n =
  Big.z_case
    (fun _ ->
    Coq_valid)
    (fun p ->
    Big.positive_case
      (fun p0 ->
      Coq_empty)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        Coq_empty)
        (fun p1 ->
        Coq_empty)
        (fun _ ->
        Coq_special)
        p0)
      (fun _ ->
      Coq_zero)
      p)
    (fun p ->
    Coq_empty)
    n

type fpu_tagWords =
| Tag0
| Tag1
| Tag2
| Tag3
| Tag4
| Tag5
| Tag6
| Tag7

(** val fpu_tagWords_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fpu_tagWords ->
    'a1 **)

let fpu_tagWords_rect f f0 f1 f2 f3 f4 f5 f6 = function
| Tag0 -> f
| Tag1 -> f0
| Tag2 -> f1
| Tag3 -> f2
| Tag4 -> f3
| Tag5 -> f4
| Tag6 -> f5
| Tag7 -> f6

(** val fpu_tagWords_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fpu_tagWords ->
    'a1 **)

let fpu_tagWords_rec f f0 f1 f2 f3 f4 f5 f6 = function
| Tag0 -> f
| Tag1 -> f0
| Tag2 -> f1
| Tag3 -> f2
| Tag4 -> f3
| Tag5 -> f4
| Tag6 -> f5
| Tag7 -> f6

(** val fp_tagWords_eq_dec : fpu_tagWords -> fpu_tagWords -> bool **)

let fp_tagWords_eq_dec x y =
  match x with
  | Tag0 ->
    (match y with
     | Tag0 -> true
     | _ -> false)
  | Tag1 ->
    (match y with
     | Tag1 -> true
     | _ -> false)
  | Tag2 ->
    (match y with
     | Tag2 -> true
     | _ -> false)
  | Tag3 ->
    (match y with
     | Tag3 -> true
     | _ -> false)
  | Tag4 ->
    (match y with
     | Tag4 -> true
     | _ -> false)
  | Tag5 ->
    (match y with
     | Tag5 -> true
     | _ -> false)
  | Tag6 ->
    (match y with
     | Tag6 -> true
     | _ -> false)
  | Tag7 ->
    (match y with
     | Tag7 -> true
     | _ -> false)

type fp_lastOperandPtr_register =
| Valid
| Undefined

(** val fp_lastOperandPtr_register_rect :
    'a1 -> 'a1 -> fp_lastOperandPtr_register -> 'a1 **)

let fp_lastOperandPtr_register_rect f f0 = function
| Valid -> f
| Undefined -> f0

(** val fp_lastOperandPtr_register_rec :
    'a1 -> 'a1 -> fp_lastOperandPtr_register -> 'a1 **)

let fp_lastOperandPtr_register_rec f f0 = function
| Valid -> f
| Undefined -> f0

(** val fp_lastOperandPtr_register_eq_dec :
    fp_lastOperandPtr_register -> fp_lastOperandPtr_register -> bool **)

let fp_lastOperandPtr_register_eq_dec x y =
  match x with
  | Valid ->
    (match y with
     | Valid -> true
     | Undefined -> false)
  | Undefined ->
    (match y with
     | Valid -> false
     | Undefined -> true)

type fp_operand =
| FPS_op of int3
| FPM16_op of address
| FPM32_op of address
| FPM64_op of address
| FPM80_op of address

(** val fp_operand_rect :
    (int3 -> 'a1) -> (address -> 'a1) -> (address -> 'a1) -> (address -> 'a1)
    -> (address -> 'a1) -> fp_operand -> 'a1 **)

let fp_operand_rect f f0 f1 f2 f3 = function
| FPS_op x -> f x
| FPM16_op x -> f0 x
| FPM32_op x -> f1 x
| FPM64_op x -> f2 x
| FPM80_op x -> f3 x

(** val fp_operand_rec :
    (int3 -> 'a1) -> (address -> 'a1) -> (address -> 'a1) -> (address -> 'a1)
    -> (address -> 'a1) -> fp_operand -> 'a1 **)

let fp_operand_rec f f0 f1 f2 f3 = function
| FPS_op x -> f x
| FPM16_op x -> f0 x
| FPM32_op x -> f1 x
| FPM64_op x -> f2 x
| FPM80_op x -> f3 x

type fp_condition_type =
| B_fct
| E_fct
| BE_fct
| U_fct
| NB_fct
| NE_fct
| NBE_fct
| NU_fct

(** val fp_condition_type_rect :
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    fp_condition_type
    ->
    'a1 **)

let fp_condition_type_rect f f0 f1 f2 f3 f4 f5 f6 = function
| B_fct ->
  f
| E_fct ->
  f0
| BE_fct ->
  f1
| U_fct ->
  f2
| NB_fct ->
  f3
| NE_fct ->
  f4
| NBE_fct ->
  f5
| NU_fct ->
  f6

(** val fp_condition_type_rec :
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    fp_condition_type
    ->
    'a1 **)

let fp_condition_type_rec f f0 f1 f2 f3 f4 f5 f6 = function
| B_fct ->
  f
| E_fct ->
  f0
| BE_fct ->
  f1
| U_fct ->
  f2
| NB_fct ->
  f3
| NE_fct ->
  f4
| NBE_fct ->
  f5
| NU_fct ->
  f6

(** val coq_Z_to_fp_condition_type :
    Big.big_int
    ->
    fp_condition_type **)

let coq_Z_to_fp_condition_type n =
  Big.z_case
    (fun _ ->
    B_fct)
    (fun p ->
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        NU_fct)
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          NU_fct)
          (fun p2 ->
          NU_fct)
          (fun _ ->
          NE_fct)
          p1)
        (fun _ ->
        U_fct)
        p0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          NU_fct)
          (fun p2 ->
          NU_fct)
          (fun _ ->
          NBE_fct)
          p1)
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          NU_fct)
          (fun p2 ->
          NU_fct)
          (fun _ ->
          NB_fct)
          p1)
        (fun _ ->
        BE_fct)
        p0)
      (fun _ ->
      E_fct)
      p)
    (fun p ->
    NU_fct)
    n

type mmx_register
  =
  fpu_register

(** val coq_Z_to_mmx_register :
    Big.big_int
    ->
    fpu_register **)

let coq_Z_to_mmx_register n =
  Big.z_case
    (fun _ ->
    ST0)
    (fun p ->
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        ST7)
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          ST7)
          (fun p2 ->
          ST7)
          (fun _ ->
          ST5)
          p1)
        (fun _ ->
        ST3)
        p0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          ST7)
          (fun p2 ->
          ST7)
          (fun _ ->
          ST6)
          p1)
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          ST7)
          (fun p2 ->
          ST7)
          (fun _ ->
          ST4)
          p1)
        (fun _ ->
        ST2)
        p0)
      (fun _ ->
      ST1)
      p)
    (fun p ->
    ST7)
    n

type mmx_granularity =
| MMX_8
| MMX_16
| MMX_32
| MMX_64

(** val mmx_granularity_rect :
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    mmx_granularity
    ->
    'a1 **)

let mmx_granularity_rect f f0 f1 f2 = function
| MMX_8 ->
  f
| MMX_16 ->
  f0
| MMX_32 ->
  f1
| MMX_64 ->
  f2

(** val mmx_granularity_rec :
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    mmx_granularity
    ->
    'a1 **)

let mmx_granularity_rec f f0 f1 f2 = function
| MMX_8 ->
  f
| MMX_16 ->
  f0
| MMX_32 ->
  f1
| MMX_64 ->
  f2

type mmx_operand =
| GP_Reg_op of register
| MMX_Addr_op of address
| MMX_Reg_op of mmx_register
| MMX_Imm_op of int32

(** val mmx_operand_rect :
    (register
    ->
    'a1)
    ->
    (address
    ->
    'a1)
    ->
    (mmx_register
    ->
    'a1)
    ->
    (int32
    ->
    'a1)
    ->
    mmx_operand
    ->
    'a1 **)

let mmx_operand_rect f f0 f1 f2 = function
| GP_Reg_op x ->
  f
    x
| MMX_Addr_op x ->
  f0
    x
| MMX_Reg_op x ->
  f1
    x
| MMX_Imm_op x ->
  f2
    x

(** val mmx_operand_rec :
    (register
    ->
    'a1)
    ->
    (address
    ->
    'a1)
    ->
    (mmx_register
    ->
    'a1)
    ->
    (int32
    ->
    'a1)
    ->
    mmx_operand
    ->
    'a1 **)

let mmx_operand_rec f f0 f1 f2 = function
| GP_Reg_op x ->
  f
    x
| MMX_Addr_op x ->
  f0
    x
| MMX_Reg_op x ->
  f1
    x
| MMX_Imm_op x ->
  f2
    x

type sse_register =
| XMM0
| XMM1
| XMM2
| XMM3
| XMM4
| XMM5
| XMM6
| XMM7

(** val sse_register_rect :
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    sse_register
    ->
    'a1 **)

let sse_register_rect f f0 f1 f2 f3 f4 f5 f6 = function
| XMM0 ->
  f
| XMM1 ->
  f0
| XMM2 ->
  f1
| XMM3 ->
  f2
| XMM4 ->
  f3
| XMM5 ->
  f4
| XMM6 ->
  f5
| XMM7 ->
  f6

(** val sse_register_rec :
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    sse_register
    ->
    'a1 **)

let sse_register_rec f f0 f1 f2 f3 f4 f5 f6 = function
| XMM0 ->
  f
| XMM1 ->
  f0
| XMM2 ->
  f1
| XMM3 ->
  f2
| XMM4 ->
  f3
| XMM5 ->
  f4
| XMM6 ->
  f5
| XMM7 ->
  f6

(** val sse_register_eq_dec :
    sse_register
    ->
    sse_register
    ->
    bool **)

let sse_register_eq_dec x y =
  match x with
  | XMM0 ->
    (match y with
     | XMM0 ->
       true
     | _ ->
       false)
  | XMM1 ->
    (match y with
     | XMM1 ->
       true
     | _ ->
       false)
  | XMM2 ->
    (match y with
     | XMM2 ->
       true
     | _ ->
       false)
  | XMM3 ->
    (match y with
     | XMM3 ->
       true
     | _ ->
       false)
  | XMM4 ->
    (match y with
     | XMM4 ->
       true
     | _ ->
       false)
  | XMM5 ->
    (match y with
     | XMM5 ->
       true
     | _ ->
       false)
  | XMM6 ->
    (match y with
     | XMM6 ->
       true
     | _ ->
       false)
  | XMM7 ->
    (match y with
     | XMM7 ->
       true
     | _ ->
       false)

(** val coq_Z_to_sse_register :
    Big.big_int
    ->
    sse_register **)

let coq_Z_to_sse_register n =
  Big.z_case
    (fun _ ->
    XMM0)
    (fun p ->
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        XMM7)
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          XMM7)
          (fun p2 ->
          XMM7)
          (fun _ ->
          XMM5)
          p1)
        (fun _ ->
        XMM3)
        p0)
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          XMM7)
          (fun p2 ->
          XMM7)
          (fun _ ->
          XMM6)
          p1)
        (fun p1 ->
        Big.positive_case
          (fun p2 ->
          XMM7)
          (fun p2 ->
          XMM7)
          (fun _ ->
          XMM4)
          p1)
        (fun _ ->
        XMM2)
        p0)
      (fun _ ->
      XMM1)
      p)
    (fun p ->
    XMM7)
    n

type mxcsr =
| FZ
| Rpos
| Rneg
| RZ
| RN
| PM
| UM
| OM
| ZM
| DM
| IM
| DAZ
| PE
| UE
| OE
| ZE
| DE
| IE

(** val mxcsr_rect :
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    mxcsr
    ->
    'a1 **)

let mxcsr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 = function
| FZ ->
  f
| Rpos ->
  f0
| Rneg ->
  f1
| RZ ->
  f2
| RN ->
  f3
| PM ->
  f4
| UM ->
  f5
| OM ->
  f6
| ZM ->
  f7
| DM ->
  f8
| IM ->
  f9
| DAZ ->
  f10
| PE ->
  f11
| UE ->
  f12
| OE ->
  f13
| ZE ->
  f14
| DE ->
  f15
| IE ->
  f16

(** val mxcsr_rec :
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    mxcsr
    ->
    'a1 **)

let mxcsr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 = function
| FZ ->
  f
| Rpos ->
  f0
| Rneg ->
  f1
| RZ ->
  f2
| RN ->
  f3
| PM ->
  f4
| UM ->
  f5
| OM ->
  f6
| ZM ->
  f7
| DM ->
  f8
| IM ->
  f9
| DAZ ->
  f10
| PE ->
  f11
| UE ->
  f12
| OE ->
  f13
| ZE ->
  f14
| DE ->
  f15
| IE ->
  f16

(** val mxcsr_eq_dec :
    mxcsr
    ->
    mxcsr
    ->
    bool **)

let mxcsr_eq_dec x y =
  match x with
  | FZ ->
    (match y with
     | FZ ->
       true
     | _ ->
       false)
  | Rpos ->
    (match y with
     | Rpos ->
       true
     | _ ->
       false)
  | Rneg ->
    (match y with
     | Rneg ->
       true
     | _ ->
       false)
  | RZ ->
    (match y with
     | RZ ->
       true
     | _ ->
       false)
  | RN ->
    (match y with
     | RN ->
       true
     | _ ->
       false)
  | PM ->
    (match y with
     | PM ->
       true
     | _ ->
       false)
  | UM ->
    (match y with
     | UM ->
       true
     | _ ->
       false)
  | OM ->
    (match y with
     | OM ->
       true
     | _ ->
       false)
  | ZM ->
    (match y with
     | ZM ->
       true
     | _ ->
       false)
  | DM ->
    (match y with
     | DM ->
       true
     | _ ->
       false)
  | IM ->
    (match y with
     | IM ->
       true
     | _ ->
       false)
  | DAZ ->
    (match y with
     | DAZ ->
       true
     | _ ->
       false)
  | PE ->
    (match y with
     | PE ->
       true
     | _ ->
       false)
  | UE ->
    (match y with
     | UE ->
       true
     | _ ->
       false)
  | OE ->
    (match y with
     | OE ->
       true
     | _ ->
       false)
  | ZE ->
    (match y with
     | ZE ->
       true
     | _ ->
       false)
  | DE ->
    (match y with
     | DE ->
       true
     | _ ->
       false)
  | IE ->
    (match y with
     | IE ->
       true
     | _ ->
       false)

type sse_operand =
| SSE_XMM_Reg_op of sse_register
| SSE_MM_Reg_op of mmx_register
| SSE_Addr_op of address
| SSE_GP_Reg_op of register
| SSE_Imm_op of int32

(** val sse_operand_rect :
    (sse_register
    ->
    'a1)
    ->
    (mmx_register
    ->
    'a1)
    ->
    (address
    ->
    'a1)
    ->
    (register
    ->
    'a1)
    ->
    (int32
    ->
    'a1)
    ->
    sse_operand
    ->
    'a1 **)

let sse_operand_rect f f0 f1 f2 f3 = function
| SSE_XMM_Reg_op x ->
  f
    x
| SSE_MM_Reg_op x ->
  f0
    x
| SSE_Addr_op x ->
  f1
    x
| SSE_GP_Reg_op x ->
  f2
    x
| SSE_Imm_op x ->
  f3
    x

(** val sse_operand_rec :
    (sse_register
    ->
    'a1)
    ->
    (mmx_register
    ->
    'a1)
    ->
    (address
    ->
    'a1)
    ->
    (register
    ->
    'a1)
    ->
    (int32
    ->
    'a1)
    ->
    sse_operand
    ->
    'a1 **)

let sse_operand_rec f f0 f1 f2 f3 = function
| SSE_XMM_Reg_op x ->
  f
    x
| SSE_MM_Reg_op x ->
  f0
    x
| SSE_Addr_op x ->
  f1
    x
| SSE_GP_Reg_op x ->
  f2
    x
| SSE_Imm_op x ->
  f3
    x

type instr =
| AAA
| AAD
| AAM
| AAS
| ADC of bool
   * operand
   * operand
| ADD of bool
   * operand
   * operand
| AND of bool
   * operand
   * operand
| ARPL of operand
   * operand
| BOUND of operand
   * operand
| BSF of operand
   * operand
| BSR of operand
   * operand
| BSWAP of register
| BT of operand
   * operand
| BTC of operand
   * operand
| BTR of operand
   * operand
| BTS of operand
   * operand
| CALL of bool
   * bool
   * operand
   * selector
     option
| CDQ
| CLC
| CLD
| CLI
| CLTS
| CMC
| CMOVcc of condition_type
   * operand
   * operand
| CMP of bool
   * operand
   * operand
| CMPS of bool
| CMPXCHG of bool
   * operand
   * operand
| CPUID
| CWDE
| DAA
| DAS
| DEC of bool
   * operand
| DIV of bool
   * operand
| F2XM1
| FABS
| FADD of bool
   * fp_operand
| FADDP of fp_operand
| FBLD of fp_operand
| FBSTP of fp_operand
| FCHS
| FCLEX
| FCMOVcc of fp_condition_type
   * fp_operand
| FCOM of fp_operand
          option
| FCOMP of fp_operand
           option
| FCOMPP
| FCOMIP of fp_operand
| FCOS
| FDECSTP
| FDIV of fp_operand
   * fp_operand
| FDIVP of fp_operand
| FDIVR of fp_operand
   * fp_operand
| FDIVRP of fp_operand
| FFREE of fp_operand
| FIADD of fp_operand
| FICOM of fp_operand
| FICOMP of fp_operand
| FIDIV of fp_operand
| FIDIVR of fp_operand
| FILD of fp_operand
| FIMUL of fp_operand
| FINCSTP
| FINIT
| FIST of fp_operand
| FISTP of fp_operand
| FISUB of fp_operand
| FISUBR of fp_operand
| FLD of fp_operand
| FLD1
| FLDCW of fp_operand
| FLDENV of fp_operand
| FLDL2E
| FLDL2T
| FLDLG2
| FLDLN2
| FLDPI
| FLDZ
| FMUL of bool
   * fp_operand
| FMULP of fp_operand
| FNOP
| FNSAVE of fp_operand
| FNSTCW of fp_operand
| FNSTSW of fp_operand
            option
| FPATAN
| FPREM
| FPREM1
| FPTAN
| FRNDINT
| FRSTOR of fp_operand
| FSCALE
| FSIN
| FSINCOS
| FSQRT
| FST of fp_operand
| FSTENV of fp_operand
| FSTP of fp_operand
| FSUB of fp_operand
   * fp_operand
| FSUBP of fp_operand
| FSUBR of fp_operand
   * fp_operand
| FSUBRP of fp_operand
| FTST
| FUCOM of fp_operand
| FUCOMP of fp_operand
| FUCOMPP
| FUCOMI of fp_operand
| FUCOMIP of fp_operand
| FXAM
| FXCH of fp_operand
| FXTRACT
| FYL2X
| FYL2XP1
| FWAIT
| EMMS
| MOVD of mmx_operand
   * mmx_operand
| MOVQ of mmx_operand
   * mmx_operand
| PACKSSDW of mmx_operand
   * mmx_operand
| PACKSSWB of mmx_operand
   * mmx_operand
| PACKUSWB of mmx_operand
   * mmx_operand
| PADD of mmx_granularity
   * mmx_operand
   * mmx_operand
| PADDS of mmx_granularity
   * mmx_operand
   * mmx_operand
| PADDUS of mmx_granularity
   * mmx_operand
   * mmx_operand
| PAND of mmx_operand
   * mmx_operand
| PANDN of mmx_operand
   * mmx_operand
| PCMPEQ of mmx_granularity
   * mmx_operand
   * mmx_operand
| PCMPGT of mmx_granularity
   * mmx_operand
   * mmx_operand
| PMADDWD of mmx_operand
   * mmx_operand
| PMULHUW of mmx_operand
   * mmx_operand
| PMULHW of mmx_operand
   * mmx_operand
| PMULLW of mmx_operand
   * mmx_operand
| POR of mmx_operand
   * mmx_operand
| PSLL of mmx_granularity
   * mmx_operand
   * mmx_operand
| PSRA of mmx_granularity
   * mmx_operand
   * mmx_operand
| PSRL of mmx_granularity
   * mmx_operand
   * mmx_operand
| PSUB of mmx_granularity
   * mmx_operand
   * mmx_operand
| PSUBS of mmx_granularity
   * mmx_operand
   * mmx_operand
| PSUBUS of mmx_granularity
   * mmx_operand
   * mmx_operand
| PUNPCKH of mmx_granularity
   * mmx_operand
   * mmx_operand
| PUNPCKL of mmx_granularity
   * mmx_operand
   * mmx_operand
| PXOR of mmx_operand
   * mmx_operand
| ADDPS of sse_operand
   * sse_operand
| ADDSS of sse_operand
   * sse_operand
| ANDNPS of sse_operand
   * sse_operand
| ANDPS of sse_operand
   * sse_operand
| CMPPS of sse_operand
   * sse_operand
   * sse_operand
| CMPSS of sse_operand
   * sse_operand
   * sse_operand
| COMISS of sse_operand
   * sse_operand
| CVTPI2PS of sse_operand
   * sse_operand
| CVTPS2PI of sse_operand
   * sse_operand
| CVTSI2SS of sse_operand
   * sse_operand
| CVTSS2SI of sse_operand
   * sse_operand
| CVTTPS2PI of sse_operand
   * sse_operand
| CVTTSS2SI of sse_operand
   * sse_operand
| DIVPS of sse_operand
   * sse_operand
| DIVSS of sse_operand
   * sse_operand
| LDMXCSR of sse_operand
| MAXPS of sse_operand
   * sse_operand
| MAXSS of sse_operand
   * sse_operand
| MINPS of sse_operand
   * sse_operand
| MINSS of sse_operand
   * sse_operand
| MOVAPS of sse_operand
   * sse_operand
| MOVHLPS of sse_operand
   * sse_operand
| MOVHPS of sse_operand
   * sse_operand
| MOVLHPS of sse_operand
   * sse_operand
| MOVLPS of sse_operand
   * sse_operand
| MOVMSKPS of sse_operand
   * sse_operand
| MOVSS of sse_operand
   * sse_operand
| MOVUPS of sse_operand
   * sse_operand
| MULPS of sse_operand
   * sse_operand
| MULSS of sse_operand
   * sse_operand
| ORPS of sse_operand
   * sse_operand
| RCPPS of sse_operand
   * sse_operand
| RCPSS of sse_operand
   * sse_operand
| RSQRTPS of sse_operand
   * sse_operand
| RSQRTSS of sse_operand
   * sse_operand
| SHUFPS of sse_operand
   * sse_operand
   * sse_operand
| SQRTPS of sse_operand
   * sse_operand
| SQRTSS of sse_operand
   * sse_operand
| STMXCSR of sse_operand
| SUBPS of sse_operand
   * sse_operand
| SUBSS of sse_operand
   * sse_operand
| UCOMISS of sse_operand
   * sse_operand
| UNPCKHPS of sse_operand
   * sse_operand
| UNPCKLPS of sse_operand
   * sse_operand
| XORPS of sse_operand
   * sse_operand
| PAVGB of sse_operand
   * sse_operand
| PEXTRW of sse_operand
   * sse_operand
   * sse_operand
| PINSRW of sse_operand
   * sse_operand
   * sse_operand
| PMAXSW of sse_operand
   * sse_operand
| PMAXUB of sse_operand
   * sse_operand
| PMINSW of sse_operand
   * sse_operand
| PMINUB of sse_operand
   * sse_operand
| PMOVMSKB of sse_operand
   * sse_operand
| PSADBW of sse_operand
   * sse_operand
| PSHUFW of sse_operand
   * sse_operand
   * sse_operand
| MASKMOVQ of sse_operand
   * sse_operand
| MOVNTPS of sse_operand
   * sse_operand
| MOVNTQ of sse_operand
   * sse_operand
| PREFETCHT0 of sse_operand
| PREFETCHT1 of sse_operand
| PREFETCHT2 of sse_operand
| PREFETCHNTA of sse_operand
| SFENCE
| HLT
| IDIV of bool
   * operand
| IMUL of bool
   * operand
   * operand
     option
   * int32
     option
| IN of bool
   * port_number
     option
| INC of bool
   * operand
| INS of bool
| INTn of interrupt_type
| INT
| INTO
| INVD
| INVLPG of operand
| IRET
| Jcc of condition_type
   * int32
| JCXZ of int8
| JMP of bool
   * bool
   * operand
   * selector
     option
| LAHF
| LAR of operand
   * operand
| LDS of operand
   * operand
| LEA of operand
   * operand
| LEAVE
| LES of operand
   * operand
| LFS of operand
   * operand
| LGDT of operand
| LGS of operand
   * operand
| LIDT of operand
| LLDT of operand
| LMSW of operand
| LODS of bool
| LOOP of int8
| LOOPZ of int8
| LOOPNZ of int8
| LSL of operand
   * operand
| LSS of operand
   * operand
| LTR of operand
| MOV of bool
   * operand
   * operand
| MOVCR of bool
   * control_register
   * register
| MOVDR of bool
   * debug_register
   * register
| MOVSR of bool
   * segment_register
   * operand
| MOVBE of operand
   * operand
| MOVS of bool
| MOVSX of bool
   * operand
   * operand
| MOVZX of bool
   * operand
   * operand
| MUL of bool
   * operand
| NEG of bool
   * operand
| NOP of operand
| NOT of bool
   * operand
| OR of bool
   * operand
   * operand
| OUT of bool
   * port_number
     option
| OUTS of bool
| POP of operand
| POPSR of segment_register
| POPA
| POPF
| PUSH of bool
   * operand
| PUSHSR of segment_register
| PUSHA
| PUSHF
| RCL of bool
   * operand
   * reg_or_immed
| RCR of bool
   * operand
   * reg_or_immed
| RDMSR
| RDPMC
| RDTSC
| RDTSCP
| RET of bool
   * int16
     option
| ROL of bool
   * operand
   * reg_or_immed
| ROR of bool
   * operand
   * reg_or_immed
| RSM
| SAHF
| SAR of bool
   * operand
   * reg_or_immed
| SBB of bool
   * operand
   * operand
| SCAS of bool
| SETcc of condition_type
   * operand
| SGDT of operand
| SHL of bool
   * operand
   * reg_or_immed
| SHLD of operand
   * register
   * reg_or_immed
| SHR of bool
   * operand
   * reg_or_immed
| SHRD of operand
   * register
   * reg_or_immed
| SIDT of operand
| SLDT of operand
| SMSW of operand
| STC
| STD
| STI
| STOS of bool
| STR of operand
| SUB of bool
   * operand
   * operand
| TEST of bool
   * operand
   * operand
| UD2
| VERR of operand
| VERW of operand
| WBINVD
| WRMSR
| XADD of bool
   * operand
   * operand
| XCHG of bool
   * operand
   * operand
| XLAT
| XOR of bool
   * operand
   * operand

(** val instr_rect :
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (register
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    bool
    ->
    operand
    ->
    selector
    option
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (condition_type
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (fp_condition_type
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    option
    ->
    'a1)
    ->
    (fp_operand
    option
    ->
    'a1)
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (fp_operand
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    option
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    option
    ->
    int32
    option
    ->
    'a1)
    ->
    (bool
    ->
    port_number
    option
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    'a1)
    ->
    (interrupt_type
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (operand
    ->
    'a1)
    ->
    'a1
    ->
    (condition_type
    ->
    int32
    ->
    'a1)
    ->
    (int8
    ->
    'a1)
    ->
    (bool
    ->
    bool
    ->
    operand
    ->
    selector
    option
    ->
    'a1)
    ->
    'a1
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    'a1
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (bool
    ->
    'a1)
    ->
    (int8
    ->
    'a1)
    ->
    (int8
    ->
    'a1)
    ->
    (int8
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    control_register
    ->
    register
    ->
    'a1)
    ->
    (bool
    ->
    debug_register
    ->
    register
    ->
    'a1)
    ->
    (bool
    ->
    segment_register
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (operand
    option
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    port_number
    option
    ->
    'a1)
    ->
    (bool
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (segment_register
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (segment_register
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    int16
    option
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    'a1)
    ->
    (condition_type
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (operand
    ->
    register
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (operand
    ->
    register
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    'a1
    ->
    (operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    instr
    ->
    'a1 **)

let instr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 f158 f159 f160 f161 f162 f163 f164 f165 f166 f167 f168 f169 f170 f171 f172 f173 f174 f175 f176 f177 f178 f179 f180 f181 f182 f183 f184 f185 f186 f187 f188 f189 f190 f191 f192 f193 f194 f195 f196 f197 f198 f199 f200 f201 f202 f203 f204 f205 f206 f207 f208 f209 f210 f211 f212 f213 f214 f215 f216 f217 f218 f219 f220 f221 f222 f223 f224 f225 f226 f227 f228 f229 f230 f231 f232 f233 f234 f235 f236 f237 f238 f239 f240 f241 f242 f243 f244 f245 f246 f247 f248 f249 f250 f251 f252 f253 f254 f255 f256 f257 f258 f259 f260 f261 f262 f263 f264 f265 f266 f267 f268 f269 f270 f271 f272 f273 f274 f275 f276 f277 f278 f279 f280 f281 f282 f283 f284 f285 f286 f287 f288 f289 f290 f291 f292 f293 f294 f295 = function
| AAA ->
  f
| AAD ->
  f0
| AAM ->
  f1
| AAS ->
  f2
| ADC (x,
       x0,
       x1) ->
  f3
    x
    x0
    x1
| ADD (x,
       x0,
       x1) ->
  f4
    x
    x0
    x1
| AND (x,
       x0,
       x1) ->
  f5
    x
    x0
    x1
| ARPL (x,
        x0) ->
  f6
    x
    x0
| BOUND (x,
         x0) ->
  f7
    x
    x0
| BSF (x,
       x0) ->
  f8
    x
    x0
| BSR (x,
       x0) ->
  f9
    x
    x0
| BSWAP x ->
  f10
    x
| BT (x,
      x0) ->
  f11
    x
    x0
| BTC (x,
       x0) ->
  f12
    x
    x0
| BTR (x,
       x0) ->
  f13
    x
    x0
| BTS (x,
       x0) ->
  f14
    x
    x0
| CALL (x,
        x0,
        x1,
        x2) ->
  f15
    x
    x0
    x1
    x2
| CDQ ->
  f16
| CLC ->
  f17
| CLD ->
  f18
| CLI ->
  f19
| CLTS ->
  f20
| CMC ->
  f21
| CMOVcc (x,
          x0,
          x1) ->
  f22
    x
    x0
    x1
| CMP (x,
       x0,
       x1) ->
  f23
    x
    x0
    x1
| CMPS x ->
  f24
    x
| CMPXCHG (x,
           x0,
           x1) ->
  f25
    x
    x0
    x1
| CPUID ->
  f26
| CWDE ->
  f27
| DAA ->
  f28
| DAS ->
  f29
| DEC (x,
       x0) ->
  f30
    x
    x0
| DIV (x,
       x0) ->
  f31
    x
    x0
| F2XM1 ->
  f32
| FABS ->
  f33
| FADD (x,
        x0) ->
  f34
    x
    x0
| FADDP x ->
  f35
    x
| FBLD x ->
  f36
    x
| FBSTP x ->
  f37
    x
| FCHS ->
  f38
| FCLEX ->
  f39
| FCMOVcc (x,
           x0) ->
  f40
    x
    x0
| FCOM x ->
  f41
    x
| FCOMP x ->
  f42
    x
| FCOMPP ->
  f43
| FCOMIP x ->
  f44
    x
| FCOS ->
  f45
| FDECSTP ->
  f46
| FDIV (x,
        x0) ->
  f47
    x
    x0
| FDIVP x ->
  f48
    x
| FDIVR (x,
         x0) ->
  f49
    x
    x0
| FDIVRP x ->
  f50
    x
| FFREE x ->
  f51
    x
| FIADD x ->
  f52
    x
| FICOM x ->
  f53
    x
| FICOMP x ->
  f54
    x
| FIDIV x ->
  f55
    x
| FIDIVR x ->
  f56
    x
| FILD x ->
  f57
    x
| FIMUL x ->
  f58
    x
| FINCSTP ->
  f59
| FINIT ->
  f60
| FIST x ->
  f61
    x
| FISTP x ->
  f62
    x
| FISUB x ->
  f63
    x
| FISUBR x ->
  f64
    x
| FLD x ->
  f65
    x
| FLD1 ->
  f66
| FLDCW x ->
  f67
    x
| FLDENV x ->
  f68
    x
| FLDL2E ->
  f69
| FLDL2T ->
  f70
| FLDLG2 ->
  f71
| FLDLN2 ->
  f72
| FLDPI ->
  f73
| FLDZ ->
  f74
| FMUL (x,
        x0) ->
  f75
    x
    x0
| FMULP x ->
  f76
    x
| FNOP ->
  f77
| FNSAVE x ->
  f78
    x
| FNSTCW x ->
  f79
    x
| FNSTSW x ->
  f80
    x
| FPATAN ->
  f81
| FPREM ->
  f82
| FPREM1 ->
  f83
| FPTAN ->
  f84
| FRNDINT ->
  f85
| FRSTOR x ->
  f86
    x
| FSCALE ->
  f87
| FSIN ->
  f88
| FSINCOS ->
  f89
| FSQRT ->
  f90
| FST x ->
  f91
    x
| FSTENV x ->
  f92
    x
| FSTP x ->
  f93
    x
| FSUB (x,
        x0) ->
  f94
    x
    x0
| FSUBP x ->
  f95
    x
| FSUBR (x,
         x0) ->
  f96
    x
    x0
| FSUBRP x ->
  f97
    x
| FTST ->
  f98
| FUCOM x ->
  f99
    x
| FUCOMP x ->
  f100
    x
| FUCOMPP ->
  f101
| FUCOMI x ->
  f102
    x
| FUCOMIP x ->
  f103
    x
| FXAM ->
  f104
| FXCH x ->
  f105
    x
| FXTRACT ->
  f106
| FYL2X ->
  f107
| FYL2XP1 ->
  f108
| FWAIT ->
  f109
| EMMS ->
  f110
| MOVD (x,
        x0) ->
  f111
    x
    x0
| MOVQ (x,
        x0) ->
  f112
    x
    x0
| PACKSSDW (x,
            x0) ->
  f113
    x
    x0
| PACKSSWB (x,
            x0) ->
  f114
    x
    x0
| PACKUSWB (x,
            x0) ->
  f115
    x
    x0
| PADD (x,
        x0,
        x1) ->
  f116
    x
    x0
    x1
| PADDS (x,
         x0,
         x1) ->
  f117
    x
    x0
    x1
| PADDUS (x,
          x0,
          x1) ->
  f118
    x
    x0
    x1
| PAND (x,
        x0) ->
  f119
    x
    x0
| PANDN (x,
         x0) ->
  f120
    x
    x0
| PCMPEQ (x,
          x0,
          x1) ->
  f121
    x
    x0
    x1
| PCMPGT (x,
          x0,
          x1) ->
  f122
    x
    x0
    x1
| PMADDWD (x,
           x0) ->
  f123
    x
    x0
| PMULHUW (x,
           x0) ->
  f124
    x
    x0
| PMULHW (x,
          x0) ->
  f125
    x
    x0
| PMULLW (x,
          x0) ->
  f126
    x
    x0
| POR (x,
       x0) ->
  f127
    x
    x0
| PSLL (x,
        x0,
        x1) ->
  f128
    x
    x0
    x1
| PSRA (x,
        x0,
        x1) ->
  f129
    x
    x0
    x1
| PSRL (x,
        x0,
        x1) ->
  f130
    x
    x0
    x1
| PSUB (x,
        x0,
        x1) ->
  f131
    x
    x0
    x1
| PSUBS (x,
         x0,
         x1) ->
  f132
    x
    x0
    x1
| PSUBUS (x,
          x0,
          x1) ->
  f133
    x
    x0
    x1
| PUNPCKH (x,
           x0,
           x1) ->
  f134
    x
    x0
    x1
| PUNPCKL (x,
           x0,
           x1) ->
  f135
    x
    x0
    x1
| PXOR (x,
        x0) ->
  f136
    x
    x0
| ADDPS (x,
         x0) ->
  f137
    x
    x0
| ADDSS (x,
         x0) ->
  f138
    x
    x0
| ANDNPS (x,
          x0) ->
  f139
    x
    x0
| ANDPS (x,
         x0) ->
  f140
    x
    x0
| CMPPS (x,
         x0,
         x1) ->
  f141
    x
    x0
    x1
| CMPSS (x,
         x0,
         x1) ->
  f142
    x
    x0
    x1
| COMISS (x,
          x0) ->
  f143
    x
    x0
| CVTPI2PS (x,
            x0) ->
  f144
    x
    x0
| CVTPS2PI (x,
            x0) ->
  f145
    x
    x0
| CVTSI2SS (x,
            x0) ->
  f146
    x
    x0
| CVTSS2SI (x,
            x0) ->
  f147
    x
    x0
| CVTTPS2PI (x,
             x0) ->
  f148
    x
    x0
| CVTTSS2SI (x,
             x0) ->
  f149
    x
    x0
| DIVPS (x,
         x0) ->
  f150
    x
    x0
| DIVSS (x,
         x0) ->
  f151
    x
    x0
| LDMXCSR x ->
  f152
    x
| MAXPS (x,
         x0) ->
  f153
    x
    x0
| MAXSS (x,
         x0) ->
  f154
    x
    x0
| MINPS (x,
         x0) ->
  f155
    x
    x0
| MINSS (x,
         x0) ->
  f156
    x
    x0
| MOVAPS (x,
          x0) ->
  f157
    x
    x0
| MOVHLPS (x,
           x0) ->
  f158
    x
    x0
| MOVHPS (x,
          x0) ->
  f159
    x
    x0
| MOVLHPS (x,
           x0) ->
  f160
    x
    x0
| MOVLPS (x,
          x0) ->
  f161
    x
    x0
| MOVMSKPS (x,
            x0) ->
  f162
    x
    x0
| MOVSS (x,
         x0) ->
  f163
    x
    x0
| MOVUPS (x,
          x0) ->
  f164
    x
    x0
| MULPS (x,
         x0) ->
  f165
    x
    x0
| MULSS (x,
         x0) ->
  f166
    x
    x0
| ORPS (x,
        x0) ->
  f167
    x
    x0
| RCPPS (x,
         x0) ->
  f168
    x
    x0
| RCPSS (x,
         x0) ->
  f169
    x
    x0
| RSQRTPS (x,
           x0) ->
  f170
    x
    x0
| RSQRTSS (x,
           x0) ->
  f171
    x
    x0
| SHUFPS (x,
          x0,
          x1) ->
  f172
    x
    x0
    x1
| SQRTPS (x,
          x0) ->
  f173
    x
    x0
| SQRTSS (x,
          x0) ->
  f174
    x
    x0
| STMXCSR x ->
  f175
    x
| SUBPS (x,
         x0) ->
  f176
    x
    x0
| SUBSS (x,
         x0) ->
  f177
    x
    x0
| UCOMISS (x,
           x0) ->
  f178
    x
    x0
| UNPCKHPS (x,
            x0) ->
  f179
    x
    x0
| UNPCKLPS (x,
            x0) ->
  f180
    x
    x0
| XORPS (x,
         x0) ->
  f181
    x
    x0
| PAVGB (x,
         x0) ->
  f182
    x
    x0
| PEXTRW (x,
          x0,
          x1) ->
  f183
    x
    x0
    x1
| PINSRW (x,
          x0,
          x1) ->
  f184
    x
    x0
    x1
| PMAXSW (x,
          x0) ->
  f185
    x
    x0
| PMAXUB (x,
          x0) ->
  f186
    x
    x0
| PMINSW (x,
          x0) ->
  f187
    x
    x0
| PMINUB (x,
          x0) ->
  f188
    x
    x0
| PMOVMSKB (x,
            x0) ->
  f189
    x
    x0
| PSADBW (x,
          x0) ->
  f190
    x
    x0
| PSHUFW (x,
          x0,
          x1) ->
  f191
    x
    x0
    x1
| MASKMOVQ (x,
            x0) ->
  f192
    x
    x0
| MOVNTPS (x,
           x0) ->
  f193
    x
    x0
| MOVNTQ (x,
          x0) ->
  f194
    x
    x0
| PREFETCHT0 x ->
  f195
    x
| PREFETCHT1 x ->
  f196
    x
| PREFETCHT2 x ->
  f197
    x
| PREFETCHNTA x ->
  f198
    x
| SFENCE ->
  f199
| HLT ->
  f200
| IDIV (x,
        x0) ->
  f201
    x
    x0
| IMUL (x,
        x0,
        x1,
        x2) ->
  f202
    x
    x0
    x1
    x2
| IN (x,
      x0) ->
  f203
    x
    x0
| INC (x,
       x0) ->
  f204
    x
    x0
| INS x ->
  f205
    x
| INTn x ->
  f206
    x
| INT ->
  f207
| INTO ->
  f208
| INVD ->
  f209
| INVLPG x ->
  f210
    x
| IRET ->
  f211
| Jcc (x,
       x0) ->
  f212
    x
    x0
| JCXZ x ->
  f213
    x
| JMP (x,
       x0,
       x1,
       x2) ->
  f214
    x
    x0
    x1
    x2
| LAHF ->
  f215
| LAR (x,
       x0) ->
  f216
    x
    x0
| LDS (x,
       x0) ->
  f217
    x
    x0
| LEA (x,
       x0) ->
  f218
    x
    x0
| LEAVE ->
  f219
| LES (x,
       x0) ->
  f220
    x
    x0
| LFS (x,
       x0) ->
  f221
    x
    x0
| LGDT x ->
  f222
    x
| LGS (x,
       x0) ->
  f223
    x
    x0
| LIDT x ->
  f224
    x
| LLDT x ->
  f225
    x
| LMSW x ->
  f226
    x
| LODS x ->
  f227
    x
| LOOP x ->
  f228
    x
| LOOPZ x ->
  f229
    x
| LOOPNZ x ->
  f230
    x
| LSL (x,
       x0) ->
  f231
    x
    x0
| LSS (x,
       x0) ->
  f232
    x
    x0
| LTR x ->
  f233
    x
| MOV (x,
       x0,
       x1) ->
  f234
    x
    x0
    x1
| MOVCR (x,
         x0,
         x1) ->
  f235
    x
    x0
    x1
| MOVDR (x,
         x0,
         x1) ->
  f236
    x
    x0
    x1
| MOVSR (x,
         x0,
         x1) ->
  f237
    x
    x0
    x1
| MOVBE (x,
         x0) ->
  f238
    x
    x0
| MOVS x ->
  f239
    x
| MOVSX (x,
         x0,
         x1) ->
  f240
    x
    x0
    x1
| MOVZX (x,
         x0,
         x1) ->
  f241
    x
    x0
    x1
| MUL (x,
       x0) ->
  f242
    x
    x0
| NEG (x,
       x0) ->
  f243
    x
    x0
| NOP x ->
  f244
    x
| NOT (x,
       x0) ->
  f245
    x
    x0
| OR (x,
      x0,
      x1) ->
  f246
    x
    x0
    x1
| OUT (x,
       x0) ->
  f247
    x
    x0
| OUTS x ->
  f248
    x
| POP x ->
  f249
    x
| POPSR x ->
  f250
    x
| POPA ->
  f251
| POPF ->
  f252
| PUSH (x,
        x0) ->
  f253
    x
    x0
| PUSHSR x ->
  f254
    x
| PUSHA ->
  f255
| PUSHF ->
  f256
| RCL (x,
       x0,
       x1) ->
  f257
    x
    x0
    x1
| RCR (x,
       x0,
       x1) ->
  f258
    x
    x0
    x1
| RDMSR ->
  f259
| RDPMC ->
  f260
| RDTSC ->
  f261
| RDTSCP ->
  f262
| RET (x,
       x0) ->
  f263
    x
    x0
| ROL (x,
       x0,
       x1) ->
  f264
    x
    x0
    x1
| ROR (x,
       x0,
       x1) ->
  f265
    x
    x0
    x1
| RSM ->
  f266
| SAHF ->
  f267
| SAR (x,
       x0,
       x1) ->
  f268
    x
    x0
    x1
| SBB (x,
       x0,
       x1) ->
  f269
    x
    x0
    x1
| SCAS x ->
  f270
    x
| SETcc (x,
         x0) ->
  f271
    x
    x0
| SGDT x ->
  f272
    x
| SHL (x,
       x0,
       x1) ->
  f273
    x
    x0
    x1
| SHLD (x,
        x0,
        x1) ->
  f274
    x
    x0
    x1
| SHR (x,
       x0,
       x1) ->
  f275
    x
    x0
    x1
| SHRD (x,
        x0,
        x1) ->
  f276
    x
    x0
    x1
| SIDT x ->
  f277
    x
| SLDT x ->
  f278
    x
| SMSW x ->
  f279
    x
| STC ->
  f280
| STD ->
  f281
| STI ->
  f282
| STOS x ->
  f283
    x
| STR x ->
  f284
    x
| SUB (x,
       x0,
       x1) ->
  f285
    x
    x0
    x1
| TEST (x,
        x0,
        x1) ->
  f286
    x
    x0
    x1
| UD2 ->
  f287
| VERR x ->
  f288
    x
| VERW x ->
  f289
    x
| WBINVD ->
  f290
| WRMSR ->
  f291
| XADD (x,
        x0,
        x1) ->
  f292
    x
    x0
    x1
| XCHG (x,
        x0,
        x1) ->
  f293
    x
    x0
    x1
| XLAT ->
  f294
| XOR (x,
       x0,
       x1) ->
  f295
    x
    x0
    x1

(** val instr_rec :
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (register
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    bool
    ->
    operand
    ->
    selector
    option
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (condition_type
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (fp_condition_type
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    option
    ->
    'a1)
    ->
    (fp_operand
    option
    ->
    'a1)
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (fp_operand
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    option
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    (fp_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_granularity
    ->
    mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (mmx_operand
    ->
    mmx_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    'a1)
    ->
    (sse_operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    option
    ->
    int32
    option
    ->
    'a1)
    ->
    (bool
    ->
    port_number
    option
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    'a1)
    ->
    (interrupt_type
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (operand
    ->
    'a1)
    ->
    'a1
    ->
    (condition_type
    ->
    int32
    ->
    'a1)
    ->
    (int8
    ->
    'a1)
    ->
    (bool
    ->
    bool
    ->
    operand
    ->
    selector
    option
    ->
    'a1)
    ->
    'a1
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    'a1
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (bool
    ->
    'a1)
    ->
    (int8
    ->
    'a1)
    ->
    (int8
    ->
    'a1)
    ->
    (int8
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    control_register
    ->
    register
    ->
    'a1)
    ->
    (bool
    ->
    debug_register
    ->
    register
    ->
    'a1)
    ->
    (bool
    ->
    segment_register
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (operand
    option
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    port_number
    option
    ->
    'a1)
    ->
    (bool
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (segment_register
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    'a1)
    ->
    (segment_register
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    int16
    option
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    'a1)
    ->
    (condition_type
    ->
    operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (operand
    ->
    register
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (operand
    ->
    register
    ->
    reg_or_immed
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    'a1
    ->
    (operand
    ->
    'a1)
    ->
    (operand
    ->
    'a1)
    ->
    'a1
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    'a1
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    'a1)
    ->
    instr
    ->
    'a1 **)

let instr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 f158 f159 f160 f161 f162 f163 f164 f165 f166 f167 f168 f169 f170 f171 f172 f173 f174 f175 f176 f177 f178 f179 f180 f181 f182 f183 f184 f185 f186 f187 f188 f189 f190 f191 f192 f193 f194 f195 f196 f197 f198 f199 f200 f201 f202 f203 f204 f205 f206 f207 f208 f209 f210 f211 f212 f213 f214 f215 f216 f217 f218 f219 f220 f221 f222 f223 f224 f225 f226 f227 f228 f229 f230 f231 f232 f233 f234 f235 f236 f237 f238 f239 f240 f241 f242 f243 f244 f245 f246 f247 f248 f249 f250 f251 f252 f253 f254 f255 f256 f257 f258 f259 f260 f261 f262 f263 f264 f265 f266 f267 f268 f269 f270 f271 f272 f273 f274 f275 f276 f277 f278 f279 f280 f281 f282 f283 f284 f285 f286 f287 f288 f289 f290 f291 f292 f293 f294 f295 = function
| AAA ->
  f
| AAD ->
  f0
| AAM ->
  f1
| AAS ->
  f2
| ADC (x,
       x0,
       x1) ->
  f3
    x
    x0
    x1
| ADD (x,
       x0,
       x1) ->
  f4
    x
    x0
    x1
| AND (x,
       x0,
       x1) ->
  f5
    x
    x0
    x1
| ARPL (x,
        x0) ->
  f6
    x
    x0
| BOUND (x,
         x0) ->
  f7
    x
    x0
| BSF (x,
       x0) ->
  f8
    x
    x0
| BSR (x,
       x0) ->
  f9
    x
    x0
| BSWAP x ->
  f10
    x
| BT (x,
      x0) ->
  f11
    x
    x0
| BTC (x,
       x0) ->
  f12
    x
    x0
| BTR (x,
       x0) ->
  f13
    x
    x0
| BTS (x,
       x0) ->
  f14
    x
    x0
| CALL (x,
        x0,
        x1,
        x2) ->
  f15
    x
    x0
    x1
    x2
| CDQ ->
  f16
| CLC ->
  f17
| CLD ->
  f18
| CLI ->
  f19
| CLTS ->
  f20
| CMC ->
  f21
| CMOVcc (x,
          x0,
          x1) ->
  f22
    x
    x0
    x1
| CMP (x,
       x0,
       x1) ->
  f23
    x
    x0
    x1
| CMPS x ->
  f24
    x
| CMPXCHG (x,
           x0,
           x1) ->
  f25
    x
    x0
    x1
| CPUID ->
  f26
| CWDE ->
  f27
| DAA ->
  f28
| DAS ->
  f29
| DEC (x,
       x0) ->
  f30
    x
    x0
| DIV (x,
       x0) ->
  f31
    x
    x0
| F2XM1 ->
  f32
| FABS ->
  f33
| FADD (x,
        x0) ->
  f34
    x
    x0
| FADDP x ->
  f35
    x
| FBLD x ->
  f36
    x
| FBSTP x ->
  f37
    x
| FCHS ->
  f38
| FCLEX ->
  f39
| FCMOVcc (x,
           x0) ->
  f40
    x
    x0
| FCOM x ->
  f41
    x
| FCOMP x ->
  f42
    x
| FCOMPP ->
  f43
| FCOMIP x ->
  f44
    x
| FCOS ->
  f45
| FDECSTP ->
  f46
| FDIV (x,
        x0) ->
  f47
    x
    x0
| FDIVP x ->
  f48
    x
| FDIVR (x,
         x0) ->
  f49
    x
    x0
| FDIVRP x ->
  f50
    x
| FFREE x ->
  f51
    x
| FIADD x ->
  f52
    x
| FICOM x ->
  f53
    x
| FICOMP x ->
  f54
    x
| FIDIV x ->
  f55
    x
| FIDIVR x ->
  f56
    x
| FILD x ->
  f57
    x
| FIMUL x ->
  f58
    x
| FINCSTP ->
  f59
| FINIT ->
  f60
| FIST x ->
  f61
    x
| FISTP x ->
  f62
    x
| FISUB x ->
  f63
    x
| FISUBR x ->
  f64
    x
| FLD x ->
  f65
    x
| FLD1 ->
  f66
| FLDCW x ->
  f67
    x
| FLDENV x ->
  f68
    x
| FLDL2E ->
  f69
| FLDL2T ->
  f70
| FLDLG2 ->
  f71
| FLDLN2 ->
  f72
| FLDPI ->
  f73
| FLDZ ->
  f74
| FMUL (x,
        x0) ->
  f75
    x
    x0
| FMULP x ->
  f76
    x
| FNOP ->
  f77
| FNSAVE x ->
  f78
    x
| FNSTCW x ->
  f79
    x
| FNSTSW x ->
  f80
    x
| FPATAN ->
  f81
| FPREM ->
  f82
| FPREM1 ->
  f83
| FPTAN -> f84
| FRNDINT -> f85
| FRSTOR x -> f86 x
| FSCALE -> f87
| FSIN -> f88
| FSINCOS -> f89
| FSQRT -> f90
| FST x -> f91 x
| FSTENV x -> f92 x
| FSTP x -> f93 x
| FSUB (x, x0) -> f94 x x0
| FSUBP x -> f95 x
| FSUBR (x, x0) -> f96 x x0
| FSUBRP x -> f97 x
| FTST -> f98
| FUCOM x -> f99 x
| FUCOMP x -> f100 x
| FUCOMPP -> f101
| FUCOMI x -> f102 x
| FUCOMIP x -> f103 x
| FXAM -> f104
| FXCH x -> f105 x
| FXTRACT -> f106
| FYL2X -> f107
| FYL2XP1 -> f108
| FWAIT -> f109
| EMMS -> f110
| MOVD (x, x0) -> f111 x x0
| MOVQ (x, x0) -> f112 x x0
| PACKSSDW (x, x0) -> f113 x x0
| PACKSSWB (x, x0) -> f114 x x0
| PACKUSWB (x, x0) -> f115 x x0
| PADD (x, x0, x1) -> f116 x x0 x1
| PADDS (x, x0, x1) -> f117 x x0 x1
| PADDUS (x, x0, x1) -> f118 x x0 x1
| PAND (x, x0) -> f119 x x0
| PANDN (x, x0) -> f120 x x0
| PCMPEQ (x, x0, x1) -> f121 x x0 x1
| PCMPGT (x, x0, x1) -> f122 x x0 x1
| PMADDWD (x, x0) -> f123 x x0
| PMULHUW (x, x0) -> f124 x x0
| PMULHW (x, x0) -> f125 x x0
| PMULLW (x, x0) -> f126 x x0
| POR (x, x0) -> f127 x x0
| PSLL (x, x0, x1) -> f128 x x0 x1
| PSRA (x, x0, x1) -> f129 x x0 x1
| PSRL (x, x0, x1) -> f130 x x0 x1
| PSUB (x, x0, x1) -> f131 x x0 x1
| PSUBS (x, x0, x1) -> f132 x x0 x1
| PSUBUS (x, x0, x1) -> f133 x x0 x1
| PUNPCKH (x, x0, x1) -> f134 x x0 x1
| PUNPCKL (x, x0, x1) -> f135 x x0 x1
| PXOR (x, x0) -> f136 x x0
| ADDPS (x, x0) -> f137 x x0
| ADDSS (x, x0) -> f138 x x0
| ANDNPS (x, x0) -> f139 x x0
| ANDPS (x, x0) -> f140 x x0
| CMPPS (x, x0, x1) -> f141 x x0 x1
| CMPSS (x, x0, x1) -> f142 x x0 x1
| COMISS (x, x0) -> f143 x x0
| CVTPI2PS (x, x0) -> f144 x x0
| CVTPS2PI (x, x0) -> f145 x x0
| CVTSI2SS (x, x0) -> f146 x x0
| CVTSS2SI (x, x0) -> f147 x x0
| CVTTPS2PI (x, x0) -> f148 x x0
| CVTTSS2SI (x, x0) -> f149 x x0
| DIVPS (x, x0) -> f150 x x0
| DIVSS (x, x0) -> f151 x x0
| LDMXCSR x -> f152 x
| MAXPS (x, x0) -> f153 x x0
| MAXSS (x, x0) -> f154 x x0
| MINPS (x, x0) -> f155 x x0
| MINSS (x, x0) -> f156 x x0
| MOVAPS (x, x0) -> f157 x x0
| MOVHLPS (x, x0) -> f158 x x0
| MOVHPS (x, x0) -> f159 x x0
| MOVLHPS (x, x0) -> f160 x x0
| MOVLPS (x, x0) -> f161 x x0
| MOVMSKPS (x, x0) -> f162 x x0
| MOVSS (x, x0) -> f163 x x0
| MOVUPS (x, x0) -> f164 x x0
| MULPS (x, x0) -> f165 x x0
| MULSS (x, x0) -> f166 x x0
| ORPS (x, x0) -> f167 x x0
| RCPPS (x, x0) -> f168 x x0
| RCPSS (x, x0) -> f169 x x0
| RSQRTPS (x, x0) -> f170 x x0
| RSQRTSS (x, x0) -> f171 x x0
| SHUFPS (x, x0, x1) -> f172 x x0 x1
| SQRTPS (x, x0) -> f173 x x0
| SQRTSS (x, x0) -> f174 x x0
| STMXCSR x -> f175 x
| SUBPS (x, x0) -> f176 x x0
| SUBSS (x, x0) -> f177 x x0
| UCOMISS (x, x0) -> f178 x x0
| UNPCKHPS (x, x0) -> f179 x x0
| UNPCKLPS (x, x0) -> f180 x x0
| XORPS (x, x0) -> f181 x x0
| PAVGB (x, x0) -> f182 x x0
| PEXTRW (x, x0, x1) -> f183 x x0 x1
| PINSRW (x, x0, x1) -> f184 x x0 x1
| PMAXSW (x, x0) -> f185 x x0
| PMAXUB (x, x0) -> f186 x x0
| PMINSW (x, x0) -> f187 x x0
| PMINUB (x, x0) -> f188 x x0
| PMOVMSKB (x, x0) -> f189 x x0
| PSADBW (x, x0) -> f190 x x0
| PSHUFW (x, x0, x1) -> f191 x x0 x1
| MASKMOVQ (x, x0) -> f192 x x0
| MOVNTPS (x, x0) -> f193 x x0
| MOVNTQ (x, x0) -> f194 x x0
| PREFETCHT0 x -> f195 x
| PREFETCHT1 x -> f196 x
| PREFETCHT2 x -> f197 x
| PREFETCHNTA x -> f198 x
| SFENCE -> f199
| HLT -> f200
| IDIV (x, x0) -> f201 x x0
| IMUL (x, x0, x1, x2) -> f202 x x0 x1 x2
| IN (x, x0) -> f203 x x0
| INC (x, x0) -> f204 x x0
| INS x -> f205 x
| INTn x -> f206 x
| INT -> f207
| INTO -> f208
| INVD -> f209
| INVLPG x -> f210 x
| IRET -> f211
| Jcc (x, x0) -> f212 x x0
| JCXZ x -> f213 x
| JMP (x, x0, x1, x2) -> f214 x x0 x1 x2
| LAHF -> f215
| LAR (x, x0) -> f216 x x0
| LDS (x, x0) -> f217 x x0
| LEA (x, x0) -> f218 x x0
| LEAVE -> f219
| LES (x, x0) -> f220 x x0
| LFS (x, x0) -> f221 x x0
| LGDT x -> f222 x
| LGS (x, x0) -> f223 x x0
| LIDT x -> f224 x
| LLDT x -> f225 x
| LMSW x -> f226 x
| LODS x -> f227 x
| LOOP x -> f228 x
| LOOPZ x -> f229 x
| LOOPNZ x -> f230 x
| LSL (x, x0) -> f231 x x0
| LSS (x, x0) -> f232 x x0
| LTR x -> f233 x
| MOV (x, x0, x1) -> f234 x x0 x1
| MOVCR (x, x0, x1) -> f235 x x0 x1
| MOVDR (x, x0, x1) -> f236 x x0 x1
| MOVSR (x, x0, x1) -> f237 x x0 x1
| MOVBE (x, x0) -> f238 x x0
| MOVS x -> f239 x
| MOVSX (x, x0, x1) -> f240 x x0 x1
| MOVZX (x, x0, x1) -> f241 x x0 x1
| MUL (x, x0) -> f242 x x0
| NEG (x, x0) -> f243 x x0
| NOP x -> f244 x
| NOT (x, x0) -> f245 x x0
| OR (x, x0, x1) -> f246 x x0 x1
| OUT (x, x0) -> f247 x x0
| OUTS x -> f248 x
| POP x -> f249 x
| POPSR x -> f250 x
| POPA -> f251
| POPF -> f252
| PUSH (x, x0) -> f253 x x0
| PUSHSR x -> f254 x
| PUSHA -> f255
| PUSHF -> f256
| RCL (x, x0, x1) -> f257 x x0 x1
| RCR (x, x0, x1) -> f258 x x0 x1
| RDMSR -> f259
| RDPMC -> f260
| RDTSC -> f261
| RDTSCP -> f262
| RET (x, x0) -> f263 x x0
| ROL (x, x0, x1) -> f264 x x0 x1
| ROR (x, x0, x1) -> f265 x x0 x1
| RSM -> f266
| SAHF -> f267
| SAR (x, x0, x1) -> f268 x x0 x1
| SBB (x, x0, x1) -> f269 x x0 x1
| SCAS x -> f270 x
| SETcc (x, x0) -> f271 x x0
| SGDT x -> f272 x
| SHL (x, x0, x1) -> f273 x x0 x1
| SHLD (x, x0, x1) -> f274 x x0 x1
| SHR (x, x0, x1) -> f275 x x0 x1
| SHRD (x, x0, x1) -> f276 x x0 x1
| SIDT x -> f277 x
| SLDT x -> f278 x
| SMSW x -> f279 x
| STC -> f280
| STD -> f281
| STI -> f282
| STOS x -> f283 x
| STR x -> f284 x
| SUB (x, x0, x1) -> f285 x x0 x1
| TEST (x, x0, x1) -> f286 x x0 x1
| UD2 -> f287
| VERR x -> f288 x
| VERW x -> f289 x
| WBINVD -> f290
| WRMSR -> f291
| XADD (x, x0, x1) -> f292 x x0 x1
| XCHG (x, x0, x1) -> f293 x x0 x1
| XLAT -> f294
| XOR (x, x0, x1) -> f295 x x0 x1

type fp_lastInstrPtr_register = instr

type fp_opcode_register = instr

type lock_or_rep =
| Coq_lock
| Coq_rep
| Coq_repn

(** val lock_or_rep_rect : 'a1 -> 'a1 -> 'a1 -> lock_or_rep -> 'a1 **)

let lock_or_rep_rect f f0 f1 = function
| Coq_lock -> f
| Coq_rep -> f0
| Coq_repn -> f1

(** val lock_or_rep_rec : 'a1 -> 'a1 -> 'a1 -> lock_or_rep -> 'a1 **)

let lock_or_rep_rec f f0 f1 = function
| Coq_lock -> f
| Coq_rep -> f0
| Coq_repn -> f1

type prefix = { lock_rep : lock_or_rep option;
                seg_override : segment_register option; op_override : 
                bool; addr_override : bool }

(** val prefix_rect :
    (lock_or_rep option -> segment_register option -> bool -> bool -> 'a1) ->
    prefix -> 'a1 **)

let prefix_rect f p =
  let { lock_rep = x; seg_override = x0; op_override = x1; addr_override =
    x2 } = p
  in
  f x x0 x1 x2

(** val prefix_rec :
    (lock_or_rep option -> segment_register option -> bool -> bool -> 'a1) ->
    prefix -> 'a1 **)

let prefix_rec f p =
  let { lock_rep = x; seg_override = x0; op_override = x1; addr_override =
    x2 } = p
  in
  f x x0 x1 x2

(** val lock_rep : prefix -> lock_or_rep option **)

let lock_rep x = x.lock_rep

(** val seg_override : prefix -> segment_register option **)

let seg_override x = x.seg_override

(** val op_override : prefix -> bool **)

let op_override x = x.op_override

(** val addr_override : prefix -> bool **)

let addr_override x = x.addr_override

