(*
  Some Auxiliary definitions for Fappli_IEEE.
*)

Require Import Flocq.Appli.Fappli_IEEE_bits.
Require Import Flocq.Core.Fcore.
Require Import Flocq.Core.Fcore_digits.
Require Import Flocq.Calc.Fcalc_digits.
Require Import Flocq.Appli.Fappli_IEEE.

Section DE_float.

(* 79 bits binary floating point numbers;
   1 bit sign; 15-bit exponent; 63-bit mantissa *)
Definition binary79 := binary_float 64 16384.

Let Hprec : (0 < 64)%Z.
apply refl_equal.
Qed.

Let Hprec_emax : (64 < 16384)%Z.
apply refl_equal.
Qed.

Definition b79_of_bits : Z -> binary79 := binary_float_of_bits 63 15 (refl_equal _) (refl_equal _) (refl_equal _).
Definition bits_of_b79 : binary79 -> Z := bits_of_binary_float 63 15.

Definition binary79_normalize := binary_normalize 64 16384 Hprec Hprec_emax.

(* 80-bit doubled extended floating point format: 
   * 1 bit for the sign of the significand
   * 15 bits for the exponent
   * 64 bits for the significand
   NOTE: in contrast to 32-bit single-precision and 64-bit double-precision
   floating-point numbers, binary80 does not include an implicit bit.
   Therefore, internally 80-bit extended precision numbers are represented as binary79
*)
Definition de_float := binary79.

Definition de_float_of_bits (x: Z) : de_float := 
  let '(sx, mx, ex) := split_bits 64 15 x in
    let mx' := Zmod mx (Zpower 2 63) in (* throw away the highest bit in mantissa *)
      b79_of_bits (join_bits 63 15 sx mx' ex).

(* when converting a de_float to bits, add the highest bit *)
Definition bits_of_de_float (f:de_float) : Z :=
  let x := bits_of_b79 f in
    let '(sx, mx, ex) := split_bits 63 15 x in
      if Zeq_bool ex 0 then
        (* exponent=0, representing pos/neg zero or a small number close to zero *)
        join_bits 64 15 sx mx ex (* the highest bit is 0 *)
      else if Zeq_bool ex (Zpower 2 15 - 1) then 
        (* exponent=max; either pos/neg infinity or nan *)
        join_bits 64 15 sx mx ex (* the highest bit is 0 *)
      else
        join_bits 64 15 sx (Zpower 2 63 + mx)%Z ex. (* the highest bit is 1 *)

Definition de_float_opp := Bopp 64 16384.
Definition de_float_plus := Bplus _ _ Hprec Hprec_emax.
Definition de_float_minus := Bminus _ _ Hprec Hprec_emax.
Definition de_float_mult := Bmult _ _ Hprec Hprec_emax.
Definition de_float_div := Bdiv _ _ Hprec Hprec_emax.
Definition de_float_sqrt := Bsqrt _ _ Hprec Hprec_emax.

End DE_float.

Section Float_conv.

Let H32prec : (0 < 24)%Z.
apply refl_equal.
Qed.
Let H32prec_emax : (24 < 128)%Z.
apply refl_equal.
Qed.
Definition binary32_normalize := 
  binary_normalize 24 128 H32prec H32prec_emax.

Let H64prec : (0 < 53)%Z.
apply refl_equal.
Qed.
Let H64prec_emax : (53 < 1024)%Z.
apply refl_equal.
Qed.
Definition binary64_normalize := 
  binary_normalize 53 1024 H64prec H64prec_emax.

Definition nan_pl_mono (prec1 prec2:Z) (nan: nan_pl prec1)
  (pf: Z.lt prec1 prec2): nan_pl prec2.
  refine (match nan with
          | exist _ pl pf => exist _ pl _
          end).
  rewrite Z.ltb_lt in *. omega.
Defined. 

Definition nan_pl_24_to_53 (nan:nan_pl 24) : nan_pl 53.
  refine (nan_pl_mono _ _ nan _). omega.
Defined. 

Definition nan_pl_24_to_64 (nan:nan_pl 24) : nan_pl 64.
  refine (nan_pl_mono _ _ nan _). omega.
Defined. 

Definition nan_pl_53_to_64 (nan:nan_pl 53) : nan_pl 64.
  refine (nan_pl_mono _ _ nan _). omega.
Defined. 


Definition b64_of_b32 (b:binary32) : binary64 := 
  match b with
    | B754_nan _ _ b n => B754_nan 53 _ b (nan_pl_24_to_53 n)
    | B754_zero _ _ boole => B754_zero _ _ boole
    | B754_infinity _ _ boole => B754_infinity _ _ boole
    | B754_finite _ _ sign mant ep _  =>
      binary64_normalize mode_NE (cond_Zopp sign (Zpos mant)) ep true
  end.

(* Definition b64_of_b32 (b:binary32) : binary64 := match b with *)
(*    | B754_nan => B754_nan _ _ *)
(*    | B754_zero boole => B754_zero _ _ boole *)
(*    | B754_infinity boole => B754_infinity _ _ boole *)
(*    | B754_finite sign mant exp _  => *)
(*      let exp' := (exp * Zpower 2 29)%Z in *)
(*      let mant' := (Zpos mant + 1920)%Z in (* 1920 is 2^11 - 2^8; here we need to adjust the bias *) *)
(*      let joined := join_bits 52 11 sign mant' exp' in *)
(*        b64_of_bits joined *)
(* end. *)

Definition b32_of_b64 (b: binary64) : binary32 :=
   match b with
   | B754_nan _ _ b n => 
     (* using the default nan below; the real processor may behave differently *)
     let (b1,n1) := default_nan_pl32 in B754_nan _ _ b1 n1
   | B754_zero _ _ boole => B754_zero _ _ boole
   | B754_infinity _ _ boole => B754_infinity _ _ boole
   | B754_finite _ _ sign mant ep _  =>
      binary32_normalize mode_NE 
      (cond_Zopp sign (Zpos mant)) ep true
   end.

Definition de_float_of_b32 (b:binary32) : de_float := 
   match b with
   | B754_nan _ _ b n => B754_nan _ _ b (nan_pl_24_to_64 n)
   | B754_zero _ _ boole => B754_zero _ _ boole
   | B754_infinity _ _ boole => B754_infinity _ _ boole
   | B754_finite _ _ sign mant ep _  =>
      binary79_normalize mode_NE 
      (cond_Zopp sign (Zpos mant)) ep true
   end.

Definition b32_of_de_float (b:de_float) : binary32 := 
   match b with
   | B754_nan _ _ b n =>
     (* using the default nan below; the real processor may behave differently *)
     let (b1,n1) := default_nan_pl32 in B754_nan _ _ b1 n1
   | B754_zero _ _ boole => B754_zero _ _ boole
   | B754_infinity _ _ boole => B754_infinity _ _ boole
   | B754_finite _ _ sign mant ep _  =>
      binary32_normalize mode_NE 
      (cond_Zopp sign (Zpos mant)) ep true
   end.

Definition de_float_of_b64 (b:binary64) : de_float := 
   match b with
   | B754_nan _ _ b n => B754_nan _ _ b (nan_pl_53_to_64 n)
   | B754_zero _ _ boole => B754_zero _ _ boole
   | B754_infinity _ _ boole => B754_infinity _ _ boole
   | B754_finite _ _ sign mant ep _  =>
      binary79_normalize mode_NE 
      (cond_Zopp sign (Zpos mant)) ep true
   end.

Definition b64_of_de_float (b:de_float) : binary64 := 
   match b with
   | B754_nan _ _ b n =>
     (* using the default nan below; the real processor may behave differently *)
     let (b1,n1) := default_nan_pl64 in B754_nan _ _ b1 n1
   | B754_zero _ _ boole => B754_zero _ _ boole
   | B754_infinity _ _ boole => B754_infinity _ _ boole
   | B754_finite _ _ sign mant ep _  =>
      binary64_normalize mode_NE 
      (cond_Zopp sign (Zpos mant)) ep true
   end.

End Float_conv.

Section Comp_Tests.

Local Open Scope positive_scope.

(* number: 1.101 * 2^0 *)
(* sign: 0; exponent: 01111111; fraction:10100000000000000000000 *)
Definition f32_num1 := b32_of_bits
  (Zpos 1~1~1~1~1~1~1
        ~1~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).

(* number: -1.11 *)
(* sign: 1; exponent: 01111111; fraction:11000000000000000000000 *)
Definition f32_num2 := b32_of_bits
  (Zpos 1~
        0~1~1~1~1~1~1~1
        ~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).

(* positive zero *)
Definition f32_pos0 := b32_of_bits 0%Z.

(* Testing simple operations on b32 *)

(* result should be: 1.101 * 2^1 *)
(* sign: 0 exponent: 1000 0000; fraction: 10100000000000000000000 *)
Eval compute in (bits_of_b32 (b32_plus mode_NE f32_num1 f32_num1)).

(* result should be - 1.000 * 2^(-3) *)
(* sign: 1 exponent: 0111 1100; fraction: 00000000000000000000000 *)
Eval compute in (bits_of_b32 (b32_plus mode_NE f32_num1 f32_num2)).

Eval compute in (bits_of_b32 (b32_plus mode_NE f32_pos0 f32_pos0)).
Eval compute in (bits_of_b32 (b32_plus mode_NE f32_pos0 f32_num1)).

(* Testing conversions *)
Eval compute in (bits_of_b64 (b64_of_b32 f32_num1)).
Eval compute in (bits_of_b64 (b64_of_b32 f32_pos0)).
Eval compute in (bits_of_b32 f32_num1).
Eval compute in (bits_of_b32 (b32_of_b64 (b64_of_b32 f32_num1))).
Eval compute in (bits_of_b64 (b64_of_b32 f32_num2)).
Eval compute in (bits_of_b32 f32_num2).
Eval compute in (bits_of_b32 (b32_of_b64 (b64_of_b32 f32_num2))).

(* result is
0
011111111111111
1101000000000000000000000000000000000000000000000000000000000000
*)
Eval compute in (bits_of_de_float (de_float_of_b32 f32_num1)).

(* result is
1
011111111111111
1110000000000000000000000000000000000000000000000000000000000000
*)
Eval compute in (bits_of_de_float (de_float_of_b32 f32_num2)).
Eval compute in (bits_of_b32 f32_num1).
Eval compute in (bits_of_b32 (b32_of_de_float (de_float_of_b32 f32_num1))).
Eval compute in (bits_of_b32 f32_num2).
Eval compute in (bits_of_b32 (b32_of_de_float (de_float_of_b32 f32_num2))).

End Comp_Tests.
