(*
  Some Auxiliary definitions for Fappli_IEEE.
  By : Mark Kogan
*)

Require Import Flocq.Appli.Fappli_IEEE_bits.
Require Import Flocq.Core.Fcore.
Require Import Flocq.Core.Fcore_digits.
Require Import Flocq.Calc.Fcalc_digits.
Require Import Flocq.Appli.Fappli_IEEE.

Section B80_bits.

Definition binary80 := binary_float 64 16384.

Let Hprec : (0 < 64)%Z.
apply refl_equal.
Qed.

Let Hprec_emax : (64 < 16384)%Z.
apply refl_equal.
Qed.

Definition b80_opp := Bopp 64 16384.
Definition b80_plus := Bplus _ _ Hprec Hprec_emax.
Definition b80_minus := Bminus _ _ Hprec Hprec_emax.
Definition b80_mult := Bmult _ _ Hprec Hprec_emax.
Definition b80_div := Bdiv _ _ Hprec Hprec_emax.
Definition b80_sqrt := Bsqrt _ _ Hprec Hprec_emax.

Definition b80_of_bits : Z -> binary80 := binary_float_of_bits 63 15 (refl_equal _) (refl_equal _) (refl_equal _).
Definition bits_of_b80 : binary80 -> Z := bits_of_binary_float 63 15.

End B80_bits.

Section Bit_Conversions.

(* Shift mantissa right 29 bits (52 - 23) and exponent 3 bits (11 - 8) to create b32 out of b64 *)
Definition b64_to_b32 (b: binary64) : binary32 :=
   match b with
   | B754_nan => B754_nan _ _
   | B754_zero boole => B754_zero _ _ boole
   | B754_infinity boole => B754_infinity _ _ boole
   | B754_finite sign mant exp' _  =>
        let (rec, shifted_m) := shr (Build_shr_record (Zpos mant) false false) (Zpos mant) 29 in
        let (rec', shifted_e) := shr (Build_shr_record exp' false false) exp' 3 in
        let joined := join_bits 24 128 sign shifted_m shifted_e in
        b32_of_bits joined
   end.

(*Shift mantissa left 29 bits and exponent 3 bits to create b64 out of b32 *)
Definition b32_to_b64 (b: binary32) : binary64 :=
        match b with
   | B754_nan => B754_nan _ _
   | B754_zero boole => B754_zero _ _ boole
   | B754_infinity boole => B754_infinity _ _ boole
   | B754_finite sign mant exp' _  =>
        let (rec, shifted_m) := shl_align 23 exp' 29 in
        let (recc, shifted_e) := shl_align 8 exp' 3 in
        let joined := join_bits 53 1024 sign shifted_m shifted_e in
        b64_of_bits joined
   end.

Definition b80_to_b64 (b: binary80) : binary64 :=
   match b with
   | B754_nan => B754_nan _ _
   | B754_zero boole => B754_zero _ _ boole
   | B754_infinity boole => B754_infinity _ _ boole
   | B754_finite sign mant exp' _  =>
        let (rec, shifted_m) := shr (Build_shr_record (Zpos mant) false false) (Zpos mant) 11 in
        let (rec', shifted_e) := shr (Build_shr_record exp' false false) exp' 5 in
        let joined := join_bits 53 1024 sign shifted_m shifted_e in
        b64_of_bits joined
   end.

Definition b64_to_b80 (b: binary64) : binary80 :=
        match b with
   | B754_nan => B754_nan _ _
   | B754_zero boole => B754_zero _ _ boole
   | B754_infinity boole => B754_infinity _ _ boole
   | B754_finite sign mant exp' _  =>
        let (rec, shifted_m) := shl_align 52 exp' 11 in
        let (recc, shifted_e) := shl_align 11 exp' 5 in
        let joined := join_bits 64 16384 sign shifted_m shifted_e in
        b80_of_bits joined
   end.

Definition b32_to_b80 (b : binary32) : binary80 :=
  let bsf := b32_to_b64 b in
  b64_to_b80 bsf.

Definition b80_to_b32 (b : binary80) : binary32 :=
  let bsf := b80_to_b64 b in
  b64_to_b32 bsf.

End Bit_Conversions.
