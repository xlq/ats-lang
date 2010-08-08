(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *) // integral OPs
(* Author: Shivkumar Chandrasekaran (shiv AT ece DOT ucsb DOT edu) *) // floating OPs

(* ****** ****** *)

%{#
#include "libc/CATS/gmp.cats"
%} // end of [%{#]

(* ****** ****** *)

// integral numbers
absviewt@ype mpz_viewt0ype = $extype "ats_mpz_viewt0ype"
stadef mpz_vt = mpz_viewt0ype

// rational numbers
absviewt@ype mpq_viewt0ype = $extype "ats_mpq_viewt0ype"
stadef mpq_vt = mpq_viewt0ype

// floating point numbers
absviewt@ype mpf_viewt0ype = $extype "ats_mpf_viewt0ype"
stadef mpf_vt = mpf_viewt0ype

(* ****** ****** *)
//
// HX: integral number operations
//
(* ****** ****** *)

// [x] is initialized with 0
fun mpz_init
  (x: &mpz_vt? >> mpz_vt):<> void = "#atslib_mpz_init" // macro!
// end of [mpz_init]

// [x] is initialized with 0 while given [n]-bit space
fun mpz_init2
  (x: &mpz_vt? >> mpz_vt, n: ulint) :<> void = "#atslib_mpz_init2"
// end of [mpz_init2]

// [x] is cleared
fun mpz_clear
  (x: &mpz_vt >> mpz_vt?):<> void = "#atslib_mpz_clear" // macro!
// end of [mpz_clear]

// [x] is reallocated; the original value of [x] is carried over
// if there is enough space or 0 is assigned to [x]
fun mpz_realloc2
  (x: &mpz_vt >> mpz_vt, n: ulint):<> void = "#atslib_mpz_realloc2"
// end of [mpz_realloc2]

(* ****** ****** *)

symintr mpz_get

fun mpz_get_int (x: &mpz_vt):<> int = "#atslib_mpz_get_int"
overload mpz_get with mpz_get_int

fun mpz_get_uint (x: &mpz_vt):<> uint = "#atslib_mpz_get_uint"
overload mpz_get with mpz_get_uint

fun mpz_get_lint (x: &mpz_vt):<> lint = "#atslib_mpz_get_lint"
overload mpz_get with mpz_get_lint

fun mpz_get_ulint (x: &mpz_vt):<> ulint = "#atslib_mpz_get_ulint"
overload mpz_get with mpz_get_ulint

fun mpz_get_double (x: &mpz_vt):<> double = "#atslib_mpz_get_double"
overload mpz_get with mpz_get_double

fun mpz_get_str
  {i:int | 2 <= i; i <= 36} (base: int i, x: &mpz_vt): Strbufptr_gc
  = "atslib_mpz_get_str" // function!
// end of [mpz_get_str]

(* ****** ****** *)

symintr mpz_set

// [x] := [y]
fun mpz_set_mpz
  (x: &mpz_vt, y: &mpz_vt):<> void = "#atslib_mpz_set_mpz"
overload mpz_set with mpz_set_mpz

// [x] := [y]
fun mpz_set_int (x: &mpz_vt, y: int):<> void = "#atslib_mpz_set_int"
overload mpz_set with mpz_set_int

// [x] := [y]
fun mpz_set_uint (x: &mpz_vt, y: uint):<> void = "#atslib_mpz_set_uint"
overload mpz_set with mpz_set_uint

// [x] := [y]
fun mpz_set_lint (x: &mpz_vt, y: lint):<> void = "#atslib_mpz_set_lint"
overload mpz_set with mpz_set_lint

// [x] := [y]
fun mpz_set_ulint (x: &mpz_vt, y: ulint):<> void = "#atslib_mpz_set_ulint"
overload mpz_set with mpz_set_ulint

// [x] := [y]
fun mpz_set_double
  (x: &mpz_vt, y: double):<> void = "#atslib_mpz_set_double"
overload mpz_set with mpz_set_double

// [x] := [y]
fun mpz_set_mpq (x: &mpz_vt, y: &mpq_vt):<> void = "#atslib_mpz_set_mpq"
overload mpz_set with mpz_set_mpq

// [x] := [y]
fun mpz_set_mpf (x: &mpz_vt, y: &mpf_vt):<> void = "#atslib_mpz_set_mpf"
overload mpz_set with mpz_set_mpf

// the function returns 0 if the string is valid, or -1 otherwise.
fun mpz_set_str_err
  {i:int | 2 <= i; i <= 62} (x: &mpz_vt, s: string, base: int i):<> int
  = "#atslib_mpz_set_str_err" // macro
// end of [mpz_set_str_err]

fun mpz_set_str_exn
  {i:int | 2 <= i; i <= 62} (x: &mpz_vt, s: string, base: int i):<> void
  = "atslib_mpz_set_str_exn" // function!
// end of [mpz_set_str_exn]

(* ****** ****** *)

symintr mpz_init_set

// [x] := [y]
fun mpz_init_set_mpz (x: &mpz_vt? >> mpz_vt, y: &mpz_vt):<> void
  = "#atslib_mpz_init_set_mpz"
overload mpz_init_set with mpz_init_set_mpz

// [x] := [y]
fun mpz_init_set_int (x: &mpz_vt? >> mpz_vt, y: int):<> void
  = "#atslib_mpz_init_set_int"
overload mpz_init_set with mpz_init_set_int

// [x] := [y]
fun mpz_init_set_uint (x: &mpz_vt? >> mpz_vt, y: uint):<> void
  = "#atslib_mpz_init_set_uint"
overload mpz_init_set with mpz_init_set_uint

// [x] := [y]
fun mpz_init_set_lint (x: &mpz_vt? >> mpz_vt, y: lint):<> void
  = "#atslib_mpz_init_set_lint"
overload mpz_init_set with mpz_init_set_lint

// [x] := [y]
fun mpz_init_set_ulint (x: &mpz_vt? >> mpz_vt, y: ulint):<> void
  = "#atslib_mpz_init_set_ulint"
overload mpz_init_set with mpz_init_set_ulint

// [x] := [y]
fun mpz_init_set_double (x: &mpz_vt? >> mpz_vt, y: double):<> void
  = "#atslib_mpz_init_set_double"
overload mpz_init_set with mpz_init_set_double

// [x] := [y]
fun mpz_init_set_mpq (x: &mpz_vt? >> mpz_vt, y: &mpq_vt):<> void
  = "atslib_mpz_init_set_mpq" // function!
overload mpz_init_set with mpz_init_set_mpq

// [x] := [y]
fun mpz_init_set_mpf (x: &mpz_vt? >> mpz_vt, y: &mpf_vt):<> void
  = "atslib_mpz_init_set_mpf" // function!
overload mpz_init_set with mpz_init_set_mpf

// the function returns 0 if the string is valid, or -1 otherwise.
fun mpz_init_set_str_err
  {i:int | 2 <= i; i <= 62} (x: &mpz_vt? >> mpz_vt, s: string, base: int i):<> int
  = "atslib_mpz_init_set_str_err" // function!

// the function exits the string is invalid.
fun mpz_init_set_str_exn
  {i:int | 2 <= i; i <= 62} (x: &mpz_vt? >> mpz_vt, s: string, base: int i):<> void
  = "atslib_mpz_init_set_str_exn" // function!

(* ****** ****** *)

#define sixtythree 63
fun mpz_out_str_err {m:file_mode} (
    pf_mode: file_mode_lte (m, w)
  | file: &FILE m, base: intBtw (2, sixtythree), x: &mpz_vt
  ) : int = "#atslib_mpz_out_str_err"
// end of [mpz_out_str_err]

fun mpz_out_str_exn {m:file_mode} (
    pf_mode: file_mode_lte (m, w)
  | file: &FILE m, base: intBtw (2, sixtythree), x: &mpz_vt
  ) : void = "atslib_mpz_out_str_exn"
// end of [mpz_out_str_exn]

(* ****** ****** *)

// negation

symintr mpz_neg

// [x] := -[y]
fun mpz_neg2 (x: &mpz_vt, y: &mpz_vt):<> void = "#atslib_mpz_neg2"
overload mpz_neg with mpz_neg2

// [x] := -[x]
fun mpz_neg1 (x: &mpz_vt):<> void = "atslib_mpz_neg1" // function!
overload mpz_neg with mpz_neg1

// absolute value

symintr mpz_abs

// [x] := | [y] |
fun mpz_abs2 (x: &mpz_vt, y: &mpz_vt):<> void = "#atslib_mpz_abs2"
overload mpz_abs with mpz_abs2

// [x] := | [x] |
fun mpz_abs1 (x: &mpz_vt):<> void = "atslib_mpz_abs1" // function!
overload mpz_abs with mpz_abs1

// addition

symintr mpz_add

// [x] := [y] + [z]
fun mpz_add3_mpz
  (x: &mpz_vt, y: &mpz_vt, z: &mpz_vt):<> void = "#atslib_mpz_add3_mpz"
overload mpz_add with mpz_add3_mpz

fun mpz_add3_int
  (x: &mpz_vt, y: &mpz_vt, z: int):<> void = "atslib_mpz_add3_int" // fun!
overload mpz_add with mpz_add3_int

fun mpz_add3_uint
  (x: &mpz_vt, y: &mpz_vt, z: uint):<> void = "#atslib_mpz_add3_uint"
overload mpz_add with mpz_add3_uint

fun mpz_add3_lint
  (x: &mpz_vt, y: &mpz_vt, z: lint):<> void = "atslib_mpz_add3_lint" // fun!
overload mpz_add with mpz_add3_lint

fun mpz_add3_ulint
  (x: &mpz_vt, y: &mpz_vt, z: ulint):<> void = "#atslib_mpz_add3_ulint"
overload mpz_add with mpz_add3_ulint

// [x] := [x] + [y]
fun mpz_add2_mpz
  (x: &mpz_vt, y: &mpz_vt):<> void = "atslib_mpz_add2_mpz"
overload mpz_add with mpz_add2_mpz

fun mpz_add2_int
  (x: &mpz_vt, y: int):<> void = "atslib_mpz_add2_int"
overload mpz_add with mpz_add2_int

fun mpz_add2_uint
  (x: &mpz_vt, y: uint):<> void = "atslib_mpz_add2_uint"
overload mpz_add with mpz_add2_uint

fun mpz_add2_lint
  (x: &mpz_vt, y: lint):<> void = "atslib_mpz_add2_lint"
overload mpz_add with mpz_add2_lint

fun mpz_add2_ulint
  (x: &mpz_vt, y: ulint):<> void = "atslib_mpz_add2_ulint"
overload mpz_add with mpz_add2_ulint

// subtraction

symintr mpz_sub

// [x] := [y] - [z]
fun mpz_sub3_mpz
  (x: &mpz_vt, y: &mpz_vt, z: &mpz_vt):<> void = "#atslib_mpz_sub3_mpz"
overload mpz_sub with mpz_sub3_mpz  

fun mpz_sub3_int
  (x: &mpz_vt, y: &mpz_vt, z: int):<> void = "atslib_mpz_sub3_int" // fun!
overload mpz_sub with mpz_sub3_int

fun mpz_sub3_uint
  (x: &mpz_vt, y: &mpz_vt, z: uint):<> void = "#atslib_mpz_sub3_uint"
overload mpz_sub with mpz_sub3_uint

fun mpz_sub3_lint
  (x: &mpz_vt, y: &mpz_vt, z: lint):<> void = "atslib_mpz_sub3_lint" // fun!
overload mpz_sub with mpz_sub3_lint  

fun mpz_sub3_ulint
  (x: &mpz_vt, y: &mpz_vt, z: ulint):<> void = "#atslib_mpz_sub3_ulint"
overload mpz_sub with mpz_sub3_ulint  

//

// [x] := [x] - [y]
fun mpz_sub2_mpz
  (x: &mpz_vt, y: &mpz_vt):<> void = "atslib_mpz_sub2_mpz"
overload mpz_sub with mpz_sub2_mpz

fun mpz_sub2_int
  (x: &mpz_vt, y: int):<> void = "atslib_mpz_sub2_int"
overload mpz_sub with mpz_sub2_int

fun mpz_sub2_uint
  (x: &mpz_vt, y: uint):<> void = "atslib_mpz_sub2_uint"
overload mpz_sub with mpz_sub2_uint

fun mpz_sub2_lint
  (x: &mpz_vt, y: lint):<> void = "atslib_mpz_sub2_lint"
overload mpz_sub with mpz_sub2_lint

fun mpz_sub2_ulint
  (x: &mpz_vt, y: ulint):<> void = "atslib_mpz_sub2_ulint"
overload mpz_sub with mpz_sub2_ulint

(* ****** ****** *)

// multiplication

symintr mpz_mul

//

// [x] := [y] * [z]
fun mpz_mul3_mpz
  (x: &mpz_vt, y: &mpz_vt, z: &mpz_vt):<> void = "#atslib_mpz_mul3_mpz"
overload mpz_mul with mpz_mul3_mpz

fun mpz_mul3_int
  (x: &mpz_vt, y: &mpz_vt, z: int):<> void = "#atslib_mpz_mul3_int"
overload mpz_mul with mpz_mul3_int

fun mpz_mul3_uint
  (x: &mpz_vt, y: &mpz_vt, z: uint):<> void = "#atslib_mpz_mul3_uint"
overload mpz_mul with mpz_mul3_uint

fun mpz_mul3_lint
  (x: &mpz_vt, y: &mpz_vt, z: lint):<> void = "#atslib_mpz_mul3_lint"
overload mpz_mul with mpz_mul3_lint

fun mpz_mul3_ulint
  (x: &mpz_vt, y: &mpz_vt, z: ulint):<> void = "#atslib_mpz_mul3_ulint"
overload mpz_mul with mpz_mul3_ulint

//

// [x] := [x] * [y]
fun mpz_mul2_mpz
  (x: &mpz_vt, y: &mpz_vt):<> void = "atslib_mpz_mul2_mpz"
overload mpz_mul with mpz_mul2_mpz

fun mpz_mul2_int (x: &mpz_vt, y: int):<> void = "atslib_mpz_mul2_int"
overload mpz_mul with mpz_mul2_int

fun mpz_mul2_uint (x: &mpz_vt, y: uint):<> void = "atslib_mpz_mul2_uint"
overload mpz_mul with mpz_mul2_uint

fun mpz_mul2_lint (x: &mpz_vt, y: lint):<> void = "atslib_mpz_mul2_lint"
overload mpz_mul with mpz_mul2_lint

fun mpz_mul2_ulint (x: &mpz_vt, y: ulint):<> void = "atslib_mpz_mul2_ulint"
overload mpz_mul with mpz_mul2_ulint

// [x] := [x] * [x]
fun mpz_mul1_mpz (x: &mpz_vt):<> void = "atslib_mpz_mul1_mpz"
overload mpz_mul with mpz_mul1_mpz

(* ****** ****** *)

(*
** Function: mpz_mul_2exp
** Input: arg1, arg2
** Output: res
** Return: void
** Description: Set res so that res = arg1 * (2 ^ arg2)
** Remarks: The same object can be passed for both res and arg1.
** Others:
**   It's up to an application to call functions like mpz_mul_2exp when appropriate.
**   General purpose functions like mpz_mul make no attempt to identify powers of two
**   or other special forms.
*)
fun mpz_mul_2exp
  (res: &mpz_vt, arg1: &mpz_vt, arg2: int):<> void = "atslib_mpz_mul_2exp"
// end of [mpz_mul_2exp]

(* ****** ****** *)
//
// truncate division
//
symintr mpz_tdiv_qr

// (q, r) = n / d
fun mpz_tdiv4_qr_mpz
  (q: &mpz_vt, r: &mpz_vt, n: &mpz_vt, d: &mpz_vt):<> void = "#atslib_mpz_tdiv4_qr_mpz"
// end of [mpz_tdiv4_qr_mpz]
overload mpz_tdiv_qr with mpz_tdiv4_qr_mpz

// (q, r) = n / d
fun mpz_tdiv4_qr_ulint
  (q: &mpz_vt, r: &mpz_vt, n: &mpz_vt, d: ulint):<> void = "#atslib_mpz_tdiv4_qr_ulint"
// end of [mpz_tdiv4_qr_ulint]
overload mpz_tdiv_qr with mpz_tdiv4_qr_ulint

//

symintr mpz_tdiv_q

// [q] := [n] / [d]
fun mpz_tdiv3_q_mpz
  (q: &mpz_vt, n: &mpz_vt, d: &mpz_vt):<> void = "#atslib_mpz_tdiv3_q_mpz"
overload mpz_tdiv_q with mpz_tdiv3_q_mpz

// [q] := [n] / [d]
fun mpz_tdiv3_q_ulint
  (q: &mpz_vt, n: &mpz_vt, d: ulint):<> void = "#atslib_mpz_tdiv3_q_ulint"
overload mpz_tdiv_q with mpz_tdiv3_q_ulint

// [q] := [q] / [d]
fun mpz_tdiv2_q_mpz
  (q: &mpz_vt, d: &mpz_vt):<> void = "atslib_mpz_tdiv2_q_mpz"
overload mpz_tdiv_q with mpz_tdiv2_q_mpz

// [q] := [q] / [d]
fun mpz_tdiv2_q_ulint
  (q: &mpz_vt, d: ulint):<> void = "atslib_mpz_tdiv2_q_ulint"
overload mpz_tdiv_q with mpz_tdiv2_q_ulint

(* ****** ****** *)
//
// floor division
//
(*
** Function: mpz_fdiv_qr
** Input: dividend, divisor
** Output: quot, rem
** Return: void
** Description:
**   Set quot and rem so that dividend = quot * divisor + rem
**   Rounds quot down towards negative infinity, and rem will
**   have the same sign as divisor, and 0 <= |rem| < |divisor|.
**   'f' stands for "floor". e.g. 5 = (-2) * (-3) + (-1); -5 = 1 * (-3) + (-2)
** Remarks:
**   The same object cannot be passed for both quot and rem, or the result will be
**   unpredictable. No other constraints on the pass of other arguments, e.g. the same
**   object can be passed to both quot and dividend.
*)

//

symintr mpz_fdiv_qr

fun mpz_fdiv4_qr_mpz
  (quot: &mpz_vt, rem: &mpz_vt, dividend: &mpz_vt, divisor: &mpz_vt):<> void
  = "#atslib_mpz_fdiv4_qr_mpz"
overload mpz_fdiv_qr with mpz_fdiv4_qr_mpz

fun mpz_fdiv4_qr_ulint
  (quot: &mpz_vt, rem: &mpz_vt, dividend: &mpz_vt, divisor: ulint):<> void
  = "#atslib_mpz_fdiv4_qr_ulint"
overload mpz_fdiv_qr with mpz_fdiv4_qr_ulint

//

symintr mpz_fdiv_q

// [q] := [n] / [d]
fun mpz_fdiv3_q_mpz
  (q: &mpz_vt, n: &mpz_vt, d: &mpz_vt):<> void = "#atslib_mpz_fdiv3_q_mpz"
overload mpz_fdiv_q with mpz_fdiv3_q_mpz

// [q] := [n] / [d]
fun mpz_fdiv3_q_ulint
  (q: &mpz_vt, n: &mpz_vt, d: ulint):<> void = "#atslib_mpz_fdiv3_q_ulint"
overload mpz_fdiv_q with mpz_fdiv3_q_ulint

// [q] := [q] / [d]
fun mpz_fdiv2_q_mpz
  (q: &mpz_vt, d: &mpz_vt):<> void = "atslib_mpz_fdiv2_q_mpz"
overload mpz_fdiv_q with mpz_fdiv2_q_mpz

// [q] := [q] / [d]
fun mpz_fdiv2_q_ulint
  (q: &mpz_vt, d: ulint):<> void = "atslib_mpz_fdiv2_q_ulint"
overload mpz_fdiv_q with mpz_fdiv2_q_ulint

(* ****** ****** *)

symintr mpz_mod

fun mpz_mod3_mpz
  (r: &mpz_vt, n: &mpz_vt, d: &mpz_vt):<> void = "#atslib_mpz_mod3_mpz"
overload mpz_mod with mpz_mod3_mpz

fun mpz_mod3_ulint
  (r: &mpz_vt, n: &mpz_vt, d: ulint):<> void = "#atslib_mpz_mod3_ulint"
overload mpz_mod with mpz_mod3_ulint

(* ****** ****** *)

// add/mul combination

symintr mpz_addmul

fun mpz_addmul3_mpz
  (x: &mpz_vt, y: &mpz_vt, z: &mpz_vt):<> void = "#atslib_mpz_addmul3_mpz"
overload mpz_addmul with mpz_addmul3_mpz

fun mpz_addmul3_uint
  (x: &mpz_vt, y: &mpz_vt, z: uint):<> void = "#atslib_mpz_addmul3_uint"
overload mpz_addmul with mpz_addmul3_uint

// sub/mul combination

symintr mpz_submul

fun mpz_submul3_mpz
  (x: &mpz_vt, y: &mpz_vt, z: &mpz_vt):<> void = "#atslib_mpz_submul3_mpz"
overload mpz_submul with mpz_submul3_mpz

fun mpz_submul3_uint
  (x: &mpz_vt, y: &mpz_vt, z: uint):<> void = "#atslib_mpz_submul3_uint"
overload mpz_submul with mpz_submul3_uint

(* ****** ****** *)

symintr mpz_cmp

fun mpz_cmp_mpz (x: &mpz_vt, y: &mpz_vt):<> Sgn = "#atslib_mpz_cmp_mpz"
overload mpz_cmp with mpz_cmp_mpz

fun mpz_cmp_int (x: &mpz_vt, y: int):<> Sgn = "#atslib_mpz_cmp_int"
overload mpz_cmp with mpz_cmp_int

fun mpz_cmp_uint (x: &mpz_vt, y: uint):<> Sgn = "#atslib_mpz_cmp_uint"
overload mpz_cmp with mpz_cmp_uint

fun mpz_cmp_lint (x: &mpz_vt, y: lint):<> Sgn = "#atslib_mpz_cmp_lint"
overload mpz_cmp with mpz_cmp_lint

fun mpz_cmp_ulint (x: &mpz_vt, y: ulint):<> Sgn = "#atslib_mpz_cmp_ulint"
overload mpz_cmp with mpz_cmp_ulint

fun mpz_sgn (x: &mpz_vt):<> Sgn = "atslib_mpz_sgn" // function!

(* ****** ****** *)

fun fprint0_mpz
  (out: FILEref, x: &mpz_vt):<!exnref> void = "atslib_fprint_mpz"
overload fprint with fprint0_mpz

fun fprint1_mpz {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: &mpz_vt):<!exnref> void
  = "atslib_fprint_mpz"
overload fprint with fprint1_mpz

fun print_mpz (x: &mpz_vt) :<!ref> void = "atslib_print_mpz"
overload print with print_mpz

fun prerr_mpz (x: &mpz_vt) :<!ref> void = "atslib_prerr_mpz"
overload prerr with prerr_mpz

fun tostring_mpz (x: &mpz_vt):<> String = "atslib_tostring_mpz"
overload tostring with tostring_mpz

(* ****** ****** *)
//
// HX: floating number operations
//
(* ****** ****** *)
//
// HX-2010-07-28: [mpf_set_default_prec] is used to make sure that
//
sta mpf_set_default_prec : bool // [mpf_set_default_prec] is called

fun mpf_get_default_prec
  {mpf_set_default_prec} (): ulint = "#atslib_mpf_get_default_prec"
// end of [mpf_get_default_prec]

fun mpf_set_default_prec
  (prec: ulint): [mpf_set_default_prec] void = "#atslib_mpf_set_default_prec"
// end of [mpf_set_default_prec]

(* ****** ****** *)
//
// HX-2010-07-28:
// [mpf_init] must be called after [mpf_set_default_prec] is called
//
fun mpf_init {mpf_set_default_prec}
  (x: &mpf_vt? >> mpf_vt):<> void = "#atslib_mpf_init"
// end of [mpf_init]

fun mpf_init2
  (x: &mpf_vt? >> mpf_vt, prec: ulint): void = "#atslib_mpf_init2"
// end of [mpf_init2]

fun mpf_clear (x: &mpf_vt >> mpf_vt?): void = "#atslib_mpf_clear"

(* ****** ****** *)

fun mpf_get_prec (x: &mpf_vt): ulint = "#atslib_mpf_get_prec"

fun mpf_set_prec (x: &mpf_vt, prec: ulint): void = "#atslib_mpf_set_prec"

fun mpf_set_prec_raw
  (dst: &mpf_vt, prec: ulint): void = "#atslib_mpf_set_prec_raw"
// end of [mpf_set_prec_raw]

(* ****** ****** *)

fun mpf_get_d (src: &mpf_vt): double = "#atslib_mpf_get_d"
fun mpf_get_d_2exp
  (exp: &lint, src: &mpf_vt): double = "#atslib_mpf_get_d_2exp"
fun mpf_get_si (src: &mpf_vt): lint = "#atslib_mpf_get_si"
fun mpf_get_ui (src: &mpf_vt): ulint = "#atslib_mpf_get_ui"

(* ****** ****** *)

symintr mpf_set

fun mpf_set_mpf
  (dst: &mpf_vt, src: &mpf_vt): void = "#atslib_mpf_set_mpf"
overload mpf_set with mpf_set_mpf

fun mpf_set_si (dst: &mpf_vt, src: lint): void = "#atslib_mpf_set_si"
overload mpf_set with mpf_set_si

fun mpf_set_ui
  (dst: &mpf_vt, src: ulint): void = "#atslib_mpf_set_ui"
overload mpf_set with mpf_set_ui

fun mpf_set_d (dst: &mpf_vt, src: double): void = "#atslib_mpf_set_d"
overload mpf_set with mpf_set_d

fun mpf_set_z (dst: &mpf_vt, src: &mpz_vt): void = "#atslib_mpf_set_z"
overload mpf_set with mpf_set_z

fun mpf_set_q (dst: &mpf_vt, src: &mpq_vt): void = "#atslib_mpf_set_q"
overload mpf_set with mpf_set_q

fun mpf_set_str // succ/fail: 0/-1
  (dst: &mpf_vt, str: string, base: int): int(*err*) = "#atslib_mpf_set_str"
overload mpf_set with mpf_set_str

(* ****** ****** *)

symintr mpf_init_set

// dst := src
fun mpf_init_set_mpf {mpf_set_default_prec}
  (dst: &mpf_vt? >> mpf_vt, src: &mpf_vt): void = "#atslib_mpf_init_set_mpf"
overload mpf_init_set with mpf_init_set_mpf

fun mpf_init_set_si {mpf_set_default_prec}
  (dst: &mpf_vt? >> mpf_vt, src: lint): void = "#atslib_mpf_init_set_si"
overload mpf_init_set with mpf_init_set_si

fun mpf_init_set_ui {mpf_set_default_prec}
  (dst: &mpf_vt? >> mpf_vt, src: ulint): void = "#atslib_mpf_init_set_ui"
overload mpf_init_set with mpf_init_set_ui

fun mpf_init_set_d {mpf_set_default_prec}
  (dst: &mpf_vt? >> mpf_vt, src: double): void = "#atslib_mpf_init_set_d"
overload mpf_init_set with mpf_init_set_d

(* ****** ****** *)

fun mpf_swap (dst1: &mpf_vt, dst2: &mpf_vt): void = "#atslib_mpf_swap"

(* ****** ****** *)

fun mpf_ceil (dst: &mpf_vt, src: &mpf_vt):<> void = "#atslib_mpf_ceil"
fun mpf_floor (dst: &mpf_vt, src: &mpf_vt):<> void = "#atslib_mpf_floor"
fun mpf_trunc (dst: &mpf_vt, src: &mpf_vt):<> void = "#atslib_mpf_trunc"
fun mpf_integer_p (src: &mpf_vt):<> bool = "#atslib_mpf_integer_p"

(* ****** ****** *)

symintr mpf_neg

// x := -y
fun mpf_neg2 (x: &mpf_vt, y: &mpf_vt): void = "#abslib_mpf_neg2"
overload mpf_neg with mpf_neg2

// x := -x
fun mpf_neg1 (x: &mpf_vt): void = "abslib_mpf_neg1" // !function
overload mpf_neg with mpf_neg1

(* ****** ****** *)

symintr mpf_abs

// x := |y|
fun mpf_abs2 (x: &mpf_vt, y: &mpf_vt): void = "#abslib_mpf_abs2"
overload mpf_abs with mpf_abs2

// x := |x|
fun mpf_abs1 (x: &mpf_vt): void = "abslib_mpf_abs1" // !function
overload mpf_abs with mpf_abs1

(* ****** ****** *)

symintr mpf_add3

fun mpf_add3_mpf (dst: &mpf_vt, src1: &mpf_vt, src2: &mpf_vt): void
  = "#atslib_mpf_add3_mpf"
overload mpf_add3 with mpf_add3_mpf

fun mpf_add3_ui
  (dst: &mpf_vt, src1: &mpf_vt, src2: ulint): void = "#atslib_mpf_add3_ui"
overload mpf_add3 with mpf_add3_ui

symintr mpf_add2

fun mpf_add2_mpf
  (dst: &mpf_vt, src1: &mpf_vt): void = "atslib_mpf_add2_mpf" // fun!
overload mpf_add2 with mpf_add2_mpf

fun mpf_add2_ui (dst: &mpf_vt, src2: ulint): void = "atslib_mpf_add2_ui" // fun!
overload mpf_add2 with mpf_add2_ui

(* ****** ****** *)

symintr mpf_sub3

fun mpf_sub3_mpf (dst: &mpf_vt, src1: &mpf_vt, src2: &mpf_vt): void
  = "#atslib_mpf_sub_mpf"
overload mpf_sub3 with mpf_sub3_mpf

fun mpf_sub3_ui
  (dst: &mpf_vt, src1: &mpf_vt, src2: ulint): void = "#atslib_mpf_sub3_ui"
overload mpf_sub3 with mpf_sub3_ui

fun mpf_ui_sub3
  (dst: &mpf_vt, src1: ulint, src2: &mpf_vt): void = "#atslib_mpf_ui_sub3"
overload mpf_sub3 with mpf_ui_sub3

symintr mpf_sub2

fun mpf_sub2_mpf (dst: &mpf_vt, src1: &mpf_vt): void = "atslib_mpf_sub2" // !fun
overload mpf_sub2 with mpf_sub2_mpf

fun mpf_sub2_ui (dst: &mpf_vt, src2: ulint): void = "#atslib_mpf_sub2_ui" // !fun
overload mpf_sub2 with mpf_sub2_ui

(* ****** ****** *)

symintr mpf_mul3

fun mpf_mul3_mpf
  (dst: &mpf_vt, src1: &mpf_vt, src2: &mpf_vt): void = "#atslib_mpf_mul3_mpf"
overload mpf_mul3 with mpf_mul3_mpf

fun mpf_mul3_ui
  (dst: &mpf_vt, src1: &mpf_vt, src2: ulint): void = "#atslib_mpf_mul3_ui"
overload mpf_mul3 with mpf_mul3_ui

symintr mpf_mul2

fun mpf_mul2_mpf
  (dst: &mpf_vt, src: &mpf_vt): void = "atslib_mpf_mul2_mpf" // !function
overload mpf_mul2 with mpf_mul2_mpf

fun mpf_mul2_ui (dst: &mpf_vt, src: &mpf_vt): void = "atslib_mpf_mul2_ui" // !fun
overload mpf_mul2 with mpf_mul2_ui

(* ****** ****** *)

symintr mpf_div3

fun mpf_div3_mpf (dst: &mpf_vt, src1: &mpf_vt, src2: &mpf_vt): void
  = "#atslib_mpf_div3_mpf"
overload mpf_div3 with mpf_div3_mpf

fun mpf_div3_ui
  (dst: &mpf_vt, src1: &mpf_vt, src2: ulint): void = "#atslib_mpf_div3_ui"
overload mpf_div3 with mpf_div3_ui

fun mpf_ui_div3
  (dst: &mpf_vt, src1: ulint, src2: &mpf_vt): void = "#atslib_mpf_ui_div3"
overload mpf_div3 with mpf_ui_div3

symintr mpf_div2

fun mpf_div2_mpf
  (dst: &mpf_vt, src: &mpf_vt): void = "atslib_mpf_div2" // !function
overload mpf_div2 with mpf_div2_mpf

fun mpf_div2_ui (dst: &mpf_vt, src: ulint): void = "atslib_mpf_div2_ui" // !fun
overload mpf_div2 with mpf_div2_ui

(* ****** ****** *)

symintr mpf_sqrt

// dst := sqrt (src)
fun mpf_sqrt_mpf
  (dst: &mpf_vt, src: &mpf_vt): void = "#atslib_mpf_sqrt_mpf"
overload mpf_sqrt with mpf_sqrt_mpf
  
fun mpf_sqrt_ui (dst: &mpf_vt, src: ulint): void = "#atslib_mpf_sqrt_ui"
overload mpf_sqrt with mpf_sqrt_ui

(* ****** ****** *)

(* end of [gmp.sats] *)
