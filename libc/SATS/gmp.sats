(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 *
 * ATS - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#

#include "libc/CATS/gmp.cats"

%}

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

// [x] is initialized with 0
fun mpz_init (x: &mpz_vt? >> mpz_vt):<> void
  = "atslib_mpz_init"

// [x] is initialized with 0 while given [n]-bit space
fun mpz_init2 (x: &mpz_vt? >> mpz_vt, n: ulint) :<> void
  = "atslib_mpz_init2"

// [x] is cleared
fun mpz_clear (x: &mpz_vt >> mpz_vt?):<> void
  = "atslib_mpz_clear"

// [x] is reallocated; the original value of [x] is carried over
// if there is enough space or 0 is assigned to [x]
fun mpz_realloc2 (x: &mpz_vt >> mpz_vt, n: ulint):<> void
  = "atslib_mpz_realloc2"

(* ****** ****** *)

fun mpz_get_int (x: &mpz_vt):<> int
  = "atslib_mpz_get_int"

fun mpz_get_lint (x: &mpz_vt):<> lint
  = "atslib_mpz_get_lint"

fun mpz_get_uint (x: &mpz_vt):<> uint
  = "atslib_mpz_get_uint"

fun mpz_get_ulint (x: &mpz_vt):<> ulint
  = "atslib_mpz_get_ulint"

fun mpz_get_double (x: &mpz_vt):<> double
  = "atslib_mpz_get_double"

fun mpz_get_str
  {i:int | 2 <= i; i <= 36} (base: int i, x: &mpz_vt): String
  = "atslib_mpz_get_str"

(* ****** ****** *)

symintr mpz_set

// [x] := [y]
fun mpz_set_mpz (x: &mpz_vt, y: &mpz_vt):<> void
  = "atslib_mpz_set_mpz"

// [x] := [y]
fun mpz_set_int (x: &mpz_vt, y: int):<> void
  = "atslib_mpz_set_int"

// [x] := [y]
fun mpz_set_lint (x: &mpz_vt, y: lint):<> void
  = "atslib_mpz_set_lint"

// [x] := [y]
fun mpz_set_uint (x: &mpz_vt, y: uint):<> void
  = "atslib_mpz_set_uint"

// [x] := [y]
fun mpz_set_ulint (x: &mpz_vt, y: ulint):<> void
  = "atslib_mpz_set_ulint"

// [x] := [y]
fun mpz_set_double (x: &mpz_vt, y: double):<> void
  = "atslib_mpz_set_double"

// [x] := [y]
fun mpz_set_mpq (x: &mpz_vt, y: &mpq_vt):<> void
  = "atslib_mpz_set_mpq"

// [x] := [y]
fun mpz_set_mpf (x: &mpz_vt, y: &mpf_vt):<> void
  = "atslib_mpz_set_mpf"

// the function returns 0 if the string is valid, or -1 otherwise.
fun mpz_set_str_err {i:int | 2 <= i; i <= 62}
  (x: &mpz_vt, s: string, base: int i):<> int
  = "atslib_mpz_set_str_err"

fun mpz_set_str {i:int | 2 <= i; i <= 62}
  (x: &mpz_vt, s: string, base: int i):<> void
  = "atslib_mpz_set_str"

overload mpz_set with mpz_set_mpz
overload mpz_set with mpz_set_uint
overload mpz_set with mpz_set_int
overload mpz_set with mpz_set_double
overload mpz_set with mpz_set_mpq
overload mpz_set with mpz_set_mpf
overload mpz_set with mpz_set_str

(* ****** ****** *)

symintr mpz_init_set

// [x] := [y]
fun mpz_init_set_mpz (x: &mpz_vt? >> mpz_vt, y: &mpz_vt):<> void
  = "atslib_mpz_init_set_mpz"

// [x] := [y]
fun mpz_init_set_int (x: &mpz_vt? >> mpz_vt, y: int):<> void
  = "atslib_mpz_init_set_int"

// [x] := [y]
fun mpz_init_set_lint (x: &mpz_vt? >> mpz_vt, y: lint):<> void
  = "atslib_mpz_init_set_lint"

// [x] := [y]
fun mpz_init_set_uint (x: &mpz_vt? >> mpz_vt, y: uint):<> void
  = "atslib_mpz_init_set_uint"

// [x] := [y]
fun mpz_init_set_ulint (x: &mpz_vt? >> mpz_vt, y: ulint):<> void
  = "atslib_mpz_init_set_ulint"

// [x] := [y]
fun mpz_init_set_double (x: &mpz_vt? >> mpz_vt, y: double):<> void
  = "atslib_mpz_init_set_double"

// [x] := [y]
fun mpz_init_set_mpq (x: &mpz_vt? >> mpz_vt, y: &mpq_vt):<> void
  = "atslib_mpz_init_set_mpq"

// [x] := [y]
fun mpz_init_set_mpf (x: &mpz_vt? >> mpz_vt, y: &mpf_vt):<> void
  = "atslib_mpz_init_set_mpf"

// the function returns 0 if the string is valid, or -1 otherwise.
fun mpz_init_set_str_err {i:int | 2 <= i; i <= 62}
  (x: &mpz_vt? >> mpz_vt, s: string, base: int i):<> int
  = "atslib_mpz_init_set_str_err"

// the function exits the string is invalid.
fun mpz_init_set_str {i:int | 2 <= i; i <= 62}
  (x: &mpz_vt? >> mpz_vt, s: string, base: int i):<> void
  = "atslib_mpz_init_set_str"

overload mpz_init_set with mpz_init_set_mpz
overload mpz_init_set with mpz_init_set_uint
overload mpz_init_set with mpz_init_set_int
overload mpz_init_set with mpz_init_set_double
overload mpz_init_set with mpz_init_set_mpq
overload mpz_init_set with mpz_init_set_mpf
overload mpz_init_set with mpz_init_set_str

(* ****** ****** *)

#define sixtythree 63
fun mpz_out_str_err {m:file_mode}
  (pf_mode: file_mode_lte (m, w) |
   file: &FILE m,
   base: intBtw (2, sixtythree),
   x: &mpz_vt): int
  = "atslib_mpz_out_str_err"

fun mpz_out_str {m:file_mode}
  (pf_mode: file_mode_lte (m, w) |
   file: &FILE m,
   base: intBtw (2, sixtythree),
   x: &mpz_vt): void
  = "atslib_mpz_out_str"

(* ****** ****** *)

// negation

symintr mpz_neg

// [x] := -[y]
fun mpz_neg_2 (x: &mpz_vt, y: &mpz_vt):<> void
  = "atslib_mpz_neg_2"

// [x] := -[x]
fun mpz_neg_1 (x: &mpz_vt):<> void
  = "atslib_mpz_neg_1"

overload mpz_neg with mpz_neg_2
overload mpz_neg with mpz_neg_1

// absolute value

symintr mpz_abs

// [x] := | [y] |
fun mpz_abs_2 (x: &mpz_vt, y: &mpz_vt):<> void
  = "atslib_mpz_abs_2"

// [x] := | [x] |
fun mpz_abs_1 (x: &mpz_vt):<> void
  = "atslib_mpz_abs_1"

overload mpz_abs with mpz_abs_2
overload mpz_abs with mpz_abs_1

// addition

symintr mpz_add

// [x] := [y] + [z]
fun mpz_add_mpz_3
  (x: &mpz_vt, y: &mpz_vt, z: &mpz_vt):<> void
  = "atslib_mpz_add_mpz_3"

fun mpz_add_int_3
  (x: &mpz_vt, y: &mpz_vt, z: int):<> void
  = "atslib_mpz_add_int_3"

fun mpz_add_lint_3
  (x: &mpz_vt, y: &mpz_vt, z: lint):<> void
  = "atslib_mpz_add_lint_3"

fun mpz_add_uint_3
  (x: &mpz_vt, y: &mpz_vt, z: uint):<> void
  = "atslib_mpz_add_uint_3"

fun mpz_add_ulint_3
  (x: &mpz_vt, y: &mpz_vt, z: ulint):<> void
  = "atslib_mpz_add_ulint_3"

overload mpz_add with mpz_add_mpz_3
overload mpz_add with mpz_add_int_3
overload mpz_add with mpz_add_lint_3
overload mpz_add with mpz_add_uint_3
overload mpz_add with mpz_add_ulint_3

// [x] := [x] + [y]
fun mpz_add_mpz_2 (x: &mpz_vt, y: &mpz_vt):<> void
  = "atslib_mpz_add_mpz_2"

fun mpz_add_int_2 (x: &mpz_vt, y: int):<> void
  = "atslib_mpz_add_int_2"

fun mpz_add_lint_2 (x: &mpz_vt, y: lint):<> void
  = "atslib_mpz_add_lint_2"

fun mpz_add_uint_2 (x: &mpz_vt, y: uint):<> void
  = "atslib_mpz_add_uint_2"

fun mpz_add_ulint_2 (x: &mpz_vt, y: ulint):<> void
  = "atslib_mpz_add_ulint_2"

overload mpz_add with mpz_add_mpz_2
overload mpz_add with mpz_add_int_2
overload mpz_add with mpz_add_lint_2
overload mpz_add with mpz_add_uint_2
overload mpz_add with mpz_add_ulint_2

// subtraction

symintr mpz_sub

// [x] := [y] - [z]
fun mpz_sub_mpz_3
  (x: &mpz_vt, y: &mpz_vt, z: &mpz_vt):<> void
  = "atslib_mpz_sub_mpz_3"

fun mpz_sub_int_3
  (x: &mpz_vt, y: &mpz_vt, z: int):<> void
  = "atslib_mpz_sub_int_3"

fun mpz_sub_lint_3
  (x: &mpz_vt, y: &mpz_vt, z: lint):<> void
  = "atslib_mpz_sub_lint_3"

fun mpz_sub_uint_3
  (x: &mpz_vt, y: &mpz_vt, z: uint):<> void
  = "atslib_mpz_sub_uint_3"

fun mpz_sub_ulint_3
  (x: &mpz_vt, y: &mpz_vt, z: ulint):<> void
  = "atslib_mpz_sub_ulint_3"

overload mpz_sub with mpz_sub_mpz_3
overload mpz_sub with mpz_sub_int_3
overload mpz_sub with mpz_sub_lint_3
overload mpz_sub with mpz_sub_uint_3
overload mpz_sub with mpz_sub_ulint_3

// [x] := [x] - [y]
fun mpz_sub_mpz_2 (x: &mpz_vt, y: &mpz_vt):<> void
  = "atslib_mpz_sub_mpz_2"

fun mpz_sub_int_2 (x: &mpz_vt, y: int):<> void
  = "atslib_mpz_sub_int_2"

fun mpz_sub_lint_2 (x: &mpz_vt, y: lint):<> void
  = "atslib_mpz_sub_lint_2"

fun mpz_sub_uint_2 (x: &mpz_vt, y: uint):<> void
  = "atslib_mpz_sub_uint_2"

fun mpz_sub_ulint_2 (x: &mpz_vt, y: ulint):<> void
  = "atslib_mpz_sub_ulint_2"

overload mpz_sub with mpz_sub_mpz_2
overload mpz_sub with mpz_sub_int_2
overload mpz_sub with mpz_sub_lint_2
overload mpz_sub with mpz_sub_uint_2
overload mpz_sub with mpz_sub_ulint_2

// multiplication

symintr mpz_mul

// [x] := [y] * [z]
fun mpz_mul_mpz_3
  (x: &mpz_vt, y: &mpz_vt, z: &mpz_vt):<> void
  = "atslib_mpz_mul_mpz_3"

fun mpz_mul_int_3
  (x: &mpz_vt, y: &mpz_vt, z: int):<> void
  = "atslib_mpz_mul_int_3"

fun mpz_mul_lint_3
  (x: &mpz_vt, y: &mpz_vt, z: lint):<> void
  = "atslib_mpz_mul_lint_3"

fun mpz_mul_uint_3
  (x: &mpz_vt, y: &mpz_vt, z: uint):<> void
  = "atslib_mpz_mul_uint_3"

fun mpz_mul_ulint_3
  (x: &mpz_vt, y: &mpz_vt, z: ulint):<> void
  = "atslib_mpz_mul_ulint_3"

overload mpz_mul with mpz_mul_mpz_3
overload mpz_mul with mpz_mul_int_3
overload mpz_mul with mpz_mul_lint_3
overload mpz_mul with mpz_mul_uint_3
overload mpz_mul with mpz_mul_ulint_3

// [x] := [x] * [y]
fun mpz_mul_mpz_2 (x: &mpz_vt, y: &mpz_vt):<> void
  = "atslib_mpz_mul_mpz_2"

fun mpz_mul_int_2 (x: &mpz_vt, y: int):<> void
  = "atslib_mpz_mul_int_2"

fun mpz_mul_lint_2 (x: &mpz_vt, y: lint):<> void
  = "atslib_mpz_mul_lint_2"

fun mpz_mul_uint_2 (x: &mpz_vt, y: uint):<> void
  = "atslib_mpz_mul_uint_2"

fun mpz_mul_ulint_2 (x: &mpz_vt, y: ulint):<> void
  = "atslib_mpz_mul_ulint_2"

overload mpz_mul with mpz_mul_mpz_2
overload mpz_mul with mpz_mul_int_2
overload mpz_mul with mpz_mul_lint_2
overload mpz_mul with mpz_mul_uint_2
overload mpz_mul with mpz_mul_ulint_2

// [x] := [x] * [x]
fun mpz_mul_mpz_1 (x: &mpz_vt):<> void
  = "atslib_mpz_mul_mpz_1"

overload mpz_mul with mpz_mul_mpz_1

(* ****** ****** *)

symintr mpz_tdiv_q

// [q] := [n] / [d]
fun mpz_tdiv_q_mpz_3
  (q: &mpz_vt, n: &mpz_vt, d: &mpz_vt):<> void
  = "atslib_mpz_tdiv_q_mpz_3"

fun mpz_tdiv_q_mpz_2 (x: &mpz_vt, d: &mpz_vt):<> void
  = "atslib_mpz_tdiv_q_mpz_2"

overload mpz_tdiv_q with mpz_tdiv_q_mpz_3
overload mpz_tdiv_q with mpz_tdiv_q_mpz_2

(* ****** ****** *)

symintr mpz_cmp

fun mpz_cmp_mpz (x: &mpz_vt, y: &mpz_vt):<> Sgn
  = "atslib_mpz_cmp_mpz"

fun mpz_cmp_int (x: &mpz_vt, y: int):<> Sgn
  = "atslib_mpz_cmp_int"

fun mpz_cmp_lint (x: &mpz_vt, y: lint):<> Sgn
  = "atslib_mpz_cmp_lint"

fun mpz_cmp_uint (x: &mpz_vt, y: uint):<> Sgn
  = "atslib_mpz_cmp_uint"

fun mpz_cmp_ulint (x: &mpz_vt, y: ulint):<> Sgn
  = "atslib_mpz_cmp_ulint"

overload mpz_cmp with mpz_cmp_mpz
overload mpz_cmp with mpz_cmp_int
overload mpz_cmp with mpz_cmp_lint
overload mpz_cmp with mpz_cmp_uint
overload mpz_cmp with mpz_cmp_ulint

fun mpz_sgn (x: &mpz_vt):<> Sgn = "atslib_mpz_sgn"

(* ****** ****** *)

fun fprint_mpz {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: &mpz_vt):<!exnref> void
  = "atslib_fprint_mpz"
overload fprint with fprint_mpz

fun print_mpz (x: &mpz_vt) :<!ref> void
  = "atslib_print_mpz"
fun prerr_mpz (x: &mpz_vt) :<!ref> void
  = "atslib_prerr_mpz"

overload print with print_mpz
overload prerr with prerr_mpz

fun tostring_mpz (x: &mpz_vt):<> String
  = "atslib_tostring_mpz"

overload tostring with tostring_mpz

(* ****** ****** *)

(* end of [gmp.sats] *)
