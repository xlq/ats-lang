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

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#

#include "libc/CATS/complex.cats"

%}

(* ****** ****** *)

abst@ype complex = $extype "ats_dcomplex_type"

(* ****** ****** *)

symintr complex_of

(* ****** ****** *)

val complex_imag_unit : complex // imaginary unit
  = "atslib_complex_imag_unit"

fun complex_of_int (i: int):<> complex
  = "atslib_complex_of_int"

fun complex_of_double (d: double):<> complex
  = "atslib_complex_of_double"

overload complex_of with complex_of_int
overload complex_of with complex_of_double

fun complex_make_cart (d1: double, d2: double):<> complex
  = "atslib_complex_make_cart"

fun complex_make_polar (d1: double, d2: double):<> complex
  = "atslib_complex_make_polar"

fun complex_real (c: complex):<> double
  = "atslib_complex_real"

fun complex_imag (c: complex):<> double
  = "atslib_complex_imag"

(* ****** ****** *)

fun abs_complex (c: complex):<> double
  = "atslib_abs_complex"

fun neg_complex (c: complex):<> complex
  = "atslib_neg_complex"

overload abs with abs_complex
overload ~ with neg_complex

fun add_complex_complex (c1: complex, c2: complex):<> complex
  = "atslib_add_complex_complex"

and sub_complex_complex (c1: complex, c2: complex):<> complex
  = "atslib_sub_complex_complex"

and mul_complex_complex (c1: complex, c2: complex):<> complex
  = "atslib_mul_complex_complex"

and div_complex_complex (c1: complex, c2: complex):<> complex
  = "atslib_div_complex_complex"

overload + with add_complex_complex
overload - with sub_complex_complex
overload * with mul_complex_complex
overload / with div_complex_complex

fun sqrt_complex (c: complex):<> complex
  = "atslib_sqrt_complex"

fun cbrt_complex (c: complex):<> complex
  = "atslib_cbrt_complex"

overload sqrt with sqrt_complex
overload cbrt with cbrt_complex

(* ****** ****** *)

fun arg_complex (c: complex):<> double
  = "atslib_arg_complex"

fun conj_complex (c: complex):<> complex
  = "atslib_conj_complex"

(* ****** ****** *)

fun exp_complex (c: complex):<> complex
  = "atslib_exp_complex"

fun log_complex (c: complex):<> complex
  = "atslib_log_complex"

fun pow_complex_complex (c1: complex, c2: complex):<> complex

(* ****** ****** *)

fun fprint_complex {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: complex):<!exnref> void
  = "atspre_fprint_complex"

fun print_complex (c: complex):<!ref> void = "atspre_print_complex"
and prerr_complex (c: complex):<!ref> void = "atspre_prerr_complex"

overload fprint with fprint_complex
overload print with print_complex
overload prerr with prerr_complex

(* ****** ****** *)

(* end of [complex.sats] *)
