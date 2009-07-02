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

// single precision
abst@ype zcmplx_t0ype = $extype "ats_fcomplex_type"
typedef zcmplx = zcmplx_t0ype

// double precision
abst@ype ccmplx_t0ype = $extype "ats_dcomplex_type"
typedef ccmplx = ccmplx_t0ype

(* ****** ****** *)

symintr ccmplx_of

(* ****** ****** *)

val ccmplx_imag_unit : ccmplx
  = "atslib_ccmplx_imag_unit" // imaginary unit
// end of [val]  

fun ccmplx_of_int (i: int):<> ccmplx
  = "atslib_ccmplx_of_int"

fun ccmplx_of_double (d: double):<> ccmplx
  = "atslib_ccmplx_of_double"

overload ccmplx_of with ccmplx_of_int
overload ccmplx_of with ccmplx_of_double

fun ccmplx_make_cart (d1: double, d2: double):<> ccmplx
  = "atslib_ccmplx_make_cart"

fun ccmplx_make_polar (d1: double, d2: double):<> ccmplx
  = "atslib_ccmplx_make_polar"

fun ccmplx_real (c: ccmplx):<> double
  = "atslib_ccmplx_real"

fun ccmplx_imag (c: ccmplx):<> double
  = "atslib_ccmplx_imag"

(* ****** ****** *)

fun abs_ccmplx (c: ccmplx):<> double
  = "atslib_abs_ccmplx"

fun neg_ccmplx (c: ccmplx):<> ccmplx
  = "atslib_neg_ccmplx"

overload abs with abs_ccmplx
overload ~ with neg_ccmplx

fun add_ccmplx_ccmplx (c1: ccmplx, c2: ccmplx):<> ccmplx
  = "atslib_add_ccmplx_ccmplx"

and sub_ccmplx_ccmplx (c1: ccmplx, c2: ccmplx):<> ccmplx
  = "atslib_sub_ccmplx_ccmplx"

and mul_ccmplx_ccmplx (c1: ccmplx, c2: ccmplx):<> ccmplx
  = "atslib_mul_ccmplx_ccmplx"

and div_ccmplx_ccmplx (c1: ccmplx, c2: ccmplx):<> ccmplx
  = "atslib_div_ccmplx_ccmplx"

overload + with add_ccmplx_ccmplx
overload - with sub_ccmplx_ccmplx
overload * with mul_ccmplx_ccmplx
overload / with div_ccmplx_ccmplx

fun sqrt_ccmplx (c: ccmplx):<> ccmplx
  = "atslib_sqrt_ccmplx"

fun cbrt_ccmplx (c: ccmplx):<> ccmplx
  = "atslib_cbrt_ccmplx"

overload sqrt with sqrt_ccmplx
overload cbrt with cbrt_ccmplx

(* ****** ****** *)

fun arg_ccmplx (c: ccmplx):<> double
  = "atslib_arg_ccmplx"

fun conj_ccmplx (c: ccmplx):<> ccmplx
  = "atslib_conj_ccmplx"

(* ****** ****** *)

fun exp_ccmplx (c: ccmplx):<> ccmplx
  = "atslib_exp_ccmplx"

fun log_ccmplx (c: ccmplx):<> ccmplx
  = "atslib_log_ccmplx"

fun pow_ccmplx_ccmplx (c1: ccmplx, c2: ccmplx):<> ccmplx

(* ****** ****** *)

fun fprint_ccmplx {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: ccmplx):<!exnref> void
  = "atspre_fprint_ccmplx"

fun print_ccmplx (c: ccmplx):<!ref> void = "atspre_print_ccmplx"
and prerr_ccmplx (c: ccmplx):<!ref> void = "atspre_prerr_ccmplx"

overload fprint with fprint_ccmplx
overload print with print_ccmplx
overload prerr with prerr_ccmplx

(* ****** ****** *)

(* end of [complex.sats] *)
