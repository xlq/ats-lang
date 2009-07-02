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

(*
** complex numbers of single precision
*)

abst@ype ccmplx_t0ype = $extype "ats_fcomplex_type"
typedef ccmplx = ccmplx_t0ype
symintr ccmplx_of

(* ****** ****** *)

val ccmplx_imag_unit : ccmplx
  = "atslib_ccmplx_imag_unit" // imaginary unit
// end of [val]  

fun ccmplx_of_int (i: int):<> ccmplx
  = "atslib_ccmplx_of_int"
overload ccmplx_of with ccmplx_of_int

fun ccmplx_of_float (f: float):<> ccmplx
  = "atslib_ccmplx_of_float"
overload ccmplx_of with ccmplx_of_float

fun ccmplx_make_cart (f1: float, f2: float):<> ccmplx
  = "atslib_ccmplx_make_cart"

fun ccmplx_make_polar (f1: float, f2: float):<> ccmplx
  = "atslib_ccmplx_make_polar"

fun ccmplx_real (c: ccmplx):<> float
  = "atslib_ccmplx_real"

fun ccmplx_imag (c: ccmplx):<> float
  = "atslib_ccmplx_imag"

(* ****** ****** *)

fun abs_ccmplx (c: ccmplx):<> float
  = "atslib_abs_ccmplx"
overload abs with abs_ccmplx

fun neg_ccmplx (c: ccmplx):<> ccmplx
  = "atslib_neg_ccmplx"
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

fun arg_ccmplx (c: ccmplx):<> float
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

(*
** complex numbers of double precision
*)

(* ****** ****** *)

abst@ype zcmplx_t0ype = $extype "ats_dcomplex_type"
typedef zcmplx = zcmplx_t0ype
symintr zcmplx_of

(* ****** ****** *)

val zcmplx_imag_unit : zcmplx
  = "atslib_zcmplx_imag_unit" // imaginary unit
// end of [val]  

fun zcmplx_of_int (i: int):<> zcmplx
  = "atslib_zcmplx_of_int"
overload zcmplx_of with zcmplx_of_int

fun zcmplx_of_double (d: double):<> zcmplx
  = "atslib_zcmplx_of_double"
overload zcmplx_of with zcmplx_of_double

fun zcmplx_make_cart (d1: double, d2: double):<> zcmplx
  = "atslib_zcmplx_make_cart"

fun zcmplx_make_polar (d1: double, d2: double):<> zcmplx
  = "atslib_zcmplx_make_polar"

fun zcmplx_real (z: zcmplx):<> double
  = "atslib_zcmplx_real"

fun zcmplx_imag (z: zcmplx):<> double
  = "atslib_zcmplx_imag"

(* ****** ****** *)

fun abs_zcmplx (z: zcmplx):<> double
  = "atslib_abs_zcmplx"
overload abs with abs_zcmplx

fun neg_zcmplx (z: zcmplx):<> zcmplx
  = "atslib_neg_zcmplx"
overload ~ with neg_zcmplx

fun add_zcmplx_zcmplx (z1: zcmplx, z2: zcmplx):<> zcmplx
  = "atslib_add_zcmplx_zcmplx"

and sub_zcmplx_zcmplx (z1: zcmplx, z2: zcmplx):<> zcmplx
  = "atslib_sub_zcmplx_zcmplx"

and mul_zcmplx_zcmplx (z1: zcmplx, z2: zcmplx):<> zcmplx
  = "atslib_mul_zcmplx_zcmplx"

and div_zcmplx_zcmplx (z1: zcmplx, z2: zcmplx):<> zcmplx
  = "atslib_div_zcmplx_zcmplx"

overload + with add_zcmplx_zcmplx
overload - with sub_zcmplx_zcmplx
overload * with mul_zcmplx_zcmplx
overload / with div_zcmplx_zcmplx

fun sqrt_zcmplx (z: zcmplx):<> zcmplx
  = "atslib_sqrt_zcmplx"

fun cbrt_zcmplx (z: zcmplx):<> zcmplx
  = "atslib_cbrt_zcmplx"

overload sqrt with sqrt_zcmplx
overload cbrt with cbrt_zcmplx

(* ****** ****** *)

fun arg_zcmplx (z: zcmplx):<> double
  = "atslib_arg_zcmplx"

fun conj_zcmplx (z: zcmplx):<> zcmplx
  = "atslib_conj_zcmplx"

(* ****** ****** *)

fun exp_zcmplx (z: zcmplx):<> zcmplx
  = "atslib_exp_zcmplx"

fun log_zcmplx (z: zcmplx):<> zcmplx
  = "atslib_log_zcmplx"

fun pow_zcmplx_zcmplx (z1: zcmplx, z2: zcmplx):<> zcmplx

(* ****** ****** *)

fun fprint_zcmplx {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: zcmplx):<!exnref> void
  = "atspre_fprint_zcmplx"

fun print_zcmplx (z: zcmplx):<!ref> void = "atspre_print_zcmplx"
and prerr_zcmplx (z: zcmplx):<!ref> void = "atspre_prerr_zcmplx"

overload fprint with fprint_zcmplx
overload print with print_zcmplx
overload prerr with prerr_zcmplx

(* ****** ****** *)

(* end of [complex.sats] *)
