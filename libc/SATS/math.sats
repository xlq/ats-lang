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
#include "libc/CATS/math.cats"
%} // end of [%{#]

(* ****** ****** *)

macdef M_E = 2.7182818284590452354	/* e */
macdef M_PI = 3.14159265358979323846	/* pi */
macdef M_PI_2 = 1.57079632679489661923	/* pi/2 */
macdef M_PI_4 = 0.78539816339744830962	/* pi/4 */

(* ****** ****** *)

fun ceil (d: double):<> double = "mac#atslib_ceil"
fun ceilf (f: float):<> float = "mac#atslib_ceilf"
fun ceill (ld: ldouble):<> ldouble = "mac#atslib_ceill"

(* ****** ****** *)

fun floor (d: double):<> double = "mac#atslib_floor"
fun floorf (f: float):<> float = "mac#atslib_floorf"
fun floorl (ld: ldouble):<> ldouble = "mac#atslib_floorl"

(* ****** ****** *)

fun round (d: double):<> double = "mac#atslib_round"
fun roundf (f: float):<> float = "mac#atslib_roundf"
fun roundl (ld: ldouble):<> ldouble = "mac#atslib_roundl"

(* ****** ****** *)

fun trunc (d: double):<> double = "mac#atslib_trunc"
fun truncf (f: float):<> float = "mac#atslib_truncf"
fun truncl (ld: ldouble):<> ldouble = "mac#atslib_truncl"

(* ****** ****** *)

fun fmod (d1: double, d2: double):<> double = "mac#atslib_fmod"
fun fmodf (f1: float, f2: float):<> float = "mac#atslib_fmodf"
fun fmodl (ld1: ldouble, ld2: ldouble):<> ldouble = "mac#atslib_fmodl"

(* ****** ****** *)
//
// HX: already available in [prelude/SATS/float.sats]
//
fun sqrt (d: double):<> double = "mac#atslib_sqrt"
fun sqrtf (f: float):<> float = "mac#atslib_sqrtf"
fun sqrtl (ld: ldouble):<> ldouble = "mac#atslib_sqrtl"

fun cbrt (d: double):<> double = "mac#atslib_cbrt"
fun cbrtf (f: float):<> float = "mac#atslib_cbrtf"
fun cbrtl (ld: ldouble):<> ldouble = "mac#atslib_cbrtl"

fun pow (d1: double, d2: double):<> double = "mac#atslib_pow"
fun powf (f1: float, f2: float):<> float = "mac#atslib_powf"
fun powl (ld1: ldouble, ld2: ldouble):<> ldouble = "mac#atslib_powl"

(* ****** ****** *)

fun exp (d: double):<> double = "mac#atslib_exp"
fun expf (f: float):<> float = "mac#atslib_expf"
fun expl (ld: ldouble):<> ldouble = "mac#atslib_expl"

(* ****** ****** *)

fun log (d: double):<> double = "mac#atslib_log"
fun logf (f: float):<> float = "mac#atslib_logf"
fun logl (ld: ldouble):<> ldouble = "mac#atslib_logl"

fun log10 (d: double):<> double = "mac#atslib_log10"
fun log10f (f: float):<> float = "mac#atslib_log10f"
fun log10l (ld: ldouble):<> ldouble = "mac#atslib_log10l"

(* ****** ****** *)

fun asin (d: double):<> double = "mac#atslib_asin"
fun asinf (f: float):<> float = "mac#atslib_asinf"
fun asinl (ld: ldouble):<> ldouble = "mac#atslib_asinl"

fun acos (d: double):<> double = "mac#atslib_acos"
fun acosf (f: float):<> float = "mac#atslib_acosf"
fun acosl (ld: ldouble):<> ldouble = "mac#atslib_acosl"

fun atan (d: double):<> double = "mac#atslib_atan"
fun atanf (f: float):<> float = "mac#atslib_atanf"
fun atanl (ld: ldouble):<> ldouble = "mac#atslib_atanl"

fun atan2 (d1: double, d2: double):<> double = "mac#atslib_atan2"
fun atan2f (f1: float, f2: float):<> float = "mac#atslib_atan2f"
fun atan2l (ld1: ldouble, ld2: ldouble):<> ldouble = "mac#atslib_atan2l"

(* ****** ****** *)

fun asinh (d: double):<> double = "mac#atslib_asinh"
fun asinhf (f: float):<> float = "mac#atslib_asinhf"
fun asinhl (ld: ldouble):<> ldouble = "mac#atslib_asinhl"

fun acosh (d: double):<> double = "mac#atslib_acosh"
fun acoshf (f: float):<> float = "mac#atslib_acoshf"
fun acoshl (ld: ldouble):<> ldouble = "mac#atslib_acoshl"

(* ****** ****** *)

fun sin (d: double):<> double = "mac#atslib_sin"
fun sinf (f: float):<> float = "mac#atslib_sinf"
fun sinl (ld: ldouble):<> ldouble = "mac#atslib_sinl"

fun cos (d: double):<> double = "mac#atslib_cos"
fun cosf (f: float):<> float = "mac#atslib_cosf"
fun cosl (ld: ldouble):<> ldouble = "mac#atslib_cosl"

fun tan (d: double):<> double = "mac#atslib_tan"
fun tanf (f: float):<> float = "mac#atslib_tanf"
fun tanl (ld: ldouble):<> ldouble = "mac#atslib_tanl"

(* ****** ****** *)

fun sinh (d: double):<> double = "mac#atslib_sinh"
fun sinhf (f: float):<> float = "mac#atslib_sinhf"
fun sinhl (ld: ldouble):<> ldouble = "mac#atslib_sinhl"

fun cosh (d: double):<> double = "mac#atslib_cosh"
fun coshf (f: float):<> float = "mac#atslib_coshf"
fun coshl (ld: ldouble):<> ldouble = "mac#atslib_coshl"

fun tanh (d: double):<> double = "mac#atslib_tanh"
fun tanhf (f: float):<> float = "mac#atslib_tanhf"
fun tanhl (ld: ldouble):<> ldouble = "mac#atslib_tanhl"

(* ****** ****** *)

fun isinf (d: double):<> int = "mac#atslib_isinf"
fun isnan (d: double):<> int = "mac#atslib_isnan"

(* ****** ****** *)

(* end of [math.sats] *)
