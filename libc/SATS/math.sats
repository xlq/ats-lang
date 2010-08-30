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

fun ceil (d: double):<> double = "atslib_ceil"
fun ceilf (f: float):<> float = "atslib_ceilf"
fun ceill (ld: ldouble):<> ldouble = "atslib_ceill"

(* ****** ****** *)

fun exp (d: double):<> double = "atslib_exp"
fun expf (f: float):<> float = "atslib_expf"
fun expl (ld: ldouble):<> ldouble = "atslib_expl"

(* ****** ****** *)

fun floor (d: double):<> double = "atslib_floor"
fun floorf (f: float):<> float = "atslib_floorf"
fun floorl (ld: ldouble):<> ldouble = "atslib_floorl"

(* ****** ****** *)

fun round (d: double):<> double = "atslib_round"
fun roundf (f: float):<> float = "atslib_roundf"
fun roundl (ld: ldouble):<> ldouble = "atslib_roundl"

(* ****** ****** *)

fun trunc (d: double):<> double = "atslib_trunc"
fun truncf (f: float):<> float = "atslib_truncf"
fun truncl (ld: ldouble):<> ldouble = "atslib_truncl"

(* ****** ****** *)

fun fmod (d1: double, d2: double):<> double = "atslib_fmod"
fun fmodf (f1: float, f2: float):<> float = "atslib_fmodf"
fun fmodl (ld1: ldouble, ld2: ldouble):<> ldouble = "atslib_fmodl"

(* ****** ****** *)
//
// HX: already available in [prelude/SATS/float.sats]
//
fun sqrt (d: double):<> double = "atslib_sqrt"
fun sqrtf (f: float):<> float = "atslib_sqrtf"
fun sqrtl (ld: ldouble):<> ldouble = "atslib_sqrtl"

fun cbrt (d: double):<> double = "atslib_cbrt"
fun cbrtf (f: float):<> float = "atslib_cbrtf"
fun cbrtl (ld: ldouble):<> ldouble = "atslib_cbrtl"

fun pow (d1: double, d2: double):<> double = "atslib_pow"
fun powf (f1: float, f2: float):<> float = "atslib_powf"
fun powl (ld1: ldouble, ld2: ldouble):<> ldouble = "atslib_powl"

(* ****** ****** *)

fun log (d: double):<> double = "atslib_log"
fun logf (f: float):<> float = "atslib_logf"
fun logl (ld: ldouble):<> ldouble = "atslib_logl"

fun log10 (d: double):<> double = "atslib_log10"
fun log10f (f: float):<> float = "atslib_log10f"
fun log10l (ld: ldouble):<> ldouble = "atslib_log10l"

(* ****** ****** *)

fun acos (d: double):<> double = "atslib_acos"
fun acosf (f: float):<> float = "atslib_acosf"
fun acosl (ld: ldouble):<> ldouble = "atslib_acosl"

fun acosh (d: double):<> double = "atslib_acosh"
fun acoshf (f: float):<> float ="atslib_acoshf"
fun acoshl (ld: ldouble):<> ldouble ="atslib_acoshl"

(* ****** ****** *)

fun asin (d: double):<> double = "atslib_asin"
fun asinf (f: float):<> float = "atslib_asinf"
fun asinl (ld: ldouble):<> ldouble = "atslib_asinl"

fun asinh (d: double):<> double = "atslib_asinh"
fun asinhf (f: float):<> float = "atslib_asinhf"
fun asinhl (ld: ldouble):<> ldouble = "atslib_asinhl"

(* ****** ****** *)

fun atan (d: double):<> double = "atslib_atan"
fun atanf (f: float):<> float = "atslib_atanf"
fun atanl (ld: ldouble):<> ldouble = "atslib_atanl"

fun atan2 (d1: double, d2: double):<> double = "atslib_atan2"
fun atan2f (f1: float, f2: float):<> float = "atslib_atan2f"
fun atan2l (ld1: ldouble, ld2: ldouble):<> ldouble = "atslib_atan2l"

(* ****** ****** *)

fun cos (d: double):<> double = "atslib_cos"
fun cosf (f: float):<> float = "atslib_cosf"
fun cosl (ld: ldouble):<> ldouble = "atslib_cosl"

fun cosh (d: double):<> double = "atslib_cosh"
fun coshf (f: float):<> float = "atslib_coshf"
fun coshl (ld: ldouble):<> ldouble = "atslib_coshl"

(* ****** ****** *)

fun sin (d: double):<> double = "atslib_sin"
fun sinf (f: float):<> float = "atslib_sinf"
fun sinl (ld: ldouble):<> ldouble = "atslib_sinl"

fun sinh (d: double):<> double = "atslib_sinh"
fun sinhf (f: float):<> float = "atslib_sinhf"
fun sinhl (ld: ldouble):<> ldouble = "atslib_sinhl"

(* ****** ****** *)

fun tan (d: double):<> double = "atslib_tan"
fun tanf (f: float):<> float = "atslib_tanf"
fun tanl (ld: ldouble):<> ldouble = "atslib_tanl"

fun tanh (d: double):<> double = "atslib_tanh"
fun tanhf (f: float):<> float = "atslib_tanhf"
fun tanhl (ld: ldouble):<> ldouble = "atslib_tanhl"

(* ****** ****** *)

fun isinf (d: double):<> int = "atslib_isinf"
fun isnan (d: double):<> int = "atslib_isnan"

(* ****** ****** *)

(* end of [math.sats] *)
