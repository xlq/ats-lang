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
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
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

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2010
//

(* ****** ****** *)

//
// HX-2010-02-27: only need for individual testing
// staload "contrib/glib/SATS/glib/gtypes.sats"
//

(* ****** ****** *)

%{#
#include "contrib/glib/CATS/glib/gbasics.cats"
%} // end of [%{#]

(* ****** ****** *)

macdef GTRUE = $extval (gboolean, "TRUE")
macdef GFALSE = $extval (gboolean, "FALSE")

castfn bool_of_gboolean {b:bool} (b: gboolean b):<> bool b
overload bool_of with bool_of_gboolean

symintr gboolean
castfn gboolean_of_bool0 (b: bool):<> gboolean
overload gboolean with gboolean_of_bool0
castfn gboolean_of_bool1 {b:bool} (b: bool b):<> gboolean b
overload gboolean with gboolean_of_bool1

(* ****** ****** *)

castfn char_of_gchar {c:char} (c: gchar c):<> char c
overload char_of with char_of_gchar

symintr gchar
castfn gchar_of_char0 (c: char):<> gchar
overload gchar with gchar_of_char0
castfn gchar_of_char1 {c:char} (c: char c):<> gchar c
overload gchar with gchar_of_char1

(* ****** ****** *)

castfn int_of_gint {i:int} (i: gint i):<> int i
overload int_of with int_of_gint

symintr gint
castfn gint_of_int0 (i: int):<> gint
overload gint with gint_of_int0
castfn gint_of_int1 {i:int} (i: int i):<> gint i
overload gint with gint_of_int1

(* ****** ****** *)

castfn uint_of_guint {i:nat} (i: guint i):<> uint i
overload uint_of with uint_of_guint

symintr guint
//
castfn guint_of_uint0 (i: uint):<> guint
overload guint with guint_of_uint0
castfn guint_of_uint1 {i:nat} (i: uint i):<> guint i
overload guint with guint_of_uint1
//
castfn guint_of_int1 {i:nat} (i: int i):<> guint i
overload guint with guint_of_int1

(* ****** ****** *)

symintr guint8
castfn guint8_of_uint (i: uint):<> guint8
overload guint8 with guint8_of_uint

symintr guint16
castfn guint16_of_uint (i: uint):<> guint16
overload guint16 with guint16_of_uint

symintr guint32
castfn guint32_of_uint (i: uint):<> guint32
overload guint32 with guint32_of_uint

(* ****** ****** *)

castfn float_of_gfloat (x: gfloat):<> float
overload float_of with float_of_gfloat

symintr gfloat
castfn gfloat_of_float (x: float):<> gfloat
overload gfloat with gfloat_of_float
castfn gfloat_of_double (x: double):<> gfloat
overload gfloat with gfloat_of_double
castfn gfloat_of_int (x: int):<> gfloat
overload gfloat with gfloat_of_int

(* ****** ****** *)

castfn double_of_gdouble (x: gdouble):<> double
overload double_of with double_of_gdouble

symintr gdouble
castfn gdouble_of_double (x: double):<> gdouble
overload gdouble with gdouble_of_double
castfn gdouble_of_int (x: int):<> gdouble
overload gdouble with gdouble_of_int

(* ****** ****** *)

typedef lt (a:t@ype) = (a, a) -<> bool
typedef lte (a:t@ype) = (a, a) -<> bool
typedef gt (a:t@ype) = (a, a) -<> bool
typedef gte (a:t@ype) = (a, a) -<> bool
typedef eq (a:t@ype) = (a, a) -<> bool
typedef neq (a:t@ype) = (a, a) -<> bool

(* ****** ****** *)

fun lt_gint_gint : lt (gint) = "atsctrb_lt_gint_gint"
overload < with lt_gint_gint
fun lte_gint_gint : lte (gint) = "atsctrb_lte_gint_gint"
overload <= with lte_gint_gint

fun gt_gint_gint : gt (gint) = "atsctrb_gt_gint_gint"
overload > with gt_gint_gint
fun gte_gint_gint : gte (gint) = "atsctrb_gte_gint_gint"
overload >= with gte_gint_gint

fun eq_gint_gint : eq (gint) = "atsctrb_eq_gint_gint"
overload = with eq_gint_gint
fun neq_gint_gint : neq (gint) = "atsctrb_neq_gint_gint"
overload <> with neq_gint_gint

(* ****** ****** *)

fun lt_gint32_gint32 : lt (gint32) = "atsctrb_lt_gint32_gint32"
overload < with lt_gint32_gint32
fun lte_gint32_gint32 : lte (gint32) = "atsctrb_lte_gint32_gint32"
overload <= with lte_gint32_gint32

fun gt_gint32_gint32 : gt (gint32) = "atsctrb_gt_gint32_gint32"
overload > with gt_gint32_gint32
fun gte_gint32_gint32 : gte (gint32) = "atsctrb_gte_gint32_gint32"
overload >= with gte_gint32_gint32

fun eq_gint32_gint32 : eq (gint32) = "atsctrb_eq_gint32_gint32"
overload = with eq_gint32_gint32
fun neq_gint32_gint32 : neq (gint32) = "atsctrb_neq_gint32_gint32"
overload <> with neq_gint32_gint32

(* ****** ****** *)

fun lt_guint32_guint32 : lt (guint32) = "atsctrb_lt_guint32_guint32"
overload < with lt_guint32_guint32
fun lte_guint32_guint32 : lte (guint32) = "atsctrb_lte_guint32_guint32"
overload <= with lte_guint32_guint32

fun gt_guint32_guint32 : gt (guint32) = "atsctrb_gt_guint32_guint32"
overload > with gt_guint32_guint32
fun gte_guint32_guint32 : gte (guint32) = "atsctrb_gte_guint32_guint32"
overload >= with gte_guint32_guint32

fun eq_guint32_guint32 : eq (guint32) = "atsctrb_eq_guint32_guint32"
overload = with eq_guint32_guint32
fun neq_guint32_guint32 : neq (guint32) = "atsctrb_neq_guint32_guint32"
overload <> with neq_guint32_guint32

(* ****** ****** *)

symintr gsize

castfn gsize_of_int1 {i:nat} (i: int i):<> gsize i
overload gsize with gsize_of_int1

castfn gsize_of_uint0 (i: uint):<> gsize
overload gsize with gsize_of_uint0
castfn gsize_of_uint1 {i:nat} (i: uint i):<> gsize i
overload gsize with gsize_of_uint1

castfn gsize_of_size0 (i: size_t):<> gsize
overload gsize with gsize_of_size0
castfn gsize_of_size1 {i:nat} (i: size_t i):<> gsize i
overload gsize with gsize_of_size1

(* ****** ****** *)

symintr gssize

castfn gssize_of_int0 (i: int):<> gssize
overload gssize with gssize_of_int0
castfn gssize_of_int1 {i:int} (i: int i):<> gssize i
overload gssize with gssize_of_int1

castfn gssize_of_size0 (i: size_t):<> gssize
overload gssize with gssize_of_size0
castfn gssize_of_size1 {i:nat} (i: size_t i):<> gssize i
overload gssize with gssize_of_size1

castfn gssize_of_ssize0 (i: ssize_t):<> gssize
overload gssize with gssize_of_ssize0
castfn gssize_of_ssize1 {i:int} (i: ssize_t i):<> gssize i
overload gssize with gssize_of_ssize1

(* ****** ****** *)

symintr gpointer
castfn gpointer_of_type {a:type} (x: a):<> gpointer
overload gpointer with gpointer_of_type

symintr gpointer_vt
castfn gpointer_of_viewtype {a:viewtype} (x: !a):<> gpointer
overload gpointer_vt with gpointer_of_viewtype

fun GPOINTER_TO_INT
  (x: gpointer): gint = "#atsctrb_GPOINTER_TO_INT"
// end of [GPOINTER_TO_INT]

fun GINT_TO_POINTER
  (x: gint): gpointer = "#atsctrb_GINT_TO_POINTER"
// end of [GINT_TO_POINTER]

(* ****** ****** *)

absviewtype gstring (l:addr)
viewtypedef gstring0 = [l:agez] gstring l
viewtypedef gstring1 = [l:addr | l > null] gstring l
castfn ptr_of_gstring {l:addr} (x: gstring l):<> ptr l

(* ****** ****** *)

(* end of [gbasics.sats] *)
