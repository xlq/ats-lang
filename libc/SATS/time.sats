(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
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

staload TYPES = "libc/sys/SATS/types.sats"

(* ****** ****** *)

%{#

#include "libc/CATS/time.cats"

%}

(* ****** ****** *)

abst@ype tm_struct = $extype "ats_tm_struct_type"

typedef time_t = $TYPES.time_t
typedef clock_t = $TYPES.clock_t

(* ****** ****** *)

fun lint_of_time_t (t: time_t):<> int_long_t0ype
  = "atslib_lint_of_time_t"

overload lint_of with lint_of_time_t

fun double_of_time_t (t: time_t):<> double_t0ype
  = "atslib_double_of_time_t"

overload double_of with double_of_time_t

//

symintr time

fun tm_sec_get (tm: &tm_struct): int
  = "atslib_tm_sec_get"

fun tm_min_get (tm: &tm_struct): int
  = "atslib_tm_min_get"

fun tm_hour_get (tm: &tm_struct): int
  = "atslib_tm_hour_get"

fun tm_mday_get (tm: &tm_struct): int
  = "atslib_tm_mday_get"

fun tm_mon_get (tm: &tm_struct): int
  = "atslib_tm_mon_get"

fun tm_year_get (tm: &tm_struct): int
  = "atslib_tm_year_get"

fun tm_wday_get (tm: &tm_struct): int
  = "atslib_tm_wday_get"

fun tm_yday_get (tm: &tm_struct): int
  = "atslib_tm_yday_get"

fun tm_isdst_get (tm: &tm_struct): int
  = "atslib_tm_isdst_get"

//

fun time_get (): time_t = "atslib_time_get"
fun time_get_and_set (p: &time_t? >> time_t): time_t
  = "atslib_time_get_and_set"

overload time with time_get
overload time with time_get_and_set

(* ****** ****** *)

// non-reentrant
fun ctime (t: &time_t):<!ref> string = "atslib_ctime"

#define CTIME_BUFLEN 26
fun ctime_r {n:nat | n >= CTIME_BUFLEN} {l:addr} ( // reentrant
    pf: ! @[byte?][n] @ l >> strbuf (n, CTIME_BUFLEN - 1) @ l
  | t: &time_t, p_buf: ptr l
  ) :<> ptr l
  = "atslib_ctime_r"

(* ****** ****** *)

fun difftime (finish: time_t, start: time_t):<> double
  = "atslib_difftime"

(* ****** ****** *)

// [localtime] is non-reentrant
fun localtime (time: &time_t):<!ref> ref (tm_struct)
  = "atslib_localtime"

// [localtime_r] is reentrant
fun localtime_r (time: &time_t, tm: &tm_struct? >> tm_struct): void
  = "atslib_localtime_r"

(* ****** ****** *)

fun lint_of_clock (c: clock_t):<> int_long_t0ype
  = "atslib_lint_of_clock"

overload lint_of with lint_of_clock

fun double_of_clock (c: clock_t):<> double_t0ype
  = "atslib_double_of_clock"

overload double_of with double_of_clock

//

macdef CLOCKS_PER_SEC = $extval (clock_t, "CLOCKS_PER_SEC")

//

fun clock (): clock_t = "atslib_clock"

(* ****** ****** *)

(* end of [time.sats] *)
