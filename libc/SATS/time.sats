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
#include "libc/CATS/time.cats"
%} // end of [%{#]

(* ****** ****** *)

staload TYPES = "libc/sys/SATS/types.sats"

(* ****** ****** *)

typedef tm_struct =
  $extype_struct "ats_tm_struct_type" of {
  tm_sec= int (* seconds *)
, tm_min= int (* minutes *)
, tm_hour= int (* hours *)
, tm_mday= int (* day of the month *)
, tm_mon= int (* month *)
, tm_year= int (* year *)
, tm_wday= int (* day of the week *)
, tm_yday= int (* day in the year *)
, tm_isdst= int (* daylight saving time *)
} // end of [tm_struct]

(* ****** ****** *)

typedef time_t = $TYPES.time_t
//
// HX: these are implemented in libc/sys/CATS/types.cats
//
fun lint_of_time (t: time_t):<> lint = "atslib_lint_of_time"
overload lint_of with lint_of_time
fun double_of_time (t: time_t):<> double = "atslib_double_of_time"
overload double_of with double_of_time

(* ****** ****** *)

fun difftime
  (finish: time_t, start: time_t):<> double = "#atslib_difftime"
// end of [difftime]

(* ****** ****** *)

(*
** HX (2010-01-15):
** These functions are now kept for backward compatibility
*)
fun tm_get_sec
  (tm: &tm_struct): int = "atslib_tm_get_sec"
fun tm_get_min
  (tm: &tm_struct): int = "atslib_tm_get_min"
fun tm_get_hour
  (tm: &tm_struct): int = "atslib_tm_get_hour"
fun tm_get_mday
  (tm: &tm_struct): int = "atslib_tm_get_mday"
fun tm_get_mon
  (tm: &tm_struct): int = "atslib_tm_get_mon"
fun tm_get_year
  (tm: &tm_struct): int = "atslib_tm_get_year"
fun tm_get_wday
  (tm: &tm_struct): int = "atslib_tm_get_wday"
fun tm_get_yday
  (tm: &tm_struct): int = "atslib_tm_get_yday"
fun tm_get_isdst
  (tm: &tm_struct): int = "atslib_tm_get_isdst"

(* ****** ****** *)

symintr time

fun time_get (): time_t = "atslib_time_get"
overload time with time_get

fun time_get_and_set // HX:  this is not really useful!!!
  (p: &time_t? >> time_t): time_t = "atslib_time_get_and_set"
overload time with time_get_and_set

(* ****** ****** *)

// non-reentrant
fun ctime (t: &time_t):<!ref>
  [l:addr] (strptr l -<lin,prf> void | strptr l) = "#atslib_ctime"
// end of [ctime]

#define CTIME_BUFLEN 26
dataview ctime_v (m:int, l:addr, addr) =
  | {l>null} ctime_v_succ (m, l, l) of strbuf (m, CTIME_BUFLEN - 1) @ l
  | ctime_v_fail (m, l, null) of b0ytes (m) @ l
fun ctime_r // reentrant
  {m:int | m >= CTIME_BUFLEN} {l:addr} (
    pf: ! b0ytes (m) @ l >> ctime_v (m, l, l1)
  | t: &time_t, p_buf: ptr l
  ) :<> #[l1:addr] ptr l1 = "#atslib_ctime_r"
// end of [ctime_r]

(* ****** ****** *)

// [localtime] is non-reentrant
fun localtime (time: &time_t):<!ref>
  [l:addr] (ptroutopt (tm_struct, l) | ptr l) = "#atslib_localtime"
// end of [localtime]

// [localtime_r] is reentrant
fun localtime_r (
    time: &time_t, tm: &tm_struct? >> opt (tm_struct, l > null)
  ) :<> #[l:addr] ptr l = "#atslib_localtime_r"
// end of [localtime_r]

(* ****** ****** *)

// [gmtime] is non-reentrant
fun gmtime (time: &time_t):<!ref>
  [l:addr] (ptroutopt (tm_struct, l) | ptr l) = "#atslib_gmtime"
// end of [gmtime]

// [gmtime_r] is reentrant
fun gmtime_r (
    time: &time_t, tm: &tm_struct? >> opt (tm_struct, l > null)
  ) :<> #[l:addr] ptr l = "#atslib_gmtime_r"
// end of [gmtime_r]

(* ****** ****** *)

fun mktime (tm: &tm_struct): time_t = "#atslib_mktime" // returns -1 on error

(* ****** ****** *)

fun asctime (tm: &tm_struct):<!ref>
  [l:addr] (strptr l -<lin,prf> void | strptr l) = "#atslib_asctime"
// end of [asctime]

(* ****** ****** *)

fun strftime {m:pos} {l:addr} (
    pf: !b0ytes m @ l >> strbuf (m, n) @ l
  | p: ptr l, m: size_t m, fmt: string, tm: &tm_struct
  ) :<> #[n:nat | n < m] size_t n
  = "#atslib_strftime" // this a macro!
// end of [strftime]

(* ****** ****** *)

(*
//
// HX-2010-09-26:
// the function is not in FreeBSD or Darwin;
// [getdate] sets [getdate_err] if an error occurs
//
fun getdate_err_get ():<> int = "atslib_getdate_err_get"
fun getdate_err_set (x: int):<> void = "atslib_getdate_err_set"
fun getdate (str: string):<!ref>
  [l:addr] (ptroutopt (tm_struct, l) | ptr l) = "#atslib_getdate"
// end of [getdate]
*)

//
// -D_XOPEN_SOURCE
//
fun strptime (
    str: string
  , fmt: string
  , tm: &tm_struct? >> opt (tm_struct, l > null)
  ) : #[l:addr] ptr l = "#atslib_strptime" // HX: it returns NULL on error
// end of [strptime]

(* ****** ****** *)

(*
extern int daylight ; // not in FreeBSD or Darwin
extern long int timezone ; // not in FreeBSD or Darwin
extern char *tzname[2] ; // not in FreeBSD or Darwin
*)
fun tzsset ():<!ref> void = "#atslib_tzset"

(* ****** ****** *)

typedef clock_t = $TYPES.clock_t
//
macdef CLOCKS_PER_SEC = $extval (clock_t, "CLOCKS_PER_SEC")
//
// HX: these are implemented in libc/sys/CATS/types.cats
//
fun lint_of_clock (c: clock_t):<> lint = "atslib_lint_of_clock"
overload lint_of with lint_of_clock
fun double_of_clock (c: clock_t):<> double = "atslib_double_of_clock"
overload double_of with double_of_clock
//
fun clock (): clock_t = "atslib_clock" // HX: it returns -1 on error

(* ****** ****** *)

typedef timespec_struct =
$extype_struct "ats_timespec_type" of {
  tv_sec= time_t (*seconds*)
, tv_nsec= lint (*nanoseconds*)
} // end of [timespec_struct]
typedef timespec = timespec_struct

(* ****** ****** *)

(* end of [time.sats] *)
