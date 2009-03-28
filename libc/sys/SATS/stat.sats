(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
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
 * along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
 * Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)  *)

(* ****** ****** *)

staload "libc/sys/SATS/types.sats"

(* ****** ****** *)

%{#

#include "libc/sys/CATS/stat.cats"

%}

(* ****** ****** *)

abst@ype stat = $extype "ats_stat_type"

(* ****** ****** *)

fun stat_st_mode_get (stbuf: &stat):<> mode_t
  = "atslib_stat_st_mode_get"

fun stat_st_size_get (stbuf: &stat):<> off_t
  = "atslib_stat_st_size_get"

(* ****** ****** *)

macdef S_IRWXU = $extval (mode_t, "S_IRWXU")
macdef S_IRUSR = $extval (mode_t, "S_IRUSR")
macdef S_IWUSR = $extval (mode_t, "S_IWUSR")
macdef S_IXUSR = $extval (mode_t, "S_IXUSR")

macdef S_IRWXG = $extval (mode_t, "S_IRWXG")
macdef S_IRGRP = $extval (mode_t, "S_IRGRP")
macdef S_IWGRP = $extval (mode_t, "S_IWGRP")
macdef S_IXGRP = $extval (mode_t, "S_IXGRP")

macdef S_IRWXO = $extval (mode_t, "S_IRWXO")
macdef S_IROTH = $extval (mode_t, "S_IROTH")
macdef S_IWOTH = $extval (mode_t, "S_IWOTH")
macdef S_IXOTH = $extval (mode_t, "S_IXOTH")

macdef S_ISUID = $extval (mode_t, "S_ISUID")
macdef S_ISGID = $extval (mode_t, "S_ISGID")
macdef S_ISVTX = $extval (mode_t, "S_ISVTX")

(* ****** ****** *)

fun S_ISBLK (m: mode_t): bool = "atslib_S_ISBLK"
fun S_ISCHR (m: mode_t): bool = "atslib_S_ISCHR"
fun S_ISDIR (m: mode_t): bool = "atslib_S_ISDIR"
fun S_ISFIFO (m: mode_t): bool = "atslib_S_ISFIFO"
fun S_ISREG (m: mode_t): bool = "atslib_S_ISREG"
fun S_ISLNK (m: mode_t): bool = "atslib_S_ISLNK"
fun S_ISSOCK (m: mode_t): bool = "atslib_S_ISSOCK"

(* ****** ****** *)

symintr chmod_err
symintr chmod_exn

fun chmod_string_err (path: string, mode: mode_t): int
  = "atslib_chmod_err"
fun chmod_string_exn (path: string, mode: mode_t): void
  = "atslib_chmod_exn"

overload chmod_err with chmod_string_err
overload chmod_exn with chmod_string_exn

(* ****** ****** *)

symintr mkdir_err
symintr mkdir_exn

fun mkdir_string_err (path: string, mode: mode_t): int
  = "atslib_mkdir_err"
fun mkdir_string_exn (path: string, mode: mode_t): void
  = "atslib_mkdir_exn"

overload mkdir_err with mkdir_string_err
overload mkdir_exn with mkdir_string_exn

(* ****** ****** *)

dataview stat_v (l:addr, int) =
  | stat_v_fail (l, ~1) of stat? @ l
  | stat_v_succ (l,  0) of stat  @ l
 
symintr stat_err
symintr stat_exn

fun stat_string_err {l:addr} (
    pf_buf: stat? @ l | name: string, p_buf: ptr l
  ) : [i:int] (stat_v (l, i) | int i)
  = "atslib_stat_err"

fun stat_string_exn (name: string, buf: &stat? >> stat): void
  = "atslib_stat_exn"

overload stat_err with stat_string_err
overload stat_exn with stat_string_exn

(* ****** ****** *)

(* end of [stat.sats] *)
