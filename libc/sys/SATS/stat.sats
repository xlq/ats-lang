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

%{#

#include "libc/sys/CATS/stat.cats"

%}

(* ****** ****** *)

fun lor_mode_mode (m1: mode_t, m2: mode_t): mode_t
  = "atslib_lor_mode_mode"

overload lor with lor_mode_mode

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

fun chmod_err (path: string, mode: mode_t): int = "atslib_chmod_err"
fun chmod_exn (path: string, mode: mode_t): void = "atslib_chmod_exn"

(* ****** ****** *)

fun mkdir_err (path: string, mode: mode_t): int = "atslib_mkdir_err"
fun mkdir_exn (path: string, mode: mode_t): void = "atslib_mkdir_exn"

(* ****** ****** *)

(* end of [stat.sats] *)
