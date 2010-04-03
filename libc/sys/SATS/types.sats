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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)  *)

(* ****** ****** *)

%{#

#include "libc/sys/CATS/types.cats"

%}

abst@ype blksize_t = $extype "ats_blksize_type" // I/O block size

abst@ype blkcnt_t = $extype "ats_blkcnt_type" // number of blocks allowed

abst@ype clock_t = $extype "ats_clock_type" // for CLOCKS_PER_SEC

abst@ype clockid_t = $extype "ats_clockid_type" // for clock ID type

(* ****** ****** *)

abst@ype dev_t = $extype "ats_dev_type" // for device IDs

fun eq_dev_dev (x1: dev_t, x2: dev_t): bool = "atslib_eq_dev_dev"
overload = with eq_dev_dev

(* ****** ****** *)

abst@ype fsblkcnt_t = $extype "ats_fsblkcnt_type" // file system block counts
abst@ype fsfilcnt_t = $extype "ats_fsfilcnt_type" // file system file counts

abst@ype gid_t = $extype "ats_gid_type" // for group IDs

(* ****** ****** *)

abst@ype ino_t = $extype "ats_ino_type" // for file serial numbers

fun eq_ino_ino (x1: ino_t, x2: ino_t): bool = "atslib_eq_ino_ino"
overload = with eq_ino_ino

(* ****** ****** *)

abst@ype key_t = $extype "ats_key_type" // for XSI interprocess communication

(* ****** ****** *)

abst@ype mode_t = $extype "ats_mode_type" // file mode

fun lor_mode_mode
  (m1: mode_t, m2: mode_t): mode_t = "atslib_lor_mode_mode"
overload lor with lor_mode_mode

(* ****** ****** *)

abst@ype nlink_t = $extype "ats_nlink_type" // number of hard links to a file

(* ****** ****** *)

abst@ype whence_t = $extype "ats_int_type"

macdef SEEK_SET = $extval (whence_t, "SEEK_SET")
macdef SEEK_CUR = $extval (whence_t, "SEEK_CUR")
macdef SEEK_END = $extval (whence_t, "SEEK_END")

(* ****** ****** *)

abst@ype off_t = $extype "ats_off_type" // file size in bytes

fun off_of_lint (li: lint):<> off_t = "atslib_off_of_lint"
fun lint_of_off (off: off_t):<> lint = "atslib_lint_of_off"

(* ****** ****** *)

// for process IDs // a signed integer type
abst@ype pid_t = $extype "ats_pid_type"
fun pid_of_int (i: int):<> pid_t = "atslib_pid_of_int"
fun int_of_pid (pid: pid_t):<> int = "atslib_int_of_pid"
fun lint_of_pid (pid: pid_t):<> lint = "atslib_lint_of_pid"

(* ****** ****** *)

abst@ype size_t = $extype "ats_size_type" // for sizes of objects
abst@ype ssize_t = $extype "ats_ssize_type" // for sizes or error indication

abst@ype time_t = $extype "ats_time_type" // for time in seconds

abst@ype timer_t = $extype "ats_timer_type" // for timers returned by timer_create ()

(******* ****** *)

abst@ype uid_t = $extype "ats_uid_type" // for user IDs
fun int_of_uid (uid: uid_t):<> int = "atslib_int_of_uid"
fun uid_of_int (int: int):<> uid_t = "atslib_uid_of_int"

(******* ****** *)

abst@ype useconds_t = $extype "ats_useconds_type" // for time in microseconds

(* ****** ****** *)

(* end of [types.sats] *)
