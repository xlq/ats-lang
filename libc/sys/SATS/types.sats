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
 * along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
 * Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
 * 02110-1301, USA.
 *
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

abst@ype dev_t = $extype "ats_dev_type" // for device IDs

abst@ype fsblkcnt_t = $extype "ats_fsblkcnt_type" // file system block counts
abst@ype fsfilcnt_t = $extype "ats_fsfilcnt_type" // file system file counts

abst@ype gid_t = $extype "ats_gid_type" // for group IDs

abst@ype ino_t = $extype "ats_ino_type" // for file serial numbers

abst@ype key_t = $extype "ats_key_type" // for XSI interprocess communication

abst@ype mode_t = $extype "ats_mode_type" // file mode

abst@ype nlink_t = $extype "ats_nlink_type" // number of hard links to a file

abst@ype off_t = $extype "ats_off_type" // file size in bytes

(* ****** ****** *)
abst@ype pid_t = $extype "ats_pid_type" // for process IDs // a signed integer type
fun int_of_pid (pid: pid_t): int = "atslib_int_of_pid"

(* ****** ****** *)

abst@ype size_t = $extype "ats_size_type" // for sizes of objects
abst@ype ssize_t = $extype "ats_ssize_type" // for sizes or error indication

abst@ype time_t = $extype "ats_time_type" // for time in seconds

abst@ype timer_t = $extype "ats_timer_type" // for timers returned by timer_create ()

abst@ype uid_t = $extype "ats_uid_type" // for user IDs

abst@ype useconds_t = $extype "ats_useconds_type" // for time in microseconds

(* ****** ****** *)

(* end of [types.sats] *)
