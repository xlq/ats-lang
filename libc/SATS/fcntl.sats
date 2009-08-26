(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
**
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

#include "libc/CATS/fcntl.cats"

%}

(* ****** ****** *)

staload TYPES = "libc/sys/SATS/types.sats"
typedef mode_t = $TYPES.mode_t

(* ****** ****** *)

datasort open_flag =
  | open_flag_rd (* read *)
  | open_flag_wr (* write *)
  | open_flag_rdwr (* read and write *)

stadef rd = open_flag_rd
stadef wr = open_flag_wr
stadef rdwr = open_flag_rdwr

(* ****** ****** *)

absprop open_flag_lte (open_flag, open_flag)

praxi open_flag_lte_refl {f:open_flag} (): open_flag_lte (f, f)

prval open_flag_lte_rd_rd : open_flag_lte (rd, rd)
prval open_flag_lte_wr_wr : open_flag_lte (wr, wr)
prval open_flag_lte_rdwr_rdwr : open_flag_lte (rdwr, rdwr)

praxi open_flag_lte_rd_rdwr (): open_flag_lte (rdwr, rd)
praxi open_flag_lte_wr_rdwr (): open_flag_lte (rdwr, wr)

(* ****** ****** *)

abst@ype flag_t (open_flag) = $extype "ats_int_type"

macdef O_RDONLY = $extval (flag_t rd, "O_RDONLY")
macdef O_WRONLY = $extval (flag_t wr, "O_WRONLY")
macdef O_RDWR   = $extval (flag_t rdwr, "O_RDWR")

abst@ype orflag_t = $extype "ats_int_type"

macdef O_CREAT = $extval (orflag_t, "O_CREAT")
macdef O_APPEND = $extval (orflag_t, "O_APPEND")

macdef O_EXCL = $extval (orflag_t, "O_EXCL")
macdef O_NOCTTY = $extval (orflag_t, "O_NOCTTY")
macdef O_NONBLOCK = $extval (orflag_t, "O_NONBLOCK")
macdef O_SYNC = $extval (orflag_t, "O_SYNC")
macdef O_TRUNC = $extval (orflag_t, "O_TRUNC")

(*
macdef O_NDELAY
macdef O_NOFOLLOW
macdef O_DIRECTORY
macdef O_DIRECT
macdef O_ASYNC
macdef O_LARGEFILE
*)

fun lor_flag_orflag {f:open_flag}
  (f: flag_t f, orf: orflag_t): flag_t f = "atslib_lor_flag_orflag"
overload lor with lor_flag_orflag

(* ****** ****** *)

absview fildes_v (int, open_flag) // file descriptor view

(* ****** ****** *)

dataview open_v (int, open_flag) =
  | {i:nat} {f:open_flag} open_v_succ (i, f) of fildes_v (i, f)
  | {f:open_flag} open_v_fail (~1, f) of ()

fun open_flag_err {f:open_flag}
  (path: string, flag: flag_t f): [i: int] (open_v (i, f) | int i)
  = "atslib_open_flag_err"

fun open_flag_exn {f:open_flag}
  (path: string, flag: flag_t f): [i: int] (fildes_v (i, f) | int i)
  = "atslib_open_flag_exn"

fun open_flag_mode_exn {f:open_flag}
  (path: string, flag: flag_t f, mode: mode_t)
  : [i: int] (fildes_v (i, f) | int i)
  = "atslib_open_flag_mode_exn"

(* ****** ****** *)

dataview close_v (fd: int, flag: open_flag, int) =
  | close_v_succ (fd, flag,  0) of ()
  | close_v_fail (fd, flag, ~1) of fildes_v (fd, flag)

fun close_err {fd:int} {flag: open_flag}
  (pf: fildes_v (fd, flag) | fd: int fd)
  : [i:int] (close_v (fd, flag, i) | int i)
  = "atslib_close_err"

fun close_exn {fd:int} {flag: open_flag}
  (pf: fildes_v (fd, flag) | fd: int fd): void
  = "atslib_close_exn"

// implemented in [libc/DATS/fcntl.dats]
fun close_loop_err {fd:int} {flag: open_flag}
  (pf: fildes_v (fd, flag) | fd: int fd)
  :<> [i:int] (close_v (fd, flag, i) | int i)

// implemented in [libc/DATS/fcntl.dats]
fun close_loop_exn {fd:int} {flag: open_flag}
  (pf: fildes_v (fd, flag) | fd: int fd): void

(* ****** ****** *)

// implemented in [libc/CATS/fcntl.cats]

fun fildes_read_err
  {fd:int} {flag:open_flag} {n,sz:nat | n <= sz} (
    pf1: open_flag_lte (flag, rd), pf2: !fildes_v (fd, flag)
  | fd: int fd, buf: &bytes sz, ntotal: size_t n
  ) : ssizeBtw(~1, n+1)
  = "atslib_fildes_read_err"

fun fildes_read_exn
  {fd:int} {flag:open_flag} {n,sz:nat | n <= sz} (
    pf1: open_flag_lte (flag, rd), pf2: !fildes_v (fd, flag)
  | fd: int fd, buf: &bytes sz, ntotal: int n
  ) : sizeLte n
  = "atslib_fildes_read_exn"

// implemented in [libc/DATS/fcntl.dats]

fun fildes_read_loop_err
  {fd:int} {flag:open_flag} {n,sz:nat | n <= sz} (
    pf1: open_flag_lte (flag, rd), pf2: !fildes_v (fd, flag)
  | fd: int fd, buf: &bytes sz, ntotal: size_t n
  ) : ssizeBtw (~1, n+1)
  = "atslib_fildes_read_loop_err"

fun fildes_read_loop_exn
  {fd:int} {flag:open_flag} {n,sz:nat | n <= sz} (
    pf1: open_flag_lte (flag, rd), pf2: !fildes_v (fd, flag)
  | fd: int fd, buf: &bytes sz, ntotal: size_t n
  ) : sizeLte n
  = "atslib_fildes_read_loop_exn"

(* ****** ****** *)

// implemented in [libc/CATS/fcntl.cats]

fun fildes_write_err
  {fd:int} {flag:open_flag} {n,sz:nat | n <= sz} (
    pf1: open_flag_lte (flag, wr), pf2: !fildes_v (fd, flag)
  | fd: int fd, buf: &bytes sz, ntotal: size_t n
  ) : ssizeBtw(~1, n+1)
  = "atslib_fildes_write_err"

fun fildes_write_exn
  {fd:int} {flag:open_flag} {n,sz:nat | n <= sz} (
    pf1: open_flag_lte (flag, wr), pf2: !fildes_v (fd, flag)
  | fd: int fd, buf: &bytes sz, ntotal: size_t n
  ) : sizeLte n
  = "atslib_fildes_write_exn"

// implemented in [libc/DATS/fcntl.dats]

fun fildes_write_loop_err
  {fd:int} {flag:open_flag} {n,sz:nat | n <= sz} (
    pf1: open_flag_lte (flag, wr), pf2: !fildes_v (fd, flag)
  | fd: int fd, buf: &bytes sz, ntotal: size_t n
  ) : ssizeBtw(~1, n+1)
  = "atslib_fildes_write_loop_err"

fun fildes_write_loop_exn
  {fd:int} {flag:open_flag} {n,sz:nat | n <= sz} (
    pf1: open_flag_lte (flag, wr), pf2: !fildes_v (fd, flag)
  | fd: int fd, buf: &bytes sz, ntotal: size_t n
  ) : void // all bytes must be written if this function returns
  = "atslib_fildes_write_loop_exn"

(* ****** ****** *)

// implemented in [libc/CATS/fcntl.cats]

fun fildes_write_substring_err
  {fd:int} {flag:open_flag} {i,n,sz:nat | i+n <= sz} (
    pf1: open_flag_lte (flag, wr), pf2: !fildes_v (fd, flag)
  | fd: int fd, str: string sz, start: size_t i, n: size_t n
  ) : ssizeBtw(~1, n+1)
  = "atslib_fildes_write_substring_err"

fun fildes_write_substring_exn
  {fd:int} {flag:open_flag} {i,n,sz:nat | i+n <= sz} (
    pf1: open_flag_lte (flag, wr), pf2: !fildes_v (fd, flag)
  | fd: int fd, str: string sz, start: size_t i, n: size_t n
  ) : sizeLte n
  = "atslib_fildes_write_substring_exn"

(* ****** ****** *)

(* end of [fcntl.sats] *)
