(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Power of Types!
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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)  *)

(* ****** ****** *)

staload "libc/sys/SATS/types.sats"

(* ****** ****** *)

%{#

#include "libc/sys/CATS/wait.cats"

%}

(* ****** ****** *)

absprop WIFEXITED_p (s: int, i: int)

fun WIFEXITED {s:int}
  (status: int s): [i:int] (WIFEXITED_p (s, i) | int i)
  = "atslib_WIFEXITED"

fun WEXITSTATUS {s:int}
  {i:int | i <> 0} (pf: WIFEXITED_p (s, i) | status: int s): int
  = "atslib_WEXITSTATUS"

(* ****** ****** *)

absprop WIFSIGNALED_p (s: int, i: int)

fun WIFSIGNALED {s:int}
  (status: int s): [i:int] (WIFSIGNALED_p (s, i) | int i)
  = "atslib_WIFSIGNALED"

fun WTERMSIG {s:int}
  {i:int | i <> 0} (pf: WIFSIGNALED_p (s, i) | status: int s): int
  = "atslib_WTERMSIG"

(* ****** ****** *)

absprop WIFSTOPPED_p (s: int, i: int)

fun WIFSTOPPED {s:int}
  (status: int s): [i:int] (WIFSTOPPED_p (s, i) | int i)
  = "atslib_WIFSTOPPED"

fun WSTOPSIG {s:int}
  {i:int | i <> 0} (pf: WIFSTOPPED_p (s, i) | status: int s): int
  = "atslib_WSTOPSIG"

(* ****** ****** *)

fun wait (status: &Int? >> Int): pid_t = "atslib_wait"

(* ****** ****** *)

abst@ype waitopt_t = $extype "ats_int_type"

macdef WNOHANG = $extval (waitopt_t, "WNOHANG")
macdef WUNTRACED = $extval (waitopt_t, "WUNTRACED")
macdef WNONE = $extval (waitopt_t, "0") // default value for [waitopt_t]

(* ****** ****** *)

fun lor_waitopt_waitopt (opt1: waitopt_t, opt2: waitopt_t): waitopt_t
overload lor with lor_waitopt_waitopt

fun waitpid
  (chldpid: pid_t, status: &int? >> int, options: waitopt_t): pid_t
  = "atslib_waitpid"

(* ****** ****** *)

(* end of [wait.sats] *)
