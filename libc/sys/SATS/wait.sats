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

fun wait (status: &int? >> int): pid_t = "atslib_wait"

(* ****** ****** *)

abst@ype waitopt_t = $extype "ats_int_type"

macdef WNOHANG = $extval (waitopt_t, "WNOHANG")
macdef WUNTRACED = $extval (waitopt_t, "WUNTRACED")

macdef WNONE = $extval (waitopt_t, "0") // default value for [waitopt_t]

fun lor_waitopt_waitopt (opt1: waitopt_t, opt2: waitopt_t): waitopt_t
overload lor with lor_waitopt_waitopt

fun waitpid
  (chldpid: pid_t, status: &int? >> int, options: waitopt_t): pid_t
  = "atslib_waitpid"

(* ****** ****** *)

(* end of [wait.sats] *)