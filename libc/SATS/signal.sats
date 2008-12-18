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
**
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#

#include "libc/CATS/signal.cats"

%}

(* ****** ****** *)

// defined in [libc/CATS/signal.cats]
abst@ype signum_t = $extype "signum_t"

macdef SIGHUP =  $extval (signum_t, "SIGHUP") // 1
macdef SIGINT =  $extval (signum_t, "SIGINT") // 2
macdef SIGQUIT = $extval (signum_t, "SIGQUIT") // 3
macdef SIGILL = $extval (signum_t, "SIGILL") // 4
macdef SIGABRT = $extval (signum_t, "SIGABRT") // 6
macdef SIGFPE = $extval (signum_t, "SIGFPE") // 8
macdef SIGKILL = $extval (signum_t, "SIGKILL") // 9
macdef SIGSEGV = $extval (signum_t, "SIGSEGV") // 11
macdef SIGPIPE = $extval (signum_t, "SIGPIPE") // 13
macdef SIGALRM = $extval (signum_t, "SIGALRM") // 14
macdef SIGTERM = $extval (signum_t, "SIGTERM") // 15
macdef SIGUSR1 = $extval (signum_t, "SIGUSR1")
macdef SIGUSR2 = $extval (signum_t, "SIGUSR2")
macdef SIGCHLD = $extval (signum_t, "SIGCHLD")
macdef SIGCONT = $extval (signum_t, "SIGCONT")
macdef SIGSTOP = $extval (signum_t, "SIGSTOP")
macdef SIGTSTP = $extval (signum_t, "SIGTSTP")
macdef SIGTTIN = $extval (signum_t, "SIGTTIN")
macdef SIGTTOU = $extval (signum_t, "SIGTTOU")

macdef SIGBUS = $extval (signum_t, "SIGBUS")
macdef SIGTRAP = $extval (signum_t, "SIGTRAP") // 5

macdef SIGIO = $extval (signum_t, "SIGIO")

(* ****** ****** *)

// typedef sighandler_t = (signum_t) -<fun> void
abstype sighandler_t // boxed type

fun sighandler_of_fun (f: signum_t -<fun> void): sighandler_t
  = "atslib_sighandler_of_fun"

fun fun_of_sighandler (f: sighandler_t): signum_t -<fun> void
  = "atslib_fun_of_sighandler"

fun signal (signum: signum_t, f: sighandler_t): sighandler_t
  = "atslib_signal"

(* ****** ****** *)

(* end of [signal.sats] *)
