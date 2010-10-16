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
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
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
%} // end of [%{#]

(* ****** ****** *)

staload TYPES = "libc/sys/SATS/types.sats"
typedef pid_t = $TYPES.pid_t
typedef uid_t = $TYPES.uid_t
typedef clock_t = $TYPES.clock_t
staload PTHREAD = "libc/SATS/pthread.sats"
typedef pthread_t = $PTHREAD.pthread_t

(* ****** ****** *)
//
// HX: defined in [libc/CATS/signal.cats]
//
abst@ype signum_t = $extype "signum_t"
//
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
//
macdef SIGBUS = $extval (signum_t, "SIGBUS")
macdef SIGTRAP = $extval (signum_t, "SIGTRAP") // 5
//
macdef SIGIO = $extval (signum_t, "SIGIO")

(* ****** ****** *)

abstype sighandler_t // this is a boxed type
//
macdef SIG_DFL = $extval (sighandler_t, "SIG_DFL")
macdef SIG_IGN = $extval (sighandler_t, "SIG_IGN")
//
symintr sighandler
castfn sighandler_of_fun (f: signum_t -<fun1> void): sighandler_t
overload sighandler with sighandler_of_fun

(* ****** ****** *)

abst@ype sigset_t = $extype "sigset_t"
fun sigemptyset // 0/-1 : fail/succ // errno set: EINVAL
  (set: &sigset_t): int = "#atslib_sigemptyset"
// end of [sigemptyset]
fun sigfillset  // 0/-1 : fail/succ // errno set: EINVAL
  (set: &sigset_t): int = "#atslib_sigfillset"
// end of [sigfillset]
fun sigaddset   // 0/-1 : fail/succ // errno set: EINVAL
  (set: &sigset_t, sgn: signum_t): int = "#atslib_sigaddset"
// end of [sigaddset]
fun sigdelset   // 0/-1 : fail/succ // errno set: EINVAL
  (set: &sigset_t, sgn: signum_t): int = "#atslib_sigdelset"
// end of [sigdelset]

fun sigismember // 0/1/-1 : false/true/error // errno set: EINVAL
  (set: &sigset_t, sgn: signum_t): int = "#atslib_sigismember"
// end of [sigismember]

(* ****** ****** *)

abst@ype sigmaskhow_t = int

macdef SIG_BLOCK = $extval (sigmaskhow_t, "SIG_BLOCK")
macdef SIG_SETMASK = $extval (sigmaskhow_t, "SIG_SETMASK")
macdef SIG_NONBLOCK = $extval (sigmaskhow_t, "SIG_NONBLOCK")

/* ****** ****** */

fun pthread_sigmask (
  how: sigmaskhow_t
, newset: &sigset_t, oldset: &sigset_t? >> opt (sigset_t, i==0)
) : #[i:int | i <= 0] int (i) = "#atslib_pthread_sigmask"
fun pthread_sigmask_null
  (how: sigmaskhow_t, newset: &sigset_t): int = "#atslib_pthread_sigmask"
// end of [pthread_sigmask_null]

fun sigprocmask (
  how: sigmaskhow_t
, newset: &sigset_t, oldset: &sigset_t? >> opt (sigset_t, i==0)
) : #[i:int | i <= 0] int (i) = "#atslib_sigprocmask"
fun sigprocmask_null
  (how: sigmaskhow_t, newset: &sigset_t): int = "#atslib_sigprocmask"
// end of [sigprocmask_null]

(* ****** ****** *)

abst@ype sigval_t = $extype "sigval_t"
abst@ype saflag_t = uint
macdef SA_NOCLDSTOP = $extval (saflag_t, "SA_NOCLDSTOP")
macdef SA_NOCLDWAIT = $extval (saflag_t, "SA_NOCLDWAIT")
macdef SA_NODEFER = $extval (saflag_t, "SA_NODEFER")
macdef SA_ONSTACK = $extval (saflag_t, "SA_ONSTACK")
macdef SA_RESETHAND = $extval (saflag_t, "SA_RESETHAND")
macdef SA_RESTART = $extval (saflag_t, "SA_RESTART")
macdef SA_SIGINFO = $extval (saflag_t, "SA_SIGINFO")

(* ****** ****** *)

typedef siginfo_t =
$extype_struct "siginfo_t" of {
  si_signo= int // signal number
, si_sigerror= int // error value
, si_code= int // signal code
, si_trapno= int // trap number that caused HW signal
, si_pid= pid_t // proc ID of the sending process
, si_uid= uid_t // real user ID of the sending process
, si_status= int // exit value or signal
, si_utime= clock_t // user time consumed
, si_stime= clock_t // system time consumed
, si_value= sigval_t // signal value
, si_int= int // signal (POSIX.1b)
, si_ptr= ptr // signal (POSIX.1b)
, si_overrun= int // timer overrun count (POSIX.1b)
, si_timerid= int // timer ID (POSIX.1b)
, si_addr= ptr // memory location that caused fault
, si_band= int // band event
, si_fd= int // file descriptor
} // end of [siginfo_t]

(* ****** ****** *)

typedef sigaction_struct =
$extype_struct "ats_sigaction_type" of {
  sa_handler= sighandler_t
, sa_sigaction= (int, &siginfo_t, ptr) -<fun1> void
, sa_mask= sigset_t
, sa_flags= saflag_t
, sa_restorer= () -<fun1> void
} // end of [sigaction_struct]
typedef sigaction = sigaction_struct

fun sigaction (
  sgn: signum_t
, newact: &sigaction, oldact: &sigaction >> opt (sigaction, i==0)
) : #[i:int | i <= 0] int i = "#atslib_sigaction" // 0/-1 : succ/fail
fun sigaction_null
  (sgn: signum_t, newact: &sigaction): int = "#atslib_sigaction_null"
// end of [sigaction_null]

(* ****** ****** *)

fun signal
  (sgn: signum_t, f: sighandler_t): sighandler_t = "#atslib_signal"
// end of [signal]

(* ****** ****** *)

fun kill // 0/-1 : succ/fail // errno set
  (proc: pid_t, sgn: signum_t): int = "#atslib_kill"
// end of [kill]
//
// HX: killpg (pgrp, sgn) = kill (-pgrp, sgn)
//
fun killpg // 0/-1 : succ/fail // errno set
  (pgrp: pid_t, sgn: signum_t): int = "#atslib_killpg"
// end of [killpg]
fun pthread_kill // 0/errno : succ/fail
  (tid: pthread_t, sgn: signum_t): int = "#atslib_pthread_kill"
// end of [pthread_kill]
//
// HX: raise(sgn) = pthread_kill (pthread_self, sgn)
//
fun raise // 0/errno : succ/fail
  (sgn: signum_t): int = "#atslib_raise" // 0/nz : succ/fail
// end of [raise]

(* ****** ****** *)

fun sigwait ( // 0/pos : succ/fail
    set: &sigset_t, sgn: &signum_t? >> opt (signum_t, i==0)
  ) : #[i:int | i >= 0] int(i) = "#atslib_sigwait"
// end of [sigwait]

(* ****** ****** *)

(* end of [signal.sats] *)
