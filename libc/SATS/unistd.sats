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

#include "libc/sys/CATS/types.cats" // for [pid_t]
#include "libc/CATS/unistd.cats"

%}

(* ****** ****** *)

staload TYPES = "libc/sys/SATS/types.sats"

typedef pid_t = $TYPES.pid_t
typedef uid_t = $TYPES.uid_t

(* ****** ****** *)

sta stdin_int : int
sta stdout_int : int
sta stderr_int : int

macdef STDIN_FILENO = $extval (int stdin_int, "STDIN_FILENO")
macdef STDOUT_FILENO = $extval (int stdout_int, "STDOUT_FILENO")
macdef STDERR_FILENO = $extval (int stderr_int, "STDERR_FILENO")

(* ****** ****** *)

// implemented in [libc/DATS/unistd.dats]

fun fork_exn (): pid_t = "atslib_fork_exn"
  
fun fork_exec_cloptr_exn {v:view}
 (pf: !v | f: (v | (*none*)) -<cloptr1> void): void
 = "atslib_fork_exec_cloptr_exn"

fun fork_exec_and_wait_cloptr_exn (proc: () -<cloptr1> void): Int
  = "atslib_fork_exec_and_wait_cloptr_exn"

(* ****** ****** *)

// implemented in [libc/DATS/unistd.dats]
fun getcwd (): String = "atslib_getcwd"

(* ****** ****** *)

symintr wait
fun wait_with_status {l:addr}
  (pf: !int? @ l >> int @ l | p: ptr l): pid_t
  = "atslib_wait_with_status"

and wait_without_status (): pid_t
  = "atslib_wait_without_status"

overload wait with wait_with_status
overload wait with wait_without_status

(* ****** ****** *)

// [sleep] may be implemented using SIGARM
fun sleep {i:nat} (t: int i): [j:nat | j <= i] int j
  = "atslib_sleep"

(* ****** ****** *)

#define MILLION 1000000
// some systems require that the argument of usleep <= 1 million
fun usleep (n: natLte MILLION (* microseconds *)): void
  = "atslib_usleep"

(* ****** ****** *)

fun getuid ():<> uid_t = "atslib_getuid"
fun geteuid ():<> uid_t = "atslib_geteuid"

(* ****** ****** *)

(* end of [unistd.sats] *)
