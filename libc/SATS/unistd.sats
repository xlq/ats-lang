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
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#

#include "libc/CATS/unistd.cats"

%}

(* ****** ****** *)

abst@ype pid_t = $extype "ats_pid_t_type"

(* ****** ****** *)

// implemented in [libc/DATS/unistd.dats]
  
fun fork_and_exec_and_wait_cloptr (proc: () -<lin,cloptr> void): int
  = "atslib_fork_and_exec_and_wait_cloptr"

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

// some systems require that the argument of usleep <= 1000000
fun usleep (n: natLte 1000000 (* microseconds *)): void
  = "atslib_usleep"

(* ****** ****** *)

(* end of [unistd.sats] *)
