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
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#
#include "libc/CATS/termios.cats"
%} // end of [%{#]

(* ****** ****** *)

staload TYPES = "libc/sys/SATS/types.sats"
typedef pid_t = $TYPES.pid_t

(* ****** ****** *)

sta NCCS: int
abst@ype cc_t
abst@ype tcflag_t
abst@ype termios_rest
typedef termios_struct =
$extype_struct "ats_termios_type" of {
  c_iflag= tcflag_t
, c_oflag= tcflag_t
, c_cflag= tcflag_t
, c_lflag= tcflag_t
, c_cc= @[cc_t][NCCS]
, _rest= termios_rest // unknown quantity
} // end of [termios_struct]
typedef termios = termios_struct

(* ****** ****** *)

fun tcgetattr {fd:nat} // 0/-1 : succ/fail // set errno
  (fd: int, tp: &termios): int = "#atslib_tcgetattr"
// end of [tcgetattr]

fun tcsetattr {fd:nat} // 0/-1 : succ/fail // set errno
  (fd: int fd, actions: int, tp: &termios): int = "#atslib_tcsetattr"
// end of [tcsetattr]

(* ****** ****** *)
//
// HX-2010-09-27: only available on SUS systems; not on FreeBSD
//
fun tcgetsid {fd:nat}
  (fd: int fd): pid_t = "#atslib_tcgetsid" // -1 is returned on error
// end of [tcgetsid]

(* ****** ****** *)

(* end of [termios.sats] *)
