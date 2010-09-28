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

sta NCCS: int // = 32?
//
abst@ype cc_t = $extype "ats_cc_type"
castfn char_of_cc (x: cc_t):<> char
castfn cc_of_char (x: char):<> cc_t
//
abst@ype tcflag_t = $extype "ats_tcflag_type"
castfn uint_of_tcflag (x: tcflag_t):<> uint
castfn tcflag_of_uint (x: uint):<> tcflag_t
//
abst@ype speed_t = $extype "ats_speed_type"
castfn speed_of_uint (x: uint):<> speed_t
castfn uint_of_speed (x: speed_t):<> uint
//
abst@ype termios_rest
typedef termios_struct =
$extype_struct "ats_termios_type" of {
  c_iflag= tcflag_t
, c_oflag= tcflag_t
, c_cflag= tcflag_t
, c_lflag= tcflag_t
, c_line= cc_t
, c_cc= @[cc_t][NCCS]
, c_ispeed= speed_t
, c_ospeed= speed_t
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
