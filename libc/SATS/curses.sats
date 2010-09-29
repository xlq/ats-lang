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
#include "libc/CATS/curses.cats"
%} // end of [%{#]

(* ****** ****** *)

typedef strcst = string

(* ****** ****** *)

macdef OK = $extval (int, "OK") // OK = 0
macdef ERR = $extval (int, "ERR") // ERR = -1

(* ****** ****** *)

fun initscr ()
  : ptr = "#atslib_initscr" // the return value pointing to stdscr
fun endwin (): int = "#atslib_endwin"
fun isendwin (): bool = "#atslib_isendwin"

(* ****** ****** *)

fun raw (): int = "#atslib_raw"
fun noraw (): int = "#atslib_noraw"

(* ****** ****** *)

fun clear (): int = "#atslib_clear"
fun clrtobot (): int = "#atslib_clrtobot"
fun clrtoeol (): int = "#atslib_clrtoeol"
fun erase (): int = "#atslib_erase"

(* ****** ****** *)

fun beep (): int = "#atslib_beep"
fun flush (): int = "#atslib_flush"

(* ****** ****** *)

fun addstr (str: strcst): int = "#atslib_addstr"
fun addnstr (str: strcst, n: int): int = "#atslib_addnstr"
fun mvaddstr (y: int, x: int, str: strcst): int = "#atslib_mvaddstr"
fun mvaddnstr (y: int, x: int, str: strcst, n: int): int = "#atslib_mvaddnstr"

(* ****** ****** *)

fun refresh (): int = "#atslib_refresh"
fun doupdate (): int = "#atslib_doupdate"

(* ****** ****** *)

(* end of [curses.sats] *)
