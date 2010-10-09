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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)  *)

(* ****** ****** *)

%{#
#include "libc/sys/CATS/resource.cats"
%} // end of [%{#]

(* ****** ****** *)

abst@ype priowhich_t = int
castfn int_of_priowhich (x: priowhich_t):<> int
macdef PRIO_PROCESS =
  $extval (priowhich_t, "PRIO_PROCESS")
macdef PRIO_PGRP = $extval (priowhich_t, "PRIO_PGRP")
macdef PRIO_USER = $extval (priowhich_t, "PRIO_USER")

(* ****** ****** *)
//
// HX: -1 maybe a legitimate return value for getpriority
//
fun getpriority
  (which: priowhich_t, who: int): int = "#atslib_getpriority"
// end of [getpriority]
//
// HX: 0/-1 : succ/fail // errno set
//
fun setpriority
  (which: priowhich_t, who: int, prio: int): int = "#atslib_setpriority"
// end of [setpriority]

(* ****** ****** *)

(* end of [resource.sats] *)
