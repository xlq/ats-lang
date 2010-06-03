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
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#
#include "contrib/glib/CATS/glib/gmem.cats"
%} // end of [%{#]

(* ****** ****** *)

absview gfree_v (l:addr)

(* ****** ****** *)

fun gptr_alloc
  {a:viewt@ype} (n: sizeof_t a)
  : [l:addr] (gfree_v l, a? @ l | ptr l) = "#atsctrb_gptr_alloc"
// end of [gptr_alloc]

fun gptr_free {a:viewt@ype} {l:addr}
  (pf1: gfree_v l, pf2: a? @ l | p: ptr l): void = "#atsctrb_g_free"
// end of [gptr_free]

(* ****** ****** *)

castfn gstring_free_null (x: gstring null):<> ptr null
fun gstring_free {l:addr} (x: gstring l): void = "#atsctrb_g_free"

(* ****** ****** *)

(* end of [gmem.sats] *)