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

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: April, 2010
//

(* ****** ****** *)

fun g_object_is_floating
  {c:cls | c <= GObject} {l:agz} (x: !gobjptr (c, l)): bool
  = "#atsctrb_g_object_is_floating"
// end of [g_object_is_floating]

(* ****** ****** *)

fun g_object_ref_count
  {c:cls} {l:addr} (x: !gobjptr (c, l)): int = "#atsctrb_g_object_ref_count"
// end of [g_object_ref_count]

(* ****** ****** *)

fun g_object_ref
  {c:cls | c <= GObject} {l:agz} (x: !gobjptr (c, l)): gobjptr (c, l)
  = "#atsctrb_g_object_ref"
// end of [g_object_ref]

fun g_object_unref
  {c:cls | c <= GObject} {l:agz} (x: gobjptr (c, l)): void
  = "#atsctrb_g_object_unref"
// end of [g_object_unref]

(* ****** ****** *)

(* end of [gobject.sats] *)
