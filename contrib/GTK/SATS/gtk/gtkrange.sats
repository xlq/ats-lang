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

fun gtk_range_set_update_policy
  {c:cls | c <= GtkRange} {l1,l2:anz}
  (range: !gobjptr (c, l1), policy: GtkUpdateType): void
  = "#atsctrb_gtk_range_set_update_policy"

(* ****** ****** *)

fun gtk_range_get_adjustment
  {c:cls | c <= GtkRange} {l:anz}
  (range: !gobjptr (c, l))
  : [l1:addr] (gobjptr (GtkAdjustment, l1) -<lin,prf> void | gobjptr (GtkAdjustment, l1))
  = "#atsctrb_gtk_range_get_adjustment"

//
// HX-2010-04-13: [g_object_ref] is called on [adj] if it is added!
//
fun gtk_range_set_adjustment
  {c:cls | c <= GtkRange} {l1,l2:anz}
  (range: !gobjptr (c, l1), adj: !gobjptr (GtkAdjustment, l2)): void
  = "#atsctrb_gtk_range_set_adjustment"

(* ****** ****** *)

(* end of [gtkrange.sats] *)
