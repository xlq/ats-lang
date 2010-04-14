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

fun gtk_adjustment_new (
    value: gdouble
  , lower: gdouble
  , upper: gdouble
  , step_increment: gdouble
  , page_increment: gdouble
  , page_size: gdouble
  ) : GtkAdjustment_ptr1 = "#atsctrb_gtk_adjustment_new"
// end of [gtk_adjustment_new]

(* ****** ****** *)

fun gtk_adjustment_changed
  {c:cls | c <= GtkAdjustment}
  {l:anz} (adj: !gobjptr (c, l)): void
  = "#atsctrb_gtk_adjustment_changed"
// end of [gtk_adjustment_changed]

fun gtk_adjustment_value_changed
  {c:cls | c <= GtkAdjustment}
  {l:anz} (adj: !gobjptr (c, l)): void
  = "#atsctrb_gtk_adjustment_value_changed"
// end of [gtk_adjustment_value_changed]

fun gtk_adjustment_clamp_page
  {c:cls | c <= GtkAdjustment} {l:anz}
  (adj: !gobjptr (c, l), lower: gdouble, upper: gdouble): void
  = "#atsctrb_gtk_adjustment_clamp_page"
// end of [gtk_adjustment_clamp_page]

(* ****** ****** *)

fun gtk_adjustment_get_value
  {c:cls | c <= GtkAdjustment}
  {l:anz} (adj: !gobjptr (c, l)): gdouble
  = "#atsctrb_gtk_adjustment_get_value"
// end of [gtk_adjustment_get_value]

fun gtk_adjustment_set_value
  {c:cls | c <= GtkAdjustment}
  {l:anz} (adj: !gobjptr (c, l), value: gdouble): void
  = "#atsctrb_gtk_adjustment_set_value"
// end of [gtk_adjustment_set_value]

(* ****** ****** *)

(* end of [gtkadjustment.sats] *)
