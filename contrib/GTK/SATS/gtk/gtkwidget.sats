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
// Start Time: April, 2010
//

(* ****** ****** *)

abst@ype GTK_WIDGET_FLAG = guint
macdef GTK_CAN_DEFAULT = $extval (GTK_WIDGET_FLAG, "GTK_CAN_DEFAULT")

fun GTK_WIDGET_SET_FLAGS
  {c:cls | c <= GtkWidget} {l:anz} (widget: !gobjptr (c, l), flag: GTK_WIDGET_FLAG): void
  = "#atsctrb_GTK_WIDGET_SET_FLAGS"
// end of [...]

(* ****** ****** *)

//
// this one is based on refcount?
//
fun gtk_widget_destroy
  {c:cls | c <= GtkWidget} {l:anz} (widget: gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_destroy"

(* ****** ****** *)

fun gtk_widget_show
  {c:cls | c <= GtkWidget} {l:anz} (widget: !gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_show"

fun gtk_widget_show_now
  {c:cls | c <= GtkWidget} {l:anz} (widget: !gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_show_now"

(* ****** ****** *)

fun gtk_widget_set_size_request
  {c:cls | c <= GtkWidget} {l:anz} (
    widegt: !gobjptr (c, l), width: gint, height: gint
  ) : void = "#atsctrb_gtk_widget_set_size_request"
// end of [gtk_widget_set_size_request]

(* ****** ****** *)

fun gtk_widget_grab_default
  {c:cls | c <= GtkWidget} {l:anz} (widget: !gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_grab_default"
// end of [gtk_widget_grab_default]

(* ****** ****** *)

(* end of [gtkwidget.sats] *)
