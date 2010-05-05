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

typedef GtkAllocation =
  $extype_struct "GtkAllocation" of {
  x= gint
, y= gint
, width= gint
, height= gint
} // end of [GtkAllocation]

(* ****** ****** *)

abst@ype GTK_WIDGET_FLAG = guint
macdef GTK_CAN_DEFAULT = $extval (GTK_WIDGET_FLAG, "GTK_CAN_DEFAULT")

fun GTK_WIDGET_SET_FLAGS
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjptr (c, l), flag: GTK_WIDGET_FLAG): void
  = "#atsctrb_GTK_WIDGET_SET_FLAGS"
// end of [...]

(* ****** ****** *)

//
// HX: this one is based on refcount?
//
fun gtk_widget_destroy
  {c:cls | c <= GtkWidget} {l:agz} (widget: gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_destroy"

(* ****** ****** *)

fun gtk_widget_map
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_map"

fun gtk_widget_unmap
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_unmap"

(* ****** ****** *)

fun gtk_widget_realize
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_realize"

fun gtk_widget_unrealize
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_unrealize"

(* ****** ****** *)

fun gtk_widget_show
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_show"

fun gtk_widget_show_now
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_show_now"

fun gtk_widget_show_all
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_show_all"

(* ****** ****** *)

fun gtk_widget_hide
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_hide"

(* ****** ****** *)

//
// HX: negative width/height can have special meaning
//
fun gtk_widget_set_size_request
  {c:cls | c <= GtkWidget} {l:agz} (
    widegt: !gobjptr (c, l), width: gint, height: gint
  ) : void = "#atsctrb_gtk_widget_set_size_request"
// end of [gtk_widget_set_size_request]

(* ****** ****** *)

fun gtk_widget_grab_default
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjptr (c, l)): void
  = "#atsctrb_gtk_widget_grab_default"
// end of [gtk_widget_grab_default]

(* ****** ****** *)

fun gtk_widget_set_events
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjptr (c, l), events: gint): void
  = "#atsctrb_gtk_widget_set_events"
// end of [gtk_widget_set_events]

(* ****** ****** *)

fun gtk_widget_add_accelerator
  {c1,c2:cls | c1 <= GtkWidget; c2 <= GtkAccelGroup}
  {l1,l2:agz} (
    widget: !gobjptr (c1, l1)
  , signal: gsignal
  , aclgrp: !gobjptr (c2, l2)
  , aclkey: guint
  , aclmod: GdkModifierType
  , aclflg: GtkAccelFlags
  ) : void = "#atsctrb_gtk_widget_add_accelerator"
// end of [gtk_widget_add_accelerator]

fun gtk_widget_remove_accelerator
  {c1,c2:cls | c1 <= GtkWidget; c2 <= GtkAccelGroup}
  {l1,l2:agz} (
    widget: !gobjptr (c1, l1)
  , aclgrp: !gobjptr (c2, l2)
  , aclkey: guint
  , aclmod: GdkModifierType
  ) : void = "#atsctrb_gtk_widget_remove_accelerator"
// end of [gtk_widget_remove_accelerator]

(* ****** ****** *)


//
// HX-2010-04-18: this is probably safe enough :)
//
fun gtk_widget_takeout_window(*GDK*)
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjptr (c, l))
  : [l_win:addr] (
    minus (gobjptr (c, l), gobjptr (GdkWindow, l_win)) | gobjptr (GdkWindow, l_win)
  ) = "atsctrb_gtk_widget_takeout_window" // function!
// end of [gtk_widget_takeout_window]

(* ****** ****** *)

// HX: since GTK-2.18
fun gtk_widget_get_allocation
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjptr (c, l), alloc: &GtkAllocation? >> GtkAllocation): void
  = "#atsctrb_gtk_widget_get_allocation"
// end of [gtk_widget_get_allocation]

// HX: since GTK-2.18
fun gtk_widget_set_allocation
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjptr (c, l), alloc: &GtkAllocation): void
  = "#atsctrb_gtk_widget_set_allocation"
// end of [gtk_widget_set_allocation]

fun gtk_widget_takeout_allocation
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjptr (c, l))
  : [l_alloc:addr] (
    GtkAllocation @ l_alloc, minus (gobjptr (c, l), GtkAllocation @ l_alloc)
  | ptr l_alloc
  ) = "atsctrb_gtk_widget_takeout_allocation" // function!
// end of [gtk_widget_takeout_allocation]

(* ****** ****** *)

fun gtk_widget_modify_fg
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjptr (c, l), state: GtkStateType, color: &GdkColor): void
  = "#atsctrb_gtk_widget_modify_fg"
// end of [gtk_widget_modify_fg]

fun gtk_widget_modify_bg
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjptr (c, l), state: GtkStateType, color: &GdkColor): void
  = "#atsctrb_gtk_widget_modify_bg"
// end of [gtk_widget_modify_bg]

(* ****** ****** *)

fun gtk_widget_get_colormap
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjptr (c, l)): [l1:agz] (
    minus (gobjptr (c, l), GdkColormap_ptr l1) | GdkColormap_ptr l1
  ) = "#atsctrb_gtk_widget_get_colormap"
// end of [gtk_widget_get_colormap]

(* ****** ****** *)

fun gtk_widget_queue_draw_area
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjptr (c, l), x: gint, y: gint, width: gint, height: gint): void
  = "#atsctrb_gtk_widget_queue_draw_area"
// end of [gtk_widget_queue_draw_area]

(* ****** ****** *)

(* end of [gtkwidget.sats] *)
