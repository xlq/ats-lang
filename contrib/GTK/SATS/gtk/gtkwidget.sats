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
  (widget: !gobjref (c, l), flag: GTK_WIDGET_FLAG): void
  = "#atsctrb_GTK_WIDGET_SET_FLAGS"
// end of [...]

(* ****** ****** *)

//
// HX: this one is based on refcount?
//
fun gtk_widget_destroy
  {c:cls | c <= GtkWidget} {l:agz} (widget: gobjref (c, l)): void
  = "#atsctrb_gtk_widget_destroy"

(* ****** ****** *)

fun gtk_widget_map
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjref (c, l)): void
  = "#atsctrb_gtk_widget_map"

fun gtk_widget_unmap
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjref (c, l)): void
  = "#atsctrb_gtk_widget_unmap"

(* ****** ****** *)

fun gtk_widget_realize
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjref (c, l)): void
  = "#atsctrb_gtk_widget_realize"

fun gtk_widget_unrealize
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjref (c, l)): void
  = "#atsctrb_gtk_widget_unrealize"

(* ****** ****** *)

fun gtk_widget_show
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjref (c, l)): void
  = "#atsctrb_gtk_widget_show"

//
// HX-2010-05-08:
// this one is implemented in [gtk.dats]
// it seems to be a commonly used combination
//
fun gtk_widget_show_unref
  {c:cls | c <= GtkWidget} {l:agz} (widget: gobjref (c, l)): void
// end of [gtk_widget_show_unref]

(* ****** ****** *)

fun gtk_widget_show_now
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjref (c, l)): void
  = "#atsctrb_gtk_widget_show_now"

fun gtk_widget_show_all
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjref (c, l)): void
  = "#atsctrb_gtk_widget_show_all"

(* ****** ****** *)

fun gtk_widget_hide
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjref (c, l)): void
  = "#atsctrb_gtk_widget_hide"

(* ****** ****** *)

fun gtk_widget_get_sensitive
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l)): gboolean = "#atsctrb_gtk_widget_get_sensitive"
// end of [gtk_widget_get_sensitive]

fun gtk_widget_set_sensitive
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l), sensitive: gboolean): void
  = "#atsctrb_gtk_widget_set_sensitive"
// end of [gtk_widget_set_sensitive]

(* ****** ****** *)

//
// HX: negative width/height can have special meaning
//
fun gtk_widget_set_size_request
  {c:cls | c <= GtkWidget} {l:agz} (
    widegt: !gobjref (c, l), width: gint, height: gint
  ) : void = "#atsctrb_gtk_widget_set_size_request"
// end of [gtk_widget_set_size_request]

(* ****** ****** *)

fun gtk_widget_grab_focus
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjref (c, l)): void
  = "#atsctrb_gtk_widget_grab_focus"
// end of [gtk_widget_grab_focus]

fun gtk_widget_grab_default
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjref (c, l)): void
  = "#atsctrb_gtk_widget_grab_default"
// end of [gtk_widget_grab_default]

(* ****** ****** *)

fun gtk_widget_set_events
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjref (c, l), events: gint): void
  = "#atsctrb_gtk_widget_set_events"
// end of [gtk_widget_set_events]

(* ****** ****** *)

fun gtk_widget_add_accelerator
  {c1,c2:cls | c1 <= GtkWidget; c2 <= GtkAccelGroup}
  {l1,l2:agz} (
    widget: !gobjref (c1, l1)
  , signal: gsignal
  , aclgrp: !gobjref (c2, l2)
  , aclkey: guint
  , aclmod: GdkModifierType
  , aclflg: GtkAccelFlags
  ) : void = "#atsctrb_gtk_widget_add_accelerator"
// end of [gtk_widget_add_accelerator]

fun gtk_widget_remove_accelerator
  {c1,c2:cls | c1 <= GtkWidget; c2 <= GtkAccelGroup}
  {l1,l2:agz} (
    widget: !gobjref (c1, l1)
  , aclgrp: !gobjref (c2, l2)
  , aclkey: guint
  , aclmod: GdkModifierType
  ) : void = "#atsctrb_gtk_widget_remove_accelerator"
// end of [gtk_widget_remove_accelerator]

(* ****** ****** *)


//
// HX-2010-04-18: this is probably safe enough :)
//
fun gtk_widget_get_window(*GDK*)
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjref (c, l))
  : [l_win:addr] (
    minus (gobjref (c, l), gobjref (GdkWindow, l_win)) | gobjref (GdkWindow, l_win)
  ) = "atsctrb_gtk_widget_get_window" // function!
// end of [gtk_widget_get_window]

(* ****** ****** *)

// HX: since GTK-2.18
fun gtk_widget_get_allocation
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l), alloc: &GtkAllocation? >> GtkAllocation): void
  = "#atsctrb_gtk_widget_get_allocation"
// end of [gtk_widget_get_allocation]

// HX: since GTK-2.18
fun gtk_widget_set_allocation
  {c:cls | c <= GtkWidget} {l:agz} (widget: !gobjref (c, l), alloc: &GtkAllocation): void
  = "#atsctrb_gtk_widget_set_allocation"
// end of [gtk_widget_set_allocation]

fun gtk_widget_getref_allocation
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l))
  : [l_alloc:addr] (
    GtkAllocation @ l_alloc, minus (gobjref (c, l), GtkAllocation @ l_alloc)
  | ptr l_alloc
  ) = "atsctrb_gtk_widget_getref_allocation" // function!
// end of [gtk_widget_getref_allocation]

(* ****** ****** *)

fun gtk_widget_modify_fg
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l), state: GtkStateType, color: &GdkColor): void
  = "#atsctrb_gtk_widget_modify_fg"
// end of [gtk_widget_modify_fg]

fun gtk_widget_modify_bg
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l), state: GtkStateType, color: &GdkColor): void
  = "#atsctrb_gtk_widget_modify_bg"
// end of [gtk_widget_modify_bg]

(* ****** ****** *)

fun gtk_widget_get_colormap
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l)): [l1:agz] (
    minus (gobjref (c, l), GdkColormap_ref l1) | GdkColormap_ref l1
  ) = "#atsctrb_gtk_widget_get_colormap"
// end of [gtk_widget_get_colormap]

(* ****** ****** *)

fun gtk_widget_modify_font
  {c:cls | c <= GtkWidget} {l1,l2:agz}
  (widget: !gobjref (c, l1), fd: !PangoFontDescription_ptr l2): void
  = "#atsctrb_gtk_widget_modify_font"
// end of [gtk_widget_modify_font]

(* ****** ****** *)

fun gtk_widget_queue_draw_area
  {c:cls | c <= GtkWidget} {l:agz}
  (widget: !gobjref (c, l), x: gint, y: gint, width: gint, height: gint): void
  = "#atsctrb_gtk_widget_queue_draw_area"
// end of [gtk_widget_queue_draw_area]

(* ****** ****** *)

(* end of [gtkwidget.sats] *)
