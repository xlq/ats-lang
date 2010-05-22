(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2010-201? Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: May 2010

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload UT = "atsui_util.sats"
staload SWL = "atsui_srcwinlst.sats"

(* ****** ****** *)

staload "atsui_topenv.sats"

(* ****** ****** *)

implement
topenv_make_menu_edit () = menu where {
  val menu = gtk_menu_new () // to be returned
//
  val undo_item =
    $UT.gtk_image_menu_item_new_from_stock_null (GTK_STOCK_UNDO)
  val () = gtk_menu_shell_append (menu, undo_item)
  val () = gtk_widget_show_unref (undo_item)
//
  val redo_item =
    $UT.gtk_image_menu_item_new_from_stock_null (GTK_STOCK_REDO)
  val () = gtk_menu_shell_append (menu, redo_item)
  val () = gtk_widget_show_unref (redo_item)
//
  val sep_item = gtk_separator_menu_item_new ()
  val () = gtk_menu_shell_append (menu, sep_item)
  val () = gtk_widget_show_unref (sep_item)
//
  val paste_item =
    $UT.gtk_image_menu_item_new_from_stock_null (GTK_STOCK_PASTE)
  val () = gtk_menu_shell_append (menu, paste_item)
  val () = gtk_widget_show_unref (paste_item)
//
  val sep_item = gtk_separator_menu_item_new ()
  val () = gtk_menu_shell_append (menu, sep_item)
  val () = gtk_widget_show_unref (sep_item)
//
  val delete_item =
    $UT.gtk_image_menu_item_new_from_stock_null (GTK_STOCK_DELETE)
  val () = gtk_menu_shell_append (menu, delete_item)
  val () = gtk_widget_show_unref (delete_item)
//
} // end of [topenv_make_menu_edit]

(* ****** ****** *)

(* end of [atsui_menu_edit.dats] *)
