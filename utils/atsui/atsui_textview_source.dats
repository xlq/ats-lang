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
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: May, 2010
//
(* ****** ****** *)

staload "libc/SATS/stdio.sats"

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gtk.sats"

(* ****** ****** *)

staload UT = "atsui_util.sats"
staload SWL = "atsui_srcwinlst.sats"

(* ****** ****** *)

staload "atsui_topenv.sats"
macdef gs = gstring_of_string

(* ****** ****** *)

implement
topenv_textview_source_update_statusbar
  () = () where {
  val (fpf_tv | tv) = topenv_get_textview_source ()
  val (fpf_tb | tb) = gtk_text_view_get_buffer (tv)
//
  val isModified = gtk_text_buffer_get_modified (tb)
  val isModified = (bool_of)isModified
  val YN = (if isModified then 'Y' else 'N'): char
//
  val (fpf_tm | tm) = gtk_text_buffer_get_insert (tb)
  var iter: GtkTextIter
  val () = gtk_text_buffer_get_iter_at_mark (tb, iter, tm)
  prval () = minus_addback (fpf_tm, tm | tb)
  val nrow = gtk_text_iter_get_line (iter)
  val nrow = int_of_gint (nrow)
  val ncol = gtk_text_iter_get_line_offset (iter)
  val ncol = int_of_gint (ncol)
//
  val (fpf_bar | bar) = topenv_get_statusbar ()
  val () = gtk_statusbar_pop (bar, (guint)0)
  val msg = g_strdup_printf ("--modified(%c)--line/col(%i/%i)--", @(YN, nrow+1, ncol+1))
  val _mid = gtk_statusbar_push (bar, (guint)0, msg)
  val () = g_free (msg)
  prval () = fpf_bar (bar)
  prval () = minus_addback (fpf_tb, tb | tv)
  prval () = fpf_tv (tv)
} // end of [topenv_textview_source_update_statusbar]

(* ****** ****** *)

implement cb_textview_source_changed () = let
  val () = topenv_textview_source_update_statusbar ()
in
  GTRUE // it is called last
end // end of [cb_textview_source_changed]

(* ****** ****** *)

(* end of [atsui_textview_source.dats] *)
