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

fun gtk_window_new
  (tp: GtkWindowType): GtkWindow_ref1 = "#atsctrb_gtk_window_new"
// end of [gtk_window_new]

(* ****** ****** *)

fun gtk_window_set_title
  {c:cls | c <= GtkWindow} {l1,l2:agz}
  (window: !gobjref (c, l1), title: !gstring l2): void
  = "#atsctrb_gtk_window_set_title"
// end of [gtk_window_set_title]

(* ****** ****** *)

fun gtk_window_set_position
  {c:cls | c <= GtkWindow} {l:agz}
  (window: !gobjref (c, l), pos: GtkWindowPosition): void
  = "#atsctrb_gtk_window_set_position"
// end of [gtk_window_set_position]

fun gtk_window_set_transient_for
  {c1,c2:cls | c1 <= GtkWindow; c2 <= GtkWindow}
  {l1,l2:agz} (window: !gobjref (c1, l1), parent: !gobjref (c2, l2)): void
  = "#atsctrb_gtk_window_set_transient_for"
// end of [gtk_window_set_transient_for]

(* ****** ****** *)

//
// [width = -1] means unset
// [height = -1] means unset
//
fun gtk_window_set_default_size
  {c:cls | c <= GtkWindow} {l:agz}
  (window: !gobjref (c, l), width: gint, height: gint): void
  = "#atsctrb_gtk_window_set_default_size"
// end of [gtk_window_set_default_size]

fun gtk_window_get_size
  {c:cls | c <= GtkWindow} {l:agz} (
    window: !gobjref (c, l), width: &gint? >> gint, height: &gint? >> gint
  ) : void = "#atsctrb_gtk_window_get_size"
// end of [gtk_window_get_size]

(* ****** ****** *)

fun gtk_window_get_resizable
  {c:cls | c <= GtkWindow} {l:agz}
  (window: !gobjref (c, l)): gboolean = "#atsctrb_gtk_window_get_resizeable"
// end of [gtk_window_get_resizeable]

fun gtk_window_set_resizable
  {c:cls | c <= GtkWindow} {l:agz}
  (window: !gobjref (c, l), resizable: gboolean): void
  = "#atsctrb_gtk_window_set_resizable"
// end of [gtk_window_set_resizable]

(* ****** ****** *)

fun gtk_window_add_accel_group
  {c1,c2:cls | c1 <= GtkWindow; c2 <= GtkAccelGroup}
  {l1,l2:agz}
  (window: !gobjref (c1, l1), aclgrp: !gobjref (c2, l2)): void
  = "#atsctrb_gtk_window_add_accel_group"
// end of [gtk_window_add_accel_group]

fun gtk_window_remove_accel_group
  {c1,c2:cls | c1 <= GtkWindow; c2 <= GtkAccelGroup}
  {l1,l2:agz}
  (window: !gobjref (c1, l1), aclgrp: !gobjref (c2, l2)): void
  = "#atsctrb_gtk_window_remove_accel_group"
// end of [gtk_window_remove_accel_group]

(* ****** ****** *)

(* end of [gtkwindow.sats] *)
