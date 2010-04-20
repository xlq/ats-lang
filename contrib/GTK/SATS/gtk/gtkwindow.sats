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
  (tp: GtkWindowType): GtkWindow_ptr1 = "#atsctrb_gtk_window_new"
// end of [gtk_window_new]

(* ****** ****** *)

fun gtk_window_set_title
  {c:cls | c <= GtkWindow} {l:agz}
  (window: !gobjptr (c, l), title: string): void
  = "#atsctrb_gtk_window_set_title"
// end of [gtk_window_set_title]

(* ****** ****** *)

//
// [width = -1] means unset
// [height = -1] means unset
//
fun gtk_window_set_default_size
  {c:cls | c <= GtkWindow} {l:agz}
  (window: !gobjptr (c, l), width: gint, height: gint): void
  = "#atsctrb_gtk_window_set_default_size"
// end of [gtk_window_set_default_size]

(* ****** ****** *)

fun gtk_window_get_resizeable
  {c:cls | c <= GtkWindow} {l:agz}
  (window: !gobjptr (c, l)): gboolean = "#atsctrb_gtk_window_get_resizeable"
// end of [gtk_window_get_resizeable]

fun gtk_window_set_resizeable
  {c:cls | c <= GtkWindow} {l:agz}
  (window: !gobjptr (c, l), resizeable: gboolean): void
  = "#atsctrb_gtk_window_set_resizeable"
// end of [gtk_window_set_resizeable]

(* ****** ****** *)

(* end of [gtkwindow.sats] *)
