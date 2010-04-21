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

fun gtk_text_view_new (): GtkTextView_ptr1 = "#atsctrb_gtk_text_view_new"

(* ****** ****** *)

fun gtk_text_view_set_buffer
  {c1,c2:cls | c1 <= GtkTextView; c2 <= GtkTextBuffer} {l1,l2:agz}
  (tv: !gobjptr (c1, l1), tb: !gobjptr (c2, l2)): void = "#atsctrb_gtk_text_view_set_buffer"
// end of [gtk_text_view_set_buffer]

//
// HX: this one should be called 'takeout' (instead of 'get')
//
fun gtk_text_view_get_buffer
  {c:cls | c <= GtkTextView} {l:agz}
  (tv: !gobjptr (c, l)):<> [l_buf:agz] (
    gobjptr (GtkTextBuffer, l_buf) -<lin,prf> void | gobjptr (GtkTextBuffer, l_buf)
  ) = "#atsctrb_gtk_text_view_get_buffer"
// end of [gtk_text_view_get_buffer]

(* ****** ****** *)

(* end of [gtktextview.sats] *)
