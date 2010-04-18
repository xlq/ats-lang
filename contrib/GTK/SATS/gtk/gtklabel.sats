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

fun gtk_label_new
  (name: string): GtkLabel_ptr1 = "#atsctrb_gtk_label_new"
// end of [gtk_label_new]

(* ****** ****** *)

fun gtk_label_set_text
  {c:cls | c <= GtkLabel} {l:agz}
  (label: !gobjptr (c, l), name: string): void = "#atsctrb_gtk_label_set_text"
// end of [gtk_label_set_text]

fun gtk_label_get_text
  {c:cls | c <= GtkLabel} {l:agz}
  (label: !gobjptr (c, l)): [t:int] (stamp t | stamped (string, t))
  = "#atsctrb_gtk_label_get_text"
// end of [gtk_label_get_text]

(* ****** ****** *)

fun gtk_label_get_justify
  {c:cls | c <= GtkLabel} {l:agz}
  (label: !gobjptr (c, l)): GtkJustification = "#atsctrb_gtk_label_get_justify"
// end of [gtk_label_get_justify]

fun gtk_label_set_justify
  {c:cls | c <= GtkLabel} {l:agz}
  (label: !gobjptr (c, l), jtype: GtkJustification): void
  = "#atsctrb_gtk_label_set_justify"
// end of [gtk_label_set_justify]

(* ****** ****** *)

fun gtk_label_get_line_wrap
  {c:cls | c <= GtkLabel} {l:agz}
  (label: !gobjptr (c, l)): gboolean = "#atsctrb_gtk_label_get_line_wrap"
// end of [gtk_label_get_line_wrap]

fun gtk_label_set_line_wrap
  {c:cls | c <= GtkLabel} {l:agz}
  (label: !gobjptr (c, l), wrap: gboolean): void
  = "#atsctrb_gtk_label_set_line_wrap"
// end of [gtk_label_set_line_wrap]

(* ****** ****** *)

(* end of [gtklabel.sats] *)
