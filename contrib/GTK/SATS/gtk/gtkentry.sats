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

fun gtk_entry_new (): GtkEntry_ptr1 = "#atsctrb_gtk_entry_new"

(* ****** ****** *)

fun gtk_entry_get_visibility
  {c:cls | c <= GtkEntry} {l:anz} (entry: !gobjptr (c, l)): gboolean
  = "#atsctrb_gtk_entry_get_visibility"
// end of [gtk_entry_get_visibility]

fun gtk_entry_set_visibility
  {c:cls | c <= GtkEntry} {l:anz} (entry: !gobjptr (c, l), visibility: gboolean): void
  = "#atsctrb_gtk_entry_set_visibility"
// end of [gtk_entry_set_visibility]

(* ****** ****** *)

fun gtk_entry_get_editable
  {c:cls | c <= GtkEntry} {l:anz} (entry: !gobjptr (c, l)): gboolean
  = "#atsctrb_gtk_entry_get_editable"
// end of [gtk_entry_get_editable]

fun gtk_entry_set_editable
  {c:cls | c <= GtkEntry} {l:anz} (entry: !gobjptr (c, l), editable: gboolean): void
  = "#atsctrb_gtk_entry_set_editable"
// end of [gtk_entry_set_editable]

(* ****** ****** *)

fun gtk_entry_get_max_length
  {c:cls | c <= GtkEntry} {l:anz} (entry: !gobjptr (c, l)): gint
  = "#atsctrb_gtk_entry_get_max_length"
// end of [gtk_entry_get_max_length]

fun gtk_entry_set_max_length
  {c:cls | c <= GtkEntry} {l:anz} (entry: !gobjptr (c, l), max: gint): void
  = "#atsctrb_gtk_entry_set_max_length"
// end of [gtk_entry_set_max_length]

(* ****** ****** *)

fun gtk_entry_get_text
  {c:cls | c <= GtkEntry} {l:anz}
  (entry: !gobjptr (c, l)): [t:int] (stamp t | stamped (string, t))
  = "#atsctrb_gtk_entry_get_text"
// end of [gtk_entry_get_text]

fun gtk_entry_set_text
  {c:cls | c <= GtkEntry} {l:anz} (entry: !gobjptr (c, l), text: string): void
  = "#atsctrb_gtk_entry_set_text"
// end of [gtk_entry_set_text]

(* ****** ****** *)

(* end of [gtkentry.sats] *)
