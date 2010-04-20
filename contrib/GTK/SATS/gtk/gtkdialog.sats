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

abst@ype
GtkResponseType = $extype "GtkResponseType"

(*
** GTK returns this if a response widget has no response_id,
** or if the dialog gets programmatically hidden or destroyed.
*)
// GTK_RESPONSE_NONE = -1
macdef GTK_RESPONSE_NONE = $extval (GtkResponseType, "GTK_RESPONSE_NONE")

(*
** GTK won't return these unless you pass them in
** as the response for an action widget. They are
** for your convenience.
*)
// GTK_RESPONSE_REJECT = -2
macdef GTK_RESPONSE_REJECT = $extval (GtkResponseType, "GTK_RESPONSE_REJECT")
// GTK_RESPONSE_ACCEPT = -3
macdef GTK_RESPONSE_ACCEPT = $extval (GtkResponseType, "GTK_RESPONSE_ACCEPT")

(* If the dialog is deleted *)
// GTK_RESPONSE_DELETE_EVENT = -4
macdef GTK_RESPONSE_DELETE_EVENT = $extval (GtkResponseType, "GTK_RESPONSE_DELETE_EVENT")

(*
** These are returned from GTK dialogs, and you can also use them
** yourself if you like.
*)
// GTK_RESPONSE_OK     = -5
macdef GTK_RESPONSE_OK = $extval (GtkResponseType, "GTK_RESPONSE_OK")
// GTK_RESPONSE_CANCEL = -6
macdef GTK_RESPONSE_CANCEL = $extval (GtkResponseType, "GTK_RESPONSE_CANCEL")
// GTK_RESPONSE_CLOSE  = -7
macdef GTK_RESPONSE_CLOSE = $extval (GtkResponseType, "GTK_RESPONSE_CLOSE")
// GTK_RESPONSE_YES    = -8
macdef GTK_RESPONSE_YES = $extval (GtkResponseType, "GTK_RESPONSE_YES")
// GTK_RESPONSE_NO     = -9
macdef GTK_RESPONSE_NO = $extval (GtkResponseType, "GTK_RESPONSE_NO")
// GTK_RESPONSE_APPLY  = -10
macdef GTK_RESPONSE_APPLY = $extval (GtkResponseType, "GTK_RESPONSE_APPLY")
// GTK_RESPONSE_HELP   = -11
macdef GTK_RESPONSE_HELP = $extval (GtkResponseType, "GTK_RESPONSE_HELP")

castfn gint_of_GtkResponseType (x: GtkResponseType):<> gint

(* ****** ****** *)

fun gtk_dialog_new (): GtkDialog_ptr1 = "#atsctrb_gtk_dialog_new"

(* ****** ****** *)

//
// HX-2010-04-10:
// If the diaglog widget is destroyed in the middle, all bets are off!!!
//
fun gtk_dialog_run
  {c:cls | c <= GtkDialog} {l:agz}
  (dialog: !gobjptr (c, l)): gint = "#atsctrb_gtk_dialog_run"
// end of [gtk_dialog_run]

(* ****** ****** *)

fun gtk_dialog_response
  {c:cls | c <= GtkDialog} {l:agz}
  (dialog: !gobjptr (c, l), response_id: gint): void = "#atsctrb_gtk_dialog_response"
// end of [gtk_dialog_response]

(* ****** ****** *)

(* end of [gtkdialog.sats] *)
