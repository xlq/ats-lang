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
// Start Time: May, 2010
//

(* ****** ****** *)

abst@ype GtkMessageType = $extype "GtkMessageType"
macdef GTK_MESSAGE_INFO = $extval (GtkMessageType, "GTK_MESSAGE_INFO")
macdef GTK_MESSAGE_WARNING = $extval (GtkMessageType, "GTK_MESSAGE_WARNING")
macdef GTK_MESSAGE_QUESTION = $extval (GtkMessageType, "GTK_MESSAGE_QUESTION")
macdef GTK_MESSAGE_ERROR = $extval (GtkMessageType, "GTK_MESSAGE_ERROR")
macdef GTK_MESSAGE_OTHER = $extval (GtkMessageType, "GTK_MESSAGE_OTHER")

(* ****** ****** *)

abst@ype GtkButtonsType = $extype "GtkButtonsType"
macdef GTK_BUTTONS_NONE = $extval (GtkButtonsType, "GTK_BUTTONS_NONE")
macdef GTK_BUTTONS_OK = $extval (GtkButtonsType, "GTK_BUTTONS_OK")
macdef GTK_BUTTONS_CLOSE = $extval (GtkButtonsType, "GTK_BUTTONS_CLOSE")
macdef GTK_BUTTONS_CANCEL = $extval (GtkButtonsType, "GTK_BUTTONS_CANCEL")
macdef GTK_BUTTONS_YES_NO = $extval (GtkButtonsType, "GTK_BUTTONS_YES_NO")
macdef GTK_BUTTONS_OK_CANCEL = $extval (GtkButtonsType, "GTK_BUTTONS_OK_CANCEL")

(* ****** ****** *)

//
// HX: these are just simplified versions
//
fun gtk_message_dialog_new0
  {l:addr} (
    flags: GtkDialogFlags
  , _type: GtkMessageType
  , buttons: GtkButtonsType
  , message: !gstring l
  ) : GtkMessageDialog_ref1
  = "atsctrb_gtk_message_dialog_new0" // function!
// end of [gtk_message_dialog_new]

fun gtk_message_dialog_new0_with_markup
  {l:addr} (
    flags: GtkDialogFlags
  , _type: GtkMessageType
  , buttons: GtkButtonsType
  , message: !gstring l
  ) : GtkMessageDialog_ref1
  = "atsctrb_gtk_message_dialog_new0_with_markup" // function!
// end of [gtk_message_dialog_new0_with_markup]

(* ****** ****** *)

fun gtk_message_dialog_set_markup
  {c:cls | c <= GtkMessageDialog} {l1,l2:agz}
  (dialog: !gobjref (c, l1), markup: !gstring l2): void
  = "#atsctrb_gtk_message_dialog_set_markup" // macro
// end of [gtk_message_dialog_set_markup]

(* ****** ****** *)

(* end of [gtkmessagedialog.sats] *)
