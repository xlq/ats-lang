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

fun gtk_file_chooser_dialog_new
  (title: Stropt, action: GtkFileChooserAction): GtkFileChooserDialog_ptr1
  = "atsctrb_gtk_file_chooser_dialog_new" // a function!
// end of [gtk_file_chooser_dialog_new]

(*
//
// HX: this one is not directly supported in ATS:
//
GtkWidget*
gtk_file_chooser_dialog_new (
  const gchar *title
, GtkWindow *parent
, GtkFileChooserAction action
, const gchar *first_button_text
, ...
) // end of [gtk_file_chooser_dialog_new]
*)

(* ****** ****** *)

//
// HX-2010-05-02:
// note that this is really a cast (intead of a field selection)
//
fun gtk_file_chooser_dialog_takeout_chooser
  {c:cls | c <= GtkFileChooserDialog} {l:agz}
  (chooserdlg: !gobjptr (c, l)): [l1:agz] (
    minus (gobjptr (c, l), gobjptr (GtkFileChooser, l1)) | gobjptr (GtkFileChooser, l1)
  ) = "#atsctrb_GTK_FILE_CHOOSER"
// end of [gtk_file_chooser_dialog_takeout_chooser]

(* ****** ****** *)

(* end of [gtkfilechooserdialog.sats] *)
