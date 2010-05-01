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

fun gtk_color_selection_dialog_new
  (title: string): GtkColorSelectionDialog_ptr1 = "#atsctrb_gtk_color_selection_dialog_new"
// end of [gtk_color_selection_dialog_new]

(* ****** ****** *)

fun gtk_color_selection_dialog_takeout_colorsel
  {c:cls | c <= GtkColorSelectionDialog} {l:agz} (dialog: !gobjptr (c, l))
  : [l_sel:agz] (
    minus (gobjptr (c, l), gobjptr (GtkColorSelection, l_sel)) | gobjptr (GtkColorSelection, l_sel)
  ) = "#atsctrb_gtk_color_selection_dialog_takeout_colorsel"
// end of [gtk_color_selection_dialog_takeout_colorsel]

(* ****** ****** *)

(* end of [gtkcolorseldialog.sats] *)
