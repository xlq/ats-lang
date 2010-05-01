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

fun gtk_menu_item_new
  (): GtkMenuItem_ptr1 = "#atsctrb_gtk_menu_item_new"
// end of [gtk_menu_item_new]

fun gtk_menu_item_new_with_label
  (name: string): GtkMenuItem_ptr1 = "#atsctrb_gtk_menu_item_new_with_label"
// end of [gtk_menu_item_new_with_label]

fun gtk_menu_item_new_with_mnemonic
  (name: string): GtkMenuItem_ptr1 = "#atsctrb_gtk_menu_item_new_with_mnemonic"
// end of [gtk_menu_item_new_with_mnemonic]

(* ****** ****** *)

fun gtk_menu_item_set_submenu
  {c1,c2:cls | c1 <= GtkMenuItem; c2 <= GtkWidget}
  {l1,l2:addr | l2 > null}
  (menuitem: !gobjptr (c1, l1), submenu: !gobjptr (c2, l2)): void
  = "#atsctrb_gtk_menu_item_set_submenu"
// end of [gtk_menu_item_set_submenu]

(* ****** ****** *)

(* end of [gtkmenuitem.sats] *)
