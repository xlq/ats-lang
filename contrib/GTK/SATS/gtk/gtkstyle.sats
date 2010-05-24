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
// Time: May, 2010
//

(* ****** ****** *)

fun gtk_style_new (): GtkStyle_ref1 = "#atsctrb_gtk_style_new"

fun gtk_style_copy
  {c:cls | c <= GtkStyle} {l:agz} (x: !gobjref (c, l)): GtkStyle_ref1
  = "#atsctrb_gtk_style_copy"
// end of [gtk_style_copy]

(* ****** ****** *)

fun gtk_style_attach
  {c1,c2:cls | c1 <= GtkStyle; c2 <= GdkWindow} {l1,l2:agz}
  (x: gobjref (c1, l1), win: !gobjref (GdkWindow, l2)): GtkStyle_ref1
  = "#atsctrb_gtk_style_attach"
// end of [gtk_style_attach]

fun gtk_style_detach
  {c:cls | c <= GtkStyle} {l:agz} (x: !gobjref (c, l)): void
  = "#atsctrb_gtk_style_detach"
// end of [gtk_style_detach]

(* ****** ****** *)

(* end of [gtkstyle.sats] *)
