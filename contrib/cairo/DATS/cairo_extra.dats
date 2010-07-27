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
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
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
// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: July, 2010
//

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no need for dynamic loading

(* ****** ****** *)

staload "contrib/cairo/SATS/cairo.sats"
staload "contrib/cairo/SATS/cairo_extra.sats"

(* ****** ****** *)

implement
cairo_show_text_inbox
  (cr, W, H, utf8) = () where {
  val (pf | ()) = cairo_save (cr)
  #define FONTSIZE 1
  val () = cairo_set_font_size (cr, (double_of)FONTSIZE)
//
  val () = () where {
    var te : cairo_text_extents_t
//
    val MN = min (W, H)
    val () = cairo_text_extents (cr, utf8, te)
    val alpha = (1.0 * MN / te.width) // this is just an estimate
    val () = cairo_scale (cr, alpha, alpha)
//
    val () = cairo_text_extents (cr, utf8, te)
    val w = te.width and h = te.height
    val x_base = w / 2 + te.x_bearing and y_base = ~te.y_bearing / 2
    val () = cairo_move_to (cr, ~x_base, y_base)
    val () = cairo_show_text (cr, utf8)
  } // end of [val]
  val () = cairo_restore (pf | cr)
} // end of [cairo_show_text_inbox]

(* ****** ****** *)

(* end of [cairo_extra.dats] *)
