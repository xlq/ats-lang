(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-20?? Hongwei Xi, ATS Trustworthy Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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
// Author: Hongwei Xi (gmhwxi AT gmail DOT com)
// Start Time: October, 2011
//
(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "contrib/cairo/SATS/cairo.sats"
staload "contrib/cairo/SATS/cairo_extra.sats"

(* ****** ****** *)

staload "contrib/atspslide/SATS/atspslide.sats"

(* ****** ****** *)

staload
TM = "libc/SATS/time.sats"
stadef tm_struct = $TM.tm_struct
macdef time_get = $TM.time_get
macdef localtime_r = $TM.localtime_r

(* ****** ****** *)

staload M = "libc/SATS/math.sats"
macdef PI = $M.M_PI
macdef _2PI = 2 * PI
macdef sin = $M.sin
macdef cos = $M.cos

(* ****** ****** *)

implement
cairodraw_clock01
  (cr) = () where {
//
  var t = time_get ()
  var tm: tm_struct // unintialized
//
  val _ptr = localtime_r (t, tm)
  val () = assertloc (_ptr > null)
  prval () = opt_unsome {tm_struct} (tm)
//
  val ms = tm.tm_min * PI / 30
  val hs = tm.tm_hour * PI / 6 + ms / 12
  val ss = tm.tm_sec * PI / 30
//
  val (pf | ()) = cairo_save (cr)
  val () = cairo_translate (cr, 0.5, 0.5)
//
  val () = cairo_set_line_cap (cr, CAIRO_LINE_CAP_ROUND)
  val () = cairo_set_line_width (cr, 0.1)
//
  // draw a black clock outline
  val () = cairo_new_path (cr)
  val () = cairo_arc (cr, 0.0, 0.0, 0.4, 0.0, _2PI)
  val () = cairo_set_source_rgba (cr, 0.0, 0.0, 0.0, 0.1)
  val () = cairo_stroke (cr)
//
  // draw a green dot on the current second
  val () = cairo_arc
    (cr, 0.4 * sin(ss), 0.4 * ~cos(ss), 0.05, 0.0, _2PI)
  val () = cairo_set_source_rgba (cr, 0.0, 1.0, 0.0, 0.250)
  val () = cairo_fill (cr)
//
  // draw the minutes indicator
  val () = cairo_move_to (cr, 0.0, 0.0)
  val () = cairo_line_to (cr, 0.4 * sin(ms), 0.4 * ~cos(ms))
  val () = cairo_set_source_rgba (cr, 0.2, 0.2, 1.0, 0.125)
  val () = cairo_stroke(cr)
//
  // draw the hours indicator
  val () = cairo_move_to (cr, 0.0, 0.0)
  val () = cairo_line_to (cr, 0.2 * sin(hs), 0.2 * ~cos(hs))
  val () = cairo_set_source_rgba (cr, 0.2, 0.2, 1.0, 0.125)
  val () = cairo_stroke (cr)
//
  val () = cairo_restore (pf | cr)
//
} // end of [cairodraw_clock01]

(* ****** ****** *)

implement
cairodraw_circnum (cr, int) = let
  val (pf | ()) = cairo_save (cr)
  val () = cairo_translate (cr, 0.5, 0.5)
  val () = cairo_arc (cr, 0.0, 0.0, 0.5, 0.0, _2PI)
  val () = cairo_set_source_rgb (cr, 1.0, 1.0, 1.0)
  val () = cairo_fill (cr)
  val utf8 = sprintf ("%i", @(int))
  val () = cairo_set_source_rgb (cr, 1.0, 1.0, 0.0)
  val () = cairo_show_text_inbox (cr, 0.50, 0.50, $UN.castvwtp1 (utf8))
  val () = cairo_restore (pf | cr)
  val () = strptr_free (utf8)
in
  // nothing
end // end of [cairodraw_circnum]

(* ****** ****** *)

(* end of [atspslide_cairodraw.dats] *)
