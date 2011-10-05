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

#define ATS_STALOADFLAG 0

(* ****** ****** *)

staload "contrib/GL/SATS/gl.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

abstype slide_type
typedef slide = slide_type
typedef slideopt = Option (slide)

fun slide_get_by_indx (indx: int): slideopt
fun slide_get_by_name (name: string): slideopt

(* ****** ****** *)
//
// atspslide_cairodraw
//
(* ****** ****** *)
(*
** HX-2011-10-01:
** a clock that may be used as background of a slide
*)
fun cairodraw_clock01 {l:agz} (cr: !cairo_ref l): void

(* ****** ****** *)
//
// atspslide_glTexture 
//
(* ****** ****** *)

fun glTexture_make_cairo_ref {l:agz}
  (fmt: GLenum_format (4), cr: !cairo_ref (l)): GLtexture
// end of [glTexture_make_cairo]

(* ****** ****** *)
//
// HX: vdir=0/1:up/down
//
fun glTexture_mapout_rect {i:int} {d:two} (
  texture: !GLtexture(i), width: double, height: double, vdir: int(d)
) : void // end of [glTexture_mapout_rect]

//
// HX: front(1), right(2), back(3), left(4), top(5) and bottom(6)
//
fun glTexture_mapout_rect12
  {i1,i2:int} {d:two} (
  texture1: !GLtexture(i1)
, texture2: !GLtexture(i2)
, width: double, height: double, vdir: int(d)
) : void // end of [glTexture_mapout_rect12]

fun glTexture_mapout_rect16
  {i1,i2:int} {d:two} (
  texture1: !GLtexture(i1)
, texture2: !GLtexture(i2)
, width: double, height: double, vdir: int(d)
) : void // end of [glTexture_mapout_rect16]

(* ****** ****** *)

(* end of [atspslide.sats] *)
