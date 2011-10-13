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
//
abstype slide_type
typedef slide = slide_type
//
fun slideopt_get_by_indx (indx: int): Option_vt (slide)
fun slideopt_get_by_name (name: string): Option_vt (slide)
//
(* ****** ****** *)
//
// atspslide_cairodraw
//
(* ****** ****** *)
(*
** HX-2011-10-01:
** A clock that may be used as a layover
** The dimension of the clock is 1.0 by 1.0
*)
fun cairodraw_clock01 {l:agz} (cr: !cairo_ref l): void

(*
** HX-2011-10-01:
** A given number at the center of a circle
** The dimension of the enclosing square is 1.0 by 1.0
*)
fun cairodraw_circnum {l:agz} (cr: !cairo_ref l, int: int): void

fun cairodraw_slide {l:agz} (cr: !cairo_ref l, x: slide): void
//
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

fun glTexture_mapout_rect14
  {i1,i2:int} {d:two} (
  texture1: !GLtexture(i1)
, texture2: !GLtexture(i2)
, width: double, height: double, vdir: int(d)
) : void // end of [glTexture_mapout_rect14]

fun glTexture_mapout_rect15
  {i1,i2:int} {d:two} (
  texture1: !GLtexture(i1)
, texture2: !GLtexture(i2)
, width: double, height: double, vdir: int(d)
) : void // end of [glTexture_mapout_rect15]

fun glTexture_mapout_rect16
  {i1,i2:int} {d:two} (
  texture1: !GLtexture(i1)
, texture2: !GLtexture(i2)
, width: double, height: double, vdir: int(d)
) : void // end of [glTexture_mapout_rect16]

(* ****** ****** *)
//
// HX-2011-10-12:
// vdir=0/1:up/down
// angle: goes from 0 to PI
// if angle = 0, this is the same as glTexture_mapout_rect
// if angle = PI/2, then the front half of the cylinder is covered
// if angle = PI, then the whole cylinder is covered
//
fun glTexture_mapout_cylinder
  {i:int} {d:two} {n:pos} (
  texture: !GLtexture(i)
, width: double, height: double, angle: double, vdir: int(d), nslice: int(n)
) : void // end of [glTexture_mapout_cylinder]

(* ****** ****** *)

(* end of [atspslide.sats] *)
