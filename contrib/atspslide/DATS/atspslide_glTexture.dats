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

staload "contrib/GL/SATS/gl.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

staload "contrib/atspslide/SATS/atspslide.sats"

(* ****** ****** *)

implement
glTexture_make_cairo_ref
  (imgfmt, cr) = let
//
  val img = cairo_get1_target (cr)
  val [l_data:addr] p_data = cairo_image_surface_get_data (img)
//
(*
// HX: it seems OK even if width and height are not powers of 2
*)
//
  val [w:int] width = cairo_image_surface_get_width (img)
  val [h:int] height = cairo_image_surface_get_height (img)
  val stride = cairo_image_surface_get_stride (img)
//
(*
  val () = printf ("width = %i\n", @(width))
  val () = printf ("height = %i\n", @(height))
  val () = printf ("stride = %i\n", @(stride))
*)
//
  val () = assertloc (stride = 4*width)
//
  var texture: GLtexture
//
  val () = glGenTexture (texture)
  val () = glBindTexture (GL_TEXTURE_2D, texture)
  val () = glTexParameteri
    (GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, (GLint)GL_LINEAR)
  val () = glTexParameteri
    (GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, (GLint)GL_LINEAR)
//
  prval (pfarr, fpfarr) =
    __assert (img) where {
    typedef T = GLarray3 (GLubyte, w, h, 4)
    extern praxi __assert {l:agz}
      (img: !cairo_surface_ref l): (T@l_data, T@l_data -<lin,prf> void)
    // end of [__assert]
  } // end of [prval]
//
  val () = glTexImage2D (
    GL_TEXTURE_2D
  , (GLint)0, (GLint)GL_RGBA(*internal format*)
  , (GLsizei)width
  , (GLsizei)height
  , 0(*border*), imgfmt, GL_UNSIGNED_BYTE
  , !p_data
  ) // end of [val]
//
  val () = assertloc (glGetError() = GL_NO_ERROR)
//
  val () = cairo_surface_destroy (img)
//
  prval () = fpfarr (pfarr)
//
in
  texture (* GLtexture *)
end // end of [glTexture_make_cairo_ref]

(* ****** ****** *)

implement
glTexture_mapout_rect
  (texture, wid, hgt, vdir) = let
//
  val () = glBindTexture (GL_TEXTURE_2D, texture)
//
  val (pfmat | ()) = glPushMatrix ()
//
  val () = glEnable (GL_TEXTURE_2D)
  val () = glTexEnvi
    (GL_TEXTURE_ENV, GL_TEXTURE_ENV_MODE, (GLint)GL_REPLACE)
  val (pfbeg | ()) = glBegin (GL_QUADS)
  val () = glTexCoord2d (0.0, 0.0)
  val lower = vdir and upper = 1-vdir
  val () = glVertex2d (0.0, lower * hgt)
//
  val () = glTexCoord2d (0.0, 1.0)
  val () = glVertex2d (0.0, upper * hgt)
//
  val () = glTexCoord2d (1.0, 1.0)
  val () = glVertex2d (wid, upper * hgt)
//
  val () = glTexCoord2d (1.0, 0.0)
  val () = glVertex2d (wid, lower * hgt)
//
  val () = glEnd (pfbeg | (*none*))
  val () = glDisable (GL_TEXTURE_2D)
//
  val () = glPopMatrix (pfmat | (*none*))
//
in
  // nothing
end // end of [glTexture_mapout_rect]

(* ****** ****** *)

(* end of [atspslide_utils.dats] *)
