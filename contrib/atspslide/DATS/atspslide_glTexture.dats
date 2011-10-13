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

staload "libc/SATS/math.sats"

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
  val width = cairo_image_surface_get_width (img)
  val [w:int] width = int1_of_int (width)
  val height = cairo_image_surface_get_height (img)
  val [h:int] height = int1_of_int (height)
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
  (gltext, wid, hgt, vdir) = let
//
  val () = glBindTexture (GL_TEXTURE_2D, gltext)
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
in
  // nothing
end // end of [glTexture_mapout_rect]

(* ****** ****** *)

implement
glTexture_mapout_rect12
  (gltext1, gltext2, wid, hgt, vdir) = let
  val () = glTexture_mapout_rect (gltext1, wid, hgt, vdir)
  val (pfmat | ()) = glPushMatrix ()
  val () = glTranslated (wid, 0.0, 0.0)
  val () = glRotated (90.0, 0.0, 1.0, 0.0)
  val () = glTexture_mapout_rect (gltext2, wid, hgt, vdir)
  val () = glPopMatrix (pfmat | (*none*))
in
  // nothing
end // end of [glTexture_mapout_rect12]

(* ****** ****** *)

implement
glTexture_mapout_rect14
  (gltext1, gltext2, wid, hgt, vdir) = let
  val () = glTexture_mapout_rect (gltext1, wid, hgt, vdir)
  val (pfmat | ()) = glPushMatrix ()
  val () = glTranslated (0.0, 0.0, ~wid)
  val () = glRotated (~90.0, 0.0, 1.0, 0.0)
  val () = glTexture_mapout_rect (gltext2, wid, hgt, vdir)
  val () = glPopMatrix (pfmat | (*none*))
in
  // nothing
end // end of [glTexture_mapout_rect14]

(* ****** ****** *)

implement
glTexture_mapout_rect15
  (gltext1, gltext2, wid, hgt, vdir) = let
  val () = glTexture_mapout_rect (gltext1, wid, hgt, vdir)
  val (pfmat | ()) = glPushMatrix ()
  val () = glTranslated (0.0, wid, 0.0)
  val () = glRotated (~90.0, 1.0, 0.0, 0.0)
  val () = glTexture_mapout_rect (gltext2, wid, hgt, vdir)
  val () = glPopMatrix (pfmat | (*none*))
in
  // nothing
end // end of [glTexture_mapout_rect15]

(* ****** ****** *)

implement
glTexture_mapout_rect16
  (gltext1, gltext2, wid, hgt, vdir) = let
  val () = glTexture_mapout_rect (gltext1, wid, hgt, vdir)
  val (pfmat | ()) = glPushMatrix ()
  val () = glTranslated (0.0, 0.0, ~wid)
  val () = glRotated (90.0, 1.0, 0.0, 0.0)
  val () = glTexture_mapout_rect (gltext2, wid, hgt, vdir)
  val () = glPopMatrix (pfmat | (*none*))
in
  // nothing
end // end of [glTexture_mapout_rect16]

(* ****** ****** *)

(*
fun glTexture_mapout_cylinder
  {i:int} {d:two} {n:pos} (
  texture: !GLtexture(i)
, width: double, height: double, angle: double, vdir: int(d), nslice: int(n)
) : void // end of [glTexture_mapout_cylinder]
*)
implement
glTexture_mapout_cylinder
  {i} {d} {n}
  (gltext, wid, hgt, angle, vdir, n) = let
//
  val dt = angle / n
  val angle2 = angle / 2
//
  #define EPSILON 1E-2 // HX: small enough
  val rad = (
    if angle >= EPSILON then wid / angle else ~1.0
  ) : double // end of [val]
  macdef xeval (t1, n, k1) = 
    if angle >= EPSILON then
      rad * sin ,(t1) else wid * (1.0 * ,(k1) / ,(n) - 0.5)
    // end of [if]
  macdef zeval (t1, n, k1) =
    if angle >= EPSILON then
      rad * (~1.0 + cos ,(t1)) else wid * (~square (1.0 * ,(k1) / ,(n) - 0.5) * angle2)
    // end of [if]
//
  fun loop
    {k:nat | k <= n} .<n-k>. (
    x0: double
  , y0: double
  , z0: double
  , t0: double, k0: int k
  ) :<cloref1> void =
    if k0 < n then let
      val k1 = k0 + 1
      val t1 = t0 + dt
      val x1 = xeval (t1, n, k1)
      val y1 = y0
      val z1 = zeval (t1, n, k1)
      val r0 = 1.0 * k0 / n
      val r1 = 1.0 * k1 / n
//
      val lower = vdir and upper = 1-vdir
//
      val () = glTexCoord2d (r0, 0.0)
      val () = glVertex3d (x0, y0+lower*hgt, z0)
      val () = glTexCoord2d (r0, 1.0)
      val () = glVertex3d (x0, y0+upper*hgt, z0)
      val () = glTexCoord2d (r1, 1.0)
      val () = glVertex3d (x1, y1+upper*hgt, z1)
      val () = glTexCoord2d (r1, 0.0)
      val () = glVertex3d (x1, y1+lower*hgt, z1)
    in
      loop (x1, y1, z1, t1, k1)
    end // end of [if]
//
  val t0 = ~angle2
  val x0 = xeval (t0, n, 0)
  val y0 = ~hgt / 2
  val z0 = zeval (t0, n, 0)
//
  val () = glBindTexture (GL_TEXTURE_2D, gltext)
//
  val () = glEnable (GL_TEXTURE_2D)
  val () = glTexEnvi
    (GL_TEXTURE_ENV, GL_TEXTURE_ENV_MODE, (GLint)GL_REPLACE)
  val (pfbeg | ()) = glBegin (GL_QUADS)
  val () = loop (x0, y0, z0, t0, 0)
  val () = glEnd (pfbeg | (*none*))
  val () = glDisable (GL_TEXTURE_2D)
in
  // nothing
end // end of [glTexture_mapout_cylinder]

(* ****** ****** *)

(* end of [atspslide_glTexture.dats] *)
