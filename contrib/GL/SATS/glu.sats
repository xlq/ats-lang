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

// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: December, 2009

(* ****** ****** *)

staload "contrib/GL/SATS/gl.sats"

(* ****** ****** *)

%{#
#include "contrib/GL/CATS/glu.cats"
%}

(* ****** ****** *)

(*
GLAPI void GLAPIENTRY gluLookAt (
  GLdouble eyeX, GLdouble eyeY, GLdouble eyeZ
, GLdouble centerX, GLdouble centerY, GLdouble centerZ
, GLdouble upX, GLdouble upY, GLdouble upZ
) ;
*)

typedef gluLookAt_type (a:t@ype) = (
  a(*eyeX*), a(*eyeY*), a(*eyeZ*)
, a(*centerX*), a(*centerY*), a(*centerZ*)
, a(*upX*), a(*upY*), a(*upZ*)
) -<fun1> void // end of [gluLookAt_type]

symintr gluLookAt

fun gluLookAt_double : gluLookAt_type (double)
  = "atsctrb_gluLookAt_double"
overload gluLookAt with gluLookAt_double

fun gluLookAt_GLdouble : gluLookAt_type (GLdouble)
  = "atsctrb_gluLookAt_GLdouble"
overload gluLookAt with gluLookAt_GLdouble

(* ****** ****** *)

(*
GLAPI void GLAPIENTRY gluOrtho2D (
  GLdouble left, GLdouble right, GLdouble bottom, GLdouble top
) ;
*)

typedef gluOrtho2D_type (a:t@ype) =
  (a(*lft*), a(*rgh*), a(*bot*), a(*top*)) -<fun1> void

symintr gluOrtho2D

fun gluOrtho2D_double : gluOrtho2D_type (double)
  = "atsctrb_gluOrtho2D_double"
overload gluOrtho2D with gluOrtho2D_double

fun gluOrtho2D_GLdouble : gluOrtho2D_type (GLdouble)
  = "atsctrb_gluOrtho2D_GLdouble"
overload gluOrtho2D with gluOrtho2D_GLdouble

(* ****** ****** *)

(*
GLAPI void GLAPIENTRY gluPerspective (GLdouble fovy, GLdouble aspect, GLdouble zNear, GLdouble zFar);
*)
typedef gluPerspective_type (a:t@ype) =
  (a(*fovy*), a(*aspect*), a(*zNear*), a(*zFar*)) -<fun1> void
// end of [gluPerspective_type]

symintr gluPerspective

fun gluPerspective_double : gluPerspective_type (double)
  = "atsctrb_gluPerspective_double"
overload gluPerspective with gluPerspective_double

fun gluPerspective_GLdouble : gluPerspective_type (GLdouble)
  = "atsctrb_gluPerspective_GLdouble"
overload gluPerspective with gluPerspective_GLdouble

(* ****** ****** *)

(*
GLAPI GLint GLAPIENTRY gluUnProject (
  GLdouble winX, GLdouble winY, GLdouble winZ
, const GLdouble *model, const GLdouble *proj
, const GLint *view
, GLdouble* objX, GLdouble* objY, GLdouble* objZ
) ;
*)

fun gluUnProject (
    winX: GLdouble
  , winY: GLdouble
  , winZ: GLdouble
  , model: &(@[GLdouble][16])
  , project: &(@[GLdouble][16])
  , viewport: &(@[GLint][4])
  , objX: &GLdouble? >> GLdouble
  , objY: &GLdouble? >> GLdouble
  , objZ: &GLdouble? >> GLdouble
  ) : GLint
  = "atsctrb_gluUnProject"

(* ****** ****** *)

(* end of [glu.sats] *)
