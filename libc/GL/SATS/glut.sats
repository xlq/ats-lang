(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

// author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "libc/GL/SATS/gl.sats"

(* ****** ****** *)

%{#

#include "libc/GL/CATS/glut.cats"

%}

(* ****** ****** *)

macdef GLUT_LEFT_BUTTON = $extval (int, "GLUT_LEFT_BUTTON")
macdef GLUT_MIDDLE_BUTTON = $extval (int, "GLUT_MIDDLE_BUTTON")
macdef GLUT_RIGHT_BUTTON = $extval (int, "GLUT_RIGHT_BUTTON")

macdef GLUT_DOWN = $extval (int, "GLUT_DOWN")

(* ****** ****** *)

// Process loop function, see freeglut_main.c
fun glutMainLoop (): void = "atslib_glutMainLoop"

(* ****** ****** *)

// Display-connected functions, see freeglut_display.c

fun glutPostWindowRedisplay (window: int): void
  = "atslib_glutPostWindowRedisplay"

fun glutPostRedisplay (): void = "atslib_glutPostRedisplay"

fun glutSwapBuffers (): void = "atslib_glutSwapBuffers"

(* ****** ****** *)

// Global callback functions, see freeglut_callbacks.c

fun glutTimerFunc
  (time: uint, callback: (int) -> void, value: int): void
  = "atslib_glutTimerFunc"

fun glutIdleFunc (callback: () -> void): void
  = "atslib_glutIdleFunc"

fun glutIdleFuncNull (): void = "atslib_glutIdleFuncNull"

(* ****** ****** *)

// Window-specific callback functions, see freeglut_callbacks.c

fun glutKeyboardFunc
  (callback: (uchar, int, int) -> void): void
  = "atslib_glutKeyboardFunc"

fun glutMouseFunc
  (callback: (int, int, int, int) -> void): void
  = "atslib_glutMouseFunc"

fun glutSpecialFunc
  (callback: (int, int, int) -> void): void
  = "atslib_glutSpecialFunc"

fun glutReshapeFunc
  (callback: (int, int) -> void): void
  = "atslib_glutReshapeFunc"

fun glutVisibilityFunc
  (callback: (int) -> void): void = "atslib_glutVisibilityFunc"

fun glutDisplayFunc
  (callback: () -> void): void = "atslib_glutDisplayFunc"

fun glutMotionFunc
  (callback: (int, int) -> void): void
  = "atslib_glutMotionFunc"

fun glutPassiveMotionFunc
  (callback: (int, int) -> void): void
  = "atslib_glutPassiveMotionFunc"

fun glutEntryFunc
  (callback: (int) -> void): void = "atslib_glutEntryFunc"

(* ****** ****** *)

symintr glutWireCube
fun glutWireCube_type (size: double): void = "atslib_glutWireCube_type"
fun glutWireCube_GLtype (size: GLdouble): void = "atslib_glutWireCube_GLtype"
overload glutWireCube with glutWireCube_type
overload glutWireCube with glutWireCube_GLtype

//

symintr glutSolidCube
fun glutSolidCube_type (size: double): void = "atslib_glutSolidCube_type"
fun glutSolidCube_GLtype (size: GLdouble): void = "atslib_glutSolidCube_GLtype"
overload glutSolidCube with glutSolidCube_type
overload glutSolidCube with glutSolidCube_GLtype

//

symintr glutWireSphere

fun glutWireSphere_type
  (radius: double, slices: int, stacks: int): void
  = "atslib_glutWireSphere_type"

fun glutWireSphere_GLtype
  (radius: GLdouble, slices: GLint, stacks: GLint): void
  = "atslib_glutWireSphere_GLtype"

overload glutWireSphere with glutWireSphere_type
overload glutWireSphere with glutWireSphere_GLtype

//

symintr glutSolidSphere

fun glutSolidSphere_type
  (radius: double, slices: int, stacks: int): void
  = "atslib_glutSolidSphere_type"

fun glutSolidSphere_GLtype
  (radius: GLdouble, slices: GLint, stacks: GLint): void
  = "atslib_glutSolidSphere_GLtype"

overload glutSolidSphere with glutSolidSphere_type
overload glutSolidSphere with glutSolidSphere_GLtype

//

symintr glutWireCone

fun glutWireCone_type
  (base: double, height: double, slices: int, stacks: int): void
  = "atslib_glutWireCone_type"

fun glutWireCone_GLtype
  (base: GLdouble, height: GLdouble, slices: GLint, stacks: GLint): void
  = "atslib_glutWireCone_GLtype"

overload glutWireCone with glutWireCone_type
overload glutWireCone with glutWireCone_GLtype

//

symintr glutSolidCone

fun glutSolidCone_type
  (base: double, height: double, slices: int, stacks: int): void
  = "atslib_glutSolidCone_type"

fun glutSolidCone_GLtype
  (base: GLdouble, height: GLdouble, slices: GLint, stacks: GLint): void
  = "atslib_glutSolidCone_GLtype"

overload glutSolidCone with glutSolidCone_type
overload glutSolidCone with glutSolidCone_GLtype

//

symintr glutWireTorus

fun glutWireTorus_type
  (innerRadius: double, outerRadius: double, sides: int, rings: int): void
  = "atslib_glutWireTorus_type"

fun glutWireTorus_GLtype
  (innerRadius: GLdouble, outerRadius: GLdouble, sides: GLint, rings: GLint): void
  = "atslib_glutWireTorus_GLtype"

overload glutWireTorus with glutWireTorus_type
overload glutWireTorus with glutWireTorus_GLtype

symintr glutSolidTorus

fun glutSolidTorus_type
  (innerRadius: double, outerRadius: double, sides: int, rings: int): void
  = "atslib_glutSolidTorus_type"

fun glutSolidTorus_GLtype
  (innerRadius: GLdouble, outerRadius: GLdouble, sides: GLint, rings: GLint): void
  = "atslib_glutSolidTorus_GLtype"

overload glutSolidTorus with glutSolidTorus_type
overload glutSolidTorus with glutSolidTorus_GLtype

(* ****** ****** *)

symintr glutWireTeapot
fun glutWireTeapot_type (size: double): void = "atslib_glutWireTeapot_type"
fun glutWireTeapot_GLtype (size: GLdouble): void = "atslib_glutWireTeapot_GLtype"
overload glutWireTeapot with glutWireTeapot_type
overload glutWireTeapot with glutWireTeapot_GLtype

//

symintr glutSolidTeapot
fun glutSolidTeapot_type (size: double): void = "atslib_glutSolidTeapot_type"
fun glutSolidTeapot_GLtype (size: GLdouble): void = "atslib_glutSolidTeapot_GLtype"
overload glutSolidTeapot with glutSolidTeapot_type
overload glutSolidTeapot with glutSolidTeapot_GLtype

(* ****** ****** *)

fun glutWireDodecahedron (): void = "atslib_glutWireDodecahedron"
fun glutSolidDodecahedron (): void = "atslib_glutSolidDodecahedron"

fun glutWireOctahedron (): void = "atslib_glutWireOctahedron"
fun glutSolidOctahedron (): void = "atslib_glutSolidOctahedron"

fun glutWireTetrahedron (): void = "atslib_glutWireTetrahedron"
fun glutSolidTetrahedron (): void = "atslib_glutSolidTetrahedron"

fun glutWireIcosahedron (): void = "atslib_glutWireIcosahedron"
fun glutSolidIcosahedron (): void = "atslib_glutSolidIcosahedron"

(* ****** ****** *)

(* end of [glut.sats] *)
