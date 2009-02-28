/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi.
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
 */

/* ****** ****** */

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef _LIBC_GL_GLUT_CATS
#define _LIBC_GL_GLUT_CATS

/* ****** ****** */

#include <GL/glut.h>

/* ****** ****** */

// Process loop function, see freeglut_main.c
static inline
ats_void_type atslib_glutMainLoop () {
  glutMainLoop () ; return ;
}

/* ****** ****** */

// Display-connected functions, see freeglut_display.c

static inline
ats_void_type
atslib_glutPostWindowRedisplay (int window) {
  glutPostWindowRedisplay (window) ; return ;
}

static inline
ats_void_type
atslib_glutPostRedisplay () { glutPostRedisplay (); return ; }

static inline
ats_void_type
atslib_glutSwapBuffers () { glutSwapBuffers (); return ; }

/* ****** ****** */

// Global callback functions, see freeglut_callbacks.c

static inline
ats_void_type atslib_glutTimerFunc (
  ats_uint_type time
, ats_ptr_type callback
, ats_int_type value
) {
  glutTimerFunc (time, (void (*)(int))callback, value); return ;
}

/* ****** ****** */

ats_void_type
atslib_glutIdleFunc (ats_ptr_type callback) {
  glutIdleFunc ((void (*)(void))callback) ; return ;
}

static inline
ats_void_type
atslib_glutIdleFuncNull () {
  glutIdleFunc ((void (*)(void))0) ; return ;
}

/* ****** ****** */

// Window-specific callback functions, see freeglut_callbacks.c

static inline
ats_void_type
atslib_glutKeyboardFunc (ats_ptr_type callback) {
  glutKeyboardFunc ((void (*)(unsigned char, int, int))callback) ;
  return ;
}

static inline
ats_void_type
atslib_glutMouseFunc (ats_ptr_type callback) {
  glutMouseFunc ((void (*)(int, int, int, int))callback) ;
  return ;
}

static inline
ats_void_type
atslib_glutSpecialFunc (ats_ptr_type callback) {
  glutSpecialFunc ((void (*)(int, int, int))callback) ; return ;
}

static inline
ats_void_type
atslib_glutReshapeFunc (ats_ptr_type callback) {
  glutReshapeFunc ((void (*)(int, int))callback) ; return ;
}

static inline
ats_void_type
atslib_glutVisibilityFunc (ats_ptr_type callback) {
  glutVisibilityFunc ((void (*)(int))callback) ; return ;
}

static inline
ats_void_type
atslib_glutDisplayFunc (ats_ptr_type callback) {
  glutDisplayFunc ((void (*)(void))callback) ; return ;
}

static inline
ats_void_type
atslib_glutMotionFunc (ats_ptr_type callback) {
  glutMotionFunc ((void (*)(int, int))callback) ; return ;
}

static inline
ats_void_type
atslib_glutPassiveMotionFunc (ats_ptr_type callback) {
  glutPassiveMotionFunc ((void (*)(int, int))callback) ; return ;
}

static inline
ats_void_type
atslib_glutEntryFunc (ats_ptr_type callback) {
  glutEntryFunc ((void (*)(int))callback) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glutWireCube_type (ats_double_type size) {
  glutWireCube (size) ; return ;
}

static inline
ats_void_type
atslib_glutWireCube_GLtype (ats_GLdouble_type size) {
  glutWireCube (size) ; return ;
}

//

static inline
ats_void_type
atslib_glutSolidCube_type (ats_double_type size) {
  glutSolidCube (size) ; return ;
}

static inline
ats_void_type
atslib_glutSolidCube_GLtype (ats_GLdouble_type size) {
  glutSolidCube (size) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glutWireSphere_type (
  ats_double_type radius
, ats_int_type slices
, ats_int_type stacks
) {
  glutWireSphere (radius, slices, stacks) ; return ;
}

static inline
ats_void_type
atslib_glutWireSphere_GLtype (
  ats_GLdouble_type radius
, ats_GLint_type slices
, ats_GLint_type stacks
) {
  glutWireSphere (radius, slices, stacks) ; return ;
}

//

static inline
ats_void_type
atslib_glutSolidSphere_type (
  ats_double_type radius
, ats_int_type slices
, ats_int_type stacks
) {
  glutSolidSphere (radius, slices, stacks) ; return ;
}

static inline
ats_void_type
atslib_glutSolidSphere_GLtype (
  ats_GLdouble_type radius
, ats_GLint_type slices
, ats_GLint_type stacks
) {
  glutSolidSphere (radius, slices, stacks) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glutWireCone_type (
  ats_double_type base
, ats_double_type height
, ats_int_type slices
, ats_int_type stacks
) {
  glutWireCone (base, height, slices, stacks) ; return ;
}

static inline
ats_void_type
atslib_glutWireCone_GLtype (
  ats_GLdouble_type base
, ats_GLdouble_type height
, ats_GLint_type slices
, ats_GLint_type stacks
) {
  glutWireCone (base, height, slices, stacks) ; return ;
}

//

static inline
ats_void_type
atslib_glutSolidCone_type (
  ats_double_type base
, ats_double_type height
, ats_int_type slices
, ats_int_type stacks
) {
  glutSolidCone (base, height, slices, stacks) ; return ;
}

static inline
ats_void_type
atslib_glutSolidCone_GLtype (
  ats_GLdouble_type base
, ats_GLdouble_type height
, ats_GLint_type slices
, ats_GLint_type stacks
) {
  glutSolidCone (base, height, slices, stacks) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glutWireTorus_type (
  ats_double_type innerRadius
, ats_double_type outerRadius
, ats_int_type sides
, ats_int_type rings
) {
  glutWireTorus (innerRadius, outerRadius, sides, rings) ; return ;
}

static inline
ats_void_type
atslib_glutWireTorus_GLtype (
  ats_GLdouble_type innerRadius
, ats_GLdouble_type outerRadius
, ats_GLint_type sides
, ats_GLint_type rings
) {
  glutWireTorus (innerRadius, outerRadius, sides, rings) ; return ;
}

//

static inline
ats_void_type
atslib_glutSolidTorus_type (
  ats_double_type innerRadius
, ats_double_type outerRadius
, ats_int_type sides
, ats_int_type rings
) {
  glutSolidTorus (innerRadius, outerRadius, sides, rings) ; return ;
}

static inline
ats_void_type
atslib_glutSolidTorus_GLtype (
  ats_GLdouble_type innerRadius
, ats_GLdouble_type outerRadius
, ats_GLint_type sides
, ats_GLint_type rings
) {
  glutSolidTorus (innerRadius, outerRadius, sides, rings) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glutWireTeapot_type (ats_double_type size) {
  glutWireTeapot (size) ; return ;
}

static inline
ats_void_type
atslib_glutWireTeapot_GLtype (ats_GLdouble_type size) {
  glutWireTeapot (size) ; return ;
}

//

static inline
ats_void_type
atslib_glutSolidTeapot_type (ats_double_type size) {
  glutSolidTeapot (size) ; return ;
}

static inline
ats_void_type
atslib_glutSolidTeapot_GLtype (ats_GLdouble_type size) {
  glutSolidTeapot (size) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glutWireDodecahedron () { glutWireDodecahedron () ; return ; }

static inline
ats_void_type
atslib_glutSolidDodecahedron () { glutSolidDodecahedron () ; return ; }

static inline
ats_void_type
atslib_glutWireOctahedron () { glutWireOctahedron () ; return ; }

static inline
ats_void_type
atslib_glutSolidOctahedron () { glutSolidOctahedron () ; return ; }

static inline
ats_void_type
atslib_glutWireTetrahedron () { glutWireTetrahedron () ; return ; }

static inline
ats_void_type
atslib_glutSolidTetrahedron () { glutSolidTetrahedron () ; return ; }

static inline
ats_void_type
atslib_glutWireIcosahedron () { glutWireIcosahedron () ; return ; }

static inline
ats_void_type
atslib_glutSolidIcosahedron () { glutSolidIcosahedron () ; return ; }

/* ****** ****** */

#endif /* _LIBC_GL_GLUT_CATS */

/* end of [glut.cats] */
