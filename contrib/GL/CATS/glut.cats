/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Power of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi.
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
*/

/* ****** ****** */

// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: December, 2009

/* ****** ****** */

#ifndef ATSTRIB_GL_GLUT_CATS
#define ATSTRIB_GL_GLUT_CATS

/* ****** ****** */

#include <GL/glut.h>

/* ****** ****** */

/*
** Initialization functions, see fglut_init.c
*/
#define atsctrb_glutInit glutInit
#define atsctrb_glutInitWindowPosition glutInitWindowPosition
#define atsctrb_glutInitWindowSize glutInitWindowSize
#define atsctrb_glutInitDisplayMode glutInitDisplayMode
#define atsctrb_glutInitDisplayString glutInitDisplayString

/* ****** ****** */

/*
** Process loop function, see freeglut_main.c
*/
#define atsctrb_glutMainLoop glutMainLoop

/* ****** ****** */

/*
** Window management functions, see freeglut_window.c
*/
#define atsctrb_glutCreateWindow glutCreateWindow
#define atsctrb_glutCreateSubWindow glutCreateSubWindow
#define atsctrb_glutDestroyWindow atsctrb_glutDestroyWindow
#define atsctrb_glutGetWindow glutGetWindow
#define atsctrb_glutSetWindow glutSetWindow
#define atsctrb_glutSetWindowTitle glutSetWindowTitle
#define atsctrb_glutSetIconTitle glutSetIconTitle
#define atsctrb_glutReshapeWindow glutReshapeWindow
#define atsctrb_glutPositionWindow glutPositionWindow
#define atsctrb_glutShowWindow glutShowWindow
#define atsctrb_glutHideWindow glutHideWindow
#define atsctrb_glutIconifyWindow glutIconifyWindow
#define atsctrb_glutPushWindow glutPushWindow
#define atsctrb_glutPopWindow glutPopWindow
#define atsctrb_glutFullScreen glutFullScreen

/* ****** ****** */

/*
** Display-connected functions, see freeglut_display.c
*/
#define atsctrb_glutPostWindowRedisplay glutPostWindowRedisplay
#define atsctrb_glutPostRedisplay glutPostRedisplay
#define atsctrb_glutSwapBuffers glutSwapBuffers

/* ****** ****** */

// Global callback functions, see freeglut_callbacks.c

static inline
ats_void_type
atsctrb_glutTimerFunc (
  ats_uint_type time
, ats_ptr_type callback
, ats_int_type value
) {
  glutTimerFunc (time, (void (*)(int))callback, value); return ;
} // end of [atsctrb_glutTimerFunc]

/* ****** ****** */

static inline
ats_void_type
atsctrb_glutIdleFunc
  (ats_ptr_type callback) {
  glutIdleFunc ((void (*)(void))callback) ; return ;
} // end of [atsctrb_glutIdleFunc]

static inline
ats_void_type
atsctrb_glutIdleFunc_null () {
  glutIdleFunc ((void (*)(void))0) ; return ;
} // end of [atsctrb_glutIdleFunc_null]

/* ****** ****** */

/*
** Window-specific callback functions, see freeglut_callbacks.c
*/

static inline
ats_void_type
atsctrb_glutKeyboardFunc
  (ats_ptr_type callback) {
  glutKeyboardFunc ((void (*)(unsigned char, int, int))callback) ;
  return ;
} // end of [atsctrb_glutKeyboardFunc]

static inline
ats_void_type
atsctrb_glutMouseFunc
  (ats_ptr_type callback) {
  glutMouseFunc ((void (*)(int, int, int, int))callback) ;
  return ;
} // end of [atsctrb_glutMouseFunc]

static inline
ats_void_type
atsctrb_glutSpecialFunc
  (ats_ptr_type callback) {
  glutSpecialFunc ((void (*)(int, int, int))callback) ; return ;
} // end of [atsctrb_glutSpecialFunc]

static inline
ats_void_type
atsctrb_glutReshapeFunc
  (ats_ptr_type callback) {
  glutReshapeFunc ((void (*)(int, int))callback) ; return ;
} // end of [atsctrb_glutReshapeFunc]

static inline
ats_void_type
atsctrb_glutVisibilityFunc
  (ats_ptr_type callback) {
  glutVisibilityFunc ((void (*)(int))callback) ; return ;
} // end of [atsctrb_glutVisibilityFunc]

static inline
ats_void_type
atsctrb_glutDisplayFunc
  (ats_ptr_type callback) {
  glutDisplayFunc ((void (*)(void))callback) ; return ;
} // end of [atsctrb_glutDisplayFunc]

static inline
ats_void_type
atsctrb_glutMotionFunc
  (ats_ptr_type callback) {
  glutMotionFunc ((void (*)(int, int))callback) ; return ;
} // end of [atsctrb_glutMotionFunc]

static inline
ats_void_type
atsctrb_glutPassiveMotionFunc
  (ats_ptr_type callback) {
  glutPassiveMotionFunc ((void (*)(int, int))callback) ; return ;
} // end of [atsctrb_glutPassiveMotionFunc]

static inline
ats_void_type
atsctrb_glutEntryFunc
  (ats_ptr_type callback) {
  glutEntryFunc ((void (*)(int))callback) ; return ;
} // end of [atsctrb_glutEntryFunc]

/* ****** ****** */

#define atsctrb_glutGet glutGet
#define atsctrb_glutDeviceGet glutDeviceGet
#define atsctrb_glutGetModifiers glutGetModifiers
#define atsctrb_glutLayerGet glutLayerGet

/* ****** ****** */

#define atsctrb_glutWireCube glutWireCube
#define atsctrb_glutSolidCube glutSolidCube

#define atsctrb_glutWireSphere glutWireSphere
#define atsctrb_glutSolidSphere glutSolidSphere

/* ****** ****** */

#define atsctrb_glutWireCone glutWireCone
#define atsctrb_glutSolidCone glutSolidCone

/* ****** ****** */

#define atsctrb_glutWireTorus glutWireTorus
#define atsctrb_glutSolidTorus glutSolidTorus

/* ****** ****** */

#define atsctrb_glutWireTeapot glutWireTeapot
#define atsctrb_glutSolidTeapot glutSolidTeapot

/* ****** ****** */

#define atsctrb_glutWireDodecahedron glutWireDodecahedron
#define atsctrb_glutSolidDodecahedron glutSolidDodecahedron

#define atsctrb_glutWireOctahedron glutWireOctahedron
#define atsctrb_glutSolidOctahedron glutSolidOctahedron

#define atsctrb_glutWireTetrahedron glutWireTetrahedron
#define atsctrb_glutSolidTetrahedron glutSolidTetrahedron

#define atsctrb_glutWireIcosahedron glutWireIcosahedron ()
#define atsctrb_glutSolidIcosahedron glutSolidIcosahedron ()

/* ****** ****** */

#endif /* ATSTRIB_GL_GLUT_CATS */

/* end of [glut.cats] */
