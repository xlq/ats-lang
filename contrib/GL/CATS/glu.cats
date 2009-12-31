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

#ifndef ATSCTRB_GL_GLU_CATS
#define ATSCTRB_GL_GLU_CATS

/* ****** ****** */

static inline
ats_void_type
atsctrb_gluLookAt_double (
  ats_double_type eyeX
, ats_double_type eyeY
, ats_double_type eyeZ
, ats_double_type centerX
, ats_double_type centerY
, ats_double_type centerZ
, ats_double_type upX
, ats_double_type upY
, ats_double_type upZ
) {
  gluLookAt(
    eyeX, eyeY, eyeZ, centerX, centerY, centerZ, upX, upY, upZ
  ) ; return ;
} // end of [atsctrb_gluLookAt_double]

/* ****** ****** */

static inline
ats_void_type
atsctrb_gluOrtho2D_double (
  ats_double_type lft, ats_double_type rgh
, ats_double_type bot, ats_double_type top
) {
  gluOrtho2D(lft, rgh, bot, top) ; return ;
} // end of [atsctrb_gluOrtho2D_double]

/* ****** ****** */

static inline
ats_void_type
atsctrb_gluPerspective_double (
  ats_double_type fovy, ats_double_type aspect
, ats_double_type zNear, ats_double_type zFar
) {
  gluPerspective(fovy, aspect, zNear, zFar) ; return ;
} // end of [atsctrb_gluPerspective_double]

static inline
ats_void_type
atsctrb_gluPerspective_GLdouble (
  ats_GLdouble_type fovy, ats_GLdouble_type aspect
, ats_GLdouble_type zNear, ats_GLdouble_type zFar
) {
  gluPerspective(fovy, aspect, zNear, zFar) ; return ;
} // end of [atsctrb_gluPerspective_GLdouble]

/* ****** ****** */

static inline
ats_GLint_type
atsctrb_gluUnProject (
  ats_GLdouble_type winX
, ats_GLdouble_type winY
, ats_GLdouble_type winZ
, ats_ref_type model
, ats_ref_type project
, ats_ref_type viewport
, ats_ref_type objX
, ats_ref_type objY
, ats_ref_type objZ
) {
  return gluUnProject (
    winX, winY, winZ
  , (GLdouble*)model, (GLdouble*)project, (GLint*)viewport
  , (GLdouble*)objX, (GLdouble*)objY, (GLint*)objZ
  ) ; // end of [return]
} // end of [atsctrb_gluUnProject]

/* ****** ****** */

#endif /* ATSCTRB_GL_GLU_CATS */

/* end of [glu.cats] */
