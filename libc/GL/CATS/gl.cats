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

#ifndef ATS_LIBC_GL_GL_CATS
#define ATS_LIBC_GL_GL_CATS

/* ****** ****** */

#include <stdio.h>

/* ****** ****** */

#include <GL/gl.h>

/* ****** ****** */

typedef GLboolean ats_GLboolean_type ;

typedef GLenum ats_GLenum_type ;
typedef GLbitfield ats_GLbitfield_type ;

typedef GLdouble ats_GLdouble_type ;
typedef GLfloat ats_GLfloat_type ;
typedef GLint ats_GLint_type ;
typedef GLshort ats_GLshort_type ;

typedef GLsizei ats_GLsizei_type ;

typedef GLclampd ats_GLclampd_type ;
typedef GLclampf ats_GLclampf_type ;

/* ****** ****** */

static inline
ats_int_type
ats_int_of_GLenum (GLenum x) { return x ; }

static inline
ats_GLint_type
atslib_GLint_of_int (int x) { return x ; }

static inline
ats_GLsizei_type
atslib_GLsizei_of_int (int x) { return x ; }

static inline
ats_GLfloat_type
atslib_GLfloat_of_doube (double x) { return x ; }

static inline
ats_GLbitfield_type
atslib_lor_GLbitfield_GLbitfield (GLbitfield b1, GLbitfield b2) {
  return (b1 | b2) ;
}

/* ****** ****** */

// Miscellaneous functions

static inline
ats_void_type
atslib_glClearColor_double (
  ats_double_type red
, ats_double_type green
, ats_double_type blue
, ats_double_type alpha
) {
  glClearColor (red, green, blue, alpha) ; return ;
}

static inline
ats_void_type
atslib_glClearColor_GLclampf (
  ats_GLclampf_type red
, ats_GLclampf_type green
, ats_GLclampf_type blue
, ats_GLclampf_type alpha
) {
  glClearColor (red, green, blue, alpha) ; return ;
}

//

static inline
ats_void_type
atslib_glClear (ats_GLbitfield_type mask) {
  glClear (mask) ; return ;
}

//

static inline
ats_void_type
atslib_glColorMask (
  ats_GLboolean_type red
, ats_GLboolean_type green
, ats_GLboolean_type blue
, ats_GLboolean_type alpha
) {
  glColorMask (red, green, blue, alpha) ; return ;
}

//

static inline
ats_void_type atslib_glAlphaFunc
  (ats_GLenum_type func, ats_GLclampf_type ref) {
  glAlphaFunc (func, ref) ; return ;
}

//

static inline
ats_void_type atslib_glBlendFunc
  (ats_GLenum_type sfactor, ats_GLenum_type dfactor) {
  glBlendFunc (sfactor, dfactor) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glPointSize_double (ats_double_type width) {
  glPointSize (width) ; return ;
}

static inline
ats_void_type
atslib_glPointSize_GLfloat (ats_GLfloat_type width) {
  glPointSize (width) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glLineWidth_double (ats_double_type width) {
  glLineWidth (width) ; return ;
}

static inline
ats_void_type
atslib_glLineWidth_GLfloat (ats_GLfloat_type width) {
  glLineWidth (width) ; return ;
}

/* ****** ****** */

static inline
ats_void_type atslib_glEnable (ats_GLenum_type cap) {
  glEnable (cap) ; return ;
}

static inline
ats_void_type atslib_glDisable (ats_GLenum_type cap) {
  glDisable (cap) ; return ;
}

//

static inline
ats_void_type atslib_glClipPlane
  (ats_GLenum_type plane, ats_ptr_type eqn) {
  glClipPlane (plane, (GLdouble*)eqn) ; return ;
}

static inline
ats_void_type atslib_glGetClipPlane
  (ats_GLenum_type plane, ats_ptr_type eqn) {
  glGetClipPlane (plane, (GLdouble*)eqn) ; return ;
}

//

static inline
ats_void_type atslib_glFlush () { glFlush () ; return ; }

/* ****** ****** */

// Depth Buffer

static inline
ats_void_type
atslib_glClearDepth (ats_GLclampd_type depth) {
  glClearDepth (depth) ; return ;
}

static inline
ats_void_type
atslib_glDepthFunc (ats_GLenum_type func) {
  glDepthFunc (func) ; return ;
}

static inline
ats_void_type
atslib_glDepthMask (ats_GLboolean_type flag) {
  glDepthMask (flag) ; return ;
}

static inline
ats_void_type
atslib_glDepthRange (
  ats_GLclampd_type near_val
, ats_GLclampd_type far_val
) {
  glDepthRange (near_val, far_val) ; return ;
}

/* ****** ****** */

// Accumulation Buffer

static inline
ats_void_type
atslib_glClearAccum (
  ats_GLfloat_type red
, ats_GLfloat_type green
, ats_GLfloat_type blue
, ats_GLfloat_type alpha
) {
  glClearAccum (red, green, blue, alpha) ; return ;
}

static inline
ats_void_type
atslib_glAccum (ats_GLenum_type opr, ats_GLfloat_type value) {
  glAccum (opr, value) ; return ;
}

/* ****** ****** */

// Transformation

static inline
ats_void_type
atslib_glMatrixMode (ats_GLenum_type mode) {
  glMatrixMode (mode) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glOrtho_double (
  ats_double_type left
, ats_double_type right
, ats_double_type bottom
, ats_double_type top
, ats_double_type near_val
, ats_double_type far_val
) {
  glOrtho (left, right, bottom, top, near_val, far_val) ;
  return ;
}

static inline
ats_void_type
atslib_glOrtho_GLdouble (
  ats_GLdouble_type left
, ats_GLdouble_type right
, ats_GLdouble_type bottom
, ats_GLdouble_type top
, ats_GLdouble_type near_val
, ats_GLdouble_type far_val
) {
  glOrtho (left, right, bottom, top, near_val, far_val) ;
  return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glFrustum_double (
  ats_double_type left
, ats_double_type right
, ats_double_type bottom
, ats_double_type top
, ats_double_type near_val
, ats_double_type far_val
) {
  glFrustum (left, right, bottom, top, near_val, far_val) ;
  return ;
}

static inline
ats_void_type
atslib_glFrustum_GLdouble (
  ats_GLdouble_type left
, ats_GLdouble_type right
, ats_GLdouble_type bottom
, ats_GLdouble_type top
, ats_GLdouble_type near_val
, ats_GLdouble_type far_val
) {
  glFrustum (left, right, bottom, top, near_val, far_val) ;
  return ;
}

/* ****** ****** */

static inline
ats_void_type atslib_glLoadIdentity () { glLoadIdentity () ; return ; }

/* ****** ****** */

static inline
ats_void_type atslib_glLoadMatrixd (ats_ptr_type mat) {
  glLoadMatrixd ((GLdouble*)mat) ; return ;
}

static inline
ats_void_type atslib_glLoadMatrixf (ats_ptr_type mat) {
  glLoadMatrixf ((GLfloat*)mat) ; return ;
}

/* ****** ****** */

static inline
ats_void_type atslib_glMultMatrixd (ats_ptr_type mat) {
  glMultMatrixd ((GLdouble*)mat) ; return ;
}

static inline
ats_void_type atslib_glMultMatrixf (ats_ptr_type mat) {
  glMultMatrixf ((GLfloat*)mat) ; return ;
}

/* ****** ****** */

static inline
ats_void_type glFrustum_double (
  ats_double_type left
, ats_double_type right
, ats_double_type bottom
, ats_double_type top
, ats_double_type near_val
, ats_double_type far_val
) {
  glFrustum (left, right, bottom, top, near_val, far_val) ; return ;
}

static inline
ats_void_type glFrustum_GLdouble (
  ats_GLdouble_type left
, ats_GLdouble_type right
, ats_GLdouble_type bottom
, ats_GLdouble_type top
, ats_GLdouble_type near_val
, ats_GLdouble_type far_val
) {
  glFrustum (left, right, bottom, top, near_val, far_val) ; return ;
}

/* ****** ****** */

static inline
ats_void_type atslib_glViewport_type (
  ats_int_type x
, ats_int_type y
, ats_int_type width
, ats_int_type height
) {
  glViewport (x, y, width, height) ; return ;
}

static inline
ats_void_type atslib_glViewport_GLtype (
  ats_GLint_type x
, ats_GLint_type y
, ats_GLsizei_type width
, ats_GLsizei_type height
) {
  glViewport (x, y, width, height) ; return ;
}

/* ****** ****** */

static inline
ats_void_type atslib_glPopMatrix () { glPopMatrix () ; return ; }

static inline
ats_void_type atslib_glPushMatrix () { glPushMatrix () ; return ; }

/* ****** ****** */

static inline
ats_void_type
atslib_glRotatef_double (
  ats_double_type angle
, ats_double_type x
, ats_double_type y
, ats_double_type z
) {
  glRotatef (angle, x, y, z) ; return ;
}

static inline
ats_void_type
atslib_glRotatef_GLfloat (
  ats_GLfloat_type angle
, ats_GLfloat_type x
, ats_GLfloat_type y
, ats_GLfloat_type z
) {
  glRotatef (angle, x, y, z) ; return ;
}

//

static inline
ats_void_type
atslib_glRotated_double (
  ats_double_type angle
, ats_double_type x
, ats_double_type y
, ats_double_type z
) {
  glRotated (angle, x, y, z) ; return ;
}

static inline
ats_void_type
atslib_glRotated_GLdouble (
  ats_GLdouble_type angle
, ats_GLdouble_type x
, ats_GLdouble_type y
, ats_GLdouble_type z
) {
  glRotated (angle, x, y, z) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glScalef_double (
  ats_double_type x
, ats_double_type y
, ats_double_type z
) {
  glScalef (x, y, z) ; return ;
}

static inline
ats_void_type
atslib_glScalef_GLfloat (
  ats_GLfloat_type x
, ats_GLfloat_type y
, ats_GLfloat_type z
) {
  glScalef (x, y, z) ; return ;
}

//

static inline
ats_void_type
atslib_glScaled_double (
  ats_double_type x
, ats_double_type y
, ats_double_type z
) {
  glScaled (x, y, z) ; return ;
}

static inline
ats_void_type
atslib_glScaled_GLdouble (
  ats_GLdouble_type x
, ats_GLdouble_type y
, ats_GLdouble_type z
) {
  glScaled (x, y, z) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glTranslatef_double (
  ats_double_type x
, ats_double_type y
, ats_double_type z
) {
  glTranslatef (x, y, z) ; return ;
}

static inline
ats_void_type
atslib_glTranslatef_GLfloat (
  ats_GLfloat_type x
, ats_GLfloat_type y
, ats_GLfloat_type z
) {
  glTranslatef (x, y, z) ; return ;
}

//

static inline
ats_void_type
atslib_glTranslated_double (
  ats_double_type x
, ats_double_type y
, ats_double_type z
) {
  glTranslated (x, y, z) ; return ;
}

static inline
ats_void_type
atslib_glTranslated_GLdouble (
  ats_GLdouble_type x
, ats_GLdouble_type y
, ats_GLdouble_type z
) {
  glTranslated (x, y, z) ; return ;
}

/* ****** ****** */

static inline
ats_uint_type
atslib_glGenList_exn () {
  uint lst = glGenLists (1) ;
  if (lst == 0) {
    fprintf (stderr, "Exit: [glGenLists] failed.\n") ;
    exit (1) ;
  }
  return lst ;
}

static inline
ats_void_type
atslib_glNewList (ats_uint_type lst, ats_GLenum_type mode) {
  glNewList (lst, mode) ; return ;
}

static inline
ats_void_type atslib_glEndList () { glEndList () ; return ; }

/* ****** ****** */

// Drawing functions

static inline
ats_void_type
atslib_glBegin (ats_GLenum_type mode) {
  glBegin(mode) ; return ;
}

static inline
ats_void_type
atslib_glEnd () { glEnd() ; return ; }

/* ****** ****** */

static inline
ats_void_type
atslib_glVertex2d_double
  (ats_double_type d1, ats_double_type d2) {
  glVertex2d (d1, d2) ; return ;
}

static inline
ats_void_type
atslib_glVertex2d_GLdouble
  (ats_GLdouble_type d1, ats_GLdouble_type d2) {
  glVertex2d (d1, d2) ; return ;
}

//

static inline
ats_void_type
atslib_glVertex2f_double
  (ats_double_type f1, ats_double_type f2) {
  glVertex2f (f1, f2) ; return ;
}

static inline
ats_void_type
atslib_glVertex2f_GLfloat
  (ats_GLfloat_type f1, ats_GLfloat_type f2) {
  glVertex2f (f1, f2) ; return ;
}

//

static inline
ats_void_type
atslib_glVertex2i
  (ats_GLint_type i1, ats_GLint_type i2) {
  glVertex2i (i1, i2) ; return ;
}

static inline
ats_void_type
atslib_glVertex2s
  (ats_GLshort_type s1, ats_GLshort_type s2) {
  glVertex2s (s1, s2) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glVertex3d
  (ats_GLdouble_type d1, ats_GLdouble_type d2, ats_GLdouble_type d3) {
  glVertex3d (d1, d2, d3) ; return ;
}

static inline
ats_void_type
atslib_glVertex3f_double
  (ats_double_type f1, ats_double_type f2, ats_double_type f3) {
  glVertex3f (f1, f2, f3) ; return ;
}

static inline
ats_void_type
atslib_glVertex3f_GLfloat
  (ats_GLfloat_type f1, ats_GLfloat_type f2, ats_GLfloat_type f3) {
  glVertex3f (f1, f2, f3) ; return ;
}

static inline
ats_void_type
atslib_glVertex3i
  (ats_GLint_type i1, ats_GLint_type i2, ats_GLint_type i3) {
  glVertex3i (i1, i2, i3) ; return ;
}

static inline
ats_void_type
atslib_glVertex3s
  (ats_GLshort_type s1, ats_GLshort_type s2, ats_GLshort_type s3) {
  glVertex3s (s1, s2, s3) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glVertex4d (
  ats_GLdouble_type d1
, ats_GLdouble_type d2
, ats_GLdouble_type d3
, ats_GLdouble_type d4
) {
  glVertex4d (d1, d2, d3, d4) ; return ;
}

static inline
ats_void_type
atslib_glVertex4f (
  ats_GLfloat_type f1
, ats_GLfloat_type f2
, ats_GLfloat_type f3
, ats_GLfloat_type f4
) {
  glVertex4f (f1, f2, f3, f4) ; return ;
}

static inline
ats_void_type
atslib_glVertex4i (
  ats_GLint_type i1
, ats_GLint_type i2
, ats_GLint_type i3
, ats_GLint_type i4
) {
  glVertex4i (i1, i2, i3, i4) ; return ;
}

static inline
ats_void_type
atslib_glVertex4s (
  ats_GLshort_type s1
, ats_GLshort_type s2
, ats_GLshort_type s3
, ats_GLshort_type s4
) {
  glVertex4s (s1, s2, s3, s4) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glVertex2dv (ats_ptr_type v) {
  glVertex2dv ((GLdouble*)v) ; return ;
}

static inline
ats_void_type
atslib_glVertex2fv (ats_ptr_type v) {
  glVertex2fv ((GLfloat*)v) ; return ;
}

static inline
ats_void_type
atslib_glVertex2iv (ats_ptr_type v) {
  glVertex2iv ((GLint*)v) ; return ;
}

static inline
ats_void_type
atslib_glVertex2sv (ats_ptr_type v) {
  glVertex2sv ((GLshort*)v) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glVertex3dv (ats_ptr_type v) {
  glVertex3dv ((GLdouble*)v) ; return ;
}

static inline
ats_void_type
atslib_glVertex3fv (ats_ptr_type v) {
  glVertex3fv ((GLfloat*)v) ; return ;
}

static inline
ats_void_type
atslib_glVertex3iv (ats_ptr_type v) {
  glVertex3iv ((GLint*)v) ; return ;
}

static inline
ats_void_type
atslib_glVertex3sv (ats_ptr_type v) {
  glVertex3sv ((GLshort*)v) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glVertex4dv (ats_ptr_type v) {
  glVertex4dv ((GLdouble*)v) ; return ;
}

static inline
ats_void_type
atslib_glVertex4fv (ats_ptr_type v) {
  glVertex4fv ((GLfloat*)v) ; return ;
}

static inline
ats_void_type
atslib_glVertex4iv (ats_ptr_type v) {
  glVertex4iv ((GLint*)v) ; return ;
}

static inline
ats_void_type
atslib_glVertex4sv (ats_ptr_type v) {
  glVertex4sv ((GLshort*)v) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glNormal3bv (ats_ptr_type v) {
  glNormal3bv ((GLbyte*)v) ; return ;
}

static inline
ats_void_type
atslib_glNormal3dv (ats_ptr_type v) {
  glNormal3dv ((GLdouble*)v) ; return ;
}

static inline
ats_void_type
atslib_glNormal3fv (ats_ptr_type v) {
  glNormal3fv ((GLfloat*)v) ; return ;
}

static inline
ats_void_type
atslib_glNormal3iv (ats_ptr_type v) {
  glNormal3iv ((GLint*)v) ; return ;
}

static inline
ats_void_type
atslib_glNormal3sv (ats_ptr_type v) {
  glNormal3sv ((GLshort*)v) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glColor3f_double (
  ats_double_type red
, ats_double_type green
, ats_double_type blue
) {
  glColor3f (red, green, blue) ; return ;
} /* end of [atslib_glColor3f_double] */

static inline
ats_void_type
atslib_glColor3f_GLfloat (
  ats_GLfloat_type red
, ats_GLfloat_type green
, ats_GLfloat_type blue
) {
  glColor3f (red, green, blue) ; return ;
} /* end of [atslib_glColor3f_GLfloat] */

/* ****** ****** */

static inline
ats_void_type
atslib_glColor4f_double (
  ats_double_type red
, ats_double_type green
, ats_double_type blue
, ats_double_type alpha
) {
  glColor4f (red, green, blue, alpha) ; return ;
} /* end of [atslib_glColor4f_double] */

static inline
ats_void_type
atslib_glColor4f_GLfloat (
  ats_GLfloat_type red
, ats_GLfloat_type green
, ats_GLfloat_type blue
, ats_GLfloat_type alpha
) {
  glColor4f (red, green, blue, alpha) ; return ;
} /* end of [atslib_glColor4f_GLfloat] */

/* ****** ****** */

static inline
ats_void_type
atslib_glRasterPos2f_double (
  ats_double_type x, ats_double_type y
) {
  glRasterPos2f (x, y) ; return ;
}

static inline
ats_void_type
atslib_glRasterPos2f_GLfloat (
  ats_GLfloat_type x, ats_GLfloat_type y
) {
  glRasterPos2f (x, y) ; return ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_glRectf_double (
  ats_double_type x1
, ats_double_type y1
, ats_double_type x2
, ats_double_type y2
) {
  glRectf (x1, y1, x2, y2) ; return ;
} /* end of [atslib_glRectf_double] */

static inline
ats_void_type
atslib_glRectf_GLfloat (
  ats_GLfloat_type x1
, ats_GLfloat_type y1
, ats_GLfloat_type x2
, ats_GLfloat_type y2
) {
  glRectf (x1, y1, x2, y2) ; return ;
} /* end of [atslib_glRectf_GLfloat] */

/* ****** ****** */

// Lighting

static inline
ats_void_type
atslib_glShadeModel (ats_GLenum_type mode) {
  glShadeModel (mode) ; return ;
} /* end of [atslib_glShadeModel] */

static inline
ats_void_type
atslib_glLightfv (
  ats_GLenum_type light
, ats_GLenum_type pname
, ats_ptr_type params) {
  glLightfv (light, pname, (GLfloat*)params) ; return ;
} /* end of [atslib_glLightfv] */

static inline
ats_void_type
atslib_glLightiv (
  ats_GLenum_type light
, ats_GLenum_type pname
, ats_ptr_type params) {
  glLightiv (light, pname, (GLint*)params) ; return ;
} /* end of [atslib_glLightiv] */

/* ****** ****** */

static inline
ats_void_type
atslib_glLightModelfv (
  ats_GLenum_type pname, ats_ptr_type params
) {
  glLightModelfv (pname, (GLfloat*)params) ; return ;
} /* end of [atslib_glLightModelfv] */

static inline
ats_void_type
atslib_glLightModeliv (
  ats_GLenum_type pname, ats_ptr_type params
) {
  glLightModeliv (pname, (GLint*)params) ; return ;
} /* end of [atslib_glLightModeliv] */

/* ****** ****** */

static inline
ats_void_type
atslib_glMaterialfv (
  ats_GLenum_type face
, ats_GLenum_type pname
, ats_ptr_type params
) {
  glMaterialfv (face, pname, (GLfloat*)params) ; return ;
} /* end of [atslib_glMaterialfv] */

static inline
ats_void_type
atslib_glMaterialiv (
  ats_GLenum_type face
, ats_GLenum_type pname
, ats_ptr_type params
) {
  glMaterialiv (face, pname, (GLint*)params) ; return ;
} /* end of [atslib_glMaterialiv] */

/* ****** ****** */

#endif /* ATS_LIBC_GL_GL_CATS */

/* end of [gl.cats] */
