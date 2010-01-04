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

#ifndef ATSCTRB_GL_GL_CATS
#define ATSCTRB_GL_GL_CATS

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

typedef GLbyte ats_GLbyte_type ;
typedef GLubyte ats_GLubyte_type ;
typedef GLuint ats_GLuint_type ;
typedef GLushort ats_GLushort_type ;

typedef GLsizei ats_GLsizei_type ;

typedef GLclampd ats_GLclampd_type ;
typedef GLclampf ats_GLclampf_type ;

/* ****** ****** */

static inline
ats_int_type
atsctrb_int_of_GLenum (GLenum x) { return x ; }

static inline
ats_bool_type
atsctrb_eq_GLenum_GLenum
  (GLenum x1, GLenum x2) {
  return (x1 == x2 ? ats_true_bool : ats_false_bool) ;
} // end of [atsctrb_eq_GLenum_GLenum]

//

static inline
ats_GLbyte_type
atsctrb_GLbyte_of_int (int x) { return x ; }

//

static inline
ats_GLubyte_type
atsctrb_GLubyte_of_int (int x) { return x ; }

static inline
ats_GLubyte_type
atsctrb_GLubyte_of_uint (unsigned int x) { return x ; }

//

static inline
ats_GLshort_type
atsctrb_GLshort_of_int (int x) { return x ; }

//

static inline
ats_GLushort_type
atsctrb_GLushort_of_int (int x) { return x ; }

static inline
ats_GLushort_type
atsctrb_GLushort_of_uint (unsigned int x) { return x ; }

//

static inline
ats_GLsizei_type
atsctrb_GLsizei_of_int (int x) { return x ; }

static inline
ats_GLfloat_type
atsctrb_GLfloat_of_double (double x) { return x ; }

static inline
ats_GLclampf_type
atsctrb_GLclampf_of_double (double x) { return x ; }

//

static inline
ats_GLbitfield_type
atsctrb_lor_GLbitfield_GLbitfield
  (GLbitfield b1, GLbitfield b2) {
  return (b1 | b2) ;
} // end of [atsctrb_lor_GLbitfield_GLbitfield]

/* ****** ****** */

//
// Miscellaneous functions
//

/* ****** ****** */

static inline
ats_void_type
atsctrb_glClearColor_double (
  ats_double_type red
, ats_double_type green
, ats_double_type blue
, ats_double_type alpha
) {
  glClearColor (red, green, blue, alpha) ; return ;
} // end of [atsctrb_glClearColor_double]

#define atsctrb_glClearColor_GLclampf glClearColor

/* ****** ****** */

#define atsctrb_glClear glClear
#define atsctrb_glColorMask glColorMask

/* ****** ****** */

#define atsctrb_glAlphaFunc glAlphaFunc
#define atsctrb_glBlendFunc glBlendFunc
#define atsctrb_glLogicOp glLogicOp

/* ****** ****** */

#define atsctrb_glCullFace glCullFace
#define atsctrb_glFrontFace glFrontFace

/* ****** ****** */

#define atsctrb_glPointSize_double glPointSize
#define atsctrb_glPointSize_GLfloat glPointSize

/* ****** ****** */

static inline
ats_void_type
atsctrb_glLineWidth_double
  (ats_double_type width) {
  glLineWidth (width) ; return ;
} // end of [atsctrb_glLineWidth_double]

#define atsctrb_glLineWidth_GLfloat glLineWidth

/* ****** ****** */

#define atsctrb_glLineStipple glLineStipple

/* ****** ****** */

#define atsctrb_glPolygonMode glPolygonMode
#define atsctrb_glPolygonOffset glPolygonOffset

static inline
ats_void_type
atsctrb_glPolygonStipple
  (ats_ref_type mask) {
  glPolygonStipple ((GLubyte*)mask) ; return ;
} // end of [atsctrb_glPolygonStipple]

static inline
ats_void_type
atsctrb_glGetPolygonStipple
  (ats_ref_type mask) {
  glGetPolygonStipple ((GLubyte*)mask) ; return ;
} // end of [atsctrb_glGetPolygonStipple]

/* ****** ****** */

static inline
ats_void_type
atsctrb_glClipPlane (
  ats_GLenum_type plane, ats_ptr_type eqn
) {
  glClipPlane(plane, (GLdouble*)eqn) ; return ;
} // end of [atsctrb_glClipPlane]

static inline
ats_void_type
atsctrb_glGetClipPlane (
  ats_GLenum_type plane, ats_ptr_type eqn
) {
  glGetClipPlane(plane, (GLdouble*)eqn) ; return ;
} // end of [atsctrb_glGetClipPlane]

#define atsctrb_glEdgeFlag glEdgeFlag

static inline
ats_void_type
atsctrb_glEdgeFlagv
  (ats_ref_type flag) {
  glEdgeFlagv((GLboolean*)flag) ; return ;
} // end of [atsctrb_glEdgeFlagv]

/* ****** ****** */

#define atsctrb_glEnable glEnable
#define atsctrb_glDisable glDisable
#define atsctrb_glIsEnabled glIsEnabled

//

static inline
ats_void_type
atsctrb_glGetBooleanv (
  ats_GLenum_type pname, ats_ptr_type params
) {
  glGetBooleanv(pname, (GLboolean*)params) ; return ;
} // end of [atsctrb_glGetBooleanv]

static inline
ats_void_type
atsctrb_glGetDoublev (
  ats_GLenum_type pname, ats_ptr_type params
) {
  glGetDoublev(pname, (GLdouble*)params) ; return ;
} // end of [atsctrb_glGetDoublev]

static inline
ats_void_type
atsctrb_glGetFloatv (
  ats_GLenum_type pname, ats_ptr_type params
) {
  glGetFloatv(pname, (GLfloat*)params) ; return ;
} // end of [atsctrb_glGetFloatv]

static inline
ats_void_type
atsctrb_glGetIntegerv (
  ats_GLenum_type pname, ats_ptr_type params
) {
  glGetIntegerv(pname, (GLint*)params) ; return ;
} // end of [atsctrb_glGetIntegerv]

/* ****** ****** */

#define atsctrb_glRenderMode glRenderMode
#define atsctrb_glGetError glGetError
#define atsctrb_glGetString glGetString
#define atsctrb_glFinish glFinish
#define atsctrb_glFlush glFlush
#define atsctrb_glHint glHint

/* ****** ****** */

// Depth Buffer

#define atsctrb_glClearDepth glClearDepth
#define atsctrb_glDepthFunc glDepthFunc
#define atsctrb_glDepthMask glDepthMask
#define atsctrb_glDepthRange glDepthRange

/* ****** ****** */

// Accumulation Buffer

static inline
ats_void_type
atsctrb_glClearAccum (
  ats_GLfloat_type red
, ats_GLfloat_type green
, ats_GLfloat_type blue
, ats_GLfloat_type alpha
) {
  glClearAccum (red, green, blue, alpha) ; return ;
} // end of [atsctrb_glClearAccum]

static inline
ats_void_type
atsctrb_glAccum (
  ats_GLenum_type opr
, ats_GLfloat_type value
) {
  glAccum (opr, value) ; return ;
} // end of [atsctrb_glAccum]

/* ****** ****** */

//
// Transformation
//

/* ****** ****** */

#define atsctrb_glMatrixMode glMatrixMode

/* ****** ****** */

#define atsctrb_glOrtho_double glOrtho
#define atsctrb_glOrtho_GLdouble glOrtho

/* ****** ****** */

#define atsctrb_glFrustum_double glFrustum
#define atsctrb_glFrustum_GLdouble glFrustum

/* ****** ****** */

#define atsctrb_glLoadIdentity glLoadIdentity

/* ****** ****** */

static inline
ats_void_type
atsctrb_glLoadMatrixd
  (ats_ptr_type mat) {
  glLoadMatrixd ((GLdouble*)mat) ; return ;
} // end of [atsctrb_glLoadMatrixd]

static inline
ats_void_type
atsctrb_glLoadMatrixf
  (ats_ptr_type mat) {
  glLoadMatrixf ((GLfloat*)mat) ; return ;
} // end of [atsctrb_glLoadMatrixf]

/* ****** ****** */

static inline
ats_void_type
atsctrb_glMultMatrixd
  (ats_ptr_type mat) {
  glMultMatrixd ((GLdouble*)mat) ; return ;
} // end of [atsctrb_glMultMatrixd]

static inline
ats_void_type
atsctrb_glMultMatrixf
  (ats_ptr_type mat) {
  glMultMatrixf ((GLfloat*)mat) ; return ;
} // end of [atsctrb_glMultMatrixf]

/* ****** ****** */

static inline
ats_void_type atsctrb_glViewport_type (
  ats_int_type x
, ats_int_type y
, ats_int_type width
, ats_int_type height
) {
  glViewport (x, y, (GLsizei)width, (GLsizei)height) ; return ;
} // end of [atsctrb_glViewport_type]

#define atsctrb_glViewport_GLtype glViewport

/* ****** ****** */

#define atsctrb_glPopMatrix glPopMatrix
#define atsctrb_glPushMatrix glPushMatrix

/* ****** ****** */

#define atsctrb_glRotated_double glRotated
#define atsctrb_glRotated_GLdouble glRotated
#define atsctrb_glRotatef glRotatef

#define atsctrb_glScaled_double glScaled
#define atsctrb_glScaled_GLdouble glScaled
#define atsctrb_glScalef glScalef

#define atsctrb_glTranslated_double glTranslated
#define atsctrb_glTranslated_GLdouble glTranslated
#define atsctrb_glTranslatef glTranslatef

/* ****** ****** */

static inline
ats_uint_type
atsctrb_glGenList_exn () {
  uint lst = glGenLists (1) ;
  if (lst == 0) {
    fprintf (stderr, "exit(ATS/GL): [glGenLists] failed.\n") ;
    exit (1) ;
  }
  return lst ;
} // end of [atsctrb_glGenList_exn]

static inline
ats_void_type
atsctrb_glNewList (
  ats_uint_type lst
, ats_GLenum_type mode
) {
  glNewList (lst, mode) ; return ;
} // end of [atsctrb_glNewList]

static inline
ats_void_type atsctrb_glEndList () { glEndList () ; return ; }

/* ****** ****** */

static inline
ats_void_type
atsctrb_glBegin (
  ats_GLenum_type mode
) {
  glBegin(mode) ; return ;
} // end of [atsctrb_glBegin]

static inline
ats_void_type
atsctrb_glEnd () { glEnd() ; return ; }

/* ****** ****** */

//
// Drawing functions
//

#define atsctrb_glVertex2d_double glVertex2d
#define atsctrb_glVertex2d_GLdouble glVertex2d
#define atsctrb_glVertex2f glVertex2f
#define atsctrb_glVertex2i glVertex2i
#define atsctrb_glVertex2s glVertex2s

#define atsctrb_glVertex3d_double glVertex3d
#define atsctrb_glVertex3d_GLdouble glVertex3d
#define atsctrb_glVertex3f glVertex3f
#define atsctrb_glVertex3i glVertex3i
#define atsctrb_glVertex3s glVertex3s

#define atsctrb_glVertex4d_double glVertex4d
#define atsctrb_glVertex4d_GLdouble glVertex4d
#define atsctrb_glVertex4f glVertex4f
#define atsctrb_glVertex4i glVertex4i
#define atsctrb_glVertex4s glVertex4s

/* ****** ****** */

static inline
ats_void_type
atsctrb_glVertex2dv
  (ats_ref_type v) {
  glVertex2dv ((GLdouble*)v) ; return ;
} // end of [atsctrb_glVertex2dv]

static inline
ats_void_type
atsctrb_glVertex2fv
  (ats_ref_type v) {
  glVertex2fv ((GLfloat*)v) ; return ;
} // end of [atsctrb_glVertex2fv]

static inline
ats_void_type
atsctrb_glVertex2iv
  (ats_ref_type v) {
  glVertex2iv ((GLint*)v) ; return ;
} // end of [atsctrb_glVertex2iv]

static inline
ats_void_type
atsctrb_glVertex2sv
  (ats_ref_type v) {
  glVertex2sv ((GLshort*)v) ; return ;
} // end of [atsctrb_glVertex2sv]

/* ****** ****** */

static inline
ats_void_type
atsctrb_glVertex3dv
  (ats_ref_type v) {
  glVertex3dv ((GLdouble*)v) ; return ;
} // end of [atsctrb_glVertex3dv]

static inline
ats_void_type
atsctrb_glVertex3fv
  (ats_ref_type v) {
  glVertex3fv ((GLfloat*)v) ; return ;
} // end of [atsctrb_glVertex3fv]

static inline
ats_void_type
atsctrb_glVertex3iv
  (ats_ref_type v) {
  glVertex3iv ((GLint*)v) ; return ;
} // end of [atsctrb_glVertex3iv]

static inline
ats_void_type
atsctrb_glVertex3sv
  (ats_ref_type v) {
  glVertex3sv ((GLshort*)v) ; return ;
} // end of [atsctrb_glVertex3sv]

/* ****** ****** */

static inline
ats_void_type
atsctrb_glVertex4dv
  (ats_ref_type v) {
  glVertex4dv ((GLdouble*)v) ; return ;
} // end of [atsctrb_glVertex4dv]

static inline
ats_void_type
atsctrb_glVertex4fv
  (ats_ref_type v) {
  glVertex4fv ((GLfloat*)v) ; return ;
} // end of [atsctrb_glVertex4fv]

static inline
ats_void_type
atsctrb_glVertex4iv
  (ats_ref_type v) {
  glVertex4iv ((GLint*)v) ; return ;
} // end of [atsctrb_glVertex4iv]

static inline
ats_void_type
atsctrb_glVertex4sv
  (ats_ref_type v) {
  glVertex4sv ((GLshort*)v) ; return ;
} // end of [atsctrb_glVertex4sv]

/* ****** ****** */

static inline
ats_void_type
atsctrb_glNormal3bv
  (ats_ref_type v) {
  glNormal3bv ((GLbyte*)v) ; return ;
} // end of [atsctrb_glNormal3bv]

static inline
ats_void_type
atsctrb_glNormal3dv
  (ats_ref_type v) {
  glNormal3dv ((GLdouble*)v) ; return ;
} // end of [atsctrb_glNormal3dv]

static inline
ats_void_type
atsctrb_glNormal3fv
  (ats_ref_type v) {
  glNormal3fv ((GLfloat*)v) ; return ;
} // end of [atsctrb_glNormal3fv]

static inline
ats_void_type
atsctrb_glNormal3iv
  (ats_ref_type v) {
  glNormal3iv ((GLint*)v) ; return ;
} // end of [atsctrb_glNormal3iv]

static inline
ats_void_type
atsctrb_glNormal3sv
  (ats_ref_type v) {
  glNormal3sv ((GLshort*)v) ; return ;
} // end of [atsctrb_glNormal3sv]

/* ****** ****** */

#define atsctrb_glColor3b glColor3b
#define atsctrb_glColor3d_double glColor3d
#define atsctrb_glColor3d_GLdouble glColor3d
#define atsctrb_glColor3f glColor3f
#define atsctrb_glColor3i glColor3i
#define atsctrb_glColor3s glColor3s
#define atsctrb_glColor3ub glColor3ub
#define atsctrb_glColor3ui glColor3ui
#define atsctrb_glColor3us glColor3us

/* ****** ****** */

static inline
ats_void_type
atsctrb_glColor3dv (
  ats_ref_type rgb
) {
  glColor3dv ((GLdouble*)rgb) ; return ;
} /* end of [atsctrb_glColor3dv] */

static inline
ats_void_type
atsctrb_glColor3fv (
  ats_ref_type rgb
) {
  glColor3fv ((GLfloat*)rgb) ; return ;
} /* end of [atsctrb_glColor3fv] */

static inline
ats_void_type
atsctrb_glColor3iv (
  ats_ref_type rgb
) {
  glColor3iv ((GLint*)rgb) ; return ;
} /* end of [atsctrb_glColor3iv] */

static inline
ats_void_type
atsctrb_glColor3sv (
  ats_ref_type rgb
) {
  glColor3sv ((GLshort*)rgb) ; return ;
} /* end of [atsctrb_glColor3sv] */

/* ****** ****** */

#define atsctrb_glColor4b glColor4b
#define atsctrb_glColor4d_double glColor4d
#define atsctrb_glColor4d_GLdouble glColor4d
#define atsctrb_glColor4f glColor4f
#define atsctrb_glColor4i glColor4i
#define atsctrb_glColor4s glColor4s
#define atsctrb_glColor4ub glColor4ub
#define atsctrb_glColor4ui glColor4ui
#define atsctrb_glColor4us glColor4us

/* ****** ****** */

static inline
ats_void_type
atsctrb_glColor4dv (
  ats_ref_type rgb
) {
  glColor4dv ((GLdouble*)rgb) ; return ;
} /* end of [atsctrb_glColor4dv] */

static inline
ats_void_type
atsctrb_glColor4fv (
  ats_ref_type rgb
) {
  glColor4fv ((GLfloat*)rgb) ; return ;
} /* end of [atsctrb_glColor4fv] */

static inline
ats_void_type
atsctrb_glColor4iv (
  ats_ref_type rgb
) {
  glColor4iv ((GLint*)rgb) ; return ;
} /* end of [atsctrb_glColor4iv] */

static inline
ats_void_type
atsctrb_glColor4sv (
  ats_ref_type rgb
) {
  glColor4sv ((GLshort*)rgb) ; return ;
} /* end of [atsctrb_glColor4sv] */

/* ****** ****** */

#define atsctrb_glTexCoord1d_double glTexCoord1d
#define atsctrb_glTexCoord1d_GLdouble glTexCoord1d
#define atsctrb_glTexCoord1f glTexCoord1f
#define atsctrb_glTexCoord1i glTexCoord1i
#define atsctrb_glTexCoord1s glTexCoord1s

#define atsctrb_glTexCoord2d_double glTexCoord2d
#define atsctrb_glTexCoord2d_GLdouble glTexCoord2d
#define atsctrb_glTexCoord2f glTexCoord2f
#define atsctrb_glTexCoord2i glTexCoord2i
#define atsctrb_glTexCoord2s glTexCoord2s

#define atsctrb_glTexCoord3d_double glTexCoord3d
#define atsctrb_glTexCoord3d_GLdouble glTexCoord3d
#define atsctrb_glTexCoord3f glTexCoord3f
#define atsctrb_glTexCoord3i glTexCoord3i
#define atsctrb_glTexCoord3s glTexCoord3s

/* ****** ****** */

#define atsctrb_glRasterPos2d_double glRasterPos2d
#define atsctrb_glRasterPos2d_GLdouble glRasterPos2d
#define atsctrb_glRasterPos2f glRasterPos2f

/* ****** ****** */

#define atsctrb_glRectd_double glRectd
#define atsctrb_glRectd_GLdouble glRectd
#define atsctrb_glRectf glRectf

/* ****** ****** */

//
// Lighting
//

/* ****** ****** */

#define atsctrb_glShadeModel glShadeModel

#define atsctrb_glLightf glLightf
#define atsctrb_glLighti glLighti

static inline
ats_void_type
atsctrb_glLightfv (
  ats_GLenum_type light
, ats_GLenum_type pname
, ats_ptr_type params) {
  glLightfv (light, pname, (GLfloat*)params) ; return ;
} /* end of [atsctrb_glLightfv] */

static inline
ats_void_type
atsctrb_glLightiv (
  ats_GLenum_type light
, ats_GLenum_type pname
, ats_ptr_type params) {
  glLightiv (light, pname, (GLint*)params) ; return ;
} /* end of [atsctrb_glLightiv] */

/* ****** ****** */

#define atsctrb_glLightModelf glLightModelf
#define atsctrb_glLightModeli glLightModeli

static inline
ats_void_type
atsctrb_glLightModelfv (
  ats_GLenum_type pname, ats_ptr_type params
) {
  glLightModelfv (pname, (GLfloat*)params) ; return ;
} /* end of [atsctrb_glLightModelfv] */

static inline
ats_void_type
atsctrb_glLightModeliv (
  ats_GLenum_type pname, ats_ptr_type params
) {
  glLightModeliv (pname, (GLint*)params) ; return ;
} /* end of [atsctrb_glLightModeliv] */

/* ****** ****** */

#define atsctrb_glMaterialf glMaterialf
#define atsctrb_glMateriali glMateriali

static inline
ats_void_type
atsctrb_glMaterialfv (
  ats_GLenum_type face
, ats_GLenum_type pname
, ats_ptr_type params
) {
  glMaterialfv (face, pname, (GLfloat*)params) ; return ;
} /* end of [atsctrb_glMaterialfv] */

static inline
ats_void_type
atsctrb_glMaterialiv (
  ats_GLenum_type face
, ats_GLenum_type pname
, ats_ptr_type params
) {
  glMaterialiv (face, pname, (GLint*)params) ; return ;
} /* end of [atsctrb_glMaterialiv] */

/* ****** ****** */

//
// Raster functions
//

#define atsctrb_glPixelStoref glPixelStoref
#define atsctrb_glPixelStorei glPixelStorei

/* ****** ****** */

//
// Texture mapping
//

#define atsctrb_glTexParameterf glTexParameterf
#define atsctrb_glTexParameteri glTexParameteri

#define atsctrb_glTexEnvf glTexEnvf
#define atsctrb_glTexEnvi glTexEnvi

/* ****** ****** */

static inline
ats_void_type
atsctrb_glDeleteTexures (
  ats_GLsizei_type n, ats_ref_type texnames
) {
  glDeleteTexures (n, (GLuint*)texnames) ; return ;
} // end of [atsctrb_glDeleteTexures]

/* ****** ****** */

static inline
ats_void_type
atsctrb_glTexImage1D (
  ats_GLenum_type target
, ats_GLint_type level
, ats_GLint_type internalFormat
, ats_GLsizei_type width
, ats_int_type border // 0 or 1
, ats_GLenum_type format
, ats_GLenum_type type
, ats_ref_type texels
) {
  glTexImage1D (
    target, level, internalFormat
  , width, border, format, type, (GLvoid*)texels
  ) ; return ;
} // end of [atsctrb_glTexImage1D]

static inline
ats_void_type
atsctrb_glTexImage2D (
  ats_GLenum_type target
, ats_GLint_type level
, ats_GLint_type internalFormat
, ats_GLsizei_type width
, ats_GLsizei_type height
, ats_int_type border // 0 or 1
, ats_GLenum_type format
, ats_GLenum_type type
, ats_ref_type texels
) {
  glTexImage2D (
    target, level, internalFormat
  , width, height, border, format, type, (GLvoid*)texels
  ) ; return ;
} // end of [atsctrb_glTexImage2D]

/* ****** ****** */

//
// OpenGL 1.1
//

static inline
ats_void_type
atsctrb_glGenTextures (
  ats_GLsizei_type n, ats_ref_type textures
) {
  glGenTextures(n, (GLuint*)textures) ; return ;
} // end of [atsctrb_glGenTextures]

#define atsctrb_glBindTexture glBindTexture

/* ****** ****** */

#endif /* ATSCTRB_GL_GL_CATS */

/* end of [gl.cats] */
