%{^

extern ats_void_type mainats (ats_int_type argc, ats_ptr_type argv) ;

%}

staload "libc/GL/SATS/gl.sats"
staload "libc/GL/SATS/glut.sats"

(* ****** ****** *)

%{^

static int day = 0 ;

static inline
ats_int_type day_get () { return day ; }

static inline
ats_void_type day_set (int x) { day = x ; return ; }

%}

extern fun day_get (): int = "day_get"
extern fun day_set (x: int): void = "day_set"

(* ****** ****** *)

extern fun initialize (): void = "initialize"
implement initialize () = let
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glShadeModel (GL_FLAT)
in
  // empty
end // end of [initialize]

(* ****** ****** *)

extern fun display (): void = "display"
implement display () = let
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3f (1.0, 1.0, 1.0)
  val (pf1_mat | ()) = glPushMatrix ()
  val () = glRotatef (270.0, 1.0, 0.0, 0.0)
  val () = glutWireSphere (1.0, 20, 16) // sun

  val day = day_get ()
  val mday = day mod 30 and yday = day

  val m_angle = (double_of mday / 30) * 360.0
  and y_angle = (double_of yday / 365) * 360.0

  val () = glRotatef (y_angle, 0.0, 0.0, 1.0)
  val () = glTranslatef (2.0, 0.0, 0.0)

  val (pf2_mat | ()) = glPushMatrix ()
  val () = glRotatef (15.0, 0.0, 1.0, 0.0)
  val () = glutWireSphere (0.25, 10, 8) // planet

  val () = glRotatef (m_angle, 0.0, 0.0, 1.0)
  val () = glTranslatef (0.5, 0.0, 0.0)  
  val () = glutWireSphere (0.10, 5, 4) // planet

  val () = glPopMatrix (pf2_mat | (*none*))

  val () = glPopMatrix (pf1_mat | (*none*))
  val () = glutSwapBuffers ()
in
  // empty
end // end of [display]

(* ****** ****** *)

local

typedef GLdouble = double

in

extern fun gluPerspective
  (_: GLdouble, _: GLdouble, _: GLdouble, _: GLdouble): void
  = "gluPerspective"

extern fun gluLookAt (
  eyeX: GLdouble, eyeY: GLdouble, eyeZ: GLdouble
, centerX: GLdouble, centerY: GLdouble, centerZ: GLdouble
, upX: GLdouble, upY: GLdouble, upZ: GLdouble
) : void
  = "gluLookAt"

end

extern fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = let
  val () = glViewport (
    GLint_of_int 0, GLint_of_int 0, GLsizei_of_int w, GLsizei_of_int h
  )
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = gluPerspective
    (60.0, (double_of w) / (double_of h), 1.0, 20.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
  val () = gluLookAt (0.0, 0.0, 5.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0)
in
  // empty
end // end of [reshape]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$

void keyboard (unsigned char key, int x, int y) {
  switch (key) {
    case 'd':
      day = (day + 5) % 365 ; glutPostRedisplay () ; break ;
    case 'D':
      day = (day - 5) % 365 ; glutPostRedisplay () ; break ;
    case '\033': exit (0) ;
    default: break ;
  }
  return ;
}

ats_void_type mainats
  (ats_int_type argc, ats_ptr_type argv) {

  glutInit ((int*)&argc, (char**)argv) ;
  glutInitDisplayMode (GLUT_DOUBLE | GLUT_RGB) ;
  glutInitWindowSize (500, 500) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow("Planet") ;
  initialize () ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;
  glutKeyboardFunc (keyboard) ;
  glutMainLoop () ;
  return ; /* deadcode */
}

%}

(* ****** ****** *)

(* end of [glPlanet.dats] *)
