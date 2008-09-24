%{^

extern ats_void_type mainats (ats_int_type argc, ats_ptr_type argv) ;

%}

staload "libc/SATS/math.sats"
staload "libc/GL/SATS/gl.sats"
staload "libc/GL/SATS/glut.sats"

(* ****** ****** *)

extern fun initialize (): void = "initialize"
implement initialize () = let
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glShadeModel (GL_FLAT)
in
  // empty
end // end of [initialize]

(* ****** ****** *)

local

typedef GLdouble = double

in

extern fun gluLookAt (
  eyeX: GLdouble, eyeY: GLdouble, eyeZ: GLdouble
, centerX: GLdouble, centerY: GLdouble, centerZ: GLdouble
, upX: GLdouble, upY: GLdouble, upZ: GLdouble
) : void
  = "gluLookAt"

end

extern fun display (): void = "display"
implement display () = let
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3f (1.0, 1.0, 1.0)
  val () = glLoadIdentity ()
  val () = gluLookAt (0.0, 0.0, 5.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0)
  val () = glScalef (1.0, 2.0, 1.0)
  val () = glutWireCube (1.0)
(*
  val () = glutSolidCube (1.0)
*)
  val () = glFlush ()
in
  // empty
end

extern fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = let
  val () = glViewport (
    GLint_of_int 0, GLint_of_int 0, GLsizei_of_int w, GLsizei_of_int h
  ) // end of [glViewport]
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = glFrustum (~1.0, 1.0, ~1.0, 1.0, 1.5, 20.0)
  val () = glMatrixMode (GL_MODELVIEW)
in
  // empty
end // end of [reshape]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$

ats_void_type mainats
  (ats_int_type argc, ats_ptr_type argv) {

  glutInit ((int*)&argc, (char**)argv) ;
  glutInitDisplayMode (GLUT_SINGLE | GLUT_RGB) ;
  glutInitWindowSize (500, 500) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow("Icosahedron") ;
  initialize () ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;
  glutMainLoop () ;
  return ; /* deadcode */
}

%}

(* ****** ****** *)

(* end of [glCubeView] *)