(*
**
** A simple implementation of the tetrix game
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Summer, 2008
**
*)

(* ****** ****** *)

%{^
extern ats_void_type mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

staload "libc/SATS/math.sats"
staload "libc/GL/SATS/gl.sats"
staload "libc/GL/SATS/glut.sats"

(* ****** ****** *)

local

typedef GLfloat = float

in

extern fun glLightfv {n:nat} {l:addr}
  (pf: !array_v (GLfloat, n, l) | light: GLenum, pname: GLenum, p: ptr l): void
  = "atslib_glLightfv"

extern fun glLightModelfv {n:nat} {l:addr}
  (pf: !array_v (GLfloat, n, l) | pname: GLenum, params: ptr l): void
  = "atslib_glLightModelfv"

extern fun glMaterialfv {n:nat} {l:addr}
  (pf: !array_v (GLfloat, n, l) | face: GLenum, pname: GLenum, params: ptr l): void
  = "atslib_glMaterialfv"

end

extern fun initialize (): void = "initialize"
implement initialize () = let
  var !p_mat_specular with pf1 = @[float](1.0, 1.0, 1.0, 1.0)
  var !p_mat_shininess with pf2 = @[float](50.0)
  var !p_light_position with pf3 = @[float](1.0, 1.0, 1.0, 0.0)
  var !p_white_light with pf4 = @[float](1.0, 1.0, 1.0, 1.0)
  var !p_lmodel_ambient with pf5 = @[float](0.1, 0.1, 0.1, 1.0)

  val () = glClearColor (0.0, 0.0, 0.0, 0.0) ;
  val () = glShadeModel (GL_SMOOTH)

  val () = glMaterialfv (pf1 | GL_FRONT, GL_SPECULAR, p_mat_specular)
  val () = glMaterialfv (pf2 | GL_FRONT, GL_SHININESS, p_mat_shininess)
  val () = glLightfv (pf3 | GL_LIGHT0, GL_POSITION, p_light_position)
  val () = glLightfv (pf4 | GL_LIGHT0, GL_DIFFUSE, p_white_light)
  val () = glLightfv (pf4 | GL_LIGHT0, GL_SPECULAR, p_white_light)
  val () = glLightModelfv (pf5 | GL_LIGHT_MODEL_AMBIENT, p_lmodel_ambient)

  val () = glEnable (GL_LIGHTING)
  val () = glEnable (GL_LIGHT0)
  val () = glEnable (GL_DEPTH_TEST)
in
  // empty
end // end of [initialize]

(* ****** ****** *)

extern fun display (): void = "display"
implement display () = let
  val () = glClear (GL_COLOR_BUFFER_BIT lor GL_DEPTH_BUFFER_BIT)
  val () = glutSolidSphere (1.0, 160, 128)
  val () = glFlush ()
in
  // empty
end // end of [display]

(* ****** ****** *)

extern fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = let
  val () = glViewport (0, 0, w, h)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = case+ 0 of
    | _ when (w <= h) => let
        val hw = (double_of h) / (double_of w)
      in
        glOrtho (~1.5, 1.5, ~1.5 * hw, 1.5 * hw, ~10.0, 10.0)
      end
    | _ (* w > h *) => let
        val wh = (double_of w) / (double_of h)
      in
        glOrtho (~1.5 * wh, 1.5 * wh, ~1.5, 1.5, ~10.0, 10.0)
      end
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
in
end // end of [reshape]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$

ats_void_type mainats
  (ats_int_type argc, ats_ptr_type argv) {
  glutInit (&argc, argv) ;
  glutInitDisplayMode (GLUT_SINGLE | GLUT_RGB | GLUT_DEPTH) ;
  glutInitWindowSize (500, 500) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow(((char**)argv)[0]) ;
  initialize () ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;
  glutMainLoop () ;
} /* end of [mainats] */

%}

(* ****** ****** *)

(* end of [glLitSphere.dats] *)
