(*
**
** A simple OpenGL example: defining and using a complete font
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: August, 2010
**
*)

(* ****** ****** *)

staload "contrib/GL/SATS/gl.sats"
staload "contrib/GL/SATS/glu.sats"
staload "contrib/GL/SATS/glut.sats"

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%} // end of [%{^]

(* ****** ****** *)

%{^
GLubyte theSpace[] = {
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
} ; // end of [theSpace]
GLubyte theLetters[][13] = {
  {0x00, 0x00, 0xc3, 0xc3, 0xc3, 0xc3, 0xff, 0xc3, 0xc3, 0xc3, 0x66, 0x3c, 0x18} // A
, {0x00, 0x00, 0xfe, 0xc7, 0xc3, 0xc3, 0xc7, 0xfe, 0xc7, 0xc3, 0xc3, 0xc7, 0xfe} // B
, {0x00, 0x00, 0x7e, 0xe7, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0, 0xe7, 0x7e} // C
, {0x00, 0x00, 0xfc, 0xce, 0xc7, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xc7, 0xce, 0xfc} // D
, {0x00, 0x00, 0xff, 0xc0, 0xc0, 0xc0, 0xc0, 0xfc, 0xc0, 0xc0, 0xc0, 0xc0, 0xff} // E
, {0x00, 0x00, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0, 0xfc, 0xc0, 0xc0, 0xc0, 0xff} // F
, {0x00, 0x00, 0x7e, 0xe7, 0xc3, 0xc3, 0xcf, 0xc0, 0xc0, 0xc0, 0xc0, 0xe7, 0x7e} // G
, {0x00, 0x00, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xff, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3} // H
, {0x00, 0x00, 0x7e, 0x18, 0x18, 0x18, 0x18, 0x18, 0x18, 0x18, 0x18, 0x18, 0x7e} // I
, {0x00, 0x00, 0x7c, 0xee, 0xc6, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06} // J
, {0x00, 0x00, 0xc3, 0xc6, 0xcc, 0xd8, 0xf0, 0xe0, 0xf0, 0xd8, 0xcc, 0xc6, 0xc3} // K
, {0x00, 0x00, 0xff, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0} // L
, {0x00, 0x00, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xdb, 0xff, 0xff, 0xe7, 0xc3} // M
, {0x00, 0x00, 0xc7, 0xc7, 0xcf, 0xcf, 0xdf, 0xdb, 0xfb, 0xf3, 0xf3, 0xe3, 0xe3} // N
, {0x00, 0x00, 0x7e, 0xe7, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xe7, 0x7e} // O
, {0x00, 0x00, 0xc0, 0xc0, 0xc0, 0xc0, 0xc0, 0xfe, 0xc7, 0xc3, 0xc3, 0xc7, 0xfe} // P
, {0x00, 0x00, 0x3f, 0x6e, 0xdf, 0xdb, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0x66, 0x3c} // Q
, {0x00, 0x00, 0xc3, 0xc6, 0xcc, 0xd8, 0xf0, 0xfe, 0xc7, 0xc3, 0xc3, 0xc7, 0xfe} // R
, {0x00, 0x00, 0x7e, 0xe7, 0x03, 0x03, 0x07, 0x7e, 0xe0, 0xc0, 0xc0, 0xe7, 0x7e} // S
, {0x00, 0x00, 0x18, 0x18, 0x18, 0x18, 0x18, 0x18, 0x18, 0x18, 0x18, 0x18, 0xff} // T
, {0x00, 0x00, 0x7e, 0xe7, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3} // U
, {0x00, 0x00, 0x18, 0x3c, 0x3c, 0x66, 0x66, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3} // V
, {0x00, 0x00, 0xc3, 0xe7, 0xff, 0xff, 0xdb, 0xdb, 0xc3, 0xc3, 0xc3, 0xc3, 0xc3} // W
, {0x00, 0x00, 0xc3, 0x66, 0x66, 0x3c, 0x3c, 0x18, 0x3c, 0x3c, 0x66, 0x66, 0xc3} // X
, {0x00, 0x00, 0x18, 0x18, 0x18, 0x18, 0x18, 0x18, 0x3c, 0x3c, 0x66, 0x66, 0xc3} // Y
, {0x00, 0x00, 0xff, 0xc0, 0xc0, 0x60, 0x30, 0x7e, 0x0c, 0x06, 0x03, 0x03, 0xff} // Z
} ; // end of [GLubyte]

ats_ptr_type getLetter (ats_int_type i) { return &theLetters[i] ; }

%} // end of [%{^]
extern val theSpace: ptr = "#theSpace"
extern fun getLetter {i:nat | i < 26} (i: int i): ptr = "#getLetter"

(* ****** ****** *)

val test1 = "THE QUICK BROWN FOX JUMPS" and test2 = "OVER A LAZY DOG"

(* ****** ****** *)

%{^
GLuint theFontOffset = 0 ;
GLuint theFontOffset_get () { return theFontOffset ; }
void theFontOffset_set (GLuint base) { theFontOffset = base ; return ; }
%} // end of [%{^]
extern fun theFontOffset_get (): GLuint = "theFontOffset_get"
extern fun theFontOffset_set (base: GLuint): void = "theFontOffset_set"

(* ****** ****** *)

fun printString
  {n:nat} (txt: string n) = let
  val len = string_length (txt)
  val (pf | ()) = glPushAttrib (GL_LIST_BIT)
  val () = glListBase (theFontOffset_get ())
  val () = glCallLists (len, GL_BYTE, txt) where {
    extern fun glCallLists {n:nat} (_: size_t n, _: GLenum_type GLbyte, _: string n): void
      = "#glCallLists"
  } // end of [val]
  val () = glPopAttrib (pf | (*none*))
in
  // nothing
end // end of [printString]

(* ****** ****** *)

fun makeRasterFont () = () where {
//
  val () = glPixelStorei (GL_UNPACK_ALIGNMENT, (GLint)1)
//
  val base = glGenLists ((GLsizei)128) where {
    extern fun glGenLists (range: GLsizei): GLuint = "atsctrb_glGenLists"
  } // end of [val]
  val () = theFontOffset_set (base)
  val base = (uint_of_GLuint)base
//
  extern fun glNewList (lst: uint, mode: GLenum): (glNewList_v | void) = "#glNewList"
  extern fun glBitmap
    (w:int, h:int, _:double, _:double, _:double, _:double, _: ptr) : void = "#glBitmap"
  // end of [glBitmap]
//
  val (pf | ()) = glNewList (base+(uint_of_char)' ', GL_COMPILE)
  val () = glBitmap (8, 13, 0.0, 2.0, 10.0, 0.0, theSpace)
  val () = glEndList (pf | (*none*))
//
  var i: Nat = 0; var lst: uint = base+(uint_of_char)'A'
  val () = for (
    i := 0; i < 26; i := i + 1, lst := lst + 1U
  ) let
    val (pf | ()) = glNewList (lst, GL_COMPILE)
    val () = glBitmap (8, 13, 0.0, 2.0, 10.0, 0.0, getLetter(i))
    val () = glEndList (pf | (*none*))
  in
    // nothing
  end // end of [for]
} // end of [makeRasterFont]

(* ****** ****** *)

extern fun initialize (): void = "initialize"
implement
initialize () = () where {
  val () = glShadeModel (GL_FLAT); val () = makeRasterFont ()
} // end of [initialize]

(* ****** ****** *)

extern fun display (): void = "display"
implement
display () = () where {
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3d (1.0, 1.0, 1.0)
  val () = glRasterPos2i ((GLint)20, (GLint)60)
  val () = printString (test1)
  val () = glRasterPos2i ((GLint)20, (GLint)40)
  val () = printString (test2)
  val () = glFlush ()
} // end of [display]

(* ****** ****** *)

extern fun reshape {w,h:nat} (w: int w, h: int h): void = "reshape"
implement
reshape (w, h) = () where {
  val () = glViewport (0, 0, w, h)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = glOrtho (0.0, (double_of)w, 0.0, (double_of)h, ~1.0, 1.0)
  val () = glMatrixMode (GL_MODELVIEW)
} // end of [reshape]

(* ****** ****** *)

extern fun keyboard (key: uchar, x: int, y: int): void = "keyboard"
implement
keyboard (key, x, y) = let
  val key = (char_of_uchar)key
in
  case+ key of
  | _ when (key = (char_of_uint)27U) => exit (0)
  | _ => ()
end // end of [keyboard]

(* ****** ****** *)

implement main_dummy () = () // [mainats] is implemented externally

(* ****** ****** *)

%{$

ats_void_type mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  glutInit ((int*)&argc, (char**)argv) ;
  glutInitWindowSize (440, 120) ;
  glutInitDisplayMode (GLUT_SINGLE | GLUT_RGB) ;
  glutCreateWindow(((char**)argv)[0]) ;
  initialize () ;
  glutReshapeFunc (reshape) ;
  glutKeyboardFunc (keyboard) ;
  glutDisplayFunc (display) ;
  glutMainLoop () ;
  return ; /* deadcode */
} // end of [mainats]

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test13.dats] *)
