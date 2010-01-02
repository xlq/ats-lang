(*
**
** A simple OpenGL example
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January, 2010
**
*)

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

typedef point = @{
  x= double, y= double, r= double, b= double, g= double, a= double
}

viewtypedef pgn (n:int) = @{
  nvrtx= int n
, cntr_x= double, cntr_y = double
, vrtxlst= list_vt (point, n)
, rot_v= double // rotating velocity
, angle= double // current angle
}

viewtypedef pgn0 = pgn 0
viewtypedef pgn = [n:nat] pgn (n)
viewtypedef pgnlst = List_vt (pgn)

(* ****** ****** *)

staload MATH = "libc/SATS/math.sats"

macdef PI = $MATH.M_PI
macdef PI2 = 2 * PI
macdef sin = $MATH.sin
macdef cos = $MATH.cos

(* ****** ****** *)

staload RAND = "libc/SATS/random.sats"
macdef drand48 = $RAND.drand48
val () = $RAND.srand48_with_time () // generating a new seed

(* ****** ****** *)

#define NSIDE_MAX 7.0
#define ROT_V_MAX 15.0

fun pgn_make (pgn: &pgn0? >> pgn): void = let
  val n = 3 + int_of_double ((NSIDE_MAX - 3.000001) * drand48 ())
  val [n:int] n = int1_of_int (n)
  val () = assert (n >= 3)
(*
  val () = printf ("pgn_make: n = %i\n", @(n))
*)
  val theta0 = drand48 () * PI2
  val delta = PI2 / n
  val pts = loop (n, theta0) where {
    fun loop {n:nat}
      (n: int n, theta: double):<cloref1> list_vt (point, n) =
      if n > 0 then let
        val xs1 = loop (n-1, theta + delta)
        val xs = list_vt_cons {point} (?, xs1)
        val list_vt_cons (!p_x, _) = xs
        val () = p_x->x := cos theta
        val () = p_x->y := sin theta
        val () = p_x->r := drand48 ()
        val () = p_x->g := drand48 ()
        val () = p_x->b := drand48 ()
        val () = p_x->a := drand48 ()
      in
        fold@ xs; xs
      end else list_vt_nil ()
  } // end of [loop]
in
  pgn.nvrtx := n;
  pgn.cntr_x := drand48 () - 0.5; pgn.cntr_y := drand48 () - 0.5;
  pgn.vrtxlst := pts;
  pgn.rot_v := ROT_V_MAX * (drand48 () - 0.5);
  pgn.angle := 360 * drand48 ()
end // end of [pgn_make]

fun pgnlst_make {k:nat}
  (k: int k): list_vt (pgn, k) = let
  fun loop {k:nat} .<k>.
    (k: int k, res: &pgnlst? >> list_vt (pgn, k)): void =
    if k > 0 then let
      val () = res := list_vt_cons {pgn0} {0} (?, ?)
      val list_vt_cons (!p_x, !p_xs1) = res
      val () = pgn_make (!p_x)
      val () = loop (k-1, !p_xs1)
    in
      fold@ res
    end else (res := list_vt_nil ())
  // end of [loop]
  var res: pgnlst // uninitialized
in
  loop (k, res); res
end // end of [pgnlst_make]

(* ****** ****** *)

var thePgnLst: pgnlst = pgnlst_make (32)

val (pf_thePgnLst | ()) =
  vbox_make_view_ptr {pgnlst} (view@ thePgnLst | &thePgnLst)
// end of [prval]

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

staload "contrib/GL/SATS/gl.sats"
staload "contrib/GL/SATS/glu.sats"
staload "contrib/GL/SATS/glut.sats"

(* ****** ****** *)

#define RADIUS 0.1

(* ****** ****** *)

#define PERTURB_COEFF 1.0/10
fn perturb (x: double): double = let
  val alpha = (drand48 () - 0.5)
in
  x + PERTURB_COEFF * alpha
end // end of [perturb]

(* ****** ****** *)

extern fun draw_pgn (pgn: &pgn): void = "draw_pgn"

implement draw_pgn (pgn) = let
  fun loop {n:nat} .<n>. (
      pts: !list_vt (point, n)
    ) : void =
    case+ pts of
    | list_vt_cons (pt, !p_pts1) => let
        val () = glColor4d (pt.r, pt.g, pt.b, pt.a)
        val () = glVertex2d (pt.x, pt.y)
        val () = loop (!p_pts1)
      in
        fold@ pts
      end // end of [list_vt_cons]
    | list_vt_nil () => fold@ pts
  // end of [loop]
  val (pf_pushmat | ()) = glPushMatrix ()
  val xc = perturb (pgn.cntr_x) and yc = perturb (pgn.cntr_y)
  val () = glTranslated (xc, yc, 0.0)
//
  val t0 = pgn.angle
  val () = glRotated (t0, 0.0, 0.0, 1.0)
  val () = pgn.angle := t0 + pgn.rot_v
//
  val () = glScaled (RADIUS, RADIUS, 1.0)
  val (pf_begin | ()) = glBegin (GL_POLYGON)
  val () = loop (pgn.vrtxlst)
  val () = glEnd (pf_begin | (*none*))
  val () = glPopMatrix (pf_pushmat | (*none*))
in
  // nothing
end // end of [draw_pgn]

(* ****** ****** *)

(*
fun draw_pgnlst (pgns: !pgnlst): void =
  case+ pgns of
  | list_vt_cons (!p_pgn, !p_pgns1) => begin
      draw_pgn (!p_pgn); draw_pgnlst (!p_pgns1); fold@ pgns
    end // end of [list_vt_cons]
  | list_vt_nil () => fold@ pgns
// end of [draw_pgnlst]
*)

extern fun{a:t@ype} array_ptr_shuffle 
  {n:nat} {l:addr} (pf: !array_v (a, n, l) | p: ptr l, n: size_t n):<> void
// end of [extern]

implement{a} array_ptr_shuffle
  (pf | p, n) = loop (pf | p, n) where {
  #define i2sz size1_of_int1; #define sz2i int1_of_size1
  fun loop {n:nat} {l:addr} .<n>.
    (pf: !array_v (a, n, l) | p: ptr l, n: size_t n):<> void =
    if n >= 2 then let
      val i = $effmask_ref ($RAND.randint (sz2i n))
      val () = if i <> 0 then array_ptr_exch<a> (!p, 0, i2sz i)
      prval (pf1, pf2) = array_v_uncons {a} (pf)
      val () = loop (pf2 | p + sizeof<a>, n-1)
      prval () = pf := array_v_cons {a} (pf1, pf2)
    in
      // nothing
    end // end of [if]
  // end of [loop]  
} (* end of [array_ptr_shuffle] *)

fn draw_pgnlst {n:nat}
  (pgns: !list_vt (pgn, n)): void = let
  val n = list_vt_length<pgn> (pgns)
  abst@ype a = pgn?
  val xs = __cast pgns where {
    extern castfn __cast (xs: !list_vt (pgn, n)): list (a, n)
  } // end of [val]
  var !p_arr with pf_arr = @[a][n]() // stack allocation
  val () = array_ptr_initialize_lst<a> (!p_arr, xs)
  val asz = size1_of_int1 n
  val () = array_ptr_shuffle<a> (pf_arr | p_arr, asz)
  extern fun f (pf: !unit_v | x: &a):<> void = "draw_pgn"
  prval pf_unit = unit_v ()
  val () = array_ptr_foreach_fun<a> {unit_v} (pf_unit | !p_arr, f, asz)
  prval unit_v () = pf_unit
in
  // nothing
end // end of [draw_pgnlst]

(* ****** ****** *)

extern
fun initialize (): void = "initialize"
implement initialize () = let
(*
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = glOrtho (0.0, 1.0, 0.0, 1.0, ~1.0, 1.0)
*)
in
  // empty
end // end of [initialize]

(* ****** ****** *)

extern
fun display (): void = "display"
implement display () = let
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = let
    prval vbox pflst = pf_thePgnLst
  in
    $effmask_ref (draw_pgnlst thePgnLst)
  end // end of [val]
  val () = glutSwapBuffers ()
in
  // nothing
end // end of [display]

(* ****** ****** *)

extern
fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = let
  val () = glViewport (0, 0, w, h)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val x = 0.65 and y = 0.65
  val () = glOrtho (~x, x, y, ~y, ~1.0, 1.0)
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
in
  // empty
end // end of [reshape]

(* ****** ****** *)

//

implement main_dummy () = ()

//

%{$

ats_void_type mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  glutInit ((int*)&argc, (char**)argv) ;
  glutInitDisplayMode (GLUT_DOUBLE | GLUT_RGB) ;
  glutInitWindowSize (500, 500) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow("Hello!") ;
  initialize () ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;
  glutIdleFunc (glutPostRedisplay) ;
  glutMainLoop () ;
  return ; /* deadcode */
} // end of [mainats]

%} // end of [%{$]

(* ****** ****** *)

(* end of [GL-test7.dats] *)
