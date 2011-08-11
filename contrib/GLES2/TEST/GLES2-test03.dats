(*
** In this demo, buffer objects are used for specifying
** mesh vertices as well as connectivity.
**
** New features in this example:
** - mesh loading (pass [-obj <filename>] as a parameter)
** - setting up modelview and projection matrices for 3D
** - (primitive) camera control:
**   use arrows and 'a'/'z' to spin the mesh
** TODO: incorporate v, vt, vn, vnt rendering (textured/lit)
**       (but first, get some datasets with normals and TCs!)
*)
//
// Author: Artyom Shakhakov (artyom DOT shalkhakov AT gmail DOT com)
// Time: June, 2011
//

(* ****** ****** *)

staload "libc/SATS/math.sats" // for [M_PI]
staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload "contrib/GLES2/SATS/gl2.sats"

(* ****** ******* *)

staload "utils/obj.sats"
staload "utils/mat4.sats"
staload "utils/util.sats"

(* ****** ******* *)

#define SHADER_VERT "test03.vert"
#define SHADER_FRAG "test03.frag"

(* ****** ****** *)

%{
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>
#include <EGL/egl.h>
%}

// HACKHACKHACK
%{^
extern ats_void_type mainats (
  ats_int_type argc, ats_ptr_type argv
);
%}

(* ****** ****** *)

var winx = 0
val (pf_view_winx | ()) =
  vbox_make_view_ptr {int} (view@ winx | &winx)
// end of [val]

var winy = 0
val (pf_view_winy | ()) =
  vbox_make_view_ptr {int} (view@ winy | &winy)
// end of [val]

(* ****** ****** *)

val attr_pos = (GLuint)(uint_of 0)
val attr_norm = (GLuint)(uint_of 1)

var u_matrix = (GLint)0
val (pf_u_matrix | ()) =
  vbox_make_view_ptr {GLint} (view@ u_matrix | &u_matrix)
// end of [val]

(* ****** ****** *)

var view_rotx = (GLfloat)0.0f
val (pf_view_rotx | ()) =
  vbox_make_view_ptr {GLfloat} (view@ view_rotx | &view_rotx)
// end of [prval]
var view_roty = (GLfloat)0.0f
val (pf_view_roty | ()) =
  vbox_make_view_ptr {GLfloat} (view@ view_roty | &view_roty)
// end of [prval]
var view_rotz = (GLfloat)0.0f
val (pf_view_rotz | ()) =
  vbox_make_view_ptr {GLfloat} (view@ view_rotz | &view_rotz)
// end of [prval]

extern
fun keypress (code: natLt 6): void = "keypress"
implement keypress (code) = let
  fn add {l:addr} (
      pf: vbox (GLfloat @ l)
    | p: ptr l, d: float
    ) :<!ref> void = let
    prval vbox pf_at = pf
  in
    !p := GLfloat (float_of !p + d)
  end // end of [add]
in
  case+ code of
  | 0 => add (pf_view_roty | &view_roty, 5.0f)
  | 1 => add (pf_view_roty | &view_roty, ~5.0f)
  | 2 => add (pf_view_rotx | &view_rotx, 5.0f)
  | 3 => add (pf_view_rotx | &view_rotx, ~5.0f)
  | 4 => add (pf_view_rotz | &view_rotz, ~5.0f)
  | 5 => add (pf_view_rotz | &view_rotz, 5.0f)
end // end of [keypress]

(* ****** ****** *)

dynload "obj_lats.dats"

(* ****** ****** *)

(*
extern
fun glVertexAttribPointer {a:t@ype} {n,k:nat} {ofs:int} (
  pf_mul: MUL (k, sizeof a, ofs)
| indx: GLuint
, size: GLint n
, type: GLenum_type a
, normalized: GLboolean
, stride: GLsizei ofs
, p: &GEVEC (a, n, k)
) : void
  = "mac#atsctrb_glVertexAttribPointer"
// end of [glVertexAttribPointer]
*)

(* ****** ****** *)

fun create_shaders (): void = let
   var stat: GLint
   var fragShader = glCreateShader GL_FRAGMENT_SHADER
   val () = shader_from_file (fragShader, SHADER_FRAG)
   var vertShader = glCreateShader GL_VERTEX_SHADER
   val () = shader_from_file (vertShader, SHADER_VERT)
   val program = glCreateProgram ()
   val () = glAttachShader (program, vertShader)
   val () = glAttachShader (program, fragShader)
   val () = glLinkProgram program
   val () = glGetProgramiv (program, GL_LINK_STATUS, stat)
   val () = if int_of_GLint stat = 0 then let
       var !p_log with pf_log = @[byte][1000]()
       var len: GLsizei // uninitialized
       prval pf_len = Some_v (view@ (len))
       val () = glGetProgramInfoLog (pf_log, pf_len | program, (GLsizei)1000, &len, p_log)
       prval Some_v pf = pf_len; prval () = view@ (len) := pf
       val () = begin
         print ("Error: linking:\n");
         fprint_strbuf (stdout_ref, !p_log);
         print_newline ()
       end // end of [begin]
       prval () = pf_log := bytes_v_of_strbuf_v (pf_log)
     in
       exit {void} (1)
     end // end of [if]
  val () = glUseProgram program
  val () = glBindAttribLocation (program, attr_pos, "pos")
  val () = glBindAttribLocation (program, attr_norm, "norm")
  val () = glLinkProgram program // needed to put attribs into effect
  val () = () where {
    val um = glGetUniformLocation (program, "mvp")
    prval vbox pf_u = pf_u_matrix
    val () = u_matrix := um
  } // end of [where]
  val () = glDeleteShader vertShader
  val () = glDeleteShader fragShader
  val () = let
      extern castfn __leak1 (x: GLprogram): void
    in
      __leak1 (program)
    end
in
  // nothing
end // end of [create_shaders]

(* ****** ****** *)
// External function prototypes.
// This is basically how we upload data to the GL: via calling
// external functions introduced for our ad-hoc purposes.
// The GL API defines some entry points which are difficult to handle
// in ATS: while it may be done, the effort of programming against
// such bindings would be too high.

%{^
ats_GLuint_type cast_size_to_GLuint (ats_size_type x) { return x; }

void
glBufferData_convert (
  ats_GLenum_type target
, ats_GLenum_type type
, ats_size_type tsz
, ats_size_type sz
, ats_ptr_type data
, ats_GLenum_type usage
) {
  glBufferData (target, sz * tsz, (void *)data, usage);
  return;
} // end of [glBufferData_convert]

void glBufferDataF3 (
  ats_size_type n
, ats_ref_type data
, ats_GLenum_type usage
) {
  glBufferData (GL_ARRAY_BUFFER, n * sizeof(float) * 3, (void *)data, usage);
  return;
}

void glVertexAttribPointerBuffer (
  ats_GLuint_type indx
, ats_GLsizei_type size
, ats_GLenum_type type
, ats_GLsizei_type stride
, ats_GLsizeiptr_type pos
) {
  glVertexAttribPointer (indx, size, type, GL_FALSE, stride, (void *)pos);
  return;
} // end of [glVertexAttribPointerBuffer]

void glDrawElementsBuffer (
  ats_GLenum_type mode
, ats_GLsizei_type count
, ats_GLenum_type type
) {
  glDrawElements (mode, count, type, NULL);
  return;
} // end of [glDrawElementsBuffer]

%}

extern
fun cast_size_to_GLuint (x: size_t):<> GLuint = "cast_size_to_GLuint"

extern
fun glBufferData {n:nat} {a:t@ype} (
  target: GLenum, type: GLenum_type a
, tsz: size_t (sizeof a)
, sz: size_t n, data: &(@[a][n]), usage: GLenum
) : void
  = "glBufferData_convert"
// end of [fun]

extern
fun glBufferDataF3 {n:nat} (
  n: size_t n, p: &(@[float3_t][n])
, usage: GLenum
) : void
  = "glBufferDataF3"
// end of [fun]

extern
fun glVertexAttribPointerBuffer {a:t@ype} (
  indx: GLuint
, size: GLsizei
, type: GLenum_type a
, stride: GLsizei
, pos: GLsizeiptr
) : void
  = "glVertexAttribPointerBuffer"
// end of [glVertexAttribPointerBuffer]

extern
fun glDrawElementsBuffer {a:t@ype} (
  mode: GLenum, count: GLsizei, type: GLenum_type a
) : void
  = "glDrawElementsBuffer"
// end of [glDrawElementsBuffer]

(* ****** ****** *)

local

// index buffer
viewtypedef gpuidx = @{
  buf= GLbuffer  // buffer object (storage)
, mode= GLenum   // GL_TRIANGLES, ...
, count= GLsizei // total count of indices
, type= [a:t@ype] GLenum_type a  // GL_UNSIGNED_INT, ...
} // end of [gpuidx]

// vertex buffer
viewtypedef gpuvrt = @{
  buf= GLbuffer                // buffer object (storage)
, pos= GLsizeiptr              // offset to position
, size= GLsizei                // element size (in [type])
, type= [a:t@ype] GLenum_type a  // GL_FLOAT, ...
} // end of [gpuvrt]

// TODO (perhaps): use smaller types if you can to conserve memory
extern
fun index_convert {n:nat} (
  A: &(@[triangle][n])
, n: size_t n
, res: &ptr? >> ptr l
, m: &size_t? >> size_t m
) :<!exn> #[l:addr] #[m:nat] (
  array_v (GLuint, m, l), free_gc_v (GLuint, m, l) | GLenum_type GLuint
)
implement index_convert {n} (A, n, res, resz) = let
  val (tp, tsz) = (GL_UNSIGNED_INT, sizeof<GLuint>)
  val (pf_mul | m) = n szmul2 (size1_of_int1 3)
  prval () = () where {
    prval pf2_mul = mul_make {n, 3} ()
    prval () = mul_isfun (pf_mul, pf2_mul)
  } // end of [where]
  val [l:addr] (pf_gc, pf_arr | p) = array_ptr_alloc_tsz {GLuint} (m, tsz)

  fn __cast (x: size_t):<!exn,cloref> GLuint = let
    val () = assert_errmsg (x < n, "[index_convert]: index out of range")
  in
    cast_size_to_GLuint x
  end // end of [__cast]

  fun loop {l,l2:addr} {n,m:nat} .<n>. (
      pf_arr: array_v (GLuint?, m, l)
    , pf_src: !array_v (triangle, n, l2)
    , pf_mul: MUL (n, 3, m)
    | p_src: ptr l2
    , n: size_t n
    , p_arr: ptr l
    , m: size_t m
    ) :<!exn,cloref> (array_v (GLuint, m, l) | void) =
    if n > 0 then let
      prval (pf_at, pf2_src) = array_v_uncons {triangle} (pf_src)
      prval () = mul_pos_pos_pos (pf_mul)
      prval MULind pf2_mul = pf_mul
      val (v0, v1, v2) = !p_src
      var p = p_arr

      prval (pf1_at, pf2_arr) = array_v_uncons {GLuint?} (pf_arr)
      val () = !p := __cast v0.vidx
      val () = p := p + sizeof<GLuint>

      prval (pf2_at, pf2_arr) = array_v_uncons {GLuint?} (pf2_arr)
      val () = !p := __cast v1.vidx
      val () = p := p + sizeof<GLuint>

      prval (pf3_at, pf2_arr) = array_v_uncons {GLuint?} (pf2_arr)
      val () = !p := __cast v2.vidx
      val () = p := p + sizeof<GLuint>

      val (pf3_arr | ()) = loop (pf2_arr, pf2_src, pf2_mul | p_src + sizeof<triangle>, n-1, p, m-3)

      prval () = pf_src := array_v_cons {triangle} (pf_at, pf2_src)
    in
      (array_v_cons {GLuint} (pf1_at, array_v_cons {GLuint} (pf2_at, array_v_cons {GLuint} (pf3_at, pf3_arr))) | ())
    end else let
      prval MULbas () = pf_mul
      prval () = array_v_unnil (pf_arr)
      prval () = array_v_unnil (pf_src)
      prval () = pf_src := array_v_nil {triangle} ()
    in
      (array_v_nil {GLuint} () | ())
    end
  // end of [loop]
  val (pf_arr | ()) = loop (pf_arr, view@ A, pf_mul | &A, n, p, m)
in
  res := p;
  resz := m;
  (pf_arr, pf_gc | tp)
end // end of [index_convert]

fun mesh_upload_indices (m: &mesh, res: &gpuidx? >> gpuidx): void = let
  var p: ptr and psz: size_t // uninitialized
  val (pf_f, pf_fgc | n, fp) = m.faces
  val (pf_arr, pf_gc | tp) = index_convert (!fp, n, p, psz)
  val () = m.faces := (pf_f, pf_fgc | n, fp)
  var i: GLbuffer // uninitialized
  val () = glGenBuffer (i)
  val () = glBindBuffer (GL_ELEMENT_ARRAY_BUFFER, i)
  val () = glBufferData (GL_ELEMENT_ARRAY_BUFFER, tp, sizeof<GLuint>, psz, !p, GL_STATIC_DRAW)
  extern
  castfn __cast (x: size_t):<> GLsizei
  // end of [extern]
in
  res.buf := i;
  res.mode := GL_TRIANGLES;
  res.count := __cast psz;
  res.type := tp;
  array_ptr_free (pf_gc, pf_arr | p);
end // end of [mesh_upload_indices]

fun mesh_upload_vertices (m: &mesh, res: &gpuvrt? >> gpuvrt): void = let
  var v: GLbuffer // uninitialized
  val () = glGenBuffer v
  val (pf_v, pf_vgc | n, vp) = m.verts
  extern
  castfn __cast (x: size_t):<> GLsizei
  // end of [extern]
  extern
  castfn __cast_uintptr (x: uintptr):<> GLsizeiptr
  // end of [extern]
in
  glBindBuffer (GL_ARRAY_BUFFER, v);
  glBufferDataF3 (n, !vp, GL_STATIC_DRAW);
  res.buf := v;
  res.pos := __cast_uintptr (uintptr_of 0);
  res.size := __cast 3;
  res.type := GL_FLOAT;
  m.verts := (pf_v, pf_vgc | n, vp)
end // end of [mesh_upload_vertices]

dataviewtype gpumesh = gpumesh_some of (gpuidx, gpuvrt) | gpumesh_none of ()
val the_gpumesh = ref<gpumesh> (gpumesh_none ())

in // in of [local]

fun the_gpumesh_destroy (): void = let
  val (vbox pf | p) = ref_get_view_ptr the_gpumesh
in
  case+ !p of
  | ~gpumesh_some (idx, vrt) => begin
      $effmask_all (glDeleteBuffer (idx.buf); glDeleteBuffer (vrt.buf));
      !p := gpumesh_none ()
    end // end of [begin]
  | gpumesh_none () => fold@ !p
end // end of [the_gpumesh_destroy]

fun the_gpumesh_init (m: &mesh): void = let
  val (vbox pf | p) = ref_get_view_ptr the_gpumesh
in
  case+ !p of
  | ~gpumesh_some (idx, vrt) => let
      val () = $effmask_all (glDeleteBuffer (idx.buf); glDeleteBuffer (vrt.buf))
      var idx: gpuidx and vrt: gpuvrt // uninitialized
    in
      $effmask_all (mesh_upload_indices (m, idx));
      $effmask_all (mesh_upload_vertices (m, vrt));
      !p := gpumesh_some (idx, vrt)
    end // end of [let]
  | ~gpumesh_none () => let
      var idx: gpuidx
      var vrt: gpuvrt
    in
      $effmask_all (mesh_upload_indices (m, idx));
      $effmask_all (mesh_upload_vertices (m, vrt));
      (!p := gpumesh_some (idx, vrt))
    end // end of [let]
end // end of [the_gpumesh_init]

fun the_gpumesh_draw (): void = let
  val (vbox pf | p) = ref_get_view_ptr (the_gpumesh)
in
  case+ !p of
  | gpumesh_some (!idx, !vrt) => ($effmask_all (begin
      glBindBuffer (GL_ELEMENT_ARRAY_BUFFER, !idx.buf);
      glBindBuffer (GL_ARRAY_BUFFER, !vrt.buf);

      glVertexAttribPointerBuffer (attr_pos, !vrt.size, !vrt.type, (GLsizei)0, !vrt.pos);
      glEnableVertexAttribArray attr_pos;

      glDrawElementsBuffer (!idx.mode, !idx.count, !idx.type);

      glDisableVertexAttribArray attr_pos;
    end); fold@ !p)
    // end of [let]
  | gpumesh_none () => fold@ !p
end // end of [the_gpumesh_draw]

end // end of [local]

extern
fun init (filename: string): void = "init"
implement init (filename) = let
  var msh: mesh0 // uninitialized
  val () = mesh_from_file (filename, msh)
  val () = print "loaded a mesh\n"
  val () = begin
    printf ("%d verts, %d norms, %d texcoords, %d tris\n", @(
      int1_of_size1 msh.verts.2, int1_of_size1 msh.norms.2
    , int1_of_size1 msh.texcoords.2, int1_of_size1 msh.faces.2
    ))
  end
  val () = the_gpumesh_init msh
  val () = mesh_free msh
in
  create_shaders ();
  glEnable GL_DEPTH_TEST;
  glEnable GL_CULL_FACE;
  glClearColor ((GLclampf)0.3f, (GLclampf)0.3f, (GLclampf)0.9f, (GLclampf)0.0f);
  assert_errmsg (glGetError () = GL_NO_ERROR, "[init]: glGetError <> GL_NO_ERROR")
end // end of [init]

(* ****** ****** *)

extern
fun draw (): void = "draw"
implement draw () = let
  var !p_proj = @[GLfloat][16]()
  val () = () where {
    val w = winx where { prval vbox pf_at = pf_view_winx }
    val h = winy where { prval vbox pf_at = pf_view_winy }
    val () = glViewport (GLint_of_int1 0, GLint_of_int1 0,
                         GLsizei_of_int1 (int1_of_int w), GLsizei_of_int1 (int1_of_int h))
    val () = mat_persp (30.0f, float_of w / float_of h, 1.0f, 300.0f, !p_proj)
  } // end of [where]
  var !p_modelview with pf_modelview = @[GLfloat][16]()
  val () = () where {
    val one = GLfloat_of_float 1.0f
    val zero = GLfloat_of_float 0.0f
    #define F float_of
    #define G GLfloat_of_float
    val () = array_ptr_copy_tsz (!p_proj, !p_modelview, size1_of_int1 16, sizeof<GLfloat>)
    val () = mat_trn (!p_modelview, G 0.0f, G 0.0f, G ~5.0f)
    val () = mat_rot (!p_modelview, G (2.0f * F M_PI * F view_rotx / 360.0f), one, zero, zero) where {
      prval vbox pf = pf_view_rotx
    } // end of [where]
    val () = mat_rot (!p_modelview, G (2.0f * F M_PI * F view_roty / 360.0f), zero, one, zero) where {
      prval vbox pf = pf_view_roty
    } // end of [where]
    val () = mat_rot (!p_modelview, G (2.0f * F M_PI * F view_rotz / 360.0f), zero, zero, one) where {
      prval vbox pf = pf_view_rotz
    } // end of [where]
  } // end of [where]
  // set model-view-projection
  prval pf_mat1 = array_v_sing (pf_modelview)
  val uni = let prval vbox pf_um = pf_u_matrix in u_matrix end
  val () = glUniformMatrix4fv (uni, (GLsizei)1, GL_FALSE, !p_modelview)
  prval () = pf_modelview := array_v_unsing pf_mat1
in
  glClear (GL_COLOR_BUFFER_BIT lor GL_DEPTH_BUFFER_BIT);
  the_gpumesh_draw ()
end // end of [draw]

(* ****** ****** *)

// new window size or exposure
extern
fun reshape {w,h:pos} (width: int w, height: int h): void = "reshape"
implement reshape (w, h) = begin
  winx := w where { prval vbox pf_at = pf_view_winx };
  winy := h where { prval vbox pf_at = pf_view_winy };
end // end of [reshape]

(* ****** ****** *)

implement main_dummy () = () // [mainats] is implemented externally

(* ****** ****** *)

%{$
/*
 * Create an RGB, double-buffered X window.
 * Return the window and context handles.
 */
static void
make_x_window(Display *x_dpy, EGLDisplay egl_dpy,
              const char *name,
              int x, int y, int width, int height,
              Window *winRet,
              EGLContext *ctxRet,
              EGLSurface *surfRet)
{
   static const EGLint attribs[] = {
      EGL_RED_SIZE, 1,
      EGL_GREEN_SIZE, 1,
      EGL_BLUE_SIZE, 1,
      EGL_DEPTH_SIZE, 1,
      EGL_RENDERABLE_TYPE, EGL_OPENGL_ES2_BIT,
      EGL_NONE
   };
   static const EGLint ctx_attribs[] = {
      EGL_CONTEXT_CLIENT_VERSION, 2,
      EGL_NONE
   };
   int scrnum;
   XSetWindowAttributes attr;
   unsigned long mask;
   Window root;
   Window win;
   XVisualInfo *visInfo, visTemplate;
   int num_visuals;
   EGLContext ctx;
   EGLConfig config;
   EGLint num_configs;
   EGLint vid;

   scrnum = DefaultScreen( x_dpy );
   root = RootWindow( x_dpy, scrnum );

   if (!eglChooseConfig( egl_dpy, attribs, &config, 1, &num_configs)) {
      printf("Error: couldn't get an EGL visual config\n");
      exit(1);
   }

   //   assert(config);
   //   assert(num_configs > 0);

   if (!eglGetConfigAttrib(egl_dpy, config, EGL_NATIVE_VISUAL_ID, &vid)) {
      printf("Error: eglGetConfigAttrib() failed\n");
      exit(1);
   }

   /* The X window visual must match the EGL config */
   visTemplate.visualid = vid;
   visInfo = XGetVisualInfo(x_dpy, VisualIDMask, &visTemplate, &num_visuals);
   if (!visInfo) {
      printf("Error: couldn't get X visual\n");
      exit(1);
   }

   /* window attributes */
   attr.background_pixel = 0;
   attr.border_pixel = 0;
   attr.colormap = XCreateColormap( x_dpy, root, visInfo->visual, AllocNone);
   attr.event_mask = StructureNotifyMask | ExposureMask | KeyPressMask;
   mask = CWBackPixel | CWBorderPixel | CWColormap | CWEventMask;

   win = XCreateWindow( x_dpy, root, 0, 0, width, height,
		        0, visInfo->depth, InputOutput,
		        visInfo->visual, mask, &attr );

   /* set hints and properties */
   {
      XSizeHints sizehints;
      sizehints.x = x;
      sizehints.y = y;
      sizehints.width  = width;
      sizehints.height = height;
      sizehints.flags = USSize | USPosition;
      XSetNormalHints(x_dpy, win, &sizehints);
      XSetStandardProperties(x_dpy, win, name, name,
                              None, (char **)NULL, 0, &sizehints);
   }

   eglBindAPI(EGL_OPENGL_ES_API);

   ctx = eglCreateContext(egl_dpy, config, EGL_NO_CONTEXT, ctx_attribs );
   if (!ctx) {
      printf("Error: eglCreateContext failed\n");
      exit(1);
   }

   /* test eglQueryContext() */
   {
      EGLint val;
      eglQueryContext(egl_dpy, ctx, EGL_CONTEXT_CLIENT_VERSION, &val);
      //      assert(val == 2);
   }

   *surfRet = eglCreateWindowSurface(egl_dpy, config, win, NULL);
   if (!*surfRet) {
      printf("Error: eglCreateWindowSurface failed\n");
      exit(1);
   }

   /* sanity checks */
   {
      EGLint val;
      eglQuerySurface(egl_dpy, *surfRet, EGL_WIDTH, &val);
      //      assert(val == width);
      eglQuerySurface(egl_dpy, *surfRet, EGL_HEIGHT, &val);
      //      assert(val == height);
      //      assert(eglGetConfigAttrib(egl_dpy, config, EGL_SURFACE_TYPE, &val));
      //      assert(val & EGL_WINDOW_BIT);
   }

   XFree(visInfo);

   *winRet = win;
   *ctxRet = ctx;
}

// shamelessly stolen from SDL
static int X11_KeyRepeat(Display *display, XEvent *event) {
    XEvent peekevent;

    if (XPending(display)) {
        XPeekEvent(display, &peekevent);
        if ((peekevent.type == KeyPress) &&
            (peekevent.xkey.keycode == event->xkey.keycode) &&
            ((peekevent.xkey.time-event->xkey.time) < 2)) {
            return 1;
        }
    }
    return 0;
}

static void
event_loop(Display *dpy, Window win,
           EGLDisplay egl_dpy, EGLSurface egl_surf)
{
   while (1) {
      int redraw = 0;
      XEvent event;

      XNextEvent(dpy, &event);

      switch (event.type) {
      case Expose:
         redraw = 1;
         break;
      case ConfigureNotify:
         reshape(event.xconfigure.width, event.xconfigure.height);
         break;
      case KeyPress:
         {
            char buffer[10];
            int r, code;
            code = XLookupKeysym(&event.xkey, 0);
	    switch (code) {
	    case XK_Left:
	      keypress(0);
	      break;
	    case XK_Right:
	      keypress(1);
	      break;
	    case XK_Up:
	      keypress(2);
	      break;
	    case XK_Down:
	      keypress(3);
	      break;
	    default:
               r = XLookupString(&event.xkey, buffer, sizeof(buffer),
                                 NULL, NULL);
	       if (buffer[0] == 'a' || buffer[0] == 'A') {
		 keypress(4);
	       }
	       else if (buffer[0] == 'z' || buffer[0] == 'Z') {
		 keypress(5);
	       }
               else if (buffer[0] == 27) {
                  /* escape */
                  return;
               }
	       break;
            }
         }
         redraw = 1;
         break;
      default:
	; /*no-op*/
      }

      if (redraw) {
         draw();
         eglSwapBuffers(egl_dpy, egl_surf);
      }
   }
}

static void
usage(void)
{
   printf("Usage:\n");
   printf("  -display <displayname>  set the display to run on\n");
   printf("  -info                   display OpenGL renderer info\n");
}

ats_void_type mainats (
  ats_int_type argc, ats_ptr_type argv
) {
   const int winWidth = 800, winHeight = 600;
   Display *x_dpy;
   Window win;
   EGLSurface egl_surf;
   EGLContext egl_ctx;
   EGLDisplay egl_dpy;
   char *dpyName = NULL;
   GLboolean printInfo = GL_FALSE;
   EGLint egl_major, egl_minor;
   int i;
   const char *s;
   const char *meshname = "data/bunny.obj";

   for (i = 1; i < argc; i++) {
     if (strcmp(((char **)argv)[i], "-display") == 0) {
       dpyName = ((char **)argv)[i+1]; // FIXME: reading past end?
       i++;
     }
     else if (strcmp(((char **)argv)[i], "-info") == 0) {
       printInfo = GL_TRUE;
     }
     else if (strcmp(((char **)argv)[i], "-obj") == 0) {
       meshname = ((char **)argv)[i+1]; // FIXME: reading past end?
       i++;
     }
     else {
       usage();
       return;
     }
   }

   x_dpy = XOpenDisplay(dpyName);
   if (!x_dpy) {
      printf("Error: couldn't open display %s\n",
	     dpyName ? dpyName : getenv("DISPLAY"));
      return;
   }

   egl_dpy = eglGetDisplay(x_dpy);
   if (!egl_dpy) {
      printf("Error: eglGetDisplay() failed\n");
      return;
   }

   if (!eglInitialize(egl_dpy, &egl_major, &egl_minor)) {
      printf("Error: eglInitialize() failed\n");
      return;
   }

   s = eglQueryString(egl_dpy, EGL_VERSION);
   printf("EGL_VERSION = %s\n", s);

   s = eglQueryString(egl_dpy, EGL_VENDOR);
   printf("EGL_VENDOR = %s\n", s);

   s = eglQueryString(egl_dpy, EGL_EXTENSIONS);
   printf("EGL_EXTENSIONS = %s\n", s);

   s = eglQueryString(egl_dpy, EGL_CLIENT_APIS);
   printf("EGL_CLIENT_APIS = %s\n", s);

   make_x_window(x_dpy, egl_dpy,
                 "OpenGL ES 2.x textured quad", 0, 0, winWidth, winHeight,
                 &win, &egl_ctx, &egl_surf);

   XMapWindow(x_dpy, win);
   if (!eglMakeCurrent(egl_dpy, egl_surf, egl_surf, egl_ctx)) {
      printf("Error: eglMakeCurrent() failed\n");
      return;
   }

   if (printInfo) {
      printf("GL_RENDERER   = %s\n", (char *) glGetString(GL_RENDERER));
      printf("GL_VERSION    = %s\n", (char *) glGetString(GL_VERSION));
      printf("GL_VENDOR     = %s\n", (char *) glGetString(GL_VENDOR));
      printf("GL_EXTENSIONS = %s\n", (char *) glGetString(GL_EXTENSIONS));
   }

   init((ats_ptr_type)meshname);

   /* Set initial projection/viewing transformation.
    * We can't be sure we'll get a ConfigureNotify event when the window
    * first appears.
    */
   reshape(winWidth, winHeight);

   event_loop(x_dpy, win, egl_dpy, egl_surf);

   eglDestroyContext(egl_dpy, egl_ctx);
   eglDestroySurface(egl_dpy, egl_surf);
   eglTerminate(egl_dpy);


   XDestroyWindow(x_dpy, win);
   XCloseDisplay(x_dpy);

   return;
} // end of [mainats]
%} // end of [%{$]

(* end of [GLES2-test03.dats] *)
