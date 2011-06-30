(*
** This demo displays a textured quad.
*)
(* ****** ****** *)
//
// Author: Artyom Shakhakov (artyom DOT shalkhakov AT gmail DOT com)
// Time: June, 2011
//
(* ****** ****** *)

staload "libc/SATS/math.sats"

staload _(*anonymous*) = "prelude/DATS/array.dats"

staload "contrib/GLES2/SATS/gl2.sats"

staload "contrib/GLES2/TEST/SATS/util.sats"

(* ****** ****** *)

#define SHADER_VERT "test02.vert"
#define SHADER_FRAG "test02.frag"
#define IMAGE "datasets/tex2d.tga"

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

val attr_pos = (GLuint)(uint_of 0)
val attr_texcoord = (GLuint)(uint_of 1)

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

extern
fun keypress (code: natLt 4):<!ref> void = "keypress"
implement keypress (code) = let
  #define F float_of_GLfloat
in
  case+ code of
  | 0 => (*left*) let
      prval vbox pf_aty = pf_view_roty
    in
      view_roty := (GLfloat)(F view_roty + 5.0f)
    end
  | 1 => (*right*) let
      prval vbox pf_aty = pf_view_roty
    in
      view_roty := (GLfloat)(F view_roty - 5.0f)
    end
  | 2 => (*up*) let
      prval vbox pf_atx = pf_view_rotx
    in
      view_rotx := (GLfloat)(F view_rotx + 5.0f)
    end
  | 3 => (*down*) let
      prval vbox pf_atx = pf_view_rotx
    in
      view_rotx := (GLfloat)(F view_rotx - 5.0f)
    end
end // end of [keypress]

(* ****** ****** *)

fun create_shaders (tex2d: GLtexture): void = let
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
  val () = glBindAttribLocation (program, attr_texcoord, "texcoord")
  val () = glLinkProgram program // needed to put attribs into effect
  val () = () where {
    val um = glGetUniformLocation (program, "mvp")
    prval vbox pf_u = pf_u_matrix
    val () = u_matrix := um
  } // end of [where]
  val () = () where {
    val um = glGetUniformLocation (program, "tex")
    // texture that is bound on TMU0 goes to [tex]
    val () = glUniform1i (um, (GLint)0)
  } // end of [where]
  val () = glDeleteShader vertShader
  val () = glDeleteShader fragShader
  val () = let
      extern castfn __leak1 (x: GLprogram): void
      extern castfn __leak2 (x: GLtexture): void
    in
      __leak1 (program); __leak2 (tex2d)
    end
in
(*
  printf ("Uniform modelviewProjection at %d\n", int_of u_matrix);
  printf ("Attrib pos at %d\n", int_of attr_pos);
  printf ("Attrib color at %d\n", int_of attr_color)
*)
end

extern
fun init (): void = "init"
implement init () = let
  var tex: GLtexture // uninitialized
in
  glGenTexture tex;
  texture_from_file (tex, IMAGE);
  create_shaders (tex);
  glClearColor ((GLclampf)0.4f, (GLclampf)0.4f, (GLclampf)0.4f, (GLclampf)0.0f);
  assert_errmsg (glGetError () = GL_NO_ERROR, "[init]: glGetError() <> GL_NO_ERROR")
end

(* ****** ****** *)

fn make_z_rot_matrix (angle: GLfloat, m: &(@[GLfloat?][16]) >> @[GLfloat][16]):<> void = let
  val c = (GLfloat) (cosf (float_of angle * 3.14f / 180.0f))
  val s = (GLfloat) (sinf (float_of angle * 3.14f / 180.0f))
  val () = array_ptr_initialize_elt<GLfloat> (m, size1_of_int1 16, (GLfloat)0.0f)
in
  m.[0] := c;
  m.[1] := s;
  m.[4] := (GLfloat)(~float_of s);
  m.[5] := c;
  m.[10] := (GLfloat)1.0f;
  m.[15] := (GLfloat)1.0f
end // end of [make_z_rot_matrix]

fn make_scale_matrix (
  xs: GLfloat, ys: GLfloat, zs: GLfloat, m: &(@[GLfloat?][16]) >> @[GLfloat][16]
) :<> void = let
  val () = array_ptr_initialize_elt<GLfloat> (m, 16, (GLfloat)0.0f)
in
  m.[0] := xs;
  m.[5] := ys;
  m.[10] := zs;
  m.[15] := (GLfloat)1.0f
end // end of [make_scale_matrix]

fn mul_matrix (
  p: &(@[GLfloat?][16]) >> @[GLfloat][16]
, a: &(@[GLfloat][16])
, b: &(@[GLfloat][16])
) : void = let
  #define F float_of
  #define G GLfloat_of_float
  // this is only for the sake of making the code below typecheck!
  val () = array_ptr_initialize_elt<GLfloat> (p, 16, G 0.0f)

  val ai0 = F a.[0] and ai1 = F a.[1] and ai2 = F a.[2] and ai3 = F a.[3]
  val () = p.[0] := G (ai0 * F b.[0] + ai1 * F b.[4] + ai2 * F b.[8] + ai3 * F b.[12]);
  val () = p.[1] := G (ai0 * F b.[1] + ai1 * F b.[5] + ai2 * F b.[9] + ai3 * F b.[13]);
  val () = p.[2] := G (ai0 * F b.[2] + ai1 * F b.[6] + ai2 * F b.[10] + ai3 * F b.[14]);
  val () = p.[3] := G (ai0 * F b.[3] + ai1 * F b.[7] + ai2 * F b.[11] + ai3 * F b.[15])

  val ai0 = F a.[4] and ai1 = F a.[5] and ai2 = F a.[6] and ai3 = F a.[7]
  val () = p.[4] := G (ai0 * F b.[0] + ai1 * F b.[4] + ai2 * F b.[8] + ai3 * F b.[12]);
  val () = p.[5] := G (ai0 * F b.[1] + ai1 * F b.[5] + ai2 * F b.[9] + ai3 * F b.[13]);
  val () = p.[6] := G (ai0 * F b.[2] + ai1 * F b.[6] + ai2 * F b.[10] + ai3 * F b.[14]);
  val () = p.[7] := G (ai0 * F b.[3] + ai1 * F b.[7] + ai2 * F b.[11] + ai3 * F b.[15])  

  val ai0 = F a.[8] and ai1 = F a.[9] and ai2 = F a.[10] and ai3 = F a.[11]
  val () = p.[8] := G (ai0 * F b.[0] + ai1 * F b.[4] + ai2 * F b.[8] + ai3 * F b.[12]);
  val () = p.[9] := G (ai0 * F b.[1] + ai1 * F b.[5] + ai2 * F b.[9] + ai3 * F b.[13]);
  val () = p.[10] := G (ai0 * F b.[2] + ai1 * F b.[6] + ai2 * F b.[10] + ai3 * F b.[14]);
  val () = p.[11] := G (ai0 * F b.[3] + ai1 * F b.[7] + ai2 * F b.[11] + ai3 * F b.[15])

  val ai0 = F a.[12] and ai1 = F a.[13] and ai2 = F a.[14] and ai3 = F a.[15]
  val () = p.[12] := G (ai0 * F b.[0] + ai1 * F b.[4] + ai2 * F b.[8] + ai3 * F b.[12]);
  val () = p.[13] := G (ai0 * F b.[1] + ai1 * F b.[5] + ai2 * F b.[9] + ai3 * F b.[13]);
  val () = p.[14] := G (ai0 * F b.[2] + ai1 * F b.[6] + ai2 * F b.[10] + ai3 * F b.[14]);
  val () = p.[15] := G (ai0 * F b.[3] + ai1 * F b.[7] + ai2 * F b.[11] + ai3 * F b.[15])
in
  ()
end // end of [mul_matrix]

extern
fun draw (): void = "draw"
implement draw () = let
  var !p_texcoord with pf_texcoord = @[GLfloat](
    (GLfloat)0.0f, (GLfloat)0.0f
  , (GLfloat)1.0f, (GLfloat)0.0f
  , (GLfloat)0.0f, (GLfloat)1.0f
  , (GLfloat)1.0f, (GLfloat)1.0f
  ) // end of [p_texcoord]
  var !p_verts with pf_verts = @[GLfloat](
    (GLfloat)~1.0f, (GLfloat)~1.0f
  , (GLfloat)1.0f,  (GLfloat)~1.0f
  , (GLfloat)~1.0f, (GLfloat)1.0f
  , (GLfloat)1.0f,  (GLfloat)1.0f
  ) // end of [p_verts]
  var !p_mat with pf_mat = @[GLfloat][16]()
  var !p_rot with pf_rot = @[GLfloat][16]()
  var !p_scale with pf_scale = @[GLfloat][16]()
in
  // set modelview/projection matrix
  make_z_rot_matrix (view_rotx, !p_rot) where { prval vbox pf = pf_view_rotx };
  make_scale_matrix ((GLfloat)0.5f, (GLfloat)0.5f, (GLfloat)0.5f, !p_scale);
  mul_matrix (!p_mat, !p_rot, !p_scale);
  () where {
    prval pf_mat1 = array_v_sing (pf_mat)
    val uni = let prval vbox pf_um = pf_u_matrix in u_matrix end
    val () = glUniformMatrix4fv (uni, (GLsizei)1, GL_FALSE, !p_mat)
    prval () = pf_mat := array_v_unsing pf_mat1
  }; // end of [where]
  glClear (GL_COLOR_BUFFER_BIT lor GL_DEPTH_BUFFER_BIT);
  () where {
    prval pfmul = mul_make {4,2} ()
    prval pfmat = matrix_v_of_array_v {GLfloat} (pfmul, pf_verts)
    val () = glVertexAttribPointer (pfmat | attr_pos, (GLint)2, GL_FLOAT, GL_FALSE, (GLsizei)0, p_verts)
    prval (pfmul', pfarr) = array_v_of_matrix_v {GLfloat} (pfmat)
    prval () = mul_isfun (pfmul, pfmul')
    prval () = pf_verts := pfarr
  }; // end of [where]
  () where {
    prval pfmul = mul_make {4,2} ()
    prval pfmat = matrix_v_of_array_v {GLfloat} (pfmul, pf_texcoord)
    val () = glVertexAttribPointer (pfmat | attr_texcoord, (GLint)2, GL_FLOAT, GL_FALSE, (GLsizei)0, p_texcoord)
    prval (pfmul', pfarr) = array_v_of_matrix_v {GLfloat} (pfmat)
    prval () = mul_isfun (pfmul, pfmul')
    prval () = pf_texcoord := pfarr
  }; // end of [where]
  glEnable GL_TEXTURE_2D;
  glEnableVertexAttribArray attr_pos;
  glEnableVertexAttribArray attr_texcoord;
  // FIXME: it is as if OpenGL holds onto our pointers until we ... what?
  // disable vertex attribute arrays?
  glDrawArrays (GL_TRIANGLE_STRIP, (GLint)0, (GLsizei)4);
  glDisableVertexAttribArray attr_pos;
  glDisableVertexAttribArray attr_texcoord;
  glDisable GL_TEXTURE_2D
end // end of [draw]

(* ****** ****** *)

extern
fun reshape {w,h:pos} (width: int w, height: int h): void = "reshape"
implement reshape (w, h) =
  glViewport (
    GLint_of_int1 0, GLint_of_int1 0
  , GLsizei_of_int1 w, GLsizei_of_int1 h
  )

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
               if (buffer[0] == 27) {
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
   const int winWidth = 300, winHeight = 300;
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

   for (i = 1; i < argc; i++) {
     if (strcmp(((char **)argv)[i], "-display") == 0) {
       dpyName = ((char **)argv)[i+1];
         i++;
      }
     else if (strcmp(((char **)argv)[i], "-info") == 0) {
         printInfo = GL_TRUE;
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

   init();

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

(* end of [GLES2-test02.dats] *)
