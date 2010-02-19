(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
**
** All rights reserved
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
*)

(* ****** ****** *)

// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: January, 2010

(* ****** ****** *)

macdef SDL_ALPHA_OPAQUE = 255
macdef SDL_ALPHA_TRANSPARENT = 0

(* ****** ****** *)

typedef SDL_Rect =
  $extype_struct "SDL_Rect" of {
  x= Sint16, y= Sint16, w= Uint16, h= Uint16
} // end of [SDL_Rect]

fun SDL_Rect_init (
    rect: &SDL_Rect? >> SDL_Rect
  , x: Sint16, y: Sint16, w: Uint16, h: Uint16
  ) :<> void
  = "atsctrb_SDL_Rect_init"

(* ****** ****** *)

typedef SDL_Color =
  $extype_struct "SDL_Color" of {
  r= Uint8, g= Uint8, b= Uint8 (* , unused= Uint8 *)
} // end of [SDL_Color]

fun SDL_Color_init (
    color: &SDL_Color? >> SDL_Color, r: Uint8, g: Uint8, b: Uint8
  ) :<> void
  = "atsctrb_SDL_Color_init"

(* ****** ****** *)

absviewt@ype SDL_PixelFormat_rest // ...

viewtypedef SDL_PixelFormat =
  $extype_struct "SDL_PixelFormat" of {
  BitsPerPixel= Uint8
, BytesPerPixel= Uint8
, Rloss= Uint8, Gloss= Uint8, Bloss= Uint8, Aloss= Uint8
, Rshift= Uint8, Gshift= Uint8, Bshift= Uint8, Ashift= Uint8
, Rmask= Uint32, Gmask= Uint32, Bmask= Uint32, Amask= Uint32
, colorkey= Uint32
, alpha= Uint8
, rest=SDL_PixelFormat_rest // fields that are not exported
} // end of [SDL_PixelFormat]

(* ****** ****** *)

// [SDL_Surface_ref] is reference counted
absviewtype SDL_Surface_ref (l:addr) // SDL_Surface* or null
viewtypedef SDL_Surface_ref0 = [l:addr] SDL_Surface_ref l
viewtypedef SDL_Surface_ref1 = [l:addr | l <> null] SDL_Surface_ref l

castfn SDL_Surface_ref_null (p: ptr null): SDL_Surface_ref null

castfn SDL_Surface_ref_free_null (sf: SDL_Surface_ref null): ptr
overload ref_free_null with SDL_Surface_ref_free_null

fun SDL_Surface_ref_is_null
  {l:addr} (x: !SDL_Surface_ref l):<> bool (l == null)
  = "atsctrb_SDL_ref_is_null"
overload ref_is_null with SDL_Surface_ref_is_null

fun SDL_Surface_ref_isnot_null
  {l:addr} (x: !SDL_Surface_ref l):<> bool (l <> null)
  = "atsctrb_SDL_ref_isnot_null"
overload ref_isnot_null with SDL_Surface_ref_isnot_null

(* ****** ****** *)

fun SDL_Surface_flags {l:anz} (sf: !SDL_Surface_ref l): Uint32
  = "#atsctrb_SDL_Surface_flags"

fun SDL_Surface_format {l:anz} (
    sf: !SDL_Surface_ref l
  ) : [l_format:addr] (
    minus (SDL_Surface_ref l, SDL_PixelFormat @ l_format)
  , SDL_PixelFormat @ l_format
  | ptr l_format
  ) = "#atsctrb_SDL_Surface_format"
// end of [SDL_Surface_format]

fun SDL_Surface_w {l:anz} (sf: !SDL_Surface_ref l): int
  = "#atsctrb_SDL_Surface_w"

fun SDL_Surface_h {l:anz} (sf: !SDL_Surface_ref l): int
  = "#atsctrb_SDL_Surface_h"

fun SDL_Surface_pitch {l:anz} (sf: !SDL_Surface_ref l): Uint16
  = "#atsctrb_SDL_Surface_pitch"

fun SDL_Surface_clip_rect {l:anz} (
    sf: !SDL_Surface_ref l
  ) : [l_rect:addr] (
    minus (SDL_Surface_ref l, SDL_Rect @ l_rect)
  , SDL_Rect @ l_rect
  | ptr l_rect
  ) = "#atsctrb_SDL_Surface_clip_rect"
// end of [SDL_Surface_clip_rect]

fun SDL_Surface_refcount {l:anz} (sf: !SDL_Surface_ref l): int
  = "#atsctrb_SDL_Surface_refcount"

(* ****** ****** *)

(*
/** Available for SDL_CreateRGBSurface() or SDL_SetVideoMode() */
#define SDL_SWSURFACE	0x00000000	/**< Surface is in system memory */
#define SDL_HWSURFACE	0x00000001	/**< Surface is in video memory */
#define SDL_ASYNCBLIT	0x00000004	/**< Use asynchronous blits if possible */
*)
macdef SDL_SWSURFACE = $extval (Uint32, "SDL_SWSURFACE")
macdef SDL_HWSURFACE = $extval (Uint32, "SDL_HWSURFACE")
macdef SDL_ASYNCBLIT = $extval (Uint32, "SDL_ASYNCBLIT")

(* ****** ****** *)

(*
/** Available for SDL_SetVideoMode() */
#define SDL_ANYFORMAT	0x10000000	/**< Allow any video depth/pixel-format */
#define SDL_HWPALETTE	0x20000000	/**< Surface has exclusive palette */
#define SDL_DOUBLEBUF	0x40000000	/**< Set up double-buffered video mode */
#define SDL_FULLSCREEN	0x80000000	/**< Surface is a full screen display */
#define SDL_OPENGL      0x00000002      /**< Create an OpenGL rendering context */
#define SDL_OPENGLBLIT	0x0000000A	/**< Create an OpenGL rendering context and use it for blitting */
#define SDL_RESIZABLE	0x00000010	/**< This video mode may be resized */
#define SDL_NOFRAME	0x00000020	/**< No window caption or edge frame */
*)
macdef SDL_ANYFORMAT = $extval (Uint32, "SDL_ANYFORMAT")
macdef SDL_HWPALETTE = $extval (Uint32, "SDL_HWPALETTE")
macdef SDL_DOUBLEBUF = $extval (Uint32, "SDL_DOUBLEBUF")
macdef SDL_FULLSCREEN = $extval (Uint32, "SDL_FULLSCREEN")
macdef SDL_OPENGL = $extval (Uint32, "SDL_OPENGL")
macdef SDL_OPENGLBLIT = $extval (Uint32, "SDL_OPENGLBLIT")
macdef SDL_RESIZABLE = $extval (Uint32, "SDL_RESIZABLE")
macdef SDL_NOFRAME = $extval (Uint32, "SDL_NOFRAME")

(*
/** Used internally (read-only) */
#define SDL_HWACCEL	0x00000100	/**< Blit uses hardware acceleration */
#define SDL_SRCCOLORKEY	0x00001000	/**< Blit uses a source color key */
#define SDL_RLEACCELOK	0x00002000	/**< Private flag */
#define SDL_RLEACCEL	0x00004000	/**< Surface is RLE encoded */
#define SDL_SRCALPHA	0x00010000	/**< Blit uses source alpha blending */
#define SDL_PREALLOC	0x01000000	/**< Surface uses preallocated memory */
*)
macdef SDL_HWACCEL = $extval (Uint32, "SDL_HWACCEL")
macdef SDL_SRCCOLORKEY = $extval (Uint32, "SDL_SRCCOLORKEY")
macdef SDL_RLEACCELOK = $extval (Uint32, "SDL_RLEACCELOK")
macdef SDL_RLEACCEL = $extval (Uint32, "SDL_RLEACCEL")
macdef SDL_SRCALPHA = $extval (Uint32, "SDL_SRCALPHA")
macdef SDL_PREALLOC = $extval (Uint32, "SDL_PREALLOC")

(* ****** ****** *)

abst@ype SDL_GLattr = $extype "SDL_GLattr"
macdef SDL_GL_RED_SIZE = $extval (SDL_GLattr, "SDL_GL_RED_SIZE")
macdef SDL_GL_GREEN_SIZE = $extval (SDL_GLattr, "SDL_GL_GREEN_SIZE")
macdef SDL_GL_BLUE_SIZE = $extval (SDL_GLattr, "SDL_GL_BLUE_SIZE")
macdef SDL_GL_ALPHA_SIZE = $extval (SDL_GLattr, "SDL_GL_ALPHA_SIZE")
macdef SDL_GL_BUFFER_SIZE = $extval (SDL_GLattr, "SDL_GL_BUFFER_SIZE")
macdef SDL_GL_DOUBLEBUFFER = $extval (SDL_GLattr, "SDL_GL_DOUBLEBUFFER")
macdef SDL_GL_DEPTH_SIZE = $extval (SDL_GLattr, "SDL_GL_DEPTH_SIZE")
macdef SDL_GL_STENCIL_SIZE = $extval (SDL_GLattr, "SDL_GL_STENCIL_SIZE")
macdef SDL_GL_ACCUM_RED_SIZE = $extval (SDL_GLattr, "SDL_GL_ACCUM_RED_SIZE")
macdef SDL_GL_ACCUM_GREEN_SIZE = $extval (SDL_GLattr, "SDL_GL_ACCUM_GREEN_SIZE")
macdef SDL_GL_ACCUM_BLUE_SIZE = $extval (SDL_GLattr, "SDL_GL_ACCUM_BLUE_SIZE")
macdef SDL_GL_ACCUM_ALPHA_SIZE = $extval (SDL_GLattr, "SDL_GL_ACCUM_ALPHA_SIZE")
macdef SDL_GL_STEREO = $extval (SDL_GLattr, "SDL_GL_STEREO")
macdef SDL_GL_MULTISAMPLEBUFFERS = $extval (SDL_GLattr, "SDL_GL_MULTISAMPLEBUFFERS")
macdef SDL_GL_MULTISAMPLESAMPLES = $extval (SDL_GLattr, "SDL_GL_MULTISAMPLESAMPLES")
macdef SDL_GL_ACCELERATED_VISUAL = $extval (SDL_GLattr, "SDL_GL_ACCELERATED_VISUAL")
macdef SDL_GL_SWAP_CONTROL = $extval (SDL_GLattr, "SDL_GL_SWAP_CONTROL")

(* ****** ****** *)

absview Video_v (l:addr)
praxi Video_v_unnull (pf: Video_v null): void

fun SDL_SetVideoMode (
    width: int
  , height: int
  , bpp: int
  , flags: Uint32
  ) : [l:addr] (Video_v l | SDL_Surface_ref l)
  = "#atsctrb_SDL_SetVideoMode"

fun SDL_SetVideoMode_exn (
    width: int
  , height: int
  , bpp: int
  , flags: Uint32
  ) : [l:anz] (Video_v l | SDL_Surface_ref l)

fun SDL_ResetVideoMode {l:addr} (
    pf: Video_v l
  | surf: SDL_Surface_ref l
  , width: int
  , height: int
  , bpp: int
  , flags: Uint32
  ) : [l:addr] (Video_v l | SDL_Surface_ref l)
  = "atsctrb_SDL_ResetVideoMode"

(* ****** ****** *)

//
// note: x=y=w=h=0 means the whole screen!
//
fun SDL_UpdateRect {l:anz} (
    screen: !SDL_Surface_ref l, x: Sint32, y: Sint32, w: Uint32, h: Uint32
  ) : void
  = "#atsctrb_SDL_UpdateRect"
  
fun SDL_UpdateRects {l:anz} {n:nat}
  (screen: !SDL_Surface_ref l, n: int n, rects: &(@[SDL_Rect][n])): void
  = "#atsctrb_SDL_UpdateRects"
  
(* ****** ****** *)

fun SDL_Flip {l:anz} (screen: !SDL_Surface_ref l): int (*err*)
  = "#atsctrb_SDL_Flip"

(* ****** ****** *)

fun SDL_SetGamma (red: float, green: float, blue: float): int (*err*)
  = "atsctrb_SDL_SetGamma"

(* ****** ****** *)

fun SDL_GetGammaRamp (
    red: &(@[Uint16?][256]) >> @[Uint16?][256]
  , green: &(@[Uint16?][256]) >> @[Uint16?][256]
  , blue: &(@[Uint16?][256]) >> @[Uint16?][256]
  ) : int (*err*)
  = "atsctrb_SDL_GetGammaRamp"

fun SDL_SetGammaRamp (
    red: &(@[Uint16][256]), green: &(@[Uint16][256]), blue: &(@[Uint16][256])
  ) : int (*err*)
  = "atsctrb_SDL_SetGammaRamp"

(* ****** ****** *)

fun SDL_MapRGB (
    format: &SDL_PixelFormat, r: Uint8, g: Uint8, b: Uint8
  ) : Uint32
  = "#atsctrb_SDL_MapRGB"

fun SDL_MapRGBA (
    format: &SDL_PixelFormat, r: Uint8, g: Uint8, b: Uint8, a: Uint8
  ) : Uint32
  = "#atsctrb_SDL_MapRGBA"

(* ****** ****** *)

fun SDL_CreateRGBSurface (
    flags: Uint32
  , width: int, height: int, depth: int
  , Rmask: Uint32, Gmask: Uint32, Bmask: Uint32, Amask: Uint32
  ) : SDL_Surface_ref0
  = "#atsctrb_SDL_CreateRGBSurface"

fun SDL_CreateRGBSurfaceFrom (
    data: ptr // this is unsafe
  , width: int, height: int, depth: int, pitch: int
  , Rmask: Uint32, Gmask: Uint32, Bmask: Uint32, Amask: Uint32
  ) : SDL_Surface_ref0
  = "#atsctrb_SDL_CreateRGBSurfaceFrom"

fun SDL_FreeSurface (surface: SDL_Surface_ref1): void = "#atsctrb_SDL_FreeSurface"

(* ****** ****** *)

absview SDL_Surface_v (l:addr)

fun SDL_LockSurface {l:anz} (surface: !SDL_Surface_ref l)
  : [i:int | i <= 0] (option_v (SDL_Surface_v l, i==0) | int i)
  = "atsctrb_SDL_LockSurface"

fun SDL_LockSurface_exn {l:anz}
  (surface: !SDL_Surface_ref l): (SDL_Surface_v l | void)
  = "atsctrb_SDL_LockSurface_exn"

fun SDL_UnlockSurface {l:anz}
  (pf: SDL_Surface_v l | surface: !SDL_Surface_ref l): int
 = "atsctrb_SDL_UnlockSurface"

(* ****** ****** *)

fun SDL_LoadBMP (filename: string): SDL_Surface_ref0
  = "#atsctrb_SDL_LoadBMP"

fun SDL_LoadBMP_exn (filename: string): SDL_Surface_ref1

(* ****** ****** *)

fun SDL_SetColorKey {l:anz}
  (surface: !SDL_Surface_ref l, flag: Uint32, key: Uint32): int (*err*)
  = "#atsctrb_SDL_SetColorKey"

fun SDL_SetAlpha {l:anz}
  (surface: !SDL_Surface_ref l, flag: Uint32, alpha: Uint8): int (*err*)
  = "#atsctrb_SDL_SetAlpha"

(* ****** ****** *)

fun SDL_GetClipRect {l:anz}
  (surface: !SDL_Surface_ref l, rect: &SDL_Rect? >> SDL_Rect): void
  = "#atsctrb_SDL_GetClipRect"

fun SDL_SetClipRect {l:anz}
  (surface: !SDL_Surface_ref l, rect: &SDL_Rect): int(*SDL_TRUE/SDL_FALSE*)
  = "#atsctrb_SDL_SetClipRect"

(* ****** ****** *)

fun SDL_UpperBlit {l1,l2:anz} (
    src: !SDL_Surface_ref l1, srcrect: &SDL_Rect
  , dst: !SDL_Surface_ref l2, dstrect: &SDL_Rect
  ) : int (*err*)
  = "#atsctrb_SDL_UpperBlit"

fun SDL_UpperBlit_ptr {l1,l2:anz} (
    src: !SDL_Surface_ref l1, srcrect: ptr, dst: !SDL_Surface_ref l2, dstrect: ptr
  ) : int (*err*)
  = "#atsctrb_SDL_UpperBlit"

(* ****** ****** *)

fun SDL_FillRect {l:anz} (
    dst: !SDL_Surface_ref l, dstrect: &SDL_Rect, color: Uint32
  ) : int (*err*)
  = "#atsctrb_SDL_FillRect"

fun SDL_FillRect_ptr {l:anz} ( // use only if dstrect=NULL
    dst: !SDL_Surface_ref l, dstrect: ptr, color: Uint32
  ) : int (*err*)
  = "#atsctrb_SDL_FillRect"

(* ****** ****** *)

fun SDL_DisplayFormat {l:anz}
  (surface: !SDL_Surface_ref l): SDL_Surface_ref0
  = "#atsctrb_SDL_DisplayFormat"

fun SDL_DisplayFormatAlpha {l:anz}
  (surface: !SDL_Surface_ref l): SDL_Surface_ref0
  = "#atsctrb_SDL_DisplayFormatAlpha"

(* ****** ****** *)

fun SDL_WM_SetCaption (title: Stropt, icon: Stropt): void
  = "#atsctrb_SDL_WM_SetCaption"

fun SDL_WM_GetCaption
  (title: &Stropt? >> Stropt, icon: &Stropt? >> Stropt): void
  = "#atsctrb_SDL_WM_GetCaption"

(* ****** ****** *)

fun SDL_GL_SwapBuffers (): void = "#atsctrb_SDL_GL_SwapBuffers"

(* ****** ****** *)

(* end of [SDL_video.sats] *)
