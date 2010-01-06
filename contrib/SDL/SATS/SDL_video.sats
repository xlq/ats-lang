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

typedef SDL_Rect = @{
  x= Sint16, y= Sint16, w= Uint16, v= Uint16
} // end of [SDL_Rect]

typedef SDL_Color = @{
  r= Uint8, g= Uint8, b= Uint8, unused= Uint8
} // end of [SDL_Color]

(* ****** ****** *)

absviewtype SDL_Surface_ref // SDL_Surface*
absviewtype SDL_Surface_refopt (int) // NULL or SDL_Surface*
viewtypedef SDL_Surface_refopt = [i:two] SDL_Surface_refopt i

symintr SDL_Surface_ref
castfn SDL_Surface_nul_of_refopt0 (x: SDL_Surface_refopt 0): ptr(*null*)
overload NULL with SDL_Surface_nul_of_refopt0

castfn SDL_Surface_ref_of_refopt1 (x: SDL_Surface_refopt 1): SDL_Surface_ref
overload SDL_Surface_ref with SDL_Surface_ref_of_refopt1

fun SDL_Surface_refopt_test {i:int} (x: !SDL_Surface_refopt i):<> bool (i > 0)
  = "atsctrb_SDL_refopt_test"
overload refopt_test with SDL_Surface_refopt_test

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

fun SDL_SetVideoMode
  (width: int, height: int, bpp: int, flags: Uint32): SDL_Surface_refopt
  = "atsctrb_SDL_SetVideoMode"

fun SDL_SetVideoMode_exn
  (width: int, height: int, bpp: int, flags: Uint32): SDL_Surface_ref

(* ****** ****** *)

//
// note: x=y=w=h=0 means the whole screen!
//
fun SDL_UpdateRect (
    screen: !SDL_Surface_ref, x: Sint32, y: Sint32, w: Uint32, h: Uint32
  ) : void
  = "atsctrb_SDL_UpdateRect"
  
fun SDL_UpdateRects {n:nat}
  (screen: !SDL_Surface_ref, n: int n, rects: &(@[SDL_Rect][n])): void
  = "atsctrb_SDL_UpdateRects"
  
(* ****** ****** *)

fun SDL_Flip(screen: !SDL_Surface_ref): int (*err*)
  = "atsctrb_SDL_Flip"

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

fun SDL_CreateRGBSurface (
    flags: Uint32
  , width: int, height: int, depth: int
  , Rmask: Uint32, Gmask: Uint32, Bmask: Uint32, Amask: Uint32
  ) : SDL_Surface_ref
  = "atsctrb_SDL_CreateRGBSurface"

fun SDL_FreeSurface (surface: SDL_Surface_ref): void = "atsctrb_SDL_FreeSurface"

(* ****** ****** *)

absview SDL_Surface_v

fun SDL_LockSurface (surface: !SDL_Surface_ref)
  : [i:int | i <= 0] (option_v (SDL_Surface_v, i==0) | int i)
  = "atsctrb_SDL_LockSurface"

fun SDL_LockSurface_exn
  (surface: !SDL_Surface_ref): (SDL_Surface_v | void)
  = "atsctrb_SDL_LockSurface_exn"

fun SDL_UnlockSurface
  (pf: SDL_Surface_v | surface: !SDL_Surface_ref): int
 = "atsctrb_SDL_UnlockSurface"

(* ****** ****** *)

fun SDL_LoadBMP (filename: string): SDL_Surface_refopt
  = "atsctrb_SDL_LoadBMP"

fun SDL_LoadBMP_exn (filename: string): SDL_Surface_ref
  = "atsctrb_SDL_LoadBMP_exn"

(* ****** ****** *)

fun SDL_SetColorKey
  (surface: !SDL_Surface_ref, flag: Uint32, key: Uint32): int (*err*)
  = "atsctrb_SDL_SetColorKey"

(* ****** ****** *)

fun SDL_SetAlpha
  (surface: !SDL_Surface_ref, flag: Uint32, alpha: Uint8): int (*err*)
  = "atsctrb_SDL_SetAlpha"

(* ****** ****** *)

fun SDL_GetClipRect
  (surface: !SDL_Surface_ref, rect: &SDL_Rect? >> SDL_Rect): void
  = "atsctrb_SDL_GetClipRect"

(* ****** ****** *)

fun SDL_UpperBlit (
    src: !SDL_Surface_ref, srcrect: &SDL_Rect
  , dst: !SDL_Surface_ref, dstrect: &SDL_Rect
  ) : int (*err*)
  = "atsctrb_SDL_UpperBlit"

fun SDL_UpperBlit_ptr (
    src: !SDL_Surface_ref, srcrect: ptr
  , dst: !SDL_Surface_ref, dstrect: ptr
  ) : int (*err*)
  = "atsctrb_SDL_UpperBlit"

(* ****** ****** *)

fun SDL_FillRect (
    dst: !SDL_Surface_ref, dstrect: &SDL_Rect, color: Uint32
  ) : int (*err*)
  = "atsctrb_SDL_FillRect"

fun SDL_FillRect_ptr ( // use only if dstrect=NULL
    dst: !SDL_Surface_ref, dstrect: ptr, color: Uint32
  ) : int (*err*)
  = "atsctrb_SDL_FillRect"

(* ****** ****** *)

fun SDL_GL_SwapBuffers (): void = "atsctrb_SDL_GL_SwapBuffers"

(* ****** ****** *)

(* end of [SDL_video.sats] *)
