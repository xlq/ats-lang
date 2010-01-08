/***********************************************************************/
/*                                                                     */
/*                         Applied Type System                         */
/*                                                                     */
/*                              Hongwei Xi                             */
/*                                                                     */
/***********************************************************************/

/*
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
*/

/* ****** ****** */

// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: January, 2010

/* ****** ****** */

#ifndef ATSCTRB_SDL_SDL_VIDEO_CATS
#define ATSCTRB_SDL_SDL_VIDEO_CATS

/* ****** ****** */

static inline
ats_ref_type // SDL_Surface_ref0
atsctrb_SDL_SetVideoMode (
  ats_int_type width, ats_int_type height, ats_int_type bpp, Uint32 flags
) {
  return SDL_SetVideoMode(width, height, bpp, flags) ;
} // end of [atsctrb_SDL_SetVideoMode]

/* ****** ****** */

static inline
ats_int_type // err
atsctrb_SDL_Flip (
  ats_ref_type screen
) {
  return SDL_Flip((SDL_Surface*)screen) ;
} // end of [atsctrb_SDL_Flip]

/* ****** ****** */

static inline
Uint32
atsctrb_SDL_MapRGB (
  ats_ref_type format, Uint8 r, Uint8 g, Uint8 b
) {
  return SDL_MapRGB ((SDL_PixelFormat*)format, r, g, b) ;
} // end of [atsctrb_SDL_MapRGB]

static inline
Uint32
atsctrb_SDL_MapRGBA (
  ats_ref_type format, Uint8 r, Uint8 g, Uint8 b, Uint8 a
) {
  return SDL_MapRGBA ((SDL_PixelFormat*)format, r, g, b, a) ;
} // end of [atsctrb_SDL_MapRGBA]

/* ****** ****** */

static inline
ats_ref_type // SDL_Surface_ref0
atsctrb_SDL_CreateRGBSurface (
  Uint32 flags
, ats_int_type wd, ats_int_type ht, ats_int_type dp
, Uint32 Rmask, Uint32 Gmask, Uint32 Bmask, Uint32 Amask
) {
  return SDL_CreateRGBSurface(flags, wd, ht, dp, Rmask, Gmask, Bmask, Amask) ;
} // end of [atsctrb_SDL_CreateRGBSurface]

static inline
ats_void_type
atsctrb_SDL_FreeSurface
  (ats_ref_type surface) {
  SDL_FreeSurface((SDL_Surface*)surface) ; return ;
} // end of [atsctrb_SDL_FreeSurface]

/* ****** ****** */

static inline
ats_ref_type
atsctrb_SDL_LoadBMP (
  ats_ptr_type filename
) {
  return SDL_LoadBMP(filename) ;
} // end of [atsctrb_SDL_LoadBMP]

/* ****** ****** */

static inline
ats_int_type // err
atsctrb_SDL_SetColorKey (
  ats_ref_type surface, Uint32 flag, Uint32 key
) {
  return SDL_SetColorKey((SDL_Surface*)surface, flag, key) ;
} // end of [atsctrb_SDL_SetColorKey]

static inline
ats_int_type // err
atsctrb_SDL_SetAlpha (
  ats_ref_type surface, Uint32 flag, Uint8 alpha
) {
  return SDL_SetAlpha((SDL_Surface*)surface, flag, alpha) ;
} // end of [atsctrb_SDL_SetAlpha]

/* ****** ****** */

static inline
ats_void_type
atsctrb_SDL_GetClipRect (
  ats_ref_type surface, ats_ref_type rect
) {
  SDL_GetClipRect((SDL_Surface*)surface, (SDL_Rect*)rect) ;
  return ;
} // end of [atsctrb_SDL_GetClipRect]

/* ****** ****** */

static inline
ats_int_type // err
atsctrb_SDL_UpperBlit (
  ats_ref_type src, ats_ref_type srcrect
, ats_ref_type dst, ats_ref_type dstrect
) {
  return SDL_UpperBlit (
    (SDL_Surface*)src, (SDL_Rect*)srcrect, (SDL_Surface*)dst, (SDL_Rect*)dstrect
  ) ; // end of [return]
} // end of [atsctrb_SDL_UpperBlit]

/* ****** ****** */

static inline
ats_int_type // err
atsctrb_SDL_FillRect (
  ats_ref_type dst, ats_ref_type dstrect, Uint32 color
) {
  return SDL_FillRect((SDL_Surface*)dst, (SDL_Rect*)dstrect, color) ;
} // end of [atsctrb_SDL_FillRect]

/* ****** ****** */

static inline
ats_ref_type // SDL_Surface_ref0
atsctrb_SDL_DisplayFormat (
  ats_ref_type surface
) {
  return SDL_DisplayFormat((SDL_Surface*)surface) ;
} // end of [atsctrb_SDL_DisplayFormat]

static inline
ats_ref_type // SDL_Surface_ref0
atsctrb_SDL_DisplayFormatAlpha (
  ats_ref_type surface
) {
  return SDL_DisplayFormatAlpha((SDL_Surface*)surface) ;
} // end of [atsctrb_SDL_DisplayFormatAlpha]

/* ****** ****** */

static inline
ats_void_type
atsctrb_SDL_WM_GetCaption (
  ats_ptr_type title, ats_ptr_type icon
) {
  SDL_WM_GetCaption((char**)title, (char**)icon) ; return ;
} // end of [atsctrb_SDL_WM_GetCaption]

static inline
ats_void_type
atsctrb_SDL_WM_SetCaption (
  ats_ptr_type title, ats_ptr_type icon
) {
  SDL_WM_SetCaption((char*)title, (char*)icon) ; return ;
} // end of [atsctrb_SDL_WM_SetCaption]

/* ****** ****** */

#endif // end of [ATSCTRB_SDL_SDL_VIDEO_CATS]

/* end of [SDL_video.cats] */
