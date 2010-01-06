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
ats_ref_type // SDL_Surface_refopt
atsctrb_SDL_SetVideoMode (
  ats_int_type width, ats_int_type height, ats_int_type bpp, Uint32 flags
) {
  return SDL_SetVideoMode(width, height, bpp, flags) ;
} // end of [atsctrb_SDL_SetVideoMode]

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
atsctrb_SDL_Flip (
  ats_ref_type screen
) {
  return SDL_Flip((SDL_Surface*)screen) ;
} // end of [atsctrb_SDL_Flip]

/* ****** ****** */

#endif // end of [ATSCTRB_SDL_SDL_VIDEO_CATS]

/* end of [SDL_VIDEO.cats] */
