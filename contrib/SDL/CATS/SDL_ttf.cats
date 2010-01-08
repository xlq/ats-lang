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

#ifndef ATSCTRB_SDL_SDL_TTF_CATS
#define ATSCTRB_SDL_SDL_TTF_CATS

/* ****** ****** */

#include "SDL/SDL.h"
#include "SDL/SDL_ttf.h"

/* ****** ****** */

#define atsctrb_TTF_Init TTF_Init 

/* ****** ****** */

static inline
ats_ref_type
atsctrb_TTF_OpenFont (
  ats_ptr_type filename, ats_int_type ptsize
) {
  return TTF_OpenFont((char*)filename, ptsize) ;
} // end of [atsctrb_TTF_OpenFont]

/* ****** ****** */

static inline
ats_ref_type
atsctrb_TTF_RenderText_Solid (
  ats_ref_type font, ats_ptr_type txt, ats_ref_type fg
) {
  return TTF_RenderText_Solid((TTF_Font*)font, (char*)txt, *(SDL_Color*)fg) ;
} // end of [atsctrb_TTF_RenderText_Solid]

/* ****** ****** */

static inline
ats_void_type
atsctrb_TTF_CloseFont
  (ats_ref_type font) {
  TTF_CloseFont ((TTF_Font*)font) ; return ;
} // end of [atsctrb_TTF_CloseFont]

/* ****** ****** */

#define atsctrb_TTF_Quit TTF_Quit 
#define atsctrb_TTF_WasInit TTF_WasInit

/* ****** ****** */

#endif // end of [ATSCTRB_SDL_SDL_TTF_CATS]

/* end of [SDL_ttf.cats] */
