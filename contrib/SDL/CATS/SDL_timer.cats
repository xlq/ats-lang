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

#ifndef ATSCTRB_SDL_SDL_TIMER_CATS
#define ATSCTRB_SDL_SDL_TIMER_CATS

/* ****** ****** */

#define atsctrb_SDL_GetTicks SDL_GetTicks
#define atsctrb_SDL_Delay SDL_Delay

/* ****** ****** */

static inline
ats_int_type
atsctrb_SDL_SetTimer (
  Uint32 interval, ats_fun_ptr_type callback
) {
  return SDL_SetTimer (interval, (SDL_TimerCallback)callback) ;
} // end of [atsctrb_SDL_SetTimer]

static inline
ats_int_type
atsctrb_SDL_CancelTimer () {
  return SDL_SetTimer ((Uint32)0, (SDL_TimerCallback)NULL) ;
} // end of [atsctrb_SDL_CancelTimer]

/* ****** ****** */

#endif // end of [ATSCTRB_SDL_SDL_TIMER_CATS]

/* end of [SDL_TIMER.cats] */
