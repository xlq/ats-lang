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

#ifndef ATSCTRB_SDL_SDL_EVENTS_CATS
#define ATSCTRB_SDL_SDL_EVENTS_CATS

/* ****** ****** */

static inline
ats_bool_type
atsctrb_eq_SDL_EventType_SDL_EventType
  (SDL_EventType x1, SDL_EventType x2) {
  return (x1 == x2 ? ats_true_bool : ats_false_bool) ;
} // end of [atsctrb_eq_SDL_EventType_SDL_EventType]

/* ****** ****** */

static inline
SDL_EventType
atsctrb_SDL_Event_type
  (ats_ref_type event) {
  return ((SDL_Event*)event)->type ;
} // end of [atsctrb_SDL_Event_type]

/* ****** ****** */

static inline
ats_int_type
atsctrb_SDL_PollEvent
  (ats_ref_type event) {
  return SDL_PollEvent((SDL_Event*)event) ;
} // end of [atsctrb_SDL_PollEvent]

static inline
ats_int_type
atsctrb_SDL_PollEvent_null () {
  return SDL_PollEvent((SDL_Event*)0) ;
} // end of [atsctrb_SDL_PollEvent_null]

/* ****** ****** */

#endif // end of [ATSCTRB_SDL_SDL_EVENTS_CATS]

/* end of [SDL_events.cats] */
