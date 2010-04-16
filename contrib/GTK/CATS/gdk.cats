/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Power of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi.
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
// Starting time: April, 2010

/* ****** ****** */

#ifndef ATSCTRB_GDK_CATS
#define ATSCTRB_GDK_CATS

/* ****** ****** */

#include "gdk/gdk.h"

/* ****** ****** */

ATSinline()
GdkEventMask
atsctrb_lor_GdkEventMask_GdkEventMask
  (GdkEventMask x1, GdkEventMask x2) { return (x1 | x2) ; }
// end of [atsctrb_lor_GdkEventMask_GdkEventMask]

/* ****** ****** */

#endif // end of [ATSCTRB_GDK_CATS]
