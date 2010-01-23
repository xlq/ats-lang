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

#ifndef ATSCTRB_XLIB_XLIB_CATS
#define ATSCTRB_XLIB_XLIB_CATS

/* ****** ****** */

#include "X11/Xlib.h"

/* ****** ****** */

#define atsctrb_XOpenDisplay XOpenDisplay

/* ****** ****** */

#define atsctrb_XAllPlanes XAllPlanes
#define atsctrb_XBlackPixel XBlackPixel
#define atsctrb_XWhitePixel XWhitePixel
#define atsctrb_XConnectionNumber XConnectionNumber
#define atsctrb_XDefaultColormap XDefaultColormap
#define atsctrb_XDefaultDepth XDefaultDepth

#define atsctrb_XListDepths XListDepths // this is a function

#define atsctrb_XDefaultGC XDefaultGC
#define atsctrb_XDefaultRootWindow XDefaultRootWindow

#define atsctrb_XDefaultScreen XDefaultScreen

#define atsctrb_XDisplayCells XDisplayCells
#define atsctrb_XDisplayPlanes XDisplayPlanes
#define atsctrb_XDisplayString XDisplayString

#define atsctrb_XLastKnownRequestProcessed XLastKnownRequestProcessed
#define atsctrb_XNextRequest XNextRequest

#define atsctrb_XQLength XQLength

#define atsctrb_XRootWindow XRootWindow
#define atsctrb_XScreenCount XScreenCount

/* ****** ****** */

#define atsctrb_XListPixmapFormats XListPixmapFormats
#define atsctrb_XImageByteOrder XImageByteOrder
#define atsctrb_XBitmapUnit XBitmapUnit
#define atsctrb_XBitmapOrder XBitmapOrder
#define atsctrb_XBitmapPad XBitmapPad

#define atsctrb_XDisplayHeight DisplayHeight
#define atsctrb_XDisplayHeightMM DisplayHeightMM
#define atsctrb_XDisplayWidth DisplayWidth
#define atsctrb_XDisplayWidthMM DisplayWidthMM

/* ****** ****** */

#define atsctrb_XNoOp XNoOp

/* ****** ****** */

#define atsctrb_XFree XFree

/* ****** ****** */

#define atsctrb_XCloseDisplay XCloseDisplay

/* ****** ****** */

#endif // end of [ATSCTRB_XLIB_XLIB_CATS]

/* end of [Xlib.cats] */
