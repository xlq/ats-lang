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
// Starting time: May, 2010

/* ****** ****** */

#ifndef ATSCTRB_PANGO_PANGO_CATS
#define ATSCTRB_PANGO_PANGO_CATS

/* ****** ****** */

#include <pango/pango.h>

/* ****** ****** */

//
// pango-font.h
//

#define atsctrb_pango_font_description_from_string \
  pango_font_description_from_string
#define atsctrb_pango_font_description_to_string \
  pango_font_description_to_string
#define atsctrb_pango_font_description_to_filename \
  pango_font_description_to_filename

#define atsctrb_pango_font_description_free pango_font_description_free

/* ****** ****** */

#endif // end of [ATSCTRB_PANGO_PANGO_CATS]

/* end of [pango.cats] */
