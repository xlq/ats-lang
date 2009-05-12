/***********************************************************************/
/*                                                                     */
/*                        Applied Type System                          */
/*                                                                     */
/*                             Hongwei Xi                              */
/*                                                                     */
/***********************************************************************/

/*
** ATS/Anairiats - Unleashing the Power of Types!
**
** Copyright (C) 2002-2009 Hongwei Xi.
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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

/* author: Likai Liu (liulk AT cs DOT bu DOT edu) */
/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef _ATS_GCBDW_H
#define _ATS_GCBDW_H

/* ****** ****** */

ats_ptr_type
ats_malloc_ngc (ats_size_type n) {
  void *p = GC_malloc(n) ; return p ;
} /* end of [ats_malloc_ngc] */

ats_ptr_type
ats_calloc_ngc
  (ats_size_type n, ats_size_type bsz) {
  void *p = GC_malloc(n * bsz) ; return p ;
} /* end of [ats_calloc_ngc] */

/* ****** ****** */

#endif /* _ATS_GCBDW_H */

/* end of [gc.h] */
