/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi.
**
** ATS is  free software;  you can redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*/

/* ****** ****** */

/*
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) 
**
*/

/* ****** ****** */

#ifndef ATS_LIBATS_LINQUEUE_ARR_CATS
#define ATS_LIBATS_LINQUEUE_ARR_CATS

/* ****** ****** */

typedef struct {
  ats_size_type cap ;
  ats_size_type nitm ;
  ats_ptr_type qarr_beg ;
  ats_ptr_type qarr_end ;
  ats_ptr_type qarr_fst ;
  ats_ptr_type qarr_lst ;
} ats_libats_linqueue_arr_QUEUE_vt ;

/* ****** ****** */

#endif /* ATS_LIBATS_LINQUEUE_ARR_CATS */

/* end of [linqueue_arr.cats] */ 
