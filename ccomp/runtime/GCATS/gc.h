/***********************************************************************/
/*                                                                     */
/*                        Applied Type System                          */
/*                                                                     */
/*                             Hongwei Xi                              */
/*                                                                     */
/***********************************************************************/

/*
 * ATS/Anairiats - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi.
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
 * Free Software Foundation; either version 3, or (at  your  option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 */

/* ****** ****** */

// June 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

/* ****** ****** */

#ifndef _ATS_GC_H
#define _ATS_GC_H

/* ****** ****** */

//

extern
ats_int_type gc_chunk_count_limit_get () ;

extern
ats_void_type gc_chunk_count_limit_set (ats_int_type n) ;

extern
ats_int_type gc_chunk_count_limit_max_get () ;

extern
ats_void_type gc_chunk_count_limit_max_set (ats_int_type n) ;

//

extern
ats_void_type gc_markroot_bsz (ats_ptr_type ptr, ats_int_type bsz) ;

/* ****** ****** */

extern
ats_ptr_type gc_aut_malloc_bsz (ats_int_type bsz) ;

extern
ats_ptr_type gc_aut_calloc_bsz (ats_int_type n, ats_int_type bsz) ;

extern ats_void_type gc_aut_free (ats_ptr_type ptr) ;

extern
ats_ptr_type gc_aut_realloc_bsz (ats_ptr_type ptr, ats_int_type bsz) ;

/* ****** ****** */

extern
ats_ptr_type gc_man_malloc_bsz (ats_int_type bsz) ;

extern
ats_ptr_type gc_man_calloc_bsz (ats_int_type n, ats_int_type bsz) ;

extern ats_void_type gc_man_free (ats_ptr_type ptr) ;

extern
ats_ptr_type gc_man_realloc_bsz (ats_ptr_type ptr, ats_int_type bsz) ;

/* ****** ****** */

#endif /* _ATS_GC_H */

/* end of [gc.h] */
