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

extern
ats_void_type gc_init () ;
extern
ats_void_type gc_markroot_bsz (ats_ptr_type ptr, size_t bsz) ;

//

extern
ats_ptr_type gcats0_malloc_err (ats_int_type nbyte) ;
extern
ats_ptr_type gcats0_malloc (ats_int_type nbyte) ;
extern
ats_ptr_type gcats0_calloc (ats_int_type nmemb, ats_int_type size) ;
extern
ats_void_type gcats0_free (ats_ptr_type ptr) ;
extern
ats_ptr_type gcats0_realloc (ats_ptr_type ptr, ats_int_type nbyte) ;

//

extern
ats_ptr_type gcats1_malloc (ats_int_type nbyte) ;
extern
ats_ptr_type gcats1_calloc (ats_int_type nmemb, ats_int_type size) ;
extern
ats_void_type gcats1_free (ats_ptr_type ptr) ;
extern
ats_ptr_type gcats1_realloc (ats_ptr_type ptr, ats_int_type nbyte) ;

/* ****** ****** */

/* end of [gc.h] */
