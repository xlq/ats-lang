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
** Copyright (C) 2002-2008 Hongwei Xi.
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

// May 2009
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

/* ****** ****** */

#ifndef _ATS_NGC_GC_H
#define _ATS_NGC_GC_H

/* ****** ****** */

// declared in [stdlib.h]
extern void *malloc (size_t bsz) ;
extern void *calloc (size_t n, size_t bsz) ;
extern void free (void *p) ;
extern void *realloc (void* p, size_t bsz) ;

/* ****** ****** */

ats_void_type
ats_gc_init () { return ; }
/* end of [ats_gc_init] */

ats_void_type
ats_gc_markroot (
  const ats_ptr_type p, ats_size_type bsz
) {
  return ;
} /* end of [ats_gc_markroot] */

ats_int_type
ats_gc_chunk_count_limit_get () { return 0 ; }
/* end of [ats_gc_chunk_count_limit_get] */

ats_void_type
ats_gc_chunk_count_limit_set
  (ats_int_type nchunk) { return ; }
/* end of [ats_gc_chunk_count_limit_set] */

ats_int_type
ats_gc_chunk_count_limit_max_get () { return 0 ; }
/* end of [ats_gc_chunk_count_limit_max_get] */

ats_void_type
ats_gc_chunk_count_limit_max_set
  (ats_int_type nchunk) { return ; }
/* end of [ats_gc_chunk_count_limit_max_set] */

/* ****** ****** */

ats_ptr_type
ats_malloc_gc (ats_size_type n) {
  ats_ptr_type *p ;
/*
  fprintf (stderr, "ats_malloc_gc: n = %i\n", n) ;
*/
  p = malloc(n) ;
/*
  fprintf (stderr, "ats_malloc_gc: p = %p(%li)\n", p, p) ;
*/
  if (!p) ats_exit_errmsg(1, "Exit: [ats_malloc_gc] failed.\n") ;
  return p ;
} /* end of [ats_malloc_gc] */

ats_ptr_type
ats_calloc_gc (ats_size_type n, ats_size_type bsz) {
  ats_ptr_type *p ;
/*
  fprintf (stderr, "ats_calloc_gc: n = %i and bsz = %i\n", n, bsz) ;
*/
  p = calloc(n, bsz) ;
/*
  fprintf (stderr, "ats_calloc_gc: p = %p(%li)\n", p, p) ;
*/
  if (!p) ats_exit_errmsg(1, "Exit: [ats_calloc_gc] failed.\n") ;
  return p ;
} /* end of [ats_calloc_gc] */

ats_void_type
ats_free_gc (const ats_ptr_type p) {
/*
  fprintf (stderr, "ats_free_gc: p = %p(%li)\n", p, p) ;
*/
  free(p) ; return ;
} /* end of [ats_free_gc] */

ats_ptr_type
ats_realloc_gc (const ats_ptr_type p, ats_size_type bsz) {
  ats_ptr_type p_new ;
/*
  fprintf (stderr, "ats_realloc_gc: p = %p and bsz = %i\n", p, bsz) ;
*/
  p_new = realloc(p, bsz) ;
/*
  fprintf (stderr, "ats_realloc_gc: p_new = %p(%li)\n", p_new, p_new) ;
*/
  if (!p_new) ats_exit_errmsg(1, "Exit: [ats_realloc_gc] failed.\n") ;
  return p_new ;
}

/* ****** ****** */

ats_ptr_type
ats_malloc_ngc (ats_size_type n) {
  ats_ptr_type *p ;
  /*
  fprintf (stderr, "ats_malloc_ngc: _ATS_NGC: n = %i\n", n) ;
  */
  p = malloc(n) ;
  /*
  fprintf (stderr, "ats_malloc_ngc: _ATS_NGC: p = %p(%li)\n", p, p) ;
  */
  if (!p) ats_exit_errmsg(1, "Exit: [ats_malloc_ngc] failed.\n") ;
  return p ;
} /* end of [ats_malloc_ngc] */

ats_ptr_type
ats_calloc_ngc (ats_size_type n, ats_size_type bsz)
{
  ats_ptr_type *p ;
  p = calloc(n, bsz) ;
  if (!p) ats_exit_errmsg (1, "Exit: [ats_calloc_ngc] failed.\n") ;
  return p ;
} /* end of [ats_calloc_ngc] */

ats_void_type
ats_free_ngc (const ats_ptr_type p) {
  /*
  fprintf (stderr, "ats_free_ngc: _ATS_NGC: p = %p\n", p) ;
  */
  free(p) ; return ;
} /* end of [ats_free_ngc] */

ats_ptr_type
ats_realloc_ngc (const ats_ptr_type p, ats_size_type bsz) {
  ats_ptr_type *p_new ;
  /*
  fprintf (stderr, "ats_realloc_ngc: _ATS_NGC: p = %p\n", p) ;
  fprintf (stderr, "ats_realloc_ngc: _ATS_NGC: bsz = %i\n", bsz) ;
  */
  p_new = realloc(p, bsz) ;
  /*
  fprintf (stderr, "ats_realloc_ngc: _ATS_NGC: p_new = %p\n", p_new) ;
  */
  if (!p_new) ats_exit_errmsg(1, "Exit: [ats_realloc_ngc] failed.\n") ;
  return p_new ;
} /* end of [ats_realloc_ngc] */

/* ****** ****** */

#endif /* _ATS_NGC_GC_H */

/* end of [gc.h] */
