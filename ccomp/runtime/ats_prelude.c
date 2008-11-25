/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi.
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
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

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#include <stdarg.h>
#include <stdlib.h>
#include <stdio.h>

#ifdef _ATS_MULTITHREAD
#include <pthread.h>
#endif

/* ****** ****** */

#include "ats_exception.h"
#include "ats_memory.h"
#include "ats_types.h"

/* ****** ****** */

extern ats_exit_errmsg (int err, char *msg) ;

/* ****** ****** */

// The following variables are used in basics.dats
int ats_stdin_view_lock = 1 ;
int ats_stdout_view_lock = 1 ;
int ats_stderr_view_lock = 1 ;

/* ****** ****** */

// some common exceptions

ats_exn_type AssertionExceptionCon = { 10, "AssertionException" } ;
ats_exn_ptr_type AssertionException = &AssertionExceptionCon ;

ats_exn_type DivisionByZeroExceptionCon = { 20, "DivisionByZeroException" } ;
ats_exn_ptr_type DivisionByZeroException = &DivisionByZeroExceptionCon ;

ats_exn_type NotFoundExceptionCon = { 30, "NotFoundException" } ;
ats_exn_ptr_type NotFoundException = &NotFoundExceptionCon ;

ats_exn_type OverflowExceptionCon = { 40, "OverflowException" } ;
ats_exn_ptr_type OverflowException = &OverflowExceptionCon ;

ats_exn_type SubscriptExceptionCon = { 50, "SubscriptException" } ;
ats_exn_ptr_type SubscriptException = &SubscriptExceptionCon ;

/* ****** ****** */

/* tags for exception constructors */

// numbers less than 1000 are reserved
int ats_exception_con_tag = 1000 ;

#ifdef _ATS_MULTITHREAD
__thread
ats_exception_frame_type *the_ats_exception_stack = NULL ;
#else /* single thread */
ats_exception_frame_type *the_ats_exception_stack = NULL ;
#endif

/* function for handling uncaught exceptions */

ats_void_type
ats_handle_exception (const ats_exn_ptr_type exn) {
  fprintf (
    stderr, "Uncaught exception: %s(%d)\n", exn->name, exn->tag
  ) ;
  exit(1);
}

/* functions for handling match failures */

ats_void_type
ats_caseof_failure (void) {
  ats_exit_errmsg(1, "Exit: match failure.\n") ;
  return ;
}

ats_void_type
ats_funarg_match_failure (void) {
  ats_exit_errmsg(1, "Exit: funarg match failure.\n") ;
  return ;
}

/* ****** ****** */

/* function for memory allocation and deallocation */

#ifdef _ATS_GC // generic GC for ATS
#include "gc/gc.h"
#elif _ATS_GCATS // special GC for ATS
#include "GCATS/gc.h"
#elif _ATS_GCATS0 // special GC for ATS
#include "GCATS0/gc.h"
#elif _ATS_gc // special GC for ATS by Rick Lavoie
#include "gc/gc.h"
#else // no GC for ATS
#include <stdlib.h>
#endif

/* ****** ****** */

ats_ptr_type
ats_malloc_ngc (const ats_int_type n) {
  void *p ;
#ifdef _ATS_GC
  p = GC_malloc(n) ;
#elif _ATS_GCATS
  /*
  fprintf (stderr, "ats_malloc_ngc: _ATS_GCATS: n = %i\n", n) ;
  */
  p = gc_man_malloc_bsz(n) ;
  /*
  fprintf (stderr, "ats_malloc_ngc: _ATS_GCATS: p = %p(%li)\n", p, p) ;
  */
#elif _ATS_GCATS0
  /*
  fprintf (stderr, "ats_malloc_ngc: _ATS_GCATS0: n = %i\n", n) ;
  */
  p = gcats0_malloc(n) ;
  /*
  fprintf (stderr, "ats_malloc_ngc: _ATS_GCATS0: p = %p(%i)\n", p, p) ;
  */
#elif _ATS_gc
  /*
  fprintf (stderr, "ats_malloc_ngc: _ATS_gc: n = %i\n", n) ;
  */
  p = gc_allocate_persistant_byte(n) ;
  /*
  fprintf (stderr, "ats_malloc_ngc: _ATS_gc: p = %p(%li)\n", p, p) ;
  */
#else
  p = malloc(n) ;
#endif
  if (!p) ats_exit_errmsg(1, "Exit: [ats_malloc_ngc] failed.\n") ;
  return p ;
}

ats_ptr_type
ats_calloc_ngc (const ats_int_type n, const ats_int_type sz)
{
  void *p ;
#ifdef _ATS_GC
  p = GC_malloc(n * sz) ;
#elif _ATS_GCATS
  p = gc_man_calloc_bsz(n, sz) ;
#elif _ATS_GCATS0
  /*
  fprintf (stderr, "ats_calloc: _ATS_GCATS0: n = %i and sz = %i\n", n, sz) ;
  */
  p = gcats0_calloc(n, sz) ;
#elif _ATS_gc
  /*
  fprintf (stderr, "ats_calloc: _ATS_gc: n = %i and sz = %i\n", n, sz) ;
  */
  p = gc_allocate_persistant_byte(n * sz) ;
#else
  p = calloc(n, sz) ;
#endif
  if (!p) ats_exit_errmsg(1, "Exit: [ats_calloc_ngc] failed.\n") ;
  return p ;
}

ats_void_type
ats_free_ngc (const ats_ptr_type p) {
#ifdef _ATS_GC
  GC_free(p) ; return ;
#elif _ATS_GCATS
  /*
  fprintf (stderr, "ats_free_ngc: _ATS_GCATS: p = %p\n", p) ;
  */
  gc_man_free(p) ;
#elif _ATS_GCATS0
  /*
  fprintf (stderr, "ats_free_ngc: _ATS_GCATS0: p = %p\n", p) ;
  */
  gcats0_free(p) ;
#elif _ATS_gc
  /*
  fprintf (stderr, "ats_free_ngc: _ATS_gc: p = %p\n", p) ;
  */
  gc_free_persistant(p) ; return ;
#else
  free(p) ; return ;
#endif

}

/* ****** ****** */

ats_ptr_type
ats_realloc_ngc (const ats_ptr_type p, const ats_int_type bsz) {
  void *p_new ;
#ifdef _ATS_GC
  p_new = GC_realloc(p, bsz) ;
#elif _ATS_GCATS
  /*
  fprintf (stderr, "ats_realloc_ngc: _ATS_GCATS: p = %p\n", p) ;
  fprintf (stderr, "ats_realloc_ngc: _ATS_GCATS: bsz = %i\n", bsz) ;
  */
  p_new = gc_man_realloc_bsz(p, bsz) ;
  /*
  fprintf (stderr, "ats_realloc_ngc: _ATS_GCATS: p_new = %p\n", p_new) ;
  */
#elif _ATS_GCATS0
  p_new = gcats0_realloc(p, bsz) ;
#elif _ATS_gc
  p_new = gc_reallocate_persistant_byte(p, bsz) ;
#else
  p_new = realloc(p, bsz) ;
#endif
  if (!p_new) ats_exit_errmsg(1, "Exit: [ats_realloc_ngc] failed.\n") ;
  return p_new ;
}

/* memory allocation/deallocation with GC support */

ats_void_type
ats_gc_init () {

#ifdef _ATS_GC
  GC_init () ;
#elif _ATS_GCATS
  gc_init () ;
#elif _ATS_GCATS0
  gc_init () ;
#elif _ATS_gc
  gc_init () ;
#endif

 return ;
} /* end of [ats_gc_init] */

ats_void_type
ats_gc_markroot (const ats_ptr_type p, const ats_int_type bsz) {
/*
  fprintf (stderr, "ats_gc_markroot: p = %p and bsz = %i\n", p, bsz) ;
*/
#ifdef _ATS_GC
  /* do nothing */
#elif _ATS_GCATS
  gc_markroot_bsz (p, bsz) ;
#elif _ATS_GCATS0
  gcats_markroot_bsz (p, bsz) ;
#elif _ATS_gc
  gc_markroot_bsz (p, bsz) ;
#else
  /* do nothing */
#endif
  return ;
} /* end of [ats_gc_markroot] */

/* ****** ****** */

ats_int_type
ats_gc_chunk_count_limit_get () {
#ifdef _ATS_GC
  return 0 ;
#elif _ATS_GCATS
  return gc_chunk_count_limit_get () ;
#else
  return 0 ;
#endif
} /* end of [ats_gc_chunk_count_limit_get] */

ats_void_type
ats_gc_chunk_count_limit_set (ats_int_type nchunk) {
#ifdef _ATS_GC
  return ;
#elif _ATS_GCATS
  gc_chunk_count_limit_set (nchunk) ; return ;
#else
  return ;
#endif
} /* end of [ats_gc_chunk_count_limit_set] */

/* ****** ****** */

ats_int_type
ats_gc_chunk_count_limit_max_get () {
#ifdef _ATS_GC
  return 0 ;
#elif _ATS_GCATS
  return gc_chunk_count_limit_max_get () ;
#else
  return 0 ;
#endif
} /* end of [ats_gc_chunk_count_limit_max_get] */

ats_void_type
ats_gc_chunk_count_limit_max_set (ats_int_type nchunk) {
#ifdef _ATS_GC
  return ;
#elif _ATS_GCATS
  gc_chunk_count_limit_max_set (nchunk) ; return ;
#else
  return ;
#endif
} /* end of [ats_gc_chunk_count_limit_max_set] */

/* ****** ****** */

ats_ptr_type
ats_malloc_gc (const ats_int_type n) {
  void *p ;
/*
  fprintf (stderr, "ats_malloc_gc: n = %i\n", n) ;
*/
#ifdef _ATS_GC
  p = GC_malloc(n) ;
#elif _ATS_GCATS
  p = gc_aut_malloc_bsz(n) ;
#elif _ATS_GCATS0
  p = gcats1_malloc(n) ;
#elif _ATS_gc
  p = gc_alloc_byte(n) ;
#else
  p = malloc(n) ;
#endif
/*
  fprintf (stderr, "ats_malloc_gc: p = %p(%li)\n", p, p) ;
*/
  if (!p) ats_exit_errmsg(1, "Exit: [ats_malloc_gc] failed.\n") ;
  return p ;
} /* end of [ats_malloc_gc] */

/* ****** ****** */

ats_ptr_type
ats_calloc_gc (const ats_int_type n, const ats_int_type sz) {
  void *p ;
/*
  fprintf (stderr, "ats_calloc_gc: n = %i and sz = %i\n", n, sz) ;
*/
#ifdef _ATS_GC
  p = GC_malloc(n*sz) ;
#elif _ATS_GCATS
  p = gc_aut_calloc_bsz(n, sz) ;
#elif _ATS_GCATS0
  p = gcats1_calloc(n, sz) ;
#elif _ATS_gc
  p = gc_alloc_byte_zero(n*sz) ;
#else
  p = calloc(n, sz) ;
#endif
/*
  fprintf (stderr, "ats_calloc_gc: p = %p(%li)\n", p, p) ;
*/
  if (!p) ats_exit_errmsg(1, "Exit: [ats_calloc_gc] failed.\n") ;
  return p ;
} /* end of [ats_calloc_gc] */

/* ****** ****** */

ats_void_type
ats_free_gc (const ats_ptr_type p) {
/*
  fprintf (stderr, "ats_free_gc: p = %p(%li)\n", p, p) ;
*/
#ifdef _ATS_GC
  GC_free(p) ;
#elif _ATS_GCATS
  gc_aut_free(p) ;
#elif _ATS_GCATS0
  gcats1_free(p) ;
#elif _ATS_gc
  gc_free(p) ;
#else
  free(p) ;
#endif
  return ;
}

/* ****** ****** */

ats_ptr_type
ats_realloc_gc (const ats_ptr_type p, const ats_int_type bsz) {
  ats_ptr_type p_new ;
/*
  fprintf (stderr, "ats_realloc_gc: p = %p and bsz = %i\n", p, bsz) ;
*/
#ifdef _ATS_GC
  p_new = GC_realloc(p, bsz) ;
#elif _ATS_GCATS
  p_new = gc_aut_realloc_bsz(p, bsz) ;
#elif _ATS_GCATS0
  fprintf (
    stderr, "There is no support for [ats_realloc_gc] under this GC (gcats).\n"
  ) ;
  exit (1) ;
#elif _ATS_gc
  fprintf (
    stderr, "There is no support for [ats_realloc_gc] under this GC (gc).\n"
  ) ;
  exit (1) ;
#else
  p_new = realloc(p, bsz) ;
#endif
/*
  fprintf (stderr, "ats_realloc_gc: p_new = %p(%li)\n", p_new, p_new) ;
*/
  if (!p_new) ats_exit_errmsg(1, "Exit: [ats_realloc_gc] failed.\n") ;
  return p_new ;
}

/* ****** ****** */

#ifdef _ATS_MULTITHREAD

static
ats_ptr_type ats_pthread_app (ats_ptr_type f) {
  ((void (*)(ats_ptr_type))((ats_clo_ptr_type)f)->closure_fun)(f) ;
  ATS_FREE (f) ; // this is a linear application
  return (ats_ptr_type)0 ;
}

#ifdef _ATS_GCATS
extern int gc_pthread_create_cloptr (
  ats_clo_ptr_type cloptr, pthread_t *pid_r, int detached, int linclo
) ;
#endif

#ifdef _ATS_gc
extern int gc_pthread_create_cloptr (
  ats_clo_ptr_type cloptr, pthread_t *pid_r, int detached, int linclo
) ;
#endif

ats_void_type
ats_pthread_create_detached_cloptr (ats_ptr_type thunk) {
#ifdef _ATS_GC
  fprintf (
    stderr, "There is no support for pthreads under this GC (GC).\n"
  ) ;
  exit (1) ;
#elif _ATS_GCATS
  int ret ;
  /*
  fprintf (
    stderr, "[ats_pthread_create_detached_cloptr] is called.\n"
  ) ;
  */
  ret = gc_pthread_create_cloptr
    (thunk, NULL/*pid_r*/, 1/*detached*/, 1/*lin*/) ;
#elif _ATS_GCATS0
  fprintf (
    stderr, "There is no support for pthreads under this GC (GCATS0).\n"
  ) ;
  exit (1) ;
#elif _ATS_gc
  int ret ;
  ret = gc_create_pthread_cloptr
    (thunk, NULL/*arg*/, NULL/*pid_r*/, 1/*detached*/) ;
#else
  pthread_t pid ; int ret ;
  ret = pthread_create (&pid, NULL, ats_pthread_app, thunk) ;
#endif
  if (ret != 0) {
    perror ("ats_pthread_create_detached_clo: ") ; exit(1) ;
  }
  return ;
} /* end of [ats_pthread_create_detach] */

/* ****** ****** */

static inline
ats_void_type ats_pthread_exit () {
#ifdef _ATS_GC
  fprintf (stderr, "There is no support for pthreads under this GC.\n");
  exit (1) ;
#elif _ATS_GCATS
  pthread_exit (NULL) ;
#elif _ATS_GCATS0
  fprintf (stderr, "There is no support for pthreads under this GC (GCATS0).\n");
  exit (1) ;
#elif _ATS_gc
  pthread_exit (NULL) ;
#else
  pthread_exit (NULL) ;
#endif
  return ;
} // end of [ats_pthread_exit]

/* ****** ****** */

#endif /* [ifdef _ATS_MULTITHREAD] */

/* end of [ats_prelude.c] */
