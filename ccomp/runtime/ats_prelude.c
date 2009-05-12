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

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#include <stdio.h>

#ifdef _ATS_MULTITHREAD
#include <pthread.h>
#endif

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

extern void ats_exit_errmsg (int err, char *msg) ;

/* ****** ****** */

// The following variables are used in basics.dats
int ats_stdin_view_lock = 1 ;
int ats_stdout_view_lock = 1 ;
int ats_stderr_view_lock = 1 ;

/* ****** ****** */

/*
** the type of [the_ats_exception_stack]
** is given in the file [ats_exception.h]
*/

#ifdef _ATS_MULTITHREAD
__thread
ats_ptr_type *the_ats_exception_stack = NULL ;
#else /* single thread */
ats_ptr_type *the_ats_exception_stack = NULL ;
#endif

/* ****** ****** */

// some common exceptions

ats_exn_type
AssertionExceptionCon = { 10, "AssertionException" } ;
ats_exn_ptr_type AssertionException = &AssertionExceptionCon ;

/* ****** ****** */

ats_exn_type
OverflowExceptionCon = { 20, "OverflowException" } ;
ats_exn_ptr_type OverflowException = &OverflowExceptionCon ;

ats_exn_type
DivisionByZeroExceptionCon = { 30, "DivisionByZeroException" } ;
ats_exn_ptr_type DivisionByZeroException = &DivisionByZeroExceptionCon ;

/* ****** ****** */

ats_exn_type
NotFoundExceptionCon = { 40, "NotFoundException" } ;
ats_exn_ptr_type NotFoundException = &NotFoundExceptionCon ;

ats_exn_type
SubscriptExceptionCon = { 50, "SubscriptException" } ;
ats_exn_ptr_type SubscriptException = &SubscriptExceptionCon ;

/* ****** ****** */

// the numbers less than 1000 are all
int ats_exception_con_tag = 1000 ; // reserved for special use

/*
** function for handling uncaught exceptions
*/

extern void exit (int status) ; // declared in [stdlib.h]

ats_void_type
ats_uncaught_exception_handle (const ats_exn_ptr_type exn) {
  fprintf (stderr, "Uncaught exception: %s(%d)\n", exn->name, exn->tag) ;
  exit(1) ;
} /* end of [ats_uncaught_exception_handle] */

/*
** functions for handling match failures
*/

ats_void_type
ats_caseof_failure_handle (void) {
  ats_exit_errmsg(1, "Exit: match failure.\n") ; return ;
} /* end of [ats_caseof_failure_handle] */

ats_void_type
ats_funarg_match_failure_handle (void) {
  ats_exit_errmsg(1, "Exit: funarg match failure.\n") ; return ;
} /* end of [ats_funarg_match_failure_handle] */

/* ****** ****** */

/*
**
**functions for memory allocation and deallocation
**
*/

#ifdef _ATS_GC // default GC for ATS
#include "GCATS/gc.h"
#elif _ATS_GCATS // special GC for ATS
#include "GCATS/gc.h"
#elif _ATS_GCATS0 // special GC for ATS
#include "GCATS0/gc.h"
#elif _ATS_GCBDW // Boehm-Demers-Weise conservative GC for C/C++
#include "GCBDW/gc.h"
#else // no GC for ATS
#include <NGC/gc.h>
#endif

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
  fprintf (stderr, "There is no support for pthreads under this GC(GCATS0).\n");
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
