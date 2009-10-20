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

#include "config.h"

#include <stdio.h>

#ifdef _ATS_MULTITHREAD
#include <pthread.h>
#endif

/* ****** ****** */

#include "ats_types.h"
#include "ats_memory.h"

/* ****** ****** */

// implemented in [prelude/DATS/basics.dats]
extern void ats_exit_errmsg (int err, char *msg) ;

/* ****** ****** */

ats_empty_type ats_empty_value ;

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
SubscriptExceptionCon = { 40, "SubscriptException" } ;
ats_exn_ptr_type SubscriptException = &SubscriptExceptionCon ;

/* ****** ****** */

// the numbers less than 1000 are all
int ats_exception_con_tag = 1000 ; // reserved for special use

/*
** function for handling uncaught exceptions
*/

extern void exit (int status) ; // declared in [stdlib.h]

ats_void_type
ats_uncaught_exception_handle
  (const ats_exn_ptr_type exn) {
  fprintf (stderr, "Uncaught exception: %s(%d)\n", exn->name, exn->tag) ;
  exit(1) ;
} /* end of [ats_uncaught_exception_handle] */

/* ****** ****** */

/*
** functions for handling match failures
*/

ats_void_type
ats_caseof_failure_handle (char *loc) {
  fprintf (stderr, "Exit: %s: match failure.\n", loc) ; exit(1) ;
} /* end of [ats_caseof_failure_handle] */

ats_void_type
ats_funarg_match_failure_handle (char *loc) {
  fprintf (stderr, "Exit: %s: funarg match failure.\n", loc) ; exit(1) ;
} /* end of [ats_funarg_match_failure_handle] */

/* ****** ****** */

/*
**functions for memory allocation and deallocation
*/

#ifdef _ATS_NGC // no GC
#include "ats_prelude_ngc.c"
#elif _ATS_GCATS // special GC for ATS
#include "ats_prelude_gcats.c"
#elif _ATS_GCBDW // Boehm-Demers-Weise conservative GC for C/C++
#include "ats_prelude_gcbdw.c"
#else // _ATS_NGC is the default
#include "ats_prelude_ngc.c"
#endif // end of [ifdef]

/* ****** ****** */

#ifdef _ATS_MULTITHREAD

static
ats_ptr_type ats_pthread_app (ats_ptr_type f) {
  ((void (*)(ats_ptr_type))((ats_clo_ptr_type)f)->closure_fun)(f) ;
  ATS_FREE (f) ; // this is a linear application; it must be freed to avoid leak
  return (ats_ptr_type)0 ;
}

#ifdef _ATS_GCATS
extern int gc_pthread_create_cloptr (
  ats_clo_ptr_type cloptr, pthread_t *pid_r, int detached, int linclo
) ;
#endif

ats_void_type
ats_pthread_create_detached_cloptr (ats_ptr_type thunk) {
#if _ATS_NGC
  pthread_t pid ; int ret ;
  ret = pthread_create (&pid, NULL, ats_pthread_app, thunk) ;
#elif _ATS_GCATS
  int ret ;
/*
  fprintf (stderr, "[ats_pthread_create_detached_cloptr] is called.\n") ;
*/
  ret = gc_pthread_create_cloptr (thunk, NULL/*pid_r*/, 1/*detached*/, 1/*lin*/) ;
#elif _ATS_GCBDW
  fprintf (stderr, "There is no support for pthreads under this GC (GCBDW).\n") ;
  exit (1) ;
#else // _ATS_NGC is the default
  pthread_t pid ; int ret ;
  ret = pthread_create (&pid, NULL, ats_pthread_app, thunk) ;
#endif
  if (ret != 0) { perror ("ats_pthread_create_detached_clo: ") ; exit(1) ; }
  return ;
} /* end of [ats_pthread_create_detach] */

/* ****** ****** */

static inline
ats_void_type ats_pthread_exit () {
#ifdef _ATS_GCATS
  pthread_exit (NULL) ; // this is clearly problematic!!!
#else
  pthread_exit (NULL) ;
#endif
  return ;
} // end of [ats_pthread_exit]

#endif /* [ifdef _ATS_MULTITHREAD] */

/* ****** ****** */

/* end of [ats_prelude.c] */
