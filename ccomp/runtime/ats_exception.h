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

/*
 *
 * Authors: 
 * Likai Liu (liulk AT cs DOT bu DOT edu) // Summer 2005
 * Rick Lavoie (coldfury AT cs DOT bu DOT edu) // Fall 2006
 * Hongwei Xi (hwxi AT cs DOT bu DOT edu) // Summer 2007
 *
 */

#ifndef __ATS_EXCEPTION_H
#define __ATS_EXCEPTION_H

#include <alloca.h>
#include <setjmp.h>

/* ****** ****** */

#include "ats_basics.h"
#include "ats_types.h"

/* ****** ****** */

/* function for handling uncaught exceptions */

extern
ats_void_type
ats_handle_exception(const ats_exn_ptr_type exn) ;

/* ****** ****** */

/* exception implementation */

typedef
struct ats_exception_frame_struct {
  ats_exn_ptr_type exn ;
  struct ats_exception_frame_struct *prev ;
  sigjmp_buf env ;
} ats_exception_frame_type ;

/* ****** ****** */

#ifdef _ATS_MULTITHREAD
extern __thread
ats_exception_frame_type *the_ats_exception_stack ;
#else /* single thread */
extern
ats_exception_frame_type *the_ats_exception_stack ;
#endif

/* ****** ****** */

#define ATS_CURRENT_FRAME (the_ats_exception_stack)

#define ATS_ENTER_EXCEPTION_FRAME() \
  do { \
    ats_exception_frame_type *frame = \
      (ats_exception_frame_type*) alloca(sizeof(ats_exception_frame_type)); \
    frame->prev = ATS_CURRENT_FRAME ; \
    ATS_CURRENT_FRAME = frame ; \
  } while(0)

#define ATS_LEAVE_EXCEPTION_FRAME() \
  do { ATS_CURRENT_FRAME = ATS_CURRENT_FRAME->prev; } while(0)

#define ATS_RAISE(exn) \
  do { \
    if (ATS_CURRENT_FRAME == 0 /*null*/) ats_handle_exception(exn) ; \
    ATS_CURRENT_FRAME->exn = exn ; \
    siglongjmp(ATS_CURRENT_FRAME->env, 0) ; \
  } while(0)

/* End of warning */

/* DO use the following macros. */

#define ATS_TRYWITH_TRY(tmp_exn) \
do { \
ATS_ENTER_EXCEPTION_FRAME() ; \
tmp_exn = (ats_exn_ptr_type)(intptr_t)sigsetjmp(ATS_CURRENT_FRAME->env, 0) ; \
if ((intptr_t)tmp_exn == 0) { /* ... */

#define ATS_TRYWITH_WITH(tmp_exn) \
ATS_LEAVE_EXCEPTION_FRAME() ; \
} else { \
tmp_exn = ATS_CURRENT_FRAME->exn ; \
ATS_LEAVE_EXCEPTION_FRAME() ; /* exception handling */

#define ATS_TRYWITH_END() \
} \
} while(0)

/* function for raising exceptions */

static inline
ats_void_type ats_raise_exn
  (const ats_exn_ptr_type exn) { ATS_RAISE(exn) ; return ; }

/* ****** ****** */

/* function for generating new exception constructor tag */

/* the following variable is defined in [ats_global.c] */
extern int ats_exception_con_tag ;

static inline
int ats_exception_con_tag_new () {
  return (++ats_exception_con_tag) ;
}

/* functions for handling match failures */

extern
ats_void_type ats_caseof_failure(void) ;

extern
ats_void_type ats_funarg_match_failure(void) ;

/* ****** ****** */

#endif /* __ATS_EXCEPTION_H */

/* end of [ats_exception.h] */
