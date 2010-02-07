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

#ifndef ATS_PRELUDE_BASICS_CATS
#define ATS_PRELUDE_BASICS_CATS

/* ****** ****** */

#include <stdarg.h>
#include <stdio.h>

/* ****** ****** */

#define _ATS_RUNTIME_CHECK
#undef _ATS_RUNTIME_CHECK // uncomment it for debugging

/* ****** ****** */

/*
** HX-2010-02-07: this one is used in many places
*/
static inline
ats_ptr_type
atspre_castfn_ptr (ats_ptr_type p) { return p ; }

/* ****** ****** */

/*
** HX: cutting the corners? yes. worth it? probably.
*/

static inline
ats_ptr_type
atspre_fun_coerce (ats_ptr_type p) { return p ; }

static inline
ats_ptr_type
atspre_clo_coerce (ats_ptr_type p) { return p ; }

/* ****** ****** */

static inline
ats_ptr_type
atspre_cloptr_get_view_ptr (ats_ptr_type p) { return p ; }

/* ****** ****** */

static inline
ats_void_type
atspre_cloptr_free (ats_ptr_type p)
  { ATS_FREE (p) ; return ; } // end of [atspre_cloptr_free]

/* ****** ****** */

static inline
ats_ptr_type
atspre_objmod_upcast (ats_ptr_type p) { return p ; }

/* ****** ****** */

static inline
ats_void_type
atspre_vbox_make_view_ptr (ats_ptr_type p) { return ; }

static inline
ats_void_type
atspre_vbox_make_view_ptr_gc (ats_ptr_type p) { return ; }

/* ****** ****** */

/* functions for exits */

extern ats_void_type ats_exit(const ats_int_type n) ;

extern ats_void_type
ats_exit_errmsg(const ats_int_type n, const ats_ptr_type msg) ;

extern ats_void_type
atspre_exit_prerrf(ats_int_type code, ats_ptr_type fmt, ...) ;

/* ****** ****** */

// int ats_stdin_view_lock = 1 ;
extern int ats_stdin_view_lock ;

static inline
ats_ptr_type
atspre_stdin_get(void) {
#ifdef _ATS_RUNTIME_CHECK
  if (!ats_stdin_view_lock) {
    ats_exit_errmsg (1, "exit(ATS): [stdin_get] failed\n") ;
  }
#endif
  ats_stdin_view_lock = 0 ;
  return (ats_ptr_type)stdin;
}

static inline
ats_void_type
atspre_stdin_view_get(void) {
#ifdef _ATS_RUNTIME_CHECK
  if (!ats_stdin_view_lock) {
    ats_exit_errmsg (1, "exit(ATS): [stdin_view_get] failed\n") ;
  }
#endif
  ats_stdin_view_lock = 0 ;
  return ;
}

static inline
ats_void_type
atspre_stdin_view_set(void) {
#ifdef _ATS_RUNTIME_CHECK
  if (ats_stdin_view_lock) {
    ats_exit_errmsg (1, "exit(ATS): [stdin_view_set] failed\n") ;
  }
#endif
  ats_stdin_view_lock = 1 ;
  return ;
}

static inline
ats_bool_type
atspre_stdin_view_get_opt(void) {
  if (ats_stdin_view_lock) {
    ats_stdin_view_lock = 0 ; return 1 ;
  }
  return 0 ;
}

static inline
ats_bool_type
atspre_stdin_view_set_opt(void) { 
  if (!ats_stdin_view_lock) {
    ats_stdin_view_lock = 1 ; return 1 ;
  }
  return 0 ;
}

/* ****** ****** */

// int ats_stdout_view_lock = 1 ;
extern int ats_stdout_view_lock ;

static inline
ats_ptr_type
atspre_stdout_get(void) {
#ifdef _ATS_RUNTIME_CHECK
  if (!ats_stdout_view_lock) {
    ats_exit_errmsg (1, "exit(ATS): [stdout_get] failed\n") ;
  }
#endif
  ats_stdout_view_lock = 0 ;
  return (ats_ptr_type)stdout ;
}

static inline
ats_void_type
atspre_stdout_view_get(void) {
#ifdef _ATS_RUNTIME_CHECK
  if (!ats_stdout_view_lock) {
    ats_exit_errmsg (1, "exit(ATS): [stdout_view_get] failed\n") ;
  }
#endif
  ats_stdout_view_lock = 0 ;
  return ;
}

static inline
ats_void_type
atspre_stdout_view_set(void) {
#ifdef _ATS_RUNTIME_CHECK
  if (ats_stdout_view_lock) {
    ats_exit_errmsg (1, "exit(ATS): [stdout_view_set] failed\n") ;
  }
#endif
  ats_stdout_view_lock = 1 ;
  return ;
}

static inline
ats_bool_type
atspre_stdout_view_get_opt(void) {
  if (ats_stdout_view_lock) {
    ats_stdout_view_lock = 0 ; return 1 ;
  }
  return 0 ;
}

static inline
ats_bool_type
atspre_stdout_view_set_opt(void) { 
  if (!ats_stdout_view_lock) {
    ats_stdout_view_lock = 1 ; return 1 ;
  }
  return 0 ;
}

/* ****** ****** */

// int ats_stderr_view_lock = 1 ;
extern int ats_stderr_view_lock ;

static inline
ats_ptr_type
atspre_stderr_get(void) {
#ifdef _ATS_RUNTIME_CHECK
  if (!ats_stderr_view_lock) {
    ats_exit_errmsg (1, "exit(ATS): [stderr_get] failed\n") ;
  }
#endif
  ats_stderr_view_lock = 0 ;
  return (ats_ptr_type)stderr ;
}

static inline
ats_void_type
atspre_stderr_view_get(void) {
#ifdef _ATS_RUNTIME_CHECK
  if (!ats_stderr_view_lock) {
    ats_exit_errmsg (1, "exit(ATS): [stderr_view_get] failed\n") ;
  }
#endif
  ats_stderr_view_lock = 0 ;
  return ;
}

static inline
ats_void_type
atspre_stderr_view_set(void) {
#ifdef _ATS_RUNTIME_CHECK
  if (ats_stderr_view_lock) {
    ats_exit_errmsg (1, (ats_ptr_type)"exit(ATS): [stderr_view_set] failed\n") ;
  }
#endif
  ats_stderr_view_lock = 1 ;
  return ;
}

static inline
ats_bool_type
atspre_stderr_view_get_opt(void) {
  if (ats_stderr_view_lock) {
    ats_stderr_view_lock = 0 ; return 1 ;
  }
  return 0 ;
}

static inline
ats_bool_type
atspre_stderr_view_set_opt(void) { 
  if (!ats_stderr_view_lock) {
    ats_stderr_view_lock = 1 ; return 1 ;
  }
  return 0 ;
}

/* ****** ****** */

// printing a newline on a given stream also fflushes the buffer
// associated with the stream.

static inline
ats_void_type
atspre_fprint_newline(const ats_ptr_type out) {
  int n1, n2 ;
  n1 = fprintf((FILE *)out, "\n") ; n2 = fflush((FILE *)out) ;
  if (n1 + n2 < 0) { ats_exit_errmsg
    (1, (ats_ptr_type)"exit(ATS): [fprint_newline] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_newline(void) {
  atspre_stdout_view_get() ;
  atspre_fprint_newline((ats_ptr_type)stdout) ;
  atspre_stdout_view_set() ;
  return ;
}

static inline
ats_void_type
atspre_prerr_newline(void) {
  atspre_stderr_view_get() ;
  atspre_fprint_newline((ats_ptr_type)stderr) ;
  atspre_stderr_view_set() ;
  return ;
}

/* ****** ****** */

#endif /* ATS_PRELUDE_BASICS_CATS */
