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

#ifndef ATS_BASICS_H
#define ATS_BASICS_H

/* ****** ****** */

/*
#define ATSstringize(id) # id
*/

/* ****** ****** */

/* [ATSextern] -> [ATSextern_val] */
#define ATSextern(ty, var) extern ty var
#define ATSextern_prf(cst) /* proof constant */
#define ATSextern_val(ty, val) extern ty val
#define ATSstatic(ty, var) static ty var
#define ATSstatic_void(var)
#define ATSunused __attribute__ ((unused))
#define ATSlocal(ty, var) ty ATSunused var
#define ATSlocal_void(var)
#define ATSglobal(ty, var) ty var
#define ATScastfn(castfn, val) val

/* ****** ****** */

#define ATSdeadcode() \
  do { \
    fprintf ( \
      stderr, \
      "Error in the file %s on line %d: the deadcode is executed!\n", \
      __FILE__, __LINE__ \
    ); \
    abort (); \
  } while (0);

/* boolean values */
#define ats_true_bool 1
#define ats_false_bool 0

/* ****** ****** */

/* closure function selection */
#define ats_closure_fun(f) ((ats_clo_ptr_type)f)->closure_fun

/* ****** ****** */

/* while loop: deprecated!!! */
#define ats_while_beg_mac(clab) while(ats_true_bool) { clab:
#define ats_while_end_mac(blab, clab) goto clab ; blab: break ; }

/* for/while loop */
#define ats_loop_beg_mac(init) while(ats_true_bool) { init:
#define ats_loop_end_mac(init, fini) goto init ; fini: break ; }

/* ****** ****** */

/* for initializing a reference */
#define ats_instr_move_ref_mac(tmp, hit, val) \
  do { tmp = ATS_MALLOC (sizeof(hit)) ; *(hit*)tmp = val ; } while (0)

/* ****** ****** */

/* for proof checking at run-time */
#define ats_termcheck_beg_mac(dyncst) \
  static int dyncst ## _flag = 0 ; \
  do { \
    if (dyncst ## _flag > 0) return ; \
    if (dyncst ## _flag < 0) { \
      fprintf (stderr, "exit(ATS): termination checking failure: [%s] is cyclically defined!\n", # dyncst) ; \
      exit (1) ; \
    } \
    dyncst ## _flag = -1 ; \
  } while (0) ;
/* end of [ats_termcheck_beg_mac] */

#define ats_termcheck_end_mac(dyncst) { dyncst ## _flag =  1 ; }

/* ****** ****** */

/*
** [mainats_prelude] is called in the function [main]
** it is implemented in [$ATSHOME/prelude/ats_main_prelude.dats]
** where it is given the name [main_prelude].
*/
extern void mainats_prelude () ;

/* ****** ****** */

/*
** functions for handling match failures
** the implementation is given in [ats_prelude.c]
*/
extern void ats_caseof_failure_handle (char *loc) ;
extern void ats_funarg_match_failure_handle (char *loc) ;

/* ****** ****** */

#endif /* ATS_BASICS_H */

/* end of [ats_basics.h] */
