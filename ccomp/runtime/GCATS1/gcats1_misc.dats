(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Power of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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
*)

(* ****** ****** *)

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: June 2008

(* ****** ****** *)

#include "gcats1.hats"

(* ****** ****** *)

staload "gcats1.sats"

(* ****** ****** *)

#define ATSCCOMP_NAMESPACE "gcats1_misc_"

(* ****** ****** *)

%{^

static int the_stack_direction = 0 ;

// dir=1/-1 : upward/downward
static ats_int_type volatile
gc_stack_dir_get_main (unsigned int *some_ptr) {
  unsigned int some_int ;
  if (&some_int > some_ptr) return 1 ; else return -1 ;
  return 0 ; /* deadcode */
}

ats_int_type gc_stack_dir_get () {
  unsigned int some_int ;
  if (!the_stack_direction) { // uninitialized
    the_stack_direction = gc_stack_dir_get_main (&some_int) ;
  }
  return the_stack_direction ;
}

/* ****** ****** */

#ifdef _ATS_MULTITHREAD
static __thread
ats_ptr_type the_stack_beg = (ats_ptr_type)0 ;
#else /* single thread */
static
ats_ptr_type the_stack_beg = (ats_ptr_type)0 ;
#endif

ats_void_type gc_stack_beg_set (ats_int_type dir) {
  long int pagesize, pagemask ; uintptr_t beg ;

  if (the_stack_beg) return ; // already set

  // pagesize must be a power of 2
  pagesize = sysconf(_SC_PAGESIZE) ; // system configuration
/*
  fprintf(stderr, "get_stack_beg_set: pagesize = %li\n", pagesize) ;
  fprintf(stderr, "get_stack_beg_set: &pagesize = %p\n", &pagesize) ;
*/
  pagemask = ~(pagesize - 1) ; // 1...10...0

  if (dir > 0) {
    beg = (uintptr_t)(&pagesize) ;
    beg &= pagemask ;
  } else {
    beg = (uintptr_t)(&pagesize) + pagesize ;
    beg &= pagemask ;
    beg -= sizeof(freeitmlst) ;
  }

  the_stack_beg = (ats_ptr_type)beg ;

  return ;
}

ats_ptr_type
gc_stack_beg_get (
  // there is no argument for this function
) {
  if (!the_stack_beg) {
    fprintf (stderr, "GC Fatal Error: [gc_stack_beg_get]") ;
    fprintf (stderr, ": [the_stack_beg] is not yet set.\n") ;
    exit (1) ;
  }
  return the_stack_beg ;
}

%}

(* ****** ****** *)

(* end of [gcats1_misc.dats] *)
