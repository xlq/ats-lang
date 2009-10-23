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
// Time: October, 2009

(* ****** ****** *)

#define ATSCCOMP_NAMESPACE "gcats2_top_"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

// this is the initialization function for the GC
implement gcmain_initialize () = () where {
  val () = mystackbeg_set (dir) where { val dir = mystackdir_get () }
#ifdef _ATS_MULTITHREAD
  val () = () where {
    viewdef V = the_manmemlst_v
    prval (pf, fpf) = __takeout () where {
      extern prfun __takeout (): (V, V -<lin> void)
    } // end of [prval]
    val () = the_manmemlst_lock_initialize (pf | (*none*))
    prval () = fpf (pf)
  } // end of [val]
#endif // end of [_ATS_MULTITHREAD]
  val () = () where {
    viewdef V = the_topsegtbl_v
    prval (pf, fpf) = __takeout () where {
      extern prfun __takeout (): (V, V -<lin> void)
    } // end of [prval]
    val () = the_topsegtbl_initialize (pf | (*none*))
    prval () = fpf (pf)
  } // end of [val]
} // end of [gcmain_initialize]

(* ****** ****** *)

%{^

#if (__WORDSIZE == 32)

// is this enough for not calling the following initialization
botsegtblptr_vt the_topsegtbl[TOPSEG_TABLESIZE] = {0} ; // function?

ats_void_type
gcats2_the_topsegtbl_initialize () {
  int i ;
  for (i = 0; i < TOPSEG_TABLESIZE; i++) the_topsegtbl[i] = (botsegtblptr_vt)0 ;
} /* end of [the_topsegtbl_initialize] */

#endif // end of [__WORDSIZE == 32]

#if (__WORDSIZE == 64)

// is this enough for not calling the following initialization
botsegtblptr_vt the_topsegtbl[TOPSEG_HASHTABLESIZE] = {0} ; // function?

ats_void_type
gcats2_the_topsegtbl_initialize () {
  int i ;
  for (i = 0; i < TOPSEG_HASHTABLESIZE; i++) the_topsegtbl[i] = (botsegtblptr_vt)0 ;
} /* end of [the_topsegtbl_initialize] */

#endif // end of [__WORDSIZE == 64]

%} // end of [%{^]

(* ****** ****** *)

%{^

// this is the total number
size_t the_totwsz = 0 ; // of words in use
size_t the_totwsz_limit = 6 * 1024 ;
size_t the_totwsz_limit_max = 0 ;

freeitmlst_vt the_chunkpagelst = (freeitmlst_vt*)0 ;

/* ****** ****** */

manmemlst_vt the_manmemlst = (manmemlst_vt)0 ;

#ifdef _ATS_MULTITHREAD

pthread_spinlock_t the_manmemlst_lock ;

ats_void_type
gcats2_the_manmemlst_lock_initialize () {
  int err ;
  err = pthread_spin_init (&the_manmemlst_lock, PTHREAD_PROCESS_PRIVATE) ;
  if (err != 0) {
    fprintf(stderr, "exit(ATS/GC): [the_manmemlst_lock_initialize] failed.\n") ; exit(1) ;
  } // end of [if]
  return ;
} /* end of [gcats2_the_manmemlst_lock_initialize] */

#endif // end of [_ATS_MULTITHREAD]

/* ****** ****** */

// FREEITMLST_ARRAYSIZE = MAX_CLICK_WORDSIZE_LOG + 1
chunklst_vt the_sweeplstarr[FREEITMLST_ARRAYSIZE] = {0} ;

ats_ptr_type
gcats2_the_sweeplstarr_get_chunk (
  ats_int_type itmwsz_log // itmwsz_log < FREEITMLST_ARRAYSIZE
) {
  chunkptr_vt p_chunk ;
#if (GCATS2_DEBUG > 0)
  if (itmwsz_log < 0 || itmwsz_log >= FREEITMLST_ARRAYSIZE) {
    fprintf(stderr, "INTERNAL ERROR") ;
    fprintf(stderr,
      ": exit(ATS/GC): the_sweeplstarr_get_chunk: itmwsz_log = %i", itmwsz_log
    ) ; exit(1) ;
  } // end of [if]
#endif // end of [GCATS2_DEBUG > 0]
  p_chunk = the_sweeplstarr[itmwsz_log] ;
  if (!p_chunk) { return (chunkptr_vt)0 ; }
  the_sweeplstarr[itmwsz_log] = p_chunk->sweepnxt ;
  return p_chunk ;
} // end of [the_sweeplstarr_get_chunk]

/* ****** ****** */

#ifdef _ATS_MULTITHREAD
__thread // thread-local storage
#endif // end of [_ATS_MULTITHREAD]
freeitmlst_vt the_freeitmlstarr[FREEITMLST_ARRAYSIZE] = {0} ;

ats_ptr_type
gcats2_the_freeitmlstarr_get_freeitm (
  ats_int_type itmwsz_log // itmwsz_log < FREEITMLST_ARRAYSIZE
) {
  freeitmptr_vt p_freeitm ;
#if (GCATS2_DEBUG > 0)
  if (itmwsz_log < 0 || itmwsz_log >= FREEITMLST_ARRAYSIZE) {
    fprintf(stderr, "INTERNAL ERROR") ;
    fprintf(stderr,
      ": exit(ATS/GC): the_freeitmlstarr_get_freeitm: itmwsz_log = %i", itmwsz_log
    ) ; exit(1) ;
  } // end of [if]
#endif // end of [GCATS2_DEBUG > 0]
  p_freeitm = the_freeitmlstarr[itmwsz_log] ;
  if (!p_freeitm) { return (freeitmptr_vt)0 ; }
  the_freeitmlstarr[itmwsz_log] = *(freeitmlst_vt*)p_freeitm ;
  return p_freeitm ;
} // end of [the_freeitmlstarr_get_freeitm]

/* ****** ****** */

#ifdef _ATS_MULTITHREAD

pthread_mutex_t
the_gcmain_lock = PTHREAD_MUTEX_INITIALIZER ;

pthread_mutex_t
the_threadinfolst_lock = PTHREAD_MUTEX_INITIALIZER ;

#endif // end of [_ATS_MULTITHREAD]

%} // end of [%{^]

(* ****** ****** *)

(* end of [gcats2_top.dats] *)
