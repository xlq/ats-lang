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

#define ATS_FUNCTION_NAME_PREFIX "gcats2_manmem_"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

%{^

typedef
struct manmem_struct {
  int itmwsz ;
  struct manmem_struct *prev ;
  struct manmem_struct *next ;
  size_t manmem_wsz ;
  void *manmem_data[0] ; // this is done for alignment concern!
} manmem_vt ;

typedef manmem_vt *manmemlst_vt ;

/* ****** ****** */

manmemlst_vt the_manmemlst = (manmemlst_vt)0 ;

/* ****** ****** */

ats_ptr_type
gcats2_manmem_data_get (
  ats_ptr_type p_manmem // p_manmem != NULL
) {
  return ((manmem_vt*)p_manmem)->manmem_data ;
} /* end of [gcats2_manmem_data_get] */

/* ****** ****** */

ats_ptr_type
gcats2_manmem_make (
  ats_size_type bsz
) {
  manmem_vt *p_manmem ;
  size_t wsz =
    (bsz + NBYTE_PER_WORD_MASK) >> NBYTE_PER_WORD_LOG ;
  // end of [wsz]
  p_manmem = gcats2_malloc_ext(sizeof(manmem_vt) + bsz) ;
  p_manmem->manmem_wsz = wsz ;
  return (ats_ptr_type)p_manmem ;
} /* end of [gcats2_manmem_make] */

ats_void_type
gcats2_manmem_free (
  ats_ptr_type p_manmem
) {
  gcats2_free_ext(p_manmem) ; return ;
} /* end of [gcats2_manmem_free] */

/* ****** ****** */

ats_int_type
gcats2_the_manmemlst_length (
  // there is no argument for this function
) {
  int n ; manmemlst_vt p ;
  n = 0 ; p = the_manmemlst ; while (p) { n += 1 ; p = p->next ; }
  return n ;
} /* end of [gcats2_the_manmemlst_length] */

/* ****** ****** */

ats_void_type
gcats2_the_manmemlst_insert (
  ats_ptr_type p_manmem // [p_manmem] != NULL
) {
  // inserted as the head of the_manmemlst
  ((manmemlst_vt)p_manmem)->prev = (manmemlst_vt)0 ;
  ((manmemlst_vt)p_manmem)->next = the_manmemlst ;
  if (the_manmemlst) the_manmemlst->prev = p_manmem ;
  the_manmemlst = p_manmem ;
  return ;
} /* end of [gcats2_the_manmemlst_insert] */

ats_ptr_type
gcats2_the_manmemlst_remove (
  ats_ptr_type p_data // [p_data] points to the middle of ...
) {
  manmemlst_vt p =
    (manmemlst_vt)((byte*)p_data - sizeof(manmem_vt)) ;
  manmemlst_vt p_prev, p_next ;
  p_prev = ((manmemlst_vt)p)->prev ; // p != NULL
  p_next = ((manmemlst_vt)p)->next ; // p != NULL
  if (p_prev)
    p_prev->next = p_next ;
  else /* p: first one in the_manmemlst */
    the_manmemlst = p_next ;
  // end of [if]
  if (p_next) p_next->prev = p_prev ;
  return p ;
} /* end of [gcats2_the_manmemlst_remove] */

/* ****** ****** */

extern
ats_int_type gcats2_ptrsize_mark (ats_ptr_type ptr, ats_size_type wsz) ;

ats_int_type
gcats2_the_manmemlst_mark (
  // there is no argument for this function
) {
  manmemlst_vt p ; int overflow ;
  p = the_manmemlst ; overflow = 0 ;
  while (p) {
    overflow += gcats2_ptrsize_mark(p->manmem_data, p->manmem_wsz) ; p = p->next ;
  } // end of [while]
  return overflow ;
} /* end of [gcats2_the_manmemlst_mark] */

/* ****** ****** */

%} // end of [%{^]

(* ****** ****** *)

(* end of [gcats2_manmem.dats] *)
