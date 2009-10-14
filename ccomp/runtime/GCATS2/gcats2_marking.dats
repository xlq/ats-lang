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

staload "gcats2.sats"

(* ****** ****** *)

%{^

typedef struct {
  void *ptr ; size_t wsz ;
} ptrsize_t ;

typedef
struct markstackpage_struct {
  struct markstackpage_struct *next ;
  struct markstackpage_struct *prev ;
  ptrsize_t entries[MARKSTACK_PAGESIZE] ;
} markstackpage_vt ;

typedef markstackpage_vt *markstackpagelst_vt ;

markstackpage_vt the_markstackpage_fst = { 0 } ;

markstackpagelst_vt // it should never be NULL!
the_markstackpagelst_cur = &the_markstackpage_fst ;

// the_markstackposition : natLte (MARKSTACK_PAGESIZE)
int the_markstackposition = 0 ; // if =MARKSTACK_PAGESIZE: markstack is all used up

/*
fun the_markstackpagelst_length
  (pf: !the_markstackpagelst_v | (*none*)):<> int // > 0
*/
ats_int_type
gcats2_the_markstackpagelst_length () {
  int n = 0 ;
  markstackpage_vt *p_page ;
  p_page = the_markstackpagelst_cur->prev ;
  while (p_page) { n += 1 ; p_page = p_page->prev ; } // going up
  p_page = the_markstackpagelst_cur->next ;
  while (p_page) { n += 1 ; p_page = p_page->next ; } // going down
  return (n + 1) ; // [+1]: the current one needs to be included
} /* end of [gcats2_the_markstackpagelst_length] */

ats_void_type
gcats2_the_markstackpagelst_pop
  (ats_ref_type r_ptr, ats_ref_type r_wsz) {
  int i ; ptrsize_t *p_entry ;
  if (the_markstackposition > 0)
    the_markstackposition -= 1 ;
  else {
    the_markstackposition = (MARKSTACK_PAGESIZE - 1) ;
    the_markstackpagelst_cur = the_markstackpagelst_cur->prev ;
  } // end of [if]
  p_entry = &(the_markstackpagelst_cur->entries[the_markstackposition]) ;
  *(ats_ptr_type*)r_ptr = p_entry->ptr ; *(ats_size_type*)r_wsz = p_entry->wsz ;
#if (GCATS2_DEBUG > 0)
  if (!the_markstackpagelst_cur) {
    fprintf (stderr, "gcats2_the_markstackpagelst_pop: underflow happened!\n"); exit(1);
  } // end of [if]
#endif // end of [GCATS2_DEBUG > 0]
  return ;
} /* end of [gcats2_the_markstackpagelst_pop] */

ats_int_type
gcats2_the_markstackpagelst_push (
  ats_ptr_type ptr, ats_size_type wsz, ats_ref_type r_overflow
) {
  ptrsize_t *p_entry ;
  if (the_markstackposition == MARKSTACK_PAGESIZE) {
    *(ats_int_type*)r_overflow += 1 ; return ; // overflow happens!
  }
  p_entry = &(the_markstackpagelst_cur->entries[the_markstackposition]) ;
  the_markstackposition += 1 ;
  if (the_markstackposition == MARKSTACK_PAGESIZE) {
    if (the_markstackpagelst_cur->next) {
      the_markstackpagelst_cur = the_markstackpagelst_cur->next ; the_markstackposition = 0 ;
    } else {
      // the markstack is all used up and overflow is imminent!
    } // end of [if]
  } // end of [if]
  p_entry->ptr = ptr ; p_entry->wsz = wsz ;
  return ;
} /* end of [gcats2_the_markstackpagelst_push] */

ats_void_type
gcats2_the_markstackpagelst_extend
  (ats_int_type n) {
#if (GCATS2_TEST > 0)
  int _n = n, _n1 = 0, _n2 = 0, _n3 = 0 ;
#endif // end of [GCATS2_DEBUG > 0]
  markstackpagelst_vt p_page, p_page_next ;
  p_page = the_markstackpagelst_cur ; p_page_next = p_page->next ;
  while (p_page_next) {
#if (GCATS2_TEST > 0)
    _n1 += 1 ;
#endif // end of [GCATS2_DEBUG > 0]
    p_page = p_page_next ; p_page_next = p_page->next ;
  }
  // [p_page] points to the last markstackpage at this point
  while (n > 0) {
    n -= 1 ;
    p_page_next = (markstackpage_vt*)gcats2_malloc_ext(sizeof(markstackpage_vt)) ;
    p_page_next->prev = p_page ;
    p_page_next->next = (markstackpage_vt*)0 ;
    p_page->next = p_page_next ;
    p_page = p_page_next ;
  } // end of [while]
#if (GCATS2_TEST > 0)
  while (p_page != the_markstackpagelst_cur) { p_page = p_page->prev ; _n2 += 1 ; }
  for (p_page = the_markstackpagelst_cur->next; p_page != 0; p_page = p_page->next) _n3 += 1 ;
  if (_n + _n1 != _n2 || _n2 != _n3) {
    fprintf(stderr, "gcats2_the_markstackpagelst_extend: _n=%i\n", _n) ;
    fprintf(stderr, "gcats2_the_markstackpagelst_extend: _n1=%i\n", _n1) ;
    fprintf(stderr, "gcats2_the_markstackpagelst_extend: _n2=%i\n", _n2) ;
    fprintf(stderr, "gcats2_the_markstackpagelst_extend: _n3=%i\n", _n3) ;
    exit(1) ;
  } // end of [if]
#endif // end of [GCATS2_DEBUG > 0]
} // end of [gcats2_the_markstackpagelst_extend]

%} // end of [%{^]

(* ****** ****** *)

%{^

extern
ats_ptr_type
gcats2_ptr_isvalid (ats_ptr_type ptr, ats_ref_type r_ofs_chkseg) ;

ats_int_type
gcats2_ptr_mark
  (ats_ptr_type ptr) { // freeitmptr_vt *ptr
  chunkptr_vt p_chunk ;
  int itmwsz, ofs_chkseg ;
  int i ; freeitmptr_vt *ptr_i ;
  freeitmptr_vt ptr_cand ;
  int overflow, found1st ;
/*
  fprintf (stderr, "gcats2_ptr_mark(0): ptr = %p\n", ptr) ;
*/
  overflow = 0 ;
  p_chunk = (chunkptr_vt)gcats2_ptr_isvalid(ptr, &ofs_chkseg) ;
/*
  fprintf (stderr, "gcats2_ptr_mark(1): p_chunk = %p\n", chks) ;
*/
  if (!p_chunk) return overflow ; // [ptr] is invalid
  // [ptr] is already marked:
  if (MARK_GETSET(p_chunk->mrkbits, ofs_chkseg)) return overflow ;
  p_chunk->mrkcnt += 1 ; // newly marked
  itmwsz = p_chunk->itmwsz ;

  // pushing a sentinel first
  gcats2_the_markstackpagelst_push((freeitmptr_vt*)0, 0, &overflow) ;
  while (ptr) { // ptr != NULL
/*
    fprintf (stderr, "gcats2_ptr_mark: ptr = %p\n", ptr) ;
    fprintf (stderr, "gcats2_ptr_mark: itwsz = %i\n", itmwsz);
*/
    if (itmwsz > MARKSTACK_CUTOFF) {
      gcats2_the_markstackpagelst_push(
        (freeitmptr_vt*)ptr + MARKSTACK_CUTOFF, itmwsz - MARKSTACK_CUTOFF, &overflow
      ) ;
      itmwsz = MARKSTACK_CUTOFF ;
    } // end of [if]
    
    // push all the valid pointers onto the markstack
    found1st = 0 ; ptr_i = (freeitmptr_vt*)ptr ;
    for (i = 0; i < itmwsz; i += 1, ptr_i += 1) {
      ptr_cand = *ptr_i ;
/*
      fprintf (stderr, "gcats2_ptr_mark: ptr_i = %p\n", ptr_i) ;
      fprintf (stderr, "gcats2_ptr_mark: ptr_cand = %p\n", ptr_cand) ;
*/
      p_chunk = (chunkptr_vt)gcats2_ptr_isvalid(ptr_cand, &ofs_chkseg) ;
      if (!p_chunk) continue ; // [ptr_cand] is invalid
      if (MARK_GETSET(p_chunk->mrkbits, ofs_chkseg)) continue ; // already marked
      p_chunk->mrkcnt += 1 ; // newly marked
      if (found1st) { // this is *not* the first one
        gcats2_the_markstackpagelst_push(ptr_cand, p_chunk->itmwsz, &overflow) ;
      } else { // this is the first one; save a push and pop
        found1st = 1 ; *(freeitmptr_vt*)ptr = ptr_cand ; itmwsz = p_chunk->itmwsz ;
      } // end of [if]
    } // end of [for]
    if (!found1st)  // no child for [ptr]; so [ptr] and [itmwsz]
      gcats2_the_markstackpagelst_pop(&ptr, &itmwsz) ; // need to be updated
    // end of [if]
  } // end of [while]
  return overflow ; // overflow > 0 if overflow happened
} /* end of [gcats2_ptr_mark] */

%} // end of [%{^]

(* ****** ****** *)

(* end of [gcats2_marking.dats] *)
