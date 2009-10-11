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
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
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

#include "gcats2_ats.hats"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

%{^

ats_void_type
gcats2_the_topsegtbl_insert_chunkptr
  (ats_ptr_type p_chunk) {
  topseg_t ofs_topseg ; int ofs_botseg ; // ofs_chkseg == 0
  botsegtblptr_vt p_botsegtbl, *r_p_botsegtbl ;
  chunkptr_vt *r_p_chunk ;

  ofs_topseg = PTR_TOPSEG_GET(p_chunk) ;
  r_p_botsegtbl =
    (botsegtblptr_vt*)(gcats2_the_topsegtbl_takeout(ofs_topseg)) ;
  p_botsegtbl = *r_p_botsegtbl ;
  if (!p_botsegtbl) {
    p_botsegtbl =
      gcats2_malloc_ext(sizeof(botsegtbl_vt)) ;
    memset(p_botsegtbl, 0, sizeof(botsegtbl_vt)) ;
#if (__WORDSIZE == 64)
     p_botsegtbl->key =(uintptr_t)ofs_topseg ; p_botsegtbl->hashnxt = (botsegtblptr_vt)0 ;
#endif // end of [#if (__WORDSIZE == 64)]
    *r_p_botsegtbl = p_botsegtbl ;
  } // end of [if]
  ofs_botseg = PTR_BOTSEG_GET(p_chunk) ;
  r_p_chunk = gcats2_botsegtblptr1_takeout(p_botsegtbl, ofs_topseg, ofs_botseg) ;
//
#if (__WORDSIZE == 64)
  if (!r_p_chunk) {
// /*
    fprintf(stderr, "gcats2_the_topsegtbl_insert_chunkptr: r_p_chunk = %p\n", r_p_chunk) ;
// */
    p_botsegtbl =
      gcats2_malloc_ext(sizeof(botsegtbl_vt)) ;
    memset(p_botsegtbl, 0, sizeof(botsegtbl_vt)) ;
    p_botsegtbl->key = (uintptr_t)ofs_topseg ; p_botsegtbl->hashnxt = *r_p_botsegtbl ;
    *r_p_botsegtbl = p_botsegtbl ;
    (p_botsegtbl->headers)[ofs_botseg] = p_chunk ;
    return ;
  } // end of [if]
#endif // end of [#if (__WORDSIZE == 64)]
//
#if (GCATS2_DEBUG > 0)
  if (*r_p_chunk != (chunkptr_vt)0) {
    fprintf(
      stderr, "exit(ATS/GC): gcats2_the_topsegtbl_insert_chunkptr: *r_p_chunk = %p\n", *r_p_chunk
    ) ;
    exit(1) ;
  } // end of [if]
#endif // end of [#if (GCATS2_DEBUG > 0)]
//
  *r_p_chunk = p_chunk ; return ;
} /* end of [gcats2_the_topsegtbl_insert_chunkptr] */

/* ****** ****** */

ats_ptr_type // chunkptr
gcats2_the_topsegtbl_remove_chunkptr
  (ats_ptr_type ptr) {
  topseg_t ofs_topseg ; int ofs_botseg ; // ofs_chkseg == 0
  botsegtblptr_vt p_botsegtbl;
  chunkptr_vt p_chunk, *r_p_chunk ;

  ofs_topseg = PTR_TOPSEG_GET(ptr) ;
  p_botsegtbl = // pf_botsegtbl, fpf_topsegtbl
    *(botsegtblptr_vt*)(gcats2_the_topsegtbl_takeout(ofs_topseg)) ;
  if (!p_botsegtbl) return (chunkptr_vt)0 ; // error return
  ofs_botseg = PTR_BOTSEG_GET(ptr) ;
  r_p_chunk = gcats2_botsegtblptr1_takeout(p_botsegtbl, ofs_topseg, ofs_botseg) ;
  if (!r_p_chunk) { return (chunkptr_vt)0 ; } // error return
  p_chunk = *r_p_chunk ; *r_p_chunk = (chunkptr_vt)0 ;
#if (GCATS2_DEBUG > 0)
  if (ptr != p_chunk) {
    fprintf(stderr,
      "exit(ATS/GC): gcats2_the_topsegtbl_remove_chunkptr: ptr = %p\n", ptr
    ) ;
    fprintf(stderr,
      "exit(ATS/GC): gcats2_the_topsegtbl_remove_chunkptr: p_chunk = %p\n", p_chunk
    ) ;
    exit(1) ;
  } // end of [if]
#endif // end of [#if (GCATS2_DEBUG > 0)]
  return p_chunk ;
} /* end of ... */

%} // end of [ %{^ ]


(* ****** ****** *)

(* end of [gcats2_chunk.dats] *)
