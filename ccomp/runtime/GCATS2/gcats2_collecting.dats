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

(*
fun the_topsegtbl_sweeplst_build
  (pf_tbl: !the_topsegtbl_v, pf_arr: !the_sweeplstarr_v | (*none*)):<> void
// end of [the_topsegtbl_sweeplst_build]
*)
implement the_topsegtbl_sweeplst_build
  (pf_tbl, pf_arr | (*none*)) = let
  viewdef tbl_v = the_topsegtbl_v and arr_v = the_sweeplstarr_v
  val f = lam {l:anz} (
      pf1: !tbl_v, pf2: !arr_v | p_chunk: !chunkptr_vt l, env: !ptr
    ) : void =<fun> let
    val (pf_chunk | p) = chunkptr_unfold (p_chunk)
    val () = chunk_sweeplst_build (pf2 | !p)
    val _(*ptr*) = chunkptr_fold (pf_chunk | p_chunk)
  in
    // nothing
  end // end of [val f]
in
  the_topsegtbl_foreach_chunkptr {arr_v} {ptr} (pf_tbl, pf_arr | f, null)
end // end of [the_topsegtbl_sweeplst_build]

(* ****** ****** *)

%{^

extern
chunklst_vt the_sweeplstarr[FREEITMLST_ARRAYSIZE] ;

ats_void_type
gcats2_chunk_sweeplst_build (
  ats_ptr_type p_chunk // p_chunk != NULL
) {
  chunklst_vt *p_chunklst ;
  int itmwsz_log, itmtot, mrkcnt ;
  mrkcnt = ((chunk_vt*)p_chunk)->mrkcnt ;
/*
  fprintf (stderr, "chunk_sweeplst_build: mrkcnt = %i\n", mrkcnt) ;
*/
  if (mrkcnt == 0) { // no freeitms in the chunk are used
    itmwsz_log = ((chunk_vt*)p_chunk)->itmwsz_log ;
    if (itmwsz_log >= 0) { // normal chunk
      gcats2_chunk_free_norm (p_chunk) ; // need for the_chunkpagelst_v
    } else { // large chunk // to be freed by gcats2_free_ext
      gcats2_chunk_free_large (p_chunk) ; // no need for the_chunkpagelst_v
    } // end of [if]
  } // end of [if]

  itmtot = ((chunk_vt*)p_chunk)->itmtot ;
/*
  fprintf (stderr, "chunk_sweeplst_build: itmtot = %i\n", itmtot) ;
*/
  if (mrkcnt > itmtot * CHUNK_SWEEP_CUTOFF) return ; // too many freeitms are still in use
//
  itmwsz_log = ((chunk_vt*)p_chunk)->itmwsz_log ;
/*
  fprintf (stderr, "chunk_sweeplst_build: itmwsz_log = %i\n", itmwsz_log) ;
*/
 p_chunklst = &the_sweeplstarr[itmwsz_log] ;
 ((chunk_vt*)p_chunk)->sweepnxt = *p_chunklst ; *p_chunklst = (chunklst_vt)p_chunk ;
 return ;
} // end of [chunk_sweeplst_build]

%} // end of [%{^]

(* ****** ****** *)

%{^

%} // end of [%{^]

(* ****** ****** *)

(* end of [gcats2_collecting.dats] *)
