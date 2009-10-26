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

// #include "gcats2_ats.hats"

(* ****** ****** *)

#define ATSCCOMP_NAMESPACE "gcats2_collecting_"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

(*
fun the_topsegtbl_sweeplst_build (
    pf_tbl: !the_topsegtbl_v, pf_arr: !the_sweeplstarr_v, pf_lst: the_chunkpagelst_v
  | (*none*)
  ) :<> void
// end of [the_topsegtbl_sweeplst_build]
*)
implement the_topsegtbl_sweeplst_build
  (pf_tbl, pf_arr, pf_lst | (*none*)) = let
//
  val () = the_sweeplstarr_clear (pf_arr | (*none*))
//
  viewdef tbl_v = the_topsegtbl_v
  viewdef arrlst_v = (the_sweeplstarr_v, the_chunkpagelst_v)
  extern fun chunk_sweeplst_build
    (pf1: !tbl_v, pf2: !arrlst_v | chk: &chunk_vt):<> void
    = "gcats2_chunk_sweeplst_build"
  val f = lam {l:anz} (
      pf1: !tbl_v, pf2: !arrlst_v | p_chunk: !chunkptr_vt l, env: !ptr
    ) : void =<fun> let
    val (pf_chunk | p) = chunkptr_unfold (p_chunk)
    val () = chunk_sweeplst_build (pf1, pf2 | !p)
    val _(*ptr*) = chunkptr_fold (pf_chunk | p_chunk)
  in
    // nothing
  end // end of [val f]
  prval pf_arrlst = (pf_arr, pf_lst)
  val () = the_topsegtbl_foreach_chunkptr {arrlst_v} {ptr} (pf_tbl, pf_arrlst | f, null)
  prval () = pf_arr := pf_arrlst.0 and () = pf_lst := pf_arrlst.1
in
  // nothing
end // end of [the_topsegtbl_sweeplst_build]

(* ****** ****** *)

extern
fun the_totwsz_limit_is_reached // the function checks if
  (pf: !the_gcmain_v | (*none*)):<> bool // the_totwsz >= the_totwsz_limt
  = "gcats2_the_totwsz_limit_is_reached"

implement the_freeitmlstarr_replenish
  (pf_the_gcmain | itmwsz_log) = let // [itmwsz_log >= 0] is assumed
  prval (pf, fpf) = the_sweeplstarr_v_takeout (pf_the_gcmain)
  val p_chunk = the_sweeplstarr_get_chunk (pf | itmwsz_log)
(*
  val () = $effmask_all begin
    prerr("the_freeitmlstarr_replenish: p_chunk =\n"); fprint_chunk(stderr_ref, p_chunk)
  end // end of [val]
*)
  prval () = pf_the_gcmain := fpf (pf)
in
  if chunkptr_is_null (p_chunk) then let
    val _(*ptr*) = chunk_free_null (p_chunk) // no-op casting
    val limit_is_reached = the_totwsz_limit_is_reached (pf_the_gcmain | (*none*))
  in
    if limit_is_reached then let
(*
      val () = $effmask_all let
        val () = fprint (stderr_ref, "gc_main starts: the_topsegtbl =\n")
        val () = fprint_the_topsegtbl (stderr_ref)
      in
        // nothing
      end // end of [val]
*)
      val () = gcmain_run (pf_the_gcmain | (*none*))
(*
      val () = $effmask_all let
        val () = fprint (stderr_ref, "gc_main finishes: the_topsegtbl =\n")
        val () = fprint_the_topsegtbl (stderr_ref)
      in
        // nothing
      end // end of [val]
*)
    in
      the_freeitmlstarr_replenish (pf_the_gcmain | itmwsz_log)
    end else let
      // totwsz_limit is not reached // a new chunkpage can be obtained
      viewdef V1 = the_totwsz_v
      viewdef V2 = the_chunkpagelst_v
      prval (
        pf1, pf2, fpf
      ) = __takeout (pf_the_gcmain) where {
        extern prfun __takeout
          (pf: the_gcmain_v): (V1, V2, (V1, V2) -<lin,prf> the_gcmain_v)
      } // end of [prval]
      val itmwsz = size_of_uint (1U << itmwsz_log)
      val [l_chunk:addr] p_chunk = chunk_make_norm (pf1, pf2 | itmwsz, itmwsz_log)
      prval () = pf_the_gcmain := fpf (pf1, pf2)
      val p1_chunk = __cast (p_chunk) where {
        extern castfn __cast (p_chunk: !chunkptr_vt l_chunk):<> chunkptr_vt l_chunk
      }
      prval (pf, fpf) = the_topsegtbl_v_takeout (pf_the_gcmain)
      val _(*err*) = the_topsegtbl_insert_chunkptr (pf | p_chunk)
      prval () = pf_the_gcmain := fpf (pf)
    in
      the_freeitmlstarr_add_chunk (p1_chunk, itmwsz_log) // new chunk is allocated
    end // end of [if]
  end else begin// p_chunk <> null
    the_freeitmlstarr_add_chunk (p_chunk, itmwsz_log) // chunk is immediately available
  end // end of [if]
end // end of [the_freeitmlstarr_replenish]

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
  fprintf(stderr, "chunk_sweeplst_build: mrkcnt = %i\n", mrkcnt) ;
*/
  if (mrkcnt == 0) { // no freeitms in the chunk are used
    itmwsz_log = ((chunk_vt*)p_chunk)->itmwsz_log ;
//
    gcats2_the_topsegtbl_remove_chunkptr(((chunk_vt*)p_chunk)->chunk_data) ;
//
    if (itmwsz_log >= 0) { // normal chunk
      gcats2_chunk_free_norm(p_chunk) ; // need for the_chunkpagelst_v
    } else { // large chunk // to be freed by gcats2_free_ext
      gcats2_chunk_free_large(p_chunk) ; // no need for the_chunkpagelst_v
    } // end of [if]
    return ;
  } // end of [if]

  itmtot = ((chunk_vt*)p_chunk)->itmtot ;
/*
  fprintf(stderr, "chunk_sweeplst_build: itmtot = %i\n", itmtot) ;
*/
  if (mrkcnt > itmtot * CHUNK_SWEEP_CUTOFF)
    return ; // too many free items are still in use
//
  itmwsz_log = ((chunk_vt*)p_chunk)->itmwsz_log ;
/*
  fprintf(stderr, "chunk_sweeplst_build: itmwsz_log = %i\n", itmwsz_log) ;
*/
 p_chunklst = &the_sweeplstarr[itmwsz_log] ;
 ((chunk_vt*)p_chunk)->sweepnxt = *p_chunklst ; *p_chunklst = (chunklst_vt)p_chunk ;
 return ;
} // end of [gcats2_chunk_sweeplst_build]

%} // end of [%{^]

(* ****** ****** *)

%{^

/*
fun gcmain_run (pf: !the_gcmain_v | (*none*)):<> void = "gcats2_gcmain_run"
*/

extern
void gcats2_the_threadinfolst_restart() ;

ats_void_type
gcats2_gcmain_run (
  // a proof of [the_gcmain_v] is needed
) {
  int overflowed ; int nmarkstackpage ;
  jmp_buf reg_save ; // register contents are potential GC roots
#if (_ATS_MULTITHREAD)
  // threadinfolst infolst ; int nother ;
#endif // end of [_ATS_MULTITHREAD]
//
  nmarkstackpage = // this is just an estimate
    the_totwsz / (MARKSTACK_PAGESIZE * NCHUNK_PER_MARKSTACKPAGE) ;
  nmarkstackpage -= gcats2_the_markstackpagelst_length() ;
/*
  fprintf(stderr, "gcats2_gcmain_run: nmarkstackpage = %i\n", nmarkstackpage) ;
*/
  if (nmarkstackpage > 0) gcats2_the_markstackpagelst_extend(nmarkstackpage) ;
//
#if (_ATS_MULTITHREAD)
  gcats2_the_threadinfolst_lock_acquire() ; gcats2_the_threadinfolst_suspend() ;
#endif // end of [_ATS_MULTITHREAD]
//
  gcats2_the_topsegtbl_clear_mrkbits() ;
//
  setjmp(reg_save) ; // push registers onto the stack
  asm volatile ("": : :"memory") ; // prevent potential optimization ;
//
  // both the_gcmain_v and the_threadinfolst_v
  overflowed = gcats2_the_gcmain_mark() ; // are held at this point
//
#if (_ATS_MULTITHREAD)
  gcats2_the_threadinfolst_restart() ; gcats2_the_threadinfolst_lock_release () ;
#endif // end of [_ATS_MULTITHREAD]
//
  if (overflowed > 0) {
    gcats2_the_markstackpagelst_extend(NMARKSTACKPAGE_OVERFLOW_EXTEND) ;
  } // end of [if]
//
  gcats2_the_freeitmlstarr_unmark() ; // this clears up the_freeitmlstarr
//
  gcats2_the_topsegtbl_sweeplst_build() ;
//
  if (the_totwsz_limit_max > 0) {
    // [the_totwsz_limit_max==0] means infinite
    if (the_totwsz_limit >= the_totwsz_limit_max) {
      fprintf(stderr, // memory thrashing is imminent
        "warning(ATS/GC): the maximal word limit (%u) is reached.\n", the_totwsz_limit
      ) ;
      return ;
    } // end of [if]
  } // end of [if]
//
  if (the_totwsz >= the_totwsz_limit * TOTWSZ_LIMIT_EXTEND_CUTOFF)
    the_totwsz_limit *= 2 ;
  // end of [if]
//
  return ;
} // end of [gcats2_gcmain_run]

%} // end of [%{^]

(* ****** ****** *)

(* end of [gcats2_collecting.dats] *)
