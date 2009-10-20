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
// Time: October 2009

(* ****** ****** *)

%{^
#include "libc/CATS/string.cats" // for [memset]
%}

(* ****** ****** *)

#define ATS_FUNCTION_NAME_PREFIX "gcats2_autmem_"

(* ****** ****** *)

#include "gcats2_ats.hats"

(* ****** ****** *)

staload "gcats2.sats"

(* ****** ****** *)

%{^
static inline
ats_int_type gcats2_log2_ceil (
  ats_size_type n0 // [n0 > 0] is assumed
) {
  int n, c ;
  c = 0 ; n = n0 - 1 ; while (n) { c += 1 ; n >>= 1 ; }
#if (GCATS2_TEST > 0)
  if (n0 > (1 << c) || (c > 0 && n0 <= (1 << (c-1)))) {
    fprintf(stderr, "log2_ceil: n0 = %lu and c = %i\n", (ats_ulint_type)n0, c) ;
    exit(1) ;
  } // end of [if]
#endif // end of [GCATS2_TEST]
  return c ;
} // end of [log2_ceil]
%}

extern
fun log2_ceil {n:pos} (n: size_t n):<> int = "gcats2_log2_ceil"

(* ****** ****** *)

implement autmem_malloc_bsz (bsz) = let
  val bsz = size1_of_size (bsz) // no-op casting
  val wsz = (bsz + NBYTE_PER_WORD_MASK) >> NBYTE_PER_WORD_LOG
  val [n:int] wsz = size1_of_size (wsz) // no-op casting
  prval () = __assert () where {
    extern prfun __assert (): [n > 0] void // since [bsz > 0]
  }
in
  autmem_malloc_wsz (wsz)
end // end of [autmem_malloc_wsz]

implement autmem_calloc_bsz (n, bsz) = let
  val (pf_mul | nbsz) = mul2_size1_size1 (n, bsz)
  prval MULind pf1_mul = pf_mul
  prval () = mul_nat_nat_nat (pf1_mul)
  val ptr = autmem_malloc_bsz (nbsz)
  val _(*ptr*) = __memset (ptr, 0, nbsz) where {
    extern fun __memset (_: ptr, _: int, _: size_t):<> ptr = "atslib_memset"
  } // end of [val]
in
  ptr
end // end of [autmem_calloc_bsz]

(* ****** ****** *)

implement autmem_malloc_wsz (wsz) = let
(*
  val () = begin
    prerr "autmem_malloc_wsz: wsz = "; prerr wsz; prerr_newline ()
  end // end of [val]
*)
//
  #assert (FREEITMLST_ARRAYSIZE == MAX_CLICK_WORDSIZE_LOG + 1)
//
  val itmwsz_log = (
    if wsz > MAX_CLICK_WORDSIZE then ~1 else log2_ceil (wsz)
  ) : int
  val [i:int] itmwsz_log = int1_of_int (itmwsz_log)
  prval () = __assert () where {
    extern prfun __assert (): [~1 <= i; i < FREEITMLST_ARRAYSIZE] void
  }
in
  case+ 0 of
  | _ when itmwsz_log >= 0 => let
      var p_itm: ptr =
        the_freeitmlstarr_get_freeitm (itmwsz_log)
      val () = if (p_itm = null) then let
        val () = the_freeitmlstarr_replenish (itmwsz_log) // GC may be triggered
        val () = p_itm := the_freeitmlstarr_get_freeitm (itmwsz_log)
        val () = $effmask_all (
          if (p_itm = null) then let
            val () = begin
              prerr "exit(ATS/GC): GC failed to reclaim more memory for allocation.";
              prerr_newline ()
            end // end of [val]
          in
            exit (1)
          end // end of [if]
        ) // end of [val]
      in
        // nothing
      end // end of [val]
    in
      p_itm // [p_itm] <> null
    end // end of [_ when ...]
  | _ => let // [itmwsz_log = -1] // large chunk
      val () = $effmask_all (assert_errmsg (false, #LOCATION)) in null
    end // end of [_]
end // end of [gc_aut_malloc_wsz]

(* ****** ****** *)

%{$

ats_void_type
gcats2_autmem_free (
  ats_ptr_type p_itm // [p_itm] is assumed to be valid
) {
  int ofs_chkseg ;
  int itmwsz_log ;
  chunk_vt *p_chunk ;
  freeitmlst_vt *p_itmlst ;
//
  p_chunk = (chunk_vt*)gcats2_ptr_isvalid(p_itm, &ofs_chkseg) ;
//
#if (GCATS2_DEBUG > 0)
  if (!p_chunk) {
    fprintf(stderr, "INTERNAL ERROR") ;
    fprintf(stderr, ": exit(ATS/GC): gcats2_autmem_free: p_itm = %p\n", p_itm) ;
    exit(1) ;
  } // end of [if]
#endif // end of [GCATS2_DEBUG]
//
  itmwsz_log = ((chunk_vt*)p_chunk)->itmwsz_log ;
//  
  if (itmwsz_log >= 0) {
    p_itmlst = &the_freeitmlstarr[itmwsz_log] ;
    *(freeitmlst_vt*)p_itm = *p_itmlst ; *p_itmlst = (freeitmlst_vt)p_itm ;
  } else { // itmwsz_log = -1 // itmtot = 1
    // the_gcmain_v needs to be acquired in order to free the item immediately
  } // end of [if]
//
  return ;
} // end of [gcats2_autmem_free]

%} // end of [%{$]

(* ****** ****** *)

(* end of [gcats2_autmem.dats] *)
