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

%{#
#include "gcats2.cats"
%}

(* ****** ****** *)

#include "gcats2_ats.hats"

(* ****** ****** *)

fun mystackdir_get (): int = "gcats2_mystackdir_get"
fun mystackbeg_set (dir: int): void = "gcats2_mystackbeg_set"
fun mystackbeg_get (): ptr = "gcats2_mystackbeg_get"

(* ****** ****** *)

abst@ype freeitm_t // size_t(freeitm) >= 1
absviewtype freeitmlst_vt (l:addr) // boxed type

// implemented in [gcats2_freeitmlst]
fun freeitmlst_length {l:addr} (xs: !freeitmlst_vt l):<> int
  = "gcats2_freeitmlst_length" // implemented in ATS
// end of [freeitmlst_length]

fun freeitmlst_is_nil {l:addr} (xs: !freeitmlst_vt l):<> bool (l==null)
  = "gcats2_freeitmlst_isnil"
fun freeitmlst_is_cons {l:addr} (xs: !freeitmlst_vt l):<> bool (l <> null)
  = "gcats2_freeitmlst_iscons"

fun freeitmlst_cons {l1,l2:addr}
  (pf: freeitm_t @ l1 | x: ptr l1, xs: freeitmlst_vt l2): freeitmlst_vt l1
  = "gcats2_freeitmlst_cons"
// end of [freeitmlst_cons]

fun freeitmlst_uncons {l:anz}
  (xs: &freeitmlst_vt l >> freeitmlst_vt l_new):<> #[l_new:addr] (freeitm_t @ l | ptr l)
  = "gcats2_freeitmlst_uncons"
// end of [freeitmlst_uncons]

castfn freeitmlst_make_null (p: ptr null):<> freeitmlst_vt null
castfn freeitmlst_free_null (xs: freeitmlst_vt null):<> ptr null

(* ****** ****** *)

(*
** implemented in [gcats2.cats]
*)

abst@ype topseg (i:int) = uintptr
castfn uintptr_of_topseg {i:int} (x: topseg i): uintptr

fun PTR_TOPSEG_GET (p: ptr):<> [i:nat] topseg i
  = "PTR_TOPSEG_GET"

fun PTR_BOTSEG_GET (p: ptr):<> natLt (BOTSEG_TABLESIZE)
  = "PTR_BOTSEG_GET"

fun PTR_CHKSEG_GET (p: ptr):<> natLt (CHKSEG_TABLESIZE)
  = "PTR_CHKSEG_GET"

#if (__WORDSIZE == 64) #then
// for the purpose of testing/debugging
fun PTR_TOPSEGHASH_GET (p: ptr):<> [i:nat] topseg i
  = "PTR_TOPSEGHASH_GET"
#endif // end of [#if (__WORDSIZE == 64)]

(* ****** ****** *)

absview the_totwsz_v

(* ****** ****** *)

//
// freepages are not deallocated
//

absview the_chunkpagelst_v
abst@ype freepage // = freeitm (CHUNK_WORDSIZE)

fun the_chunkpagelst_length
  (pf: !the_chunkpagelst_v | (*none*)):<> int
  = "gcats2_the_chunkpagelst_length" // implemented in C

fun the_chunkpagelst_insert {l:addr} // inserting one page
  (pf: !the_chunkpagelst_v, pf_page: freepage @ l | p: ptr l):<> void
  = "gcats2_the_chunkpagelst_insert" // implemented in C
// end of [...]

fun the_chunkpagelst_remove // taking out one page
  (pf: !the_chunkpagelst_v | (*none*)):<> [l:anz] (freepage @ l | ptr l)
  = "gcats2_the_chunkpagelst_remove" // implemented in ATS
// end of [...]

fun the_chunkpagelst_remove_opt // taking out one page
  (pf: !the_chunkpagelst_v | (*none*)):<> [l:addr] (ptropt_v (freepage, l) | ptr l)
  = "gcats2_the_chunkpagelst_remove_opt" // implemented in C
// end of [...]

// on success, [n] is returned; on failure
fun the_chunkpagelst_replenish {n:pos} // [-1] is returned
  (pf: !the_chunkpagelst_v | n: int n):<> int // adding n pages for some n >= 1
  = "gcats2_the_chunkpagelst_replenish" // implemented in C via mmap
// end of [...]

(* ****** ****** *)

abst@ype chunk_vt // = $extype "chunk_vt"

fun chunk_data_get (chk: &chunk_vt):<> ptr = "gcats2_chunk_data_get"
fun chunk_mrkbits_clear (chk: &chunk_vt):<> void = "gcats2_chunk_mrkbits_clear"

absviewtype chunkptr_vt (l: addr) // boxed type
castfn ptr_of_chunkptr {l:addr} (p: !chunkptr_vt l):<> ptr l

castfn chunkptr_fold
  {l:addr} (pf: chunk_vt @ l | p: !ptr l >> chunkptr_vt l):<> ptr l
castfn chunkptr_unfold
  {l:addr | l <> null} (p: !chunkptr_vt l >> ptr l):<> (chunk_vt @ l | ptr l)

// implemented in [gcats2_chunk.dats]
fun chunk_make_norm {i:nat} (
    pf1: !the_totwsz_v
  , pf2: !the_chunkpagelst_v
  | itmwsz: int, itmwsz_log: int i
  ) :<> [l:anz] chunkptr_vt l
  = "gcats2_chunk_make_norm"

// implemented in [gcats2_chunk.dats]
fun chunk_free_norm {l:anz} (
    pf1: !the_totwsz_v, pf2: !the_chunkpagelst_v | p_chunk: chunkptr_vt l
  ) :<> void
  = "gcats2_chunk_free_norm"

// implemented in [gcats2_chunk.dats]
fun chunk_make_large
  (pf: !the_totwsz_v | itmwsz: size_t):<> [l:anz] chunkptr_vt l
  = "gcats2_chunk_make_large"

// implemented in [gcats2_chunk.dats]
fun chunk_free_large {l:anz}
  (pf: !the_totwsz_v | p_chunk: chunkptr_vt l):<> void
  = "gcats2_chunk_free_large"

// implemented in [gcats2.cats]
fun chunk_make_null ():<> chunkptr_vt null = "gcats2_chunk_make_null"
fun chunk_free_null (p: chunkptr_vt null):<> void = "gcats2_chunk_free_null"

// implemented in [gcats2_chunk.dats]
fun chunk_add_freeitmlst {l:addr}
  (chk: &chunk_vt, xs: freeitmlst_vt l):<> [l:addr] freeitmlst_vt l
  = "gcats2_chunk_add_freeitmlst"
// end of ...

(* ****** ****** *)

absview the_topsegtbl_v

// it is implemented in [gcats2_top.dats]
fun the_topsegtbl_initialize (pf: !the_topsegtbl_v | (*none*)):<> void
  = "gcats2_the_topsegtbl_initialize"

(* ****** ****** *)

(*
** [botsegtbl_vt] depends on __WORDSIZE:
*)
absviewt@ype botsegtbl_vt = $extype "botsegtbl_vt"
absviewtype botsegtblptr_vt (l:addr) // this is a boxed type
viewtypedef botsegtblptr_vt = [l:addr] botsegtblptr_vt (l)

castfn botsegtblptr_free_null (_: botsegtblptr_vt null): ptr

fun the_nbotsegtbl_alloc_get ():<> lint // for gathering statistics
  = "gcats2_the_nbotsegtbl_alloc_get"

(* ****** ****** *)

fun the_topsegtbl_takeout {i:nat} (
    pf: the_topsegtbl_v | i: topseg i
  ) :<> [l:addr] (
    botsegtblptr_vt @ l, botsegtblptr_vt @ l -<lin> the_topsegtbl_v | ptr l
  ) = "gcats2_the_topsegtbl_takeout"
// end of [the_topsegtbl_takeout]

(*
** this function may call [malloc_ext] to allocate a new botsegtbl; if so, the
** new botsegtbl is always added at the beginning
*)
fun the_topsegtbl_insert_chunkptr // succ/fail: 0/1
  {l:addr | l <> null} (pf: !the_topsegtbl_v | p_chunk: chunkptr_vt l):<> int(*err*)
  = "gcats2_the_topsegtbl_insert_chunkptr"
// end of ...

(*
** if this function fails to remove the chunkptr, it would be an irrecoverable error
** note that [ptr==p_chunk->chunk_data] where [p_chunk] is to be removed
*)
fun the_topsegtbl_remove_chunkptr
  (pf: !the_topsegtbl_v | ptr: ptr):<> [l:addr] chunkptr_vt l // notfound: l = null
  = "gcats2_the_topsegtbl_remove_chunkptr"
// end of ...

(* ****** ****** *)

fun ptr_isvalid ( // implemented in C in [gcats2_point.dats]
    pf: the_topsegtbl_v | ptr: ptr, nitm: &int? >> opt (int, l <> null)
  ) :<> #[l:addr] (
    chunkptr_vt l -<prf> the_topsegtbl_v | chunkptr_vt l
  ) = "gcats2_ptr_isvalid"
// end of [ptr_isvalid]

(* ****** ****** *)

// implemented in C in [gcats2_chunk.dats]
fun the_topsegtbl_foreach_chunkptr
  {v:view} {vt:viewtype} (
    pf1: !the_topsegtbl_v, pf2: !v // or assuming [the_topsegtbl_v <= v]
  | f: {l:anz} (!the_topsegtbl_v, !v | !chunkptr_vt l, !vt) -<fun> void, env: !vt
  ) :<> void
  = "gcats2_the_topsegtbl_foreach_chunkptr"
// end of ...

// implemented in ATS in [gcats2_chunk.dats]
fun the_topsegtbl_clear_mrkbits (pf: !the_topsegtbl_v | (*none*)):<> void

(* ****** ****** *)

absview the_globalrts_v

fun the_globalrts_insert (
    pf: !the_globalrts_v | ptr: ptr, wsz: size_t
  ) :<> void
  = "gcats2_the_globalrts_insert" // implemented in C
// end of ...

(* ****** ****** *)

abst@ype manmem_vt // unboxed type
fun manmem_data_get (itm: &manmem_vt):<> ptr = "gcats2_manmem_data_get"

fun manmem_make // bsz: number of bytes
  (bsz: size_t):<> [l:addr] (manmem_vt @ l | ptr l)
  = "gcats2_manmem_make"
// end of ...

fun manmem_free {l:addr}
  (pf: manmem_vt @ l | p: ptr l):<> void
  = "gcats2_manmem_free"
// end of ...

absview the_manmemlst_v

fun the_manmemlst_length
  (pf: !the_manmemlst_v | (*none*)):<> int
  = "gcats2_the_manmemlst_length" // mostly for gathering some statistic info
// end of ...

fun the_manmemlst_insert {l:addr}
  (pf: !the_manmemlst_v, pf2: manmem_vt @ l | p: ptr l):<> void
  = "gcats2_the_manmemlst_insert"
// end of ...

fun the_manmemlst_remove // [p] must be in the_manmemlst!
  (pf: !the_manmemlst_v | p: ptr):<> [l:addr] (manmem_vt @ l | ptr l)
  = "gcats2_the_manmemlst_remove"
// end of ...

(* ****** ****** *)

absview the_markstack_v

// implemented in [gcats2_marking.dats]
fun the_markstackpagelst_length
  (pf: !the_markstack_v | (*none*)):<> int // > 0
  = "gcats2_the_markstackpagelst_length" // implemented in C
// end of ...

// implemented in [gcats2_marking.dats]
fun the_markstackpagelst_pop (
    pf: !the_markstack_v | p: &ptr? >> ptr, wsz: &size_t? >> size_t
  ) :<> void
  = "gcats2_the_markstackpagelst_pop" // implemented in C
// end of ...

// implemented in [gcats2_marking.dats]
fun the_markstackpagelst_push
  (pf: !the_markstack_v | p: ptr, wsz: size_t, overflow: &int):<> void
  = "gcats2_the_markstackpagelst_push" // implemented in C
// end of ...

// implemented in [gcats2_marking.dats]
fun the_markstackpagelst_extend {n:nat}
  (pf: !the_markstack_v | n: int n):<> void
  = "gcats2_the_markstackpagelst_extend" // implemented in C
// end of ...

(* ****** ****** *)

// implemented in [gcats2_marking]
fun freeitmlst_mark {l:addr}
  (pf: !the_topsegtbl_v | xs: !freeitmlst_vt l):<> void
  = "gcats2_freeitmlst_mark"
// end of ...

// implemented in [gcats2_marking]
fun ptr_mark (
    pf1: !the_topsegtbl_v, pf2: !the_markstack_v | ptr: ptr
  ) :<> int(*overflow*)
  = "gcats2_ptr_mark"
// end of ...

// implemented in [gcats2_marking]
fun ptrsize_mark (
    pf1: !the_topsegtbl_v, pf2: !the_markstack_v | ptr: ptr, wsz: size_t
  ) :<> int(*overflow*)
  = "gcats2_ptrsize_mark"
// end of ...

// implemented in [gcats2_marking]
fun chunk_mark (
    pf1: !the_topsegtbl_v, pf2: !the_markstack_v | chk: &chunk_vt
  ) :<> int(*overflow*)
  = "gcats2_chunk_mark"
// end of ...

// implemented in [gcats2_marking]
fun mystack_mark ():<> int(*overflow*) = "gcats2_mystack_mark"

(* ****** ****** *)

// this view contains contains
absview the_GCmain_v // the resources for performing GC

(*
prfun the_topsegtbl_v_takeout (pf: the_GCmain_v)
  : (the_topsegtbl_v, the_topsegtbl_v -<lin,prf> the_GCmain_v)
// end of [the_topsegtbl_v_takeout]

prfun the_globalrts_v_takeout (pf: the_GCmain_v)
  : (the_globalrts_v, the_globalrts_v -<lin,prf> the_GCmain_v)
// end of [the_globalrts_v_takeout]

prfun the_manmemlst_v_takeout (pf: the_GCmain_v)
  : (the_manmemlst_v, the_manmemlst_v -<lin,prf> the_GCmain_v)
// end of [the_manmemlst_v_takeout]

prfun the_markstack_v_takeout (pf: the_GCmain_v)
  : (the_markstack_v, the_markstack_v -<lin,prf> the_GCmain_v)
// end of [the_markstack_v_takeout]
*)

// implemented in [gcats2_mark.dats]
fun the_topsegtbl_mark
  (pf1: !the_GCmain_v | (*none*)):<> int(*overflow*)
// end of ...

// implemented in [gcats2_globalrts.dats]
fun the_globalrts_mark
  (pf: !the_GCmain_v | (*none*)) :<> int(*overflow*)
  = "gcats2_the_globalrts_mark"

// implemented in [gcats2_manmem.dats]
fun the_manmemlst_mark
  (pf: !the_GCmain_v | (*none*)) :<> int(*overflow*)
  = "gcats2_the_manmemlst_mark"

// implemented in [gcats2_marking.dats]
fun the_GCmain_mark // [overflowed] determines if [markstack] needs
  (pf: !the_GCmain_v | (*none*)):<> int(*overflowed*) // to be extended

(* ****** ****** *)

absview the_sweeplstarr_v

// implemented in [gcats2_collecting.dats]
fun chunk_sweeplst_build (pf: !the_sweeplstarr_v | chk: &chunk_vt):<> void
  = "gcats2_chunk_sweeplst_build"

// implemented in [gcats2_collecting.dats]
fun the_topsegtbl_sweeplst_build
  (pf_tbl: !the_topsegtbl_v, pf_arr: !the_sweeplstarr_v | (*none*)):<> void

(* ****** ****** *)

(* end of [gcats2.sats] *)
