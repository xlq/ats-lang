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
    pf: !the_chunkpagelst_v | itmwsz: int, itmwsz_log: int i
  ) :<> [l:anz] chunkptr_vt l
  = "gcats2_chunk_make_norm"

// implemented in [gcats2_chunk.dats]
fun chunk_free_norm {l:anz}
  (pf: !the_chunkpagelst_v | p_chunk: chunkptr_vt l):<> void
  = "gcats2_chunk_free_norm"

// implemented in [gcats2_chunk.dats]
fun chunk_make_large (itmwsz: int):<> [l:anz] chunkptr_vt l
  = "gcats2_chunk_make_large"

// implemented in [gcats2_chunk.dats]
fun chunk_free_large {l:anz} (p_chunk: chunkptr_vt l):<> void
  = "gcats2_chunk_free_large"

// implemented in [gcats2.cats]
fun chunk_make_null ():<> chunkptr_vt null = "gcats2_chunk_make_null"
fun chunk_free_null (p: chunkptr_vt null):<> void = "gcats2_chunk_free_null"

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
    pf1: !the_topsegtbl_v, pf2: !v
  | f: {l:anz} (!v | !chunkptr_vt l, !vt) -<fun> void, env: !vt
  ) :<> void
  = "gcats2_the_topsegtbl_foreach_chunkptr"
// end of ...

// implemented in ATS in [gcats2_chunk.dats]
fun the_topsegtbl_clear_mrkbits (pf: !the_topsegtbl_v | (*none*)):<> void

(* ****** ****** *)

absview the_markstackpagelst_v

// implemented in [gcats2_marking.dats]
fun the_markstackpagelst_length
  (pf: !the_markstackpagelst_v | (*none*)):<> int // > 0
  = "gcats2_the_markstackpagelst_length" // implemented in C
// end of ...

// implemented in [gcats2_marking.dats]
fun the_markstackpagelst_pop (
    pf: !the_markstackpagelst_v | p: &ptr? >> ptr, wsz: &size_t? >> size_t
  ) :<> void
  = "gcats2_the_markstackpagelst_pop" // implemented in C
// end of ...

// implemented in [gcats2_marking.dats]
fun the_markstackpagelst_push
  (pf: !the_markstackpagelst_v | p: ptr, wsz: size_t, overflow: &int):<> void
  = "gcats2_the_markstackpagelst_push" // implemented in C
// end of ...

// implemented in [gcats2_marking.dats]
fun the_markstackpagelst_extend {n:nat}
  (pf: !the_markstackpagelst_v | n: int n):<> void
  = "gcats2_the_markstackpagelst_extend" // implemented in C
// end of ...

fun ptr_mark
  (pf1: !the_topsegtbl_v, pf2: !the_markstackpagelst_v | ptr: ptr):<> int
  = "gcats2_ptr_mark"
// end of ...

(* ****** ****** *)

(* end of [gcats2.sats] *)
