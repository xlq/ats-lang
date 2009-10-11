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

abst@ype freeitm (wsz:int) (* size unit: word *)

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

abst@ype chunk_vt // = $extype "chunk_vt"
absviewtype chunkptr_vt (l: addr) // boxed type

// implemented in [gcats2.cats]

fun chunkptr_null ():<> chunkptr_vt null = "gcats2_chunkptr_null"

castfn chunkptr_fold
  {l:addr} (pf: chunk_vt @ l | p: !ptr l >> chunkptr_vt l):<> void
castfn chunkptr_unfold
  {l:addr | l <> null} (p: !chunkptr_vt l >> ptr l):<> (chunk_vt @ l | void)

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
fun the_topsegtbl_insert_chunkptr
  {l:addr | l <> null} (pf: !the_topsegtbl_v | p_chunk: chunkptr_vt l):<> void
  = "gcats2_the_topsegtbl_insert_chunkptr"
// end of ...

(*
** if this function fails to remove the chunkptr; it would be an irrecoverable
** error otherwise
*)
fun the_topsegtbl_remove_chunkptr
  (pf: !the_topsegtbl_v | ptr: ptr):<> [l:addr] chunkptr_vt l // notfound: l = null
  = "gcats2_the_topsegtbl_remove_chunkptr"
// end of ...

(* ****** ****** *)

fun ptr_is_valid ( // implemented in C in [gcats2_point.dats]
    pf: the_topsegtbl_v | ptr: ptr, nitm: &int? >> opt (int, l <> null)
  ) :<> #[l:addr] (
    chunkptr_vt l -<prf> the_topsegtbl_v, chunkptr_vt l
  ) = "gcats2_ptr_is_valid"
// end of [ptr_is_valid]

(* ****** ****** *)

//
// freepages are not deallocated
//

absview the_chunkpagelst_v
abst@ype freepage // = freeitm (CHUNK_WORDSIZE)

fun the_chunkpagelst_insert {l:addr} // inserting one page
  (pf: !the_chunkpagelst_v, pf_page: freepage @ l | p: ptr l):<> void
// end of [...]

fun the_chunkpagelst_remove // taking out one page
  (pf: !the_chunkpagelst_v | (*none*)):<> [l:addr] (ptropt_v (freepage, l) | ptr l)
// end of [...]

fun the_chunkpagelst_replenish
  (pf: !the_chunkpagelst_v | (*none*)):<> void // adding N pages for some N >= 1
// end of [...]

(* ****** ****** *)

(* end of [gcats2.sats] *)
