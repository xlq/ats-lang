(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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
//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: February, 2011
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0

(* ****** ****** *)

absviewtype slseg (
  a:viewt@ype, n:int, la:addr, lz:addr
) // end of [slseg]

viewtypedef slist
  (a:viewt@ype, n:int, l:addr) = slseg (a, n, l, null)
// end of [slist]

castfn ptr_of_slseg {a:viewt@ype}
  {n:int} {la,lz:addr} (xs: !slseg (a, n, la, lz)):<> ptr (la)
overload ptr_of with ptr_of_slseg

castfn ptrnul_of_slseg
  {a:viewt@ype} {la,lz:addr} (xs: slseg (a, 0, la, lz)):<> ptr (la)
overload ptrnul_of with ptrnul_of_slseg

(* ****** ****** *)

absviewtype
slseg_node (a:viewt@ype, la:addr, lb:addr)

absviewtype
slsegopt (a:viewt@ype+, la:addr)

castfn ptr_of_slsegopt
  {a:viewt@ype} {la:addr} (x: !slsegopt (a, la)):<> ptr (la)
overload ptr_of with ptr_of_slsegopt

castfn ptrnul_of_slsegopt
  {a:viewt@ype} {la:addr} (x: slsegopt (a, null)):<> ptr (null)
overload ptrnul_of with ptrnul_of_slsegopt

(* ****** ****** *)

fun slist_make_nil {a:viewt@ype} ():<> slist (a, 0, null) // poly

fun slseg_free_nil
  {a:viewt@ype} {la,lz:addr} (xs: slseg (a, 0, la, lz)):<> void // poly
// end of [slseg_free_nil]

(* ****** ****** *)

typedef
slseg_node_alloc_type
  (a:viewt@ype) = () -<fun> [la:agez] slsegopt (a, la)
fun{a:viewt@ype} slseg_node_alloc : slseg_node_alloc_type (a)

prfun slsegopt_unsome {a:viewt@ype} {la:agz}
  (x: !slsegopt (a, la) >> slseg_node (a, la, lb)): #[lb:addr] (a? @ la | void)
// end of [slsegopt_unsome]

(* ****** ****** *)

typedef
slseg_node_free_type (a:viewt@ype) =
  {la,lb:addr} (a? @ la | slseg_node (a, la, lb)) -<fun> void
// end of [slseg_node_free_type]

fun{a:viewt@ype} slseg_node_free : slseg_node_free_type (a)

(* ****** ****** *)

fun slist_is_nil // poly
  {a:viewt@ype} {n:int} {l:addr}
  (xs: !slist (a, n, l)):<> bool (n==0) = "atspre_ptr_is_null"
// end of [slist_is_nil]

fun slist_isnot_nil // poly
  {a:viewt@ype} {n:int} {l:addr}
  (xs: !slist (a, n, l)):<> bool (n > 0) = "atspre_ptr_isnot_null"
// end of [slist_isnot_nil]

(* ****** ****** *)
//
// HX: this one must be a proof function!
//
prfun
slseg_fold
  {a:viewt@ype} {n:nat} {la,lb,lz:addr} (
  pf: a @ la
| h: !slseg_node (a, la, lb) >> slseg (a, n+1, la, lz)
, t: slseg (a, n, lb, lz)
) :<prf> void // end of [slseg_fold]

(*
prfun slseg_unfold :  this is just the proof version of [slseg_uncons]
*)

(* ****** ****** *)

typedef
slseg_cons_type
  (a:viewt@ype) =
  {n:nat} {la,lb1:addr} {lb2,lz:addr} (
  a @ la
| slseg_node (a, la, lb1), slseg (a, n, lb2, lz)
) -<fun>
  slseg (a, n+1, la, lz)
// end of [slseg_cons_type]

fun{a:viewt@ype} slseg_cons : slseg_cons_type (a) // specific

(* ****** ****** *)

typedef
slseg_uncons_type
  (a:viewt@ype) =
  {n:pos} {la,lz:addr} (
  !slseg (a, n, la, lz) >> slseg_node (a, la, lb)
) -<fun> #[lb:addr] (
  a @ la | slseg (a, n-1, lb, lz)
) // end of [slseg_uncons_type]

fun{a:viewt@ype} slseg_uncons : slseg_uncons_type (a) // specific

(* ****** ****** *)

fun{a:viewt@ype} // generic
slist_length {n:nat} {la:addr} (xs: !slist (a, n, la)):<> size_t (n)

(* ****** ****** *)

fun{a:viewt@ype} // generic
slseg_split {n,i:nat | i <= n} {la,lz:addr} (
  xs: !slseg (a, n, la, lz) >> slseg (a, i, la, lm), i: size_t (i)
) : #[lm:addr] slseg (a, n-i, lm, lz)

fun{a:viewt@ype} // generic
slist_split {n,i:nat} {la:addr} (
  xs: !slist (a, n, la) >> slseg (a, k, la, lm), i: size_t (i)
) : #[k:int;lm:addr | k==min(n,i)] slist (a, n-k, lm)

(* ****** ****** *)

fun{a:viewt@ype} // generic
slist_foreach_fun {n:nat} {l:addr}
  (xs: !slist (a, n, l), f: (&a) -<fun> void):<> void
// end of [slist_foreach_fun]

fun{a:viewt@ype} // generic
slist_foreach_clo {v:view} {n:nat} {l:addr}
  (pf: !v | xs: !slist (a, n, l), f: &(!v | &a) -<clo> void):<> void
// end of [slist_foreach_clo]

(* ****** ****** *)

fun{a:t@ype} // generic
slist_free {n:nat} {l:addr} (xs: slist (a, n, l)):<> void

fun{a:viewt@ype} // generic
slist_free_fun {n:nat} {l:addr}
  (xs: slist (a, n, l), f: (&a >> a?) -<fun> void):<> void
// end of [slist_free_fun]

(* ****** ****** *)

(* end of [slist.sats] *)
