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

absviewtype slseg_node (a:viewt@ype, la:addr, lb:addr)

viewtypedef slist
  (a:viewt@ype, n:int, l:addr) = slseg (a, n, l, null)
// end of [slist]

(* ****** ****** *)

castfn ptr_of_slseg
  {a:viewt@ype} {n:int} {la,lz:addr} (xs: !slseg (a, n, la, lz)):<> ptr (la)
overload ptr_of with ptr_of_slseg

(* ****** ****** *)

fun slseg_free_nil
  {a:viewt@ype} {la,lz:addr} (xs: slseg (a, 0, la, lz)): void
// end of [slseg_free_nil]

(* ****** ****** *)

fun slseg_node_free
  {a:viewt@ype} {la,lb:addr}
  (pf: a? @ la | xs: slseg_node (a, la, lb)): void
// end of [slseg_node_free]

(* ****** ****** *)

fun slist_is_nil
  {a:viewt@ype} {n:nat} {l:addr}
  (xs: !slist (a, n, l)):<> bool (n==0) = "atspre_ptr_is_null"
// end of [slist_is_nil]

fun slist_isnot_nil
  {a:viewt@ype} {n:nat} {l:addr}
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

(* ****** ****** *)

fun{a:viewt@ype}
slseg_cons {n:nat} {la,lb1:addr} {lb2,lz:addr} (
  pf: a @ la
| h: !slseg_node (a, la, lb1) >> slseg (a, n+1, la, lz), t: slseg (a, n, lb2, lz)
) :<> void // end of [slseg_cons]

fun{a:viewt@ype}
slseg_uncons {n:pos} {la,lz:addr} (
  xs: !slseg (a, n, la, lz) >> slseg_node (a, la, lb)
) :<> #[lb:addr] (a @ la | slseg (a, n-1, lb, lz)) // end of [slseg_uncons]

(* ****** ****** *)

fun{a:viewt@ype}
slist_foreach_clo {v:view} {n:nat} {l:addr}
  (pf: !v | xs: !slist (a, n, l), f: &(!v | &a) -<clo> void):<> void
// end of [slist_foreach_clo]

(* ****** ****** *)

(* end of [slist.sats] *)
