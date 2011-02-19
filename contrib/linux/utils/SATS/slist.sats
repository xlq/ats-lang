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
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
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

absviewtype slist
  (a:viewt@ype, n:int, l:addr) = ptr
absviewtype slist_head (a:viewt@ype, l0:addr, l1:addr)

(* ****** ****** *)

castfn ptr_of_slist
  {a:viewt@ype} {n:int} {l:addr} (xs: !slist (a, n, l)):<> ptr (l)
overload ptr_of with ptr_of_slist

castfn ptr_of_slist_head
  {a:viewt@ype} {l0,l1:addr} (xs: !slist_head (a, l0, l1)):<> ptr (l0)
overload ptr_of with ptr_of_slist_head

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
slist_fold
  {a:viewt@ype} {n:nat} {l0,l1:addr} (
  pf: a @ l0
| h: !slist_head (a, l0, l1) >> slist (a, n+1, l0), t: slist (a, n, l1)
) :<prf> void // end of [slist_fold]

(* ****** ****** *)

fun{a:viewt@ype}
slist_cons {n:nat} {l0,l1:addr} {l2:addr} (
  pf: a @ l0
| h: !slist_head (a, l0, l1) >> slist (a, n+1, l0), t: slist (a, n, l2)
) :<> void // end of [slist_cons]

fun{a:viewt@ype}
slist_uncons {n:pos} {l0:addr} (
  xs: !slist (a, n, l0) >> slist_head (a, l0, l1)
) :<> #[l1:addr] (a @ l0 | slist (a, n-1, l1)) // end of [slist_uncons]

(* ****** ****** *)

fun{a:viewt@ype}
slist_foreach_clo {v:view} {n:nat} {l:addr}
  (pf: !v | xs: !slist (a, n, l), f: (!v | &a) -<clo> void):<> void
// end of [slist_foreach_clo]

(* ****** ****** *)

(* end of [slist.sats] *)
