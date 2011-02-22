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
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
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
// Time: December, 2010
//
(* ****** ****** *)
//
// HX: generic fully indexed linear lists (linear gflists)
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // there is no need for staloading at run-time

(* ****** ****** *)

staload "libats/SATS/ilistp.sats" // for handling integer sequences

(* ****** ****** *)

absviewt@ype
elt (a:viewt@ype, x:int) = a

dataviewtype
gflist_vt (a:viewt@ype, ilist) =
  | {x:int} {xs:ilist}
    gflist_vt_cons (a, ilist_cons (x, xs)) of (elt (a, x), gflist_vt (a, xs))
  | gflist_vt_nil (a, ilist_nil) of ()
// end of [gflist_vt]

(* ****** ****** *)

prfun list_vt_of_gflist_vt {a:viewt@ype} {xs:ilist}
  (xs: !gflist_vt (a, xs) >> list_vt (a, n)): #[n:nat] LENGTH (xs, n)
// end of [list_of_gflist_vt]

prfun gflist_vt_of_list_vt {a:viewt@ype} {n:int}
  (xs: !list_vt (a, n) >> gflist_vt (a, xs)): #[xs:ilist] LENGTH (xs, n)
// end of [gflist_vt_of_list]

(* ****** ****** *)

fun{a:viewt@ype}
gflist_vt_length {xs:ilist}
  (xs: !gflist_vt (a, xs)):<> [n:nat] (LENGTH (xs, n) | int n)
// end of [gflist_vt_length]

(* ****** ****** *)

(* end of [gflist_vt.sats] *)
