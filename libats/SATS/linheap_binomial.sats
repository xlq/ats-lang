(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
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
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time

(* ****** ****** *)

absviewtype
heap_viewt0ype_viewtype (a:viewt@ype+)
stadef heap = heap_viewt0ype_viewtype

(* ****** ****** *)

sortdef vt0p = viewt@ype

(* ****** ****** *)
//
typedef cmp (a:vt0p) = (&a, &a) -<cloref> Sgn
//
fun{a:vt0p}
compare_elt_elt (x1: &a, x2: &a, cmp: cmp a):<> Sgn
//
(* ****** ****** *)

fun{} linheap_make_nil {a:vt0p} ():<> heap (a)

(* ****** ****** *)

fun{a:vt0p} linheap_size (hp: !heap a): size_t

(* ****** ****** *)

fun{a:vt0p}
linheap_insert (hp: &heap (a), x: a, cmp: cmp a):<> void

(* ****** ****** *)

fun{a:vt0p}
linheap_delmin (
  hp: &heap (a), res: &a? >> opt (a, b), cmp: cmp a
) :<> #[b:bool] bool b // end of [linheap_delim]

(* ****** ****** *)

fun{a:t@ype}
linheap_free (hp: heap (a)):<> void

(* ****** ****** *)

(* end of [linheap_binomial.sats] *)
