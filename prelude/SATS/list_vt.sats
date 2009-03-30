(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#include "prelude/params.hats"

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [list_vt.sats] starts!\n"

#endif

(* ****** ****** *)

%{#

#include "prelude/CATS/list_vt.cats"

%}

(* ****** ****** *)

prfun list_vt_length_is_nonnegative
  {a:viewt@ype} {n:int} (xs: !list_vt (a, n)): [n>=0] void

(* ****** ****** *)

fun{a:viewt@ype} list_vt_of_arraysize
  {n:nat} (arrsz: arraysize (a, n)):<> list_vt (a, n)

(* ****** ****** *)

fun{a:t@ype} list_vt_copy {n:nat} (xs: !list_vt (a, n)):<> list_vt (a, n)

fun{a:t@ype} list_vt_free (xs: List_vt a):<> void

(* ****** ****** *)

// this one is more general than [list_length] as [a] can be linear
fun{a:viewt@ype} list_vt_length {n:nat} (xs: !list_vt (a, n)):<> int n

(* ****** ****** *)

fun{a:viewt@ype} list_vt_append
  {m,n:nat} (xs: list_vt (a, m), ys: list_vt (a, n)):<> list_vt (a, m+n)

fun{a:viewt@ype} list_vt_reverse
  {n:nat} (xs: list_vt (a, n)):<> list_vt (a, n)

(* ****** ****** *)

fun{a:viewt@ype} list_vt_tabulate__main
  {v:view} {vt:viewtype} {n:nat} {f:eff}
  (pf: !v | f: (!v | natLt n, !vt) -<f> a, n: int n, env: !vt)
  :<f> list_vt (a, n)

fun{a:viewt@ype} list_vt_tabulate_fun {n:nat} {f:eff}
  (f: natLt n -<f> a, n: int n):<f> list_vt (a, n)

fun{a:viewt@ype} list_vt_tabulate_clo {n:nat} {f:eff}
  (f: &natLt n -<clo,f> a, n: int n):<f> list_vt (a, n)

(* ****** ****** *)

fun{a:viewt@ype} list_vt_foreach__main
  {v:view} {vt:viewtype} {n:nat} {f:eff}
  (pf: !v | xs: !list_vt (a, n), f: !(!v | &a, !vt) -<f> void, env: !vt)
  :<f> void

(* ****** ****** *)

fun{a:t@ype} list_vt_iforeach__main
  {v:view} {vt:viewtype} {n:nat} {f:eff}
  (pf: !v | xs: !list_vt (a, n), f: (!v | natLt n, &a, !vt) -<fun,f> void, env: !vt)
  :<f> void

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [list_vt.sats] finishes!\n"

#endif

(* end of [list_vt.sats] *)
