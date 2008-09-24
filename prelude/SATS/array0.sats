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

#print "Loading [array0.sats] starts!\n"

#endif

(* ****** ****** *)

fun array0_make_arraysize
  {a:viewt@ype} {n:nat} (arrsz: arraysize (a, n)):<> array0 (a)

macdef array0 (x) = array0_make_arraysize ,(x)

(* ****** ****** *)

fun{a:t@ype} array0_make_elt (asz: int, x: a):<!exnref> array0 a

(* ****** ****** *)

fun array0_size {a:t@ype} (A: array0 a):<> int

(* ****** ****** *)

fun{a:t@ype} array0_get_elt_at_exn
  (A: array0 a, i: int):<!exnref> a

fun{a:t@ype} array0_set_elt_at_exn
  (A: array0 a, i: int, x: a):<!exnref> void

overload [] with array0_get_elt_at_exn
overload [] with array0_set_elt_at_exn

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [array0.sats] finishes!\n"

#endif

(* end of [array0.sats] *)
