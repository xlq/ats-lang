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

#print "Loading [lazy.sats] starts!\n"

#endif

(* ****** ****** *)

fun{a:t@ype} stream_filter_fun
  (xs: stream a, p: a -<1,~ref> bool):<1,~ref> stream a

fun{a:t@ype} stream_filter_cloref
  (xs: stream a, p: a -<cloref1,~ref> bool):<1,~ref> stream a

(* ****** ****** *)

fun{a,b:t@ype} stream_map_fun
  (xs: stream a, f: a -<1,~ref> b):<1,~ref> stream b

fun{a,b:t@ype} stream_map_cloref
  (xs: stream a, f: a -<cloref1,~ref> b):<1,~ref> stream b

(* ****** ****** *)

fun{a1,a2,b:t@ype} stream_map2_fun
  (xs1: stream a1, xs2: stream a2, f: (a1, a2) -<1,~ref> b)
  :<1,~ref> stream b

fun{a1,a2,b:t@ype} stream_map2_cloref
  (xs1: stream a1, xs2: stream a2, f: (a1, a2) -<cloref1,~ref> b)
  :<1,~ref> stream b

(* ****** ****** *)

fun{a:t@ype} stream_merge_ord
  (xs1: stream a, xs2: stream a, lte: (a, a) -<cloref1,~ref> bool)
  :<1,~ref> stream a

(* ****** ****** *)

fun{a:t@ype} stream_nth (xs: stream a, i: Nat):<1,~ref> a

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [lazy.sats] finishes!\n"

#endif

(* end of [lazy.sats] *)
