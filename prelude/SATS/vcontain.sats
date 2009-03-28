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

// some proofs involving view containment.

(* ****** ****** *)

#include "prelude/params.hats"

#if VERBOSE_PRELUDE #then

#print "Loading [vcontain.sats] starts!\n"

#endif

(* ****** ****** *)

prfun vcontain_make {v1:view} {v2:view}
 (fpf: v1 -<prf> [v:view] @(v2, v)): vcontain_p (v1, v2)

(* ****** ****** *)

prfun vcontain_refl {v:view} (): vcontain_p (v, v)
prfun vcontain_trans {v1,v2,v3:view}
  (pf12: vcontain_p (v1, v2), pf23: vcontain_p (v2, v3)): vcontain_p (v1, v3)

(* ****** ****** *)

prfun vcontain_tuple_2_0 {v0,v1:view} (): vcontain_p (@(v0, v1), v0)
prfun vcontain_tuple_2_1 {v0,v1:view} (): vcontain_p (@(v0, v1), v1)

(* ****** ****** *)

prval vcontain_array_elt :
  {a:viewtype} {n,i:nat | i < n} {l:addr} {ofs:int}
  MUL (i, sizeof a, ofs) -<> vcontain_p (@[a][n] @ l, a @ l + ofs)

prval vcontain_array_subarray :
  {a:viewtype} {n,i,len:nat | i+len <= n} {l:addr} {ofs:int}
  MUL (i, sizeof a, ofs) -<> vcontain_p (@[a][n] @ l, @[a][len] @ l + ofs)

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [vcontain.dats] starts!\n"

#endif

(* end of [vcontain.sats] *)
