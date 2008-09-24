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

#if VERBOSE_PRELUDE #then

#print "Loading [vcontain.sats] starts!\n"

#endif

(* ****** ****** *)

prval vcontain_p_refl : {V:view} () -<> vcontain_p (V, V)
prval vcontain_p_trans : {V1,V2,V3:view}
  (vcontain_p (V1, V2), vcontain_p (V2, V3)) -<> vcontain_p (V1, V3)

(* ****** ****** *)

prval vcontain_p_tuple_2_1 : {V1,V2:view} () -<> vcontain_p (@(V1, V2), V1)
prval vcontain_p_tuple_2_2 : {V1,V2:view} () -<> vcontain_p (@(V1, V2), V2)

(* ****** ****** *)

prval vcontain_p_array_subarray :
  {a:viewtype} {n,i,len:nat | i+len <= n} {l:addr} {ofs:int}
    MUL (i, sizeof a, ofs) -<> vcontain_p (@[a][n] @ l, @[a][len] @ l + ofs)

prval vcontain_p_array_elt :
  {a:viewtype} {n,i:nat | i < n} {l:addr} {ofs:int}
    MUL (i, sizeof a, ofs) -<> vcontain_p (@[a][n] @ l, a @ l + ofs)

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [vcontain.dats] starts!\n"

#endif

(* end of [vcontain.sats] *)
