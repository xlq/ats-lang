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

// some pointer operations

#define VERBOSE 1

#if VERBOSE #then

#print "Loading pointer.dats starts!\n"

#endif

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

implement ptr_alloc<a> () = ptr_alloc_tsz {a} (sizeof<a>)

(* ****** ****** *)

implement ptr_get_t<a> (pf | p) = !p
implement ptr_set_t<a> (pf | p, x) = (!p := x)
implement ptr_move_t<a> (pf1, pf2 | p1, p2) = (!p2 := !p1)

(* ****** ****** *)

implement ptr_get_vt<a> (pf | p) = !p
implement ptr_set_vt<a> (pf | p, x) = (!p := x)
implement ptr_move_vt<a> (pf1, pf2 | p1, p2) = (!p2 := !p1)

(* ****** ****** *)

implement ptr_get_inv<a> (pf | p) = !p
implement ptr_set_inv<a> (pf | p, x) = (!p := x)

(* ****** ****** *)

#if VERBOSE #then

#print "Loading pointer.dats finishes!\n"

#endif
