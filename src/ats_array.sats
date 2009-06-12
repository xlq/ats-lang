(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS/Anairiats - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
 * Free Software Foundation; either version 3, or (at  your  option)  any
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

// March 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

fun array_ptr_alloc_tsz
  {a:viewt@ype} {n:nat} (asz: int n, sz: sizeof_t a):<>
    [l:addr | l <> null] (free_gc_v (a, n, l), array_v (a?, n, l) | ptr l)
  = "ats_array_ptr_alloc_tsz"

(* ****** ****** *)

fun array_ptr_free
  {a:viewt@ype} {n:int} {l:addr}
  (_: free_gc_v (a, n, l), _: array_v (a?, n, l) | _: ptr l):<> void
  = "ats_array_ptr_free" 

(* ****** ****** *)

fun{a:t@ype} array_ptr_initialize_elt {n:nat} (
    base: &(@[a?][n]) >> @[a][n], asz: int n, x: a
  ) :<> void

fun{a:t@ype} array_ptr_make_elt {n:nat} (asz: int n, x:a)
  :<> [l:addr | l <> null] (free_gc_v (a, n, l), array_v (a, n, l) | ptr l)
// end of [array_ptr_make_elt]

(* ****** ****** *)

fun{a:t@ype} array_ptr_initialize_lst {n:nat} (
    base: &(@[a?][n]) >> @[a][n], xs: list (a, n)
  ) :<> void

fun{a:t@ype} array_ptr_make_lst {n:nat} (
    asz: int n, xs: list (a, n)
  ) :<> [l:addr | l <> null] (
    free_gc_v (a, n, l), array_v (a, n, l) | ptr l
  ) // end of [array_ptr_make_lst]

// not used
fun{a:viewt@ype} array_ptr_initialize_lst_vt {n:nat} (
    base: &(@[a?][n]) >> @[a][n], xs: list_vt (a, n)
  ) :<> void

fun{a:viewt@ype} array_ptr_make_lst_vt {n:nat} (
    asz: int n, xs: list_vt (a, n)
  ) :<> [l:addr | l <> null] (
    free_gc_v (a, n, l), array_v (a, n, l) | ptr l
  ) // end of [array_ptr_make_lst]

(* ****** ****** *)

(* end of [ats_array.sats] *)
