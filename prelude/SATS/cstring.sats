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
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
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

// some common functions on linear strings

#if VERBOSE #then

#warning "Loading cstring.sats starts!\n"

#endif

(* ****** ****** *)

abstype cstring_int_int_type (size: int, size_max: int)
stadef cstring = cstring_int_int_type

fun cstring_make_bytes_main :
  {V:view} {n,max:nat | n <= max} {l0:addr}
    (!V, vcontain_p (V, bytes_v (n, l0)) | int max, ptr l0, int n) -<>
      [l:addr] (cstring (n, max) @ l | ptr l)

fun cstring_make_bytes :
  {n,max:nat | n <= max} {sz:nat} {l0:addr}
    (!bytes_v (sz, l0) | int max, ptr l0, int n) -<>
      [l:addr] (cstring (n, max) @ l | ptr l)

fun cstring_make_empty :
  {max:nat} int max -<> [l:addr] (cstring (0, max) @ l | ptr l)

fun cstring_make_string : {n,max:nat | n <= max}
  (int max, string n) -<> [l:addr] (cstring (n, max) @ l | ptr l)

(* ****** ****** *)

fun cstring_free :
  {n,max:nat} {l:addr} (cstring (n, max) @ l | ptr l) -<> void

fun cstring_size :
  {n,max:nat} {l:addr} (!cstring (n, max) @ l | ptr l) -<> int n

fun cstring_size_max :
  {n,max:nat} {l:addr} (!cstring (n, max) @ l | ptr l) -<> int max

(* ****** ****** *)

fun cstring_cat :
  {n1,max1:nat} {n2,max2:nat | n2 <= max2; n1+n2 <= max1} {l_dest,l_src:addr}
    (cstring (n1, max1) @ l_dest >> cstring (n1+n2, max1) @ l_dest,
     !cstring (n2, max2) @ l_src | ptr l_dest, ptr l_src) -<> ptr l_dest

fun cstring_char_find : {n,max:nat | n <= max} {l:addr}
  (!cstring (n, max) @ l | ptr l, char) -<> intBtw (~1, n)

fun cstring_to_list : {n,max:nat | n <= max} {l:addr}
  (!cstring (n, max) @ l | ptr l) -<> list (char, n)

(* ****** ****** *)

// operations on linear strings

#if VERBOSE #then

#warning "Loading cstring.sats finishes!\n"

#endif

(* end of [cstring.sats] *)
