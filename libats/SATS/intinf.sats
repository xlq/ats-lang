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
 * along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
 * Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

// infinite precision integers based on the gmp package

(* ****** ****** *)

staload "libc/SATS/gmp.sats"

(* ****** ****** *)

%{#

#include "libats/CATS/intinf.cats"

%}

(* ****** ****** *)

absviewtype intinf (int)
viewtypedef Intinf = [n:int] intinf n

symintr intinf_of

fun intinf_of_int1 {i:int} (i: int i): intinf i
overload intinf_of with intinf_of_int1

fun intinf_free {i:int} (i: intinf i): void

(* ****** ****** *)

fun fprint_intinf {m:file_mode} {i:int}
  (pf: file_mode_lte (m, w) | fil: &FILE m, i: !intinf i): void

fun print_intinf {i:int} (i: !intinf i): void
overload print with print_intinf

#define sixtythree 63

fun fprint_intinf_base {m:file_mode} {i:int}
  (pf: file_mode_lte (m, w) | fil: &FILE m, b: intBtw (2, sixtythree), i: !intinf i): void

fun print_intinf_base {i:int} (b: intBtw (2, sixtythree), i: !intinf i): void
overload print with print_intinf_base

(* ****** ****** *)

fun pred_intinf {i:int} (i: !intinf i): intinf (i-1)
overload pred with pred_intinf

fun succ_intinf {i:int} (i: !intinf i): intinf (i+1)
overload succ with succ_intinf

//

fun add_intinf_int {i,j:int}
  (i: !intinf i, j: int j): intinf (i+j)

fun add_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): intinf (i+j)

overload + with add_intinf_int
overload + with add_intinf_intinf

//

fun sub_intinf_int {i,j:int}
  (i: !intinf i, j: int j): intinf (i-j)

fun sub_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): intinf (i-j)

overload - with sub_intinf_int
overload - with sub_intinf_intinf

//

fun mul_intinf_int {m,n:int}
  (m: !intinf m, n: int n): [p:int] (MUL (m, n, p) | intinf p)

fun mul_intinf_intinf {m,n:int}
  (m: !intinf m, n: !intinf n): [p:int] (MUL (m, n, p) | intinf p)

overload * with mul_intinf_int
overload * with mul_intinf_intinf

//

fun div_intinf_int {m,n:int | n > 0}
  (m: !intinf m, n: int n): [q,r:int | 0 <= r; r < n] (MUL (q, n, m-r) | intinf q)

overload / with div_intinf_int

(* ****** ****** *)

fun lt_intinf_int {i,j:int}
  (i: !intinf i, j: int j): bool (i < j)
  = "atslib_lt_intinf_int"

fun lt_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): bool (i < j)
  = "atslib_lt_intinf_intinf"

overload < with lt_intinf_int
overload < with lt_intinf_intinf

//

fun lte_intinf_int {i,j:int}
  (i: !intinf i, j: int j): bool (i <= j)
  = "atslib_lte_intinf_int"

fun lte_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): bool (i <= j)
  = "atslib_lte_intinf_intinf"

overload <= with lte_intinf_int
overload <= with lte_intinf_intinf

//

fun gt_intinf_int {i,j:int}
  (i: !intinf i, j: int j): bool (i > j)
  = "atslib_gt_intinf_int"

fun gt_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): bool (i > j)
  = "atslib_gt_intinf_intinf"

overload > with gt_intinf_int
overload > with gt_intinf_intinf

//

fun gte_intinf_int {i,j:int}
  (i: !intinf i, j: int j): bool (i >= j)
  = "atslib_gte_intinf_int"

fun gte_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): bool (i >= j)
  = "atslib_gte_intinf_intinf"

overload >= with gte_intinf_int
overload >= with gte_intinf_intinf

//

fun eq_intinf_int {i,j:int}
  (i: !intinf i, j: int j): bool (i == j)
  = "atslib_eq_intinf_int"

fun eq_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): bool (i == j)
  = "atslib_eq_intinf_intinf"

overload = with eq_intinf_int
overload = with eq_intinf_intinf

//

fun neq_intinf_int {i,j:int}
  (i: !intinf i, j: int j): bool (i <> j)
  = "atslib_neq_intinf_int"

fun neq_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): bool (i <> j)
  = "atslib_neq_intinf_intinf"

overload <> with neq_intinf_int
overload <> with neq_intinf_intinf

//

fun compare_intinf_int {i,j:int}
  (i: !intinf i, j: int j): [k:int | sgn_r (i-j, k)] int k
  = "atslib_compare_intinf_int"

fun compare_intinf_intinf {i,j:int}
  (i: !intinf i, j: !intinf j): [k:int | sgn_r (i-j, k)] int k
  = "atslib_compare_intinf_intinf"

overload compare with compare_intinf_int
overload compare with compare_intinf_intinf

(* ****** ****** *)

(* end of [intinf.sats] *)
