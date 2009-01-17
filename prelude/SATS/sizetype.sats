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

#print "Loading [sizetype.sats] starts!\n"

#endif

(* ****** ****** *)

%{#

#include "prelude/CATS/sizetype.cats" ;

%}

(* ****** ****** *)

// unindexed size type

fun size0_of_int {i:nat} (i: int i):<> size_t
  = "atspre_size0_of_int"

fun add_size0_size0 (sz1: size_t, sz2: size_t):<> size_t
  = "atspre_add_size_size"
overload + with add_size0_size0

fun mul_size0_size0 (sz1: size_t, sz2: size_t):<> size_t
  = "atspre_mul_size_size"
overload * with mul_size0_size0

(* ****** ****** *)

// indexed size type

(* ****** ****** *)

fun size1_of_size (i: size_t):<> [i:nat] size_t i
  = "atspre_size1_of_size"

(* ****** ****** *)

fun int_of_size {i:nat} (sz: size_t i):<> int i
  = "atspre_int_of_size"

// ------ ------

fun size_of_int {i:nat} (i: int i):<> size_t i
  = "atspre_size_of_int"

fun size_of_ssize {i:nat} (_: ssize_t i):<> size_t i
  = "atspre_size_of_ssize"

fun size_of_ptrdiff {i:nat} (_: ptrdiff_t i):<> size_t i
  = "atspre_size_of_ptrdiff"

(* ****** ****** *)

fun succ_size {i:nat} (i: size_t i):<> size_t (i+1)
  = "atspre_succ_size"

and pred_size {i:pos} (i: size_t i):<> size_t (i-1)
  = "atspre_pred_size"

overload succ with succ_size
overload pred with pred_size

// ------ ------

fun add_size_size {i,j:nat}
  (i: size_t i, j: size_t j):<> size_t (i+j)
  = "atspre_add_size_size"
overload + with add_size_size

fun add_size_int {i,j:nat}
  (i: size_t i, j: int j):<> size_t (i+j)
  = "atspre_add_size_int"
overload + with add_size_int

fun sub_size_size {i,j:nat | j <= i}
  (i: size_t i, j: size_t j):<> size_t (i-j)
  = "atspre_sub_size_size"
overload - with sub_size_size

fun sub_size_int {i,j:nat | j <= i}
  (i: size_t i, j: int j):<> size_t (i-j)
  = "atspre_sub_size_int"
overload - with sub_size_int

// ------ ------

fun mul_size_size
  {i,j:nat} (i: size_t i, j: size_t j):<> size_t (i*j)
  = "atspre_mul_size_size"
overload * with mul_size_size

symintr szmul1 szmul2; infixl ( * ) szmul1 szmul2

fun mul1_size_size
  {i,j:nat} (i: size_t i, j: size_t j):<> [p:nat] size_t p
  = "atspre_mul1_size_size"
overload szmul1 with mul1_size_size

fun mul2_size_size
  {i,j:nat} (i: size_t i, j: size_t j)
  :<> [p:int] (MUL (i, j, p) | size_t p)
  = "atspre_mul2_size_size"
overload szmul2 with mul2_size_size

// ------ ------

symintr szmod1; infixl szmod1

fun mod1_size_size {i:nat;j:int | j > 0}
  (i: size_t i, j: size_t j):<> [r:nat | r < j] size_t r
  = "atspre_mod1_size_size"
overload szmod1 with mod1_size_size

// ------ ------

fun lt_size_size {i,j:nat}
  (i: size_t i, j: size_t j):<> bool (i < j)
  = "atspre_lt_size_size"
overload < with lt_size_size

fun lt_size_int {i,j:nat}
  (i: size_t i, j: int j):<> bool (i < j)
  = "atspre_lt_size_int"
overload < with lt_size_int

fun lt_int_size {i,j:nat}
  (i: int i, j: size_t j):<> bool (i < j)
  = "atspre_lt_int_size"
overload < with lt_int_size

// ------ ------

fun lte_size_size {i,j:nat}
  (i: size_t i, j: size_t j):<> bool (i <= j)
  = "atspre_lte_size_size"
overload <= with lte_size_size

fun lte_size_int {i,j:nat}
  (i: size_t i, j: int j):<> bool (i <= j)
  = "atspre_lte_size_int"
overload <= with lte_size_int

// ------ ------

fun gt_size_size {i,j:nat}
  (i: size_t i, j: size_t j):<> bool (i > j)
  = "atspre_gt_size_size"
overload > with gt_size_size

fun gt_size_int {i,j:nat}
  (i: size_t i, j: int j):<> bool (i > j)
  = "atspre_gt_size_int"
overload > with gt_size_int

// ------ ------

fun gte_size_size {i,j:nat}
  (i: size_t i, j: size_t j):<> bool (i >= j)
  = "atspre_gte_size_size"
overload >= with gte_size_size

fun gte_size_int {i,j:nat}
  (i: size_t i, j: int j):<> bool (i >= j)
  = "atspre_gte_size_int"
overload >= with gte_size_int

// ------ ------

fun eq_size_size {i,j:nat}
  (i: size_t i, j: size_t j):<> bool (i == j)
  = "atspre_eq_size_size"
overload = with eq_size_size

fun eq_size_int {i,j:nat}
  (i: size_t i, j: int j):<> bool (i == j)
  = "atspre_eq_size_int"
overload = with eq_size_int

// ------ ------

fun neq_size_size {i,j:nat}
  (i: size_t i, j: size_t j):<> bool (i <> j)
  = "atspre_neq_size_size"
overload <> with neq_size_size

fun neq_size_int {i,j:nat}
  (i: size_t i, j: int j):<> bool (i <> j)
  = "atspre_neq_size_int"
overload <> with neq_size_int

// ------ ------

fun max_size_size {i,j:nat}
  (i: size_t i, j: size_t j):<> size_t (max (i, j))
  = "atspre_max_size_size"
and min_size_size {i,j:nat}
  (i: size_t i, j: size_t j):<> size_t (min (i, j))
  = "atspre_min_size_size"

overload max with max_size_size
overload min with min_size_size

(* ****** ****** *)

symintr fprint_size

fun fprint0_size (out: FILEref, x: size_t):<!exnref> void
  = "atspre_fprint_size"

fun fprint1_size {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: size_t):<!exnref> void
  = "atspre_fprint_size"

overload fprint_size with fprint0_size
overload fprint_size with fprint1_size
overload fprint with fprint_size

(* ****** ****** *)

fun print_size (i: size_t):<!ref> void
  = "atspre_print_size"

and prerr_size (i: size_t):<!ref> void
  = "atspre_prerr_size"

overload print with print_size
overload prerr with prerr_size

(* ****** ****** *)

// signed indexed size type

(* ****** ****** *)

fun int_of_ssize {i:int} (sz: ssize_t i):<> int i
  = "atspre_int_of_ssize"

fun ssize_of_int {i:int} (i: int i):<> ssize_t i
  = "atspre_ssize_of_int"

fun ssize_of_size {i:nat} (sz: size_t i):<> ssize_t i
  = "atspre_ssize_of_size"

(* ****** ****** *)

fun lt_ssize_int {i,j:int}
  (i: ssize_t i, j: int j):<> bool (i < j)
  = "atspre_lt_ssize_int"
overload < with lt_ssize_int

// ------ ------

fun lte_ssize_int {i,j:int}
  (i: ssize_t i, j: int j):<> bool (i <= j)
  = "atspre_lt_ssize_int"
overload <= with lte_ssize_int

// ------ ------

fun gt_ssize_int {i,j:int}
  (i: ssize_t i, j: int j):<> bool (i > j)
  = "atspre_gt_ssize_int"
overload > with gt_ssize_int

// ------ ------

fun gte_ssize_int {i,j:int}
  (i: ssize_t i, j: int j):<> bool (i >= j)
  = "atspre_gte_ssize_int"
overload >= with gte_ssize_int

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [sizetype.sats] finishes!\n"

#endif

(* end of [sizetype.sats] *)
