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

// some random number generators

(* ****** ****** *)

%{#

#include "libc/CATS/random.cats"
#include "libc/CATS/time.cats"

%}

(* ****** ****** *)

// typedef lint = long_int_t0ype

// a seeding function
fun srand48 (li: lint): void = "atslib_srand48"
fun srand48_with_time (): void = "atslib_srand48_with_time"

(* ****** ****** *)

fun drand48 ():<!ref> double // inside [0.0, 1.0)
  = "atslib_drand48"

fun lrand48 ():<!ref> lint // signed [0, 2^31)
  = "atslib_lrand48"

fun mrand48 ():<!ref> lint // signed [-2^31, 2^31)
  = "atslib_mrand48"

(* ****** ****** *)

abst@ype drand48_data = $extype "ats_drand48_data_type"

fun srand48_r // the return is always 0
  (seed: lint, buf: &drand48_data? >> drand48_data):<> int
  = "atslib_srand48_r"

(* ****** ****** *)

fun drand48_r // the return is always 0
  (buf: &drand48_data, result: &double? >> double):<> int
  = "atslib_drand48_r"

fun lrand48_r // the return is always 0
  (buf: &drand48_data, result: &lint? >> lint):<> int
  = "atslib_lrand48_r"

fun mrand48_r // the return is always 0
  (buf: &drand48_data, result: &lint? >> lint):<> int
  = "atslib_mrand48_r"

(* ****** ****** *)

// non-reentrant
fun randint {n:pos} (n: int n):<!ref> natLt n
  = "atslib_randint"

// this one is reentrant
fun randint_r {n:pos}
  (buf: &drand48_data, n: int n, res: &int? >> natLt n):<> void
  = "atslib_randint_r"

(* ****** ****** *)

(* end of [random.sats] *)
