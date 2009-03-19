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

#if VERBOSE_PRELUDE #then

#print "Loading [integer_ptr.sats] starts!\n"

#endif

(* ****** ****** *)

// intrptr and uintptr

(* ****** ****** *)

typedef intptr = intptr_type

symintr intptr_of

fun intptr_of_int (i: int):<> intptr
  = "atspre_intptr_of_int"

overload intptr_of with intptr_of_int

// ------ ------

fun abs_intptr (i: intptr):<> intptr
  = "atspre_abs_intptr"
overload abs with abs_intptr

fun neg_intptr (i: intptr):<> intptr
  = "atspre_neg_intptr"
overload ~ with neg_intptr

fun succ_intptr (i: intptr):<> intptr
  = "atspre_succ_intptr"

and pred_intptr (i: intptr):<> intptr
  = "atspre_pred_intptr"

overload succ with succ_intptr
overload pred with pred_intptr

fun add_intptr_intptr (i: intptr, j: intptr):<> intptr
  = "atspre_add_intptr_intptr"

and sub_intptr_intptr (i: intptr, j: intptr):<> intptr
  = "atspre_sub_intptr_intptr"

and mul_intptr_intptr (i: intptr, j: intptr):<> intptr
  = "atspre_mul_intptr_intptr"

and div_intptr_intptr (i: intptr, j: intptr):<> intptr
  = "atspre_div_intptr_intptr"

and mod_intptr_intptr (i: intptr, j: intptr):<> intptr
  = "atspre_mod_intptr_intptr"

overload + with add_intptr_intptr
overload - with sub_intptr_intptr
overload * with mul_intptr_intptr
overload / with div_intptr_intptr
overload mod with mod_intptr_intptr

fun lt_intptr_intptr (i: intptr, j: intptr):<> bool
  = "atspre_lt_intptr_intptr"

and lte_intptr_intptr (i: intptr, j: intptr):<> bool
  = "atspre_lte_intptr_intptr"

fun gt_intptr_intptr (i: intptr, j: intptr):<> bool
  = "atspre_gt_intptr_intptr"

and gte_intptr_intptr (i: intptr, j: intptr):<> bool
  = "atspre_gte_intptr_intptr"

fun eq_intptr_intptr (i: intptr, j: intptr):<> bool
  = "atspre_eq_intptr_intptr"

and neq_intptr_intptr (i: intptr, j: intptr):<> bool
  = "atspre_neq_intptr_intptr"

overload < with lt_intptr_intptr
overload <= with lte_intptr_intptr
overload > with gt_intptr_intptr
overload >= with gte_intptr_intptr
overload = with eq_intptr_intptr
overload <> with neq_intptr_intptr

fun max_intptr_intptr (i: intptr, j: intptr):<> intptr
  = "atspre_max_intptr_intptr"
and min_intptr_intptr (i: intptr, j: intptr):<> intptr
  = "atspre_min_intptr_intptr"

overload max with max_intptr_intptr
overload min with min_intptr_intptr

(* ****** ****** *)

symintr fprint_intptr

fun fprint0_intptr (out: FILEref, x: intptr):<!exnref> void
  = "atspre_fprint_intptr"

fun fprint1_intptr {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: intptr):<!exnref> void
  = "atspre_fprint_intptr"

overload fprint_intptr with fprint0_intptr
overload fprint_intptr with fprint1_intptr
overload fprint with fprint_intptr

(* ****** ****** *)

fun print_intptr (i: intptr):<!ref> void
  = "atspre_print_intptr"

and prerr_intptr (i: intptr):<!ref> void
  = "atspre_prerr_intptr"

overload print with print_intptr
overload prerr with prerr_intptr

(* ****** ****** *)

typedef uintptr = uintptr_type

symintr uintptr_of

fun uintptr_of_int (i: int):<> uintptr
  = "atspre_uintptr_of_int"

overload uintptr_of with uintptr_of_int

// arithmetic functions and comparison functions

fun succ_uintptr (u: uintptr):<> uintptr
  = "atspre_succ_uintptr"

and pred_uintptr (u: uintptr):<> uintptr
  = "atspre_pred_uintptr"

overload succ with succ_uintptr
overload pred with pred_uintptr

fun add_uintptr_uintptr (i: uintptr, j: uintptr):<> uintptr
  = "atspre_add_uintptr_uintptr"

and sub_uintptr_uintptr (i: uintptr, j: uintptr):<> uintptr
  = "atspre_sub_uintptr_uintptr"

and mul_uintptr_uintptr (i: uintptr, j: uintptr):<> uintptr
  = "atspre_mul_uintptr_uintptr"

and div_uintptr_uintptr (i: uintptr, j: uintptr):<> uintptr
  = "atspre_div_uintptr_uintptr"

and mod_uintptr_uintptr (i: uintptr, j: uintptr):<> uintptr
  = "atspre_mod_uintptr_uintptr"

overload + with add_uintptr_uintptr
overload - with sub_uintptr_uintptr
overload * with mul_uintptr_uintptr
overload / with div_uintptr_uintptr
overload mod with mod_uintptr_uintptr

fun lt_uintptr_uintptr (i: uintptr, j: uintptr):<> bool
  = "atspre_lt_uintptr_uintptr"

and lte_uintptr_uintptr (i: uintptr, j: uintptr):<> bool
  = "atspre_lte_uintptr_uintptr"

fun gt_uintptr_uintptr (i: uintptr, j: uintptr):<> bool
  = "atspre_gt_uintptr_uintptr"

and gte_uintptr_uintptr (i: uintptr, j: uintptr):<> bool
  = "atspre_gte_uintptr_uintptr"

fun eq_uintptr_uintptr (i: uintptr, j: uintptr):<> bool
  = "atspre_eq_uintptr_uintptr"

and neq_uintptr_uintptr (i: uintptr, j: uintptr):<> bool
  = "atspre_neq_uintptr_uintptr"

overload < with lt_uintptr_uintptr
overload <= with lte_uintptr_uintptr
overload > with gt_uintptr_uintptr
overload >= with gte_uintptr_uintptr
overload = with eq_uintptr_uintptr
overload <> with neq_uintptr_uintptr

fun max_uintptr_uintptr (i: uintptr, j: uintptr):<> uintptr
  = "atspre_max_uintptr_uintptr"

and min_uintptr_uintptr (i: uintptr, j: uintptr):<> uintptr
  = "atspre_min_uintptr_uintptr"

overload max with max_uintptr_uintptr
overload min with min_uintptr_uintptr

(* ****** ****** *)

// bit operations

fun lnot_uintptr (u: uintptr):<> uintptr
  = "atspre_lnot_uintptr" (* bitwise *)
overload ~ with lnot_uintptr

fun land_uintptr_uintptr (u1: uintptr, u2: uintptr):<> uintptr
  = "atspre_land_uintptr_uintptr"

fun lor_uintptr_uintptr (u1: uintptr, u2: uintptr):<> uintptr
  = "atspre_lor_uintptr_uintptr"

fun lxor_uintptr_uintptr (u1: uintptr, u2: uintptr):<> uintptr
  = "atspre_lxor_uintptr_uintptr"

overload land with land_uintptr_uintptr
overload lor with lor_uintptr_uintptr
overload lxor with lxor_uintptr_uintptr

fun lsl_uintptr_int1 (u: uintptr, n: Nat):<> uintptr
  = "atspre_lsl_uintptr_int1"

and lsr_uintptr_int1 (u: uintptr, n: Nat):<> uintptr
  = "atspre_lsr_uintptr_int1"

overload << with lsl_uintptr_int1
overload >> with lsr_uintptr_int1

(* ****** ****** *)

symintr fprint_uintptr

fun fprint0_uintptr (out: FILEref, x: uintptr):<!exnref> void
  = "atspre_fprint_uintptr"

fun fprint1_uintptr {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: uintptr):<!exnref> void
  = "atspre_fprint_uintptr"

overload fprint_uintptr with fprint0_uintptr
overload fprint_uintptr with fprint1_uintptr
overload fprint with fprint_uintptr

(* ****** ****** *)

fun print_uintptr (u: uintptr):<!ref> void
  = "atspre_print_uintptr"

and prerr_uintptr (u: uintptr):<!ref> void
  = "atspre_prerr_uintptr"

overload print with print_uintptr
overload prerr with prerr_uintptr

(* ****** ****** *)

#if VERBOSE_PRELUDE #then

#print "Loading [integer_ptr.sats] finishes!\n"

#endif

(* end of [integer_ptr.sats] *)