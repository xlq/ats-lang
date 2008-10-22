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

#print "Loading [integer.sats] starts!\n"

#endif

(* ****** ****** *)

// signed integers (of unindexed type)

(* ****** ****** *)

//

fun int_of_char (c: char):<> int
  = "atspre_int_of_char"
overload int_of with int_of_char

fun int_of_schar (c: schar):<> int
  = "atspre_int_of_schar"
overload int_of with int_of_schar

fun int_of_uchar (c: uchar):<> int
  = "atspre_int_of_uchar"
overload int_of with int_of_uchar

//

fun int_of_double (d: double):<> int
  = "atspre_int_of_double"
overload int_of with int_of_double

// This function is based on [atoi] in [stdlib.h]
fun int_of_string (s: string):<> int
  = "atspre_int_of_string"
overload int_of with int_of_string

fun int_of_uint (u: uint):<> int
  = "atspre_int_of_uint"
overload int_of with int_of_uint

// arithmetic functions and comparison functions

fun abs_int (i: int):<> int = "atspre_abs_int"
overload abs with abs_int

fun neg_int (i: int):<> int = "atspre_neg_int"
overload ~ with neg_int

fun succ_int (i: int):<> int = "atspre_succ_int"

and pred_int (i: int):<> int = "atspre_pred_int"

overload succ with succ_int
overload pred with pred_int

fun add_int_int (i1: int, i2: int):<> int
  = "atspre_add_int_int"

and sub_int_int (i1: int, i2: int):<> int
  = "atspre_sub_int_int"

and mul_int_int (i1: int, i2: int):<> int
  = "atspre_mul_int_int"

and div_int_int (i1: int, i2: int):<> int
  = "atspre_div_int_int"

and mod_int_int (i1: int, i2: int):<> int
  = "atspre_mod_int_int"

and gcd_int_int (i1: int, i2: int):<> int
  = "atspre_gcd_int_int"

overload + with add_int_int
overload - with sub_int_int
overload * with mul_int_int
overload / with div_int_int
overload mod with mod_int_int
overload gcd with gcd_int_int

fun lt_int_int (i1: int, i2: int):<> bool
  = "atspre_lt_int_int"

and lte_int_int (i1: int, i2: int):<> bool
  = "atspre_lte_int_int"

fun gt_int_int (i1: int, i2: int):<> bool
  = "atspre_gt_int_int"

and gte_int_int (i1: int, i2: int):<> bool
  = "atspre_gte_int_int"

fun eq_int_int (i1: int, i2: int):<> bool
  = "atspre_eq_int_int"

and neq_int_int (i1: int, i2: int):<> bool
  = "atspre_neq_int_int"

overload < with lt_int_int
overload <= with lte_int_int
overload > with gt_int_int
overload >= with gte_int_int
overload = with eq_int_int
overload <> with neq_int_int

fun compare_int_int (i1: int, i2: int):<> Sgn
  = "atspre_compare_int_int"
overload compare with compare_int_int

fun max_int_int (i1: int, i2: int):<> int
  = "atspre_max_int_int"
and min_int_int (i1: int, i2: int):<> int
  = "atspre_min_int_int"

overload max with max_int_int
overload min with min_int_int

fun square_int (i: int):<> int = "atspre_square_int"
overload square with square_int

fun cube_int (i: int):<> int = "atspre_cube_int"
overload cube with cube_int

fun pow_int_int1 (base: int, exponent: Nat):<> int
  = "atspre_pow_int_int1"
overload pow with pow_int_int1

(* ****** ****** *)

// bit operations

fun asl_int_int1 (i: int, n: Nat):<> int
  = "atspre_asl_int_int1"

and asr_int_int1 (i: int, n: Nat):<> int
  = "atspre_asr_int_int1"

overload << with asl_int_int1
overload >> with asr_int_int1

(* ****** ****** *)

symintr fprint_int

fun fprint0_int (out: FILEref, x: int):<!exnref> void
  = "atspre_fprint_int"

fun fprint1_int {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: int):<!exnref> void
  = "atspre_fprint_int"

overload fprint_int with fprint0_int
overload fprint_int with fprint1_int
overload fprint with fprint_int

//

fun print_int (i: int):<!ref> void
  = "atspre_print_int"

and prerr_int (i: int):<!ref> void
  = "atspre_prerr_int"

overload print with print_int
overload prerr with prerr_int

(* ****** ****** *)

// stringization

fun tostring_int (i: int):<> string
  = "atspre_tostring_int"

overload tostring with tostring_int

(* ****** ****** *)

// unsigned integers (of unindexed type)

(* ****** ****** *)

fun uint_of_char (c: char):<> uint
  = "atspre_uint_of_char"

overload uint_of with uint_of_char

fun uint_of_int (i: int):<> uint
  = "atspre_uint_of_int"

overload uint_of with uint_of_int

// arithmetic functions and comparison functions

fun succ_uint (u: uint):<> uint = "atspre_succ_uint"

and pred_uint (u: uint):<> uint = "atspre_pred_uint"

overload succ with succ_uint
overload pred with pred_uint

fun add_uint_uint (u1: uint, u2: uint):<> uint
  = "atspre_add_uint_uint"

and sub_uint_uint (u1: uint, u2: uint):<> uint
  = "atspre_sub_uint_uint"

and mul_uint_uint (u1: uint, u2: uint):<> uint
  = "atspre_mul_uint_uint"

and div_uint_uint (u1: uint, u2: uint):<> uint
  = "atspre_div_uint_uint"

and mod_uint_uint (u1: uint, u2: uint):<> uint
  = "atspre_mod_uint_uint"

and gcd_uint_uint (u1: uint, u2: uint):<> uint
  = "atspre_gcd_uint_uint"

overload + with add_uint_uint
overload - with sub_uint_uint
overload * with mul_uint_uint
overload / with div_uint_uint
overload mod with mod_uint_uint
overload gcd with gcd_uint_uint

(* ****** ****** *)

fun square_uint (u: uint):<> uint
  = "atspre_square_uint"

overload square with square_uint

(* ****** ****** *)

fun lt_uint_uint (u1: uint, u2: uint):<> bool
  = "atspre_lt_uint_uint"

and lte_uint_uint (u1: uint, u2: uint):<> bool
  = "atspre_lte_uint_uint"

fun gt_uint_uint (u1: uint, u2: uint):<> bool
  = "atspre_gt_uint_uint"

and gte_uint_uint (u1: uint, u2: uint):<> bool
  = "atspre_gte_uint_uint"

fun eq_uint_uint (u1: uint, u2: uint):<> bool
  = "atspre_eq_uint_uint"

and neq_uint_uint (u1: uint, u2: uint):<> bool
  = "atspre_neq_uint_uint"

overload < with lt_uint_uint
overload <= with lte_uint_uint
overload > with gt_uint_uint
overload >= with gte_uint_uint
overload = with eq_uint_uint
overload <> with neq_uint_uint

(* ****** ****** *)

fun compare_uint_uint (u1: uint, u2: uint):<> Sgn
  = "atspre_compare_uint_uint"
overload compare with compare_uint_uint

fun max_uint_uint (u1: uint, u2: uint):<> uint
  = "atspre_max_uint_uint"

and min_uint_uint (u1: uint, u2: uint):<> uint
  = "atspre_min_uint_uint"

overload max with max_uint_uint
overload min with min_uint_uint

(* ****** ****** *)

// bit operations

fun lnot_uint (u: uint):<> uint
  = "atspre_lnot_uint" (* bitwise *)
overload ~ with lnot_uint

fun land_uint_uint (u1: uint, u2: uint):<> uint
  = "atspre_land_uint_uint"

fun lor_uint_uint (u1: uint, u2: uint):<> uint
  = "atspre_lor_uint_uint"

fun lxor_uint_uint (u1: uint, u2: uint):<> uint
  = "atspre_lxor_uint_uint"

overload land with lxor_uint_uint
overload lor with lxor_uint_uint
overload lxor with lxor_uint_uint

fun lsl_uint_int1 (u: uint, n: Nat):<> uint
  = "atspre_lsl_uint_int1"

and lsr_uint_int1 (u: uint, n: Nat):<> uint
  = "atspre_lsr_uint_int1"

overload << with lsl_uint_int1
overload >> with lsr_uint_int1

(* ****** ****** *)

symintr fprint_uint

fun fprint0_uint (out: FILEref, x: uint):<!exnref> void
  = "atspre_fprint_uint"

fun fprint1_uint {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: uint):<!exnref> void
  = "atspre_fprint_uint"

overload fprint_uint with fprint0_uint
overload fprint_uint with fprint1_uint
overload fprint with fprint_uint

(* ****** ****** *)

fun print_uint (u: uint):<!ref> void
  = "atspre_print_uint"

and prerr_uint (u: uint):<!ref> void
  = "atspre_prerr_uint"

overload print with print_uint
overload prerr with prerr_uint

(* ****** ****** *)

// stringization

fun tostring_uint (u: uint):<> string
  = "atspre_tostring_uint"

overload tostring with tostring_uint

(* ****** ****** *)

// signed integers (of indexed type)

(* ****** ****** *)

// Note that the following coersion is automatic
fun int1_of_int (i: int):<> [i:int] int i
  = "atspre_int1_of_int"
overload int1_of with int1_of_int

fun int1_of_string (s: string):<> [i:int] int i
  = "atspre_int1_of_string"
overload int1_of with int1_of_string

// arithmetic functions and comparison functions

fun iabs {i:int} (i: int i):<> [j:int | abs_r (i, j)] int j
  = "atspre_iabs"
overload abs with iabs

fun ineg {i:int} (i: int i):<> int (~i)
  = "atspre_ineg"
overload ~ with ineg

fun isucc {i:int} (i: int i):<> int (i + 1)
  = "atspre_isucc"
and ipred {i:int} (i: int i):<> int (i - 1)
  = "atspre_ipred"

overload succ with isucc
overload pred with ipred

fun iadd {i,j:int} (i: int i, j: int j):<> int (i+j)
  = "atspre_iadd"

and isub {i,j:int} (i: int i, j: int j):<> int (i-j)
  = "atspre_isub"

and imul {i,j:int} (i: int i, j: int j):<> int (i*j)
  = "atspre_imul"

and idiv {i,j:int | j <> 0}
  (i: int i, j: int j):<> int (i/j)
  = "atspre_idiv"

and igcd {i,j:int}
  (i: int i, j: int j):<> [r:int | r >= 0] int r
  = "atspre_igcd"

overload + with iadd
overload - with isub
overload * with imul
overload / with idiv
overload gcd with igcd

fun imul1 (i: Int, j: Int):<> Int = "atspre_imul1"

and idiv1 {j:int | j <> 0} (i: Int, j: int j):<> Int
  = "atspre_idiv1"

and igcd1 {i,j:int}
  (i: int i, j: int j):<> [r:int | r >= 0] int r
  = "atspre_igcd1"

fun imul2 {i,j:int}
  (i: int i, j: int j):<> [p:int] (MUL (i, j, p) | int p)
  = "atspre_imul2"

and igcd2 {i,j:int}
  (i: int i, j: int j):<> [r:int] (GCD (i, j, r) | int r)
  = "atspre_igcd2"

//

fun nmul (i: Nat, j: Nat):<> Nat = "atspre_nmul"

and ndiv {j:int | j > 0} (i: Nat, j: int j):<> Nat
  = "atspre_ndiv"

and nmod {i,j:int | i >= 0; j > 0}
  (i: int i, j: int j):<> [q,r:int | 0 <= r; r < j; i == q*j + r] int r
  = "atspre_nmod"

fun nmod1 {i,j:int | i >= 0; j > 0}
  (i: int i, j: int j):<> [r:nat | r < j] int r
  = "atspre_nmod1"

overload mod with nmod

(* ****** ****** *)

fun ilt {i,j:int} (i: int i, j: int j):<> bool (i < j)
  = "atspre_ilt"

and ilte {i,j:int} (i: int i, j: int j):<> bool (i <= j)
  = "atspre_ilte"

fun igt {i,j:int} (i: int i, j: int j):<> bool (i > j)
  = "atspre_igt"

and igte {i,j:int} (i: int i, j: int j):<> bool (i >= j)
  = "atspre_igte"

fun ieq {i,j:int} (i: int i, j: int j):<> bool (i == j)
  = "atspre_ieq"

and ineq {i,j:int} (i: int i, j: int j):<> bool (i <> j)
  = "atspre_ineq"

overload < with ilt
overload <= with ilte
overload > with igt
overload >= with igte
overload = with ieq
overload <> with ineq

fun icompare {i,j:int}
  (i: int i, j: int j):<> [k:int | sgn_r (i-j, k)] int k
  = "atspre_icompare"

overload compare with icompare

fun imax {i,j:int}
  (i: int i, j: int j):<> [k:int | max_r (i, j, k)] int k
  = "atspre_imax"

and imin {i,j:int}
  (i: int i, j: int j):<> [k:int | min_r (i, j, k)] int k
  = "atspre_imin"

overload max with imax
overload min with imin

fun ipow (base: Int, exponent: Nat):<> Int = "atspre_ipow"
overload pow with ipow

fun npow (base: Int, exponent: Nat):<> Nat = "atspre_npow"

fun ihalf {i:int} (i: int i):<> [q:int | div_r (i, 2, q)] int q
  = "atspre_ihalf"

fun nhalf {n:nat} (n: int n):<> [q:nat | ndiv_r (n, 2, q)] int q
  = "atspre_nhalf"

(* ****** ****** *)

// unsigned integers (of indexed type)

(* ****** ****** *)

fun uint1_of_int (i: int):<> [i:nat] uint i
  = "atspre_uint1_of_int"
overload uint1_of with uint1_of_int

fun uint1_of_int1 {i:nat} (i: int i):<> uint i
  = "atspre_uint1_of_int1"

fun uint1_of_uint (i: uint):<> [i:nat] uint i
  = "atspre_uint1_of_uint"
overload uint1_of with uint1_of_uint

// arithmetic functions and comparison functions

fun usucc {i:nat} (i: uint i):<> uint (i + 1)
  = "atspre_usucc"
and upred {i:pos} (i: uint i):<> uint (i - 1)
  = "atspre_upred"

overload succ with usucc
overload pred with upred

fun uadd {i,j:nat} (i: uint i, j: uint j):<> uint (i+j)
  = "atspre_uadd"

and usub {i,j:nat | i >= j} (i: uint i, j: uint j):<> uint (i-j)
  = "atspre_usub"

and umul {i,j:nat} (i: uint i, j: uint j):<> uint (i*j)
  = "atspre_umul"

and udiv {i,j:nat | j > 0} (i: uint i, j: uint j):<> uint (i/j)
  = "atspre_udiv"

and umod {i,j:nat | j > 0} (i: uint i, j: uint j)
  :<> [q,r:int | 0 <= r; r < j; i == q*j + r] uint r
  = "atspre_umod"

overload + with uadd
overload - with usub
overload * with umul
overload / with udiv
overload mod with umod

fun uimod {j:nat | j > 0}
  (i: uint, j: int j):<> [r:nat | r < j] int r
  = "atspre_uimod"

overload mod with uimod

fun ult {i,j:nat} (i: uint i, j: uint j):<> bool (i < j)
  = "atspre_ult"

and ulte {i,j:nat} (i: uint i, j: uint j):<> bool (i <= j)
  = "atspre_ulte"

fun ugt {i,j:nat} (i: uint i, j: uint j):<> bool (i > j)
  = "atspre_ugt"

and ugte {i,j:nat} (i: uint i, j: uint j):<> bool (i >= j)
  = "atspre_ugte"

fun ueq {i,j:nat} (i: uint i, j: uint j):<> bool (i == j)
  = "atspre_ueq"

and uneq {i,j:nat} (i: uint i, j: uint j):<> bool (i <> j)
  = "atspre_uneq"

overload < with ult
overload <= with ulte
overload > with ugt
overload >= with ugte
overload = with ueq
overload <> with uneq

fun umax {i,j:nat}
  (i: uint i, j: uint j):<> [k:int | max_r (i, j, k)] uint k
  = "atspre_umax"
and umin {i,j:nat}
  (i: uint i, j: uint j):<> [k:int | min_r (i, j, k)] uint k
  = "atspre_umin"

overload max with umax
overload min with umin

fun uhalf {i:nat} (i: uint i):<> uint (i/2)
  = "atspre_uhalf"

(* ****** ****** *)

// signed long integers

(* ****** ****** *)

typedef lint = int_long_t0ype

// Note that the following coersion is automatic
fun lint_of_int (i: int):<> lint
  = "atspre_lint_of_int"
overload lint_of with lint_of_int

// This function is based on [atol] in [stdlib.h]
fun lint_of_string (s: string):<> lint
  = "atspre_lint_of_string"
overload lint_of with lint_of_string

// arithmetic functions and comparison functions

fun abs_lint (li: lint):<> lint
  = "atspre_abs_lint"
overload abs with abs_lint

fun neg_lint (li: lint):<> lint
  = "atspre_neg_lint"
overload ~ with neg_lint

fun succ_lint (li: lint):<> lint
  = "atspre_succ_lint"

and pred_lint (li: lint):<> lint
  = "atspre_pred_lint"

overload succ with succ_lint
overload pred with pred_lint

fun add_lint_lint (i: lint, j: lint):<> lint
  = "atspre_add_lint_lint"
and sub_lint_lint (i: lint, j: lint):<> lint
  = "atspre_sub_lint_lint"

and mul_lint_lint (i: lint, j: lint):<> lint
  = "atspre_mul_lint_lint"

and div_lint_lint (i: lint, j: lint):<> lint
  = "atspre_div_lint_lint"

and mod_lint_lint (i: lint, j: lint):<> lint
  = "atspre_mod_lint_lint"

overload + with add_lint_lint
overload - with sub_lint_lint
overload * with mul_lint_lint
overload / with div_lint_lint
overload mod with mod_lint_lint

fun lt_lint_lint (i: lint, j: lint):<> bool
  = "atspre_lt_lint_lint"

and lte_lint_lint (i: lint, j: lint):<> bool
  = "atspre_lte_lint_lint"

fun gt_lint_lint (i: lint, j: lint):<> bool
  = "atspre_gt_lint_lint"

and gte_lint_lint (i: lint, j: lint):<> bool
  = "atspre_gte_lint_lint"

fun eq_lint_lint (i: lint, j: lint):<> bool
  = "atspre_eq_lint_lint"

and neq_lint_lint (i: lint, j: lint):<> bool
  = "atspre_neq_lint_lint"

overload < with lt_lint_lint
overload <= with lte_lint_lint
overload > with gt_lint_lint
overload >= with gte_lint_lint
overload = with eq_lint_lint
overload <> with neq_lint_lint

fun max_lint_lint (i: lint, j: lint):<> lint
  = "atspre_max_lint_lint"
and min_lint_lint (i: lint, j: lint):<> lint
  = "atspre_min_lint_lint"

overload max with max_lint_lint
overload min with min_lint_lint

(* ****** ****** *)

symintr fprint_lint

fun fprint0_lint (out: FILEref, x: lint):<!exnref> void
  = "atspre_fprint_lint"

fun fprint1_lint {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: lint):<!exnref> void
  = "atspre_fprint_lint"

overload fprint_lint with fprint0_lint
overload fprint_lint with fprint1_lint
overload fprint with fprint_lint

(* ****** ****** *)

fun print_lint (li: lint):<!ref> void
  = "atspre_print_lint"

and prerr_lint (li: lint):<!ref> void
  = "atspre_prerr_lint"

overload print with print_lint
overload prerr with prerr_lint

(* ****** ****** *)

// stringization

fun tostring_lint (i: lint):<> string
  = "atspre_tostring_lint"

overload tostring with tostring_lint

(* ****** ****** *)

// unsigned long integers

(* ****** ****** *)

typedef ulint = uint_long_t0ype

fun ulint_of_int (i: int):<> ulint
overload ulint_of with ulint_of_int

// arithmetic functions and comparison functions

fun succ_ulint (lu: ulint):<> ulint
  = "atspre_succ_ulint"

and pred_ulint (lu: ulint):<> ulint
  = "atspre_pred_ulint"

overload succ with succ_ulint
overload pred with pred_ulint

fun add_ulint_ulint (i: ulint, j: ulint):<> ulint
  = "atspre_add_ulint_ulint"

and sub_ulint_ulint (i: ulint, j: ulint):<> ulint
  = "atspre_sub_ulint_ulint"

and mul_ulint_ulint (i: ulint, j: ulint):<> ulint
  = "atspre_mul_ulint_ulint"

and div_ulint_ulint (i: ulint, j: ulint):<> ulint
  = "atspre_div_ulint_ulint"

and mod_ulint_ulint (i: ulint, j: ulint):<> ulint
  = "atspre_mod_ulint_ulint"

overload + with add_ulint_ulint
overload - with sub_ulint_ulint
overload * with mul_ulint_ulint
overload / with div_ulint_ulint
overload mod with mod_ulint_ulint

fun lt_ulint_ulint (i: ulint, j: ulint):<> bool
  = "atspre_lt_ulint_ulint"

and lte_ulint_ulint (i: ulint, j: ulint):<> bool
  = "atspre_lte_ulint_ulint"

fun gt_ulint_ulint (i: ulint, j: ulint):<> bool
  = "atspre_gt_ulint_ulint"

and gte_ulint_ulint (i: ulint, j: ulint):<> bool
  = "atspre_gte_ulint_ulint"

fun eq_ulint_ulint (i: ulint, j: ulint):<> bool
  = "atspre_eq_ulint_ulint"

and neq_ulint_ulint (i: ulint, j: ulint):<> bool
  = "atspre_neq_ulint_ulint"

overload < with lt_ulint_ulint
overload <= with lte_ulint_ulint
overload > with gt_ulint_ulint
overload >= with gte_ulint_ulint
overload = with eq_ulint_ulint
overload <> with neq_ulint_ulint

fun max_ulint_ulint (i: ulint, j: ulint):<> ulint
  = "atspre_max_ulint_ulint"

and min_ulint_ulint (i: ulint, j: ulint):<> ulint
  = "atspre_min_ulint_ulint"

overload max with max_ulint_ulint
overload min with min_ulint_ulint

(* ****** ****** *)

symintr fprint_ulint

fun fprint0_ulint (out: FILEref, x: ulint):<!exnref> void
  = "atspre_fprint_ulint"

fun fprint1_ulint {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: ulint):<!exnref> void
  = "atspre_fprint_ulint"

overload fprint_ulint with fprint0_ulint
overload fprint_ulint with fprint1_ulint
overload fprint with fprint_ulint

(* ****** ****** *)

fun print_ulint (lu: ulint):<!ref> void
  = "atspre_print_ulint"

and prerr_ulint (lu: ulint):<!ref> void
  = "atspre_prerr_ulint"

overload print with print_ulint
overload prerr with prerr_ulint

(* ****** ****** *)

// stringization

fun tostring_ulint (i: ulint):<> string
  = "atspre_tostring_ulint"

overload tostring with tostring_ulint

(* ****** ****** *)

// signed long long integers

(* ****** ****** *)

typedef llint = int_long_long_t0ype

// Note that the following coersion is automatic
fun llint_of_int (i: int):<> llint
  = "atspre_llint_of_int"
overload llint_of with llint_of_int

// This function is based on [atoll] in [stdlib.h]
fun llint_of_string (s: string):<> llint
  = "atspre_llint_of_string"
overload llint_of with llint_of_string

// arithmetic functions and comparison functions

fun abs_llint (lli: llint):<> llint
  = "atspre_abs_llint"
overload abs with abs_llint

fun neg_llint (lli: llint):<> llint
  = "atspre_neg_llint"
overload ~ with neg_llint

fun succ_llint (lli: llint):<> llint
  = "atspre_succ_llint"

and pred_llint (lli: llint):<> llint
  = "atspre_pred_llint"

overload succ with succ_llint
overload pred with pred_llint

fun add_llint_llint (i: llint, j: llint):<> llint
  = "atspre_add_llint_llint"

and sub_llint_llint (i: llint, j: llint):<> llint
  = "atspre_sub_llint_llint"

and mul_llint_llint (i: llint, j: llint):<> llint
  = "atspre_mul_llint_llint"

and div_llint_llint (i: llint, j: llint):<> llint
  = "atspre_div_llint_llint"

and mod_llint_llint (i: llint, j: llint):<> llint
  = "atspre_mod_llint_llint"

overload + with add_llint_llint
overload - with sub_llint_llint
overload * with mul_llint_llint
overload / with div_llint_llint
overload mod with mod_llint_llint

fun lt_llint_llint (i: llint, j: llint):<> bool
  = "atspre_lt_llint_llint"

and lte_llint_llint (i: llint, j: llint):<> bool
  = "atspre_lte_llint_llint"

fun gt_llint_llint (i: llint, j: llint):<> bool
  = "atspre_gt_llint_llint"

and gte_llint_llint (i: llint, j: llint):<> bool
  = "atspre_gte_llint_llint"

fun eq_llint_llint (i: llint, j: llint):<> bool
  = "atspre_eq_llint_llint"

and neq_llint_llint (i: llint, j: llint):<> bool
  = "atspre_neq_llint_llint"

overload < with lt_llint_llint
overload <= with lte_llint_llint
overload > with gt_llint_llint
overload >= with gte_llint_llint
overload = with eq_llint_llint
overload <> with neq_llint_llint

fun max_llint_llint (i: llint, j: llint):<> llint
  = "atspre_max_llint_llint"

and min_llint_llint (i: llint, j: llint):<> llint
  = "atspre_min_llint_llint"

overload max with max_llint_llint
overload min with min_llint_llint

(* ****** ****** *)

symintr fprint_llint

fun fprint0_llint (out: FILEref, x: llint):<!exnref> void
  = "atspre_fprint_llint"

fun fprint1_llint {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: llint):<!exnref> void
  = "atspre_fprint_llint"

overload fprint_llint with fprint0_llint
overload fprint_llint with fprint1_llint
overload fprint with fprint_llint

(* ****** ****** *)

fun print_llint (lli: llint):<!ref> void
  = "atspre_print_llint"

and prerr_llint (lli: llint):<!ref> void
  = "atspre_prerr_llint"

overload print with print_llint
overload prerr with prerr_llint

(* ****** ****** *)

// stringization

fun tostring_llint (i: llint):<> string
  = "atspre_tostring_llint"

overload tostring with tostring_llint

(* ****** ****** *)

// unsigned long long integers

(* ****** ****** *)

typedef ullint = uint_long_long_t0ype

fun ullint_of_int (i: int):<> ullint
  = "atspre_ullint_of_int"

overload ullint_of with ullint_of_int

// arithmetic functions and comparison functions

fun succ_ullint (llu: ullint):<> ullint
  = "atspre_succ_ullint"

and pred_ullint (llu: ullint):<> ullint
  = "atspre_pred_ullint"

overload succ with succ_ullint
overload pred with pred_ullint

fun add_ullint_ullint (i: ullint, j: ullint):<> ullint
  = "atspre_add_ullint_ullint"

and sub_ullint_ullint (i: ullint, j: ullint):<> ullint
  = "atspre_sub_ullint_ullint"

and mul_ullint_ullint (i: ullint, j: ullint):<> ullint
  = "atspre_mul_ullint_ullint"

and div_ullint_ullint (i: ullint, j: ullint):<> ullint
  = "atspre_div_ullint_ullint"

and mod_ullint_ullint (i: ullint, j: ullint):<> ullint
  = "atspre_mod_ullint_ullint"

overload + with add_ullint_ullint
overload - with sub_ullint_ullint
overload * with mul_ullint_ullint
overload / with div_ullint_ullint
overload mod with mod_ullint_ullint

fun lt_ullint_ullint (i: ullint, j: ullint):<> bool
  = "atspre_lt_ullint_ullint"

and lte_ullint_ullint (i: ullint, j: ullint):<> bool
  = "atspre_lte_ullint_ullint"

fun gt_ullint_ullint (i: ullint, j: ullint):<> bool
  = "atspre_gt_ullint_ullint"

and gte_ullint_ullint (i: ullint, j: ullint):<> bool
  = "atspre_gte_ullint_ullint"

fun eq_ullint_ullint (i: ullint, j: ullint):<> bool
  = "atspre_eq_ullint_ullint"

and neq_ullint_ullint (i: ullint, j: ullint):<> bool
  = "atspre_neq_ullint_ullint"

overload < with lt_ullint_ullint
overload <= with lte_ullint_ullint
overload > with gt_ullint_ullint
overload >= with gte_ullint_ullint
overload = with eq_ullint_ullint
overload <> with neq_ullint_ullint

fun max_ullint_ullint (i: ullint, j: ullint):<> ullint
  = "atspre_max_ullint_ullint"

and min_ullint_ullint (i: ullint, j: ullint):<> ullint
  = "atspre_min_ullint_ullint"

overload max with max_ullint_ullint
overload min with min_ullint_ullint

(* ****** ****** *)

symintr fprint_ullint

fun fprint0_ullint (out: FILEref, x: ullint):<!exnref> void
  = "atspre_fprint_ullint"

fun fprint1_ullint {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: ullint):<!exnref> void
  = "atspre_fprint_ullint"

overload fprint_ullint with fprint0_ullint
overload fprint_ullint with fprint1_ullint
overload fprint with fprint_ullint

(* ****** ****** *)

fun print_ullint (llu: ullint):<!ref> void
  = "atspre_print_ullint"

and prerr_ullint (llu: ullint):<!ref> void
  = "atspre_prerr_ullint"

overload print with print_ullint
overload prerr with prerr_ullint

(* ****** ****** *)

// stringization

fun tostring_ullint (i: ullint):<> string
  = "atspre_tostring_ullint"

overload tostring with tostring_ullint

(* ****** ****** *)

// signed integers with fixed length

(* ****** ****** *)

typedef int8 = int8_t0ype

symintr int8_of

fun int8_of_int (i: int):<> int8
  = "atspre_int8_of_int"
overload int8_of with int8_of_int

// ------ ------

fun abs_int8 (i: int8):<> int8
  = "atspre_abs_int8"
overload abs with abs_int8

fun neg_int8 (i: int8):<> int8
  = "atspre_neg_int8"
overload ~ with neg_int8

fun succ_int8 (i: int8):<> int8
  = "atspre_succ_int8"

and pred_int8 (i: int8):<> int8
  = "atspre_pred_int8"

overload succ with succ_int8
overload pred with pred_int8

fun add_int8_int8 (i: int8, j: int8):<> int8
 = "atspre_add_int8_int8"

and sub_int8_int8 (i: int8, j: int8):<> int8
  = "atspre_sub_int8_int8"

and mul_int8_int8 (i: int8, j: int8):<> int8
  = "atspre_mul_int8_int8"

and div_int8_int8 (i: int8, j: int8):<> int8
  = "atspre_div_int8_int8"

and mod_int8_int8 (i: int8, j: int8):<> int8
  = "atspre_mod_int8_int8"

overload + with add_int8_int8
overload - with sub_int8_int8
overload * with mul_int8_int8
overload / with div_int8_int8
overload mod with mod_int8_int8 

fun lt_int8_int8 (i: int8, j: int8):<> bool
  = "atspre_lt_int8_int8"

and lte_int8_int8 (i: int8, j: int8):<> bool
  = "atspre_lte_int8_int8"

fun gt_int8_int8 (i: int8, j: int8):<> bool
  = "atspre_gt_int8_int8"

and gte_int8_int8 (i: int8, j: int8):<> bool
  = "atspre_gte_int8_int8"

fun eq_int8_int8 (i: int8, j: int8):<> bool
  = "atspre_eq_int8_int8"

and neq_int8_int8 (i: int8, j: int8):<> bool
  = "atspre_neq_int8_int8"

overload < with lt_int8_int8
overload <= with lte_int8_int8
overload > with gt_int8_int8
overload >= with gte_int8_int8
overload = with eq_int8_int8
overload <> with neq_int8_int8

fun max_int8_int8 (i: int8, j: int8):<> int8
  = "atspre_max_int8_int8"

and min_int8_int8 (i: int8, j: int8):<> int8
  = "atspre_min_int8_int8"

overload max with max_int8_int8
overload min with min_int8_int8

(* ****** ****** *)

symintr fprint_int8

fun fprint0_int8 (out: FILEref, x: int8):<!exnref> void
  = "atspre_fprint_int8"

fun fprint1_int8 {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: int8):<!exnref> void
  = "atspre_fprint_int8"

overload fprint_int8 with fprint0_int8
overload fprint_int8 with fprint1_int8
overload fprint with fprint_int8

(* ****** ****** *)

fun print_int8 (i: int8):<!ref> void
  = "atspre_print_int8"

and prerr_int8 (i: int8):<!ref> void
  = "atspre_prerr_int8"

overload print with print_int8
overload prerr with prerr_int8

(* ****** ****** *)

typedef int16 = int16_t0ype

symintr int16_of

fun int16_of_int (i: int):<> int16
  = "atspre_int16_of_int"
overload int16_of with int16_of_int

fun abs_int16 (i: int16):<> int16
  = "atspre_abs_int16"
overload abs with abs_int16

fun neg_int16 (i: int16):<> int16
  = "atspre_neg_int16"
overload ~ with neg_int16

fun succ_int16 (i: int16):<> int16
  = "atspre_succ_int16"

and pred_int16 (i: int16):<> int16
  = "atspre_pred_int16" 

overload succ with succ_int16
overload pred with pred_int16

fun add_int16_int16 (i: int16, j: int16):<> int16
  = "atspre_add_int16_int16"

and sub_int16_int16 (i: int16, j: int16):<> int16
  = "atspre_sub_int16_int16"

and mul_int16_int16 (i: int16, j: int16):<> int16
  = "atspre_mul_int16_int16"

and div_int16_int16 (i: int16, j: int16):<> int16
  = "atspre_div_int16_int16"

and mod_int16_int16 (i: int16, j: int16):<> int16
  = "atspre_mod_int16_int16"

overload + with add_int16_int16
overload - with sub_int16_int16
overload * with mul_int16_int16
overload / with div_int16_int16
overload mod with mod_int16_int16

fun lt_int16_int16 (i: int16, j: int16):<> bool
  = "atspre_lt_int16_int16"

and lte_int16_int16 (i: int16, j: int16):<> bool
  = "atspre_lte_int16_int16"

fun gt_int16_int16 (i: int16, j: int16):<> bool
  = "atspre_gt_int16_int16"

and gte_int16_int16 (i: int16, j: int16):<> bool
  = "atspre_gte_int16_int16"

fun eq_int16_int16 (i: int16, j: int16):<> bool
  = "atspre_eq_int16_int16"

and neq_int16_int16 (i: int16, j: int16):<> bool
  = "atspre_neq_int16_int16"

overload < with lt_int16_int16
overload <= with lte_int16_int16
overload > with gt_int16_int16
overload >= with gte_int16_int16
overload = with eq_int16_int16
overload <> with neq_int16_int16

fun max_int16_int16 (i: int16, j: int16):<> int16
  = "atspre_max_int16_int16"

and min_int16_int16 (i: int16, j: int16):<> int16
  = "atspre_min_int16_int16"

overload max with max_int16_int16
overload min with min_int16_int16

(* ****** ****** *)

symintr fprint_int16

fun fprint0_int16 (out: FILEref, x: int16):<!exnref> void
  = "atspre_fprint_int16"

fun fprint1_int16 {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: int16):<!exnref> void
  = "atspre_fprint_int16"

overload fprint_int16 with fprint0_int16
overload fprint_int16 with fprint1_int16
overload fprint with fprint_int16

(* ****** ****** *)

fun print_int16 (i: int16):<!ref> void
  = "atspre_print_int16"

and prerr_int16 (i: int16):<!ref> void
  = "atspre_prerr_int16"

overload print with print_int16
overload prerr with prerr_int16

(* ****** ****** *)

typedef int32 = int32_t0ype

symintr int32_of

fun int32_of_int (i: int):<> int32
  = "atspre_int32_of_int"
overload int32_of with int32_of_int

// ------ ------

fun abs_int32 (i: int32):<> int32
  = "atspre_abs_int32"
overload abs with abs_int32

fun neg_int32 (i: int32):<> int32
  = "atspre_neg_int32"
overload ~ with neg_int32

fun succ_int32 (i: int32):<> int32
  = "atspre_succ_int32"

and pred_int32 (i: int32):<> int32
  = "atspre_pred_int32"

overload succ with succ_int32
overload pred with pred_int32

fun add_int32_int32 (i: int32, j: int32):<> int32
  = "atspre_add_int32_int32"

and sub_int32_int32 (i: int32, j: int32):<> int32
  = "atspre_sub_int32_int32"

and mul_int32_int32 (i: int32, j: int32):<> int32
  = "atspre_mul_int32_int32"

and div_int32_int32 (i: int32, j: int32):<> int32
  = "atspre_div_int32_int32"

and mod_int32_int32 (i: int32, j: int32):<> int32
  = "atspre_mod_int32_int32"

overload + with add_int32_int32
overload - with sub_int32_int32
overload * with mul_int32_int32
overload / with div_int32_int32
overload mod with mod_int32_int32

fun lt_int32_int32 (i: int32, j: int32):<> bool
  = "atspre_lt_int32_int32"
and lte_int32_int32 (i: int32, j: int32):<> bool
  = "atspre_lte_int32_int32"
fun gt_int32_int32 (i: int32, j: int32):<> bool
  = "atspre_gt_int32_int32"
and gte_int32_int32 (i: int32, j: int32):<> bool
 = "atspre_gte_int32_int32"

fun eq_int32_int32 (i: int32, j: int32):<> bool
  = "atspre_eq_int32_int32"

and neq_int32_int32 (i: int32, j: int32):<> bool
  = "atspre_neq_int32_int32"

overload < with lt_int32_int32
overload <= with lte_int32_int32
overload > with gt_int32_int32
overload >= with gte_int32_int32
overload = with eq_int32_int32
overload <> with neq_int32_int32

fun max_int32_int32 (i: int32, j: int32):<> int32
  = "atspre_max_int32_int32"

and min_int32_int32 (i: int32, j: int32):<> int32
  = "atspre_min_int32_int32"

overload max with max_int32_int32
overload min with min_int32_int32

(* ****** ****** *)

symintr fprint_int32

fun fprint0_int32 (out: FILEref, x: int32):<!exnref> void
  = "atspre_fprint_int32"

fun fprint1_int32 {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: int32):<!exnref> void
  = "atspre_fprint_int32"

overload fprint_int32 with fprint0_int32
overload fprint_int32 with fprint1_int32
overload fprint with fprint_int32

(* ****** ****** *)

fun print_int32 (i: int32):<!ref> void
  = "atspre_print_int32"

and prerr_int32 (i: int32):<!ref> void
  = "atspre_prerr_int32"

overload print with print_int32
overload prerr with prerr_int32

(* ****** ****** *)

typedef int64 = int64_t0ype

symintr int64_of

fun int64_of_int (i: int):<> int64
  = "atspre_int64_of_int"

overload int64_of with int64_of_int

// ------ ------

fun abs_int64 (i: int64):<> int64
  = "atspre_abs_int64"
overload abs with abs_int64

fun neg_int64 (i: int64):<> int64
  = "atspre_neg_int64"
overload ~ with neg_int64

fun succ_int64 (i: int64):<> int64
  = "atspre_succ_int64"

and pred_int64 (i: int64):<> int64
  = "atspre_pred_int64"

overload succ with succ_int64
overload pred with pred_int64

fun add_int64_int64 (i: int64, j: int64):<> int64
  = "atspre_add_int64_int64"

and sub_int64_int64 (i: int64, j: int64):<> int64
  = "atspre_sub_int64_int64"

and mul_int64_int64 (i: int64, j: int64):<> int64
  = "atspre_mul_int64_int64"

and div_int64_int64 (i: int64, j: int64):<> int64
  = "atspre_div_int64_int64"

and mod_int64_int64 (i: int64, j: int64):<> int64
  = "atspre_mod_int64_int64"

overload + with add_int64_int64
overload - with sub_int64_int64
overload * with mul_int64_int64
overload / with div_int64_int64
overload mod with mod_int64_int64

fun lt_int64_int64 (i: int64, j: int64):<> bool
  = "atspre_lt_int64_int64"

and lte_int64_int64 (i: int64, j: int64):<> bool
  = "atspre_lte_int64_int64"

fun gt_int64_int64 (i: int64, j: int64):<> bool
  = "atspre_gt_int64_int64"

and gte_int64_int64 (i: int64, j: int64):<> bool
  = "atspre_gte_int64_int64"

fun eq_int64_int64 (i: int64, j: int64):<> bool
  = "atspre_eq_int64_int64"

and neq_int64_int64 (i: int64, j: int64):<> bool
  = "atspre_neq_int64_int64"

overload < with lt_int64_int64
overload <= with lte_int64_int64
overload > with gt_int64_int64
overload >= with gte_int64_int64
overload = with eq_int64_int64
overload <> with neq_int64_int64

fun max_int64_int64 (i: int64, j: int64):<> int64
  = "atspre_max_int64_int64"
and min_int64_int64 (i: int64, j: int64):<> int64
  = "atspre_min_int64_int64"

overload max with max_int64_int64
overload min with min_int64_int64

(* ****** ****** *)

symintr fprint_int64

fun fprint0_int64 (out: FILEref, x: int64):<!exnref> void
  = "atspre_fprint_int64"

fun fprint1_int64 {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, x: int64):<!exnref> void
  = "atspre_fprint_int64"

overload fprint_int64 with fprint0_int64
overload fprint_int64 with fprint1_int64
overload fprint with fprint_int64

(* ****** ****** *)

fun print_int64 (i: int64):<!ref> void
  = "atspre_print_int64"

and prerr_int64 (i: int64):<!ref> void
  = "atspre_prerr_int64"

overload print with print_int64
overload prerr with prerr_int64

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

#print "Loading [integer.sats] finishes!\n"

#endif

(* end of [integer.sats] *)
