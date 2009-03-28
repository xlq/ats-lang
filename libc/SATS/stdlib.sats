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

%{#

#include "libc/CATS/stdlib.cats"

%}

(* ****** ****** *)

fun atoi (s: string):<> int = "atslib_atoi"
fun atof (s: string):<> double = "atslib_atof"
fun atol (s: string):<> lint = "atslib_atol"
fun atoll (s: string):<> llint = "atslib_atoll"

(* ****** ****** *)

fun getenv_opt (name: string):<!ref> Stropt = "atslib_getenv_opt"
fun getenv_exn (name: string):<!exnref> String = "atslib_getenv_exn"

fun setenv_err (name: string, value: string, overwrite: int): int
  = "atslib_setenv_err"

fun setenv_exn (name: string, value: string, overwrite: int): void
  = "atslib_setenv_exn"

(* ****** ****** *)

// a generic binary search function

fun bsearch {a:viewt@ype} {n:nat} (
    key: &a
  , base: &(@[a][n]), nmemb: size_t n, size: sizeof_t a
  , compar: (&a, &a) -<fun1> int
  ) : intBtw (~1, n)
  = "atslib_bsearch"

(* ****** ****** *)

// a generic quicksort function

fun qsort {a:viewt@ype} {n:nat} (
    base: &(@[a][n])
  , nmemb: size_t n, size: sizeof_t a
  , compar: (&a, &a) -<fun1> int
  ) : void
  = "atslib_qsort"

(* ****** ****** *)

(* end of [stdlib.sats] *)
