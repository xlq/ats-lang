(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#
#include "libc/CATS/stdlib.cats"
%} // end of [%{#]

(* ****** ****** *)

staload FCNTL = "libc/SATS/fcntl.sats" // for [mkstemp]
stadef open_v = $FCNTL.open_v

(* ****** ****** *)

macdef EXIT_SUCCESS = $extval (int, "EXIT_SUCCESS")
macdef EXIT_FAILURE = $extval (int, "EXIT_FAILURE")

(* ****** ****** *)

fun atoi (s: string):<> int = "#atslib_atoi"
fun atof (s: string):<> double = "#atslib_atof"
fun atol (s: string):<> lint = "#atslib_atol"
fun atoll (s: string):<> llint = "#atslib_atoll"

(* ****** ****** *)

fun getenv (name: string)
  : [l:addr] (strptr l -<lin,prf> void | strptr l) = "#atslib_getenv"
// end of [atslib_getenv]

//
// HX-201-09-29:
// [nameval] is copied and put into the environment.
// potential memory leak!!! 
//
fun putenv {l:agz} (nameval: !strptr l): int // 0/nz : succ/fail

//
// HX-2010-09-29:
// [name] and [value] are copied into the environment
// also note that the original value may be leaked out!!!
//
fun setenv // 0/-1 : succ/fail
  (name: string, value: string, overwrite: int): int = "#atslib_setenv"
// end of [atslib_setenv]

fun unsetenv (name: string): int = "#atslib_unsetenv" // 0/-1: succ/fail

(* ****** ****** *)

fun atexit_err (f: () -> void): int = "#atslib_atexit_err" // !macro
fun atexit_exn (f: () -> void): void = "atslib_atexit_exn" // !function

(* ****** ****** *)

fun system (cmd: string): int = "#atslib_system"

(* ****** ****** *)

fun mkstemp {m,n:nat}
  (path: string): [i: int] (open_v (i) | int i) = "#atslib_mkstemp"
// end of [mkstemp]

(* ****** ****** *)
//
// HX: this one returns an integer (not a pointer)!
//
fun bsearch {a:viewt@ype} {n:nat} (
    key: &a
  , base: &(@[a][n]), nmemb: size_t n, size: sizeof_t a
  , compar: (&a, &a) -<fun> int
  ) :<> intBtw (~1, n)
  = "atslib_bsearch" // function!
// end of [bsearch]

(* ****** ****** *)
//
// HX: a generic quicksort function
//
fun qsort
  {a:viewt@ype} {n:nat} (
    base: &(@[a][n])
  , nmemb: size_t n, size: sizeof_t a
  , compar: (&a, &a) -<fun> int
  ) :<> void
  = "atslib_qsort" // function!
// end of [qsort]

(* ****** ****** *)

(* end of [stdlib.sats] *)
