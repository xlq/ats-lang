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
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
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
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(*
**
** A array-based stack implementation
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: March, 2010 // based on a version done in October, 2008
**
*)

(* ****** ****** *)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

%{#
#include "libats/CATS/linstack_arr.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time

(* ****** ****** *)
//
// a: item type
// m: maximal capacity
// n: current size
//
absviewt@ype STACK
  (a:viewt@ype+, m: int, n: int)
  = $extype "atslib_linstack_arr_STACK"
// end of [STACK]
typedef STACK0 (a:viewt@ype) = STACK (a, 0, 0)?

(* ****** ****** *)

fun stack_get_cap {a:viewt@ype} {m,n:nat} (s: &STACK (a, m, n)):<> size_t m
fun stack_get_size {a:viewt@ype} {m,n:nat} (s: &STACK (a, m, n)):<> size_t n

(* ****** ****** *)

fun stack_is_empty {a:viewt@ype} {m,n:nat} (s: &STACK (a, m, n)):<> bool (n==0)
fun stack_isnot_empty {a:viewt@ype} {m,n:nat} (s: &STACK (a, m, n)):<> bool (n > 0)

fun stack_is_full {a:viewt@ype} {m,n:nat} (s: &STACK (a, m, n)):<> bool (m==n)
fun stack_isnot_full {a:viewt@ype} {m,n:nat} (s: &STACK (a, m, n)):<> bool (m > n)

(* ****** ****** *)

// initializing to a stack of capacity [m]
fun{a:viewt@ype} stack_initialize {m:nat}
  (s: &STACK0 a >> STACK (a, m, 0), m: size_t m):<> void
// end of [linstackarr_initialize]

(* ****** ****** *)

fun{a:viewt@ype}
stack_insert (*last*) // HX: stack_push
  {m,n:nat | m > n}
  (s: &STACK (a, m, n) >> STACK (a, m, n+1), x: a):<> void
// end of [stack_insert]

fun{a:viewt@ype}
stack_remove (*first*) // HX: stack_pop
  {m,n:nat | n > 0} (s: &STACK (a, m, n) >> STACK (a, m, n-1)):<> a
// end of [stack_remove]

(* ****** ****** *)

fun{a:t@ype}
stack_clear
  {m:int} {n1,n2:nat | n1 >= n2}
  (s: &STACK (a, m, n1) >> STACK (a, m, n2), n2: size_t n2):<> void
// end of [stack_clear]

(* ****** ****** *)

fun stack_uninitialize {a:t@ype}
  {m,n:nat} {l:addr} (s: &STACK (a, m, n) >> STACK0 a):<> void
// end of [stack_uninitialize]

//
// uninitializeing an empty stack of capacity [m]
//
fun stack_uninitialize_vt {a:viewt@ype}
  {m:nat} {l:addr} (s: &STACK (a, m, 0) >> STACK0 a):<> void
// end of [stack_unintialize_vt]

(* ****** ****** *)

(* end of [linstack_arr.sats] *)
