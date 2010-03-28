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
  = $extype "ats_libats_linstack_arr_STACK_vt"
// end of [STACK]
typedef STACK0 (a:viewt@ype) = STACK (a, 0, 0)?

(* ****** ****** *)

// initializing to a stack of capacity [m]
fun{a:viewt@ype} stack_initialize {m:nat}
  (q: &STACK0 a >> STACK (a, m, 0), m: size_t m):<> void
// end of [linstackarr_initialize]

(* ****** ****** *)

fun{a:viewt@ype}
stack_insert (*last*)
  {m,n:nat | m > n}
  (q: &STACK (a, m, n) >> STACK (a, m, n+1), x: a):<> void
// end of [stack_insert]

fun{a:viewt@ype}
stack_remove (*first*)
  {m,n:nat | n > 0} (q: &STACK (a, m, n) >> STACK (a, m, n-1)):<> a
// end of [stack_remove]

(* ****** ****** *)

fun stack_uninitialize {a:t@ype}
  {m,n:nat} {l:addr} (q: &STACK (a, m, n) >> STACK0 a):<> void
// end of [stack_uninitialize]

//
// uninitializeing an empty stack of capacity [m]
//
fun stack_uninitialize_vt {a:viewt@ype}
  {m:nat} {l:addr} (q: &STACK (a, m, 0) >> STACK0 a):<> void
// end of [stack_unintialize_vt]

(* ****** ****** *)

(* end of [linstack_arr.sats] *)
