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
** An array-based queue implementation
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
#include "libats/ngc/CATS/queue_arr.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time

(* ****** ****** *)
//
// HX:
// a: item type
// m: maximal capacity
// n: current size
//
absviewt@ype QUEUE
  (a:viewt@ype+, m: int, n: int)
  = $extype "atslib_ngc_queue_arr_QUEUE"
// end of [QUEUE]
typedef QUEUE0 (a:viewt@ype) = QUEUE (a, 0, 0)?
viewtypedef QUEUE1 (a:viewt@ype) = [m,n:nat] QUEUE (a, m, n)

(* ****** ****** *)

prfun queue_param_lemma
  {a:viewt@ype} {m,n:int}
  (x: &QUEUE (a, m, n)): [0 <= n; n <= m] void
// end of [queue_lemma]

(* ****** ****** *)

fun queue_cap {a:viewt@ype}
  {m,n:int} (q: &QUEUE (a, m, n)):<> size_t m
fun queue_size {a:viewt@ype}
  {m,n:int} (q: &QUEUE (a, m, n)):<> size_t n

(* ****** ****** *)

fun queue_is_empty {a:viewt@ype}
  {m,n:nat} (q: &QUEUE (a, m, n)):<> bool (n <= 0)
fun queue_isnot_empty {a:viewt@ype}
  {m,n:nat} (q: &QUEUE (a, m, n)):<> bool (n > 0)

fun queue_is_full {a:viewt@ype}
  {m,n:nat} (q: &QUEUE (a, m, n)):<> bool (m <= n)
fun queue_isnot_full {a:viewt@ype}
  {m,n:nat} (q: &QUEUE (a, m, n)):<> bool (m > n)

(* ****** ****** *)
//
// HX: initializing to a queue of capacity [m]
//
fun{a:viewt@ype}
queue_initialize
  {m:nat} {l:addr} (
  pfgc: free_gc_v (a, m, l), pfarr: array_v (a?, m, l)
| q: &QUEUE0 a >> QUEUE (a, m, 0), m: size_t m, p: ptr l
) :<> void // end of [queue_initialize]

fun queue_initialize_tsz
  {a:viewt@ype} {m:nat} {l:addr} (
  pfgc: free_gc_v (a, m, l), pfarr: array_v (a?, m, l)
| q: &QUEUE0 a >> QUEUE (a, m, 0), m: size_t m, p: ptr l, tsz: sizeof_t a
) :<> void
  = "atslib_ngc_queue_arr_queue_initialize_tsz"
// end of [queue_initialize_tsz]

(* ****** ****** *)
//
// HX: uninitializeing a queue of capacity [m]
//
fun queue_uninitialize
  {a:t@ype}
  {m,n:nat} (
  q: &QUEUE (a, m, n) >> QUEUE0 a
) :<> [l:addr] (
  free_gc_v (a, m, l), array_v (a?, m, l)
| ptr l
) = "atslib_ngc_queue_arr_queue_uninitialize"
// end of [queue_uninitialize]

//
// HX: uninitializeing an empty queue of capacity [m]
//
fun queue_uninitialize_vt
  {a:viewt@ype}
  {m:nat} (
  q: &QUEUE (a, m, 0) >> QUEUE0 a
) :<> [l:addr] (
  free_gc_v (a, m, l), array_v (a?, m, l)
| ptr l
) // end of [queue_uninitialize_vt]

(* ****** ****** *)

fun{a:viewt@ype}
queue_enque (*last*)
  {m,n:nat | m > n}
  (q: &QUEUE (a, m, n) >> QUEUE (a, m, n+1), x: a):<> void
// end of [queue_enque]

fun{a:viewt@ype}
queue_enque_many
  {m,n:nat}
  {k:nat | n+k <= m} (
  q: &QUEUE (a, m, n) >> QUEUE (a, m, n+k)
, k: size_t k
, xs: &(@[a][k]) >> @[a?!][k]
) :<> void // end of [queue_enque_many]

fun
queue_enque_many_tsz
  {a:viewt@ype}
  {m,n:nat}
  {k:nat | n+k <= m} (
  q: &QUEUE (a, m, n) >> QUEUE (a, m, n+k)
, k: size_t k
, xs: &(@[a][k]) >> @[a?!][k]
, tsz: sizeof_t (a)
) :<> void // end of [queue_enque_many_tsz]
  = "atslib_ngc_queue_arr_queue_enque_many_tsz"

(* ****** ****** *)

fun{a:viewt@ype}
queue_deque (*first*)
  {m,n:nat | n > 0} (
  q: &QUEUE (a, m, n) >> QUEUE (a, m, n-1)
) :<> a // end of [queue_deque]

fun{a:viewt@ype}
queue_deque_many
  {m,n:nat}
  {k:nat | k <= n} (
  q: &QUEUE (a, m, n) >> QUEUE (a, m, n-k)
, k: size_t k
, xs: &(@[a?][k]) >> @[a][k]
) :<> void // end of [queue_deque_many]

fun
queue_deque_many_tsz
  {a:viewt@ype}
  {m,n:nat}
  {k:nat | k <= n} (
  q: &QUEUE (a, m, n) >> QUEUE (a, m, n-k)
, k: size_t k
, xs: &(@[a?][k]) >> @[a][k]
, tsz: sizeof_t a
) :<> void // end of [queue_deque_many_tsz]
  = "atslib_ngc_queue_arr_queue_deque_many_tsz"

(* ****** ****** *)

fun{a:viewt@ype}
queue_update_capacity
  {m1,n:nat}
  {m2:nat | n <= m2}
  {l:addr} (
  pfgc: free_gc_v (a, m2, l)
, pfarr: array_v (a?, m2, l)
| q: &QUEUE (a, m1, n) >> QUEUE (a, m2, n)
, m2: size_t (m2), parr: ptr l
) : [l:addr] (
  free_gc_v (a, m1, l), array_v (a?!, m1, l)
| ptr l
) // end of [queue_update_capcity]

fun
queue_update_capacity_tsz
  {a:viewt@ype}
  {m1,n:nat}
  {m2:nat | n <= m2}
  {l:addr} (
  pfgc: free_gc_v (a, m2, l)
, pfarr: array_v (a?, m2, l)
| q: &QUEUE (a, m1, n) >> QUEUE (a, m2, n)
, m2: size_t (m2), parr: ptr l
, tsz: sizeof_t (a)
) : [l:addr] (
  free_gc_v (a, m1, l), array_v (a?!, m1, l)
| ptr l
) = "atslib_ngc_queue_arr_queue_update_capacity_tsz"

(* ****** ****** *)

(* end of [queue_arr.sats] *)
