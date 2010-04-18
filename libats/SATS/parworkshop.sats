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
** Copyright (C) 2002-2009 Hongwei Xi, Boston University
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
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Start Time: March, 2010
**
*)

(* ****** ****** *)

%{#
#include "libc/CATS/pthread.cats"
#include "libats/CATS/parworkshop.cats"
%} // end of [%{#]

(* ****** ****** *)

absviewtype WORKSHOPptr
(a:viewt@ype, l:addr) // boxed linear type
viewtypedef WORKSHOPptr (a:viewt@ype) =
  [l:addr] WORKSHOPptr (a, l) // note that [l > null] always holds 
// end of [WORKSHOPptr]

(* ****** ****** *)

fun{a:viewt@ype}
workshop_make {n:pos} (
  qsz: size_t n
, fwork: {l:addr} (!WORKSHOPptr (a, l), &a >> a?) -<fun1> int
) : WORKSHOPptr a
// end of [workshop_make]

fun workshop_make_tsz {a:viewt@ype} {n:pos} (
  qsz: size_t n
, fwork: {l:addr} (!WORKSHOPptr (a, l), &a >> a?) -<fun1> int
, tsz: sizeof_t a
) : WORKSHOPptr a
  = "atslib_parworkshop_workshop_make_tsz"
// end of [workshop_make_tsz]

(* ****** ****** *)

//
// locking/unlocking
//
fun workshop_nworker_get
  {a:viewt@ype} {l:addr} (ws: !WORKSHOPptr (a, l)):<> int
  = "atslib_parworkshop_workshop_nworker_get"
// end of [workshop_nworker_get]

//
// locking/unlocking
//
fun workshop_npaused_get
  {a:viewt@ype} {l:addr} (ws: !WORKSHOPptr (a, l)):<> int
  = "atslib_parworkshop_workshop_npaused_get"
// end of [workshop_npaused_get]

//
// locking/unlocking
//
fun workshop_nblocked_get
  {a:viewt@ype} {l:addr} (ws: !WORKSHOPptr (a, l)):<> int
  = "atslib_parworkshop_workshop_nblocked_get"
// end of [workshop_nblocked_get]

(* ****** ****** *)

fun{a:viewt@ype}
workshop_add_worker
  {l:addr} (ws: !WORKSHOPptr (a, l)): int(*err*)
// end of [workshop_add_worker]

fun{a:viewt@ype}
workshop_add_nworker
  {l:addr} {n:nat} (ws: !WORKSHOPptr (a, l), n: int n): int(*err*)
// end of [workshop_add_nworker]

(* ****** ****** *)

fun{a:viewt@ype}
workshop_insert_work
  {l:addr} (ws: !WORKSHOPptr (a, l), work: a): void
// end of [workshop_insert_work]

fun{a:viewt@ype}
workshop_remove_work {l:addr} (ws: !WORKSHOPptr (a, l)): a

(* ****** ****** *)

fun workshop_wait_quit_all
  {a:viewt@ype} {l:addr} (ws: !WORKSHOPptr (a, l)): void
// end of [workshop_wait_quit_all]

fun workshop_wait_paused_all
  {a:viewt@ype} {l:addr} (ws: !WORKSHOPptr (a, l)): void
// end of [workshop_wait_paused_all]

fun workshop_resume_paused_all
  {a:viewt@ype} {l:addr} (ws: !WORKSHOPptr (a, l)): void
// end of [workshop_resume_paused_all]

fun workshop_wait_blocked_all
  {a:viewt@ype} {l:addr} (ws: !WORKSHOPptr (a, l)): void
// end of [workshop_wait_blocked_all]

(* ****** ****** *)

//
// HX-2010-03-31:
// freeing a workshop must wait until all workers quit
//

fun workshop_free
  {a:t@ype} {l:addr} (ws: WORKSHOPptr (a, l)): void
  = "atslib_parworkshop_workshop_free"
// end of [workshop_free]

fun workshop_free_vt_exn
  {a:viewt@ype} {l:addr} (ws: WORKSHOPptr (a, l)): void
  = "atslib_parworkshop_workshop_free_vt_exn"
// end of [workshop_free_vt_exn]

(* ****** ****** *)

(* end of [parworkshop.sats] *)
