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

//
// some history:
//
// Rui Shi and Hongwei Xi first did [pthread] in ATS/Proto, on which
// this version is primarily based.
//

(* ****** ****** *)

%{#
#include "libc/CATS/pthread.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for static loading at run-time

(* ****** ****** *)

// implemented in [$ATSHOME/ccomp/runtime/ats_prelude.c]
fun pthread_create_detached {vt:viewtype}
  (f: (vt) -<fun1> void, env: vt): void // env is to be processed by f
  = "ats_pthread_create_detached"
// end of [pthread_create_detached]

fun pthread_create_detached_cloptr
  (f: () -<lin,cloptr1> void): void // closure must be freed to avoid leak!
// end of [pthread_create_detached_cloptr]

//
// this function does not return to the caller
// implemented in [$ATSHOME/ccomp/runtime/ats_prelude.c]
//
fun pthread_exit (): void = "ats_pthread_exit" // end of [pthread_exit]

(* ****** ****** *)

absviewt@ype
pthread_mutex_view_viewt0ype
  (v:view) = $extype "pthread_mutex_t"
// end of [absviewt@ype]
stadef mutex_vt = pthread_mutex_view_viewt0ype

absviewtype
pthread_mutexref_view_type (v:view, l:addr) // a boxed type
// end of [absviewt@ype]
stadef mutexref_t = pthread_mutexref_view_type
viewtypedef mutexref_t (v:view) = [l:addr] mutexref_t (v, l)

castfn mutexref_get_view_ptr
  {v:view} {l:addr} (x: mutexref_t (v, l))
  : (minus (mutexref_t (v, l), mutex_vt v @ l), mutex_vt v @ l | ptr l)
// end of [mutexref_get_view_ptr]

castfn mutexref_make_view_ptr
  {v:view} {l:addr} (pf: mutex_vt v @ l | p: ptr l):<> mutexref_t (v, l)
// end of [mutexref_make_view_ptr]

(* ****** ****** *)

fun pthread_mutex_init_locked
  {v:view} (mut: &mutex_vt? >> mutex_vt v): void
  = "atslib_pthread_mutex_init_locked"
// end of [pthread_mutex_init_locked]

fun pthread_mutex_init_unlocked
  {v:view} (pf_resource: v | mut: &mutex_vt? >> mutex_vt v): void
  = "atslib_pthread_mutex_init_unlocked"
// end of [pthread_mutex_init_unlocked]

(* ****** ****** *)

fun pthread_mutex_create_locked {v:view} {l:addr}
  (): [l:addr] @(free_gc_v l, mutex_vt v @ l | ptr l)
  = "atslib_pthread_mutex_create_locked"

fun pthread_mutex_create_unlocked {v:view} {l:addr}
  (resource: v | (*none*)): [l:addr] @(free_gc_v l, mutex_vt v @ l | ptr l)
  = "atslib_pthread_mutex_create_unlocked"

(* ****** ****** *)

//
// HX-2010-03-14:
// it should be called uninitialize in ATS
//
fun pthread_mutex_destroy {v:view} {l:addr}
  (pf: !mutex_vt v @ l >> mutex_vt? @ l | p: ptr l): (v | void)
  = "atslib_pthread_mutex_destroy"
// end of [pthread_mutex_destroy]

(* ****** ****** *)

fun pthread_mutex_lock
  {v:view} (mutex: &mutex_vt v): (v | void)
  = "atslib_pthread_mutex_lock"

fun pthread_mutex_unlock {v:view}
  (resource: v | mutex: &mutex_vt v): void
  = "atslib_pthread_mutex_unlock"

(* ****** ****** *)

absviewt@ype pthread_cond_viewt0ype = $extype "pthread_cond_t"
stadef cond_vt = pthread_cond_viewt0ype

(* ****** ****** *)

fun pthread_cond_create ()
  : [l:addr] @(free_gc_v l, cond_vt @ l | ptr l)
  = "atslib_pthread_cond_create"

fun pthread_cond_wait_mutex {v:view}
  (resource: !v | cond: &cond_vt, p: &mutex_vt v) :<> void
  = "atslib_pthread_cond_wait_mutex"

fun pthread_cond_signal (cond: &cond_vt):<> void
  = "atslib_pthread_cond_signal"

fun pthread_cond_broadcast (cond: &cond_vt):<> void
  = "atslib_pthread_cond_broadcast"

(* ****** ****** *)

(* end of [pthread.sats] *)
