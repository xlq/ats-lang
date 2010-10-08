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

abst@ype pthread_t = $extype "pthread_t"
castfn int_of_pthread (x: pthread_t):<> int
castfn lint_of_pthread (x: pthread_t):<> lint
fun pthread_self (): pthread_t = "#atslib_pthread_self"

(* ****** ****** *)

//
// HX: this one is implemented in [$ATSHOME/ccomp/runtime/ats_prelude.c]
//
fun pthread_create_detached {vt:viewtype}
  (f: (vt) -<fun1> void, env: !vt >> opt (vt, i <> 0)): #[i:int] int i
  = "ats_pthread_create_detached"
// end of [pthread_create_detached]

//
// HX: [pthread_create_detached_exn] is implemented in
// [$ATSHOME/libc/DATS/pthread.dats]
//
fun pthread_create_detached_exn {vt:viewtype}
  (f: (vt) -<fun1> void, env: vt): void // env is to be processed by f
// end of [pthread_create_detached_exn]

//
// HX: [pthread_create_detached_cloptr] is implemented in
// [$ATSHOME/libc/DATS/pthread.dats]
//
fun pthread_create_detached_cloptr
  (f: () -<lincloptr1> void): void // closure must be freed to avoid leak!
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

(* ****** ****** *)
//
// HX: this one does initialization and locking
//
fun pthread_mutex_init_locked
  {v:view} (mut: &mutex_vt? >> opt (mutex_vt(v), i==0)): #[i:int] int i
  = "atslib_pthread_mutex_init_locked"
// end of [pthread_mutex_init_locked]

fun pthread_mutex_init_unlocked {v:view} (
    pf: !v >> option_v (v, i > 0)
  | mut: &mutex_vt? >> opt (mutex_vt(v), i==0)
  ) : #[i:int] int i = "atslib_pthread_mutex_init_unlocked"
// end of [pthread_mutex_init_unlocked]

(* ****** ****** *)

fun pthread_mutex_create_locked {v:view} {l:addr}
  (): [l:addr] (option_v ((free_gc_v l, mutex_vt v @ l), l > null) | ptr l)
  = "atslib_pthread_mutex_create_locked"

fun pthread_mutex_create_unlocked {v:view} {l:addr}
  (pf: !v >> option_v (v, l==null) | (*none*))
  : [l:addr] (option_v ((free_gc_v l, mutex_vt v @ l), l > null) | ptr l)
  = "atslib_pthread_mutex_create_unlocked"

(* ****** ****** *)

//
// HX-2010-03-14:
// it should be called 'uninitialize' or 'clear' in ATS
//
fun pthread_mutex_destroy {v:view} {l:addr}
  (p: &mutex_vt(v) >> opt (mutex_vt(v), i > 0)): #[i:int] (option_v (v, i==0) | int i)
  = "atslib_pthread_mutex_destroy"
// end of [pthread_mutex_destroy]

(* ****** ****** *)

fun pthread_mutex_lock
  {v:view} (mutex: &mutex_vt v):<> [i:int] (option_v (v, i==0) | int i)
  = "#atslib_pthread_mutex_lock" // macro!
fun pthread_mutex_unlock {v:view}
  (resource: v | mutex: &mutex_vt v):<> [i:int] (option_v (v, i > 0) | int i)
  = "#atslib_pthread_mutex_unlock" // macro!

(* ****** ****** *)

absviewt@ype
pthread_cond_viewt0ype = $extype "pthread_cond_t"
stadef cond_vt = pthread_cond_viewt0ype

(* ****** ****** *)

fun pthread_cond_create ()
  : [l:addr] (option_v ((free_gc_v l, cond_vt @ l), l > null) | ptr l)
  = "atslib_pthread_cond_create"

fun pthread_cond_wait {v:view}
  (resource: !v | cond: &cond_vt, p: &mutex_vt v) :<> int
  = "#atslib_pthread_cond_wait"
// end of [pthread_cond_wait]

fun pthread_cond_signal
  (cond: &cond_vt):<> int = "#atslib_pthread_cond_signal"
// end of [pthread_cond_signal]

fun pthread_cond_broadcast
  (cond: &cond_vt):<> int = "#atslib_pthread_cond_broadcast"
// end of [pthread_cond_broadcast]

(* ****** ****** *)

//
// HX-2010-10: refcounted mutex
//
absviewtype
mutexref_view_type (v:view, l:addr) // a boxed type
// end of [absviewtype]
stadef mutexref_t = mutexref_view_type

castfn mutexref_get_view_ptr
  {v:view} {l1:addr} (x: mutexref_t (v, l1))
  :<> [l2:addr] (minus (mutexref_t (v, l1), mutex_vt v @ l2), mutex_vt v @ l2 | ptr l2)
// end of [mutexref_get_view_ptr]

fun mutexref_lock {v:view} {l:addr}
  (x: !mutexref_t (v, l)): (v | void) = "atslib_pthread_mutexref_lock"
// end of [mutexref_lock]

fun mutexref_unlock {v:view} {l:addr}
  (pf: v | x: !mutexref_t (v, l)): void = "atslib_pthread_mutexref_unlock"
// end of [mutexref_unlock]

fun mutexref_ref
  {v:view} {l:addr} (
    x: !mutexref_t (v, l)
  ) :<> mutexref_t (v, l) = "atslib_pthread_mutexref_ref"
// end of [mutexref_ref]

fun mutexref_unref
  {v:view} {l:addr}
  (x: mutexref_t (v, l)):<> void = "atslib_pthread_mutexref_unref"
// end of [mutexref_unref]

(* ****** ****** *)

(* end of [pthread.sats] *)
