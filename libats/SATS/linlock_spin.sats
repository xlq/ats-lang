(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2011 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
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
//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//
(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no static loading at run-time

(* ****** ****** *)

%{#
#include "libats/CATS/linlock_spin.cats"
%} // end of [%{#]

(* ****** ****** *)

abstype
lock_view_type
  (v:view, l:addr)
stadef lock = lock_view_type
typedef lock0 (v:view) = [l:addr] lock (v, l)
typedef lock1 (v:view) = [l:addr | l > null] lock (v, l)

(* ****** ****** *)

castfn ptr_of_lock
  {v:view} {l:addr} (x: lock (v, l)):<> ptr (l)
// end of [ptr_of_lock]

(* ****** ****** *)

fun linlock_create_locked
  {v:view} (
  pshared: int
) : lock0 (v)
  = "atslib_linlock_create_locked"
// end of [linlock_create_locked]

fun linlock_create_unlocked
  {v:view} (
  pf: !v >> option_v (v, l==null) | pshared: int
) : #[l:addr] lock (v, l)
  = "atslib_linlock_create_unlocked"
// end of [linlock_create_unlocked]

(* ****** ****** *)

fun linlock_destroy
  {v:view} (x: lock1 (v)): (v | void)
// end of [linlock_destroy]

(* ****** ****** *)

fun linlock_acquire
  {v:view} {l:agz} (x: lock (v, l)): (v | void)
  = "mac#atslib_linlock_acquire"
// end of [linlock_acquire]

fun linlock_acquire_try
  {v:view} {l:agz}
  (x: lock (v, l)): [i:nat] (option_v (v, i==0) | int i)
  = "mac#atslib_linlock_acquire_try"
// end of [linlock_acquire_try]

fun linlock_release
  {v:view} {l:agz} (pf: v | x: lock (v, l)): void
  = "mac#atslib_linlock_release"
// end of [linlock_release]

(* ****** ****** *)

(* end of [linlock_spin.sats] *)
