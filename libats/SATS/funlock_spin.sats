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
#include "libats/CATS/funlock_spin.cats"
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

fun funlock_create_locked
  {v:view} (
  pshared: int
) : lock0 (v)
  = "atslib_funlock_create_locked"
// end of [funlock_create_locked]

fun funlock_create_unlocked
  {v:view} (
  pf: !v >> option_v (v, l==null) | pshared: int
) : #[l:addr] lock (v, l)
  = "atslib_funlock_create_unlocked"
// end of [funlock_create_unlocked]

(* ****** ****** *)

fun funlock_destroy
  {v:view} (x: lock1 (v)): (v | void)
// end of [funlock_destroy]

(* ****** ****** *)

fun funlock_acquire
  {v:view} {l:agz} (x: lock (v, l)): (v | void)
  = "mac#atslib_funlock_acquire"
// end of [funlock_acquire]

fun funlock_acquire_try
  {v:view} {l:agz}
  (x: lock (v, l)): [i:nat] (option_v (v, i==0) | int i)
  = "mac#atslib_funlock_acquire_try"
// end of [funlock_acquire_try]

fun funlock_release
  {v:view} {l:agz} (pf: v | x: lock (v, l)): void
  = "mac#atslib_funlock_release"
// end of [funlock_release]

(* ****** ****** *)

(* end of [funlock_spin.sats] *)
