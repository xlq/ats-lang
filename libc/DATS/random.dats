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
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

staload "libc/sys/SATS/time.sats" // for gettimeofday
staload "libc/sys/SATS/types.sats" // for several lint_of* functions

(* ****** ****** *)

staload "libc/SATS/random.sats"

(* ****** ****** *)

implement
srand48_with_gettimeofday () = let
  var tv: timeval?
  val err = gettimeofday (tv)
  val () = if err = 0 then let
    prval () = opt_unsome {timeval} (tv)
    val seed = (lint_of)tv.tv_sec * 1000000L + (lint_of)tv.tv_usec
    val () = srand48 (seed)
  in
    // nothing
  end else let
    prval () = opt_unnone {timeval} (tv)
  in
    // nothing
  end // end of [if]
in
  err (* 0/-1 : succ/fail *)
end // end of [srand48_with_gettimeofday]

(* ****** ****** *)

implement
randint {n} (n) = let
  val d01 = drand48 ()
  val r = int_of(d01 * n)
  val [r:int] r = int1_of (r)
  prval () = __assert () where {
    extern prfun __assert (): [0 <= r; r <= n] void
  } // end of [prval]
in
  if r < n then r else 0
end // end of [randint]

(* ****** ****** *)

implement
randint_r {n}
  (buf, n, res) = let
  var d01: double
  val _0 = drand48_r (buf, d01)
  val r = int_of(d01 * n)
  val [r:int] r = int1_of (r)
  prval () = __assert () where {
    extern prfun __assert (): [0 <= r; r <= n] void
  } // end of [prval]
in
  if r < n then res := r else res := 0
end // end of [randint_r]

(* ****** ****** *)

(* end of [random.dats] *)
