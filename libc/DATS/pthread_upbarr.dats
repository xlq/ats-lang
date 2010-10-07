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

staload "libc/SATS/pthread_upbarr.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

implement
pthread_upbarr_elimunit {v} (barr) = let
  prfn fpf (pf: @(unit_v, v)): v = let prval unit_v () = pf.0 in pf.1 end
in
  pthread_upbarr_trans (fpf | barr)
end // end of [pthread_upbarr_elimunit]

(* ****** ****** *)

implement
pthread_upbarr_download_and_destroy
  (barr) = (pf | ()) where {
  val (pf | ()) = pthread_upbarr_download (barr)
  val () = pthread_upbarr_destroy (barr)
} // end of [pthread_upbarr_download_and_destroy]

(* ****** ****** *)

(* end of [pthread_upbarr.dats] *)
