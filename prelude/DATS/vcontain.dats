(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

// some proofs involving view containment.

(* ****** ****** *)

staload "prelude/SATS/vcontain.sats"

(* ****** ****** *)

assume vcontain_p
  (v1:view, v2:view) = (v1 -<prf> [v:view] @(v2, v))

(* ****** ****** *)

implement vcontain_make (fpf) = fpf

(* ****** ****** *)

implement vcontain_refl {v} () = lam (pf) => @(pf, unit_v ())

implement vcontain_trans (fpf12, fpf23) = lam (pf1) => let
  prval (pf2, pf12) = fpf12 (pf1); val (pf3, pf23) = fpf23 (pf2)
in
  (pf3, @(pf12, pf23))
end // end of [vcontain_trans]

(* ****** ****** *)

implement vcontain_tuple_2_0 () = lam (pf) => @(pf.0, pf.1)
implement vcontain_tuple_2_1 () = lam (pf) => @(pf.1, pf.0)

(* ****** ****** *)

(* end of [vcontain.dats] *)
