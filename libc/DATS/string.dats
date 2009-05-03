(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
**
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
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
**
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

staload "libc/SATS/string.sats"

(* ****** ****** *)

implement strdup_gc (str) = let
  val n = strlen (str)
  val (pf_gc, pf_buf | p_buf) = malloc_gc (n + 1)
  val p_buf = strcpy (pf_buf | p_buf, str)
in
  @(pf_gc, pf_buf | p_buf)
end // end of [strdup_gc]

implement strdup_ngc (str) = let
  val n = strlen (str)
  val (pf_ngc, pf_buf | p_buf) = malloc_ngc (n + 1)
  val p_buf = strcpy (pf_buf | p_buf, str)
in
  @(pf_ngc, pf_buf | p_buf)
end // end of [strdup_ngc]

(* ****** ****** *)

(* end of string.dats] *)
