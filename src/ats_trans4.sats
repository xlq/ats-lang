(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS/Anairiats - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
 * Free Software Foundation; either version 3, or (at  your  option)  any
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

// Time: March 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp3.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"

(* ****** ****** *)

fun s2exp_tr (deep: int, s2e0: s2exp): hityp
fun s2explst_arg_tr (npf: int, s2es: s2explst): hityplst
fun labs2explst_arg_tr (npf: int, ls2es: labs2explst): labhityplst

(* ****** ****** *)

fun p3at_tr (p3t: p3at): hipat
fun p3atlst_tr (p3ts: p3atlst): hipatlst

(* ****** ****** *)

fun d3exp_tr (d3e: d3exp): hiexp
fun d3explst_tr (d3es: d3explst): hiexplst

(* ****** ****** *)

(* there is no [d3ec_tr] *)
fun d3eclst_tr (d3cs: d3eclst): hideclst

(* ****** ****** *)

(* end of [ats_trans4.sats] *)
