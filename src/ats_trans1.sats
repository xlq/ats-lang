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

// Time: August 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

(* The first translation mainly resolves the issue of operator fixity *)

(* ****** ****** *)

staload Syn = "ats_syntax.sats"
staload SEXP = "ats_staexp1.sats"
staload DEXP = "ats_dynexp1.sats"

(* ****** ****** *)

fun e0xp_tr (_: $Syn.e0xp): $SEXP.e1xp
fun e0xplst_tr (_: $Syn.e0xplst): $SEXP.e1xplst

fun s0rt_tr (_: $Syn.s0rt): $SEXP.s1rt
fun s0rtlst_tr (_: $Syn.s0rtlst): $SEXP.s1rtlst
fun s0rtopt_tr (_: $Syn.s0rtopt): $SEXP.s1rtopt

fun s0exp_tr (_: $Syn.s0exp): $SEXP.s1exp
fun s0explst_tr (_: $Syn.s0explst): $SEXP.s1explst
fun s0expopt_tr (_: $Syn.s0expopt): $SEXP.s1expopt
fun s0explstlst_tr (_: $Syn.s0explstlst): $SEXP.s1explstlst
fun labs0explst_tr (_: $Syn.labs0explst): $SEXP.labs1explst

fun s0rtext_tr (_: $Syn.s0rtext): $SEXP.s1rtext

fun p0at_tr (_: $Syn.p0at): $DEXP.p1at
fun p0atlst_tr (_: $Syn.p0atlst): $DEXP.p1atlst
fun labp0atlst_tr (_: $Syn.labp0atlst): $DEXP.labp1atlst

fun d0exp_tr (_: $Syn.d0exp): $DEXP.d1exp
fun d0explst_tr (_: $Syn.d0explst): $DEXP.d1explst
fun d0explstlst_tr (_: $Syn.d0explstlst): $DEXP.d1explstlst
fun labd0explst_tr (_: $Syn.labd0explst): $DEXP.labd1explst
fun d0expopt_tr (_: $Syn.d0expopt): $DEXP.d1expopt

fun d0ec_tr (_: $Syn.d0ec): $DEXP.d1ec
fun d0eclst_tr (_: $Syn.d0eclst): $DEXP.d1eclst

(* ****** ****** *)

fun initialize (): void and finalize (): void

(* ****** ****** *)

(* end of [ats_trans1.sats] *)
