(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: July 2007
//
(* ****** ****** *)
//
// ats_fixity: for handing prefix, infix and postfix operators
//
(* ****** ****** *)

staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t

(* ****** ****** *)

staload Prec = "ats_fixity_prec.sats"
typedef prec_t = $Prec.prec_t

(* ****** ****** *)

datatype assoc = ASSOCnon | ASSOClft | ASSOCrgt

(* ****** ****** *)

datatype fxty =
  | FXTYnon
  | FXTYinf of (prec_t, assoc)
  | FXTYpre of prec_t
  | FXTYpos of prec_t
// end of [fxty]

(* ****** ****** *)

val fxty_non : fxty
fun fxty_inf (p: prec_t, a: assoc): fxty
fun fxty_pre (p: prec_t): fxty
fun fxty_pos (p: prec_t): fxty

(* ****** ****** *)

val selptr_fixity_dyn : fxty
val deref_fixity_dyn : fxty // for dereference

(* ****** ****** *)

fun fprint_fxty {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, fxty: fxty): void
// end of [fprint_fxty]

fun prerr_fxty (fxty: fxty): void
fun print_fxty (fxty: fxty): void

(* ****** ****** *)

fun fixity_get_prec (fxty: fxty): Option_vt (prec_t)

(* ****** ****** *)

datatype oper (a:type) = 
  | OPERinf (a) of (prec_t, assoc, (a, a) -<cloref1> item a)
  | OPERpre (a) of (prec_t, a -<cloref1> item a)
  | OPERpos (a) of (prec_t, a -<cloref1> item a)
// end of [oper]
        
and item (a: type) = ITEMatm (a) of a | ITEMopr (a) of oper a

fun oper_precedence {a:type} (opr: oper a): prec_t
fun oper_associativity {a:type} (opr: oper a): assoc

(* ****** ****** *)

fun item_app {a:type}
  (app: (a, a) -<cloref1> item a): item a
// end of [item_app]

(* ****** ****** *)

fun oper_make_backslash {a:type} (
    locf: a -<cloref1> loc_t
  , appf: (loc_t, a, loc_t, List a) -<cloref1> a
  ) : item a 
// end of [oper_make_backslash]

fun oper_make {a:type} (
    locf: a -<cloref1> loc_t
  , appf: (loc_t, a, loc_t, List a) -<cloref1> a
  , opr: a
  , fxty: fxty
  ) : item a 
// end of [oper_make]

(* ****** ****** *)

fun fixity_resolve {a:type}
  (loc: loc_t, app: item a, xs: List (item a)): a
// end of [fixity_resolve]

(* ****** ****** *)

(* end of [ats_fixity_fxty.sats] *)
