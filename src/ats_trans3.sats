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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: December 2007

(* ****** ****** *)

staload Loc = "ats_location.sats"

(* ****** ****** *)

staload SEXP2 = "ats_staexp2.sats"
staload PATCST2 = "ats_patcst2.sats"
staload DEXP2 = "ats_dynexp2.sats"

staload SOL = "ats_staexp2_solve.sats"
staload TRENV3 = "ats_trans3_env.sats"

(* ****** ****** *)

staload "ats_dynexp3.sats"

(* ****** ****** *)

fun d3exp_open_and_add (d3e: d3exp): void
fun d3explst_open_and_add (d3es: d3explst): void

(* ****** ****** *)

fun p2at_tr_dn (_: $DEXP2.p2at, _: $SEXP2.s2exp): p3at
fun p2atlst_tr_dn {n:nat}
  (_: $DEXP2.p2atlst n, _: $SEXP2.s2explst n): p3atlst n

fun p2at_arg_tr_up (_: $DEXP2.p2at): p3at
fun p2at_arg_tr_dn (_: $DEXP2.p2at, _: $SEXP2.s2exp): p3at

fun p2atlst_arg_tr_up {n:nat}
  (npf: int, _: $DEXP2.p2atlst n): p3atlst n
fun p2atlst_arg_tr_dn {n:nat}
  (npf: int, _: $DEXP2.p2atlst n, _: $SEXP2.s2explst n): p3atlst n

(* ****** ****** *)

// implemented in [ats_trans3_assgn.dats]

fun s2exp_addr_slablst_assgn
  (loc0: $Loc.location_t,
   s2e0: $SEXP2.s2exp, s2ls: $SEXP2.s2lablst, _new: $SEXP2.s2exp)
  : $SEXP2.s2lablst

fun d2var_mut_slablst_assgn
  (loc0: $Loc.location_t,
   d2v: $DEXP2.d2var_t, s2ls: $SEXP2.s2lablst, _new: $SEXP2.s2exp)
  : $SEXP2.s2lablst

fun d2var_lin_slablst_assgn {n:nat}
  (loc0: $Loc.location_t,
   d2v: $DEXP2.d2var_t, s2ls: list ($SEXP2.s2lab, n), _new: $SEXP2.s2exp)
  : list ($SEXP2.s2lab, n)

// implemented in [ats_trans3_deref.dats]

fun s2exp_addr_slablst_deref
  (loc0: $Loc.location_t, s2e0: $SEXP2.s2exp, s2ls: $SEXP2.s2lablst)
  : ($SEXP2.s2exp(*result*), $SEXP2.s2lablst)

// implemented in [ats_trans3_view.dats]

fun s2exp_addr_viewat_slablst_try
  (loc0: $Loc.location_t, s2e0: $SEXP2.s2exp, s2ls: $SEXP2.s2lablst)
  : $SEXP2.s2lablst

fun s2exp_addr_viewat_slablst_get
  (loc0: $Loc.location_t, s2e0: $SEXP2.s2exp, s2ls: $SEXP2.s2lablst)
  : ($SEXP2.s2exp, // result
     $SEXP2.s2lablst, // path
     $DEXP2.d2var_t, // viewroot
     $SEXP2.s2lablst // viewpath
    ) // end of [s2exp_addr_viewat_slablst_get]

fun s2exp_addr_viewat_slablst_set
  (loc0: $Loc.location_t,
   s2e0: $SEXP2.s2exp, s2ls: $SEXP2.s2lablst, s2e_new_at: $SEXP2.s2exp)
  : $SEXP2.s2lablst

(* ****** ****** *)

fun d3exp_lval_typ_set (
    loc0: $Loc.location_t
  , refval: int
  , d3e0: d3exp
  , s2e: $SEXP2.s2exp
  , err: &int
  ) : void

fun d3exp_lval_typ_set_arg (refval: int, d3e0: d3exp, s2e: $SEXP2.s2exp)
  : int (*freeknd*)

fun d3exp_lval_typ_set_pat (d3e0: d3exp, p3t: p3at): void

(* ****** ****** *)

fun d3exp_tr_dn (d3e: d3exp, s2e: $SEXP2.s2exp): void

(* ****** ****** *)

fun d2exp_tr_up (_: $DEXP2.d2exp): d3exp
fun d2explst_tr_up {n:nat} (_: $DEXP2.d2explst n): d3explst n
fun d2explstlst_tr_up (_: $DEXP2.d2explstlst): d3explstlst

fun d2exp_cst_tr_up (_: $Loc.location_t, d2c: $DEXP2.d2cst_t): d3exp
fun d2exp_var_tr_up (_: $Loc.location_t, d2v: $DEXP2.d2var_t): d3exp

// 0/1: break/continue
fun d2exp_loopexn_tr_up (_: $Loc.location_t, i: int): d3exp

fun d2exp_loop_tr_up (
    _: $Loc.location_t
  , _inv: $DEXP2.loopi2nv
  , _init: $DEXP2.d2expopt
  , _test: $DEXP2.d2exp
  , _post: $DEXP2.d2expopt
  , _body: $DEXP2.d2exp
  ) : d3exp

(* ****** ****** *)

fun assert_bool_tr_dn
  (loc: $Loc.location_t, b: bool, s2e: $SEXP2.s2exp): void

fun d2exp_tr_dn (_: $DEXP2.d2exp, _: $SEXP2.s2exp): d3exp
fun d2exp_tr_dn_rest (_: $DEXP2.d2exp, _: $SEXP2.s2exp): d3exp

fun d2exp_if_tr_dn (
    loc0: $Loc.location_t
  , res: $DEXP2.i2nvresstate
  , d2e_cond: $DEXP2.d2exp
  , d2e_then: $DEXP2.d2exp
  , od2e_else: $DEXP2.d2expopt
  , s2e0: $SEXP2.s2exp
  ) : d3exp

fun d2exp_caseof_tr_dn {n:nat} (
    loc: $Loc.location_t
  , casknd: int
  , res: $DEXP2.i2nvresstate
  , n: int n
  , d2es: $DEXP2.d2explst n
  , c2ls: $DEXP2.c2laulst n
  , s2e0: $SEXP2.s2exp
  ) : d3exp

fun d2exp_sif_tr_dn (
    loc0: $Loc.location_t
  , res: $DEXP2.i2nvresstate
  , s2p_cond: $SEXP2.s2exp
  , d2e_then: $DEXP2.d2exp
  , d2e_else: $DEXP2.d2exp
  , s2e0: $SEXP2.s2exp
  ) : d3exp

fun d2exp_scaseof_tr_dn (
    loc0: $Loc.location_t
  , res: $DEXP2.i2nvresstate
  , s2e_val: $SEXP2.s2exp
  , sc2ls: $DEXP2.sc2laulst
  , s2e0: $SEXP2.s2exp
  ) : d3exp

(* ****** ****** *)

dataviewtype sacsbisopt =
  | {n:nat} SACSBISsome of ($TRENV3.staftscstr_t n, $TRENV3.stbefitemlst n)
  | SACSBISnone

fun c2lau_tr_dn {n:nat} (
    c2l: $DEXP2.c2lau n
  , op2tcss: Option_vt ($PATCST2.p2atcstlstlst n)
  , d3es: d3explst n // for restoration
  , n: int n
  , s2es_pat: $SEXP2.s2explst n
  , s2e0_exp: $SEXP2.s2exp
  , osacsbis: sacsbisopt
  ) : c3lau n

fun c2laulst_tr_dn {n:nat} (
    loc0: $Loc.location_t
  , cmplt: &int
  , casknd: int
  , res: $DEXP2.i2nvresstate
  , c2ls: $DEXP2.c2laulst n
  , d3es: d3explst n
  , n: int n
  , s2es_pat: $SEXP2.s2explst n
  , s2e0: $SEXP2.s2exp
  ) : c3laulst n

(* ****** ****** *)

fun d2ec_tr (_: $DEXP2.d2ec): d3ec
fun d2eclst_tr (_: $DEXP2.d2eclst): d3eclst
fun c3str_final_get (): $TRENV3.c3str

(* ****** ****** *)

(* end of [ats_trans3.sats] *)
