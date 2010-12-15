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
// Time: April 2008
//
(* ****** ****** *)

staload Fil = "ats_filename.sats"
staload Loc = "ats_location.sats"
typedef loc_t = $Loc.location_t
staload Set = "ats_set_fun.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"
staload "ats_ccomp.sats"

(* ****** ****** *)

// for accumulating type defintiions (rec/sum/uni)
dataviewtype typdeflst =
  | TYPDEFLSTcons of (typkey, string(*name*), typdeflst)
  | TYPDEFLSTnil of ()
// end of [typdeflst]

fun typdeflst_get (): typdeflst

(* ****** ****** *)

dataviewtype datcstlst =
  | DATCSTLSTcons of (s2cst_t, datcstlst) | DATCSTLSTnil of ()
// end of [datcstlst]

fun datcstlst_free (s2cs: datcstlst): void

fun the_datcstlst_add (s2c: s2cst_t): void
fun the_datcstlst_adds (s2cs: s2cstlst): void
fun the_datcstlst_get (): datcstlst

(* ****** ****** *)

dataviewtype exnconlst =
  | EXNCONLSTcons of (d2con_t, exnconlst) | EXNCONLSTnil of ()
// end of [exnconlst]

fun exnconlst_free (d2cs: exnconlst): void

fun the_exnconlst_add (d2c: d2con_t): void
fun the_exnconlst_adds (d2cs: d2conlst): void
fun the_exnconlst_get (): exnconlst

(* ****** ****** *)
//
// HX: implemented in [ats_ccomp_trans.dats]
//
absviewtype dynctx_vt

fun the_dynctx_add (d2v: d2var_t, vp: valprim): void

absview dynctx_mark_token
fun the_dynctx_mark (): @(dynctx_mark_token | void)
fun the_dynctx_unmark (pf: dynctx_mark_token | (*none*)): void

fun the_dynctx_free (): void // free the (toplevel) dynctx

fun the_dynctx_find (d2v: d2var_t): valprim

absview dynctx_push_token
fun the_dynctx_pop (pf: dynctx_push_token | (*none*)): void
fun the_dynctx_push (): @(dynctx_push_token | void)

fun dynctx_foreach_main
  {v:view} {vt:viewtype} {f:eff} (
    pf: !v
  | m: !dynctx_vt
  , f: (!v | d2var_t, valprim, !vt) -<f> void
  , env: !vt
  ) :<f> void
// end of [dynctx_foreach_main]

(* ****** ****** *)

typedef vartypset = $Set.set_t (vartyp_t)
fun the_vartypset_add (vtp: vartyp_t): void
fun the_vartypset_pop (): vartypset and the_vartypset_push (): void

fun vartypset_d2varlst_make (vtps: vartypset): d2varlst_vt

fun vartypset_foreach_main
  {v:view} {vt:viewtype} {f:eff} (
    pf: !v
  | vtps: vartypset
  , f: (!v | vartyp_t, !vt) -<f> void
  , env: !vt
  ) :<f> void
// end of [vartypset_foreach_main]

fun vartypset_union
  (vtps1: vartypset, vtps2: vartypset): vartypset
fun vartypset_foreach_cloptr {f:eff}
  (vtps: vartypset, f: !vartyp_t -<cloptr,f> void):<f> void

fun print_vartypset (vtps: vartypset): void
fun prerr_vartypset (vtps: vartypset): void

(* ****** ****** *)

typedef funlabset = $Set.set_t (funlab_t)

fun the_funlabset_add (fl: funlab_t): void
fun the_funlabset_mem (fl: funlab_t): bool
fun the_funlabset_pop (): funlabset and the_funlabset_push (): void

fun funlabset_foreach_main
  {v:view} {vt:viewtype} {f:eff} (
    pf: !v
  | fls: funlabset
  , f: (!v | funlab_t, !vt) -<f> void
  , env: !vt
  ) :<f> void
// end of [funlabset_foreach_main]

fun funlabset_foreach_cloptr {f:eff}
  (fls: funlabset, f: !funlab_t -<cloptr,f> void):<f> void

fun print_funlabset (fls: funlabset): void
fun prerr_funlabset (fls: funlabset): void

(* ****** ****** *)

// [abstype dyncstcon_t] is in [ats_hiexp.sats]

fun dynconset_foreach_main
  {v:view} {vt:viewtype} {f:eff} (
    pf: !v
  | d2cs: dynconset_t
  , f: (!v | d2con_t, !vt) -<f> void
  , env: !vt
  ) :<f> void
// end of [dynconset_foreach_main]

fun the_dynconset_get (): dynconset_t
fun the_dynconset_add (d2c: d2con_t): void

(* ****** ****** *)

// [abstype dyncstset_t] is in [ats_hiexp.sats]

fun dyncstset_foreach_main
  {v:view} {vt:viewtype} {f:eff} (
    pf: !v
  | d2cs: dyncstset_t
  , f: (!v | d2cst_t, !vt) -<f> void
  , env: !vt
  ) :<f> void
// end of [dyncstset_foreach_main]

fun the_dyncstset_get (): dyncstset_t = "ats_ccomp_env_the_dyncstset_get"
fun the_dyncstset_add_if (d2c: d2cst_t): void // [d2c] is added only if it has not been
  = "ats_ccomp_env_the_dyncstset_add_if"

fun the_dyncstsetlst_push (): void = "ats_ccomp_env_the_dyncstsetlst_push"
fun the_dyncstsetlst_pop (): dyncstset_t = "ats_ccomp_env_the_dyncstsetlst_pop"

(* ****** ****** *)

dataviewtype extypelst =
  | EXTYPELSTcons of (string (*name*), hityp_t, extypelst)
  | EXTYPELSTnil of ()
// end of [extypelst]  

fun the_extypelst_get (): extypelst
fun the_extypelst_add (name: string, hit: hityp_t): void

(* ****** ****** *)

dataviewtype extvallst =
  | EXTVALLSTcons of (string (*name*), valprim, extvallst)
  | EXTVALLSTnil

fun extvallst_free (exts: extvallst): void

fun the_extvallst_get (): extvallst
fun the_extvallst_add (name: string, vp: valprim): void

(* ****** ****** *)

dataviewtype extcodelst =
  | EXTCODELSTcons of
      (loc_t, int(*position*), string (*code*), extcodelst)
  | EXTCODELSTnil of ()
// end of [extcodelst]

fun extcodelst_free (codes: extcodelst): void

fun the_extcodelst_get (): extcodelst
fun the_extcodelst_add (loc: loc_t, pos: int, code: string): void

(* ****** ****** *)

dataviewtype stafilelst =
  | STAFILELSTcons of ($Fil.filename_t, int(*loadflag*), stafilelst)
  | STAFILELSTnil of ()
// end of [stafilelst]

fun stafilelst_free (fils: stafilelst): void

fun the_stafilelst_get (): stafilelst
fun the_stafilelst_add (fil: $Fil.filename_t, loadflag: int): void

(* ****** ****** *)

dataviewtype dynfilelst =
  | DYNFILELSTcons of ($Fil.filename_t, dynfilelst)
  | DYNFILELSTnil of ()
// end of [dynfilelst]

fun dynfilelst_free (fils: dynfilelst): void

fun the_dynfilelst_get (): dynfilelst
fun the_dynfilelst_add (fil: $Fil.filename_t): void

(* ****** ****** *)

absview funlab_token
fun funlab_pop (pf: funlab_token | (*none*)): void
fun funlab_push (fl: funlab_t): (funlab_token | void)
fun funlab_top (): funlab_t

(* ****** ****** *)

fun funentry_make (
    loc: loc_t
  , fl: funlab_t
  , level: int
  , fls: funlabset
  , vtps: vartypset
  , _ret: tmpvar_t
  , inss: instrlst
  ) : funentry_t

fun funentry_loc_get (entry: funentry_t): loc_t
fun funentry_lab_get (entry: funentry_t): funlab_t
fun funentry_lev_get (entry: funentry_t): int
fun funentry_vtps_get (entry: funentry_t): vartypset
fun funentry_vtps_set (entry: funentry_t, vtps: vartypset): void
  = "ats_ccomp_env_funentry_vtps_set"

fun funentry_vtps_flag_get (entry: funentry_t): int
fun funentry_vtps_flag_set (entry: funentry_t): void // set to 1
  = "ats_ccomp_env_funentry_vtps_flag_set"

fun funentry_labset_get (entry: funentry_t): funlabset
fun funentry_ret_get (entry: funentry_t): tmpvar_t
fun funentry_body_get (entry: funentry_t): instrlst

//

fun funentry_tailjoin_get (entry: funentry_t): tailjoinlst
fun funentry_tailjoin_set (entry: funentry_t, tjs: tailjoinlst): void
  = "ats_ccomp_env_funentry_tailjoin_set"

//
 
fun funentry_associate (entry: funentry_t): void
fun funentry_vtps_get_all (entry: funentry_t): vartypset

//

fun varindmap_find (d2v: d2var_t): Option_vt int
fun varindmap_find_some (d2v: d2var_t): int

fun funentry_varindmap_reset (): void
fun funentry_varindmap_set (vtps: vartypset): void

(* ****** ****** *)

fun funentry_lablst_get (): funlablst_vt
fun funentry_lablst_add (fl: funlab_t): void

(* ****** ****** *)

fun loopexnlablst_pop (): void
fun loopexnlablst_push
  (tl_init: tmplab_t, tl_fini: tmplab_t, tl_cont: tmplab_t): void
fun loopexnlablst_get (i: int): tmplab_t

(* ****** ****** *)

dataviewtype glocstlst =
  | GLOCSTLSTcons_clo of (d2cst_t, glocstlst)
  | GLOCSTLSTcons_fun of (d2cst_t, glocstlst)
  | GLOCSTLSTcons_val of (d2cst_t, valprim, glocstlst)
  | GLOCSTLSTnil of ()
// end of [glocstlst]

fun the_glocstlst_get (): glocstlst

fun the_glocstlst_add_clo (d2c: d2cst_t): void
fun the_glocstlst_add_fun (d2c: d2cst_t): void

fun the_glocstlst_add_val (d2c: d2cst_t, vp: valprim): void

(* ****** ****** *)

// implemented in [ats_ccomp_trans.dats]
fun the_topcstctx_add (d2c: d2cst_t, vp: valprim): void
fun the_topcstctx_find (d2c: d2cst_t): Option_vt (valprim)

(* ****** ****** *)

fun the_valprimlst_free_add (vp: valprim): void
fun the_valprimlst_free_get (): valprimlst_vt

(* ****** ****** *)
//
// HX: for tailcall optimization
//
dataviewtype tailcallst =
  | TAILCALLSTcons of (funlab_t, tmpvarlst, tailcallst)
  | TAILCALLSTmark of tailcallst
  | TAILCALLSTnil of ()
// end of [tailcallst]

absview tailcallst_token

fun the_tailcallst_add (fl: funlab_t, tmps: tmpvarlst): void
fun the_tailcallst_find (fl: funlab_t): Option_vt (tmpvarlst)
fun the_tailcallst_mark (): (tailcallst_token | void)
fun the_tailcallst_unmark (pf: tailcallst_token | (*none*)): void

(* ****** ****** *)

(* end of [ats_ccomp_env.sats] *)
