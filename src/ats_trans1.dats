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

staload Eff = "ats_effect.sats"
staload Err = "ats_error.sats"
staload Fil = "ats_filename.sats"
staload Fix = "ats_fixity.sats"
staload Glo = "ats_global.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload Par = "ats_parser.sats"
staload Sym = "ats_symbol.sats"

(* ****** ****** *)

staload "ats_syntax.sats"
staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"
staload "ats_trans1_env.sats"
staload "ats_e1xp_eval.sats"

(* ****** ****** *)

staload "ats_trans1.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef loc_t = $Loc.location_t
typedef fil_t = $Fil.filename_t

(* ****** ****** *)

overload prerr with $Loc.prerr_location
overload prerr with $Sym.prerr_symbol

(* ****** ****** *)

#define CLOPTR 1; #define CLOREF ~1
macdef FUNCLOcloptr = $Syn.FUNCLOclo CLOPTR
macdef FUNCLOcloref = $Syn.FUNCLOclo CLOREF

(* ****** ****** *)

fn prec_tr_errmsg (opr: i0de): $Fix.prec_t = begin
  prerr opr.i0de_loc;
  prerr ": error(1)";
  prerr ": the operator [";
  prerr opr.i0de_sym;
  prerr "] is given no fixity.";
  prerr_newline ();
  $Err.abort ()
end

fn p0rec_tr (p0: p0rec): $Fix.prec_t = begin
  case+ p0 of
  | P0RECide id => begin
    case+ the_fxtyenv_find id.i0de_sym of
    | ~Some_vt fxty => let
(*
        val () = begin
          print "p0rec_tr: Some: id = ";
          $Sym.print_symbol_code id.i0de_sym;
          print_newline ()
        end
*)
        val p_opt = $Fix.precedence_of_fixity fxty
      in
        case+ p_opt of Some p => p | None () => prec_tr_errmsg id
      end
    | ~None_vt () => prec_tr_errmsg id
    end // end of [begin]
  | P0RECint int => $Fix.prec_make_int int
end // end of [p0rec_tr]

fn f0xty_tr (f0xty: f0xty): $Fix.fxty_t = begin
 case+ f0xty of
  | F0XTYinf (p0, a) =>
      let val p = p0rec_tr p0 in $Fix.fxty_inf (p, a) end
  | F0XTYpre p0 =>
      let val p = p0rec_tr p0 in $Fix.fxty_pre p end
  | F0XTYpos p0 =>
      let val p = p0rec_tr p0 in $Fix.fxty_pos p end
end // end of [f0xty_tr]

(* ****** ****** *)

typedef e1xpitm = $Fix.item (e1xp)
typedef e1xpitmlst = List e1xpitm

val e1xpitm_app : e1xpitm = let

fn f (e1: e1xp, e2: e1xp):<cloref1> e1xpitm = let
  val loc = $Loc.location_combine (e1.e1xp_loc, e2.e1xp_loc)
  val es2 = (
    case+ e2.e1xp_node of E1XPlist es => es | _ => '[e2]
  ) : e1xplst
  val e_app = e1xp_app (loc, e1, e2.e1xp_loc, es2)
(*
  val () = begin
    print "e1xpitm_app: f: e_app = "; print e_app; print_newline ()
  end
*)
in
  $Fix.ITEMatm (e_app)
end // end of [f]
    
in // in of [let]
  $Fix.item_app f
end // end of [e1xpitm_app]

fun e1xp_make_opr (e: e1xp, f: $Fix.fxty_t): e1xpitm = begin
  $Fix.oper_make {e1xp} (
    lam x => x.e1xp_loc,
    lam (loc, x, loc_arg, xs) => e1xp_app (loc, x, loc_arg, xs), e, f
  )
end // end of [e1xpitm_opr]

val e1xpitm_backslash : e1xpitm = begin
  $Fix.oper_make_backslash {e1xp} (
    lam x => x.e1xp_loc,
    lam (loc, x, loc_arg, xs) => e1xp_app (loc, x, loc_arg, xs)
  )
end // end of [e1xpitm_backslash]

(* ****** ****** *)

fn e0xp_tr_errmsg_opr (loc: loc_t): e1xp = begin
  prerr loc;
  prerr ": error(1)";
  prerr ": the operator needs to be applied.\n";
  $Err.abort {e1xp} ()
end
  
implement e0xp_tr e0 = let

fun aux_item (e0: e0xp): e1xpitm =
  let val loc = e0.e0xp_loc in case+ e0.e0xp_node of
    | E0XPapp _ => let
        val es_new = aux_itemlst e0
        val e0_new = $Fix.fixity_resolve (loc, e1xpitm_app, es_new)
      in
        $Fix.ITEMatm (e0_new)
      end
    | E0XPchar (c: char) => $Fix.ITEMatm (e1xp_char (loc, c))
    | E0XPfloat (f: string) => $Fix.ITEMatm (e1xp_float (loc, f))
    | E0XPide id when id = $Sym.symbol_BACKSLASH => e1xpitm_backslash
    | E0XPide id => begin case+ the_fxtyenv_find id of
      | ~Some_vt f => begin
          let val e = e1xp_ide (loc, id) in e1xp_make_opr (e, f) end
        end
      | ~None_vt () => $Fix.ITEMatm (e1xp_ide (loc, id))
      end
    | E0XPint (int: string) => $Fix.ITEMatm (e1xp_int (loc, int))
    | E0XPlist (es) => $Fix.ITEMatm (e1xp_list (loc, e0xplst_tr es))
    | E0XPstring (str, len) => $Fix.ITEMatm (e1xp_string (loc, str, len))
  end

and aux_itemlst (e0: e0xp): e1xpitmlst =
  let
    fun aux (res: e1xpitmlst, e0: e0xp): e1xpitmlst =
      case+ e0.e0xp_node of
        | E0XPapp (e1, e2) =>
          let val res = aux_item e2 :: res in aux (res, e1) end
        | _ => aux_item e0 :: res
  in
    aux (nil (), e0)
  end

in
  case+ aux_item e0 of
    | $Fix.ITEMatm e => e
    | $Fix.ITEMopr _ => e0xp_tr_errmsg_opr e0.e0xp_loc
end // end of [e0xp_tr]

implement e0xplst_tr es = case+ es of
  | cons (e, es) => cons (e0xp_tr e, e0xplst_tr es)
  | nil () => nil ()

(* ****** ****** *)

// translation of sorts

typedef s1rtitm = $Fix.item s1rt
typedef s1rtitmlst = List s1rtitm

val s1rtitm_app : s1rtitm = let

fn f (s1t1: s1rt, s1t2: s1rt):<cloref1> s1rtitm =
  let
    val loc = $Loc.location_combine (s1t1.s1rt_loc, s1t2.s1rt_loc)
    val s1ts2 = (
      case+ s1t2.s1rt_node of
      | S1RTlist s1ts => s1ts | _ => cons (s1t2, nil ())
    ) : s1rtlst
    val s1t_app = s1rt_app (loc, s1t1, s1ts2)
  in
    $Fix.ITEMatm s1t_app
  end

in
  $Fix.item_app f
end // end of [app_s1rt_item]

fun s1rt_make_opr (s1t: s1rt, f: $Fix.fxty_t): s1rtitm = begin
  $Fix.oper_make {s1rt} (
    lam x => x.s1rt_loc,
    lam (loc, x, _(*loc_arg*), xs) => s1rt_app (loc, x, xs), s1t, f
  )
end // end of [s1rt_make_opr]

val s1rtitm_backslash : s1rtitm = begin
  $Fix.oper_make_backslash {s1rt} (
    lam x => x.s1rt_loc,
    lam (loc, x, _(*loc_arg*), xs) => s1rt_app (loc, x, xs)
  )
end // end of [s1rtitm_backslash]

(* ****** ****** *)

fn s0rt_tr_errmsg_opr (loc: loc_t): s1rt = begin
  prerr loc;
  prerr ": error(1)";
  prerr ": the operator needs to be applied.\n";
  $Err.abort {s1rt} ()
end
  
implement s0rt_tr s0t0 = let

fun aux_item (s0t0: s0rt): s1rtitm = let
  val loc0 = s0t0.s0rt_loc in case+ s0t0.s0rt_node of
    | S0RTapp _ => let 
        val s1t0 =
          $Fix.fixity_resolve (loc0, s1rtitm_app, aux_itemlst s0t0)
      in
        $Fix.ITEMatm s1t0
      end
    | S0RTide id when id = $Sym.symbol_BACKSLASH => s1rtitm_backslash
    | S0RTide id => begin case+ the_fxtyenv_find id of
      | ~Some_vt f => s1rt_make_opr (s1rt_ide (loc0, id), f)
      | ~None_vt () => $Fix.ITEMatm (s1rt_ide (loc0, id))
      end
    | S0RTlist (s0ts) => $Fix.ITEMatm (s1rt_list (loc0, s0rtlst_tr s0ts))
    | S0RTqid (q, id) => $Fix.ITEMatm (s1rt_qid (loc0, q, id))
    | S0RTtup (s0ts) => $Fix.ITEMatm (s1rt_tup (loc0, s0rtlst_tr s0ts))
  end

and aux_itemlst (s0t0: s0rt): s1rtitmlst =
  let
    fun aux (res: s1rtitmlst, s0t0: s0rt): s1rtitmlst =
      case+ s0t0.s0rt_node of
      | S0RTapp (s0t1, s0t2) => let
          val res = aux_item s0t2 :: res
        in
          aux (res, s0t1)
        end
      | _ => aux_item s0t0 :: res
  in
    aux (nil (), s0t0)
  end

in
  case+ aux_item s0t0 of
    | $Fix.ITEMatm s1t => s1t
    | $Fix.ITEMopr _ => s0rt_tr_errmsg_opr s0t0.s0rt_loc
end

implement s0rtlst_tr (s0ts: s0rtlst) =
  case+ s0ts of
    | s0t :: s0ts => s0rt_tr s0t :: s0rtlst_tr s0ts
    | nil () => nil ()

implement s0rtopt_tr (os0t: s0rtopt) =
  case+ os0t of Some s0t => Some (s0rt_tr s0t) | None () => None ()

(* ****** ****** *)

fn s0rtpol_tr (s0tp: s0rtpol): s1rtpol =
  s1rtpol_make (s0tp.s0rtpol_loc, s0rt_tr s0tp.s0rtpol_srt, s0tp.s0rtpol_pol)

fn s0rtpol_srt_tr (s0tp: s0rtpol): s1rt =
  if s0tp.s0rtpol_pol = 0 then s0rt_tr s0tp.s0rtpol_srt
  else begin
    prerr s0tp.s0rtpol_loc;
    prerr ": error(1)";
    prerr ": only a nonpolarized sort is allowed here.";
    prerr_newline ();
    $Err.abort ()
  end

(* ****** ****** *)

fn d0atarg_tr (d0a: d0atarg): d1atarg = begin
  case+ d0a.d0atarg_node of
  | D0ATARGsrt s0tp => begin
      d1atarg_srt (d0a.d0atarg_loc, s0rtpol_tr s0tp)
    end
  | D0ATARGidsrt (id, s0tp) => begin
      d1atarg_idsrt (d0a.d0atarg_loc, id, s0rtpol_tr s0tp)
    end
end // end of [d0atarg_tr]

fun d0atarglst_tr (d0as: d0atarglst): d1atarglst =
  case+ d0as of
  | cons (d0a, d0as) => cons (d0atarg_tr d0a, d0atarglst_tr d0as)
  | nil () => nil ()

fun d0atarglst_srtlst_tr (d0as: d0atarglst): s1rtlst = begin
  case+ d0as of
  | cons (d0a, d0as) => let
      val s0tp: s0rtpol = case+ d0a.d0atarg_node of
        | D0ATARGsrt s0tp => s0tp | D0ATARGidsrt (_(*id*), s0tp) => s0tp
      val s1t = s0rtpol_srt_tr s0tp
    in
      cons (s1t, d0atarglst_srtlst_tr d0as)
    end
  | nil () => nil ()
end // end of [d0atarglst_srtlst_tr]

(* ****** ****** *)

fun d0ec_fixity_tr
  (f0xty: f0xty, ids: i0delst): void = let
  fun loop (fxty: $Fix.fxty_t, ids: i0delst): void =
    case+ ids of
    | cons (id, ids) => let
(*
        val () = begin
          print "d0ec_fixity_tr: loop: id = ";
          $Sym.print_symbol_code id.i0de_sym;
          print_newline ()
        end
        val () = begin
          print "the_fxtyenv_add: before: \n"; fxty_env_print ()
        end
*)
        val () = the_fxtyenv_add (id.i0de_sym, fxty)
(*
        val () = begin
          print "the_fxtyenv_add: after: \n"; fxty_env_print ()
        end
*)
      in
        loop (fxty, ids)
      end
    | nil () => ()
in
  loop (f0xty_tr f0xty, ids)
end // end of [d0ec_fixity_tr]

fun d0ec_nonfix_tr (ids: i0delst): void = let
  fun loop (ids: i0delst): void = case+ ids of
    | cons (id, ids) => begin
        the_fxtyenv_add (id.i0de_sym, $Fix.fxty_non); loop ids
      end
    | nil () => ()
in
  loop ids
end // end of [d0ec_nonfix_tr]

(* ****** ****** *)

fn do_e0xpact_assert (loc: loc_t, v: v1al): void = let
  val is_false = case+ v of
    | V1ALchar c => c = '\0'
    | V1ALfloat f => f = 0.0
    | V1ALint i => i = 0
    | V1ALstring s => string0_is_empty s
in
  if is_false then begin
    prerr loc;
    prerr ": error(1)";
    prerr ": [#assert] failed.";
    prerr_newline ();
    exit {void} (1)
  end
end // end of [do_e0xpact_assert]

fn do_e0xpact_error (loc: loc_t, v: v1al): void = let
  val () = begin
    prerr loc; prerr ": error(1)"; prerr ": [#error]: "
  end
  val () = case+ v of
    | V1ALchar c => prerr c
    | V1ALfloat f => prerr f
    | V1ALint i => prerr i
    | V1ALstring s => prerr s
in
  exit {void} (1)
end // end of [do_e0xpact_error]

fn do_e0xpact_print (v: v1al): void = case+ v of
  | V1ALchar c => prerr c
  | V1ALfloat f => prerr f
  | V1ALint i => prerr i
  | V1ALstring s => prerr s

(* ****** ****** *)

fn s0tacon_tr (d: s0tacon): s1tacon = let
  val arg = (
    case+ d.s0tacon_arg of
    | Some d0as => Some (d0atarglst_tr d0as) | None () => None ()
  ) : Option d1atarglst 
  val def = s0expopt_tr d.s0tacon_def
in
  s1tacon_make (d.s0tacon_loc, d.s0tacon_sym, arg, def)
end // end of [s0tacon_tr]

fn s0taconlst_tr (ds: s0taconlst): s1taconlst =
  $Lst.list_map_fun (ds, s0tacon_tr)

(* ****** ****** *)

fn s0tacst_tr (d: s0tacst): s1tacst = let
  val os1ts_arg = (
    case+ d.s0tacst_arg of
    | Some arg => Some (d0atarglst_srtlst_tr arg) | None () => None ()
  ) : s1rtlstopt
  val s1t_res: s1rt = s0rt_tr d.s0tacst_res
in
  s1tacst_make (d.s0tacst_loc, d.s0tacst_sym, os1ts_arg, s1t_res)
end

fn s0tacstlst_tr (ds: s0tacstlst): s1tacstlst =
  $Lst.list_map_fun (ds, s0tacst_tr)

(* ****** ****** *)

fn s0tavar_tr (d: s0tavar): s1tavar = let
  val s1t: s1rt = s0rt_tr d.s0tavar_srt
in
  s1tavar_make (d.s0tavar_loc, d.s0tavar_sym, s1t)
end

fn s0tavarlst_tr (ds: s0tavarlst): s1tavarlst =
  $Lst.list_map_fun (ds, s0tavar_tr)

(* ****** ****** *)

fn d0atsrtcon_tr (x: d0atsrtcon): d1atsrtcon = let
  val loc = x.d0atsrtcon_loc and nam = x.d0atsrtcon_sym
  val s1ts = (
    case+ x.d0atsrtcon_arg of
    | Some s0t => let
        val s1t = s0rt_tr s0t
      in
        case+ s1t.s1rt_node of
          | S1RTlist s1ts => s1ts | _ => cons (s1t, nil ())
      end
    | None () => nil ()
  ) : s1rtlst
in
  d1atsrtcon_make (loc, nam, s1ts)
end // end of [d0atsrtcon_tr]

fn d0atsrtconlst_tr (xs: d0atsrtconlst): d1atsrtconlst =
  $Lst.list_map_fun (xs, d0atsrtcon_tr)

fn d0atsrtdec_tr (d: d0atsrtdec): d1atsrtdec = let
  val loc = d.d0atsrtdec_loc and nam = d.d0atsrtdec_sym
in
  d1atsrtdec_make (loc, nam, d0atsrtconlst_tr d.d0atsrtdec_con)
end // end of [d0atsrtdec_tr]

fun d0atsrtdeclst_tr (ds: d0atsrtdeclst): d1atsrtdeclst =
  $Lst.list_map_fun (ds, d0atsrtdec_tr)

(* ****** ****** *)

// translation of static expressions

typedef s1expitm = $Fix.item s1exp
typedef s1expitmlst = List s1expitm

val s1expitm_app : s1expitm = let

fn f (s1e1: s1exp, s1e2: s1exp):<cloref1> s1expitm = let
  val loc = $Loc.location_combine (s1e1.s1exp_loc, s1e2.s1exp_loc)
  val s1es2 = (
    case+ s1e2.s1exp_node of
    | S1Elist (npf, s1es) => s1es // should [npf = 0] be enforced?
    | _ => cons (s1e2, nil ())
  ) : s1explst
  val s1e_app = s1exp_app (loc, s1e1, s1e2.s1exp_loc, s1es2)
(*
  val () = begin
    print "s1expitm_app: f: s1e_app = "; print s1e_app; print_newline ()
  end
*)
in
  $Fix.ITEMatm s1e_app
end // end of [f]

in
  $Fix.item_app f
end // end of [app_s1exp_item]

fun s1exp_make_opr (s1e: s1exp, f: $Fix.fxty_t): s1expitm = begin
  $Fix.oper_make {s1exp} (
    lam x => x.s1exp_loc,
    lam (loc, x, loc_arg, xs) => s1exp_app (loc, x, loc_arg, xs), s1e, f
  )
end // end of [s1exp_make_opr]

val s1expitm_backslash : s1expitm = begin
  $Fix.oper_make_backslash {s1exp} (
    lam x => x.s1exp_loc,
    lam (loc, x1, loc_arg, x2) => s1exp_app (loc, x1, loc_arg, x2)
  )
end // end of [s1expitm_backslash]

(* ****** ****** *)

fn s0arg_tr (s0a: s0arg): s1arg = let
  val res = s0rtopt_tr s0a.s0arg_srt
in
  s1arg_make (s0a.s0arg_loc, s0a.s0arg_sym, res)
end // end of [s0arg_tr]

fn s0arglst_tr (s0as: s0arglst): s1arglst =
  $Lst.list_map_fun (s0as, s0arg_tr)

fun s0arglstlst_tr (s0ass: s0arglstlst): s1arglstlst =
  $Lst.list_map_fun (s0ass, s0arglst_tr)

fn s0qua_tr (s0q: s0qua): s1qua = begin
  case+ s0q.s0qua_node of
  | S0QUAprop s0p => s1qua_prop (s0q.s0qua_loc, s0exp_tr s0p)
  | S0QUAvars (id, ids, s0te) => begin
      s1qua_vars (s0q.s0qua_loc, id :: ids, s0rtext_tr s0te)
    end
end // end of [s0qua_tr]

fn s0qualst_tr (s0qs: s0qualst): s1qualst =
  $Lst.list_map_fun (s0qs, s0qua_tr)

fn s0qualstlst_tr (s0qss: s0qualstlst): s1qualstlst =
  $Lst.list_map_fun (s0qss, s0qualst_tr)

(* ****** ****** *)

fn s0exp_tr_errmsg_opr (loc: loc_t): s1exp = begin
  prerr loc;
  prerr ": error(1)";
  prerr ": the operator needs to be applied.\n";
  $Err.abort {s1exp} ()
end

implement s0exp_tr s0e0 = let

fun aux_item (s0e0: s0exp): s1expitm = let
  val loc0 = s0e0.s0exp_loc in case+ s0e0.s0exp_node of
    | S0Eann (s0e, s0t) => let
        val s1e = s0exp_tr s0e and s1t = s0rt_tr s0t
        val s1e_ann = s1exp_ann (loc0, s1e, s1t)
      in
        $Fix.ITEMatm s1e_ann
      end
    | S0Eapp _ => let 
        val s1e = $Fix.fixity_resolve (loc0, s1expitm_app, aux_itemlst s0e0)
      in
        $Fix.ITEMatm s1e
      end
    | S0Echar c => $Fix.ITEMatm (s1exp_char (loc0, c))
    | S0Eexi (knd(*funres*), s0qs) => let
        val s1qs = s0qualst_tr s0qs
        fn f (body: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (loc0, body.s1exp_loc) in
            $Fix.ITEMatm (s1exp_exi (loc0, knd, s1qs, body))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.exi_prec_sta, f))
      end
    | S0Eextype name => $Fix.ITEMatm (s1exp_extype (loc0, name))
    | S0Eint int (*string*) => $Fix.ITEMatm (s1exp_int (loc0, int))
    | S0Eide id when id = $Sym.symbol_AMPERSAND => let
        fn f (s1e: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (loc0, s1e.s1exp_loc) in
            $Fix.ITEMatm (s1exp_invar (loc0, 1(*ref*), s1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.invar_prec_sta, f))
      end
    | S0Eide id when id = $Sym.symbol_BACKSLASH => s1expitm_backslash
    | S0Eide id when id = $Sym.symbol_BANG => let
        fn f (s1e: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (loc0, s1e.s1exp_loc) in
            $Fix.ITEMatm (s1exp_invar (loc0, 0(*val*), s1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.invar_prec_sta, f))
      end
    | S0Eide id when id = $Sym.symbol_QMARK => let
        fn f (s1e: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (s1e.s1exp_loc, loc0) in
            $Fix.ITEMatm (s1exp_top (loc0, 0(*knd*), s1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpos ($Fix.qmark_prec_sta, f))
      end
    | S0Eide id when id = $Sym.symbol_QMARKBANG => let
        fn f (s1e: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (s1e.s1exp_loc, loc0) in
            $Fix.ITEMatm (s1exp_top (loc0, 1(*knd*), s1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpos ($Fix.qmarkbang_prec_sta, f))
      end
    | S0Eide id when id = $Sym.symbol_GTGT => let
        fn f (s1e1: s1exp, s1e2: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (s1e1.s1exp_loc, s1e2.s1exp_loc) in
            $Fix.ITEMatm (s1exp_trans (loc0, s1e1, s1e2))
          end
      in
        $Fix.ITEMopr ($Fix.OPERinf ($Fix.trans_prec_sta, $Fix.ASSOCnon, f))
      end
    | S0Eide id when id = $Sym.symbol_R0EAD => let
        fn f (s1e: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (loc0, s1e.s1exp_loc) in
            $Fix.ITEMatm (s1exp_read (loc0, s1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.r0ead_prec_sta, f))
      end
    | S0Eide id => let
        // [e1xpdef] expansion is to be done in [ats_trans2.dats]
        // if it is done here, then it is only one level expansion
        val s1e = s1exp_ide (loc0, id)
      in
        case+ the_fxtyenv_find id of
          | ~Some_vt f => s1exp_make_opr (s1e, f) | ~None_vt () => $Fix.ITEMatm s1e
      end
    | S0Eimp tags => let
        val fc = $Syn.FUNCLOfun () // default is [function]
        val (fc, lin, prf, efc) = $Eff.e0fftaglst_tr (fc, tags)
(*
        val () = begin
          print "s0exp_tr: S0Eimp: efc = "; print efc; print_newline ()
        end
*)
      in
        case+ the_fxtyenv_find $Sym.symbol_MINUSGT of
        | ~Some_vt f => let
            val s1e_imp = s1exp_imp (loc0, fc, lin, prf, Some efc)
          in
            s1exp_make_opr (s1e_imp, f)
          end
        | ~None_vt () => begin
            prerr "Internal Error: ";
            prerr "s0exp_tr: the fixity of -> is unavailable.";
            prerr_newline ();
            $Err.abort ()
          end
      end
    | S0Elam (arg, res, body) => let
        val arg = s0arglst_tr arg
        val res = s0rtopt_tr res
        val body = s0exp_tr body
        val s1e_lam = s1exp_lam (loc0, arg, res, body)
(*
        val () = begin
          print "s0exp_tr: S0Elam: s1e_lam = ";
          print s1e_lam;
          print_newline ();
        end
*)
      in
        $Fix.ITEMatm s1e_lam
      end
    | S0Elist (s0es) => let
        val s1es = s0explst_tr s0es
      in
        $Fix.ITEMatm (s1exp_list (loc0, s1es))
      end
    | S0Elist2 (s0es1, s0es2) => let
        val s1es1 = s0explst_tr s0es1
        val s1es2 = s0explst_tr s0es2
      in
        $Fix.ITEMatm (s1exp_list2 (loc0, s1es1, s1es2))
      end
    | S0Eopide id => $Fix.ITEMatm (s1exp_ide (loc0, id))
    | S0Eqid (q, id) => $Fix.ITEMatm (s1exp_qid (loc0, q, id))
    | S0Estruct (ls0es) => let
        val ls1es = labs0explst_tr ls0es
      in
        $Fix.ITEMatm (s1exp_struct (loc0, ls1es))
      end
    | S0Etyarr (s0e_elt, s0ess_dim) => let
        val s1e_elt = s0exp_tr s0e_elt
        val s1ess_dim = s0explstlst_tr s0ess_dim
      in
        $Fix.ITEMatm (s1exp_tyarr (loc0, s1e_elt, s1ess_dim))
      end
    | S0Etyrec (flat, ls0es) => let
        val ls1es = labs0explst_tr ls0es
      in
        $Fix.ITEMatm (s1exp_tyrec (loc0, flat, ls1es))
      end
    | S0Etytup (flat, s0es) => let
        val s1es = s0explst_tr s0es
      in
        $Fix.ITEMatm (s1exp_tytup (loc0, flat, s1es))
      end
    | S0Etytup2 (flat, s0es1, s0es2) => let
        val s1es1 = s0explst_tr s0es1
        val s1es2 = s0explst_tr s0es2
      in
        $Fix.ITEMatm (s1exp_tytup2 (loc0, flat, s1es1, s1es2))
      end
    | S0Euni (s0qs) => let
        val s1qs = s0qualst_tr s0qs
        fn f (body: s1exp):<cloref1> s1expitm =
          let val loc0 = $Loc.location_combine (loc0, body.s1exp_loc) in
            $Fix.ITEMatm (s1exp_uni (loc0, s1qs, body))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.uni_prec_sta, f))
      end
    | S0Eunion (s0e, ls0es) => let
        val s1e = s0exp_tr s0e
        val ls1es = labs0explst_tr ls0es
      in
        $Fix.ITEMatm (s1exp_union (loc0, s1e, ls1es))
      end
    | _ => begin
        prerr loc0;
        prerr ": error(1)";
        prerr ": s0exp_tr: not available yet.\n";
        $Err.abort {s1expitm} ()
      end
  end

and aux_itemlst (s0e0: s0exp): s1expitmlst =
  let
    fun aux (res: s1expitmlst, s0e0: s0exp): s1expitmlst =
      case+ s0e0.s0exp_node of
      | S0Eapp (s0e1, s0e2) => 
        let val res = aux_item s0e2 :: res in
          aux (res, s0e1)
        end
      | _ => aux_item s0e0 :: res
  in
    aux (nil (), s0e0)
  end

in
  case+ aux_item s0e0 of
    | $Fix.ITEMatm s1e => s1e
    | $Fix.ITEMopr _ => s0exp_tr_errmsg_opr s0e0.s0exp_loc
end

implement s0explst_tr s0es =
  $Lst.list_map_fun (s0es, s0exp_tr)

implement s0expopt_tr (os0e) = case+ os0e of
  | Some s0e => Some (s0exp_tr s0e) | None () => None ()

implement s0explstlst_tr s0ess =
  $Lst.list_map_fun (s0ess, s0explst_tr)

implement labs0explst_tr ls0es = case+ ls0es of
  | LABS0EXPLSTcons (l, s0e, ls0es) =>
    LABS1EXPLSTcons (l.l0ab_lab, s0exp_tr s0e, labs0explst_tr ls0es)
  | LABS0EXPLSTnil () => LABS1EXPLSTnil ()

implement s0rtext_tr s0te = let
  val loc = s0te.s0rtext_loc
in
  case+ s0te.s0rtext_node of
  | S0TEsrt s0t => s1rtext_srt (loc, s0rt_tr s0t)
  | S0TEsub (id, s0te, s0p, s0ps) => let
      val s1te = s0rtext_tr s0te
      val s1p = s0exp_tr s0p and s1ps = s0explst_tr s0ps
    in
      s1rtext_sub (loc, id.i0de_sym, s1te, s1p :: s1ps)
    end
end // end of [s0rtext_tr]

(* ****** ****** *)

fun tmps0explstlst_tr (ts0ess: tmps0explstlst): tmps1explstlst = begin
  case+ ts0ess of
  | TMPS0EXPLSTLSTnil () => TMPS1EXPLSTLSTnil ()
  | TMPS0EXPLSTLSTcons (loc, s0es, ts0ess) => begin
     TMPS1EXPLSTLSTcons (loc, s0explst_tr s0es, tmps0explstlst_tr ts0ess)
    end
end // end of [tmps0explstlst_tr]

(* ****** ****** *)

fn witht0ype_tr (w0t: witht0ype): witht1ype = case+ w0t of
  | WITHT0YPEnone () => WITHT1YPEnone ()
  | WITHT0YPEprop s0e => WITHT1YPEprop (s0exp_tr s0e)
  | WITHT0YPEtype s0e => WITHT1YPEtype (s0exp_tr s0e)
  | WITHT0YPEview s0e => WITHT1YPEview (s0exp_tr s0e)
  | WITHT0YPEviewtype s0e => WITHT1YPEviewtype (s0exp_tr s0e)

(* ****** ****** *)

fn s0rtdef_tr (d: s0rtdef): s1rtdef = let
  val s1te = s0rtext_tr d.s0rtdef_def
(*
  val () = print "s0rtdef_tr: s1te = "
  val (pf_stdout | ptr_stdout) = stdout_get ()
  val () = fprint (file_mode_lte_w_w | !ptr_stdout, s1te)
  val () = stdout_view_set (pf_stdout | (*none*))
  val () = print_newline ()
*)
in
  s1rtdef_make (d.s0rtdef_loc, d.s0rtdef_sym, s1te)
end // end of [s0rtdef_tr]

fn s0rtdeflst_tr (ds: s0rtdeflst): s1rtdeflst =
  $Lst.list_map_fun (ds, s0rtdef_tr)

(* ****** ****** *)

fn s0expdef_tr (d: s0expdef): s1expdef = let
  val arg = s0arglstlst_tr d.s0expdef_arg
  val res = s0rtopt_tr d.s0expdef_res
  val def = s0exp_tr d.s0expdef_def
(*
  val () = begin
    print "s0expdef_tr: def = "; print def; print_newline ()
  end
*)
in
  s1expdef_make (d.s0expdef_loc, d.s0expdef_sym, arg, res, def)
end // end of [s0expdef_tr]

fn s0expdeflst_tr (ds: s0expdeflst): s1expdeflst =
  $Lst.list_map_fun (ds, s0expdef_tr)

(* ****** ****** *)

fn s0aspdec_tr (d: s0aspdec): s1aspdec = let
  val arg = s0arglstlst_tr d.s0aspdec_arg
  val res = s0rtopt_tr d.s0aspdec_res
  val def = s0exp_tr d.s0aspdec_def
in
  s1aspdec_make (d.s0aspdec_loc, d.s0aspdec_qid, arg, res, def)
end // end of [s0aspdec_tr]

(* ****** ****** *)

fn d0atcon_tr (d0c: d0atcon): d1atcon = let

val qua = s0qualstlst_tr (d0c.d0atcon_qua)
var npf_var: int = 0
val arg = (
  case+ d0c.d0atcon_arg of
  | Some s0e => let
      val s1e = s0exp_tr s0e
    in
      case+ s1e.s1exp_node of
      | S1Elist (npf, s1es) => (npf_var := npf; s1es)
      | _ => cons (s1e, nil ())
    end
  | None () => nil ()
) : s1explst

val ind = (
  case+ d0c.d0atcon_ind of
  | Some s0e => let
      val s1es = case+ s0e.s0exp_node of
        | S0Elist s0es => s0explst_tr s0es | _ => begin
            prerr "Internal Error: ";
            prerr "ats_trans1: d0atcon_tr: index is not a list.";
            prerr_newline ();
            $Err.abort ()
          end
    in
      Some s1es
    end
  | None () => None ()
) : s1explstopt

in
  d1atcon_make (d0c.d0atcon_loc, d0c.d0atcon_sym, qua, npf_var, arg, ind)
end // end of [d0atcon_tr]

fun d0atconlst_tr (ds: d0atconlst): d1atconlst = begin
  case+ ds of
  | cons (d, ds) => cons (d0atcon_tr d, d0atconlst_tr ds)
  | nil () => nil ()
end // end of [d0atconlst_tr]

fn d0atdec_tr (d0c: d0atdec): d1atdec = let
  val arg = (
    case+ d0c.d0atdec_arg of
    | Some d0as => Some (d0atarglst_tr d0as) | None () => None ()
  ) : d1atarglstopt

  val con = d0atconlst_tr d0c.d0atdec_con
in
  d1atdec_make (
    d0c.d0atdec_loc, d0c.d0atdec_fil, d0c.d0atdec_sym, arg, con
  ) // end of [d1atdec_make]
end // end of [d0atdec_tr]

fun d0atdeclst_tr (ds: d0atdeclst): d1atdeclst = begin
  case+ ds of
  | cons (d, ds) => cons (d0atdec_tr d, d0atdeclst_tr ds)
  | nil () => nil ()
end // end of [d0atdeclst_tr]

(* ****** ****** *)

fn e0xndec_tr (d: e0xndec): e1xndec = let

val qua = s0qualstlst_tr (d.e0xndec_qua)
var npf_var: int = 0
val arg = (
  case+ d.e0xndec_arg of
  | Some s0e => let
      val s1e = s0exp_tr s0e
    in
      case+ s1e.s1exp_node of
      | S1Elist (npf, s1es) => (npf_var := npf; s1es)
      | _ => cons (s1e, nil ())
    end
  | None () => nil ()
) : s1explst

in
  e1xndec_make (
    d.e0xndec_loc, d.e0xndec_fil, d.e0xndec_sym, qua, npf_var, arg
  ) // end of [e1xndec_make]
end // end of [e0xndec_tr]

fun e0xndeclst_tr (ds: e0xndeclst): e1xndeclst = begin
  case+ ds of
  | cons (d, ds) => cons (e0xndec_tr d, e0xndeclst_tr ds)
  | nil () => nil ()
end // end of [e0xndeclst_tr]

(* ****** ****** *)

typedef efc = $Eff.effcst
typedef efcopt = Option efc

// translation of dynamic constants

local // defining [d0cstdec_tr]

fun aux1 (xs: p0arglst): s1explst = begin case+ xs of
  | cons (x, xs) => begin case+ x.p0arg_ann of
    | Some s0e => begin
        let val s1e = s0exp_tr s0e in s1e :: aux1 xs end
      end
    | None () => begin
        prerr x.p0arg_loc;
        prerr ": error(1)";
        prerr ": unascribed variable: ["; prerr x.p0arg_sym; prerr "]";
        prerr_newline ();
        $Err.abort ()
      end
  end
  | nil () => nil ()
end // end of [aux1]

fun aux2
  (fc: funclo, lin: int, prf: int, oefc: efcopt,
   fst: int, lst: &int, xs: d0arglst, s1e_res: s1exp)
  : s1exp = begin case+ xs of
  | x :: xs => begin case+ x.d0arg_node of
    | D0ARGdyn ys => let
        val loc_x = x.d0arg_loc
        val s1es_arg = s1exp_list (loc_x, aux1 ys)
        val s1e_res = aux2 (fc, lin, prf, oefc, fst+1, lst, xs, s1e_res)
        val loc_res = s1e_res.s1exp_loc
        val loc = $Loc.location_combine (loc_x, loc_res)
        val fc = if fst > 0 then FUNCLOcloptr else fc
        val imp: s1exp =
          if lst > 0 then begin
            s1exp_imp (loc_res, fc, 0, 0, None ())
          end else begin
            s1exp_imp (loc_res, fc, lin, prf, oefc)
          end
      in
        lst := lst + 1; s1exp_app (loc, imp, loc, '[s1es_arg, s1e_res])
      end
    | D0ARGdyn2 (ys1, ys2) => let
        val loc_x = x.d0arg_loc
        val s1es_arg = s1exp_list2 (loc_x, aux1 ys1, aux1 ys2)
        val s1e_res = aux2 (fc, lin, prf, oefc, fst+1, lst, xs, s1e_res)
        val loc_res = s1e_res.s1exp_loc
        val loc = $Loc.location_combine (loc_x, loc_res)
        val fc = if fst > 0 then FUNCLOcloptr else fc
        val imp: s1exp =
          if lst > 0 then begin
            s1exp_imp (loc_res, fc, 0, 0, None ())
          end else begin
            s1exp_imp (loc_res, fc, lin, prf, oefc)
          end
      in
        lst := lst + 1; s1exp_app (loc, imp, loc, '[s1es_arg, s1e_res])
      end
    | D0ARGsta s0qs => let
        val loc_x = x.d0arg_loc
        val s1qs = s0qualst_tr s0qs
        val s1e_res = aux2 (fc, lin, prf, oefc, fst, lst, xs, s1e_res)
        val loc_res = s1e_res.s1exp_loc
        val loc = $Loc.location_combine (loc_x, loc_res)
        val () =
          if lst = 0 then begin
            prerr loc_res;
            prerr ": error(1)";
            prerr ": illegal use of effect annotation.";
            prerr_newline ();
            $Err.abort {void} ()
          end
      in
        s1exp_uni (loc, s1qs, s1e_res)
      end
    end
  | nil () => s1e_res
end // end of [aux2]

fn aux3 (
    loc0: loc_t
  , isfun: bool
  , isprf: bool
  , xs: d0arglst
  , otags: Option e0fftaglst
  , s1e_res: s1exp
  ) : s1exp = let
  var fc: funclo = $Syn.FUNCLOfun ()
  var lin: int = 0 and prf: int = (if isprf then 1 else 0): int
  var oefc: efcopt = None ()
  val () = case+ otags of
    | Some tags => let
        val (fc1, lin1, prf1, efc1) = $Eff.e0fftaglst_tr (fc, tags)
      in
        fc := fc1; lin := lin1; prf := prf + prf1; oefc := Some efc1
      end
    | None () => ()
  val () = case+ fc of
    | $Syn.FUNCLOclo knd => begin
        if knd <> CLOREF then begin
          prerr loc0;
          prerr ": error(1)";
          if knd = 0 then begin
            prerr ": Internal Error: a closure at the toplevel."
          end;
          if knd = 1 then begin
            prerr ": a closure pointer is not allowed at the toplevel."
          end;
          prerr_newline ();
          $Err.abort {void} ()
        end
      end // end of [FUNCLOclo]
    | $Syn.FUNCLOfun () => ()
  var lst: int = 0
in
  aux2 (fc, lin, prf, oefc, 0, lst, xs, s1e_res)
end // end of [aux2]

in // in of [local]

fn d0cstdec_tr (isfun: bool, isprf: bool, d: d0cstdec): d1cstdec =
  let
    val loc0 = d.d0cstdec_loc
    val s1e_res = s0exp_tr d.d0cstdec_res
    val s1e = aux3 (loc0, isfun, isprf, d.d0cstdec_arg, d.d0cstdec_eff, s1e_res)
  in
    d1cstdec_make (loc0, d.d0cstdec_fil, d.d0cstdec_sym, s1e, d.d0cstdec_ext)
  end

fun d0cstdeclst_tr
  (isfun: bool, isprf: bool, ds: d0cstdeclst): d1cstdeclst = 
  case+ ds of
  | cons (d, ds) => begin
      cons (d0cstdec_tr (isfun, isprf, d), d0cstdeclst_tr (isfun, isprf, ds))
    end
  | nil () => nil ()

end // end of [local]

(* ****** ****** *)

// translation of dynamic patterns

typedef p1atitm = $Fix.item p1at
typedef p1atitmlst = List p1atitm

val p1atitm_app : p1atitm = let

fn f (p1t1: p1at, p1t2: p1at):<cloref1> p1atitm =
  let
    val loc = $Loc.location_combine (p1t1.p1at_loc, p1t2.p1at_loc)
    val p1t_app = case+ p1t2.p1at_node of
      | P1Tlist (npf, p1ts) => begin
          p1at_app_dyn (loc, p1t1, p1t2.p1at_loc, npf, p1ts)
        end
      | P1Tsvararg s1a => begin case+ p1t1.p1at_node of
          | P1Tapp_sta (p1t1, s1as) => begin
              p1at_app_sta (loc, p1t1, $Lst.list_extend (s1as, s1a))
            end
          | _ => begin
              p1at_app_sta (loc, p1t1, cons (s1a, nil ()))
            end
        end
      | _ => begin
          p1at_app_dyn (loc, p1t1, p1t2.p1at_loc, 0, cons (p1t2, nil ()))
        end
(*
    val () = begin
      print "p1atitm_app: f: p1t_app = "; print p1t_app; print_newline ()
    end
*)
  in
    $Fix.ITEMatm p1t_app
  end

in
  $Fix.item_app f
end // end of [app_p1at_item]

fun p1at_make_opr (p1t: p1at, f: $Fix.fxty_t): p1atitm = begin
  $Fix.oper_make {p1at} (
    lam x => x.p1at_loc
  , lam (loc, x, loc_arg, xs) => p1at_app_dyn (loc, x, loc_arg, 0, xs)
  , p1t
  , f
  )
end // end of [p1at_make_opr]

val p1atitm_backslash : p1atitm = begin
  $Fix.oper_make_backslash {p1at} (
    lam x => x.p1at_loc,
    lam (loc, x, loc_arg, xs) => p1at_app_dyn (loc, x, loc_arg, 0, xs)
  )
end // end of [p1atitm_backslash]

(* ****** ****** *)

fn s0vararg_tr (s0a: s0vararg): s1vararg =
  case+ s0a of
  | S0VARARGseq (s0as) => S1VARARGseq (s0arglst_tr s0as)
  | S0VARARGone () => S1VARARGone ()
  | S0VARARGall () => S1VARARGall ()

(* ****** ****** *)

fn p0at_tr_errmsg_opr (loc: loc_t): p1at = begin
  prerr loc;
  prerr ": error(1)";
  prerr ": the operator needs to be applied.\n";
  $Err.abort {p1at} ()
end

implement p0at_tr p0t0 = let

fun aux_item (p0t0: p0at): p1atitm = let
  val loc = p0t0.p0at_loc in case+ p0t0.p0at_node of
    | P0Tann (p0t, s0e) => let
        val p1t = p0at_tr p0t and s1e = s0exp_tr s0e
        val p1t_ann = p1at_ann (loc, p1t, s1e)
      in
        $Fix.ITEMatm p1t_ann
      end
    | P0Tapp _ => let 
        val p1t = $Fix.fixity_resolve
          (loc, p1atitm_app, aux_itemlst p0t0)
      in
        $Fix.ITEMatm p1t
      end
    | P0Tas (id, p0t) => begin
        $Fix.ITEMatm (p1at_as (loc, id, p0at_tr p0t))
      end
    | P0Tchar c(*char*) => $Fix.ITEMatm (p1at_char (loc, c))
    | P0Texist (s0as) => let
        val s1as = s0arglst_tr s0as
        fn f (body: p1at):<cloref1> p1atitm =
          let val loc = $Loc.location_combine (loc, body.p1at_loc) in
            $Fix.ITEMatm (p1at_exist (loc, s1as, body))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.exist_prec_dyn, f))
      end
    | P0Tfloat f(*string*) => $Fix.ITEMatm (p1at_float (loc, f))
    | P0Tfree (p0t) => begin
        $Fix.ITEMatm (p1at_free (loc, p0at_tr p0t))
      end
    | P0Tide id when id = $Sym.symbol_UNDERSCORE => begin
        $Fix.ITEMatm (p1at_anys loc)
      end
    | P0Tide id when id = $Sym.symbol_BACKSLASH => begin
        p1atitm_backslash
      end
    | P0Tide id => let
        val p1t = p1at_ide (loc, id)
      in
        case+ the_fxtyenv_find id of
        | ~Some_vt f => p1at_make_opr (p1t, f)
        | ~None_vt () => $Fix.ITEMatm p1t
      end
    | P0Tint (str) => begin
        $Fix.ITEMatm (p1at_int (loc, str))
      end
    | P0Tlist (p0ts) => let
        val p1ts = p0atlst_tr p0ts
      in
        $Fix.ITEMatm (p1at_list (loc, p1ts))
      end
    | P0Tlist2 (p0ts1, p0ts2) => let
        val s1es1 = p0atlst_tr p0ts1 and s1es2 = p0atlst_tr p0ts2
      in
        $Fix.ITEMatm (p1at_list2 (loc, s1es1, s1es2))
      end
    | P0Tlst (p0ts) => let
        val p1ts = p0atlst_tr p0ts
      in
        $Fix.ITEMatm (p1at_lst (loc, p1ts))
      end
    | P0Topide id => $Fix.ITEMatm (p1at_ide (loc, id))
    | P0Tqid (q, id) => $Fix.ITEMatm (p1at_qid (loc, q, id))
    | P0Trec (recknd, lp0ts) => begin
        $Fix.ITEMatm (p1at_rec (loc, recknd, labp0atlst_tr lp0ts))
      end
    | P0Tref (id) => begin
        $Fix.ITEMatm (p1at_ref (loc, id))
      end
    | P0Trefas (id, p0t) => begin
        $Fix.ITEMatm (p1at_refas (loc, id, p0at_tr p0t))
      end
    | P0Tsvararg s0a => begin
        $Fix.ITEMatm (p1at_svararg (loc, s0vararg_tr s0a))
      end
    | P0Tstring str => begin
        $Fix.ITEMatm (p1at_string (loc, str))
      end
    | P0Ttup (tupknd, p0ts) => let
        val p1ts = p0atlst_tr p0ts
      in
        $Fix.ITEMatm (p1at_tup (loc, tupknd, p1ts))
      end
    | P0Ttup2 (tupknd, p0ts1, p0ts2) => let
        val p1ts1 = p0atlst_tr p0ts1
        val p1ts2 = p0atlst_tr p0ts2
      in
        $Fix.ITEMatm (p1at_tup2 (loc, tupknd, p1ts1, p1ts2))
      end
(*
    | _ => begin
        prerr p0t0.p0at_loc;
        prerr ": error(1)";
        prerr ": p0at_tr: not available yet.\n";
        $Err.abort {p1atitm} ()
      end
*)
  end

and aux_itemlst (p0t0: p0at): p1atitmlst =
  let
    fun aux (res: p1atitmlst, p0t0: p0at): p1atitmlst =
      case+ p0t0.p0at_node of
      | P0Tapp (p0t1, p0t2) => let
          val res = aux_item p0t2 :: res
        in
          aux (res, p0t1)
        end
      | _ => aux_item p0t0 :: res
  in
    aux (nil (), p0t0)
  end

in
  case+ aux_item p0t0 of
    | $Fix.ITEMatm p1t => p1t
    | $Fix.ITEMopr _ => p0at_tr_errmsg_opr p0t0.p0at_loc
end

implement p0atlst_tr p0ts = case+ p0ts of
  | p0t :: p0ts => p0at_tr p0t :: p0atlst_tr p0ts
  | nil () => nil ()

implement labp0atlst_tr (lp0ts) = case+ lp0ts of
  | LABP0ATLSTcons (l, p0t, lp0ts) => begin
      LABP1ATLSTcons (l, p0at_tr p0t, labp0atlst_tr lp0ts)
    end
  | LABP0ATLSTnil () => LABP1ATLSTnil ()
  | LABP0ATLSTdot () => LABP1ATLSTdot ()

(* ****** ****** *)

// translation of dynamic expressions

typedef d1expitm = $Fix.item d1exp
typedef d1expitmlst = List d1expitm

val d1expitm_app : d1expitm = let

fn f (d1e1: d1exp, d1e2: d1exp):<cloref1> d1expitm = let
  val loc = $Loc.location_combine (d1e1.d1exp_loc, d1e2.d1exp_loc)
  val d1e_app = begin case+ d1e2.d1exp_node of
    | D1Elist (npf, d1es) => begin
        d1exp_app_dyn (loc, d1e1, d1e2.d1exp_loc, npf, d1es)
      end
    | D1Esexparg s1a => begin case+ d1e1.d1exp_node of
      | D1Eapp_sta (d1e1, s1as) => begin
          d1exp_app_sta (loc, d1e1, $Lst.list_extend (s1as, s1a))
        end
      | _ => begin
          d1exp_app_sta (loc, d1e1, cons (s1a, nil ()))
        end
      end // end of [D1Esexparg]
    | _ => d1exp_app_dyn
        (loc, d1e1, d1e2.d1exp_loc, 0, cons (d1e2, nil ()))
  end // end of [val]
(*
  val () = begin
    print "d1expitm_app: f: d1e_app = "; print d1e_app; print_newline ()
  end
*)
in
  $Fix.ITEMatm d1e_app
end // end of [f]

in
  $Fix.item_app f
end // end of [app_d1exp_item]

fun d1exp_make_opr (d1e: d1exp, f: $Fix.fxty_t): d1expitm = begin
  $Fix.oper_make {d1exp} (
    lam x => x.d1exp_loc
  , lam (loc, x, loc_arg, xs) => d1exp_app_dyn (loc, x, loc_arg, 0, xs)
  , d1e
  , f
  )
end // end of [d1exp_make_opr]

val d1expitm_backslash : d1expitm = begin
  $Fix.oper_make_backslash {d1exp} (
    lam x => x.d1exp_loc,
    lam (loc, x, loc_arg, xs) => d1exp_app_dyn (loc, x, loc_arg, 0, xs)
  )
end // end of [d1expitm_backslash]

(* ****** ****** *)

fn s0exparg_tr (loc: loc_t, s0a: s0exparg): s1exparg =
  case+ s0a of
  | S0EXPARGone () => s1exparg_one (loc)
  | S0EXPARGall () => s1exparg_all (loc)
  | S0EXPARGseq (s0as) => s1exparg_seq (loc, s0explst_tr s0as)

fn s0expdarg_tr (d0e: d0exp): s1exparg = let
  val d1e = d0exp_tr d0e in case+ d1e.d1exp_node of
    | D1Esexparg s1a => s1a
    | _ => begin
        prerr d0e.d0exp_loc;
        prerr ": Internal Error: d0exp_tr: D0Efoldat";
        prerr_newline ();
        $Err.abort {s1exparg} ()
      end
end // end of [s0expdarg_tr]

fun s0expdarglst_tr (d0es: d0explst): s1exparglst = begin
  case+ d0es of
  | cons (d0e, d0es) => cons (s0expdarg_tr d0e, s0expdarglst_tr d0es)
  | nil () => nil ()
end // end of [s0expdarglst_tr]

(* ****** ****** *)

(*

fun d1exp_retpos_set (d1e0: d1exp): void = let
  fn* aux (d1e: d1exp): void = begin case+ d1e.d1exp_node of
    | D1Eann_type (d1e, _(*s1e*)) => aux (d1e)
    | D1Ecaseof (_(*casknd*), retpos, _(*inv*), _(*d1es*), c1ls) => begin
        !retpos := 1; auxclaulst (c1ls)
      end // end of [D1Ecaseof]
    | D1Eif (retpos, _(*inv*), _(*cond*), d1e_then, od1e_else) => begin
        !retpos := 1; aux d1e_then; auxopt od1e_else
      end // end of [D1Eif]
    | D1Esif (retpos, _(*inv*), _(*cond*), d1e_then, d1e_else) => begin
        !retpos := 1; aux d1e_then; aux d1e_else
      end // end of [D1Esif]
    | D1Eseq (d1es) => begin case+ d1es of
      | list_cons (d1e, d1es) => auxseq (d1e, d1es) | list_nil () => ()
      end
    | D1Elet (_(*d1cs*), d1e) => aux (d1e)
    | _ => ()
  end // end of [aux]

  and auxopt (od1e: d1expopt): void = begin
    case+ od1e of Some d1e => aux d1e | None () => ()
  end // end of [auxopt]

  and auxseq (d1e: d1exp, d1es: d1explst): void = begin case+ d1es of
    | list_cons (d1e, d1es) => auxseq (d1e, d1es) | list_nil () => aux d1e
  end // end of [auxseq]

  and auxclau (c1l: c1lau): void = aux (c1l.c1lau_exp)

  and auxclaulst (c1ls: c1laulst): void = begin case+ c1ls of
    | list_cons (c1l, c1ls) => (auxclau c1l; auxclaulst c1ls) | list_nil () => ()
  end // end of [auxclaulst]
in
  aux (d1e0)
end // end of [d1exp_retpos_set]

*)

(* ****** ****** *)

fn d0exp_lams_dyn_tr
  (oloc: Option loc_t,
   ofc: Option funclo,
   lin: int,
   args: f0arglst,
   res: s0expopt,
   oefc: efcopt,
   d0e_body: d0exp): d1exp = let

fun aux (args: f0arglst, d1e_body: d1exp, flag: int)
  :<cloptr1> d1exp = begin case+ args of
  | arg :: args => let
      val loc_arg = arg.f0arg_loc
      val d1e_body = aux (args, d1e_body, flag1) where {
        val flag1 = (
          case+ arg.f0arg_node of F0ARGdyn _ => flag + 1 | _ => flag
        ) : int
      } // end of [where]
      val loc_body = d1e_body.d1exp_loc
      val loc = case+ oloc of
        | Some loc => loc
        | None () => begin
            $Loc.location_combine (loc_arg, loc_body)
          end
    in
      case+ arg.f0arg_node of
      | F0ARGsta1 s0qs => begin
          d1exp_lam_sta_syn (loc, loc_arg, s0qualst_tr s0qs, d1e_body)
        end
      | F0ARGsta2 s0as => begin
          d1exp_lam_sta_ana (loc, loc_arg, s0arglst_tr s0as, d1e_body)
        end
      | F0ARGdyn p0t => let
          val p1t = p0at_tr p0t
          val d1e_body = (
            if flag = 0 then d1e_body else begin
              // linear closure
              d1exp_ann_funclo_opt (loc_body, d1e_body, FUNCLOcloptr)
            end
          ) : d1exp
        in
          d1exp_lam_dyn (loc, lin, p1t, d1e_body)
        end
      | F0ARGmet s0es => begin
          d1exp_lam_met (loc, loc_arg, s0explst_tr s0es, d1e_body)
        end
    end
  | nil () => d1e_body
end // end of [aux]

val d1e_body = d0exp_tr d0e_body
(*
val () = d1exp_retpos_set (d1e_body) // set retpos for case/if/sif-expressions
*)

val d1e_body = (
  case+ res of
  | Some s0e => let
      val loc = begin
        $Loc.location_combine (s0e.s0exp_loc, d1e_body.d1exp_loc)
      end
      val s1e = s0exp_tr s0e
    in
      d1exp_ann_type (loc, d1e_body, s1e)
    end
  | None () => d1e_body
) : d1exp

val d1e_body = (
  case+ oefc of
  | Some efc => begin
      d1exp_ann_effc (d1e_body.d1exp_loc, d1e_body, efc)
    end
  | None () => d1e_body
) : d1exp

val d1e_body = (
  case+ ofc of
  | Some fc => begin
      d1exp_ann_funclo (d1e_body.d1exp_loc, d1e_body, fc)
    end
  | None () => d1e_body
) : d1exp

in
  aux (args, d1e_body, 0(*flag*))
end // end of [d0exp_lams_dyn_tr]

(* ****** ****** *)

fn termination_metric_check
  (loc: loc_t, is_met: bool, oefc: efcopt): void =
  case+ oefc of
  | Some efc => let
      val is_okay =
        if is_met then true else $Eff.effcst_contain_ntm efc
    in
      if (is_okay) then () else begin
        prerr loc;
        prerr ": error(1)";
        prerr ": a termination metric is missing.";
        prerr_newline ();
        $Err.abort ()
      end
    end
  | None () => ()

(* ****** ****** *)

fn i0nvarg_tr (arg: i0nvarg): i1nvarg =
  let val os1e = s0expopt_tr arg.i0nvarg_typ in
    i1nvarg_make (arg.i0nvarg_loc, arg.i0nvarg_sym, os1e)
  end

fun i0nvarglst_tr (args: i0nvarglst): i1nvarglst =
  case+ args of
  | cons (arg, args) => cons (i0nvarg_tr arg, i0nvarglst_tr args)
  | nil () => nil ()

fn i0nvresstate_tr
  (res: i0nvresstate): i1nvresstate = let
  val s1qs = (
    case+ res.i0nvresstate_qua of
    | Some s0qs => s0qualst_tr s0qs | None () => nil ()
  ) : s1qualst
  val arg = i0nvarglst_tr res.i0nvresstate_arg
in
  i1nvresstate_make (s1qs, arg)
end // end of [i0nvresstate_tr]

val i1nvresstate_nil = i1nvresstate_make (nil (), nil ())

fn loopi0nv_tr
  (loc0: loc_t, inv: loopi0nv): loopi1nv = let
  val qua = (
    case+ inv.loopi0nv_qua of
    | Some s0qs => s0qualst_tr s0qs | None () => nil ()
  ) : s1qualst
  val met = (
    case+ inv.loopi0nv_met of
    | Some s0es => Some (s0explst_tr s0es)
    | None () => None ()
  ) : s1explstopt
  val arg = i0nvarglst_tr inv.loopi0nv_arg
  val res = i0nvresstate_tr inv.loopi0nv_res
in
  loopi1nv_make (loc0, qua, met, arg, res)
end // end of [loopi0nv_tr]

fun loopi1nv_nil (loc0: loc_t): loopi1nv = begin
  loopi1nv_make (loc0, nil (), None (), nil (), i1nvresstate_nil)
end // end of [loopi1nv_nil]

(* ****** ****** *)

fn m0atch_tr (m0at: m0atch): m1atch = let
  val d1e = d0exp_tr m0at.m0atch_exp
  val op1t = (
    case+ m0at.m0atch_pat of
    | Some p0t => Some (p0at_tr p0t) | None () => None ()
  ) : p1atopt
in
  m1atch_make (m0at.m0atch_loc, d1e, op1t)
end

fn m0atchlst_tr (m0ats: m0atchlst): m1atchlst =
  $Lst.list_map_fun (m0ats, m0atch_tr)

fn c0lau_tr (c0l: c0lau): c1lau = let

val gp0t = c0l.c0lau_pat
val gua = m0atchlst_tr (gp0t.guap0at_gua)
val p1t = p0at_tr (gp0t.guap0at_pat)
val body = d0exp_tr (c0l.c0lau_body)

in
  c1lau_make (c0l.c0lau_loc, p1t, gua, c0l.c0lau_seq, c0l.c0lau_neg, body)
end // end of [c0lau_tr]

fun c0laulst_tr (c0ls: c0laulst): c1laulst = case+ c0ls of
  | cons (c0l, c0ls) => cons (c0lau_tr c0l, c0laulst_tr c0ls)
  | nil () => nil ()

(* ****** ****** *)

fn d0exp_tr_errmsg_opr (loc: loc_t): d1exp = begin
  prerr loc;
  prerr ": error(1)";
  prerr ": the operator needs to be applied.\n";
  $Err.abort {d1exp} ()
end

implement d0exp_tr d0e0 = let

fun aux_item (d0e0: d0exp): d1expitm = let
  val loc0 = d0e0.d0exp_loc in case+ d0e0.d0exp_node of
    | D0Eann (d0e, s0e) => let
        val d1e = d0exp_tr d0e and s1e = s0exp_tr s0e
        val d1e_ann = d1exp_ann_type (loc0, d1e, s1e)
      in
        $Fix.ITEMatm d1e_ann
      end
    | D0Eapp _ => let 
        val d1e =
          $Fix.fixity_resolve (loc0, d1expitm_app, aux_itemlst d0e0)
      in
        $Fix.ITEMatm d1e
      end
    | D0Earr (s0e_elt, d0es_elt) => let
        val s1e_elt = s0exp_tr s0e_elt
        val d1es_elt = d0explst_tr d0es_elt
        val d1e_arr = d1exp_arr (loc0, s1e_elt, d1es_elt)
      in
        $Fix.ITEMatm (d1e_arr)
      end
    | D0Earrsub (qid, loc_ind, d0ess) => let
        val d1e_arr =
          d1exp_qid (qid.arrqi0de_loc, qid.arrqi0de_qua, qid.arrqi0de_sym)
        val d1ess_ind = d0explstlst_tr d0ess
      in
        $Fix.ITEMatm (d1exp_arrsub (loc0, d1e_arr, loc_ind, d1ess_ind))
      end
    | D0Ecaseof (hd, d0e, c0ls) => let
        val casknd = hd.casehead_knd
        val inv = i0nvresstate_tr (hd.casehead_inv)
        val d1e = d0exp_tr d0e
        val d1es = (
          case+ d1e.d1exp_node of
          | D1Elist (_npf, d1es) => d1es | _ => cons (d1e, nil ())
        ) : d1explst
        val c1ls = c0laulst_tr c0ls
      in
        $Fix.ITEMatm (d1exp_caseof (loc0, casknd, inv, d1es, c1ls))
      end
    | D0Echar chr => begin
        $Fix.ITEMatm (d1exp_char (loc0, chr))
      end
    | D0Ecrypt (knd) => let
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc) in
            $Fix.ITEMatm (d1exp_crypt (loc0, knd, d1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.crypt_prec_dyn, f))
      end
    | D0Edelay (lin) => let
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc) in
            $Fix.ITEMatm (d1exp_delay (loc0, lin, d1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.delay_prec_dyn, f))
      end
    | D0Edynload () => let
        fn f (d1e: d1exp):<cloref1> d1expitm = case+ d1e.d1exp_node of
          | D1Estring (name, _) => let
              val fil = case+ $Fil.filenameopt_make name of
                | ~Some_vt fil => fil
                | ~None_vt () => begin
                    prerr d1e.d1exp_loc; prerr ": error(1)";
                    prerr ": the file ["; prerr name;
                    prerr "] is not available for dynamic loading.";
                    prerr_newline ();
                    $Err.abort {fil_t} ()
                  end
              val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc)
            in
              $Fix.ITEMatm (d1exp_dynload (loc0, fil))
            end
          | _ => begin
              prerr d1e.d1exp_loc; prerr ": error(1)";
              prerr ": the dynamic expression must be a string constant.";
              prerr_newline ();
              $Err.abort {d1expitm} ()
            end
          // end of [case]
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.dynload_prec_dyn, f))
      end
    | D0Eeffmask (effs) => let
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc) in
            $Fix.ITEMatm (d1exp_effmask (loc0, effs, d1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.delay_prec_dyn, f))
      end
    | D0Eempty () => $Fix.ITEMatm (d1exp_empty loc0)
    | D0Eexist (qualoc, s0a, d0e) => let
        val s1a = s0exparg_tr (qualoc, s0a) and d1e = d0exp_tr d0e
      in
        $Fix.ITEMatm (d1exp_exist (loc0, s1a, d1e))
      end
    | D0Eextval (s0e_typ, code (*string*)) => let
        val s1e_typ = s0exp_tr s0e_typ
      in
        $Fix.ITEMatm (d1exp_extval (loc0, s1e_typ, code))
      end 
    | D0Efix (id, args, res, otags, body) => let
        val oloc0 = Some loc0
        val (ofc, lin, oefc) = (
          case+ otags of
          | Some tags => let
              val fc = $Syn.FUNCLOfun () // default is [function]
              val (fc, lin, prf, efc) = $Eff.e0fftaglst_tr (fc, tags)
            in
              (Some fc, lin, Some efc)
            end
          | None () => (None () (*ofc*), 0 (*lin*), None () (*oefc*))
        ) : (Option funclo, int, efcopt)
        val d1e_fun =
          d0exp_lams_dyn_tr (oloc0, ofc, lin, args, res, oefc, body)
        val () = termination_metric_check (loc0, false (*met*), oefc)
      in
        $Fix.ITEMatm (d1exp_fix (loc0, id, d1e_fun))
      end
    | D0Efloat (str (*float*)) => begin
        $Fix.ITEMatm (d1exp_float (loc0, str))
      end
    | D0Efloatsp (str (*float*)) => begin
        $Fix.ITEMatm (d1exp_floatsp (loc0, str))
      end
    | D0Efoldat (d0es) => let
        val s1as = s0expdarglst_tr d0es
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc) in
            $Fix.ITEMatm (d1exp_foldat (loc0, s1as, d1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.foldat_prec_dyn, f))
      end
    | D0Efor (inv, loc_inv, ini, test, post, body) => let
        val inv: loopi1nv = case+ inv of
          | Some inv => loopi0nv_tr (loc_inv, inv)
          | None () => loopi1nv_nil (loc_inv)
        val ini = d0exp_tr ini
        val test = d0exp_tr test
        val post = d0exp_tr post
        val body = d0exp_tr body
      in 
        $Fix.ITEMatm (d1exp_for (loc0, inv, ini, test, post, body))
      end
    | D0Efreeat (d0es) => let
        val s1as = s0expdarglst_tr d0es
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc) in
            $Fix.ITEMatm (d1exp_freeat (loc0, s1as, d1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.freeat_prec_dyn, f))
      end
    | D0Eide id when id = $Sym.symbol_BACKSLASH => d1expitm_backslash
    | D0Eide id => let
        val d1e = d1exp_ide (loc0, id)
      in
        case+ the_fxtyenv_find id of
        | ~Some_vt f => d1exp_make_opr (d1e, f)
        | ~None_vt () => $Fix.ITEMatm d1e
      end
    | D0Eif (hd, d0e_cond, d0e_then, od0e_else) => let
        val inv = i0nvresstate_tr hd.ifhead_inv
        val d1e_cond = d0exp_tr d0e_cond
        val d1e_then = d0exp_tr d0e_then
        val od1e_else = d0expopt_tr od0e_else
        val d1e_if = d1exp_if (loc0, inv, d1e_cond, d1e_then, od1e_else)
      in
        $Fix.ITEMatm (d1e_if)        
      end
    | D0Eint (str (*int*)) => begin
        $Fix.ITEMatm (d1exp_int (loc0, str))
      end
    | D0Eintsp (str (*int*)) => begin
        $Fix.ITEMatm (d1exp_intsp (loc0, str))
      end
    | D0Elam (lin0, args, res, otags, body) => let
        val oloc0 = Some loc0
        val (ofc, lin, oefc) = (
          case+ otags of
          | Some tags => let
              val fc = $Syn.FUNCLOfun () // default is [function]
              val (fc, lin, prf, efc) = $Eff.e0fftaglst_tr (fc, tags)
              val lin = if lin0 > 0 then 1 else lin
            in
              (Some fc, lin, Some efc)
            end
          | None () => (None (), lin0, None ())
        ) : (Option funclo, int, efcopt)
        val d1e_lam = d0exp_lams_dyn_tr (oloc0, ofc, lin, args, res, oefc, body)
      in
        $Fix.ITEMatm (d1e_lam)
      end
    | D0Elet (d0cs, d0e) => let
        val (pf | ()) = trans1_level_inc ()
        val () = trans1_env_push ()
        val d1cs = d0eclst_tr d0cs
        val d1e = d0exp_tr d0e
        val () = trans1_env_pop ()
        val () = trans1_level_dec (pf | (*none*))
      in
        $Fix.ITEMatm (d1exp_let (loc0, d1cs, d1e))
      end
    | D0Elist (d0es) => let
        val d1es = d0explst_tr d0es
      in
        $Fix.ITEMatm (d1exp_list (loc0, d1es))
      end
    | D0Elist2 (d0es1, d0es2) => let
        val s1es1 = d0explst_tr d0es1 and s1es2 = d0explst_tr d0es2
      in
        $Fix.ITEMatm (d1exp_list2 (loc0, s1es1, s1es2))
      end
    | D0Eloopexn (i (*break/continue*)) => begin
        $Fix.ITEMatm (d1exp_loopexn (loc0, i))
      end
    | D0Elst (lin, os0e_elt, d0es_elt) => let
        val os1e_elt = s0expopt_tr os0e_elt
        val d1es_elt = d0explst_tr d0es_elt
        val d1e_lst = d1exp_lst (loc0, lin, os1e_elt, d1es_elt)
      in
        $Fix.ITEMatm (d1e_lst)
      end
    | D0Emacsyn (knd, d0e) => begin
        $Fix.ITEMatm (d1exp_macsyn (loc0, knd, d0exp_tr d0e))
      end
    | D0Eopide id => $Fix.ITEMatm (d1exp_ide (loc0, id))
    | D0Eptrof () => let
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc) in
            $Fix.ITEMatm (d1exp_ptrof (loc0, d1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.ptrof_prec_dyn, f))
      end
    | D0Eqid (q, id) => $Fix.ITEMatm (d1exp_qid (loc0, q, id))
    | D0Eraise (d0e) => begin
        $Fix.ITEMatm (d1exp_raise (loc0, d0exp_tr d0e))
      end
    | D0Erec (recknd, ld0es) => let
        val ld1es = labd0explst_tr ld0es
      in
        $Fix.ITEMatm (d1exp_rec (loc0, recknd, ld1es))
      end
    | D0Esel_lab (knd, lab) => let
        val d1l = d1lab_lab (loc0, lab)
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (d1e.d1exp_loc, loc0) in
            $Fix.ITEMatm (d1exp_sel (loc0, knd, d1e, d1l))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpos ($Fix.select_prec, f))
      end
    | D0Esel_ind (knd, ind) => let
        val ind = d0explstlst_tr ind
        val d1l = d1lab_ind (loc0, ind)
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (d1e.d1exp_loc, loc0) in
            $Fix.ITEMatm (d1exp_sel (loc0, knd, d1e, d1l))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpos ($Fix.select_prec, f))
      end
    | D0Eseq d0es => begin
        $Fix.ITEMatm (d1exp_seq (loc0, d0explst_tr d0es))
      end
    | D0Esexparg (s0a) => let
        val s1a = s0exparg_tr (loc0, s0a)
      in
        $Fix.ITEMatm (d1exp_sexparg (loc0, s1a))
      end
    | D0Esif (hd, s0e_cond, d0e_then, d0e_else) => let
        val inv = i0nvresstate_tr hd.ifhead_inv
        val s1e_cond = s0exp_tr s0e_cond
        val d1e_then = d0exp_tr d0e_then
        val d1e_else = d0exp_tr d0e_else
        val d1e_sif = d1exp_sif (loc0, inv, s1e_cond, d1e_then, d1e_else)
      in
        $Fix.ITEMatm (d1e_sif)        
      end
    | D0Espawn () => let
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc) in
            $Fix.ITEMatm (d1exp_spawn (loc0, d1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.spawn_prec_dyn, f))
      end
    | D0Estring (str, len) => begin
        $Fix.ITEMatm (d1exp_string (loc0, str, len))
      end
    | D0Estruct (ld0es) => let
        val ld1es = labd0explst_tr ld0es
      in
        $Fix.ITEMatm (d1exp_struct (loc0, ld1es))
      end
    | D0Etmpid (qid, ts0ess) => let
        val ts1ess = tmps0explstlst_tr ts0ess
      in
        $Fix.ITEMatm (d1exp_tmpid (loc0, qid, ts1ess))
      end
    | D0Etop () => $Fix.ITEMatm (d1exp_top loc0)
    | D0Etrywith (d0e, c0ls) => begin
        $Fix.ITEMatm (d1exp_trywith (loc0, d0exp_tr d0e, c0laulst_tr c0ls))
      end
    | D0Etup (tupknd, d0es) => let
        val d1es = d0explst_tr d0es
      in
        $Fix.ITEMatm (d1exp_tup (loc0, tupknd, d1es))
      end
    | D0Etup2 (tupknd, d0es1, d0es2) => let
        val d1es1 = d0explst_tr d0es1
        val d1es2 = d0explst_tr d0es2
      in
        $Fix.ITEMatm (d1exp_tup2 (loc0, tupknd, d1es1, d1es2))
      end
    | D0Eviewat () => let
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc) in
            $Fix.ITEMatm (d1exp_viewat (loc0, d1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.viewat_prec_dyn, f))
      end
    | D0Ewhere (d0e, d0cs) => let
        val (pf | ()) = trans1_level_inc ()
        val () = trans1_env_push ()
        // declarations are translated first!
        val d1cs = d0eclst_tr d0cs
        val d1e = d0exp_tr d0e
        val () = trans1_env_pop ()
        val () = trans1_level_dec (pf | (*none*))
      in
        $Fix.ITEMatm (d1exp_where (loc0, d1e, d1cs))
      end
    | D0Ewhile (oinv, loc_inv, d0e_test, d0e_body) => let
        val inv = (
          case+ oinv of
          | Some inv => loopi0nv_tr (loc_inv, inv)
          | None () => loopi1nv_nil (loc_inv)
        ) : loopi1nv
        val d1e_test = d0exp_tr d0e_test
        val d1e_body = d0exp_tr d0e_body
      in
        $Fix.ITEMatm (d1exp_while (loc0, inv, d1e_test, d1e_body))
      end
(*
    | _ => begin
        prerr d0e0.d0exp_loc;
        prerr ": error(1)";
        prerr ": d0exp_tr: not available yet.\n";
        $Err.abort {d1expitm} ()
      end
*)
  end

and aux_itemlst (d0e0: d0exp): d1expitmlst =
  let
    fun aux (res: List d1expitm, d0e0: d0exp): d1expitmlst =
      case+ d0e0.d0exp_node of
      | D0Eapp (d0e1, d0e2) => let
          val res = aux_item d0e2 :: res
        in
          aux (res, d0e1)
        end
      | _ => aux_item d0e0 :: res
  in
    aux (nil (), d0e0)
  end

in
  case+ aux_item d0e0 of
    | $Fix.ITEMatm d1e => d1e
    | $Fix.ITEMopr _ => d0exp_tr_errmsg_opr d0e0.d0exp_loc
end

implement d0explst_tr d0es = case+ d0es of
  | d0e :: d0es => d0exp_tr d0e :: d0explst_tr d0es
  | nil () => nil ()

implement d0explstlst_tr d0ess = case+ d0ess of
  | d0es :: d0ess => d0explst_tr d0es :: d0explstlst_tr d0ess
  | nil () => nil ()

implement labd0explst_tr ld0es = case+ ld0es of
  | LABD0EXPLSTcons (l, d0e, ld0es) =>
    LABD1EXPLSTcons (l, d0exp_tr d0e, labd0explst_tr ld0es)
  | LABD0EXPLSTnil () => LABD1EXPLSTnil ()

implement d0expopt_tr (od0e) = case+ od0e of
  | Some d0e => Some (d0exp_tr d0e) | None () => None ()

(* ****** ****** *)

// translation of declarations

fn v0ardec_tr (d: v0ardec): v1ardec =
  let
    val os1e = s0expopt_tr d.v0ardec_typ
    val od1e = d0expopt_tr d.v0ardec_ini
  in
    v1ardec_make (
      d.v0ardec_loc, d.v0ardec_sym, d.v0ardec_sym_loc, os1e, od1e
    )
  end

fun v0ardeclst_tr (ds: v0ardeclst): v1ardeclst =
  case+ ds of
  | cons (d, ds) => cons (v0ardec_tr d, v0ardeclst_tr ds)
  | nil () => nil ()

(* ****** ****** *)

fn v0aldec_tr (d: v0aldec): v1aldec =
  let
    val p1t = p0at_tr d.v0aldec_pat
    val d1e = d0exp_tr d.v0aldec_def
(*
    val () = begin
      print "v0aldec_tr: d1e = "; print d1e; print_newline ()
    end
*)
    val ann = witht0ype_tr d.v0aldec_ann
  in
    v1aldec_make (d.v0aldec_loc, p1t, d1e, ann)
  end

fun v0aldeclst_tr (ds: v0aldeclst): v1aldeclst =
  case+ ds of
  | cons (d, ds) => cons (v0aldec_tr d, v0aldeclst_tr ds)
  | nil () => nil ()

(* ****** ****** *)

fn f0undec_tr
  (is_prf: bool, is_rec: bool, d: f0undec): f1undec = let

val loc = d.f0undec_loc
val otags = d.f0undec_eff
val (ofc, oefc) = (
  case+ otags of
  | Some tags => let
      val fc0 = $Syn.FUNCLOfun () // default is [function]
      val (fc, lin, prf, efc) = $Eff.e0fftaglst_tr (fc0, tags)
    in
      (Some fc, Some efc)
    end
  | None () => let
      val efc: efc =
        if is_prf then $Eff.EFFCSTnil () else $Eff.EFFCSTall ()
    in
      (None(*ofc*), Some efc)
    end
) : @(Option funclo, efcopt)

val d1e_def =
  d0exp_lams_dyn_tr (
    None () (*oloc*), ofc, 0 (*lin*), d.f0undec_arg, d.f0undec_res, oefc, d.f0undec_def
  ) // end of [d0exp_lams_dyn_tr]

val () = begin
  if is_rec then termination_metric_check (loc, d1exp_is_metric d1e_def, oefc)
end

val ann = witht0ype_tr d.f0undec_ann

in
  f1undec_make (loc, d.f0undec_sym, d.f0undec_sym_loc, d1e_def, ann)
end // end of [f0undec_tr]

fun f0undeclst_tr (fk: funkind, ds: f0undeclst): f1undeclst =
  let
    val is_prf = funkind_is_proof fk
    and is_rec = funkind_is_recursive fk
  in
    case+ ds of
    | d :: ds => begin
        f0undec_tr (is_prf, is_rec, d) :: f0undeclst_tr (fk, ds)
      end
    | nil () => nil ()
  end

(* ****** ****** *)

fn m0acdef_tr (d: m0acdef): m1acdef =
  let val def = d0exp_tr d.m0acdef_def in
    m1acdef_make (d.m0acdef_loc, d.m0acdef_sym, d.m0acdef_arg, def)
  end

fun m0acdeflst_tr (ds: m0acdeflst): m1acdeflst =
  case+ ds of
  | cons (d, ds) => cons (m0acdef_tr d, m0acdeflst_tr ds)
  | nil () => nil ()

(* ****** ****** *)

fn i0mpdec_tr (d: i0mpdec): i1mpdec = let
  val qid = d.i0mpdec_qid
  val decarg = s0arglstlst_tr qid.impqi0de_arg
  val def = d0exp_lams_dyn_tr (
    None () (*oloc*), None () (*ofc*), 0 (*lin*),
    d.i0mpdec_arg, d.i0mpdec_res, None () (*oefc*),
    d.i0mpdec_def
  ) // end of [val]
in
  i1mpdec_make (d.i0mpdec_loc, qid, decarg, def)
end // end of [i0mpdec_tr]

(* ****** ****** *)

fn guad0ec_tr (knd: srpifkind, gd: guad0ec): d1eclst = let
  fun loop (knd: srpifkind, gdn: guad0ec_node): d1eclst =
    case+ gdn of
    | GD0Cone (e0xp, d0cs) => let
        val v1al = e1xp_eval_if (knd, e0xp_tr e0xp)
      in
        if v1al_is_true v1al then d0eclst_tr d0cs else nil ()
      end
    | GD0Ctwo (e0xp, d0cs_then, d0cs_else) => let
        val v1al = e1xp_eval_if (knd, e0xp_tr e0xp)
      in
        if v1al_is_true v1al then d0eclst_tr d0cs_then
        else d0eclst_tr d0cs_else
      end
    | GD0Ccons (e0xp, d0cs_then, knd_elif, gdn_else) => let
        val v1al = e1xp_eval_if (knd, e0xp_tr e0xp)
      in
        if v1al_is_true v1al then d0eclst_tr d0cs_then
        else loop (knd_elif, gdn_else)
      end
in
  loop (knd, gd.guad0ec_node)
end // end of [guad0ec_tr]

(* ****** ****** *)

fn i0nclude_tr
  (loc: loc_t, stadyn: int, filename: fil_t): d1ec = let
  val () = $Fil.the_filenamelst_push filename
  val fullname = $Fil.filename_full filename
(*
  val () = begin
    print "Including ["; print fullname; print "] starts.";
    print_newline ()
  end
*)
  val d0cs = $Par.parse_from_filename (stadyn, filename)
(*
  val () = begin
    print "Including ["; print fullname; print "] finishes.";
    print_newline ()
  end
*)
  val () = $Fil.the_filenamelst_pop ()

  val d1cs = d0eclst_tr d0cs

in
  d1ec_list (loc, d1cs)
end

(* ****** ****** *)

extern fun string_is_dats (s: string): bool
  = "ats_trans1_string_is_dats"

extern fun string_suffix_is_dats (s: string): bool
  = "ats_trans1_string_suffix_is_dats"

%{^

static inline
ats_bool_type
ats_trans1_string_is_dats (ats_ptr_type s0) {
  char *s = s0 ;
  s = ++s ; if (*s != 'd') return ats_false_bool ;
  s = ++s ; if (*s != 'a') return ats_false_bool ;
  s = ++s ; if (*s != 't') return ats_false_bool ;
  s = ++s ; if (*s != 's') return ats_false_bool ;
  s = ++s ; if (*s != '\0') return ats_false_bool ;
  return ats_true_bool ;
}

static inline
ats_bool_type
ats_trans1_string_suffix_is_dats (ats_ptr_type s0) {
  char *s = strrchr (s0, '.') ;
  if (s) return ats_trans1_string_is_dats (s) ;
  return ats_false_bool ;
}

%}

fn s0taload_tr
  (loc: loc_t, idopt: Option sym_t, fil: fil_t): d1ec = let
  val fullname = $Fil.filename_full fil
  val d1cs = (
    case+ staload_file_search fullname of
    | ~None_vt () => let
        val () = $Fil.the_filenamelst_push fil
        val flag = (
          if string_suffix_is_dats fullname then 1(*dyn*) else 0(*sta*)
        ) : int
        val d0cs = $Par.parse_from_filename (flag, fil)
        val () = $Fil.the_filenamelst_pop ()
(*
        val () = begin
          printf ("Translating [%s] begins.", @(fullname));
          print_newline ()
        end
*)
        val () = trans1_env_save ()
        val d1cs = d0eclst_tr d0cs
        val () = trans1_env_restore ()
(*
        val () = begin
          printf ("Translating [%s] ends.", @(fullname));
          print_newline ()
        end
*)
        val () = staload_file_insert (fullname, d1cs)
      in
        d1cs
      end
    | ~Some_vt (d1cs) => let
(*
        val () = begin
          printf ("The file [%s] is already loaded.", @(fullname));
          print_newline ()
        end
*)
      in
        d1cs
      end
  ) : d1eclst
in
  d1ec_staload (loc, idopt, fil, 0(*loaded*), d1cs)
end

(* ****** ****** *)

implement d0ec_tr d0c0 = begin
  case+ d0c0.d0ec_node of
  | D0Cfixity (f0xty, ids) => begin
      d0ec_fixity_tr (f0xty, ids); d1ec_none (d0c0.d0ec_loc)
    end
  | D0Cnonfix ids => begin
      d0ec_nonfix_tr ids; d1ec_none (d0c0.d0ec_loc)
    end
  | D0Csymintr ids => d1ec_symintr (d0c0.d0ec_loc, ids)
  | D0Ce0xpdef (id, def) => let
      val def: e1xp = case+ def of
        | Some e0xp => e0xp_tr e0xp | None () => e1xp_none ()
    in
      the_e1xpenv_add (id, def); d1ec_e1xpdef (d0c0.d0ec_loc, id, def)
    end
  | D0Ce0xpact (actkind, e0xp) => let
      val e1xp = e0xp_tr e0xp
(*
      val () = begin
        print "d0ec_tr: D0Ce0xpact: e1xp = ";
        print e1xp;
        print_newline ()
      end
*)
      val v1al = e1xp_eval e1xp
      val () = case+ actkind of
        | E0XPACTassert () =>
            do_e0xpact_assert (e0xp.e0xp_loc, v1al)
        | E0XPACTerror () =>
            do_e0xpact_error (e0xp.e0xp_loc, v1al)
        | E0XPACTprint () => do_e0xpact_print v1al
    in
      d1ec_none (d0c0.d0ec_loc)
    end
  | D0Cdatsrts (d0c, d0cs) => let
      val d1c = d0atsrtdec_tr d0c and d1cs = d0atsrtdeclst_tr d0cs
    in
      d1ec_datsrts (d0c0.d0ec_loc, d1c :: d1cs)
    end
  | D0Csrtdefs (d0c, d0cs) => let
      val d1c = s0rtdef_tr d0c and d1cs = s0rtdeflst_tr d0cs
    in
      d1ec_srtdefs (d0c0.d0ec_loc, d1c :: d1cs)
    end
  | D0Cstacons (impsrt, d0c, d0cs) => let
      val d1c = s0tacon_tr d0c and d1cs = s0taconlst_tr d0cs
    in
      d1ec_stacons (d0c0.d0ec_loc, impsrt, d1c :: d1cs)
    end
  | D0Cstacsts (d0c, d0cs) => let
      val d1c = s0tacst_tr d0c and d1cs = s0tacstlst_tr d0cs
    in
      d1ec_stacsts (d0c0.d0ec_loc, d1c :: d1cs)
    end
  | D0Cstavars (d0c, d0cs) => let
      val d1c = s0tavar_tr d0c and d1cs = s0tavarlst_tr d0cs
    in
      d1ec_stavars (d0c0.d0ec_loc, d1c :: d1cs)
    end
  | D0Csexpdefs (os0t, d0c, d0cs) => let
      val os1t = s0rtopt_tr os0t
      val d1c = s0expdef_tr d0c and d1cs = s0expdeflst_tr d0cs
    in
      d1ec_sexpdefs (d0c0.d0ec_loc, os1t, d1c :: d1cs)
    end
  | D0Csaspdec (d0c) => begin
      d1ec_saspdec (d0c0.d0ec_loc, s0aspdec_tr d0c)
    end
  | D0Cdatdecs (dk, d0c1, d0cs1, d0cs2) => let
      val d1c1 = d0atdec_tr d0c1 and d1cs1 = d0atdeclst_tr d0cs1
      val d1cs2 = s0expdeflst_tr d0cs2
    in
      d1ec_datdecs (d0c0.d0ec_loc, dk, d1c1 :: d1cs1, d1cs2)
    end
  | D0Cexndecs (d0c, d0cs) => let
      val d1c = e0xndec_tr d0c and d1cs = e0xndeclst_tr d0cs
    in
      d1ec_exndecs (d0c0.d0ec_loc, d1c :: d1cs)
    end
  | D0Cdcstdecs (dck, s0qss, d0c, d0cs) => let
      val isfun = dcstkind_is_fun dck
      and isprf = dcstkind_is_proof dck
      val s1qss = s0qualstlst_tr s0qss
      val d1c = d0cstdec_tr (isfun, isprf, d0c)
      and d1cs = d0cstdeclst_tr (isfun, isprf, d0cs)
    in
      d1ec_dcstdecs (d0c0.d0ec_loc, dck, s1qss, d1c :: d1cs)
    end
  | D0Coverload (id, qid) => begin
      d1ec_overload (d0c0.d0ec_loc, id, qid)
    end
  | D0Cextype (name, s0e_def) => begin
      d1ec_extype (d0c0.d0ec_loc, name, s0exp_tr s0e_def)
    end
  | D0Cextval (name, d0e_def) => begin
      d1ec_extval (d0c0.d0ec_loc, name, d0exp_tr d0e_def)
    end
  | D0Cextcode (position, code) => begin
      d1ec_extcode (d0c0.d0ec_loc, position, code)
    end
  | D0Cvaldecs (valknd, d0c, d0cs) => let
      val d1c = v0aldec_tr d0c and d1cs = v0aldeclst_tr d0cs
    in
      d1ec_valdecs (d0c0.d0ec_loc, valknd, d1c :: d1cs)
    end
  | D0Cvaldecs_par (d0c, d0cs) => let
      val d1c = v0aldec_tr d0c and d1cs = v0aldeclst_tr d0cs
    in
      d1ec_valdecs_par (d0c0.d0ec_loc, d1c :: d1cs)
    end
  | D0Cvaldecs_rec (d0c, d0cs) => let
      val d1c = v0aldec_tr d0c and d1cs = v0aldeclst_tr d0cs
    in
      d1ec_valdecs_rec (d0c0.d0ec_loc, d1c :: d1cs)
    end
  | D0Cfundecs (funkind, s0qss, d0c, d0cs) => let
      val s1qss = s0qualstlst_tr s0qss
      val d1cs = f0undeclst_tr (funkind, d0c :: d0cs)
    in
      d1ec_fundecs (d0c0.d0ec_loc, funkind, s1qss, d1cs)
    end
  | D0Cvardecs (d0c, d0cs) => let
      val d1c = v0ardec_tr d0c and d1cs = v0ardeclst_tr d0cs
    in
      d1ec_vardecs (d0c0.d0ec_loc, d1c :: d1cs)
    end
  | D0Cmacdefs (knd, d0c, d0cs) => let
      // knd: 0/1/2 => short/long/long rec
      val d1c = m0acdef_tr d0c and d1cs = m0acdeflst_tr d0cs
    in
      d1ec_macdefs (d0c0.d0ec_loc, knd, d1c :: d1cs)
    end
  | D0Cimpdec (d0c) => begin
      d1ec_impdec (d0c0.d0ec_loc, i0mpdec_tr d0c)
    end
  | D0Cdynload (name) => let
      val filename: fil_t = case+ $Fil.filenameopt_make name of
        | ~Some_vt filename => filename
        | ~None_vt () => begin
            prerr d0c0.d0ec_loc;
            prerr ": error(1)";
            prerr ": the file [";
            prerr name;
            prerr "] is not available for dynamic loading.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end
    in
      d1ec_dynload (d0c0.d0ec_loc, filename)
    end
  | D0Cstaload (idopt, name) => let
      val filename: fil_t = case+ $Fil.filenameopt_make name of
        | ~Some_vt filename => filename
        | ~None_vt () => begin
            prerr d0c0.d0ec_loc;
            prerr ": error(1)";
            prerr ": the file [";
            prerr name;
            prerr "] is not available for static loading.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end
    in
      s0taload_tr (d0c0.d0ec_loc, idopt, filename)
    end
  | D0Clocal (d0cs_head, d0cs_body) => let
      val (pf | ()) = trans1_level_inc ()
      val () = trans1_env_push ()
      val d1cs_head = d0eclst_tr d0cs_head
      val () = trans1_level_dec (pf | (*none*))
      val () = trans1_env_push ()
      val d1cs_body = d0eclst_tr d0cs_body
      val () = trans1_env_localjoin ()
    in
      d1ec_local (d0c0.d0ec_loc, d1cs_head, d1cs_body)
    end
  | D0Cguadec (knd, gd0c) => begin
      d1ec_list (d0c0.d0ec_loc, guad0ec_tr (knd, gd0c))
    end
  | D0Cinclude (stadyn, name) => let
      val filename: fil_t = case+ $Fil.filenameopt_make name of
        | ~Some_vt filename => filename
        | ~None_vt () => begin
            prerr d0c0.d0ec_loc;
            prerr ": error(1)";
            prerr ": the file [";
            prerr name;
            prerr "] is not available for inclusion.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end
    in
      i0nclude_tr (d0c0.d0ec_loc, stadyn, filename)
    end
(*
  | _ => begin
      prerr d0c0.d0ec_loc;
      prerr ": error(1)";
      prerr ": d0ec_tr: not available yet.\n";
      $Err.abort {d1ec} ()
    end
*)
end // end of [d0ec_tr]

// [$Lst.list_map_fun] is tail-recursive!
implement d0eclst_tr (d0cs) = $Lst.list_map_fun (d0cs, d0ec_tr)

(* ****** ****** *)

implement initialize () = begin
  $Glo.ats_dynloadflag_set (1) // [1] is the default value
end // end of [initialize]

implement finalize () = let
  fun aux_function_name_prefix (): void = begin
    case+ the_e1xpenv_find ($Sym.symbol_ATS_FUNCTION_NAME_PREFIX) of
    | ~Some_vt e1xp => let
        val v1al = e1xp_eval (e1xp)
      in
        case+ v1al of
        | V1ALstring s => let
            val s = string1_of_string0 s
          in
            $Glo.ats_function_name_prefix_set (stropt_some s)
          end
        | _ => begin
            prerr e1xp.e1xp_loc; prerr ": error(1)";
            prerr ": a string definition is required for ATS_FUNCTION_NAME_PREFIX.";
            prerr_newline ();
            $Err.abort {void} ()
          end
      end // end of [Some_vt]
    | ~None_vt () => () // use the default value
  end // end of [aux_function_name_prefix]
  val () = aux_function_name_prefix ()

  fun aux_dynloadflag (): void = begin
    case+ the_e1xpenv_find ($Sym.symbol_ATS_DYNLOADFLAG) of
    | ~Some_vt e1xp => let
        val v1al = e1xp_eval (e1xp)
        val flag = if v1al_is_true v1al then 1 else 0
      in
        $Glo.ats_dynloadflag_set (flag)
      end
    | ~None_vt () => () // use the default value
  end // end of [aux_dynloadflag]
  fun aux_dynloadfuname (): void = begin
    case+ the_e1xpenv_find ($Sym.symbol_ATS_DYNLOADFUNAME) of
    | ~Some_vt e1xp => let
        val v1al = e1xp_eval (e1xp)
      in
        case+ v1al of
        | V1ALstring s => let
            val s = string1_of_string0 s
          in
            $Glo.ats_dynloadfuname_set (stropt_some s)
          end
        | _ => begin
            prerr e1xp.e1xp_loc; prerr ": error(1)";
            prerr ": a string definition is required for ATS_DYNLOADFUNAME.";
            prerr_newline ();
            $Err.abort {void} ()
          end
      end // end of [Some_vt]
    | ~None_vt () => () // use the default value
  end // end of [aux_dynloadfuname]
  val () = aux_dynloadflag (); val () = aux_dynloadfuname ()
in
  // empty
end // end of [finalize]

(* ****** ****** *)

(* end of [ats_trans1.dats] *)
