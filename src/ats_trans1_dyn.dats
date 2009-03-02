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

overload prerr with $Sym.prerr_symbol

(* ****** ****** *)

#define CLOPTR 1; #define CLOREF ~1
macdef FUNCLOcloptr = $Syn.FUNCLOclo CLOPTR
macdef FUNCLOcloref = $Syn.FUNCLOclo CLOREF

(* ****** ****** *)

fn prerr_loc_error1 (loc: loc_t): void =
  ($Loc.prerr_location loc; prerr ": error(1)")
// end of [prerr_loc_error1]

(* ****** ****** *)

typedef efc = $Eff.effcst
typedef efcopt = Option efc

// translation of dynamic constants

local // defining [d0cstdec_tr]

fun aux1 (xs: p0arglst): s1explst = begin case+ xs of
  | cons (x, xs) => begin case+ x.p0arg_ann of
    | Some s0e => begin
        let val s1e = s0exp_tr s0e in s1e :: aux1 xs end
      end // end of [Some]
    | None () => begin
        prerr_loc_error1 (x.p0arg_loc);
        prerr ": unascribed variable: ["; prerr x.p0arg_sym; prerr "]";
        prerr_newline ();
        $Err.abort ()
      end // end of [None]
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
      end // end of [D0ARGdyn]
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
      end // end of [D0ARGdyn2]
    | D0ARGsta s0qs => let
        val loc_x = x.d0arg_loc
        val s1qs = s0qualst_tr s0qs
        val s1e_res = aux2 (fc, lin, prf, oefc, fst, lst, xs, s1e_res)
        val loc_res = s1e_res.s1exp_loc
        val loc = $Loc.location_combine (loc_x, loc_res)
        val () = if lst = 0 then begin
          prerr_loc_error1 (loc_res);
          prerr ": illegal use of effect annotation";
          prerr_newline ();
          $Err.abort {void} ()
        end // end of [val]
      in
        s1exp_uni (loc, s1qs, s1e_res)
      end (* end of [D0ARGsta] *)
    end (* end of [::] *)
  | list_nil () => s1e_res
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
  // end of [val]
  val () = case+ fc of
    | $Syn.FUNCLOclo knd => begin
        if knd <> CLOREF then () where {
          val () = if knd = 0 then begin
            $Loc.prerr_location loc0;
            prerr ": INTERNAL ERROR: a closure at the toplevel"
          end // end of [val]
          val () = if knd = 1 then begin
            prerr_loc_error1 (loc0);
            prerr ": a closure pointer is not allowed at the toplevel"
          end // end of [val]
          val () = prerr_newline ()
          val () = $Err.abort {void} ()
        } // end of [if]
      end // end of [FUNCLOclo]
    | $Syn.FUNCLOfun () => ()
  // end of [val]
  var lst: int = 0
in
  aux2 (fc, lin, prf, oefc, 0, lst, xs, s1e_res)
end // end of [aux2]

in // in of [local]

fn d0cstdec_tr (isfun: bool, isprf: bool, d: d0cstdec): d1cstdec = let
  val loc0 = d.d0cstdec_loc
  val s1e_res = s0exp_tr d.d0cstdec_res
  val s1e = aux3 (loc0, isfun, isprf, d.d0cstdec_arg, d.d0cstdec_eff, s1e_res)
in
  d1cstdec_make (loc0, d.d0cstdec_fil, d.d0cstdec_sym, s1e, d.d0cstdec_ext)
end // end of [d0cstdec_tr]

fun d0cstdeclst_tr
  (isfun: bool, isprf: bool, ds: d0cstdeclst): d1cstdeclst = case+ ds of
  | cons (d, ds) => begin
      cons (d0cstdec_tr (isfun, isprf, d), d0cstdeclst_tr (isfun, isprf, ds))
    end // end of [cons]
  | nil () => nil ()
// end of [d0cstdeclst_tr]

end // end of [local]

(* ****** ****** *)

// translation of dynamic patterns

typedef p1atitm = $Fix.item p1at
typedef p1atitmlst = List p1atitm

val p1atitm_app : p1atitm = let

fn f (p1t1: p1at, p1t2: p1at):<cloref1> p1atitm = let
  val loc = $Loc.location_combine (p1t1.p1at_loc, p1t2.p1at_loc)
  val p1t_app = case+ p1t2.p1at_node of
    | P1Tlist (npf, p1ts) => begin
        p1at_app_dyn (loc, p1t1, p1t2.p1at_loc, npf, p1ts)
      end // end of [P1Tlist]
    | P1Tsvararg s1a => begin case+ p1t1.p1at_node of
        | P1Tapp_sta (p1t1, s1as) => begin
            p1at_app_sta (loc, p1t1, $Lst.list_extend (s1as, s1a))
          end // end of [P1Tapp_sta]
        | _ => begin
            p1at_app_sta (loc, p1t1, cons (s1a, nil ()))
          end // end of [_]
      end // end of [P1Tsvararg]
    | _ => begin
        p1at_app_dyn (loc, p1t1, p1t2.p1at_loc, 0, cons (p1t2, nil ()))
      end // end of [_]
(*
    val () = begin
      print "p1atitm_app: f: p1t_app = "; print p1t_app; print_newline ()
    end
*)
  in
    $Fix.ITEMatm p1t_app
  end // end of [f]

in
  $Fix.item_app f
end // end of [app_p1at_item]

fun p1at_make_opr (p1t: p1at, f: $Fix.fxty_t): p1atitm = begin
  $Fix.oper_make {p1at} (
    lam x => x.p1at_loc
  , lam (loc, x, loc_arg, xs) => p1at_app_dyn (loc, x, loc_arg, 0, xs)
  , p1t
  , f
  ) // end of [oper_make]
end // end of [p1at_make_opr]

val p1atitm_backslash : p1atitm = begin
  $Fix.oper_make_backslash {p1at} (
    lam x => x.p1at_loc,
    lam (loc, x, loc_arg, xs) => p1at_app_dyn (loc, x, loc_arg, 0, xs)
  ) // end of [oper_make_backslash]
end // end of [p1atitm_backslash]

(* ****** ****** *)

fn s0vararg_tr (s0a: s0vararg): s1vararg =
  case+ s0a of
  | S0VARARGseq (s0as) => S1VARARGseq (s0arglst_tr s0as)
  | S0VARARGone () => S1VARARGone ()
  | S0VARARGall () => S1VARARGall ()

(* ****** ****** *)

fn p0at_tr_errmsg_opr (loc: loc_t): p1at = begin
  prerr_loc_error1 loc;
  prerr ": the operator needs to be applied";
  prerr_newline ();
  $Err.abort {p1at} ()
end // end of [p0at_tr_errmsg_opr]

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
        prerr_loc_error1 p0t0.p0at_loc;
        prerr ": p0at_tr: not available yet"; prerr_newline ();
        $Err.abort {p1atitm} ()
      end // end of [_]
*)
end // end of [aux_item]

and aux_itemlst (p0t0: p0at): p1atitmlst = let
  fun aux (res: p1atitmlst, p0t0: p0at): p1atitmlst =
    case+ p0t0.p0at_node of
    | P0Tapp (p0t1, p0t2) => let
        val res = aux_item p0t2 :: res in aux (res, p0t1)
      end // end of [P0Tapp]
    | _ => aux_item p0t0 :: res
in
  aux (nil (), p0t0)
end // end of [aux_itemlst]

in
  case+ aux_item p0t0 of
    | $Fix.ITEMatm p1t => p1t
    | $Fix.ITEMopr _ => p0at_tr_errmsg_opr p0t0.p0at_loc
end // end of [p0at_tr]

implement p0atlst_tr p0ts = $Lst.list_map_fun (p0ts, p0at_tr)

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
        end // end of [D1Eapp_sta]
      | _ => begin
          d1exp_app_sta (loc, d1e1, cons (s1a, nil ()))
        end // end of [_]
      end // end of [D1Esexparg]
    | _ => d1exp_app_dyn
        (loc, d1e1, d1e2.d1exp_loc, 0, cons (d1e2, nil ()))
      // end of [_]
  end // end of [val]
(*
  val () = begin
    print "d1expitm_app: f: d1e_app = "; print d1e_app; print_newline ()
  end // end of [val]
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
// end of [s0exparg_tr]

fn s0expdarg_tr (d0e: d0exp): s1exparg = let
  val d1e = d0exp_tr d0e in case+ d1e.d1exp_node of
    | D1Esexparg s1a => s1a | _ => begin
        $Loc.prerr_location d0e.d0exp_loc;
        prerr ": INTERNAL ERROR: d0exp_tr: D0Efoldat";
        prerr_newline ();
        $Err.abort {s1exparg} ()
      end // end of [_]
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

fn d0exp_lams_dyn_tr (
    knd: lamkind
  , oloc: Option loc_t, ofc: Option funclo
  , lin: int
  , args: f0arglst
  , res: s0expopt
  , oefc: efcopt
  , d0e_body: d0exp
  ) : d1exp = let

fun aux (
    knd: lamkind
  , args: f0arglst
  , d1e_body: d1exp
  , flag: int
  ) :<cloptr1> d1exp = begin case+ args of
  | arg :: args => let
      val loc_arg = arg.f0arg_loc
      val d1e_body = aux (knd, args, d1e_body, flag1) where {
        val flag1 = (
          case+ arg.f0arg_node of F0ARGdyn _ => flag + 1 | _ => flag
        ) : int
      } // end of [where]
      val loc_body = d1e_body.d1exp_loc
      val loc = case+ oloc of
        | Some loc => loc | None () => begin
            $Loc.location_combine (loc_arg, loc_body)
          end // end of [None]
      // end of [val]
    in
      case+ arg.f0arg_node of
      | F0ARGsta1 s0qs => begin
          d1exp_lam_sta_syn (loc, loc_arg, s0qualst_tr s0qs, d1e_body)
        end // end of [F0ARGsta1]
      | F0ARGsta2 s0as => begin
          d1exp_lam_sta_ana (loc, loc_arg, s0arglst_tr s0as, d1e_body)
        end // end of [F0ARGsta2]
      | F0ARGdyn p0t when flag = 0 => let
          val p1t = p0at_tr p0t
          val isat = (case+ knd of
            | LAMKINDlam _ => 0 | LAMKINDatlam _ => 1
            | LAMKINDllam _ => 0 | LAMKINDatllam _ => 1
            | LAMKINDfix () => 0
          ) : int
        in
          if isat = 0 then
            d1exp_lam_dyn (loc, lin, p1t, d1e_body)
          else
            d1exp_laminit_dyn (loc, lin, p1t, d1e_body)
          // end of [if]
        end // end of [F0ARGdyn when ...]
      | F0ARGdyn p0t (* flag > 0 *) => let
          val p1t = p0at_tr p0t
          val d1e_body = // linear closure
            d1exp_ann_funclo_opt (loc_body, d1e_body, FUNCLOcloptr)
          // end of [val]
        in
          d1exp_lam_dyn (loc, lin, p1t, d1e_body)
        end // end of [F0ARGdyn]
      | F0ARGmet s0es => begin
          d1exp_lam_met (loc, loc_arg, s0explst_tr s0es, d1e_body)
        end // end of [F0ARGmet]
    end // end of [::]
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
    end // end of [Some]
  | None () => d1e_body
) : d1exp

val d1e_body = (
  case+ oefc of
  | Some efc => begin
      d1exp_ann_effc (d1e_body.d1exp_loc, d1e_body, efc)
    end // end of [Some]
  | None () => d1e_body
) : d1exp

val d1e_body = (
  case+ ofc of
  | Some fc => begin
      d1exp_ann_funclo (d1e_body.d1exp_loc, d1e_body, fc)
    end // end of [Some]
  | None () => d1e_body
) : d1exp

in
  aux (knd, args, d1e_body, 0(*flag*))
end // end of [d0exp_lams_dyn_tr]

(* ****** ****** *)

fn termination_metric_check
  (loc: loc_t, is_met: bool, oefc: efcopt): void =
  case+ oefc of
  | Some efc => let
      val is_okay = begin
        if is_met then true else $Eff.effcst_contain_ntm efc
      end : bool
    in
      if (is_okay) then () else begin
        prerr_loc_error1 loc;
        prerr ": a termination metric is missing"; prerr_newline ();
        $Err.abort ()
      end // end of [if]
    end // end of [Some]
  | None () => ()
// end of [termination_metric_check]

(* ****** ****** *)

fn i0nvarg_tr (arg: i0nvarg): i1nvarg = let
  val os1e = s0expopt_tr arg.i0nvarg_typ
in
  i1nvarg_make (arg.i0nvarg_loc, arg.i0nvarg_sym, os1e)
end // end of [i0nvarg_tr]

fun i0nvarglst_tr (args: i0nvarglst): i1nvarglst =
  case+ args of
  | cons (arg, args) => cons (i0nvarg_tr arg, i0nvarglst_tr args)
  | nil () => nil ()
// end of [i0nvarglst_tr]

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
end // end of [m0atch_tr]

fn m0atchlst_tr (m0ats: m0atchlst): m1atchlst =
  $Lst.list_map_fun (m0ats, m0atch_tr)
// end of [m0atchlst_tr]

fn c0lau_tr (c0l: c0lau): c1lau = let
  val gp0t = c0l.c0lau_pat
  val gua = m0atchlst_tr (gp0t.guap0at_gua)
  val p1t = p0at_tr (gp0t.guap0at_pat)
  val body = d0exp_tr (c0l.c0lau_body)
in
  c1lau_make (c0l.c0lau_loc, p1t, gua, c0l.c0lau_seq, c0l.c0lau_neg, body)
end // end of [c0lau_tr]

fn c0laulst_tr (c0ls: c0laulst): c1laulst =
  $Lst.list_map_fun (c0ls, c0lau_tr)
// end of [c0laulst_tr]

fn sc0lau_tr (sc0l: sc0lau): sc1lau = let
  val sp1t = sp0at_tr (sc0l.sc0lau_pat)
  val body = d0exp_tr (sc0l.sc0lau_body)
in
  sc1lau_make (sc0l.sc0lau_loc, sp1t, body)
end // end of [sc0lau_tr]

fn sc0laulst_tr (sc0ls: sc0laulst): sc1laulst =
  $Lst.list_map_fun (sc0ls, sc0lau_tr)
// end of [sc0laulst_tr]

(* ****** ****** *)

fn d0exp_tr_errmsg_opr (loc: loc_t): d1exp = begin
  prerr_loc_error1 loc;
  prerr ": the operator needs to be applied";
  prerr_newline ();
  $Err.abort {d1exp} ()
end // end of [d0exp_tr_errmsg_opr]

implement d0exp_tr d0e0 = let

fun aux_item (d0e0: d0exp): d1expitm = let
  val loc0 = d0e0.d0exp_loc in case+ d0e0.d0exp_node of
    | D0Eann (d0e, s0e) => let
        val d1e = d0exp_tr d0e and s1e = s0exp_tr s0e
        val d1e_ann = d1exp_ann_type (loc0, d1e, s1e)
      in
        $Fix.ITEMatm d1e_ann
      end // end of [D0Eann]
    | D0Eapp _ => let 
        val d1e =
          $Fix.fixity_resolve (loc0, d1expitm_app, aux_itemlst d0e0)
      in
        $Fix.ITEMatm d1e
      end // end of [D0Eapp]
    | D0Earrinit (s0e_elt, od0e_asz, d0es_elt) => let
        val s1e_elt = s0exp_tr s0e_elt
        val od1e_asz = d0expopt_tr od0e_asz
        val d1es_elt = d0explst_tr d0es_elt
      in
        $Fix.ITEMatm (d1exp_arrinit (loc0, s1e_elt, od1e_asz, d1es_elt))
      end // end of [D0Earrinit]
    | D0Earrsize (os0e_elt, d0es_elt) => let
        val os1e_elt = s0expopt_tr os0e_elt
        val d1es_elt = d0explst_tr d0es_elt
        val d1e_arrsize = d1exp_arrsize (loc0, os1e_elt, d1es_elt)
      in
        $Fix.ITEMatm (d1e_arrsize)
      end // end of [D0Earrsize]
    | D0Earrsub (qid, loc_ind, d0ess) => let
        val d1e_arr =
          d1exp_qid (qid.arrqi0de_loc, qid.arrqi0de_qua, qid.arrqi0de_sym)
        val d1ess_ind = d0explstlst_tr d0ess
      in
        $Fix.ITEMatm (d1exp_arrsub (loc0, d1e_arr, loc_ind, d1ess_ind))
      end // end of [D0Earrsub]
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
      end // end of [D0Ecaseof]
    | D0Echar chr => begin
        $Fix.ITEMatm (d1exp_char (loc0, chr))
      end // end of [D0Echar]
    | D0Ecrypt (knd) => let
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc) in
            $Fix.ITEMatm (d1exp_crypt (loc0, knd, d1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.crypt_prec_dyn, f))
      end // end of [D0Ecrypt]
    | D0Edelay (lin) => let
        fn f (d1e: d1exp):<cloref1> d1expitm = let
          val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc)
        in
          $Fix.ITEMatm (d1exp_lazy_delay (loc0, lin, d1e))
        end // end of [f]
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.delay_prec_dyn, f))
      end // end of [D0Edelay]
    | D0Edynload () => let
        fn f (d1e: d1exp):<cloref1> d1expitm = case+ d1e.d1exp_node of
          | D1Estring (name, _) => let
              val fil = case+ $Fil.filenameopt_make name of
                | ~Some_vt fil => fil
                | ~None_vt () => begin
                    prerr_loc_error1 d1e.d1exp_loc;
                    prerr ": the file ["; prerr name;
                    prerr "] is not available for dynamic loading";
                    prerr_newline ();
                    $Err.abort {fil_t} ()
                  end
              val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc)
            in
              $Fix.ITEMatm (d1exp_dynload (loc0, fil))
            end
          | _ => begin
              prerr_loc_error1 d1e.d1exp_loc;
              prerr ": the dynamic expression must be a string constant";
              prerr_newline ();
              $Err.abort {d1expitm} ()
            end
          // end of [case]
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.dynload_prec_dyn, f))
      end // end of [D0Edynlaod]
    | D0Eeffmask (effs) => let
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc) in
            $Fix.ITEMatm (d1exp_effmask (loc0, effs, d1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.delay_prec_dyn, f))
      end // end of [D0Eeffmask]
    | D0Eempty () => $Fix.ITEMatm (d1exp_empty loc0)
    | D0Eexist (qualoc, s0a, d0e) => let
        val s1a = s0exparg_tr (qualoc, s0a) and d1e = d0exp_tr d0e
      in
        $Fix.ITEMatm (d1exp_exist (loc0, s1a, d1e))
      end // end of [D0Eexist]
    | D0Eextval (s0e_typ, code (*string*)) => let
        val s1e_typ = s0exp_tr s0e_typ
      in
        $Fix.ITEMatm (d1exp_extval (loc0, s1e_typ, code))
      end // end of [D0Eextval]
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
        val d1e_fun = d0exp_lams_dyn_tr
          (LAMKINDfix (), oloc0, ofc, lin, args, res, oefc, body)
        val () = termination_metric_check (loc0, false (*met*), oefc)
      in
        $Fix.ITEMatm (d1exp_fix (loc0, id, d1e_fun))
      end // end of [D0Efix]
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
      end // end of [D0Efoldat]
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
      end // end of [D0Efor]
    | D0Efreeat (d0es) => let
        val s1as = s0expdarglst_tr d0es
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc) in
            $Fix.ITEMatm (d1exp_freeat (loc0, s1as, d1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.freeat_prec_dyn, f))
      end // end of [D0Efreeat]
    | D0Eide id when id = $Sym.symbol_BACKSLASH => d1expitm_backslash
    | D0Eide id => let
        val d1e = d1exp_ide (loc0, id)
      in
        case+ the_fxtyenv_find id of
        | ~Some_vt f => d1exp_make_opr (d1e, f)
        | ~None_vt () => $Fix.ITEMatm d1e
      end // end of [D0Eide]
    | D0Eif (hd, d0e_cond, d0e_then, od0e_else) => let
        val inv = i0nvresstate_tr hd.ifhead_inv
        val d1e_cond = d0exp_tr d0e_cond
        val d1e_then = d0exp_tr d0e_then
        val od1e_else = d0expopt_tr od0e_else
        val d1e_if = d1exp_if (loc0, inv, d1e_cond, d1e_then, od1e_else)
      in
        $Fix.ITEMatm (d1e_if)        
      end // end of [D0Eif]
    | D0Eint (str (*int*)) => begin
        $Fix.ITEMatm (d1exp_int (loc0, str))
      end
    | D0Eintsp (str (*int*)) => begin
        $Fix.ITEMatm (d1exp_intsp (loc0, str))
      end
    | D0Elam (knd, args, res, otags, body) => let
        val oloc0 = Some loc0
        val lin0 = (case+ knd of
          | LAMKINDlam _ => 0 | LAMKINDatlam _ => 0
          | LAMKINDllam _ => 1 | LAMKINDatllam _ => 1
          | LAMKINDfix () => 0
        ) : int // end of [val]
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
        val d1e_lam = d0exp_lams_dyn_tr
          (knd, oloc0, ofc, lin, args, res, oefc, body)
      in
        $Fix.ITEMatm (d1e_lam)
      end // end of [D0Elam]
    | D0Elet (d0cs, d0e) => let
        val (pf | ()) = trans1_level_inc ()
        val () = trans1_env_push ()
        val d1cs = d0eclst_tr d0cs
        val d1e = d0exp_tr d0e
        val () = trans1_env_pop ()
        val () = trans1_level_dec (pf | (*none*))
      in
        $Fix.ITEMatm (d1exp_let (loc0, d1cs, d1e))
      end // end of [D0Elet]
    | D0Elist (d0es) => let
        val d1es = d0explst_tr d0es
      in
        $Fix.ITEMatm (d1exp_list (loc0, d1es))
      end // end of [D0Elist]
    | D0Elist2 (d0es1, d0es2) => let
        val s1es1 = d0explst_tr d0es1 and s1es2 = d0explst_tr d0es2
      in
        $Fix.ITEMatm (d1exp_list2 (loc0, s1es1, s1es2))
      end // end of [D0Elist2]
    | D0Eloopexn (i (*break/continue*)) => begin
        $Fix.ITEMatm (d1exp_loopexn (loc0, i))
      end
    | D0Elst (lin, os0e_elt, d0es_elt) => let
        val os1e_elt = s0expopt_tr os0e_elt
        val d1es_elt = d0explst_tr d0es_elt
        val d1e_lst = d1exp_lst (loc0, lin, os1e_elt, d1es_elt)
      in
        $Fix.ITEMatm (d1e_lst)
      end // end of [D0Elst]
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
      end // end of [D0Eptrof]
    | D0Eqid (q, id) => $Fix.ITEMatm (d1exp_qid (loc0, q, id))
    | D0Eraise (d0e) => begin
        $Fix.ITEMatm (d1exp_raise (loc0, d0exp_tr d0e))
      end
    | D0Erec (recknd, ld0es) => let
        val ld1es = labd0explst_tr ld0es
      in
        $Fix.ITEMatm (d1exp_rec (loc0, recknd, ld1es))
      end
    | D0Escaseof (hd, s0e, sc0ls) => let
        // hd.casehead_knd is always 0
        val inv = i0nvresstate_tr (hd.casehead_inv)
        val s1e = s0exp_tr s0e
        val sc1ls = sc0laulst_tr sc0ls
      in
        $Fix.ITEMatm (d1exp_scaseof (loc0, inv, s1e, sc1ls))
      end // end of [D0Escaseof]
    | D0Esel_lab (knd, lab) => let
        val d1l = d1lab_lab (loc0, lab)
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (d1e.d1exp_loc, loc0) in
            $Fix.ITEMatm (d1exp_sel (loc0, knd, d1e, d1l))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpos ($Fix.select_prec, f))
      end // end of [D0Esel_lab]
    | D0Esel_ind (knd, ind) => let
        val ind = d0explstlst_tr ind
        val d1l = d1lab_ind (loc0, ind)
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (d1e.d1exp_loc, loc0) in
            $Fix.ITEMatm (d1exp_sel (loc0, knd, d1e, d1l))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpos ($Fix.select_prec, f))
      end // end of [D0Esel_ind]
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
      end // end of [D0Esif]
    | D0Espawn () => let
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc) in
            $Fix.ITEMatm (d1exp_spawn (loc0, d1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.spawn_prec_dyn, f))
      end // end of [D0Espawn]
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
      end // end of [D0Etmpid]
    | D0Etop () => $Fix.ITEMatm (d1exp_top loc0)
    | D0Etrywith (hd, d0e, c0ls) => let
        val inv = i0nvresstate_tr (hd.tryhead_inv)
        val d1e = d0exp_tr d0e
        val c1ls = c0laulst_tr c0ls
      in
        $Fix.ITEMatm (d1exp_trywith (loc0, inv, d1e, c1ls))
      end // end of [D0Etrywith]
    | D0Etup (tupknd, d0es) => let
        val d1es = d0explst_tr d0es
      in
        $Fix.ITEMatm (d1exp_tup (loc0, tupknd, d1es))
      end // end of [D0Etup]
    | D0Etup2 (tupknd, d0es1, d0es2) => let
        val d1es1 = d0explst_tr d0es1
        val d1es2 = d0explst_tr d0es2
      in
        $Fix.ITEMatm (d1exp_tup2 (loc0, tupknd, d1es1, d1es2))
      end // end of [D0Etup2]
    | D0Eviewat () => let
        fn f (d1e: d1exp):<cloref1> d1expitm =
          let val loc0 = $Loc.location_combine (loc0, d1e.d1exp_loc) in
            $Fix.ITEMatm (d1exp_viewat (loc0, d1e))
          end
      in
        $Fix.ITEMopr ($Fix.OPERpre ($Fix.viewat_prec_dyn, f))
      end // end of [D0Eviewat]
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
      end // end of [D0Ewhere]
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
      end // end of [D0Ewhile]
(*
    | _ => begin
        prerr_loc_error1 d0e0.d0exp_loc;
        prerr ": d0exp_tr: not available yet"; prerr_newline ();
        $Err.abort {d1expitm} ()
      end // end of [_]
*)
end // end of [aux_item]

and aux_itemlst (d0e0: d0exp): d1expitmlst = let
  fun aux (res: List d1expitm, d0e0: d0exp): d1expitmlst =
    case+ d0e0.d0exp_node of
    | D0Eapp (d0e1, d0e2) => let
        val res = aux_item d0e2 :: res in aux (res, d0e1)
      end // end of [D0Eapp]
    | _ => aux_item d0e0 :: res
in
  aux (nil (), d0e0)
end // end of [aux_itemlst]

in
  case+ aux_item d0e0 of
  | $Fix.ITEMatm d1e => d1e
  | $Fix.ITEMopr _ => d0exp_tr_errmsg_opr d0e0.d0exp_loc
end // end of [d0exp_tr]

implement d0explst_tr d0es = 
  $Lst.list_map_fun (d0es, d0exp_tr)
// end of [d0explst_tr]

implement d0explstlst_tr d0ess =
  $Lst.list_map_fun (d0ess, d0explst_tr)
// end of [d0explstlst_tr]

implement labd0explst_tr ld0es = case+ ld0es of
  | LABD0EXPLSTcons (l, d0e, ld0es) =>
    LABD1EXPLSTcons (l, d0exp_tr d0e, labd0explst_tr ld0es)
  | LABD0EXPLSTnil () => LABD1EXPLSTnil ()
// end of [labd0explst_tr]

implement d0expopt_tr (od0e) = case+ od0e of
  | Some d0e => Some (d0exp_tr d0e) | None () => None ()
// end of [d0expopt_tr]

(* ****** ****** *)

// translation of declarations

fn v0ardec_tr
  (d: v0ardec): v1ardec = let
  val loc = d.v0ardec_loc
  val knd = d.v0ardec_knd
  val os1e = s0expopt_tr d.v0ardec_typ
  val wth = d.v0ardec_wth // i0deopt
  val od1e = d0expopt_tr d.v0ardec_ini
in
  v1ardec_make (
    loc, knd, d.v0ardec_sym, d.v0ardec_sym_loc, os1e, wth, od1e
  ) // end of [v1ardec_make]
end // end of [v0ardec_tr]

fn v0ardeclst_tr (ds: v0ardeclst): v1ardeclst =
  $Lst.list_map_fun (ds, v0ardec_tr)

(* ****** ****** *)

fn v0aldec_tr
  (d: v0aldec): v1aldec = let
  val p1t = p0at_tr d.v0aldec_pat
  val d1e = d0exp_tr d.v0aldec_def
(*
  val () = begin
    print "v0aldec_tr: d1e = "; print d1e; print_newline ()
  end // end of [val]
*)
  val ann = witht0ype_tr d.v0aldec_ann
in
  v1aldec_make (d.v0aldec_loc, p1t, d1e, ann)
end // end of [v0aldec_tr]

fn v0aldeclst_tr (ds: v0aldeclst): v1aldeclst =
  $Lst.list_map_fun (ds, v0aldec_tr)

(* ****** ****** *)

fn f0undec_tr
  (is_prf: bool, is_rec: bool, d: f0undec): f1undec = let
  val loc = d.f0undec_loc
  val knd = LAMKINDfix ()
  val otags = d.f0undec_eff
  val (ofc, oefc) = (case+ otags of
    | Some tags => let
        val fc0 = $Syn.FUNCLOfun () // default is [function]
        val (fc, lin, prf, efc) = $Eff.e0fftaglst_tr (fc0, tags)
      in
        (Some fc, Some efc)
      end // end of [Some]
    | None () => let
        val efc: efc =
          if is_prf then $Eff.EFFCSTnil () else $Eff.EFFCSTall ()
      in
        (None(*ofc*), Some efc)
      end // end of [None]
    ) : @(Option funclo, efcopt)

  val d1e_def = d0exp_lams_dyn_tr (
      knd, None () (*oloc*), ofc, 0 (*lin*)
    , d.f0undec_arg, d.f0undec_res, oefc, d.f0undec_def
    ) // end of [d0exp_lams_dyn_tr]

  val () = if is_rec then
    termination_metric_check (loc, d1exp_is_metric d1e_def, oefc)
  // end of [if]

  val ann = witht0ype_tr d.f0undec_ann
in
  f1undec_make (loc, d.f0undec_sym, d.f0undec_sym_loc, d1e_def, ann)
end // end of [f0undec_tr]

fun f0undeclst_tr
  (fk: funkind, ds: f0undeclst): f1undeclst = let
  val is_prf = funkind_is_proof fk
  and is_rec = funkind_is_recursive fk
in
  case+ ds of
  | d :: ds => begin
      f0undec_tr (is_prf, is_rec, d) :: f0undeclst_tr (fk, ds)
    end
  | nil () => nil ()
end // end of [f0undeclst_tr]

(* ****** ****** *)

fn m0acdef_tr
  (d: m0acdef): m1acdef = let
  val def = d0exp_tr d.m0acdef_def
in
  m1acdef_make (
    d.m0acdef_loc, d.m0acdef_sym, d.m0acdef_arg, def
  ) // end of [m1acdef_make]
end // end of [m0acdef_tr]

fn m0acdeflst_tr
  (ds: m0acdeflst): m1acdeflst =
  $Lst.list_map_fun (ds, m0acdef_tr)
// end of [m0acdeflst_tr]

(* ****** ****** *)

fn i0mpdec_tr (d: i0mpdec): i1mpdec = let
  val qid = d.i0mpdec_qid
  val tmparg = s0explstlst_tr qid.impqi0de_arg
  val knd = LAMKINDfix ()
  val def = d0exp_lams_dyn_tr (
    knd, None(*oloc*), None(*ofc*), 0(*lin*),
    d.i0mpdec_arg, d.i0mpdec_res, None(*oefc*),
    d.i0mpdec_def
  ) // end of [val]
in
  i1mpdec_make (d.i0mpdec_loc, qid, tmparg, def)
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
end // end of [i0nclude_tr]

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

fn s0taload_tr (
    loc: loc_t
  , idopt: Option sym_t
  , fil: fil_t
  ) : d1ec = let
  val fullname = $Fil.filename_full fil
  val od1cs = staload_file_search fullname
  val d1cs = (case+ od1cs of
    | ~Some_vt (d1cs) => let
(*
        val () = begin
          printf ("The file [%s] is already loaded.", @(fullname));
          print_newline ()
        end // end of [val]
*)
      in
        d1cs
      end // end of [Some_vt]
    | ~None_vt () => d1cs where {
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
        end // end of [val]
*)
        val () = staload_file_insert (fullname, d1cs)
      } // end of [None_vt]
  ) : d1eclst
in
  d1ec_staload (loc, idopt, fil, 0(*loaded*), d1cs)
end // end of [s0taload_tr]

(* ****** ****** *)

implement d0ec_tr d0c0 = begin
  case+ d0c0.d0ec_node of
  | D0Cfixity (f0xty, ids) => begin
      d0ec_fixity_tr (f0xty, ids); d1ec_none (d0c0.d0ec_loc)
    end // end of [D0Cfixity]
  | D0Cnonfix ids => begin
      d0ec_nonfix_tr ids; d1ec_none (d0c0.d0ec_loc)
    end // end of [D0Cnonfix]
  | D0Csymintr ids => d1ec_symintr (d0c0.d0ec_loc, ids)
  | D0Ce0xpdef (id, def) => let
      val def: e1xp = case+ def of
        | Some e0xp => e0xp_tr e0xp | None () => e1xp_none ()
    in
      the_e1xpenv_add (id, def); d1ec_e1xpdef (d0c0.d0ec_loc, id, def)
    end // end of [D0Ce0xpdef]
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
        | E0XPACTprint () => do_e0xpact_prerr v1al
    in
      d1ec_none (d0c0.d0ec_loc)
    end // end of [D0Ce0xpact]
  | D0Cdatsrts (para, d0c, d0cs) => let
      val d1c = d0atsrtdec_tr d0c and d1cs = d0atsrtdeclst_tr d0cs
    in
      d1ec_datsrts (d0c0.d0ec_loc, para, d1c :: d1cs)
    end // end of [D0Cdatsrts]
  | D0Csrtdefs (d0c, d0cs) => let
      val d1c = s0rtdef_tr d0c and d1cs = s0rtdeflst_tr d0cs
    in
      d1ec_srtdefs (d0c0.d0ec_loc, d1c :: d1cs)
    end // end of [D0Csrtdefs]
  | D0Cstacons (impsrt, d0c, d0cs) => let
      val d1c = s0tacon_tr d0c and d1cs = s0taconlst_tr d0cs
    in
      d1ec_stacons (d0c0.d0ec_loc, impsrt, d1c :: d1cs)
    end // end of [D0Cstacons]
  | D0Cstacsts (d0c, d0cs) => let
      val d1c = s0tacst_tr d0c and d1cs = s0tacstlst_tr d0cs
    in
      d1ec_stacsts (d0c0.d0ec_loc, d1c :: d1cs)
    end // end of [D0Cstacsts]
  | D0Cstavars (d0c, d0cs) => let
      val d1c = s0tavar_tr d0c and d1cs = s0tavarlst_tr d0cs
    in
      d1ec_stavars (d0c0.d0ec_loc, d1c :: d1cs)
    end // end of [D0Cstavars]
  | D0Csexpdefs (os0t, d0c, d0cs) => let
      val os1t = s0rtopt_tr os0t
      val d1c = s0expdef_tr d0c and d1cs = s0expdeflst_tr d0cs
    in
      d1ec_sexpdefs (d0c0.d0ec_loc, os1t, d1c :: d1cs)
    end // end of [D0Csexpdefs]
  | D0Csaspdec (d0c) => begin
      d1ec_saspdec (d0c0.d0ec_loc, s0aspdec_tr d0c)
    end // end of [D0Csaspdec]
  | D0Cdatdecs (dk, d0c1, d0cs1, d0cs2) => let
      val d1c1 = d0atdec_tr d0c1 and d1cs1 = d0atdeclst_tr d0cs1
      val d1cs2 = s0expdeflst_tr d0cs2
    in
      d1ec_datdecs (d0c0.d0ec_loc, dk, d1c1 :: d1cs1, d1cs2)
    end // end of [D0Cdatdecs]
  | D0Cexndecs (d0c, d0cs) => let
      val d1c = e0xndec_tr d0c and d1cs = e0xndeclst_tr d0cs
    in
      d1ec_exndecs (d0c0.d0ec_loc, d1c :: d1cs)
    end // end of [D0Cexndecs]
  | D0Cdcstdecs (dck, s0qss, d0c, d0cs) => let
      val isfun = dcstkind_is_fun dck
      and isprf = dcstkind_is_proof dck
      val s1qss = s0qualstlst_tr s0qss
      val d1c = d0cstdec_tr (isfun, isprf, d0c)
      and d1cs = d0cstdeclst_tr (isfun, isprf, d0cs)
    in
      d1ec_dcstdecs (d0c0.d0ec_loc, dck, s1qss, d1c :: d1cs)
    end // end of [D0Cdcstdecs]
  | D0Coverload (id, qid) => begin
      d1ec_overload (d0c0.d0ec_loc, id, qid)
    end // end of [D0Coverload]
  | D0Cextype (name, s0e_def) => begin
      d1ec_extype (d0c0.d0ec_loc, name, s0exp_tr s0e_def)
    end // end of [D0Cextype]
  | D0Cextval (name, d0e_def) => begin
      d1ec_extval (d0c0.d0ec_loc, name, d0exp_tr d0e_def)
    end // end of [D0Cextval]
  | D0Cextcode (position, code) => begin
      d1ec_extcode (d0c0.d0ec_loc, position, code)
    end // end of [D0Cextcode]
  | D0Cvaldecs (valknd, d0c, d0cs) => let
      val d1c = v0aldec_tr d0c and d1cs = v0aldeclst_tr d0cs
    in
      d1ec_valdecs (d0c0.d0ec_loc, valknd, d1c :: d1cs)
    end // end of [D0Cvaldecs]
  | D0Cvaldecs_par (d0c, d0cs) => let
      val d1c = v0aldec_tr d0c and d1cs = v0aldeclst_tr d0cs
    in
      d1ec_valdecs_par (d0c0.d0ec_loc, d1c :: d1cs)
    end // end of [D0Cvaldecs_par]
  | D0Cvaldecs_rec (d0c, d0cs) => let
      val d1c = v0aldec_tr d0c and d1cs = v0aldeclst_tr d0cs
    in
      d1ec_valdecs_rec (d0c0.d0ec_loc, d1c :: d1cs)
    end // end of [D0Cvaldecs_rec]
  | D0Cfundecs (funkind, s0qss, d0c, d0cs) => let
      val s1qss = s0qualstlst_tr s0qss
      val d1cs = f0undeclst_tr (funkind, d0c :: d0cs)
    in
      d1ec_fundecs (d0c0.d0ec_loc, funkind, s1qss, d1cs)
    end // end of [D0Cfundecs]
  | D0Cvardecs (d0c, d0cs) => let
      val d1c = v0ardec_tr d0c and d1cs = v0ardeclst_tr d0cs
    in
      d1ec_vardecs (d0c0.d0ec_loc, d1c :: d1cs)
    end // end of [D0Cvardecs]
  | D0Cmacdefs (knd, d0c, d0cs) => let
      // knd: 0/1/2 => short/long/long rec
      val d1c = m0acdef_tr d0c and d1cs = m0acdeflst_tr d0cs
    in
      d1ec_macdefs (d0c0.d0ec_loc, knd, d1c :: d1cs)
    end // end of [D0Cmacdefs]
  | D0Cimpdec (i0mparg, d0c) => let
      val i1mparg = s0arglstlst_tr i0mparg
    in
      d1ec_impdec (d0c0.d0ec_loc, i1mparg, i0mpdec_tr d0c)
    end // end of [D0Cimpdec]
  | D0Cdynload (name) => let
      val filename: fil_t = case+ $Fil.filenameopt_make name of
        | ~Some_vt filename => filename | ~None_vt () => begin
            prerr_loc_error1 d0c0.d0ec_loc;
            prerr ": the file [";
            prerr name;
            prerr "] is not available for dynamic loading";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end // end of [None_vt]
      // end of [val]
    in
      d1ec_dynload (d0c0.d0ec_loc, filename)
    end // end of [D0Cdynload]
  | D0Cstaload (idopt, name) => let
      val filename: fil_t = case+ $Fil.filenameopt_make name of
        | ~Some_vt filename => filename
        | ~None_vt () => begin
            prerr_loc_error1 d0c0.d0ec_loc;
            prerr ": the file [";
            prerr name;
            prerr "] is not available for static loading";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end // end of [None_vt]
    in
      s0taload_tr (d0c0.d0ec_loc, idopt, filename)
    end // end of [D0Cstaload]
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
    end // end of [D0Clocal]
  | D0Cguadec (knd, gd0c) => begin
      d1ec_list (d0c0.d0ec_loc, guad0ec_tr (knd, gd0c))
    end // end of [D0Cguadec]
  | D0Cinclude (stadyn, name) => let
      val filename: fil_t = case+ $Fil.filenameopt_make name of
        | ~Some_vt filename => filename
        | ~None_vt () => begin
            prerr_loc_error1 d0c0.d0ec_loc;
            prerr ": the file [";
            prerr name;
            prerr "] is not available for inclusion";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end // end of [None_vt]
    in
      i0nclude_tr (d0c0.d0ec_loc, stadyn, filename)
    end // end of [D0Cinclude]
(*
  | _ => begin
      prerr_loc_error1 d0c0.d0ec_loc;
      prerr ": d0ec_tr: not available yet.\n";
      $Err.abort {d1ec} ()
    end // end of [_]
*)
end // end of [d0ec_tr]

// [$Lst.list_map_fun] is tail-recursive!
implement d0eclst_tr (d0cs) = $Lst.list_map_fun (d0cs, d0ec_tr)

(* ****** ****** *)

implement initialize () = () where {
  val () = $Glo.ats_dynloadflag_set (1) // [1] is the default value
} // end of [initialize]

implement finalize () = () where {
  val () = aux_function_name_prefix () where {
    fun aux_function_name_prefix (): void = begin
    case+ the_e1xpenv_find ($Sym.symbol_ATS_FUNCTION_NAME_PREFIX) of
    | ~Some_vt e1xp => let
        val v1al = e1xp_eval (e1xp)
      in
        case+ v1al of
        | V1ALstring s => let
            val s = string1_of_string s
          in
            $Glo.ats_function_name_prefix_set (stropt_some s)
          end // end of [V1ALstring]
        | _ => begin
            prerr_loc_error1 e1xp.e1xp_loc;
            prerr ": a string definition is required for [ATS_FUNCTION_NAME_PREFIX]";
            prerr_newline ();
            $Err.abort {void} ()
          end // end of [_]
      end // end of [Some_vt]
    | ~None_vt () => () // use the default value
    end // end of [aux_function_name_prefix]
  } // end of [where]

  val () = aux_dynloadflag () where {
    fun aux_dynloadflag (): void = begin
    case+ the_e1xpenv_find ($Sym.symbol_ATS_DYNLOADFLAG) of
    | ~Some_vt e1xp => let
        val v1al = e1xp_eval (e1xp)
        val flag = if v1al_is_true v1al then 1 else 0
      in
        $Glo.ats_dynloadflag_set (flag)
      end // end of [Some_vt]
    | ~None_vt () => () // use the default value
    end // end of [aux_dynloadflag]
  } // end of [where]

  val () = aux_dynloadfuname () where {
    fun aux_dynloadfuname (): void = begin
    case+ the_e1xpenv_find ($Sym.symbol_ATS_DYNLOADFUNAME) of
    | ~Some_vt e1xp => let
        val v1al = e1xp_eval (e1xp) in case+ v1al of
        | V1ALstring s => let
            val s = string1_of_string s
          in
            $Glo.ats_dynloadfuname_set (stropt_some s)
          end // end of [V1ALstring]
        | _ => begin
            prerr_loc_error1 e1xp.e1xp_loc;
            prerr ": a string definition is required for [ATS_DYNLOADFUNAME]";
            prerr_newline ();
            $Err.abort {void} ()
          end // end of [_]
      end // end of [Some_vt]
    | ~None_vt () => () // use the default value
    end // end of [aux_dynloadfuname]
  } // end of [where]
} // end of [finalize]

(* ****** ****** *)

(* end of [ats_trans1.dats] *)
