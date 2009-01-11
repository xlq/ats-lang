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

// Time: November 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Arr = "ats_array.sats"
staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload Fil = "ats_filename.sats"
staload Glo = "ats_global.sats"
staload IntInf = "ats_intinf.sats"
staload Lab = "ats_label.sats"
staload Loc = "ats_location.sats"
staload Lst = "ats_list.sats"
staload NS = "ats_namespace.sats"
staload Stamp = "ats_stamp.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"
staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_stadyncst2.sats"
staload "ats_trans2_env.sats"

(* ****** ****** *)

staload "ats_trans2.sats"

(* ****** ****** *)

staload _(*anonymous*) = "ats_array.dats"

(* ****** ****** *)

#define THISFILENAME "ats_trans2_dyn.dats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef loc_t = $Loc.location_t
typedef funclo = $Syn.funclo
typedef funcloopt = Option funclo
typedef efc = $Eff.effcst
typedef efcopt = Option efc
typedef sym_t = $Sym.symbol_t
typedef symopt_t = Option sym_t

(* ****** ****** *)

overload = with $Sym.eq_symbol_symbol

overload prerr with $Syn.prerr_d0ynq
overload prerr with $Sym.prerr_symbol
overload prerr with $Loc.prerr_location

(* ****** ****** *)

fun s2exp_arity_list (s2e: s2exp): List int = begin
  case+ s2e.s2exp_node of
  | S2Efun (_, _, _, _, s2es, s2e) => begin
      cons ($Lst.list_length s2es, s2exp_arity_list s2e)
    end
  | S2Eexi (_, _, s2e) => s2exp_arity_list s2e
  | S2Euni (_, _, s2e) => s2exp_arity_list s2e
  | S2Emetfn (_, _, s2e) => s2exp_arity_list s2e
  | _ => nil ()
end // end of [s2exp_arity_list]

fn d1cstdec_tr
  (dck: $Syn.dcstkind, s2vpslst: s2qualst, d1c: d1cstdec): d2cst_t = let
  val loc = d1c.d1cstdec_loc
  val fil = d1c.d1cstdec_fil
  val id = d1c.d1cstdec_sym
  var s2e_cst: s2exp =
    if $Syn.dcstkind_is_proof dck then s1exp_tr_dn_view d1c.d1cstdec_typ
    else s1exp_tr_dn_viewt0ype d1c.d1cstdec_typ
  val arilst = s2exp_arity_list s2e_cst
  val ext = d1c.d1cstdec_ext
  val d2c = d2cst_make (loc, fil, id, dck, s2vpslst, arilst, s2e_cst, ext)
in
  the_d2expenv_add_dcst d2c; d2c
end // end of [d1cstdec_tr]

implement d1cstdeclst_tr (dck, s2vpslst, d1cs) = begin
  case+ d1cs of
  | cons (d1c, d1cs) => let
      val d2c = d1cstdec_tr (dck, s2vpslst, d1c)
    in
      cons (d2c, d1cstdeclst_tr (dck, s2vpslst, d1cs))
    end
  | nil () => nil ()
end // end of [d1cstdeclst_tr]

(* ****** ****** *)

fn s1arg_arg_tr (s1a: s1arg): s2arg = begin
  s2arg_make (s1a.s1arg_loc, s1a.s1arg_sym, s1rtopt_tr s1a.s1arg_srt)
end // end of [s1arg_arg_tr]

fun s1arglst_arg_tr (s1as: s1arglst): s2arglst = begin case+ s1as of
  | cons (s1a, s1as) => cons (s1arg_arg_tr s1a, s1arglst_arg_tr s1as)
  | nil () => nil ()
end // end of [s1arglst_arg_tr]

(* ****** ****** *)

fun d2con_select_arity (d2cs: d2conlst, n: int): d2conlst = begin
  case+ d2cs of
  | D2CONLSTcons (d2c, d2cs) =>
      if d2con_arity_full_get d2c = n then begin
        D2CONLSTcons (d2c, d2con_select_arity (d2cs, n))
      end else begin
        d2con_select_arity (d2cs, n)
      end
  | D2CONLSTnil () => D2CONLSTnil ()
end // end of [d2con_select_arity]

fun d2con_select_arity_err_some
  (loc_id: loc_t, q: d0ynq, id: sym_t, n: int): d2con_t = begin
  prerr loc_id;
  prerr ": error(2)";
  prerr ": the dynamic identifier [";
  prerr q; prerr id;
  prerrf ("] refers to multiple constructors of arity %i.", @(n));
  prerr_newline ();
  $Err.abort {d2con_t} ()
end // end of [d2con_select_arity_err_some]

fun d2con_select_arity_err_none
  (loc_id: loc_t, q: d0ynq, id: sym_t, n: int): d2con_t = begin
  prerr loc_id;
  prerr ": error(2)";
  prerr ": the dynamic identifier [";
  prerr q; prerr id;
  prerrf ("] does not refer to any constructor of arity %i.", @(n));
  prerr_newline ();
  $Err.abort {d2con_t} ()
end // end of [d2con_select_arity_err_none]

(* ****** ****** *)

fun p1at_make_p1at (p1t: p1at): p1at = begin
  case+ p1t.p1at_node of
  | P1Tqid (q, id) => begin
    case+ the_d2expenv_find_qua (q, id) of
    | ~Some_vt d2i => begin case+ d2i of
      | D2ITEMe1xp e1xp => begin
          p1at_make_p1at (p1at_make_e1xp (p1t.p1at_loc, e1xp))
        end
      | _ => p1t
      end // end of [Some_vt]
    | ~None_vt () => p1t
    end
  | _ => p1t
end // end of [p1at_make_p1at]

fun d1exp_make_d1exp (d1e: d1exp): d1exp = begin
  case+ d1e.d1exp_node of
  | D1Eqid (q, id) => begin
    case+ the_d2expenv_find_qua (q, id) of
    | ~Some_vt d2i => begin case+ d2i of
      | D2ITEMe1xp e1xp => begin
          d1exp_make_d1exp (d1exp_make_e1xp (d1e.d1exp_loc, e1xp))
        end
      | _ => d1e
      end // end of [Some_vt]
    | ~None_vt () => d1e
    end
  | _ => d1e
end // end of [d1exp_make_d1exp]

(* ****** ****** *)

local // implementing [p1at_con_tr]

fun aux1
  (d2c: d2con_t, sub: stasub_t,
   s2vpslst: s2qualst, out: &s2qualst): s2exp = begin
  case+ s2vpslst of
  | cons (s2vps, s2vpslst) => let
      val @(sub, s2vs) = stasub_extend_svarlst (sub, s2vps.0)
      val s2ps = s2explst_subst (sub, s2vps.1)
    in
      out := @(s2vs, s2ps) :: out; aux1 (d2c, sub, s2vpslst, out)
    end
  | nil () => let
      val npf = d2con_npf_get d2c
      val s2es_arg =
        s2explst_subst (sub, d2con_arg_get d2c)
      val s2c = d2con_scst_get d2c
      val s2e_res: s2exp = case+ d2con_ind_get d2c of
        | Some s2es_ind => let
            val s2es_ind = s2explst_subst (sub, s2es_ind)
          in
            s2exp_cstapp (s2c, s2es_ind)
          end
        | None () => s2exp_cst s2c
    in
      out := s2qualst_reverse out;
      s2exp_confun (npf, s2es_arg, s2e_res)
    end
end // end [aux1]

fun aux2
  (loc_sap: loc_t,
   d2c: d2con_t, sub: stasub_t, s2vpss: s2qualst, s1as: s1vararglst,
   out: &s2qualst): s2exp = let

fn err (loc_sap: loc_t, d2c: d2con_t): s2exp = begin
  prerr loc_sap;
  prerr ": error(2)";
  $Deb.debug_prerrf (": %s: p1at_con_tr: aux2", @(THISFILENAME));
  prerr ": the constructor [";
  prerr d2c;
  prerr "] is applied to too many static arguments.";
  prerr_newline ();
  $Err.abort {s2exp} ()
end

in // in of [let]
  case+ s1as of
  | cons (s1a, s1as) => begin case+ s1a of
    | S1VARARGone () => begin case+ s2vpss of
      | cons (s2vps, s2vpss) => let
          val @(sub, s2vs) = stasub_extend_svarlst (sub, s2vps.0)
          val s2ps = s2explst_subst (sub, s2vps.1)
        in
          out := @(s2vs, s2ps) :: out;
          aux2 (loc_sap, d2c, sub, s2vpss, s1as, out)
        end
      | nil () => err (loc_sap, d2c)
      end
    | S1VARARGall () => aux1 (d2c, sub, s2vpss, out)
    | S1VARARGseq arg => begin case+ s2vpss of
      | cons (s2vps, s2vpss) => let
          val arg = s1arglst_arg_tr arg
          val @(sub, s2vs) =
            stasub_extend_sarglst_svarlst (loc_sap, sub, arg, s2vps.0)
          val s2ps = s2explst_subst (sub, s2vps.1)
        in
          out := @(s2vs, s2ps) :: out;
          aux2 (loc_sap, d2c, sub, s2vpss, s1as, out)
        end
      | nil () => err (loc_sap, d2c)
      end
    end
  | nil () => aux1 (d2c, sub, s2vpss, out)
end // end of [aux2]

in // in of [local]

fn p1at_con_tr
  (loc_dap: loc_t, loc_sap: loc_t,
   d2c: d2con_t, s1as: s1vararglst, npf: int, p1ts: p1atlst)
  : p2at = let
  val s2vpss = d2con_qua_get d2c
  var out: s2qualst = nil ()
  val s2e = aux2 (loc_sap, d2c, stasub_nil, s2vpss, s1as, out)
  val p2ts = p1atlst_tr p1ts
in
  p2at_con (loc_dap, 1(*freeknd*), d2c, out, s2e, npf, p2ts)
end // end of [p1at_con_tr]

implement p1at_con_instantiate (loc_sap, d2c) = let
  var out: s2qualst = nil ()
  val s2e = begin
    aux2 (loc_sap, d2c, stasub_nil, d2con_qua_get d2c, nil (), out)
  end
in
  @(out, s2e)
end // end of [p1at_con_instantiate]

end // end of [local]

(* ****** ****** *)

fn p1at_qid_app_dyn_tr
  (loc_dap: loc_t, loc_sap: loc_t, loc_id: loc_t,
   q: $Syn.d0ynq, id: sym_t, s1as: s1vararglst, npf: int, p1ts: p1atlst)
  : p2at = let

  fn err1 (loc_id: loc_t, q: $Syn.d0ynq, id: sym_t): d2conlst = begin
    prerr loc_id;
    prerr ": error(2)";
    $Deb.debug_prerrf (": %s: p1at_qid_app_dyn_tr", @(THISFILENAME));
    prerr ": the dynamic identifier [";
    prerr q; prerr id;
    prerr "] does not refer to a constructor.";
    prerr_newline ();
    $Err.abort {d2conlst} ()     
  end

  fn err2 (loc_id: loc_t, q: $Syn.d0ynq, id: sym_t): d2conlst = begin
    prerr loc_id;
    prerr ": error(2)";
    $Deb.debug_prerrf (": %s: p1at_qid_app_dyn_tr", @(THISFILENAME));
    prerr ": unrecognized dynamic constructor [";
    prerr q; prerr id;
    prerr "].";
    prerr_newline ();
    $Err.abort {d2conlst} ()
  end

  val d2cs = begin
    case+ the_d2expenv_find_qua (q, id) of
    | ~Some_vt d2i => begin case+ d2i of
      | D2ITEMcon d2cs => d2cs | _ => err1 (loc_id, q, id)
      end
    | ~None_vt () => err2 (loc_id, q, id)
  end // end of [val]
  val is_arg_omit: bool = begin
    case+ p1ts of
    | cons (p1t, nil ()) => begin
        case+ p1t.p1at_node of P1Tanys () => true | _ => false
      end
    | _ => false
  end // end of [val]
  val np1ts = $Lst.list_length p1ts
  val d2cs = (
    if is_arg_omit then d2cs else d2con_select_arity (d2cs, np1ts)
  ) : d2conlst
  val d2c = begin case+ d2cs of
    | D2CONLSTcons (d2c, d2cs) => begin case+ d2cs of
      | D2CONLSTcons _ => begin
          d2con_select_arity_err_some (loc_id, q, id, np1ts)
        end
      | D2CONLSTnil _ => d2c
      end
    | _ => begin
        d2con_select_arity_err_none (loc_id, q, id, np1ts)
      end
  end // end of [val]
  val p1ts = begin
    if is_arg_omit then begin case+ p1ts of
      | cons (p1t, nil ()) => let
          val npf = d2con_npf_get d2c and s2es = d2con_arg_get d2c
          fun aux (loc: loc_t, s2es: s2explst): p1atlst =
            case+ s2es of
            | cons (_, s2es) => cons (p1at_any loc, aux (loc, s2es))
            | nil () => nil ()
        in
          aux (p1t.p1at_loc, s2es)
        end
      | _ => p1ts // deadcode
    end else p1ts
  end // end of [val]
in
  p1at_con_tr (loc_dap, loc_sap, d2c, s1as, npf, p1ts)
end // end of [p1at_qid_app_dyn_tr]

(* ****** ****** *)

fn p1at_app_tr
  (loc_dap: loc_t, loc_sap: loc_t,
   p1t_fun: p1at, sarg: s1vararglst, npf: int, darg: p1atlst)
  : p2at = let
  val p1t_fun = p1at_make_p1at (p1t_fun)
in
  case+ p1t_fun.p1at_node of
  | P1Tqid (q, id) => let
      val loc_id = p1t_fun.p1at_loc
    in
      p1at_qid_app_dyn_tr (loc_dap, loc_sap, loc_id, q, id, sarg, npf, darg)
    end
  | _ => begin
     prerr loc_dap;
     prerr ": error(2)";
     $Deb.debug_prerrf (": %s: p1at_app_tr", @(THISFILENAME));
     prerr ": the application in the pattern is not allowed.";
     prerr_newline ();
     $Err.abort {p2at} ()
   end
end // end of [p1at_app_tr]

(* ****** ****** *)

// [freeknd]: 0: nonlinear; 1: preserve; ~1: free
fn p1at_free_tr (loc0: loc_t, p1t: p1at): p2at = let
  val p2t = p1at_tr p1t
in
  case+ p2t.p2at_node of
  | P2Tcon (freeknd, d2c, s2vpss, s2e, npf, p2ts) => begin
      p2at_con (loc0, ~freeknd, d2c, s2vpss, s2e, npf, p2ts)
    end
  | _ => begin
      prerr loc0;
      prerr ": error(2)";
      $Deb.debug_prerrf (": %s: p1at_free_tr", @(THISFILENAME));
      prerr ": values that match this pattern are not allowed to be freed.";
      prerr_newline ();
      $Err.abort {p2at} ()
    end
end // end of [p1at_free_tr]

(* ****** ****** *)

fn qid_is_vbox (q: $Syn.d0ynq, id: sym_t): bool = begin
  case+ q.d0ynq_node of
  | $Syn.D0YNQnone () => id = $Sym.symbol_VBOX | _ => false
end // end of [qid_is_vbox]

fn p1at_vbox_tr (loc: loc_t, npf: int, p1ts: p1atlst): p2at = let
  fn err {a:viewt@ype} (loc: loc_t): a = begin
    $Loc.prerr_location loc;
    prerr ": error(2)";
    prerr ": the [vbox] pattern is syntactically incorrect.";
    prerr_newline ();
    $Err.abort {a} ()
  end

  val () = if npf <> 0 then err {void} (loc) else ()
  val p1t = (
    case+ p1ts of cons (p1t, nil ()) => p1t | _ => err {p1at} (loc)
  ) : p1at
  val p2t = p1at_tr p1t
in
  case+ p2t.p2at_node of
  | P2Tvar (refknd, d2v) when refknd = 0 => p2at_vbox (loc, d2v)
  | _ => err {p2at} (loc)
end // end of [p2at_vbox_tr]

(* ****** ****** *)

implement p1at_tr (p1t0) = let
val loc0 = p1t0.p1at_loc
var linearity_check: int = 0
val p2t0 = (
  case+ p1t0.p1at_node of
  | P1Tann (p1t, s1e) => let
      val p2t = p1at_tr p1t
      val s2e = s1exp_tr_dn_impredicative s1e
    in
      p2at_ann (loc0, p2t, s2e)
    end
  | P1Tany _ => p2at_any (loc0)
  | P1Tanys _ => p2at_any (loc0)
  | P1Tapp_dyn (p1t_fun, _(*loc_arg*), npf, darg) => let
      val loc1 = p1t_fun.p1at_loc
      val p1t_fun = p1at_make_p1at p1t_fun
    in
      case+ p1t_fun.p1at_node of
      | P1Tqid (q, id) => begin case+ 0 of
        | _ when qid_is_vbox (q, id) => p1at_vbox_tr (loc0, npf, darg)
        | _ => begin
            linearity_check := 2;
            p1at_qid_app_dyn_tr (loc0, loc1, loc1, q, id, '[], npf, darg)
          end
        end // end of [P1Tqid]
      | P1Tapp_sta (p1t_fun, sarg) => begin
          linearity_check := 2;
          p1at_app_tr (loc0, loc1, p1t_fun, sarg, npf, darg)
        end // end of [P1Tapp_sta]
      | _ => begin
          prerr loc0;
          prerr ": error(2)";
          $Deb.debug_prerrf (": %s: p1at_tr", @(THISFILENAME));
          prerr ": the application in the pattern is not allowed.";
          prerr_newline ();
          $Err.abort {p2at} ()
        end
    end
  | P1Tapp_sta (p1t_fun, sarg) => let
      val loc1 = p1t_fun.p1at_loc
    in
      linearity_check := 1;
      p1at_app_tr (loc0, loc1, p1t_fun, sarg, 0, '[])
    end
  | P1Tas (id, p1t) => let
      val d2v = d2var_make (id.i0de_loc, id.i0de_sym)
    in
      linearity_check := 2;
      p2at_as (loc0, 0(*refknd*), d2v, p1at_tr p1t)
    end
  | P1Tchar c(*char*) => p2at_char (loc0, c)
  | P1Texist (s1as, p1t) => let
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val s2vs = s1arglst_var_tr s1as
      val p2t = p1at_tr p1t
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
    in
      linearity_check := 1; p2at_exist (loc0, s2vs, p2t)
    end
  | P1Tempty () => p2at_empty (loc0)
  | P1Tfloat f(*string*) => p2at_float (loc0, f)
  | P1Tfree p1t => p1at_free_tr (loc0, p1t)
  | P1Tint str(*string*) => let
      val int = $IntInf.intinf_make_string str
    in
      p2at_int (loc0, str, int)
    end
  | P1Tqid (q, id) => begin case+ q.d0ynq_node of
    | $Syn.D0YNQnone () => begin case+ the_d2expenv_find id of
      | ~Some_vt d2i => begin case+ d2i of
        | D2ITEMe1xp e1xp => begin
            let val p1t = p1at_make_e1xp (loc0, e1xp) in p1at_tr p1t end
          end
        | _ => p2at_var (loc0, 0(*refknd*), d2var_make (loc0, id))
        end
      | ~None_vt () => p2at_var (loc0, 0(*refknd*), d2var_make (loc0, id))
      end
    | _ => begin
        p1at_qid_app_dyn_tr (loc0, loc0, loc0, q, id, '[], 0(*npf*), '[])
      end
    end
  | P1Tlist (npf, p1ts) => begin case+ p1ts of
    | cons _ => let
        val p2ts = p1atlst_tr p1ts
      in
        linearity_check := 2; p2at_tup (loc0, 0(*tupknd*), npf, p2ts)
      end
    | nil _ => p2at_empty (loc0)
    end
  | P1Tlst (p1ts) => begin
      linearity_check := 2; p2at_lst (loc0, p1atlst_tr p1ts)
    end
  | P1Trec (recknd, lp1ts) => let
      val lp2ts = labp1atlst_tr lp1ts
    in
      linearity_check := 2; p2at_rec (loc0, recknd, 0(*npf*), lp2ts)
    end
  | P1Tref (id) => begin
      p2at_var (loc0, 1(*refknd*), d2var_make (id.i0de_loc, id.i0de_sym))
    end
  | P1Trefas (id, p1t) => let
      val d2v = d2var_make (id.i0de_loc, id.i0de_sym)
    in
      linearity_check := 2;
      p2at_as (loc0, 1(*refknd*), d2v, p1at_tr p1t)
    end
  | P1Tstring str => p2at_string (loc0, str)
  | P1Tsvararg _ => begin
      prerr loc0;
      prerr ": Internal Error: p1at_tr: P1Tsvararg";
      prerr_newline ();
      $Err.abort {p2at} ()
    end
  | P1Ttup (tupknd, npf, p1ts) => begin
      linearity_check := 2; p2at_tup (loc0, tupknd, npf, p1atlst_tr p1ts)
    end
) : p2at // end of [val]

in

if linearity_check >= 1 then begin
  s2varlstord_linearity_test (loc0, p2t0.p2at_svs);
end;

if linearity_check >= 2 then begin
  d2varlstord_linearity_test (loc0, p2t0.p2at_dvs);
end;

p2t0

end // end of [p1at_tr]

implement p1atlst_tr (p1ts) = $Lst.list_map_fun (p1ts, p1at_tr)

implement labp1atlst_tr (lp1ts) = begin
  case+ lp1ts of
  | LABP1ATLSTcons (l0, p1t, lp1ts) => begin
      LABP2ATLSTcons (l0.l0ab_lab, p1at_tr p1t, labp1atlst_tr lp1ts)
    end
  | LABP1ATLSTnil () => LABP2ATLSTnil ()
  | LABP1ATLSTdot () => LABP2ATLSTdot ()
end // end of [labp1atlst_tr]

(* ****** ****** *)

implement p1at_arg_tr (p1t0, wths1es) = begin
  case+ p1t0.p1at_node of
  | P1Tann (p1t, s1e) => let
      val p2t = p1at_tr p1t
      val s2e = s1exp_arg_tr_dn_impredicative (s1e, wths1es)
    in
      p2at_ann (p1t0.p1at_loc, p2t, s2e)
    end
  | P1Tlist (npf, p1ts) => let
      val p2ts = p1atlst_arg_tr (p1ts, wths1es)
    in
      p2at_list (p1t0.p1at_loc, npf, p2ts)
    end
  | _ => p1at_tr p1t0
end // end of [p1at_arg_tr]

implement p1atlst_arg_tr (p1ts, wths1es) = begin
  case+ p1ts of
  | cons (p1t, p1ts) => begin
      cons (p1at_arg_tr (p1t, wths1es), p1atlst_arg_tr (p1ts, wths1es))
    end
  | nil () => nil ()
end // end of [p1atlst_arg_tr]

(* ****** ****** *)

fn d2sym_lrbrackets (loc: loc_t): d2sym = let
  val id = $Sym.symbol_LRBRACKETS
  var d2is0: d2itemlst = list_nil () and err: int = 0
  val () = begin case+ the_d2expenv_find (id) of
    | ~Some_vt d2i => begin
        case+ d2i of D2ITEMsym d2is => d2is0 := d2is | _ => err := 1
      end
    | ~None_vt () => (err := 1)
  end // end of [val]
  val () = // run-time checking
    if err > 0 then begin
      prerr loc;
      prerr ": Internal Error: d2sym_lrbrackets";
      prerr_newline ();
      $Err.abort {void} ()
    end
in
  d2sym_make (loc, $Syn.d0ynq_none (), id, d2is0)
end // end of [d2sym_lrbrackets]

fn d1exp_arrsub_tr
  (loc0: loc_t, d1e_arr: d1exp, loc_ind: loc_t, d1ess_ind: d1explstlst)
  : d2exp = let
  val d2s = d2sym_lrbrackets (loc0)
  val d2e_arr = d1exp_tr d1e_arr
  val d2ess_ind = d1explstlst_tr d1ess_ind
in
  d2exp_arrsub (loc0, d2s, d2e_arr, loc_ind, d2ess_ind)
end // end of [d1exp_arrsub_tr]

(* ****** ****** *)

fn d1exp_assgn_tr (loc0: loc_t, d1es: d1explst): d2exp = begin
  case+ d1es of
  | cons (d1e1, cons (d1e2, nil ())) => begin
      d2exp_assgn (loc0, d1exp_tr d1e1, d1exp_tr d1e2)
    end
  | _ => begin
      prerr loc0;
      prerr ": Internal Error: d1exp_assgn_tr";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end
end // end of [d1exp_assgn_tr]

fn d1exp_deref_tr (loc0: loc_t, d1es: d1explst): d2exp = begin
  case+ d1es of
  | cons (d1e, nil ()) => d2exp_deref (loc0, d1exp_tr d1e)
  | _ => begin
      prerr loc0;
      prerr ": Internal Error: d1exp_deref_tr";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end
end // end of [d1exp_deref_tr]

(* ****** ****** *)

fn macro_def_check
  (loc0: loc_t, knd: int, id: sym_t): void = let
  val level = macro_level_get ()
in
  if level > 0 then begin
    if knd > 0 then begin (* long form *)
      prerr loc0;
      prerr ": error(2)";
      prerr ": the identifier ["; prerr id;
      prerr "] refers to a macro definition in long form";
      prerr ", but one in short form is expected.";
      prerr_newline ();
      $Err.abort {void} ()
    end
  end else begin (* level = 0 *)
    if knd = 0 then begin (* short form *)
      prerr loc0;
      prerr ": error(2)";
      prerr ": the identifier ["; prerr id;
      prerr "] refers to a macro definition in short form";
      prerr ", but one in long form is expected.";
      prerr_newline ();
      $Err.abort {void} ()
    end
  end
end // end of [macro_def_check]

fn macro_var_check (loc0: loc_t, id: sym_t): void = let
  val level = macro_level_get ()
in
  if level > 0 then begin
    prerr loc0;
    prerr ": error(2)";
    prerr ": the identifier ["; prerr id;
    prerr "] incorrectly refers to a macro argument variable.";
    prerr_newline ();
    $Err.abort {void} ()
  end
end // end of [macro_var_check]

(* ****** ****** *)

dataviewtype specdynid = SPDIDassgn | SPDIDderef | SPDIDnone

fn specdynid_of_qid (q: d0ynq, id: sym_t): specdynid = begin
  case+ q.d0ynq_node of
  | $Syn.D0YNQnone () => begin
      if id = $Sym.symbol_COLONEQ then SPDIDassgn ()
      else if id = $Sym.symbol_BANG then SPDIDderef ()
      else SPDIDnone ()        
    end
  | _ => SPDIDnone ()
end // end of [specdynid_of_qid]

(* ****** ****** *)

fn d1exp_qid_tr
  (loc0: loc_t, q: $Syn.d0ynq, id: sym_t): d2exp = begin
  case+ the_d2expenv_find_qua (q, id) of
  | ~Some_vt d2i => begin case+ d2i of
    | D2ITEMcon d2cs => let
        val d2cs = d2con_select_arity (d2cs, 0)
        val d2c: d2con_t = case+ d2cs of
          | D2CONLSTcons (d2c, d2cs) => begin case+ d2cs of
            | D2CONLSTcons _ => begin
                d2con_select_arity_err_some (loc0, q, id, 0)
              end
            | _ => d2c
            end
          | _ => begin
              d2con_select_arity_err_none (loc0, q, id, 0)
            end
      in
        d2exp_con (loc0, d2c, nil (), 0(*npf*), nil ())
      end
    | D2ITEMcst d2c => d2exp_cst (loc0, d2c)
    | D2ITEMe1xp e1xp => d1exp_tr (d1exp_make_e1xp (loc0, e1xp))
    | D2ITEMmacdef d2m => let
        val knd = d2mac_kind_get d2m
        val () = macro_def_check (loc0, knd, id)
      in
        d2exp_mac (loc0, d2m)
      end
    | D2ITEMmacvar d2v => let
        val () = macro_var_check (loc0, id)
      in
        d2exp_var (loc0, d2v)
      end
    | D2ITEMsym d2is => let
        val d2s = d2sym_make (loc0, q, id, d2is)
      in
        d2exp_sym (loc0, d2s)
      end
    | D2ITEMvar d2v => d2exp_var (loc0, d2v)
    end // end of [Some d2i]
  | ~None_vt () => begin
      prerr loc0;
      prerr ": error(2)";
      $Deb.debug_prerrf (": %s: d1exp_qid_tr", @(THISFILENAME));
      prerr ": the dynamic identifier [";
      prerr q; prerr id;
      prerr "] is unrecognized.";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end
end // end of [d1exp_qid_tr]

(* ****** ****** *)

fn d1exp_qid_app_sta_tr
  (loc_sap: loc_t, loc_id: loc_t, q: d0ynq, id: sym_t, s1as: s1exparglst)
  : d2exp = let
  val s2as = s1exparglst_tr s1as
  val od2i = the_d2expenv_find_qua (q, id)
in
  case+ od2i of
  | ~Some_vt d2i => begin case+ d2i of
    | D2ITEMcon d2cs => let
        val d2cs = d2con_select_arity (d2cs, 0)
        val d2c: d2con_t = case+ d2cs of
          | D2CONLSTcons (d2c, d2cs) => begin case+ d2cs of
            | D2CONLSTcons _ => begin
                d2con_select_arity_err_some (loc_id, q, id, 0)
              end
            | _ => d2c
            end
          | _ => begin
              d2con_select_arity_err_none (loc_id, q, id, 0)
            end
      in
        d2exp_con (loc_sap, d2c, s2as, 0(*npf*), nil ())
      end
    | D2ITEMcst d2c => let
        val d2e_fun = d2exp_cst (loc_id, d2c)
      in
        d2exp_app_sta (loc_sap, d2e_fun, s2as)
      end
    | D2ITEMvar d2v => let
        val d2e_fun = d2exp_var (loc_id, d2v)
      in
        d2exp_app_sta (loc_sap, d2e_fun, s2as)
      end
    | D2ITEMmacdef _ => begin
        prerr loc_id;
        prerr ": error(2)";
        $Deb.debug_prerrf (": %s: d1exp_qid_app_sta_tr", @(THISFILENAME));
        prerr ": the identifier refers to a macro definition";
        prerr ", which cannot be applied to static arguments.";
        prerr_newline ();
        $Err.abort {d2exp} ()
      end
    | D2ITEMmacvar _ => begin
        prerr loc_id;
        prerr ": error(2)";
        $Deb.debug_prerrf (": %s: d1exp_qid_app_sta_tr", @(THISFILENAME));
        prerr ": the identifier refers to a macro argument variable";
        prerr ", which cannot be applied.";
        prerr_newline ();
        $Err.abort {d2exp} ()
      end
    | _ => begin
        prerr loc_id;
        prerr ": error(2)";
        $Deb.debug_prerrf (": %s: d1exp_qid_app_sta_tr", @(THISFILENAME));
        prerr ": the identifier refers to a dynamic term that cannot be applied.";
        prerr_newline ();
        $Err.abort {d2exp} ()
      end
    end // end of [Some d2i]
  | ~None_vt () => begin
      prerr loc_id;
      prerr ": error(2)";
      $Deb.debug_prerrf (": %s: d1exp_qid_app_sta_tr", @(THISFILENAME));
      prerr ": unrecognized dynamic identifier [";
      prerr q; prerr id;
      prerr "]";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end
end // end of [d2exp_qid_app_sta_tr]

(* ****** ****** *)

fn d1exp_qid_app_dyn_tr
  (loc_dap: loc_t, loc_sap: loc_t, loc_id: loc_t, 
   q: d0ynq, id: sym_t, sarg: s1exparglst,
   loc_arg: loc_t, npf: int, darg: d1explst): d2exp = let
  val sarg = s1exparglst_tr sarg
  val darg = d1explst_tr darg
  val od2i = the_d2expenv_find_qua (q, id)
in
  case+ od2i of
  | ~Some_vt d2i => begin case+ d2i of
    | D2ITEMcon d2cs => let
        val n = $Lst.list_length darg
        val d2cs = d2con_select_arity (d2cs, n)
        val d2c = case+ d2cs of
          | D2CONLSTcons (d2c, D2CONLSTnil ()) => d2c
          | D2CONLSTcons (d2c, _) => begin
              d2con_select_arity_err_some (loc_id, q, id, n)
            end
          | D2CONLSTnil () => begin
              d2con_select_arity_err_none (loc_id, q, id, n)
            end
      in
        d2exp_con (loc_dap, d2c, sarg, npf, darg)
      end
    | D2ITEMcst d2c => let
        val d2e_fun = d2exp_cst (loc_id, d2c)
      in
        d2exp_app_sta_dyn (loc_dap, loc_sap, d2e_fun, sarg, loc_arg, npf, darg)
      end
    | D2ITEMmacdef d2m => let
        val knd = d2mac_kind_get d2m
        val () = macro_def_check (loc_id, knd, id)
        val d2e_fun = d2exp_mac (loc_id, d2m)
      in
        d2exp_app_sta_dyn (loc_dap, loc_sap, d2e_fun, sarg, loc_arg, npf, darg)
      end
    | D2ITEMsym d2is => let
        val d2s = d2sym_make (loc_id, q, id, d2is)
        val d2e_fun = d2exp_sym (loc_id, d2s)
      in
        d2exp_app_sta_dyn (loc_dap, loc_sap, d2e_fun, sarg, loc_arg, npf, darg)
      end
    | D2ITEMvar d2v => let
        val d2e_fun = d2exp_var (loc_id, d2v)
      in
        d2exp_app_sta_dyn (loc_dap, loc_sap, d2e_fun, sarg, loc_arg, npf, darg)
      end
    | D2ITEMmacvar _ => begin
        prerr loc_id;
        prerr ": error(2)";
        prerr ": the identifer refers to a macro argument variable";
        prerr ", which cannot be applied.";
        prerr_newline ();
        $Err.abort {d2exp} ()
      end
    | D2ITEMe1xp _ => begin
        prerr loc_id;
        prerr ": Internal Error: d1exp_qid_app_dyn_tr: D2ITEMe1xp";
        prerr_newline ();
        $Err.abort {d2exp} ()
      end
    end // end of [Some d2i]
  | ~None_vt () => begin
      prerr loc_id;
      prerr ": error(2)";
      $Deb.debug_prerrf (": %s: d1exp_qid_app_dyn_tr", @(THISFILENAME));
      prerr ": the dynamic identifier [";
      prerr q; prerr id;
      prerr "] is unrecognized.";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end
end // end of [d1exp_qid_app_dyn_tr]

(* ****** ****** *)

// [wths1es] is assumed to be not empty
fun d1exp_wths1explst_tr
  (d1e0: d1exp, wths1es: wths1explst): d2exp = begin
  case+ d1e0.d1exp_node of
  | D1Eann_type (d1e, s1e) => let
      val d2e = d1exp_tr d1e
      val s2e = s1exp_res_tr_dn_impredicative (s1e, wths1es)
    in
      d2exp_ann_type (d1e0.d1exp_loc, d2e, s2e)
    end
  | D1Eann_effc (d1e, efc) => let
      val d2e = d1exp_wths1explst_tr (d1e, wths1es)
      val s2fe = effcst_tr (efc)
    in
      d2exp_ann_seff (d1e0.d1exp_loc, d2e, s2fe)
    end
  | D1Eann_funclo (d1e, fc) => let
      val d2e = d1exp_wths1explst_tr (d1e, wths1es)
    in
      d2exp_ann_funclo (d1e0.d1exp_loc, d2e, fc)
    end
  | _ => begin
      prerr d1e0.d1exp_loc;
      prerr ": error(2)";
      $Deb.debug_prerrf (": %s: d1exp_wths1explst_tr", @(THISFILENAME));
      prerr ": the dynamic expression is expected to be ascribed a type but it is not.";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end
end // end of [d1exp_wths1explst_tr]

(* ****** ****** *)

fun i1nvarglst_tr
  (xs: i1nvarglst): i2nvarglst = begin case+ xs of
  | cons (x, xs) => begin
    case+ the_d2expenv_find x.i1nvarg_sym of
    | ~Some_vt d2i => begin case+ d2i of
      | D2ITEMvar d2v => let
          val os2e = (
            case+ x.i1nvarg_typ of
            | Some s1e => Some (s1exp_tr_dn_impredicative s1e)
            | None () => None ()
          ) : s2expopt
          val arg = i2nvarg_make (d2v, os2e)
        in
          cons (arg, i1nvarglst_tr xs)
        end // end of [D2ITEMvar]
      | _ => begin
          prerr x.i1nvarg_loc;
          prerr ": error(2)";
          $Deb.debug_prerrf (": %s: i1nvarglst_tr", @(THISFILENAME));
          prerr ": the dynamic identifier [";
          prerr x.i1nvarg_sym;
          prerr "] does not refer to a variable.";
          prerr_newline ();
          $Err.abort ()
        end
      end // end of [Some_vt]
    | ~None_vt () => begin
        prerr x.i1nvarg_loc;
        prerr ": error(2)";
        $Deb.debug_prerrf (": %s: i1nvarglst_tr", @(THISFILENAME));
        prerr ": the dynamic identifier [";
        prerr x.i1nvarg_sym;
        prerr "] is unrecognized.";
        prerr_newline ();
        $Err.abort ()
      end // end of [None_vt]
    end // end of [cons]
  | nil () => nil ()
end // end of [i1nvarglst_tr]

fn i1nvresstate_tr (r1es: i1nvresstate): i2nvresstate = let
  val @(s2vs, s2ps) = s1qualst_tr (r1es.i1nvresstate_qua)
  val body = i1nvarglst_tr r1es.i1nvresstate_arg
in
  i2nvresstate_make (s2vs, s2ps, body)
end // end of [i1nvresstate_tr]

fn loopi1nv_tr (inv: loopi1nv): loopi2nv = let
  val @(s2vs, s2ps) = s1qualst_tr (inv.loopi1nv_qua)
  val met = (
    case+ inv.loopi1nv_met of
    | Some s1es => Some (s1explst_tr_dn_int s1es) | None () => None ()
  ) : s2explstopt
  val arg = i1nvarglst_tr inv.loopi1nv_arg
  val res = i1nvresstate_tr inv.loopi1nv_res
in
  loopi2nv_make (inv.loopi1nv_loc, s2vs, s2ps, met, arg, res)
end // end of [loopi1nv_tr]

(* ****** ****** *)

fn m1atch_tr (m1at: m1atch): m2atch = let
  val d2e = d1exp_tr (m1at.m1atch_exp); val op2t = (
    case+ m1at.m1atch_pat of
    | Some p1t => let
        val p2t = p1at_tr p1t
        val s2vs = s2varlst_of_s2varlstord (p2t.p2at_svs)
        val () = the_s2expenv_add_svarlst s2vs
        val d2vs = d2varlst_of_d2varlstord (p2t.p2at_dvs)
        val () = the_d2expenv_add_dvarlst d2vs
      in
        Some p2t
      end
    | None () => None ()
  ) : p2atopt // end of [val]
in
  m2atch_make (m1at.m1atch_loc, d2e, op2t)
end // end of [m1atch_tr]

fn m1atchlst_tr (m1ats: m1atchlst): m2atchlst =
  $Lst.list_map_fun (m1ats, m1atch_tr)

(* ****** ****** *)

fn c1lau_tr {n:nat} (n: int n, c1l: c1lau): c2lau n = let
  val p1t = c1l.c1lau_pat
  val p1ts = (
    case+ p1t.p1at_node of
    | P1Tlist (_(*npf*), p1ts) => p1ts | _ => cons (p1t, nil ())
  ) : p1atlst
  val p2ts: p2atlst = p1atlst_tr p1ts
  stavar np2ts: int
  val np2ts: int np2ts = $Lst.list_length p2ts
(*
  val () = begin
    printf ("c1lau_tr: n = %i and np2ts = %i\n", @(n, np2ts))
  end
*)
  val () = (
    if np2ts <> n then begin
      prerr c1l.c1lau_loc;
      prerr ": error(2)";
      $Deb.debug_prerrf (": %s: c1lau_tr", @(THISFILENAME));
      if np2ts < n then prerr ": this clause should contain more patterns.";
      if np2ts > n then prerr ": this clause should contain less patterns.";
      prerr_newline ();
      $Err.abort {void} ();
      assert (np2ts = n) // deadcode
    end else begin
      () // [np2ts = n] holds!
    end // end of [if]
  ) : [np2ts==n] void
  val (pf_env2 | ()) = trans2_env_push ()
  val () = let
    val s2vs = s2varlst_of_s2varlstord (p2atlst_svs_union p2ts)
  in
    the_s2expenv_add_svarlst s2vs
  end
  val () = let
    val d2vs = d2varlst_of_d2varlstord (p2atlst_dvs_union p2ts)
  in
    the_d2expenv_add_dvarlst d2vs
  end
  val gua = m1atchlst_tr (c1l.c1lau_gua)
  val d2e = d1exp_tr (c1l.c1lau_exp)
  val () = trans2_env_pop (pf_env2 | (*none*))
in
  c2lau_make (c1l.c1lau_loc, p2ts, gua, c1l.c1lau_seq, c1l.c1lau_neg, d2e)
end // end of [c1lau_tr]

fun c1laulst_tr {n:nat}
  (n: int n, c1ls: c1laulst): c2laulst n = begin case+ c1ls of
  | cons (c1l, c1ls) => cons (c1lau_tr (n, c1l), c1laulst_tr (n, c1ls))
  | nil () => nil ()
end // end of [c1laulst_tr]

(* ****** ****** *)

fn sc1lau_tr_dn
  (sc1l: sc1lau, s2t_pat: s2rt): sc2lau = let
  val (pf_s2expenv | ()) = the_s2expenv_push ()
  val sp2t = sp1at_tr_dn (sc1l.sc1lau_pat, s2t_pat)
  val d2e = d1exp_tr (sc1l.sc1lau_exp)
  val () = the_s2expenv_pop (pf_s2expenv | (*none*))  
in
  sc2lau_make (sc1l.sc1lau_loc, sp2t, d2e)
end // end of [sc1lau_tr]

fun sc1laulst_tr_dn
  (sc1ls: sc1laulst, s2t_pat: s2rt): sc2laulst =
  case+ sc1ls of
  | list_cons (sc1l, sc1ls) => let
      val sc2l = sc1lau_tr_dn (sc1l, s2t_pat)
      val sc2ls = sc1laulst_tr_dn (sc1ls, s2t_pat)
    in
      list_cons (sc2l, sc2ls)
    end // end of [list_cons]
  | list_nil () => list_nil ()
// end of [sc1laulst_tr_dn]

fn sc2laulst_covercheck
  (loc0: loc_t, sc2ls: sc2laulst, s2t_pat: s2rt): void = let
  val s2tb_pat = case+ s2t_pat of
    | S2RTbas s2tb => s2tb | _ => begin
        $Loc.prerr_location loc0; prerr ": error(2)";
        prerr ": the static expression being analyzed is of the sort [";
        prerr s2t_pat; prerr "], which is not a base sort as is required.";
        prerr_newline ();
        $Err.abort {s2rtbas} ()
      end // end of [_]
  val s2tdat_pat = case+ s2tb_pat of
    | S2RTBASdef s2td => s2td | _ => begin
        $Loc.prerr_location loc0; prerr ": error(2)";
        prerr ": the static expression being analyzed is of the sort [";
        prerr s2t_pat; prerr "], which is not a datasort as is required.";
        prerr_newline ();
        $Err.abort {s2rtdat_t} ()
      end // end of [_]
  val s2cs = s2rtdat_conlst_get (s2tdat_pat)
  val ns2cs = s2cstlst_length (s2cs)
  val (pf_gc, pf_arr | A) = $Arr.array_ptr_make_elt<int> (ns2cs, 0)
  val () = check (pf_arr | A, ns2cs, sc2ls) where {
    fun check {n:nat} {l:addr} (
        pf: !array_v (int, n, l) | p: ptr l, n: int n, sc2ls: sc2laulst
      ) : void = case+ sc2ls of
      | list_cons (sc2l, sc2ls) => let
          val sp2t = sc2l.sc2lau_pat
          val+ SP2Tcon (s2c, _) = sp2t.sp2at_node
          val tag = s2cst_tag_get (s2c); val tag = int1_of_int tag
          val () = assert (tag >= 0); val () = assert (tag < n)
          val () = p->[tag] := p->[tag] + 1
        in
          check (pf | p, n, sc2ls)
        end // end of [list_cons]
      | list_nil () => ()
  } // end of [val]
  val err = errmsg
    (pf_arr | loc0, A, ns2cs, s2cs, 0, 0) where {
    fun errmsg {n,i:nat | i <= n} {l:addr} .<n-i>. (
        pf: !array_v (int, n, l)
      | loc0: loc_t, p: ptr l, n: int n, s2cs: s2cstlst, i: int i, err: int
      ) : int =
      if i < n then let
        val times = p->[i] in case+ s2cs of
        | S2CSTLSTcons (s2c, s2cs) => begin case+ 0 of
          | _ when times = 1 => errmsg (pf | loc0, p, n, s2cs, i+1, err)
          | _ when times = 0 => begin
              $Loc.prerr_location loc0; prerr ": error(2)";
              prerr ": ill-formed static case-expression";
              prerr ": the constructor ["; prerr s2c; prerr "] is missing.";
              prerr_newline ();
              errmsg (pf | loc0, p, n, s2cs, i+1, err+1)
            end // end of [_ when times = 0]
          | _ (* times > 1 *) => begin
              $Loc.prerr_location loc0; prerr ": error(2)";
              prerr ": ill-formed static case-expression";
              prerr ": the constructor ["; prerr s2c; prerr "] occurs repeatedly.";
              prerr_newline ();
              errmsg (pf | loc0, p, n, s2cs, i+1, err+1)
            end // end of [_ when times > 0]
          end // end of [S2CSTLSTcons]
        | S2CSTLSTnil () => err // deadcode!
      end else begin
        err // return value
      end // end of [if]
  } // end of [errmsg]
  val () = $Arr.array_ptr_free {int} (pf_gc, pf_arr | A)
  val () = if err > 0 then $Err.abort {void} ()
in
  // empty
end // end of [sc2laulst_covercheck]

(* ****** ****** *)

implement d1exp_tr (d1e0): d2exp = let
  val loc0 = d1e0.d1exp_loc
(*
  val () = begin
    prerr "d1exp_tr: d1e0 = "; prerr_d1exp d1e0; print_newline ()
  end // end of [val]
*)
in
  case+ d1e0.d1exp_node of
  | D1Eann_type (d1e, s1e) => let
      val d2e = d1exp_tr d1e; val s2e = s1exp_tr_dn_impredicative s1e
    in
      d2exp_ann_type (loc0, d2e, s2e)
    end
  | D1Eann_effc (d1e, efc) => let
      val d2e = d1exp_tr d1e; val s2fe = effcst_tr (efc)
    in
      d2exp_ann_seff (loc0, d2e, s2fe)
    end
  | D1Eann_funclo (d1e, fc) => begin
      let val d2e = d1exp_tr d1e in d2exp_ann_funclo (loc0, d2e, fc) end
    end
  | D1Eapp_dyn (d1e_fun, loc_arg, npf, darg) => let
      val loc1 = d1e_fun.d1exp_loc
      val d1e_fun = d1exp_make_d1exp d1e_fun
    in
      case+ d1e_fun.d1exp_node of
      | D1Eqid (q, id) => let
          val spdid = specdynid_of_qid (q, id)
        in
          case+ spdid of
          | ~SPDIDnone () => d1exp_qid_app_dyn_tr (
              loc0, loc1, loc1, q, id, '[], loc_arg, npf, darg
            ) // end of [SPDIDnone]
          | ~SPDIDassgn () => d1exp_assgn_tr (loc0, darg)
          | ~SPDIDderef () => d1exp_deref_tr (loc0, darg)
        end // end of [D1Eapp_dyn]
      | D1Eapp_sta (d1e_fun, sarg) => let
          val d1e_fun = d1exp_make_d1exp d1e_fun
        in
          case+ d1e_fun.d1exp_node of
          | D1Eqid (q, id) => let
              val loc_id = d1e_fun.d1exp_loc
            in
              d1exp_qid_app_dyn_tr (
                loc0, loc1, loc_id, q, id, sarg, loc_arg, npf, darg
              ) // end of [d1exp_qid_app_dyn_tr]
            end
          | _ => let
              val d2e_fun = d1exp_tr d1e_fun
              val sarg = s1exparglst_tr sarg
              val darg = d1explst_tr darg
            in
              d2exp_app_sta_dyn (
                loc0, loc1, d2e_fun, sarg, loc_arg, npf, darg
              ) // end of [d1exp_app_sta_dyn]
            end
        end // end of [D1Eapp_sta]
      | _ => let
          val d2e_fun = d1exp_tr d1e_fun
          val darg = d1explst_tr darg
        in
          d2exp_app_dyn (loc0, d2e_fun, loc_arg, npf, darg)
        end
    end // end of [D1Eapp_dyn]
  | D1Eapp_sta (d1e_fun, sarg) => let
      val d1e_fun = d1exp_make_d1exp d1e_fun
    in
      case+ d1e_fun.d1exp_node of
      | D1Eqid (q, id) => begin
          d1exp_qid_app_sta_tr (loc0, d1e_fun.d1exp_loc, q, id, sarg)
        end
      | _ => let
          val d2e_fun = d1exp_tr d1e_fun
          val sarg = s1exparglst_tr sarg
        in
          d2exp_app_sta (loc0, d2e_fun, sarg)
        end
    end // end of [D1Eapp_sta]
  | D1Earrinit (s1e_elt, od1e_asz, d1es_elt) => let
      val s2t_elt = (case+ od1e_asz of
        | Some _ => begin case+ d1es_elt of
          | list_cons _ (*initialized*) => s2rt_t0ype // cannot be linear
          | list_nil () (*uninitialized*) => s2rt_viewt0ype // can be linear
          end // end of [Some]
        | None () => s2rt_viewt0ype // can be linear
      ) : s2rt // end of [val]
      val s2e_elt = s1exp_tr_dn (s1e_elt, s2t_elt)
      val od2e_asz = d1expopt_tr od1e_asz; val d2es_elt = d1explst_tr d1es_elt
    in
      d2exp_arrinit (loc0, s2e_elt, od2e_asz, d2es_elt)
    end // end of [D1Earrinit]
  | D1Earrsize (os1e_elt, d1es_elt) => let
      val os2e_elt = (case+ os1e_elt of
        | Some s1e => Some (s1exp_tr_dn (s1e, s2rt_viewt0ype))
        | None () => None ()
      ) : s2expopt // end of [val]
      val d2es_elt = d1explst_tr d1es_elt
    in
      d2exp_arrsize (loc0, os2e_elt, d2es_elt)
    end // end of [D1Earrsize]
  | D1Earrsub (d1e_arr, loc_ind, d1ess_ind) => begin
      d1exp_arrsub_tr (loc0, d1e_arr, loc_ind, d1ess_ind)
    end // end of [D1Earrsub]
  | D1Echar chr => d2exp_char (loc0, chr)
  | D1Ecaseof (knd, r1es, d1es, c1ls) => let
      val r2es = i1nvresstate_tr r1es
      val d2es = d1explst_tr d1es
      val nd2es = $Lst.list_length d2es
      val c2ls = c1laulst_tr (nd2es, c1ls)
    in
      d2exp_caseof (loc0, knd, r2es, nd2es, d2es, c2ls)
    end // end of [D1Ecaseof]
  | D1Ecrypt (knd, d1e) => begin
      d2exp_crypt (loc0, knd, d1exp_tr d1e)
    end
  | D1Edynload fil => d2exp_dynload (loc0, fil)
  | D1Eeffmask (effs, d1e) => begin
      d2exp_effmask (loc0, effs, d1exp_tr d1e)
    end
  | D1Eempty () => d2exp_empty (loc0)
  | D1Eexist (s1a, d1e) =>
      d2exp_exist (loc0, s1exparg_tr s1a, d1exp_tr d1e)
  | D1Eextval (s1e, code) =>
      d2exp_extval (loc0, s1exp_tr_dn_viewt0ype s1e, code)
  | D1Efix (id, d1e) => let
      val d2v = d2var_make (id.i0de_loc, id.i0de_sym)
      val () = d2var_isfix_set (d2v, true)
      val (pf_d2expenv | ()) = the_d2expenv_push ()
      val () = the_d2expenv_add_dvar d2v
      val d2e = d1exp_tr d1e
      val () = the_d2expenv_pop (pf_d2expenv | (*none*))
    in
      d2exp_fix (loc0, d2v, d2e)
    end // end of [D1Efix]
  | D1Efloat f(*string*) => d2exp_float (d1e0.d1exp_loc, f)
  | D1Efloatsp f(*string*) => d2exp_floatsp (d1e0.d1exp_loc, f)
  | D1Efoldat (s1as, d1e) => begin
      d2exp_foldat (loc0, s1exparglst_tr s1as, d1exp_tr d1e)
    end
  | D1Efor (inv, ini, test, post, body) => let
      val ini = d1exp_tr ini
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val inv = loopi1nv_tr inv
      val test = d1exp_tr test
      val post = d1exp_tr post
      val body = d1exp_tr body
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
    in
      d2exp_for (loc0, inv, ini, test, post, body)
    end // end of [D1Efor]
  | D1Efreeat (s1as, d1e) => begin
      d2exp_freeat (loc0, s1exparglst_tr s1as, d1exp_tr d1e)
    end
  | D1Eif (r1es, d1e_cond, d1e_then, od1e_else) => let
      val r2es = i1nvresstate_tr r1es
      val d2e_cond = d1exp_tr d1e_cond
      val d2e_then = d1exp_tr d1e_then
      val od2e_else = d1expopt_tr od1e_else
    in
      d2exp_if (loc0, r2es, d2e_cond, d2e_then, od2e_else)
    end // end of [D1Eif]
  | D1Eint str(*string*) => begin
      d2exp_int (loc0, str, $IntInf.intinf_make_string str)
    end
  | D1Eintsp str(*string*) => begin
      d2exp_intsp (loc0, str, $IntInf.intinf_make_stringsp str)
    end
  | D1Elam_dyn (lin, p1t_arg, d1e_body) => let
      var wths1es = WTHS1EXPLSTnil ()
      val p2t_arg = p1at_arg_tr (p1t_arg, wths1es)
      val () = wths1es := wths1explst_reverse wths1es
      var npf: int = 0
      val p2ts_arg = (
        case+ p2t_arg.p2at_node of
        | P2Tlist (npf1, p2ts) => (npf := npf1; p2ts)
        | _ => cons (p2t_arg, nil ())
      ) : p2atlst
      val (pf_env | ()) = trans2_env_push ()
      val () = let
        val s2vs = s2varlst_of_s2varlstord p2t_arg.p2at_svs
      in
        the_s2expenv_add_svarlst s2vs
      end
      val () = let
        val d2vs = d2varlst_of_d2varlstord p2t_arg.p2at_dvs
      in
        the_d2expenv_add_dvarlst d2vs
      end
      val (pf_level | ()) = d2var_current_level_inc ()
      val d2e_body: d2exp = begin
        if wths1explst_is_none wths1es then begin
          d1exp_tr d1e_body // regular translation
        end else begin
          d1exp_wths1explst_tr (d1e_body, wths1es)
        end // end of [if]
      end
      val () = d2var_current_level_dec (pf_level | (*none*))
      val () = trans2_env_pop (pf_env | (*none*))
    in
      d2exp_lam_dyn (loc0, lin, npf, p2ts_arg, d2e_body)
    end // end of [D1Elam_dyn]
  | D1Elam_met (_, met, body) => let
      val met = s1explst_tr_up met; val body = d1exp_tr body
    in
      d2exp_lam_met_new (loc0, met, body)
    end // end of [D1Elam_met]
  | D1Elam_sta_ana _ => begin
      prerr loc0;
      prerr ": error(2)";
      $Deb.debug_prerrf (": %s: d1exp_tr: D1Elam_sta_ana: ", @(THISFILENAME));
      prerr "illegal use of static lambda-abstraction in analysis form.";
      prerr_newline ();
      $Err.abort {d2exp} ()
    end
  | D1Elam_sta_syn (_, s1qs, d1e) => let
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val @(s2vs, s2ps) = s1qualst_tr (s1qs)
      val d2e = d1exp_tr d1e
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
    in
      d2exp_lam_sta (loc0, s2vs, s2ps, d2e)
    end // end of [D1Elam_sta_syn]
  | D1Elazy_delay (lin, d1e) => begin case+ 0 of
    | _ when lin = 0 => let
        val d2e = d1exp_tr d1e in d2exp_lazy_delay (loc0, d2e)
      end // end of [_ when lin = 0]
    | _ (* lin = 1 *) => begin case+ d1e.d1exp_node of
      | D1Elist (_(*npf*), d1es) => begin case+ d1es of
        | cons (d1e1, cons (d1e2, nil ())) => let
            val d2e1 = d1exp_tr d1e1 and d2e2 = d1exp_tr d1e2
          in
            d2exp_lazy_vt_delay (loc0, d2e1, d2e2)
          end // end of [cons (_, cons (_, nil))]
        | _ => let
            val n = $Lst.list_length d1es; val () = begin
              prerr loc0; prerr ": error(2)";
              if n > 2 then prerr ": less argumnets should be given.";
              if n < 2 then prerr ": more argumnets should be given.";
              prerr_newline ()
            end // end of [val]
          in
            $Err.abort {d2exp} ()
          end // end of [_]
        end // end of [D1Elist]
      | _ => let
          val d2e1 = d1exp_tr d1e and d2e2 = d2exp_empty (d1e.d1exp_loc)
        in
          d2exp_lazy_vt_delay (loc0, d2e1, d2e2)
        end // end of [_]
      end // end of [_ when lin = 1]
    end // end of [D1Elazy_delay]
  | D1Elet (d1cs, d1e) => let
      val (pf_env | ()) = trans2_env_push ()
      val d2cs = d1eclst_tr d1cs; val d2e = d1exp_tr d1e
      val () = trans2_env_pop (pf_env | (*none*))
    in
      d2exp_let (loc0, d2cs, d2e)
    end // end of [D1Elet]
  | D1Elist (npf, d1es) => begin case+ d1es of
    | cons _ => let
        val d2es = d1explst_tr d1es in d2exp_tup (loc0, 0, npf, d2es)
      end // end of [cons]
    | nil () => d2exp_empty (loc0)
    end // end of [D1Elist]
  | D1Eloopexn flag => d2exp_loopexn (loc0, flag)
  | D1Elst (lin, os1e_elt, d1es_elt) => let
      val s2t_elt: s2rt =
        if lin > 0 then s2rt_viewt0ype else s2rt_t0ype
      val os2e_elt = (
        case+ os1e_elt of
        | Some s1e_elt => Some (s1exp_tr_dn (s1e_elt, s2t_elt))
        | None () => None ()
      ) : s2expopt
      val d2es_elt = d1explst_tr d1es_elt
    in
      d2exp_lst (loc0, lin, os2e_elt, d2es_elt)
    end // end of [D1Elst]
  | D1Emacsyn (knd, d1e) => let
(*
      val () = begin
        print "d1exp_tr: d1e0 = "; print d1e0; print_newline ()
      end
*)
    in
      case+ knd of
      | $Syn.MACSYNKINDcross () => let
          val () = macro_level_dec (loc0)
          val d2e0 = d2exp_macsyn (loc0, knd, d1exp_tr d1e)
          val () = macro_level_inc (loc0)
        in
          d2e0
        end
      | $Syn.MACSYNKINDdecode () => let
          val () = macro_level_dec (loc0)
          val d2e0 = d2exp_macsyn (loc0, knd, d1exp_tr d1e)
          val () = macro_level_inc (loc0)
        in
          d2e0
        end
      | $Syn.MACSYNKINDencode () => let
          val () = macro_level_inc (loc0)
          val d2e0 = d2exp_macsyn (loc0, knd, d1exp_tr d1e)
          val () = macro_level_dec (loc0)
        in
          d2e0
        end
    end // end of [D1Emacsyn]
(*
  | D1Emod (m1ids) => d2exp_mod (loc, mid1_list_tr m1ids)
*)
  | D1Eqid (q, id) => d1exp_qid_tr (loc0, q, id)
  | D1Eptrof d1e => d2exp_ptrof (loc0, d1exp_tr d1e)
  | D1Eraise (d1e) => begin
      d2exp_raise (loc0, d1exp_tr d1e)
    end
  | D1Erec (recknd, ld1es) => begin
      d2exp_rec (loc0, recknd, 0(*npf*), labd1explst_tr ld1es)
    end
  | D1Escaseof (r1es, s1e, sc1ls) => let
      val r2es = i1nvresstate_tr r1es
      val s2e = s1exp_tr_up s1e; val s2t_pat = s2e.s2exp_srt
      val sc2ls = sc1laulst_tr_dn (sc1ls, s2t_pat)
      val () = sc2laulst_covercheck (loc0, sc2ls, s2t_pat)
    in
      d2exp_scaseof (loc0, r2es, s2e, sc2ls)
    end // end of [D1Escaseof]
  | D1Esel (ptr, d1e, d1l) => let
      val d2e = d1exp_tr d1e; val d2l = d1lab_tr d1l
    in
      if ptr > 0 then d2exp_sel_ptr (loc0, d2e, d2l)
      else begin case+ d2e.d2exp_node of
      | D2Esel (d2e_root, d2ls) => begin
          d2exp_sel (loc0, d2e_root, $Lst.list_extend (d2ls, d2l))
        end
       | _ => begin
          d2exp_sel (loc0, d2e, cons (d2l, nil ()))
         end // end of [_]
      end // end of [if]
    end // end of [D1Esel]
  | D1Eseq d1es => d2exp_seq (d1e0.d1exp_loc, d1explst_tr d1es)
  | D1Esif (r1es, s1e_cond, d1e_then, d1e_else) => let
      val r2es = i1nvresstate_tr r1es
      val s2e_cond = s1exp_tr_dn_bool s1e_cond
      val d2e_then = d1exp_tr d1e_then
      val d2e_else = d1exp_tr d1e_else
    in
      d2exp_sif (loc0, r2es, s2e_cond, d2e_then, d2e_else)
    end // end of [D1Esif]
  | D1Estring (str, len) => d2exp_string (loc0, str, len)
  | D1Estruct ld1es => d2exp_struct (loc0, labd1explst_tr ld1es)
  | D1Etmpid (qid, ts1ess) => let
      val loc_id = qid.tmpqi0de_loc
      val q = qid.tmpqi0de_qua and id = qid.tmpqi0de_sym
      val d2e_qid = d1exp_qid_tr (loc_id, q, id)
      val ts2ess = tmps1explstlst_tr_up ts1ess
    in
      d2exp_tmpid (loc0, d2e_qid, ts2ess)
    end // end of [D1Etmpid]
  | D1Etop () => d2exp_top (loc0)
  | D1Etrywith (r1es, d1e, c1ls) => let
      val r2es = i1nvresstate_tr r1es
      val d2e = d1exp_tr d1e; val c2ls = c1laulst_tr (1, c1ls)
    in
      d2exp_trywith (loc0, r2es, d2e, c2ls)
    end // end of [D1Etrywith]
  | D1Etup (tupknd, npf, d1es) => begin
      d2exp_tup (loc0, tupknd, npf, d1explst_tr d1es)
    end
  | D1Eviewat d1e => d2exp_viewat (loc0, d1exp_tr d1e)
  | D1Ewhere (d1e, d1cs) => let
      val (pf_env | ()) = trans2_env_push ()
      val d2cs = d1eclst_tr d1cs; val d2e = d1exp_tr d1e
      val () = trans2_env_pop (pf_env | (*none*))
    in
      d2exp_where (loc0, d2e, d2cs)
    end // end of [D1Ewhere]
  | D1Ewhile (inv, test, body) => let
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val inv = loopi1nv_tr inv
      val test = d1exp_tr test
      val body = d1exp_tr body
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
    in
      d2exp_while (loc0, inv, test, body)
    end // end of [D1Ewhile]
  | _ => begin
      prerr loc0;
      prerr ": d1exp_tr: not implemented yet: ";
      prerr_d1exp d1e0;
      prerr_newline ();
      $Err.abort {d2exp} ()
    end
end // end of [d1exp_tr]

implement d1explst_tr (d1es) = $Lst.list_map_fun (d1es, d1exp_tr)
implement d1explstlst_tr (d1ess) = $Lst.list_map_fun (d1ess, d1explst_tr)

implement d1expopt_tr (od1e) = case+ od1e of
  | Some d1e => Some (d1exp_tr d1e) | None () => None ()

implement labd1explst_tr (ld1es) = case+ ld1es of
  | LABD1EXPLSTcons (l0, d1e, ld1es) =>
      LABD2EXPLSTcons (l0.l0ab_lab, d1exp_tr d1e, labd1explst_tr ld1es)
  | LABD1EXPLSTnil () => LABD2EXPLSTnil ()

implement d1lab_tr (d1l) = case+ d1l.d1lab_node of
  | D1LABlab lab => d2lab_lab (d1l.d1lab_loc, lab)
  | D1LABind ind => d2lab_ind (d1l.d1lab_loc, d1explstlst_tr ind)

(* ****** ****** *)

fn witht1ype_tr (w1t: witht1ype): s2expopt = begin
  case+ w1t of
  | WITHT1YPEnone () => None ()
  | WITHT1YPEprop s1e => Some (s1exp_tr_dn (s1e, s2rt_prop))
  | WITHT1YPEtype s1e => Some (s1exp_tr_dn (s1e, s2rt_t0ype))
  | WITHT1YPEview s1e => Some (s1exp_tr_dn (s1e, s2rt_view))
  | WITHT1YPEviewtype s1e => Some (s1exp_tr_dn (s1e, s2rt_viewt0ype))
end // end of [witht1ype_tr]

(* ****** ****** *)

fn symintr_tr (ids: i0delst): void = let
  fun aux (ids: i0delst): void = case+ ids of
    | cons (id, ids) => begin
        the_d2expenv_add (id.i0de_sym, D2ITEMsym (nil ())); aux ids
      end
    | nil () => ()
in
  aux ids
end // end of [symintr_tr]

fn symelim_tr (ids: i0delst): void = let
  fun aux (ids: i0delst): void = case+ ids of
    | cons (id, ids) => begin
        the_d2expenv_add (id.i0de_sym, D2ITEMsym (nil ())); aux ids
      end
    | nil () => ()
in
  aux ids
end // end of [symelim_tr]

(* ****** ****** *)

fn overload_tr (id: $Syn.i0de, qid: $Syn.dqi0de): void = let
(*
  val () = begin
    print "overload_tr: id = "; print id.i0de_sym;
    print " and qid = "; print qid.dqi0de_qua; print qid.dqi0de_sym;
    print_newline ();
  end
*)
  val d2i = (
    case+ the_d2expenv_find_qua (qid.dqi0de_qua, qid.dqi0de_sym) of
    | ~Some_vt d2i => d2i
    | ~None_vt () => begin
        prerr qid.dqi0de_loc;
        prerr ": error(2)";
        $Deb.debug_prerrf (": %s: overload_tr", @(THISFILENAME));
        prerr ": the dynamic identifier [";
        prerr qid.dqi0de_qua; prerr qid.dqi0de_sym;
        prerr "] is unrecognized.";
        prerr_newline ();
        $Err.abort {d2item} ()
      end
  ) : d2item
  val d2is = (case+
    the_d2expenv_find id.i0de_sym of
    | ~Some_vt d2i => begin case+ d2i of
      | D2ITEMsym d2is => d2is | _ => begin
          prerr id.i0de_loc;
          prerr ": error(2)";
          $Deb.debug_prerrf (": %s: overload_tr", @(THISFILENAME));
          prerr ": the identifier [";
          prerr id.i0de_sym;
          prerr "] should refer to a symbol but it does not.";
          prerr_newline ();
          $Err.abort {d2itemlst} ()          
        end
      end // end of [Some_vt]
    | ~None_vt () => begin
        prerr id.i0de_loc;
        prerr ": error(2)";
        $Deb.debug_prerrf (": %s: overload_tr", @(THISFILENAME));
        prerr ": the identifier [";
        prerr id.i0de_sym;
        prerr "] is unrecognized.";
        prerr_newline ();
        $Err.abort {d2itemlst} ()
      end // end of [None_vt]
  ) : d2itemlst
in
  the_d2expenv_add (id.i0de_sym, D2ITEMsym (d2i :: d2is))
end // end of [overload_tr]

(* ****** ****** *)

fn v1aldec_tr (d1c: v1aldec, p2t: p2at): v2aldec = let
  val loc = d1c.v1aldec_loc
  val def = d1exp_tr (d1c.v1aldec_def)
  val ann = witht1ype_tr (d1c.v1aldec_ann)
in
  v2aldec_make (loc, p2t, def, ann)
end // end of [v1aldec_tr]

fn v1aldeclst_tr {n:nat}
  (isrec: bool, d1cs: list (v1aldec, n)): v2aldeclst = let
  fun aux1 {n:nat} (d1cs: list (v1aldec, n)): list (p2at, n) =
    case+ d1cs of
    | cons (d1c, d1cs) => cons (p1at_tr d1c.v1aldec_pat, aux1 d1cs)
    | nil () => nil ()
  fun aux2 {n:nat}
    (d1cs: list (v1aldec, n), p2ts: list (p2at, n)): v2aldeclst =
    case+ d1cs of
    | cons (d1c, d1cs) => let
        val+ cons (p2t, p2ts) = p2ts
      in
        cons (v1aldec_tr (d1c, p2t), aux2 (d1cs, p2ts))
      end
    | nil () => nil ()
  val p2ts: list (p2at, n) = aux1 d1cs
  val s2vs = s2varlst_of_s2varlstord (p2atlst_svs_union p2ts)
  val d2vs = d2varlst_of_d2varlstord (p2atlst_dvs_union p2ts)
in
  if isrec then let
    val () = the_d2expenv_add_dvarlst d2vs
    val d2cs = aux2 (d1cs, p2ts)
  in
    the_s2expenv_add_svarlst s2vs; d2cs
  end else let
    val d2cs = aux2 (d1cs, p2ts)
    val () = the_d2expenv_add_dvarlst d2vs
  in
    the_s2expenv_add_svarlst s2vs; d2cs
  end
end // end of [v1aldeclst_tr]

(* ****** ****** *)

fn f1undec_tr (
    level: int
  , decarg: s2qualst
  , d2v: d2var_t
  , d1c: f1undec
  ) : f2undec = let
  val () = d2var_lev_set (d2v, level)
  val () = d2var_decarg_set (d2v, decarg)
  val def = d1exp_tr (d1c.f1undec_def)
(*
  val () = begin
    print "f1undec_tr: d2v = "; print d2v; print_newline ()
  end
  val () = begin
    print "f1undec_tr: def = "; print def; print_newline ()
  end
*)
  val ann = witht1ype_tr (d1c.f1undec_ann)
in
  f2undec_make (d1c.f1undec_loc, d2v, def, ann)
end // end of [f1undec_tr]

fn f1undeclst_tr {n:nat} (
    fk: $Syn.funkind
  , level: int
  , decarg: s2qualst
  , d1cs: list (f1undec, n)
  ) : f2undeclst = let
  val isprf = $Syn.funkind_is_proof fk
  val isrec = $Syn.funkind_is_recursive fk
  val d2vs: list (d2var_t, n) = aux1 (isprf, d1cs) where {
    fun aux1 {n:nat}
      (isprf: bool, d1cs: list (f1undec, n))
      : list (d2var_t, n) = begin case+ d1cs of
      | cons (d1c, d1cs) => let
          val d2v = d2var_make (d1c.f1undec_sym_loc, d1c.f1undec_sym)
          val () = d2var_isfix_set (d2v, true)
          val () = d2var_isprf_set (d2v, isprf)
        in
          cons (d2v, aux1 (isprf, d1cs))
        end
      | nil () => nil ()
    end // end of [aux1]
  } // end of [where]
  fun aux2 {n:nat} (
      level: int
    , decarg: s2qualst
    , d2vs: list (d2var_t, n)
    , d1cs: list (f1undec, n)
    ) : list (f2undec, n) =
    case+ d2vs of
    | cons (d2v, d2vs) => let
        val+ cons (d1c, d1cs) = d1cs
        val d2c = f1undec_tr (level, decarg, d2v, d1c)
        val d2cs = aux2 (level, decarg, d2vs, d1cs)
      in
        cons (d2c, d2cs)
      end
    | nil () => nil ()
  val () = if isrec then the_d2expenv_add_dvarlst (d2vs) else ()
  val d2cs = aux2 (level, decarg, d2vs, d1cs)
  val () = if isrec then () else the_d2expenv_add_dvarlst (d2vs)
in
  d2cs
end // end of [f1undeclst_tr]

(* ****** ****** *)

fn v1ardec_tr (d1c: v1ardec): v2ardec = let
  val knd = d1c.v1ardec_knd
  val id = d1c.v1ardec_sym
  val loc_id = d1c.v1ardec_sym_loc
  val d2v_ptr = d2var_make (loc_id, id)
  val s2v_ptr = s2var_make_id_srt (id, s2rt_addr)
  val os2e_ptr = Some (s2exp_var s2v_ptr)
  val () = d2var_addr_set (d2v_ptr, os2e_ptr)
  val typ = (
    case+ d1c.v1ardec_typ of
    | Some s1e => Some (s1exp_tr_dn_impredicative s1e)
    | None () => None ()
  ) : s2expopt
  val wth = (case+ d1c.v1ardec_wth of
    | Some (i0de) => let
        val d2v = d2var_make (i0de.i0de_loc, i0de.i0de_sym)
      in
        D2VAROPTsome d2v
      end // end of [Some]
    | None () => D2VAROPTnone ()
  ) : d2varopt // end of [val]
  val ini = d1expopt_tr d1c.v1ardec_ini
in
  v2ardec_make (d1c.v1ardec_loc, knd, d2v_ptr, s2v_ptr, typ, wth, ini)
end // end of [v1ardec_tr]

fn v1ardeclst_tr (d1cs: v1ardeclst): v2ardeclst = let
  val d2cs = aux d1cs where {
    fun aux (d1cs: v1ardeclst): v2ardeclst =
      case+ d1cs of
      | cons (d1c, d1cs) => cons (v1ardec_tr d1c, aux d1cs)
      | nil () => nil ()
  } // end of [where]
  val () = aux d2cs where {
    fun aux (d2cs: v2ardeclst): void =
      case+ d2cs of
      | cons (d2c, d2cs) => let
          val () = the_s2expenv_add_svar (d2c.v2ardec_svar)
          val () = the_d2expenv_add_dvar (d2c.v2ardec_dvar)
          val () = case+ d2c.v2ardec_wth of
            | D2VAROPTsome d2v => the_d2expenv_add_dvar d2v
            | D2VAROPTnone () => ()
          // end of [val]
        in
          aux d2cs
        end // end of [cons]
      | nil () => ()
  } // end of [where]
in
  d2cs
end // end of [v2ardeclst_tr]

(* ****** ****** *)

fn s1arglst_bind_svarlst
  (loc0: loc_t, s1as: s1arglst, s2vs: s2varlst, sub: &stasub_t)
  : s2varlst = let
  fun aux {n:nat}
    (s1as: list (s1arg, n), s2vs: list (s2var_t, n), sub: &stasub_t)
    : list (s2var_t, n) = case+ s1as of
    | cons (s1a, s1as) => let
        val+ cons (s2v, s2vs) = s2vs
        val s2v_new = s1arg_var_tr_srt (s1a, s2var_srt_get s2v)
        val () =
          if ~(s2var_srt_get s2v <= s2var_srt_get s2v_new) then begin
            prerr s1a.s1arg_loc;
            prerr ": error(2)";
            $Deb.debug_prerrf (": %s: s1arglst_bind_svarlst", @(THISFILENAME));
            prerr ": the ascribed sort for the static variable [";
            prerr s1a.s1arg_sym;
            prerr "] is incorrect.";
            prerr_newline ();
            $Err.abort {void} ()
          end
        val s2e_new = s2exp_var (s2v_new)
        val () = sub := stasub_add (sub, s2v, s2e_new)
      in
        cons (s2v_new, aux (s1as, s2vs, sub))
      end // end of [cons]
    | nil () => nil ()
  val ns1as = $Lst.list_length s1as and ns2vs = $Lst.list_length s2vs
in
  if ns1as <> ns2vs then begin
    prerr loc0;
    prerr ": error(2)";
    if ns1as < ns2vs then prerr ": more static arguments should be given.";
    if ns1as > ns2vs then prerr ": less static arguments should be given.";
    prerr_newline ();
    $Err.abort {s2varlst} ()
  end else begin
    aux (s1as, s2vs, sub)
  end
end // end of [s1arglst_bind_svarlst]
      
(* ****** ****** *)

fn s1explst_bind_svarlst
  (loc0: loc_t, s1es: s1explst, s2vs: s2varlst, sub: &stasub_t)
  : s2explst = let
  fun aux {n:nat} (
      s1es: list (s1exp, n)
    , s2vs: list (s2var_t, n)
    , sub: &stasub_t
    ) : s2explst = begin case+ s1es of
    | cons (s1e, s1es) => let
        val+ cons (s2v, s2vs) = s2vs; val s2e = s1exp_tr_up (s1e)
        val s2t_s2v = s2var_srt_get s2v and s2t_s2e = s2e.s2exp_srt
        val () =
          if ~(s2t_s2e <= s2t_s2v) then begin
            prerr s1e.s1exp_loc;
            prerr ": error(2)";
            $Deb.debug_prerrf (": %s: s1explst_bind_svarlst", @(THISFILENAME));
            prerr ": the sort of the static expression ["; prerr s1e;
            prerr "] is expected to be ["; prerr s2t_s2v;
            prerr "], but it is ["; prerr s2t_s2e; prerr "] instead.";
            prerr_newline ();
            $Err.abort {void} ()
          end
        val () = sub := stasub_add (sub, s2v, s2e)
      in
        list_cons (s2e, aux (s1es, s2vs, sub))
      end // end of [cons]
    | nil () => nil ()
  end // end of [aux]
  val ns1es = $Lst.list_length s1es and ns2vs = $Lst.list_length s2vs
in
  if ns1es <> ns2vs then begin
    prerr loc0;
    prerr ": error(2)";
    if ns1es < ns2vs then prerr ": more template arguments should be given.";
    if ns1es > ns2vs then prerr ": less template arguments should be given.";
    prerr_newline ();
    $Err.abort {s2explst} ()
  end else begin
    aux (s1es, s2vs, sub)
  end // end of [if]
end // end of [s1explst_bind_svarlst]

(* ****** ****** *)

fun d1exp_tr_ann (d1e0: d1exp, s2e0: s2exp): d2exp = begin
  case+ s2e0.s2exp_node of
  | S2Euni (s2vs, s2ps, s2e) => begin
    case+ d1e0.d1exp_node of
    | D1Elam_sta_ana (loc_arg, arg, body) => let
        var sub: stasub_t = stasub_nil
        val s2vs = s1arglst_bind_svarlst (loc_arg, arg, s2vs, sub)
        val (pf_s2expenv | ()) = the_s2expenv_push ()
        val () = the_s2expenv_add_svarlst s2vs
        val s2ps = s2explst_subst (sub, s2ps)
        val s2e = s2exp_subst (sub, s2e)
        val body = d1exp_tr_ann (body, s2e)
        val () = the_s2expenv_pop (pf_s2expenv | (*none*))
      in
        d2exp_lam_sta (d1e0.d1exp_loc, s2vs, s2ps, body)
      end
    | _ => let
        val d2e0 = d1exp_tr_ann (d1e0, s2e)
      in
        d2exp_lam_sta (d1e0.d1exp_loc, s2vs, s2ps, d2e0)
      end
    end // end of [S2Euni]
  | S2Efun (fc, lin1, s2fe, npf1, s2es_arg, s2e_res) => begin
    case+ d1e0.d1exp_node of
    | D1Elam_dyn (lin2, p1t_arg, d1e_body) => let // lin2 = 0
        val () = // check of linearity match
          if lin1 <> lin2 then begin
            prerr d1e0.d1exp_loc;
            prerr ": error(2)";
            $Deb.debug_prerrf (": %s: d1exp_tr_ann", @(THISFILENAME));
            if lin1 < lin2 then prerr ": linear function is given a nonlinear type.";
            if lin1 > lin2 then prerr ": nonlinear function is given a linear type.";
            prerr_newline ();
            $Err.abort {void} ()
          end
        var wths1es = WTHS1EXPLSTnil ()
        val p2t_arg = p1at_arg_tr (p1t_arg, wths1es)
        val () = // check for refval types
          if wths1explst_is_none wths1es then () else begin
            prerr p1t_arg.p1at_loc;
            prerr ": error(2)";
            prerr ": the function argument cannot be ascribed refval types.";
            prerr_newline ();
            $Err.abort {void} ()
          end
        var npf2: int = 0
        val p2ts_arg = (
          case+ p2t_arg.p2at_node of
          | P2Tlist (npf, p2ts) => (npf2 := npf; p2ts)
          | _ => cons (p2t_arg, nil ())
        ) : p2atlst
        val () = // check for pfarity match
          if npf1 <> npf2 then begin
            prerr d1e0.d1exp_loc;
            prerr ": error(2)";
            $Deb.debug_prerrf (": %s: d1exp_tr_ann", @(THISFILENAME));
            if npf1 < npf2 then prerr ": less proof arguments are expected.";
            if npf1 > npf2 then prerr ": more proof arguments are expected.";
            prerr_newline ();
            $Err.abort {void} ()
          end
        val p2ts_arg: p2atlst = let
          val ns2es = $Lst.list_length s2es_arg
          val np2ts = $Lst.list_length p2ts_arg
          fun aux {n:nat}
            (p2ts: list (p2at, n), s2es: list (s2exp, n)): list (p2at, n) =
            case+ p2ts of
            | cons (p2t, p2ts) => let
                val+ cons (s2e, s2es) = s2es
              in
                cons (p2at_ann (p2t.p2at_loc, p2t, s2e), aux (p2ts, s2es))
              end
            | nil () => nil ()            
        in
          if ns2es <> np2ts then begin
            prerr d1e0.d1exp_loc;
            prerr ": error(2)";
            $Deb.debug_prerrf (": %s: d1exp_tr_ann", @(THISFILENAME));
            if ns2es < np2ts then prerr ": less arguments are expected.";
            if ns2es > np2ts then prerr ": more arguments are expected.";
            prerr_newline ();
            $Err.abort {p2atlst} ()
          end else begin
            aux (p2ts_arg, s2es_arg)
          end
        end
        val (pf_env2 | ()) = trans2_env_push ()
        val () = let
          val s2vs = s2varlst_of_s2varlstord p2t_arg.p2at_svs
        in
          the_s2expenv_add_svarlst s2vs
        end
        val () = let
          val d2vs = d2varlst_of_d2varlstord p2t_arg.p2at_dvs
        in
          the_d2expenv_add_dvarlst d2vs
        end
        val d2e_body = d1exp_tr_ann (d1e_body, s2e_res)
        val () = trans2_env_pop (pf_env2 | (*none*))
        val loc_body = d2e_body.d2exp_loc
        val d2e_body = d2exp_ann_seff (loc_body, d2e_body, s2fe)
        val d2e_body = d2exp_ann_funclo (loc_body, d2e_body, fc)
      in
        d2exp_lam_dyn (d1e0.d1exp_loc, lin1, npf1, p2ts_arg, d2e_body)
      end
    | _ => d2exp_ann_type (d1e0.d1exp_loc, d1exp_tr d1e0, s2e0)
    end // end of [S2Efun]
  | _ => d2exp_ann_type (d1e0.d1exp_loc, d1exp_tr d1e0, s2e0)
end // end of [d1exp_tr_ann]

(* ****** ****** *)

fn m1acdef_tr
  (knd: int, d2m: d2mac_t, d1c: m1acdef): void = let
  val loc = d1c.m1acdef_loc and name = d1c.m1acdef_sym
  val (pf_d2expenv | ()) = the_d2expenv_push ()
  val () = aux (d2mac_arglst_get d2m) where {
    fun aux (args: macarglst): void = begin case+ args of
      | cons (arg, args) => let
          val () = case+ arg of
            | MACARGone (d2v) => the_d2expenv_add_dmac_var (d2v)
            | MACARGlst (_(*n*), d2vs) => the_d2expenv_add_dmac_varlst (d2vs)
        in
          aux args
        end // end of [cons]
      | nil () => ()
    end // end of [aux]
  } // end of [where]
  val () = if knd > 0 then macro_level_dec (loc)
  val def = d1exp_tr (d1c.m1acdef_def)
  val () = if knd > 0 then macro_level_inc (loc)
  val () = the_d2expenv_pop (pf_d2expenv | (*none*))
  val () = d2mac_def_set (d2m, def)
in
  // empty
end // end of [m1acdef_tr]

fun m1acdeflst_tr (knd: int, d1cs: m1acdeflst): void = let
  // knd: 0/1/2 => short/long/long rec
  fn aux1 (d1c: m1acdef):<cloptr1> d2mac_t = let
    val args = auxarglst d1c.m1acdef_arg where {
      fun auxarg (arg: $Syn.m0acarg): macarg = let
        fn f (x: $Syn.i0de): d2var_t = d2var_make (x.i0de_loc, x.i0de_sym)
      in
        case+ arg of
        | $Syn.M0ACARGone (x) => MACARGone (f x)
        | $Syn.M0ACARGlst (xs) => let
            val d2vs = $Lst.list_map_fun (xs, f); val n = $Lst.list_length d2vs
          in
            MACARGlst (n, d2vs)
          end
      end
      fun auxarglst (args: $Syn.m0acarglst): macarglst = begin case+ args of
        | cons (arg, args) => cons (auxarg arg, auxarglst args) | nil () => nil ()
      end // end of [auxarglst]
    } // end of [where]
    val def = d2exp_empty ($Loc.location_none)
    val d2m = d2mac_make (
      d1c.m1acdef_loc, d1c.m1acdef_sym, knd, args, def
    ) // end of [d2mac_make]
  in
    // [knd > 1] : recursive
    if knd > 1 then the_d2expenv_add_dmac_def (d2m); d2m
  end
  fun aux2 {n:nat}
    (d2ms: list (d2mac_t, n), d1cs: list (m1acdef, n))
    : void = begin case+ d2ms of
    | cons (d2m, d2ms) => let
        val+ cons (d1c, d1cs) = d1cs
        val knd = d2mac_kind_get (d2m)
      in
        m1acdef_tr (knd, d2m, d1c);
        // [knd <= 1] : non-recursive
        if knd <= 1 then the_d2expenv_add_dmac_def (d2m);
        aux2 (d2ms, d1cs)
      end
    | nil () => ()
  end // end of [aux2]
  val d2ms = $Lst.list_map_cloptr (d1cs, aux1)
in
  aux2 (d2ms, d1cs)
end // end of [m1acdeflst_tr]

(* ****** ****** *)

viewtypedef d2cstlst_vt = List_vt d2cst_t

fun d1exp_arity_check (d1e: d1exp, ns: List int): bool = let
  fn* aux1 (d1e: d1exp, ns: List int): bool = begin
    case+ ns of list_cons (n, ns) => aux2 (d1e, n, ns) | list_nil () => true
  end

  and aux2 (d1e: d1exp, n: int, ns: List int): bool = begin
(*
    prerr "d1exp_arith_check: n = "; prerr n; prerr_newline ();
    prerr "d1exp_arith_check: d1e = "; prerr_d1exp d1e; prerr_newline ();
*)
    case+ d1e.d1exp_node of
    | D1Elam_dyn (_(*lin*), p1t, d1e) => let
        val narg = (case+ p1t.p1at_node of
          | P1Tlist (_(*npf*), p1ts) => $Lst.list_length (p1ts) | _ => 1
        ) : int
      in
        if (n = narg) then aux1 (d1e, ns) else false
      end // end of [D1Elam_dyn]
    | D1Elam_met (_(*loc*), _(*met*), d1e) => aux2 (d1e, n, ns)
    | D1Elam_sta_ana (_(*loc*), _(*s1as*), d1e) => aux2 (d1e, n, ns)
    | D1Elam_sta_syn (_(*loc*), _(*s1qs*), d1e) => aux2 (d1e, n, ns)
    | _ => false
  end
in
  aux1 (d1e, ns)
end // end of [d1exp_arity_check]

fn i1mpdec_tr_d2cst_select
  (d1c: i1mpdec, d2is: d2itemlst): d2cst_t = let
  fun aux (d2is: d2itemlst)
    :<cloptr1> d2cstlst_vt = begin case+ d2is of
    | list_cons (d2i, d2is) => begin case+ d2i of
      | D2ITEMcst d2c => let
          val ns = d2cst_arilst_get (d2c)
          val ismat = d1exp_arity_check (d1c.i1mpdec_def, ns)
        in 
          if (ismat) then list_vt_cons (d2c, aux d2is) else aux d2is
        end
      | _ => aux d2is
      end // end of [list_cons]
    | list_nil () => list_vt_nil ()
  end // end of [aux]
  val d2cs = aux (d2is)
in
  case+ d2cs of
  | ~list_vt_cons (d2c1, d2cs) => begin case+ d2cs of
    | ~list_vt_nil () => d2c1
    | ~list_vt_cons (d2c2, d2cs) => let
        val qid = d1c.i1mpdec_qid
        val q = qid.impqi0de_qua and id = qid.impqi0de_sym
      in
        $Loc.prerr_location d1c.i1mpdec_loc;
        prerr ": error(2)"; prerr ": the dynamic constants [";
        prerr d2c1; prerr "] and [";
        prerr d2c2; prerr "] cannot be resolved for [";
        $Syn.prerr_d0ynq q; $Sym.prerr_symbol id; prerr "].";
        prerr_newline ();
        $Lst.list_vt_free (d2cs);
        $Err.abort {d2cst_t} ()
      end // end of [list_vt_cons]
    end // end of [list_vt_cons]
  | ~list_vt_nil () => let
      val qid = d1c.i1mpdec_qid
      val q = qid.impqi0de_qua and id = qid.impqi0de_sym
    in
      $Loc.prerr_location d1c.i1mpdec_loc;
      prerr ": error(2)";
      prerr ": no dynamic constant can be found for [";
      $Syn.prerr_d0ynq q; $Sym.prerr_symbol id; prerr "].";
      prerr_newline ();
      $Err.abort {d2cst_t} ()
    end // end of [list_vt_nil]
end // end of [i1mpdec_tr_d2cst_select]

fn i1mpdec_tr
  (loc0: loc_t, i1mparg: s1arglstlst, d1c: i1mpdec): i2mpdec = let
  val t1mparg = d1c.i1mpdec_tmparg
  val () = case+ (i1mparg, t1mparg) of
    | (cons _, cons _) => begin
        prerr loc0; prerr ": error(2)";
        prerr ": template implementation and instantiation may not be combined.";
        prerr_newline ();
        $Err.abort {void} ()
      end // end of [cons, cons]
    | (_, _) => ()
  val qid = d1c.i1mpdec_qid
  val q = qid.impqi0de_qua and id = qid.impqi0de_sym
  val d2c = begin
    case+ the_d2expenv_find_qua (q, id) of
    | ~Some_vt d2i => begin case+ d2i of
      | D2ITEMcst d2c => d2c
      | D2ITEMsym (d2is) => i1mpdec_tr_d2cst_select (d1c, d2is)
      | _ => begin
          prerr d1c.i1mpdec_loc; prerr ": error(2)";
          $Deb.debug_prerrf (": %s: i1mpdec_tr", @(THISFILENAME));
          prerr ": the identifier [";
          prerr q; prerr id;
          prerr "] should refer to a dynamic constant but it does not.";
          prerr_newline ();
          $Err.abort {d2cst_t} ()
        end // end of [_]
      end // end of [Some_vt]
    | ~None_vt () => begin
        prerr d1c.i1mpdec_loc;
        prerr ": error(2)";
        $Deb.debug_prerrf (": %s: i1mpdec_tr", @(THISFILENAME));
        prerr ": the dynamic identifier [";
        prerr q; prerr id;
        prerr "] is unrecognized.";
        prerr_newline ();
        $Err.abort {d2cst_t} ()
      end // end of [None_vt]
  end // end of [val]
(*
  // automatic instantiation is not supported as it can readily lead
  // to confusion as for whether an implementation is actually compiled.
  fun aux1
    (s2vpss: s2qualst, s2e: s2exp, out: &s2qualst): s2exp = begin
    case+ s2vpss of
    | cons (s2vps, s2vpss) => let
        val (sub, s2vs) = stasub_extend_svarlst (stasub_nil, s2vps.0)
        val s2ps = s2explst_subst (sub, s2vps.1)
        val s2e = s2exp_subst (sub, s2e)
      in
        out := @(s2vs, s2ps) :: out; aux1 (s2vpss, s2e, out)
      end
    | nil () => (out := s2qualst_reverse out; s2e)
  end // end of [aux1]
*)
  fun aux2_imp (
      loc0: loc_t
    , args: s1arglstlst
    , s2vpss: s2qualst
    , s2e: s2exp
    , out_imp: &s2qualst
    ) :<cloptr1> s2exp = begin case+ args of
    | cons (arg, args) => begin case+ s2vpss of
      | cons (s2vps, s2vpss) => let
          var sub: stasub_t = stasub_nil
          val s2vs = s1arglst_bind_svarlst (loc0, arg, s2vps.0, sub)
          val () = the_s2expenv_add_svarlst s2vs
          val s2ps = s2explst_subst (sub, s2vps.1)
          val s2e = s2exp_subst (sub, s2e)
          val () = out_imp := @(s2vs, s2ps) :: out_imp
        in
          aux2_imp (loc0, args, s2vpss, s2e, out_imp)
        end // end of [cons]
      | nil () => begin
          prerr loc0;
          prerr ": error(2)";
          $Deb.debug_prerrf (": %s: i1mpdec_tr: aux2_imp", @(THISFILENAME));
          prerr ": the implementation for [";
          prerr q; prerr id;
          prerr "] should be applied to less template arguments.";
          prerr_newline ();
          $Err.abort {s2exp} ()
        end // end of [nil]
      end // end of [cons]
    | nil () => let
        val () = case+ s2vpss of
          | cons _ => begin
              prerr loc0;
              prerr ": error(2)";
              $Deb.debug_prerrf (": %s: i1mpdec_tr: aux2_imp", @(THISFILENAME));
              prerr ": the implementation for [";
              prerr q; prerr id;
              prerr "] should be applied to more template arguments.";
              prerr_newline ();
              $Err.abort {void} ()
            end // end of [cons]
          | nil () => ()
      in
        s2e // no automatic instantiation
      end // end of [nil]
  end // end of [aux2_imp]
  fun aux2_tmp (
      loc0: loc_t
    , args: s1explstlst
    , s2vpss: s2qualst
    , s2e: s2exp
    , out_tmparg: &s2explstlst
    , out_tmpgua: &s2explstlst
    ) :<cloptr1> s2exp = begin case+ args of
    | cons (arg, args) => begin case+ s2vpss of
      | cons (s2vps, s2vpss) => let
          var sub: stasub_t = stasub_nil
          val s2es = s1explst_bind_svarlst (loc0, arg, s2vps.0, sub)
          val s2ps = s2explst_subst (sub, s2vps.1)
          val s2e = s2exp_subst (sub, s2e)
          val () = out_tmparg := s2es :: out_tmparg
          val () = out_tmpgua := s2ps :: out_tmpgua
        in
          aux2_tmp (loc0, args, s2vpss, s2e, out_tmparg, out_tmpgua)
        end // end of [cons]
      | nil () => begin
          prerr loc0;
          prerr ": error(2)";
          $Deb.debug_prerrf (": %s: i1mpdec_tr: aux2_tmp", @(THISFILENAME));
          prerr ": the implementation for [";
          prerr q; prerr id;
          prerr "] should be applied to less template arguments.";
          prerr_newline ();
          $Err.abort {s2exp} ()
        end // end of [nil]
      end // end of [cons]
    | nil () => let
        val () = case+ s2vpss of
          | cons _ => begin
              prerr loc0;
              prerr ": error(2)";
              $Deb.debug_prerrf (": %s: i1mpdec_tr: aux2_tmp", @(THISFILENAME));
              prerr ": the implementation for [";
              prerr q; prerr id;
              prerr "] should be applied to more template arguments.";
              prerr_newline ();
              $Err.abort {void} ()
            end // end of [cons]
          | nil () => ()
      in
        s2e // no automatic instantiation
      end // end of [nil]
  end // end of [aux2_tmp]
  val loc_id = qid.impqi0de_loc
  val decarg = d2cst_decarg_get d2c and s2e_d2c = d2cst_typ_get d2c
  val () = begin case+ decarg of
    | cons _ => begin case+ (i1mparg, t1mparg) of
      | (nil (), nil ()) => begin
          prerr loc0; prerr ": error(2)";
          prerr ": the dynamic constant [";
          prerr d2c; prerr "] requires a template implemenation";
          prerr_newline ();
          $Err.abort {void} ()
        end // end of [nil, nil]
      | (_, _) => ()
      end // end of [cons]
    | _ => ()
  end // end of [val]
  var out_imp: s2qualst = nil ()
  var out_tmparg: s2explstlst = nil ()
  var out_tmpgua: s2explstlst = nil ()
  val s2e = s2e_d2c
  val (pf_s2expenv | ()) = the_s2expenv_push ()
  val () = begin
    case+ decarg of cons _ => template_level_inc () | nil _ => ()
  end // end of [val]
  val s2e = (case+ i1mparg of
    | cons _ => aux2_imp (loc_id, i1mparg, decarg, s2e, out_imp)
    | nil () => s2e
  ) : s2exp
  val s2e = (case+ t1mparg of
    | cons _ => aux2_tmp
        (loc_id, t1mparg, decarg, s2e, out_tmparg, out_tmpgua)
    | nil () => s2e
  ) : s2exp        
  // val out_imp = $Lst.list_reverse (out_imp) // a serious bug!!!
  val out_imp = s2qualst_reverse (out_imp)
  val () = s2qualst_tmplev_set (out_imp, template_level_get ())
  val out_tmparg = $Lst.list_reverse (out_tmparg: s2explstlst)
  val out_tmpgua = $Lst.list_reverse (out_tmpgua: s2explstlst)
  val d2e = d1exp_tr_ann (d1c.i1mpdec_def, s2e)
  val () = begin
    case+ decarg of cons _ => template_level_dec () | nil _ => ()
  end // end of [val]
  val () = the_s2expenv_pop (pf_s2expenv | (*none*))
  val () = d2cst_def_set (d2c, Some d2e)
in
  i2mpdec_make (
    d1c.i1mpdec_loc, loc_id, d2c, out_imp, out_tmparg, out_tmpgua, d2e
  ) // end of [i2mpdec_make]
end // end of [i1mpdec_tr]

(* ****** ****** *)

fn s1taload_tr
  (loc0: loc_t,
   idopt: symopt_t, fil: fil_t, loaded: int,
   d1cs: d1eclst)
  : d2ec = let
(*
  val () = begin case+ idopt of
    | Some id => begin
        print "s1taload_tr: staid = "; print id; print_newline ()
      end
    | None () => begin
        print "s1taload_tr: staid = None"; print_newline ()
      end
  end // end of [val]
  val () = begin
    print "s1taload_tr: filename = "; print fil; print_newline ()
  end // end of [val]
*)
  val fil_sym = $Fil.filename_full_sym fil
  val od2cs = (
    case+ d2eclst_namespace_find fil_sym of
    | ~Some_vt _ => None () | ~None_vt _ => let
        val (pf_token | ()) = staload_level_inc ()
        val () = trans2_env_save ()
        val d2cs = d1eclst_tr d1cs
        val () = trans2_env_namespace_add_top (fil_sym)
        val () = trans2_env_restore ()
        val () = staload_level_dec (pf_token | (*none*))
        val () = d2eclst_namespace_add (fil_sym, d2cs)
      in
        Some d2cs
      end // end of [None_vt]
  ) : Option d2eclst
  val () = case+ idopt of
    | Some id => the_s2expenv_add (id, S2ITEMfil fil)
    | None () => begin
        $NS.the_namespace_add fil_sym (* opened file *)
      end
in
  d2ec_staload (loc0, fil, od2cs)
end // end of [s1taload_tr]

(* ****** ****** *)

implement d1ec_tr (d1c0) = begin
  case+ d1c0.d1ec_node of
  | D1Cnone () => d2ec_none (d1c0.d1ec_loc)
  | D1Clist d1cs => begin
      d2ec_list (d1c0.d1ec_loc, d1eclst_tr d1cs)
    end
  | D1Csymintr ids => begin
      symintr_tr (ids); d2ec_none (d1c0.d1ec_loc)
    end
  | D1Csymelim ids => begin
      symelim_tr (ids); d2ec_none (d1c0.d1ec_loc)
    end
  | D1Ce1xpdef (id, def) => begin
      the_s2expenv_add (id, S2ITEMe1xp def);
      the_d2expenv_add (id, D2ITEMe1xp def);
      d2ec_none (d1c0.d1ec_loc)
    end
  | D1Cdatsrts (para, d1cs) => begin
      d1atsrtdeclst_tr d1cs; d2ec_none (d1c0.d1ec_loc)
    end
  | D1Csrtdefs d1cs => begin
      s1rtdeflst_tr d1cs; d2ec_none (d1c0.d1ec_loc)
    end
  | D1Cstacons (absknd, d1cs) => begin
      s1taconlst_tr (absknd, d1cs); d2ec_none (d1c0.d1ec_loc)
    end
  | D1Cstacsts d1cs => begin
      s1tacstlst_tr d1cs; d2ec_none (d1c0.d1ec_loc)
    end
  | D1Cstavars d1cs => let
      val d2cs = s1tavarlst_tr d1cs
    in
      d2ec_stavars (d1c0.d1ec_loc, d2cs)
    end
  | D1Csexpdefs (os1t, d1cs) => begin
      s1expdeflst_tr (s1rtopt_tr os1t, d1cs);
      d2ec_none (d1c0.d1ec_loc)
    end
  | D1Csaspdec (d1c) => begin
      d2ec_saspdec (d1c0.d1ec_loc, s1aspdec_tr d1c)
    end
  | D1Cdatdecs (dtk, d1cs_dat, d1cs_def) => let
      val s2cs = d1atdeclst_tr (dtk, d1cs_dat, d1cs_def)
    in
      d2ec_datdec (d1c0.d1ec_loc, dtk, s2cs)
    end
  | D1Cexndecs (d1cs) => let
      val d2cs = e1xndeclst_tr d1cs
    in
      d2ec_exndec (d1c0.d1ec_loc, d2cs)
    end
  | D1Cdcstdecs (dck, decarg, d1cs) => let
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val s2vpss = s1qualstlst_tr (decarg)
      val d2cs = d1cstdeclst_tr (dck, s2vpss, d1cs)
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
    in
      d2ec_dcstdec (d1c0.d1ec_loc, dck, d2cs)
    end
  | D1Coverload (id, qid) => begin
      overload_tr (id, qid); d2ec_none (d1c0.d1ec_loc)
    end
  | D1Cextype (name, s1e_def) => let
      val s2e_def = s1exp_tr_dn_viewt0ype s1e_def
    in
      d2ec_extype (d1c0.d1ec_loc, name, s2e_def)
    end
  | D1Cextval (name, d1e_def) => begin
      d2ec_extval (d1c0.d1ec_loc, name, d1exp_tr d1e_def)
    end
  | D1Cextcode (pos, code) => begin
      d2ec_extcode (d1c0.d1ec_loc, pos, code)
    end
  | D1Cvaldecs (valknd, d1cs) => let
      val d2cs = v1aldeclst_tr (false(*isrec*), d1cs)
    in
      d2ec_valdecs (d1c0.d1ec_loc, valknd, d2cs)
    end
  | D1Cvaldecs_par (d1cs) => let
      val d2cs = v1aldeclst_tr (false(*isrec*), d1cs)
    in
      d2ec_valdecs_par (d1c0.d1ec_loc, d2cs)
    end
  | D1Cvaldecs_rec (d1cs) => let
      val d2cs = v1aldeclst_tr (true(*isrec*), d1cs)
    in
      d2ec_valdecs_rec (d1c0.d1ec_loc, d2cs)
    end
  | D1Cfundecs (funknd, decarg, d1cs) => let
      val (pf_s2expenv | ()) = the_s2expenv_push ()
      val () = begin
        case+ decarg of cons _ => template_level_inc () | nil _ => ()
      end // end of [val]
      val s2vpss = s1qualstlst_tr (decarg)
      val () = s2qualst_tmplev_set (s2vpss, template_level_get ())
      val level = d2var_current_level_get ()
      val d2cs = f1undeclst_tr (funknd, level, s2vpss, d1cs)
      val () = the_s2expenv_pop (pf_s2expenv | (*none*))
      val () = begin
        case+ decarg of cons _ => template_level_dec () | nil _ => ()
      end // end of [val]
    in
      d2ec_fundecs (d1c0.d1ec_loc, s2vpss, funknd, d2cs)
    end
  | D1Cvardecs (d1cs) => let
      val d2cs = v1ardeclst_tr d1cs
    in
      d2ec_vardecs (d1c0.d1ec_loc, d2cs)
    end
  | D1Cmacdefs (knd, d1cs) => begin
       // knd: 0/1/2 => short/long/long rec
       m1acdeflst_tr (knd, d1cs); d2ec_none (d1c0.d1ec_loc)
    end
  | D1Cimpdec (i1mparg, d1c) => let
      val loc0 = d1c0.d1ec_loc
      val d2c = i1mpdec_tr (loc0, i1mparg, d1c)
    in
      d2ec_impdec (loc0, d2c)
    end // end of [D1Cimpdec]
  | D1Clocal (d1cs_head, d1cs_body) => let
      val (pf1_env | ()) = trans2_env_push ()
      val d2cs_head = d1eclst_tr d1cs_head
      val (pf2_env | ()) = trans2_env_push ()
      val d2cs_body = d1eclst_tr d1cs_body
      val () = trans2_env_localjoin (pf1_env, pf2_env | (*none*))
    in
      d2ec_local (d1c0.d1ec_loc, d2cs_head, d2cs_body)
    end
  | D1Cdynload (fil) => d2ec_dynload (d1c0.d1ec_loc, fil)
  | D1Cstaload (idopt, fil, loaded, d1cs) => begin
      s1taload_tr (d1c0.d1ec_loc, idopt, fil, loaded, d1cs)
    end
end // end of [d1ec_tr]

(* ****** ****** *)

// [list_map_fun] is tail-recursive!
implement d1eclst_tr (d1cs) = $Lst.list_map_fun (d1cs, d1ec_tr)

(* ****** ****** *)

(* end of [ats_trans2_dyn.dats] *)
