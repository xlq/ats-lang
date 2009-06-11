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

// Time: December 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

macdef fprint_label = $Lab.fprint_label
macdef fprint_symbol = $Sym.fprint_symbol

(* ****** ****** *)

implement fprint_d2sym (pf | out, d2s) = begin
  $Syn.fprint_d0ynq (pf | out, d2s.d2sym_qua);
  fprint_symbol (pf | out, d2s.d2sym_sym)
end

implement print_d2sym (d2s) = print_mac (fprint_d2sym, d2s)
implement prerr_d2sym (d2s) = prerr_mac (fprint_d2sym, d2s)

(* ****** ****** *)

implement fprint_d2item (pf | out, d2i) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ d2i of
  | D2ITEMcon d2cs => begin
      strpr "D2ITEMcon("; fprint_d2conlst (pf | out, d2cs); strpr ")"
    end
  | D2ITEMcst d2c => begin
      strpr "D2ITEMcst("; fprint_d2cst (pf | out, d2c); strpr ")"
    end
  | D2ITEMe1xp e1xp => begin
      strpr "D2ITEMe1xp("; fprint_e1xp (pf | out, e1xp); strpr ")"
    end
  | D2ITEMmacdef d2m => begin
      strpr "D2ITEMmacdef("; fprint_d2mac (pf | out, d2m); strpr ")"
    end
  | D2ITEMmacvar d2v => begin
      strpr "D2ITEMmacvar("; fprint_d2var (pf | out, d2v); strpr ")"
    end
  | D2ITEMsym d2is => begin
      fprint1_string (pf | out, "D2ITEMsym(...)")
    end
  | D2ITEMvar d2v => begin
      strpr "D2ITEMvar("; fprint_d2var (pf | out, d2v); strpr ")"
    end
end // end of [fprint_d2item]

implement print_d2item (d2i) = print_mac (fprint_d2item, d2i)
implement prerr_d2item (d2i) = prerr_mac (fprint_d2item, d2i)

//

implement fprint_d2itemlst {m} (pf | out, d2is) = let
  fun aux (out: &FILE m, i: int, d2is: d2itemlst): void =
    case+ d2is of
    | cons (d2i, d2is) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_d2item (pf | out, d2i); aux (out, i+1, d2is)
      end
    | nil () => ()
in
  aux (out, 0, d2is)
end // end of [fprint_d2itemlst]

implement print_d2itemlst (d2is) = print_mac (fprint_d2itemlst, d2is)
implement prerr_d2itemlst (d2is) = prerr_mac (fprint_d2itemlst, d2is)

(* ****** ****** *)

implement fprint_p2at (pf | out, p2t) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ p2t.p2at_node of
  | P2Tann (p2t, s2e) => begin
      strpr "P2Tann(";
      fprint_p2at (pf | out, p2t);
      strpr "; ";
      fprint_s2exp (pf | out, s2e);
      strpr ")"
    end
  | P2Tany () => fprint1_string (pf | out, "P2Tany()")
  | P2Tas (refknd, d2v, p2t) => begin
      strpr "P2Tas(";
      if (refknd > 0) then strpr "!";
      fprint_d2var (pf | out, d2v);
      strpr "; ";
      fprint_p2at (pf | out, p2t);
      strpr ")"
    end // end of [P2Tas]
  | P2Tbool b => begin
      strpr "P2Tbool("; fprint1_bool (pf | out, b); strpr ")"
    end
  | P2Tchar c => begin
      strpr "P2Tchar("; fprint1_char (pf | out, c); strpr ")"
    end
  | P2Tcon (freeknd, d2c, s2qs, s2e, npf, p2ts) => begin
      strpr "P2Tcon(";
      if (freeknd < 0) then strpr "~";
      fprint_d2con (pf | out, d2c);
      strpr "; ";
      fprint_p2atlst (pf | out, p2ts);
      strpr ")"
    end
  | P2Tempty () => begin
      fprint1_string (pf | out, "P2Tempty()")
    end
  | P2Texist (s2vs, p2t) => begin
      strpr "P2Texist(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_p2at (pf | out, p2t);
      strpr ")"
    end
  | P2Tfloat f(*string*) => begin
      strpr "P2Tfloat("; fprint1_string (pf | out, f); strpr ")"
    end
  | P2Tint (str, _(*intinf*)) => begin
      strpr "P2Tint("; fprint1_string (pf | out, str); strpr ")"
    end
  | P2Tlist (npf, p2ts) => begin
      strpr "P2Tlist(";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_p2atlst (pf | out, p2ts);
      strpr ")"
    end // end of [P2Tlist]
  | P2Tlst p2ts => begin
      strpr "P2Tlst("; fprint_p2atlst (pf | out, p2ts); strpr ")"
    end
  | P2Trec (recknd, npf, lp2ts) => begin
      strpr "P2Trec(";
      fprint1_int (pf | out, recknd);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_labp2atlst (pf | out, lp2ts);
      strpr ")"
    end // end of [P2Trec]
  | P2Tstring str => begin
      strpr "P2Tstring(\""; fprint1_string (pf | out, str); strpr "\")"
    end // end of [P2Tstring]
  | P2Tvar (refknd, d2v) => begin
      strpr "P2Tvar(";
      if (refknd > 0) then strpr "!";
      fprint_d2var (pf | out, d2v);
      strpr ")"
    end // end of [P2Tvar]
  | P2Tvbox (d2v) => begin
      strpr "P2Tvbox("; fprint_d2var (pf | out, d2v); strpr ")"
    end // end of [P2Tvbox]
(*
  | _ => begin
      prerr "Internal Error: ";
      prerr "[fprint_p2at]: the pattern at [";
      prerr p2t.p2at_loc;
      prerr "] is not supported yet";
      prerr_newline ();
      exit (1)
    end
*)
end // end of [fprint_p2at]

implement fprint_p2atlst {m} (pf | out, p2ts) = let
  fun aux (out: &FILE m, i: int, p2ts: p2atlst): void =
    case+ p2ts of
    | cons (p2t, p2ts) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_p2at (pf | out, p2t); aux (out, i+1, p2ts)
      end
    | nil () => ()
in
  aux (out, 0, p2ts)
end // end of [fprint_p2atlst]

implement fprint_labp2atlst {m} (pf | out, lp2ts) = let
  fun aux (out: &FILE m, i: int, lp2ts: labp2atlst): void = let
    macdef strpr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ lp2ts of
    | LABP2ATLSTcons (l, p2t, lp2ts) => begin
        if i > 0 then strpr ", ";
        fprint_label (pf | out, l); strpr "= "; fprint_p2at (pf | out, p2t);
        aux (out, i+1, lp2ts)
      end
    | LABP2ATLSTnil () => ()
    | LABP2ATLSTdot () => begin
        if i > 0 then strpr ", "; fprint1_string (pf | out, "...")
      end
  end // end of [aux]
in
  aux (out, 0, lp2ts)
end // end of [fprint_labp2atlst]

(* ****** ****** *)

implement print_p2at (p2t) = print_mac (fprint_p2at, p2t)
implement prerr_p2at (p2t) = prerr_mac (fprint_p2at, p2t)

implement print_p2atlst (p2ts) = print_mac (fprint_p2atlst, p2ts)
implement prerr_p2atlst (p2ts) = prerr_mac (fprint_p2atlst, p2ts)

(* ****** ****** *)

implement fprint_i2nvarg (pf | out, i2nv) = let
  val () = fprint_d2var (pf | out, i2nv.i2nvarg_var)
  val () = fprint1_string (pf | out, ": ")
  val () = fprint_s2expopt (pf | out, i2nv.i2nvarg_typ)
in
  // empty
end

implement fprint_i2nvarglst {m} (pf | out, args) = let
  fun aux (out: &FILE m, i: int, args: i2nvarglst): void =
    case+ args of
    | cons (arg, args) => begin
        if (i > 0) then fprint1_string (pf | out, ", ");
        fprint_i2nvarg (pf | out, arg); aux (out, i + 1, args)
      end
    | nil () => ()
  // end of [aux]
in
  aux (out, 0, args)
end // end of [fprint_i2nvarglst]

implement fprint_i2nvresstate (pf | out, res) = let
  val () = fprint1_string (pf | out, "[");
  val () = fprint_s2varlst (pf | out, res.i2nvresstate_svs);
  val () = fprint1_string (pf | out, "; ");
  val () = fprint_s2explst (pf | out, res.i2nvresstate_gua);
  val () = fprint1_string (pf | out, "] (");
  val () = fprint_i2nvarglst (pf | out, res.i2nvresstate_arg);
  val () = fprint_string (pf | out, ")")
in
  // empty
end // end of [fprint_i2nvresstate]

//

implement print_i2nvarglst (args) = print_mac (fprint_i2nvarglst, args)
implement prerr_i2nvarglst (args) = prerr_mac (fprint_i2nvarglst, args)

implement print_i2nvresstate (res) = print_mac (fprint_i2nvresstate, res)
implement prerr_i2nvresstate (res) = prerr_mac (fprint_i2nvresstate, res)

(* ****** ****** *)

implement fprint_d2exparg (pf | out, d2a) = begin
  case+ d2a of
  | D2EXPARGsta s2as => begin
      fprint_s2exparglst (pf | out, s2as)
    end
  | D2EXPARGdyn (_(*loc_arg*), _(*npf*), d2es) => begin
      fprint_d2explst (pf | out, d2es)
    end
end // end of [fprint_d2exparg]

implement print_d2exparg (arg) = print_mac (fprint_d2exparg, arg)
implement prerr_d2exparg (arg) = prerr_mac (fprint_d2exparg, arg)

implement fprint_d2exparglst {m} (pf | out, d2as) = let
  fun aux (out: &FILE m, i: int, d2as: d2exparglst): void =
    case+ d2as of
    | cons (d2a, d2as) => begin
        if (i > 0) then fprint1_string (pf | out, "; ");
        fprint_d2exparg (pf | out, d2a); aux (out, i+1, d2as)
      end
    | nil () => ()
in
  aux (out, 0, d2as)
end // end of [fprint_d2exparglst]

implement print_d2exparglst (args) = print_mac (fprint_d2exparglst, args)
implement prerr_d2exparglst (args) = prerr_mac (fprint_d2exparglst, args)

(* ****** ****** *)

implement fprint_d2exp (pf | out, d2e0) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ d2e0.d2exp_node of
  | D2Eann_seff (d2e, s2fe) => begin
      strpr "D2Eann_seff(";
      fprint_d2exp (pf | out, d2e);
      strpr "; ";
      fprint_s2eff (pf | out, s2fe);
      strpr ")"
    end // end of [D2Eann_seff]
  | D2Eann_funclo (d2e, fc) => begin
      strpr "D2Eann_funclo(";
      fprint_d2exp (pf | out, d2e);
      strpr "; ";
      $Syn.fprint_funclo (pf | out, fc);
      strpr ")"
    end // end of [D2Eann_funclo]
  | D2Eann_type (d2e, s2e) => begin
      strpr "D2Eann_type(";
      fprint_d2exp (pf | out, d2e);
      strpr "; ";
      fprint_s2exp (pf | out, s2e);
      strpr ")"
    end // end of [D2Eann_type]
  | D2Eapps (d2e_fun, d2as_arg) => begin
      strpr "D2Eapps(";
      fprint_d2exp (pf | out, d2e_fun);
      strpr "; ";
      fprint_d2exparglst (pf | out, d2as_arg);
      strpr ")"
    end // end of [D2Eapps]
  | D2Earrinit (s2e_elt, od2e_asz, d2es_elt) => begin
      strpr "D2Earrinit(";
      fprint_s2exp (pf | out, s2e_elt);
      strpr "; ";
      begin case+ od2e_asz of
      | Some d2e => fprint_d2exp (pf | out, d2e) | None () => ()
      end;
      strpr "; ";
      fprint_d2explst (pf | out, d2es_elt);
      strpr ")"
    end // end of [D2Earrsize]
  | D2Earrsize (os2e_elt, d2es_elt) => begin
      strpr "D2Earrsize(";
      begin case+ os2e_elt of
      | Some s2e => fprint_s2exp (pf | out, s2e) | None () => ()
      end;
      strpr "; ";
      fprint_d2explst (pf | out, d2es_elt);
      strpr ")"
    end // end of [D2Earrsize]
  | D2Earrsub (d2s, d2e_arr, _(*loc_ind*), d2ess_ind) => begin
      strpr "D2Earrsub(";
      fprint_d2sym (pf | out, d2s);
      strpr "; ";
      fprint_d2exp (pf | out, d2e_arr);
      strpr "; ";
      fprint1_string (pf | out, "...");
      strpr ")"
    end // end of [D2Earrsub]
  | D2Eassgn (d2e_lval, d2e_val) => begin
      strpr "D2Eassgn(";
      fprint_d2exp (pf | out, d2e_lval);
      strpr "; ";
      fprint_d2exp (pf | out, d2e_val);
      strpr ")"
    end // end of [D2Eassgn]
  | D2Ecaseof _ => begin
      strpr "D2Ecaseof("; fprint1_string (pf | out, "..."); strpr ")"
    end // end of [D2Ecaseof]
  | D2Echar c => begin
      strpr "D2Echar("; fprint1_char (pf | out, c); strpr ")"
    end // end of [D2Echar]
  | D2Econ (d2c, s2as, npf, d2es) => begin
      strpr "D2Econ(";
      fprint_d2con (pf | out, d2c);
      strpr "; ";
      fprint_d2explst (pf | out, d2es);
      strpr ")"
    end // end of [D2Econ]
  | D2Ecst d2c => begin
      strpr "D2Ecst("; fprint_d2cst (pf | out, d2c); strpr ")"
    end // en dof [D2Ecst]
  | D2Ecrypt (knd, d2e) => begin
      strpr "D2Ecrypt(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_d2exp (pf | out, d2e);
      strpr ")"
    end // end of [D2Ecrypt]
  | D2Elazy_delay (d2e) => begin
      strpr "D2Elazy_delay("; fprint_d2exp (pf | out, d2e); strpr ")"
    end // end of [D2Elazy_delay]
  | D2Elazy_vt_delay (d2e_eval, d2e_free) => begin
      strpr "D2Elazy_vt_delay(";
      fprint_d2exp (pf | out, d2e_eval);
      strpr "; ";
      fprint_d2exp (pf | out, d2e_free);
      strpr ")"
    end // end of [D2Elazy_vt_delay]
  | D2Ederef d2e => begin
      strpr "D2Ederef("; fprint_d2exp (pf | out, d2e); strpr ")"
    end // end of [D2Ederef]
  | D2Edynload (fil) => begin
      strpr "D2Edynload("; $Fil.fprint_filename (pf | out, fil); strpr ")"
    end // end of [D2Edynload]
  | D2Eeffmask (effs, d2e) => begin
      strpr "D2Eeffmask(";
      $Eff.fprint_effectlst (pf | out, effs);
      strpr "; ";
      fprint_d2exp (pf | out, d2e);
      strpr ")"
    end // end of [D2Eeffmask]
  | D2Eempty () => begin
      fprint1_string (pf | out, "D2Eempty()")
    end // end of [D2Eempty]
  | D2Eexist (s2a, d2e) => begin
      strpr "D2Eexist(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d2exp (pf | out, d2e);
      strpr ")"
    end // end of [D2Eexist]
  | D2Eextval (s2e, code) => begin
      strpr "D2Eextval(";
      fprint_s2exp (pf | out, s2e);
      strpr "; ";
      strpr "\"";
      fprint1_string (pf | out, code);
      strpr "\"";
      strpr ")"
    end // end of [D2Eextval]
  | D2Efix (d2v_fun, d2e_body) => begin
      strpr "D2Efix(";
      fprint_d2var (pf | out, d2v_fun);
      strpr "; ";
      fprint_d2exp (pf | out, d2e_body);
      strpr ")"
    end // end of [D2Efix]
  | D2Efloat f(*string*) => begin
      strpr "D2Efloat("; fprint1_string (pf | out, f); strpr ")"
    end // end of [D2Efloat]
  | D2Efloatsp f(*string*) => begin
      strpr "D2Efloatsp("; fprint1_string (pf | out, f); strpr ")"
    end // end of [D2Efloatsp]
  | D2Efoldat (sarg, d2e) => begin
      strpr "D2Efoldat("; fprint_d2exp (pf | out, d2e); strpr ")"
    end // end of [D2Efoldat]
  | D2Efor (inv, ini, test, post, body) => begin
      strpr "D2Efor(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d2exp (pf | out, ini);
      strpr "; ";
      fprint_d2exp (pf | out, test);
      strpr "; ";
      fprint_d2exp (pf | out, post);
      strpr "; ";
      fprint_d2exp (pf | out, body);
      strpr ")"
    end // end of [D2Efor]
  | D2Efreeat (sarg, d2e) => begin
      strpr "D2Efreeat("; fprint_d2exp (pf | out, d2e); strpr ")"
    end // end of [D2Efree]
  | D2Eif (_(*inv*), d2e_cond, d2e_then, od2e_else) => begin
      strpr "D2Eif(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d2exp (pf | out, d2e_cond);
      strpr "; ";
      fprint_d2exp (pf | out, d2e_then);
      begin case+ od2e_else of
        | Some d2e_else => begin
           strpr "; "; fprint_d2exp (pf | out, d2e_else)
          end // end of [Some]
        | None () => ()
      end;
      strpr ")"
    end
  | D2Eint (str, int) => begin
      strpr "D2Eint("; fprint1_string (pf | out, str); strpr ")"
    end
  | D2Eintsp (str, int) => begin
      strpr "D2Eintsp("; fprint1_string (pf | out, str); strpr ")"
    end
  | D2Elam_dyn (lin, npf, p2ts, d2e) => begin
      strpr "D2Elam_dyn(";
      fprint1_int (pf | out, lin);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_p2atlst (pf | out, p2ts);
      strpr "; ";
      fprint_d2exp (pf | out, d2e);
      strpr ")"
    end // end of [D2Elam_dyn]
  | D2Elaminit_dyn (lin, npf, p2ts, d2e) => begin
      strpr "D2Elaminit_dyn(";
      fprint1_int (pf | out, lin);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_p2atlst (pf | out, p2ts);
      strpr "; ";
      fprint_d2exp (pf | out, d2e);
      strpr ")"
    end // end of [D2Elaminit_dyn]
  | D2Elam_met (_, s2es, d2e) => begin
      strpr "D2Elam_met(";
      fprint_s2explst (pf | out, s2es);
      strpr "; ";
      fprint_d2exp (pf | out, d2e);
      strpr ")"
    end // end of [D2Elam_met]
  | D2Elam_sta (s2vs, s2ps, d2e) => begin
      strpr "D2Elam_sta(";
      fprint_s2varlst (pf | out, s2vs);
      strpr "; ";
      fprint_s2explst (pf | out, s2ps);
      strpr "; ";
      fprint_d2exp (pf | out, d2e);
      strpr ")";
    end // end of [D2Elam_sta]
  | D2Elet (d2cs, d2e) => begin
      strpr "D2Elet(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d2exp (pf | out, d2e);
      strpr ")"
    end // end of [D2Elet]
  | D2Emac d2m => begin
      strpr "D2Emac("; fprint_d2mac (pf | out, d2m); strpr ")"
    end
  | D2Emacsyn (knd, d2e) => let
      val () = case+ knd of
        | $Syn.MACSYNKINDcross () => fprint1_string (pf | out, "%(")
        | $Syn.MACSYNKINDdecode () => fprint1_string (pf | out, ",(")
        | $Syn.MACSYNKINDencode () => fprint1_string (pf | out, "`(")
    in
      fprint_d2exp (pf | out, d2e); strpr ")"
    end // end of [D2Emacsyn]
  | D2Eptrof d2e => begin
      strpr "D2Eptrof("; fprint_d2exp (pf | out, d2e); strpr ")"
    end // end of [D2Eptrof]
  | D2Eloopexn i => begin
      strpr "D2Eloopexn("; fprint1_int (pf | out, i); strpr ")"
    end // end of [D2Eloopexn]
  | D2Elst (lin, os2e, d2es) => begin
      strpr "D2Elst(";
      fprint1_int (pf | out, lin);
      strpr "; ";
      begin case+ os2e of
        | Some s2e => begin
            fprint_s2exp (pf | out, s2e); strpr "; "
          end
        | None () => ()
      end;
      fprint_d2explst (pf | out, d2es);
      strpr ")"
    end // end of [D2Elst]
  | D2Eraise (d2e) => begin
      strpr "D2Eraise("; fprint_d2exp (pf | out, d2e); strpr ")"
    end // end of [D2Eraise]
  | D2Erec (recknd, npf, ld2es) => begin
      strpr "D2Erec(";
      fprint1_int (pf | out, recknd);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_labd2explst (pf | out, ld2es);
      strpr ")"
    end // end of [D2Erec]
  | D2Escaseof _ => begin
      strpr "D2Escaseof("; fprint1_string (pf | out, "..."); strpr ")"
    end // end of [D2Escaseof]
  | D2Esel (d2e, d2ls) => begin
      strpr "D2Esel(";
      fprint_d2exp (pf | out, d2e);
      strpr "; ";
      fprint_d2lablst (pf | out, d2ls);
      strpr ")"
    end // end of [D2Esel]
  | D2Eseq d2es => begin
      strpr "D2Eseq("; fprint_d2explst (pf | out, d2es); strpr ")"
    end // end of [D2Eseq]
  | D2Esif (_(*inv*), s2e_cond, d2e_then, d2e_else) => begin
      strpr "D2Esif(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_s2exp (pf | out, s2e_cond);
      strpr "; ";
      fprint_d2exp (pf | out, d2e_then);
      strpr "; ";
      fprint_d2exp (pf | out, d2e_else);
      strpr ")"
    end // end of [D2Esif]
  | D2Espawn d2e => begin
      strpr "D2Espawn("; fprint_d2exp (pf | out, d2e); strpr ")"
    end // end of [D2Espawn]
  | D2Estring (str, len) => begin
      fprintf1_exn (pf | out, "D2Estring(\"%s\", %i)", @(str, len))
    end // end of [D2Estring]
  | D2Estruct (ld2es) => begin
      strpr "D2Estruct("; fprint_labd2explst (pf | out, ld2es); strpr ")"
    end // end of [D2Estruct]
  | D2Esym d2s => begin
      strpr "D2Esym("; fprint_d2sym (pf | out, d2s); strpr ")"
    end // end of [D2Esym]
  | D2Etmpid (d2e, ts2ess) => begin
      strpr "D2Etmpid(";
      fprint_d2exp (pf | out, d2e);
      strpr "; ";
      fprint_tmps2explstlst (pf | out, ts2ess);
      strpr ")"
    end // end of [D2Etmpid]
  | D2Etop () => begin
      fprint1_string (pf | out, "D2Etop()")
    end // end of [D2Etop]
  | D2Etrywith (_(*r2es*), d2e, c2ls) => begin
      strpr "D2Etrywith(";
      fprint_d2exp (pf | out, d2e);
      strpr "; ";
      fprint1_string (pf | out, "...");
      strpr ")"
    end // end of [D2Etrywith]
  | D2Evar (d2v) => begin
      strpr "D2Evar("; fprint_d2var (pf | out, d2v); strpr ")"
    end // end of [D2Evar]
  | D2Eviewat (d2e) => begin
      strpr "D2Eviewat("; fprint_d2exp (pf | out, d2e); strpr ")"
    end // end of [D2Eviewat]
  | D2Ewhere (d2e, d2cs) => begin
      strpr "D2Ewhere(";
      fprint_d2exp (pf | out, d2e);
      strpr "; ";
      fprint1_string (pf | out, "...");
      strpr ")"
    end // end of [D2Ewhere]
  | D2Ewhile (inv, test, body) => begin
        strpr "D2Ewhile(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d2exp (pf | out, test);
      strpr "; ";
      fprint_d2exp (pf | out, body);
      strpr ")"
    end // end of [D2Ewhile]
end // end of [fprint_d2exp]

//

implement fprint_d2explst {m} (pf | out, d2es) = let
  fun aux (out: &FILE m, i: int, d2es: d2explst)
    : void = begin case+ d2es of
    | cons (d2e, d2es) => begin
        if (i > 0) then fprint1_string (pf | out, ", ");
        fprint_d2exp (pf | out, d2e); aux (out, i + 1, d2es)
      end
    | nil () => ()
  end // end of [aux]
in
  aux (out, 0, d2es)
end // end of [fprint_d2explst]

//

implement fprint_d2explstlst {m} (pf | out, d2ess) = let
  fun aux (out: &FILE m, i: int, d2ess: d2explstlst)
    : void = begin case+ d2ess of
    | cons (d2es, d2ess) => begin
        if (i > 0) then fprint1_string (pf | out, "; ");
        fprint_d2explst (pf | out, d2es); aux (out, i + 1, d2ess)
      end
    | nil () => ()
  end // end of [aux]
in
  aux (out, 0, d2ess)
end // end of [fprint_d2explstlst]

//

implement fprint_labd2explst {m} (pf | out, ld2es) = let
  fun aux
    (out: &FILE m, i: int, ld2es: labd2explst): void = let
    macdef strpr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ ld2es of
    | LABD2EXPLSTcons (l, d2e, ld2es) => begin
        if i > 0 then strpr ", ";
        fprint_label (pf | out, l); strpr "= "; fprint_d2exp (pf | out, d2e);
        aux (out, i+1, ld2es)
      end
    | LABD2EXPLSTnil () => ()
  end // end of [aux]
in
  aux (out, 0, ld2es)
end // end of [fprint_labd2explst]

(* ****** ****** *)

implement print_d2exp (d2e) = print_mac (fprint_d2exp, d2e)
implement prerr_d2exp (d2e) = prerr_mac (fprint_d2exp, d2e)

implement print_d2explst (d2es) = print_mac (fprint_d2explst, d2es)
implement prerr_d2explst (d2es) = prerr_mac (fprint_d2explst, d2es)

implement print_d2explstlst (d2ess) = print_mac (fprint_d2explstlst, d2ess)
implement prerr_d2explstlst (d2ess) = prerr_mac (fprint_d2explstlst, d2ess)

implement print_labd2explst (ld2es) = print_mac (fprint_labd2explst, ld2es)
implement prerr_labd2explst (ld2es) = prerr_mac (fprint_labd2explst, ld2es)

(* ****** ****** *)

implement fprint_d2lab (pf | out, d2l) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ d2l.d2lab_node of
  | D2LABlab lab => fprint_label (pf | out, lab)
  | D2LABind ind =>  begin
      strpr "["; fprint_d2explstlst (pf | out, ind); strpr "]"
    end
end // end of [fprint_d2lab]

implement fprint_d2lablst {m} (pf | out, d2ls) = let
  fun aux (out: &FILE m, i: int, d2ls: d2lablst): void =
    case+ d2ls of
    | cons (d2l, d2ls) => begin
        if (i > 0) then fprint1_string (pf | out, ", ");
        fprint_d2lab (pf | out, d2l); aux (out, i + 1, d2ls)
      end
    | nil () => ()
  // end of [aux]
in
  aux (out, 0, d2ls)
end // end of [fprint_d2lablst]

(* ****** ****** *)

(* end of [ats_dynexp2_print.dats] *)
