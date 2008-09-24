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

// Time: October 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Eff = "ats_effect.sats"
staload Fil = "ats_filename.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_dynexp1.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef l0ab = $Syn.l0ab

(* ****** ****** *)

implement fprint_p1at (pf | out, p1t) = begin
  case+ p1t.p1at_node of
  | P1Tann (p1t, s1e) => begin
      fprint (pf | out, "P1Tann(");
      fprint (pf | out, p1t);
      fprint (pf | out, "; ");
      fprint (pf | out, s1e);
      fprint (pf | out, ")")
    end
  | P1Tany () => fprint (pf | out, "P1Tany()")
  | P1Tanys () => fprint (pf | out, "P1Tanys()")
  | P1Tapp_sta (p1t, s1as) => begin
      fprint (pf | out, "P1Tapp_sta(");
      fprint (pf | out, p1t);
      fprint (pf | out, "; ");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | P1Tapp_dyn (p1t, _(*loc_arg*), npf, p1ts) => begin
      fprint (pf | out, "P1Tapp_dyn(");
      fprint (pf | out, p1t);
      fprint (pf | out, "; ");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, p1ts);
      fprint (pf | out, ")")
    end
  | P1Tas (id, p1t) => begin
      fprint (pf | out, "P1Tas(");
      $Sym.fprint_symbol (pf | out, id.i0de_sym);
      fprint (pf | out, "; ");
      fprint (pf | out, p1t);
      fprint (pf | out, ")")
    end
  | P1Tchar c => begin
      fprint (pf | out, "P1Tchar(");
      fprint (pf | out, c);
      fprint (pf | out, ")")
    end
  | P1Tempty () => begin
      fprint (pf | out, "P1Tempty()")
    end
  | P1Texist (s1vs, p1t) => begin
      fprint (pf | out, "P1Texist(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, p1t);
      fprint (pf | out, ")")
    end
  | P1Tfloat (str) => begin
      fprint (pf | out, "P1Tfloat(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | P1Tfree p1t => begin
      fprint (pf | out, "P1Tfree(");
      fprint (pf | out, p1t);
      fprint (pf | out, ")")
    end
  | P1Tint (str) => begin
      fprint (pf | out, "P1Tint(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | P1Tlist (npf, p1ts) => begin
      fprint (pf | out, "P1Tlist(");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, p1ts);
      fprint (pf | out, ")")
    end
  | P1Tlst p1ts => begin
      fprint (pf | out, "P1Tlst(");
      fprint (pf | out, p1ts);
      fprint (pf | out, ")")
    end
  | P1Tqid (d0q, id) => begin
      $Syn.fprint_d0ynq (pf | out, d0q);
      $Sym.fprint_symbol (pf | out, id)
    end
  | P1Trec (rk, lp1ts) => begin
      fprint (pf | out, "P1Trec(");
      fprint (pf | out, rk);
      fprint (pf | out, "; ");
      fprint (pf | out, lp1ts);
      fprint (pf | out, ")")
    end
  | P1Tref (id) => begin
      fprint (pf | out, "P1Tref(");
      $Sym.fprint_symbol (pf | out, id.i0de_sym);
      fprint (pf | out, ")")
    end
  | P1Trefas (id, p1t) => begin
      fprint (pf | out, "P1Tref(");
      $Sym.fprint_symbol (pf | out, id.i0de_sym);
      fprint (pf | out, "; ");
      fprint (pf | out, p1t);
      fprint (pf | out, ")")
    end
  | P1Tstring s => begin
      fprint (pf | out, "P1Tstring(\"");
      fprint (pf | out, s);
      fprint (pf | out, "\")")
    end
  | P1Tsvararg s1a => begin
      fprint (pf | out, "P1Tsvararg(");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | P1Ttup (tupknd, npf, p1ts) => begin
      fprint (pf | out, "P1Ttup(");
      fprint (pf | out, tupknd);
      fprint (pf | out, "; ");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, p1ts);
      fprint (pf | out, ")")
    end
(*
  | _ => begin
      prerr "Internal Error: ";
      prerr "[fprint_p1at]: the pattern at [";
      prerr p1t.p1at_loc;
      prerr "] is not supported yet";
      prerr_newline ();
      exit (1)
    end
*)
end // end of [fprint_p1at]

implement fprint_p1atlst {m} (pf | out, p1ts0) = let
  fun aux (out: &FILE m, i: int, p1ts: p1atlst): void =
    case+ p1ts of
    | cons (p1t, p1ts) => begin
        if i > 0 then fprint (pf | out, ", "); 
        fprint (pf | out, p1t); aux (out, i+1, p1ts)
      end
    | nil () => ()
in
  aux (out, 0, p1ts0)
end // end of [fprint_p1atlst]

implement fprint_labp1atlst {m} (pf | out, lp1ts0) = let
  fun aux (out: &FILE m, i: int, lp1ts: labp1atlst): void =
    case+ lp1ts of
    | LABP1ATLSTcons (l, p1t, lp1ts) => begin
        if i > 0 then fprint (pf | out, ", ");
        $Lab.fprint_label (pf | out, l.l0ab_lab);
        fprint (pf | out, "= ");
        fprint (pf | out, p1t);
        aux (out, i+1, lp1ts)
      end
    | LABP1ATLSTnil () => ()
    | LABP1ATLSTdot () => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint (pf | out, "...")
      end
in
  aux (out, 0, lp1ts0)
end // end of [fprint_labp1atlst]

//

implement print_p1at (p1t) = print_mac (fprint_p1at, p1t)
implement prerr_p1at (p1t) = prerr_mac (fprint_p1at, p1t)

(* ****** ****** *)

implement fprint_d1exp (pf | out, d1e0) = begin
  case+ d1e0.d1exp_node of
  | D1Eann_effc (d1e, efc) => begin
      fprint (pf | out, "D1Eann_effc(");
      fprint (pf | out, d1e);
      fprint (pf | out, "; ");
      $Eff.fprint_effcst (pf | out, efc);
      fprint (pf | out, ")")
    end
  | D1Eann_funclo (d1e, fc) => begin
      fprint (pf | out, "D1Eann_funclo(");
      fprint (pf | out, d1e);
      fprint (pf | out, "; ");
      $Syn.fprint_funclo (pf | out, fc);
      fprint (pf | out, ")")
    end
  | D1Eann_type (d1e, s1e) => begin
      fprint (pf | out, "D1Eann_type(");
      fprint (pf | out, d1e);
      fprint (pf | out, "; ");
      fprint (pf | out, s1e);
      fprint (pf | out, ")")
    end
  | D1Eapp_dyn (d1e, _(*loc_arg*), npf, d1es) => begin
      fprint (pf | out, "D1Eapp_dyn(");
      fprint (pf | out, d1e);
      fprint (pf | out, "; ");
      fprint (pf | out, npf );
      fprint (pf | out, "; ");
      fprint (pf | out, d1es);
      fprint (pf | out, ")")
    end
  | D1Eapp_sta (d1e, s1as) => begin
      fprint (pf | out, "D1Eapp_sta(");
      fprint (pf | out, d1e);
      fprint (pf | out, "; ");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | D1Earr (s1e, d1es) => begin
      fprint (pf | out, "D1Earr(");
      fprint (pf | out, s1e);
      fprint (pf | out, "; ");
      fprint (pf | out, d1es);
      fprint (pf | out, ")")
    end
  | D1Earrsub (d1e_arr, _(*loc_ind*), d1ess_ind) => begin
      fprint (pf | out, "D1Earrsub(");
      fprint (pf | out, d1e_arr);
      fprint (pf | out, "; ");
      fprint (pf | out, d1ess_ind);
      fprint (pf | out, ")")
    end
  | D1Ecaseof _ => begin
      fprint (pf | out, "D1Ecaseof(");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | D1Echar c => begin
      fprint (pf | out, "D1Echar(");
      fprint (pf | out, c);
      fprint (pf | out, ")")
    end
  | D1Ecrypt (knd, d1e) => begin
      fprint (pf | out, "D1Ecrypt(");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint (pf | out, d1e);
      fprint (pf | out, ")")
    end
  | D1Edelay (lin, d1e) => begin
      fprint (pf | out, "D1Edelay(");
      fprint (pf | out, lin);
      fprint (pf | out, "; ");
      fprint (pf | out, d1e);
      fprint (pf | out, ")")
    end
  | D1Edynload (fil) => begin
      fprint (pf | out, "D1Edynload(");
      $Fil.fprint_filename (pf | out, fil);
      fprint (pf | out, ")")
    end
  | D1Eeffmask (effs, d1e) => begin
      fprint (pf | out, "D1Eeffmask(");
      $Eff.fprint_effectlst (pf | out, effs);
      fprint (pf | out, "; ");
      fprint (pf | out, d1e);
      fprint (pf | out, ")")
    end
  | D1Eempty () => begin
      fprint (pf | out, "D1Eempty()");
    end
  | D1Eexist (s1a, d1e) => begin
      fprint (pf | out, "D1Eexist(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, d1e);
      fprint (pf | out, ")")
    end
  | D1Eextval (s1e, code) => begin
      fprint (pf | out, s1e);
      fprint (pf | out, "; ");
      fprint (pf | out, "\"");
      fprint (pf | out, code);
      fprint (pf | out, "\"");
      fprint (pf | out, ")")
    end
  | D1Efix (id_fun, d1e_body) => begin
      fprint (pf | out, "D1Efix(");
      $Syn.fprint_i0de (pf | out, id_fun);
      fprint (pf | out, "; ");
      fprint (pf | out, d1e_body);
      fprint (pf | out, ")")
    end
  | D1Efloat str => begin
      fprint (pf | out, "D1Efloat(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | D1Efloatsp str => begin
      fprint (pf | out, "D1Efloatsp(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | D1Efoldat (_(*s1as*), d1e) => begin
      fprint (pf | out, "D1Efoldat(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, d1e);
      fprint (pf | out, ")")
    end
  | D1Efor (inv, ini, test, post, body) => begin
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, ini);
      fprint (pf | out, "; ");
      fprint (pf | out, test);
      fprint (pf | out, "; ");
      fprint (pf | out, post);
      fprint (pf | out, "; ");
      fprint (pf | out, body);
    end
  | D1Efreeat (_(*s1as*), d1e) => begin
      fprint (pf | out, "D1Efreeat(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, d1e);
      fprint (pf | out, ")")
    end
  | D1Eif (_(*inv*), d1e_cond, d1e_then, od1e_else) => begin
      fprint (pf | out, "D1Eif(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, d1e_cond);
      fprint (pf | out, "; ");
      fprint (pf | out, d1e_then);
      begin case+ od1e_else of
        | Some d1e_else => begin
           fprint (pf | out, "; "); fprint (pf | out, d1e_else)
          end
        | None () => ()
      end;
      fprint (pf | out, ")")
    end // end of [D1Eif]
  | D1Eint (str) => begin
      fprint (pf | out, "D1Eint(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | D1Eintsp (str) => begin
      fprint (pf | out, "D1Eintsp(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | D1Elam_dyn (lin, p1t, d1e) => begin
      fprint (pf | out, "D1Elam_dyn(");
      fprint (pf | out, lin);
      fprint (pf | out, "; ");
      fprint (pf | out, p1t);
      fprint (pf | out, "; ");
      fprint (pf | out, d1e);
      fprint (pf | out, ")")
    end
  | D1Elam_met (_, s1es, d1e) => begin
      fprint (pf | out, "D1Elam_met(");
      fprint (pf | out, s1es);
      fprint (pf | out, "; ");
      fprint (pf | out, d1e);
      fprint (pf | out, ")")
    end
  | D1Elam_sta_ana (_, s1as, d1e) => begin
      fprint (pf | out, "D1Elam_sta_ana(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, d1e);
      fprint (pf | out, ")");
    end
  | D1Elam_sta_syn (_, s1qs, d1e) => begin
      fprint (pf | out, "D1Elam_sta_syn(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, d1e);
      fprint (pf | out, ")");
    end
  | D1Elet (d1cs, d1e) => begin
      fprint (pf | out, "D1Elet(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, d1e);
      fprint (pf | out, ")")
    end
  | D1Eptrof d1e => begin
      fprint (pf | out, "D1Eptrof(");
      fprint (pf | out, d1e);
      fprint (pf | out, ")")
    end
  | D1Elist (npf, d1es) => begin
      fprint (pf | out, "D1Elist(");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, d1es);
      fprint (pf | out, ")")
    end
  | D1Eloopexn i => begin
      fprint (pf | out, "D1Eloopexn(");
      fprint (pf | out, i);
      fprint (pf | out, ")")
    end
  | D1Elst (lin, os1e, d1es) => begin
      fprint (pf | out, "D1Elst(");
      fprint (pf | out, lin);
      fprint (pf | out, "; ");
      begin case+ os1e of
        | Some s1e => begin
            fprint (pf | out, s1e); fprint (pf | out, "; ")
          end
        | None () => ()
      end ;
      fprint (pf | out, d1es);
      fprint (pf | out, ")")
    end
  | D1Emacsyn (knd, d1e) => let
      val () = case+ knd of
        | $Syn.MACSYNKINDcross () => fprint (pf | out, "%(")
        | $Syn.MACSYNKINDdecode () => fprint (pf | out, ",(")
        | $Syn.MACSYNKINDencode () => fprint (pf | out, "`(")
    in
      fprint (pf | out, d1e); fprint (pf | out, ")")
    end
  | D1Eqid (q, id) => begin
      $Syn.fprint_d0ynq (pf | out, q);
      $Sym.fprint_symbol (pf | out, id)
    end
  | D1Eraise (d1e) => begin
      fprint (pf | out, "D1Eraise(");
      fprint (pf | out, d1e);
      fprint (pf | out, ")")
    end
  | D1Erec (recknd, ld1es) => begin
      fprint (pf | out, "D1Erec(");
      fprint (pf | out, recknd);
      fprint (pf | out, "; ");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | D1Esel (knd, d1e, d1l) => begin
      fprint (pf | out, "D1Esel(");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint (pf | out, d1e);
      fprint (pf | out, "; ");
      fprint (pf | out, d1l);
      fprint (pf | out, ")")
    end
  | D1Eseq d1es => begin
      fprint (pf | out, "D1Eseq(");
      fprint (pf | out, d1es);
      fprint (pf | out, ")")
    end
  | D1Esexparg s1a => begin
      fprint (pf | out, "D1Esexparg(");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | D1Esif (_(*inv*), s1e_cond, d1e_then, d1e_else) => begin
      fprint (pf | out, "D1Esif(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, s1e_cond);
      fprint (pf | out, "; ");
      fprint (pf | out, d1e_then);
      fprint (pf | out, "; ");
      fprint (pf | out, d1e_else);
      fprint (pf | out, ")")
    end // end of [D1Esif]
  | D1Espawn d1e => begin
      fprint (pf | out, "D1Espawn(");
      fprint (pf | out, d1e);
      fprint (pf | out, ")")
    end
  | D1Estring (str, len) => begin
      fprintf (pf | out, "D1Estring(\"%s\", %i)", @(str, len))
    end
  | D1Estruct (ld1es) => begin
      fprint (pf | out, "D1Estruct(");
      fprint (pf | out, ld1es);
      fprint (pf | out, ")")
    end
  | D1Etmpid (qid, ts1ess) => begin
      fprint (pf | out, "D1Etmpid(");
      $Syn.fprint_d0ynq (pf | out, qid.tmpqi0de_qua);
      $Sym.fprint_symbol (pf | out, qid.tmpqi0de_sym);
      fprint (pf | out, "; ");
      fprint (pf | out, ts1ess);
      fprint (pf | out, ")")
    end
  | D1Etop () => begin
      fprint (pf | out, "D1Etop()")
    end
  | D1Etrywith (d1e, c1ls) => begin
      fprint (pf | out, "D1Etrywith(");
      fprint (pf | out, d1e);
      fprint (pf | out, "; ");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | D1Etup (tupknd, npf, d1es) => begin
      fprint (pf | out, "D1Etup(");
      fprint (pf | out, tupknd);
      fprint (pf | out, "; ");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, d1es);
      fprint (pf | out, ")")
    end
  | D1Eviewat (d1e) => begin
      fprint (pf | out, "D1Eviewat(");
      fprint (pf | out, d1e);
      fprint (pf | out, ")")
    end
  | D1Ewhere (d1e, d1cs) => begin
      fprint (pf | out, "D1Ewhere(");
      fprint (pf | out, d1e);
      fprint (pf | out, "; ");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | D1Ewhile (inv, test, body) => begin
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, test);
      fprint (pf | out, "; ");
      fprint (pf | out, body);
    end
(*
  | _ => begin
      prerr "fprint_d1exp: not yet available";
      prerr_newline ();
      exit 1
    end
*)
end // end of [fprint_d1exp]

//

implement fprint_d1explst {m} (pf | out, d1es0) = let
  fun aux (out: &FILE m, i: int, d1es: d1explst): void =
    case+ d1es of
    | cons (d1e, d1es) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint (pf | out, d1e); aux (out, i+1, d1es)
      end
    | nil () => ()
in
  aux (out, 0, d1es0)
end // end of [fprint_d1explst]

//

implement fprint_d1explstlst {m} (pf | out, d1ess0) = let
  fun aux (out: &FILE m, i: int, d1ess: d1explstlst): void =
    case+ d1ess of
    | cons (d1es, d1ess) => begin
        if i > 0 then fprint (pf | out, "; ");
        fprint (pf | out, d1es); aux (out, i+1, d1ess)
      end
    | nil () => ()
in
  aux (out, 0, d1ess0)
end // end of [fprint_d1explstlst]

//

implement fprint_labd1explst {m} (pf | out, ld1es0) = let
  fun aux (out: &FILE m, i: int, ld1es: labd1explst): void =
    case+ ld1es of
    | LABD1EXPLSTcons (l, d1e, ld1es) => begin
        if i > 0 then fprint (pf | out, ", ");
        $Lab.fprint_label (pf | out, l.l0ab_lab);
        fprint (pf | out, "= "); fprint (pf | out, d1e);
        aux (out, i+1, ld1es)
      end
    | LABD1EXPLSTnil () => ()
in
  aux (out, 0, ld1es0)
end // end of [fprint_labd1explst]

(* ****** ****** *)

implement print_d1exp (d1e) = print_mac (fprint_d1exp, d1e)
implement prerr_d1exp (d1e) = prerr_mac (fprint_d1exp, d1e)

(* ****** ****** *)

implement fprint_d1lab (pf | out, d1l) = begin
  case+ d1l.d1lab_node of
  | D1LABlab lab => $Lab.fprint_label (pf | out, lab)
  | D1LABind ind => begin
      fprint (pf | out, "["); fprint (pf | out, ind); fprint (pf | out, "]")
    end
end // end of [fprint_d1lab]

(* ****** ****** *)

(* end of [ats_dynexp1_print.dats] *)
