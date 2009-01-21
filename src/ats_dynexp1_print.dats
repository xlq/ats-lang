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

staload "ats_staexp1.sats"
staload "ats_dynexp1.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

typedef l0ab = $Syn.l0ab

(* ****** ****** *)

macdef fprint_label = $Lab.fprint_label

(* ****** ****** *)

implement fprint_p1at (pf | out, p1t) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ p1t.p1at_node of
  | P1Tann (p1t, s1e) => begin
      strpr "P1Tann(";
      fprint_p1at (pf | out, p1t);
      strpr "; ";
      fprint_s1exp (pf | out, s1e);
      strpr ")"
    end // end of [P1Tann]
  | P1Tany () => fprint1_string (pf | out, "P1Tany()")
  | P1Tanys () => fprint1_string (pf | out, "P1Tanys()")
  | P1Tapp_sta (p1t, s1as) => begin
      strpr "P1Tapp_sta(";
      fprint_p1at (pf | out, p1t);
      strpr "; ";
      fprint1_string (pf | out, "...");
      strpr ")"
    end
  | P1Tapp_dyn (p1t, _(*loc_arg*), npf, p1ts) => begin
      strpr "P1Tapp_dyn(";
      fprint_p1at (pf | out, p1t);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_p1atlst (pf | out, p1ts);
      strpr ")"
    end // end of [P1Tapp_dyn]
  | P1Tas (id, p1t) => begin
      strpr "P1Tas(";
      $Sym.fprint_symbol (pf | out, id.i0de_sym);
      strpr "; ";
      fprint_p1at (pf | out, p1t);
      strpr ")"
    end // end of [P1Tas]
  | P1Tchar c => begin
      strpr "P1Tchar("; fprint1_char (pf | out, c); strpr ")"
    end
  | P1Tempty () => begin
      fprint1_string (pf | out, "P1Tempty()")
    end
  | P1Texist (s1vs, p1t) => begin
      strpr "P1Texist(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_p1at (pf | out, p1t);
      strpr ")"
    end // end of [P1Texist]
  | P1Tfloat f(*string*) => begin
      strpr "P1Tfloat("; fprint1_string (pf | out, f); strpr ")"
    end // end of [P1Tfloat]
  | P1Tfree p1t => begin
      strpr "P1Tfree("; fprint_p1at (pf | out, p1t); strpr ")"
    end // end of [P1Tfree]
  | P1Tint i(*string*) => begin
      strpr "P1Tint("; fprint1_string (pf | out, i); strpr ")"
    end
  | P1Tlist (npf, p1ts) => begin
      strpr "P1Tlist(";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_p1atlst (pf | out, p1ts);
      strpr ")"
    end // end of [P1Tlist]
  | P1Tlst p1ts => begin
      strpr "P1Tlst("; fprint_p1atlst (pf | out, p1ts); strpr ")"
    end // end of [P1Tlst]
  | P1Tqid (d0q, id) => begin
      $Syn.fprint_d0ynq (pf | out, d0q);
      $Sym.fprint_symbol (pf | out, id)
    end // end of [P1Tqid]
  | P1Trec (rk, lp1ts) => begin
      strpr "P1Trec(";
      fprint1_int (pf | out, rk);
      strpr "; ";
      fprint_labp1atlst (pf | out, lp1ts);
      strpr ")"
    end // end of [P1Trec]
  | P1Tref (id) => begin
      strpr "P1Tref(";
      $Sym.fprint_symbol (pf | out, id.i0de_sym);
      strpr ")"
    end // end of [P1Tref]
  | P1Trefas (id, p1t) => begin
      strpr "P1Tref(";
      $Sym.fprint_symbol (pf | out, id.i0de_sym);
      strpr "; ";
      fprint_p1at (pf | out, p1t);
      strpr ")"
    end // end of [P1Trefas]
  | P1Tstring s => begin
      strpr "P1Tstring(\""; fprint1_string (pf | out, s); strpr "\")"
    end // end of [P1Tstring]
  | P1Tsvararg s1a => begin
      strpr "P1Tsvararg("; fprint1_string (pf | out, "..."); strpr ")"
    end // end of [P1Tsvararg]
  | P1Ttup (tupknd, npf, p1ts) => begin
      strpr "P1Ttup(";
      fprint1_int (pf | out, tupknd);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_p1atlst (pf | out, p1ts);
      strpr ")"
    end // end of [P1Ttup]
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
        if i > 0 then fprint1_string (pf | out, ", "); 
        fprint_p1at (pf | out, p1t); aux (out, i+1, p1ts)
      end
    | nil () => ()
in
  aux (out, 0, p1ts0)
end // end of [fprint_p1atlst]

implement fprint_labp1atlst {m} (pf | out, lp1ts0) = let
  fun aux (out: &FILE m, i: int, lp1ts: labp1atlst): void = let
    macdef strpr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ lp1ts of
    | LABP1ATLSTcons (l, p1t, lp1ts) => begin
        if i > 0 then strpr ", ";
        fprint_label (pf | out, l.l0ab_lab); strpr "= ";
        fprint_p1at (pf | out, p1t);
        aux (out, i+1, lp1ts)
      end
    | LABP1ATLSTnil () => ()
    | LABP1ATLSTdot () => begin
        if i > 0 then strpr ", "; fprint1_string (pf | out, "...")
      end // end of [LABP1ATLSTdot]
  end // end of [aux]
in
  aux (out, 0, lp1ts0)
end // end of [fprint_labp1atlst]

//

implement print_p1at (p1t) = print_mac (fprint_p1at, p1t)
implement prerr_p1at (p1t) = prerr_mac (fprint_p1at, p1t)

(* ****** ****** *)

implement fprint_d1exp (pf | out, d1e0) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ d1e0.d1exp_node of
  | D1Eann_effc (d1e, efc) => begin
      strpr "D1Eann_effc(";
      fprint_d1exp (pf | out, d1e);
      strpr "; ";
      $Eff.fprint_effcst (pf | out, efc);
      strpr ")"
    end
  | D1Eann_funclo (d1e, fc) => begin
      strpr "D1Eann_funclo(";
      fprint_d1exp (pf | out, d1e);
      strpr "; ";
      $Syn.fprint_funclo (pf | out, fc);
      strpr ")"
    end
  | D1Eann_type (d1e, s1e) => begin
      strpr "D1Eann_type(";
      fprint_d1exp (pf | out, d1e);
      strpr "; ";
      fprint_s1exp (pf | out, s1e);
      strpr ")"
    end
  | D1Eapp_dyn (d1e, _(*loc_arg*), npf, d1es) => begin
      strpr "D1Eapp_dyn(";
      fprint_d1exp (pf | out, d1e);
      strpr "; ";
      fprint1_int (pf | out, npf );
      strpr "; ";
      fprint_d1explst (pf | out, d1es);
      strpr ")"
    end
  | D1Eapp_sta (d1e, s1as) => begin
      strpr "D1Eapp_sta(";
      fprint_d1exp (pf | out, d1e);
      strpr "; ";
      fprint1_string (pf | out, "...");
      strpr ")"
    end
  | D1Earrinit (s1e, od1e_asz, d1es_elt) => begin
      strpr "D1Earrinit(";
      fprint_s1exp (pf | out, s1e);
      strpr "; ";
      begin case+ od1e_asz of
      | Some d1e => fprint_d1exp (pf | out, d1e) | None () => ()
      end;
      strpr "; ";      
      fprint_d1explst (pf | out, d1es_elt);
      strpr ")"
    end // end of [D1Earrinit]
  | D1Earrsize (os1e_elt, d1es_elt) => begin
      strpr "D1Earrsize(";
      begin case+ os1e_elt of
      | Some s1e => fprint_s1exp (pf | out, s1e) | None () => ()
      end;
      strpr "; ";
      fprint_d1explst (pf | out, d1es_elt);
      strpr ")"
    end // end of [D1Earrsize]
  | D1Earrsub (d1e_arr, _(*loc_ind*), d1ess_ind) => begin
      strpr "D1Earrsub(";
      fprint_d1exp (pf | out, d1e_arr);
      strpr "; ";
      fprint_d1explstlst (pf | out, d1ess_ind);
      strpr ")"
    end // end of [D1Earrsub]
  | D1Ecaseof _ => begin
      strpr "D1Ecaseof("; fprint1_string (pf | out, "..."); strpr ")"
    end
  | D1Echar c => begin
      strpr "D1Echar("; fprint1_char (pf | out, c); strpr ")"
    end
  | D1Ecrypt (knd, d1e) => begin
      strpr "D1Ecrypt(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_d1exp (pf | out, d1e);
      strpr ")"
    end
  | D1Edynload (fil) => begin
      strpr "D1Edynload(";
      $Fil.fprint_filename (pf | out, fil);
      strpr ")"
    end
  | D1Eeffmask (effs, d1e) => begin
      strpr "D1Eeffmask(";
      $Eff.fprint_effectlst (pf | out, effs);
      strpr "; ";
      fprint_d1exp (pf | out, d1e);
      strpr ")"
    end
  | D1Eempty () => begin
      strpr "D1Eempty()";
    end
  | D1Eexist (s1a, d1e) => begin
      strpr "D1Eexist(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d1exp (pf | out, d1e);
      strpr ")"
    end // end of [D1Eexist]
  | D1Eextval (s1e, code) => begin
      fprint_s1exp (pf | out, s1e);
      strpr "; ";
      strpr "\"";
      fprint1_string (pf | out, code);
      strpr "\"";
      strpr ")"
    end // end of [D1Eextval]
  | D1Efix (id_fun, d1e_body) => begin
      strpr "D1Efix(";
      $Syn.fprint_i0de (pf | out, id_fun);
      strpr "; ";
      fprint_d1exp (pf | out, d1e_body);
      strpr ")"
    end // end of [D1Efix]
  | D1Efloat f(*string*) => begin
      strpr "D1Efloat("; fprint1_string (pf | out, f); strpr ")"
    end
  | D1Efloatsp f(*string*) => begin
      strpr "D1Efloatsp("; fprint1_string (pf | out, f); strpr ")"
    end
  | D1Efoldat (_(*s1as*), d1e) => begin
      strpr "D1Efoldat(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d1exp (pf | out, d1e);
      strpr ")"
    end // end of [D1Efoldat]
  | D1Efor (inv, ini, test, post, body) => begin
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d1exp (pf | out, ini);
      strpr "; ";
      fprint_d1exp (pf | out, test);
      strpr "; ";
      fprint_d1exp (pf | out, post);
      strpr "; ";
      fprint_d1exp (pf | out, body);
    end // end of [D1Efor]
  | D1Efreeat (_(*s1as*), d1e) => begin
      strpr "D1Efreeat(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d1exp (pf | out, d1e);
      strpr ")"
    end // end of [D1Efreeat]
  | D1Eif (_(*inv*), d1e_cond, d1e_then, od1e_else) => begin
      strpr "D1Eif(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d1exp (pf | out, d1e_cond);
      strpr "; ";
      fprint_d1exp (pf | out, d1e_then);
      begin case+ od1e_else of
        | Some d1e_else => begin
            strpr "; "; fprint_d1exp (pf | out, d1e_else)
          end
        | None () => ()
      end;
      strpr ")"
    end // end of [D1Eif]
  | D1Eint i(*string*) => begin
      strpr "D1Eint("; fprint1_string (pf | out, i); strpr ")"
    end
  | D1Eintsp i(*string*) => begin
      strpr "D1Eintsp("; fprint1_string (pf | out, i); strpr ")"
    end
  | D1Elam_dyn (atlin, p1t, d1e) => begin
      strpr "D1Elam_dyn(";
      fprint1_int (pf | out, atlin);
      strpr "; ";
      fprint_p1at (pf | out, p1t);
      strpr "; ";
      fprint_d1exp (pf | out, d1e);
      strpr ")"
    end // end of [D1Elam_dyn]
  | D1Elam_met (_, s1es, d1e) => begin
      strpr "D1Elam_met(";
      fprint_s1explst (pf | out, s1es);
      strpr "; ";
      fprint_d1exp (pf | out, d1e);
      strpr ")"
    end // end of [D1Elam_met]
  | D1Elam_sta_ana (_, s1as, d1e) => begin
      strpr "D1Elam_sta_ana(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d1exp (pf | out, d1e);
      strpr ")";
    end // end of [D1Elam_sta_ana]
  | D1Elam_sta_syn (_, s1qs, d1e) => begin
      strpr "D1Elam_sta_syn(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d1exp (pf | out, d1e);
      strpr ")";
    end // end of [D1Elam_sta_syn]
  | D1Elazy_delay (lin, d1e) => begin
      strpr "D1Elazy_delay(";
      fprint1_int (pf | out, lin);
      strpr "; ";
      fprint_d1exp (pf | out, d1e);
      strpr ")"
    end // end of [D1Elazy_delay]
  | D1Elet (d1cs, d1e) => begin
      strpr "D1Elet(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d1exp (pf | out, d1e);
      strpr ")"
    end // end of [D1Elet]
  | D1Eptrof d1e => begin
      strpr "D1Eptrof("; fprint_d1exp (pf | out, d1e); strpr ")"
    end
  | D1Elist (npf, d1es) => begin
      strpr "D1Elist(";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_d1explst (pf | out, d1es);
      strpr ")"
    end // end of [D1Elist]
  | D1Eloopexn i => begin
      strpr "D1Eloopexn("; fprint1_int (pf | out, i); strpr ")"
    end // end of [D1Eloopexn]
  | D1Elst (lin, os1e, d1es) => begin
      strpr "D1Elst(";
      fprint1_int (pf | out, lin);
      strpr "; ";
      begin case+ os1e of
        | Some s1e => begin
            fprint_s1exp (pf | out, s1e); strpr "; "
          end
        | None () => ()
      end;
      fprint_d1explst (pf | out, d1es);
      strpr ")"
    end // end of [D1Elst]
  | D1Emacsyn (knd, d1e) => let
      val () = case+ knd of
        | $Syn.MACSYNKINDcross () => fprint1_string (pf | out, "%(")
        | $Syn.MACSYNKINDdecode () => fprint1_string (pf | out, ",(")
        | $Syn.MACSYNKINDencode () => fprint1_string (pf | out, "`(")
    in
      fprint_d1exp (pf | out, d1e); strpr ")"
    end // end of [D1Emacsyn]
  | D1Eqid (q, id) => begin
      $Syn.fprint_d0ynq (pf | out, q); $Sym.fprint_symbol (pf | out, id)
    end // end of [D1Eqid]
  | D1Eraise (d1e) => begin
      strpr "D1Eraise("; fprint_d1exp (pf | out, d1e); strpr ")"
    end // end of [D1Eraise]
  | D1Erec (recknd, ld1es) => begin
      strpr "D1Erec(";
      fprint1_int (pf | out, recknd);
      strpr "; ";
      fprint1_string (pf | out, "...");
      strpr ")"
    end // end of [D1Erec]
  | D1Escaseof _ => begin
      strpr "D1Escaseof("; fprint1_string (pf | out, "..."); strpr ")"
    end // end of [D1Escaseof]
  | D1Esel (knd, d1e, d1l) => begin
      strpr "D1Esel(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_d1exp (pf | out, d1e);
      strpr "; ";
      fprint_d1lab (pf | out, d1l);
      strpr ")"
    end // end of [D1Esel]
  | D1Eseq d1es => begin
      strpr "D1Eseq("; fprint_d1explst (pf | out, d1es); strpr ")"
    end // end of [D1Eseq]
  | D1Esexparg s1a => begin
      strpr "D1Esexparg("; fprint1_string (pf | out, "..."); strpr ")"
    end // end of [D1Esexparg]
  | D1Esif (_(*inv*), s1e_cond, d1e_then, d1e_else) => begin
      strpr "D1Esif(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_s1exp (pf | out, s1e_cond);
      strpr "; ";
      fprint_d1exp (pf | out, d1e_then);
      strpr "; ";
      fprint_d1exp (pf | out, d1e_else);
      strpr ")"
    end // end of [D1Esif]
  | D1Espawn d1e => begin
      strpr "D1Espawn("; fprint_d1exp (pf | out, d1e); strpr ")"
    end // end of [D1Espawn]
  | D1Estring (str, len) => begin
      fprintf1_exn (pf | out, "D1Estring(\"%s\", %i)", @(str, len))
    end // end of [D1Estring]
  | D1Estruct (ld1es) => begin
      strpr "D1Estruct(";
      fprint_labd1explst (pf | out, ld1es);
      strpr ")"
    end // end of [D1Estruct]
  | D1Etmpid (qid, ts1ess) => begin
      strpr "D1Etmpid(";
      $Syn.fprint_d0ynq (pf | out, qid.tmpqi0de_qua);
      $Sym.fprint_symbol (pf | out, qid.tmpqi0de_sym);
      strpr "; ";
      fprint_tmps1explstlst (pf | out, ts1ess);
      strpr ")"
    end // end of [D1Etmpid]
  | D1Etop () => begin
      fprint1_string (pf | out, "D1Etop()")
    end
  | D1Etrywith (_(*r1es*), d1e, c1ls) => begin
      strpr "D1Etrywith(";
      fprint_d1exp (pf | out, d1e);
      strpr "; ";
      fprint1_string (pf | out, "...");
      strpr ")"
    end // end of [D1Etrywith]
  | D1Etup (tupknd, npf, d1es) => begin
      strpr "D1Etup(";
      fprint1_int (pf | out, tupknd);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_d1explst (pf | out, d1es);
      strpr ")"
    end // end of [D1Etup]
  | D1Eviewat (d1e) => begin
      strpr "D1Eviewat("; fprint_d1exp (pf | out, d1e); strpr ")"
    end
  | D1Ewhere (d1e, d1cs) => begin
      strpr "D1Ewhere(";
      fprint_d1exp (pf | out, d1e);
      strpr "; ";
      fprint1_string (pf | out, "...");
      strpr ")"
    end // end of [D1Ewhere]
  | D1Ewhile (inv, test, body) => begin
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d1exp (pf | out, test);
      strpr "; ";
      fprint_d1exp (pf | out, body);
    end // end of [D1Ewhile]
(*
  | _ => begin
      prerr "fprint_d1exp: not yet available"; prerr_newline ();
      exit {void} (1)
    end
*)
end // end of [fprint_d1exp]

//

implement fprint_d1explst {m} (pf | out, d1es0) = let
  fun aux (out: &FILE m, i: int, d1es: d1explst): void =
    case+ d1es of
    | cons (d1e, d1es) => let
        val () = if i > 0 then fprint1_string (pf | out, ", ")
      in
        fprint_d1exp (pf | out, d1e); aux (out, i+1, d1es)
      end // end of [cons]
    | nil () => ()
in
  aux (out, 0, d1es0)
end // end of [fprint_d1explst]

//

implement fprint_d1explstlst {m} (pf | out, d1ess0) = let
  fun aux (out: &FILE m, i: int, d1ess: d1explstlst): void =
    case+ d1ess of
    | cons (d1es, d1ess) => let
        val () = if i > 0 then fprint1_string (pf | out, "; ")
      in
        fprint_d1explst (pf | out, d1es); aux (out, i+1, d1ess)
      end // end of [cons]
    | nil () => ()
in
  aux (out, 0, d1ess0)
end // end of [fprint_d1explstlst]

//

implement fprint_labd1explst {m} (pf | out, ld1es0) = let
  fun aux (out: &FILE m, i: int, ld1es: labd1explst): void = let
    macdef strpr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ ld1es of
    | LABD1EXPLSTcons (l, d1e, ld1es) => begin
        if i > 0 then strpr ", ";
        fprint_label (pf | out, l.l0ab_lab); strpr "= ";
        fprint_d1exp (pf | out, d1e);
        aux (out, i+1, ld1es)
      end
    | LABD1EXPLSTnil () => ()
  end // end of [aux]
in
  aux (out, 0, ld1es0)
end // end of [fprint_labd1explst]

(* ****** ****** *)

implement print_d1exp (d1e) = print_mac (fprint_d1exp, d1e)
implement prerr_d1exp (d1e) = prerr_mac (fprint_d1exp, d1e)

(* ****** ****** *)

implement fprint_d1lab (pf | out, d1l) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ d1l.d1lab_node of
  | D1LABlab lab => fprint_label (pf | out, lab)
  | D1LABind ind => begin
      strpr "["; fprint_d1explstlst (pf | out, ind); strpr "]"
    end // end of [D1LABind]
end // end of [fprint_d1lab]

(* ****** ****** *)

(* end of [ats_dynexp1_print.dats] *)
