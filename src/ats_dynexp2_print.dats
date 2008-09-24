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

overload fprint with $Lab.fprint_label
overload fprint with $Sym.fprint_symbol

(* ****** ****** *)

implement fprint_d2sym (pf | out, d2s) = begin
  $Syn.fprint_d0ynq (pf | out, d2s.d2sym_qua);
  fprint (pf | out, d2s.d2sym_sym)
end

implement print_d2sym (d2s) = print_mac (fprint_d2sym, d2s)
implement prerr_d2sym (d2s) = prerr_mac (fprint_d2sym, d2s)

(* ****** ****** *)

implement fprint_d2item (pf | out, d2i) = begin
  case+ d2i of
  | D2ITEMcon d2cs => begin
      fprint (pf | out, "D2ITEMcon(");
      fprint_d2conlst (pf | out, d2cs);
      fprint (pf | out, ")")
    end
  | D2ITEMcst d2c => begin
      fprint (pf | out, "D2ITEMcst(");
      fprint_d2cst (pf | out, d2c);
      fprint (pf | out, ")")
    end
  | D2ITEMe1xp e1xp => begin
      fprint (pf | out, "D2ITEMe1xp(");
      fprint_e1xp (pf | out, e1xp);
      fprint (pf | out, ")")
    end
  | D2ITEMmacdef d2m => begin
      fprint (pf | out, "D2ITEMmacdef(");
      fprint_d2mac (pf | out, d2m);
      fprint (pf | out, ")")
    end
  | D2ITEMmacvar d2v => begin
      fprint (pf | out, "D2ITEMmacvar(");
      fprint_d2var (pf | out, d2v);
      fprint (pf | out, ")")
    end
  | D2ITEMsym d2is => begin
      fprint (pf | out, "D2ITEMsym(...)")
    end
  | D2ITEMvar d2v => begin
      fprint (pf | out, "D2ITEMvar(");
      fprint_d2var (pf | out, d2v);
      fprint (pf | out, ")")
    end
end // end of [fprint_d2item]

implement print_d2item (d2i) = print_mac (fprint_d2item, d2i)
implement prerr_d2item (d2i) = prerr_mac (fprint_d2item, d2i)

//

implement fprint_d2itemlst {m} (pf | out, d2is) = let
  fun aux (out: &FILE m, i: int, d2is: d2itemlst): void =
    case+ d2is of
    | cons (d2i, d2is) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_d2item (pf | out, d2i); aux (out, i+1, d2is)
      end
    | nil () => ()
in
  aux (out, 0, d2is)
end // end of [fprint_d2itemlst]

implement print_d2itemlst (d2is) = print_mac (fprint_d2itemlst, d2is)
implement prerr_d2itemlst (d2is) = prerr_mac (fprint_d2itemlst, d2is)

(* ****** ****** *)

implement fprint_p2at (pf | out, p2t) = case+ p2t.p2at_node of
  | P2Tann (p2t, s2e) => begin
      fprint (pf | out, "P2Tann(");
      fprint (pf | out, p2t);
      fprint (pf | out, "; ");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | P2Tany () => fprint (pf | out, "P2Tany()")
  | P2Tas (refknd, d2v, p2t) => begin
      fprint (pf | out, "P2Tas(");
      if (refknd > 0) then fprint (pf | out, "!");
      fprint (pf | out, d2v);
      fprint (pf | out, "; ");
      fprint (pf | out, p2t);
      fprint (pf | out, ")")
    end
  | P2Tbool b => begin
      fprint (pf | out, "P2Tbool(");
      fprint (pf | out, b);
      fprint (pf | out, ")")
    end
  | P2Tchar c => begin
      fprint (pf | out, "P2Tchar(");
      fprint (pf | out, c);
      fprint (pf | out, ")")
    end
  | P2Tcon (freeknd, d2c, s2qs, s2e, npf, p2ts) => begin
      fprint (pf | out, "P2Tcon(");
      if (freeknd < 0) then fprint (pf | out, "~");
      fprint (pf | out, d2c);
      fprint (pf | out, "; ");
      fprint (pf | out, p2ts);
      fprint (pf | out, ")")
    end
  | P2Tempty () => begin
      fprint (pf | out, "P2Tempty()")
    end
  | P2Texist (s2vs, p2t) => begin
      fprint (pf | out, "P2Texist(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, p2t);
      fprint (pf | out, ")")
    end
  | P2Tfloat (str) => begin
      fprint (pf | out, "P2Tfloat(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | P2Tint (str, _(*intinf*)) => begin
      fprint (pf | out, "P2Tint(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | P2Tlist (npf, p2ts) => begin
      fprint (pf | out, "P2Tlist(");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, p2ts);
      fprint (pf | out, ")")
    end
  | P2Tlst p2ts => begin
      fprint (pf | out, "P2Tlst(");
      fprint (pf | out, p2ts);
      fprint (pf | out, ")")
    end
  | P2Trec (recknd, npf, lp2ts) => begin
      fprint (pf | out, "P2Trec(");
      fprint (pf | out, recknd);
      fprint (pf | out, "; ");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, lp2ts);
      fprint (pf | out, ")")
    end
  | P2Tstring s => begin
      fprint (pf | out, "P2Tstring(\"");
      fprint (pf | out, s);
      fprint (pf | out, "\")")
    end
  | P2Tvar (refknd, d2v) => begin
      fprint (pf | out, "P2Tvar(");
      if (refknd > 0) then fprint (pf | out, "!");
      fprint (pf | out, d2v);
      fprint (pf | out, ")")
    end
  | P2Tvbox (d2v) => begin
      fprint (pf | out, "P2Tvbox(");
      fprint (pf | out, d2v);
      fprint (pf | out, ")")
    end
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

implement fprint_p2atlst {m} (pf | out, p2ts) = let
  fun aux (out: &FILE m, i: int, p2ts: p2atlst): void =
    case+ p2ts of
    | cons (p2t, p2ts) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint (pf | out, p2t); aux (out, i+1, p2ts)
      end
    | nil () => ()
in
  aux (out, 0, p2ts)
end // end of [fprint_p2atlst]

implement fprint_labp2atlst {m} (pf | out, lp2ts) = let
  fun aux (out: &FILE m, i: int, lp2ts: labp2atlst): void = begin
    case+ lp2ts of
    | LABP2ATLSTcons (l, p2t, lp2ts) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint (pf | out, l); fprint (pf | out, "= "); fprint (pf | out, p2t);
        aux (out, i+1, lp2ts)
      end
    | LABP2ATLSTnil () => ()
    | LABP2ATLSTdot () => begin
        if i > 0 then fprint (pf | out, ", "); fprint (pf | out, "...")
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
  val () = fprint (pf | out, i2nv.i2nvarg_var)
  val () = fprint (pf | out, ": ")
  val () = fprint (pf | out, i2nv.i2nvarg_typ)
in
  // empty
end

implement fprint_i2nvarglst {m} (pf | out, args) = let
  fun aux (out: &FILE m, i: int, args: i2nvarglst)
    : void = begin case+ args of
    | cons (arg, args) => begin
        if (i > 0) then fprint (pf | out, ", ");
        fprint (pf | out, arg); aux (out, i + 1, args)
      end
    | nil () => ()
  end // end of [aux]
in
  aux (out, 0, args)
end // end of [fprint_i2nvarglst]

implement fprint_i2nvresstate (pf | out, res) = let
  val () = fprint (pf | out, "[");
  val () = fprint (pf | out, res.i2nvresstate_svs);
  val () = fprint (pf | out, "; ");
  val () = fprint (pf | out, res.i2nvresstate_gua);
  val () = fprint (pf | out, "] (");
  val () = fprint (pf | out, res.i2nvresstate_arg);
  val () = fprint (pf | out, ")")
in
  // empty
end

//

implement print_i2nvarglst (args) = print_mac (fprint_i2nvarglst, args)
implement prerr_i2nvarglst (args) = prerr_mac (fprint_i2nvarglst, args)

implement print_i2nvresstate (res) = print_mac (fprint_i2nvresstate, res)
implement prerr_i2nvresstate (res) = prerr_mac (fprint_i2nvresstate, res)

(* ****** ****** *)

implement fprint_d2exparg (pf | out, d2a) = begin case+ d2a of
  | D2EXPARGsta s2as => fprint (pf | out, s2as)
  | D2EXPARGdyn (_(*loc_arg*), _(*npf*), d2es) => fprint (pf | out, d2es)
end // end of [fprint_d2exparg]

implement print_d2exparg (arg) = print_mac (fprint_d2exparg, arg)
implement prerr_d2exparg (arg) = prerr_mac (fprint_d2exparg, arg)

implement fprint_d2exparglst {m} (pf | out, d2as) = let
  fun aux (out: &FILE m, i: int, d2as: d2exparglst): void =
    case+ d2as of
    | cons (d2a, d2as) => begin
        if (i > 0) then fprint (pf | out, "; ");
        fprint_d2exparg (pf | out, d2a); aux (out, i+1, d2as)
      end
    | nil () => ()
in
  aux (out, 0, d2as)
end // end of [fprint_d2exparglst]

implement print_d2exparglst (args) = print_mac (fprint_d2exparglst, args)
implement prerr_d2exparglst (args) = prerr_mac (fprint_d2exparglst, args)

(* ****** ****** *)

implement fprint_d2exp (pf | out, d2e0) = begin
  case+ d2e0.d2exp_node of
  | D2Eann_seff (d2e, s2fe) => begin
      fprint (pf | out, "D2Eann_seff(");
      fprint (pf | out, d2e);
      fprint (pf | out, "; ");
      fprint (pf | out, s2fe);
      fprint (pf | out, ")")
    end
  | D2Eann_funclo (d2e, fc) => begin
      fprint (pf | out, "D2Eann_funclo(");
      fprint (pf | out, d2e);
      fprint (pf | out, "; ");
      $Syn.fprint_funclo (pf | out, fc);
      fprint (pf | out, ")")
    end
  | D2Eann_type (d2e, s2e) => begin
      fprint (pf | out, "D2Eann_type(");
      fprint (pf | out, d2e);
      fprint (pf | out, "; ");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | D2Eapps (d2e_fun, d2as_arg) => begin
      fprint (pf | out, "D2Eapps(");
      fprint (pf | out, d2e_fun);
      fprint (pf | out, "; ");
      fprint_d2exparglst (pf | out, d2as_arg);
      fprint (pf | out, ")")
    end
  | D2Earr (s2e_elt, d2es_elt) => begin
      fprint (pf | out, "D2Earr(");
      fprint (pf | out, s2e_elt);
      fprint (pf | out, "; ");
      fprint (pf | out, d2es_elt);
      fprint (pf | out, ")")
    end
  | D2Earrsub (d2s, d2e_arr, _(*loc_ind*), d2ess_ind) => begin
      fprint (pf | out, "D2Earrsub(");
      fprint (pf | out, d2s);
      fprint (pf | out, "; ");
      fprint (pf | out, d2e_arr);
      fprint (pf | out, "; ");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | D2Eassgn (d2e_lval, d2e_val) => begin
      fprint (pf | out, "D2Eassgn(");
      fprint (pf | out, d2e_lval);
      fprint (pf | out, "; ");
      fprint (pf | out, d2e_val);
      fprint (pf | out, ")")
    end
 | D2Ecaseof _ => begin
      fprint (pf | out, "D2Ecaseof(");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | D2Echar c => begin
      fprint (pf | out, "D2Echar(");
      fprint (pf | out, c);
      fprint (pf | out, ")")
    end
  | D2Econ (d2c, s2as, npf, d2es) => begin
      fprint (pf | out, "D2Econ(");
      fprint (pf | out, d2c);
      fprint (pf | out, "; ");
      fprint (pf | out, d2es);
      fprint (pf | out, ")")      
    end
  | D2Ecst d2c => begin
      fprint (pf | out, "D2Ecst(");
      fprint (pf | out, d2c);
      fprint (pf | out, ")")
    end
  | D2Ecrypt (knd, d2e) => begin
      fprint (pf | out, "D2Ecrypt(");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Edelay (lin, d2e) => begin
      fprint (pf | out, "D2Edelay(");
      fprint (pf | out, lin);
      fprint (pf | out, "; ");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Ederef d2e => begin
      fprint (pf | out, "D2Ederef(");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Edynload (fil) => begin
      fprint (pf | out, "D2Edynload(");
      $Fil.fprint_filename (pf | out, fil);
      fprint (pf | out, ")")
    end
  | D2Eeffmask (effs, d2e) => begin
      fprint (pf | out, "D2Eeffmask(");
      $Eff.fprint_effectlst (pf | out, effs);
      fprint (pf | out, "; ");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Eempty () => begin
      fprint (pf | out, "D2Eempty()");
    end
  | D2Eexist (s2a, d2e) => begin
      fprint (pf | out, "D2Eexist(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Eextval (s2e, code) => begin
      fprint (pf | out, s2e);
      fprint (pf | out, "; ");
      fprint (pf | out, "\"");
      fprint (pf | out, code);
      fprint (pf | out, "\"");
      fprint (pf | out, ")")
    end
  | D2Efix (d2v_fun, d2e_body) => begin
      fprint (pf | out, "D2Efix(");
      fprint (pf | out, d2v_fun);
      fprint (pf | out, "; ");
      fprint (pf | out, d2e_body);
      fprint (pf | out, ")")
    end
  | D2Efloat str => begin
      fprint (pf | out, "D2Efloat(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | D2Efloatsp str => begin
      fprint (pf | out, "D2Efloatsp(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | D2Efoldat (sarg, d2e) => begin
      fprint (pf | out, "D2Efoldat(");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Efor (inv, ini, test, post, body) => begin
      fprint (pf | out, "D2Efor(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, ini);
      fprint (pf | out, "; ");
      fprint (pf | out, test);
      fprint (pf | out, "; ");
      fprint (pf | out, post);
      fprint (pf | out, "; ");
      fprint (pf | out, body);
      fprint (pf | out, ")")
    end
  | D2Efreeat (sarg, d2e) => begin
      fprint (pf | out, "D2Efreeat(");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Eif (_(*inv*), d2e_cond, d2e_then, od2e_else) => begin
      fprint (pf | out, "D2Eif(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, d2e_cond);
      fprint (pf | out, "; ");
      fprint (pf | out, d2e_then);
      begin case+ od2e_else of
        | Some d2e_else => begin
           fprint (pf | out, "; "); fprint (pf | out, d2e_else)
          end
        | None () => ()
      end;
      fprint (pf | out, ")")
    end
  | D2Eint (str, int) => begin
      fprint (pf | out, "D2Eint(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | D2Eintsp (str, int) => begin
      fprint (pf | out, "D2Eintsp(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | D2Elam_dyn (lin, npf, p2ts, d2e) => begin
      fprint (pf | out, "D2Elam_dyn(");
      fprint (pf | out, lin);
      fprint (pf | out, "; ");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, p2ts);
      fprint (pf | out, "; ");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Elam_met (_, s2es, d2e) => begin
      fprint (pf | out, "D2Elam_met(");
      fprint (pf | out, s2es);
      fprint (pf | out, "; ");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Elam_sta (s2vs, s2ps, d2e) => begin
      fprint (pf | out, "D2Elam_sta(");
      fprint (pf | out, s2vs);
      fprint (pf | out, "; ");
      fprint (pf | out, s2ps);
      fprint (pf | out, "; ");
      fprint (pf | out, d2e);
      fprint (pf | out, ")");
    end
  | D2Elet (d2cs, d2e) => begin
      fprint (pf | out, "D2Elet(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Emac d2m => begin
      fprint (pf | out, "D2Emac(");
      fprint (pf | out, d2m);
      fprint (pf | out, ")")
    end
  | D2Emacsyn (knd, d2e) => let
      val () = case+ knd of
        | $Syn.MACSYNKINDcross () => fprint (pf | out, "%(")
        | $Syn.MACSYNKINDdecode () => fprint (pf | out, ",(")
        | $Syn.MACSYNKINDencode () => fprint (pf | out, "`(")
    in
      fprint (pf | out, d2e); fprint (pf | out, ")")
    end
  | D2Eptrof d2e => begin
      fprint (pf | out, "D2Eptrof(");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Eloopexn i => begin
      fprint (pf | out, "D2Eloopexn(");
      fprint (pf | out, i);
      fprint (pf | out, ")")
    end
  | D2Elst (lin, os2e, d2es) => begin
      fprint (pf | out, "D2Elst(");
      fprint (pf | out, lin);
      fprint (pf | out, "; ");
      begin case+ os2e of
        | Some s2e => begin
            fprint (pf | out, s2e); fprint (pf | out, "; ")
          end
        | None () => ()
      end ;
      fprint (pf | out, d2es);
      fprint (pf | out, ")")
    end
  | D2Eraise (d2e) => begin
      fprint (pf | out, "D2Eraise(");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Erec (recknd, npf, ld2es) => begin
      fprint (pf | out, "D2Erec(");
      fprint (pf | out, recknd);
      fprint (pf | out, "; ");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | D2Esel (d2e, d2ls) => begin
      fprint (pf | out, "D2Esel(");
      fprint (pf | out, d2e);
      fprint (pf | out, "; ");
      fprint (pf | out, d2ls);
      fprint (pf | out, ")")
    end
  | D2Eseq d2es => begin
      fprint (pf | out, "D2Eseq(");
      fprint (pf | out, d2es);
      fprint (pf | out, ")")
    end
  | D2Esif (_(*inv*), s2e_cond, d2e_then, d2e_else) => begin
      fprint (pf | out, "D2Esif(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, s2e_cond);
      fprint (pf | out, "; ");
      fprint (pf | out, d2e_then);
      fprint (pf | out, "; ");
      fprint (pf | out, d2e_else);
      fprint (pf | out, ")")
    end
  | D2Espawn d2e => begin
      fprint (pf | out, "D2Espawn(");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Estring (str, len) => begin
      fprintf (pf | out, "D2Estring(\"%s\", %i)", @(str, len))
    end
  | D2Estruct (ld2es) => begin
      fprint (pf | out, "D2Estruct(");
      fprint (pf | out, ld2es);
      fprint (pf | out, ")")
    end
  | D2Esym d2s => begin
      fprint (pf | out, "D2Esym(");
      fprint (pf | out, d2s);
      fprint (pf | out, ")")
    end
  | D2Etmpid (d2e, ts2ess) => begin
      fprint (pf | out, "D2Etmpid(");
      fprint (pf | out, d2e);
      fprint (pf | out, "; ");
      fprint (pf | out, ts2ess);
      fprint (pf | out, ")")
    end
  | D2Etop () => begin
      fprint (pf | out, "D2Etop()")
    end
  | D2Etrywith (d2e, c2ls) => begin
      fprint (pf | out, "D2Etrywith(");
      fprint (pf | out, d2e);
      fprint (pf | out, "; ");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | D2Evar (d2v) => begin
      fprint (pf | out, "D2Evar(");
      fprint (pf | out, d2v);
      fprint (pf | out, ")")
    end
  | D2Eviewat (d2e) => begin
      fprint (pf | out, "D2Eviewat(");
      fprint (pf | out, d2e);
      fprint (pf | out, ")")
    end
  | D2Ewhere (d2e, d2cs) => begin
      fprint (pf | out, "D2Ewhere(");
      fprint (pf | out, d2e);
      fprint (pf | out, "; ");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | D2Ewhile (inv, test, body) => begin
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, test);
      fprint (pf | out, "; ");
      fprint (pf | out, body);
    end
end // end of [fprint_d2exp]

//

implement fprint_d2explst {m} (pf | out, d2es) = let
  fun aux (out: &FILE m, i: int, d2es: d2explst)
    : void = begin case+ d2es of
    | cons (d2e, d2es) => begin
        if (i > 0) then fprint (pf | out, ", ");
        fprint (pf | out, d2e); aux (out, i + 1, d2es)
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
        if (i > 0) then fprint (pf | out, "; ");
        fprint (pf | out, d2es); aux (out, i + 1, d2ess)
      end
    | nil () => ()
  end // end of [aux]
in
  aux (out, 0, d2ess)
end // end of [fprint_d2explstlst]

//

implement fprint_labd2explst {m} (pf | out, ld2es0) = let

fun aux (out: &FILE m, i: int, ld2es: labd2explst)
  : void = begin case+ ld2es of
    | LABD2EXPLSTcons (l, d2e, ld2es) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint (pf | out, l);
        fprint (pf | out, "= ");
        fprint (pf | out, d2e);
        aux (out, i+1, ld2es)
      end
    | LABD2EXPLSTnil () => ()
  end // end of [aux]
in
  aux (out, 0, ld2es0)
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

implement fprint_d2lab (pf | out, d2l) =
  case+ d2l.d2lab_node of
  | D2LABlab lab => fprint (pf | out, lab)
  | D2LABind ind =>  begin
      fprint (pf | out, "["); fprint (pf | out, ind); fprint (pf | out, "]")
    end

implement fprint_d2lablst {m} (pf | out, d2ls) = let
  fun aux (out: &FILE m, i: int, d2ls: d2lablst)
    : void = begin case+ d2ls of
    | cons (d2l, d2ls) => begin
        if (i > 0) then fprint (pf | out, ", ");
        fprint (pf | out, d2l); aux (out, i + 1, d2ls)
      end
    | nil () => ()
  end // end of [aux]
in
  aux (out, 0, d2ls)
end // end of [fprint_d2lablst]

(* ****** ****** *)

(* end of [ats_dynexp2_print.dats] *)
