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

// Time: January 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Eff = "ats_effect.sats"
staload Lab = "ats_label.sats"

(* ****** ****** *)

staload "ats_dynexp3.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

implement fprint_p3at (pf | out, p3t) = case+ p3t.p3at_node of
  | P3Tann (p3t, s2e) => begin
      fprint (pf | out, "P3Tann(");
      fprint (pf | out, p3t);
      fprint (pf | out, "; ");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | P3Tany d2v => begin
      fprint (pf | out, "P3Tany(");
      fprint (pf | out, d2v);
      fprint (pf | out, ")")
    end
  | P3Tas (refknd, d2v, p3t) => begin
      fprint (pf | out, "P3Tas(");
      if (refknd > 0) then fprint (pf | out, "!");
      fprint (pf | out, d2v);
      fprint (pf | out, "; ");
      fprint (pf | out, p3t);
      fprint (pf | out, ")")
    end
  | P3Tbool b => begin
      fprint (pf | out, "P3Tbool(");
      fprint (pf | out, b);
      fprint (pf | out, ")")
    end
  | P3Tchar c => begin
      fprint (pf | out, "P3Tchar(");
      fprint (pf | out, c);
      fprint (pf | out, ")")
    end
  | P3Tcon (refknd, d2c, npf, p3ts) => begin
      fprint (pf | out, "P3Tcon(");
      fprint (pf | out, refknd);
      fprint (pf | out, "; ");
      fprint (pf | out, d2c);
      fprint (pf | out, "; ");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, p3ts);
      fprint (pf | out, ")")
    end
  | P3Tempty () => begin
      fprint (pf | out, "P3Tempty()")
    end
  | P3Texist (s2vs, p3t) => begin
      fprint (pf | out, "P3Texist(");
      fprint (pf | out, s2vs);
      fprint (pf | out, "; ");
      fprint (pf | out, p3t);
      fprint (pf | out, ")")
    end
  | P3Tfloat str => begin
      fprintf (pf | out, "P3Tfloat(%s)", @(str))
    end
  | P3Tint (str, int) => begin
      fprintf (pf | out, "P3Tint(%s)", @(str))
    end
  | P3Tlst (s2e, p3ts) => begin
      fprint (pf | out, "P3Tlst(");
      fprint (pf | out, s2e);
      fprint (pf | out, "; ");
      fprint (pf | out, p3ts);
      fprint (pf | out, ")")
    end
  | P3Trec (recknd, npf, lp3ts) => begin
      fprint (pf | out, "P3Trec(...)")
    end
  | P3Tstring str => begin
      fprintf (pf | out, "P3Tstring(\"%s\")", @(str))
    end
  | P3Tvar (refknd, d2v) => begin
      fprint (pf | out, "P3Tvar(");
      if (refknd > 0) then fprint (pf | out, "!");
      fprint (pf | out, d2v);
      fprint (pf | out, ")")
    end
  | P3Tvbox (d2v) => begin
      fprint (pf | out, "P3Tvbox(");
      fprint (pf | out, d2v);
      fprint (pf | out, ")")
    end
(*
  | _ => begin
      fprint (pf | out, "fprint_p3at: not implemented yet");
      fprint_newline (pf | out);
      exit (1)
    end
*)

implement fprint_p3atlst {m} (pf | out, p3ts) = let
  fun aux (out: &FILE m, i: int, p3ts: p3atlst)
    : void = begin case+ p3ts of
    | cons (p3t, p3ts) => begin
        if (i > 0) then fprint (pf | out, ", ");
        fprint (pf | out, p3t); aux (out, i + 1, p3ts)
      end
    | nil () => ()
  end // end of [aux]
in
  aux (out, 0, p3ts)
end // end of [fprint_p3atlst]

(* ****** ****** *)

implement print_p3at (p3t) = print_mac (fprint_p3at, p3t)
implement prerr_p3at (p3t) = prerr_mac (fprint_p3at, p3t)

(* ****** ****** *)

implement fprint_d3exp (pf | out, d3e) = begin
  case+ d3e.d3exp_node of
  | D3Eann_type (d3e, s2e) => begin
      fprint (pf | out, "D3Eann_type(");
      fprint (pf | out, d3e);
      fprint (pf | out, "; ");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | D3Eapp_dyn (d3e_fun, npf, d3es_arg) => begin
      fprint (pf | out, "D3Eapp_dyn(");
      fprint (pf | out, d3e_fun);
      fprint (pf | out, "; ");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, d3es_arg);
      fprint (pf | out, ")")
    end
  | D3Eapp_sta d3e => begin
      fprint (pf | out, "D3Eapp_sta(");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Earr (s2e, d3es) => begin
      fprint (pf | out, "D3Earr(");
      fprint (pf | out, s2e);
      fprint (pf | out, "; ");
      fprint (pf | out, d3es);
      fprint (pf | out, ")")
    end
  | D3Eassgn_ptr (d3e_ptr, d3ls, d3e_val) => begin
      fprint (pf | out, "D3Eassgn_ptr(");
      fprint (pf | out, d3e_ptr);
      fprint (pf | out, "; ");
      fprint (pf | out, d3ls);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e_val);
      fprint (pf | out, ")")
    end
  | D3Eassgn_var (d2v_ptr, d3ls, d3e_val) => begin
      fprint (pf | out, "D3Eassgn_val(");
      fprint (pf | out, d2v_ptr);
      fprint (pf | out, "; ");
      fprint (pf | out, d3ls);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e_val);
      fprint (pf | out, ")")
    end
  | D3Ecaseof (knd, d3es, c3ls) => begin
      fprint (pf | out, "D3Ecaseof(...)")
    end
  | D3Echar chr => begin
      fprint (pf | out, "D3Echar(");
      fprint (pf | out, chr);
      fprint (pf | out, ")")
    end
  | D3Econ (d2c, npf, d3es) => begin
      fprint (pf | out, "D3Econ(");
      fprint (pf | out, d2c);
      fprint (pf | out, "; ");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, d3es);
      fprint (pf | out, ")")
    end
  | D3Ecst d2c => begin
      fprint (pf | out, "D3Ecst(");
      fprint (pf | out, d2c);
      fprint (pf | out, ")")
    end
  | D3Ecrypt (knd, d3e) => begin
      fprint (pf | out, "D3Ecrypt(");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Edelay (lin, d3e) => begin
      fprint (pf | out, "D3Edelay(");
      fprint (pf | out, lin);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Edynload fil => begin
      fprint (pf | out, "D3Edynload(");
      $Fil.fprint_filename (pf | out, fil);
      fprint (pf | out, ")")
    end
  | D3Eeffmask (effs, d3e) => begin
      fprint (pf | out, "D3Eeffmask(");
      $Eff.fprint_effectlst (pf | out, effs);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Eempty () => begin
      fprint (pf | out, "D3Eempty()")
    end
  | D3Eextval (str) => begin
      fprintf (pf | out, "D3Eextval(\"%s\")", @(str))
    end
  | D3Efix (d2v, d3e) => begin
      fprint (pf | out, "D3Efix(");
      fprint (pf | out, d2v);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Efloat (str) => begin
      fprintf (pf | out, "D3Efloat(%s)", @(str))
    end
  | D3Efloatsp (str) => begin
      fprintf (pf | out, "D3Efloatsp(%s)", @(str))
    end
  | D3Efoldat d3e => begin
      fprint (pf | out, "D3Efoldat(");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Efor (d3e_init, d3e_test, d3e_post, d3e_body) => begin
      fprint (pf | out, "D3Efor(");
      fprint (pf | out, d3e_init);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e_test);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e_post);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e_body);
      fprint (pf | out, ")")
    end
  | D3Efreeat d3e => begin
      fprint (pf | out, "D3Efreeat(");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Eif (d3e_cond, d3e_then, d3e_else) => begin
      fprint (pf | out, "D3Eif(");
      fprint (pf | out, d3e_cond);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e_then);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e_else);
      fprint (pf | out, ")")
    end
  | D3Eint (str, _(*intinf*)) => begin
      fprintf (pf | out, "D3Eint(%s)", @(str))
    end
  | D3Eintsp (str, _(*intinf*)) => begin
      fprintf (pf | out, "D3Eintsp(%s)", @(str))
    end
  | D3Elam_dyn (lin, npf, p3ts, d3e) => begin
      fprint (pf | out, "D3Elam_dyn(");
      fprint (pf | out, lin);
      fprint (pf | out, "; ");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, p3ts);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Elam_met (s2es, d3e) => begin
      fprint (pf | out, "D3Elam_met(");
      fprint (pf | out, s2es);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Elam_sta (s2vs, s2ps, d3e) => begin
      fprint (pf | out, "D3Elam_sta(");
      fprint (pf | out, s2vs);
      fprint (pf | out, "; ");
      fprint (pf | out, s2ps);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Elet (d3cs, d3e) => begin
      fprint (pf | out, "D3Elet(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Eloopexn i => begin
      fprintf (pf | out, "D3Eloopexn(%i)", @(i))
    end
  | D3Elst (lin, s2e, d3es) => begin
      fprint (pf | out, "D3Elst(");
      fprint (pf | out, s2e);
      fprint (pf | out, "; ");
      fprint (pf | out, d3es);
      fprint (pf | out, ")")
    end
  | D3Emod d3cs => begin
      fprint (pf | out, "D3Emod(...)")
    end
  | D3Eptrof_ptr (d3e, d3ls) => begin
      fprint (pf | out, "D3Eptrof_ptr(");
      fprint (pf | out, d3e);
      fprint (pf | out, "; ");
      fprint (pf | out, d3ls);
      fprint (pf | out, ")")
    end
  | D3Eptrof_var (d2v, d3ls) => begin
      fprint (pf | out, "D3Eptrof_var(");
      fprint (pf | out, d2v);
      fprint (pf | out, "; ");
      fprint (pf | out, d3ls);
      fprint (pf | out, ")")
    end
  | D3Eraise (d3e_exn) => begin
      fprint (pf | out, "D3Eraise(");
      fprint (pf | out, d3e_exn);
      fprint (pf | out, ")")
    end
  | D3Erec (knd, npf, ld3es) => begin
      fprint (pf | out, "D3Erec(");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, ld3es);
      fprint (pf | out, ")")
    end
  | D3Erefarg (refval, freeknd, d3e) => begin
      fprint (pf | out, "D3Etrans(");
      fprint (pf | out, refval);
      fprint (pf | out, "; ");
      fprint (pf | out, freeknd);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Esel (d3e, d3ls) => begin
      fprint (pf | out, "D3Esel(");
      fprint (pf | out, d3e);
      fprint (pf | out, "; ");
      fprint (pf | out, d3ls);
      fprint (pf | out, ")")
    end
  | D3Esel_ptr (d3e, d3ls) => begin
      fprint (pf | out, "D3Esel_ptr(");
      fprint (pf | out, d3e);
      fprint (pf | out, "; ");
      fprint (pf | out, d3ls);
      fprint (pf | out, ")")
    end
  | D3Esel_var (d2v, d3ls) => begin
      fprint (pf | out, "D3Esel_var(");
      fprint (pf | out, d2v);
      fprint (pf | out, "; ");
      fprint (pf | out, d3ls);
      fprint (pf | out, ")")
    end
  | D3Eseq d3es => begin
      fprint (pf | out, "D3Eseq(");
      fprint (pf | out, d3es);
      fprint (pf | out, ")")
    end
  | D3Esif (s2e_cond, d3e_then, d3e_else) => begin
      fprint (pf | out, "D3Esif(");
      fprint (pf | out, s2e_cond);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e_then);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e_else);
      fprint (pf | out, ")")
    end
  | D3Espawn (d3e) => begin
      fprint (pf | out, "D3Espawn(");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Estring (str, len) => begin
      fprintf (pf | out, "D3Estring(\"%s\", %i)", @(str, len))
    end
  | D3Estruct (ld3es) => begin
      fprint (pf | out, "D3Estruct(");
      fprint (pf | out, ld3es);
      fprint (pf | out, ")")
    end
  | D3Etmpcst (d2c, s2ess) => begin
      fprint (pf | out, "D3Etmpcst(");
      fprint (pf | out, d2c);
      fprint (pf | out, "; ");
      fprint (pf | out, s2ess);
      fprint (pf | out, ")")
    end
  | D3Etmpvar (d2v, s2ess) => begin
      fprint (pf | out, "D3Etmpvar(");
      fprint (pf | out, d2v);
      fprint (pf | out, "; ");
      fprint (pf | out, s2ess);
      fprint (pf | out, ")")
    end
  | D3Etop () => begin
      fprint (pf | out, "D3Etop()")
    end
  | D3Etrywith (d3e, c3ls) => begin
      fprint (pf | out, "D3Etrywith(...)")
    end
  | D3Evar d2v => begin
      fprint (pf | out, "D3Evar(");
      fprint (pf | out, d2v);
      fprint (pf | out, ")")
    end
  | D3Eviewat_assgn_ptr (d3e_l, d3ls, d3e_r) => begin
      fprint (pf | out, "D3Eviewat_assgn_ptr(");
      fprint (pf | out, d3e_l);
      fprint (pf | out, "; ");
      fprint (pf | out, d3ls);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e_r);
      fprint (pf | out, ")")
    end
  | D3Eviewat_assgn_var (d2v_l, d3ls, d3e_r) => begin
      fprint (pf | out, "D3Eviewat_assgn_var(");
      fprint (pf | out, d2v_l);
      fprint (pf | out, "; ");
      fprint (pf | out, d3ls);
      fprint (pf | out, "; ");
      fprint (pf | out, d3e_r);
      fprint (pf | out, ")")
    end
  | D3Eviewat_ptr (d3e, _, _, _) => begin
      fprint (pf | out, "D3Eviewat_ptr(");
      fprint (pf | out, d3e);
      fprint (pf | out, ")")
    end
  | D3Eviewat_var (d2v, _, _, _) => begin
      fprint (pf | out, "D3Eviewat_var(");
      fprint (pf | out, d2v);
      fprint (pf | out, ")")
    end
  | D3Ewhere (d3e, d3cs) => begin
      fprint (pf | out, "D3Ewhere(");
      fprint (pf | out, d3e);
      fprint (pf | out, "; ");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | D3Ewhile (d3e_test, d3e_body) => begin
      fprint (pf | out, "D3Ewhile(");
      fprint (pf | out, d3e_test);
      fprint (pf | out, d3e_body);
      fprint (pf | out, ")")
    end
(*
  | _ => begin
      fprint (pf | out, "[...]")
    end
*)
end // end of [fprint_d3exp]

implement fprint_d3explst {m} (pf | out, d3es) = let
  fun aux (out: &FILE m, i: int, d3es: d3explst)
    : void = begin case+ d3es of
    | cons (d3e, d3es) => begin
        if (i > 0) then fprint (pf | out, ", ");
        fprint (pf | out, d3e); aux (out, i + 1, d3es)
      end
    | nil () => ()
  end // end of [aux]
in
  aux (out, 0, d3es)
end // end of [fprint_d3explst]

implement fprint_d3explstlst {m} (pf | out, d3ess) = let
  fun aux (out: &FILE m, i: int, d3ess: d3explstlst)
    : void = begin case+ d3ess of
    | cons (d3es, d3ess) => begin
        if (i > 0) then fprint (pf | out, ", ");
        fprint (pf | out, d3es); aux (out, i + 1, d3ess)
      end
    | nil () => ()
  end // end of [aux]
in
  aux (out, 0, d3ess)
end // end of [fprint_d3explstlst]

implement fprint_labd3explst {m} (pf | out, ld3es0) = let
  fun aux
    (out: &FILE m, i: int, ld3es: labd3explst)
    : void = begin case+ ld3es of
    | LABD3EXPLSTcons (l, d3e, ld3es) => begin
        if i > 0 then fprint (pf | out, ", ");
        $Lab.fprint_label (pf | out, l);
        fprint (pf | out, "= ");
        fprint (pf | out, d3e);
        aux (out, i+1, ld3es)
      end
    | LABD3EXPLSTnil () => ()
    end // end of [aux]
in
  aux (out, 0, ld3es0)
end // end of [fprint_labd3explst]

(* ****** ****** *)

implement fprint_d3lab1 (pf | out, d3l) = begin
  case+ d3l.d3lab1_node of
  | D3LAB1lab (l, s2e_rec) => begin
      $Lab.fprint_label (pf | out, l);
      fprint (pf | out, "(");
      fprint (pf | out, s2e_rec);
      fprint (pf | out, ")")
    end
  | D3LAB1ind (d3ess_ind, s2e_elt) => begin
      fprint (pf | out, "[");
      fprint (pf | out, d3ess_ind);
      fprint (pf | out, "]");
      fprint (pf | out, "(");
      fprint (pf | out, s2e_elt);
      fprint (pf | out, ")")
    end
end // end of [fprint_d3lab1]

implement fprint_d3lab1lst {m} (pf | out, d3ls) = let
  fun aux (out: &FILE m, i: int, d3ls: d3lab1lst)
    : void = begin case+ d3ls of
    | cons (d3l, d3ls) => begin
        if (i > 0) then fprint (pf | out, ", ");
        fprint (pf | out, d3l); aux (out, i + 1, d3ls)
      end
    | nil () => ()
  end // end of [aux]
in
  aux (out, 0, d3ls)
end // end of [fprint_d3lab1lst]

(* ****** ****** *)

implement print_d3exp (d3e) = print_mac (fprint_d3exp, d3e)
implement prerr_d3exp (d3e) = prerr_mac (fprint_d3exp, d3e)

implement print_d3explst (d3es) = print_mac (fprint_d3explst, d3es)
implement prerr_d3explst (d3es) = prerr_mac (fprint_d3explst, d3es)

implement print_d3explstlst (d3ess) = print_mac (fprint_d3explstlst, d3ess)
implement prerr_d3explstlst (d3ess) = prerr_mac (fprint_d3explstlst, d3ess)

implement print_labd3explst (ld3es) = print_mac (fprint_labd3explst, ld3es)
implement prerr_labd3explst (ld3es) = prerr_mac (fprint_labd3explst, ld3es)

(* ****** ****** *)

(* end of [ats_dynexp3_print.dats] *)
