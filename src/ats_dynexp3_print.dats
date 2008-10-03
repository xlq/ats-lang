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

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_dynexp3.sats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

macdef fprint_label = $Lab.fprint_label

(* ****** ****** *)

implement fprint_p3at (pf | out, p3t) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ p3t.p3at_node of
  | P3Tann (p3t, s2e) => begin
      strpr "P3Tann(";
      fprint_p3at (pf | out, p3t);
      strpr "; ";
      fprint_s2exp (pf | out, s2e);
      strpr ")"
    end
  | P3Tany d2v => begin
      strpr "P3Tany("; fprint_d2var (pf | out, d2v); strpr ")"
    end
  | P3Tas (refknd, d2v, p3t) => begin
      strpr "P3Tas(";
      if (refknd > 0) then strpr "!";
      fprint_d2var (pf | out, d2v);
      strpr "; ";
      fprint_p3at (pf | out, p3t);
      strpr ")"
    end // end of [P3Tas]
  | P3Tbool b => begin
      strpr "P3Tbool("; fprint1_bool (pf | out, b); strpr ")"
    end
  | P3Tchar c => begin
      strpr "P3Tchar("; fprint1_char (pf | out, c); strpr ")"
    end
  | P3Tcon (refknd, d2c, npf, p3ts) => begin
      strpr "P3Tcon(";
      fprint1_int (pf | out, refknd);
      strpr "; ";
      fprint_d2con (pf | out, d2c);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_p3atlst (pf | out, p3ts);
      strpr ")"
    end // end of [P3Tcon]
  | P3Tempty () => begin
      fprint1_string (pf | out, "P3Tempty()")
    end
  | P3Texist (s2vs, p3t) => begin
      strpr "P3Texist(";
      fprint_s2varlst (pf | out, s2vs);
      strpr "; ";
      fprint_p3at (pf | out, p3t);
      strpr ")"
    end // end of [P3Texist]
  | P3Tfloat str => begin
      fprintf1_exn (pf | out, "P3Tfloat(%s)", @(str))
    end
  | P3Tint (str, int) => begin
      fprintf1_exn (pf | out, "P3Tint(%s)", @(str))
    end
  | P3Tlst (s2e, p3ts) => begin
      strpr "P3Tlst(";
      fprint_s2exp (pf | out, s2e);
      strpr "; ";
      fprint_p3atlst (pf | out, p3ts);
      strpr ")"
    end // end of [P3Tlst]
  | P3Trec (recknd, npf, lp3ts) => begin
      fprint1_string (pf | out, "P3Trec(...)")
    end // end of [P3Trec]
  | P3Tstring str => begin
      fprintf1_exn (pf | out, "P3Tstring(\"%s\")", @(str))
    end // end of [P3Tstring]
  | P3Tvar (refknd, d2v) => begin
      strpr "P3Tvar(";
      if (refknd > 0) then strpr "!";
      fprint_d2var (pf | out, d2v);
      strpr ")"
    end
  | P3Tvbox (d2v) => begin
      strpr "P3Tvbox("; fprint_d2var (pf | out, d2v); strpr ")"
    end
(*
  | _ => begin
      strpr "fprint_p3at: not implemented yet"; fprint_newline (pf | out);
      exit (1)
    end
*)
end // end of [fprint_p3at]

implement fprint_p3atlst {m} (pf | out, p3ts) = let
  fun aux (out: &FILE m, i: int, p3ts: p3atlst)
    : void = begin case+ p3ts of
    | cons (p3t, p3ts) => begin
        if (i > 0) then fprint1_string (pf | out, ", ");
        fprint_p3at (pf | out, p3t); aux (out, i + 1, p3ts)
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

implement fprint_d3exp (pf | out, d3e) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ d3e.d3exp_node of
  | D3Eann_type (d3e, s2e) => begin
      strpr "D3Eann_type(";
      fprint_d3exp (pf | out, d3e);
      strpr "; ";
      fprint_s2exp (pf | out, s2e);
      strpr ")"
    end
  | D3Eapp_dyn (d3e_fun, npf, d3es_arg) => begin
      strpr "D3Eapp_dyn(";
      fprint_d3exp (pf | out, d3e_fun);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_d3explst (pf | out, d3es_arg);
      strpr ")"
    end
  | D3Eapp_sta d3e => begin
      strpr "D3Eapp_sta("; fprint_d3exp (pf | out, d3e); strpr ")"
    end
  | D3Earr (s2e, d3es) => begin
      strpr "D3Earr(";
      fprint_s2exp (pf | out, s2e);
      strpr "; ";
      fprint_d3explst (pf | out, d3es);
      strpr ")"
    end
  | D3Eassgn_ptr (d3e_ptr, d3ls, d3e_val) => begin
      strpr "D3Eassgn_ptr(";
      fprint_d3exp (pf | out, d3e_ptr);
      strpr "; ";
      fprint_d3lab1lst (pf | out, d3ls);
      strpr "; ";
      fprint_d3exp (pf | out, d3e_val);
      strpr ")"
    end // end of [D3Eassgn_ptr]
  | D3Eassgn_var (d2v_ptr, d3ls, d3e_val) => begin
      strpr "D3Eassgn_val(";
      fprint_d2var (pf | out, d2v_ptr);
      strpr "; ";
      fprint_d3lab1lst (pf | out, d3ls);
      strpr "; ";
      fprint_d3exp (pf | out, d3e_val);
      strpr ")"
    end // end of [D3Eassgn_var]
  | D3Ecaseof (knd, d3es, c3ls) => begin
      fprint1_string (pf | out, "D3Ecaseof(...)")
    end
  | D3Echar chr => begin
      strpr "D3Echar("; fprint1_char (pf | out, chr); strpr ")"
    end
  | D3Econ (d2c, npf, d3es) => begin
      strpr "D3Econ(";
      fprint_d2con (pf | out, d2c);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_d3explst (pf | out, d3es);
      strpr ")"
    end // end of [D3Econ]
  | D3Ecst d2c => begin
      strpr "D3Ecst("; fprint_d2cst (pf | out, d2c); strpr ")"
    end
  | D3Ecrypt (knd, d3e) => begin
      strpr "D3Ecrypt(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_d3exp (pf | out, d3e);
      strpr ")"
    end // end of [D3Ecrypt]
  | D3Edelay (lin, d3e) => begin
      strpr "D3Edelay(";
      fprint1_int (pf | out, lin);
      strpr "; ";
      fprint_d3exp (pf | out, d3e);
      strpr ")"
    end // end of [D3Edelay]
  | D3Edynload fil => begin
      strpr "D3Edynload(";
      $Fil.fprint_filename (pf | out, fil);
      strpr ")"
    end
  | D3Eeffmask (effs, d3e) => begin
      strpr "D3Eeffmask(";
      $Eff.fprint_effectlst (pf | out, effs);
      strpr "; ";
      fprint_d3exp (pf | out, d3e);
      strpr ")"
    end
  | D3Eempty () => begin
      fprint1_string (pf | out, "D3Eempty()")
    end
  | D3Eextval (str) => begin
      fprintf1_exn (pf | out, "D3Eextval(\"%s\")", @(str))
    end
  | D3Efix (d2v, d3e) => begin
      strpr "D3Efix(";
      fprint_d2var (pf | out, d2v);
      strpr "; ";
      fprint_d3exp (pf | out, d3e);
      strpr ")"
    end // end of [D3Efix]
  | D3Efloat (str) => begin
      fprintf1_exn (pf | out, "D3Efloat(%s)", @(str))
    end
  | D3Efloatsp (str) => begin
      fprintf1_exn (pf | out, "D3Efloatsp(%s)", @(str))
    end
  | D3Efoldat d3e => begin
      strpr "D3Efoldat("; fprint_d3exp (pf | out, d3e); strpr ")"
    end
  | D3Efreeat d3e => begin
      strpr "D3Efreeat("; fprint_d3exp (pf | out, d3e); strpr ")"
    end
  | D3Eif (d3e_cond, d3e_then, d3e_else) => begin
      strpr "D3Eif(";
      fprint_d3exp (pf | out, d3e_cond);
      strpr "; ";
      fprint_d3exp (pf | out, d3e_then);
      strpr "; ";
      fprint_d3exp (pf | out, d3e_else);
      strpr ")"
    end // end of [D3Eif]
  | D3Eint (str, _(*intinf*)) => begin
      fprintf1_exn (pf | out, "D3Eint(%s)", @(str))
    end
  | D3Eintsp (str, _(*intinf*)) => begin
      fprintf1_exn (pf | out, "D3Eintsp(%s)", @(str))
    end
  | D3Elam_dyn (lin, npf, p3ts, d3e) => begin
      strpr "D3Elam_dyn(";
      fprint1_int (pf | out, lin);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_p3atlst (pf | out, p3ts);
      strpr "; ";
      fprint_d3exp (pf | out, d3e);
      strpr ")"
    end // end of [D3Elam_dyn]
  | D3Elam_met (s2es, d3e) => begin
      strpr "D3Elam_met(";
      fprint_s2explst (pf | out, s2es);
      strpr "; ";
      fprint_d3exp (pf | out, d3e);
      strpr ")"
    end // end of [D3Elam_met]
  | D3Elam_sta (s2vs, s2ps, d3e) => begin
      strpr "D3Elam_sta(";
      fprint_s2varlst (pf | out, s2vs);
      strpr "; ";
      fprint_s2explst (pf | out, s2ps);
      strpr "; ";
      fprint_d3exp (pf | out, d3e);
      strpr ")"
    end // end of [D3Elam_sta]
  | D3Elet (d3cs, d3e) => begin
      strpr "D3Elet(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_d3exp (pf | out, d3e);
      strpr ")"
    end // end of [D3Elet]
  | D3Eloop (od3e_init, d3e_test, od3e_post, d3e_body) => begin
      strpr "D3Eloop(";
      begin case+ od3e_init of
        | None () => () | Some d3e => fprint_d3exp (pf | out, d3e);
      end;
      strpr "; ";
      fprint_d3exp (pf | out, d3e_test);
      strpr "; ";
      begin case+ od3e_post of
        | None () => () | Some d3e => fprint_d3exp (pf | out, d3e)
      end;
      strpr "; ";
      fprint_d3exp (pf | out, d3e_body);
      strpr ")"
    end // end of [D3Eloop]
  | D3Eloopexn i => begin
      fprintf1_exn (pf | out, "D3Eloopexn(%i)", @(i))
    end
  | D3Elst (lin, s2e, d3es) => begin
      strpr "D3Elst(";
      fprint_s2exp (pf | out, s2e);
      strpr "; ";
      fprint_d3explst (pf | out, d3es);
      strpr ")"
    end // end of [D3Elst]
  | D3Emod d3cs => begin
      fprint1_string (pf | out, "D3Emod(...)")
    end
  | D3Eptrof_ptr (d3e, d3ls) => begin
      strpr "D3Eptrof_ptr(";
      fprint_d3exp (pf | out, d3e);
      strpr "; ";
      fprint_d3lab1lst (pf | out, d3ls);
      strpr ")"
    end // end of [D3Eptrof_ptr]
  | D3Eptrof_var (d2v, d3ls) => begin
      strpr "D3Eptrof_var(";
      fprint_d2var (pf | out, d2v);
      strpr "; ";
      fprint_d3lab1lst (pf | out, d3ls);
      strpr ")"
    end // end of [D3Eptrof_var]
  | D3Eraise (d3e_exn) => begin
      strpr "D3Eraise("; fprint_d3exp (pf | out, d3e_exn); strpr ")"
    end // end of [D3Eraise]
  | D3Erec (knd, npf, ld3es) => begin
      strpr "D3Erec(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_labd3explst (pf | out, ld3es);
      strpr ")"
    end // end of [D3Erec]
  | D3Erefarg (refval, freeknd, d3e) => begin
      strpr "D3Erefarg(";
      fprint1_int (pf | out, refval);
      strpr "; ";
      fprint1_int (pf | out, freeknd);
      strpr "; ";
      fprint_d3exp (pf | out, d3e);
      strpr ")"
    end // end of [D3Erefarg]
  | D3Esel (d3e, d3ls) => begin
      strpr "D3Esel(";
      fprint_d3exp (pf | out, d3e);
      strpr "; ";
      fprint_d3lab1lst (pf | out, d3ls);
      strpr ")"
    end // end of [D3Esel]
  | D3Esel_ptr (d3e, d3ls) => begin
      strpr "D3Esel_ptr(";
      fprint_d3exp (pf | out, d3e);
      strpr "; ";
      fprint_d3lab1lst (pf | out, d3ls);
      strpr ")"
    end // end of [D3Esel_ptr]
  | D3Esel_var (d2v, d3ls) => begin
      strpr "D3Esel_var(";
      fprint_d2var (pf | out, d2v);
      strpr "; ";
      fprint_d3lab1lst (pf | out, d3ls);
      strpr ")"
    end // end of [D3Esel_var]
  | D3Eseq d3es => begin
      strpr "D3Eseq("; fprint_d3explst (pf | out, d3es); strpr ")"
    end
  | D3Esif (s2e_cond, d3e_then, d3e_else) => begin
      strpr "D3Esif(";
      fprint_s2exp (pf | out, s2e_cond);
      strpr "; ";
      fprint_d3exp (pf | out, d3e_then);
      strpr "; ";
      fprint_d3exp (pf | out, d3e_else);
      strpr ")"
    end // end of [sif]
  | D3Espawn (d3e) => begin
      strpr "D3Espawn("; fprint_d3exp (pf | out, d3e); strpr ")"
    end
  | D3Estring (str, len) => begin
      fprintf1_exn (pf | out, "D3Estring(\"%s\", %i)", @(str, len))
    end
  | D3Estruct (ld3es) => begin
      strpr "D3Estruct("; fprint_labd3explst (pf | out, ld3es); strpr ")"
    end // end of [D3Estruct]
  | D3Etmpcst (d2c, s2ess) => begin
      strpr "D3Etmpcst(";
      fprint_d2cst (pf | out, d2c);
      strpr "; ";
      fprint_s2explstlst (pf | out, s2ess);
      strpr ")"
    end // end of [D3Etmpcst]
  | D3Etmpvar (d2v, s2ess) => begin
      strpr "D3Etmpvar(";
      fprint_d2var (pf | out, d2v);
      strpr "; ";
      fprint_s2explstlst (pf | out, s2ess);
      strpr ")"
    end // end of [D3Etmpvar]
  | D3Etop () => begin
      fprint1_string (pf | out, "D3Etop()")
    end // end of [D3Etop]
  | D3Etrywith (d3e, c3ls) => begin
      fprint1_string (pf | out, "D3Etrywith(...)")
    end // end of [trywith]
  | D3Evar d2v => begin
      strpr "D3Evar("; fprint_d2var (pf | out, d2v); strpr ")"
    end // end of [D3Evar]
  | D3Eviewat_assgn_ptr (d3e_l, d3ls, d3e_r) => begin
      strpr "D3Eviewat_assgn_ptr(";
      fprint_d3exp (pf | out, d3e_l);
      strpr "; ";
      fprint_d3lab1lst (pf | out, d3ls);
      strpr "; ";
      fprint_d3exp (pf | out, d3e_r);
      strpr ")"
    end // end of [D3Eviewat_assgn_ptr]
  | D3Eviewat_assgn_var (d2v_l, d3ls, d3e_r) => begin
      strpr "D3Eviewat_assgn_var(";
      fprint_d2var (pf | out, d2v_l);
      strpr "; ";
      fprint_d3lab1lst (pf | out, d3ls);
      strpr "; ";
      fprint_d3exp (pf | out, d3e_r);
      strpr ")"
    end // end of [D3Eviewat_assgn_var]
  | D3Eviewat_ptr (d3e, _, _, _) => begin
      strpr "D3Eviewat_ptr("; fprint_d3exp (pf | out, d3e); strpr ")"
    end // end of [D3Eviewat_ptr]
  | D3Eviewat_var (d2v, _, _, _) => begin
      strpr "D3Eviewat_var("; fprint_d2var (pf | out, d2v); strpr ")"
    end // end of [D3Eviewat_var]
  | D3Ewhere (d3e, d3cs) => begin
      strpr "D3Ewhere(";
      fprint_d3exp (pf | out, d3e);
      strpr "; ";
      fprint1_string (pf | out, "...");
      strpr ")"
    end // end of [D3Ewhere]
(*
  | _ => begin
      fprint1_string (pf | out, "[...]")
    end
*)
end // end of [fprint_d3exp]

implement fprint_d3explst {m} (pf | out, d3es) = let
  fun aux (out: &FILE m, i: int, d3es: d3explst)
    : void = begin case+ d3es of
    | cons (d3e, d3es) => begin
        if (i > 0) then fprint1_string (pf | out, ", ");
        fprint_d3exp (pf | out, d3e); aux (out, i + 1, d3es)
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
        if (i > 0) then fprint1_string (pf | out, ", ");
        fprint_d3explst (pf | out, d3es); aux (out, i + 1, d3ess)
      end
    | nil () => ()
  end // end of [aux]
in
  aux (out, 0, d3ess)
end // end of [fprint_d3explstlst]

implement fprint_labd3explst {m} (pf | out, ld3es0) = let
  fun aux (out: &FILE m, i: int, ld3es: labd3explst): void = let
    macdef strpr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ ld3es of
    | LABD3EXPLSTcons (l, d3e, ld3es) => begin
        if i > 0 then strpr ", ";
        fprint_label (pf | out, l); strpr "= ";
        fprint_d3exp (pf | out, d3e); aux (out, i+1, ld3es)
      end
    | LABD3EXPLSTnil () => ()
    end // end of [aux]
in
  aux (out, 0, ld3es0)
end // end of [fprint_labd3explst]

(* ****** ****** *)

implement fprint_d3lab1 (pf | out, d3l) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ d3l.d3lab1_node of
  | D3LAB1lab (l, s2e_rec) => begin
      fprint_label (pf | out, l);
      strpr "("; fprint_s2exp (pf | out, s2e_rec); strpr ")"
    end // end of [D3LAB1lab]
  | D3LAB1ind (d3ess_ind, s2e_elt) => begin
      strpr "[";
      fprint_d3explstlst (pf | out, d3ess_ind);
      strpr "]";
      strpr "(";
      fprint_s2exp (pf | out, s2e_elt);
      strpr ")"
    end // end of [D3LAB1ind]
end // end of [fprint_d3lab1]

implement fprint_d3lab1lst {m} (pf | out, d3ls) = let
  fun aux (out: &FILE m, i: int, d3ls: d3lab1lst)
    : void = begin case+ d3ls of
    | cons (d3l, d3ls) => begin
        if (i > 0) then fprint1_string (pf | out, ", ");
        fprint_d3lab1 (pf | out, d3l); aux (out, i + 1, d3ls)
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
