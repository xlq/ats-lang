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

// Time: March 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

(* high-level intermediate representation *)

(* ****** ****** *)

staload Fil = "ats_filename.sats"
staload IntInf = "ats_intinf.sats"
staload Lab = "ats_label.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"

(* ****** ****** *)

implement fprint_hityp (pf | out, hit) = begin
  case+ hit.hityp_node of
  | HITfun (fc, hits_arg, hit_res) => begin
      fprint (pf | out, "HITfun(");
      $Syn.fprint_funclo (pf | out, fc);
      fprint (pf | out, "; ");
      fprint (pf | out, hits_arg);
      fprint (pf | out, "; ");
      fprint (pf | out, hit_res);
      fprint (pf | out, ")")
    end
  | HITrefarg (refval, hit) => begin
      fprint (pf | out, "HITrefarg(");
      fprint_int (pf | out, refval);
      fprint (pf | out, "; ");
      fprint_hityp (pf | out, hit);
      fprint (pf | out, ")")
    end
  | HITtyrectemp (knd, lhits) => begin
      fprint (pf | out, "HITtyrectemp(...)")
    end
  | HITtysumtemp (d2c, hits) => begin
      fprint (pf | out, "HITsumtemp(");
      fprint (pf | out, d2c);
      fprint (pf | out, "; ");
      fprint (pf | out, hits);
      fprint (pf | out, ")")
    end
  | HITs2var s2v => begin
      fprint (pf | out, "HITs2var(");
      fprint (pf | out, s2v);
      fprint (pf | out, ")")
    end
  | _ => let
      val HITNAM (knd, name) = hit.hityp_name
    in
      if knd > 0 then fprint (pf | out, "*");
      fprint (pf | out, name)
    end
end // end of [fprint_hityp]

implement fprint_hityplst {m} (pf | out, hits0) = let
  fun aux (out: &FILE m, i: int, hits: hityplst): void =
    case+ hits of
    | list_cons (hit, hits) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_hityp (pf | out, hit); aux (out, i+1, hits)
      end
    | list_nil () => ()
in
  aux (out, 0, hits0)
end // end of [fprint_hityplst]

implement fprint_hityplstlst {m} (pf | out, hitss0) = let
  fun aux (out: &FILE m, i: int, hitss: hityplstlst): void =
    case+ hitss of
    | list_cons (hits, hitss) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_hityplst (pf | out, hits); aux (out, i+1, hitss)
      end
    | list_nil () => ()
in
  aux (out, 0, hitss0)
end // end of [fprint_hityplstlst]

(* ****** ****** *)

implement print_hityp (hit) = print_mac (fprint_hityp, hit)
implement prerr_hityp (hit) = prerr_mac (fprint_hityp, hit)

implement print_hityplst (hits) = print_mac (fprint_hityplst, hits)
implement prerr_hityplst (hits) = prerr_mac (fprint_hityplst, hits)

(* ****** ****** *)

implement fprint_hipat (pf | out, hip0) = begin
  case+ hip0.hipat_node of
  | HIPann (hip, hit_ann) => begin
      fprint (pf | out, "HIPann(");
      fprint (pf | out, hip);
      fprint (pf | out, "; ");
      fprint (pf | out, hit_ann);
      fprint (pf | out, ")")
    end
  | HIPany () => begin
      fprint (pf | out, "HIPany()")
    end
  | HIPas (knd, d2v, hip) => begin
      fprint (pf | out, "HIPas(");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint (pf | out, d2v);
      fprint (pf | out, "; ");
      fprint (pf | out, hip);
      fprint (pf | out, ")")
    end
  | HIPbool b => begin
      fprint (pf | out, "HIPbool(");
      fprint (pf | out, b);
      fprint (pf | out, ")")
    end
  | HIPchar c => begin
      fprint (pf | out, "HIPchar(");
      fprint (pf | out, c);
      fprint (pf | out, ")")
    end
  | HIPcon (freeknd, d2c, hips_arg, hit_sum) => begin
      fprint (pf | out, "HIPcon(");
      fprint_int (pf | out, freeknd);
      fprint (pf | out, "; ");
      fprint_d2con (pf | out, d2c);
      fprint (pf | out, "; ");
      fprint_hipatlst (pf | out, hips_arg);
      fprint (pf | out, "; ");
      fprint_hityp (pf | out, hit_sum);
      fprint (pf | out, ")")
    end
  | HIPcon_any (freeknd, d2c) => begin
      fprint (pf | out, "HIPcon_any(");
      fprint_int (pf | out, freeknd);
      fprint (pf | out, "; ");
      fprint_d2con (pf | out, d2c);
      fprint (pf | out, ")")
    end
  | HIPempty () => begin
      fprint (pf | out, "HIPempty()");
    end
  | HIPfloat f => begin
      fprintf (pf | out, "HIPfloat(%s)", @(f))
    end
  | HIPint (str, int) => begin
      fprint (pf | out, "HIPint(");
      $IntInf.fprint_intinf (pf | out, int);
      fprint (pf | out, ")")
    end
  | HIPlst (hips_elt, hit_elt) => begin
      fprint (pf | out, "HIPlst(");
      fprint_hipatlst (pf | out, hips_elt);
      fprint (pf | out, "; ");
      fprint_hityp (pf | out, hit_elt);
      fprint (pf | out, ")")
    end
  | HIPrec (knd, lhips, hit_rec) => begin
      fprint (pf | out, "HIPrec(");
      fprint_int (pf | out, knd);
      fprint (pf | out, "; ");
      fprint_labhipatlst (pf | out, lhips);
      fprint (pf | out, "; ");
      fprint_hityp (pf | out, hit_rec);
      fprint (pf | out, ")")
    end
  | HIPstring str => begin
      fprint (pf | out, "HIPstring(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | HIPvar (refknd, d2v) => begin
      fprint (pf | out, "HIPvar(");
      fprint (pf | out, d2v);
      fprint (pf | out, ")")
    end
end // end of [fprint_hipat]

implement fprint_hipatlst {m} (pf | out, hips0) = let
  fun aux (out: &FILE m, i: int, hips: hipatlst): void =
    case+ hips of
    | list_cons (hip, hips) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_hipat (pf | out, hip); aux (out, i+1, hips)
      end
    | list_nil () => ()
in
  aux (out, 0, hips0)
end // end of [fprint_hipatlst]

implement fprint_labhipatlst {m} (pf | out, lhips0) = let
  fun aux (out: &FILE m, i: int, lhips: labhipatlst): void =
    case+ lhips of
    | LABHIPATLSTcons (l, hip, lhips) => begin
        if i > 0 then fprint (pf | out, ", ");
        $Lab.fprint_label (pf | out, l); fprint (pf | out, "= ");
        fprint_hipat (pf | out, hip);
        aux (out, i+1, lhips)
      end
    | LABHIPATLSTdot () => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint (pf | out, "...")
      end
    | LABHIPATLSTnil () => ()
in
  aux (out, 0, lhips0)
end // end of [fprint_labhipatlst]

(* ****** ****** *)

implement print_hipat (hip) = print_mac (fprint_hipat, hip)
implement prerr_hipat (hip) = prerr_mac (fprint_hipat, hip)

implement print_hipatlst (hips) = print_mac (fprint_hipatlst, hips)
implement prerr_hipatlst (hips) = prerr_mac (fprint_hipatlst, hips)

(* ****** ****** *)

implement fprint_hiexp (pf | out, hie0) = begin
  case+ hie0.hiexp_node of
  | HIEapp (hit_fun, hie_fun, hies_arg) => begin
      fprint (pf | out, "HIEapp(");
      fprint (pf | out, hit_fun);
      fprint (pf | out, "; ");
      fprint (pf | out, hie_fun);
      fprint (pf | out, "; ");
      fprint (pf | out, hies_arg);
      fprint (pf | out, ")")
    end
  | HIEarr (hit_elt, hies_elt) => begin
      fprint (pf | out, "HIEarr(");
      fprint (pf | out, hit_elt);
      fprint (pf | out, "; ");
      fprint (pf | out, hies_elt);
      fprint (pf | out, ")")
    end
  | HIEassgn_ptr (hie, hils, hie_val) => begin
      fprint (pf | out, "HIEassgn_ptr(");
      fprint (pf | out, hie);
      fprint (pf | out, "; ");
      fprint (pf | out, hils);
      fprint (pf | out, "; ");
      fprint (pf | out, hie_val);
      fprint (pf | out, ")")
    end
  | HIEassgn_var (d2v, hils, hie_val) => begin
      fprint (pf | out, "HIEassgn_var(");
      fprint (pf | out, d2v);
      fprint (pf | out, "; ");
      fprint (pf | out, hils);
      fprint (pf | out, "; ");
      fprint (pf | out, hie_val);
      fprint (pf | out, ")")
    end
  | HIEbool b => begin
      fprint (pf | out, "HIEbool(");
      fprint (pf | out, b);
      fprint (pf | out, ")")
    end
  | HIEcaseof _ => begin
      fprint (pf | out, "HIEcaseof(");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | HIEchar c => begin
      fprint (pf | out, "HIEchar(");
      fprint (pf | out, c);
      fprint (pf | out, ")")
    end
  | HIEcon (hit_sum, d2c, hies_arg) => begin
      fprint (pf | out, "HIEcon(");
      fprint (pf | out, hit_sum);
      fprint (pf | out, "; ");
      fprint (pf | out, d2c);
      fprint (pf | out, "; ");
      fprint (pf | out, hies_arg);
      fprint (pf | out, ")")
    end
  | HIEcst d2c => begin
      fprint (pf | out, "HIEcst(");
      fprint (pf | out, d2c);
      fprint (pf | out, ")")
    end
  | HIEdelay (lin, hie) => begin
      fprint (pf | out, "HIEdelay(");
      fprint (pf | out, lin);
      fprint (pf | out, "; ");
      fprint (pf | out, hie);
      fprint (pf | out, ")")
    end
  | HIEdynload fil => begin
      fprint (pf | out, "HIEdynload(");
      $Fil.fprint_filename (pf | out, fil);
      fprint (pf | out, ")");
    end
  | HIEempty () => begin
      fprint (pf | out, "HIEempty()")
    end
  | HIEextval code => begin
      fprint (pf | out, "HIEextval(");
      fprint (pf | out, code);
      fprint (pf | out, ")")
    end
  | HIEfix (d2v_fun, hie_body) => begin
      fprint (pf | out, "HIEfix(");
      fprint (pf | out, d2v_fun);
      fprint (pf | out, "; ");
      fprint (pf | out, hie_body);
      fprint (pf | out, ")")
    end
  | HIEfloat str => begin
      fprint (pf | out, "HIEfloat(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | HIEfloatsp str => begin
      fprint (pf | out, "HIEfloatsp(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | HIEfreeat hie => begin
      fprint (pf | out, "HIEfreeat(");
      fprint (pf | out, hie);
      fprint (pf | out, ")")
    end
  | HIEif (hie_cond, hie_then, hie_else) => begin
      fprint (pf | out, "HIEif(");
      fprint (pf | out, hie_cond);
      fprint (pf | out, "; ");
      fprint (pf | out, hie_then);
      fprint (pf | out, "; ");
      fprint (pf | out, hie_else);
      fprint (pf | out, ")")
    end
  | HIEint (str, int) => begin
      fprint (pf | out, "HIEint(");
      $IntInf.fprint_intinf (pf | out, int);
      fprint (pf | out, ")")
    end
  | HIEintsp (str, int) => begin
      fprint (pf | out, "HIEintsp(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | HIElam (hips_arg, hie_body) => begin
      fprint (pf | out, "HIElam(");
      fprint (pf | out, hips_arg);
      fprint (pf | out, "; ");
      fprint (pf | out, hie_body);
      fprint (pf | out, ")")
    end
  | HIElet (hids, hie) => begin
      fprint (pf | out, "HIElet(");
      fprint (pf | out, "...");
      fprint (pf | out, "; ");
      fprint (pf | out, hie);
      fprint (pf | out, ")")
    end
  | HIEloop (ohie_init, hie_test, ohie_post, hie_body) => begin
      fprint (pf | out, "HIEloop(");
      case+ ohie_post of None () => () | Some hie => fprint (pf | out, hie);
      fprint (pf | out, "; ");
      fprint (pf | out, hie_test);
      fprint (pf | out, "; ");
      case+ ohie_post of None () => () | Some hie => fprint (pf | out, hie);
      fprint (pf | out, "; ");
      fprint (pf | out, hie_body);
      fprint (pf | out, ")")
    end
  | HIEloopexn i => begin
      fprint (pf | out, "HIEloopexn(");
      fprint (pf | out, i);
      fprint (pf | out, ")")
    end
  | HIElst (lin, hit, hies) => begin
      fprint (pf | out, "HIElst(");
      fprint (pf | out, lin);
      fprint (pf | out, "; ");
      fprint (pf | out, hit);
      fprint (pf | out, "; ");
      fprint (pf | out, hies);
      fprint (pf | out, ")")
    end
  | HIEptrof_ptr (hie, hils) => begin
      fprint (pf | out, "HIEptrof_ptr(");
      fprint (pf | out,  hie);
      fprint (pf | out, "; ");
      fprint (pf | out, hils);
      fprint (pf | out, ")")
    end
  | HIEptrof_var (d2v, hils) => begin
      fprint (pf | out, "HIEptrof_var(");
      fprint (pf | out,  d2v);
      fprint (pf | out, "; ");
      fprint (pf | out, hils);
      fprint (pf | out, ")")
    end
  | HIEraise (hie) => begin
      fprint (pf | out, "HIEraise(");
      fprint (pf | out, hie);
      fprint (pf | out, ")")
    end
  | HIErec (knd, hit_rec, lhies) => begin
      fprint (pf | out, "HIErec(");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint (pf | out, hit_rec);
      fprint (pf | out, "; ");
      fprint (pf | out, lhies);
      fprint (pf | out, ")")
    end
  | HIErefarg (refval, freeknd, hie_arg) => begin
      fprint (pf | out, "HIErefarg(");
      fprint (pf | out, refval);
      fprint (pf | out, "; ");
      fprint (pf | out, freeknd);
      fprint (pf | out, "; ");
      fprint (pf | out, hie_arg);
      fprint (pf | out, ")")
    end
  | HIEsel (hie, hils) => begin
      fprint (pf | out, "HIEsel(");
      fprint (pf | out,  hie);
      fprint (pf | out, "; ");
      fprint (pf | out, hils);
      fprint (pf | out, ")")
    end
  | HIEsel_ptr (hie, hils) => begin
      fprint (pf | out, "HIEsel_ptr(");
      fprint (pf | out,  hie);
      fprint (pf | out, "; ");
      fprint (pf | out, hils);
      fprint (pf | out, ")")
    end
  | HIEsel_var (d2v, hils) => begin
      fprint (pf | out, "HIEsel_var(");
      fprint (pf | out,  d2v);
      fprint (pf | out, "; ");
      fprint (pf | out, hils);
      fprint (pf | out, ")")
    end
  | HIEseq (hies) => begin
      fprint (pf | out, "HIEseq(");
      fprint (pf | out, hies);
      fprint (pf | out, ")")
    end
  | HIEsizeof (hit) => begin
      fprint (pf | out, "HIEsizeof(");
      fprint (pf | out, hit);
      fprint (pf | out, ")")
    end
  | HIEspawn (hie) => begin
      fprint (pf | out, "HIEspawn(");
      fprint (pf | out,  hie);
      fprint (pf | out, ")")
    end
  | HIEstring (str, len) => begin
      fprintf (pf | out, "HIEstring(\"%s\", %i)", @(str, len))
    end
  | HIEtmpcst (d2c, hitss) => begin
      fprint (pf | out, "HIEtmpcst(");
      fprint (pf | out, d2c);
      fprint (pf | out, "; ");
      fprint (pf | out, hitss);
      fprint (pf | out, ")")
    end
  | HIEtmpvar (d2v, hitss) => begin
      fprint (pf | out, "HIEtmpvar(");
      fprint (pf | out, d2v);
      fprint (pf | out, "; ");
      fprint (pf | out, hitss);
      fprint (pf | out, ")")
    end
  | HIEtop () => begin
      fprint (pf | out, "HIEtop()")
    end
  | HIEtrywith _ => begin
      fprint (pf | out, "HIEtrywith(...)")
    end
  | HIEvar d2v => begin
      fprint (pf | out, "HIEvar(");
      fprint (pf | out, d2v);
      fprint (pf | out, ")")
    end
end // end of [fprint_hiexp]

implement fprint_hiexplst {m} (pf | out, hies0) = let
  fun aux (out: &FILE m, i: int, hies: hiexplst): void =
    case+ hies of
    | list_cons (hie, hies) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_hiexp (pf | out, hie); aux (out, i+1, hies)
      end
    | list_nil () => ()
in
  aux (out, 0, hies0)
end // end of [fprint_hiexplst]

implement fprint_hiexplstlst {m} (pf | out, hiess0) = let
  fun aux (out: &FILE m, i: int, hiess: hiexplstlst): void =
    case+ hiess of
    | list_cons (hies, hiess) => begin
        if i > 0 then fprint (pf | out, "; ");
        fprint_hiexplst (pf | out, hies); aux (out, i+1, hiess)
      end
    | list_nil () => ()
in
  aux (out, 0, hiess0)
end // end of [fprint_hiexplstlst]

implement fprint_labhiexplst {m} (pf | out, lhies0) = let
  fun aux (out: &FILE m, i: int, lhies: labhiexplst): void =
    case+ lhies of
    | LABHIEXPLSTcons (l, hie, lhies) => begin
        if i > 0 then fprint (pf | out, ", ");
        $Lab.fprint_label (pf | out, l); fprint (pf | out, "= ");
        fprint_hiexp (pf | out, hie);
        aux (out, i+1, lhies)
      end
    | LABHIEXPLSTnil () => ()
in
  aux (out, 0, lhies0)
end // end of [fprint_labhiexplst]

implement fprint_hilab (pf | out, hil) = begin
  case+ hil.hilab_node of
  | HILlab (l, s2e_rec) => begin
      fprint (pf | out, "HILlab(");
      $Lab.fprint_label (pf | out, l);
      fprint (pf | out, ")")
    end
  | HILind (hiess, s2e_elt) => begin
      fprint (pf | out, "HILind(");
      fprint (pf | out, hiess);
      fprint (pf | out, ")")
    end
end // end of [fprint_hilab]

implement fprint_hilablst {m} (pf | out, hils0) = let
  fun aux (out: &FILE m, i: int, hils: hilablst): void =
    case+ hils of
    | list_cons (hil, hils) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint_hilab (pf | out, hil); aux (out, i+1, hils)
      end
    | list_nil () => ()
in
  aux (out, 0, hils0)
end // end of [fprint_hilablst]

(* ****** ****** *)

implement print_hiexp (hie) = print_mac (fprint_hiexp, hie)
implement prerr_hiexp (hie) = prerr_mac (fprint_hiexp, hie)

implement print_hiexplst (hies) = print_mac (fprint_hiexplst, hies)
implement prerr_hiexplst (hies) = prerr_mac (fprint_hiexplst, hies)

(* ****** ****** *)

implement fprint_vartyp (pf | out, vtp) = begin
  fprint_d2var (pf | out, vartyp_var_get vtp);
  fprint (pf | out, "(");
  fprint_hityp (pf | out, hityp_decode (vartyp_typ_get vtp));
  fprint (pf | out, ")")
end // end of [fprint_vartyp]

implement print_vartyp (vtp) = print_mac (fprint_vartyp, vtp)
implement prerr_vartyp (vtp) = prerr_mac (fprint_vartyp, vtp)

(* ****** ****** *)

(* end of [ats_hiexp_print.dats] *)
