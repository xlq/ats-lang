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

macdef fprint_label = $Lab.fprint_label

(* ****** ****** *)

implement fprint_hityp (pf | out, hit) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ hit.hityp_node of
  | HITextype name => begin
      strpr "HITextype(";
      fprint_string (pf | out, name);
      strpr ")"
    end // end of [HITextype]
  | HITfun (fc, hits_arg, hit_res) => begin
      strpr "HITfun(";
      $Syn.fprint_funclo (pf | out, fc);
      strpr "; ";
      fprint_hityplst (pf | out, hits_arg);
      strpr "; ";
      fprint_hityp (pf | out, hit_res);
      strpr ")"
    end // end of [HITfun]
  | HITrefarg (refval, hit) => begin
      strpr "HITrefarg(";
      fprint1_int (pf | out, refval);
      strpr "; ";
      fprint_hityp (pf | out, hit);
      strpr ")"
    end // end of [HITrefarg]
  | HITtyrecsin hit => begin
      strpr "HITtyrecsin(";
      fprint_hityp (pf | out, hit);
      strpr ")"
    end // end of [HITtyrecsin]
  | HITtyrectemp (knd, lhits) => begin
      fprint1_string (pf | out, "HITtyrectemp(...)")
    end
  | HITtysumtemp (d2c, hits) => begin
      strpr "HITsumtemp(";
      fprint_d2con (pf | out, d2c);
      strpr "; ";
      fprint_hityplst (pf | out, hits);
      strpr ")"
    end // end of [HITtysumtemp]
  | HITs2var s2v => begin
      strpr "HITs2var("; fprint_s2var (pf | out, s2v); strpr ")"
    end
  | _ => let
      val HITNAM (knd, name) = hit.hityp_name
    in
      if knd > 0 then fprint1_string (pf | out, "*");
      fprint1_string (pf | out, name)
    end // end of [_]
end // end of [fprint_hityp]

implement fprint_hityplst {m} (pf | out, hits0) = let
  fun aux (out: &FILE m, i: int, hits: hityplst): void =
    case+ hits of
    | list_cons (hit, hits) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
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
        if i > 0 then fprint1_string (pf | out, ", ");
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

implement fprint_hipat (pf | out, hip0) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ hip0.hipat_node of
  | HIPann (hip, hit_ann) => begin
      strpr "HIPann(";
      fprint_hipat (pf | out, hip);
      strpr "; ";
      fprint_hityp (pf | out, hit_ann);
      strpr ")"
    end // end of [HIPann]
  | HIPany () => begin
      fprint1_string (pf | out, "HIPany()")
    end
  | HIPas (knd, d2v, hip) => begin
      strpr "HIPas(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_d2var (pf | out, d2v);
      strpr "; ";
      fprint_hipat (pf | out, hip);
      strpr ")"
    end // end of [HIPas]
  | HIPbool b => begin
      strpr "HIPbool("; fprint1_bool (pf | out, b); strpr ")"
    end // end of [HIPbool]
  | HIPchar c => begin
      strpr "HIPchar("; fprint1_char (pf | out, c); strpr ")"
    end // end of [HIPchar]
  | HIPcon (freeknd, d2c, hips_arg, hit_sum) => begin
      strpr "HIPcon(";
      fprint1_int (pf | out, freeknd);
      strpr "; ";
      fprint_d2con (pf | out, d2c);
      strpr "; ";
      fprint_hipatlst (pf | out, hips_arg);
      strpr "; ";
      fprint_hityp (pf | out, hit_sum);
      strpr ")"
    end // end of [HIPcon]
  | HIPcon_any (freeknd, d2c) => begin
      strpr "HIPcon_any(";
      fprint1_int (pf | out, freeknd);
      strpr "; ";
      fprint_d2con (pf | out, d2c);
      strpr ")"
    end // end of [HIPcon_any]
  | HIPempty () => begin
      fprint1_string (pf | out, "HIPempty()");
    end
  | HIPfloat f(*string*) => begin
      fprintf1_exn (pf | out, "HIPfloat(%s)", @(f))
    end
  | HIPint (str, int) => begin
      strpr "HIPint(";
      $IntInf.fprint_intinf (pf | out, int);
      strpr ")"
    end // end of [HIPint]
  | HIPlst (hips_elt, hit_elt) => begin
      strpr "HIPlst(";
      fprint_hipatlst (pf | out, hips_elt);
      strpr "; ";
      fprint_hityp (pf | out, hit_elt);
      strpr ")"
    end // end of [HIPlst]
  | HIPrec (knd, lhips, hit_rec) => begin
      strpr "HIPrec(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_labhipatlst (pf | out, lhips);
      strpr "; ";
      fprint_hityp (pf | out, hit_rec);
      strpr ")"
    end // end of [HIPrec]
  | HIPstring s => begin
      strpr "HIPstring("; fprint1_string (pf | out, s); strpr ")"
    end // end of [HIPstring]
  | HIPvar (refknd, d2v) => begin
      strpr "HIPvar("; fprint_d2var (pf | out, d2v); strpr ")"
    end // end of [HIPvar]
end // end of [fprint_hipat]

implement fprint_hipatlst {m} (pf | out, hips0) = let
  fun aux (out: &FILE m, i: int, hips: hipatlst): void =
    case+ hips of
    | list_cons (hip, hips) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
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
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_label (pf | out, l);
        fprint1_string (pf | out, "= ");
        fprint_hipat (pf | out, hip);
        aux (out, i+1, lhips)
      end
    | LABHIPATLSTdot () => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint1_string (pf | out, "...")
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

implement fprint_hiexp (pf | out, hie0) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ hie0.hiexp_node of
  | HIEapp (hit_fun, hie_fun, hies_arg) => begin
      strpr "HIEapp(";
      fprint_hityp (pf | out, hit_fun);
      strpr "; ";
      fprint_hiexp (pf | out, hie_fun);
      strpr "; ";
      fprint_hiexplst (pf | out, hies_arg);
      strpr ")"
    end // end of [HIEapp]
  | HIEarrinit (hit_elt, ohie_asz, hies_elt) => begin
      strpr "HIEarrinit(";
      fprint_hityp (pf | out, hit_elt);
      strpr "; ";
      begin case+ ohie_asz of
      | Some hie => fprint_hiexp (pf | out, hie) | None () => ()
      end;
      strpr "; ";
      fprint_hiexplst (pf | out, hies_elt);
      strpr ")"
    end // end of [HIEarrinit]
  | HIEarrsize (hit_elt, hies_elt) => begin
      strpr "HIEarrsize(";
      fprint_hityp (pf | out, hit_elt);
      strpr "; ";
      fprint_hiexplst (pf | out, hies_elt);
      strpr ")"
    end // end of [HIEarrsize]
  | HIEassgn_ptr (hie, hils, hie_val) => begin
      strpr "HIEassgn_ptr(";
      fprint_hiexp (pf | out, hie);
      strpr "; ";
      fprint_hilablst (pf | out, hils);
      strpr "; ";
      fprint_hiexp (pf | out, hie_val);
      strpr ")"
    end // end of [HIEassgn_ptr]
  | HIEassgn_var (d2v, hils, hie_val) => begin
      strpr "HIEassgn_var(";
      fprint_d2var (pf | out, d2v);
      strpr "; ";
      fprint_hilablst (pf | out, hils);
      strpr "; ";
      fprint_hiexp (pf | out, hie_val);
      strpr ")"
    end // end of [HIEassgn_var]
  | HIEbool b => begin
      strpr "HIEbool("; fprint1_bool (pf | out, b); strpr ")"
    end
  | HIEcaseof _ => begin
      strpr "HIEcaseof("; fprint1_string (pf | out, "..."); strpr ")"
    end
  | HIEchar c => begin
      strpr "HIEchar("; fprint1_char (pf | out, c); strpr ")"
    end
  | HIEcon (hit_sum, d2c, hies_arg) => begin
      strpr "HIEcon(";
      fprint_hityp (pf | out, hit_sum);
      strpr "; ";
      fprint_d2con (pf | out, d2c);
      strpr "; ";
      fprint_hiexplst (pf | out, hies_arg);
      strpr ")"
    end // end of [HIEcon]
  | HIEcst d2c => begin
      strpr "HIEcst("; fprint_d2cst (pf | out, d2c); strpr ")"
    end
  | HIEdynload fil => begin
      strpr "HIEdynload(";
      $Fil.fprint_filename (pf | out, fil);
      strpr ")";
    end
  | HIEempty () => begin
      fprint1_string (pf | out, "HIEempty()")
    end
  | HIEextval code => begin
      strpr "HIEextval("; fprint1_string (pf | out, code); strpr ")"
    end
  | HIEfix (d2v_fun, hie_body) => begin
      strpr "HIEfix(";
      fprint_d2var (pf | out, d2v_fun);
      strpr "; ";
      fprint_hiexp (pf | out, hie_body);
      strpr ")"
    end // end of [HIEfix]
  | HIEfloat f(*string*) => begin
      strpr "HIEfloat("; fprint1_string (pf | out, f); strpr ")"
    end
  | HIEfloatsp f(*string*) => begin
      strpr "HIEfloatsp("; fprint1_string (pf | out, f); strpr ")"
    end
  | HIEfreeat hie => begin
      strpr "HIEfreeat("; fprint_hiexp (pf | out, hie); strpr ")"
    end
  | HIEif (hie_cond, hie_then, hie_else) => begin
      strpr "HIEif(";
      fprint_hiexp (pf | out, hie_cond);
      strpr "; ";
      fprint_hiexp (pf | out, hie_then);
      strpr "; ";
      fprint_hiexp (pf | out, hie_else);
      strpr ")"
    end // end of [HIEif]
  | HIEint (str, int) => begin
      strpr "HIEint(";
      $IntInf.fprint_intinf (pf | out, int);
      strpr ")"
    end // end of [HIEint]
  | HIEintsp (str, int) => begin
      strpr "HIEintsp("; fprint1_string (pf | out, str); strpr ")"
    end
  | HIElam (hips_arg, hie_body) => begin
      strpr "HIElam(";
      fprint_hipatlst (pf | out, hips_arg);
      strpr "; ";
      fprint_hiexp (pf | out, hie_body);
      strpr ")"
    end // end of [HIElam]
  | HIElazy_delay (lin, hie_body) => begin
      strpr "HIElazy_delay(";
      fprint1_int (pf | out, lin);
      strpr "; ";
      fprint_hiexp (pf | out, hie_body);
      strpr ")"
    end // end of [HIElazy_delay]
  | HIElazy_force (lin, hie_lazy) => begin
      strpr "HIElazy_force(";
      fprint_int (pf | out, lin);
      strpr "; ";
      fprint_hiexp (pf | out, hie_lazy);
      strpr ")"
    end // end of [HIElazy_force]
  | HIElet (hids, hie) => begin
      strpr "HIElet(";
      fprint1_string (pf | out, "...");
      strpr "; ";
      fprint_hiexp (pf | out, hie);
      strpr ")"
    end // end of [HIElet]
  | HIEloop (ohie_init, hie_test, ohie_post, hie_body) => begin
      strpr "HIEloop(";
      begin case+ ohie_post of
        | None () => () | Some hie => fprint_hiexp (pf | out, hie)
      end;
      strpr "; ";
      fprint_hiexp (pf | out, hie_test);
      strpr "; ";
      begin case+ ohie_post of
        | None () => () | Some hie => fprint_hiexp (pf | out, hie)
      end;
      strpr "; ";
      fprint_hiexp (pf | out, hie_body);
      strpr ")"
    end // end of [HIEloop]
  | HIEloopexn i => begin
      strpr "HIEloopexn("; fprint1_int (pf | out, i); strpr ")"
    end // end of [HIEloopexn]
  | HIElst (lin, hit, hies) => begin
      strpr "HIElst(";
      fprint1_int (pf | out, lin);
      strpr "; ";
      fprint_hityp (pf | out, hit);
      strpr "; ";
      fprint_hiexplst (pf | out, hies);
      strpr ")"
    end // end of [HIElst]
  | HIEptrof_ptr (hie, hils) => begin
      strpr "HIEptrof_ptr(";
      fprint_hiexp (pf | out,  hie);
      strpr "; ";
      fprint_hilablst (pf | out, hils);
      strpr ")"
    end // end of [HIEptrof_ptr]
  | HIEptrof_var (d2v, hils) => begin
      strpr "HIEptrof_var(";
      fprint_d2var (pf | out,  d2v);
      strpr "; ";
      fprint_hilablst (pf | out, hils);
      strpr ")"
    end // end of [HIEptrof_var]
  | HIEraise (hie) => begin
      strpr "HIEraise("; fprint_hiexp (pf | out, hie); strpr ")"
    end // end of [HIEraise]
  | HIErec (knd, hit_rec, lhies) => begin
      strpr "HIErec(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_hityp (pf | out, hit_rec);
      strpr "; ";
      fprint_labhiexplst (pf | out, lhies);
      strpr ")"
    end // end of [HIErec]
  | HIErefarg (refval, freeknd, hie_arg) => begin
      strpr "HIErefarg(";
      fprint1_int (pf | out, refval);
      strpr "; ";
      fprint1_int (pf | out, freeknd);
      strpr "; ";
      fprint_hiexp (pf | out, hie_arg);
      strpr ")"
    end // end of [HIErefarg]
  | HIEsel (hie, hils) => begin
      strpr "HIEsel(";
      fprint_hiexp (pf | out,  hie);
      strpr "; ";
      fprint_hilablst (pf | out, hils);
      strpr ")"
    end // end of [HIEsel]
  | HIEsel_ptr (hie, hils) => begin
      strpr "HIEsel_ptr(";
      fprint_hiexp (pf | out,  hie);
      strpr "; ";
      fprint_hilablst (pf | out, hils);
      strpr ")"
    end // end of [HIEsel_ptr]
  | HIEsel_var (d2v, hils) => begin
      strpr "HIEsel_var(";
      fprint_d2var (pf | out,  d2v);
      strpr "; ";
      fprint_hilablst (pf | out, hils);
      strpr ")"
    end // end of [HIEsel_var]
  | HIEseq (hies) => begin
      strpr "HIEseq("; fprint_hiexplst (pf | out, hies); strpr ")"
    end // end of [HIEseq]
  | HIEsizeof (hit) => begin
      strpr "HIEsizeof("; fprint_hityp (pf | out, hit); strpr ")"
    end // end of [HIEsizeof]
  | HIEspawn (hie) => begin
      strpr "HIEspawn("; fprint_hiexp (pf | out,  hie); strpr ")"
    end // end of [HIEspawn]
  | HIEstring (str, len) => begin
      fprintf1_exn (pf | out, "HIEstring(\"%s\", %i)", @(str, len))
    end // end of [HIEstring]
  | HIEtmpcst (d2c, hitss) => begin
      strpr "HIEtmpcst(";
      fprint_d2cst (pf | out, d2c);
      strpr "; ";
      fprint_hityplstlst (pf | out, hitss);
      strpr ")"
    end // end of [HIEtmpcst]
  | HIEtmpvar (d2v, hitss) => begin
      strpr "HIEtmpvar(";
      fprint_d2var (pf | out, d2v);
      strpr "; ";
      fprint_hityplstlst (pf | out, hitss);
      strpr ")"
    end // end of [HIEtmpvar]
  | HIEtop () => begin
      fprint1_string (pf | out, "HIEtop()")
    end // end of [HIEtop]
  | HIEtrywith _ => begin
      fprint1_string (pf | out, "HIEtrywith(...)")
    end // end of [HIEtrywith]
  | HIEvar d2v => begin
      strpr "HIEvar("; fprint_d2var (pf | out, d2v); strpr ")"
    end // end of [HIEvar]
end // end of [fprint_hiexp]

implement fprint_hiexplst {m} (pf | out, hies0) = let
  fun aux (out: &FILE m, i: int, hies: hiexplst): void =
    case+ hies of
    | list_cons (hie, hies) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
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
        if i > 0 then fprint1_string (pf | out, "; ");
        fprint_hiexplst (pf | out, hies); aux (out, i+1, hiess)
      end
    | list_nil () => ()
  // end of [aux]
in
  aux (out, 0, hiess0)
end // end of [fprint_hiexplstlst]

implement fprint_labhiexplst {m} (pf | out, lhies0) = let
  fun aux (out: &FILE m, i: int, lhies: labhiexplst): void =
    case+ lhies of
    | LABHIEXPLSTcons (l, hie, lhies) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_label (pf | out, l);
        fprint1_string (pf | out, "= ");
        fprint_hiexp (pf | out, hie);
        aux (out, i+1, lhies)
      end
    | LABHIEXPLSTnil () => ()
  // end of [aux]
in
  aux (out, 0, lhies0)
end // end of [fprint_labhiexplst]

implement fprint_hilab (pf | out, hil) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ hil.hilab_node of
  | HILlab (l, s2e_rec) => begin
      strpr "HILlab("; fprint_label (pf | out, l); strpr ")"
    end // end of [HILlab]
  | HILind (hiess, s2e_elt) => begin
      strpr "HILind("; fprint_hiexplstlst (pf | out, hiess); strpr ")"
    end // end of [HILind]
end // end of [fprint_hilab]

implement fprint_hilablst {m} (pf | out, hils0) = let
  fun aux (out: &FILE m, i: int, hils: hilablst): void =
    case+ hils of
    | list_cons (hil, hils) => begin
        if i > 0 then fprint1_string (pf | out, ", ");
        fprint_hilab (pf | out, hil); aux (out, i+1, hils)
      end // end of [list_cons]
    | list_nil () => ()
  // end of [aux]
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
  fprint1_string (pf | out, "(");
  fprint_hityp (pf | out, hityp_decode (vartyp_typ_get vtp));
  fprint1_string (pf | out, ")")
end // end of [fprint_vartyp]

implement print_vartyp (vtp) = print_mac (fprint_vartyp, vtp)
implement prerr_vartyp (vtp) = prerr_mac (fprint_vartyp, vtp)

(* ****** ****** *)

(* end of [ats_hiexp_print.dats] *)
