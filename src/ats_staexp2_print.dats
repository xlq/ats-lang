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

%{^

#include "ats_counter.cats" /* only needed for [ATS/Geizella] */

%}

(* ****** ****** *)

staload "ats_stamp.sats"
staload "ats_staexp2.sats"

(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)

overload fprint with $Lab.fprint_label
overload fprint with $Sym.fprint_symbol

(* ****** ****** *)

fun fprint_tyreckind {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, k: tyreckind): void =
  case+ k of
  | TYRECKINDbox _ => fprint (pf | out, "box")
  | TYRECKINDflt0 _ => fprint (pf | out, "flt")
  | TYRECKINDflt1 s => begin
      fprint (pf | out, "flt(");
      $Stamp.fprint_stamp (pf | out, s);
      fprint (pf | out, ")")
    end

(* ****** ****** *)

fn fprint_s2rtdat {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2td: s2rtdat_t): void =
  fprint (pf | out, s2rtdat_sym_get s2td)

fn fprint_s2rtbas {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2tb: s2rtbas): void =
  case+ s2tb of
  | S2RTBASpre x => fprint (pf | out, x)
  | S2RTBASimp (x, _, _) => fprint (pf | out, x)
  | S2RTBASdef x => fprint_s2rtdat (pf | out, x)

(* ****** ****** *)

implement fprint_s2item (pf | out, s2i) = begin
  case+ s2i of
  | S2ITEMcst _ => begin
      fprint (pf | out, "S2ITEMcst(...)")
    end
  | S2ITEMdatconptr d2c => begin
      fprint (pf | out, "S2ITEMdatconptr(");
      fprint (pf | out, d2c);
      fprint (pf | out, ")")
    end
  | S2ITEMdatcontyp d2c => begin
      fprint (pf | out, "S2ITEMdatcontyp(");
      fprint (pf | out, d2c);
      fprint (pf | out, ")")
    end
  | S2ITEMe1xp e1xp => begin
      fprint (pf | out, "S2ITEMe1xp(");
      fprint (pf | out, e1xp);
      fprint (pf | out, ")")
    end
  | S2ITEMfil fil => begin
      fprint (pf | out, "S2ITEMfil(");
      $Fil.fprint_filename (pf | out, fil);
      fprint (pf | out, ")")
    end
  | S2ITEMvar s2v => begin
      fprint (pf | out, "S2ITEMvar(");
      fprint (pf | out, s2v);
      fprint (pf | out, ")")
    end
end // end of [fprint_s2item]

implement print_s2item (s2i) = print_mac (fprint_s2item, s2i)
implement prerr_s2item (s2i) = prerr_mac (fprint_s2item, s2i)

(* ****** ****** *)

implement fprint_s2rt (pf | out, s2t) = case+ s2t of
  | S2RTbas s2tb => fprint_s2rtbas (pf | out, s2tb)
  | S2RTfun (s2ts, s2t) => begin
      fprint (pf | out, "S2RTfun(");
      fprint_s2rtlst (pf | out, s2ts);
      fprint (pf | out, "; ");
      fprint_s2rt (pf | out, s2t);
      fprint (pf | out, ")")
    end
  | S2RTtup s2ts => begin
      fprint (pf | out, "S2RTtup(");
      fprint_s2rtlst (pf | out, s2ts);
      fprint (pf | out, ")")
    end

(* ****** ****** *)

implement fprint_s2rtlst {m} (pf | out, s2ts0) = let
fun aux (out: &FILE m, s2t0: s2rt, s2ts: s2rtlst): void =
  case+ s2ts of
  | cons (s2t, s2ts) => begin
      fprint (pf | out, s2t0); fprint (pf | out, ", "); aux (out, s2t, s2ts)
    end
  | nil () => fprint (pf | out, s2t0)
in
  case+ s2ts0 of cons (s2t, s2ts) => aux (out, s2t, s2ts) | nil () => ()
end // end of [fprint_s2rtlst]

implement fprint_s2rtlstlst {m} (pf | out, s2tss0) = let
fun aux (out: &FILE m, s2ts0: s2rtlst, s2tss: s2rtlstlst): void =
  case+ s2tss of
  | cons (s2ts, s2tss) => begin
      fprint (pf | out, s2ts0); fprint (pf | out, ", "); aux (out, s2ts, s2tss)
    end
  | nil () => fprint (pf | out, s2ts0)
in
  case+ s2tss0 of
    | cons (s2ts, s2tss) => aux (out, s2ts, s2tss) | nil () => ()
end // end of [fprint_s2rtlstlst]

(* ****** ****** *)

implement print_s2rt (s2t) = print_mac (fprint_s2rt, s2t)
implement prerr_s2rt (s2t) = prerr_mac (fprint_s2rt, s2t)

(* ****** ****** *)

implement fprint_s2rtext (pf | out, s2te) = case+ s2te of
  | S2TEsrt s2t => fprint_s2rt (pf | out, s2t)
  | S2TEsub (s2v, s2t, s2es) => begin
      fprint (pf  | out, "{");
      fprint_s2var (pf | out, s2v);
      fprint (pf  | out, ": ");
      fprint_s2rt (pf | out, s2t);
      fprint (pf  | out, " | ");
      fprint_s2explst (pf | out, s2es);
      fprint (pf | out, "}")
    end

(* ****** ****** *)

implement fprint_s2eff (pf | out, s2fe) = case+ s2fe of
  | S2EFFall () => begin
      fprint (pf | out, "<all>")
    end
  | S2EFFnil () => begin
      fprint (pf | out, "<nil>")
    end
  | S2EFFset (effs, s2es) => begin
      fprint (pf | out, "<");
      $Eff.fprint_effset (pf | out, effs);
      fprint (pf | out, ";");
      fprint (pf | out, s2es);
      fprint (pf | out, ">")
    end

implement print_s2eff (s2fe) = print_mac (fprint_s2eff, s2fe)
implement prerr_s2eff (s2fe) = prerr_mac (fprint_s2eff, s2fe)

(* ****** ****** *)

implement fprint_s2exp (pf | out, s2e0) = case+ s2e0.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) => begin
      fprint (pf | out, "S2Eapp(");
      fprint (pf | out, s2e_fun);
      fprint (pf | out, "; ");
      fprint (pf | out, s2es_arg);
      fprint (pf | out, ")")
    end      
  | S2Echar c => begin
      fprint (pf | out, "S2Echar(");
      fprint (pf | out, c);
      fprint (pf | out, ")")
    end
  | S2Eclo (knd, s2e) => begin
      fprint (pf | out, "S2Eclo(");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint_s2exp (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S2Ecrypt (s2e) => begin
      fprint (pf | out, "S2Ecrypt(");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S2Ecst s2c => begin
      fprint (pf | out, "S2Ecst(");
      fprint_s2cst (pf | out, s2c);
      fprint (pf | out, ")")
    end
  | S2Edatconptr (d2c, s2es) => begin
      fprint (pf | out, "S2Edatconptr(");
      fprint_d2con (pf | out, d2c);
      fprint (pf | out, "; ");
      fprint (pf | out, s2es);
      fprint (pf | out, ")")
    end
  | S2Edatcontyp (d2c, s2es) => begin
      fprint (pf | out, "S2Edatcontyp(");
      fprint_d2con (pf | out, d2c);
      fprint (pf | out, "; ");
      fprint (pf | out, s2es);
      fprint (pf | out, ")")
    end
  | S2Eeff s2fe => begin
      fprint (pf | out, "S2Eeff(");
      fprint_s2eff (pf | out, s2fe);
      fprint (pf | out, ")")
    end
  | S2Eeqeq (s2e1, s2e2) => begin
      fprint (pf | out, "S2Eeqeq(");
      fprint (pf | out, s2e1);
      fprint (pf | out, ", ");
      fprint (pf | out, s2e2);
      fprint (pf | out, ")")
    end
  | S2Eexi (s2vs, s2ps, s2e) => begin
      fprint (pf | out, "S2Eexi(");
      fprint_s2varlst (pf | out, s2vs);
      fprint (pf | out, "; ");
      fprint (pf | out, s2ps);
      fprint (pf | out, "; ");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S2Eextype name => begin
      fprint (pf | out, "S2Eextype(");
      fprint (pf | out, name);
      fprint (pf | out, ")")
    end
  | S2Efun (fc, lin, s2fe, npf, s2es, s2e) => begin
      fprint (pf | out, "S2Efun(");
      $Syn.fprint_funclo (pf | out, fc);
      fprint (pf | out, "; ");
      fprint (pf | out, lin);
      fprint (pf | out, "; ");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, s2es);
      fprint (pf | out, "; ");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S2Eint i(*int*) => begin
      fprint (pf | out, "S2Eint(");
      fprint (pf | out, i);
      fprint (pf | out, ")")
    end
  | S2Eintinf i(*intinf*) => begin
      fprint (pf | out, "S2Eint(");
      $IntInf.fprint_intinf (pf | out, i);
      fprint (pf | out, ")")
    end
  | S2Elam (s2vs, s2e) => begin
      fprint (pf | out, "S2Elam(");
      fprint_s2varlst (pf | out, s2vs);
      fprint (pf | out, "; ");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S2Emetfn (_(*stamp*), s2es, s2e) => begin
      fprint (pf | out, "S2Emetfn(");
      fprint (pf | out, s2es);
      fprint (pf | out, "; ");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S2Emetlt (s2es1, s2es2) => begin
      fprint (pf | out, "S2Emetlt(");
      fprint (pf | out, s2es1);
      fprint (pf | out, ", ");
      fprint (pf | out, s2es2);
      fprint (pf | out, ")")
    end
  | S2Eout s2e => begin
      fprint (pf | out, "S2Eout(");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S2Eproj (s2e, s2l) => begin
      fprint (pf | out, "S2Eproj(");
      fprint (pf | out, s2e);
      fprint (pf | out, "; ");
      fprint (pf | out, s2l);
      fprint (pf | out, ")")
    end
  | S2Eread (s2e_v, s2e_vt) => begin
      fprint (pf | out, "S2Eread(");
      fprint (pf | out, s2e_v);
      fprint (pf | out, ", ");
      fprint (pf | out, s2e_vt);
      fprint (pf | out, ")")
    end
  | S2Erefarg (refval, s2e) => begin
      fprint (pf | out, "S2Erefarg(");
      fprint (pf | out, refval);
      fprint (pf | out, ", ");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S2Esel (s2e, i) => begin
      fprint (pf | out, "S2Esel(");
      fprint (pf | out, s2e);
      fprint (pf | out, "; ");
      fprint (pf | out, i);
      fprint (pf | out, ")")
    end
  | S2Esize (s2ze) => begin
      fprint (pf | out, "S2Esize(");
      fprint (pf | out, s2ze);
      fprint (pf | out, ")")
    end
  | S2Esizeof (s2e) => begin
      fprint (pf | out, "S2Esizeof(");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S2Etop (knd, s2e) => begin
      fprint (pf | out, "S2Etop(");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S2Etup s2es => begin
      fprint (pf | out, "S2Etup(");
      fprint (pf | out, s2es);
      fprint (pf | out, ")")
    end
  | S2Etyarr (s2e_elt, s2ess_dim) => begin
      fprint (pf | out, "S2Etyarr(");
      fprint (pf | out, s2e_elt);
      fprint (pf | out, "; ");
      fprint (pf | out, s2ess_dim);
      fprint (pf | out, ")")
    end
  | S2Etyleq (knd, s2e1, s2e2) => begin
      fprint (pf | out, "S2Etyleq(");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint (pf | out, s2e1);
      fprint (pf | out, ", ");
      fprint (pf | out, s2e2);
      fprint (pf | out, ")")
    end
  | S2Etylst s2es => begin
      fprint (pf | out, "S2Etylst(");
      fprint (pf | out, s2es);
      fprint (pf | out, ")")
    end
  | S2Etyrec (k, npf, ls2es) => begin
      fprint (pf | out, "S2Etyrec(");
      fprint_tyreckind (pf | out, k);
      fprint (pf | out, "; ");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, ls2es);
      fprint (pf | out, ")")
    end
  | S2Euni (s2vs, s2ps, s2e) => begin
      fprint (pf | out, "S2Euni(");
      fprint_s2varlst (pf | out, s2vs);
      fprint (pf | out, "; ");
      fprint (pf | out, s2ps);
      fprint (pf | out, "; ");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S2Eunion (stamp, s2e_ind, ls2es) => begin
      fprint (pf | out, "S2Eunion(");
      $Stamp.fprint_stamp (pf | out, stamp);
      fprint (pf | out, "; ");
      fprint (pf | out, s2e_ind);
      fprint (pf | out, "; ");
      fprint (pf | out, ls2es);
      fprint (pf | out, ")")
    end
  | S2Evar s2v => begin
      fprint (pf | out, "S2Evar(");
      fprint_s2var (pf | out, s2v);
      fprint (pf | out, ")")
    end
  | S2EVar s2V => let
      val () = fprint (pf | out, "S2EVar(")
      val () = fprint (pf | out, s2V)
      val () = fprint (pf | out, ")")
(*
      val () = let
        val os2e = s2Var_link_get s2V in case+ os2e of
        | Some s2e => begin
            fprint (pf | out, "["); fprint (pf | out, s2e); fprint (pf | out, "]")
          end
        | None () => ()
      end
*)
    in
      // empty
    end // end of [S2EVar]
  | S2Evararg s2e => begin
      fprint (pf | out, "S2Evararg(");
      fprint (pf | out, s2e);
      fprint (pf | out, ")")
    end
  | S2Ewth (s2e_res, wths2es) => begin
      fprint (pf | out, "S2Ewth(");
      fprint (pf | out, s2e_res);
      fprint (pf | out, "; ");
      fprint (pf | out, wths2es);
      fprint (pf | out, ")")
    end
(*
  | _ => begin
      prerr "Internal Error: ";
      prerr "[fprint_s2exp]: unsupported static expression";
      prerr_newline ();
      exit (1)      
    end
*)

(* ****** ****** *)

implement print_s2exp (s2e) = print_mac (fprint_s2exp, s2e)
implement prerr_s2exp (s2e) = prerr_mac (fprint_s2exp, s2e)

(* ****** ****** *)

implement fprint_s2explst {m} (pf | out, s2es) = let
fun aux (out: &FILE m, i: int, s2es: s2explst): void =
  case+ s2es of
  | cons (s2e, s2es) => begin
      if i > 0 then fprint (pf | out, ", ");
      fprint_s2exp (pf | out, s2e); aux (out, i+1, s2es)
    end
  | nil () => ()
in
  aux (out, 0, s2es)
end // end of [fprint_s2explst]

implement fprint_s2explstlst {m} (pf | out, s2ess) = let
fun aux (out: &FILE m, i: int, s2ess: s2explstlst): void =
  case+ s2ess of
  | cons (s2es, s2ess) => begin
      if i > 0 then fprint (pf | out, "; ");
      fprint_s2explst (pf | out, s2es); aux (out, i + 1, s2ess)
    end
  | nil () => ()
in
  aux (out, 0, s2ess)
end // end of [fprint_s2explstlst]

(* ****** ****** *)

implement fprint_s2expopt {m} (pf | out, os2e) =
  case+ os2e of
  | Some s2e => begin
      fprint (pf | out, "Some("); fprint (pf | out, s2e); fprint (pf | out, ")")
    end
  | None () => begin
      fprint (pf | out, "None()")
    end

(* ****** ****** *)

implement fprint_labs2explst {m} (pf | out, ls2es) = let
fun aux (out: &FILE m, l0: lab_t, s2e0: s2exp, ls2es: labs2explst): void =
  case+ ls2es of
  | LABS2EXPLSTcons (l, s2e, ls2es) => begin
      fprint (pf | out, l0); fprint (pf | out, "=");
      fprint (pf | out, s2e0); fprint (pf | out, ", ");
      aux (out, l, s2e, ls2es)
    end
  | LABS2EXPLSTnil () => begin
      fprint (pf | out, l0); fprint (pf | out, "="); fprint (pf | out, s2e0)
    end
in
  case+ ls2es of
  | LABS2EXPLSTcons (l, s2e, ls2es) => aux (out, l, s2e, ls2es)
  | LABS2EXPLSTnil () => ()
end // end of [fprint_labs2explst]

(* ****** ****** *)

implement fprint_tmps2explstlst {m} (pf | out, ts2ess) = let
fun aux (out: &FILE m, i: int, ts2ess: tmps2explstlst): void =
  case+ ts2ess of
  | TMPS2EXPLSTLSTcons (_(*loc*), s2es, ts2ess) => begin
      if i > 0 then fprint (pf | out, "; ");
      fprint_s2explst (pf | out, s2es); aux (out, i + 1, ts2ess)
    end
  | TMPS2EXPLSTLSTnil () => ()
in
  aux (out, 0, ts2ess)
end // end of [fprint_s2explstlst]

implement fprint_wths2explst {m} (pf | out, wths2es) = let
fun aux (out: &FILE m, i: int, wths2es: wths2explst): void =
  case+ wths2es of
  | WTHS2EXPLSTcons_some (refval, s2e, wths2es) => begin
      if i > 0 then fprint (pf | out, "; ");
      fprint (pf | out, "Some("); fprint (pf | out, s2e);
      fprint (pf | out, ")"); aux (out, i + 1, wths2es)
    end
  | WTHS2EXPLSTcons_none (wths2es) => begin
      if i > 0 then fprint (pf | out, "; ");
      fprint (pf | out, "None()"); aux (out, i + 1, wths2es)
    end
  | WTHS2EXPLSTnil () => ()
in
  aux (out, 0, wths2es)
end // end of [fprint_wths2explst]

(* ****** ****** *)

implement fprint_s2lab (pf | out, s2l): void = begin case+ s2l of
  | S2LAB0lab l => fprint (pf | out, l)
  | S2LAB0ind s2ess => begin
      fprint (pf | out, "["); fprint (pf | out, s2ess); fprint (pf | out, "]")
    end
  | S2LAB1lab (l, _) => fprint (pf | out, l)
  | S2LAB1ind (s2ess, _) =>  begin
      fprint (pf | out, "["); fprint (pf | out, s2ess); fprint (pf | out, "]")
    end
end // end of [fprint_s2lab]

implement print_s2lab (s2l) = print_mac (fprint_s2lab, s2l)
implement prerr_s2lab (s2l) = prerr_mac (fprint_s2lab, s2l)

(* ****** ****** *)

implement fprint_s2kexp (pf | out, s2ke): void = case+ s2ke of
  | S2KEany () => begin
      fprint (pf | out, "S2KEany()")
    end
  | S2KEapp(s2ke, s2kes) => begin
      fprint (pf | out, "S2KEapp(");
      fprint (pf | out, s2ke);
      fprint (pf | out, "; ");
      fprint (pf | out, s2kes);
      fprint (pf | out, ")")
    end
  | S2KEcst s2c => begin
      fprint_s2cst (pf | out, s2c)
    end
  | S2KEfun (fc, s2kes, s2ke) => begin
      fprint (pf | out, "S2KEfun(");
      $Syn.fprint_funclo (pf | out, fc);
      fprint (pf | out, "; ");
      fprint (pf | out, s2kes);
      fprint (pf | out, "; ");
      fprint (pf | out, s2ke);
      fprint (pf | out, ")")
    end
  | S2KEtyarr () => begin
      fprint (pf | out, "S2KEtyarr()")
    end
  | S2KEtyrec (recknd, ls2kes) => begin
      fprint (pf | out, "S2KEtyrec(");
      fprint (pf | out, ls2kes);
      fprint (pf | out, ")")
    end
  | S2KEunion (s2kes) => begin
      fprint (pf | out, "S2KEunion(");
      fprint (pf | out, s2kes);
      fprint (pf | out, ")")
    end
  | S2KEvar s2v => begin
      fprint_s2var (pf | out, s2v)
    end

implement fprint_s2kexplst {m} (pf | out, s2kes0) = let
fun aux (out: &FILE m, s2ke0: s2kexp, s2kes: s2kexplst): void =
  case+ s2kes of
  | cons (s2ke, s2kes) => begin
      fprint_s2kexp (pf | out, s2ke0); fprint (pf | out, ", "); aux (out, s2ke, s2kes)
    end
  | nil () => fprint_s2kexp (pf | out, s2ke0)
in
  case+ s2kes0 of
    | cons (s2ke, s2kes) => aux (out, s2ke, s2kes) | nil () => ()
end // end of [fprint_s2kexplst]

implement fprint_labs2kexplst {m} (pf | out, ls2kes) = let
fun aux (out: &FILE m, l0: lab_t, s2ke0: s2kexp, ls2kes: labs2kexplst): void =
  case+ ls2kes of
  | LABS2KEXPLSTcons (l, s2ke, ls2kes) => begin
      fprint (pf | out, l0); fprint (pf | out, "=");
      fprint (pf | out, s2ke0); fprint (pf | out, ", ");
      aux (out, l, s2ke, ls2kes)
    end
  | LABS2KEXPLSTnil () => begin
      fprint (pf | out, l0); fprint (pf | out, "="); fprint (pf | out, s2ke0)
    end
in
  case+ ls2kes of
  | LABS2KEXPLSTcons (l, s2ke, ls2kes) => aux (out, l, s2ke, ls2kes)
  | LABS2KEXPLSTnil () => ()
end // end of [fprint_labs2kexplst]

//

implement print_s2kexp (s2ke) = print_mac (fprint_s2kexp, s2ke)
implement prerr_s2kexp (s2ke) = prerr_mac (fprint_s2kexp, s2ke)

(* ****** ****** *)

implement fprint_s2zexp (pf | out, s2ze) = case+ s2ze of
  | S2ZEapp (s2ze_fun, s2zes_arg) => begin
      fprint (pf | out, "S2ZEapp(");
      fprint_s2zexp (pf | out, s2ze_fun);
      fprint (pf | out, "; ");
      fprint_s2zexplst (pf | out, s2zes_arg);
      fprint (pf | out, ")")
    end
  | S2ZEbot () => begin
      fprint (pf | out, "S2ZEbot()")
    end
  | S2ZEbyte n => begin
      fprint (pf | out, "S2ZEbyte(");
      fprint (pf | out, n);
      fprint (pf | out, ")")
    end
  | S2ZEcst s2c => begin
      fprint (pf | out, "S2ZEcst(");
      fprint (pf | out, s2c);
      fprint (pf | out, ")")
    end
  | S2ZEextype name => begin
      fprint (pf | out, "S2ZEextype(");
      fprint (pf | out, name);
      fprint (pf | out, ")")
    end
(*
  | S2ZEout s2ze => begin
      fprint (pf | out, "S2ZEout(");
      fprint (pf | out, s2ze);
      fprint (pf | out, ")")
    end
*)
  | S2ZEtyarr (s2ze, s2ess_dim) => begin
      fprint (pf | out, "S2ZEtyarr(");
      fprint (pf | out, s2ze);
      fprint (pf | out, "; ");
      fprint (pf | out, s2ess_dim);
      fprint (pf | out, ")")
    end
  | S2ZEtyrec (_(*knd*), ls2zes) => begin
      fprint (pf | out, "S2ZEtyrec(");
      fprint_labs2zexplst (pf | out, ls2zes);
      fprint (pf | out, ")")
    end
  | S2ZEunion (_(*stamp*), ls2zes) => begin
      fprint (pf | out, "S2ZEunion(");
      fprint_labs2zexplst (pf | out, ls2zes);
      fprint (pf | out, ")")
    end
  | S2ZEvar s2v => begin
      fprint (pf | out, "S2ZEvar(");
      fprint (pf | out, s2v);
      fprint (pf | out, ")")
    end
  | S2ZEword n => begin
      fprint (pf | out, "S2ZEword(");
      fprint (pf | out, n);
      fprint (pf | out, ")")
    end

(* ****** ****** *)

implement fprint_s2zexplst {m} (pf | out, s2zes) = let
fun aux (out: &FILE m, i: int, s2zes: s2zexplst): void =
  case+ s2zes of
  | cons (s2ze, s2zes) => begin
      if i > 0 then fprint (pf | out, ", ");
      fprint (pf | out, s2ze); aux (out, i+1, s2zes)
    end
  | nil () => ()
in
  aux (out, 0, s2zes)
end // end of [fprint_s2zexplst]

(* ****** ****** *)

implement fprint_labs2zexplst {m} (pf | out, ls2zes) = let
fun aux (out: &FILE m, i: int, ls2zes: labs2zexplst): void =
  case+ ls2zes of
  | LABS2ZEXPLSTcons (l, s2ze, ls2zes) => begin
      if i > 0 then fprint (pf | out, ", ");
      fprint (pf | out, l); fprint (pf | out, "="); fprint (pf | out, s2ze);
      aux (out, i+1, ls2zes)
    end
  | LABS2ZEXPLSTnil () => ()
in
  aux (out, 0, ls2zes)
end // end of [fprint_labs2zexplst]

(* ****** ****** *)

implement print_s2explst (s2es) = print_mac (fprint_s2explst, s2es)
implement prerr_s2explst (s2es) = prerr_mac (fprint_s2explst, s2es)

(* ****** ****** *)

implement print_labs2explst (ls2es) = print_mac (fprint_labs2explst, ls2es)
implement prerr_labs2explst (ls2es) = prerr_mac (fprint_labs2explst, ls2es)

(* ****** ****** *)

implement fprint_s2exparg (pf | out, s2a) =
  case+ s2a.s2exparg_node of
  | S2EXPARGone() => fprint (pf | out, "..")
  | S2EXPARGall() => fprint (pf | out, "...")
  | S2EXPARGseq s2es => fprint (pf | out, s2es)

implement fprint_s2exparglst {m} (pf | out, s2as0) = let
fun aux (out: &FILE m, s2a0: s2exparg, s2as: s2exparglst): void =
  case+ s2as of
  | cons (s2a, s2as) => begin
      fprint_s2exparg (pf | out, s2a0);
      fprint (pf | out, ", ");
      aux (out, s2a, s2as)
    end
  | nil () => fprint_s2exparg (pf | out, s2a0)
in
  case+ s2as0 of
    | cons (s2a, s2as) => aux (out, s2a, s2as) | nil () => ()
end // end of [fprint_s2exparglst]

implement print_s2exparglst (s2as) = print_mac (fprint_s2exparglst, s2as)
implement prerr_s2exparglst (s2as) = prerr_mac (fprint_s2exparglst, s2as)

(* ****** ****** *)

(* end of [ats_staexp2_print.dats] *)
