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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October 2007

(* ****** ****** *)

%{^

#include "ats_counter.cats" /* only needed for [ATS/Geizella] */

%}

(* ****** ****** *)

staload "ats_stamp.sats"
staload "ats_staexp1.sats"
staload "ats_staexp2.sats"

(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)

macdef fprint_label = $Lab.fprint_label
macdef fprint_symbol = $Sym.fprint_symbol

(* ****** ****** *)

fun fprint_tyreckind {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, k: tyreckind): void =
  case+ k of
  | TYRECKINDbox _ => fprint1_string (pf | out, "box")
  | TYRECKINDflt0 _ => fprint1_string (pf | out, "flt")
  | TYRECKINDflt1 s => begin
      fprint1_string (pf | out, "flt(");
      $Stamp.fprint_stamp (pf | out, s);
      fprint1_string (pf | out, ")")
    end
// end of [fprint_tyreckind]

(* ****** ****** *)

fn fprint_s2rtdat {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2td: s2rtdat_t): void =
  fprint_symbol (pf | out, s2rtdat_sym_get s2td)
// end of [fprint_s2rtdat]

fn fprint_s2rtbas {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s2tb: s2rtbas): void =
  case+ s2tb of
  | S2RTBASpre x => fprint_symbol (pf | out, x)
  | S2RTBASimp (x, _, _) => fprint_symbol (pf | out, x)
  | S2RTBASdef x => fprint_s2rtdat (pf | out, x)
// end of [fprint_s2rtbas]

(* ****** ****** *)

implement fprint_s2item (pf | out, s2i) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s2i of
  | S2ITEMcst _ => begin
      fprint1_string (pf | out, "S2ITEMcst(...)")
    end // end of [S2ITEMcst]
  | S2ITEMdatconptr d2c => begin
      strpr "S2ITEMdatconptr("; fprint_d2con (pf | out, d2c); strpr ")"
    end // end of [S2ITEMdatconptr]
  | S2ITEMdatcontyp d2c => begin
      strpr "S2ITEMdatcontyp("; fprint_d2con (pf | out, d2c); strpr ")"
    end // end of [S2ITEMdatcontyp]
  | S2ITEMe1xp e1xp => begin
      strpr "S2ITEMe1xp("; fprint_e1xp (pf | out, e1xp); strpr ")"
    end // end of [S2ITEMe1xp]
  | S2ITEMfil fil => begin
      strpr "S2ITEMfil(";
      $Fil.fprint_filename (pf | out, fil);
      strpr ")"
    end // end of [S2ITEMfil]
  | S2ITEMvar s2v => begin
      strpr "S2ITEMvar("; fprint_s2var (pf | out, s2v); strpr ")"
    end // end of [S2ITEMvar]
end (* end of [fprint_s2item] *)

implement print_s2item (s2i) = print_mac (fprint_s2item, s2i)
implement prerr_s2item (s2i) = prerr_mac (fprint_s2item, s2i)

(* ****** ****** *)

implement fprint_s2rt (pf | out, s2t) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s2t of
  | S2RTbas s2tb => fprint_s2rtbas (pf | out, s2tb)
  | S2RTfun (s2ts, s2t) => begin
      strpr "S2RTfun(";
      fprint_s2rtlst (pf | out, s2ts);
      strpr "; ";
      fprint_s2rt (pf | out, s2t);
      strpr ")"
    end // end of [S2RTfun]
  | S2RTtup s2ts => begin
      strpr "S2RTtup("; fprint_s2rtlst (pf | out, s2ts); strpr ")"
    end // end of [S2RTtup]
end (* end of [fprint_s2rt] *)

(* ****** ****** *)

implement fprint_s2rtlst {m} (pf | out, s2ts) = let
  fun aux (out: &FILE m, s2ts: s2rtlst, i: int): void =
    case+ s2ts of
    | cons (s2t, s2ts) => aux (out, s2ts, i+1) where {
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = fprint_s2rt (pf | out, s2t)
      } // end of [cons]
    | nil () => ()
  // end of [aux]
in
  aux (out, s2ts, 0)
end (* end of [fprint_s2rtlst] *)

implement fprint_s2rtlstlst {m} (pf | out, s2tss) = let
  fun aux (out: &FILE m, s2tss: s2rtlstlst, i: int): void =
    case+ s2tss of
    | cons (s2ts, s2tss) => aux (out, s2tss, i+1) where {
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = fprint_s2rtlst (pf | out, s2ts)
      } // end of [cons]
    | nil () => ()
  // end of [aux]
in
  aux (out, s2tss, 0)
end // end of [fprint_s2rtlstlst]

(* ****** ****** *)

implement print_s2rt (s2t) = print_mac (fprint_s2rt, s2t)
implement prerr_s2rt (s2t) = prerr_mac (fprint_s2rt, s2t)

(* ****** ****** *)

implement fprint_s2rtext (pf | out, s2te) = begin
  case+ s2te of
  | S2TEsrt s2t => fprint_s2rt (pf | out, s2t)
  | S2TEsub (s2v, s2t, s2es) => begin
      fprint1_string (pf  | out, "{");
      fprint_s2var (pf | out, s2v);
      fprint1_string (pf  | out, ": ");
      fprint_s2rt (pf | out, s2t);
      fprint1_string (pf  | out, " | ");
      fprint_s2explst (pf | out, s2es);
      fprint1_string (pf | out, "}")
    end // end of [S2TEsub]
(*
  | S2TElam (s2vs, s2te) => begin
      fprint1_string (pf | out, "S2TElam(");
      fprint_s2varlst (pf | out, s2vs);
      fprint1_string (pf | out, "; ");
      fprint_s2rtext (pf | out, s2te);
      fprint1_string (pf | out, ")")
    end // end of [S2TElam]
  | S2TEapp (s2te, s2es) => begin
      fprint1_string (pf | out, "S2TEapp(");
      fprint_s2rtext (pf | out, s2te);
      fprint1_string (pf | out, "; ");
      fprint_s2explst (pf | out, s2es);
      fprint1_string (pf | out, ")")
    end // end of [S2TEapp]
*)
end (* end of [fprint_s2rtext] *)

(* ****** ****** *)

implement fprint_s2eff (pf | out, s2fe) = begin
  case+ s2fe of
  | S2EFFall () => begin
      fprint1_string (pf | out, "<all>")
    end
  | S2EFFnil () => begin
      fprint1_string (pf | out, "<nil>")
    end
  | S2EFFset (effs, s2es) => begin
      fprint1_string (pf | out, "<");
      $Eff.fprint_effset (pf | out, effs);
      fprint1_string (pf | out, ";");
      fprint_s2explst (pf | out, s2es);
      fprint1_string (pf | out, ">")
    end
end (* end of [fprint_s2eff] *)

implement print_s2eff (s2fe) = print_mac (fprint_s2eff, s2fe)
implement prerr_s2eff (s2fe) = prerr_mac (fprint_s2eff, s2fe)

(* ****** ****** *)

implement fprint_s2exp (pf | out, s2e0) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s2e0.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) => begin
      strpr "S2Eapp(";
      fprint_s2exp (pf | out, s2e_fun);
      strpr "; ";
      fprint_s2explst (pf | out, s2es_arg);
      strpr ")"
    end // end of [S2Eapp]
  | S2Echar c => begin
      strpr "S2Echar("; fprint1_char (pf | out, c); strpr ")"
    end // end of [S2Echar]
  | S2Eclo (knd, s2e) => begin
      strpr "S2Eclo(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_s2exp (pf | out, s2e);
      strpr ")"
    end // end of [S2Eclo]
  | S2Ecrypt (s2e) => begin
      strpr "S2Ecrypt("; fprint_s2exp (pf | out, s2e); strpr ")"
    end // end of [S2Ecrypt]
  | S2Ecst s2c => begin
      strpr "S2Ecst("; fprint_s2cst (pf | out, s2c); strpr ")"
    end // end of [S2Ecst]
  | S2Edatconptr (d2c, s2es) => begin
      strpr "S2Edatconptr(";
      fprint_d2con (pf | out, d2c);
      strpr "; ";
      fprint_s2explst (pf | out, s2es);
      strpr ")"
    end // end of [S2Edatconptr]
  | S2Edatcontyp (d2c, s2es) => begin
      strpr "S2Edatcontyp(";
      fprint_d2con (pf | out, d2c);
      strpr "; ";
      fprint_s2explst (pf | out, s2es);
      strpr ")"
    end // end of [S2Edatcontyp]
  | S2Eeff s2fe => begin
      strpr "S2Eeff("; fprint_s2eff (pf | out, s2fe); strpr ")"
    end // end of [S2Eeff]
  | S2Eeqeq (s2e1, s2e2) => begin
      strpr "S2Eeqeq(";
      fprint_s2exp (pf | out, s2e1);
      strpr ", ";
      fprint_s2exp (pf | out, s2e2);
      strpr ")"
    end // end of [S2Eeqeq]
  | S2Eexi (s2vs, s2ps, s2e) => begin
      strpr "S2Eexi(";
      fprint_s2varlst (pf | out, s2vs);
      strpr "; ";
      fprint_s2explst (pf | out, s2ps);
      strpr "; ";
      fprint_s2exp (pf | out, s2e);
      strpr ")"
    end // end of [S2Eexi]
  | S2Eextype name => begin
      strpr "S2Eextype("; fprint1_string (pf | out, name); strpr ")"
    end // end of [S2Eextype]
  | S2Efun (fc, lin, s2fe, npf, s2es, s2e) => begin
      strpr "S2Efun(";
      $Syn.fprint_funclo (pf | out, fc);
      strpr "; ";
      fprint1_int (pf | out, lin);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_s2explst (pf | out, s2es);
      strpr "; ";
      fprint_s2exp (pf | out, s2e);
      strpr ")"
    end // end of [S2Efun]
  | S2Eint i(*int*) => begin
      strpr "S2Eint("; fprint1_int (pf | out, i); strpr ")"
    end // end of [S2Eint]
  | S2Eintinf i(*intinf*) => begin
      strpr "S2Eint(";
      $IntInf.fprint_intinf (pf | out, i);
      strpr ")"
    end // end of [S2Eintinf]
  | S2Elam (s2vs, s2e) => begin
      strpr "S2Elam(";
      fprint_s2varlst (pf | out, s2vs);
      strpr "; ";
      fprint_s2exp (pf | out, s2e);
      strpr ")"
    end // end of [S2Elam]
  | S2Emetfn (_(*stamp*), s2es, s2e) => begin
      strpr "S2Emetfn(";
      fprint_s2explst (pf | out, s2es);
      strpr "; ";
      fprint_s2exp (pf | out, s2e);
      strpr ")"
    end // end of [S2Emetfn]
  | S2Emetlt (s2es1, s2es2) => begin
      strpr "S2Emetlt(";
      fprint_s2explst (pf | out, s2es1);
      strpr ", ";
      fprint_s2explst (pf | out, s2es2);
      strpr ")"
    end // end of [S2Emetlt]
  | S2Enamed (name, s2e) => begin
      strpr "S2Enamed(";
      $Sym.fprint_symbol (pf | out, name);
      strpr ", ";
      fprint_s2exp (pf | out, s2e);
      strpr ")"
    end // end of [S2Enamed]
  | S2Eout s2e => begin
      strpr "S2Eout("; fprint_s2exp (pf | out, s2e); strpr ")"
    end // end of [S2Eout]
  | S2Eproj (s2e, s2l) => begin
      strpr "S2Eproj(";
      fprint_s2exp (pf | out, s2e);
      strpr "; ";
      fprint_s2lab (pf | out, s2l);
      strpr ")"
    end // end of [S2Eproj]
  | S2Eread (s2e_v, s2e_vt) => begin
      strpr "S2Eread(";
      fprint_s2exp (pf | out, s2e_v);
      strpr ", ";
      fprint_s2exp (pf | out, s2e_vt);
      strpr ")"
    end // end of [S2Eread]
  | S2Erefarg (refval, s2e) => begin
      strpr "S2Erefarg(";
      fprint1_int (pf | out, refval);
      strpr ", ";
      fprint_s2exp (pf | out, s2e);
      strpr ")"
    end // end of [S2Erefarg]
  | S2Esel (s2e, i) => begin
      strpr "S2Esel(";
      fprint_s2exp (pf | out, s2e);
      strpr "; ";
      fprint1_int (pf | out, i);
      strpr ")"
    end // end of [S2Esel]
  | S2Esize (s2ze) => begin
      strpr "S2Esize("; fprint_s2zexp (pf | out, s2ze); strpr ")"
    end
  | S2Esizeof (s2e) => begin
      strpr "S2Esizeof("; fprint_s2exp (pf | out, s2e); strpr ")"
    end
  | S2Etop (knd, s2e) => begin
      strpr "S2Etop(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_s2exp (pf | out, s2e);
      strpr ")"
    end // end of [S2Etop]
  | S2Etup s2es => begin
      strpr "S2Etup(";
      fprint_s2explst (pf | out, s2es);
      strpr ")"
    end // end of [S2Etup]
  | S2Etyarr (s2e_elt, s2ess_dim) => begin
      strpr "S2Etyarr(";
      fprint_s2exp (pf | out, s2e_elt);
      strpr "; ";
      fprint_s2explstlst (pf | out, s2ess_dim);
      strpr ")"
    end // end of [S2Etyarr]
  | S2Etyleq (knd, s2e1, s2e2) => begin
      strpr "S2Etyleq(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_s2exp (pf | out, s2e1);
      strpr ", ";
      fprint_s2exp (pf | out, s2e2);
      strpr ")"
    end // end of [S2Etyleq]
  | S2Etylst s2es => begin
      strpr "S2Etylst("; fprint_s2explst (pf | out, s2es); strpr ")"
    end // end of [S2Etylst]
  | S2Etyrec (k, npf, ls2es) => begin
      strpr "S2Etyrec(";
      fprint_tyreckind (pf | out, k);
      strpr "; ";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_labs2explst (pf | out, ls2es);
      strpr ")"
    end // end of [S2Etyrec]
  | S2Euni (s2vs, s2ps, s2e) => begin
      strpr "S2Euni(";
      fprint_s2varlst (pf | out, s2vs);
      strpr "; ";
      fprint_s2explst (pf | out, s2ps);
      strpr "; ";
      fprint_s2exp (pf | out, s2e);
      strpr ")"
    end // end of [S2Euni]
  | S2Eunion (stamp, s2e_ind, ls2es) => begin
      strpr "S2Eunion(";
      $Stamp.fprint_stamp (pf | out, stamp);
      strpr "; ";
      fprint_s2exp (pf | out, s2e_ind);
      strpr "; ";
      fprint_labs2explst (pf | out, ls2es);
      strpr ")"
    end // end of [S2Eunion]
  | S2Evar s2v => begin
      strpr "S2Evar("; fprint_s2var (pf | out, s2v); strpr ")"
    end // end of [S2Evar]
  | S2EVar s2V => let
      val () = begin
        strpr "S2EVar("; fprint_s2Var (pf | out, s2V); strpr ")"
      end // end of [val]
(*
      val () = let
        val os2e = s2Var_link_get s2V in case+ os2e of
        | Some s2e => begin
            strpr "["); fprint_s2exp (pf | out, s2e); strpr "]")
          end
        | None () => ()
      end
*)
    in
      // empty
    end // end of [S2EVar]
  | S2Evararg s2e => begin
      strpr "S2Evararg("; fprint_s2exp (pf | out, s2e); strpr ")"
    end // end of [S2Evararg]
  | S2Ewth (s2e_res, wths2es) => begin
      strpr "S2Ewth(";
      fprint_s2exp (pf | out, s2e_res);
      strpr "; ";
      fprint_wths2explst (pf | out, wths2es);
      strpr ")"
    end // end of [S2Ewth]
(*
  | _ => begin
      prerr "Internal Error: ";
      prerr "[fprint_s2exp]: unsupported static expression";
      prerr_newline ();
      exit (1)      
    end (* end of [_] *)
*)
end (* end of [fprint_s2exp] *)

(* ****** ****** *)

implement print_s2exp (s2e) = print_mac (fprint_s2exp, s2e)
implement prerr_s2exp (s2e) = prerr_mac (fprint_s2exp, s2e)

(* ****** ****** *)

implement fprint_s2explst {m} (pf | out, s2es) = let
  fun aux (out: &FILE m, s2es: s2explst, i: int): void =
    case+ s2es of
    | cons (s2e, s2es) => aux (out, s2es, i+1) where {
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = fprint_s2exp (pf | out, s2e)
      } // end of [cons]
    | nil () => ()
  // end of [aux]
in
  aux (out, s2es, 0)
end (* end of [fprint_s2explst] *)

implement fprint_s2explstlst {m} (pf | out, s2ess) = let
  fun aux (out: &FILE m, s2ess: s2explstlst, i: int): void =
    case+ s2ess of
    | cons (s2es, s2ess) => aux (out, s2ess, i+1) where {
        val () = if i > 0 then fprint1_string (pf | out, "; ")
        val () = fprint_s2explst (pf | out, s2es)
      } // end of [cons]
    | nil () => ()
  // end of [aux]
in
  aux (out, s2ess, 0)
end (* end of [fprint_s2explstlst] *)

(* ****** ****** *)

implement fprint_s2expopt {m} (pf | out, os2e) = begin
  case+ os2e of
  | Some s2e => begin
      fprint1_string (pf | out, "Some(");
      fprint_s2exp (pf | out, s2e);
      fprint1_string (pf | out, ")")
    end // end of [Some]
  | None () => begin
      fprint1_string (pf | out, "None()")
    end // end of [None]
end (* end of [fprint_s2expopt] *)

(* ****** ****** *)

implement fprint_labs2explst {m} (pf | out, ls2es) = let
  fun aux (out: &FILE m, ls2es: labs2explst, i: int): void =
    case+ ls2es of
    | LABS2EXPLSTcons (l, s2e, ls2es) => let
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = fprint_label (pf | out, l)
        val () = fprint1_string (pf | out, "=")
        val () = fprint_s2exp (pf | out, s2e)
      in
        aux (out, ls2es, i+1)
      end // end of [LABS2EXPLSTcons]
    | LABS2EXPLSTnil () => ()
  // end of [aux]
in
  aux (out, ls2es, 0)
end (* end of [fprint_labs2explst] *)

(* ****** ****** *)

implement fprint_tmps2explstlst {m} (pf | out, ts2ess) = let
  fun aux (out: &FILE m, i: int, ts2ess: tmps2explstlst): void =
    case+ ts2ess of
    | TMPS2EXPLSTLSTcons (_(*loc*), s2es, ts2ess) => begin
        if i > 0 then fprint1_string (pf | out, "; ");
        fprint_s2explst (pf | out, s2es); aux (out, i + 1, ts2ess)
      end
    | TMPS2EXPLSTLSTnil () => ()
  // end of [aux]
in
  aux (out, 0, ts2ess)
end // end of [fprint_s2explstlst]

implement fprint_wths2explst {m} (pf | out, wths2es) = let
  fun aux (
      out: &FILE m, wths2es: wths2explst, i: int
    ) : void = let
    macdef strpr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ wths2es of
    | WTHS2EXPLSTcons_some (refval, s2e, wths2es) => let
        val () = if i > 0 then strpr "; "
        val () = begin
          strpr "Some("; fprint_s2exp (pf | out, s2e); strpr ")"
        end // end of [val]
      in
        aux (out, wths2es, i+1)
      end // end of [WTHS2EXPLSTcons_some]
    | WTHS2EXPLSTcons_none (wths2es) => let
        val () = if i > 0 then strpr "; "
        val () = fprint1_string (pf | out, "None()")
      in
        aux (out, wths2es, i+1)
      end // end of [STHS2EXPLSTcons_none]
    | WTHS2EXPLSTnil () => ()
  end // end of [aux]
in
  aux (out, wths2es, 0)
end (* end of [fprint_wths2explst] *)

(* ****** ****** *)

implement fprint_s2lab (pf | out, s2l): void = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s2l of
  | S2LAB0lab l => fprint_label (pf | out, l)
  | S2LAB0ind s2ess => begin
      strpr "["; fprint_s2explstlst (pf | out, s2ess); strpr "]"
    end
  | S2LAB1lab (l, _) => fprint_label (pf | out, l)
  | S2LAB1ind (s2ess, _) =>  begin
      strpr "["; fprint_s2explstlst (pf | out, s2ess); strpr "]"
    end
end (* end of [fprint_s2lab] *)

implement print_s2lab (s2l) = print_mac (fprint_s2lab, s2l)
implement prerr_s2lab (s2l) = prerr_mac (fprint_s2lab, s2l)

(* ****** ****** *)

implement fprint_s2kexp (pf | out, s2ke) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s2ke of
  | S2KEany () => begin
      fprint1_string (pf | out, "S2KEany()")
    end
  | S2KEapp(s2ke, s2kes) => begin
      strpr "S2KEapp(";
      fprint_s2kexp (pf | out, s2ke);
      strpr "; ";
      fprint_s2kexplst (pf | out, s2kes);
      strpr ")"
    end // end of [S2KEapp]
  | S2KEcst s2c => begin
      fprint_s2cst (pf | out, s2c)
    end
  | S2KEfun (fc, s2kes, s2ke) => begin
      strpr "S2KEfun(";
      $Syn.fprint_funclo (pf | out, fc);
      strpr "; ";
      fprint_s2kexplst (pf | out, s2kes);
      strpr "; ";
      fprint_s2kexp (pf | out, s2ke);
      strpr ")"
    end // end of [S2KEfun]
  | S2KEtyarr () => begin
      fprint1_string (pf | out, "S2KEtyarr()")
    end
  | S2KEtyrec (recknd, ls2kes) => begin
      strpr "S2KEtyrec(";
      fprint_labs2kexplst (pf | out, ls2kes);
      strpr ")"
    end
  | S2KEunion (s2kes) => begin
      strpr "S2KEunion("; fprint_s2kexplst (pf | out, s2kes); strpr ")"
    end // end of [S2KEunion]
  | S2KEvar s2v => begin
      fprint_s2var (pf | out, s2v)
    end
end // end of [fprint_sk2exp]

implement fprint_s2kexplst {m} (pf | out, s2kes) = let
  fun aux (out: &FILE m, s2kes: s2kexplst, i: int): void =
    case+ s2kes of
    | cons (s2ke, s2kes) => aux (out, s2kes, i+1) where {
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = fprint_s2kexp (pf | out, s2ke)
      } // end of [cons]
    | nil () => ()
  // end of [aux]
in
  aux (out, s2kes, 0)
end // end of [fprint_s2kexplst]

implement fprint_labs2kexplst {m} (pf | out, ls2kes) = let
  fun aux (
      out: &FILE m
    , ls2kes: labs2kexplst
    , i: int
    ) : void = let
    macdef strpr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ ls2kes of
    | LABS2KEXPLSTcons (l, s2ke, ls2kes) => let
        val () = if (i > 0) then strpr ", "
        val () = (fprint_label (pf | out, l); strpr "=")
        val () = fprint_s2kexp (pf | out, s2ke)
      in
        aux (out, ls2kes, i+1)
      end // end of [LABS2KEXPLSTcons]
    | LABS2KEXPLSTnil () => ()
  end // end of [aux]
in
  aux (out, ls2kes, 0)
end (* end of [fprint_labs2kexplst] *)

(* ****** ****** *)

implement print_s2kexp (s2ke) = print_mac (fprint_s2kexp, s2ke)
implement prerr_s2kexp (s2ke) = prerr_mac (fprint_s2kexp, s2ke)

(* ****** ****** *)

implement fprint_s2zexp (pf | out, s2ze) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s2ze of
  | S2ZEapp (s2ze_fun, s2zes_arg) => begin
      strpr "S2ZEapp(";
      fprint_s2zexp (pf | out, s2ze_fun);
      strpr "; ";
      fprint_s2zexplst (pf | out, s2zes_arg);
      strpr ")"
    end // end of [S2ZEapp]
  | S2ZEbot () => begin
      fprint1_string (pf | out, "S2ZEbot()")
    end // end of [S2ZEbot]
  | S2ZEbyte n => begin
      strpr "S2ZEbyte("; fprint1_int (pf | out, n); strpr ")"
    end // end of [S2ZEbyte]
  | S2ZEcst s2c => begin
      strpr "S2ZEcst("; fprint_s2cst (pf | out, s2c); strpr ")"
    end // end of [S2ZEcst]
  | S2ZEextype name => begin
      strpr "S2ZEextype("; fprint1_string (pf | out, name); strpr ")"
    end // end of [S2ZEextype]
(*
  | S2ZEout s2ze => begin
      strpr "S2ZEout(");
      fprint_s2zexp (pf | out, s2ze);
      strpr ")")
    end // end of [S2ZEout]
*)
  | S2ZEtyarr (s2ze, s2ess_dim) => begin
      strpr "S2ZEtyarr(";
      fprint_s2zexp (pf | out, s2ze);
      strpr "; ";
      fprint_s2explstlst (pf | out, s2ess_dim);
      strpr ")"
    end // end of [S2ZEtyarr]
  | S2ZEtyrec (_(*knd*), ls2zes) => begin
      strpr "S2ZEtyrec(";
      fprint_labs2zexplst (pf | out, ls2zes);
      strpr ")"
    end // end of [S2ZEtyrec]
  | S2ZEunion (_(*stamp*), ls2zes) => begin
      strpr "S2ZEunion(";
      fprint_labs2zexplst (pf | out, ls2zes);
      strpr ")"
    end // end of [S2ZEunion]
  | S2ZEvar s2v => begin
      strpr "S2ZEvar("; fprint_s2var (pf | out, s2v); strpr ")"
    end // end of [S2ZEvar]
  | S2ZEword n => begin
      strpr "S2ZEword("; fprint1_int (pf | out, n); strpr ")"
    end // end of [S2ZEword]
end (* end of [fprint_s2zexp] *)

(* ****** ****** *)

implement fprint_s2zexplst {m} (pf | out, s2zes) = let
  fun aux (out: &FILE m, s2zes: s2zexplst, i: int): void =
    case+ s2zes of
    | cons (s2ze, s2zes) => aux (out, s2zes, i+1) where {
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = fprint_s2zexp (pf | out, s2ze)
      } // end of [cons]
    | nil () => ()
  // end of [aux]
in
  aux (out, s2zes, 0)
end (* end of [fprint_s2zexplst] *)

(* ****** ****** *)

implement fprint_labs2zexplst {m} (pf | out, ls2zes) = let
  fun aux (out: &FILE m, ls2zes: labs2zexplst, i: int): void =
    case+ ls2zes of
    | LABS2ZEXPLSTcons
        (l, s2ze, ls2zes) => aux (out, ls2zes, i+1) where {
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = (fprint_label (pf | out, l); fprint1_string (pf | out, "="))
        val () = fprint_s2zexp (pf | out, s2ze)
      } // end of [LABS2ZEXPLSTcons]
    | LABS2ZEXPLSTnil () => ()
in
  aux (out, ls2zes, 0)
end (* end of [fprint_labs2zexplst] *)

(* ****** ****** *)

implement print_s2explst (s2es) = print_mac (fprint_s2explst, s2es)
implement prerr_s2explst (s2es) = prerr_mac (fprint_s2explst, s2es)

(* ****** ****** *)

implement print_labs2explst (ls2es) = print_mac (fprint_labs2explst, ls2es)
implement prerr_labs2explst (ls2es) = prerr_mac (fprint_labs2explst, ls2es)

(* ****** ****** *)

implement fprint_s2exparg (pf | out, s2a) =
  case+ s2a.s2exparg_node of
  | S2EXPARGone() => fprint1_string (pf | out, "..")
  | S2EXPARGall() => fprint1_string (pf | out, "...")
  | S2EXPARGseq s2es => fprint_s2explst (pf | out, s2es)
// end of [fprint_s2exparg]

implement fprint_s2exparglst {m} (pf | out, s2as) = let
  fun aux (out: &FILE m, s2as: s2exparglst, i: int): void =
    case+ s2as of
    | cons (s2a, s2as) => aux (out, s2as, i+1) where {
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = fprint_s2exparg (pf | out, s2a)
      } // end of [cons]
    | nil () => ()
  // end of [aux]
in
  aux (out, s2as, 0)
end (* end of [fprint_s2exparglst] *)

implement print_s2exparglst (s2as) = print_mac (fprint_s2exparglst, s2as)
implement prerr_s2exparglst (s2as) = prerr_mac (fprint_s2exparglst, s2as)

(* ****** ****** *)

implement fprint_s2qua (pf | out, s2q) = begin
  fprint_string (pf | out, "(");
  fprint_s2varlst (pf | out, s2q.0);
  fprint_string (pf | out, " | ");
  fprint_s2explst (pf | out, s2q.1);
  fprint_string (pf | out, ")");
end // end of [fprint_s2qua]

implement fprint_s2qualst {m} (pf | out, s2qs) = let
  fun aux (out: &FILE m, i: int, s2qs: s2qualst): void =
    case+ s2qs of
    | cons (s2q, s2qs) => aux (out, i+1, s2qs) where {
        val () = if i > 0 then fprint1_string (pf | out, ", ")
        val () = fprint_s2qua (pf | out, s2q)
      } // end of [cons]
    | nil () => ()
  // end of [aux]
in
  aux (out, 0, s2qs)
end // end of [fprint_s2qualst]

(* ****** ****** *)

implement print_s2qualst (s2qs) = print_mac (fprint_s2qualst, s2qs)
implement prerr_s2qualst (s2qs) = prerr_mac (fprint_s2qualst, s2qs)

(* ****** ****** *)

(* end of [ats_staexp2_print.dats] *)
