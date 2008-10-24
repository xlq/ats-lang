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

// Time: August 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Eff = "ats_effect.sats"
staload Lab = "ats_label.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"

(* ****** ****** *)

#define nil list_nil
#define :: list_cons
#define cons list_cons

(* ****** ****** *)

typedef lab_t = $Lab.label_t
typedef sym_t = $Sym.symbol_t

(* ****** ****** *)

macdef fprint_label = $Lab.fprint_label

(* ****** ****** *)

implement fprint_e1xp (pf | out, e0) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ e0.e1xp_node of
  | E1XPapp (e, _(*loc_arg*), es) => begin
      strpr "E1XPapp(";
      fprint_e1xp (pf | out, e);
      strpr "; ";
      fprint_e1xplst (pf | out, es);
      strpr ")"
    end // end of [E1XPapp]
  | E1XPchar (c: char) => begin
      strpr "E1XPchar("; fprint1_char (pf | out, c); strpr ")"
    end // end of [E1XPchar]
  | E1XPfloat (f: string) => begin
      strpr "E1XPfloat("; fprint1_string (pf | out, f); strpr ")"
    end // end of [E1XPfloat]
  | E1XPide (id: sym_t) => begin
      $Sym.fprint_symbol (pf | out, id)
    end // end of [E1XPide]
  | E1XPint (int(*string*)) => begin
      strpr "E1XPint("; fprint1_string (pf | out, int); strpr ")"
    end // end of [E1XPint]
  | E1XPlist es => begin
      strpr "E1XPlist("; fprint_e1xplst (pf | out, es); strpr ")"
    end // end of [E1XPlist]
  | E1XPnone () => begin
      fprint1_string (pf | out, "E1XPnone()")
    end // end of [E1XPnone]
  | E1XPstring (str, len) => begin
      strpr "E1XPstring(";
      fprint1_string (pf | out, str);
      strpr ", ";
      fprint1_int (pf | out, len);
      strpr ")"
    end // end of [E1XPstring]
end // end of [fprint_e1xp]

implement fprint_e1xplst {m} (pf | out, es0) = let
  fun aux (out: &FILE m, i: int, es: e1xplst): void =
    case+ es of
    | cons (e, es) => let
        val () = if i > 0 then fprint1_string (pf | out, ", ")
      in
        fprint_e1xp (pf | out, e); aux (out, i+1, es)
      end // end of [cons]
    | nil () => ()
in
  aux (out, 0, es0)
end // end of [fprint_e1xplst]

implement print_e1xp (e) = print_mac (fprint_e1xp, e)
implement prerr_e1xp (e) = prerr_mac (fprint_e1xp, e)

implement print_e1xplst (es) = print_mac (fprint_e1xplst, es)
implement prerr_e1xplst (es) = prerr_mac (fprint_e1xplst, es)

(* ****** ****** *)

implement fprint_s1rt (pf | out, s1t0) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s1t0.s1rt_node of
  | S1RTapp (s1t, s1ts) => begin
      strpr "S1RTapp(";
      fprint_s1rt (pf | out, s1t);
      strpr "; ";
      fprint_s1rtlst (pf | out, s1ts);
      strpr ")"
    end // end of [S1RTapp]
  | S1RTlist s1ts => begin
      strpr "S1RTlist("; fprint_s1rtlst (pf | out, s1ts); strpr ")"
    end // end of [S1RTlist]
  | S1RTqid (q, id) => begin
      strpr "S1RTqid(";
      $Syn.fprint_s0rtq (pf | out, q);
      $Sym.fprint_symbol (pf | out, id);
      strpr ")"
    end // end of [S1RTqid]
  | S1RTtup s1ts => begin
      strpr "S1RTtup(";
      fprint_s1rtlst (pf | out, s1ts);
      strpr ")"
    end // end of [S1RTtup]
end // end of [fprint_s1rt]

implement fprint_s1rtlst {m} (pf | out, s1ts0) = let
  fun aux (out: &FILE m, i: int, s1ts: s1rtlst): void =
    case+ s1ts of
    | cons (s1t, s1ts) => let
        val () = if i > 0 then fprint1_string (pf | out, ", ")
      in
        fprint_s1rt (pf | out, s1t); aux (out, i+1, s1ts)
      end
    | nil () => ()
in
  aux (out, 0, s1ts0)
end // end of [fprint_s1rtlst]

implement fprint_s1rtopt (pf | out, os1t) = case+ os1t of
  | Some s1t => fprint_s1rt (pf | out, s1t) | None () => ()

(* ****** ****** *)

implement print_s1rt (s1t) = print_mac (fprint_s1rt, s1t)
implement prerr_s1rt (s1t) = prerr_mac (fprint_s1rt, s1t)

implement print_s1rtlst (s1ts) = print_mac (fprint_s1rtlst, s1ts)
implement prerr_s1rtlst (s1ts) = prerr_mac (fprint_s1rtlst, s1ts)

(* ****** ****** *)

fun fprint_s1arg {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s1a: s1arg)
  : void = let
  val () = $Sym.fprint_symbol (pf | out, s1a.s1arg_sym)
in
  case+ s1a.s1arg_srt of
  | Some s1t => begin
      fprint1_string (pf | out, ": "); fprint_s1rt (pf | out, s1t)
    end
  | None () => ()
end // end of [fprint_s1arg]

fun fprint_s1arglst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s1as: s1arglst)
  : void = let
  fun aux (out: &FILE m, i: int, s1as: s1arglst): void =
    case+ s1as of
    | cons (s1a, s1as) => begin
        if i > 0 then fprint1_string (pf | out, ", "); 
        fprint_s1arg (pf | out, s1a); aux (out, i+1, s1as)
      end
    | nil () => ()
in
  aux (out, 0, s1as)
end // end of [fprint_s1qualst]

(* ****** ****** *)

fun fprint_s1qua {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s1q: s1qua)
  : void = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s1q.s1qua_node of
  | S1Qprop s1e => begin
      strpr "S1Qprop(";
      fprint_s1exp (pf | out, s1e);
      strpr ")"
    end
  | S1Qvars (ids, s1te) => begin
      strpr "S1Qvars(";
      $Syn.fprint_i0delst (pf | out, ids);
      strpr "; ";
      fprint_s1rtext (pf | out, s1te);
      strpr ")"
    end
end // end of [fprint_s1qua]

fun fprint_s1qualst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s1qs0: s1qualst)
  : void = let
  fun aux (out: &FILE m, i: int, s1qs: s1qualst): void =
    case+ s1qs of
    | cons (s1q, s1qs) => begin
        if i > 0 then fprint1_string (pf | out, ", "); 
        fprint_s1qua (pf | out, s1q); aux (out, i+1, s1qs)
      end
    | nil () => ()
in
  aux (out, 0, s1qs0)
end // end of [fprint_s1qualst]

(* ****** ****** *)

implement fprint_s1exp (pf | out, s1e0) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s1e0.s1exp_node of
  | S1Eann (s1e, s1t) => begin
      strpr "S1Eann(";
      fprint_s1exp (pf | out, s1e);
      strpr ", ";
      fprint_s1rt (pf | out, s1t);
      strpr ")"
    end
  | S1Eany () => fprint1_string (pf | out, "S1Eany()")
  | S1Eapp (s1e_fun, _(*loc_arg*), s1es_arg) => begin
      strpr "S1Eapp(";
      fprint_s1exp (pf | out, s1e_fun);
      strpr "; ";
      fprint_s1explst (pf | out, s1es_arg);
      strpr ")"
    end // end of [S1Eapp]
  | S1Echar c => begin
      strpr "S1Echar("; fprint1_char (pf | out, c); strpr ")"
    end // end of [S1Echar]
  | S1Eexi (knd(*funres*), s1qs, s1e) => begin
      strpr "S1Eexi(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_s1qualst (pf | out, s1qs);
      strpr "; ";
      fprint_s1exp (pf | out, s1e);
      strpr ")"
    end // end of [S1Eexi]
  | S1Eextype name => begin
      strpr "S1Eextype(";
      fprint1_string (pf | out, name);
      strpr ")"
    end // end of [S1Eextype]
  | S1Eimp (fc, lin, prf, oefc) => begin
      strpr "S1Eimp(";
      $Syn.fprint_funclo (pf | out, fc); strpr "; ";
      fprint1_int (pf | out, lin); strpr "; ";
      fprint1_int (pf | out, prf); strpr "; ";
      begin case+ oefc of
      | Some efc => $Eff.fprint_effcst (pf | out, efc)
      | None () => ()
      end;
      strpr ")"
    end // end of [S1Eimp]
  | S1Eint str => begin
      strpr "S1Eint("; fprint1_string (pf | out, str); strpr ")"
    end // end of [S1Eint]
  | S1Einvar (refval, s1e) => begin
      strpr "S1Einvar(";
      fprint1_int (pf | out, refval);
      strpr "; ";
      fprint_s1exp (pf | out, s1e);
      strpr ")"
    end // end of [S1Einvar]
  | S1Elam _ => strpr "S1Elam(...)"
  | S1Elist (npf, s1es) => begin
      strpr "S1Elist(";
      fprint1_int (pf | out, npf);
      strpr "; ";
      fprint_s1explst (pf | out, s1es);
      strpr ")"
    end // end of [S1Elist]
  | S1Emod _ => begin
      strpr "S1Emod(";
      fprint1_string (pf | out, "...");
      strpr ")"
    end // end of [S1Emod]
  | S1Eqid (q, id: sym_t) => begin
      $Syn.fprint_s0taq (pf | out, q);
      $Sym.fprint_symbol (pf | out, id)
    end // end of [S1Eqid]
  | S1Eread (s1e1, s1e2) => begin
      strpr "S1Eread(";
      fprint_s1exp (pf | out, s1e1);
      strpr ", ";
      fprint_s1exp (pf | out, s1e2);
      strpr ")"
    end // end of [S1Eread]
  | S1Estruct ls1es => begin
      strpr "S1Estruct(";
      fprint_labs1explst (pf | out, ls1es);
      strpr ")"
    end // end of [S1Estruct]
  | S1Etop (knd, s1e) => begin
      strpr "S1Etop(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_s1exp (pf | out, s1e);
      strpr ")"
    end // end of [S1Etop]
  | S1Etrans (s1e1, s1e2) => begin
      strpr "S1Etrans(";
      fprint_s1exp (pf | out, s1e1);
      strpr ", ";
      fprint_s1exp (pf | out, s1e2);
      strpr ")"
    end // end of [S1Etrans]
  | S1Etyarr (s1e_elt, s1ess_dim) => begin
      strpr "S1Earray(";
      fprint_s1exp (pf | out, s1e_elt);
      fprint1_string (pf | out, ", ...");
      strpr ")"
    end // end pf [S1Etyarr]
  | S1Etyrec (knd, ls1es) => begin
      strpr "S1Etyrec(";
      fprint1_int (pf | out, knd);
      strpr "; ";
      fprint_labs1explst (pf | out, ls1es);
      strpr ")"
    end // end of [S1Etyrec]
  | S1Etytup (flat, s1es) => begin
      strpr "S1Etytup(";
      fprint1_int (pf | out, flat);
      strpr "; ";
      fprint_s1explst (pf | out, s1es);
      strpr ")"
    end // end of [S1Etytup]
  | S1Etytup2 (flat, s1es1, s1es2) => begin
      strpr "S1Etytup2(";
      fprint1_int (pf | out, flat);
      strpr "; ";
      fprint_s1explst (pf | out, s1es1);
      strpr "; ";
      fprint_s1explst (pf | out, s1es2);
      strpr ")"
    end // end of [S1Etytup2]
  | S1Euni (s1qs, s1e) => begin
      strpr "S1Euni(";
      fprint_s1qualst (pf | out, s1qs);
      strpr "; ";
      fprint_s1exp (pf | out, s1e);
      strpr ")"
    end // end of [S1Euni]
  | S1Eunion (s1e, ls1es) => begin
      strpr "S1Eunion(";
      fprint_s1exp (pf | out, s1e);
      strpr "; ";
      fprint_labs1explst (pf | out, ls1es);
      strpr ")"
    end // end of [S1Eunion]
end // end of [fprint_s1exp]

implement fprint_s1explst {m} (pf | out, s1es0) = let
  fun aux (out: &FILE m, i: int, s1es: s1explst): void =
    case+ s1es of
    | cons (s1e, s1es) => let
        val () = if i > 0 then fprint1_string (pf | out, ", ")
      in
        fprint_s1exp (pf | out, s1e); aux (out, i+1, s1es)
      end
    | nil () => ()
in
  aux (out, 0, s1es0)
end // end of [fprint_s1explst]

implement fprint_s1expopt {m} (pf | out, os1e) = begin
  case+ os1e of Some s1e => fprint_s1exp (pf | out, s1e) | None () => ()
end // end of [fprint_s1expopt]

implement fprint_s1explstlst {m} (pf | out, s1ess0) = let
  fun aux (out: &FILE m, i: int, s1ess: s1explstlst): void =
    case+ s1ess of
    | cons (s1es, s1ess) => let
        val () = if i > 0 then fprint1_string (pf | out, "; ")
      in
        fprint_s1explst (pf | out, s1es); aux (out, i+1, s1ess)
      end
    | nil () => ()
in
  aux (out, 0, s1ess0)
end // end of [fprint_s1explstlst]

(* ****** ****** *)

implement fprint_labs1explst {m} (pf | out, ls1es) = let
  fun aux (out: &FILE m, i: int, ls1es: labs1explst): void = let
    macdef strpr (s) = fprint1_string (pf | out, ,(s))
  in
    case+ ls1es of
    | LABS1EXPLSTcons (l, s1e, ls1es) => begin
        if i > 0 then strpr ", ";
        fprint_label (pf | out, l); strpr "=";
        fprint_s1exp (pf | out, s1e); aux (out, i + 1, ls1es)
      end
    | LABS1EXPLSTnil () => ()
  end // end of [aux]
in
  aux (out, 0, ls1es)
end // end of [fprint_labs1explst]

(* ****** ****** *)

implement fprint_tmps1explstlst {m} (pf | out, ts1ess0) = let
  fun aux (out: &FILE m, i: int, ts1ess: tmps1explstlst): void =
    case+ ts1ess of
    | TMPS1EXPLSTLSTcons (_(*loc*), s1es, ts1ess) => let
        val () = if i > 0 then fprint1_string (pf | out, "; ")
      in
        fprint_s1explst (pf | out, s1es); aux (out, i + 1, ts1ess)
      end // end of [TMPS1EXPLSTLSTcons]
    | TMPS1EXPLSTLSTnil () => ()
in
  aux (out, 0, ts1ess0)
end // end of [fprint_s1explstlst]

(* ****** ****** *)

implement fprint_s1rtext (pf | out, s1te) = let
  macdef strpr (s) = fprint1_string (pf | out, ,(s))
in
  case+ s1te.s1rtext_node of
  | S1TEsrt s1t => fprint_s1rt (pf | out, s1t)
  | S1TEsub (sym, s1te, s1es) => begin
      strpr "S1TEsub(";
      $Sym.fprint_symbol (pf | out, sym);
      strpr "; ";
      fprint_s1rtext (pf | out, s1te);
      strpr "; ";
      fprint_s1explst (pf | out, s1es);
      strpr ")"
    end // end of [S1TEsub]
end // end of [fprint_s1rtext]

(* ****** ****** *)

implement print_s1exp (s1e) = print_mac (fprint_s1exp, s1e)
implement prerr_s1exp (s1e) = prerr_mac (fprint_s1exp, s1e)

implement print_s1explst (s1es) = print_mac (fprint_s1explst, s1es)
implement prerr_s1explst (s1es) = prerr_mac (fprint_s1explst, s1es)

(* ****** ****** *)

(* end of [ats_staexp1_print.dats] *)
