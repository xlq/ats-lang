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

implement fprint_e1xp (pf | out, e0) = begin
  case+ e0.e1xp_node of
  | E1XPapp (e, _(*loc_arg*), es) => begin
      fprint (pf | out, "E1XPapp(");
      fprint (pf | out, e);
      fprint (pf | out, "; ");
      fprint (pf | out, es);
      fprint (pf | out, ")")
    end
  | E1XPchar (c: char) => begin
      fprint (pf | out, "E1XPchar(");
      fprint (pf | out, c);
      fprint (pf | out, ")")
    end
  | E1XPfloat (f: string) => begin
      fprint (pf | out, "E1XPfloat(");
      fprint (pf | out, f);
      fprint (pf | out, ")")
    end
  | E1XPide (id: sym_t) => begin
      $Sym.fprint_symbol (pf | out, id)
    end
  | E1XPint (int(*string*)) => begin
      fprint (pf | out, "E1XPint(");
      fprint (pf | out, int);
      fprint (pf | out, ")")
    end
  | E1XPlist es => begin
      fprint (pf | out, "E1XPlist(");
      fprint (pf | out, es);
      fprint (pf | out, ")")
    end
  | E1XPnone () => begin
      fprint (pf | out, "E1XPnone()")
    end
  | E1XPstring (str, len) => begin
      fprint (pf | out, "E1XPstring(");
      fprint (pf | out, str);
      fprint (pf | out, ", ");
      fprint (pf | out, len);
      fprint (pf | out, ")")
    end
end // end of [fprint_e1xp]

implement fprint_e1xplst {m} (pf | out, es0) = let
  fun aux (out: &FILE m, i: int, es: e1xplst): void =
    case+ es of
    | cons (e, es) => begin
        if i > 0 then fprint (pf | out, ", "); 
        fprint (pf | out, e); aux (out, i+1, es)
      end
    | nil () => ()
in
  aux (out, 0, es0)
end // end of [fprint_e1xplst]

implement print_e1xp (e) = print_mac (fprint_e1xp, e)
implement prerr_e1xp (e) = prerr_mac (fprint_e1xp, e)

implement print_e1xplst (es) = print_mac (fprint_e1xplst, es)
implement prerr_e1xplst (es) = prerr_mac (fprint_e1xplst, es)

(* ****** ****** *)

implement fprint_s1rt (pf | out, s1t0) = begin
  case+ s1t0.s1rt_node of
  | S1RTapp (s1t, s1ts) => begin
      fprint (pf | out, "S1RTapp(");
      fprint (pf | out, s1t);
      fprint (pf | out, "; ");
      fprint (pf | out, s1ts);
      fprint (pf | out, ")")
    end
  | S1RTlist s1ts => begin
      fprint (pf | out, "S1RTlist(");
      fprint (pf | out, s1ts);
      fprint (pf | out, ")")
    end
  | S1RTqid (q, id) => begin
      fprint (pf | out, "S1RTqid(");
      $Syn.fprint_s0rtq (pf | out, q);
      $Sym.fprint_symbol (pf | out, id);
      fprint (pf | out, ")")
    end
  | S1RTtup s1ts => begin
      fprint (pf | out, "S1RTtup(");
      fprint (pf | out, s1ts);
      fprint (pf | out, ")")
    end
end // end of [fprint_s1rt]

implement fprint_s1rtlst {m} (pf | out, s1ts0) = let
  fun aux (out: &FILE m, i: int, s1ts: s1rtlst): void =
    case+ s1ts of
    | cons (s1t, s1ts) => begin
        if i > 0 then fprint (pf | out, ", ");
        fprint (pf | out, s1t); aux (out, i+1, s1ts)
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

fun fprint_s1qua {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s1q: s1qua)
  : void = begin case+ s1q.s1qua_node of
  | S1Qprop s1e => begin
      fprint (pf | out, "S1Qprop(");
      fprint (pf | out, s1e);
      fprint (pf | out, ")")
    end
  | S1Qvars (ids, s1te) => begin
      fprint (pf | out, "S1Qvars(");
      $Syn.fprint_i0delst (pf | out, ids);
      fprint (pf | out, "; ");
      fprint (pf | out, s1te);
      fprint (pf | out, ")")
    end
end // end of [fprint_s1qua]

fun fprint_s1qualst {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, s1qs0: s1qualst)
  : void = let
  fun aux (out: &FILE m, i: int, s1qs: s1qualst): void =
    case+ s1qs of
    | cons (s1q, s1qs) => begin
        if i > 0 then fprint (pf | out, ", "); 
        fprint_s1qua (pf | out, s1q); aux (out, i+1, s1qs)
      end
    | nil () => ()
in
  aux (out, 0, s1qs0)
end // end of [fprint_s1qualst]

//

implement fprint_s1exp (pf | out, s1e0) = case+ s1e0.s1exp_node of
  | S1Eann (s1e, s1t) => begin
      fprint (pf | out, "S1Eann(");
      fprint (pf | out, s1e);
      fprint (pf | out, s1t);
      fprint (pf | out, ")")
    end
  | S1Eany () => fprint (pf | out, "S1Eany()")
  | S1Eapp (s1e_fun, _(*loc_arg*), s1es_arg) => begin
      fprint (pf | out, "S1Eapp(");
      fprint (pf | out, s1e_fun);
      fprint (pf | out, "; ");
      fprint (pf | out, s1es_arg);
      fprint (pf | out, ")")
    end      
  | S1Echar c => begin
      fprint (pf | out, "S1Echar(");
      fprint (pf | out, c);
      fprint (pf | out, ")")
    end
  | S1Eexi (knd(*funres*), s1qs, s1e) => begin
      fprint (pf | out, "S1Eexi(");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint_s1qualst (pf | out, s1qs);
      fprint (pf | out, "; ");
      fprint (pf | out, s1e);
      fprint (pf | out, ")")
    end
  | S1Eextype name => begin
      fprint (pf | out, "S1Eextype(");
      fprint (pf | out, name);
      fprint (pf | out, ")")
    end
  | S1Eimp (fc, lin, prf, oefc) => begin
      fprint (pf | out, "S1Eimp(");
      $Syn.fprint_funclo (pf | out, fc); fprint (pf | out, "; ");
      fprint (pf | out, lin); fprint (pf | out, "; ");
      fprint (pf | out, prf); fprint (pf | out, "; ");
      begin case+ oefc of
      | Some efc => $Eff.fprint_effcst (pf | out, efc)
      | None () => ()
      end;
      fprint (pf | out, ")")
    end
  | S1Eint str => begin
      fprint (pf | out, "S1Eint(");
      fprint (pf | out, str);
      fprint (pf | out, ")")
    end
  | S1Einvar (refval, s1e) => begin
      fprint (pf | out, "S1Einvar(");
      fprint (pf | out, refval);
      fprint (pf | out, "; ");
      fprint (pf | out, s1e);
      fprint (pf | out, ")")
    end
  | S1Elam _ => fprint (pf | out, "S1Elam(...)")
  | S1Elist (npf, s1es) => begin
      fprint (pf | out, "S1Elist(");
      fprint (pf | out, npf);
      fprint (pf | out, "; ");
      fprint (pf | out, s1es);
      fprint (pf | out, ")")
    end
  | S1Emod _ => begin
      fprint (pf | out, "S1Emod(");
      fprint (pf | out, "...");
      fprint (pf | out, ")")
    end
  | S1Eqid (q, id: sym_t) => begin
      $Syn.fprint_s0taq (pf | out, q);
      $Sym.fprint_symbol (pf | out, id)
    end
  | S1Eread (s1e1, s1e2) => begin
      fprint (pf | out, "S1Eread(");
      fprint (pf | out, s1e1);
      fprint (pf | out, ", ");
      fprint (pf | out, s1e2);
      fprint (pf | out, ")")
    end
  | S1Estruct ls1es => begin
      fprint (pf | out, "S1Estruct(");
      fprint (pf | out, ls1es);
      fprint (pf | out, ")")
    end
  | S1Etop (knd, s1e) => begin
      fprint (pf | out, "S1Etop(");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint (pf | out, s1e);
      fprint (pf | out, ")")
    end
  | S1Etrans (s1e1, s1e2) => begin
      fprint (pf | out, "S1Etrans(");
      fprint (pf | out, s1e1);
      fprint (pf | out, ", ");
      fprint (pf | out, s1e2);
      fprint (pf | out, ")")
    end
  | S1Etyarr (s1e_elt, s1ess_dim) => begin
      fprint (pf | out, "S1Earray(");
      fprint (pf | out, s1e_elt);
      fprint (pf | out, ", ...");
      fprint (pf | out, ")")
    end
  | S1Etyrec (knd, ls1es) => begin
      fprint (pf | out, "S1Etyrec(");
      fprint (pf | out, knd);
      fprint (pf | out, "; ");
      fprint (pf | out, ls1es);
      fprint (pf | out, ")")
    end
  | S1Etytup (flat, s1es) => begin
      fprint (pf | out, "S1Etytup(");
      fprint (pf | out, flat);
      fprint (pf | out, "; ");
      fprint (pf | out, s1es);
      fprint (pf | out, ")")
    end
  | S1Etytup2 (flat, s1es1, s1es2) => begin
      fprint (pf | out, "S1Etytup2(");
      fprint (pf | out, flat);
      fprint (pf | out, "; ");
      fprint (pf | out, s1es1);
      fprint (pf | out, "; ");
      fprint (pf | out, s1es2);
      fprint (pf | out, ")")
    end
  | S1Euni (s1qs, s1e) => begin
      fprint (pf | out, "S1Euni(");
      fprint_s1qualst (pf | out, s1qs);
      fprint (pf | out, "; ");
      fprint (pf | out, s1e);
      fprint (pf | out, ")")
    end
  | S1Eunion (s1e, ls1es) => begin
      fprint (pf | out, "S1Eunion(");
      fprint (pf | out, s1e);
      fprint (pf | out, "; ");
      fprint (pf | out, ls1es);
      fprint (pf | out, ")")
    end

implement fprint_s1explst {m} (pf | out, s1es0) = let
  fun aux (out: &FILE m, i: int, s1es: s1explst): void =
    case+ s1es of
    | cons (s1e, s1es) => begin
        if i > 0 then fprint (pf | out, ", "); 
        fprint (pf | out, s1e); aux (out, i+1, s1es)
      end
    | nil () => ()
in
  aux (out, 0, s1es0)
end // end of [fprint_s1explst]

implement fprint_s1expopt {m} (pf | out, os1e) =
  case+ os1e of Some s1e => fprint (pf | out, s1e) | None () => ()

implement fprint_s1explstlst {m} (pf | out, s1ess0) = let
  fun aux (out: &FILE m, i: int, s1ess: s1explstlst): void =
    case+ s1ess of
    | cons (s1es, s1ess) => begin
        if i > 0 then fprint (pf | out, "; ");
        fprint (pf | out, s1es); aux (out, i+1, s1ess)
      end
    | nil () => ()
in
  aux (out, 0, s1ess0)
end // end of [fprint_s1explstlst]

(* ****** ****** *)

implement fprint_labs1explst {m} (pf | out, ls1es0) = let
  fun aux (out: &FILE m, i: int, ls1es: labs1explst): void =
    case+ ls1es of
    | LABS1EXPLSTcons (l, s1e, ls1es) => begin
        if i > 0 then fprint (pf | out, ", ");
        $Lab.fprint_label (pf | out, l); fprint (pf | out, "=");
        fprint (pf | out, s1e); aux (out, i + 1, ls1es)
      end
    | LABS1EXPLSTnil () => ()
in
  aux (out, 0, ls1es0)
end // end of [fprint_labs1explst]

(* ****** ****** *)

implement fprint_tmps1explstlst {m} (pf | out, ts1ess0) = let
  fun aux (out: &FILE m, i: int, ts1ess: tmps1explstlst): void =
    case+ ts1ess of
    | TMPS1EXPLSTLSTcons (_(*loc*), s1es, ts1ess) => begin
        if i > 0 then fprint (pf | out, "; ");
        fprint (pf | out, s1es); aux (out, i + 1, ts1ess)
      end
    | TMPS1EXPLSTLSTnil () => ()
in
  aux (out, 0, ts1ess0)
end // end of [fprint_s1explstlst]

(* ****** ****** *)

implement fprint_s1rtext (pf | out, s1te) = begin
  case+ s1te.s1rtext_node of
  | S1TEsrt s1t => fprint (pf | out, s1t)
  | S1TEsub (sym, s1te, s1es) => begin
      fprint (pf | out, "S1TEsub(");
      $Sym.fprint_symbol (pf | out, sym);
      fprint (pf | out, "; ");
      fprint (pf | out, s1te);
      fprint (pf | out, "; ");
      fprint (pf | out, s1es);
      fprint (pf | out, ")");
    end
end // end of [fprint_s1rtext]

(* ****** ****** *)

implement print_s1exp (s1e) = print_mac (fprint_s1exp, s1e)
implement prerr_s1exp (s1e) = prerr_mac (fprint_s1exp, s1e)

implement print_s1explst (s1es) = print_mac (fprint_s1explst, s1es)
implement prerr_s1explst (s1es) = prerr_mac (fprint_s1explst, s1es)

(* ****** ****** *)

(* end of [ats_staexp1_print.dats] *)
