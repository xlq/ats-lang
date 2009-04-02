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
 *)

(* ****** ****** *)

// Time: March 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

staload Deb = "ats_debug.sats"
staload Err = "ats_error.sats"
staload Lst = "ats_list.sats"
staload Set = "ats_set_fun.sats"
staload Sym = "ats_symbol.sats"
staload Syn = "ats_syntax.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_dynexp3.sats"

staload "ats_hiexp.sats"

(* ****** ****** *)

staload "ats_trans4.sats"

(* ****** ****** *)

staload "ats_reference.sats"
staload _(*anonymous*) = "ats_reference.dats"

(* ****** ****** *)

#define THISFILENAME "ats_trans4.dats"

(* ****** ****** *)

#define nil list_nil; #define cons list_cons; #define :: list_cons

(* ****** ****** *)

overload = with $Sym.eq_symbol_symbol

(* ****** ****** *)

local
  #define STRING_EMPTY ""
  val the_typedef_cnt: ref int = ref_make_elt<int> (0)
  val the_typedef_base: ref string = ref_make_elt<string> (STRING_EMPTY)
in
  fn typedef_base_set (base: string): void = (!the_typedef_base := base)
end // end of [local]

(* ****** ****** *)

fn s2exp_app_tr (
    deep: int
  , s2t_app: s2rt
  , s2e_fun: s2exp
  , s2es_arg: s2explst
  ) : hityp = let
(*
  val () = begin
    prerr "s2exp_app_tr: s2t_app = "; prerr s2t_app; prerr_newline ()
  end
  val () = begin
    prerr "s2exp_app_tr: s2e_fun = "; prerr s2e_fun; prerr_newline ()
  end
  val () = begin
    prerr "s2exp_app_tr: s2es_arg = "; prerr s2es_arg; prerr_newline ()
  end
*)
in
  case+ s2e_fun.s2exp_node of
  | S2Ecst s2c => begin case+ s2t_app of
    | _ when s2rt_is_boxed s2t_app => hityp_ptr
    | _ => begin case+ s2cst_isabs_get s2c of
      | Some (os2e) => begin case+ os2e of
        | Some s2e => begin case+ s2e.s2exp_node of
          | S2Elam (s2vs_arg, s2e_body) => let
              val sub = aux (s2vs_arg, s2es_arg) where {
                fun aux (s2vs: s2varlst, s2es: s2explst): stasub_t =
                  case+ (s2vs, s2es) of
                  | (cons (s2v, s2vs), cons (s2e, s2es)) =>
                      stasub_add (aux (s2vs, s2es), s2v, s2e)
                  | (nil _, nil _) => stasub_nil
                  | (_, _) => begin
                      prerr "Internal Error";
                      $Deb.debug_prerrf (": %s", @(THISFILENAME));
                      prerr ": s2exp_app_tr: S2Eapp: arity error";
                      prerr_newline ();
                      $Err.abort {stasub_t} ()
                    end // end [_,_]
              } // end of [where]
              val s2e_app = s2exp_subst (sub, s2e_body)
            in
              s2exp_tr (deep, s2e_app)
            end // end of [S2Elam]
          | _ => hityp_abs
          end // end of [Some]
        | None () => hityp_abs
        end // end of [case]
      | None () => hityp_abs
      end // end of [case]
    end // end of [S2Ecst]
  | _ => begin
      if s2rt_is_boxed s2t_app then hityp_ptr else hityp_abs
    end
end // end of [s2exp_app_tr]

fn s2Var_tr (deep: int, s2V: s2Var_t): hityp = begin
  case+ s2Var_lbs_get s2V of
  | cons (s2Vb, _) => s2exp_tr (deep, s2Varbound_val_get s2Vb)
  | nil () => begin case+ s2Var_ubs_get s2V of
    | cons (s2Vb, _) => s2exp_tr (deep, s2Varbound_val_get s2Vb)
    | nil () => hityp_abs
    end
end // end of [s2Var_tr]

implement s2exp_tr (deep, s2e0) = let
  val s2e0 = s2exp_whnf s2e0; val s2t0 = s2e0.s2exp_srt
(*
  val () = begin
    prerr "s2exp_tr: s2e0 = "; prerr s2e0; prerr_newline ()
  end // end of [val]
*)
in
  case+ s2e0.s2exp_node of
  | S2Eapp (s2e_fun, s2es_arg) => begin
      s2exp_app_tr (deep, s2e0.s2exp_srt, s2e_fun, s2es_arg)
    end // end of [S2Eapp]
  | S2Ecrypt s2e => s2exp_tr (deep, s2e)
  | S2Ecst s2c => begin case+ s2t0 of
    | _ when s2rt_is_boxed (s2t0) => hityp_ptr
    | _ => begin
      case+ s2cst_isabs_get s2c of
      | Some os2e => begin case+ os2e of
        | Some s2e => s2exp_tr (deep, s2e) | None () => hityp_abs
        end
      | None () => begin
          prerr "Internal Error: [ats_trans4]: ";
          prerr_newline ();
          prerr "Internal Error: s2exp_tr: s2t0 = "; prerr s2t0;
          prerr_newline ();
          prerr "Internal Error: s2exp_tr: s2e0 = "; prerr s2e0;
          prerr_newline ();
          $Err.abort {hityp} ()
        end
      end // end of [_]
    end // end of [S2Ecst]
  | S2Eclo (knd, s2exp) => begin
      if knd <> 0 then hityp_ptr (*cloptr/cloref*) else hityp_abs (*clo*)
    end // end of [S2Eclo]
  | S2Edatconptr _ => hityp_ptr
  | S2Edatcontyp (d2c, s2es) => begin
      if deep > 0 then let
        val npf = d2con_npf_get d2c; val hits_arg = s2explst_arg_tr (npf, s2es)
      in
        hityp_tysumtemp (d2c, hits_arg)
      end else begin
        hityp_ptr // deep = 0
      end // end of [if]
    end // end of [S2Edatcontyp]
  | S2Eexi (_(*s2vs*), _(*s2ps*), s2e) => s2exp_tr (deep, s2e)
  | S2Eextype name => hityp_extype name
  | S2Efun (fc, _(*lin*), _(*s2fe*), npf, s2es_arg, s2e_res) => begin
      if deep > 0 then let
        val hits_arg = s2explst_arg_tr (npf, s2es_arg)
        val hit_res = s2exp_tr (0, s2e_res)
      in
        hityp_fun (fc, hits_arg, hit_res)
      end else begin case+ fc of
        | $Syn.FUNCLOfun () => hityp_ptr // function pointer
        | $Syn.FUNCLOclo knd => if knd = 0 then begin
            hityp_clo // GCC is to report an error as [hityp_clo] is abstract
          end else begin
            if knd > 0 then hityp_clo_ptr else hityp_clo_ref (*knd = -1*)
          end // end of [FUNCLOclo]
      end // end of [if]
    end // end of [S2Efun]
  | S2Elam (_(*s2vs*), s2e_body) => s2exp_tr (deep, s2e_body)
  | S2Emetfn (_(*stamp*), _(*met*), s2e) => s2exp_tr (deep, s2e)
  | S2Enamed (name, _) => let
      val name = $Sym.symbol_name name in hityp_extype name
    end // end of [S2Enamed]
  | S2Erefarg (refval, s2e_arg) => begin
      hityp_refarg (refval, s2exp_tr (0, s2e_arg))
    end // end of [S2Erefarg]
  | S2Etop (_(*knd*), s2e) => s2exp_tr (0, s2e)
  | S2Etyarr (s2e_elt, s2ess_dim) => let
      val hit_elt = s2exp_tr (0, s2e_elt)
    in
      hityp_tyarr (hit_elt, s2ess_dim)
    end // end of [S2Etyarr]
  | S2Etyrec (knd, npf, ls2es) => let
(*
      val () = begin
        prerr "s2exp_tr: S2Etyrec: s2e0 = "; prerr s2e0; prerr_newline ()
      end // end of [val]
*)
      val lhits = labs2explst_arg_tr (npf, ls2es)
      val hit0 = (case+ knd of
        | TYRECKINDbox () => begin
            if deep > 0 then hityp_tyrectemp (1(*box*), lhits) else hityp_ptr
          end // end of [TYRECKINDbox]
        | _ (*TYRECKINDflt0 or TYRECKINDflt1*) => begin case+ lhits of
          | LABHITYPLSTcons (_(*lab*), hit, LABHITYPLSTnil ()) => hityp_tyrecsin hit
          | _ => hityp_tyrectemp (0(*flt*), lhits)
          end // end of [_]
      ) : hityp
(*
      val () = begin
        prerr "s2exp_tr: S2Etyrec: hit0 = "; prerr hit0; prerr_newline ()
      end // end of [val]
*)
    in
      hit0 
    end // end of [S2Etyrec]
  | S2Euni (_(*s2vs*), _(*s2ps*), s2e) => s2exp_tr (deep, s2e)
(*
  | S2Eunion (stamp, s2i, ls2es) => let
      val lhits = labs2explst_arg_tr (0, ls2es)
      val lnames = List.map labhityp_labname_get lhits
      val tk_uni = TYKEYuni lnames
      val name = typedef_map_find tk
    in
      hityp_union (name, lhits)
    end // end of [S2Eunion]
*)
  | S2EVar s2V => s2Var_tr (deep, s2V)
  | S2Evar s2v => hityp_s2var s2v
  | S2Evararg _ => hityp_vararg
  | S2Ewth (s2e, _(*wths2es*)) => s2exp_tr (deep, s2e)
  | _ => begin
      prerr "Internal Error: [ats_trans4]";
      prerr ": s2exp_tr: s2e0 = "; prerr s2e0; prerr_newline ();
      $Err.abort {hityp} ()
    end // end of [_]
end // end of [s2exp_tr]

fn s2explst_tr (s2es: s2explst): hityplst = begin
  $Lst.list_map_fun {s2exp,hityp}
    (s2es, lam (s2e) =<1> s2exp_tr (0(*deep*), s2e))
end // end of [s2explst_tr]

implement s2explst_arg_tr (npf, s2es): hityplst = let
  fun aux1 (s2es: s2explst): hityplst =
    case+ s2es of
    | cons (s2e, s2es) => begin
        if s2exp_is_proof s2e then aux1 s2es
        else begin
          cons (s2exp_tr (0, s2e), aux1 s2es)
        end
      end // end of [cons]
    | nil () => nil ()
  fun aux2 (i: int, s2es: s2explst): hityplst =
    if i > 0 then begin case+ s2es of
      | cons (_, s2es) => aux2 (i-1, s2es)
      | nil () => nil () // deadcode
    end else begin
      aux1 (s2es) // proof arguments have been dropped
    end // end of [if]
in
  aux2 (npf, s2es)
end

implement labs2explst_arg_tr (npf, ls2es) = let
  fun aux1 (ls2es: labs2explst): labhityplst = begin
    case+ ls2es of
    | LABS2EXPLSTcons (l, s2e, ls2es) =>
        if s2exp_is_proof s2e then begin
          aux1 ls2es
        end else begin
          LABHITYPLSTcons (l, s2exp_tr (0, s2e), aux1 ls2es)
        end
    | LABS2EXPLSTnil () => LABHITYPLSTnil ()
  end // end of [aux1]
  fun aux2 (i: int, ls2es: labs2explst): labhityplst =
    if i > 0 then begin case+ ls2es of
      | LABS2EXPLSTcons (_, _, ls2es) => aux2 (i-1, ls2es)
      | LABS2EXPLSTnil () => LABHITYPLSTnil () // deadcode
    end else begin
      aux1 ls2es // proof arguments have been dropped
    end
in
  aux2 (npf, ls2es)
end // end of [labs2explst_tr]

(* ****** ****** *)

fn hipatlst_typ_get (hips: hipatlst): hityplst =
  $Lst.list_map_fun {hipat, hityp} (hips, lam hip =<> hip.hipat_typ)

fn p3at_is_proof (p3t: p3at): bool = s2exp_is_proof (p3t.p3at_typ)

fn p3atlst_arg_tr
  (npf: int, p3ts: p3atlst): hipatlst = let
  fun aux (i: int, p3ts: p3atlst): hipatlst = case+ p3ts of
    | cons (p3t, p3ts) =>
        if i > 0 then aux (i-1, p3ts)
        else begin
          if p3at_is_proof p3t then aux (0, p3ts)
          else cons (p3at_tr p3t, aux (0, p3ts))
        end
    | nil () => nil ()
in
  aux (npf, p3ts)
end // end of [p3atlst_arg_tr]

fn labp3atlst_arg_tr
  (npf: int, lp3ts: labp3atlst): labhipatlst = let
  fun aux (i: int, lp3ts: labp3atlst): labhipatlst = begin
    case+ lp3ts of
    | LABP3ATLSTcons (l, p3t, lp3ts) =>
        if i > 0 then aux (i-1, lp3ts) else begin
          if p3at_is_proof p3t then aux (0, lp3ts)
          else begin
            LABHIPATLSTcons (l, p3at_tr p3t, aux (0, lp3ts))
          end
        end // end of [if]
    | LABP3ATLSTdot () => LABHIPATLSTdot ()
    | LABP3ATLSTnil () => LABHIPATLSTnil ()
  end // end of [aux]
in
  aux (npf, lp3ts)
end // end of [labp3atlst_arg_tr]

(* ****** ****** *)

implement p3at_tr (p3t0): hipat = let
  val loc0 = p3t0.p3at_loc
  val hit0 = s2exp_tr (0(*deep*), p3t0.p3at_typ)
(*
  val () = begin
    prerr "p3at_tr: p3t0 = "; prerr_p3at p3t0; prerr_newline ()
    prerr "p3at_tr: p3t0.p3at_typ = "; prerr_s2exp p3t0.p3at_typ; prerr_newline ();
    prerr "p3at_tr: hit0 = "; prerr_hityp hit0; prerr_newline ();
  end // end of [val]
*)
in
  case+ p3t0.p3at_node of
  | P3Tann (p3t, s2e_ann) => let
      val hip = p3at_tr p3t
      val hit_ann = s2exp_tr (0(*deep*), s2e_ann)
    in
      hipat_ann (loc0, hit0, hip, hit_ann)
    end
  | P3Tany _ => hipat_any (loc0, hit0)
  | P3Tas (refknd, d2v, p3t) => begin
      hipat_as (loc0, hit0, refknd, d2v, p3at_tr p3t)
    end
  | P3Tbool b => hipat_bool (loc0, hit0, b)
  | P3Tchar c => hipat_char (loc0, hit0, c)
  | P3Tcon (freeknd, d2c, npf, p3ts_arg) => let
      val hips_arg = p3atlst_arg_tr (npf, p3ts_arg)
      val freeknd = (case+ p3ts_arg of
        | list_cons _ => freeknd | list_nil _ => 1 (*nonfreeable*)
      ) : int
    in
      case+ 0 of
      | _ when hipatlst_is_unused hips_arg =>
          hipat_con_any (loc0, hit0, freeknd, d2c)
      | _ => let
          val hits_arg = hipatlst_typ_get (hips_arg)
(*
          val () = begin
            prerr "p3at_tr: P3Tcon: hits_arg = "; prerr hits_arg; prerr_newline ()
*)
          val hit_sum = hityp_tysumtemp (d2c, hits_arg)
(*
          val () = begin
            prerr "p3at_tr: P3Tcon: hit_sum = "; prerr hit_sum; prerr_newline ()
          end
*)
        in
          hipat_con (loc0, hit0, freeknd, d2c, hips_arg, hit_sum)
        end
    end // end of [P3Tcon]
  | P3Tempty () => hipat_empty (loc0, hit0)
  | P3Texist (_(*s2vs*), p3t) => p3at_tr p3t
  | P3Tint (str, int) => hipat_int (loc0, hit0, str, int)
  | P3Tlst (s2e_elt, p3ts_elt) => let
      val hit_elt = s2exp_tr (0(*deep*), s2e_elt)
      val hips_elt = p3atlst_tr p3ts_elt
    in
      hipat_lst (loc0, hit0, hips_elt, hit_elt)
    end // end of [P3Tlst]
  | P3Trec (knd, npf, lp3ts) => let
      val hit_rec = s2exp_tr (1(*deep*), p3t0.p3at_typ)
      val lhips = labp3atlst_arg_tr (npf, lp3ts)
    in
      hipat_rec (loc0, hit0, knd, lhips, hit_rec)
    end // end of [P3Trec]
  | P3Tstring str => hipat_string (loc0, hit0, str)
  | P3Tvar (refknd, d2v) => begin
      hipat_var (loc0, hit0, refknd, d2v)
    end
  | _ => begin
      prerr "Internal Error: [ats_trans4]";
      prerr ": p3at_tr: p3t0 = "; prerr_p3at p3t0; prerr_newline ();
      $Err.abort {hipat} ()
    end
end // end of [p3at_tr]

implement p3atlst_tr (p3ts) = $Lst.list_map_fun (p3ts, p3at_tr)

(* ****** ****** *)

fn hiexplst_typ_get (hies: hiexplst): hityplst =
  $Lst.list_map_fun {hiexp, hityp} (hies, lam hie =<> hie.hiexp_typ)

fn d3exp_is_proof (d3e: d3exp): bool = s2exp_is_proof (d3e.d3exp_typ)

viewtypedef hiexplst_vt = List_vt hiexp

extern fun d3explst_funarg_tr
  (isvararg: bool, npf: int, arg: d3explst): hiexplst

implement d3explst_funarg_tr (isvararg, npf, d3es) = let
  fun aux0
    (hies: hiexplst_vt, ld3es: labd3explst): hiexplst = begin
    case+ ld3es of
    | LABD3EXPLSTcons (_(*lab*), d3e, ld3es) => let
        val hie = d3exp_tr d3e; val hies = list_vt_cons (hie, hies)
      in
        aux0 (hies, ld3es)
      end
    | LABD3EXPLSTnil () => $Lst.list_vt_reverse_list (hies)
  end // end of [aux0]
  fun aux1 (hies: hiexplst_vt, d3e: d3exp, d3es: d3explst)
    :<cloptr1> hiexplst = begin case+ d3es of
    | cons (d3e1, d3es1) => let
        val hie = d3exp_tr d3e; val hies = list_vt_cons (hie, hies)
      in
        aux1 (hies, d3e1, d3es1)
      end
    | nil () => begin
        if isvararg then begin case+ d3e.d3exp_node of
          | D3Erec (_, _, ld3es) => aux0 (hies, ld3es)
          | _ => begin
            $Lst.list_vt_free__boxed (hies);
            prerr "Internal Error: [ats_trans4]";
            prerr ": d3explst_funarg_tr: aux1: d3e = "; prerr_d3exp d3e;
            prerr_newline ();
            $Err.abort {hiexplst} ()
          end
        end else let
          val hie = d3exp_tr d3e; val hies = list_vt_cons (hie, hies)
        in
          $Lst.list_vt_reverse_list (hies)
        end
      end // end of [nil ()]
  end // end of [aux1]
  fun aux2 (i: int, d3es: d3explst)
    :<cloptr1> hiexplst = begin case+ d3es of
    | cons (d3e, d3es) => begin
        if i > 0 then aux2 (i-1, d3es) else aux1 (list_vt_nil (), d3e, d3es)
      end
    | nil () => nil ()
  end // end of [aux2]
in
  aux2 (npf, d3es)
end // end of [d3explst_funarg_tr]

fn d3explst_arg_tr
  (npf: int, d3es: d3explst): hiexplst = let
  fun aux (i: int, d3es: d3explst): hiexplst = begin
    case+ d3es of
    | cons (d3e, d3es) => begin case+ i of
      | _ when i > 0 => aux (i-1, d3es)
      | _ => begin
          if d3exp_is_proof d3e then begin
            aux (i-1, d3es)
          end else begin
            cons (d3exp_tr d3e, aux (i-1, d3es))
          end
        end // end of [_]
      end // end of [cons]
    | nil () => nil ()
  end // end of [aux]
in
  aux (npf, d3es)
end // end of [d3explst_arg_tr]

fn labd3explst_arg_tr
  (npf: int, ld3es: labd3explst): labhiexplst = let
  fun aux (i: int, ld3es: labd3explst): labhiexplst = begin
    case+ ld3es of
    | LABD3EXPLSTcons (l, d3e, ld3es) => begin case+ i of
      | _ when i > 0 => aux (i-1, ld3es)
      | _ => begin
          if d3exp_is_proof d3e then begin
            aux (i-1, ld3es)
          end else begin
            LABHIEXPLSTcons (l, d3exp_tr d3e, aux (i-1, ld3es))
          end
        end
      end // end of [LABHIEXPLSTcons]
    | LABD3EXPLSTnil () => LABHIEXPLSTnil ()
  end // end of [aux]
in
  aux (npf, ld3es)
end // end of [labd3explst_arg_tr]

(* ****** ****** *)

fn d3exp_cst_tr
  (loc0: loc_t, hit0: hityp, d2c: d2cst_t): hiexp = let
  val sym = d2cst_sym_get d2c
in
  case+ sym of
  | _ when sym = $Sym.symbol_TRUE => hiexp_bool (loc0, hit0, true)
  | _ when sym = $Sym.symbol_FALSE => hiexp_bool (loc0, hit0, false)
  | _ => hiexp_cst (loc0, hit0, d2c)
end // end of [d3exp_cst_tr]

fn d3exp_seq_tr
  (loc0: loc_t, hit0: hityp, d3es: d3explst): hiexp = let
  val hies = d3explst_tr d3es
in
  hiexp_seq_simplify (loc0, hit0, hies)
end // end of [d3exp_seq_tr]

//

and d3exp_tmpcst_tr
  (loc0: loc_t, hit0: hityp, d2c: d2cst_t, s2ess: s2explstlst)
  : hiexp = let
  val sym = d2cst_sym_get d2c
in
  case+ sym of
  | _ when sym = $Sym.symbol_SIZEOF => begin case+ s2ess of
    | cons (cons (s2e, nil ()), nil ()) => begin
        hiexp_sizeof (loc0, hit0, s2exp_tr (0(*deep*), s2e))
      end
    | _ => begin
        prerr "Internal Error: [ats_trans4]";
        prerr ": d3exp_tmpcst_tr: sizeof"; prerr_newline ();
        $Err.abort {hiexp} ()
      end
    end
  | _ => let
      val hitss = $Lst.list_map_fun (s2ess, s2explst_tr)
(*
      val () = begin
        prerr "d3exp_tmpcst_tr: hitss = "; prerr hitss; prerr_newline ()
      end
*)
    in
      hiexp_tmpcst (loc0, hit0, d2c, hitss)
    end
end // end of [d3exp_tmpcst_tr]

fn d3exp_tmpvar_tr
  (loc0: loc_t, hit0: hityp, d2v: d2var_t, s2ess: s2explstlst)
  : hiexp = let
  val hitss = $Lst.list_map_fun (s2ess, s2explst_tr)
in
  hiexp_tmpvar (loc0, hit0, d2v, hitss)
end // end of [d3exp_tmpvar_tr]

//

fn d3lab1_tr (d3l: d3lab1): hilab = begin
  case+ d3l.d3lab1_node of
  | D3LAB1lab (l, s2e_rec) => let
      val hit_rec = s2exp_tr (1(*deep*), s2e_rec)
    in
      hilab_lab (d3l.d3lab1_loc, l, hit_rec)
    end
  | D3LAB1ind (d3ess, s2e_elt) => let
      val hiess: hiexplstlst = $Lst.list_map_fun (d3ess, d3explst_tr)
      val hit_elt = s2exp_tr (0(*deep*), s2e_elt)
    in
      hilab_ind (d3l.d3lab1_loc, hiess, hit_elt)
    end
end // end of [d3lab1_tr]

fn d3lab1lst_tr (d3ls: d3lab1lst): hilablst =
  $Lst.list_map_fun (d3ls, d3lab1_tr)

//

fn m3atch_tr (m3at: m3atch): himat = let
  val hie = d3exp_tr m3at.m3atch_exp
  val ohip = (
    case+ m3at.m3atch_pat of
    | Some p3t => Some (p3at_tr p3t) | None () => None ()
  ) : hipatopt
in
  himat_make (m3at.m3atch_loc, hie, ohip)
end // end of [m3atch_tr]

fn m3atchlst_tr (m3ats: m3atchlst): himatlst =
  $Lst.list_map_fun (m3ats, m3atch_tr)

//

fn c3lau_tr (c3l: c3lau): hiclau = let
  val loc0 = c3l.c3lau_loc
(*
  val () = begin
    prerr "cla3_tr: c3l = "; prerr c3l; prerr_newline ()
  end
*)
  val hips = p3atlst_tr c3l.c3lau_pat
(*
  val () = begin
    prerr "cla3_tr: hips = "; prerr hips; prerr_newline ()
  end
*)
  val gua = m3atchlst_tr c3l.c3lau_gua
  val body = d3exp_tr c3l.c3lau_exp
in
  hiclau_make (loc0, hips, gua, body)
end // end of [c3lau_tr]

fn c3laulst_tr (c3ls: c3laulst): hiclaulst = let
  fun aux // tail-recursive function
    (c3ls: c3laulst, res: &hiclaulst? >> hiclaulst)
    : void = begin case+ c3ls of
    | cons (c3l, c3ls) => begin case+ 0 of
      | _ when c3l.c3lau_neg > 0 => aux (c3ls, res)
      | _ => let
          val hicl = c3lau_tr c3l
          val () = (res := cons {hiclau} {0} (hicl, ?))
          val+ cons (_, !res_nxt) = res
        in
          aux (c3ls, !res_nxt); fold@ (res)
        end
      end
    | nil () => (res := nil ())
  end // end of [aux]
  var res: c3laulst // uninitialized
  val () = aux (c3ls, res)
in
  res
end // end of [c3laulst_tr]

(* ****** ****** *)

absview dyncstsetlst_push_token
extern fun the_dyncstset_get (): dyncstset_t
  = "ats_ccomp_env_the_dyncstset_get"
extern fun the_dyncstsetlst_push (): (dyncstsetlst_push_token | void)
  = "ats_ccomp_env_the_dyncstsetlst_push"
extern fun the_dyncstsetlst_pop (pf: dyncstsetlst_push_token | (*none*)): dyncstset_t
  = "ats_ccomp_env_the_dyncstsetlst_pop"
extern fun // this function is implemented in [ats_ccomp_env.dats]
  the_dyncstset_add_if (d2c: d2cst_t): void = "ats_ccomp_env_the_dyncstset_add_if"

(* ****** ****** *)

implement d3exp_tr (d3e0) = let
  val loc0 = d3e0.d3exp_loc
  val s2e0 = d3e0.d3exp_typ
(*
  val () = begin
    prerr "d3exp_tr: s2e0 = " prerr s2e0; prerr_newline ();
    prerr "d3exp_tr: d3e0 = " prerr d3e0; prerr_newline ();
  end // end of [val]
*)
in
  case+ d3e0.d3exp_node of
  | D3Eann_type (d3e, _) => d3exp_tr d3e
  | D3Eapp_dyn (d3e_fun, npf, d3es_arg) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hit_fun = s2exp_tr (1(*deep*), d3e_fun.d3exp_typ)
      val hie_fun = d3exp_tr d3e_fun
      val isvararg = hityp_fun_is_vararg hit_fun
      val hies_arg = d3explst_funarg_tr (isvararg, npf, d3es_arg)
    in
      case+ hie_fun.hiexp_node of
      | HIEcst d2c when d2cst_is_castfn d2c => let
          val hie = case+ hies_arg of
          | list_cons (hie, list_nil ()) => hie | _ => begin
              $Loc.prerr_location loc0; prerr ": Internal Error";
              prerr ": a casting function must be applied to exactly one argument.";
              prerr_newline (); $Err.abort {hiexp} ()
            end // end of [list_cons]
          // end of [val]
        in
          hiexp_castfn (loc0, hit0, d2c, hie)
        end // end of [HIEcst]
      | _ => hiexp_app (loc0, hit0, hit_fun, hie_fun, hies_arg)
    end // end of [D3Eapp_dyn]
  | D3Eapp_sta d3e => d3exp_tr d3e
  | D3Earrinit (s2e_elt, od3e_asz, d3es_elt) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hit_elt = s2exp_tr (0(*deep*), s2e_elt)
      val ohie_asz = d3expopt_tr od3e_asz
      val hies_elt = d3explst_tr d3es_elt
    in
      hiexp_arrinit (loc0, hit0, hit_elt, ohie_asz, hies_elt)
    end // end of [D3Earrinit]
  | D3Earrsize (s2e_elt, d3es_elt) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hit_elt = s2exp_tr (0(*deep*), s2e_elt)
      val hies_elt = d3explst_tr d3es_elt
    in
      hiexp_arrsize (loc0, hit0, hit_elt, hies_elt)
    end // end of [D3Earrsize]
  | D3Eassgn_ptr (d3e_ptr, d3ls, d3e_val) => begin
      if d3exp_is_proof d3e_val then begin
        hiexp_empty (loc0, hityp_void)
      end else let
        val hie_ptr = d3exp_tr d3e_ptr
        val hils = d3lab1lst_tr (d3ls)
        val hie_val = d3exp_tr d3e_val
      in
        hiexp_assgn_ptr (loc0, hityp_void, hie_ptr, hils, hie_val)
      end
    end // end of [D3Eassgn_ptr]
  | D3Eassgn_var (d2v_ptr, d3ls, d3e_val) => begin
      if d3exp_is_proof d3e_val then
        hiexp_empty (loc0, hityp_void)
      else let
        val () = d2var_count_inc d2v_ptr
        val hils = d3lab1lst_tr (d3ls)
        val hie_val = d3exp_tr d3e_val
      in
        hiexp_assgn_var (loc0, hityp_void, d2v_ptr, hils, hie_val)
      end
    end // end of [D3Eassgn_var]
  | D3Ecaseof (knd, d3es, c3ls) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hies = d3explst_tr d3es
(*
      val () = begin
        prerr "d3exp_tr: D2Ecase: c3ls = "; prerr c3ls; prerr_newline ()
      end
*)
      val hicls = c3laulst_tr c3ls
    in
      hiexp_caseof_if (loc0, hit0, knd, hies, hicls)
    end // end of [D3Ecase]
  | D3Echar c => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_char (loc0, hit0, c)
    end // end of [D3Echar]
  | D3Econ (d2c, npf, d3es_arg) => let
(*
      val () = begin
        prerr "d3exp_tr: d2c = "; prerr d2c; prerr_newline ();
        prerr "d3exp_tr: npf = "; prerr npf; prerr_newline ();
        prerr "d3exp_tr: d3es_arg = "; prerr d3es_arg; prerr_newline ()
      end
*)
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hies_arg = d3explst_arg_tr (npf, d3es_arg)
(*
      val () = begin
        prerr "d3exp_tr: hies_arg = "; prerr hies_arg; prerr_newline ()
      end
*)
      val hits_arg = hiexplst_typ_get hies_arg
      val hit_sum = hityp_tysumtemp (d2c, hits_arg)
    in
      hiexp_con (loc0, hit0, hit_sum, d2c, hies_arg)
    end // end of [D2Econ]
  | D3Ecst d2c => let (* d2c is external as it is used *)
      val () = the_dyncstset_add_if (d2c)
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      d3exp_cst_tr (loc0, hit0, d2c)
    end // end of [D3Ecst]
  | D3Ecrypt (_(*knd*), d3e) => d3exp_tr d3e
  | D3Edynload fil => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_dynload (loc0, hit0, fil)
    end // end of [D3Edynload]
  | D3Eeffmask (_, d3e) => d3exp_tr d3e
  | D3Eempty () => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_empty (loc0, hit0)
    end // end of [D3Eempty]
  | D3Eextval code => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_extval (loc0, hit0, code)
    end // end of [D3Eextval]
  | D3Efix (d2v_fun, d3e_body) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hie_body = d3exp_tr d3e_body
      val () = // check for valueness of the body
        if hiexp_is_value hie_body then () else begin
          $Loc.prerr_location loc0; prerr ": error(4)";
          prerr ": a non-value fixed-point dynamic expression is not supported.";
          prerr_newline ();
          $Err.abort {void} ()
        end
    in
      hiexp_fix (loc0, hit0, d2v_fun, hie_body)
    end // end of [D3Efix]
  | D3Efloat str => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_float (loc0, hit0, str)
    end // end of [D3Efloat]
  | D3Efloatsp str => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_floatsp (loc0, hit0, str)
    end // end of [D3Efloatsp]
  | D3Efoldat _ => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_empty (loc0, hit0)
    end // end of [D3Efoldat]
  | D3Efreeat d3e => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_freeat (loc0, hit0, d3exp_tr d3e)
    end // end of [D3Efreeat]
  | D3Eif (d3e_cond, d3e_then, d3e_else) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hie_cond = d3exp_tr d3e_cond
      val hie_then = d3exp_tr d3e_then
      val hie_else = d3exp_tr d3e_else
    in
      hiexp_if (loc0, hit0, hie_cond, hie_then, hie_else)
    end // end of [D3Eif]
  | D3Eint (str, int) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_int (loc0, hit0, str, int)
    end // end of [D3Eint]
  | D3Eintsp (str, int) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_intsp (loc0, hit0, str, int)
    end // end of [D3Eintsp]
  | D3Elam_dyn (lin, npf, p3ts_arg, d3e_body) => let
      val hit_fun = s2exp_tr (1(*deep*), s2e0)
      val hips_arg = p3atlst_arg_tr (npf, p3ts_arg)
      val hie_body = d3exp_tr d3e_body
    in
      hiexp_lam (loc0, hit_fun, hips_arg, hie_body)
    end // end of [D3Elam_dyn]
  | D3Elaminit_dyn (lin, npf, p3ts_arg, d3e_body) => let
      val hit_fun = s2exp_tr (1(*deep*), s2e0)
      val hips_arg = p3atlst_arg_tr (npf, p3ts_arg)
      val hie_body = d3exp_tr d3e_body
    in
      hiexp_laminit (loc0, hit_fun, hips_arg, hie_body)
    end // end of [D3Elaminit_dyn]
  | D3Elam_sta (_(*s2vs*), _(*s2ps*), d3e_body) => let
      val hie_body = d3exp_tr d3e_body
      val () = // check for valueness
        if hiexp_is_value hie_body then () else begin
          $Loc.prerr_location loc0; prerr ": error(4)";
          prerr ": a non-value body for static lambda-abstraction is not supported.";
          prerr_newline ();
          $Err.abort {void} ()
        end // end of [if]
    in
      hie_body
    end // end of [D3Elam_sta]
  | D3Elam_met (_(*s2es_met*), d3e) => d3exp_tr d3e
  | D3Elazy_delay (d3e_eval) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_lazy_delay (loc0, hit0, d3exp_tr d3e_eval)
    end // end of [D3Elazy_delay]
  | D3Elazy_vt_delay (d3e_eval, d3e_free) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hie_eval = d3exp_tr d3e_eval and hie_free = d3exp_tr d3e_free
    in
      hiexp_lazy_vt_delay (loc0, hit0, hie_eval, hie_free)
    end // end of [D3Elazy_delay]
  | D3Elazy_force (lin, d3e_lazy) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_lazy_force (loc0, hit0, lin, d3exp_tr d3e_lazy)
    end // end of [D3Elazy_force]
  | D3Elet (d3cs, d3e) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hids = d3eclst_tr d3cs; val hie = d3exp_tr d3e
    in
      hiexp_let_simplify (loc0, hit0, hids, hie)
    end // end of [D3Elet]
  | D3Eloop (init, test, post, body) => let
      val init = d3expopt_tr init
      val test = d3exp_tr test
      val post = d3expopt_tr post
      val body = d3exp_tr body
    in
      hiexp_loop (loc0, hityp_void, init, test, post, body)
    end // end of [D3Eloop]
  | D3Eloopexn i => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_loopexn (loc0, hit0, i)
    end // end of [D3Eloopexn]
  | D3Elst (lin, s2e_elt, d3es_elt) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hit_elt = s2exp_tr (0(*deep*), s2e_elt)
      val hies_elt = d3explst_tr d3es_elt
    in
      hiexp_lst (loc0, hit0, lin, hit_elt, hies_elt)
    end // end of [D3Elst]
  | D3Emod _ => begin
      $Loc.prerr_location loc0;
      prerr ": d3exp_tr: D2Emod: not implemented yet.";
      prerr_newline ();
      $Err.abort {hiexp} ()
    end // end of [D3Emod]
  | D3Eptrof_ptr (d3e, d3ls) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hie = d3exp_tr d3e; val hils = d3lab1lst_tr d3ls
    in
      hiexp_ptrof_ptr (loc0, hit0, hie, hils)
    end // end of [D3Eptrof_ptr]
  | D3Eptrof_var (d2v, d3ls) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val () = d2var_count_inc d2v; val hils = d3lab1lst_tr d3ls
    in
      hiexp_ptrof_var (loc0, hit0, d2v, hils)
    end // end of [D3Eptrof_var]
  | D3Eraise d3e_exn => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_raise (loc0, hit0, d3exp_tr d3e_exn)
    end // end of [D3Eraise]
  | D3Erec (knd, npf, ld3es) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hit_rec = s2exp_tr (1(*deep*), s2e0)
      val lhies = labd3explst_arg_tr (npf, ld3es)
    in
      hiexp_rec (loc0, hit0, knd, hit_rec, lhies)
    end // end of [D3Erec]
  | D3Erefarg (refval, freeknd, d3e) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hie = d3exp_tr d3e
    in
      hiexp_refarg (loc0, hit0, refval, freeknd, hie)
    end // end of [D3Erefarg]
  | D3Escaseof _ => begin
      $Loc.prerr_location loc0; prerr ": Internal Error";
      prerr ": the static caseof-expression should have already been erased.";
      prerr_newline ();
      $Err.abort {hiexp} ()
    end // end of [D3Escaseof]
  | D3Esel (d3e, d3ls) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hie = d3exp_tr d3e
      val hils = d3lab1lst_tr d3ls
    in
      hiexp_sel (loc0, hit0, hie, hils)
    end // end of [D3Esel]
  | D3Esel_ptr (d3e_ptr, d3ls) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hie_ptr = d3exp_tr d3e_ptr
      val hils = d3lab1lst_tr d3ls
    in
      hiexp_sel_ptr (loc0, hit0, hie_ptr, hils)
    end // end of [D3Esel_ptr]
  | D3Esel_var (d2v_ptr, d3ls) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val () = d2var_count_inc d2v_ptr
      val hils = d3lab1lst_tr d3ls
    in
      hiexp_sel_var (loc0, hit0, d2v_ptr, hils)
    end // end of [D3Esel_var]
  | D3Eseq d3es => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      d3exp_seq_tr (loc0, hit0, d3es)
    end // end of [D3Eseq]
  | D3Esif (_(*cond*), d3e_then, d3e_else) => let
      val hie_then = d3exp_tr d3e_then
      and hie_else = d3exp_tr d3e_else
    in
      hiexp_sif (loc0, hityp_void, hie_then, hie_else)
    end // end of [D3Esif]
  | D3Espawn (d3e) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hie = d3exp_tr d3e
    in
      hiexp_spawn (loc0, hit0, hie)
    end // end of [D3Espawn]
  | D3Estring (str, len) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_string (loc0, hit0, str, len)
    end // end of [D3Estring]
  | D3Estruct ld3es => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hit_rec = s2exp_tr (1(*deep*), s2e0)
      val lhies = labd3explst_arg_tr (0, ld3es)
    in
      hiexp_rec (loc0, hit0, 0(*@{}*), hit_rec, lhies)
    end // end of [D3Estruct]
  | D3Etmpcst (d2c, s2ess) => let
      val hit_fun = s2exp_tr (1(*deep*), s2e0)
    in
      d3exp_tmpcst_tr (loc0, hit_fun, d2c, s2ess)
    end // end of [D3Etmpcst]
  | D3Etmpvar (d2v, s2ess) => let
      val hit_fun = s2exp_tr (1(*deep*), s2e0)
    in
      d3exp_tmpvar_tr (loc0, hit_fun, d2v, s2ess)
    end // end of [D3Etmpvar]
  | D3Etop () => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      hiexp_top (loc0, hit0)
    end // end of [D3Etop]
  | D3Etrywith (d3e, c3ls) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hie = d3exp_tr d3e; val hicls = c3laulst_tr c3ls
    in
      hiexp_trywith (loc0, hit0, hie, hicls)
    end // end of [D3Etrywith]
  | D3Evar d2v => let
      val () =  if d2var_isprf_get d2v then begin
        $Loc.prerr_location loc0; prerr ": error(4)";
        prerr ": the dynamic variable ["; prerr_d2var d2v;
        prerr "] refers to a proof and thus should have been erased.";
        prerr_newline ();
        $Err.abort {void} ()
      end // end of [val]
      val hit0 = s2exp_tr (0(*deep*), s2e0)
    in
      d2var_count_inc d2v; hiexp_var (loc0, hit0, d2v)
    end // end of [D3Evar]
  | D3Eviewat_assgn_ptr _ => hiexp_empty (loc0, hityp_void)
  | D3Eviewat_assgn_var _ => hiexp_empty (loc0, hityp_void)
  | D3Eviewat_ptr _ => begin
      $Loc.prerr_location loc0; prerr ": Internal Error";
      prerr ": this proof expression should have already been erased.";
      prerr_newline ();
      $Err.abort {hiexp} ()
    end // end of [D3Eviewat_ptr]
  | D3Eviewat_var _ => begin
      $Loc.prerr_location loc0; prerr ": Internal Error";
      prerr ": this proof expression should have already been erased.";
      prerr_newline ();
      $Err.abort {hiexp} ()
    end // end of [D3Eviewat_var]
  | D3Ewhere (d3e, d3cs) => let
      val hit0 = s2exp_tr (0(*deep*), s2e0)
      val hids = d3eclst_tr d3cs; val hie = d3exp_tr d3e
    in
      hiexp_let_simplify (loc0, hit0, hids, hie)
    end // end of [D3Ewhere]
end // end of [d3exp_tr]

implement d3explst_tr (d3es) = $Lst.list_map_fun (d3es, d3exp_tr)

implement d3expopt_tr (od3e) = begin case+ od3e of
  | Some d3e => Some (d3exp_tr d3e) | None () => None ()
end // end of [d3expopt_tr]

(* ****** ****** *)

fun labd3explst_prf_tr (ld3es: labd3explst): void =
  case+ ld3es of
  | LABD3EXPLSTcons (l, d3e, ld3es) => begin
      d3exp_prf_tr d3e; labd3explst_prf_tr ld3es
    end // end of [LABD3EXPLSTcons]
  | LABD3EXPLSTnil () => ()
// end of [labd3explst_prf_tr]

fn c3laulst_prf_tr (c3ls: c3laulst): void = let
  fn f (c3l: c3lau): void = d3exp_prf_tr (c3l.c3lau_exp)
in
  $Lst.list_foreach_fun (c3ls,  f)
end // end of [c3laulst_prf_tr]

implement d3exp_prf_tr (d3e0) = let
(*
  val () = begin
    prerr "d3exp_prf_tr: d3e0 = " prerr d3e0; prerr_newline ();
  end // end of [val]
*)
in
  case+ d3e0.d3exp_node of
  | D3Eann_type (d3e, _) => d3exp_prf_tr d3e
  | D3Eapp_dyn (d3e_fun, npf, d3es_arg) => let
      val () = d3exp_prf_tr d3e_fun
      val () = d3explst_prf_tr d3es_arg
    in
      // empty
    end // end of [D3Eapp_dyn]
  | D3Eapp_sta d3e => d3exp_prf_tr d3e
  | D3Eassgn_ptr (d3e_ptr, d3ls, d3e_val) => let
      val () = d3exp_prf_tr d3e_ptr
      // val () = d3lab1lst_prf_tr (d3ls) // is this really needed?
      val () = d3exp_prf_tr d3e_val
    in
      // empty
    end // end of [D3Eassgn_ptr]
  | D3Eassgn_var (d2v_ptr, d3ls, d3e_val) => let
      // val hils = d3lab1lst_prf_tr (d3ls) // is this really needed?
      val hie_val = d3exp_prf_tr d3e_val
    in
      // empty
    end // end of [D3Eassgn_var]
  | D3Ecaseof (knd, d3es, c3ls) => let
      val () = d3explst_prf_tr d3es
      val () = c3laulst_prf_tr c3ls
    in
      // empty
    end // end of [D3Ecase]
  | D3Echar c => ()
  | D3Econ (d2c, npf, d3es_arg) => let
      val () = d3explst_prf_tr (d3es_arg)
    in
      // empty
    end // end of [D2Econ]
  | D3Ecst d2c => let (* d2c is external as it is used *)
      val () = the_dyncstset_add_if (d2c)
    in
      // empty
    end // end of [D3Ecst]
  | D3Ecrypt (_(*knd*), d3e) => d3exp_prf_tr d3e
  | D3Eeffmask (_, d3e) => d3exp_prf_tr d3e
  | D3Eempty () => ()
  | D3Eextval _(*code*) => ()
  | D3Efix (d2v_fun, d3e_body) => d3exp_prf_tr d3e_body
(*
  | D3Efloat _(*str*) => ()
  | D3Efloatsp _(*str*) => ()
*)
  | D3Efoldat d3e => d3exp_prf_tr d3e
(*
  | D3Efreeat _ => ()
*)
  | D3Eif (d3e_cond, d3e_then, d3e_else) => let
      val () = d3exp_prf_tr d3e_cond
      val () = d3exp_prf_tr d3e_then
      val () = d3exp_prf_tr d3e_else
    in
      // empty
    end // end of [D3Eif]
  | D3Eint _ => ()
  | D3Elam_dyn (_, _, _(*arg*), d3e_body) => d3exp_prf_tr d3e_body
  | D3Elam_sta (_(*s2vs*), _(*s2ps*), d3e_body) => d3exp_prf_tr d3e_body
  | D3Elam_met (_(*s2es_met*), d3e) => d3exp_prf_tr d3e
  | D3Elet (d3cs, d3e) => let
      val () = d3eclst_prf_tr d3cs; val () = d3exp_prf_tr d3e
    in
      // empty
    end // end of [D3Elet]
  | D3Elst (_(*lin*), _(*s2e*), d3es_elt) => let
      val () = d3explst_prf_tr d3es_elt
    in
      // empty
    end // end of [D3Elst]
  | D3Erec (_(*knd*), _(*npf*), ld3es) => labd3explst_prf_tr ld3es
  | D3Erefarg _ => ()
  | D3Escaseof (_(*s2e*), sc3ls) => $Lst.list_foreach_fun (sc3ls, f) where {
      fn f (sc3l: sc3lau): void = d3exp_prf_tr (sc3l.sc3lau_exp)
    } // end of [D3Escaseof]
  | D3Esel (d3e, d3ls) => d3exp_prf_tr d3e
  | D3Esel_ptr (d3e_ptr, d3ls) => d3exp_prf_tr d3e_ptr
  | D3Esel_var (d2v_ptr, d3ls) => ()
  | D3Eseq d3es => d3explst_prf_tr d3es
  | D3Esif (_(*cond*), d3e_then, d3e_else) => let
      val () = d3exp_prf_tr d3e_then
      and () = d3exp_prf_tr d3e_else
    in
      // empty
    end // end of [D3Esif]
  | D3Estring _ => ()
  | D3Estruct ld3es => labd3explst_prf_tr ld3es
  | D3Evar _ => ()
  | D3Eviewat_assgn_ptr (d3e_ptr, d3ls, d3e_val) => let
      val () = d3exp_prf_tr d3e_ptr
      // val () = d3lablst_prf_tr (d3ls) // is this really needed?
      val () = d3exp_prf_tr d3e_val
    in
      // empty
    end // end of [D3Eviewat_assgn_ptr]
  | D3Eviewat_assgn_var (d2v_ptr, d3ls, d3e_val) => let
      // val () = d3lablst_prf_tr (d3ls) // is this really needed?
      val () = d3exp_prf_tr d3e_val
    in
      // empty
    end // end of [D3Eviewat_assgn_var]
  | D3Eviewat_ptr (d3e_ptr, d3ls, _, _) => let
      val () = d3exp_prf_tr d3e_ptr
      // val () = d3lablst_prf_tr (d3ls) // is this really needed?
    in
      // empty
    end // end of [D3Eviewat_ptr]
  | D3Eviewat_var (d2v_ptr, d3ls, _, _) => let
      // val () = d3lablst_prf_tr (d3ls) // is this really needed?
    in
      // empty
    end // end of [D3Eviewat_var]
  | D3Ewhere (d3e, d3cs) => let
      val () = d3eclst_prf_tr d3cs; val () = d3exp_prf_tr d3e
    in
      // empty
    end // end of [D3Ewhere]
  | _ => begin
      $Loc.prerr_location d3e0.d3exp_loc; prerr ": Internal Error";
      prerr ": d3exp_prf_tr: d3e0 = "; prerr_d3exp d3e0; prerr_newline ();
      $Err.abort {void} ()
    end // end of [_]
end // end of [d3exp_prf_tr]

implement d3explst_prf_tr (d3es) = $Lst.list_foreach_fun (d3es, d3exp_prf_tr)

(* ****** ****** *)

fn f3undec_tr (decarg: s2qualst, d3c: f3undec): hifundec = let
  val loc = d3c.f3undec_loc
  val d2v_fun = d3c.f3undec_var
  val hie_def = d3exp_tr d3c.f3undec_def
  val () = begin case+ decarg of
    | list_cons _ => begin
        tmpvarmap_add (d2v_fun, decarg, hie_def) // template function
      end
    | list_nil () => ()
  end // end of [val]
(*
  val () = begin
    prerr "f3undec_tr: d2v_fun = "; prerr d2v_fun; prerr_newline ();
    prerr "f3undec_tr: hie_def = "; prerr hie_def; prerr_newline ();
  end
*)
in
  hifundec_make (loc, d2v_fun, hie_def)
end // end of [f3undec_tr]

fn f3undeclst_tr
  (decarg: s2qualst, d3cs: f3undeclst): hifundeclst =
  $Lst.list_map_cloptr (
     d3cs, lam d3c =<cloptr1> f3undec_tr (decarg, d3c)
  )

fun f3undeclst_prf_tr
  (fundecs: f3undeclst): void = case+ fundecs of
  | list_cons (fundec, fundecs) => begin
      d3exp_prf_tr (fundec.f3undec_def); f3undeclst_prf_tr fundecs
    end // end of [list_cons]
  | list_nil () => ()
// end of [f3undeclst_prf_tr]

(* ****** ****** *)

fn v3aldec_tr (d3c: v3aldec): hivaldec = let
  val loc = d3c.v3aldec_loc
  val hip = p3at_tr d3c.v3aldec_pat
  val hie = d3exp_tr d3c.v3aldec_def
in
  hivaldec_make (loc, hip, hie)
end // end of [v3aldec_tr]

fn v3aldeclst_tr (d3cs: v3aldeclst): hivaldeclst =
  $Lst.list_map_fun (d3cs, v3aldec_tr)

fn v3ardec_tr (d3c: v3ardec): hivardec = let
  val loc = d3c.v3ardec_loc
  val knd = d3c.v3ardec_knd
  val d2v_ptr = d3c.v3ardec_dvar_ptr
  val ini = (
    case+ d3c.v3ardec_ini of
    | Some d3e => Some (d3exp_tr d3e) | None () => None ()
  ) : hiexpopt
in
  hivardec_make (loc, knd, d2v_ptr, ini)
end // end of [v3ardec_tr]

fn v3ardeclst_tr (d3cs: v3ardeclst): hivardeclst =
  $Lst.list_map_fun (d3cs, v3ardec_tr)

fun v3aldeclst_prf_tr
  (valdecs: v3aldeclst): void = case+ valdecs of
  | list_cons (valdec, valdecs) => begin
      d3exp_prf_tr (valdec.v3aldec_def); v3aldeclst_prf_tr valdecs
    end // end of [list_cons]
  | list_nil () => ()
// end of [v3aldeclst_prf_tr]

(* ****** ****** *)

fn i3mpdec_tr (d3c: i3mpdec): hiimpdec = let
  val loc = d3c.i3mpdec_loc
  val d2c = d3c.i3mpdec_cst
  val decarg = d3c.i3mpdec_decarg
  val tmp = (case+ decarg of cons _ => 1 | nil _ => 0): int
  val tmparg = $Lst.list_map_fun (d3c.i3mpdec_tmparg, s2explst_tr)
  val def = d3exp_tr d3c.i3mpdec_def
  val () = begin case+ 0 of
    | _ when d2cst_is_fun d2c => begin
      case+ def.hiexp_node of
      | HIElam _ => () | _ => begin
          $Loc.prerr_location loc;
          prerr ": error(4)";
          prerr ": the dynamic constant [";
          prerr d2c;
          prerr "] is required to be implemented as a function";
          prerr ", but it is not.";
          prerr_newline ();
          $Err.abort {void} ()
        end // end of [_]
      end // end of [_ when ...]
    | _ => ()
  end : void // end of [val]
  val () = if tmp > 0 then tmpcstmap_add (d2c, decarg, def)
  val d2cs = the_dyncstset_get ()
in
  hiimpdec_make (loc, d2c, tmp, decarg, tmparg, def, d2cs)
end // end of [i3mpdec_tr]

(* ****** ****** *)

implement d3eclst_tr (d3cs0: d3eclst): hideclst = let
  // [aux0] and [aux1] are mutually tail-recursive
  fn* aux0 (d3cs: d3eclst, res: &hideclst? >> hideclst)
    : void = begin case+ d3cs of
    | cons (d3c, d3cs) => begin case+ d3c.d3ec_node of
      | D3Cnone () => aux0 (d3cs, res)
      | D3Clist d3cs1 => let
          val hid = hidec_list (d3c.d3ec_loc, d3eclst_tr d3cs1)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Clist]
      | D3Csaspdec saspdec => let
          val hid = hidec_saspdec (d3c.d3ec_loc, saspdec)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Csaspdec]
      | D3Cextype (name, s2e_def) => let
          val hit_def = s2exp_tr (1(*deep*), s2e_def)
          val hid = hidec_extype (d3c.d3ec_loc, name, hit_def)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Cextype]
      | D3Cextval (name, d3e_def) => let
          val hie_def = d3exp_tr d3e_def
          val hid = hidec_extval (d3c.d3ec_loc, name, hie_def)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Cextval]
      | D3Cextcode (position(*int*), code) => let
          val hid = hidec_extern (d3c.d3ec_loc, position, code)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Cextcode]
      | D3Cdatdec (knd, s2cs) => let
          val hid = hidec_datdec (d3c.d3ec_loc, knd, s2cs)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Cdatdec]
      | D3Cexndec d3cs1 => let
          val hid = hidec_exndec (d3c.d3ec_loc, d3cs1)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Cexndec]
      | D3Cdcstdec (knd, d3cs1) => let
          val hid = hidec_dcstdec (d3c.d3ec_loc, knd, d3cs1)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Cdcstdec]
      | D3Cimpdec impdec => let
          val d2c = impdec.i3mpdec_cst
          val hid = begin case+ 0 of
            | _ when d2cst_is_proof d2c => let
                val (pf_token | ()) = the_dyncstsetlst_push ()
                val () = d3exp_prf_tr (impdec.i3mpdec_def)
                val d2cs = the_dyncstsetlst_pop (pf_token | (*none*))
                val () = the_dyncstset_add_if (d2c)
                val hid = hiimpdec_prf_make (impdec.i3mpdec_loc, d2c, d2cs)
              in
                hidec_impdec_prf (d3c.d3ec_loc, hid)
              end // end of [_ when ...]
            | _ (* nonproof implementation *) => let
                val hid = i3mpdec_tr impdec in hidec_impdec (d3c.d3ec_loc, hid)
              end // end of [_]
          end : hidec
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Cimpdec]
      | D3Cfundecs (decarg, knd, fundecs) => begin
          if $Syn.funkind_is_proof knd then let
            val () = f3undeclst_prf_tr (fundecs) in aux0 (d3cs, res)
          end else let
            val hifundecs = f3undeclst_tr (decarg, fundecs)
            val hid = hidec_fundecs (d3c.d3ec_loc, decarg, knd, hifundecs)
          in
            aux1 (d3cs, hid, res)
          end // end of [if]
        end // end of [D3Cfundecs]
      | D3Cvaldecs (knd, valdecs) => begin
          if $Syn.valkind_is_proof knd then let
            val () = v3aldeclst_prf_tr (valdecs) in aux0 (d3cs, res)
          end else let
            val hid = begin
              hidec_valdecs (d3c.d3ec_loc, knd, v3aldeclst_tr valdecs)
            end
          in
            aux1 (d3cs, hid, res)
          end // end of [if]
        end // end of [D3Cvaldecs]
      | D3Cvaldecs_par valdecs => let
          val hid = hidec_valdecs_par (d3c.d3ec_loc, v3aldeclst_tr valdecs)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Cvaldecs_par]
      | D3Cvaldecs_rec valdecs => let
          val hid = hidec_valdecs_rec (d3c.d3ec_loc, v3aldeclst_tr valdecs)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Cvaldecs_rec]
      | D3Cvardecs vardecs => let
          val hid = hidec_vardecs (d3c.d3ec_loc, v3ardeclst_tr vardecs)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Cvardecs]
      | D3Clocal (d3cs_head, d3cs_body) => let
          val hids_head = d3eclst_tr d3cs_head
          val hids_body = d3eclst_tr d3cs_body
          val hid = hidec_local (d3c.d3ec_loc, hids_head, hids_body)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Clocal]
      | D3Cstaload (fil, od3c) => let
          val () = begin case+ od3c of
            | Some d3cs => begin
                // record definitions for templates
                let val _(*hideclst*) = d3eclst_tr d3cs in () end
              end // end of [Some]
            | None () => ()
          end // end of [val]
          val hid = hidec_staload (d3c.d3ec_loc, fil)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Cstaload]
      | D3Cdynload fil => let
          val hid = hidec_dynload (d3c.d3ec_loc, fil)
        in
          aux1 (d3cs, hid, res)
        end // end of [D3Cdynload]
      end // end of [cons]
    | nil () => (res := nil ())
  end // end of [aux0]

  and aux1 (
      d3cs: d3eclst, hid: hidec, res: &hideclst? >> hideclst
    ) : void = let
    val () = (res := cons {hidec} {0} (hid, ?))
    val+ cons (_, !res_nxt) = res
  in
    aux0 (d3cs, !res_nxt); fold@ res
  end // end of [aux1]

  var res: hideclst // uninitialize
  val () = aux0 (d3cs0, res)
in
  res
end // end of [d3eclst_tr]

(* ****** ****** *)

implement d3eclst_prf_tr (d3cs0: d3eclst): void = aux (d3cs0) where {
  fun aux (d3cs: d3eclst): void = begin case+ d3cs of
    | list_cons (d3c, d3cs) => begin case+ d3c.d3ec_node of
      | D3Cnone () => aux (d3cs)
      | D3Clist d3cs1 => let
          val () = d3eclst_prf_tr d3cs1 in aux d3cs
        end // end of [D3Clist]
      | D3Cdatdec _ => aux d3cs
      | D3Cexndec _ => aux d3cs
      | D3Cdcstdec _ => aux d3cs
      | D3Cfundecs (decarg, knd, fundecs) => let
          val () = f3undeclst_prf_tr fundecs in aux (d3cs)
        end // end of [D3Cfundecs]
      | D3Cvaldecs (knd, valdecs) => let
          val () = v3aldeclst_prf_tr valdecs in aux (d3cs)
        end // end of [D3Cvaldecs]
      | D3Cvaldecs_rec valdecs => let
          val () = v3aldeclst_prf_tr valdecs in aux (d3cs)
        end // end of [D3Cvaldecs_rec]
      | D3Clocal (d3cs_head, d3cs_body) => let
          val () = d3eclst_prf_tr d3cs_head
          val () = d3eclst_prf_tr d3cs_body
        in
          aux (d3cs)
        end // end of [D3Clocal]
      | D3Cstaload _ => aux d3cs
      | D3Cdynload _ => aux d3cs
      | _ => begin
          $Loc.prerr_location d3c.d3ec_loc; prerr ": Internal Error";
          prerr ": d3explst_prf_tr: illegal proof declaration"; prerr_newline ();
          $Err.abort {void} ()
        end // end of [_]
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [aux]
} // end of [d3eclst_prf_tr]

(* ****** ****** *)

(* end of [ats_trans4.dats] *)
