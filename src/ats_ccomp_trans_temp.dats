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

// Time: May 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

%{^

#include "ats_counter.cats" /* only needed for [ATS/Geizella] */

%}

(* ****** ****** *)

staload "ats_reference.sats"

(* ****** ****** *)

staload CS = "ats_charlst.sats"
staload Err = "ats_error.sats"
staload HT = "ats_hashtbl.sats"
staload Lst = "ats_list.sats"
staload Map = "ats_map_lin.sats"
staload Stamp = "ats_stamp.sats"
staload Sym = "ats_symbol.sats"

(* ****** ****** *)

staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"

(* ****** ****** *)

staload "ats_hiexp.sats"
staload "ats_ccomp.sats"
staload "ats_ccomp_env.sats"

(* ****** ****** *)

staload _(*anonymous*) = "ats_reference.dats"
staload _(*anonymois*) = "ats_hashtbl.dats"
staload _(*anonymois*) = "ats_map_lin.dats"

(* ****** ****** *)

absviewtype stactx_vt
absview stactx_token_v

extern fun the_stactx_add (s2v: s2var_t, hit: hityp_t): void
extern fun the_stactx_free ():<> void // free the (toplevel) stactx
extern fun the_stactx_find (s2v: s2var_t): Option_vt (hityp_t)
extern fun the_stactx_push (): @(stactx_token_v | void)
extern fun the_stactx_pop (pf: stactx_token_v | (*none*)): void

(* ****** ****** *)

local

viewtypedef stactx = $Map.map_vt (s2var_t, hityp_t)
viewtypedef stactxlst = List_vt (stactx)

assume stactx_vt = stactx
assume stactx_token_v = unit_v

fn stactx_nil ():<> stactx = $Map.map_make (compare_s2var_s2var)

val the_stactx = ref_make_elt<stactx> (stactx_nil ())
val the_stactxlst = ref_make_elt<stactxlst> (list_vt_nil ())

in // in of [local]

implement the_stactx_add (s2v, hit) = let
  val (vbox pf | p) = ref_get_view_ptr (the_stactx)
in
  $Map.map_insert<s2var_t,hityp_t> (!p, s2v, hit)
end // end of [the_stactx_add]

implement the_stactx_find (s2v) = let
  val (vbox pf | p) = ref_get_view_ptr (the_stactx)
in
  $Map.map_search<s2var_t,hityp_t> (!p, s2v)
end // end of [the_stactx_find]

implement the_stactx_push () = let
  val stactx = let
    val (vbox pf | p) = ref_get_view_ptr (the_stactx)
    val stactx = !p
  in
    !p := stactx_nil (); stactx
  end
  val () = let
    val (vbox pf | p) = ref_get_view_ptr (the_stactxlst)
  in
    !p := list_vt_cons (stactx, !p)
  end
in
  (unit_v () | ())
end // end of [the_stactx_push]

implement the_stactx_pop (pf | (*none*)) = let
  prval unit_v () = pf
  var err: int = 0
  val stactx = let
    val (vbox pf | p) = ref_get_view_ptr (the_stactxlst)
    val stactx = (
      case+ !p of
      | ~list_vt_cons (x, xs) => (!p := (xs: stactxlst); x)
      | list_vt_nil () => begin
          fold@ (!p); err := 1; stactx_nil ()
        end
    ) : stactx
  in
    stactx
  end // end of [val]
  val () = // error checking
    if err > 0 then begin
      prerr "Internal Error: ats_ccomp_trans_temp: the_stactx_pop";
      prerr_newline ();
      $Err.abort {void} ()
    end
  val stactx = let
    val (vbox pf | p) = ref_get_view_ptr (the_stactx)
    val () = $Map.map_free (!p)
  in
    !p := stactx
  end // end of [val]
in
  // empty
end // end of [the_stactx_pop]

end // end of [local]

(* ****** ****** *)

// declared in [ats_hiexp.sats]
implement hityp_s2var_normalize (s2v) = the_stactx_find (s2v)

(* ****** ****** *)

#define PTR_TYPE_NAME "ats_ptr_type"

extern fun template_name_make
  (basename: string, hitss: hityplstlst_t): string

implement template_name_make (basename, hitss) = let
  viewtypedef T = $CS.Charlst_vt
  fun aux_char (cs: &T, c: char): void = (cs := $CS.CHARLSTcons (c, cs))

  fun aux_string {n,i:nat | i <= n}
     (cs: &T, i: int i, s: string n): void = begin
    if string1_is_at_end (s, i) then () else begin
      cs := $CS.CHARLSTcons (s[i], cs); aux_string (cs, i+1, s)
    end // end of [if]
  end // end of [aux_string]

  fun aux_hityp
    (cs: &T, hit: hityp): void = let
    val HITNAM (knd, name) = hit.hityp_name
    val name = (if knd > 0 then PTR_TYPE_NAME else name): string
    val name = string1_of_string0 name
  in
    aux_string (cs, 0, name)
  end // end of [aux_hityp]

  fun aux_hityplst
    (cs: &T, hits: hityplst): void = begin
    case+ hits of
    | list_cons (hit, hits) => let
        val () = (aux_char (cs, '_'); aux_hityp (cs, hit))
      in
        aux_hityplst (cs, hits)
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [aux_hityplst]

  fun aux_hityplstlst
    (cs: &T, hitss: hityplstlst): void = begin
    case+ hitss of
    | list_cons (hits, hitss) => let
        val () = (aux_char (cs, '_'); aux_hityplst (cs, hits))
      in
        aux_hityplstlst (cs, hitss)
      end // end of [list_cons]
    | list_nil () => ()
  end // end of [aux_hityplstlst]

  var cs: T = $CS.CHARLSTnil ()
  val basename = string1_of_string0 (basename)
  val () = aux_string (cs, 0, basename)
  val () = aux_hityplstlst (cs, hityplstlst_decode hitss)
in
  $CS.string_make_rev_charlst (cs)
end // end of [template_name_make]

(* ****** ****** *)

datatype tmpcstvar =
  | TMPcst of d2cst_t | TMPvar of d2var_t

fn fprint_tmpcstvar {m:file_mode}
  (pf: file_mode_lte (m, w) | out: &FILE m, tcv: tmpcstvar)
  : void = begin case+ tcv of
  | TMPcst d2c => fprint_d2cst (pf | out, d2c)
  | TMPvar d2v => fprint_d2var (pf | out, d2v)
end // end of [fprint_tmpcstvar]

fn print_tmpcstvar (tcv: tmpcstvar): void = print_mac (fprint_tmpcstvar, tcv)
fn prerr_tmpcstvar (tcv: tmpcstvar): void = prerr_mac (fprint_tmpcstvar, tcv)

(* ****** ****** *)

extern fun ccomp_tmpdef (
  loc0: loc_t
, res: &instrlst_vt
, hit0: hityp_t
, tcv: tmpcstvar
, hitss: hityplstlst_t
, fullname: string
, tmpdef: tmpdef_t
) : valprim

(* ****** ****** *)

fn template_arg_match (
    loc0: loc_t
  , tcv: tmpcstvar
  , tmparg: s2qualst
  , hitss: hityplstlst_t
  ) : void = let
  fn aux (s2v: s2var_t, hit: hityp) :<cloptr1> void = begin
    let val hit = hityp_encode hit in the_stactx_add (s2v, hit) end
  end // end of [aux]

  fun auxlst (s2vs: s2varlst, hits: hityplst)
    :<cloptr1> void = begin case+ (s2vs, hits) of
    | (list_cons (s2v, s2vs), list_cons (hit, hits)) => begin
        let val () = aux (s2v, hit) in auxlst (s2vs, hits) end
      end
    | (list_nil (), list_nil ()) => ()
    | (_, _) => begin
        $Loc.prerr_location loc0;
        prerr ": error(ccomp)";
        prerr ": template argument mismatch for ["; prerr_tmpcstvar tcv; prerr "].";
        prerr_newline ();
        $Err.abort {void} ()
      end
  end // end of [auxlst]

  fun auxlstlst
    (s2qs: s2qualst, hitss: hityplstlst)
    :<cloptr1> void = begin case+ (s2qs, hitss) of
    | (list_cons (s2q, s2qs), list_cons (hits, hitss)) => begin
        let val () = auxlst (s2q.0, hits) in auxlstlst (s2qs, hitss) end
      end
    | (list_nil (), list_nil ()) => ()
    | (_, _) => begin
        $Loc.prerr_location loc0;
        prerr ": error(ccomp)";
        prerr ": template argument mismatch for ["; prerr_tmpcstvar tcv; prerr "].";
        prerr_newline ();
        $Err.abort {void} ()
      end
  end // end of [auxlstlst]
in
  auxlstlst (tmparg, hityplstlst_decode hitss)
end // end of [template_arg_match]

(* ****** ****** *)

extern fun tmpnamtbl_add (fullname: string, vp_funclo: valprim): void
extern fun tmpnamtbl_find (fullname: string): Option_vt (valprim)

(* ****** ****** *)

local

#define TMPNAMETBL_SIZE_HINT 1024

typedef tmpnamtbl = $HT.hashtbl_t (string, valprim)

val the_tmpnamtbl: tmpnamtbl = begin
  $HT.hashtbl_str_make_hint {valprim} (TMPNAMETBL_SIZE_HINT)
end

in // in of [local]

implement tmpnamtbl_add (fullname, vp_funclo) = let
  val ans = $HT.hashtbl_insert (the_tmpnamtbl, fullname, vp_funclo)
in
  case+ ans of
  | ~None_vt () => () | ~Some_vt _(*valprim*) => begin
      prerr "Internal Error: tmpnamtbl_add: fullname = ";
      prerr fullname;
      prerr_newline ();
      $Err.abort {void} ()
    end
end // end of [tmpnamtbl_add]

implement tmpnamtbl_find (fullname) =
  $HT.hashtbl_search (the_tmpnamtbl, fullname)

end // end of [local]

(* ****** ****** *)

implement ccomp_tmpdef
  (loc0, res, hit0, tcv, hitss, fullname, tmpdef) = let
  val fl = funlab_make_nam_typ (fullname, hit0)
  val vp_funclo = valprim_funclo_make (fl)
  val (pf_stactx_token | ()) = the_stactx_push ()
  val (pf_dynctx_token | ()) = the_dynctx_push ()
  val tmparg = tmpdef_arg_get tmpdef
  val () = template_arg_match (loc0, tcv, tmparg, hitss)
  val () = tmpnamtbl_add (fullname, vp_funclo)
  (* ****** ****** *)
  val (pf_tailcallst_mark | ()) = the_tailcallst_mark ()
  val () = the_tailcallst_add (fl, list_nil ())
  val _(*funentry_t*) = let
    val prolog = '[INSTRfunlab fl]
    val hie = tmpdef_exp_get (tmpdef); val loc_fun = hie.hiexp_loc
  in
    case+ hie.hiexp_node of
    | HIElam (hips_arg, hie_body) => begin
        ccomp_exp_lam_funlab (loc_fun, prolog, hips_arg, hie_body, fl)
      end
    | _ => begin
        $Loc.prerr_location loc_fun;
        prerr ": Internal Error: ccomp_tmpdef";
        prerr ": not a lambda-expression: ["; prerr hie; prerr "]";
        prerr_newline ();
        $Err.abort {funentry_t} ()
      end
   end // end of [val]
  val () = the_tailcallst_unmark (pf_tailcallst_mark | (*none*))
  (* ****** ****** *)
  val () = the_stactx_pop (pf_stactx_token | (*none*))
  val () = the_dynctx_pop (pf_dynctx_token | (*none*))
in
  vp_funclo
end // end of [ccomp_tmpdef]

(* ****** ****** *)

implement ccomp_exp_template_cst
  (loc0, res, hit0, d2c, hitss) = let
  val tmpdef = (
    case+ tmpcstmap_find d2c of
    | ~Some_vt tmpdef => tmpdef | ~None_vt () => begin
        $Loc.prerr_location loc0;
        prerr ": the templation definition for [";
        prerr d2c;
        prerr "] is unavailable.";
        prerr_newline ();
        $Err.abort {tmpdef_t} ()
      end
  ) : tmpdef_t
  val hitss = hityplstlst_normalize (hitss)
  val fullname = let
    val ext = d2cst_ext_get d2c
    val basename = (
      if stropt_is_some ext then stropt_unsome ext else let
        val sym = d2cst_sym_get d2c
        val stamp = d2cst_stamp_get d2c
      in
        tostringf (
          "%s$%s", @($Sym.symbol_name sym, $Stamp.tostring_stamp stamp)
        )
      end // end of [if]
    ) : string
  in
    template_name_make (basename, hitss)
  end // end of [val]
(*
  val () = begin
    prerr "ccomp_exp_tmpcst: hit0 = "; prerr hit0; prerr_newline ();
    prerr "ccomp_exp_tmpcst: fullname = "; prerr fullname; prerr_newline ();
  end
*)
  val ovp = tmpnamtbl_find (fullname)
in
  case+ ovp of
  | ~Some_vt vp => vp | ~None_vt () => begin
      ccomp_tmpdef (
        loc0, res, hit0, TMPcst d2c, hitss, fullname, tmpdef
      )
    end
end // end of [ccomp_exp_tmpcst]

(* ****** ****** *)

implement ccomp_exp_template_var
  (loc0, res, hit0, d2v, hitss) = let
  val tmpdef = (
    case+ tmpvarmap_find d2v of
    | ~Some_vt tmpdef => tmpdef | ~None_vt () => begin
        $Loc.prerr_location loc0;
        prerr ": the templation definition for [";
        prerr d2v;
        prerr "] is unavailable.";
        prerr_newline ();
        $Err.abort {tmpdef_t} ()
      end
  ) : tmpdef_t
  val hitss = hityplstlst_normalize (hitss)
  val fullname = let
    val sym = d2var_sym_get d2v and stamp = d2var_stamp_get d2v
    val basename = tostringf (
      "%s$%s", @($Sym.symbol_name sym, $Stamp.tostring_stamp stamp)
    )
  in
    template_name_make (basename, hitss)
  end // end of [val]
(*
  val () = begin
    prerr "ccomp_exp_tmpvar: hit0 = "; prerr hit0; prerr_newline ();
    prerr "ccomp_exp_tmpvar: fullname = "; prerr fullname; prerr_newline ();
  end
*)
  val ovp = tmpnamtbl_find (fullname)
in
  case+ ovp of
  | ~Some_vt vp => vp | ~None_vt () => begin
      ccomp_tmpdef (
        loc0, res, hit0, TMPvar d2v, hitss, fullname, tmpdef
      )
    end
end // end of [ccomp_exp_tmpvar]

(* ****** ****** *)

(* end of [ats_ccomp_trans_temp.dats] *)
