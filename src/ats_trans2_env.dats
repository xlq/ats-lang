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

staload Err = "ats_error.sats"
staload Fil = "ats_filename.sats"
staload HT = "ats_hashtbl.sats"
staload Lst = "ats_list.sats"
staload NS = "ats_namespace.sats"
staload Sym = "ats_symbol.sats"
staload SymEnv = "ats_symenv.sats"

(* ****** ****** *)

staload "ats_reference.sats"

(* ****** ****** *)

staload "ats_staexp1.sats"
staload "ats_staexp2.sats"
staload "ats_dynexp2.sats"
staload "ats_trans2_env.sats"

(* ****** ****** *)

staload _(*anonymous*) = "ats_hashtbl.dats"
staload _(*anonymous*) = "ats_map_lin.dats"
staload _(*anonymous*) = "ats_symenv.dats"

(* ****** ****** *)

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

overload = with $Sym.eq_symbol_symbol

(* ****** ****** *)

viewtypedef s2rtextmap = $SymEnv.symmap_t (s2rtext)
typedef s2rtextmapref = ref s2rtextmap
typedef s2rtextmaptbl = $HT.hashtbl_t (sym_t, s2rtextmapref)

val the_s2rtextmaptbl: s2rtextmaptbl =
  $HT.hashtbl_make_hint {sym_t, s2rtextmapref} (
    lam s => $Sym.symbol_hash s, lam (s1, s2) => s1 = s2, 256
  )

(* ****** ****** *)

viewtypedef s2itemmap = $SymEnv.symmap_t (s2item)
typedef s2itemmapref = ref s2itemmap
typedef s2itemmaptbl = $HT.hashtbl_t (sym_t, s2itemmapref)

val the_s2itemmaptbl: s2itemmaptbl =
  $HT.hashtbl_make_hint {sym_t, s2itemmapref} (
    lam s => $Sym.symbol_hash s, lam (s1, s2) => s1 = s2, 256
  )

(* ****** ****** *)

viewtypedef d2itemmap = $SymEnv.symmap_t (d2item)
typedef d2itemmapref = ref d2itemmap
typedef d2itemmaptbl = $HT.hashtbl_t (sym_t, d2itemmapref)

val the_d2itemmaptbl: d2itemmaptbl =
  $HT.hashtbl_make_hint {sym_t, d2itemmapref} (
    lam s => $Sym.symbol_hash s, lam (s1, s2) => s1 = s2, 256
  )

(* ****** ****** *)

typedef d2eclsttbl = $HT.hashtbl_t (sym_t, d2eclst)

val the_d2eclsttbl: d2eclsttbl =
  $HT.hashtbl_make_hint {sym_t, d2eclst} (
    lam s => $Sym.symbol_hash s, lam (s1, s2) => s1 = s2, 256
  )

implement d2eclst_namespace_add (id, d2cs) = let
  val ans = $HT.hashtbl_insert (the_d2eclsttbl, id, d2cs)
in
  case+ ans of
  | ~Some_vt _ => begin
      prerr "Internal Error: ";
      prerr "d2eclst_namespace_add: id = ";
      $Sym.prerr_symbol id;
      prerr_newline ();
      $Err.abort {void} ()
    end
  | ~None_vt _ => ()
end // end of [d2eclst_namespace_add]

implement d2eclst_namespace_find (id) = 
  $HT.hashtbl_search (the_d2eclsttbl, id)

(* ****** ****** *)

assume s2rtenv_token = unit_v
typedef s2rtenv = $SymEnv.symenv_t (s2rtext)

local

val the_s2rtenv: s2rtenv = $SymEnv.symenv_make ()

in // in of [local]

implement the_s2rtenv_add (id, s2te) = let
  val () = case+
    $SymEnv.symenv_remove (the_s2rtenv, id) of
    | ~Some_vt _ => () | ~None_vt () => ()
in
  $SymEnv.symenv_insert (the_s2rtenv, id, s2te)
end // end of [the_s2rtenv_add]

fn the_s2rtenv_namespace_find
  (id: sym_t): s2rtextopt_vt = let
  fn f (name: sym_t):<cloptr1> s2rtextopt_vt = let
    val r_m: s2rtextmapref =
      case+ $HT.hashtbl_search (the_s2rtextmaptbl, name) of
      | ~Some_vt m => m | ~None_vt _ => begin
          prerr "Internal Error: s2rtenv_namespace_find: name = ";
          $Sym.prerr_symbol name;
          prerr_newline ();
          $Err.abort {s2rtextmapref} ()
        end // end of [None_vt]
  in
    $SymEnv.symmap_ref_search (r_m, id)
  end // end of [f]
in
  $NS.the_namespace_search (f)
end // end of [the_s2rtenv_namespace_find]

implement the_s2rtenv_find (id) = let
  val ans = $SymEnv.symenv_search (the_s2rtenv, id)
in
  case+ ans of
  | Some_vt _ => (fold@ ans; ans)
  | ~None_vt () => let
      val ans = the_s2rtenv_namespace_find id
    in
      case+ ans of
      | Some_vt _ => begin fold@ ans; ans end
      | ~None_vt () => begin
          $SymEnv.symenv_pervasive_search (the_s2rtenv, id)
        end // end of [None_vt]
    end // end of [None_vt]
end // end of [the_s2rtenv_find]

implement the_s2rtenv_find_qua (q, id) = begin
  case+ q.s0rtq_node of
  | $Syn.S0RTQnone () => the_s2rtenv_find id
  | $Syn.S0RTQsym q_id => let
      val fil = case+ the_s2expenv_find q_id of
        | ~Some_vt (S2ITEMfil fil) => fil
        | ~Some_vt _ => begin
            $Loc.prerr_location q.s0rtq_loc;
            prerr ": error(2)";
            prerr ": the qualifier [";
            $Sym.prerr_symbol q_id;
            prerr "] should refer to a filename but it does not.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end
        | ~None_vt _ => begin
            $Loc.prerr_location q.s0rtq_loc;
            prerr ": error(2)";
            prerr ": the qualifier [";
            $Sym.prerr_symbol q_id;
            prerr "] is unrecognized.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end
      val fil_sym = $Fil.filename_full_sym fil
    in
      case+ $HT.hashtbl_search (the_s2rtextmaptbl, fil_sym) of
      | ~Some_vt r_m => $SymEnv.symmap_ref_search (r_m, id)
      | ~None_vt () => begin
          prerr "Internal Error: the loaded file [";
          $Sym.prerr_symbol fil_sym;
          prerr "] cannot be located.";
          prerr_newline ();
          $Err.abort {s2rtextopt_vt} ()
        end
    end // end of [S0RTQsym]
  | $Syn.S0RTQstr name => let
      // a feature that should probably be deprecated!!!
    in
      None_vt ()
    end
end // end [the_s2rtenv_find_qua]

implement the_s2rtenv_pop (pf | (*none*)) = begin
  let prval unit_v () = pf in $SymEnv.symenv_pop (the_s2rtenv) end
end // end of [the_s2rtenv_pop]

implement the_s2rtenv_push () = begin
  (unit_v | $SymEnv.symenv_push (the_s2rtenv))
end // end of [the_s2rtenv_push]

implement the_s2rtenv_localjoin (pf1, pf2 | (*none*)) = let
  prval unit_v () = pf1 and unit_v () = pf2
in
  $SymEnv.symenv_localjoin (the_s2rtenv)
end // end of [the_s2rtenv_localjoin]

fn the_s2rtenv_pervasive_add_top (): void = let
  val m = $SymEnv.symenv_top (the_s2rtenv)
in
  $SymEnv.symenv_pervasive_add (the_s2rtenv, m)
end // end of [the_s2rtenv_pervasive_add_top]

fn the_s2rtenv_namespace_add_top (id: sym_t): void = let
  val m = $SymEnv.symenv_top the_s2rtenv
  val r_m: s2rtextmapref = ref_make_elt (m)
  val ans = $HT.hashtbl_insert (the_s2rtextmaptbl, id, r_m)
in
  case+ ans of
  | ~Some_vt _ => begin
      prerr "Internal Error: ";
      prerr "s2rtenv_namespace_add_top: id = ";
      $Sym.prerr_symbol id;
      prerr_newline ();
      $Err.abort {void} ()
    end
  | ~None_vt _ => ()  
end // end of [the_s2rtenv_namespace_add_top]

fn the_s2rtenv_save () = $SymEnv.symenv_save (the_s2rtenv)
fn the_s2rtenv_restore () = $SymEnv.symenv_restore (the_s2rtenv)

end // end of [local]

(* ****** ****** *)

assume s2expenv_token = unit_v
typedef s2expenv = $SymEnv.symenv_t (s2item)

local

val the_s2expenv: s2expenv = $SymEnv.symenv_make ()

in // in of [local]

implement the_s2expenv_add (id, s2i) = let
  val () = case+
    $SymEnv.symenv_remove (the_s2expenv, id) of
    | ~Some_vt _ => () | ~None_vt () => ()
in
  $SymEnv.symenv_insert (the_s2expenv, id, s2i)
end // end of [the_s2expenv_add]

implement the_s2expenv_add_scst (s2c) = let
(*
  val () = begin
    print "s2expenv_add_scst: s2c = "; print s2c; print_newline ()
  end
  val () = begin
    print "s2expenv_add_scst: s2c_s2t = ";
    print (s2cst_srt_get s2c);
    print_newline ()
  end
*)
  val id = s2cst_sym_get s2c
  val s2cs = (
    case+ the_s2expenv_find (id) of
    | ~Some_vt s2i => begin case+ s2i of
      | S2ITEMcst s2cs => s2cs | _ => S2CSTLSTnil ()
      end
    | ~None_vt () => S2CSTLSTnil ()
  ) : s2cstlst
  val () = begin
    case+ $SymEnv.symenv_remove (the_s2expenv, id) of
    | ~Some_vt s2i => () | ~None_vt () => ()
  end // end of [val]
in
  $SymEnv.symenv_insert (
    the_s2expenv, id, S2ITEMcst (S2CSTLSTcons (s2c, s2cs))
  )
end // end of [the_s2expenv_add_scst]

implement the_s2expenv_add_svar (s2v) = let
  val id = s2var_sym_get s2v in the_s2expenv_add (id, S2ITEMvar s2v)
end // end of [the_s2expenv_add_svar]

implement the_s2expenv_add_svarlst (s2vs) = begin
  case+ s2vs of
  | cons (s2v, s2vs) => begin
      the_s2expenv_add_svar s2v; the_s2expenv_add_svarlst s2vs
    end
  | nil () => ()
end // end of [the_s2expenv_add_svarlst]

(* ****** ****** *)

implement the_s2expenv_add_datconptr (d2c) = let
  val sym = d2con_sym_get d2c
  val name = $Sym.symbol_name sym
  val id = $Sym.symbol_make_string (name + "_unfold")
  val () = the_s2expenv_add (id, S2ITEMdatconptr d2c)
in
  // empty
end // end of [the_s2expenv_add_datconptr]

implement the_s2expenv_add_datcontyp (d2c) = let
  val sym = d2con_sym_get d2c
  val name = $Sym.symbol_name sym
  val id = $Sym.symbol_make_string (name + "_pstruct")
  val () = the_s2expenv_add (id, S2ITEMdatcontyp d2c)
in
  // empty
end // end of [the_s2expenv_add_datcontyp]

(* ****** ****** *)

fn the_s2expenv_namespace_find (id: sym_t): s2itemopt_vt = let
  fn f (name: sym_t):<cloptr1> s2itemopt_vt = let
    val r_m: s2itemmapref = begin
      case+ $HT.hashtbl_search (the_s2itemmaptbl, name) of
      | ~Some_vt m => m | ~None_vt _ => begin
          prerr "Internal Error: the_s2expenv_namespace_find: name = ";
          $Sym.prerr_symbol name;
          prerr_newline ();
          $Err.abort {s2itemmapref} ()
        end // end of [None_vt]
    end // end of [val]
  in
    $SymEnv.symmap_ref_search (r_m, id)
  end // end of [f]
in
  $NS.the_namespace_search (f)
end // end of [the_s2expenv_namespace_find]

implement the_s2expenv_find (id) = let
  val ans = $SymEnv.symenv_search (the_s2expenv, id)
in
  case+ ans of
  | Some_vt _ => (fold@ ans; ans)
  | ~None_vt () => let
      val ans = the_s2expenv_namespace_find id
    in
      case+ ans of
      | ~None_vt () => begin
          $SymEnv.symenv_pervasive_search (the_s2expenv, id)
        end
      | Some_vt _ => (fold@ ans; ans)
    end // end of [None_vt]
end // end of [the_s2expenv_find]

implement the_s2expenv_pervasive_find (id) = begin
  $SymEnv.symenv_pervasive_search (the_s2expenv, id)
end // end of [the_s2expenv_pervasive_find]

implement the_s2expenv_find_qua (q, id) = begin
  case+ q.s0taq_node of
  | $Syn.S0TAQnone () => the_s2expenv_find id
  | $Syn.S0TAQsymdot (q_id) => let
      val fil = case+ the_s2expenv_find q_id of
        | ~Some_vt (S2ITEMfil fil) => fil
        | ~Some_vt _ => begin
            $Loc.prerr_location q.s0taq_loc;
            prerr ": error(2)";
            prerr ": the qualifier [";
            $Sym.prerr_symbol q_id;
            prerr "] should refer to a filename but it does not.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end // end of [Some_vt]
        | ~None_vt _ => begin
            $Loc.prerr_location q.s0taq_loc;
            prerr ": error(2)";
            prerr ": the qualifier [";
            $Sym.prerr_symbol q_id;
            prerr "] is unrecognized.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end // end of [None_vt]
      val fil_sym = $Fil.filename_full_sym fil
    in
      case+ $HT.hashtbl_search (the_s2itemmaptbl, fil_sym) of
      | ~Some_vt r_m => $SymEnv.symmap_ref_search (r_m, id)
      | ~None_vt () => None_vt ()
    end // end of [$Syn.S0TAQsymdot]
  | _ => None_vt ()
end // end of [the_s2expenv_find_qua]

implement the_s2expenv_pop (pf | (*none*)) = begin
  let prval unit_v () = pf in $SymEnv.symenv_pop (the_s2expenv) end
end // end of [the_s2expenv_pop]

implement the_s2expenv_push () = begin
  (unit_v | $SymEnv.symenv_push (the_s2expenv))
end // end of [the_s2expenv_push]

implement the_s2expenv_localjoin (pf1, pf2 | (*none*)) = let
  prval unit_v () = pf1 and unit_v () = pf2
in
  $SymEnv.symenv_localjoin (the_s2expenv)
end // end of [the_s2expenv_localjoin]

fn the_s2expenv_pervasive_add_top (): void = let
  val m = $SymEnv.symenv_top (the_s2expenv)
in
  $SymEnv.symenv_pervasive_add (the_s2expenv, m)
end // end of [the_s2expenv_pervasive_add_top]

fn the_s2expenv_namespace_add_top (id: sym_t): void = let
  val m = $SymEnv.symenv_top the_s2expenv
  val r_m: s2itemmapref = ref_make_elt (m)
  val ans = $HT.hashtbl_insert (the_s2itemmaptbl, id, r_m)
in
  case+ ans of
  | ~Some_vt _ => begin
      prerr "Internal Error: ";
      prerr "the_s2expenv_namespace_add_top: id = ";
      $Sym.prerr_symbol id;
      prerr_newline ();
      $Err.abort {void} ()
    end // end of [Some_vt]
  | ~None_vt _ => ()  
end // end of [the_s2expenv_namespace_add_top]

fn the_s2expenv_save () = $SymEnv.symenv_save (the_s2expenv)
fn the_s2expenv_restore () = $SymEnv.symenv_restore (the_s2expenv)

end // end of [local]

(* ****** ****** *)

local

val the_macro_level: ref int = ref_make_elt<int> (1)

in // in of [local]

implement macro_level_get () = !the_macro_level

implement macro_level_inc (loc) = let
  val level = !the_macro_level
(*
  val () =
    if level > 0 then begin
      $Loc.prerr_location loc;
      prerr ": error(2)";
      prerr ": the syntax `(...) is used incorrectly at this location.";
      prerr_newline ();
      $Err.abort {void} ()
    end
*)
in
  !the_macro_level := level + 1
end // end of [macro_level_inc]

implement macro_level_dec (loc) = let
  val level = !the_macro_level
  val () =
    if level = 0 then begin
      $Loc.prerr_location loc; prerr ": error(2)";
      prerr ": the syntax ,(...) or %(...) is used incorrectly at this location.";
      prerr_newline ();
      $Err.abort {void} ()
    end
in
  !the_macro_level := level - 1
end // end of [macro_level_dec]

end // end of [local]

(* ****** ****** *)

local

val the_template_level = ref_make_elt<int> (0)

in

implement template_level_get () =
  !the_template_level

implement template_level_inc () =
  !the_template_level := !the_template_level + 1

implement template_level_dec () =
  !the_template_level := !the_template_level - 1

end // end of [local]

implement
  s2var_tmplev_check (loc, s2v) = let
  val s2v_tmplev = s2var_tmplev_get (s2v)
in
  case+ 0 of
  | _ when s2v_tmplev > 0 => let
      val tmplev = template_level_get ()
    in
      if s2v_tmplev < tmplev then begin
        $Loc.prerr_location loc; prerr ": error(2)";
        prerr ": the static variable ["; prerr s2v; prerr "] is out of scope.";
        prerr_newline ();
        $Err.abort {void} ()
      end // end of [if]
    end // end of [_ when s2v_tmplev > 0]
  | _ => () // not a template variable
end // end of [s2var_tmplev_check]

implement s2qualst_tmplev_set (s2vpss, tmplev) = let
  fun aux_s2vs
    (s2vs: s2varlst, tmplev: int): void = case+ s2vs of
    | cons (s2v, s2vs) => begin
        s2var_tmplev_set (s2v, tmplev); aux_s2vs (s2vs, tmplev)
      end // end of [cons]
    | nil () => ()
  fun aux_s2qualst (s2vpss: s2qualst, tmplev: int): void =
    case+ s2vpss of
    | cons (s2vps, s2vpss) => begin
        aux_s2vs (s2vps.0, tmplev); aux_s2qualst (s2vpss, tmplev)
      end // end of [cons]
    | nil () => ()
in
  aux_s2qualst (s2vpss, tmplev)
end // end of s2qualst_tmplev_set]

(* ****** ****** *)

assume d2expenv_token = unit_v
typedef d2expenv = $SymEnv.symenv_t (d2item)

local

val the_d2expenv: d2expenv = $SymEnv.symenv_make ()

in // in of [local]

implement the_d2expenv_add (id, d2i) = let
  val () = case+
    $SymEnv.symenv_remove (the_d2expenv, id) of
    | ~Some_vt _ => () | ~None_vt () => ()
in
  $SymEnv.symenv_insert (the_d2expenv, id, d2i)
end // end of [the_d2expenv_add]

implement the_d2expenv_add_dcon (d2c) = let
  val id = d2con_sym_get d2c
  val d2cs = (
    case+ the_d2expenv_find (id) of
    | ~Some_vt d2i => begin case+ d2i of
      | D2ITEMcon d2cs => d2cs | _ => D2CONLSTnil ()
      end // end of [Some_vt]
    | ~None_vt () => D2CONLSTnil ()
  ) : d2conlst
  val () = begin
    case+ $SymEnv.symenv_remove (the_d2expenv, id) of
    | ~Some_vt _ => () | ~None_vt () => ()
  end // end of [val]
in
  $SymEnv.symenv_insert (
    the_d2expenv, id, D2ITEMcon (D2CONLSTcons (d2c, d2cs))
  )
end // end of [the_d2expenv_add_dcon]

implement the_d2expenv_add_dcst (d2c) = begin
  let val id = d2cst_sym_get d2c in the_d2expenv_add (id, D2ITEMcst d2c) end
end // end of [the_d2expenv_add_dcst]

implement the_d2expenv_add_dmac_def (d2m) = let
  val id = d2mac_sym_get d2m in the_d2expenv_add (id, D2ITEMmacdef d2m)
end // end of [the_d2expenv_add_dmac_def]

implement the_d2expenv_add_dmac_var (d2v) = let
  val id = d2var_sym_get d2v in the_d2expenv_add (id, D2ITEMmacvar d2v)
end // end of [the_d2expenv_add_dmac_var]

implement the_d2expenv_add_dmac_varlst (d2vs) = begin
  $Lst.list_foreach_fun (d2vs, the_d2expenv_add_dmac_var)
end // end of [the_d2expenv_add_dmac_varlst]

implement the_d2expenv_add_dvar (d2v) = let
  val id = d2var_sym_get d2v in the_d2expenv_add (id, D2ITEMvar d2v)
end // end of [the_d2expenv_add_dvar]

implement the_d2expenv_add_dvarlst (d2vs) = begin
  $Lst.list_foreach_fun (d2vs, the_d2expenv_add_dvar)
end // end of [the_d2expenv_add_dvarlst]

fn the_d2expenv_namespace_find (id: sym_t): d2itemopt_vt = let
  fn f (name: sym_t):<cloptr1> d2itemopt_vt = let
    val r_m = (
      case+ $HT.hashtbl_search (the_d2itemmaptbl, name) of
      | ~Some_vt m => m
      | ~None_vt _ => begin
          prerr "Internal Error: d2expenv_namespace_find: name = ";
          $Sym.prerr_symbol name;
          prerr_newline ();
          $Err.abort {d2itemmapref} ()
        end
    ) : d2itemmapref
  in
    $SymEnv.symmap_ref_search (r_m, id)
  end // end of [f]
in
  $NS.the_namespace_search (f)
end // end of [the_d2expenv_namespace_find]

implement the_d2expenv_find (id) = let
  val ans = $SymEnv.symenv_search (the_d2expenv, id)
in
  case+ ans of
  | Some_vt _ => (fold@ ans; ans)
  | ~None_vt () => let
      val ans = the_d2expenv_namespace_find id
    in
      case+ ans of
      | Some_vt _ => (fold@ ans; ans)
      | ~None_vt () => begin
          $SymEnv.symenv_pervasive_search (the_d2expenv, id)
        end // end of [None_vt]
    end // end of [None_vt]
end // end of [the_d2expenv_find]

implement the_d2expenv_pervasive_find (id) = begin
  $SymEnv.symenv_pervasive_search (the_d2expenv, id)
end // end of [the_d2expenv_pervasive_find]

implement the_d2expenv_find_qua (q, id) = begin
  case+ q.d0ynq_node of
  | $Syn.D0YNQnone () => the_d2expenv_find id
  | $Syn.D0YNQsymdot (q_id) => let
      val fil = case+ the_s2expenv_find q_id of
        | ~Some_vt (S2ITEMfil fil) => fil
        | ~Some_vt _ => begin
            $Loc.prerr_location q.d0ynq_loc;
            prerr ": error(2)";
            prerr ": the qualifier [";
            $Sym.prerr_symbol q_id;
            prerr "] should refer to a filename but it does not.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end
        | ~None_vt _ => begin
            $Loc.prerr_location q.d0ynq_loc;
            prerr ": error(2)";
            prerr ": the qualifier [";
            $Sym.prerr_symbol q_id;
            prerr "] is unrecognized.";
            prerr_newline ();
            $Err.abort {fil_t} ()
          end
      val fil_sym = $Fil.filename_full_sym fil
    in
      case+ $HT.hashtbl_search (the_d2itemmaptbl, fil_sym) of
      | ~Some_vt r_m => $SymEnv.symmap_ref_search (r_m, id)
      | ~None_vt () => None_vt ()
    end
  | _ => None_vt ()
end // end of [the_d2expenv_find_qua]

implement the_d2expenv_pop (pf | (*none*)) = begin
  let prval unit_v () = pf in $SymEnv.symenv_pop (the_d2expenv) end
end // end of [the_d2expenv_pop]

implement the_d2expenv_push () = begin
  (unit_v | $SymEnv.symenv_push (the_d2expenv))
end // end of [the_d2expenv_push]

implement the_d2expenv_localjoin (pf1, pf2 | (*none*)) = let
  prval unit_v () = pf1 and unit_v () = pf2
in
  $SymEnv.symenv_localjoin (the_d2expenv)
end // end of [the_d2expenv_localjoin]

fn the_d2expenv_pervasive_add_top (): void =
  let val m = $SymEnv.symenv_top (the_d2expenv) in
    $SymEnv.symenv_pervasive_add (the_d2expenv, m)
  end

fn the_d2expenv_namespace_add_top (id: sym_t): void = let
  val m = $SymEnv.symenv_top the_d2expenv
  val r_m: d2itemmapref = ref_make_elt (m)
  val ans = $HT.hashtbl_insert (the_d2itemmaptbl, id, r_m)
in
  case+ ans of
  | ~Some_vt _ => begin
      prerr "Internal Error: ";
      prerr "d2expenv_namespace_add_top: id = ";
      $Sym.prerr_symbol id;
      prerr_newline ();
      $Err.abort {void} ()
    end
  | ~None_vt _ => ()  
end // end of [the_d2expenv_namespace_add_top]

fn the_d2expenv_save () = $SymEnv.symenv_save (the_d2expenv)
fn the_d2expenv_restore () = $SymEnv.symenv_restore (the_d2expenv)

end // end of [local]

(* ****** ****** *)

assume staload_level_token = unit_v

local

val the_staload_level = ref_make_elt<int> (0)

in

implement staload_level_get () = !the_staload_level

implement staload_level_inc () = let
  val () = !the_staload_level := !the_staload_level + 1
in
  (unit_v () | ())
end // end of [staload_level_inc]

implement staload_level_dec (pf | (*none*)) = let
  prval unit_v () = pf
in
  !the_staload_level := !the_staload_level - 1
end // end of [staload_level_dec]

end // end of [local]

(* ****** ****** *)

assume trans2_env_token = @(unit_v, unit_v, unit_v)

implement trans2_env_pop (pf | (*none*)) = let
  val () = $NS.the_namespace_pop ()
  val () = the_s2rtenv_pop (pf.0 | (*none*))
  val () = the_s2expenv_pop (pf.1 | (*none*))
  val () = the_d2expenv_pop (pf.2 | (*none*))
in
  // empty
end // end of [trans2_env_pop]

implement trans2_env_push () = let
  val () = $NS.the_namespace_push ()
  val (pf0 | ()) = the_s2rtenv_push ()
  val (pf1 | ()) = the_s2expenv_push ()
  val (pf2 | ()) = the_d2expenv_push ()
in
  (@(pf0, pf1, pf2) | ())
end // end of [trans2_env_push]

implement trans2_env_localjoin (pf1, pf2 | (*none*)) = let
  val () = $NS.the_namespace_localjoin ()
  val () = the_s2rtenv_localjoin (pf1.0, pf2.0 | (*none*))
  val () = the_s2expenv_localjoin (pf1.1, pf2.1 | (*none*))
  val () = the_d2expenv_localjoin (pf1.2, pf2.2 | (*none*))
in
  // empty
end // end of [trans2_env_localjoin]


implement trans2_env_save () = begin
  $NS.the_namespace_save ();
  the_s2rtenv_save (); the_s2expenv_save (); the_d2expenv_save ()
end

implement trans2_env_restore () = begin
  $NS.the_namespace_restore ();
  the_s2rtenv_restore (); the_s2expenv_restore (); the_d2expenv_restore ()
end

implement trans2_env_pervasive_add_top () = let
  val () = the_s2rtenv_pervasive_add_top ()
  val () = the_s2expenv_pervasive_add_top ()
  val () = the_d2expenv_pervasive_add_top ()
in
  // empty
end // end of [trans2_env_pervasive_add_top]

implement trans2_env_namespace_add_top (id) = let
  val () = the_s2rtenv_namespace_add_top (id)
  val () = the_s2expenv_namespace_add_top (id)
  val () = the_d2expenv_namespace_add_top (id)
in
  // empty
end // end of [trans2_env_namespace_add_top]

implement trans2_env_initialize () = begin
  // sort environment
  the_s2rtenv_add ($Sym.symbol_ADDR, S2TEsrt s2rt_addr);
  the_s2rtenv_add ($Sym.symbol_BOOL, S2TEsrt s2rt_bool);
  the_s2rtenv_add ($Sym.symbol_CHAR, S2TEsrt s2rt_char);
  the_s2rtenv_add ($Sym.symbol_EFF, S2TEsrt s2rt_eff);
  the_s2rtenv_add ($Sym.symbol_INT, S2TEsrt s2rt_int);
  the_s2rtenv_add ($Sym.symbol_PROP, S2TEsrt s2rt_prop);
  the_s2rtenv_add ($Sym.symbol_TYPE, S2TEsrt s2rt_type);
  the_s2rtenv_add ($Sym.symbol_T0YPE, S2TEsrt s2rt_t0ype);
  the_s2rtenv_add ($Sym.symbol_VIEW, S2TEsrt s2rt_view);
  the_s2rtenv_add ($Sym.symbol_VIEWTYPE, S2TEsrt s2rt_viewtype);
  the_s2rtenv_add ($Sym.symbol_VIEWT0YPE, S2TEsrt s2rt_viewt0ype);
  the_s2rtenv_add ($Sym.symbol_TYPES, S2TEsrt s2rt_types);
  the_s2rtenv_pervasive_add_top ();
  // dynamic environment
  the_d2expenv_add ($Sym.symbol_LRBRACKETS, D2ITEMsym (nil ()));
  the_d2expenv_pervasive_add_top ()
end // end of [trans2_env_initialize]

(* ****** ****** *)

(* end of [ats_trans2_env.dats] *)

